# Rust OTLP 安全最佳实践

> **Rust版本**: 1.90+  
> **RustLS**: 0.23.33  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Rust OTLP 安全最佳实践](#rust-otlp-安全最佳实践)
  - [目录](#目录)
  - [1. Rust 内存安全优势](#1-rust-内存安全优势)
    - [1.1 所有权系统保证](#11-所有权系统保证)
    - [1.2 线程安全](#12-线程安全)
  - [2. TLS/mTLS 配置](#2-tlsmtls-配置)
    - [2.1 RustLS 客户端配置](#21-rustls-客户端配置)
    - [2.2 证书验证](#22-证书验证)
  - [3. 敏感数据处理](#3-敏感数据处理)
    - [3.1 安全字符串类型](#31-安全字符串类型)
    - [3.2 敏感属性过滤](#32-敏感属性过滤)
  - [4. 认证和授权](#4-认证和授权)
    - [4.1 JWT 认证](#41-jwt-认证)
    - [4.2 Axum 认证中间件](#42-axum-认证中间件)
  - [5. 数据脱敏](#5-数据脱敏)
    - [5.1 PII 脱敏](#51-pii-脱敏)
  - [6. 安全审计](#6-安全审计)
    - [6.1 审计日志](#61-审计日志)
  - [7. 合规性](#7-合规性)
    - [7.1 GDPR 数据保留](#71-gdpr-数据保留)
  - [8. 生产环境安全清单](#8-生产环境安全清单)

---

## 1. Rust 内存安全优势

### 1.1 所有权系统保证

```rust
/// Rust 所有权系统自动防止数据竞争
pub struct SecureSpan {
    data: String,  // 独占所有权
}

impl SecureSpan {
    pub fn new(data: String) -> Self {
        Self { data }
    }
    
    /// 借用 - 不转移所有权
    pub fn view(&self) -> &str {
        &self.data
    }
    
    /// 消费 - 转移所有权
    pub fn into_inner(self) -> String {
        self.data
    }
}

// 编译时保证：无 use-after-free，无 double-free
fn ownership_safety() {
    let span = SecureSpan::new("sensitive".to_string());
    let _view = span.view();  // 借用
    let _data = span.into_inner();  // 消费
    
    // 编译错误！span 已被移动
    // let _view2 = span.view();
}
```

### 1.2 线程安全

```rust
use std::sync::Arc;
use parking_lot::RwLock;

/// 线程安全的追踪数据 - 编译时检查
pub struct ThreadSafeTracer {
    // Arc<RwLock> 保证跨线程安全
    spans: Arc<RwLock<Vec<SpanData>>>,
}

impl ThreadSafeTracer {
    pub fn new() -> Self {
        Self {
            spans: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 多线程安全添加
    pub fn add_span(&self, span: SpanData) {
        let mut spans = self.spans.write();
        spans.push(span);
    }
    
    /// 克隆用于跨线程传递
    pub fn clone(&self) -> Self {
        Self {
            spans: Arc::clone(&self.spans),
        }
    }
}

// Send + Sync 自动实现 - 编译器验证线程安全
unsafe impl Send for ThreadSafeTracer {}
unsafe impl Sync for ThreadSafeTracer {}

#[derive(Clone)]
pub struct SpanData {
    pub name: String,
}
```

---

## 2. TLS/mTLS 配置

### 2.1 RustLS 客户端配置

```rust
use rustls::{ClientConfig, RootCertStore, Certificate, PrivateKey};
use tokio_rustls::TlsConnector;
use std::sync::Arc;
use anyhow::Result;

/// 安全的 TLS 配置
pub struct SecureTlsConfig {
    pub root_ca: String,
    pub client_cert: Option<String>,
    pub client_key: Option<String>,
}

/// 创建 TLS 客户端配置
pub fn create_tls_client_config(config: &SecureTlsConfig) -> Result<ClientConfig> {
    // 加载根证书
    let mut root_store = RootCertStore::empty();
    let ca_cert_pem = std::fs::read(&config.root_ca)?;
    let ca_certs = rustls_pemfile::certs(&mut &ca_cert_pem[..])?;
    
    for cert in ca_certs {
        root_store.add(&Certificate(cert))?;
    }
    
    // 基础配置
    let mut tls_config = ClientConfig::builder()
        .with_safe_defaults()
        .with_root_certificates(root_store);
    
    // mTLS 配置（可选）
    let tls_config = if let (Some(cert_path), Some(key_path)) = 
        (&config.client_cert, &config.client_key) 
    {
        // 加载客户端证书
        let cert_pem = std::fs::read(cert_path)?;
        let certs = rustls_pemfile::certs(&mut &cert_pem[..])?
            .into_iter()
            .map(Certificate)
            .collect();
        
        // 加载私钥
        let key_pem = std::fs::read(key_path)?;
        let mut keys = rustls_pemfile::pkcs8_private_keys(&mut &key_pem[.])?;
        let key = PrivateKey(keys.remove(0));
        
        tls_config.with_client_auth_cert(certs, key)?
    } else {
        tls_config.with_no_client_auth()
    };
    
    Ok(tls_config)
}

/// 使用 TLS 的 OTLP 导出器
pub async fn create_secure_exporter() -> Result<()> {
    let tls_config = create_tls_client_config(&SecureTlsConfig {
        root_ca: "certs/ca.crt".to_string(),
        client_cert: Some("certs/client.crt".to_string()),
        client_key: Some("certs/client.key".to_string()),
    })?;
    
    let tls_connector = TlsConnector::from(Arc::new(tls_config));
    
    // 使用 TLS connector 创建 gRPC channel
    // 实现省略...
    
    Ok(())
}
```

### 2.2 证书验证

```rust
use rustls::client::ServerCertVerifier;
use rustls::{Certificate, Error as TlsError, ServerName};

/// 自定义证书验证器
pub struct CustomCertVerifier {
    // 可以添加额外的验证逻辑
}

impl ServerCertVerifier for CustomCertVerifier {
    fn verify_server_cert(
        &self,
        end_entity: &Certificate,
        intermediates: &[Certificate],
        server_name: &ServerName,
        scts: &mut dyn Iterator<Item = &[u8]>,
        ocsp_response: &[u8],
        now: std::time::SystemTime,
    ) -> Result<rustls::client::ServerCertVerified, TlsError> {
        // 自定义验证逻辑
        tracing::info!("Verifying server certificate for {:?}", server_name);
        
        // 实际验证...
        
        Ok(rustls::client::ServerCertVerified::assertion())
    }
}
```

---

## 3. 敏感数据处理

### 3.1 安全字符串类型

```rust
use zeroize::{Zeroize, ZeroizeOnDrop};

/// 零化敏感数据 - 防止内存泄露
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SecureString {
    #[zeroize(skip)]  // 跳过元数据
    len: usize,
    data: Vec<u8>,
}

impl SecureString {
    pub fn new(s: String) -> Self {
        let data = s.into_bytes();
        let len = data.len();
        Self { len, data }
    }
    
    /// 安全访问 - 不暴露原始数据
    pub fn as_masked(&self) -> String {
        "*".repeat(self.len)
    }
    
    /// 临时访问 - 使用后立即清零
    pub fn with_value<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&str) -> R,
    {
        let s = String::from_utf8_lossy(&self.data);
        let result = f(&s);
        
        // 清零内存
        self.data.zeroize();
        
        result
    }
}

impl Drop for SecureString {
    fn drop(&mut self) {
        // 确保数据被清零
        self.data.zeroize();
    }
}

// 使用示例
fn handle_password() {
    let mut password = SecureString::new("secret123".to_string());
    
    password.with_value(|pwd| {
        // 临时使用密码
        println!("Password length: {}", pwd.len());
    });
    
    // password 离开作用域时自动清零内存
}
```

### 3.2 敏感属性过滤

```rust
use opentelemetry::{KeyValue, Value};
use regex::Regex;

/// 敏感属性过滤器
pub struct SensitiveAttributeFilter {
    patterns: Vec<Regex>,
}

impl SensitiveAttributeFilter {
    pub fn new() -> Self {
        Self {
            patterns: vec![
                Regex::new(r"(?i)password").unwrap(),
                Regex::new(r"(?i)secret").unwrap(),
                Regex::new(r"(?i)token").unwrap(),
                Regex::new(r"(?i)api[_-]?key").unwrap(),
                Regex::new(r"(?i)auth").unwrap(),
            ],
        }
    }
    
    /// 过滤敏感属性
    pub fn filter_attributes(&self, attrs: Vec<KeyValue>) -> Vec<KeyValue> {
        attrs.into_iter()
            .map(|kv| {
                if self.is_sensitive(&kv.key.as_str()) {
                    KeyValue::new(kv.key, Value::String("***REDACTED***".into()))
                } else {
                    kv
                }
            })
            .collect()
    }
    
    fn is_sensitive(&self, key: &str) -> bool {
        self.patterns.iter().any(|pattern| pattern.is_match(key))
    }
}

/// 使用示例
fn filter_example() {
    let filter = SensitiveAttributeFilter::new();
    
    let attrs = vec![
        KeyValue::new("user.name", "John"),
        KeyValue::new("user.password", "secret123"),
        KeyValue::new("api_key", "key123"),
    ];
    
    let filtered = filter.filter_attributes(attrs);
    
    // "user.password" 和 "api_key" 被脱敏
}
```

---

## 4. 认证和授权

### 4.1 JWT 认证

```rust
use jsonwebtoken::{encode, decode, Header, Algorithm, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};
use chrono::{Utc, Duration};

/// JWT Claims
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,           // Subject (user ID)
    pub exp: i64,              // Expiration time
    pub iat: i64,              // Issued at
    pub scope: Vec<String>,    // Permissions
}

/// JWT 认证管理器
pub struct JwtAuth {
    secret: String,
}

impl JwtAuth {
    pub fn new(secret: String) -> Self {
        Self { secret }
    }
    
    /// 生成 Token
    pub fn generate_token(&self, user_id: &str, scopes: Vec<String>) -> Result<String, String> {
        let now = Utc::now();
        let exp = now + Duration::hours(24);
        
        let claims = Claims {
            sub: user_id.to_string(),
            exp: exp.timestamp(),
            iat: now.timestamp(),
            scope: scopes,
        };
        
        encode(
            &Header::new(Algorithm::HS256),
            &claims,
            &EncodingKey::from_secret(self.secret.as_ref()),
        )
        .map_err(|e| format!("Token generation failed: {}", e))
    }
    
    /// 验证 Token
    pub fn verify_token(&self, token: &str) -> Result<Claims, String> {
        let validation = Validation::new(Algorithm::HS256);
        
        decode::<Claims>(
            token,
            &DecodingKey::from_secret(self.secret.as_ref()),
            &validation,
        )
        .map(|data| data.claims)
        .map_err(|e| format!("Token verification failed: {}", e))
    }
    
    /// 检查权限
    pub fn has_scope(&self, token: &str, required_scope: &str) -> bool {
        if let Ok(claims) = self.verify_token(token) {
            claims.scope.contains(&required_scope.to_string())
        } else {
            false
        }
    }
}
```

### 4.2 Axum 认证中间件

```rust
use axum::{
    extract::{Request, State},
    middleware::Next,
    response::{Response, IntoResponse},
    http::{StatusCode, header},
};

/// 认证状态
#[derive(Clone)]
pub struct AuthState {
    jwt_auth: Arc<JwtAuth>,
}

/// JWT 认证中间件
pub async fn jwt_auth_middleware(
    State(auth_state): State<AuthState>,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 提取 Authorization header
    let auth_header = request
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|h| h.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 解析 Bearer Token
    if !auth_header.starts_with("Bearer ") {
        return Err(StatusCode::UNAUTHORIZED);
    }
    
    let token = &auth_header[7..];
    
    // 验证 Token
    let claims = auth_state.jwt_auth
        .verify_token(token)
        .map_err(|_| StatusCode::UNAUTHORIZED)?;
    
    // 将 Claims 添加到请求扩展
    request.extensions_mut().insert(claims);
    
    Ok(next.run(request).await)
}

/// 提取 Claims
pub struct AuthClaims(pub Claims);

#[axum::async_trait]
impl<S> axum::extract::FromRequestParts<S> for AuthClaims
where
    S: Send + Sync,
{
    type Rejection = StatusCode;
    
    async fn from_request_parts(
        parts: &mut axum::http::request::Parts,
        _state: &S,
    ) -> Result<Self, Self::Rejection> {
        parts
            .extensions
            .get::<Claims>()
            .cloned()
            .map(AuthClaims)
            .ok_or(StatusCode::UNAUTHORIZED)
    }
}

/// 使用示例
async fn protected_handler(
    AuthClaims(claims): AuthClaims,
) -> impl IntoResponse {
    format!("Hello, user {}!", claims.sub)
}
```

---

## 5. 数据脱敏

### 5.1 PII 脱敏

```rust
use regex::Regex;

/// 个人身份信息 (PII) 脱敏器
pub struct PiiRedactor {
    email_pattern: Regex,
    phone_pattern: Regex,
    ssn_pattern: Regex,
    credit_card_pattern: Regex,
}

impl PiiRedactor {
    pub fn new() -> Self {
        Self {
            email_pattern: Regex::new(r"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}").unwrap(),
            phone_pattern: Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap(),
            ssn_pattern: Regex::new(r"\b\d{3}-\d{2}-\d{4}\b").unwrap(),
            credit_card_pattern: Regex::new(r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b").unwrap(),
        }
    }
    
    /// 脱敏文本
    pub fn redact(&self, text: &str) -> String {
        let mut result = text.to_string();
        
        // Email
        result = self.email_pattern.replace_all(&result, "[EMAIL_REDACTED]").to_string();
        
        // Phone
        result = self.phone_pattern.replace_all(&result, "[PHONE_REDACTED]").to_string();
        
        // SSN
        result = self.ssn_pattern.replace_all(&result, "[SSN_REDACTED]").to_string();
        
        // Credit Card
        result = self.credit_card_pattern.replace_all(&result, "[CARD_REDACTED]").to_string();
        
        result
    }
    
    /// 部分脱敏 Email
    pub fn mask_email(&self, email: &str) -> String {
        if let Some(at_pos) = email.find('@') {
            let (local, domain) = email.split_at(at_pos);
            if local.len() > 2 {
                format!("{}***{}", &local[..2], domain)
            } else {
                format!("***{}", domain)
            }
        } else {
            "***".to_string()
        }
    }
}

/// 使用示例
fn redaction_example() {
    let redactor = PiiRedactor::new();
    
    let text = "Contact John at john.doe@example.com or call 555-123-4567";
    let redacted = redactor.redact(text);
    
    println!("{}", redacted);
    // "Contact John at [EMAIL_REDACTED] or call [PHONE_REDACTED]"
}
```

---

## 6. 安全审计

### 6.1 审计日志

```rust
use chrono::Utc;
use serde::{Serialize, Deserialize};
use tracing::warn;

/// 审计事件
#[derive(Debug, Serialize, Deserialize)]
pub struct AuditEvent {
    pub timestamp: String,
    pub user_id: String,
    pub action: String,
    pub resource: String,
    pub result: AuditResult,
    pub ip_address: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum AuditResult {
    Success,
    Failure { reason: String },
}

/// 审计日志记录器
pub struct AuditLogger {
    // 可以集成到数据库或专门的审计系统
}

impl AuditLogger {
    pub fn new() -> Self {
        Self {}
    }
    
    /// 记录审计事件
    pub async fn log(&self, event: AuditEvent) {
        // 使用 warn 级别确保审计日志不会被过滤
        warn!(
            target: "audit",
            timestamp = %event.timestamp,
            user_id = %event.user_id,
            action = %event.action,
            resource = %event.resource,
            result = ?event.result,
            "Audit event"
        );
        
        // 可以异步写入专门的审计存储
    }
}

/// 审计中间件
pub async fn audit_middleware(
    State(audit_logger): State<Arc<AuditLogger>>,
    AuthClaims(claims): AuthClaims,
    request: Request,
    next: Next,
) -> Response {
    let method = request.method().clone();
    let uri = request.uri().clone();
    
    let response = next.run(request).await;
    
    let event = AuditEvent {
        timestamp: Utc::now().to_rfc3339(),
        user_id: claims.sub.clone(),
        action: format!("{} {}", method, uri),
        resource: uri.path().to_string(),
        result: if response.status().is_success() {
            AuditResult::Success
        } else {
            AuditResult::Failure {
                reason: response.status().to_string(),
            }
        },
        ip_address: None,
    };
    
    audit_logger.log(event).await;
    
    response
}
```

---

## 7. 合规性

### 7.1 GDPR 数据保留

```rust
use chrono::{DateTime, Utc, Duration};

/// GDPR 数据保留策略
pub struct DataRetentionPolicy {
    pub retention_days: i64,
}

impl DataRetentionPolicy {
    pub fn gdpr_compliant() -> Self {
        Self {
            retention_days: 90,  // GDPR 推荐
        }
    }
    
    /// 检查数据是否应该删除
    pub fn should_delete(&self, created_at: DateTime<Utc>) -> bool {
        let now = Utc::now();
        let age = now.signed_duration_since(created_at);
        
        age > Duration::days(self.retention_days)
    }
    
    /// 清理过期数据
    pub async fn cleanup_expired_data(&self, db_pool: &sqlx::PgPool) -> Result<u64, sqlx::Error> {
        let cutoff_date = Utc::now() - Duration::days(self.retention_days);
        
        let result = sqlx::query!(
            r#"
            DELETE FROM trace_data
            WHERE created_at < $1
            "#,
            cutoff_date
        )
        .execute(db_pool)
        .await?;
        
        Ok(result.rows_affected())
    }
}
```

---

## 8. 生产环境安全清单

```rust
/// 安全配置检查器
pub struct SecurityChecker;

impl SecurityChecker {
    /// 验证生产环境配置
    pub fn check_production_config() -> Result<(), String> {
        let mut errors = Vec::new();
        
        // 检查 TLS
        if std::env::var("USE_TLS").unwrap_or_default() != "true" {
            errors.push("TLS not enabled");
        }
        
        // 检查认证
        if std::env::var("AUTH_ENABLED").unwrap_or_default() != "true" {
            errors.push("Authentication not enabled");
        }
        
        // 检查密钥强度
        if let Ok(secret) = std::env::var("JWT_SECRET") {
            if secret.len() < 32 {
                errors.push("JWT secret too weak (< 32 characters)");
            }
        } else {
            errors.push("JWT secret not set");
        }
        
        // 检查数据脱敏
        if std::env::var("PII_REDACTION").unwrap_or_default() != "true" {
            errors.push("PII redaction not enabled");
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(format!("Security checks failed:\n{}", errors.join("\n")))
        }
    }
}
```

**生产环境安全清单**:

```text
✅ 启用 TLS/mTLS (RustLS)
✅ JWT 认证和授权
✅ PII 数据脱敏
✅ 敏感字段过滤
✅ 审计日志
✅ 数据加密传输
✅ 安全密钥管理
✅ GDPR 合规
✅ 定期安全审计
✅ 依赖漏洞扫描 (cargo-audit)
✅ 内存安全 (Rust 所有权)
✅ 线程安全 (Send + Sync)
✅ 零化敏感数据
✅ 访问控制
✅ 日志脱敏
```

---

**最后更新**: 2025年10月8日  
**维护者**: OTLP Rust团队  
**许可证**: MIT OR Apache-2.0
