# 多租户隔离与安全 - Rust 完整版

## 目录

- [多租户隔离与安全 - Rust 完整版](#多租户隔离与安全---rust-完整版)
  - [目录](#目录)
  - [1. 多租户概述](#1-多租户概述)
    - [1.1 核心挑战](#11-核心挑战)
    - [1.2 租户模型](#12-租户模型)
  - [2. 租户识别与认证](#2-租户识别与认证)
    - [2.1 API Key 认证](#21-api-key-认证)
    - [2.2 JWT 认证](#22-jwt-认证)
  - [3. 数据隔离](#3-数据隔离)
    - [3.1 租户标签注入](#31-租户标签注入)
    - [3.2 存储分区](#32-存储分区)
  - [4. 资源配额管理](#4-资源配额管理)
    - [4.1 速率限制器](#41-速率限制器)
  - [5. 数据脱敏](#5-数据脱敏)
    - [5.1 脱敏处理器](#51-脱敏处理器)
  - [6. TLS 与加密](#6-tls-与加密)
    - [6.1 TLS 配置](#61-tls-配置)
    - [6.2 数据加密（静态数据）](#62-数据加密静态数据)
  - [7. 审计日志](#7-审计日志)
    - [7.1 审计日志记录](#71-审计日志记录)
  - [8. 完整示例](#8-完整示例)
    - [8.1 安全的多租户 Collector](#81-安全的多租户-collector)
  - [总结](#总结)

---

## 1. 多租户概述

**多租户（Multi-Tenancy）** 是指单个 OTLP 系统服务多个独立客户（租户）。

### 1.1 核心挑战

```text
┌─────────────────────────────────────────┐
│  Tenant A                               │
│  ├── App1 → Collector → Backend         │
│  ├── App2 → Collector → Backend         │
│  └── 资源配额：100k spans/min           │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│  Tenant B                               │
│  ├── App1 → Collector → Backend         │
│  └── 资源配额：50k spans/min            │
└─────────────────────────────────────────┘

要求：
1. 数据隔离：Tenant A 无法访问 Tenant B 的数据
2. 资源隔离：Tenant A 不影响 Tenant B 的性能
3. 安全认证：每个租户独立认证
```

### 1.2 租户模型

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Tenant {
    pub id: String,
    pub name: String,
    pub api_key: String,
    pub quotas: ResourceQuotas,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceQuotas {
    /// 最大 Spans/分钟
    pub max_spans_per_minute: usize,
    /// 最大 Metrics/分钟
    pub max_metrics_per_minute: usize,
    /// 最大存储（GB）
    pub max_storage_gb: usize,
}

pub struct TenantRegistry {
    tenants: Arc<RwLock<HashMap<String, Tenant>>>,
}

impl TenantRegistry {
    pub fn new() -> Self {
        Self {
            tenants: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn register(&self, tenant: Tenant) {
        let mut tenants = self.tenants.write().await;
        tenants.insert(tenant.id.clone(), tenant);
    }
    
    pub async fn get(&self, tenant_id: &str) -> Option<Tenant> {
        let tenants = self.tenants.read().await;
        tenants.get(tenant_id).cloned()
    }
    
    pub async fn validate_api_key(&self, api_key: &str) -> Option<Tenant> {
        let tenants = self.tenants.read().await;
        tenants.values().find(|t| t.api_key == api_key).cloned()
    }
}
```

---

## 2. 租户识别与认证

### 2.1 API Key 认证

```rust
use axum::{
    extract::{Request, State},
    http::{HeaderMap, StatusCode},
    middleware::{self, Next},
    response::Response,
};

#[derive(Clone)]
pub struct AuthState {
    registry: Arc<TenantRegistry>,
}

pub async fn auth_middleware(
    State(state): State<AuthState>,
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 从 Header 提取 API Key
    let api_key = headers
        .get("x-api-key")
        .and_then(|v| v.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 验证租户
    let tenant = state.registry
        .validate_api_key(api_key)
        .await
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 将租户信息注入 Request
    request.extensions_mut().insert(tenant);
    
    Ok(next.run(request).await)
}

// 应用中间件
pub fn app(registry: Arc<TenantRegistry>) -> Router {
    let state = AuthState { registry };
    
    Router::new()
        .route("/v1/traces", post(handle_traces))
        .route("/v1/metrics", post(handle_metrics))
        .layer(middleware::from_fn_with_state(state.clone(), auth_middleware))
        .with_state(state)
}
```

### 2.2 JWT 认证

```rust
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub tenant_id: String,
    pub exp: usize,  // 过期时间
    pub iat: usize,  // 签发时间
}

pub struct JwtAuth {
    encoding_key: EncodingKey,
    decoding_key: DecodingKey,
}

impl JwtAuth {
    pub fn new(secret: &str) -> Self {
        Self {
            encoding_key: EncodingKey::from_secret(secret.as_bytes()),
            decoding_key: DecodingKey::from_secret(secret.as_bytes()),
        }
    }
    
    pub fn generate_token(&self, tenant_id: &str) -> Result<String, jsonwebtoken::errors::Error> {
        let now = chrono::Utc::now().timestamp() as usize;
        let claims = Claims {
            tenant_id: tenant_id.to_string(),
            exp: now + 3600,  // 1小时过期
            iat: now,
        };
        
        encode(&Header::default(), &claims, &self.encoding_key)
    }
    
    pub fn validate_token(&self, token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
        let validation = Validation::new(Algorithm::HS256);
        decode::<Claims>(token, &self.decoding_key, &validation)
            .map(|data| data.claims)
    }
}

// JWT 中间件
pub async fn jwt_middleware(
    State(auth): State<Arc<JwtAuth>>,
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let token = headers
        .get("authorization")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.strip_prefix("Bearer "))
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    let claims = auth.validate_token(token)
        .map_err(|_| StatusCode::UNAUTHORIZED)?;
    
    request.extensions_mut().insert(claims);
    
    Ok(next.run(request).await)
}
```

---

## 3. 数据隔离

### 3.1 租户标签注入

```rust
use opentelemetry::KeyValue;

pub struct TenantTagProcessor {
    tenant_id: String,
}

impl TenantTagProcessor {
    pub fn new(tenant_id: String) -> Self {
        Self { tenant_id }
    }
}

#[async_trait]
impl Processor for TenantTagProcessor {
    fn name(&self) -> &str {
        "tenant_tag"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        // 注入租户标签
        span.attributes.push(KeyValue::new("tenant.id", self.tenant_id.clone()));
        Some(span)
    }
}
```

### 3.2 存储分区

```rust
pub struct TenantAwareExporter {
    exporters: Arc<RwLock<HashMap<String, Arc<dyn CollectorExporter>>>>,
}

impl TenantAwareExporter {
    pub fn new() -> Self {
        Self {
            exporters: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn register_tenant_exporter(
        &self,
        tenant_id: String,
        exporter: Arc<dyn CollectorExporter>,
    ) {
        let mut exporters = self.exporters.write().await;
        exporters.insert(tenant_id, exporter);
    }
}

#[async_trait]
impl CollectorExporter for TenantAwareExporter {
    fn name(&self) -> &str {
        "tenant_aware"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        // 按租户分组
        let mut tenant_spans: HashMap<String, Vec<SpanData>> = HashMap::new();
        
        for span in spans {
            let tenant_id = span.attributes
                .iter()
                .find(|kv| kv.key.as_str() == "tenant.id")
                .map(|kv| kv.value.to_string())
                .unwrap_or_else(|| "default".to_string());
            
            tenant_spans.entry(tenant_id).or_insert_with(Vec::new).push(span);
        }
        
        // 并行导出
        let exporters = self.exporters.read().await;
        let mut tasks = Vec::new();
        
        for (tenant_id, spans) in tenant_spans {
            if let Some(exporter) = exporters.get(&tenant_id) {
                let exporter = exporter.clone();
                tasks.push(tokio::spawn(async move {
                    exporter.export_traces(spans).await
                }));
            }
        }
        
        for task in tasks {
            task.await.map_err(|e| ExporterError::BackendError(e.to_string()))??;
        }
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}
```

---

## 4. 资源配额管理

### 4.1 速率限制器

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

pub struct TenantRateLimiter {
    limits: Arc<RwLock<HashMap<String, RateLimitState>>>,
}

struct RateLimitState {
    quota: usize,
    current_count: usize,
    window_start: Instant,
    window_duration: Duration,
}

impl TenantRateLimiter {
    pub fn new() -> Self {
        Self {
            limits: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn set_quota(&self, tenant_id: String, quota: usize, window: Duration) {
        let mut limits = self.limits.write().await;
        limits.insert(tenant_id, RateLimitState {
            quota,
            current_count: 0,
            window_start: Instant::now(),
            window_duration: window,
        });
    }
    
    pub async fn check_and_increment(&self, tenant_id: &str, count: usize) -> Result<(), String> {
        let mut limits = self.limits.write().await;
        
        let state = limits.get_mut(tenant_id).ok_or("Unknown tenant")?;
        
        // 检查是否需要重置窗口
        if state.window_start.elapsed() >= state.window_duration {
            state.current_count = 0;
            state.window_start = Instant::now();
        }
        
        // 检查配额
        if state.current_count + count > state.quota {
            return Err(format!(
                "Quota exceeded: {}/{} spans/min",
                state.current_count, state.quota
            ));
        }
        
        state.current_count += count;
        Ok(())
    }
}

// 中间件
pub async fn rate_limit_middleware(
    State(limiter): State<Arc<TenantRateLimiter>>,
    Extension(tenant): Extension<Tenant>,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 检查配额
    if let Err(e) = limiter.check_and_increment(&tenant.id, 1).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }
    
    Ok(next.run(request).await)
}
```

---

## 5. 数据脱敏

### 5.1 脱敏处理器

```rust
use regex::Regex;

pub struct DataMaskingProcessor {
    email_regex: Regex,
    phone_regex: Regex,
    ssn_regex: Regex,
    credit_card_regex: Regex,
}

impl DataMaskingProcessor {
    pub fn new() -> Self {
        Self {
            email_regex: Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap(),
            phone_regex: Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap(),
            ssn_regex: Regex::new(r"\b\d{3}-\d{2}-\d{4}\b").unwrap(),
            credit_card_regex: Regex::new(r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b").unwrap(),
        }
    }
    
    fn mask_value(&self, value: &str) -> String {
        let value = self.email_regex.replace_all(value, "***@***.***");
        let value = self.phone_regex.replace_all(&value, "***-***-****");
        let value = self.ssn_regex.replace_all(&value, "***-**-****");
        let value = self.credit_card_regex.replace_all(&value, "**** **** **** ****");
        value.to_string()
    }
}

#[async_trait]
impl Processor for DataMaskingProcessor {
    fn name(&self) -> &str {
        "data_masking"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        // 脱敏属性
        for attr in &mut span.attributes {
            let value = attr.value.to_string();
            let masked = self.mask_value(&value);
            if masked != value {
                attr.value = masked.into();
            }
        }
        
        // 脱敏事件
        for event in &mut span.events {
            for attr in &mut event.attributes {
                let value = attr.value.to_string();
                let masked = self.mask_value(&value);
                if masked != value {
                    attr.value = masked.into();
                }
            }
        }
        
        Some(span)
    }
}
```

---

## 6. TLS 与加密

### 6.1 TLS 配置

```rust
use tonic::transport::{Identity, ServerTlsConfig, ClientTlsConfig};
use std::fs;

pub struct TlsConfig {
    pub cert_path: String,
    pub key_path: String,
    pub ca_path: Option<String>,
}

impl TlsConfig {
    pub fn load_server_tls(&self) -> Result<ServerTlsConfig, Box<dyn std::error::Error>> {
        let cert = fs::read_to_string(&self.cert_path)?;
        let key = fs::read_to_string(&self.key_path)?;
        
        let identity = Identity::from_pem(cert, key);
        
        let mut tls_config = ServerTlsConfig::new().identity(identity);
        
        // 客户端证书验证（mTLS）
        if let Some(ca_path) = &self.ca_path {
            let ca_cert = fs::read_to_string(ca_path)?;
            tls_config = tls_config.client_ca_root(ca_cert.parse()?);
        }
        
        Ok(tls_config)
    }
    
    pub fn load_client_tls(&self) -> Result<ClientTlsConfig, Box<dyn std::error::Error>> {
        let cert = fs::read_to_string(&self.cert_path)?;
        let key = fs::read_to_string(&self.key_path)?;
        
        let identity = Identity::from_pem(cert, key);
        
        let tls_config = ClientTlsConfig::new().identity(identity);
        
        Ok(tls_config)
    }
}
```

### 6.2 数据加密（静态数据）

```rust
use aes_gcm::{
    aead::{Aead, KeyInit, OsRng},
    Aes256Gcm, Nonce,
};
use rand::RngCore;

pub struct DataEncryption {
    cipher: Aes256Gcm,
}

impl DataEncryption {
    pub fn new(key: &[u8; 32]) -> Self {
        let cipher = Aes256Gcm::new_from_slice(key).unwrap();
        Self { cipher }
    }
    
    pub fn encrypt(&self, plaintext: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let mut nonce_bytes = [0u8; 12];
        OsRng.fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::from_slice(&nonce_bytes);
        
        let ciphertext = self.cipher.encrypt(nonce, plaintext)
            .map_err(|e| format!("Encryption error: {}", e))?;
        
        // nonce + ciphertext
        let mut result = nonce_bytes.to_vec();
        result.extend_from_slice(&ciphertext);
        
        Ok(result)
    }
    
    pub fn decrypt(&self, data: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        if data.len() < 12 {
            return Err("Invalid data".into());
        }
        
        let nonce = Nonce::from_slice(&data[..12]);
        let ciphertext = &data[12..];
        
        let plaintext = self.cipher.decrypt(nonce, ciphertext)
            .map_err(|e| format!("Decryption error: {}", e))?;
        
        Ok(plaintext)
    }
}
```

---

## 7. 审计日志

### 7.1 审计日志记录

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct AuditEvent {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub tenant_id: String,
    pub user_id: Option<String>,
    pub action: String,
    pub resource: String,
    pub status: String,
    pub ip_address: String,
}

pub struct AuditLogger {
    events: Arc<Mutex<Vec<AuditEvent>>>,
}

impl AuditLogger {
    pub fn new() -> Self {
        Self {
            events: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub async fn log(&self, event: AuditEvent) {
        let mut events = self.events.lock().await;
        events.push(event.clone());
        
        // 同时写入日志
        tracing::info!(
            tenant_id = %event.tenant_id,
            action = %event.action,
            resource = %event.resource,
            status = %event.status,
            "Audit event"
        );
    }
}

// 审计中间件
pub async fn audit_middleware(
    State(logger): State<Arc<AuditLogger>>,
    Extension(tenant): Extension<Tenant>,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    
    let response = next.run(request).await;
    
    let event = AuditEvent {
        timestamp: chrono::Utc::now(),
        tenant_id: tenant.id.clone(),
        user_id: None,
        action: format!("{} {}", method, uri),
        resource: uri.path().to_string(),
        status: response.status().to_string(),
        ip_address: "127.0.0.1".to_string(),
    };
    
    logger.log(event).await;
    
    Ok(response)
}
```

---

## 8. 完整示例

### 8.1 安全的多租户 Collector

```rust
use axum::{Router, routing::post};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化租户注册表
    let registry = Arc::new(TenantRegistry::new());
    
    // 注册租户
    registry.register(Tenant {
        id: "tenant_a".to_string(),
        name: "Tenant A".to_string(),
        api_key: "key_a_12345".to_string(),
        quotas: ResourceQuotas {
            max_spans_per_minute: 100_000,
            max_metrics_per_minute: 50_000,
            max_storage_gb: 100,
        },
        created_at: chrono::Utc::now(),
    }).await;
    
    // 2. 初始化速率限制器
    let rate_limiter = Arc::new(TenantRateLimiter::new());
    rate_limiter.set_quota(
        "tenant_a".to_string(),
        100_000,
        Duration::from_secs(60),
    ).await;
    
    // 3. 初始化审计日志
    let audit_logger = Arc::new(AuditLogger::new());
    
    // 4. 配置 TLS
    let tls_config = TlsConfig {
        cert_path: "certs/server.crt".to_string(),
        key_path: "certs/server.key".to_string(),
        ca_path: Some("certs/ca.crt".to_string()),
    };
    
    // 5. 构建应用
    let app = Router::new()
        .route("/v1/traces", post(handle_traces))
        .layer(middleware::from_fn_with_state(
            Arc::clone(&audit_logger),
            audit_middleware,
        ))
        .layer(middleware::from_fn_with_state(
            Arc::clone(&rate_limiter),
            rate_limit_middleware,
        ))
        .layer(middleware::from_fn_with_state(
            AuthState { registry },
            auth_middleware,
        ));
    
    // 6. 启动服务器
    let addr = "0.0.0.0:4318";
    println!("Secure multi-tenant collector listening on {}", addr);
    
    axum::serve(
        tokio::net::TcpListener::bind(addr).await?,
        app,
    )
    .await?;
    
    Ok(())
}

async fn handle_traces(
    Extension(tenant): Extension<Tenant>,
    Json(payload): Json<TracePayload>,
) -> Result<StatusCode, StatusCode> {
    println!("Received traces from tenant: {}", tenant.id);
    Ok(StatusCode::OK)
}
```

---

## 总结

多租户隔离与安全是 OTLP 系统的**企业级特性**，Rust 实现时需要考虑：

1. **租户识别**：API Key、JWT、mTLS
2. **数据隔离**：租户标签、存储分区
3. **资源配额**：速率限制、内存限制
4. **数据脱敏**：PII 检测与掩码
5. **传输加密**：TLS/mTLS
6. **静态加密**：AES-GCM
7. **审计日志**：所有关键操作记录

通过完善的安全机制，可以构建符合 SOC2、GDPR 等合规要求的 OTLP 系统。
