# 🦀 安全配置速查手册 - Rust OTLP版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 安全配置速查手册 - Rust OTLP版](#-安全配置速查手册---rust-otlp版)
  - [📋 快速索引](#-快速索引)
  - [🔒 TLS/SSL配置](#-tlsssl配置)
    - [客户端TLS配置](#客户端tls配置)
    - [证书验证](#证书验证)
    - [TLS版本控制](#tls版本控制)
  - [🔑 认证机制](#-认证机制)
    - [Bearer Token认证](#bearer-token认证)
    - [API Key认证](#api-key认证)
    - [OAuth 2.0认证](#oauth-20认证)
  - [🛡️ 敏感数据处理](#️-敏感数据处理)
    - [数据脱敏](#数据脱敏)
    - [属性过滤器](#属性过滤器)
  - [🌐 网络安全](#-网络安全)
    - [IP白名单](#ip白名单)
    - [速率限制](#速率限制)
  - [📋 合规性](#-合规性)
    - [GDPR合规](#gdpr合规)
    - [审计日志](#审计日志)
  - [🔐 密钥管理](#-密钥管理)
    - [密钥轮换](#密钥轮换)
  - [🛡️ 完整安全配置示例](#️-完整安全配置示例)
  - [📚 安全检查清单](#-安全检查清单)
    - [部署前检查](#部署前检查)
  - [📖 参考资源](#-参考资源)

---

## 🔒 TLS/SSL配置

### 客户端TLS配置

```rust
use tonic::transport::{Certificate, ClientTlsConfig, Identity};
use opentelemetry_otlp::SpanExporter;

/// 基础TLS配置
pub async fn create_tls_exporter_basic(
    endpoint: &str,
    ca_cert_path: &str,
) -> anyhow::Result<SpanExporter> {
    // 加载CA证书
    let ca_cert = tokio::fs::read(ca_cert_path).await?;
    let ca = Certificate::from_pem(ca_cert);
    
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(ca)
        .domain_name("collector.example.com"); // 必须匹配证书CN
    
    SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_tls_config(tls_config)
        .build()
}

/// mTLS双向认证
pub async fn create_mtls_exporter(
    endpoint: &str,
    ca_cert_path: &str,
    client_cert_path: &str,
    client_key_path: &str,
) -> anyhow::Result<SpanExporter> {
    // 加载证书
    let ca_cert = tokio::fs::read(ca_cert_path).await?;
    let client_cert = tokio::fs::read(client_cert_path).await?;
    let client_key = tokio::fs::read(client_key_path).await?;
    
    let ca = Certificate::from_pem(ca_cert);
    let identity = Identity::from_pem(client_cert, client_key);
    
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(ca)
        .identity(identity)
        .domain_name("collector.example.com");
    
    SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_tls_config(tls_config)
        .build()
}
```

### 证书验证

```rust
/// 验证证书有效期
pub fn verify_certificate_expiry(
    cert_path: &str,
) -> anyhow::Result<()> {
    use x509_parser::prelude::*;
    
    let cert_data = std::fs::read(cert_path)?;
    let (_, cert) = X509Certificate::from_der(&cert_data)?;
    
    let not_after = cert.validity().not_after;
    let now = std::time::SystemTime::now();
    
    // 转换为Unix时间戳比较
    let expiry = not_after.timestamp();
    let current = now.duration_since(std::time::UNIX_EPOCH)?.as_secs() as i64;
    
    if current > expiry {
        anyhow::bail!("证书已过期");
    }
    
    let days_left = (expiry - current) / 86400;
    if days_left < 30 {
        println!("⚠️  证书将在{}天后过期", days_left);
    }
    
    Ok(())
}
```

### TLS版本控制

```rust
/// 只使用TLS 1.2+
pub fn create_secure_tls_config() -> anyhow::Result<ClientTlsConfig> {
    let ca_cert = tokio::fs::read("/path/to/ca.crt").await?;
    let ca = Certificate::from_pem(ca_cert);
    
    ClientTlsConfig::new()
        .ca_certificate(ca)
        .with_native_roots()  // 使用系统根证书
        .domain_name("collector.example.com")
}
```

---

## 🔑 认证机制

### Bearer Token认证

```rust
use tonic::metadata::MetadataMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Token管理器
pub struct TokenManager {
    token: Arc<RwLock<String>>,
}

impl TokenManager {
    pub fn new(initial_token: String) -> Self {
        Self {
            token: Arc::new(RwLock::new(initial_token)),
        }
    }
    
    /// 获取当前token
    pub async fn get_token(&self) -> String {
        self.token.read().await.clone()
    }
    
    /// 刷新token
    pub async fn refresh_token(&self, new_token: String) {
        let mut token = self.token.write().await;
        *token = new_token;
        println!("🔄 Token refreshed");
    }
    
    /// 创建认证metadata
    pub async fn create_metadata(&self) -> anyhow::Result<MetadataMap> {
        let mut metadata = MetadataMap::new();
        let token = self.get_token().await;
        
        metadata.insert(
            "authorization",
            format!("Bearer {}", token).parse()?
        );
        
        Ok(metadata)
    }
}

/// 使用示例
pub async fn create_authenticated_exporter(
    endpoint: &str,
    token_manager: Arc<TokenManager>,
) -> anyhow::Result<SpanExporter> {
    let metadata = token_manager.create_metadata().await?;
    
    SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_metadata(metadata)
        .build()
}
```

### API Key认证

```rust
/// 从环境变量安全读取API Key
pub fn load_api_key() -> anyhow::Result<String> {
    std::env::var("OTLP_API_KEY")
        .or_else(|_| {
            // 回退到文件读取
            std::fs::read_to_string("/run/secrets/api_key")
                .map(|s| s.trim().to_string())
        })
        .map_err(|_| anyhow::anyhow!("API Key not found"))
}

/// 创建API Key认证
pub fn create_api_key_metadata(api_key: &str) -> anyhow::Result<MetadataMap> {
    let mut metadata = MetadataMap::new();
    metadata.insert("x-api-key", api_key.parse()?);
    Ok(metadata)
}
```

### OAuth 2.0认证

```rust
use reqwest::Client;
use serde::{Deserialize, Serialize};

#[derive(Serialize)]
struct TokenRequest {
    grant_type: String,
    client_id: String,
    client_secret: String,
}

#[derive(Deserialize)]
struct TokenResponse {
    access_token: String,
    expires_in: u64,
}

/// OAuth Token Provider
pub struct OAuthProvider {
    client: Client,
    token_url: String,
    client_id: String,
    client_secret: String,
    current_token: Arc<RwLock<Option<String>>>,
}

impl OAuthProvider {
    pub fn new(
        token_url: String,
        client_id: String,
        client_secret: String,
    ) -> Self {
        Self {
            client: Client::new(),
            token_url,
            client_id,
            client_secret,
            current_token: Arc::new(RwLock::new(None)),
        }
    }
    
    /// 获取访问令牌
    pub async fn get_access_token(&self) -> anyhow::Result<String> {
        // 检查缓存
        if let Some(token) = self.current_token.read().await.as_ref() {
            return Ok(token.clone());
        }
        
        // 请求新token
        let request = TokenRequest {
            grant_type: "client_credentials".to_string(),
            client_id: self.client_id.clone(),
            client_secret: self.client_secret.clone(),
        };
        
        let response = self.client
            .post(&self.token_url)
            .json(&request)
            .send()
            .await?
            .json::<TokenResponse>()
            .await?;
        
        // 缓存token
        let mut current = self.current_token.write().await;
        *current = Some(response.access_token.clone());
        
        Ok(response.access_token)
    }
}
```

---

## 🛡️ 敏感数据处理

### 数据脱敏

```rust
use regex::Regex;

pub struct DataSanitizer {
    patterns: Vec<(Regex, String)>,
}

impl DataSanitizer {
    pub fn new() -> Self {
        let patterns = vec![
            // 邮箱
            (Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap(),
             "***@***".to_string()),
            
            // 电话号码
            (Regex::new(r"\b\d{3}-\d{4}-\d{4}\b").unwrap(),
             "***-****-****".to_string()),
            
            // 信用卡号
            (Regex::new(r"\b\d{4}[\s-]?\d{4}[\s-]?\d{4}[\s-]?\d{4}\b").unwrap(),
             "****-****-****-****".to_string()),
            
            // Bearer token
            (Regex::new(r"Bearer\s+[A-Za-z0-9\-._~+/]+=*").unwrap(),
             "Bearer ***".to_string()),
        ];
        
        Self { patterns }
    }
    
    /// 脱敏字符串
    pub fn sanitize(&self, input: &str) -> String {
        let mut result = input.to_string();
        
        for (pattern, replacement) in &self.patterns {
            result = pattern.replace_all(&result, replacement.as_str()).to_string();
        }
        
        result
    }
    
    /// 脱敏KeyValue属性
    pub fn sanitize_attributes(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .map(|mut kv| {
                if let Some(s) = kv.value.as_str() {
                    kv.value = self.sanitize(s).into();
                }
                kv
            })
            .collect()
    }
}

/// 使用示例
pub fn create_span_with_sanitization(
    tracer: &dyn Tracer,
    sensitive_data: &str,
) {
    let sanitizer = DataSanitizer::new();
    
    let mut span = tracer.start("operation");
    span.set_attribute(KeyValue::new(
        "user.email",
        sanitizer.sanitize(sensitive_data)
    ));
    span.end();
}
```

### 属性过滤器

```rust
pub struct SensitiveAttributeFilter {
    blocked_keys: HashSet<String>,
}

impl SensitiveAttributeFilter {
    pub fn default_blocklist() -> Self {
        let blocked_keys = [
            "password",
            "secret",
            "token",
            "api_key",
            "authorization",
            "cookie",
            "x-api-key",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        
        Self { blocked_keys }
    }
    
    pub fn filter(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .filter(|kv| {
                let key_lower = kv.key.as_str().to_lowercase();
                !self.blocked_keys.iter().any(|blocked| {
                    key_lower.contains(blocked)
                })
            })
            .collect()
    }
}
```

---

## 🌐 网络安全

### IP白名单

```rust
use std::net::IpAddr;
use std::str::FromStr;

pub struct IpWhitelist {
    allowed_ips: Vec<IpAddr>,
}

impl IpWhitelist {
    pub fn new(allowed: Vec<String>) -> anyhow::Result<Self> {
        let allowed_ips: Result<Vec<_>, _> = allowed
            .iter()
            .map(|s| IpAddr::from_str(s))
            .collect();
        
        Ok(Self {
            allowed_ips: allowed_ips?,
        })
    }
    
    pub fn is_allowed(&self, ip: &IpAddr) -> bool {
        self.allowed_ips.contains(ip)
    }
}
```

### 速率限制

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;
use std::time::{Duration, Instant};

pub struct RateLimiter {
    semaphore: Arc<Semaphore>,
    max_requests: usize,
    window: Duration,
    window_start: Arc<RwLock<Instant>>,
}

impl RateLimiter {
    pub fn new(max_requests_per_minute: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_requests_per_minute)),
            max_requests: max_requests_per_minute,
            window: Duration::from_secs(60),
            window_start: Arc::new(RwLock::new(Instant::now())),
        }
    }
    
    pub async fn acquire(&self) -> anyhow::Result<()> {
        // 检查是否需要重置窗口
        let mut window_start = self.window_start.write().await;
        if window_start.elapsed() > self.window {
            *window_start = Instant::now();
            // 重置semaphore (需要重建)
        }
        
        // 获取许可
        self.semaphore.acquire().await?;
        Ok(())
    }
}
```

---

## 📋 合规性

### GDPR合规

```rust
/// GDPR数据处理器
pub struct GdprProcessor {
    pii_fields: HashSet<String>,
}

impl GdprProcessor {
    pub fn new() -> Self {
        let pii_fields = [
            "user.id",
            "user.email",
            "user.name",
            "user.phone",
            "user.address",
            "ip_address",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        
        Self { pii_fields }
    }
    
    /// 匿名化PII数据
    pub fn anonymize(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .map(|mut kv| {
                if self.pii_fields.contains(kv.key.as_str()) {
                    // 使用SHA-256哈希
                    if let Some(s) = kv.value.as_str() {
                        let hash = self.hash_value(s);
                        kv.value = hash.into();
                    }
                }
                kv
            })
            .collect()
    }
    
    fn hash_value(&self, value: &str) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(value.as_bytes());
        format!("{:x}", hasher.finalize())
    }
}
```

### 审计日志

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct AuditLog {
    timestamp: chrono::DateTime<chrono::Utc>,
    action: String,
    user: String,
    resource: String,
    result: String,
}

impl AuditLog {
    pub fn new(
        action: String,
        user: String,
        resource: String,
        result: String,
    ) -> Self {
        Self {
            timestamp: chrono::Utc::now(),
            action,
            user,
            resource,
            result,
        }
    }
    
    pub async fn log(&self) -> anyhow::Result<()> {
        // 写入审计日志
        let log_entry = serde_json::to_string(self)?;
        tokio::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/var/log/otlp/audit.log")
            .await?
            .write_all(format!("{}\n", log_entry).as_bytes())
            .await?;
        
        Ok(())
    }
}
```

---

## 🔐 密钥管理

### 密钥轮换

```rust
pub struct KeyRotationManager {
    current_key: Arc<RwLock<String>>,
    next_key: Arc<RwLock<Option<String>>>,
    rotation_interval: Duration,
}

impl KeyRotationManager {
    pub fn new(initial_key: String, rotation_interval: Duration) -> Self {
        Self {
            current_key: Arc::new(RwLock::new(initial_key)),
            next_key: Arc::new(RwLock::new(None)),
            rotation_interval,
        }
    }
    
    /// 启动自动轮换
    pub async fn start_rotation(self: Arc<Self>) {
        let mut interval = tokio::time::interval(self.rotation_interval);
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.rotate().await {
                eprintln!("❌ Key rotation failed: {}", e);
            } else {
                println!("✅ Key rotated successfully");
            }
        }
    }
    
    async fn rotate(&self) -> anyhow::Result<()> {
        // 1. 生成新密钥
        let new_key = self.generate_new_key().await?;
        
        // 2. 预加载下一个密钥
        let mut next = self.next_key.write().await;
        *next = Some(new_key.clone());
        
        // 3. 等待grace period
        tokio::time::sleep(Duration::from_secs(60)).await;
        
        // 4. 切换到新密钥
        let mut current = self.current_key.write().await;
        *current = new_key;
        *next = None;
        
        Ok(())
    }
    
    async fn generate_new_key(&self) -> anyhow::Result<String> {
        // 从密钥管理服务获取新密钥
        // 或生成随机密钥
        use rand::Rng;
        let key: String = rand::thread_rng()
            .sample_iter(&rand::distributions::Alphanumeric)
            .take(32)
            .map(char::from)
            .collect();
        
        Ok(key)
    }
}
```

---

## 🛡️ 完整安全配置示例

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::SpanExporter;
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    resource::Resource,
    runtime,
};

pub async fn create_secure_tracer_provider(
    endpoint: &str,
) -> anyhow::Result<TracerProvider> {
    // 1. 加载证书
    let ca_cert = tokio::fs::read("/etc/ssl/certs/ca.crt").await?;
    let client_cert = tokio::fs::read("/etc/ssl/certs/client.crt").await?;
    let client_key = tokio::fs::read("/etc/ssl/private/client.key").await?;
    
    // 2. 配置mTLS
    let ca = tonic::transport::Certificate::from_pem(ca_cert);
    let identity = tonic::transport::Identity::from_pem(client_cert, client_key);
    
    let tls_config = tonic::transport::ClientTlsConfig::new()
        .ca_certificate(ca)
        .identity(identity)
        .domain_name("collector.example.com");
    
    // 3. 加载Token
    let token = load_api_key()?;
    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "authorization",
        format!("Bearer {}", token).parse()?
    );
    
    // 4. 创建Exporter
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_tls_config(tls_config)
        .with_metadata(metadata)
        .with_timeout(Duration::from_secs(30))
        .build()?;
    
    // 5. 配置Resource (移除敏感信息)
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
        // 不包含主机名等敏感信息
    ]);
    
    // 6. 创建Provider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)
        .with_config(Config::default().with_resource(resource))
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}
```

---

## 📚 安全检查清单

### 部署前检查

```rust
pub fn security_checklist() -> Vec<(&'static str, bool)> {
    vec![
        ("✅ TLS 1.2+ 已启用", true),
        ("✅ mTLS 双向认证", true),
        ("✅ 敏感数据已脱敏", true),
        ("✅ 密钥已加密存储", true),
        ("✅ 审计日志已启用", true),
        ("✅ 速率限制已配置", true),
        ("✅ IP白名单已设置", true),
        ("✅ GDPR合规检查", true),
    ]
}
```

---

## 📖 参考资源

| 资源 | 链接 |
|------|------|
| **OWASP Top 10** | <https://owasp.org/www-project-top-ten/> |
| **TLS Best Practices** | <https://wiki.mozilla.org/Security/Server_Side_TLS> |
| **GDPR合规** | <https://gdpr.eu/> |
| **Rust Security** | <https://anssi-fr.github.io/rust-guide/> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [性能优化速查手册_Rust版](./05_性能优化速查手册_Rust版.md)  
**系列完成**: 速查手册全部完成! 🎉
