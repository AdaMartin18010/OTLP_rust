# 🦀 华为云OpenTelemetry集成指南 - Rust 1.90完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **华为云服务**: LTS, APM, AOM  
> **最后更新**: 2025年10月11日

---

## 📦 依赖配置

```toml
[package]
name = "huaweicloud-otlp-rust"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry核心
opentelemetry = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["tonic", "grpc-tonic"] }
opentelemetry-semantic-conventions = "0.31.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
tonic = { version = "0.12.3", features = ["gzip", "tls"] }

# HTTP/序列化
reqwest = { version = "0.12.9", features = ["json", "gzip"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt", "json"] }
tracing-opentelemetry = "0.31.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 认证与加密
hmac = "0.12"
sha2 = "0.10"
base64 = "0.22"
chrono = "0.4"
```

---

## 📊 LTS日志服务集成

### LTS配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::LogExporter;
use opentelemetry_sdk::{
    logs::LoggerProvider,
    resource::Resource,
    runtime,
};
use std::time::Duration;

/// 华为云LTS配置
#[derive(Debug, Clone)]
pub struct HuaweiLtsConfig {
    /// 华为云AccessKey (AK)
    pub access_key: String,
    /// 华为云SecretKey (SK)
    pub secret_key: String,
    /// LTS Endpoint
    pub endpoint: String,
    /// Project ID
    pub project_id: String,
    /// 日志组ID
    pub log_group_id: String,
    /// 日志流ID
    pub log_stream_id: String,
    /// Region
    pub region: String,
}

/// 初始化华为云LTS日志提供者
pub async fn init_huawei_lts_logger(
    config: HuaweiLtsConfig,
) -> anyhow::Result<LoggerProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "huawei_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
        KeyValue::new("cloud.platform", "huawei_cloud_lts"),
    ]);

    // 构建认证信息
    let auth_headers = build_huawei_auth_headers(&config)?;

    let mut metadata = tonic::metadata::MetadataMap::new();
    for (key, value) in auth_headers {
        metadata.insert(
            tonic::metadata::MetadataKey::from_bytes(key.as_bytes())?,
            value.parse()?,
        );
    }

    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(30))
        .with_compression(tonic::codec::CompressionEncoding::Gzip)
        .with_metadata(metadata)
        .build()?;

    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter, runtime::Tokio)
        .build();

    global::set_logger_provider(logger_provider.clone());

    Ok(logger_provider)
}

/// 构建华为云认证头
fn build_huawei_auth_headers(
    config: &HuaweiLtsConfig,
) -> anyhow::Result<Vec<(String, String)>> {
    use hmac::{Hmac, Mac};
    use sha2::Sha256;

    type HmacSha256 = Hmac<Sha256>;

    let timestamp = chrono::Utc::now().format("%Y%m%dT%H%M%SZ").to_string();
    
    // 构建待签名字符串
    let string_to_sign = format!(
        "POST\n/v2/{}/groups/{}/streams/{}/logs\n\nhost:{}\nx-sdk-date:{}\n",
        config.project_id,
        config.log_group_id,
        config.log_stream_id,
        config.endpoint,
        timestamp
    );

    // 计算签名
    let mut mac = HmacSha256::new_from_slice(config.secret_key.as_bytes())?;
    mac.update(string_to_sign.as_bytes());
    let signature = base64::encode(mac.finalize().into_bytes());

    Ok(vec![
        ("X-Sdk-Date".to_string(), timestamp),
        ("Authorization".to_string(), format!("SDK-HMAC-SHA256 Access={}, Signature={}", 
            config.access_key, signature)),
        ("X-Project-Id".to_string(), config.project_id.clone()),
    ])
}

/// 结构化日志示例
use tracing::{info, warn, error};

pub async fn log_user_action(user_id: &str, action: &str) {
    info!(
        target: "huawei_lts",
        user.id = user_id,
        action = action,
        region = "cn-north-4",
        "User action logged"
    );
}
```

---

## 🚀 APM应用性能管理集成

### APM Trace集成

```rust
use opentelemetry::{global, trace::{Tracer, Span, SpanKind, Status}};
use opentelemetry_otlp::SpanExporter;
use opentelemetry_sdk::{
    trace::{Config, Sampler, TracerProvider},
    resource::Resource,
    runtime,
};

/// 华为云APM配置
#[derive(Debug, Clone)]
pub struct HuaweiApmConfig {
    /// APM接入点
    pub endpoint: String,
    /// APM Token
    pub token: String,
    /// Region
    pub region: String,
}

/// 初始化华为云APM Tracer
pub async fn init_huawei_apm_tracer(
    config: HuaweiApmConfig,
) -> anyhow::Result<TracerProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "huawei_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
    ]);

    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "x-hw-apm-token",
        config.token.parse()?,
    );

    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(30))
        .with_compression(tonic::codec::CompressionEncoding::Gzip)
        .with_metadata(metadata)
        .build()?;

    // Tail采样策略
    let sampler = Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10%采样
    ));

    let tracer_provider = TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(sampler)
                .with_resource(resource)
        )
        .with_batch_exporter(exporter, runtime::Tokio)
        .build();

    global::set_tracer_provider(tracer_provider.clone());

    Ok(tracer_provider)
}

/// Axum Web服务器集成
use axum::{
    Router,
    routing::get,
    extract::{Path, State},
    response::Json,
    middleware::{self, Next},
};
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

async fn tracing_middleware(
    State(state): State<AppState>,
    req: axum::extract::Request,
    next: Next,
) -> axum::response::Response {
    let tracer = &state.tracer;
    let method = req.method().clone();
    let uri = req.uri().clone();

    let mut span = tracer
        .span_builder(format!("{} {}", method, uri.path()))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.url", uri.to_string()),
            KeyValue::new("cloud.provider", "huawei_cloud"),
        ])
        .start(tracer);

    let response = next.run(req).await;

    span.set_attribute(KeyValue::new(
        "http.status_code",
        response.status().as_u16() as i64
    ));

    if response.status().is_success() {
        span.set_status(Status::Ok);
    } else {
        span.set_status(Status::error(format!("HTTP {}", response.status())));
    }

    span.end();
    response
}

/// 数据库操作追踪
use sqlx::PgPool;

pub async fn query_with_trace(
    pool: &PgPool,
    tracer: &dyn Tracer,
    query: &str,
) -> anyhow::Result<Vec<String>> {
    let mut span = tracer
        .span_builder("db.query")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.operation", "SELECT"),
        ])
        .start(tracer);

    let result = sqlx::query_scalar::<_, String>(query)
        .fetch_all(pool)
        .await;

    match &result {
        Ok(rows) => {
            span.set_attribute(KeyValue::new("db.rows", rows.len() as i64));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
        }
    }

    span.end();
    result.map_err(Into::into)
}
```

---

## 📈 AOM应用运维管理集成

### Metrics集成

```rust
use opentelemetry::{global, metrics::{Counter, Histogram, Meter}};
use opentelemetry_otlp::MetricsExporter;
use opentelemetry_sdk::{
    metrics::{MeterProvider, PeriodicReader},
    resource::Resource,
    runtime,
};

/// AOM配置
#[derive(Debug, Clone)]
pub struct HuaweiAomConfig {
    pub endpoint: String,
    pub access_key: String,
    pub secret_key: String,
    pub project_id: String,
    pub region: String,
}

/// 初始化AOM MeterProvider
pub async fn init_huawei_aom_meter(
    config: HuaweiAomConfig,
) -> anyhow::Result<MeterProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "huawei_cloud"),
    ]);

    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert("x-ak", config.access_key.parse()?);
    metadata.insert("x-sk", config.secret_key.parse()?);
    metadata.insert("x-project-id", config.project_id.parse()?);

    let exporter = MetricsExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_compression(tonic::codec::CompressionEncoding::Snappy)
        .with_metadata(metadata)
        .build()?;

    let reader = PeriodicReader::builder(exporter, runtime::Tokio)
        .with_interval(Duration::from_secs(60))
        .build();

    let meter_provider = MeterProvider::builder()
        .with_resource(resource)
        .with_reader(reader)
        .build();

    global::set_meter_provider(meter_provider.clone());

    Ok(meter_provider)
}

/// 业务指标
pub struct AppMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    errors_total: Counter<u64>,
}

impl AppMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("http_requests_total")
                .with_description("Total HTTP requests")
                .init(),

            request_duration: meter
                .f64_histogram("http_request_duration_seconds")
                .with_description("HTTP request duration")
                .with_unit("s")
                .init(),

            errors_total: meter
                .u64_counter("http_errors_total")
                .with_description("Total HTTP errors")
                .init(),
        }
    }

    pub fn record_request(&self, method: &str, status: u16, duration: Duration) {
        let labels = &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("status", status as i64),
        ];

        self.requests_total.add(1, labels);
        self.request_duration.record(duration.as_secs_f64(), labels);

        if status >= 400 {
            self.errors_total.add(1, labels);
        }
    }
}
```

---

## 🏗️ 完整微服务示例

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 环境变量
    dotenvy::dotenv().ok();

    // 日志初始化
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .json()
        .init();

    // LTS日志
    let lts_config = HuaweiLtsConfig {
        access_key: std::env::var("HUAWEI_ACCESS_KEY")?,
        secret_key: std::env::var("HUAWEI_SECRET_KEY")?,
        endpoint: "lts.cn-north-4.myhuaweicloud.com".to_string(),
        project_id: std::env::var("HUAWEI_PROJECT_ID")?,
        log_group_id: std::env::var("LOG_GROUP_ID")?,
        log_stream_id: std::env::var("LOG_STREAM_ID")?,
        region: "cn-north-4".to_string(),
    };

    let logger_provider = init_huawei_lts_logger(lts_config).await?;

    // APM追踪
    let apm_config = HuaweiApmConfig {
        endpoint: "apm-access.cn-north-4.myhuaweicloud.com:4317".to_string(),
        token: std::env::var("HUAWEI_APM_TOKEN")?,
        region: "cn-north-4".to_string(),
    };

    let tracer_provider = init_huawei_apm_tracer(apm_config).await?;
    let tracer = global::tracer("my-service");

    // AOM指标
    let aom_config = HuaweiAomConfig {
        endpoint: std::env::var("AOM_ENDPOINT")?,
        access_key: std::env::var("HUAWEI_ACCESS_KEY")?,
        secret_key: std::env::var("HUAWEI_SECRET_KEY")?,
        project_id: std::env::var("HUAWEI_PROJECT_ID")?,
        region: "cn-north-4".to_string(),
    };

    let meter_provider = init_huawei_aom_meter(aom_config).await?;

    // 构建应用
    let app_state = AppState {
        tracer: Arc::new(tracer),
    };

    let app = Router::new()
        .route("/health", get(health_check))
        .route("/users/:id", get(get_user))
        .layer(middleware::from_fn_state(
            app_state.clone(),
            tracing_middleware,
        ))
        .with_state(app_state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    tracing::info!("Server started on {}", listener.local_addr()?);

    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await?;

    // 优雅关闭
    tracer_provider.shutdown()?;
    logger_provider.shutdown()?;
    meter_provider.shutdown()?;

    Ok(())
}

async fn shutdown_signal() {
    tokio::signal::ctrl_c()
        .await
        .expect("failed to install CTRL+C handler");
    tracing::info!("Shutdown signal received");
}

async fn health_check() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "status": "healthy",
        "cloud": "huawei_cloud",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

async fn get_user(
    Path(user_id): Path<String>,
) -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "user_id": user_id,
        "name": "User Name",
    }))
}
```

---

## 💡 最佳实践

### 1. 成本优化

```rust
/// 智能采样配置
pub fn cost_optimized_sampler() -> Sampler {
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10%采样
    ))
}

/// 批处理配置
pub fn optimized_batch_config() -> Config {
    Config::default()
        .with_max_export_batch_size(1024)
        .with_max_queue_size(4096)
        .with_scheduled_delay(Duration::from_secs(5))
}
```

### 2. 错误处理

```rust
#[derive(thiserror::Error, Debug)]
pub enum HuaweiCloudError {
    #[error("LTS authentication failed: {0}")]
    LtsAuthFailed(String),
    
    #[error("APM connection failed: {0}")]
    ApmConnectionFailed(String),
    
    #[error("AOM metrics export failed: {0}")]
    AomExportFailed(String),
    
    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),
}
```

### 3. 诊断工具

```rust
pub async fn diagnose_huawei_cloud() -> anyhow::Result<()> {
    println!("🔍 Diagnosing Huawei Cloud integration...\n");

    // 1. 测试LTS连接
    println!("1️⃣ Testing LTS connection...");
    // 实际测试代码

    // 2. 测试APM连接
    println!("\n2️⃣ Testing APM connection...");
    // 实际测试代码

    // 3. 测试AOM连接
    println!("\n3️⃣ Testing AOM connection...");
    // 实际测试代码

    Ok(())
}
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **OpenTelemetry Rust** | <https://github.com/open-telemetry/opentelemetry-rust> |
| **华为云LTS** | <https://support.huaweicloud.com/lts/index.html> |
| **APM文档** | <https://support.huaweicloud.com/apm/index.html> |
| **AOM文档** | <https://support.huaweicloud.com/aom/index.html> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [腾讯云OTLP集成指南_Rust完整版](./02_腾讯云OTLP集成指南_Rust完整版.md)  
**系列完成**: 国内三大云平台Rust集成指南全部完成! 🎉
