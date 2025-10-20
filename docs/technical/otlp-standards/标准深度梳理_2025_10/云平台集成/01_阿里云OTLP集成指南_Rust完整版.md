# 🦀 阿里云OpenTelemetry集成指南 - Rust 1.90完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **阿里云服务**: SLS, ARMS, Prometheus  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🦀 阿里云OpenTelemetry集成指南 - Rust 1.90完整版](#-阿里云opentelemetry集成指南---rust-190完整版)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [阿里云可观测性服务](#阿里云可观测性服务)
    - [核心优势](#核心优势)
  - [📦 依赖配置](#-依赖配置)
    - [Cargo.toml](#cargotoml)
    - [Rust Toolchain配置](#rust-toolchain配置)
  - [📊 SLS日志服务集成](#-sls日志服务集成)
    - [完整示例](#完整示例)
    - [类型安全的日志结构](#类型安全的日志结构)
  - [🚀 ARMS应用监控集成](#-arms应用监控集成)
    - [Trace集成](#trace集成)
    - [分布式追踪Context传播](#分布式追踪context传播)
  - [📈 Prometheus监控集成](#-prometheus监控集成)
    - [Metrics集成](#metrics集成)
  - [🏗️ 完整示例](#️-完整示例)
    - [生产级微服务示例](#生产级微服务示例)
  - [💡 最佳实践](#-最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 资源管理](#2-资源管理)
    - [3. 性能优化](#3-性能优化)
  - [🔍 故障排查](#-故障排查)
    - [诊断工具](#诊断工具)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

本文档提供阿里云OpenTelemetry与Rust 1.90的完整集成方案，涵盖SLS、ARMS、Prometheus等服务的生产级配置。

### 阿里云可观测性服务

| 服务 | Rust SDK支持 | 推荐场景 |
|-----|------------|---------|
| **SLS (日志服务)** | ✅ Full | 日志中心化 |
| **ARMS (应用监控)** | ✅ Full | APM追踪 |
| **Prometheus监控** | ✅ Full | 指标监控 |

### 核心优势

```text
✅ 零成本抽象 - Rust编译期优化
✅ 类型安全 - 编译期捕获错误
✅ 高性能 - 原生性能,无GC开销
✅ 内存安全 - 无数据竞争
✅ 异步高效 - Tokio生态成熟
```

---

## 📦 依赖配置

### Cargo.toml

```toml
[package]
name = "aliyun-otlp-example"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry核心
opentelemetry = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31.0", features = ["tonic", "grpc-tonic", "trace", "metrics", "logs"] }
opentelemetry-semantic-conventions = "0.31.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
tonic = { version = "0.12.3", features = ["gzip"] }

# HTTP客户端
reqwest = { version = "0.12.9", features = ["json", "gzip"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt", "json"] }
tracing-opentelemetry = "0.31.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 时间处理
chrono = "0.4"

# 配置管理
config = "0.14"
dotenvy = "0.15"

[dev-dependencies]
tokio-test = "0.4"
```

### Rust Toolchain配置

```toml
# rust-toolchain.toml
[toolchain]
channel = "1.90"
components = ["rustfmt", "clippy", "rust-analyzer"]
targets = ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"]
profile = "default"
```

---

## 📊 SLS日志服务集成

### 完整示例

```rust
use opentelemetry::{
    global,
    logs::LogResult,
    KeyValue,
};
use opentelemetry_otlp::{LogExporter, WithExportConfig};
use opentelemetry_sdk::{
    logs::{self as sdklogs, LoggerProvider},
    resource::{Resource, ResourceDetector},
    runtime,
};
use std::time::Duration;
use tonic::metadata::MetadataMap;

/// 阿里云SLS配置
#[derive(Debug, Clone)]
pub struct AliyunSlsConfig {
    /// 阿里云AccessKey ID
    pub access_key_id: String,
    /// 阿里云AccessKey Secret
    pub access_key_secret: String,
    /// SLS Endpoint (例如: cn-hangzhou.log.aliyuncs.com)
    pub endpoint: String,
    /// Project名称
    pub project: String,
    /// Logstore名称
    pub logstore: String,
    /// Region
    pub region: String,
}

/// 初始化阿里云SLS日志提供者
pub async fn init_aliyun_sls_logger(
    config: AliyunSlsConfig,
) -> anyhow::Result<LoggerProvider> {
    // 创建Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("cloud.provider", "alibaba_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
        KeyValue::new("cloud.platform", "alibaba_cloud_sls"),
    ]);

    // 构建OTLP Endpoint
    let otlp_endpoint = format!(
        "https://{}/v1/logs",
        config.endpoint
    );

    // 创建metadata (用于认证)
    let mut metadata = MetadataMap::new();
    metadata.insert(
        "x-log-apiversion",
        "0.6.0".parse().unwrap(),
    );
    metadata.insert(
        "x-log-signaturemethod",
        "hmac-sha1".parse().unwrap(),
    );
    // 实际生产环境需要实现阿里云签名算法
    metadata.insert(
        "Authorization",
        format!("ACS {}:{}", config.access_key_id, compute_signature(&config))
            .parse()
            .unwrap(),
    );

    // 创建OTLP Log Exporter
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint(&otlp_endpoint)
        .with_timeout(Duration::from_secs(30))
        .with_compression(tonic::codec::CompressionEncoding::Gzip)
        .with_metadata(metadata)
        .build()?;

    // 创建LoggerProvider
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(
            exporter,
            runtime::Tokio,
        )
        .build();

    global::set_logger_provider(logger_provider.clone());

    Ok(logger_provider)
}

/// 计算阿里云API签名 (简化版)
fn compute_signature(config: &AliyunSlsConfig) -> String {
    use hmac::{Hmac, Mac};
    use sha1::Sha1;
    
    type HmacSha1 = Hmac<Sha1>;
    
    let string_to_sign = format!(
        "POST\n/v1/logs\n\nx-log-apiversion:0.6.0\n",
    );
    
    let mut mac = HmacSha1::new_from_slice(config.access_key_secret.as_bytes())
        .expect("HMAC can take key of any size");
    mac.update(string_to_sign.as_bytes());
    
    base64::encode(mac.finalize().into_bytes())
}

/// Tracing集成示例
use tracing::{info, error, warn, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[instrument]
pub async fn example_with_tracing() -> anyhow::Result<()> {
    info!(
        target: "aliyun_sls",
        user_id = "12345",
        action = "login",
        "User logged in successfully"
    );

    warn!(
        target: "aliyun_sls",
        latency_ms = 150,
        "API response slow"
    );

    Ok(())
}

/// 主函数示例
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 加载配置
    let config = AliyunSlsConfig {
        access_key_id: std::env::var("ALIYUN_ACCESS_KEY_ID")?,
        access_key_secret: std::env::var("ALIYUN_ACCESS_KEY_SECRET")?,
        endpoint: "cn-hangzhou.log.aliyuncs.com".to_string(),
        project: "my-observability-project".to_string(),
        logstore: "otlp-logs".to_string(),
        region: "cn-hangzhou".to_string(),
    };

    // 初始化日志提供者
    let logger_provider = init_aliyun_sls_logger(config).await?;

    // 配置tracing订阅者
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(global::tracer("aliyun-sls-example"));

    tracing_subscriber::registry()
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer())
        .init();

    // 使用日志
    example_with_tracing().await?;

    // 优雅关闭
    logger_provider.shutdown()?;

    Ok(())
}
```

### 类型安全的日志结构

```rust
use serde::{Deserialize, Serialize};
use opentelemetry::logs::{Logger, LogRecord, Severity};

/// 结构化日志事件
#[derive(Debug, Serialize, Deserialize)]
pub struct StructuredLogEvent {
    pub level: LogLevel,
    pub message: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub service: String,
    pub trace_id: Option<String>,
    pub span_id: Option<String>,
    #[serde(flatten)]
    pub attributes: std::collections::HashMap<String, serde_json::Value>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

impl From<LogLevel> for Severity {
    fn from(level: LogLevel) -> Self {
        match level {
            LogLevel::Trace => Severity::Trace,
            LogLevel::Debug => Severity::Debug,
            LogLevel::Info => Severity::Info,
            LogLevel::Warn => Severity::Warn,
            LogLevel::Error => Severity::Error,
            LogLevel::Fatal => Severity::Fatal,
        }
    }
}

/// 发送结构化日志
pub fn emit_structured_log(
    logger: &dyn Logger,
    event: StructuredLogEvent,
) {
    let mut log_record = LogRecord::default();
    log_record.set_severity(event.level.into());
    log_record.set_body(event.message.into());
    log_record.set_timestamp(
        chrono::Utc::now().timestamp_nanos_opt().unwrap_or(0) as u64
    );

    // 添加属性
    for (key, value) in event.attributes {
        log_record.add_attribute(KeyValue::new(key, value.to_string()));
    }

    logger.emit(log_record);
}
```

---

## 🚀 ARMS应用监控集成

### Trace集成

```rust
use opentelemetry::{global, trace::{Tracer, Span, SpanKind, Status}};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_sdk::{
    trace::{self as sdktrace, Sampler, TracerProvider},
    resource::Resource,
    runtime,
};
use std::time::Duration;

/// 阿里云ARMS配置
#[derive(Debug, Clone)]
pub struct AliyunArmsConfig {
    /// ARMS接入点
    pub endpoint: String,
    /// ARMS Token
    pub token: String,
    /// Region
    pub region: String,
}

/// 初始化ARMS Tracer
pub async fn init_aliyun_arms_tracer(
    config: AliyunArmsConfig,
) -> anyhow::Result<TracerProvider> {
    // 创建Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("cloud.provider", "alibaba_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
    ]);

    // 创建metadata
    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "Authentication",
        config.token.parse().unwrap(),
    );

    // 创建OTLP Span Exporter
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(30))
        .with_compression(tonic::codec::CompressionEncoding::Gzip)
        .with_metadata(metadata)
        .build()?;

    // 创建Sampler (智能采样)
    let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));

    // 创建TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(
            sdktrace::Config::default()
                .with_sampler(sampler)
                .with_resource(resource)
        )
        .with_batch_exporter(
            exporter,
            runtime::Tokio,
        )
        .build();

    global::set_tracer_provider(tracer_provider.clone());

    Ok(tracer_provider)
}

/// 带Trace的HTTP请求示例
use axum::{
    Router,
    routing::get,
    extract::State,
    response::Json,
};
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

async fn health_check(
    State(state): State<AppState>,
) -> Json<serde_json::Value> {
    let tracer = &state.tracer;
    
    let mut span = tracer.start("health_check");
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.route", "/health"));
    
    // 业务逻辑
    let result = check_dependencies().await;
    
    match result {
        Ok(_) => {
            span.set_status(Status::Ok);
            span.set_attribute(KeyValue::new("health.status", "healthy"));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("health.status", "unhealthy"));
        }
    }
    
    span.end();
    
    Json(serde_json::json!({
        "status": "ok",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

async fn check_dependencies() -> anyhow::Result<()> {
    // 检查数据库、缓存等依赖
    tokio::time::sleep(Duration::from_millis(10)).await;
    Ok(())
}

/// 数据库查询追踪
use sqlx::{PgPool, Row};

#[instrument(skip(pool))]
pub async fn query_users_with_trace(
    pool: &PgPool,
    tracer: &dyn Tracer,
) -> anyhow::Result<Vec<String>> {
    let mut span = tracer.start_with_context(
        "db.query",
        &opentelemetry::Context::current(),
    );
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    span.set_attribute(KeyValue::new("db.sql.table", "users"));
    
    let result = sqlx::query("SELECT name FROM users LIMIT 10")
        .fetch_all(pool)
        .await;
    
    match &result {
        Ok(rows) => {
            span.set_attribute(KeyValue::new("db.rows_affected", rows.len() as i64));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    span.end();
    
    result
        .map(|rows| rows.iter().map(|r| r.get(0)).collect())
        .map_err(Into::into)
}
```

### 分布式追踪Context传播

```rust
use opentelemetry::{
    global,
    propagation::{Extractor, Injector, TextMapPropagator},
    trace::{TraceContextExt, TraceId, SpanId},
    Context,
};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use std::collections::HashMap;

/// HTTP Headers适配器
struct HeaderExtractor<'a>(&'a axum::http::HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

struct HeaderInjector<'a>(&'a mut reqwest::header::HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(header_value) = reqwest::header::HeaderValue::from_str(&value) {
            self.0.insert(
                reqwest::header::HeaderName::from_bytes(key.as_bytes()).unwrap(),
                header_value,
            );
        }
    }
}

/// 从HTTP请求中提取Context
pub fn extract_context_from_request(
    headers: &axum::http::HeaderMap,
) -> Context {
    let propagator = TraceContextPropagator::new();
    let extractor = HeaderExtractor(headers);
    propagator.extract(&extractor)
}

/// 将Context注入到HTTP请求中
pub fn inject_context_into_request(
    context: &Context,
    headers: &mut reqwest::header::HeaderMap,
) {
    let propagator = TraceContextPropagator::new();
    let mut injector = HeaderInjector(headers);
    propagator.inject_context(context, &mut injector);
}

/// 跨服务调用示例
pub async fn call_downstream_service(
    client: &reqwest::Client,
    url: &str,
    tracer: &dyn Tracer,
) -> anyhow::Result<String> {
    let mut span = tracer.start("http.client.request");
    span.set_attribute(KeyValue::new("http.url", url.to_string()));
    span.set_attribute(KeyValue::new("http.method", "GET"));
    
    let context = Context::current_with_span(span.clone());
    
    let mut headers = reqwest::header::HeaderMap::new();
    inject_context_into_request(&context, &mut headers);
    
    let response = client
        .get(url)
        .headers(headers)
        .send()
        .await?;
    
    let status = response.status();
    span.set_attribute(KeyValue::new("http.status_code", status.as_u16() as i64));
    
    if status.is_success() {
        span.set_status(Status::Ok);
    } else {
        span.set_status(Status::error(format!("HTTP {}", status)));
    }
    
    let body = response.text().await?;
    span.end();
    
    Ok(body)
}
```

---

## 📈 Prometheus监控集成

### Metrics集成

```rust
use opentelemetry::{global, metrics::{Counter, Histogram, Meter}};
use opentelemetry_otlp::{MetricsExporter, WithExportConfig};
use opentelemetry_sdk::{
    metrics::{self as sdkmetrics, MeterProvider, PeriodicReader},
    resource::Resource,
    runtime,
};
use std::time::Duration;

/// Prometheus Remote Write配置
#[derive(Debug, Clone)]
pub struct PrometheusConfig {
    pub endpoint: String,
    pub token: String,
    pub region: String,
}

/// 初始化Prometheus MeterProvider
pub async fn init_prometheus_meter(
    config: PrometheusConfig,
) -> anyhow::Result<MeterProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
    ]);

    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "Authorization",
        format!("Bearer {}", config.token).parse().unwrap(),
    );

    let exporter = MetricsExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(30))
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

/// 业务指标定义
pub struct BusinessMetrics {
    pub http_requests_total: Counter<u64>,
    pub http_request_duration: Histogram<f64>,
    pub active_connections: Counter<i64>,
    pub cache_hits: Counter<u64>,
    pub cache_misses: Counter<u64>,
}

impl BusinessMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            http_requests_total: meter
                .u64_counter("http_requests_total")
                .with_description("Total HTTP requests")
                .init(),
            
            http_request_duration: meter
                .f64_histogram("http_request_duration_seconds")
                .with_description("HTTP request duration in seconds")
                .with_unit("s")
                .init(),
            
            active_connections: meter
                .i64_up_down_counter("active_connections")
                .with_description("Current active connections")
                .init(),
            
            cache_hits: meter
                .u64_counter("cache_hits_total")
                .with_description("Total cache hits")
                .init(),
            
            cache_misses: meter
                .u64_counter("cache_misses_total")
                .with_description("Total cache misses")
                .init(),
        }
    }
}

/// HTTP服务器with指标
use axum::{
    middleware::{self, Next},
    response::Response,
    body::Body,
};
use std::time::Instant;

pub async fn metrics_middleware(
    req: axum::extract::Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let uri = req.uri().clone();
    
    let response = next.run(req).await;
    
    let duration = start.elapsed();
    let status = response.status();
    
    // 记录指标
    let meter = global::meter("http_server");
    let metrics = BusinessMetrics::new(&meter);
    
    metrics.http_requests_total.add(
        1,
        &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("route", uri.path().to_string()),
            KeyValue::new("status", status.as_u16() as i64),
        ],
    );
    
    metrics.http_request_duration.record(
        duration.as_secs_f64(),
        &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("route", uri.path().to_string()),
        ],
    );
    
    response
}
```

---

## 🏗️ 完整示例

### 生产级微服务示例

```rust
use axum::{Router, routing::get};
use std::sync::Arc;
use tokio::signal;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 加载环境变量
    dotenvy::dotenv().ok();
    
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .json()
        .init();
    
    // 初始化OpenTelemetry
    let arms_config = AliyunArmsConfig {
        endpoint: std::env::var("ARMS_ENDPOINT")
            .unwrap_or_else(|_| "tracing-analysis-dc-hz.aliyuncs.com:8090".to_string()),
        token: std::env::var("ARMS_TOKEN")?,
        region: "cn-hangzhou".to_string(),
    };
    
    let tracer_provider = init_aliyun_arms_tracer(arms_config).await?;
    let tracer = global::tracer("my-rust-service");
    
    let prometheus_config = PrometheusConfig {
        endpoint: std::env::var("PROMETHEUS_ENDPOINT")?,
        token: std::env::var("PROMETHEUS_TOKEN")?,
        region: "cn-hangzhou".to_string(),
    };
    
    let meter_provider = init_prometheus_meter(prometheus_config).await?;
    
    // 构建路由
    let app_state = AppState {
        tracer: Arc::new(tracer),
    };
    
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/metrics", get(metrics_handler))
        .layer(middleware::from_fn(metrics_middleware))
        .with_state(app_state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    tracing::info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await?;
    
    // 优雅关闭
    tracer_provider.shutdown()?;
    meter_provider.shutdown()?;
    
    Ok(())
}

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    tracing::info!("Signal received, starting graceful shutdown");
}

async fn metrics_handler() -> String {
    // 导出Prometheus格式指标
    "# Metrics placeholder\n".to_string()
}
```

---

## 💡 最佳实践

### 1. 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ObservabilityError {
    #[error("Failed to initialize tracer: {0}")]
    TracerInit(#[from] opentelemetry::trace::TraceError),
    
    #[error("Failed to initialize logger: {0}")]
    LoggerInit(#[from] opentelemetry::logs::LogError),
    
    #[error("Failed to initialize meter: {0}")]
    MeterInit(#[from] opentelemetry::metrics::MetricsError),
    
    #[error("Aliyun authentication failed: {0}")]
    AuthenticationFailed(String),
    
    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),
}

pub type Result<T> = std::result::Result<T, ObservabilityError>;
```

### 2. 资源管理

```rust
pub struct ObservabilityStack {
    tracer_provider: Option<TracerProvider>,
    logger_provider: Option<LoggerProvider>,
    meter_provider: Option<MeterProvider>,
}

impl ObservabilityStack {
    pub async fn new() -> Result<Self> {
        Ok(Self {
            tracer_provider: None,
            logger_provider: None,
            meter_provider: None,
        })
    }
    
    pub async fn shutdown(self) -> Result<()> {
        if let Some(tp) = self.tracer_provider {
            tp.shutdown()?;
        }
        if let Some(lp) = self.logger_provider {
            lp.shutdown()?;
        }
        if let Some(mp) = self.meter_provider {
            mp.shutdown()?;
        }
        Ok(())
    }
}
```

### 3. 性能优化

```rust
// 批量导出配置
const BATCH_SIZE: usize = 1024;
const BATCH_TIMEOUT_MS: u64 = 5000;

pub fn optimized_batch_config() -> sdktrace::Config {
    sdktrace::Config::default()
        .with_max_export_batch_size(BATCH_SIZE)
        .with_max_queue_size(BATCH_SIZE * 4)
        .with_scheduled_delay(Duration::from_millis(BATCH_TIMEOUT_MS))
}
```

---

## 🔍 故障排查

### 诊断工具

```rust
pub async fn diagnose_aliyun_connection(
    config: &AliyunArmsConfig,
) -> anyhow::Result<()> {
    println!("🔍 Diagnosing Aliyun ARMS connection...\n");
    
    // 1. 检查网络连接
    println!("1️⃣ Testing network connectivity...");
    let client = reqwest::Client::new();
    match client.get(&config.endpoint).send().await {
        Ok(resp) => println!("   ✅ Network OK (status: {})", resp.status()),
        Err(e) => println!("   ❌ Network failed: {}", e),
    }
    
    // 2. 检查认证
    println!("\n2️⃣ Testing authentication...");
    if config.token.is_empty() {
        println!("   ❌ Token is empty!");
    } else {
        println!("   ✅ Token is set (length: {})", config.token.len());
    }
    
    // 3. 测试OTLP导出
    println!("\n3️⃣ Testing OTLP export...");
    // 实际测试代码
    
    Ok(())
}
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **OpenTelemetry Rust** | <https://github.com/open-telemetry/opentelemetry-rust> |
| **阿里云SLS** | <https://help.aliyun.com/product/28958.html> |
| **ARMS文档** | <https://help.aliyun.com/product/34364.html> |
| **Rust 1.90发布说明** | <https://blog.rust-lang.org/2024/11/28/Rust-1.90.0.html> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**下一篇**: [腾讯云OTLP集成指南_Rust完整版](./02_腾讯云OTLP集成指南_Rust完整版.md)
