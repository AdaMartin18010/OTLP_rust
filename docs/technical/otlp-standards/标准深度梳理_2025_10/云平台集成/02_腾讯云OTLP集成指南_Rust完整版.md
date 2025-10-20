# 🦀 腾讯云OpenTelemetry集成指南 - Rust 1.90完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **腾讯云服务**: CLS, APM, TMP  
> **最后更新**: 2025年10月11日

---

## 📦 依赖配置

```toml
[package]
name = "tencentcloud-otlp-rust"
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

# 序列化与编码
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
prost = "0.13"

# HTTP/gRPC
reqwest = { version = "0.12.9", features = ["json", "gzip"] }
hyper = { version = "1.5", features = ["full"] }

# 日志与Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt", "json"] }
tracing-opentelemetry = "0.31.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 工具
chrono = "0.4"
uuid = { version = "1.11", features = ["v4"] }
base64 = "0.22"
hmac = "0.12"
sha2 = "0.10"
```

---

## 📊 CLS日志服务集成

### Kafka协议集成

```rust
use opentelemetry::{global, logs::LogResult, KeyValue};
use opentelemetry_otlp::LogExporter;
use opentelemetry_sdk::{
    logs::{LoggerProvider, BatchLogProcessor},
    resource::Resource,
    runtime,
};
use std::time::Duration;

/// 腾讯云CLS配置
#[derive(Debug, Clone)]
pub struct TencentClsConfig {
    /// CLS Kafka Endpoint
    pub kafka_endpoint: String,
    /// 日志主题ID
    pub topic_id: String,
    /// SecretId
    pub secret_id: String,
    /// SecretKey
    pub secret_key: String,
    /// Region
    pub region: String,
}

/// 初始化腾讯云CLS日志提供者
pub async fn init_tencent_cls_logger(
    config: TencentClsConfig,
) -> anyhow::Result<LoggerProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "tencent_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
        KeyValue::new("cloud.platform", "tencent_cloud_cls"),
    ]);

    // 创建Kafka exporter配置
    let kafka_config = create_kafka_config(&config)?;
    
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint(&config.kafka_endpoint)
        .with_timeout(Duration::from_secs(30))
        .build()?;

    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter, runtime::Tokio)
        .build();

    global::set_logger_provider(logger_provider.clone());

    Ok(logger_provider)
}

fn create_kafka_config(config: &TencentClsConfig) -> anyhow::Result<String> {
    // 腾讯云CLS Kafka认证配置
    Ok(format!(
        "sasl.mechanism=PLAIN\n\
         sasl.username={}\n\
         sasl.password={}\n\
         security.protocol=SASL_SSL",
        config.secret_id,
        config.secret_key
    ))
}

/// 结构化日志示例
use tracing::{info, warn, error, instrument};

#[instrument(
    name = "process_order",
    skip(order_data),
    fields(
        order.id = %order_data.id,
        order.amount = order_data.amount,
        user.id = order_data.user_id
    )
)]
pub async fn process_order_with_logging(
    order_data: OrderData,
) -> anyhow::Result<()> {
    info!(
        order_id = %order_data.id,
        "Starting order processing"
    );

    // 业务逻辑
    match validate_order(&order_data).await {
        Ok(_) => {
            info!("Order validated successfully");
        }
        Err(e) => {
            error!(error = %e, "Order validation failed");
            return Err(e);
        }
    }

    info!(
        processing_time_ms = 150,
        "Order processed successfully"
    );

    Ok(())
}

#[derive(Debug)]
struct OrderData {
    id: String,
    user_id: String,
    amount: f64,
}

async fn validate_order(order: &OrderData) -> anyhow::Result<()> {
    // 验证逻辑
    Ok(())
}
```

---

## 🚀 APM应用性能监控集成

### Trace集成

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, TraceContextExt},
    Context, KeyValue,
};
use opentelemetry_otlp::SpanExporter;
use opentelemetry_sdk::{
    trace::{Config, Sampler, TracerProvider},
    resource::Resource,
    runtime,
};

/// 腾讯云APM配置
#[derive(Debug, Clone)]
pub struct TencentApmConfig {
    /// APM接入点
    pub endpoint: String,
    /// APM Token
    pub token: String,
    /// Region
    pub region: String,
}

/// 初始化腾讯云APM Tracer
pub async fn init_tencent_apm_tracer(
    config: TencentApmConfig,
) -> anyhow::Result<TracerProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "tencent_cloud"),
        KeyValue::new("cloud.region", config.region.clone()),
    ]);

    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "authorization",
        format!("Bearer {}", config.token).parse()?,
    );

    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(30))
        .with_compression(tonic::codec::CompressionEncoding::Gzip)
        .with_metadata(metadata)
        .build()?;

    // 智能采样策略
    let sampler = Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10%采样率
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

/// HTTP服务器with Trace
use axum::{
    Router,
    routing::get,
    extract::{Path, State},
    response::{Json, IntoResponse},
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
) -> impl IntoResponse {
    let tracer = &state.tracer;
    let method = req.method().clone();
    let uri = req.uri().clone();

    let mut span = tracer
        .span_builder(format!("{} {}", method, uri.path()))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.url", uri.to_string()),
            KeyValue::new("http.scheme", "http"),
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
        span.set_status(Status::error(format!(
            "HTTP {}",
            response.status()
        )));
    }

    span.end();

    response
}

async fn get_user(
    Path(user_id): Path<String>,
    State(state): State<AppState>,
) -> Json<serde_json::Value> {
    let tracer = &state.tracer;
    
    let mut span = tracer
        .span_builder("get_user")
        .with_attributes(vec![
            KeyValue::new("user.id", user_id.clone()),
        ])
        .start(tracer);

    // 模拟数据库查询
    let user_data = fetch_user_from_db(&user_id, tracer).await;

    span.end();

    Json(serde_json::json!({
        "user_id": user_id,
        "name": "John Doe"
    }))
}

async fn fetch_user_from_db(
    user_id: &str,
    tracer: &dyn Tracer,
) -> Option<String> {
    let mut span = tracer
        .span_builder("db.query")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.operation", "SELECT"),
            KeyValue::new("db.sql.table", "users"),
        ])
        .start(tracer);

    // 模拟数据库查询
    tokio::time::sleep(Duration::from_millis(10)).await;

    span.set_attribute(KeyValue::new("db.rows_affected", 1));
    span.set_status(Status::Ok);
    span.end();

    Some(user_id.to_string())
}
```

---

## 📈 TMP云原生监控集成

### Metrics集成

```rust
use opentelemetry::{
    global,
    metrics::{Counter, Histogram, Meter, ObservableGauge},
};
use opentelemetry_otlp::MetricsExporter;
use opentelemetry_sdk::{
    metrics::{MeterProvider, PeriodicReader},
    resource::Resource,
    runtime,
};

/// TMP配置
#[derive(Debug, Clone)]
pub struct TmpConfig {
    pub endpoint: String,
    pub token: String,
    pub region: String,
}

/// 初始化TMP MeterProvider
pub async fn init_tmp_meter(
    config: TmpConfig,
) -> anyhow::Result<MeterProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("cloud.provider", "tencent_cloud"),
    ]);

    let mut metadata = tonic::metadata::MetadataMap::new();
    metadata.insert(
        "authorization",
        format!("Bearer {}", config.token).parse()?,
    );
    metadata.insert(
        "x-prometheus-remote-write-version",
        "0.1.0".parse()?,
    );

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

/// 业务指标定义
pub struct ServiceMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    active_requests: Counter<i64>,
    error_total: Counter<u64>,
}

impl ServiceMetrics {
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

            active_requests: meter
                .i64_up_down_counter("http_requests_active")
                .with_description("Currently active HTTP requests")
                .init(),

            error_total: meter
                .u64_counter("http_errors_total")
                .with_description("Total HTTP errors")
                .init(),
        }
    }

    pub fn record_request(
        &self,
        method: &str,
        status: u16,
        duration: Duration,
    ) {
        let labels = &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("status", status as i64),
        ];

        self.requests_total.add(1, labels);
        self.request_duration.record(duration.as_secs_f64(), labels);

        if status >= 400 {
            self.error_total.add(1, labels);
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
    // 加载环境变量
    dotenvy::dotenv().ok();

    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .json()
        .init();

    // 初始化OpenTelemetry
    let cls_config = TencentClsConfig {
        kafka_endpoint: std::env::var("CLS_KAFKA_ENDPOINT")?,
        topic_id: std::env::var("CLS_TOPIC_ID")?,
        secret_id: std::env::var("TENCENT_SECRET_ID")?,
        secret_key: std::env::var("TENCENT_SECRET_KEY")?,
        region: "ap-guangzhou".to_string(),
    };

    let logger_provider = init_tencent_cls_logger(cls_config).await?;

    let apm_config = TencentApmConfig {
        endpoint: "apm.tencentcs.com:4317".to_string(),
        token: std::env::var("TENCENT_APM_TOKEN")?,
        region: "ap-guangzhou".to_string(),
    };

    let tracer_provider = init_tencent_apm_tracer(apm_config).await?;
    let tracer = global::tracer("my-service");

    let tmp_config = TmpConfig {
        endpoint: std::env::var("TMP_ENDPOINT")?,
        token: std::env::var("TMP_TOKEN")?,
        region: "ap-guangzhou".to_string(),
    };

    let meter_provider = init_tmp_meter(tmp_config).await?;

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
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    tokio::select! {
        _ = ctrl_c => {},
    }

    tracing::info!("Shutdown signal received");
}

async fn health_check() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}
```

---

## 💡 最佳实践

### 1. 成本优化

```rust
/// 智能采样配置
pub fn create_cost_optimized_sampler() -> Sampler {
    use opentelemetry_sdk::trace::Sampler;

    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10%基础采样
    ))
}

/// Tail采样配置 (保留所有错误)
pub struct TailSamplingConfig {
    pub error_sampling_rate: f64,    // 1.0 = 100%错误
    pub normal_sampling_rate: f64,   // 0.1 = 10%正常
    pub slow_request_threshold_ms: u64, // 慢请求阈值
}
```

### 2. 错误处理

```rust
#[derive(thiserror::Error, Debug)]
pub enum TencentCloudError {
    #[error("CLS Kafka connection failed: {0}")]
    ClsConnectionFailed(String),
    
    #[error("APM authentication failed: {0}")]
    ApmAuthFailed(String),
    
    #[error("TMP remote write failed: {0}")]
    TmpWriteFailed(String),
    
    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),
}
```

### 3. 性能监控

```rust
/// 自动性能监控
pub async fn monitor_performance<F, T>(
    operation_name: &str,
    tracer: &dyn Tracer,
    f: F,
) -> anyhow::Result<T>
where
    F: std::future::Future<Output = anyhow::Result<T>>,
{
    let start = std::time::Instant::now();
    let mut span = tracer.start(operation_name);

    let result = f.await;

    let duration = start.elapsed();
    span.set_attribute(KeyValue::new(
        "duration_ms",
        duration.as_millis() as i64
    ));

    match &result {
        Ok(_) => span.set_status(Status::Ok),
        Err(e) => span.set_status(Status::error(e.to_string())),
    }

    span.end();
    result
}
```

---

## 🔍 故障排查

### 诊断工具

```rust
pub async fn diagnose_tencent_cloud() -> anyhow::Result<()> {
    println!("🔍 Diagnosing Tencent Cloud integration...\n");

    // 1. 测试CLS连接
    println!("1️⃣ Testing CLS Kafka connection...");
    // 实际测试代码

    // 2. 测试APM连接
    println!("\n2️⃣ Testing APM connection...");
    // 实际测试代码

    // 3. 测试TMP连接
    println!("\n3️⃣ Testing TMP connection...");
    // 实际测试代码

    Ok(())
}
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **OpenTelemetry Rust** | <https://github.com/open-telemetry/opentelemetry-rust> |
| **腾讯云CLS** | <https://cloud.tencent.com/document/product/614> |
| **APM文档** | <https://cloud.tencent.com/document/product/1463> |
| **TMP文档** | <https://cloud.tencent.com/document/product/1416> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [阿里云OTLP集成指南_Rust完整版](./01_阿里云OTLP集成指南_Rust完整版.md)  
**下一篇**: [华为云OTLP集成指南_Rust完整版](./03_华为云OTLP集成指南_Rust完整版.md)
