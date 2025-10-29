# 监控和可观测性完整指南

**Crate:** c11_libraries  
**主题:** Observability & Monitoring  
**Rust 版本:** 1.90.0  
**最后更新:** 2025年10月28日

---

## 📋 目录

- [监控和可观测性完整指南](#监控和可观测性完整指南)
  - [📋 目录](#-目录)
  - [🎯 监控和可观测性概述](#-监控和可观测性概述)
    - [可观测性三大支柱](#可观测性三大支柱)
    - [OpenTelemetry 架构](#opentelemetry-架构)
  - [📝 日志（Logging）](#日志logging)
    - [1. 结构化日志](#1-结构化日志)
    - [2. 日志级别管理](#2-日志级别管理)
    - [3. 日志聚合和搜索](#3-日志聚合和搜索)
  - [📊 指标（Metrics）](#指标metrics)
    - [1. Prometheus 集成](#1-prometheus-集成)
    - [2. 自定义指标](#2-自定义指标)
    - [3. 暴露 Metrics 端点](#3-暴露-metrics-端点)
  - [🔍 分布式追踪（Tracing）](#分布式追踪tracing)
    - [1. OpenTelemetry Tracing](#1-opentelemetry-tracing)
    - [2. 跨服务追踪](#2-跨服务追踪)
    - [3. Jaeger 可视化](#3-jaeger-可视化)
  - [❤️ 健康检查](#健康检查)
    - [1. 基本健康检查](#1-基本健康检查)
    - [2. 存活探针和就绪探针](#2-存活探针和就绪探针)
  - [🚨 告警策略](#告警策略)
    - [1. Prometheus 告警规则](#1-prometheus-告警规则)
    - [2. 告警通知](#2-告警通知)
  - [⚡ 性能剖析](#性能剖析)
    - [1. CPU Profiling](#1-cpu-profiling)
    - [2. 内存Profiling](#2-内存profiling)
  - [💡 综合实践](#综合实践)
    - [完整的可观测性栈](#完整的可观测性栈)
    - [监控仪表板](#监控仪表板)
  - [📚 总结](#-总结)
    - [可观测性清单](#可观测性清单)
    - [最佳实践](#最佳实践)

---

## 🎯 监控和可观测性概述

### 可观测性三大支柱

```text
┌────────────────────────────────────────┐
│         可观测性 (Observability)        │
├────────────┬──────────────┬────────────┤
│   日志     │    指标       │    追踪    │
│  (Logs)    │  (Metrics)   │  (Traces)  │
├────────────┼──────────────┼────────────┤
│ 离散事件    │  聚合数值    │  请求路径   │
│ 文本描述    │  时间序列    │  调用链     │
│ 故障排查    │  趋势分析    │  性能分析   │
└────────────┴──────────────┴────────────┘
```

### OpenTelemetry 架构

```rust
use opentelemetry::{global, sdk::Resource, KeyValue};
use opentelemetry_otlp::WithExportConfig;

pub async fn init_observability() -> Result<()> {
    // 1. 初始化追踪
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            opentelemetry::sdk::trace::config().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "my-service"),
                KeyValue::new("service.version", "1.0.0"),
            ]))
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer);
    
    // 2. 初始化指标
    let meter = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry::runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .build()?;
    
    global::set_meter_provider(meter);
    
    Ok(())
}
```

---

## 日志（Logging）

### 1. 结构化日志

#### 使用 tracing

```rust
use tracing::{info, warn, error, debug, trace};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_logging() {
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| {
            "my_app=debug,tower_http=debug,sqlx=warn".into()
        }))
        .with(tracing_subscriber::fmt::layer().json())  // JSON 格式
        .init();
}

// 使用示例
#[tracing::instrument(
    name = "process_order",
    skip(order),
    fields(
        order.id = %order.id,
        order.user_id = %order.user_id,
        order.amount = %order.amount
    )
)]
pub async fn process_order(order: Order) -> Result<()> {
    info!("Processing order");
    
    // 自动添加 span 上下文
    debug!(items_count = order.items.len(), "Order details");
    
    match validate_order(&order).await {
        Ok(_) => info!("Order validated"),
        Err(e) => {
            error!(error = ?e, "Order validation failed");
            return Err(e);
        }
    }
    
    info!("Order processed successfully");
    Ok(())
}
```

#### 输出示例

```json
{
  "timestamp": "2025-10-28T10:30:45.123Z",
  "level": "INFO",
  "target": "my_app::orders",
  "span": {
    "name": "process_order",
    "order.id": "12345",
    "order.user_id": "user_789",
    "order.amount": "99.99"
  },
  "fields": {
    "message": "Processing order"
  }
}
```

---

### 2. 日志级别管理

#### 动态日志级别

```rust
use tracing_subscriber::reload;
use std::sync::Arc;

pub struct LogLevelManager {
    handle: reload::Handle<EnvFilter, tracing_subscriber::Registry>,
}

impl LogLevelManager {
    pub fn new() -> (Self, impl tracing::Subscriber) {
        let filter = EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| "info".into());
        
        let (filter, handle) = reload::Layer::new(filter);
        
        let subscriber = tracing_subscriber::registry()
            .with(filter)
            .with(tracing_subscriber::fmt::layer());
        
        (Self { handle }, subscriber)
    }
    
    pub fn set_level(&self, level: &str) -> Result<()> {
        let new_filter = EnvFilter::try_new(level)?;
        self.handle.reload(new_filter)?;
        Ok(())
    }
}

// HTTP 端点控制日志级别
async fn set_log_level_handler(
    State(manager): State<Arc<LogLevelManager>>,
    Json(request): Json<SetLogLevelRequest>,
) -> Result<Json<()>> {
    manager.set_level(&request.level)?;
    Ok(Json(()))
}
```

---

### 3. 日志聚合和搜索

#### ELK Stack 集成

```rust
use serde_json::json;
use reqwest::Client;

pub struct ElasticsearchLogger {
    client: Client,
    endpoint: String,
    index: String,
}

impl ElasticsearchLogger {
    pub async fn log_event(&self, event: LogEvent) -> Result<()> {
        let doc = json!({
            "@timestamp": event.timestamp,
            "level": event.level,
            "message": event.message,
            "service": event.service,
            "trace_id": event.trace_id,
            "span_id": event.span_id,
            "fields": event.fields,
        });
        
        let url = format!("{}/_doc", self.endpoint);
        self.client.post(&url)
            .json(&doc)
            .send()
            .await?;
        
        Ok(())
    }
}

// 与 tracing 集成
use tracing_subscriber::Layer;

pub struct ElasticsearchLayer {
    logger: Arc<ElasticsearchLogger>,
}

impl<S> Layer<S> for ElasticsearchLayer
where
    S: tracing::Subscriber,
{
    fn on_event(
        &self,
        event: &tracing::Event<'_>,
        _ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        // 提取事件信息并发送到 Elasticsearch
        let log_event = extract_log_event(event);
        tokio::spawn(async move {
            self.logger.log_event(log_event).await.ok();
        });
    }
}
```

---

## 指标（Metrics）

### 1. Prometheus 集成

#### 基本指标类型

```rust
use prometheus::{
    Counter, Histogram, Gauge, IntCounter, IntGauge,
    Opts, Registry, HistogramOpts,
};
use lazy_static::lazy_static;

lazy_static! {
    // Counter: 只增不减的计数器
    static ref HTTP_REQUESTS_TOTAL: IntCounter = IntCounter::new(
        "http_requests_total",
        "Total number of HTTP requests"
    ).unwrap();
    
    // Gauge: 可增可减的仪表
    static ref ACTIVE_CONNECTIONS: IntGauge = IntGauge::new(
        "active_connections",
        "Number of active connections"
    ).unwrap();
    
    // Histogram: 直方图（用于响应时间等）
    static ref HTTP_REQUEST_DURATION: Histogram = Histogram::with_opts(
        HistogramOpts::new(
            "http_request_duration_seconds",
            "HTTP request duration in seconds"
        )
        .buckets(vec![0.001, 0.01, 0.1, 0.5, 1.0, 5.0, 10.0])
    ).unwrap();
}

pub fn register_metrics(registry: &Registry) -> Result<()> {
    registry.register(Box::new(HTTP_REQUESTS_TOTAL.clone()))?;
    registry.register(Box::new(ACTIVE_CONNECTIONS.clone()))?;
    registry.register(Box::new(HTTP_REQUEST_DURATION.clone()))?;
    Ok(())
}

// 使用示例
pub async fn handle_request() -> Result<Response> {
    // 增加请求计数
    HTTP_REQUESTS_TOTAL.inc();
    
    // 增加活跃连接
    ACTIVE_CONNECTIONS.inc();
    
    // 记录响应时间
    let timer = HTTP_REQUEST_DURATION.start_timer();
    
    let response = process_request().await;
    
    timer.observe_duration();
    
    // 减少活跃连接
    ACTIVE_CONNECTIONS.dec();
    
    response
}
```

---

### 2. 自定义指标

#### 业务指标

```rust
use prometheus::{IntCounterVec, HistogramVec, GaugeVec, Opts};

lazy_static! {
    // 按状态码分组的请求计数
    static ref HTTP_REQUESTS_BY_STATUS: IntCounterVec = IntCounterVec::new(
        Opts::new("http_requests_by_status", "HTTP requests by status code"),
        &["method", "endpoint", "status"]
    ).unwrap();
    
    // 按端点分组的响应时间
    static ref ENDPOINT_DURATION: HistogramVec = HistogramVec::new(
        HistogramOpts::new(
            "endpoint_duration_seconds",
            "Endpoint duration in seconds"
        ),
        &["method", "endpoint"]
    ).unwrap();
    
    // 订单金额
    static ref ORDER_AMOUNT: GaugeVec = GaugeVec::new(
        Opts::new("order_amount_total", "Total order amount"),
        &["status"]
    ).unwrap();
}

// 中间件记录指标
pub async fn metrics_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let method = req.method().clone();
    let path = req.uri().path().to_string();
    
    let timer = ENDPOINT_DURATION
        .with_label_values(&[method.as_str(), &path])
        .start_timer();
    
    let response = next.run(req).await;
    
    timer.observe_duration();
    
    HTTP_REQUESTS_BY_STATUS
        .with_label_values(&[
            method.as_str(),
            &path,
            response.status().as_str(),
        ])
        .inc();
    
    response
}
```

---

### 3. 暴露 Metrics 端点

#### Axum 集成

```rust
use axum::{Router, routing::get};
use prometheus::{Encoder, TextEncoder, Registry};

pub fn metrics_routes(registry: Arc<Registry>) -> Router {
    Router::new()
        .route("/metrics", get(metrics_handler))
        .with_state(registry)
}

async fn metrics_handler(
    State(registry): State<Arc<Registry>>,
) -> Result<String> {
    let encoder = TextEncoder::new();
    let metric_families = registry.gather();
    
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer)?;
    
    Ok(String::from_utf8(buffer)?)
}
```

#### Prometheus 输出示例

```text
# HELP http_requests_total Total number of HTTP requests
# TYPE http_requests_total counter
http_requests_total 12345

# HELP http_request_duration_seconds HTTP request duration in seconds
# TYPE http_request_duration_seconds histogram
http_request_duration_seconds_bucket{le="0.001"} 100
http_request_duration_seconds_bucket{le="0.01"} 500
http_request_duration_seconds_bucket{le="0.1"} 1000
http_request_duration_seconds_bucket{le="+Inf"} 1200
http_request_duration_seconds_sum 45.5
http_request_duration_seconds_count 1200

# HELP active_connections Number of active connections
# TYPE active_connections gauge
active_connections 42
```

---

## 分布式追踪（Tracing）

### 1. OpenTelemetry Tracing

#### 基本使用

```rust
use opentelemetry::{global, trace::{Tracer, SpanKind, Status}, KeyValue};
use tracing_opentelemetry::OpenTelemetryLayer;

#[tracing::instrument(
    name = "create_user",
    skip(pool),
    fields(
        user.email = %user_data.email,
        otel.kind = "server"
    )
)]
pub async fn create_user(
    pool: &PgPool,
    user_data: CreateUserRequest,
) -> Result<User> {
    let tracer = global::tracer("my-service");
    
    // 创建子 span
    let mut span = tracer
        .span_builder("validate_user")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    
    // 添加属性
    span.set_attribute(KeyValue::new("user.email", user_data.email.clone()));
    
    // 验证用户
    validate_user_data(&user_data).await?;
    
    span.end();
    
    // 另一个子 span
    let _db_span = tracer
        .span_builder("insert_user_db")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    let user = sqlx::query_as::<_, User>(
        "INSERT INTO users (email, name) VALUES ($1, $2) RETURNING *"
    )
    .bind(&user_data.email)
    .bind(&user_data.name)
    .fetch_one(pool)
    .await?;
    
    Ok(user)
}
```

---

### 2. 跨服务追踪

#### HTTP 请求传播

```rust
use opentelemetry::propagation::{Injector, Extractor};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

// 注入追踪上下文到 HTTP Headers
pub struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}

// 从 HTTP Headers 提取追踪上下文
pub struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

// 发送请求时注入上下文
pub async fn call_downstream_service(url: &str) -> Result<Response> {
    use opentelemetry::global;
    
    let client = reqwest::Client::new();
    let mut headers = HeaderMap::new();
    
    // 注入当前追踪上下文
    let propagator = global::get_text_map_propagator(|propagator| {
        propagator.inject(&mut HeaderInjector(&mut headers))
    });
    
    let response = client
        .get(url)
        .headers(headers)
        .send()
        .await?;
    
    Ok(response)
}

// 接收请求时提取上下文
pub async fn extract_trace_context(headers: &HeaderMap) -> Context {
    use opentelemetry::global;
    
    global::get_text_map_propagator(|propagator| {
        propagator.extract(&HeaderExtractor(headers))
    })
}
```

---

### 3. Jaeger 可视化

#### Jaeger 配置

```rust
use opentelemetry::sdk::trace::Sampler;
use opentelemetry_jaeger::config::agent::AgentPipeline;

pub fn init_jaeger_tracing() -> Result<()> {
    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("my-service")
        .with_endpoint("localhost:6831")
        .with_trace_config(
            opentelemetry::sdk::trace::config()
                .with_sampler(Sampler::AlwaysOn)  // 生产环境使用概率采样
                .with_max_events_per_span(64)
                .with_max_attributes_per_span(32)
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    opentelemetry::global::set_tracer_provider(tracer);
    
    Ok(())
}
```

#### Trace 示例

```tex
Trace ID: 1234567890abcdef
Span: create_order (12ms)
├─ Span: validate_order (2ms)
│  ├─ validate_user (1ms)
│  └─ validate_items (1ms)
├─ Span: calculate_total (1ms)
├─ Span: insert_order_db (5ms)
└─ Span: send_confirmation (4ms)
   └─ call_email_service (3ms)
```

---

## 健康检查

### 1. 基本健康检查

#### 实现

```rust
use axum::{Json, http::StatusCode};
use serde::{Serialize, Deserialize};

#[derive(Serialize)]
pub struct HealthResponse {
    status: HealthStatus,
    version: String,
    uptime_seconds: u64,
    checks: Vec<HealthCheck>,
}

#[derive(Serialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

#[derive(Serialize)]
pub struct HealthCheck {
    name: String,
    status: HealthStatus,
    message: Option<String>,
    latency_ms: Option<u64>,
}

pub async fn health_check_handler(
    State(state): State<Arc<AppState>>,
) -> (StatusCode, Json<HealthResponse>) {
    let start_time = state.start_time;
    let uptime = start_time.elapsed().as_secs();
    
    let mut checks = Vec::new();
    
    // 1. 数据库健康检查
    checks.push(check_database_health(&state.pool).await);
    
    // 2. Redis 健康检查
    checks.push(check_redis_health(&state.redis).await);
    
    // 3. 外部服务健康检查
    checks.push(check_external_services().await);
    
    // 确定整体状态
    let overall_status = determine_overall_status(&checks);
    
    let response = HealthResponse {
        status: overall_status.clone(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        uptime_seconds: uptime,
        checks,
    };
    
    let status_code = match overall_status {
        HealthStatus::Healthy => StatusCode::OK,
        HealthStatus::Degraded => StatusCode::OK,
        HealthStatus::Unhealthy => StatusCode::SERVICE_UNAVAILABLE,
    };
    
    (status_code, Json(response))
}

async fn check_database_health(pool: &PgPool) -> HealthCheck {
    let start = Instant::now();
    
    match sqlx::query("SELECT 1").fetch_one(pool).await {
        Ok(_) => HealthCheck {
            name: "database".to_string(),
            status: HealthStatus::Healthy,
            message: Some("Connected".to_string()),
            latency_ms: Some(start.elapsed().as_millis() as u64),
        },
        Err(e) => HealthCheck {
            name: "database".to_string(),
            status: HealthStatus::Unhealthy,
            message: Some(format!("Error: {}", e)),
            latency_ms: None,
        },
    }
}
```

---

### 2. 存活探针和就绪探针

#### Kubernetes 集成

```rust
// 存活探针：检查服务是否运行
pub async fn liveness_probe() -> StatusCode {
    // 简单检查：服务是否能响应
    StatusCode::OK
}

// 就绪探针：检查服务是否准备好接收流量
pub async fn readiness_probe(
    State(state): State<Arc<AppState>>,
) -> StatusCode {
    // 检查关键依赖
    if !state.is_ready() {
        return StatusCode::SERVICE_UNAVAILABLE;
    }
    
    // 检查数据库连接
    if sqlx::query("SELECT 1")
        .fetch_one(&state.pool)
        .await
        .is_err()
    {
        return StatusCode::SERVICE_UNAVAILABLE;
    }
    
    StatusCode::OK
}

// 启动探针：检查服务是否已完成启动
pub async fn startup_probe(
    State(state): State<Arc<AppState>>,
) -> StatusCode {
    if state.is_started() {
        StatusCode::OK
    } else {
        StatusCode::SERVICE_UNAVAILABLE
    }
}
```

#### Kubernetes 配置

```yaml
livenessProbe:
  httpGet:
    path: /health/live
    port: 8080
  initialDelaySeconds: 10
  periodSeconds: 10
  
readinessProbe:
  httpGet:
    path: /health/ready
    port: 8080
  initialDelaySeconds: 5
  periodSeconds: 5
  
startupProbe:
  httpGet:
    path: /health/startup
    port: 8080
  initialDelaySeconds: 0
  periodSeconds: 10
  failureThreshold: 30
```

---

## 告警策略

### 1. Prometheus 告警规则

#### 定义告警

```yaml
groups:
  - name: my_service_alerts
    interval: 30s
    rules:
      # 高错误率告警
      - alert: HighErrorRate
        expr: |
          rate(http_requests_total{status=~"5.."}[5m])
          / rate(http_requests_total[5m])
          > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }} for {{ $labels.endpoint }}"
      
      # 高响应时间告警
      - alert: HighLatency
        expr: |
          histogram_quantile(0.99, 
            rate(http_request_duration_seconds_bucket[5m])
          ) > 1.0
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "P99 latency is {{ $value }}s for {{ $labels.endpoint }}"
      
      # 数据库连接池耗尽
      - alert: DatabasePoolExhausted
        expr: |
          pg_pool_connections_active / pg_pool_connections_max > 0.9
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Database connection pool exhausted"
```

---

### 2. 告警通知

#### 集成 Alertmanager

```rust
use reqwest::Client;
use serde_json::json;

pub struct AlertManager {
    client: Client,
    endpoint: String,
}

impl AlertManager {
    pub async fn send_alert(&self, alert: Alert) -> Result<()> {
        let payload = json!([{
            "labels": alert.labels,
            "annotations": alert.annotations,
            "startsAt": alert.starts_at,
            "endsAt": alert.ends_at,
        }]);
        
        self.client
            .post(&format!("{}/api/v1/alerts", self.endpoint))
            .json(&payload)
            .send()
            .await?;
        
        Ok(())
    }
}

// 自定义告警逻辑
pub async fn check_and_alert(state: &AppState) -> Result<()> {
    // 检查错误率
    let error_rate = state.metrics.get_error_rate();
    if error_rate > 0.05 {
        state.alert_manager.send_alert(Alert {
            labels: hashmap!{
                "alertname" => "HighErrorRate",
                "severity" => "critical",
            },
            annotations: hashmap!{
                "summary" => format!("Error rate: {}%", error_rate * 100.0),
            },
            starts_at: Utc::now(),
            ends_at: None,
        }).await?;
    }
    
    Ok(())
}
```

---

## 性能剖析

### 1. CPU Profiling

#### 使用 pprof

```rust
use pprof::ProfilerGuard;

pub async fn profile_endpoint() -> Result<Vec<u8>> {
    let guard = ProfilerGuard::new(100)?;  // 100 Hz 采样
    
    // 运行需要分析的代码
    heavy_computation().await;
    
    // 生成报告
    let report = guard.report().build()?;
    
    // 生成 flamegraph
    let mut body = Vec::new();
    report.flamegraph(&mut body)?;
    
    Ok(body)
}

// HTTP 端点
async fn profile_handler() -> Response {
    let svg = profile_endpoint().await.unwrap();
    
    Response::builder()
        .header("Content-Type", "image/svg+xml")
        .body(Body::from(svg))
        .unwrap()
}
```

---

### 2. 内存Profiling

#### 使用 heaptrack

```rust
#[cfg(feature = "profiling")]
use jemalloc_ctl::{stats, epoch};

pub async fn memory_stats_handler() -> Json<MemoryStats> {
    epoch::mib().unwrap().advance().unwrap();
    
    let allocated = stats::allocated::mib().unwrap();
    let resident = stats::resident::mib().unwrap();
    
    Json(MemoryStats {
        allocated_bytes: allocated.read().unwrap(),
        resident_bytes: resident.read().unwrap(),
    })
}
```

---

## 综合实践

### 完整的可观测性栈

```rust
use axum::Router;
use tower_http::trace::TraceLayer;

pub async fn create_observable_server() -> Router {
    // 1. 初始化日志
    init_logging();
    
    // 2. 初始化追踪
    init_jaeger_tracing().unwrap();
    
    // 3. 初始化指标
    let registry = Arc::new(Registry::new());
    register_metrics(&registry).unwrap();
    
    // 4. 创建应用状态
    let state = Arc::new(AppState {
        pool: create_pool().await.unwrap(),
        registry: registry.clone(),
        start_time: Instant::now(),
    });
    
    // 5. 构建路由
    Router::new()
        // 业务端点
        .route("/users", get(list_users).post(create_user))
        .route("/users/:id", get(get_user))
        
        // 可观测性端点
        .route("/metrics", get(metrics_handler))
        .route("/health", get(health_check_handler))
        .route("/health/live", get(liveness_probe))
        .route("/health/ready", get(readiness_probe))
        .route("/profile", get(profile_handler))
        
        // 中间件
        .layer(TraceLayer::new_for_http())
        .layer(axum::middleware::from_fn(metrics_middleware))
        
        .with_state(state)
}

#[tokio::main]
async fn main() {
    let app = create_observable_server().await;
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080")
        .await
        .unwrap();
    
    println!("Server running on http://localhost:8080");
    println!("Metrics: http://localhost:8080/metrics");
    println!("Health: http://localhost:8080/health");
    
    axum::serve(listener, app).await.unwrap();
}
```

### 监控仪表板

```text
┌────────────────────────────────────────────────┐
│              Service Dashboard                 │
├────────────┬────────────┬────────────┬─────────┤
│  QPS: 1234 │  Latency   │  Error     │ Memory  │
│            │  P99: 50ms │  Rate: 0.1%│ 512MB   │
├────────────┴────────────┴────────────┴─────────┤
│                                                │
│  [Request Rate Chart]                          │
│                                                │
├────────────────────────────────────────────────┤
│                                                │
│  [Latency Distribution Chart]                  │
│                                                │
├────────────────────────────────────────────────┤
│                                                │
│  [Error Rate Chart]                            │
│                                                │
├────────────────────────────────────────────────┤
│  Recent Traces:                                │
│  • Order 12345: 45ms [View Trace]              │
│  • User Login: 12ms [View Trace]               │
└────────────────────────────────────────────────┘
```

---

## 📚 总结

### 可观测性清单

- ✅ **日志**: 结构化、可搜索、聚合
- ✅ **指标**: Prometheus、自定义业务指标
- ✅ **追踪**: OpenTelemetry、Jaeger 可视化
- ✅ **健康检查**: Liveness、Readiness、Startup
- ✅ **告警**: 实时告警、多渠道通知
- ✅ **性能剖析**: CPU、内存、火焰图

### 最佳实践

1. **全面覆盖**: 日志 + 指标 + 追踪
2. **结构化数据**: 便于搜索和分析
3. **合理采样**: 平衡可观测性和性能
4. **主动告警**: 问题发生前预警
5. **持续优化**: 根据监控数据优化系统

---

**文档贡献者:** AI Assistant  
**审核状态:** ✅ 已完成  
**最后更新:** 2025年10月28日
