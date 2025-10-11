# Honeycomb - Rust + OTLP 完整集成指南

## 📋 目录

- [Honeycomb - Rust + OTLP 完整集成指南](#honeycomb---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Honeycomb?](#什么是-honeycomb)
    - [为什么选择 Honeycomb?](#为什么选择-honeycomb)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Honeycomb 架构](#1-honeycomb-架构)
    - [2. 核心特性](#2-核心特性)
  - [环境准备](#环境准备)
    - [1. Honeycomb 账户设置](#1-honeycomb-账户设置)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. OTLP 导出器配置](#1-otlp-导出器配置)
    - [2. 基本追踪](#2-基本追踪)
    - [3. 结构化字段](#3-结构化字段)
  - [高级查询](#高级查询)
    - [1. BubbleUp 查询](#1-bubbleup-查询)
    - [2. 热图分析](#2-热图分析)
    - [3. SLO 监控](#3-slo-监控)
  - [Triggers 告警](#triggers-告警)
    - [1. 创建 Trigger](#1-创建-trigger)
    - [2. 通知集成](#2-通知集成)
  - [Boards 仪表板](#boards-仪表板)
    - [1. 创建仪表板](#1-创建仪表板)
    - [2. 图表类型](#2-图表类型)
  - [分布式追踪](#分布式追踪)
    - [1. Trace 可视化](#1-trace-可视化)
    - [2. 跨服务追踪](#2-跨服务追踪)
  - [性能优化](#性能优化)
    - [1. 采样策略](#1-采样策略)
    - [2. 字段优化](#2-字段优化)
  - [实战示例](#实战示例)
    - [1. 微服务监控](#1-微服务监控)
    - [2. 性能调优](#2-性能调优)
  - [最佳实践](#最佳实践)
    - [1. 字段命名](#1-字段命名)
    - [2. 采样配置](#2-采样配置)
    - [3. 成本优化](#3-成本优化)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Honeycomb vs 其他 APM](#honeycomb-vs-其他-apm)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Honeycomb?

**Honeycomb** 是为现代软件工程设计的可观测性平台:

```text
┌─────────────────────────────────────┐
│        Honeycomb Platform           │
│  ┌──────────────────────────────┐   │
│  │  • BubbleUp (异常检测)        │   │
│  │  • 高维度查询                 │   │
│  │  │  • Triggers (智能告警)     │   │
│  │  • SLO 监控                   │   │
│  │  • Boards (仪表板)            │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
         ↑ OTLP
┌─────────────────────────────────────┐
│      Rust Application               │
└─────────────────────────────────────┘
```

**核心特性**:

- **高基数支持**: 支持数百万唯一值
- **BubbleUp**: 自动发现异常原因
- **实时查询**: 秒级查询响应
- **SLO 监控**: 内置 SLO 跟踪
- **智能采样**: 保留重要 Trace

### 为什么选择 Honeycomb?

| 优势 | 说明 |
|------|------|
| **高基数** | 支持 user_id, trace_id 等高基数字段 |
| **可探索性** | 无需预定义指标,自由探索 |
| **协作** | 团队共享查询和仪表板 |
| **成本可控** | 智能采样降低成本 |
| **OTLP 原生** | 完全兼容 OpenTelemetry |

### OTLP 集成价值

```text
Rust App → OpenTelemetry SDK → OTLP → Honeycomb
    ↓              ↓               ↓        ↓
  业务逻辑      标准化追踪      统一协议  深度分析
```

**优势**:

- **供应商中立**: OpenTelemetry 标准
- **丰富上下文**: 高基数字段支持
- **灵活查询**: 探索式分析
- **智能告警**: Triggers 自动检测

---

## 核心概念

### 1. Honeycomb 架构

```text
┌─────────────────────────────────────────┐
│           Honeycomb UI                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐ │
│  │  Query  │  │ Boards  │  │Triggers │ │
│  └─────────┘  └─────────┘  └─────────┘ │
└──────────────────┬──────────────────────┘
                   │ Query API
┌──────────────────▼──────────────────────┐
│         Honeycomb Backend               │
│  • 列式存储 (Clickhouse)                 │
│  • BubbleUp 引擎                        │
│  • SLO 计算                             │
└──────────────────┬──────────────────────┘
                   │ OTLP Ingestion
┌──────────────────▼──────────────────────┐
│      OpenTelemetry Collector (可选)     │
└──────────────────┬──────────────────────┘
                   │ OTLP
┌──────────────────▼──────────────────────┐
│         Rust Application                │
└─────────────────────────────────────────┘
```

### 2. 核心特性

**Dataset**: Honeycomb 的数据集,类似数据库表
**Event**: 一条追踪数据(Span)
**Field**: 事件的属性
**Query**: 数据查询和可视化
**Trigger**: 智能告警规则

---

## 环境准备

### 1. Honeycomb 账户设置

```bash
# 1. 注册 Honeycomb 账户
# https://ui.honeycomb.io/signup

# 2. 获取 API Key
# Settings → Team Settings → API Keys → Create API Key

# 3. 创建 Dataset
# 左侧导航 → New Dataset → 输入名称 (例如: rust-app)

# 4. 设置环境变量
export HONEYCOMB_API_KEY="your_api_key_here"
export HONEYCOMB_DATASET="rust-app"
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "honeycomb-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["grpc-tonic", "http-proto"] }

# Tracing
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }

# HTTP
axum = "0.7"
tower-http = { version = "0.5", features = ["trace"] }
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 其他
uuid = { version = "1.8", features = ["v4", "serde"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. OTLP 导出器配置

```rust
// src/honeycomb.rs
use opentelemetry::{
    global,
    trace::TracerProvider,
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use anyhow::Result;

pub fn init_honeycomb_tracing(
    api_key: &str,
    dataset: &str,
    service_name: &str,
) -> Result<()> {
    // 配置 OTLP 导出器指向 Honeycomb
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()  // Honeycomb 推荐使用 HTTP
                .with_endpoint("https://api.honeycomb.io")
                .with_headers(std::collections::HashMap::from([
                    ("x-honeycomb-team".to_string(), api_key.to_string()),
                    ("x-honeycomb-dataset".to_string(), dataset.to_string()),
                ])),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider);
    
    // 初始化 Tracing Subscriber
    let telemetry = tracing_opentelemetry::layer()
        .with_tracer(global::tracer(service_name));
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}

pub fn shutdown_honeycomb_tracing() {
    global::shutdown_tracer_provider();
}
```

### 2. 基本追踪

```rust
// src/main.rs
use tracing::{info, instrument};

#[tokio::main]
async fn main() -> Result<()> {
    let api_key = std::env::var("HONEYCOMB_API_KEY")?;
    let dataset = std::env::var("HONEYCOMB_DATASET")?;
    
    init_honeycomb_tracing(&api_key, &dataset, "rust-app")?;
    
    info!("Application started");
    
    // 处理请求
    process_request("user123", "order456").await?;
    
    shutdown_honeycomb_tracing();
    Ok(())
}

#[instrument]
async fn process_request(user_id: &str, order_id: &str) -> Result<()> {
    info!("Processing request");
    
    // 业务逻辑
    validate_order(order_id).await?;
    charge_payment(user_id, 99.99).await?;
    send_confirmation(user_id).await?;
    
    info!("Request completed successfully");
    Ok(())
}

#[instrument]
async fn validate_order(order_id: &str) -> Result<()> {
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}

#[instrument]
async fn charge_payment(user_id: &str, amount: f64) -> Result<()> {
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    Ok(())
}

#[instrument]
async fn send_confirmation(user_id: &str) -> Result<()> {
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    Ok(())
}
```

### 3. 结构化字段

```rust
use tracing::{info_span, Span};
use opentelemetry::trace::TraceContextExt;

#[instrument(
    fields(
        user_id = %user_id,
        order_id = %order_id,
        cart_total,
        payment_method,
        user_tier,
    )
)]
async fn checkout(
    user_id: &str,
    order_id: &str,
    cart_total: f64,
    payment_method: &str,
) -> Result<()> {
    let span = Span::current();
    
    // 添加高基数字段 (Honeycomb 的优势)
    span.record("cart_total", cart_total);
    span.record("payment_method", payment_method);
    
    // 查询用户信息
    let user_tier = get_user_tier(user_id).await?;
    span.record("user_tier", &user_tier.as_str());
    
    // 根据用户等级处理
    match user_tier.as_str() {
        "premium" => {
            span.record("discount_applied", true);
            apply_premium_discount(cart_total).await?;
        }
        _ => {
            span.record("discount_applied", false);
        }
    }
    
    Ok(())
}

async fn get_user_tier(user_id: &str) -> Result<String> {
    // 模拟数据库查询
    Ok("premium".to_string())
}
```

---

## 高级查询

### 1. BubbleUp 查询

**BubbleUp** 自动发现异常原因:

```rust
// 在代码中添加丰富的字段,Honeycomb 会自动分析
#[instrument(
    fields(
        user_id,
        region,
        device_type,
        api_version,
        cache_hit,
        db_query_time_ms,
    )
)]
async fn api_handler(req: Request) -> Result<Response> {
    let span = Span::current();
    
    // 记录请求属性
    span.record("user_id", &req.user_id);
    span.record("region", &req.region);
    span.record("device_type", &req.device_type);
    span.record("api_version", &req.api_version);
    
    // 记录性能指标
    let start = std::time::Instant::now();
    let data = fetch_from_db(&req).await?;
    let db_time = start.elapsed().as_millis();
    
    span.record("db_query_time_ms", db_time as i64);
    span.record("cache_hit", data.from_cache);
    
    Ok(Response::new(data))
}
```

**在 Honeycomb UI 中**:

1. 选择 `duration_ms > 1000` (慢请求)
2. 点击 **BubbleUp**
3. Honeycomb 自动显示: "region=us-west AND device_type=mobile 的请求慢 3x"

### 2. 热图分析

```rust
// 添加分布式跟踪的延迟信息
use opentelemetry::metrics::{Counter, Histogram};

pub struct Metrics {
    request_duration: Histogram<f64>,
    request_count: Counter<u64>,
}

impl Metrics {
    pub fn new() -> Self {
        let meter = global::meter("rust-app");
        
        Self {
            request_duration: meter
                .f64_histogram("request.duration")
                .with_description("Request duration in seconds")
                .with_unit("s")
                .init(),
            request_count: meter
                .u64_counter("request.count")
                .with_description("Total request count")
                .init(),
        }
    }
    
    pub fn record_request(&self, duration_ms: f64, endpoint: &str, status: u16) {
        let attributes = vec![
            KeyValue::new("endpoint", endpoint.to_string()),
            KeyValue::new("status_code", status as i64),
        ];
        
        self.request_duration.record(duration_ms / 1000.0, &attributes);
        self.request_count.add(1, &attributes);
    }
}
```

### 3. SLO 监控

```rust
// src/slo.rs
#[instrument(fields(slo.target = "api_latency_p99"))]
async fn track_slo_latency(duration_ms: f64) {
    let span = Span::current();
    
    // Honeycomb 会自动聚合这些数据用于 SLO 监控
    span.record("latency_ms", duration_ms);
    
    // 标记 SLO 违规
    if duration_ms > 500.0 {
        span.record("slo.violated", true);
        span.record("slo.target_ms", 500.0);
    }
}
```

**在 Honeycomb UI 中设置 SLO**:

```text
1. 导航到 SLOs → Create SLO
2. 名称: API Latency P99 < 500ms
3. Query: 
   - CALC: P99(duration_ms)
   - WHERE: name = "api_handler"
   - Target: < 500
4. Time Window: 30 days
5. Success Rate: 99.9%
```

---

## Triggers 告警

### 1. 创建 Trigger

```rust
// 代码中添加告警相关字段
#[instrument(fields(
    error_type,
    error_severity,
    affects_users,
))]
async fn handle_error(error: &AppError) {
    let span = Span::current();
    
    span.record("error_type", &format!("{:?}", error));
    span.record("error_severity", error.severity());
    span.record("affects_users", error.user_count());
    
    // Honeycomb Trigger 会检测这些字段
}
```

**Honeycomb UI Trigger 配置**:

```yaml
# Trigger: High Error Rate
name: "High Error Rate Alert"
query:
  calculation: COUNT
  filter: "status_code >= 500"
  group_by: ["service.name", "error_type"]
threshold:
  operator: ">="
  value: 10
  window: "5m"
frequency: "1m"
recipients:
  - type: slack
    channel: "#alerts"
  - type: pagerduty
    service_key: "xxx"
```

### 2. 通知集成

```rust
// src/alerts.rs
use serde::{Deserialize, Serialize};

#[derive(Serialize)]
pub struct AlertContext {
    pub service: String,
    pub environment: String,
    pub error_rate: f64,
    pub affected_users: u64,
}

#[instrument(skip(alert_ctx))]
pub async fn send_custom_alert(alert_ctx: AlertContext) -> Result<()> {
    let span = Span::current();
    
    // 记录告警上下文
    span.record("alert.service", &alert_ctx.service);
    span.record("alert.error_rate", alert_ctx.error_rate);
    span.record("alert.affected_users", alert_ctx.affected_users as i64);
    
    // 发送到 Slack
    send_to_slack(&alert_ctx).await?;
    
    // 创建 PagerDuty incident
    if alert_ctx.error_rate > 5.0 {
        create_pagerduty_incident(&alert_ctx).await?;
    }
    
    Ok(())
}
```

---

## Boards 仪表板

### 1. 创建仪表板

```rust
// 在代码中确保记录关键指标
pub struct DashboardMetrics {
    pub request_rate: f64,
    pub error_rate: f64,
    pub p50_latency: f64,
    pub p99_latency: f64,
    pub active_users: u64,
}

#[instrument]
pub async fn collect_dashboard_metrics() -> Result<DashboardMetrics> {
    let span = Span::current();
    
    let metrics = DashboardMetrics {
        request_rate: calculate_request_rate().await?,
        error_rate: calculate_error_rate().await?,
        p50_latency: calculate_p50_latency().await?,
        p99_latency: calculate_p99_latency().await?,
        active_users: count_active_users().await?,
    };
    
    // 记录到 Span (Honeycomb 会聚合)
    span.record("metrics.request_rate", metrics.request_rate);
    span.record("metrics.error_rate", metrics.error_rate);
    span.record("metrics.p50_latency", metrics.p50_latency);
    span.record("metrics.p99_latency", metrics.p99_latency);
    span.record("metrics.active_users", metrics.active_users as i64);
    
    Ok(metrics)
}
```

### 2. 图表类型

**Honeycomb Board 配置示例**:

```yaml
# Board: Service Health
charts:
  - name: "Request Rate"
    type: "timeseries"
    query:
      calculation: "RATE_AVG(COUNT)"
      filter: "name = 'http_request'"
      group_by: ["service.name"]
  
  - name: "Error Rate"
    type: "timeseries"
    query:
      calculation: "RATE_AVG(COUNT)"
      filter: "status_code >= 500"
      group_by: ["error_type"]
  
  - name: "Latency Heatmap"
    type: "heatmap"
    query:
      calculation: "HEATMAP(duration_ms)"
      filter: "name = 'api_handler'"
  
  - name: "Top Slow Endpoints"
    type: "table"
    query:
      calculation: "P99(duration_ms)"
      filter: "name = 'http_request'"
      group_by: ["http.route"]
      order_by: "P99(duration_ms) DESC"
      limit: 10
```

---

## 分布式追踪

### 1. Trace 可视化

```rust
// src/distributed_trace.rs
use opentelemetry::trace::{SpanContext, TraceContextExt};

#[instrument]
pub async fn distributed_operation() -> Result<()> {
    let span = Span::current();
    let ctx = span.context();
    let span_ctx = ctx.span().span_context();
    
    // 记录 Trace ID (Honeycomb 会自动关联)
    tracing::info!(
        trace_id = %span_ctx.trace_id(),
        span_id = %span_ctx.span_id(),
        "Starting distributed operation"
    );
    
    // 调用下游服务
    call_downstream_service_a().await?;
    call_downstream_service_b().await?;
    
    Ok(())
}

#[instrument]
async fn call_downstream_service_a() -> Result<()> {
    // Honeycomb 会显示为子 Span
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}

#[instrument]
async fn call_downstream_service_b() -> Result<()> {
    tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
    Ok(())
}
```

### 2. 跨服务追踪

```rust
// Service A
#[instrument]
async fn service_a_handler() -> Result<()> {
    let client = reqwest::Client::new();
    
    // OpenTelemetry 会自动注入 Trace Context
    let response = client
        .get("http://service-b/api")
        .send()
        .await?;
    
    Ok(())
}

// Service B
#[instrument]
async fn service_b_handler(req: Request) -> Result<Response> {
    // OpenTelemetry 会自动提取 Trace Context
    // Honeycomb 会将两个服务的 Span 关联起来
    
    Ok(Response::new("success"))
}
```

---

## 性能优化

### 1. 采样策略

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

// 智能采样器
pub struct HoneycombSampler {
    default_rate: f64,
}

impl HoneycombSampler {
    pub fn new(default_rate: f64) -> Self {
        Self { default_rate }
    }
    
    // 根据请求特征动态采样
    pub fn should_sample(&self, span: &SpanContext) -> bool {
        // 1. 总是采样错误
        if span.attributes().contains_key("error") {
            return true;
        }
        
        // 2. 总是采样慢请求
        if let Some(duration) = span.attributes().get("duration_ms") {
            if duration.as_f64() > 1000.0 {
                return true;
            }
        }
        
        // 3. 其他请求按比例采样
        rand::random::<f64>() < self.default_rate
    }
}

// 使用采样器
pub fn init_with_sampling(api_key: &str, dataset: &str) -> Result<()> {
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(/* ... */)
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::ParentBased(Box::new(
                    Sampler::TraceIdRatioBased(0.1)  // 10% 采样
                )))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(())
}
```

### 2. 字段优化

```rust
// 优化字段命名和结构
#[instrument(
    // 使用一致的命名约定
    fields(
        // 高基数字段 (Honeycomb 优势)
        user.id = %user_id,
        request.id = %request_id,
        
        // 低基数字段 (用于分组)
        http.method = %method,
        http.status_code,
        
        // 数值字段 (用于聚合)
        duration_ms,
        bytes_sent,
    )
)]
async fn optimized_handler(
    user_id: &str,
    request_id: &str,
    method: &str,
) -> Result<Response> {
    let span = Span::current();
    
    let start = std::time::Instant::now();
    
    let result = process_request().await;
    
    let duration = start.elapsed().as_millis();
    span.record("duration_ms", duration as i64);
    
    match &result {
        Ok(resp) => {
            span.record("http.status_code", 200);
            span.record("bytes_sent", resp.body.len() as i64);
        }
        Err(e) => {
            span.record("http.status_code", 500);
            span.record("error", true);
        }
    }
    
    result
}
```

---

## 实战示例

### 1. 微服务监控

```rust
// src/microservice_example.rs
use axum::{
    Router,
    routing::get,
    extract::Path,
    Json,
};

pub async fn start_microservice() -> Result<()> {
    let app = Router::new()
        .route("/api/users/:id", get(get_user))
        .route("/api/orders/:id", get(get_order))
        .layer(tower_http::trace::TraceLayer::new_for_http());
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument(
    fields(
        user_id = %id,
        cache_hit,
        db_query_ms,
    )
)]
async fn get_user(Path(id): Path<String>) -> Result<Json<User>> {
    let span = Span::current();
    
    // 尝试缓存
    if let Some(user) = check_cache(&id).await? {
        span.record("cache_hit", true);
        return Ok(Json(user));
    }
    
    span.record("cache_hit", false);
    
    // 查询数据库
    let start = std::time::Instant::now();
    let user = query_database(&id).await?;
    let db_time = start.elapsed().as_millis();
    
    span.record("db_query_ms", db_time as i64);
    
    Ok(Json(user))
}
```

### 2. 性能调优

```rust
// 使用 Honeycomb 进行性能调优
#[instrument(
    fields(
        query.type,
        query.complexity,
        optimization.applied,
    )
)]
async fn optimized_query(query: &str) -> Result<Vec<Record>> {
    let span = Span::current();
    
    // 分析查询复杂度
    let complexity = analyze_query_complexity(query);
    span.record("query.complexity", complexity);
    
    // 根据复杂度选择优化策略
    let result = if complexity > 100 {
        span.record("optimization.applied", "parallel_execution");
        execute_parallel(query).await?
    } else {
        span.record("optimization.applied", "standard_execution");
        execute_standard(query).await?
    };
    
    span.record("query.type", classify_query(query));
    
    Ok(result)
}
```

---

## 最佳实践

### 1. 字段命名

```rust
// ✅ 好的实践
#[instrument(fields(
    user.id,           // 使用命名空间
    http.method,
    db.query_time_ms,
    cache.hit,
))]

// ❌ 避免
#[instrument(fields(
    userid,            // 没有命名空间
    method,            // 不明确
    time,              // 太通用
))]
```

### 2. 采样配置

```rust
// 生产环境采样配置
pub fn production_sampling() -> Sampler {
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.01)  // 1% 基础采样
    ))
}

// 总是采样重要事件
#[instrument]
async fn critical_operation() {
    // 强制采样
    let span = Span::current();
    span.record("sample.priority", 1);
}
```

### 3. 成本优化

```rust
// 减少字段数量
#[instrument(
    skip(large_payload),  // 跳过大对象
    fields(
        // 只记录必要字段
        essential.field1,
        essential.field2,
    )
)]
async fn cost_optimized_handler(large_payload: Vec<u8>) -> Result<()> {
    // 不要记录整个 large_payload
    Ok(())
}
```

---

## 总结

### 核心要点

1. **Honeycomb**: 高基数可观测性平台
2. **BubbleUp**: 自动异常检测
3. **OTLP 原生**: 完全兼容 OpenTelemetry
4. **智能采样**: 保留重要 Trace
5. **SLO 监控**: 内置 SLO 跟踪

### Honeycomb vs 其他 APM

| 特性 | Honeycomb | Datadog | New Relic | Prometheus |
|------|-----------|---------|-----------|------------|
| **高基数支持** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐ |
| **BubbleUp** | ✅ 独有 | ❌ | ❌ | ❌ |
| **探索性查询** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **OTLP 原生** | ✅ | ✅ | ✅ | ⚠️ |
| **价格** | 按事件数 | 按主机数 | 按主机数 | 免费 |

### 下一步

- **Honeycomb Query Language**: 学习高级查询
- **Derived Columns**: 创建计算字段
- **Refinery**: 部署智能采样代理

---

## 参考资料

- [Honeycomb 官方文档](https://docs.honeycomb.io/)
- [OpenTelemetry + Honeycomb](https://docs.honeycomb.io/getting-data-in/opentelemetry/)
- [BubbleUp 指南](https://docs.honeycomb.io/working-with-your-data/bubbleup/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.30+  
**Honeycomb**: Latest
