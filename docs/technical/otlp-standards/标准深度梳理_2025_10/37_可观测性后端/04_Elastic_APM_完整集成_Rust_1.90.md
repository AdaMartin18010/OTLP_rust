# Elastic APM 完整集成 - Rust 1.90 + OTLP

## 📋 目录

- [Elastic APM 完整集成 - Rust 1.90 + OTLP](#elastic-apm-完整集成---rust-190--otlp)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Elastic APM?](#什么是-elastic-apm)
    - [为什么使用 Rust?](#为什么使用-rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Elastic Stack 架构](#1-elastic-stack-架构)
    - [2. APM 数据模型](#2-apm-数据模型)
  - [Rust 1.90 实现](#rust-190-实现)
    - [1. 项目设置](#1-项目设置)
    - [2. OTLP → Elastic APM](#2-otlp--elastic-apm)
    - [3. Axum 集成](#3-axum-集成)
  - [Trace 追踪](#trace-追踪)
    - [1. 分布式追踪](#1-分布式追踪)
    - [2. 数据库查询追踪](#2-数据库查询追踪)
    - [3. 外部 API 调用](#3-外部-api-调用)
  - [Metrics 指标](#metrics-指标)
    - [1. 应用指标](#1-应用指标)
    - [2. 自定义指标](#2-自定义指标)
  - [Logs 日志](#logs-日志)
    - [1. 结构化日志](#1-结构化日志)
    - [2. ECS 格式](#2-ecs-格式)
  - [Kibana 可视化](#kibana-可视化)
    - [1. APM UI](#1-apm-ui)
    - [2. 自定义仪表板](#2-自定义仪表板)
    - [3. 告警配置](#3-告警配置)
  - [高级特性](#高级特性)
    - [1. Span 链接](#1-span-链接)
    - [2. 采样策略](#2-采样策略)
    - [3. 错误追踪](#3-错误追踪)
  - [性能优化](#性能优化)
    - [1. 批量发送](#1-批量发送)
    - [2. 索引生命周期管理](#2-索引生命周期管理)
    - [3. 数据流优化](#3-数据流优化)
  - [最佳实践](#最佳实践)
    - [1. 命名规范](#1-命名规范)
    - [2. 标签策略](#2-标签策略)
    - [3. 生产部署](#3-生产部署)
  - [完整示例](#完整示例)
    - [1. 电商微服务](#1-电商微服务)
    - [2. Docker Compose 部署](#2-docker-compose-部署)
    - [3. Kibana 查询](#3-kibana-查询)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Elastic APM vs 其他方案](#elastic-apm-vs-其他方案)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Elastic APM?

**Elastic APM**(Application Performance Monitoring)是 Elastic Stack 的一部分,提供:

```text
Application (Rust)
    ↓ OTLP
APM Server
    ↓
Elasticsearch (存储)
    ↓
Kibana (可视化)
```

**核心组件**:

- **APM Server**: 接收遥测数据
- **Elasticsearch**: 存储 Trace/Metrics/Logs
- **Kibana APM UI**: 可视化分析
- **Elastic Agent**: 可选的统一采集器

### 为什么使用 Rust?

- **高性能**: 低延迟应用,减少可观测性开销
- **类型安全**: 编译期保证数据正确性
- **异步支持**: Tokio 异步导出数据
- **零成本抽象**: 最小化性能影响

### OTLP 集成价值

| 可观测性维度 | OTLP → Elastic APM |
|------------|-------------------|
| **分布式追踪** | Trace → APM Traces |
| **应用指标** | Metrics → APM Metrics |
| **日志关联** | Logs → Elasticsearch |
| **服务拓扑** | Service Map 自动生成 |
| **错误分析** | Error Tracking |

---

## 核心概念

### 1. Elastic Stack 架构

```text
┌─────────────────────────────────────┐
│    Rust Application (OTLP SDK)      │
└──────────────┬──────────────────────┘
               │ OTLP/gRPC (4317)
┌──────────────▼──────────────────────┐
│         APM Server (8200)           │
│  - OTLP Receiver                    │
│  - Data Transformation              │
└──────────────┬──────────────────────┘
               │ Bulk API
┌──────────────▼──────────────────────┐
│        Elasticsearch (9200)         │
│  - traces-apm*                      │
│  - metrics-apm*                     │
│  - logs-apm*                        │
└──────────────┬──────────────────────┘
               │ Query
┌──────────────▼──────────────────────┐
│          Kibana (5601)              │
│  - APM UI                           │
│  - Discover                         │
│  - Dashboards                       │
└─────────────────────────────────────┘
```

### 2. APM 数据模型

```json
{
  "@timestamp": "2025-10-11T12:00:00.000Z",
  "trace.id": "abc123...",
  "span.id": "def456...",
  "parent.id": "ghi789...",
  "transaction": {
    "id": "tx-1",
    "name": "GET /orders",
    "type": "request",
    "duration": {
      "us": 125000
    },
    "result": "HTTP 2xx",
    "sampled": true
  },
  "service": {
    "name": "order-service",
    "version": "1.0.0",
    "environment": "production"
  },
  "labels": {
    "user_id": "123",
    "region": "us-west"
  }
}
```

---

## Rust 1.90 实现

### 1. 项目设置

```toml
# Cargo.toml
[dependencies]
# Web 框架
axum = "0.7"
tokio = { version = "1.40", features = ["full"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["trace"] }

# OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics", "logs"] }
opentelemetry-semantic-conventions = "0.30"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"
```

### 2. OTLP → Elastic APM

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry(
    service_name: &str,
    service_version: &str,
    apm_endpoint: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // 创建资源属性
    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", service_version.to_string()),
        KeyValue::new("deployment.environment", "production"),
    ]);

    // 配置 OTLP 导出器 → APM Server
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(apm_endpoint), // http://apm-server:8200
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(resource.clone()),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 配置 Metrics 导出器
    let meter = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(apm_endpoint),
        )
        .with_resource(resource)
        .build()?;

    global::set_meter_provider(meter);

    // 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,order_service=debug".into()),
        )
        .with(tracing_subscriber::fmt::layer().json()) // JSON 格式日志
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!("Telemetry initialized for {}", service_name);

    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

### 3. Axum 集成

```rust
// src/main.rs
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tower_http::trace::{DefaultMakeSpan, DefaultOnResponse, TraceLayer};
use tracing::{info, instrument, Level};

mod telemetry;

#[derive(Clone)]
struct AppState {
    db: sqlx::PgPool,
    http_client: reqwest::Client,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Telemetry
    telemetry::init_telemetry(
        "order-service",
        "1.0.0",
        "http://apm-server:8200",
    )?;

    // 数据库连接池
    let db = sqlx::postgres::PgPoolOptions::new()
        .max_connections(10)
        .connect("postgresql://user:pass@localhost/orders")
        .await?;

    let state = AppState {
        db,
        http_client: reqwest::Client::new(),
    };

    let app = Router::new()
        .route("/orders", get(list_orders).post(create_order))
        .route("/orders/:id", get(get_order))
        .route("/health", get(health_check))
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::new().level(Level::INFO))
                .on_response(DefaultOnResponse::new().level(Level::INFO)),
        )
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    info!("Order service listening on http://0.0.0.0:8080");

    axum::serve(listener, app).await?;

    telemetry::shutdown_telemetry();

    Ok(())
}

#[derive(Debug, Serialize, Deserialize)]
struct Order {
    id: Option<i64>,
    user_id: i64,
    product_id: i64,
    quantity: i32,
    total: f64,
}

async fn health_check() -> &'static str {
    "OK"
}
```

---

## Trace 追踪

### 1. 分布式追踪

```rust
#[instrument(skip(state), fields(
    otel.kind = "server",
    http.method = "POST",
    http.route = "/orders"
))]
async fn create_order(
    State(state): State<AppState>,
    Json(mut order): Json<Order>,
) -> Result<Json<Order>, AppError> {
    info!(user_id = order.user_id, "Creating order");

    // 1. 检查库存(调用外部服务)
    check_inventory(&state.http_client, order.product_id, order.quantity).await?;

    // 2. 创建订单(数据库操作)
    let order_id = insert_order(&state.db, &order).await?;
    order.id = Some(order_id);

    // 3. 发送确认邮件(异步任务)
    tokio::spawn(async move {
        send_confirmation_email(order_id).await;
    });

    info!(order_id, "Order created successfully");

    Ok(Json(order))
}

#[instrument(skip(client), fields(
    otel.kind = "client",
    http.method = "POST",
    http.url = "http://inventory-service/check"
))]
async fn check_inventory(
    client: &reqwest::Client,
    product_id: i64,
    quantity: i32,
) -> Result<(), AppError> {
    let response = client
        .post("http://inventory-service:8080/check")
        .json(&serde_json::json!({
            "product_id": product_id,
            "quantity": quantity
        }))
        .send()
        .await?;

    if !response.status().is_success() {
        return Err(AppError::InsufficientInventory);
    }

    Ok(())
}
```

### 2. 数据库查询追踪

```rust
#[instrument(skip(db), fields(
    db.system = "postgresql",
    db.operation = "INSERT",
    db.table = "orders"
))]
async fn insert_order(db: &sqlx::PgPool, order: &Order) -> Result<i64, sqlx::Error> {
    let row = sqlx::query!(
        r#"
        INSERT INTO orders (user_id, product_id, quantity, total)
        VALUES ($1, $2, $3, $4)
        RETURNING id
        "#,
        order.user_id,
        order.product_id,
        order.quantity,
        order.total
    )
    .fetch_one(db)
    .await?;

    info!(order_id = row.id, "Order inserted into database");

    Ok(row.id)
}

#[instrument(skip(db), fields(
    db.system = "postgresql",
    db.operation = "SELECT",
    db.table = "orders"
))]
async fn get_order(
    State(state): State<AppState>,
    Path(id): Path<i64>,
) -> Result<Json<Order>, AppError> {
    let order = sqlx::query_as!(
        Order,
        r#"
        SELECT id, user_id, product_id, quantity, total
        FROM orders
        WHERE id = $1
        "#,
        id
    )
    .fetch_optional(&state.db)
    .await?
    .ok_or(AppError::NotFound)?;

    Ok(Json(order))
}
```

### 3. 外部 API 调用

```rust
use opentelemetry::{global, trace::TraceContextExt, Context};

#[instrument(skip(client))]
async fn call_payment_service(
    client: &reqwest::Client,
    order_id: i64,
    amount: f64,
) -> Result<String, AppError> {
    // 获取当前 Span Context
    let cx = Context::current();
    let span = cx.span();
    let span_context = span.span_context();

    // 手动注入 Trace Context (如果需要)
    let response = client
        .post("http://payment-service:8080/charge")
        .header("traceparent", format!(
            "00-{}-{}-01",
            span_context.trace_id(),
            span_context.span_id()
        ))
        .json(&serde_json::json!({
            "order_id": order_id,
            "amount": amount
        }))
        .send()
        .await?;

    let transaction_id = response.text().await?;

    info!(transaction_id, "Payment processed");

    Ok(transaction_id)
}
```

---

## Metrics 指标

### 1. 应用指标

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use std::sync::Arc;

pub struct AppMetrics {
    orders_created: Counter<u64>,
    order_value: Histogram<f64>,
    inventory_checks: Counter<u64>,
}

impl AppMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            orders_created: meter
                .u64_counter("orders.created")
                .with_description("Number of orders created")
                .init(),
            order_value: meter
                .f64_histogram("orders.value")
                .with_description("Order total value")
                .with_unit("USD")
                .init(),
            inventory_checks: meter
                .u64_counter("inventory.checks")
                .with_description("Number of inventory checks")
                .init(),
        }
    }

    pub fn record_order_created(&self, value: f64, user_id: i64) {
        use opentelemetry::KeyValue;

        self.orders_created.add(1, &[
            KeyValue::new("user_id", user_id.to_string()),
        ]);

        self.order_value.record(value, &[]);
    }
}

// 在 main 中使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    telemetry::init_telemetry("order-service", "1.0.0", "http://apm-server:8200")?;

    let meter = global::meter("order_service");
    let metrics = Arc::new(AppMetrics::new(&meter));

    // ...
}
```

### 2. 自定义指标

```rust
use opentelemetry::metrics::MeterProvider;

pub async fn collect_system_metrics(meter: &Meter) {
    let cpu_usage = meter
        .f64_observable_gauge("system.cpu.usage")
        .with_description("CPU usage percentage")
        .init();

    let memory_usage = meter
        .u64_observable_gauge("system.memory.usage")
        .with_description("Memory usage in bytes")
        .init();

    tokio::spawn(async move {
        loop {
            // 收集系统指标
            let cpu = get_cpu_usage();
            let mem = get_memory_usage();

            // 记录
            cpu_usage.observe(cpu, &[]);
            memory_usage.observe(mem, &[]);

            tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
        }
    });
}

fn get_cpu_usage() -> f64 {
    // 实现 CPU 使用率采集
    use sysinfo::{System, SystemExt};
    let mut sys = System::new_all();
    sys.refresh_all();
    sys.global_cpu_info().cpu_usage() as f64
}

fn get_memory_usage() -> u64 {
    use sysinfo::{System, SystemExt};
    let mut sys = System::new_all();
    sys.refresh_all();
    sys.used_memory()
}
```

---

## Logs 日志

### 1. 结构化日志

```rust
use tracing::{debug, error, info, warn};

#[instrument]
async fn process_order(order_id: i64) -> Result<(), AppError> {
    info!(order_id, "Processing order");

    match validate_order(order_id).await {
        Ok(_) => {
            debug!(order_id, "Order validation passed");
        }
        Err(e) => {
            warn!(order_id, error = %e, "Order validation failed");
            return Err(e);
        }
    }

    if let Err(e) = charge_customer(order_id).await {
        error!(order_id, error = %e, "Payment processing failed");
        return Err(e);
    }

    info!(order_id, "Order processed successfully");

    Ok(())
}
```

### 2. ECS 格式

配置日志输出为 Elastic Common Schema (ECS) 格式:

```rust
use tracing_subscriber::fmt::format::FmtSpan;

tracing_subscriber::fmt()
    .json()
    .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
    .with_current_span(true)
    .with_target(false)
    .init();
```

输出示例:

```json
{
  "@timestamp": "2025-10-11T12:00:00.123Z",
  "log.level": "INFO",
  "message": "Order processed successfully",
  "ecs.version": "1.12.0",
  "trace.id": "abc123...",
  "span.id": "def456...",
  "service.name": "order-service",
  "labels": {
    "order_id": "12345"
  }
}
```

---

## Kibana 可视化

### 1. APM UI

访问 Kibana APM UI: `http://kibana:5601/app/apm`

**核心视图**:

- **Services**: 所有服务列表
- **Transactions**: 端点性能
- **Errors**: 错误追踪
- **Service Map**: 服务依赖拓扑

### 2. 自定义仪表板

创建 Kibana Dashboard:

```json
{
  "title": "Order Service Dashboard",
  "panels": [
    {
      "title": "Request Rate",
      "visualization": {
        "type": "line",
        "query": "service.name:order-service"
      }
    },
    {
      "title": "P99 Latency",
      "visualization": {
        "type": "histogram",
        "aggregation": "percentile",
        "field": "transaction.duration.us",
        "percentile": 99
      }
    },
    {
      "title": "Error Rate",
      "visualization": {
        "type": "gauge",
        "query": "event.outcome:failure"
      }
    }
  ]
}
```

### 3. 告警配置

创建 Kibana Alert:

```json
{
  "name": "High Error Rate",
  "tags": ["order-service", "production"],
  "alertTypeId": "apm.error_rate",
  "schedule": {
    "interval": "1m"
  },
  "params": {
    "serviceName": "order-service",
    "environment": "production",
    "threshold": 5,
    "windowSize": 5,
    "windowUnit": "m"
  },
  "actions": [
    {
      "group": "default",
      "id": "slack-connector",
      "params": {
        "message": "🚨 Order Service error rate > 5%"
      }
    }
  ]
}
```

---

## 高级特性

### 1. Span 链接

```rust
use opentelemetry::trace::{Link, SpanBuilder, TraceContextExt};

#[instrument]
async fn process_batch(order_ids: Vec<i64>) {
    let cx = Context::current();
    let parent_span = cx.span();

    for order_id in order_ids {
        // 创建链接到父 Span 的子 Span
        let link = Link::new(parent_span.span_context().clone(), vec![]);

        let span = global::tracer("order_service")
            .span_builder("process_single_order")
            .with_links(vec![link])
            .start(&global::tracer("order_service"));

        let _guard = span.in_scope(|| {
            info!(order_id, "Processing single order");
        });
    }
}
```

### 2. 采样策略

```rust
use opentelemetry_sdk::trace::Sampler;

// 自定义采样器
pub struct CustomSampler {
    high_value_threshold: f64,
}

impl Sampler for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &opentelemetry::trace::OrderMap<opentelemetry::Key, opentelemetry::Value>,
        links: &[opentelemetry::trace::Link],
    ) -> opentelemetry::trace::SamplingResult {
        // 高价值订单总是采样
        if let Some(total) = attributes.get(&opentelemetry::Key::new("order.total")) {
            if let Some(value) = total.as_f64() {
                if value > self.high_value_threshold {
                    return opentelemetry::trace::SamplingResult {
                        decision: opentelemetry::trace::SamplingDecision::RecordAndSample,
                        attributes: vec![],
                        trace_state: Default::default(),
                    };
                }
            }
        }

        // 其他请求 10% 采样
        if trace_id.to_bytes()[0] < 26 {  // ~10%
            opentelemetry::trace::SamplingResult {
                decision: opentelemetry::trace::SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            }
        } else {
            opentelemetry::trace::SamplingResult {
                decision: opentelemetry::trace::SamplingDecision::Drop,
                attributes: vec![],
                trace_state: Default::default(),
            }
        }
    }
}
```

### 3. 错误追踪

```rust
use opentelemetry::trace::{Span, Status, StatusCode};

#[instrument]
async fn process_with_error_tracking(order_id: i64) -> Result<(), AppError> {
    let span = tracing::Span::current();

    match risky_operation(order_id).await {
        Ok(result) => {
            span.record("result", &result);
            Ok(())
        }
        Err(e) => {
            // 记录错误到 Span
            span.record_exception(&e);
            span.set_status(Status::error(format!("Operation failed: {}", e)));

            error!(order_id, error = %e, "Operation failed");

            Err(e)
        }
    }
}

// 扩展 trait 以支持 record_exception
trait SpanExt {
    fn record_exception(&self, error: &dyn std::error::Error);
}

impl SpanExt for tracing::Span {
    fn record_exception(&self, error: &dyn std::error::Error) {
        self.record("exception.message", &error.to_string());
        self.record("exception.type", &std::any::type_name_of_val(error));
    }
}
```

---

## 性能优化

### 1. 批量发送

配置 OTLP 导出器批量发送:

```rust
use opentelemetry_sdk::trace::BatchConfig;

let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://apm-server:8200"),
    )
    .with_batch_config(
        BatchConfig::default()
            .with_max_queue_size(2048)
            .with_scheduled_delay(std::time::Duration::from_secs(5))
            .with_max_export_batch_size(512),
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

### 2. 索引生命周期管理

配置 Elasticsearch ILM 策略:

```json
PUT _ilm/policy/apm-policy
{
  "policy": {
    "phases": {
      "hot": {
        "actions": {
          "rollover": {
            "max_size": "50GB",
            "max_age": "1d"
          }
        }
      },
      "warm": {
        "min_age": "7d",
        "actions": {
          "shrink": {
            "number_of_shards": 1
          },
          "forcemerge": {
            "max_num_segments": 1
          }
        }
      },
      "delete": {
        "min_age": "30d",
        "actions": {
          "delete": {}
        }
      }
    }
  }
}
```

### 3. 数据流优化

配置 APM Server 数据流:

```yaml
# apm-server.yml
apm-server:
  host: "0.0.0.0:8200"
  rum:
    enabled: false

output.elasticsearch:
  hosts: ["elasticsearch:9200"]
  pipeline: "apm"
  bulk_max_size: 5120

queue.mem:
  events: 8192
  flush.min_events: 2048
  flush.timeout: 1s

logging.level: info
logging.to_files: true
```

---

## 最佳实践

### 1. 命名规范

```rust
// ✅ 好的命名
#[instrument(name = "order_service.create_order")]
async fn create_order() {}

#[instrument(name = "order_service.db.insert_order")]
async fn insert_order() {}

// ❌ 避免
#[instrument(name = "func1")]  // 太模糊
async fn create_order() {}
```

### 2. 标签策略

```rust
use opentelemetry::KeyValue;

// 高基数标签(避免)
span.set_attribute(KeyValue::new("user_email", email));  // ❌

// 低基数标签(推荐)
span.set_attribute(KeyValue::new("user_tier", "premium"));  // ✅
span.set_attribute(KeyValue::new("region", "us-west"));     // ✅
```

### 3. 生产部署

```yaml
# docker-compose.yml (生产配置)
version: '3.8'

services:
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.12.0
    environment:
      - discovery.type=single-node
      - ES_JAVA_OPTS=-Xms4g -Xmx4g
      - xpack.security.enabled=false
    volumes:
      - es_data:/usr/share/elasticsearch/data
    deploy:
      resources:
        limits:
          memory: 8G

  apm-server:
    image: docker.elastic.co/apm/apm-server:8.12.0
    command: >
      apm-server -e
        -E apm-server.rum.enabled=false
        -E output.elasticsearch.hosts=["elasticsearch:9200"]
        -E apm-server.host=0.0.0.0:8200
    ports:
      - "8200:8200"
    depends_on:
      - elasticsearch

  kibana:
    image: docker.elastic.co/kibana/kibana:8.12.0
    ports:
      - "5601:5601"
    environment:
      ELASTICSEARCH_HOSTS: http://elasticsearch:9200
    depends_on:
      - elasticsearch

volumes:
  es_data:
```

---

## 完整示例

### 1. 电商微服务

(见上文代码示例)

### 2. Docker Compose 部署

(见上文)

### 3. Kibana 查询

**查找慢查询**:

```text
GET traces-apm*/_search
{
  "query": {
    "bool": {
      "must": [
        { "term": { "service.name": "order-service" }},
        { "range": { "transaction.duration.us": { "gte": 1000000 }}}
      ]
    }
  },
  "sort": [
    { "transaction.duration.us": "desc" }
  ]
}
```

**错误分析**:

```text
GET traces-apm*/_search
{
  "query": {
    "bool": {
      "must": [
        { "term": { "service.name": "order-service" }},
        { "term": { "event.outcome": "failure" }}
      ]
    }
  },
  "aggs": {
    "error_types": {
      "terms": { "field": "error.exception.type" }
    }
  }
}
```

---

## 总结

### 核心要点

1. **OTLP 原生支持**: Elastic APM Server 8.0+ 原生支持 OTLP
2. **统一可观测性**: Trace/Metrics/Logs 统一存储在 Elasticsearch
3. **强大可视化**: Kibana APM UI 提供开箱即用的可视化
4. **灵活查询**: Elasticsearch 强大的查询能力
5. **生态丰富**: 与 Elastic Stack 无缝集成

### Elastic APM vs 其他方案

| 特性 | Elastic APM | Jaeger | Zipkin |
|-----|-------------|--------|--------|
| **Trace** | ✅ | ✅ | ✅ |
| **Metrics** | ✅ | ❌ | ❌ |
| **Logs** | ✅ | ❌ | ❌ |
| **统一存储** | Elasticsearch | Cassandra/ES | Cassandra/ES |
| **查询能力** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **可视化** | Kibana | Jaeger UI | Zipkin UI |
| **学习曲线** | 中 | 低 | 低 |

### 下一步

- **Machine Learning**: 使用 Elastic ML 进行异常检测
- **Alerting**: 配置智能告警
- **APM Agents**: 尝试 Elastic APM 原生 Rust Agent(实验性)
- **跨集群查询**: Elasticsearch CCS 实现多集群可观测性

---

## 参考资料

- [Elastic APM 官方文档](https://www.elastic.co/guide/en/apm/guide/current/index.html)
- [Elastic Common Schema (ECS)](https://www.elastic.co/guide/en/ecs/current/index.html)
- [APM Server OTLP Support](https://www.elastic.co/guide/en/apm/server/current/open-telemetry.html)
- [Kibana APM UI](https://www.elastic.co/guide/en/kibana/current/apm.html)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Elastic Stack 版本**: 8.12+  
**OpenTelemetry**: 0.30+
