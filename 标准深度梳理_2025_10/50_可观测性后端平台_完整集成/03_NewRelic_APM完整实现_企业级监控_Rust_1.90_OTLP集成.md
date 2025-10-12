# New Relic APM 完整实现指南

## 目录

- [New Relic APM 完整实现指南](#new-relic-apm-完整实现指南)
  - [目录](#目录)
  - [1. New Relic APM 概述](#1-new-relic-apm-概述)
    - [1.1 什么是 New Relic?](#11-什么是-new-relic)
    - [1.2 核心功能](#12-核心功能)
    - [1.3 为什么选择 New Relic?](#13-为什么选择-new-relic)
  - [2. 架构设计](#2-架构设计)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
    - [3.2 环境变量配置](#32-环境变量配置)
  - [4. OpenTelemetry 集成](#4-opentelemetry-集成)
    - [4.1 New Relic OTLP Exporter](#41-new-relic-otlp-exporter)
    - [4.2 自动仪表化](#42-自动仪表化)
  - [5. 分布式追踪](#5-分布式追踪)
    - [5.1 HTTP 服务追踪](#51-http-服务追踪)
    - [5.2 数据库追踪](#52-数据库追踪)
    - [5.3 消息队列追踪](#53-消息队列追踪)
  - [6. 自定义指标](#6-自定义指标)
    - [6.1 业务指标](#61-业务指标)
    - [6.2 系统指标](#62-系统指标)
  - [7. 错误追踪](#7-错误追踪)
    - [7.1 错误上报](#71-错误上报)
    - [7.2 错误分组](#72-错误分组)
  - [8. 日志集成](#8-日志集成)
    - [8.1 结构化日志](#81-结构化日志)
    - [8.2 日志关联](#82-日志关联)
  - [9. 性能优化](#9-性能优化)
    - [9.1 批量发送](#91-批量发送)
    - [9.2 采样策略](#92-采样策略)
  - [10. 告警配置](#10-告警配置)
    - [10.1 NRQL 告警](#101-nrql-告警)
    - [10.2 基线告警](#102-基线告警)
  - [11. 生产部署](#11-生产部署)
    - [11.1 Docker Compose](#111-docker-compose)
    - [11.2 Kubernetes](#112-kubernetes)
  - [12. 国际标准对齐](#12-国际标准对齐)
    - [12.1 OpenTelemetry 标准](#121-opentelemetry-标准)
    - [12.2 New Relic 最佳实践](#122-new-relic-最佳实践)
  - [总结](#总结)
    - [New Relic APM 核心优势](#new-relic-apm-核心优势)
    - [适用场景](#适用场景)
    - [性能基准](#性能基准)

---

## 1. New Relic APM 概述

### 1.1 什么是 New Relic?

**New Relic** 是企业级应用性能监控 (APM) 平台,提供:

- **全栈可观测性**: 前端、后端、基础设施
- **AI 驱动分析**: 自动异常检测和根因分析
- **实时监控**: 毫秒级数据延迟
- **NRQL 查询语言**: 强大的数据查询能力

### 1.2 核心功能

| 功能 | 描述 |
|------|------|
| **APM** | 应用性能监控 |
| **分布式追踪** | 端到端事务追踪 |
| **日志管理** | 集中式日志聚合 |
| **基础设施监控** | 服务器/容器监控 |
| **合成监控** | 主动监控和告警 |
| **错误追踪** | 实时错误分析 |

### 1.3 为什么选择 New Relic?

- ✅ **企业级稳定性**: 99.99% SLA
- ✅ **AI 驱动**: 自动异常检测
- ✅ **完整集成**: 支持 OpenTelemetry
- ✅ **强大查询**: NRQL 查询语言
- ✅ **实时告警**: 智能告警系统

---

## 2. 架构设计

```text
┌────────────────────────────────────────────────────────┐
│                New Relic APM 架构                      │
├────────────────────────────────────────────────────────┤
│                                                        │
│  ┌─────────────────┐                                   │
│  │   Rust App      │                                   │
│  │  (OpenTelemetry)│                                   │
│  └────────┬────────┘                                   │
│           │                                            │
│           │ OTLP/gRPC or HTTP                          │
│           │                                            │
│           ▼                                            │
│  ┌─────────────────┐                                   │
│  │  OTLP Endpoint  │                                   │
│  │  (otlp.nr-data  │                                   │
│  │   .net:4317)    │                                   │
│  └────────┬────────┘                                   │
│           │                                            │
│           ▼                                            │
│  ┌─────────────────────────────────────┐               │
│  │       New Relic Platform            │               │
│  │  ┌──────────┐  ┌──────────────┐     │               │
│  │  │   APM    │  │ Distributed  │     │               │
│  │  │          │  │   Tracing    │     │               │
│  │  └──────────┘  └──────────────┘     │               │
│  │  ┌──────────┐  ┌──────────────┐     │               │
│  │  │   Logs   │  │   Metrics    │     │               │
│  │  │          │  │              │     │               │
│  │  └──────────┘  └──────────────┘     │               │
│  │  ┌──────────┐  ┌──────────────┐     │               │
│  │  │  Errors  │  │   Insights   │     │               │
│  │  │          │  │   (NRQL)     │     │               │
│  │  └──────────┘  └──────────────┘     │               │
│  └─────────────────────────────────────┘               │
│                                                        │
└────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "newrelic-rust-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# 异步运行时
tokio = { version = "1", features = ["full"] }

# Web 框架
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic", "http-proto"] }
opentelemetry-semantic-conventions = "0.25"

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# Metrics
opentelemetry-prometheus = "0.25"
prometheus = "0.13"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 错误处理
thiserror = "1"
anyhow = "1"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 环境变量
dotenvy = "0.15"
```

### 3.2 环境变量配置

```bash
# .env
NEW_RELIC_LICENSE_KEY=your_license_key_here
NEW_RELIC_OTLP_ENDPOINT=https://otlp.nr-data.net:4317
SERVICE_NAME=rust-app
DEPLOYMENT_ENVIRONMENT=production
RUST_LOG=info
```

---

## 4. OpenTelemetry 集成

### 4.1 New Relic OTLP Exporter

```rust
use opentelemetry::{
    global, trace::TracerProvider, KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{Config, Sampler},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化 New Relic 遥测
pub fn init_new_relic_telemetry() -> anyhow::Result<()> {
    // 获取环境变量
    let license_key = std::env::var("NEW_RELIC_LICENSE_KEY")
        .expect("NEW_RELIC_LICENSE_KEY not set");
    let otlp_endpoint = std::env::var("NEW_RELIC_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "https://otlp.nr-data.net:4317".to_string());
    let service_name = std::env::var("SERVICE_NAME")
        .unwrap_or_else(|_| "rust-app".to_string());
    let environment = std::env::var("DEPLOYMENT_ENVIRONMENT")
        .unwrap_or_else(|_| "production".to_string());

    // 1. 配置 OTLP Tracer
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint)
                .with_metadata(
                    tonic::metadata::MetadataMap::from_headers(
                        [(
                            "api-key".parse().unwrap(),
                            license_key.parse().unwrap(),
                        )]
                        .into_iter()
                        .collect(),
                    ),
                ),
        )
        .with_trace_config(
            Config::default()
                .with_sampler(Sampler::AlwaysOn) // 生产环境可使用 TraceIdRatioBased
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.clone()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", environment.clone()),
                    KeyValue::new("telemetry.sdk.name", "opentelemetry"),
                    KeyValue::new("telemetry.sdk.language", "rust"),
                    KeyValue::new("telemetry.sdk.version", "0.25.0"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    // 2. 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!(
        service.name = %service_name,
        deployment.environment = %environment,
        "New Relic telemetry initialized"
    );

    Ok(())
}

/// 优雅关闭
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
    tracing::info!("Telemetry shutdown complete");
}
```

### 4.2 自动仪表化

```rust
use axum::{
    extract::State,
    http::StatusCode,
    routing::get,
    Json, Router,
};
use tower_http::trace::{DefaultMakeSpan, DefaultOnResponse, TraceLayer};
use tracing::Level;

/// 创建带追踪的 Axum 路由
pub fn create_traced_router() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/api/users", get(list_users))
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::new().level(Level::INFO))
                .on_response(DefaultOnResponse::new().level(Level::INFO)),
        )
}

#[tracing::instrument]
async fn health_check() -> StatusCode {
    StatusCode::OK
}

#[tracing::instrument]
async fn list_users() -> Json<Vec<String>> {
    Json(vec!["Alice".to_string(), "Bob".to_string()])
}
```

---

## 5. 分布式追踪

### 5.1 HTTP 服务追踪

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

/// 带追踪的 HTTP 请求处理
#[instrument(skip(pool), fields(
    http.method = "GET",
    http.route = "/api/orders/{order_id}"
))]
pub async fn get_order(
    order_id: String,
    pool: sqlx::PgPool,
) -> Result<Json<Order>, AppError> {
    let tracer = global::tracer("http-server");
    
    // 创建 Span
    let span = tracer
        .span_builder(format!("GET /api/orders/{}", order_id))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.route", "/api/orders/{order_id}"),
            KeyValue::new("http.target", format!("/api/orders/{}", order_id)),
            KeyValue::new("order.id", order_id.clone()),
        ])
        .start(&tracer);
    
    let _cx = opentelemetry::Context::current_with_span(span).attach();
    
    // 查询数据库
    let order = fetch_order_from_db(&pool, &order_id).await?;
    
    // 调用外部服务
    let enriched_order = enrich_order_data(&order).await?;
    
    Ok(Json(enriched_order))
}

/// 数据库查询 (自动追踪)
#[instrument(skip(pool))]
async fn fetch_order_from_db(
    pool: &sqlx::PgPool,
    order_id: &str,
) -> Result<Order, AppError> {
    let order = sqlx::query_as!(
        Order,
        "SELECT * FROM orders WHERE id = $1",
        order_id
    )
    .fetch_one(pool)
    .await?;
    
    Ok(order)
}

/// 外部服务调用 (手动追踪)
#[instrument]
async fn enrich_order_data(order: &Order) -> Result<Order, AppError> {
    let tracer = global::tracer("http-client");
    
    let mut span = tracer
        .span_builder("Enrich Order Data")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "https://api.example.com/enrichment"),
            KeyValue::new("order.id", order.id.to_string()),
        ])
        .start(&tracer);
    
    let client = reqwest::Client::new();
    let response = client
        .get("https://api.example.com/enrichment")
        .query(&[("order_id", &order.id)])
        .send()
        .await;
    
    match response {
        Ok(resp) if resp.status().is_success() => {
            span.set_attribute(KeyValue::new("http.status_code", resp.status().as_u16() as i64));
            let enriched: Order = resp.json().await?;
            span.end();
            Ok(enriched)
        }
        Ok(resp) => {
            span.set_status(Status::error("HTTP error"));
            span.set_attribute(KeyValue::new("http.status_code", resp.status().as_u16() as i64));
            span.end();
            Err(AppError::ExternalServiceError)
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.end();
            Err(AppError::from(e))
        }
    }
}
```

### 5.2 数据库追踪

```rust
use sqlx::{PgPool, Executor};

/// 自动数据库追踪 (使用 SQLx tracing)
#[instrument(skip(pool))]
pub async fn create_user(
    pool: &PgPool,
    name: &str,
    email: &str,
) -> Result<User, sqlx::Error> {
    // SQLx 自动添加追踪信息
    let user = sqlx::query_as!(
        User,
        r#"
        INSERT INTO users (name, email, created_at)
        VALUES ($1, $2, NOW())
        RETURNING id, name, email, created_at
        "#,
        name,
        email
    )
    .fetch_one(pool)
    .await?;
    
    tracing::info!(
        user.id = %user.id,
        user.email = %email,
        "User created"
    );
    
    Ok(user)
}

/// 手动数据库追踪 (更细粒度控制)
#[instrument(skip(pool))]
pub async fn complex_query(pool: &PgPool) -> Result<Vec<Order>, sqlx::Error> {
    let tracer = global::tracer("database");
    
    let mut span = tracer
        .span_builder("Complex Order Query")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.name", "orders_db"),
            KeyValue::new("db.operation", "SELECT"),
            KeyValue::new("db.statement", "SELECT o.*, u.name FROM orders o JOIN users u ..."),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let orders = sqlx::query_as!(
        Order,
        r#"
        SELECT o.*, u.name as user_name
        FROM orders o
        JOIN users u ON o.user_id = u.id
        WHERE o.status = 'pending'
        ORDER BY o.created_at DESC
        LIMIT 100
        "#
    )
    .fetch_all(pool)
    .await?;
    
    let duration = start.elapsed();
    
    span.set_attribute(KeyValue::new("db.rows_affected", orders.len() as i64));
    span.set_attribute(KeyValue::new("db.query_time_ms", duration.as_millis() as i64));
    span.end();
    
    Ok(orders)
}
```

### 5.3 消息队列追踪

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;

/// Kafka 生产者追踪
#[instrument(skip(producer, event))]
pub async fn publish_event(
    producer: &FutureProducer,
    topic: &str,
    event: &OrderEvent,
) -> Result<(), AppError> {
    let tracer = global::tracer("kafka-producer");
    
    let mut span = tracer
        .span_builder(format!("Kafka Publish {}", topic))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "kafka"),
            KeyValue::new("messaging.destination", topic),
            KeyValue::new("messaging.destination_kind", "topic"),
            KeyValue::new("messaging.operation", "send"),
        ])
        .start(&tracer);
    
    let payload = serde_json::to_vec(event)?;
    
    let record = FutureRecord::to(topic)
        .key(&event.order_id)
        .payload(&payload);
    
    let result = producer.send(record, std::time::Duration::from_secs(5)).await;
    
    match result {
        Ok((partition, offset)) => {
            span.set_attribute(KeyValue::new("messaging.kafka.partition", partition as i64));
            span.set_attribute(KeyValue::new("messaging.kafka.offset", offset));
            span.set_attribute(KeyValue::new("messaging.message_payload_size_bytes", payload.len() as i64));
            span.end();
            Ok(())
        }
        Err((e, _)) => {
            span.set_status(Status::error(e.to_string()));
            span.end();
            Err(AppError::from(e))
        }
    }
}
```

---

## 6. 自定义指标

### 6.1 业务指标

```rust
use opentelemetry::{global, metrics::{Counter, Histogram}};

/// 业务指标收集器
pub struct BusinessMetrics {
    orders_created: Counter<u64>,
    order_value: Histogram<f64>,
    payment_success: Counter<u64>,
    payment_failed: Counter<u64>,
}

impl BusinessMetrics {
    pub fn new() -> Self {
        let meter = global::meter("business-metrics");
        
        Self {
            orders_created: meter
                .u64_counter("orders.created")
                .with_description("Total number of orders created")
                .init(),
            
            order_value: meter
                .f64_histogram("orders.value")
                .with_description("Order value distribution")
                .with_unit("USD")
                .init(),
            
            payment_success: meter
                .u64_counter("payments.success")
                .with_description("Successful payments")
                .init(),
            
            payment_failed: meter
                .u64_counter("payments.failed")
                .with_description("Failed payments")
                .init(),
        }
    }
    
    /// 记录订单创建
    pub fn record_order_created(&self, value: f64, currency: &str) {
        self.orders_created.add(
            1,
            &[KeyValue::new("currency", currency.to_string())],
        );
        
        self.order_value.record(
            value,
            &[KeyValue::new("currency", currency.to_string())],
        );
    }
    
    /// 记录支付结果
    pub fn record_payment(&self, success: bool, method: &str) {
        let attributes = vec![KeyValue::new("payment_method", method.to_string())];
        
        if success {
            self.payment_success.add(1, &attributes);
        } else {
            self.payment_failed.add(1, &attributes);
        }
    }
}
```

### 6.2 系统指标

```rust
use sysinfo::{System, SystemExt, ProcessExt};

/// 系统指标收集器
pub struct SystemMetrics {
    cpu_usage: Histogram<f64>,
    memory_usage: Histogram<f64>,
    active_connections: Counter<u64>,
}

impl SystemMetrics {
    pub fn new() -> Self {
        let meter = global::meter("system-metrics");
        
        Self {
            cpu_usage: meter
                .f64_histogram("system.cpu.usage")
                .with_description("CPU usage percentage")
                .with_unit("percent")
                .init(),
            
            memory_usage: meter
                .f64_histogram("system.memory.usage")
                .with_description("Memory usage in MB")
                .with_unit("MB")
                .init(),
            
            active_connections: meter
                .u64_counter("system.connections.active")
                .with_description("Active connections")
                .init(),
        }
    }
    
    /// 收集系统指标
    pub fn collect(&self) {
        let mut system = System::new_all();
        system.refresh_all();
        
        // CPU 使用率
        self.cpu_usage.record(
            system.global_cpu_info().cpu_usage() as f64,
            &[],
        );
        
        // 内存使用
        let memory_mb = (system.used_memory() as f64) / 1024.0 / 1024.0;
        self.memory_usage.record(memory_mb, &[]);
    }
}
```

---

## 7. 错误追踪

### 7.1 错误上报

```rust
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("External service error")]
    ExternalServiceError,
    
    #[error("Validation error: {0}")]
    Validation(String),
    
    #[error("Not found: {0}")]
    NotFound(String),
}

/// 错误处理中间件
#[instrument(skip(err))]
pub fn handle_error(err: AppError) -> (StatusCode, Json<ErrorResponse>) {
    let tracer = global::tracer("error-handler");
    let span = tracing::Span::current();
    
    // 记录错误到 Span
    span.record("error", &tracing::field::display(&err));
    span.record("error.type", &format!("{:?}", err));
    
    // 设置 OpenTelemetry Span 状态
    if let Some(otel_span) = span.extensions().get::<opentelemetry::trace::SpanContext>() {
        let mut otel_span = global::tracer("error-handler")
            .span_builder("error")
            .start(&tracer);
        
        otel_span.set_status(Status::error(err.to_string()));
        otel_span.set_attribute(KeyValue::new("error", true));
        otel_span.set_attribute(KeyValue::new("error.type", format!("{:?}", err)));
        otel_span.set_attribute(KeyValue::new("error.message", err.to_string()));
        otel_span.end();
    }
    
    let (status, message) = match err {
        AppError::Database(e) => (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()),
        AppError::ExternalServiceError => (StatusCode::BAD_GATEWAY, "External service unavailable".to_string()),
        AppError::Validation(msg) => (StatusCode::BAD_REQUEST, msg),
        AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
    };
    
    tracing::error!(
        error = %err,
        status_code = %status.as_u16(),
        "Request failed"
    );
    
    (status, Json(ErrorResponse { error: message }))
}

#[derive(serde::Serialize)]
struct ErrorResponse {
    error: String,
}
```

### 7.2 错误分组

```rust
/// 自动错误分组 (使用 fingerprint)
#[instrument]
pub fn create_error_fingerprint(err: &AppError) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let error_type = format!("{:?}", err);
    let mut hasher = DefaultHasher::new();
    error_type.hash(&mut hasher);
    
    format!("{:x}", hasher.finish())
}
```

---

## 8. 日志集成

### 8.1 结构化日志

```rust
use tracing::{info, warn, error};

/// 结构化日志示例
#[instrument(fields(
    user.id = %user_id,
    order.id = %order_id
))]
pub async fn process_order(user_id: String, order_id: String) {
    info!(
        action = "order_processing_started",
        "Starting order processing"
    );
    
    // 业务逻辑
    match validate_order(&order_id).await {
        Ok(_) => {
            info!(
                action = "order_validated",
                "Order validated successfully"
            );
        }
        Err(e) => {
            warn!(
                action = "order_validation_failed",
                error = %e,
                "Order validation failed"
            );
            return;
        }
    }
    
    info!(
        action = "order_processing_completed",
        "Order processing completed"
    );
}
```

### 8.2 日志关联

```rust
/// 日志与 Trace 自动关联
pub fn init_correlated_logging() -> anyhow::Result<()> {
    use tracing_subscriber::fmt::format::FmtSpan;
    
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(
            tracing_subscriber::fmt::layer()
                .json()
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_current_span(true)
                .with_span_list(true),
        )
        .with(tracing_opentelemetry::layer())
        .init();
    
    Ok(())
}
```

---

## 9. 性能优化

### 9.1 批量发送

```rust
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

/// 配置批量导出
pub fn create_batch_exporter() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("https://otlp.nr-data.net:4317"),
        )
        .with_batch_config(
            BatchConfig::default()
                .with_max_queue_size(2048)
                .with_max_export_batch_size(512)
                .with_scheduled_delay(Duration::from_secs(5))
                .with_max_concurrent_exports(2),
        )
        .install_batch(runtime::Tokio)?;
    
    Ok(())
}
```

### 9.2 采样策略

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision};

/// 自适应采样
pub struct AdaptiveSampler {
    base_rate: f64,
    error_threshold: f64,
}

impl AdaptiveSampler {
    pub fn new(base_rate: f64) -> Self {
        Self {
            base_rate,
            error_threshold: 0.01,
        }
    }
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::trace::SpanContext>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &opentelemetry::trace::OrderedMap<opentelemetry::Key, opentelemetry::Value>,
        links: &[opentelemetry::trace::Link],
    ) -> opentelemetry_sdk::trace::SamplingResult {
        // 错误和慢请求总是采样
        if attributes.get(&opentelemetry::Key::from_static_str("error")).is_some() {
            return opentelemetry_sdk::trace::SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            };
        }
        
        // 基于概率采样
        let random: f64 = rand::random();
        let decision = if random < self.base_rate {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        opentelemetry_sdk::trace::SamplingResult {
            decision,
            attributes: vec![],
            trace_state: Default::default(),
        }
    }
}
```

---

## 10. 告警配置

### 10.1 NRQL 告警

```sql
-- 错误率告警 (NRQL 示例)
SELECT percentage(count(*), WHERE error = true) 
FROM Span 
WHERE service.name = 'rust-app' 
SINCE 5 minutes ago

-- 响应时间 P95 告警
SELECT percentile(duration, 95) 
FROM Span 
WHERE service.name = 'rust-app' 
AND span.kind = 'server'
SINCE 5 minutes ago

-- 吞吐量告警
SELECT rate(count(*), 1 minute) 
FROM Span 
WHERE service.name = 'rust-app' 
AND http.method = 'POST'
SINCE 10 minutes ago
```

### 10.2 基线告警

```rust
/// 自动基线检测 (使用 New Relic Baseline Alerts)
/// 
/// 在 New Relic UI 配置:
/// 1. Alerts & AI > Baselines
/// 2. Select metric: transaction.duration
/// 3. Set sensitivity: Medium
/// 4. Set deviation: 3 standard deviations
```

---

## 11. 生产部署

### 11.1 Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    environment:
      NEW_RELIC_LICENSE_KEY: ${NEW_RELIC_LICENSE_KEY}
      NEW_RELIC_OTLP_ENDPOINT: https://otlp.nr-data.net:4317
      SERVICE_NAME: rust-app
      DEPLOYMENT_ENVIRONMENT: production
      RUST_LOG: info
    ports:
      - "8080:8080"
    depends_on:
      - postgres
    restart: unless-stopped

  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: app_db
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
    volumes:
      - postgres_data:/var/lib/postgresql/data

volumes:
  postgres_data:
```

### 11.2 Kubernetes

```yaml
# kubernetes/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: rust-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: NEW_RELIC_LICENSE_KEY
          valueFrom:
            secretKeyRef:
              name: newrelic-secrets
              key: license-key
        - name: NEW_RELIC_OTLP_ENDPOINT
          value: "https://otlp.nr-data.net:4317"
        - name: SERVICE_NAME
          value: "rust-app"
        - name: DEPLOYMENT_ENVIRONMENT
          value: "production"
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 30
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 10

---
apiVersion: v1
kind: Secret
metadata:
  name: newrelic-secrets
type: Opaque
data:
  license-key: <base64-encoded-key>
```

---

## 12. 国际标准对齐

### 12.1 OpenTelemetry 标准

- ✅ **W3C Trace Context**: 分布式追踪上下文传播
- ✅ **OpenTelemetry Semantic Conventions**: 标准属性命名
- ✅ **OTLP Protocol**: gRPC/HTTP 协议支持

### 12.2 New Relic 最佳实践

- ✅ **Unified Service Tagging**: 统一服务标签
- ✅ **Custom Attributes**: 业务维度标签
- ✅ **Error Tracking**: 自动错误分组和根因分析
- ✅ **NRQL Queries**: 强大的查询语言

---

## 总结

### New Relic APM 核心优势

1. **企业级稳定性**: 99.99% SLA,全球部署
2. **AI 驱动**: 自动异常检测和根因分析
3. **完整集成**: 原生支持 OpenTelemetry
4. **实时监控**: 毫秒级数据延迟
5. **强大查询**: NRQL 查询语言

### 适用场景

- ✅ 企业级应用监控
- ✅ 微服务架构
- ✅ 分布式系统
- ✅ 高并发场景
- ✅ 合规审计要求

### 性能基准

- **数据延迟**: < 1 秒
- **采样率**: 0.01-1.0 可配置
- **吞吐量**: > 10,000 spans/s
- **存储**: 8 天数据保留 (可扩展)

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
