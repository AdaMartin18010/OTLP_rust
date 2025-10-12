# Datadog APM Rust SDK 完整集成指南

## 目录

- [Datadog APM Rust SDK 完整集成指南](#datadog-apm-rust-sdk-完整集成指南)
  - [目录](#目录)
  - [1. Datadog APM 架构](#1-datadog-apm-架构)
    - [1.1 国际标准对标](#11-国际标准对标)
  - [2. Rust SDK 集成](#2-rust-sdk-集成)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 完整初始化](#22-完整初始化)
  - [3. OpenTelemetry Bridge](#3-opentelemetry-bridge)
    - [3.1 完整示例 (Axum Web 应用)](#31-完整示例-axum-web-应用)
  - [4. 高级特性](#4-高级特性)
    - [4.1 自定义 Span 标签](#41-自定义-span-标签)
    - [4.2 错误追踪](#42-错误追踪)
    - [4.3 分布式追踪传播](#43-分布式追踪传播)
  - [5. 生产部署](#5-生产部署)
    - [5.1 Datadog Agent 配置](#51-datadog-agent-配置)
    - [5.2 Docker Compose](#52-docker-compose)
    - [5.3 Kubernetes Deployment](#53-kubernetes-deployment)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 Unified Service Tagging](#61-unified-service-tagging)
    - [6.2 采样策略](#62-采样策略)
    - [6.3 性能指标](#63-性能指标)
  - [总结](#总结)

## 1. Datadog APM 架构

```text
┌─────────────────────────────────────────────────────────┐
│               Rust 应用程序                              │
│  • ddtrace-rs / OpenTelemetry                           │
│  • 自动/手动 instrumentation                             │
└─────────────────────────────────────────────────────────┘
                    │ (OTLP/HTTP)
                    ▼
┌─────────────────────────────────────────────────────────┐
│           Datadog Agent (localhost:8126)                │
│  • Trace 聚合                                           │
│  • 采样决策                                              │
│  • 指标收集                                              │
└─────────────────────────────────────────────────────────┘
                    │ (HTTPS)
                    ▼
┌─────────────────────────────────────────────────────────┐
│           Datadog 云平台                                 │
│  • APM 追踪分析                                          │
│  • 服务拓扑图                                            │
│  • 性能监控                                              │
└─────────────────────────────────────────────────────────┘
```

### 1.1 国际标准对标

| 标准 | Datadog 实现 | 文档 |
|------|--------------|------|
| **OpenTelemetry** | OTLP Exporter | [Datadog OTLP](https://docs.datadoghq.com/tracing/trace_collection/opentelemetry/rust/) |
| **Unified Service Tagging** | `env`, `service`, `version` | [UST](https://docs.datadoghq.com/getting_started/tagging/unified_service_tagging/) |
| **Semantic Conventions** | 自动映射 | [SemConv](https://opentelemetry.io/docs/specs/semconv/) |

---

## 2. Rust SDK 集成

### 2.1 Cargo.toml

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31", features = ["trace", "metrics"] }
opentelemetry-otlp = { version = "0.31", features = ["http-proto", "reqwest-client"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"

# Tracing 集成
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# Datadog 专用
opentelemetry-datadog = "0.31"  # Datadog Exporter

# Web 框架 (示例: Axum)
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
```

### 2.2 完整初始化

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, Sampler, TracerProvider},
    Resource,
    runtime,
};
use opentelemetry_datadog::DatadogPropagator;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_datadog_telemetry() -> anyhow::Result<()> {
    // 1. 设置 Datadog Propagator (支持 Datadog 和 W3C Trace Context)
    global::set_text_map_propagator(DatadogPropagator::default());

    // 2. 配置 OTLP Exporter (发送到 Datadog Agent)
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces")  // Datadog Agent OTLP 端点
                .with_headers(std::collections::HashMap::from([
                    ("DD-API-KEY".to_string(), std::env::var("DD_API_KEY")?),
                ]))
        )
        .with_trace_config(
            Config::default()
                .with_sampler(Sampler::TraceIdRatioBased(0.1))  // 10% 采样
                .with_resource(Resource::new(vec![
                    // Unified Service Tagging
                    KeyValue::new("service.name", std::env::var("DD_SERVICE").unwrap_or_else(|_| "rust-app".to_string())),
                    KeyValue::new("service.version", std::env::var("DD_VERSION").unwrap_or_else(|_| "1.0.0".to_string())),
                    KeyValue::new("deployment.environment", std::env::var("DD_ENV").unwrap_or_else(|_| "production".to_string())),
                    
                    // Datadog 特定标签
                    KeyValue::new("dd.service", std::env::var("DD_SERVICE")?),
                    KeyValue::new("dd.env", std::env::var("DD_ENV")?),
                    KeyValue::new("dd.version", std::env::var("DD_VERSION")?),
                ]))
        )
        .install_batch(runtime::Tokio)?;

    // 3. 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string())
        ))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!("Datadog telemetry initialized");

    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

---

## 3. OpenTelemetry Bridge

### 3.1 完整示例 (Axum Web 应用)

```rust
// src/main.rs
use axum::{
    routing::get,
    Router,
    extract::State,
    http::StatusCode,
    response::IntoResponse,
};
use tracing::{info, instrument};
use std::sync::Arc;

mod telemetry;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化 Datadog
    telemetry::init_datadog_telemetry()?;

    // 创建应用
    let app_state = Arc::new(AppState {
        db_pool: create_db_pool().await?,
    });

    let app = Router::new()
        .route("/", get(root_handler))
        .route("/users/:id", get(get_user))
        .with_state(app_state)
        .layer(tower_http::trace::TraceLayer::new_for_http());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("Server running at http://0.0.0.0:3000");

    axum::serve(listener, app).await?;

    // 清理
    telemetry::shutdown_telemetry();

    Ok(())
}

#[instrument]
async fn root_handler() -> impl IntoResponse {
    info!("Root handler called");
    "Hello, Datadog APM!"
}

#[instrument(skip(state), fields(user.id = %user_id))]
async fn get_user(
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<String>,
) -> Result<impl IntoResponse, StatusCode> {
    info!("Fetching user");

    // 模拟数据库查询
    let user = fetch_user_from_db(&state.db_pool, &user_id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(axum::Json(user))
}

#[instrument(skip(pool))]
async fn fetch_user_from_db(pool: &DbPool, user_id: &str) -> Result<User, DbError> {
    // 自动创建 Span: "fetch_user_from_db"
    let span = tracing::Span::current();
    span.record("db.system", "postgresql");
    span.record("db.operation", "SELECT");

    // SQLx 会自动集成 tracing
    let user = sqlx::query_as!(
        User,
        "SELECT id, name, email FROM users WHERE id = $1",
        user_id
    )
    .fetch_one(pool)
    .await?;

    Ok(user)
}

struct AppState {
    db_pool: DbPool,
}
```

---

## 4. 高级特性

### 4.1 自定义 Span 标签

```rust
use tracing::{info_span, Instrument};
use opentelemetry::{global, trace::{TraceContextExt, Tracer}, KeyValue};

#[instrument(skip(order))]
async fn process_order(order: Order) -> Result<OrderId> {
    let span = tracing::Span::current();

    // Datadog 特定标签
    span.record("order.id", &tracing::field::display(&order.id));
    span.record("order.amount", order.amount);
    span.record("customer.tier", "premium");

    // 添加 OpenTelemetry Attributes
    let otel_span = span.context().span();
    otel_span.set_attributes(vec![
        KeyValue::new("order.payment_method", "credit_card"),
        KeyValue::new("order.items_count", order.items.len() as i64),
    ]);

    // 业务逻辑
    validate_order(&order).await?;
    charge_payment(&order).await?;

    Ok(order.id)
}
```

### 4.2 错误追踪

```rust
use tracing::error;
use opentelemetry::trace::Status;

#[instrument(err)]
async fn risky_operation() -> Result<()> {
    match perform_operation().await {
        Ok(result) => Ok(result),
        Err(e) => {
            // 记录错误到 Datadog
            let span = tracing::Span::current();
            span.record("error", true);
            span.record("error.message", &tracing::field::display(&e));
            span.record("error.type", std::any::type_name::<_>());

            // OpenTelemetry Status
            let otel_span = span.context().span();
            otel_span.set_status(Status::error(e.to_string()));

            error!(error = %e, "Operation failed");
            Err(e)
        }
    }
}
```

### 4.3 分布式追踪传播

```rust
use reqwest::Client;
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;

#[instrument]
async fn call_external_service(url: &str) -> Result<Response> {
    let client = Client::new();
    let mut headers = reqwest::header::HeaderMap::new();

    // 注入 Datadog Trace Context
    let propagator = global::get_text_map_propagator();
    propagator.inject_context(
        &tracing::Span::current().context(),
        &mut HeaderInjector(&mut headers)
    );

    let response = client
        .get(url)
        .headers(headers)
        .send()
        .await?;

    Ok(response)
}

// 辅助结构
struct HeaderInjector<'a>(&'a mut reqwest::header::HeaderMap);

impl opentelemetry::propagation::Injector for HeaderInjector<'_> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}
```

---

## 5. 生产部署

### 5.1 Datadog Agent 配置

```yaml
# datadog.yaml
apm_config:
  enabled: true
  apm_non_local_traffic: true
  # 启用 OTLP 接收器
  otlp_config:
    receiver:
      protocols:
        grpc:
          endpoint: 0.0.0.0:4317
        http:
          endpoint: 0.0.0.0:4318
    # 资源属性映射
    resource_attributes_as_tags: true

logs_enabled: true
process_config:
  enabled: true

tags:
  - env:production
  - service:rust-app
```

### 5.2 Docker Compose

```yaml
version: '3.8'

services:
  app:
    build: .
    environment:
      DD_SERVICE: rust-app
      DD_ENV: production
      DD_VERSION: 1.0.0
      DD_AGENT_HOST: datadog-agent
      DD_TRACE_AGENT_PORT: 8126
      RUST_LOG: info
    depends_on:
      - datadog-agent
    ports:
      - "3000:3000"

  datadog-agent:
    image: gcr.io/datadoghq/agent:7
    environment:
      DD_API_KEY: ${DD_API_KEY}
      DD_APM_ENABLED: "true"
      DD_APM_NON_LOCAL_TRAFFIC: "true"
      DD_LOGS_ENABLED: "true"
      DD_PROCESS_AGENT_ENABLED: "true"
      DD_OTLP_CONFIG_RECEIVER_PROTOCOLS_GRPC_ENDPOINT: 0.0.0.0:4317
      DD_OTLP_CONFIG_RECEIVER_PROTOCOLS_HTTP_ENDPOINT: 0.0.0.0:4318
    ports:
      - "8126:8126"  # APM
      - "4317:4317"  # OTLP gRPC
      - "4318:4318"  # OTLP HTTP
    volumes:
      - /var/run/docker.sock:/var/run/docker.sock:ro
      - /proc/:/host/proc/:ro
      - /sys/fs/cgroup/:/host/sys/fs/cgroup:ro
```

### 5.3 Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  labels:
    tags.datadoghq.com/service: rust-app
    tags.datadoghq.com/env: production
    tags.datadoghq.com/version: "1.0.0"
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
        tags.datadoghq.com/service: rust-app
        tags.datadoghq.com/env: production
        tags.datadoghq.com/version: "1.0.0"
    spec:
      containers:
      - name: app
        image: rust-app:latest
        env:
        - name: DD_SERVICE
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/service']
        - name: DD_ENV
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/env']
        - name: DD_VERSION
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/version']
        - name: DD_AGENT_HOST
          valueFrom:
            fieldRef:
              fieldPath: status.hostIP
        ports:
        - containerPort: 3000
```

---

## 6. 最佳实践

### 6.1 Unified Service Tagging

```rust
// 环境变量
DD_SERVICE=rust-app
DD_ENV=production
DD_VERSION=1.0.0

// 在所有 Span 中自动添加
```

### 6.2 采样策略

```rust
// 生产环境: 10% 基础采样 + 100% 错误采样
use opentelemetry_sdk::trace::Sampler;

let sampler = Sampler::ParentBased(Box::new(
    Sampler::TraceIdRatioBased(0.1)  // 10% 基础采样
));

// Datadog Agent 会自动保留所有错误 Trace
```

### 6.3 性能指标

| 指标 | 目标值 | Datadog 监控 |
|------|--------|--------------|
| **P50 延迟** | < 100ms | `trace.http.request.duration{service:rust-app}.by(resource_name).p50` |
| **P99 延迟** | < 500ms | `trace.http.request.duration{service:rust-app}.by(resource_name).p99` |
| **错误率** | < 1% | `trace.http.request.errors{service:rust-app}.as_rate()` |
| **吞吐量** | > 1000 req/s | `trace.http.request.hits{service:rust-app}.as_rate()` |

---

## 总结

✅ **完整 Datadog APM 集成** (OpenTelemetry Bridge)  
✅ **分布式追踪** (Datadog + W3C Trace Context)  
✅ **统一服务标签** (UST)  
✅ **生产级部署** (Docker Compose + Kubernetes)  
✅ **最佳实践** (采样策略 + 性能监控)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
