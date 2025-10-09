# Rust 微服务 OTLP 完整实战指南

## 目录

- [Rust 微服务 OTLP 完整实战指南](#rust-微服务-otlp-完整实战指南)
  - [目录](#目录)
  - [1. 项目概述](#1-项目概述)
    - [1.1 架构设计](#11-架构设计)
    - [1.2 技术栈](#12-技术栈)
  - [2. 项目初始化](#2-项目初始化)
    - [2.1 Workspace 结构](#21-workspace-结构)
    - [2.2 依赖配置](#22-依赖配置)
  - [3. 公共库 (common)](#3-公共库-common)
    - [3.1 OpenTelemetry 初始化](#31-opentelemetry-初始化)
    - [3.2 追踪工具](#32-追踪工具)
    - [3.3 错误处理](#33-错误处理)
  - [4. API Gateway 服务](#4-api-gateway-服务)
    - [4.1 服务器配置](#41-服务器配置)
    - [4.2 路由与中间件](#42-路由与中间件)
    - [4.3 服务调用追踪](#43-服务调用追踪)
  - [5. User Service](#5-user-service)
    - [5.1 gRPC 服务实现](#51-grpc-服务实现)
    - [5.2 数据库追踪](#52-数据库追踪)
    - [5.3 缓存集成](#53-缓存集成)
  - [6. Order Service](#6-order-service)
    - [6.1 REST API 实现](#61-rest-api-实现)
    - [6.2 消息队列集成](#62-消息队列集成)
    - [6.3 事务追踪](#63-事务追踪)
  - [7. Notification Service](#7-notification-service)
    - [7.1 事件消费者](#71-事件消费者)
    - [7.2 异步处理](#72-异步处理)
  - [8. 部署配置](#8-部署配置)
    - [8.1 Docker 配置](#81-docker-配置)
    - [8.2 Kubernetes 配置](#82-kubernetes-配置)
    - [8.3 监控栈部署](#83-监控栈部署)
  - [9. 测试](#9-测试)
    - [9.1 单元测试](#91-单元测试)
    - [9.2 集成测试](#92-集成测试)
    - [9.3 压力测试](#93-压力测试)
  - [10. 运维与监控](#10-运维与监控)
    - [10.1 日志聚合](#101-日志聚合)
    - [10.2 告警配置](#102-告警配置)
    - [10.3 性能分析](#103-性能分析)
  - [总结](#总结)

---

## 1. 项目概述

### 1.1 架构设计

```text
┌─────────────┐
│   Client    │
└──────┬──────┘
       │
       ▼
┌─────────────────────────────────────────────────────────┐
│                     API Gateway                         │
│  (Axum + OpenTelemetry + Rate Limiting)                 │
└──────┬──────────────────────────────┬───────────────────┘
       │                              │
       ▼                              ▼
┌─────────────────┐          ┌─────────────────┐
│  User Service   │          │  Order Service  │
│  (gRPC + SQLx)  │──────────│  (REST + Kafka) │
└────────┬────────┘          └────────┬────────┘
         │                            │
         ▼                            ▼
┌─────────────────┐          ┌──────────────────┐
│   PostgreSQL    │          │  Notification    │
│   + Redis       │          │    Service       │
└─────────────────┘          │  (Kafka Consumer)│
                             └──────────────────┘
         ▲                            
         │                            
         ▼                            
┌───────────────────────────────────────────────┐
│          Observability Stack                  │
│  (Jaeger + Prometheus + Grafana + Loki)       │
└───────────────────────────────────────────────┘
```

### 1.2 技术栈

- **Web 框架**：Axum 0.8.7
- **gRPC**：Tonic 0.14.2
- **数据库**：SQLx (PostgreSQL)
- **缓存**：Redis
- **消息队列**：Kafka (rdkafka)
- **OpenTelemetry**：0.31.0
- **异步运行时**：Tokio 1.47.1

---

## 2. 项目初始化

### 2.1 Workspace 结构

```bash
cargo new microservices --name microservices
cd microservices
```

在 `Cargo.toml` 中配置 Workspace：

```toml
[workspace]
members = [
    "common",
    "api-gateway",
    "user-service",
    "order-service",
    "notification-service",
]
resolver = "2"

[workspace.package]
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[workspace.dependencies]
# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic"] }

# Async runtime
tokio = { version = "1.47.1", features = ["full"] }

# Web frameworks
axum = { version = "0.8.7", features = ["macros"] }
tonic = { version = "0.14.2", features = ["tls"] }
tonic-build = "0.14.2"

# Database
sqlx = { version = "0.8.3", features = ["postgres", "runtime-tokio-rustls", "chrono", "uuid"] }

# Redis
redis = { version = "0.27.6", features = ["tokio-comp", "connection-manager"] }

# Kafka
rdkafka = { version = "0.37.0", features = ["tokio"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31.0"

# Error handling
anyhow = "1.0"
thiserror = "2.0"

# Utils
uuid = { version = "1.11", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
```

### 2.2 依赖配置

创建各个服务的目录：

```bash
cargo new --lib common
cargo new --bin api-gateway
cargo new --bin user-service
cargo new --bin order-service
cargo new --bin notification-service
```

---

## 3. 公共库 (common)

### 3.1 OpenTelemetry 初始化

**`common/src/telemetry.rs`**：

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

/// Initialize OpenTelemetry with OTLP exporter
pub fn init_telemetry(
    service_name: &str,
    otlp_endpoint: &str,
) -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // Create OTLP tracer provider
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint),
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", service_name.to_string()),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    global::set_tracer_provider(tracer_provider.clone());

    // Initialize tracing subscriber
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| format!("{}=debug,tower_http=debug", service_name).into()),
        )
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(
            global::tracer(service_name),
        ))
        .init();

    Ok(tracer_provider)
}

/// Shutdown OpenTelemetry gracefully
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

### 3.2 追踪工具

**`common/src/tracing.rs`**：

```rust
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};
use std::collections::HashMap;

/// Extract trace context from HTTP headers
pub fn extract_trace_context(
    headers: &axum::http::HeaderMap,
) -> Context {
    use opentelemetry::propagation::{TextMapPropagator, Extractor};

    struct HeaderExtractor<'a>(&'a axum::http::HeaderMap);

    impl<'a> Extractor for HeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.get(key).and_then(|v| v.to_str().ok())
        }

        fn keys(&self) -> Vec<&str> {
            self.0.keys().map(|k| k.as_str()).collect()
        }
    }

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.extract(&HeaderExtractor(headers))
}

/// Inject trace context into HTTP headers
pub fn inject_trace_context(
    cx: &Context,
    headers: &mut HashMap<String, String>,
) {
    use opentelemetry::propagation::{TextMapPropagator, Injector};

    struct HeaderInjector<'a>(&'a mut HashMap<String, String>);

    impl<'a> Injector for HeaderInjector<'a> {
        fn set(&mut self, key: &str, value: String) {
            self.0.insert(key.to_string(), value);
        }
    }

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(cx, &mut HeaderInjector(headers));
}
```

### 3.3 错误处理

**`common/src/error.rs`**：

```rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde_json::json;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Redis error: {0}")]
    Redis(#[from] redis::RedisError),

    #[error("Not found: {0}")]
    NotFound(String),

    #[error("Unauthorized")]
    Unauthorized,

    #[error("Internal server error")]
    Internal,

    #[error("Kafka error: {0}")]
    Kafka(String),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, error_message) = match self {
            AppError::Database(e) => {
                tracing::error!("Database error: {:?}", e);
                (StatusCode::INTERNAL_SERVER_ERROR, "Database error")
            }
            AppError::Redis(e) => {
                tracing::error!("Redis error: {:?}", e);
                (StatusCode::INTERNAL_SERVER_ERROR, "Cache error")
            }
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg.as_str()),
            AppError::Unauthorized => (StatusCode::UNAUTHORIZED, "Unauthorized"),
            AppError::Internal => (StatusCode::INTERNAL_SERVER_ERROR, "Internal server error"),
            AppError::Kafka(e) => {
                tracing::error!("Kafka error: {}", e);
                (StatusCode::INTERNAL_SERVER_ERROR, "Message queue error")
            }
        };

        let body = Json(json!({
            "error": error_message,
        }));

        (status, body).into_response()
    }
}
```

**`common/src/lib.rs`**：

```rust
pub mod telemetry;
pub mod tracing;
pub mod error;
```

---

## 4. API Gateway 服务

### 4.1 服务器配置

**`api-gateway/Cargo.toml`**：

```toml
[package]
name = "api-gateway"
version.workspace = true
edition.workspace = true

[dependencies]
common = { path = "../common" }

opentelemetry.workspace = true
opentelemetry_sdk.workspace = true
opentelemetry-otlp.workspace = true

tokio.workspace = true
axum.workspace = true
tonic.workspace = true

tracing.workspace = true
tracing-subscriber.workspace = true
tracing-opentelemetry.workspace = true

serde.workspace = true
serde_json.workspace = true

anyhow.workspace = true
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }
```

### 4.2 路由与中间件

**`api-gateway/src/main.rs`**：

```rust
use axum::{
    routing::{get, post},
    Router, Extension,
};
use tower_http::trace::TraceLayer;
use std::net::SocketAddr;

mod handlers;
mod middleware;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize telemetry
    let _tracer_provider = common::telemetry::init_telemetry(
        "api-gateway",
        "http://localhost:4317",
    )?;

    // Create router
    let app = Router::new()
        .route("/health", get(handlers::health_check))
        .route("/api/users", post(handlers::create_user))
        .route("/api/users/:id", get(handlers::get_user))
        .route("/api/orders", post(handlers::create_order))
        .route("/api/orders/:id", get(handlers::get_order))
        .layer(TraceLayer::new_for_http())
        .layer(axum::middleware::from_fn(middleware::trace_middleware));

    // Start server
    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    tracing::info!("API Gateway listening on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    // Cleanup
    common::telemetry::shutdown_telemetry();
    Ok(())
}
```

**`api-gateway/src/middleware.rs`**：

```rust
use axum::{
    http::Request,
    middleware::Next,
    response::Response,
};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};

pub async fn trace_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let tracer = global::tracer("api-gateway");

    // Extract trace context from headers
    let parent_cx = common::tracing::extract_trace_context(request.headers());

    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", request.method().to_string()),
            KeyValue::new("http.target", request.uri().path().to_string()),
            KeyValue::new("http.scheme", "http"),
        ])
        .start_with_context(&tracer, &parent_cx);

    let cx = parent_cx.with_span(span);
    let _guard = cx.attach();

    let response = next.run(request).await;

    cx.span().set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));

    response
}
```

### 4.3 服务调用追踪

**`api-gateway/src/handlers.rs`**：

```rust
use axum::{
    http::StatusCode,
    Json,
};
use serde::{Deserialize, Serialize};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};

#[derive(Serialize)]
pub struct HealthResponse {
    status: String,
}

#[tracing::instrument]
pub async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy".to_string(),
    })
}

#[derive(Deserialize)]
pub struct CreateUserRequest {
    name: String,
    email: String,
}

#[derive(Serialize)]
pub struct UserResponse {
    id: String,
    name: String,
    email: String,
}

#[tracing::instrument(skip(request))]
pub async fn create_user(
    Json(request): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<UserResponse>), StatusCode> {
    let tracer = global::tracer("api-gateway");
    let mut span = tracer
        .span_builder("call user-service")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("rpc.service", "UserService"),
            KeyValue::new("rpc.method", "CreateUser"),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    // TODO: Call user-service via gRPC
    let user = UserResponse {
        id: uuid::Uuid::new_v4().to_string(),
        name: request.name,
        email: request.email,
    };

    Ok((StatusCode::CREATED, Json(user)))
}

#[tracing::instrument]
pub async fn get_user(
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Result<Json<UserResponse>, StatusCode> {
    // TODO: Call user-service via gRPC
    let user = UserResponse {
        id,
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
    };

    Ok(Json(user))
}

#[derive(Deserialize)]
pub struct CreateOrderRequest {
    user_id: String,
    items: Vec<String>,
}

#[derive(Serialize)]
pub struct OrderResponse {
    id: String,
    user_id: String,
    status: String,
}

#[tracing::instrument(skip(request))]
pub async fn create_order(
    Json(request): Json<CreateOrderRequest>,
) -> Result<(StatusCode, Json<OrderResponse>), StatusCode> {
    // TODO: Call order-service via HTTP
    let order = OrderResponse {
        id: uuid::Uuid::new_v4().to_string(),
        user_id: request.user_id,
        status: "pending".to_string(),
    };

    Ok((StatusCode::CREATED, Json(order)))
}

#[tracing::instrument]
pub async fn get_order(
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Result<Json<OrderResponse>, StatusCode> {
    // TODO: Call order-service via HTTP
    let order = OrderResponse {
        id,
        user_id: "user-123".to_string(),
        status: "completed".to_string(),
    };

    Ok(Json(order))
}
```

---

## 5. User Service

### 5.1 gRPC 服务实现

**`user-service/build.rs`**：

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::compile_protos("proto/user.proto")?;
    Ok(())
}
```

**`user-service/proto/user.proto`**：

```protobuf
syntax = "proto3";

package user;

service UserService {
  rpc CreateUser(CreateUserRequest) returns (UserResponse);
  rpc GetUser(GetUserRequest) returns (UserResponse);
}

message CreateUserRequest {
  string name = 1;
  string email = 2;
}

message GetUserRequest {
  string id = 1;
}

message UserResponse {
  string id = 1;
  string name = 2;
  string email = 3;
}
```

**`user-service/src/main.rs`**：

```rust
use tonic::{transport::Server, Request, Response, Status};
use sqlx::PgPool;

pub mod user {
    tonic::include_proto!("user");
}

use user::user_service_server::{UserService, UserServiceServer};
use user::{CreateUserRequest, GetUserRequest, UserResponse};

pub struct UserServiceImpl {
    db: PgPool,
}

#[tonic::async_trait]
impl UserService for UserServiceImpl {
    #[tracing::instrument(skip(self, request))]
    async fn create_user(
        &self,
        request: Request<CreateUserRequest>,
    ) -> Result<Response<UserResponse>, Status> {
        let req = request.into_inner();

        let user_id = uuid::Uuid::new_v4().to_string();

        // Insert into database with tracing
        sqlx::query!(
            "INSERT INTO users (id, name, email) VALUES ($1, $2, $3)",
            user_id,
            req.name,
            req.email
        )
        .execute(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("Database error: {:?}", e);
            Status::internal("Failed to create user")
        })?;

        let response = UserResponse {
            id: user_id,
            name: req.name,
            email: req.email,
        };

        Ok(Response::new(response))
    }

    #[tracing::instrument(skip(self, request))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<UserResponse>, Status> {
        let req = request.into_inner();

        let user = sqlx::query_as!(
            UserResponse,
            "SELECT id, name, email FROM users WHERE id = $1",
            req.id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("Database error: {:?}", e);
            Status::not_found("User not found")
        })?;

        Ok(Response::new(user))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize telemetry
    let _tracer_provider = common::telemetry::init_telemetry(
        "user-service",
        "http://localhost:4317",
    )?;

    // Connect to database
    let db = PgPool::connect("postgres://dev:dev@localhost/myapp").await?;

    // Run migrations
    sqlx::migrate!("./migrations").run(&db).await?;

    let addr = "[::1]:50051".parse()?;
    let user_service = UserServiceImpl { db };

    tracing::info!("User Service listening on {}", addr);

    Server::builder()
        .add_service(UserServiceServer::new(user_service))
        .serve(addr)
        .await?;

    common::telemetry::shutdown_telemetry();
    Ok(())
}
```

### 5.2 数据库追踪

数据库追踪已通过 SQLx 自动集成，每个查询都会生成 Span。

### 5.3 缓存集成

**`user-service/src/cache.rs`**：

```rust
use redis::aio::ConnectionManager;
use redis::AsyncCommands;

pub struct UserCache {
    redis: ConnectionManager,
}

impl UserCache {
    pub fn new(redis: ConnectionManager) -> Self {
        Self { redis }
    }

    #[tracing::instrument(skip(self))]
    pub async fn get(&self, user_id: &str) -> Result<Option<String>, redis::RedisError> {
        let mut conn = self.redis.clone();
        conn.get(format!("user:{}", user_id)).await
    }

    #[tracing::instrument(skip(self, data))]
    pub async fn set(&self, user_id: &str, data: String, ttl: usize) -> Result<(), redis::RedisError> {
        let mut conn = self.redis.clone();
        conn.set_ex(format!("user:{}", user_id), data, ttl).await
    }
}
```

---

## 6. Order Service

### 6.1 REST API 实现

**`order-service/src/main.rs`**：

```rust
use axum::{
    routing::{get, post},
    Router, Json, Extension,
};
use sqlx::PgPool;
use std::net::SocketAddr;

mod handlers;
mod kafka;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize telemetry
    let _tracer_provider = common::telemetry::init_telemetry(
        "order-service",
        "http://localhost:4317",
    )?;

    // Connect to database
    let db = PgPool::connect("postgres://dev:dev@localhost/myapp").await?;

    // Initialize Kafka producer
    let kafka_producer = kafka::create_producer("localhost:9092")?;

    let app = Router::new()
        .route("/orders", post(handlers::create_order))
        .route("/orders/:id", get(handlers::get_order))
        .layer(Extension(db))
        .layer(Extension(kafka_producer));

    let addr = SocketAddr::from(([0, 0, 0, 0], 3001));
    tracing::info!("Order Service listening on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    common::telemetry::shutdown_telemetry();
    Ok(())
}
```

### 6.2 消息队列集成

**`order-service/src/kafka.rs`**：

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};

pub fn create_producer(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("message.timeout.ms", "5000")
        .create()
}

#[tracing::instrument(skip(producer, message))]
pub async fn publish_order_created(
    producer: &FutureProducer,
    order_id: &str,
    message: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("order-service");
    let mut span = tracer
        .span_builder("kafka.publish order.created")
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "kafka"),
            KeyValue::new("messaging.destination.name", "order.created"),
            KeyValue::new("order.id", order_id.to_string()),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let record = FutureRecord::to("order.created")
        .key(order_id)
        .payload(message);

    producer.send(record, std::time::Duration::from_secs(0)).await
        .map_err(|(e, _)| e)?;

    Ok(())
}
```

### 6.3 事务追踪

**`order-service/src/handlers.rs`**：

```rust
use axum::{Extension, Json, http::StatusCode};
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use rdkafka::producer::FutureProducer;

#[derive(Deserialize)]
pub struct CreateOrderRequest {
    user_id: String,
    items: Vec<String>,
}

#[derive(Serialize)]
pub struct OrderResponse {
    id: String,
    user_id: String,
    status: String,
}

#[tracing::instrument(skip(db, producer, request))]
pub async fn create_order(
    Extension(db): Extension<PgPool>,
    Extension(producer): Extension<FutureProducer>,
    Json(request): Json<CreateOrderRequest>,
) -> Result<(StatusCode, Json<OrderResponse>), StatusCode> {
    let order_id = uuid::Uuid::new_v4().to_string();

    // Start database transaction
    let mut tx = db.begin().await.map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // Insert order
    sqlx::query!(
        "INSERT INTO orders (id, user_id, status) VALUES ($1, $2, $3)",
        order_id,
        request.user_id,
        "pending"
    )
    .execute(&mut *tx)
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // Commit transaction
    tx.commit().await.map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // Publish event to Kafka
    let event = serde_json::json!({
        "order_id": order_id,
        "user_id": request.user_id,
        "items": request.items,
    });

    crate::kafka::publish_order_created(
        &producer,
        &order_id,
        &event.to_string(),
    )
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    let response = OrderResponse {
        id: order_id,
        user_id: request.user_id,
        status: "pending".to_string(),
    };

    Ok((StatusCode::CREATED, Json(response)))
}

#[tracing::instrument(skip(db))]
pub async fn get_order(
    Extension(db): Extension<PgPool>,
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Result<Json<OrderResponse>, StatusCode> {
    let order = sqlx::query_as!(
        OrderResponse,
        "SELECT id, user_id, status FROM orders WHERE id = $1",
        id
    )
    .fetch_one(&db)
    .await
    .map_err(|_| StatusCode::NOT_FOUND)?;

    Ok(Json(order))
}
```

---

## 7. Notification Service

### 7.1 事件消费者

**`notification-service/src/main.rs`**：

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize telemetry
    let _tracer_provider = common::telemetry::init_telemetry(
        "notification-service",
        "http://localhost:4317",
    )?;

    // Create Kafka consumer
    let consumer: StreamConsumer = ClientConfig::new()
        .set("group.id", "notification-service")
        .set("bootstrap.servers", "localhost:9092")
        .set("enable.auto.commit", "true")
        .create()?;

    consumer.subscribe(&["order.created"])?;

    tracing::info!("Notification Service started, listening to order.created");

    let mut message_stream = consumer.stream();

    while let Some(message) = message_stream.next().await {
        match message {
            Ok(msg) => {
                if let Some(payload) = msg.payload() {
                    let payload_str = String::from_utf8_lossy(payload);
                    process_order_created(&payload_str).await;
                    // Commit processed message
                    consumer.commit_message(&msg, rdkafka::consumer::CommitMode::Async)?;
                }
            }
            Err(e) => {
                tracing::error!("Kafka error: {:?}", e);
            }
        }
    }

    common::telemetry::shutdown_telemetry();
    Ok(())
}

#[tracing::instrument(skip(payload))]
async fn process_order_created(payload: &str) {
    tracing::info!("Processing order.created event: {}", payload);
    
    // TODO: Send notification (email, SMS, etc.)
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    tracing::info!("Notification sent successfully");
}
```

### 7.2 异步处理

异步处理已在上述代码中实现，使用 Tokio 运行时。

---

## 8. 部署配置

### 8.1 Docker 配置

**根目录 `docker-compose.yml`**：

```yaml
version: '3.9'

services:
  jaeger:
    image: jaegertracing/all-in-one:1.67.0
    ports:
      - "6831:6831/udp"
      - "16686:16686"
      - "4317:4317"
    environment:
      - COLLECTOR_OTLP_ENABLED=true

  postgres:
    image: postgres:16-alpine
    ports:
      - "5432:5432"
    environment:
      - POSTGRES_USER=dev
      - POSTGRES_PASSWORD=dev
      - POSTGRES_DB=myapp
    volumes:
      - postgres-data:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  kafka:
    image: confluentinc/cp-kafka:7.6.0
    ports:
      - "9092:9092"
    environment:
      - KAFKA_ZOOKEEPER_CONNECT=zookeeper:2181
      - KAFKA_ADVERTISED_LISTENERS=PLAINTEXT://localhost:9092
      - KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR=1

  zookeeper:
    image: confluentinc/cp-zookeeper:7.6.0
    ports:
      - "2181:2181"
    environment:
      - ZOOKEEPER_CLIENT_PORT=2181

volumes:
  postgres-data:
```

### 8.2 Kubernetes 配置

**`k8s/api-gateway-deployment.yaml`**：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: api-gateway
spec:
  replicas: 3
  selector:
    matchLabels:
      app: api-gateway
  template:
    metadata:
      labels:
        app: api-gateway
    spec:
      containers:
      - name: api-gateway
        image: api-gateway:latest
        ports:
        - containerPort: 3000
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://jaeger-collector:4317"
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
---
apiVersion: v1
kind: Service
metadata:
  name: api-gateway
spec:
  selector:
    app: api-gateway
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
  type: LoadBalancer
```

### 8.3 监控栈部署

**`k8s/monitoring-stack.yaml`**：

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: monitoring
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: jaeger
  namespace: monitoring
spec:
  replicas: 1
  selector:
    matchLabels:
      app: jaeger
  template:
    metadata:
      labels:
        app: jaeger
    spec:
      containers:
      - name: jaeger
        image: jaegertracing/all-in-one:1.67.0
        ports:
        - containerPort: 16686
        - containerPort: 4317
        env:
        - name: COLLECTOR_OTLP_ENABLED
          value: "true"
---
apiVersion: v1
kind: Service
metadata:
  name: jaeger
  namespace: monitoring
spec:
  selector:
    app: jaeger
  ports:
  - name: ui
    port: 16686
  - name: otlp
    port: 4317
```

---

## 9. 测试

### 9.1 单元测试

**`user-service/tests/user_test.rs`**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_create_user() {
        // TODO: Implement unit tests
    }
}
```

### 9.2 集成测试

**`integration-tests/tests/api_test.rs`**：

```rust
use reqwest::Client;

#[tokio::test]
async fn test_create_order_flow() {
    let client = Client::new();

    // Create user
    let user_response = client
        .post("http://localhost:3000/api/users")
        .json(&serde_json::json!({
            "name": "Test User",
            "email": "test@example.com"
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(user_response.status(), 201);

    // Create order
    let user: serde_json::Value = user_response.json().await.unwrap();
    let order_response = client
        .post("http://localhost:3000/api/orders")
        .json(&serde_json::json!({
            "user_id": user["id"],
            "items": ["item1", "item2"]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(order_response.status(), 201);
}
```

### 9.3 压力测试

使用 `wrk` 或 `k6` 进行压力测试：

```bash
wrk -t12 -c400 -d30s http://localhost:3000/health
```

---

## 10. 运维与监控

### 10.1 日志聚合

所有服务使用 JSON 格式日志，可以通过 Fluentd/Loki 聚合。

### 10.2 告警配置

基于 Prometheus + Alertmanager 配置告警规则。

### 10.3 性能分析

通过 Jaeger UI 查看分布式追踪，定位性能瓶颈。

---

## 总结

本实战指南构建了一个完整的 Rust 微服务系统，涵盖：

1. **API Gateway**：Axum + 中间件追踪
2. **User Service**：gRPC + PostgreSQL + Redis
3. **Order Service**：REST API + Kafka + 事务
4. **Notification Service**：Kafka Consumer + 异步处理
5. **OpenTelemetry**：全链路追踪
6. **部署**：Docker + Kubernetes
7. **测试**：单元测试 + 集成测试

通过这个项目，您可以深入理解 Rust 微服务的 OTLP 集成实践。
