# Actix-web 4.9 OTLP 完整集成指南

> **框架地位**: 🚀 世界最快 Rust Web 框架 (GitHub 21.9k stars)  
> **性能基准**: TechEmpower Benchmark Top 10 (Plaintext/JSON/Database)  
> **Actix-web 版本**: 4.9.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **完整示例**: RESTful API + gRPC + WebSocket + SSE

---

## 📋 目录

- [Actix-web 4.9 OTLP 完整集成指南](#actix-web-49-otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [🌟 Actix-web 概述](#-actix-web-概述)
    - [为什么选择 Actix-web?](#为什么选择-actix-web)
    - [国际标准对标](#国际标准对标)
  - [🎯 核心特性](#-核心特性)
    - [1. Actor 模型](#1-actor-模型)
    - [2. 中间件系统](#2-中间件系统)
    - [3. Extractor 系统](#3-extractor-系统)
  - [🔭 OTLP 集成策略](#-otlp-集成策略)
    - [集成点](#集成点)
  - [📦 完整 RESTful API 示例](#-完整-restful-api-示例)
    - [1. 项目初始化](#1-项目初始化)
    - [2. OTLP 中间件](#2-otlp-中间件)
    - [3. 错误处理](#3-错误处理)
    - [4. Handler 实现](#4-handler-实现)
    - [5. Database 集成 (SQLx)](#5-database-集成-sqlx)
    - [6. 主应用](#6-主应用)
  - [🔌 高级特性集成](#-高级特性集成)
    - [1. gRPC 集成 (Tonic)](#1-grpc-集成-tonic)
    - [2. WebSocket 追踪](#2-websocket-追踪)
    - [3. Server-Sent Events (SSE)](#3-server-sent-events-sse)
  - [📊 性能优化](#-性能优化)
    - [1. 连接池优化](#1-连接池优化)
    - [2. Actix-web Workers](#2-actix-web-workers)
    - [3. 异步 Span 优化](#3-异步-span-优化)
  - [🧪 测试策略](#-测试策略)
    - [集成测试](#集成测试)
  - [🚀 生产部署](#-生产部署)
    - [Cargo.toml](#cargotoml)
    - [Docker Compose](#docker-compose)
    - [Dockerfile](#dockerfile)
  - [✅ 最佳实践](#-最佳实践)
    - [Actix-web 设计](#actix-web-设计)
    - [OTLP 集成](#otlp-集成)
    - [性能优化](#性能优化)

---

## 🌟 Actix-web 概述

### 为什么选择 Actix-web?

**Actix-web** 是基于 Actor 模型的高性能 Web 框架,在 TechEmpower Benchmark 中排名前列。

```text
TechEmpower Benchmark (Round 22):
┌────────────────────────────────────────────┐
│ Framework        │ Requests/sec │ Latency  │
├──────────────────┼──────────────┼──────────┤
│ Actix-web (Rust) │   7,041,235  │  0.14ms  │
│ Spring (Java)    │     481,089  │  2.08ms  │
│ Django (Python)  │      29,456  │ 34.00ms  │
│ Express (Node)   │     122,342  │  8.17ms  │
└────────────────────────────────────────────┘
```

**核心优势**:

- ✅ **极致性能**: 700万+ RPS (Plaintext)
- ✅ **Actor 模型**: 高并发、消息驱动
- ✅ **类型安全**: Compile-time 保证
- ✅ **零成本抽象**: 无运行时开销
- ✅ **生态丰富**: 21.9k stars, 活跃社区

### 国际标准对标

| 标准/来源 | 内容 |
|----------|------|
| **官方文档** | [actix.rs](https://actix.rs) |
| **GitHub** | [actix/actix-web](https://github.com/actix/actix-web) (21.9k stars) |
| **TechEmpower** | [Benchmark Results](https://www.techempower.com/benchmarks/) (Top 10) |
| **Actor 模型** | Carl Hewitt (1973) - Erlang/Akka 同源 |
| **比较对象** | Rocket (Rust), Axum (Rust), Spring Boot (Java), Express (Node.js) |

---

## 🎯 核心特性

### 1. Actor 模型

```rust
/// Actix Actor 示例
use actix::prelude::*;

#[derive(Message)]
#[rtype(result = "Result<String, ()>")]
struct GetUser(String);

struct UserActor;

impl Actor for UserActor {
    type Context = Context<Self>;
}

impl Handler<GetUser> for UserActor {
    type Result = Result<String, ()>;
    
    fn handle(&mut self, msg: GetUser, _ctx: &mut Context<Self>) -> Self::Result {
        Ok(format!("User: {}", msg.0))
    }
}
```

### 2. 中间件系统

```rust
/// Actix-web 中间件
use actix_web::{
    dev::{Service, ServiceRequest, ServiceResponse, Transform},
    Error, HttpMessage,
};
use std::future::{ready, Ready, Future};
use std::pin::Pin;

pub struct TracingMiddleware;

impl<S, B> Transform<S, ServiceRequest> for TracingMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = TracingMiddlewareService<S>;
    type InitError = ();
    type Future = Ready<Result<Self::Transform, Self::InitError>>;
    
    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(TracingMiddlewareService { service }))
    }
}
```

### 3. Extractor 系统

```rust
/// Actix-web Extractor (类型安全)
use actix_web::{web, HttpResponse};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct CreateUserRequest {
    name: String,
    email: String,
}

async fn create_user(
    user: web::Json<CreateUserRequest>,  // JSON Extractor
    db: web::Data<DbPool>,               // Shared State
    path: web::Path<String>,             // Path Parameter
) -> HttpResponse {
    // Type-safe extraction!
}
```

---

## 🔭 OTLP 集成策略

### 集成点

```text
Request Flow with OTLP:
┌─────────────────────────────────────────────────────┐
│  1. HTTP Request                                    │
│     ↓                                               │
│  2. TracingMiddleware (创建 Root Span)             │
│     ├─ extract trace context (W3C)                 │
│     ├─ create span                                 │
│     └─ inject into extensions                      │
│     ↓                                               │
│  3. Router Matching                                 │
│     ↓                                               │
│  4. Extractors (Path/Query/Json)                   │
│     ↓                                               │
│  5. Handler (#[instrument])                        │
│     ├─ business logic span                         │
│     ├─ database query span                         │
│     └─ external API call span                      │
│     ↓                                               │
│  6. Response                                        │
│     └─ TracingMiddleware (finalize span)          │
└─────────────────────────────────────────────────────┘
```

**关键点**:

1. **中间件层**: 自动创建 HTTP Span
2. **Handler 层**: `#[instrument]` 宏
3. **Database 层**: SQLx 集成
4. **外部调用**: HTTP Client 追踪

---

## 📦 完整 RESTful API 示例

### 1. 项目初始化

```toml
# Cargo.toml
[package]
name = "actix-otlp-example"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Actix-web
actix-web = "4.9"
actix-rt = "2.10"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"
tracing-actix-web = "0.7"  # Actix-web 专用追踪

# Database
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "uuid"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Error Handling
anyhow = "1.0"
thiserror = "2.0"

# Utilities
uuid = { version = "1.11", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
```

### 2. OTLP 中间件

```rust
// src/middleware/tracing.rs
use actix_web::{
    dev::{Service, ServiceRequest, ServiceResponse, Transform},
    Error, HttpMessage,
};
use futures_util::future::LocalBoxFuture;
use std::future::{ready, Ready};
use tracing::{Span, instrument};
use opentelemetry::trace::{TraceContextExt, SpanKind};
use opentelemetry::KeyValue;

/// Actix-web OTLP 中间件
pub struct OtlpMiddleware;

impl<S, B> Transform<S, ServiceRequest> for OtlpMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = OtlpMiddlewareService<S>;
    type InitError = ();
    type Future = Ready<Result<Self::Transform, Self::InitError>>;
    
    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(OtlpMiddlewareService { service }))
    }
}

pub struct OtlpMiddlewareService<S> {
    service: S,
}

impl<S, B> Service<ServiceRequest> for OtlpMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;
    
    actix_web::dev::forward_ready!(service);
    
    fn call(&self, req: ServiceRequest) -> Self::Future {
        use tracing_actix_web::RootSpanBuilder;
        
        // 提取 W3C Trace Context
        let trace_parent = req.headers()
            .get("traceparent")
            .and_then(|v| v.to_str().ok())
            .map(|s| s.to_string());
        
        // 创建 Root Span
        let span = tracing::info_span!(
            "HTTP request",
            otel.kind = ?SpanKind::Server,
            http.method = %req.method(),
            http.target = %req.path(),
            http.route = %req.path(),
            http.scheme = %req.connection_info().scheme(),
            http.host = %req.connection_info().host(),
            http.client_ip = ?req.peer_addr(),
            trace.parent = ?trace_parent,
        );
        
        // 将 Span 注入 Request Extensions
        req.extensions_mut().insert(span.clone());
        
        let fut = self.service.call(req);
        
        Box::pin(async move {
            let _enter = span.enter();
            
            let start = std::time::Instant::now();
            let res = fut.await;
            let duration = start.elapsed();
            
            match &res {
                Ok(response) => {
                    span.record("http.status_code", response.status().as_u16());
                    span.record("http.response_time_ms", duration.as_millis() as u64);
                    
                    if response.status().is_server_error() {
                        tracing::error!(
                            status = response.status().as_u16(),
                            "Server error"
                        );
                    }
                }
                Err(err) => {
                    span.record("error", true);
                    span.record("error.message", err.to_string());
                    tracing::error!(error = %err, "Request error");
                }
            }
            
            res
        })
    }
}
```

### 3. 错误处理

```rust
// src/error.rs
use actix_web::{error::ResponseError, http::StatusCode, HttpResponse};
use thiserror::Error;
use serde::Serialize;

#[derive(Debug, Error)]
pub enum ApiError {
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Internal server error: {0}")]
    InternalError(String),
    
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
}

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    message: String,
}

impl ResponseError for ApiError {
    fn status_code(&self) -> StatusCode {
        match self {
            Self::NotFound(_) => StatusCode::NOT_FOUND,
            Self::BadRequest(_) => StatusCode::BAD_REQUEST,
            Self::InternalError(_) => StatusCode::INTERNAL_SERVER_ERROR,
            Self::DatabaseError(_) => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
    
    fn error_response(&self) -> HttpResponse {
        HttpResponse::build(self.status_code()).json(ErrorResponse {
            error: self.status_code().to_string(),
            message: self.to_string(),
        })
    }
}
```

### 4. Handler 实现

```rust
// src/handlers/users.rs
use actix_web::{web, HttpResponse, Result};
use tracing::{instrument, info, error};
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use sqlx::PgPool;
use crate::error::ApiError;

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

#[derive(Debug, Serialize)]
pub struct UserResponse {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

/// 创建用户
#[instrument(
    skip(db, user),
    fields(
        otel.kind = "server",
        http.route = "/api/users",
        user.email = %user.email
    )
)]
pub async fn create_user(
    user: web::Json<CreateUserRequest>,
    db: web::Data<PgPool>,
) -> Result<HttpResponse, ApiError> {
    info!(name = %user.name, email = %user.email, "Creating user");
    
    let user_id = Uuid::new_v4().to_string();
    
    let result = sqlx::query!(
        r#"
        INSERT INTO users (id, name, email, created_at)
        VALUES ($1, $2, $3, NOW())
        RETURNING id, name, email, created_at
        "#,
        user_id,
        user.name,
        user.email
    )
    .fetch_one(db.get_ref())
    .await?;
    
    info!(user_id = %result.id, "User created successfully");
    
    Ok(HttpResponse::Created().json(UserResponse {
        id: result.id,
        name: result.name,
        email: result.email,
        created_at: result.created_at.and_utc(),
    }))
}

/// 获取用户
#[instrument(
    skip(db),
    fields(
        otel.kind = "server",
        http.route = "/api/users/{id}",
        user.id = %user_id
    )
)]
pub async fn get_user(
    user_id: web::Path<String>,
    db: web::Data<PgPool>,
) -> Result<HttpResponse, ApiError> {
    info!(user_id = %user_id, "Fetching user");
    
    let user = sqlx::query!(
        r#"
        SELECT id, name, email, created_at
        FROM users
        WHERE id = $1
        "#,
        user_id.as_str()
    )
    .fetch_optional(db.get_ref())
    .await?
    .ok_or_else(|| ApiError::NotFound(format!("User {} not found", user_id)))?;
    
    info!(user_id = %user.id, "User fetched successfully");
    
    Ok(HttpResponse::Ok().json(UserResponse {
        id: user.id,
        name: user.name,
        email: user.email,
        created_at: user.created_at.and_utc(),
    }))
}

/// 列出用户
#[instrument(
    skip(db),
    fields(otel.kind = "server", http.route = "/api/users")
)]
pub async fn list_users(
    db: web::Data<PgPool>,
) -> Result<HttpResponse, ApiError> {
    info!("Listing users");
    
    let users = sqlx::query!(
        r#"
        SELECT id, name, email, created_at
        FROM users
        ORDER BY created_at DESC
        LIMIT 100
        "#
    )
    .fetch_all(db.get_ref())
    .await?;
    
    let response: Vec<UserResponse> = users
        .into_iter()
        .map(|u| UserResponse {
            id: u.id,
            name: u.name,
            email: u.email,
            created_at: u.created_at.and_utc(),
        })
        .collect();
    
    info!(count = response.len(), "Users listed successfully");
    
    Ok(HttpResponse::Ok().json(response))
}

/// 删除用户
#[instrument(
    skip(db),
    fields(
        otel.kind = "server",
        http.route = "/api/users/{id}",
        user.id = %user_id
    )
)]
pub async fn delete_user(
    user_id: web::Path<String>,
    db: web::Data<PgPool>,
) -> Result<HttpResponse, ApiError> {
    info!(user_id = %user_id, "Deleting user");
    
    let result = sqlx::query!(
        r#"DELETE FROM users WHERE id = $1"#,
        user_id.as_str()
    )
    .execute(db.get_ref())
    .await?;
    
    if result.rows_affected() == 0 {
        return Err(ApiError::NotFound(format!("User {} not found", user_id)));
    }
    
    info!(user_id = %user_id, "User deleted successfully");
    
    Ok(HttpResponse::NoContent().finish())
}
```

### 5. Database 集成 (SQLx)

```rust
// src/db.rs
use sqlx::{postgres::PgPoolOptions, PgPool};
use tracing::info;
use anyhow::Result;

/// 初始化数据库连接池
pub async fn init_pool(database_url: &str) -> Result<PgPool> {
    info!(database_url = database_url, "Initializing database pool");
    
    let pool = PgPoolOptions::new()
        .max_connections(50)
        .min_connections(5)
        .acquire_timeout(std::time::Duration::from_secs(5))
        .connect(database_url)
        .await?;
    
    info!("Database pool initialized successfully");
    
    // 运行 migrations
    sqlx::migrate!("./migrations")
        .run(&pool)
        .await?;
    
    info!("Database migrations completed");
    
    Ok(pool)
}
```

**Migrations** (`migrations/001_create_users.sql`):

```sql
-- migrations/001_create_users.sql
CREATE TABLE IF NOT EXISTS users (
    id VARCHAR(255) PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_created_at ON users(created_at);
```

### 6. 主应用

```rust
// src/main.rs
use actix_web::{web, App, HttpServer, middleware};
use tracing::{info, Level};
use anyhow::Result;

mod middleware;
mod handlers;
mod error;
mod db;

use middleware::tracing::OtlpMiddleware;
use handlers::users;

#[actix_web::main]
async fn main() -> Result<()> {
    // 初始化 OTLP
    init_otlp()?;
    
    // 初始化数据库
    let database_url = std::env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://user:pass@localhost/actix_db".to_string());
    let db_pool = db::init_pool(&database_url).await?;
    
    info!("Starting Actix-web server on http://0.0.0.0:8080");
    
    HttpServer::new(move || {
        App::new()
            // Shared State
            .app_data(web::Data::new(db_pool.clone()))
            
            // Middleware
            .wrap(middleware::Logger::default())
            .wrap(OtlpMiddleware)
            
            // Routes
            .service(
                web::scope("/api")
                    .route("/users", web::post().to(users::create_user))
                    .route("/users", web::get().to(users::list_users))
                    .route("/users/{id}", web::get().to(users::get_user))
                    .route("/users/{id}", web::delete().to(users::delete_user))
            )
            
            // Health check
            .route("/health", web::get().to(|| async { "OK" }))
    })
    .workers(num_cpus::get())
    .bind(("0.0.0.0", 8080))?
    .run()
    .await?;
    
    Ok(())
}

fn init_otlp() -> Result<()> {
    use opentelemetry::trace::TracerProvider;
    use opentelemetry_sdk::trace::{self, Sampler};
    use opentelemetry_otlp::WithExportConfig;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    // OTLP Exporter
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint)
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "actix-web-api"),
                    opentelemetry::KeyValue::new("service.version", "0.1.0"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // Tracing Subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info,actix_web=debug".into())
        ))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer.tracer("actix-web-api")))
        .init();
    
    info!("OTLP initialized with endpoint: {}", otlp_endpoint);
    Ok(())
}
```

---

## 🔌 高级特性集成

### 1. gRPC 集成 (Tonic)

```rust
// src/grpc/server.rs
use tonic::{transport::Server, Request, Response, Status};
use tracing::{instrument, info};

// Proto 定义
pub mod user_service {
    tonic::include_proto!("user");
}

use user_service::{
    user_service_server::{UserService, UserServiceServer},
    GetUserRequest, UserResponse,
};

pub struct UserServiceImpl {
    db: sqlx::PgPool,
}

#[tonic::async_trait]
impl UserService for UserServiceImpl {
    #[instrument(skip(self), fields(otel.kind = "server", rpc.service = "UserService"))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<UserResponse>, Status> {
        let user_id = &request.get_ref().id;
        info!(user_id = %user_id, "gRPC: GetUser");
        
        let user = sqlx::query!(
            "SELECT id, name, email FROM users WHERE id = $1",
            user_id
        )
        .fetch_optional(&self.db)
        .await
        .map_err(|e| Status::internal(e.to_string()))?
        .ok_or_else(|| Status::not_found("User not found"))?;
        
        Ok(Response::new(UserResponse {
            id: user.id,
            name: user.name,
            email: user.email,
        }))
    }
}

/// 启动 gRPC 服务器 (与 Actix-web 并行)
pub async fn start_grpc_server(db: sqlx::PgPool) -> Result<(), Box<dyn std::error::Error>> {
    let addr = "0.0.0.0:50051".parse()?;
    let user_service = UserServiceImpl { db };
    
    info!("Starting gRPC server on {}", addr);
    
    Server::builder()
        .add_service(UserServiceServer::new(user_service))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 2. WebSocket 追踪

```rust
// src/handlers/websocket.rs
use actix_web::{web, HttpRequest, HttpResponse, Error};
use actix_ws::{Message, Session};
use tracing::{instrument, info, warn};
use futures_util::StreamExt;

#[instrument(skip(req, stream), fields(otel.kind = "server", ws.connection_id = %uuid::Uuid::new_v4()))]
pub async fn websocket_handler(
    req: HttpRequest,
    stream: web::Payload,
) -> Result<HttpResponse, Error> {
    info!("WebSocket connection request");
    
    let (response, mut session, mut msg_stream) = actix_ws::handle(&req, stream)?;
    
    actix_web::rt::spawn(async move {
        info!("WebSocket connected");
        
        while let Some(Ok(msg)) = msg_stream.next().await {
            match msg {
                Message::Text(text) => {
                    info!(message = %text, "Received WebSocket message");
                    
                    // Echo
                    if session.text(text).await.is_err() {
                        warn!("Failed to send WebSocket message");
                        break;
                    }
                }
                Message::Ping(bytes) => {
                    let _ = session.pong(&bytes).await;
                }
                Message::Close(reason) => {
                    info!(?reason, "WebSocket closed");
                    break;
                }
                _ => {}
            }
        }
        
        info!("WebSocket disconnected");
    });
    
    Ok(response)
}
```

### 3. Server-Sent Events (SSE)

```rust
// src/handlers/sse.rs
use actix_web::{web, HttpResponse, Result};
use actix_web_lab::sse;
use tracing::{instrument, info};
use futures_util::stream;
use std::time::Duration;

#[instrument(fields(otel.kind = "server", http.route = "/api/events"))]
pub async fn sse_handler() -> Result<HttpResponse> {
    info!("SSE connection established");
    
    let event_stream = stream::iter(0..10).then(|i| async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        
        info!(event_id = i, "Sending SSE event");
        
        sse::Event::Data(
            sse::Data::new(format!("Event {}", i))
                .id(i.to_string())
                .event("message")
        )
    });
    
    Ok(sse::Sse::from_stream(event_stream).into())
}
```

---

## 📊 性能优化

### 1. 连接池优化

```rust
// src/db.rs (优化版)
pub async fn init_pool_optimized(database_url: &str) -> Result<PgPool> {
    let pool = PgPoolOptions::new()
        .max_connections(100)              // 增加连接数
        .min_connections(10)
        .acquire_timeout(Duration::from_secs(3))
        .idle_timeout(Duration::from_secs(600))
        .max_lifetime(Duration::from_secs(1800))
        .test_before_acquire(true)         // 健康检查
        .connect(database_url)
        .await?;
    
    Ok(pool)
}
```

### 2. Actix-web Workers

```rust
// src/main.rs (优化版)
HttpServer::new(move || {
    App::new()
        .app_data(web::Data::new(db_pool.clone()))
        .wrap(OtlpMiddleware)
        // ... routes
})
.workers(num_cpus::get())                  // 多 Worker
.backlog(8192)                             // 增加 Backlog
.keep_alive(Duration::from_secs(75))       // Keep-Alive
.client_request_timeout(Duration::from_secs(30))
.bind(("0.0.0.0", 8080))?
.run()
.await?;
```

### 3. 异步 Span 优化

```rust
// 避免跨 await 持有 Span guard
#[instrument(skip(db))]
pub async fn optimized_handler(db: web::Data<PgPool>) -> Result<HttpResponse> {
    // ✅ Good: Span 自动管理
    let result = sqlx::query!("SELECT * FROM users")
        .fetch_all(db.get_ref())
        .await?;
    
    Ok(HttpResponse::Ok().json(result))
}

// ❌ Bad: 手动管理 guard
pub async fn bad_handler(db: web::Data<PgPool>) -> Result<HttpResponse> {
    let span = tracing::info_span!("bad_handler");
    let _guard = span.enter();  // ❌ 跨 await 持有
    
    let result = sqlx::query!("SELECT * FROM users")
        .fetch_all(db.get_ref())
        .await?;
    
    Ok(HttpResponse::Ok().json(result))
}
```

---

## 🧪 测试策略

### 集成测试

```rust
// tests/integration_test.rs
use actix_web::{test, App};
use actix_otlp_example::{handlers, middleware};

#[actix_web::test]
async fn test_create_user() {
    let db = init_test_db().await;
    
    let app = test::init_service(
        App::new()
            .app_data(web::Data::new(db.clone()))
            .wrap(middleware::OtlpMiddleware)
            .route("/api/users", web::post().to(handlers::users::create_user))
    ).await;
    
    let req = test::TestRequest::post()
        .uri("/api/users")
        .set_json(&serde_json::json!({
            "name": "Test User",
            "email": "test@example.com"
        }))
        .to_request();
    
    let resp = test::call_service(&app, req).await;
    
    assert!(resp.status().is_success());
}

async fn init_test_db() -> sqlx::PgPool {
    sqlx::PgPoolOptions::new()
        .connect("postgres://test:test@localhost/test_db")
        .await
        .unwrap()
}
```

---

## 🚀 生产部署

### Cargo.toml

```toml
[package]
name = "actix-otlp-example"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
actix-web = "4.9"
actix-rt = "2.10"
actix-ws = "0.3"  # WebSocket
actix-web-lab = "0.22"  # SSE

opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"
tracing-actix-web = "0.7"

sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "uuid", "migrate"] }

tonic = "0.12"  # gRPC
prost = "0.13"

serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "2.0"
uuid = { version = "1.11", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
futures-util = "0.3"
num_cpus = "1.16"

[dev-dependencies]
actix-web-test = "0.1"
```

### Docker Compose

```yaml
# docker-compose.yml
version: '3.9'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: actix_db
      POSTGRES_USER: actix_user
      POSTGRES_PASSWORD: actix_pass
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  jaeger:
    image: jaegertracing/all-in-one:1.62
    environment:
      COLLECTOR_OTLP_ENABLED: true
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP

  actix-app:
    build: .
    environment:
      DATABASE_URL: postgres://actix_user:actix_pass@postgres:5432/actix_db
      OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info,actix_web=debug,actix_otlp_example=debug
    ports:
      - "8080:8080"    # HTTP
      - "50051:50051"  # gRPC
    depends_on:
      - postgres
      - jaeger

volumes:
  postgres_data:
```

### Dockerfile

```dockerfile
# Dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app

# 复制依赖清单
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release

# 复制源代码
COPY src ./src
COPY migrations ./migrations
RUN touch src/main.rs && cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    libpq5 \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/actix-otlp-example /usr/local/bin/app

EXPOSE 8080 50051

CMD ["app"]
```

---

## ✅ 最佳实践

### Actix-web 设计

1. **使用 Extractors** ✅
   - `web::Json`, `web::Path`, `web::Query`
   - 类型安全的参数提取

2. **共享状态** ✅

   ```rust
   .app_data(web::Data::new(db_pool.clone()))
   ```

3. **中间件顺序** ✅

   ```rust
   .wrap(middleware::Logger::default())
   .wrap(OtlpMiddleware)  // 后添加先执行
   ```

4. **错误处理** ✅
   - 实现 `ResponseError` trait
   - 统一错误响应格式

### OTLP 集成

1. **中间件层** ✅
   - 自动创建 HTTP Span
   - W3C Trace Context 传播

2. **Handler 层** ✅
   - `#[instrument]` 宏
   - 记录业务参数

3. **Database 层** ✅
   - SQLx 自动追踪
   - 记录 SQL 语句

4. **异步追踪** ✅
   - 避免跨 await 持有 guard
   - 使用 `#[instrument]` 宏

### 性能优化

1. **连接池** ✅
   - 100 连接 (高并发)
   - 健康检查

2. **Workers** ✅
   - `num_cpus::get()` 个 Worker
   - 多核并行

3. **Keep-Alive** ✅
   - 减少 TCP 握手
   - 提升性能

---

**🚀 Actix-web 4.9 - 构建世界最快的 Rust Web API！**

**下一篇**: `Tower 生态系统 OTLP 中间件完整指南` (Week 2)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**Actix-web**: 4.9.0  
**OpenTelemetry**: 0.31.0
