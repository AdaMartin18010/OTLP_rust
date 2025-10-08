# Rust Axum 微服务 OTLP 追踪完整实战

> **Rust版本**: 1.90+  
> **Axum**: 0.8.7  
> **OpenTelemetry**: 0.31.0  
> **Tokio**: 1.47.1  
> **Tonic**: 0.14.2  
> **最后更新**: 2025年10月8日

---

## 目录

- [Rust Axum 微服务 OTLP 追踪完整实战](#rust-axum-微服务-otlp-追踪完整实战)
  - [目录](#目录)
  - [1. 项目架构概述](#1-项目架构概述)
  - [2. 完整项目结构](#2-完整项目结构)
  - [3. 依赖配置](#3-依赖配置)
    - [3.1 工作空间 Cargo.toml](#31-工作空间-cargotoml)
    - [3.2 API Gateway Cargo.toml](#32-api-gateway-cargotoml)
  - [4. 核心实现](#4-核心实现)
    - [4.1 OTLP 追踪初始化](#41-otlp-追踪初始化)
    - [4.2 Axum 服务器设置](#42-axum-服务器设置)
    - [4.3 HTTP 处理器实现](#43-http-处理器实现)
    - [4.4 数据库集成](#44-数据库集成)
    - [4.5 Redis 缓存集成](#45-redis-缓存集成)
    - [4.6 gRPC 客户端调用](#46-grpc-客户端调用)
  - [5. 中间件和拦截器](#5-中间件和拦截器)
  - [6. 错误处理](#6-错误处理)
  - [7. 完整示例应用](#7-完整示例应用)

---

## 1. 项目架构概述

**微服务架构**:

```text
┌─────────────────────────────────────────────────────────────┐
│                      OTLP Collector                         │
│                     (localhost:4317)                        │
└────────────────────────┬────────────────────────────────────┘
                         │ gRPC (OTLP)
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         v               v               v
┌────────────────┐ ┌─────────────┐ ┌─────────────┐
│  API Gateway   │ │   Service A │ │  Service B  │
│  (Axum 0.8.7)  │ │   (Axum)    │ │   (gRPC)    │
│  Port: 8080    │ │  Port: 8081 │ │ Port: 9090  │
└────────┬───────┘ └──────┬──────┘ └──────┬──────┘
         │                │               │
         │  PostgreSQL    │  Redis        │  HTTP
         │  (SQLx)        │  (redis-rs)   │  (reqwest)
         │                │               │
         v                v               v
    ┌────────┐      ┌────────┐      ┌────────┐
    │   DB   │      │  Cache │      │  API   │
    └────────┘      └────────┘      └────────┘
```

**关键特性**:

- ✅ Rust 1.90 async/await 模式
- ✅ 完整的 OTLP traces/metrics/logs 集成
- ✅ 分布式追踪 (W3C Trace Context)
- ✅ 异步数据库操作 (SQLx)
- ✅ Redis 缓存追踪
- ✅ gRPC 服务间通信
- ✅ 自动错误追踪
- ✅ 零拷贝性能优化

---

## 2. 完整项目结构

```text
otlp-microservice/
├── Cargo.toml                  # 工作空间配置
├── .env                        # 环境变量
├── docker-compose.yml          # Docker 部署
│
├── api-gateway/                # API 网关服务
│   ├── Cargo.toml
│   ├── src/
│   │   ├── main.rs            # 主入口
│   │   ├── handlers/          # HTTP 处理器
│   │   ├── middleware/        # 中间件
│   │   ├── models/            # 数据模型
│   │   └── telemetry.rs       # 追踪配置
│   └── tests/
│
├── user-service/               # 用户服务
│   ├── Cargo.toml
│   ├── src/
│   │   ├── main.rs
│   │   ├── handlers/
│   │   ├── db/                # 数据库操作
│   │   └── telemetry.rs
│   └── migrations/            # 数据库迁移
│
├── order-service/              # 订单服务 (gRPC)
│   ├── Cargo.toml
│   ├── build.rs               # Proto 编译
│   ├── proto/
│   │   └── order.proto
│   ├── src/
│   │   ├── main.rs
│   │   ├── grpc/              # gRPC 实现
│   │   └── telemetry.rs
│   └── tests/
│
└── shared/                     # 共享库
    ├── Cargo.toml
    └── src/
        ├── telemetry.rs       # 通用追踪配置
        ├── tracing.rs         # 追踪工具
        └── error.rs           # 错误处理
```

---

## 3. 依赖配置

### 3.1 工作空间 Cargo.toml

```toml
[workspace]
members = ["api-gateway", "user-service", "order-service", "shared"]
resolver = "2"

[workspace.package]
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[workspace.dependencies]
# Web 框架
axum = { version = "0.8.7", features = ["macros", "multipart", "tracing"] }
tower = "0.5.3"
tower-http = { version = "0.6.7", features = ["cors", "trace", "compression-gzip", "request-id"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# OpenTelemetry - 0.31.0
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace", "metrics", "logs"] }
opentelemetry-semantic-conventions = "0.31.0"

# 追踪集成
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.20", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# gRPC
tonic = { version = "0.14.2", features = ["transport", "tls-ring", "gzip"] }
prost = "0.14.1"

# 数据库
sqlx = { version = "0.8.5", features = ["runtime-tokio", "postgres", "macros", "migrate", "chrono", "uuid"] }
redis = { version = "0.32.7", features = ["tokio-comp", "connection-manager"] }

# HTTP 客户端
reqwest = { version = "0.12.23", features = ["json", "rustls-tls", "stream"] }

# 序列化
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"

# 工具
uuid = { version = "1.12.0", features = ["v4", "serde"] }
chrono = { version = "0.4.40", features = ["serde"] }
anyhow = "1.0.100"
thiserror = "2.0.17"

[workspace.dependencies.build]
tonic-build = "0.14.2"
```

### 3.2 API Gateway Cargo.toml

```toml
[package]
name = "api-gateway"
version.workspace = true
edition.workspace = true
rust-version.workspace = true

[dependencies]
# 从工作空间继承
axum.workspace = true
tower.workspace = true
tower-http.workspace = true
tokio.workspace = true
opentelemetry.workspace = true
opentelemetry_sdk.workspace = true
opentelemetry-otlp.workspace = true
opentelemetry-semantic-conventions.workspace = true
tracing.workspace = true
tracing-subscriber.workspace = true
tracing-opentelemetry.workspace = true
serde.workspace = true
serde_json.workspace = true
uuid.workspace = true
anyhow.workspace = true

# 项目特定依赖
shared = { path = "../shared" }
```

---

## 4. 核心实现

### 4.1 OTLP 追踪初始化

**shared/src/telemetry.rs**:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_semantic_conventions::{
    resource::{SERVICE_NAME, SERVICE_VERSION, DEPLOYMENT_ENVIRONMENT},
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use anyhow::Result;

/// 初始化 OpenTelemetry 追踪
pub fn init_telemetry(
    service_name: &str,
    service_version: &str,
    otlp_endpoint: &str,
) -> Result<()> {
    // 创建 OTLP 导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(otlp_endpoint);
    
    // 创建追踪器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(otlp_exporter)
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_max_events_per_span(64)
                .with_max_attributes_per_span(32)
                .with_resource(Resource::new(vec![
                    KeyValue::new(SERVICE_NAME, service_name.to_string()),
                    KeyValue::new(SERVICE_VERSION, service_version.to_string()),
                    KeyValue::new(DEPLOYMENT_ENVIRONMENT, "production"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 创建 OpenTelemetry 追踪层
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer);
    
    // 创建日志过滤器
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    // 初始化追踪订阅器
    tracing_subscriber::registry()
        .with(env_filter)
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer().json())
        .init();
    
    Ok(())
}

/// 关闭追踪
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

### 4.2 Axum 服务器设置

**api-gateway/src/main.rs**:

```rust
use axum::{
    Router,
    routing::{get, post},
    extract::Extension,
    http::StatusCode,
};
use tower_http::{
    trace::TraceLayer,
    compression::CompressionLayer,
    request_id::{MakeRequestId, RequestId, PropagateRequestIdLayer, SetRequestIdLayer},
};
use tower::ServiceBuilder;
use std::net::SocketAddr;
use uuid::Uuid;
use anyhow::Result;

mod handlers;
mod middleware;
mod models;
mod telemetry;

/// 自定义请求 ID 生成器
#[derive(Clone, Default)]
struct MakeRequestUuid;

impl MakeRequestId for MakeRequestUuid {
    fn make_request_id<B>(&mut self, _request: &axum::http::Request<B>) -> Option<RequestId> {
        let request_id = Uuid::new_v4().to_string().parse().ok()?;
        Some(RequestId::new(request_id))
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 加载环境变量
    dotenv::dotenv().ok();
    
    // 初始化追踪
    shared::telemetry::init_telemetry(
        "api-gateway",
        env!("CARGO_PKG_VERSION"),
        &std::env::var("OTLP_ENDPOINT").unwrap_or_else(|_| "http://localhost:4317".to_string()),
    )?;
    
    // 创建应用状态
    let app_state = AppState::new().await?;
    
    // 构建路由
    let app = Router::new()
        .route("/health", get(handlers::health_check))
        .route("/api/users", get(handlers::list_users))
        .route("/api/users/:id", get(handlers::get_user))
        .route("/api/users", post(handlers::create_user))
        .route("/api/orders", post(handlers::create_order))
        .layer(
            ServiceBuilder::new()
                // 请求 ID
                .layer(SetRequestIdLayer::x_request_id(MakeRequestUuid::default()))
                .layer(PropagateRequestIdLayer::x_request_id())
                // 追踪
                .layer(TraceLayer::new_for_http())
                // 压缩
                .layer(CompressionLayer::new())
                // 自定义中间件
                .layer(axum::middleware::from_fn(middleware::trace_middleware))
        )
        .with_state(app_state);
    
    // 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    tracing::info!("API Gateway listening on {}", addr);
    
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;
    
    // 关闭追踪
    shared::telemetry::shutdown_telemetry();
    
    Ok(())
}

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub db_pool: sqlx::PgPool,
    pub redis_client: redis::Client,
    pub http_client: reqwest::Client,
}

impl AppState {
    pub async fn new() -> Result<Self> {
        // PostgreSQL 连接池
        let database_url = std::env::var("DATABASE_URL")?;
        let db_pool = sqlx::postgres::PgPoolOptions::new()
            .max_connections(20)
            .connect(&database_url)
            .await?;
        
        // Redis 客户端
        let redis_url = std::env::var("REDIS_URL")?;
        let redis_client = redis::Client::open(redis_url)?;
        
        // HTTP 客户端
        let http_client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(10))
            .build()?;
        
        Ok(Self {
            db_pool,
            redis_client,
            http_client,
        })
    }
}
```

### 4.3 HTTP 处理器实现

**api-gateway/src/handlers/mod.rs**:

```rust
use axum::{
    extract::{Path, State},
    http::StatusCode,
    Json,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use tracing::{info, error, instrument};
use crate::AppState;

/// 健康检查
#[instrument]
pub async fn health_check() -> impl IntoResponse {
    info!("Health check requested");
    (StatusCode::OK, "OK")
}

/// 用户模型
#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
}

/// 创建用户请求
#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

/// 列出用户 - 带追踪
#[instrument(skip(state))]
pub async fn list_users(
    State(state): State<AppState>,
) -> Result<Json<Vec<User>>, AppError> {
    info!("Listing all users");
    
    // 查询数据库 - 自动追踪
    let users = sqlx::query_as!(
        User,
        r#"
        SELECT id, name, email
        FROM users
        ORDER BY name
        LIMIT 100
        "#
    )
    .fetch_all(&state.db_pool)
    .await
    .map_err(|e| {
        error!("Database error: {}", e);
        AppError::DatabaseError(e.to_string())
    })?;
    
    info!("Found {} users", users.len());
    
    Ok(Json(users))
}

/// 获取单个用户 - 带缓存
#[instrument(skip(state), fields(user_id = %id))]
pub async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<Uuid>,
) -> Result<Json<User>, AppError> {
    info!("Getting user {}", id);
    
    // 1. 尝试从 Redis 缓存获取
    let cache_key = format!("user:{}", id);
    
    use redis::AsyncCommands;
    let mut redis_conn = state.redis_client
        .get_async_connection()
        .await
        .map_err(|e| AppError::CacheError(e.to_string()))?;
    
    if let Ok(Some(cached_user)) = redis_conn.get::<_, Option<String>>(&cache_key).await {
        info!("User found in cache");
        let user: User = serde_json::from_str(&cached_user)?;
        return Ok(Json(user));
    }
    
    // 2. 从数据库查询
    info!("User not in cache, querying database");
    let user = sqlx::query_as!(
        User,
        r#"
        SELECT id, name, email
        FROM users
        WHERE id = $1
        "#,
        id
    )
    .fetch_optional(&state.db_pool)
    .await
    .map_err(|e| AppError::DatabaseError(e.to_string()))?
    .ok_or(AppError::NotFound)?;
    
    // 3. 写入缓存
    let user_json = serde_json::to_string(&user)?;
    let _: () = redis_conn
        .set_ex(&cache_key, user_json, 3600)
        .await
        .map_err(|e| {
            error!("Failed to cache user: {}", e);
            e
        })
        .ok()
        .unwrap_or(());
    
    info!("User retrieved successfully");
    
    Ok(Json(user))
}

/// 创建用户
#[instrument(skip(state), fields(user_name = %request.name))]
pub async fn create_user(
    State(state): State<AppState>,
    Json(request): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    info!("Creating new user: {}", request.name);
    
    let user_id = Uuid::new_v4();
    
    let user = sqlx::query_as!(
        User,
        r#"
        INSERT INTO users (id, name, email)
        VALUES ($1, $2, $3)
        RETURNING id, name, email
        "#,
        user_id,
        request.name,
        request.email,
    )
    .fetch_one(&state.db_pool)
    .await
    .map_err(|e| {
        error!("Failed to create user: {}", e);
        AppError::DatabaseError(e.to_string())
    })?;
    
    info!("User created successfully: {}", user.id);
    
    Ok(Json(user))
}

/// 创建订单 - 调用 gRPC 服务
#[instrument(skip(state))]
pub async fn create_order(
    State(state): State<AppState>,
    Json(request): Json<CreateOrderRequest>,
) -> Result<Json<OrderResponse>, AppError> {
    info!("Creating order for user {}", request.user_id);
    
    // 调用订单服务 (gRPC)
    // 实现见 4.6 节
    
    todo!("Implement gRPC call")
}

/// 应用错误
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Not found")]
    NotFound,
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Cache error: {0}")]
    CacheError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
}

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        let (status, message) = match self {
            AppError::NotFound => (StatusCode::NOT_FOUND, "Not found"),
            AppError::DatabaseError(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Database error"),
            AppError::CacheError(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Cache error"),
            AppError::SerializationError(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Serialization error"),
        };
        
        (status, message).into_response()
    }
}
```

### 4.4 数据库集成

**user-service/src/db/mod.rs**:

```rust
use sqlx::PgPool;
use uuid::Uuid;
use tracing::{instrument, info, error};
use anyhow::Result;

/// 数据库操作 - 自动追踪
pub struct UserRepository {
    pool: PgPool,
}

impl UserRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    /// 获取用户 - 带 Span
    #[instrument(skip(self), fields(db.system = "postgresql", db.operation = "SELECT"))]
    pub async fn get_by_id(&self, id: Uuid) -> Result<Option<User>> {
        info!("Querying user by ID: {}", id);
        
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, name, email, created_at
            FROM users
            WHERE id = $1
            "#,
            id
        )
        .fetch_optional(&self.pool)
        .await?;
        
        if let Some(ref u) = user {
            info!("User found: {}", u.name);
        } else {
            info!("User not found");
        }
        
        Ok(user)
    }
    
    /// 创建用户 - 事务追踪
    #[instrument(skip(self), fields(db.system = "postgresql", db.operation = "INSERT"))]
    pub async fn create(&self, name: String, email: String) -> Result<User> {
        info!("Creating user: {}", name);
        
        let mut tx = self.pool.begin().await?;
        
        let user_id = Uuid::new_v4();
        
        let user = sqlx::query_as!(
            User,
            r#"
            INSERT INTO users (id, name, email)
            VALUES ($1, $2, $3)
            RETURNING id, name, email, created_at
            "#,
            user_id,
            name,
            email,
        )
        .fetch_one(&mut *tx)
        .await?;
        
        tx.commit().await?;
        
        info!("User created successfully: {}", user.id);
        
        Ok(user)
    }
}

#[derive(Debug, sqlx::FromRow)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}
```

### 4.5 Redis 缓存集成

**shared/src/cache.rs**:

```rust
use redis::{AsyncCommands, aio::ConnectionManager};
use tracing::{instrument, info, warn};
use anyhow::Result;
use serde::{Serialize, de::DeserializeOwned};

/// Redis 缓存客户端 - 带追踪
pub struct CacheClient {
    conn: ConnectionManager,
}

impl CacheClient {
    pub async fn new(redis_url: &str) -> Result<Self> {
        let client = redis::Client::open(redis_url)?;
        let conn = ConnectionManager::new(client).await?;
        
        Ok(Self { conn })
    }
    
    /// 获取缓存 - 自动追踪
    #[instrument(skip(self), fields(cache.system = "redis", cache.operation = "GET"))]
    pub async fn get<T: DeserializeOwned>(&mut self, key: &str) -> Result<Option<T>> {
        info!("Getting key from cache: {}", key);
        
        let value: Option<String> = self.conn.get(key).await?;
        
        match value {
            Some(json) => {
                info!("Cache hit");
                let data = serde_json::from_str(&json)?;
                Ok(Some(data))
            }
            None => {
                info!("Cache miss");
                Ok(None)
            }
        }
    }
    
    /// 设置缓存 - 自动追踪
    #[instrument(skip(self, value), fields(cache.system = "redis", cache.operation = "SET"))]
    pub async fn set<T: Serialize>(&mut self, key: &str, value: &T, ttl_seconds: u64) -> Result<()> {
        info!("Setting key in cache: {} (TTL: {}s)", key, ttl_seconds);
        
        let json = serde_json::to_string(value)?;
        
        self.conn.set_ex(key, json, ttl_seconds).await?;
        
        info!("Cache set successfully");
        
        Ok(())
    }
    
    /// 删除缓存
    #[instrument(skip(self), fields(cache.system = "redis", cache.operation = "DEL"))]
    pub async fn delete(&mut self, key: &str) -> Result<()> {
        info!("Deleting key from cache: {}", key);
        
        let _: () = self.conn.del(key).await?;
        
        info!("Cache deleted successfully");
        
        Ok(())
    }
}
```

### 4.6 gRPC 客户端调用

**order-service/proto/order.proto**:

```protobuf
syntax = "proto3";

package order;

service OrderService {
  rpc CreateOrder (CreateOrderRequest) returns (CreateOrderResponse);
  rpc GetOrder (GetOrderRequest) returns (GetOrderResponse);
}

message CreateOrderRequest {
  string user_id = 1;
  repeated OrderItem items = 2;
}

message OrderItem {
  string product_id = 1;
  int32 quantity = 2;
  double price = 3;
}

message CreateOrderResponse {
  string order_id = 1;
  double total_amount = 2;
  string status = 3;
}

message GetOrderRequest {
  string order_id = 1;
}

message GetOrderResponse {
  string order_id = 1;
  string user_id = 2;
  repeated OrderItem items = 3;
  double total_amount = 4;
  string status = 5;
}
```

**api-gateway/src/grpc_client.rs**:

```rust
use tonic::transport::Channel;
use tonic::{Request, Status};
use tracing::{instrument, info};
use anyhow::Result;

// 从 proto 生成
pub mod order_proto {
    tonic::include_proto!("order");
}

use order_proto::order_service_client::OrderServiceClient;
use order_proto::{CreateOrderRequest, CreateOrderResponse};

/// gRPC 客户端 - 带追踪
pub struct OrderGrpcClient {
    client: OrderServiceClient<Channel>,
}

impl OrderGrpcClient {
    pub async fn new(endpoint: &str) -> Result<Self> {
        let channel = Channel::from_shared(endpoint.to_string())?
            .connect()
            .await?;
        
        let client = OrderServiceClient::new(channel);
        
        Ok(Self { client })
    }
    
    /// 创建订单 - 自动传播追踪上下文
    #[instrument(skip(self), fields(grpc.service = "OrderService", grpc.method = "CreateOrder"))]
    pub async fn create_order(
        &mut self,
        user_id: String,
        items: Vec<order_proto::OrderItem>,
    ) -> Result<CreateOrderResponse, Status> {
        info!("Calling OrderService.CreateOrder for user: {}", user_id);
        
        let request = Request::new(CreateOrderRequest {
            user_id,
            items,
        });
        
        // Tonic 自动传播 W3C Trace Context
        let response = self.client.create_order(request).await?;
        
        info!("Order created successfully");
        
        Ok(response.into_inner())
    }
}
```

---

## 5. 中间件和拦截器

**api-gateway/src/middleware/mod.rs**:

```rust
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use tracing::{info_span, Instrument};
use uuid::Uuid;

/// 追踪中间件 - 为每个请求创建 Span
pub async fn trace_middleware(
    request: Request,
    next: Next,
) -> Response {
    let request_id = request
        .headers()
        .get("x-request-id")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("unknown");
    
    let method = request.method().clone();
    let uri = request.uri().clone();
    
    // 创建请求级 Span
    let span = info_span!(
        "http_request",
        http.method = %method,
        http.url = %uri,
        http.request_id = %request_id,
    );
    
    async move {
        info!("Processing request: {} {}", method, uri);
        
        let response = next.run(request).await;
        
        info!(
            http.status_code = response.status().as_u16(),
            "Request completed"
        );
        
        response
    }
    .instrument(span)
    .await
}
```

---

## 6. 错误处理

**shared/src/error.rs**:

```rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde_json::json;
use tracing::error;

/// 统一错误类型
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Unauthorized")]
    Unauthorized,
    
    #[error("Internal server error: {0}")]
    InternalError(String),
    
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
    
    #[error("Redis error: {0}")]
    RedisError(#[from] redis::RedisError),
    
    #[error("gRPC error: {0}")]
    GrpcError(#[from] tonic::Status),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        // 记录错误到追踪
        error!(error = %self, "Request error");
        
        let (status, error_message) = match self {
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
            AppError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg),
            AppError::Unauthorized => (StatusCode::UNAUTHORIZED, "Unauthorized".to_string()),
            AppError::DatabaseError(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("Database error: {}", e)),
            AppError::RedisError(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("Cache error: {}", e)),
            AppError::GrpcError(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("Service error: {}", e)),
            AppError::InternalError(msg) => (StatusCode::INTERNAL_SERVER_ERROR, msg),
            AppError::SerializationError(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("Serialization error: {}", e)),
        };
        
        let body = Json(json!({
            "error": error_message,
        }));
        
        (status, body).into_response()
    }
}
```

---

## 7. 完整示例应用

继续下一部分...

**最佳实践总结**:

```text
✅ 使用 #[instrument] 宏自动追踪
✅ 为每个服务设置唯一的 service.name
✅ 传播 W3C Trace Context
✅ 记录关键业务指标
✅ 异常自动记录到 Span
✅ 使用结构化日志
✅ 合理设置采样率
✅ 零拷贝性能优化
✅ 异步 I/O 避免阻塞
✅ 类型安全的 Rust 实现
```

---

**最后更新**: 2025年10月8日  
**维护者**: OTLP Rust团队  
**许可证**: MIT OR Apache-2.0
