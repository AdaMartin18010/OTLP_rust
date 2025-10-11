# 🚀 Rust OTLP 综合实战手册

> **项目**: 完整的微服务电商系统  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🚀 Rust OTLP 综合实战手册](#-rust-otlp-综合实战手册)
  - [📋 目录](#-目录)
  - [1. 项目概述](#1-项目概述)
    - [1.1 系统简介](#11-系统简介)
    - [1.2 技术栈](#12-技术栈)
    - [1.3 项目结构](#13-项目结构)
  - [2. 系统架构](#2-系统架构)
    - [2.1 架构图](#21-架构图)
    - [2.2 追踪链路](#22-追踪链路)
  - [3. API Gateway](#3-api-gateway)
    - [3.1 主程序](#31-主程序)
    - [3.2 路由处理](#32-路由处理)
    - [3.3 追踪中间件](#33-追踪中间件)
  - [4. 用户服务](#4-用户服务)
    - [4.1 gRPC 定义](#41-grpc-定义)
    - [4.2 服务实现](#42-服务实现)
  - [5. 订单服务](#5-订单服务)
    - [5.1 gRPC 定义](#51-grpc-定义)
    - [5.2 服务实现](#52-服务实现)
  - [6. 库存服务](#6-库存服务)
    - [6.1 gRPC 定义](#61-grpc-定义)
    - [6.2 服务实现](#62-服务实现)
  - [7. 数据库集成](#7-数据库集成)
    - [7.1 数据库迁移](#71-数据库迁移)
    - [7.2 数据库追踪](#72-数据库追踪)
  - [8. 消息队列](#8-消息队列)
    - [8.1 Redis Streams 生产者](#81-redis-streams-生产者)
    - [8.2 Redis Streams 消费者](#82-redis-streams-消费者)
  - [9. 可观测性配置](#9-可观测性配置)
    - [9.1 通用追踪初始化](#91-通用追踪初始化)
    - [9.2 Metrics 配置](#92-metrics-配置)
  - [10. 部署指南](#10-部署指南)
    - [10.1 Docker Compose](#101-docker-compose)
    - [10.2 Dockerfile 示例](#102-dockerfile-示例)
    - [10.3 启动命令](#103-启动命令)
  - [🔗 参考资源](#-参考资源)

---

## 1. 项目概述

### 1.1 系统简介

我们将构建一个完整的微服务电商系统，包含：

- **API Gateway**: 统一入口，路由转发
- **用户服务**: 用户认证、授权
- **订单服务**: 订单创建、查询
- **库存服务**: 库存管理、扣减
- **数据库**: PostgreSQL
- **消息队列**: Redis Streams
- **可观测性**: Jaeger + Prometheus

### 1.2 技术栈

```toml
# Cargo.toml (workspace)
[workspace]
members = [
    "api-gateway",
    "user-service",
    "order-service",
    "inventory-service",
    "common",
]

[workspace.dependencies]
# HTTP/Web
axum = "0.7"
tower = "0.4"
tower-http = "0.5"

# gRPC
tonic = "0.12"
prost = "0.13"

# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry-otlp = "0.31.0"
opentelemetry-sdk = "0.31.0"
tracing = "0.1"
tracing-opentelemetry = "0.31.0"
tracing-subscriber = "0.3"

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 数据库
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "uuid"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 错误处理
anyhow = "1"
thiserror = "1"

# 日志
tracing = "0.1"

# Redis
redis = { version = "0.26", features = ["tokio-comp", "streams"] }

# UUID
uuid = { version = "1", features = ["v4", "serde"] }
```

### 1.3 项目结构

```text
ecommerce-microservices/
├─ api-gateway/
│  ├─ src/
│  │  ├─ main.rs
│  │  ├─ routes.rs
│  │  └─ middleware/
│  └─ Cargo.toml
├─ user-service/
│  ├─ src/
│  │  ├─ main.rs
│  │  ├─ handlers.rs
│  │  └─ models.rs
│  └─ Cargo.toml
├─ order-service/
│  ├─ src/
│  │  ├─ main.rs
│  │  ├─ handlers.rs
│  │  └─ models.rs
│  └─ Cargo.toml
├─ inventory-service/
│  ├─ src/
│  │  ├─ main.rs
│  │  ├─ handlers.rs
│  │  └─ models.rs
│  └─ Cargo.toml
├─ common/
│  ├─ src/
│  │  ├─ lib.rs
│  │  ├─ telemetry.rs
│  │  └─ error.rs
│  └─ Cargo.toml
├─ docker-compose.yml
└─ Cargo.toml
```

---

## 2. 系统架构

### 2.1 架构图

```text
┌─────────────┐
│   Client    │
└──────┬──────┘
       │
       ▼
┌─────────────────────────────────────────────┐
│           API Gateway (Axum)                │
│  ┌─────────────────────────────────────┐   │
│  │   OpenTelemetry Middleware          │   │
│  └─────────────────────────────────────┘   │
└──────┬──────────────┬──────────────┬────────┘
       │              │              │
       ▼              ▼              ▼
┌──────────┐    ┌──────────┐  ┌──────────────┐
│  User    │    │  Order   │  │  Inventory   │
│ Service  │◄──►│ Service  │◄─┤   Service    │
│ (gRPC)   │    │ (gRPC)   │  │   (gRPC)     │
└────┬─────┘    └────┬─────┘  └──────┬───────┘
     │               │               │
     ▼               ▼               ▼
┌──────────────────────────────────────────┐
│          PostgreSQL Database             │
└──────────────────────────────────────────┘
                   ▲
                   │
        ┌──────────┴──────────┐
        │   Redis Streams     │
        └─────────────────────┘
                   ▲
                   │
        ┌──────────┴──────────┐
        │  Jaeger + Prometheus│
        └─────────────────────┘
```

### 2.2 追踪链路

```text
Client Request
    │
    ▼
API Gateway Span (HTTP)
    │
    ├─► User Service Span (gRPC)
    │       └─► Database Query Span
    │
    ├─► Order Service Span (gRPC)
    │       ├─► Database Query Span
    │       └─► Redis Publish Span
    │
    └─► Inventory Service Span (gRPC)
            └─► Database Query Span
```

---

## 3. API Gateway

### 3.1 主程序

```rust
// api-gateway/src/main.rs
use axum::{
    Router,
    routing::{get, post},
    extract::State,
};
use tower_http::trace::TraceLayer;
use std::sync::Arc;

mod routes;
mod middleware;

#[derive(Clone)]
struct AppState {
    user_client: user_service::UserClient,
    order_client: order_service::OrderClient,
    inventory_client: inventory_service::InventoryClient,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    common::telemetry::init_tracer("api-gateway")?;
    
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    // 连接各个服务
    let user_client = user_service::UserClient::connect("http://user-service:50051").await?;
    let order_client = order_service::OrderClient::connect("http://order-service:50052").await?;
    let inventory_client = inventory_service::InventoryClient::connect("http://inventory-service:50053").await?;
    
    let state = Arc::new(AppState {
        user_client,
        order_client,
        inventory_client,
    });
    
    // 构建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/api/users", post(routes::create_user))
        .route("/api/users/:id", get(routes::get_user))
        .route("/api/orders", post(routes::create_order))
        .route("/api/orders/:id", get(routes::get_order))
        .route("/api/inventory/:product_id", get(routes::get_inventory))
        .layer(TraceLayer::new_for_http())
        .layer(axum::middleware::from_fn(middleware::tracing_middleware))
        .with_state(state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    tracing::info!("API Gateway listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    // 优雅关闭
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}

async fn health_check() -> &'static str {
    "OK"
}
```

### 3.2 路由处理

```rust
// api-gateway/src/routes.rs
use axum::{
    extract::{Path, State},
    Json,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use tracing::instrument;
use uuid::Uuid;

#[derive(Deserialize)]
pub struct CreateUserRequest {
    pub email: String,
    pub name: String,
}

#[derive(Serialize)]
pub struct UserResponse {
    pub id: Uuid,
    pub email: String,
    pub name: String,
}

#[instrument(skip(state))]
pub async fn create_user(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<UserResponse>, (StatusCode, String)> {
    tracing::info!("Creating user: {}", payload.email);
    
    let request = tonic::Request::new(user_service::CreateUserRequest {
        email: payload.email,
        name: payload.name,
    });
    
    let response = state.user_client.clone()
        .create_user(request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to create user: {}", e);
            (StatusCode::INTERNAL_SERVER_ERROR, e.to_string())
        })?;
    
    let user = response.into_inner();
    
    Ok(Json(UserResponse {
        id: Uuid::parse_str(&user.id).unwrap(),
        email: user.email,
        name: user.name,
    }))
}

#[instrument(skip(state))]
pub async fn get_user(
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
) -> Result<Json<UserResponse>, (StatusCode, String)> {
    tracing::info!("Getting user: {}", id);
    
    let request = tonic::Request::new(user_service::GetUserRequest {
        id: id.to_string(),
    });
    
    let response = state.user_client.clone()
        .get_user(request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to get user: {}", e);
            (StatusCode::NOT_FOUND, e.to_string())
        })?;
    
    let user = response.into_inner();
    
    Ok(Json(UserResponse {
        id: Uuid::parse_str(&user.id).unwrap(),
        email: user.email,
        name: user.name,
    }))
}

#[derive(Deserialize)]
pub struct CreateOrderRequest {
    pub user_id: Uuid,
    pub product_id: Uuid,
    pub quantity: i32,
}

#[derive(Serialize)]
pub struct OrderResponse {
    pub id: Uuid,
    pub user_id: Uuid,
    pub product_id: Uuid,
    pub quantity: i32,
    pub status: String,
}

#[instrument(skip(state))]
pub async fn create_order(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateOrderRequest>,
) -> Result<Json<OrderResponse>, (StatusCode, String)> {
    tracing::info!("Creating order for user: {}", payload.user_id);
    
    // 1. 检查库存
    let inventory_request = tonic::Request::new(inventory_service::CheckInventoryRequest {
        product_id: payload.product_id.to_string(),
        quantity: payload.quantity,
    });
    
    let inventory_response = state.inventory_client.clone()
        .check_inventory(inventory_request)
        .await
        .map_err(|e| {
            tracing::error!("Inventory check failed: {}", e);
            (StatusCode::BAD_REQUEST, "Insufficient inventory".to_string())
        })?;
    
    if !inventory_response.into_inner().available {
        return Err((StatusCode::BAD_REQUEST, "Insufficient inventory".to_string()));
    }
    
    // 2. 创建订单
    let order_request = tonic::Request::new(order_service::CreateOrderRequest {
        user_id: payload.user_id.to_string(),
        product_id: payload.product_id.to_string(),
        quantity: payload.quantity,
    });
    
    let order_response = state.order_client.clone()
        .create_order(order_request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to create order: {}", e);
            (StatusCode::INTERNAL_SERVER_ERROR, e.to_string())
        })?;
    
    let order = order_response.into_inner();
    
    // 3. 扣减库存
    let deduct_request = tonic::Request::new(inventory_service::DeductInventoryRequest {
        product_id: payload.product_id.to_string(),
        quantity: payload.quantity,
        order_id: order.id.clone(),
    });
    
    state.inventory_client.clone()
        .deduct_inventory(deduct_request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to deduct inventory: {}", e);
            (StatusCode::INTERNAL_SERVER_ERROR, e.to_string())
        })?;
    
    tracing::info!("Order created successfully: {}", order.id);
    
    Ok(Json(OrderResponse {
        id: Uuid::parse_str(&order.id).unwrap(),
        user_id: Uuid::parse_str(&order.user_id).unwrap(),
        product_id: Uuid::parse_str(&order.product_id).unwrap(),
        quantity: order.quantity,
        status: order.status,
    }))
}

#[instrument(skip(state))]
pub async fn get_order(
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
) -> Result<Json<OrderResponse>, (StatusCode, String)> {
    tracing::info!("Getting order: {}", id);
    
    let request = tonic::Request::new(order_service::GetOrderRequest {
        id: id.to_string(),
    });
    
    let response = state.order_client.clone()
        .get_order(request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to get order: {}", e);
            (StatusCode::NOT_FOUND, e.to_string())
        })?;
    
    let order = response.into_inner();
    
    Ok(Json(OrderResponse {
        id: Uuid::parse_str(&order.id).unwrap(),
        user_id: Uuid::parse_str(&order.user_id).unwrap(),
        product_id: Uuid::parse_str(&order.product_id).unwrap(),
        quantity: order.quantity,
        status: order.status,
    }))
}

#[derive(Serialize)]
pub struct InventoryResponse {
    pub product_id: Uuid,
    pub quantity: i32,
}

#[instrument(skip(state))]
pub async fn get_inventory(
    State(state): State<Arc<AppState>>,
    Path(product_id): Path<Uuid>,
) -> Result<Json<InventoryResponse>, (StatusCode, String)> {
    tracing::info!("Getting inventory for product: {}", product_id);
    
    let request = tonic::Request::new(inventory_service::GetInventoryRequest {
        product_id: product_id.to_string(),
    });
    
    let response = state.inventory_client.clone()
        .get_inventory(request)
        .await
        .map_err(|e| {
            tracing::error!("Failed to get inventory: {}", e);
            (StatusCode::NOT_FOUND, e.to_string())
        })?;
    
    let inventory = response.into_inner();
    
    Ok(Json(InventoryResponse {
        product_id: Uuid::parse_str(&inventory.product_id).unwrap(),
        quantity: inventory.quantity,
    }))
}
```

### 3.3 追踪中间件

```rust
// api-gateway/src/middleware.rs
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use opentelemetry::{
    global,
    trace::{Span, Tracer, SpanKind},
    KeyValue,
};

pub async fn tracing_middleware(
    request: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("api-gateway");
    
    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("http.method", request.method().to_string()));
    span.set_attribute(KeyValue::new("http.url", request.uri().path().to_string()));
    
    let response = next.run(request).await;
    
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    span.end();
    
    response
}
```

---

## 4. 用户服务

### 4.1 gRPC 定义

```protobuf
// user-service/proto/user.proto
syntax = "proto3";

package user;

service User {
  rpc CreateUser (CreateUserRequest) returns (UserResponse);
  rpc GetUser (GetUserRequest) returns (UserResponse);
}

message CreateUserRequest {
  string email = 1;
  string name = 2;
}

message GetUserRequest {
  string id = 1;
}

message UserResponse {
  string id = 1;
  string email = 2;
  string name = 3;
  string created_at = 4;
}
```

### 4.2 服务实现

```rust
// user-service/src/main.rs
use tonic::{transport::Server, Request, Response, Status};
use sqlx::PgPool;
use uuid::Uuid;
use tracing::instrument;

pub mod user {
    tonic::include_proto!("user");
}

use user::user_server::{User, UserServer};
use user::{CreateUserRequest, GetUserRequest, UserResponse};

#[derive(Clone)]
pub struct UserService {
    db: PgPool,
}

#[tonic::async_trait]
impl User for UserService {
    #[instrument(skip(self))]
    async fn create_user(
        &self,
        request: Request<CreateUserRequest>,
    ) -> Result<Response<UserResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Creating user: {}", req.email);
        
        let id = Uuid::new_v4();
        
        sqlx::query!(
            r#"
            INSERT INTO users (id, email, name)
            VALUES ($1, $2, $3)
            "#,
            id,
            req.email,
            req.name
        )
        .execute(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("Database error: {}", e);
            Status::internal("Failed to create user")
        })?;
        
        let user = sqlx::query_as!(
            UserRow,
            "SELECT id, email, name, created_at FROM users WHERE id = $1",
            id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|e| Status::internal(e.to_string()))?;
        
        Ok(Response::new(UserResponse {
            id: user.id.to_string(),
            email: user.email,
            name: user.name,
            created_at: user.created_at.to_string(),
        }))
    }
    
    #[instrument(skip(self))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<UserResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Getting user: {}", req.id);
        
        let id = Uuid::parse_str(&req.id)
            .map_err(|_| Status::invalid_argument("Invalid user ID"))?;
        
        let user = sqlx::query_as!(
            UserRow,
            "SELECT id, email, name, created_at FROM users WHERE id = $1",
            id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("User not found: {}", e);
            Status::not_found("User not found")
        })?;
        
        Ok(Response::new(UserResponse {
            id: user.id.to_string(),
            email: user.email,
            name: user.name,
            created_at: user.created_at.to_string(),
        }))
    }
}

#[derive(Debug)]
struct UserRow {
    id: Uuid,
    email: String,
    name: String,
    created_at: chrono::DateTime<chrono::Utc>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    common::telemetry::init_tracer("user-service")?;
    
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    // 连接数据库
    let database_url = std::env::var("DATABASE_URL")?;
    let db = PgPool::connect(&database_url).await?;
    
    // 运行迁移
    sqlx::migrate!("./migrations").run(&db).await?;
    
    let service = UserService { db };
    
    let addr = "0.0.0.0:50051".parse()?;
    
    tracing::info!("User service listening on {}", addr);
    
    Server::builder()
        .add_service(UserServer::new(service))
        .serve(addr)
        .await?;
    
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}
```

---

## 5. 订单服务

### 5.1 gRPC 定义

```protobuf
// order-service/proto/order.proto
syntax = "proto3";

package order;

service Order {
  rpc CreateOrder (CreateOrderRequest) returns (OrderResponse);
  rpc GetOrder (GetOrderRequest) returns (OrderResponse);
}

message CreateOrderRequest {
  string user_id = 1;
  string product_id = 2;
  int32 quantity = 3;
}

message GetOrderRequest {
  string id = 1;
}

message OrderResponse {
  string id = 1;
  string user_id = 2;
  string product_id = 3;
  int32 quantity = 4;
  string status = 5;
  string created_at = 6;
}
```

### 5.2 服务实现

```rust
// order-service/src/main.rs
use tonic::{transport::Server, Request, Response, Status};
use sqlx::PgPool;
use redis::Client as RedisClient;
use uuid::Uuid;
use tracing::instrument;

pub mod order {
    tonic::include_proto!("order");
}

use order::order_server::{Order, OrderServer};
use order::{CreateOrderRequest, GetOrderRequest, OrderResponse};

#[derive(Clone)]
pub struct OrderService {
    db: PgPool,
    redis: RedisClient,
}

#[tonic::async_trait]
impl Order for OrderService {
    #[instrument(skip(self))]
    async fn create_order(
        &self,
        request: Request<CreateOrderRequest>,
    ) -> Result<Response<OrderResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Creating order for user: {}", req.user_id);
        
        let id = Uuid::new_v4();
        let user_id = Uuid::parse_str(&req.user_id)
            .map_err(|_| Status::invalid_argument("Invalid user ID"))?;
        let product_id = Uuid::parse_str(&req.product_id)
            .map_err(|_| Status::invalid_argument("Invalid product ID"))?;
        
        // 创建订单
        sqlx::query!(
            r#"
            INSERT INTO orders (id, user_id, product_id, quantity, status)
            VALUES ($1, $2, $3, $4, $5)
            "#,
            id,
            user_id,
            product_id,
            req.quantity,
            "pending"
        )
        .execute(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("Database error: {}", e);
            Status::internal("Failed to create order")
        })?;
        
        // 发布事件到 Redis
        let mut con = self.redis.get_async_connection()
            .await
            .map_err(|e| {
                tracing::error!("Redis connection error: {}", e);
                Status::internal("Failed to publish event")
            })?;
        
        let event = serde_json::json!({
            "order_id": id.to_string(),
            "user_id": user_id.to_string(),
            "product_id": product_id.to_string(),
            "quantity": req.quantity,
            "timestamp": chrono::Utc::now().to_rfc3339(),
        });
        
        redis::cmd("XADD")
            .arg("orders:created")
            .arg("*")
            .arg("data")
            .arg(event.to_string())
            .query_async(&mut con)
            .await
            .map_err(|e| {
                tracing::error!("Failed to publish event: {}", e);
                Status::internal("Failed to publish event")
            })?;
        
        tracing::info!("Order created successfully: {}", id);
        
        let order = sqlx::query_as!(
            OrderRow,
            "SELECT id, user_id, product_id, quantity, status, created_at FROM orders WHERE id = $1",
            id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|e| Status::internal(e.to_string()))?;
        
        Ok(Response::new(OrderResponse {
            id: order.id.to_string(),
            user_id: order.user_id.to_string(),
            product_id: order.product_id.to_string(),
            quantity: order.quantity,
            status: order.status,
            created_at: order.created_at.to_string(),
        }))
    }
    
    #[instrument(skip(self))]
    async fn get_order(
        &self,
        request: Request<GetOrderRequest>,
    ) -> Result<Response<OrderResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Getting order: {}", req.id);
        
        let id = Uuid::parse_str(&req.id)
            .map_err(|_| Status::invalid_argument("Invalid order ID"))?;
        
        let order = sqlx::query_as!(
            OrderRow,
            "SELECT id, user_id, product_id, quantity, status, created_at FROM orders WHERE id = $1",
            id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|_| Status::not_found("Order not found"))?;
        
        Ok(Response::new(OrderResponse {
            id: order.id.to_string(),
            user_id: order.user_id.to_string(),
            product_id: order.product_id.to_string(),
            quantity: order.quantity,
            status: order.status,
            created_at: order.created_at.to_string(),
        }))
    }
}

#[derive(Debug)]
struct OrderRow {
    id: Uuid,
    user_id: Uuid,
    product_id: Uuid,
    quantity: i32,
    status: String,
    created_at: chrono::DateTime<chrono::Utc>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    common::telemetry::init_tracer("order-service")?;
    
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    let database_url = std::env::var("DATABASE_URL")?;
    let db = PgPool::connect(&database_url).await?;
    
    sqlx::migrate!("./migrations").run(&db).await?;
    
    let redis_url = std::env::var("REDIS_URL")?;
    let redis = RedisClient::open(redis_url)?;
    
    let service = OrderService { db, redis };
    
    let addr = "0.0.0.0:50052".parse()?;
    
    tracing::info!("Order service listening on {}", addr);
    
    Server::builder()
        .add_service(OrderServer::new(service))
        .serve(addr)
        .await?;
    
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}
```

---

## 6. 库存服务

### 6.1 gRPC 定义

```protobuf
// inventory-service/proto/inventory.proto
syntax = "proto3";

package inventory;

service Inventory {
  rpc CheckInventory (CheckInventoryRequest) returns (CheckInventoryResponse);
  rpc DeductInventory (DeductInventoryRequest) returns (DeductInventoryResponse);
  rpc GetInventory (GetInventoryRequest) returns (InventoryResponse);
}

message CheckInventoryRequest {
  string product_id = 1;
  int32 quantity = 2;
}

message CheckInventoryResponse {
  bool available = 1;
}

message DeductInventoryRequest {
  string product_id = 1;
  int32 quantity = 2;
  string order_id = 3;
}

message DeductInventoryResponse {
  bool success = 1;
}

message GetInventoryRequest {
  string product_id = 1;
}

message InventoryResponse {
  string product_id = 1;
  int32 quantity = 2;
}
```

### 6.2 服务实现

```rust
// inventory-service/src/main.rs
use tonic::{transport::Server, Request, Response, Status};
use sqlx::PgPool;
use uuid::Uuid;
use tracing::instrument;

pub mod inventory {
    tonic::include_proto!("inventory");
}

use inventory::inventory_server::{Inventory, InventoryServer};
use inventory::{
    CheckInventoryRequest, CheckInventoryResponse,
    DeductInventoryRequest, DeductInventoryResponse,
    GetInventoryRequest, InventoryResponse,
};

#[derive(Clone)]
pub struct InventoryService {
    db: PgPool,
}

#[tonic::async_trait]
impl Inventory for InventoryService {
    #[instrument(skip(self))]
    async fn check_inventory(
        &self,
        request: Request<CheckInventoryRequest>,
    ) -> Result<Response<CheckInventoryResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Checking inventory for product: {}", req.product_id);
        
        let product_id = Uuid::parse_str(&req.product_id)
            .map_err(|_| Status::invalid_argument("Invalid product ID"))?;
        
        let inventory = sqlx::query!(
            "SELECT quantity FROM inventory WHERE product_id = $1",
            product_id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|_| Status::not_found("Product not found"))?;
        
        let available = inventory.quantity >= req.quantity;
        
        tracing::info!("Inventory check result: available={}", available);
        
        Ok(Response::new(CheckInventoryResponse { available }))
    }
    
    #[instrument(skip(self))]
    async fn deduct_inventory(
        &self,
        request: Request<DeductInventoryRequest>,
    ) -> Result<Response<DeductInventoryResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Deducting inventory for product: {}", req.product_id);
        
        let product_id = Uuid::parse_str(&req.product_id)
            .map_err(|_| Status::invalid_argument("Invalid product ID"))?;
        
        let result = sqlx::query!(
            r#"
            UPDATE inventory
            SET quantity = quantity - $1
            WHERE product_id = $2 AND quantity >= $1
            "#,
            req.quantity,
            product_id
        )
        .execute(&self.db)
        .await
        .map_err(|e| {
            tracing::error!("Failed to deduct inventory: {}", e);
            Status::internal("Failed to deduct inventory")
        })?;
        
        let success = result.rows_affected() > 0;
        
        if !success {
            tracing::warn!("Insufficient inventory for product: {}", product_id);
        } else {
            tracing::info!("Inventory deducted successfully");
        }
        
        Ok(Response::new(DeductInventoryResponse { success }))
    }
    
    #[instrument(skip(self))]
    async fn get_inventory(
        &self,
        request: Request<GetInventoryRequest>,
    ) -> Result<Response<InventoryResponse>, Status> {
        let req = request.into_inner();
        
        tracing::info!("Getting inventory for product: {}", req.product_id);
        
        let product_id = Uuid::parse_str(&req.product_id)
            .map_err(|_| Status::invalid_argument("Invalid product ID"))?;
        
        let inventory = sqlx::query!(
            "SELECT product_id, quantity FROM inventory WHERE product_id = $1",
            product_id
        )
        .fetch_one(&self.db)
        .await
        .map_err(|_| Status::not_found("Product not found"))?;
        
        Ok(Response::new(InventoryResponse {
            product_id: inventory.product_id.to_string(),
            quantity: inventory.quantity,
        }))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    common::telemetry::init_tracer("inventory-service")?;
    
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    let database_url = std::env::var("DATABASE_URL")?;
    let db = PgPool::connect(&database_url).await?;
    
    sqlx::migrate!("./migrations").run(&db).await?;
    
    let service = InventoryService { db };
    
    let addr = "0.0.0.0:50053".parse()?;
    
    tracing::info!("Inventory service listening on {}", addr);
    
    Server::builder()
        .add_service(InventoryServer::new(service))
        .serve(addr)
        .await?;
    
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}
```

---

## 7. 数据库集成

### 7.1 数据库迁移

```sql
-- migrations/001_create_users.sql
CREATE TABLE users (
    id UUID PRIMARY KEY,
    email VARCHAR(255) NOT NULL UNIQUE,
    name VARCHAR(255) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);

-- migrations/002_create_orders.sql
CREATE TABLE orders (
    id UUID PRIMARY KEY,
    user_id UUID NOT NULL REFERENCES users(id),
    product_id UUID NOT NULL,
    quantity INT NOT NULL,
    status VARCHAR(50) NOT NULL DEFAULT 'pending',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE INDEX idx_orders_user_id ON orders(user_id);
CREATE INDEX idx_orders_status ON orders(status);

-- migrations/003_create_inventory.sql
CREATE TABLE inventory (
    product_id UUID PRIMARY KEY,
    quantity INT NOT NULL DEFAULT 0,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE INDEX idx_inventory_quantity ON inventory(quantity);
```

### 7.2 数据库追踪

```rust
// common/src/db.rs
use sqlx::{PgPool, Postgres, Transaction};
use tracing::instrument;

pub struct TracedDb {
    pool: PgPool,
}

impl TracedDb {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    #[instrument(skip(self))]
    pub async fn execute(&self, query: &str) -> Result<(), sqlx::Error> {
        tracing::debug!("Executing query: {}", query);
        sqlx::query(query).execute(&self.pool).await?;
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn fetch_one<T>(&self, query: &str) -> Result<T, sqlx::Error>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Unpin + Send,
    {
        tracing::debug!("Fetching one: {}", query);
        let result = sqlx::query_as(query).fetch_one(&self.pool).await?;
        Ok(result)
    }
}
```

---

## 8. 消息队列

### 8.1 Redis Streams 生产者

```rust
// common/src/messaging/producer.rs
use redis::{Client, AsyncCommands};
use tracing::instrument;
use serde::Serialize;

pub struct EventProducer {
    client: Client,
}

impl EventProducer {
    pub fn new(redis_url: &str) -> Result<Self, redis::RedisError> {
        let client = Client::open(redis_url)?;
        Ok(Self { client })
    }
    
    #[instrument(skip(self, event))]
    pub async fn publish<T: Serialize>(
        &self,
        stream: &str,
        event: &T,
    ) -> Result<(), Box<dyn std::error::Error>> {
        tracing::info!("Publishing event to stream: {}", stream);
        
        let mut con = self.client.get_async_connection().await?;
        
        let data = serde_json::to_string(event)?;
        
        con.xadd(stream, "*", &[("data", data)]).await?;
        
        tracing::info!("Event published successfully");
        
        Ok(())
    }
}
```

### 8.2 Redis Streams 消费者

```rust
// common/src/messaging/consumer.rs
use redis::{Client, AsyncCommands, streams::StreamReadReply};
use tracing::instrument;
use serde::de::DeserializeOwned;

pub struct EventConsumer {
    client: Client,
    group: String,
    consumer_name: String,
}

impl EventConsumer {
    pub fn new(redis_url: &str, group: &str, consumer_name: &str) -> Result<Self, redis::RedisError> {
        let client = Client::open(redis_url)?;
        Ok(Self {
            client,
            group: group.to_string(),
            consumer_name: consumer_name.to_string(),
        })
    }
    
    #[instrument(skip(self))]
    pub async fn consume<T: DeserializeOwned>(
        &self,
        stream: &str,
    ) -> Result<Vec<T>, Box<dyn std::error::Error>> {
        tracing::info!("Consuming from stream: {}", stream);
        
        let mut con = self.client.get_async_connection().await?;
        
        let reply: StreamReadReply = con.xread_group(
            &self.group,
            &self.consumer_name,
            &[stream],
            &[">"]
        ).await?;
        
        let mut events = Vec::new();
        
        for stream_messages in reply.keys {
            for message in stream_messages.ids {
                if let Some(data) = message.map.get("data") {
                    if let redis::Value::Data(bytes) = data {
                        let json = String::from_utf8(bytes.to_vec())?;
                        let event: T = serde_json::from_str(&json)?;
                        events.push(event);
                    }
                }
            }
        }
        
        tracing::info!("Consumed {} events", events.len());
        
        Ok(events)
    }
}
```

---

## 9. 可观测性配置

### 9.1 通用追踪初始化

```rust
// common/src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, Sampler, TracerProvider},
    Resource,
    runtime::Tokio,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use std::time::Duration;

pub fn init_tracer(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://jaeger:4317".to_string());
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&otlp_endpoint)
        .with_timeout(Duration::from_secs(10));
    
    let config = Config::default()
        .with_sampler(Sampler::TraceIdRatioBased(
            std::env::var("OTEL_TRACES_SAMPLER_ARG")
                .unwrap_or_else(|_| "1.0".to_string())
                .parse::<f64>()
                .unwrap_or(1.0)
        ))
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", service_name.to_string()),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        ]));
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_trace_config(config)
        .install_batch(Tokio)?;
    
    global::set_tracer_provider(tracer.clone());
    
    // 集成 tracing
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer.tracer(service_name));
    
    tracing_subscriber::registry()
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}
```

### 9.2 Metrics 配置

```rust
// common/src/metrics.rs
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram};
use std::sync::OnceLock;

static HTTP_REQUESTS: OnceLock<Counter<u64>> = OnceLock::new();
static HTTP_DURATION: OnceLock<Histogram<f64>> = OnceLock::new();

pub fn init_metrics() {
    let meter = global::meter("microservices");
    
    HTTP_REQUESTS.set(
        meter
            .u64_counter("http_requests_total")
            .with_description("Total HTTP requests")
            .init()
    ).ok();
    
    HTTP_DURATION.set(
        meter
            .f64_histogram("http_request_duration_seconds")
            .with_description("HTTP request duration in seconds")
            .init()
    ).ok();
}

pub fn record_request(method: &str, path: &str, status: u16, duration: f64) {
    if let Some(counter) = HTTP_REQUESTS.get() {
        counter.add(1, &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("path", path.to_string()),
            KeyValue::new("status", status as i64),
        ]);
    }
    
    if let Some(histogram) = HTTP_DURATION.get() {
        histogram.record(duration, &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("path", path.to_string()),
        ]);
    }
}
```

---

## 10. 部署指南

### 10.1 Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_USER: postgres
      POSTGRES_PASSWORD: postgres
      POSTGRES_DB: ecommerce
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  jaeger:
    image: jaegertracing/all-in-one:latest
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
    ports:
      - "4317:4317"   # OTLP gRPC
      - "16686:16686" # Jaeger UI
      - "14250:14250" # Jaeger gRPC

  api-gateway:
    build:
      context: .
      dockerfile: api-gateway/Dockerfile
    environment:
      DATABASE_URL: postgres://postgres:postgres@postgres/ecommerce
      REDIS_URL: redis://redis:6379
      OTEL_EXPORTER_OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info
    ports:
      - "8080:8080"
    depends_on:
      - postgres
      - redis
      - jaeger

  user-service:
    build:
      context: .
      dockerfile: user-service/Dockerfile
    environment:
      DATABASE_URL: postgres://postgres:postgres@postgres/ecommerce
      OTEL_EXPORTER_OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info
    depends_on:
      - postgres
      - jaeger

  order-service:
    build:
      context: .
      dockerfile: order-service/Dockerfile
    environment:
      DATABASE_URL: postgres://postgres:postgres@postgres/ecommerce
      REDIS_URL: redis://redis:6379
      OTEL_EXPORTER_OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info
    depends_on:
      - postgres
      - redis
      - jaeger

  inventory-service:
    build:
      context: .
      dockerfile: inventory-service/Dockerfile
    environment:
      DATABASE_URL: postgres://postgres:postgres@postgres/ecommerce
      OTEL_EXPORTER_OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info
    depends_on:
      - postgres
      - jaeger

volumes:
  postgres_data:
```

### 10.2 Dockerfile 示例

```dockerfile
# api-gateway/Dockerfile
FROM rust:1.90 as builder

WORKDIR /app

# 复制 workspace 配置
COPY Cargo.toml Cargo.lock ./

# 复制所有服务
COPY api-gateway ./api-gateway
COPY common ./common

# 构建
RUN cargo build --release --bin api-gateway

# 运行时镜像
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/api-gateway /usr/local/bin/

ENV RUST_LOG=info

EXPOSE 8080

CMD ["api-gateway"]
```

### 10.3 启动命令

```bash
# 启动所有服务
docker-compose up -d

# 查看日志
docker-compose logs -f

# 访问 Jaeger UI
open http://localhost:16686

# 测试 API
curl -X POST http://localhost:8080/api/users \
  -H "Content-Type: application/json" \
  -d '{"email":"test@example.com","name":"Test User"}'

# 创建订单
curl -X POST http://localhost:8080/api/orders \
  -H "Content-Type: application/json" \
  -d '{
    "user_id":"<user-id>",
    "product_id":"<product-id>",
    "quantity":5
  }'

# 停止服务
docker-compose down
```

---

## 🔗 参考资源

- [Axum 文档](https://docs.rs/axum/)
- [Tonic 文档](https://docs.rs/tonic/)
- [SQLx 文档](https://docs.rs/sqlx/)
- [OpenTelemetry Rust](https://docs.rs/opentelemetry/)
- [Rust OTLP 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)
- [Rust OTLP 常见模式](../33_教程与示例/02_Rust_OTLP_常见模式.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [📚 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md) | [❓ FAQ](../33_教程与示例/03_Rust_OTLP_FAQ.md)
