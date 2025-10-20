# 🎨 Poem 框架 + OTLP 集成 - OpenAPI 自动化追踪指南

> **文档版本**: v1.0  
> **创建日期**: 2025年10月11日  
> **Rust 版本**: 1.90+  
> **Poem 版本**: 3.1+  
> **OpenTelemetry**: 0.31.0  
> **难度等级**: ⭐⭐⭐⭐

---

## 📋 目录

- [🎨 Poem 框架 + OTLP 集成 - OpenAPI 自动化追踪指南](#-poem-框架--otlp-集成---openapi-自动化追踪指南)
  - [📋 目录](#-目录)
  - [🎯 Poem 框架概述](#-poem-框架概述)
    - [什么是 Poem？](#什么是-poem)
    - [为什么选择 Poem？](#为什么选择-poem)
  - [🧩 核心特性](#-核心特性)
    - [1. 快速开始](#1-快速开始)
    - [2. OpenAPI 集成](#2-openapi-集成)
  - [🔍 OTLP 中间件集成](#-otlp-中间件集成)
    - [1. 创建 OTLP 中间件](#1-创建-otlp-中间件)
    - [2. 完整的追踪配置](#2-完整的追踪配置)
  - [📖 OpenAPI 自动生成 + 追踪](#-openapi-自动生成--追踪)
    - [完整的 API 实现](#完整的-api-实现)
  - [🚀 GraphQL 集成](#-graphql-集成)
  - [📊 性能优化](#-性能优化)
    - [1. 连接池配置](#1-连接池配置)
    - [2. 响应缓存](#2-响应缓存)
  - [⚖️ 与 Axum 对比](#️-与-axum-对比)
  - [✅ 最佳实践](#-最佳实践)
    - [1. 项目结构](#1-项目结构)
    - [2. Cargo.toml](#2-cargotoml)
  - [📚 参考资源](#-参考资源)

---

## 🎯 Poem 框架概述

### 什么是 Poem？

**Poem** 是一个现代化的 Rust Web 框架，专注于:

- ✅ **OpenAPI 原生支持** - 自动生成 API 文档
- ✅ **类型安全** - 编译时验证 API 契约
- ✅ **高性能** - 基于 Tokio,性能接近 Axum
- ✅ **易用性** - 简洁的宏和类型推导

### 为什么选择 Poem？

| 特性 | Poem | Axum | Actix-web |
|------|------|------|-----------|
| **OpenAPI 生成** | ✅ 原生支持 | ❌ 需要额外库 | ⚠️ 社区插件 |
| **类型安全** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **学习曲线** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| **生态成熟度** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

**适用场景**:

- 🎯 需要自动生成 OpenAPI 文档的项目
- 🎯 API 优先设计 (API-first)
- 🎯 GraphQL + REST 混合架构
- 🎯 微服务 API Gateway

---

## 🧩 核心特性

### 1. 快速开始

```rust
use poem::{
    Route, Server,
    listener::TcpListener,
    web::{Json, Path},
    handler,
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
}

#[handler]
async fn create_user(Json(user): Json<User>) -> Json<User> {
    Json(user)
}

#[handler]
async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User {
        id,
        name: "Alice".to_string(),
    })
}

#[tokio::main]
async fn main() -> Result<(), std::io::Error> {
    let app = Route::new()
        .at("/users", poem::post(create_user))
        .at("/users/:id", poem::get(get_user));

    Server::new(TcpListener::bind("0.0.0.0:3000"))
        .run(app)
        .await
}
```

### 2. OpenAPI 集成

```rust
use poem_openapi::{
    OpenApi, OpenApiService,
    payload::Json,
    Object, Tags,
};
use poem::{Route, Server, listener::TcpListener};

/// API 标签
#[derive(Tags)]
enum ApiTags {
    /// 用户管理
    User,
    /// 订单管理
    Order,
}

/// 用户模型
#[derive(Debug, Object, Clone)]
struct User {
    /// 用户 ID
    id: u64,
    /// 用户名称
    #[oai(validator(max_length = 50))]
    name: String,
    /// 电子邮件
    #[oai(validator(email))]
    email: String,
}

/// 创建用户请求
#[derive(Debug, Object)]
struct CreateUserRequest {
    /// 用户名称
    name: String,
    /// 电子邮件
    email: String,
}

struct UserApi;

#[OpenApi]
impl UserApi {
    /// 创建用户
    /// 
    /// 创建一个新用户
    #[oai(path = "/users", method = "post", tag = "ApiTags::User")]
    async fn create_user(
        &self,
        req: Json<CreateUserRequest>,
    ) -> Json<User> {
        Json(User {
            id: 1,
            name: req.0.name,
            email: req.0.email,
        })
    }

    /// 获取用户
    /// 
    /// 通过 ID 获取用户信息
    #[oai(path = "/users/:id", method = "get", tag = "ApiTags::User")]
    async fn get_user(
        &self,
        #[oai(name = "id", in = "path")] id: u64,
    ) -> Json<User> {
        Json(User {
            id,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        })
    }
}

#[tokio::main]
async fn main() -> Result<(), std::io::Error> {
    // 创建 OpenAPI 服务
    let api_service = OpenApiService::new(UserApi, "User API", "1.0")
        .server("http://localhost:3000/api");

    // 挂载 Swagger UI
    let ui = api_service.swagger_ui();

    let app = Route::new()
        .nest("/api", api_service)
        .nest("/", ui);

    Server::new(TcpListener::bind("0.0.0.0:3000"))
        .run(app)
        .await
}
```

---

## 🔍 OTLP 中间件集成

### 1. 创建 OTLP 中间件

```rust
// src/middleware/telemetry.rs
use poem::{
    Endpoint, Middleware, Request, Result,
    http::StatusCode,
};
use opentelemetry::{
    global,
    trace::{Tracer, SpanKind, Status, TraceContextExt},
    KeyValue,
};
use tracing::{info, error};

/// OTLP 追踪中间件
pub struct TelemetryMiddleware;

impl<E: Endpoint> Middleware<E> for TelemetryMiddleware {
    type Output = TelemetryMiddlewareImpl<E>;

    fn transform(&self, ep: E) -> Self::Output {
        TelemetryMiddlewareImpl { ep }
    }
}

pub struct TelemetryMiddlewareImpl<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for TelemetryMiddlewareImpl<E> {
    type Output = E::Output;

    async fn call(&self, req: Request) -> Result<Self::Output> {
        let tracer = global::tracer("poem-api");
        
        // 创建 span
        let span = tracer
            .span_builder(format!("{} {}", req.method(), req.uri().path()))
            .with_kind(SpanKind::Server)
            .with_attributes(vec![
                KeyValue::new("http.method", req.method().to_string()),
                KeyValue::new("http.target", req.uri().path().to_string()),
                KeyValue::new("http.scheme", req.uri().scheme_str().unwrap_or("http").to_string()),
            ])
            .start(&tracer);

        let cx = opentelemetry::Context::current_with_span(span);
        let _guard = cx.attach();

        info!("收到请求: {} {}", req.method(), req.uri().path());

        // 执行请求
        let result = self.ep.call(req).await;

        // 记录结果
        match &result {
            Ok(_) => {
                cx.span().set_status(Status::Ok);
                info!("请求成功");
            }
            Err(e) => {
                let status_code = e.status().as_u16();
                cx.span().set_attribute(KeyValue::new("http.status_code", status_code as i64));
                cx.span().set_status(Status::error(format!("HTTP {}", status_code)));
                error!("请求失败: {}", e);
            }
        }

        result
    }
}

/// 使用示例
pub fn with_telemetry<E: Endpoint>(endpoint: E) -> impl Endpoint {
    endpoint.with(TelemetryMiddleware)
}
```

### 2. 完整的追踪配置

```rust
// src/telemetry/mod.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use std::time::Duration;

pub fn init_telemetry() -> anyhow::Result<()> {
    // 1. 配置 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
                .with_timeout(Duration::from_secs(3)),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "poem-api"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 2. 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info,poem_api=debug".into()),
        ))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

---

## 📖 OpenAPI 自动生成 + 追踪

### 完整的 API 实现

```rust
// src/api/user_api.rs
use poem_openapi::{
    OpenApi, OpenApiService,
    payload::Json,
    param::{Path, Query},
    Object, Tags, ApiResponse,
};
use serde::{Deserialize, Serialize};
use tracing::instrument;
use uuid::Uuid;

#[derive(Tags)]
enum ApiTags {
    /// 用户管理 API
    User,
}

/// 用户模型
#[derive(Debug, Object, Clone, Serialize, Deserialize)]
struct User {
    /// 用户 ID
    id: Uuid,
    /// 用户名
    #[oai(validator(max_length = 50))]
    name: String,
    /// 邮箱
    #[oai(validator(email))]
    email: String,
    /// 年龄
    #[oai(validator(minimum(value = "18"), maximum(value = "150")))]
    age: Option<u8>,
}

/// 创建用户请求
#[derive(Debug, Object)]
struct CreateUserRequest {
    /// 用户名
    name: String,
    /// 邮箱
    email: String,
    /// 年龄
    age: Option<u8>,
}

/// 更新用户请求
#[derive(Debug, Object)]
struct UpdateUserRequest {
    /// 用户名
    name: Option<String>,
    /// 邮箱
    email: Option<String>,
    /// 年龄
    age: Option<u8>,
}

/// 用户列表响应
#[derive(Debug, Object)]
struct UserListResponse {
    /// 用户列表
    users: Vec<User>,
    /// 总数
    total: usize,
}

/// API 响应
#[derive(ApiResponse)]
enum UserResponse {
    /// 成功
    #[oai(status = 200)]
    Ok(Json<User>),
    /// 未找到
    #[oai(status = 404)]
    NotFound,
    /// 内部错误
    #[oai(status = 500)]
    InternalError,
}

struct UserApi {
    // 这里可以注入数据库连接等依赖
    db: Arc<DatabasePool>,
}

impl UserApi {
    pub fn new(db: Arc<DatabasePool>) -> Self {
        Self { db }
    }
}

#[OpenApi(prefix_path = "/users", tag = "ApiTags::User")]
impl UserApi {
    /// 创建用户
    /// 
    /// 创建一个新用户
    #[oai(path = "/", method = "post")]
    #[instrument(skip(self))]
    async fn create_user(
        &self,
        req: Json<CreateUserRequest>,
    ) -> UserResponse {
        let user = User {
            id: Uuid::new_v4(),
            name: req.0.name,
            email: req.0.email,
            age: req.0.age,
        };

        // 保存到数据库
        match self.db.insert_user(&user).await {
            Ok(_) => UserResponse::Ok(Json(user)),
            Err(_) => UserResponse::InternalError,
        }
    }

    /// 获取用户
    /// 
    /// 通过 ID 获取用户信息
    #[oai(path = "/:id", method = "get")]
    #[instrument(skip(self))]
    async fn get_user(
        &self,
        /// 用户 ID
        id: Path<Uuid>,
    ) -> UserResponse {
        match self.db.get_user(id.0).await {
            Ok(Some(user)) => UserResponse::Ok(Json(user)),
            Ok(None) => UserResponse::NotFound,
            Err(_) => UserResponse::InternalError,
        }
    }

    /// 获取用户列表
    /// 
    /// 分页获取用户列表
    #[oai(path = "/", method = "get")]
    #[instrument(skip(self))]
    async fn list_users(
        &self,
        /// 页码（从 1 开始）
        #[oai(default = "1")]
        page: Query<u32>,
        /// 每页数量
        #[oai(default = "20")]
        page_size: Query<u32>,
    ) -> Json<UserListResponse> {
        let users = self.db.list_users(page.0, page_size.0).await.unwrap_or_default();
        let total = self.db.count_users().await.unwrap_or(0);

        Json(UserListResponse { users, total })
    }

    /// 更新用户
    /// 
    /// 更新用户信息
    #[oai(path = "/:id", method = "put")]
    #[instrument(skip(self))]
    async fn update_user(
        &self,
        /// 用户 ID
        id: Path<Uuid>,
        req: Json<UpdateUserRequest>,
    ) -> UserResponse {
        match self.db.update_user(id.0, req.0).await {
            Ok(Some(user)) => UserResponse::Ok(Json(user)),
            Ok(None) => UserResponse::NotFound,
            Err(_) => UserResponse::InternalError,
        }
    }

    /// 删除用户
    /// 
    /// 删除指定用户
    #[oai(path = "/:id", method = "delete")]
    #[instrument(skip(self))]
    async fn delete_user(
        &self,
        /// 用户 ID
        id: Path<Uuid>,
    ) -> UserResponse {
        match self.db.delete_user(id.0).await {
            Ok(true) => UserResponse::Ok(Json(User {
                id: id.0,
                name: "".to_string(),
                email: "".to_string(),
                age: None,
            })),
            Ok(false) => UserResponse::NotFound,
            Err(_) => UserResponse::InternalError,
        }
    }
}

// 数据库 Mock
struct DatabasePool;

impl DatabasePool {
    async fn insert_user(&self, _user: &User) -> Result<(), String> {
        Ok(())
    }

    async fn get_user(&self, _id: Uuid) -> Result<Option<User>, String> {
        Ok(Some(User {
            id: Uuid::new_v4(),
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            age: Some(25),
        }))
    }

    async fn list_users(&self, _page: u32, _size: u32) -> Result<Vec<User>, String> {
        Ok(vec![])
    }

    async fn count_users(&self) -> Result<usize, String> {
        Ok(0)
    }

    async fn update_user(&self, _id: Uuid, _req: UpdateUserRequest) -> Result<Option<User>, String> {
        Ok(None)
    }

    async fn delete_user(&self, _id: Uuid) -> Result<bool, String> {
        Ok(true)
    }
}
```

---

## 🚀 GraphQL 集成

```rust
// src/api/graphql_api.rs
use async_graphql::{
    Context, Object, Schema, EmptySubscription,
    SimpleObject, InputObject,
};
use poem::{
    Route, Server,
    listener::TcpListener,
    web::Json,
};
use poem_openapi::OpenApiService;
use tracing::instrument;
use uuid::Uuid;

/// 用户模型
#[derive(Debug, Clone, SimpleObject)]
struct User {
    id: Uuid,
    name: String,
    email: String,
}

/// 创建用户输入
#[derive(Debug, InputObject)]
struct CreateUserInput {
    name: String,
    email: String,
}

/// 查询根
struct QueryRoot;

#[Object]
impl QueryRoot {
    /// 获取用户
    #[instrument(skip(self, _ctx))]
    async fn user(&self, _ctx: &Context<'_>, id: Uuid) -> Option<User> {
        Some(User {
            id,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        })
    }

    /// 获取所有用户
    #[instrument(skip(self, _ctx))]
    async fn users(&self, _ctx: &Context<'_>) -> Vec<User> {
        vec![
            User {
                id: Uuid::new_v4(),
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
            },
            User {
                id: Uuid::new_v4(),
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
            },
        ]
    }
}

/// 变更根
struct MutationRoot;

#[Object]
impl MutationRoot {
    /// 创建用户
    #[instrument(skip(self, _ctx))]
    async fn create_user(
        &self,
        _ctx: &Context<'_>,
        input: CreateUserInput,
    ) -> User {
        User {
            id: Uuid::new_v4(),
            name: input.name,
            email: input.email,
        }
    }
}

/// 创建 GraphQL Schema
pub fn create_schema() -> Schema<QueryRoot, MutationRoot, EmptySubscription> {
    Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .finish()
}

/// GraphQL Endpoint
#[poem::handler]
async fn graphql_handler(
    schema: poem::web::Data<&Schema<QueryRoot, MutationRoot, EmptySubscription>>,
    req: async_graphql_poem::GraphQL<async_graphql::Request>,
) -> poem::Result<async_graphql_poem::GraphQL<async_graphql::Response>> {
    Ok(async_graphql_poem::GraphQL(schema.execute(req.0).await))
}

/// GraphQL Playground
#[poem::handler]
async fn graphql_playground() -> poem::web::Html<&'static str> {
    poem::web::Html(async_graphql::http::playground_source(
        async_graphql::http::GraphQLPlaygroundConfig::new("/graphql"),
    ))
}
```

---

## 📊 性能优化

### 1. 连接池配置

```rust
// src/database/pool.rs
use sqlx::{PgPool, postgres::PgPoolOptions};
use std::time::Duration;

pub async fn create_pool() -> anyhow::Result<PgPool> {
    let pool = PgPoolOptions::new()
        .max_connections(50)
        .min_connections(10)
        .acquire_timeout(Duration::from_secs(30))
        .idle_timeout(Duration::from_secs(600))
        .test_before_acquire(true)
        .connect(&std::env::var("DATABASE_URL")?)
        .await?;

    Ok(pool)
}
```

### 2. 响应缓存

```rust
// src/middleware/cache.rs
use poem::{Endpoint, Middleware, Request, Result};
use dashmap::DashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

pub struct CacheMiddleware {
    cache: Arc<DashMap<String, (Vec<u8>, Instant)>>,
    ttl: Duration,
}

impl CacheMiddleware {
    pub fn new(ttl: Duration) -> Self {
        Self {
            cache: Arc::new(DashMap::new()),
            ttl,
        }
    }

    fn cache_key(&self, req: &Request) -> String {
        format!("{} {}", req.method(), req.uri().path())
    }
}

impl<E: Endpoint> Middleware<E> for CacheMiddleware {
    type Output = CacheMiddlewareImpl<E>;

    fn transform(&self, ep: E) -> Self::Output {
        CacheMiddlewareImpl {
            ep,
            cache: self.cache.clone(),
            ttl: self.ttl,
        }
    }
}

pub struct CacheMiddlewareImpl<E> {
    ep: E,
    cache: Arc<DashMap<String, (Vec<u8>, Instant)>>,
    ttl: Duration,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for CacheMiddlewareImpl<E> {
    type Output = E::Output;

    async fn call(&self, req: Request) -> Result<Self::Output> {
        // 只缓存 GET 请求
        if req.method() != poem::http::Method::GET {
            return self.ep.call(req).await;
        }

        let key = format!("{} {}", req.method(), req.uri().path());

        // 检查缓存
        if let Some(entry) = self.cache.get(&key) {
            let (data, timestamp) = entry.value();
            if timestamp.elapsed() < self.ttl {
                // 缓存命中
                metrics::counter!("cache_hits", 1);
                // 返回缓存数据
                // 注意：这里需要根据实际情况处理响应
            }
        }

        // 缓存未命中,执行请求
        metrics::counter!("cache_misses", 1);
        self.ep.call(req).await
    }
}
```

---

## ⚖️ 与 Axum 对比

| 特性 | Poem | Axum |
|------|------|------|
| **OpenAPI** | ✅ 原生支持,自动生成 | ❌ 需要 `utoipa` 等库 |
| **类型安全** | ✅ 编译时验证 | ✅ 编译时验证 |
| **性能** | ⭐⭐⭐⭐⭐ (~98% Axum) | ⭐⭐⭐⭐⭐ (基准) |
| **生态系统** | ⭐⭐⭐ 新兴 | ⭐⭐⭐⭐⭐ Tokio 官方 |
| **学习曲线** | ⭐⭐⭐⭐ 稍陡峭 | ⭐⭐⭐ 较平缓 |
| **GraphQL** | ✅ `async-graphql-poem` | ✅ `async-graphql-axum` |
| **WebSocket** | ✅ 原生支持 | ✅ 原生支持 |
| **中间件** | ✅ Trait-based | ✅ Layer-based |

**选择建议**:

- 🎯 **选 Poem**: 需要 OpenAPI 自动化、API 优先设计
- 🎯 **选 Axum**: 需要成熟生态、Tokio 官方支持

---

## ✅ 最佳实践

### 1. 项目结构

```text
poem-api-project/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── api/
│   │   ├── mod.rs
│   │   ├── user_api.rs
│   │   ├── order_api.rs
│   │   └── graphql_api.rs
│   ├── models/
│   │   ├── mod.rs
│   │   ├── user.rs
│   │   └── order.rs
│   ├── database/
│   │   ├── mod.rs
│   │   └── pool.rs
│   ├── middleware/
│   │   ├── mod.rs
│   │   ├── telemetry.rs
│   │   └── cache.rs
│   └── telemetry/
│       └── mod.rs
└── openapi.json  # 自动生成
```

### 2. Cargo.toml

```toml
[package]
name = "poem-api"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Web 框架
poem = "3.1"
poem-openapi = { version = "5.1", features = ["swagger-ui"] }

# GraphQL
async-graphql = "7.0"
async-graphql-poem = "7.0"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }

# 追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["grpc-tonic"] }

# 指标
metrics = "0.23"
metrics-exporter-prometheus = "0.15"

# 工具
tokio = { version = "1.41", features = ["full"] }
anyhow = "1.0"
uuid = { version = "1.10", features = ["v4", "serde"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
dashmap = "6.1"
```

---

## 📚 参考资源

- [Poem 官方文档](https://docs.rs/poem/)
- [poem-openapi 文档](https://docs.rs/poem-openapi/)
- [async-graphql](https://async-graphql.github.io/async-graphql/)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust 框架团队  

---

**🎨 使用 Poem 构建自动化 OpenAPI 的现代 Web 服务！🚀**-
