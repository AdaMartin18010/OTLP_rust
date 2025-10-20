# Axum 高级特性深度解析 - Rust 1.90 + OTLP 完整集成指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90+  
> **核心依赖**: axum 0.7, tokio 1.40, tower 0.5, opentelemetry 0.31  
> **对齐标准**: RESTful API Design, CNCF OpenTelemetry, HTTP/1.1 & HTTP/2 RFCs

---

## 目录

- [Axum 高级特性深度解析 - Rust 1.90 + OTLP 完整集成指南](#axum-高级特性深度解析---rust-190--otlp-完整集成指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 Axum？](#11-什么是-axum)
    - [1.2 Axum 与其他框架对比](#12-axum-与其他框架对比)
    - [1.3 本文档目标](#13-本文档目标)
  - [2. 核心架构与设计理念](#2-核心架构与设计理念)
    - [2.1 基于 Tower 的分层架构](#21-基于-tower-的分层架构)
    - [2.2 提取器 (Extractor) 模式](#22-提取器-extractor-模式)
    - [2.3 响应构建 (IntoResponse)](#23-响应构建-intoresponse)
  - [3. 环境准备与依赖配置](#3-环境准备与依赖配置)
    - [3.1 Cargo.toml 依赖](#31-cargotoml-依赖)
    - [3.2 项目结构](#32-项目结构)
  - [4. 高级路由系统](#4-高级路由系统)
    - [4.1 基础路由定义](#41-基础路由定义)
    - [4.2 嵌套路由与版本控制](#42-嵌套路由与版本控制)
    - [4.3 路由组与中间件](#43-路由组与中间件)
    - [4.4 路径参数与查询参数](#44-路径参数与查询参数)
  - [5. 提取器 Extractor 深度应用](#5-提取器-extractor-深度应用)
    - [5.1 内置提取器](#51-内置提取器)
    - [5.2 自定义提取器](#52-自定义提取器)
    - [5.3 可选提取器](#53-可选提取器)
    - [5.4 提取器顺序](#54-提取器顺序)
  - [6. 状态管理与依赖注入](#6-状态管理与依赖注入)
    - [6.1 应用状态定义](#61-应用状态定义)
    - [6.2 使用 State 提取器](#62-使用-state-提取器)
    - [6.3 依赖注入模式](#63-依赖注入模式)
  - [7. 中间件系统完整实现](#7-中间件系统完整实现)
    - [7.1 认证中间件](#71-认证中间件)
    - [7.2 日志中间件](#72-日志中间件)
    - [7.3 限流中间件](#73-限流中间件)
    - [7.4 CORS 中间件](#74-cors-中间件)
    - [7.5 请求 ID 中间件](#75-请求-id-中间件)
  - [8. 错误处理与响应构建](#8-错误处理与响应构建)
    - [8.1 自定义错误类型](#81-自定义错误类型)
    - [8.2 验证错误处理](#82-验证错误处理)
    - [8.3 Result 组合响应](#83-result-组合响应)
    - [8.4 自定义响应头](#84-自定义响应头)
  - [9. WebSocket 实时通信](#9-websocket-实时通信)
    - [9.1 WebSocket 基础](#91-websocket-基础)
    - [9.2 聊天室实现](#92-聊天室实现)
  - [10. SSE (Server-Sent Events)](#10-sse-server-sent-events)
    - [10.1 SSE 基础实现](#101-sse-基础实现)
    - [10.2 实时日志流](#102-实时日志流)
    - [10.3 数据库变更通知](#103-数据库变更通知)
  - [11. 请求验证与序列化](#11-请求验证与序列化)
    - [11.1 使用 Validator](#111-使用-validator)
    - [11.2 自定义验证提取器](#112-自定义验证提取器)
  - [12. 数据库集成 SQLx](#12-数据库集成-sqlx)
    - [12.1 数据库连接池](#121-数据库连接池)
    - [12.2 CRUD 操作](#122-crud-操作)
    - [12.3 事务处理](#123-事务处理)
  - [13. OTLP 分布式追踪集成](#13-otlp-分布式追踪集成)
    - [13.1 OTLP 初始化](#131-otlp-初始化)
    - [13.2 HTTP 追踪中间件](#132-http-追踪中间件)
    - [13.3 自定义追踪 Span](#133-自定义追踪-span)
    - [13.4 分布式追踪传播](#134-分布式追踪传播)
  - [14. 性能优化与最佳实践](#14-性能优化与最佳实践)
    - [14.1 连接池优化](#141-连接池优化)
    - [14.2 响应压缩](#142-响应压缩)
    - [14.3 请求超时](#143-请求超时)
    - [14.4 并发限制](#144-并发限制)
    - [14.5 负载脱落](#145-负载脱落)
  - [15. 测试策略](#15-测试策略)
    - [15.1 单元测试](#151-单元测试)
    - [15.2 集成测试](#152-集成测试)
  - [16. 部署与监控](#16-部署与监控)
    - [16.1 Docker Compose](#161-docker-compose)
  - [17. 国际标准对齐](#17-国际标准对齐)
  - [18. 总结](#18-总结)

---

## 1. 概述

### 1.1 什么是 Axum？

**Axum** 是由 Tokio 团队开发的 Rust Web 框架，专注于人体工程学和模块化。它构建在 **Tower** 和 **Hyper** 之上，充分利用 Rust 的类型系统提供编译时安全性。

**核心特性**：

- **类型安全**: 利用 Rust 类型系统，编译时捕获错误
- **模块化**: 基于 Tower Service 和 Layer 抽象
- **高性能**: 基于 Hyper HTTP 库和 Tokio 运行时
- **人体工程学**: 最小化样板代码，直观的 API 设计
- **可扩展**: 丰富的中间件生态系统

### 1.2 Axum 与其他框架对比

| 特性 | Axum | Actix-Web | Rocket | Warp |
|------|------|-----------|--------|------|
| **类型安全** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **生态系统** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| **文档质量** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |

### 1.3 本文档目标

1. **全面覆盖**: Axum 所有核心特性和高级用法
2. **生产级实践**: 错误处理、中间件、状态管理、测试
3. **OTLP 集成**: 深度集成 OpenTelemetry 分布式追踪
4. **国际标准对齐**: RESTful API 设计、HTTP 标准、CNCF 最佳实践

---

## 2. 核心架构与设计理念

### 2.1 基于 Tower 的分层架构

Axum 的核心设计理念是**可组合性**，通过 Tower 的 `Service` 和 `Layer` trait 实现：

```text
┌─────────────────────────────────────┐
│         Application Layer           │
│    (Handler Functions + Routes)     │
├─────────────────────────────────────┤
│         Middleware Layer            │
│  (Logging, Auth, Rate Limit, etc.)  │
├─────────────────────────────────────┤
│          Tower Service              │
│  (Request → Response Transformation)│
├─────────────────────────────────────┤
│            Hyper HTTP               │
│      (HTTP/1.1, HTTP/2, HTTP/3)     │
├─────────────────────────────────────┤
│           Tokio Runtime             │
│        (Async I/O Executor)         │
└─────────────────────────────────────┘
```

### 2.2 提取器 (Extractor) 模式

Axum 使用 **Extractor** 模式从请求中提取数据，所有提取器实现 `FromRequest` 或 `FromRequestParts` trait：

```rust
#[async_trait]
pub trait FromRequest<S>: Sized {
    type Rejection: IntoResponse;

    async fn from_request(
        req: Request<Body>,
        state: &S,
    ) -> Result<Self, Self::Rejection>;
}
```

**内置提取器**：

- `Path<T>`: 路径参数
- `Query<T>`: 查询字符串
- `Json<T>`: JSON 请求体
- `State<T>`: 应用状态
- `Extension<T>`: 请求扩展
- `Headers`: HTTP 头部

### 2.3 响应构建 (IntoResponse)

所有 Handler 返回值必须实现 `IntoResponse` trait：

```rust
pub trait IntoResponse {
    fn into_response(self) -> Response;
}
```

**内置响应类型**：

- `Json<T>`: JSON 响应
- `Html<String>`: HTML 响应
- `StatusCode`: HTTP 状态码
- `(StatusCode, Json<T>)`: 组合响应
- `Result<T, E>`: 错误处理

---

## 3. 环境准备与依赖配置

### 3.1 Cargo.toml 依赖

```toml
[package]
name = "axum-otlp-example"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Axum 核心
axum = { version = "0.7", features = ["macros", "ws", "multipart"] }
axum-extra = { version = "0.9", features = ["typed-header", "cookie", "query"] }

# Tokio 异步运行时
tokio = { version = "1.40", features = ["full"] }
tokio-stream = "0.1"

# Tower 中间件
tower = { version = "0.5", features = ["util", "timeout", "limit", "load-shed", "buffer"] }
tower-http = { version = "0.6", features = [
    "trace", "timeout", "compression-gzip", "cors", "fs", "limit",
    "request-id", "sensitive-headers", "set-header"
] }

# HTTP 核心
hyper = { version = "1.5", features = ["full"] }
http = "1.1"
http-body-util = "0.1"

# OpenTelemetry 可观测性
opentelemetry = { version = "0.31", features = ["trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic", "trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "uuid", "chrono", "json"] }

# 工具库
uuid = { version = "1.11", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
thiserror = "2.0"
anyhow = "1.0"

# 验证
validator = { version = "0.18", features = ["derive"] }

# JWT
jsonwebtoken = "9.3"

# 密码哈希
argon2 = "0.5"

# 限流
governor = "0.7"

# WebSocket
futures = "0.3"

[dev-dependencies]
mockall = "0.13"
tokio-test = "0.4"
tower = { version = "0.5", features = ["util"] }
hyper = { version = "1.5", features = ["client"] }
```

### 3.2 项目结构

```text
axum-otlp-example/
├── src/
│   ├── main.rs                 # 应用入口
│   ├── routes/                 # 路由定义
│   │   ├── mod.rs
│   │   ├── users.rs
│   │   ├── posts.rs
│   │   └── websocket.rs
│   ├── handlers/               # 业务处理器
│   │   ├── mod.rs
│   │   ├── user_handlers.rs
│   │   └── post_handlers.rs
│   ├── middlewares/            # 中间件
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   ├── logging.rs
│   │   └── rate_limit.rs
│   ├── extractors/             # 自定义提取器
│   │   ├── mod.rs
│   │   └── authenticated_user.rs
│   ├── models/                 # 数据模型
│   │   ├── mod.rs
│   │   ├── user.rs
│   │   └── post.rs
│   ├── db/                     # 数据库层
│   │   ├── mod.rs
│   │   └── postgres.rs
│   ├── telemetry/              # 可观测性
│   │   ├── mod.rs
│   │   └── otlp.rs
│   └── errors.rs               # 错误处理
├── Cargo.toml
└── README.md
```

---

## 4. 高级路由系统

### 4.1 基础路由定义

```rust
// src/routes/mod.rs
use axum::{
    Router,
    routing::{get, post, put, delete},
};
use crate::handlers::{user_handlers, post_handlers};
use crate::AppState;

pub fn create_routes(state: AppState) -> Router {
    Router::new()
        // 健康检查
        .route("/health", get(health_check))
        // 用户路由
        .nest("/api/v1/users", user_routes())
        // 文章路由
        .nest("/api/v1/posts", post_routes())
        // WebSocket
        .route("/ws", get(crate::handlers::websocket_handler))
        // 共享状态
        .with_state(state)
}

fn user_routes() -> Router<AppState> {
    Router::new()
        .route("/", post(user_handlers::create_user))
        .route("/", get(user_handlers::list_users))
        .route("/:id", get(user_handlers::get_user))
        .route("/:id", put(user_handlers::update_user))
        .route("/:id", delete(user_handlers::delete_user))
}

fn post_routes() -> Router<AppState> {
    Router::new()
        .route("/", post(post_handlers::create_post))
        .route("/", get(post_handlers::list_posts))
        .route("/:id", get(post_handlers::get_post))
}

async fn health_check() -> &'static str {
    "OK"
}
```

### 4.2 嵌套路由与版本控制

```rust
pub fn create_routes(state: AppState) -> Router {
    Router::new()
        // API v1
        .nest("/api/v1", api_v1_routes())
        // API v2
        .nest("/api/v2", api_v2_routes())
        .with_state(state)
}

fn api_v1_routes() -> Router<AppState> {
    Router::new()
        .nest("/users", user_routes_v1())
        .nest("/posts", post_routes_v1())
}

fn api_v2_routes() -> Router<AppState> {
    Router::new()
        .nest("/users", user_routes_v2())
        .nest("/posts", post_routes_v2())
}
```

### 4.3 路由组与中间件

```rust
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    timeout::TimeoutLayer,
    compression::CompressionLayer,
};
use std::time::Duration;

pub fn create_routes(state: AppState) -> Router {
    // 公开路由（无需认证）
    let public_routes = Router::new()
        .route("/login", post(auth_handlers::login))
        .route("/register", post(auth_handlers::register));
    
    // 受保护路由（需要认证）
    let protected_routes = Router::new()
        .route("/profile", get(user_handlers::get_profile))
        .route("/posts", post(post_handlers::create_post))
        .layer(ServiceBuilder::new()
            // 认证中间件
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                crate::middlewares::auth::auth_middleware
            ))
            // 限流中间件
            .layer(axum::middleware::from_fn(
                crate::middlewares::rate_limit::rate_limit_middleware
            ))
        );
    
    // 管理员路由
    let admin_routes = Router::new()
        .route("/users", get(admin_handlers::list_all_users))
        .route("/users/:id/ban", post(admin_handlers::ban_user))
        .layer(axum::middleware::from_fn_with_state(
            state.clone(),
            crate::middlewares::auth::admin_middleware
        ));
    
    // 组合路由
    Router::new()
        .nest("/api/v1", public_routes)
        .nest("/api/v1", protected_routes)
        .nest("/api/v1/admin", admin_routes)
        // 全局中间件
        .layer(ServiceBuilder::new()
            // 超时
            .layer(TimeoutLayer::new(Duration::from_secs(30)))
            // Gzip 压缩
            .layer(CompressionLayer::new())
            // 追踪
            .layer(TraceLayer::new_for_http())
        )
        .with_state(state)
}
```

### 4.4 路径参数与查询参数

```rust
use axum::extract::{Path, Query};
use serde::Deserialize;

#[derive(Deserialize)]
pub struct Pagination {
    pub page: Option<u32>,
    pub page_size: Option<u32>,
}

#[derive(Deserialize)]
pub struct ListUsersQuery {
    pub filter: Option<String>,
    pub sort_by: Option<String>,
    #[serde(flatten)]
    pub pagination: Pagination,
}

// Handler: GET /users/:id
pub async fn get_user(
    Path(user_id): Path<String>,
) -> Result<Json<User>, AppError> {
    // 处理逻辑
}

// Handler: GET /users?filter=active&page=1&page_size=20
pub async fn list_users(
    Query(query): Query<ListUsersQuery>,
) -> Result<Json<Vec<User>>, AppError> {
    let page = query.pagination.page.unwrap_or(1);
    let page_size = query.pagination.page_size.unwrap_or(20);
    // 处理逻辑
}
```

---

## 5. 提取器 Extractor 深度应用

### 5.1 内置提取器

```rust
use axum::{
    extract::{Path, Query, Json, State, Extension, Form, Multipart},
    http::{HeaderMap, Method, Uri},
};

pub async fn complex_handler(
    // 路径参数
    Path(id): Path<String>,
    // 查询参数
    Query(params): Query<HashMap<String, String>>,
    // JSON 请求体
    Json(payload): Json<CreateUserRequest>,
    // 应用状态
    State(app_state): State<AppState>,
    // 请求扩展
    Extension(current_user): Extension<User>,
    // HTTP 头部
    headers: HeaderMap,
    // HTTP 方法
    method: Method,
    // 请求 URI
    uri: Uri,
) -> Result<Json<User>, AppError> {
    // 处理逻辑
}
```

### 5.2 自定义提取器

```rust
// src/extractors/authenticated_user.rs
use axum::{
    async_trait,
    extract::{FromRequestParts, TypedHeader},
    headers::{authorization::Bearer, Authorization},
    http::request::Parts,
    RequestPartsExt,
};
use crate::{AppState, errors::AppError, models::User};

/// 认证用户提取器
pub struct AuthenticatedUser(pub User);

#[async_trait]
impl FromRequestParts<AppState> for AuthenticatedUser {
    type Rejection = AppError;

    async fn from_request_parts(
        parts: &mut Parts,
        state: &AppState,
    ) -> Result<Self, Self::Rejection> {
        // 提取 Authorization 头部
        let TypedHeader(Authorization(bearer)) = parts
            .extract::<TypedHeader<Authorization<Bearer>>>()
            .await
            .map_err(|_| AppError::Unauthorized("Missing authorization header".to_string()))?;
        
        // 验证 JWT
        let token = bearer.token();
        let claims = crate::auth::verify_jwt(token)
            .map_err(|_| AppError::Unauthorized("Invalid token".to_string()))?;
        
        // 从数据库加载用户
        let user = sqlx::query_as::<_, User>(
            "SELECT * FROM users WHERE id = $1"
        )
        .bind(&claims.sub)
        .fetch_one(&state.db)
        .await
        .map_err(|_| AppError::Unauthorized("User not found".to_string()))?;
        
        Ok(AuthenticatedUser(user))
    }
}

// 使用自定义提取器
pub async fn get_profile(
    AuthenticatedUser(user): AuthenticatedUser,
) -> Json<User> {
    Json(user)
}
```

### 5.3 可选提取器

```rust
use axum::extract::Query;

#[derive(Deserialize)]
pub struct OptionalAuth {
    pub token: Option<String>,
}

pub async fn optional_auth_handler(
    Query(auth): Query<OptionalAuth>,
) -> String {
    match auth.token {
        Some(token) => format!("Authenticated with token: {}", token),
        None => "Anonymous request".to_string(),
    }
}
```

### 5.4 提取器顺序

提取器的顺序很重要，以下规则必须遵守：

1. **消耗请求体的提取器**（如 `Json<T>`, `String`, `Bytes`）必须放在最后
2. **`State`** 可以放在任何位置
3. **`Extension`** 和 **`Path`** 可以放在任何位置

```rust
// ✅ 正确：State 在 Json 之前
pub async fn handler(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {}

// ❌ 错误：Json 在 State 之前
pub async fn handler(
    Json(payload): Json<CreateUserRequest>,
    State(state): State<AppState>,
) -> Result<Json<User>, AppError> {}
```

---

## 6. 状态管理与依赖注入

### 6.1 应用状态定义

```rust
// src/main.rs
use sqlx::PgPool;
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    pub db: PgPool,
    pub config: Arc<Config>,
    pub jwt_secret: String,
}

pub struct Config {
    pub app_name: String,
    pub app_version: String,
    pub environment: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建数据库连接池
    let db = PgPool::connect(&std::env::var("DATABASE_URL")?).await?;
    
    // 创建应用状态
    let state = AppState {
        db,
        config: Arc::new(Config {
            app_name: "Axum OTLP Example".to_string(),
            app_version: env!("CARGO_PKG_VERSION").to_string(),
            environment: "production".to_string(),
        }),
        jwt_secret: std::env::var("JWT_SECRET")?,
    };
    
    // 创建路由
    let app = create_routes(state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

### 6.2 使用 State 提取器

```rust
use axum::extract::State;

pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    // 访问数据库连接池
    let user = sqlx::query_as::<_, User>(
        "INSERT INTO users (username, email) VALUES ($1, $2) RETURNING *"
    )
    .bind(&payload.username)
    .bind(&payload.email)
    .fetch_one(&state.db)
    .await?;
    
    // 访问配置
    tracing::info!(
        app_name = %state.config.app_name,
        "User created"
    );
    
    Ok(Json(user))
}
```

### 6.3 依赖注入模式

```rust
use std::sync::Arc;

pub trait UserRepository: Send + Sync {
    async fn create(&self, req: CreateUserRequest) -> Result<User, AppError>;
    async fn find_by_id(&self, id: &str) -> Result<User, AppError>;
}

pub struct PostgresUserRepository {
    db: PgPool,
}

impl UserRepository for PostgresUserRepository {
    async fn create(&self, req: CreateUserRequest) -> Result<User, AppError> {
        // 实现
    }
    
    async fn find_by_id(&self, id: &str) -> Result<User, AppError> {
        // 实现
    }
}

#[derive(Clone)]
pub struct AppState {
    pub user_repo: Arc<dyn UserRepository>,
}

pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    let user = state.user_repo.create(payload).await?;
    Ok(Json(user))
}
```

---

## 7. 中间件系统完整实现

### 7.1 认证中间件

```rust
// src/middlewares/auth.rs
use axum::{
    middleware::Next,
    http::{Request, StatusCode},
    response::Response,
    extract::State,
};
use crate::{AppState, auth::verify_jwt};

pub async fn auth_middleware<B>(
    State(state): State<AppState>,
    mut req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    // 提取 Authorization 头部
    let auth_header = req.headers()
        .get("authorization")
        .and_then(|value| value.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    if !auth_header.starts_with("Bearer ") {
        return Err(StatusCode::UNAUTHORIZED);
    }
    
    let token = &auth_header[7..];
    
    // 验证 JWT
    let claims = verify_jwt(token, &state.jwt_secret)
        .map_err(|_| StatusCode::UNAUTHORIZED)?;
    
    // 从数据库加载用户
    let user = sqlx::query_as::<_, User>(
        "SELECT * FROM users WHERE id = $1"
    )
    .bind(&claims.sub)
    .fetch_one(&state.db)
    .await
    .map_err(|_| StatusCode::UNAUTHORIZED)?;
    
    // 将用户注入到请求扩展
    req.extensions_mut().insert(user);
    
    Ok(next.run(req).await)
}
```

### 7.2 日志中间件

```rust
// src/middlewares/logging.rs
use axum::{
    middleware::Next,
    http::Request,
    response::Response,
};
use tracing::{info, error, Span};
use std::time::Instant;

pub async fn logging_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let uri = req.uri().clone();
    let version = req.version();
    
    // 为每个请求创建一个 span
    let span = tracing::info_span!(
        "http_request",
        method = %method,
        uri = %uri,
        version = ?version,
    );
    
    let _enter = span.enter();
    
    info!("Request started");
    
    // 执行请求
    let response = next.run(req).await;
    
    let duration = start.elapsed();
    let status = response.status();
    
    if status.is_success() {
        info!(
            status = %status,
            duration_ms = %duration.as_millis(),
            "Request completed"
        );
    } else {
        error!(
            status = %status,
            duration_ms = %duration.as_millis(),
            "Request failed"
        );
    }
    
    response
}
```

### 7.3 限流中间件

```rust
// src/middlewares/rate_limit.rs
use axum::{
    middleware::Next,
    http::{Request, StatusCode},
    response::{Response, IntoResponse},
};
use governor::{
    Quota, RateLimiter,
    state::{direct::NotKeyed, InMemoryState},
    clock::DefaultClock,
};
use std::sync::Arc;
use std::num::NonZeroU32;

pub struct RateLimitLayer {
    limiter: Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
}

impl RateLimitLayer {
    pub fn new(requests_per_second: u32) -> Self {
        let quota = Quota::per_second(NonZeroU32::new(requests_per_second).unwrap());
        let limiter = Arc::new(RateLimiter::direct(quota));
        
        Self { limiter }
    }
}

pub async fn rate_limit_middleware<B>(
    limiter: Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    match limiter.check() {
        Ok(_) => Ok(next.run(req).await),
        Err(_) => {
            tracing::warn!("Rate limit exceeded");
            Err(StatusCode::TOO_MANY_REQUESTS)
        }
    }
}
```

### 7.4 CORS 中间件

```rust
use tower_http::cors::{CorsLayer, Any};
use http::Method;

pub fn create_routes(state: AppState) -> Router {
    Router::new()
        .route("/api/users", get(list_users))
        .layer(
            CorsLayer::new()
                // 允许所有来源（生产环境应限制）
                .allow_origin(Any)
                // 允许的方法
                .allow_methods([
                    Method::GET,
                    Method::POST,
                    Method::PUT,
                    Method::DELETE,
                    Method::OPTIONS,
                ])
                // 允许的头部
                .allow_headers(Any)
                // 暴露的头部
                .expose_headers(Any)
                // 凭证支持
                .allow_credentials(true)
                // 预检请求缓存时间
                .max_age(Duration::from_secs(3600))
        )
        .with_state(state)
}
```

### 7.5 请求 ID 中间件

```rust
use tower_http::request_id::{
    SetRequestIdLayer, PropagateRequestIdLayer, MakeRequestUuid
};

pub fn create_routes(state: AppState) -> Router {
    Router::new()
        .route("/api/users", get(list_users))
        .layer(ServiceBuilder::new()
            // 生成请求 ID
            .layer(SetRequestIdLayer::x_request_id(MakeRequestUuid))
            // 传播请求 ID 到响应头
            .layer(PropagateRequestIdLayer::x_request_id())
        )
        .with_state(state)
}
```

---

## 8. 错误处理与响应构建

### 8.1 自定义错误类型

```rust
// src/errors.rs
use axum::{
    http::StatusCode,
    response::{Response, IntoResponse},
    Json,
};
use serde::Serialize;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
    
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Unauthorized: {0}")]
    Unauthorized(String),
    
    #[error("Validation error: {0}")]
    ValidationError(String),
    
    #[error("Internal server error: {0}")]
    InternalError(String),
}

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    details: Option<serde_json::Value>,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, error_type, message) = match &self {
            AppError::DatabaseError(e) => {
                tracing::error!(error = %e, "Database error");
                (StatusCode::INTERNAL_SERVER_ERROR, "database_error", "Database error occurred")
            }
            AppError::NotFound(msg) => {
                (StatusCode::NOT_FOUND, "not_found", msg.as_str())
            }
            AppError::Unauthorized(msg) => {
                (StatusCode::UNAUTHORIZED, "unauthorized", msg.as_str())
            }
            AppError::ValidationError(msg) => {
                (StatusCode::BAD_REQUEST, "validation_error", msg.as_str())
            }
            AppError::InternalError(msg) => {
                tracing::error!(error = %msg, "Internal error");
                (StatusCode::INTERNAL_SERVER_ERROR, "internal_error", "Internal server error")
            }
        };
        
        let body = Json(ErrorResponse {
            error: error_type.to_string(),
            message: message.to_string(),
            details: None,
        });
        
        (status, body).into_response()
    }
}
```

### 8.2 验证错误处理

```rust
use validator::{Validate, ValidationErrors};

#[derive(Deserialize, Validate)]
pub struct CreateUserRequest {
    #[validate(length(min = 3, max = 50))]
    pub username: String,
    
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8))]
    pub password: String,
}

pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    // 验证输入
    payload.validate()
        .map_err(|e: ValidationErrors| {
            AppError::ValidationError(format!("{:?}", e))
        })?;
    
    // 处理逻辑
}
```

### 8.3 Result 组合响应

```rust
use axum::http::StatusCode;

// 返回 201 Created + JSON
pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), AppError> {
    let user = state.user_repo.create(payload).await?;
    Ok((StatusCode::CREATED, Json(user)))
}

// 返回 204 No Content
pub async fn delete_user(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<StatusCode, AppError> {
    state.user_repo.delete(&id).await?;
    Ok(StatusCode::NO_CONTENT)
}
```

### 8.4 自定义响应头

```rust
use axum::{
    http::HeaderMap,
    response::AppendHeaders,
};

pub async fn get_user_with_cache(
    Path(id): Path<String>,
) -> Result<(AppendHeaders<[(String, String); 1]>, Json<User>), AppError> {
    let user = fetch_user(&id).await?;
    
    let headers = AppendHeaders([
        ("Cache-Control".to_string(), "max-age=3600".to_string()),
    ]);
    
    Ok((headers, Json(user)))
}
```

---

## 9. WebSocket 实时通信

### 9.1 WebSocket 基础

```rust
// src/handlers/websocket.rs
use axum::{
    extract::{ws::{WebSocket, WebSocketUpgrade, Message}, State},
    response::IntoResponse,
};
use futures::{sink::SinkExt, stream::StreamExt};
use tracing::{info, error};

pub async fn websocket_handler(
    ws: WebSocketUpgrade,
    State(state): State<AppState>,
) -> impl IntoResponse {
    ws.on_upgrade(|socket| handle_socket(socket, state))
}

async fn handle_socket(socket: WebSocket, state: AppState) {
    let (mut sender, mut receiver) = socket.split();
    
    info!("WebSocket connection established");
    
    // 接收消息任务
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(msg)) = receiver.next().await {
            match msg {
                Message::Text(text) => {
                    info!(message = %text, "Received text message");
                    // 处理文本消息
                }
                Message::Binary(data) => {
                    info!(size = data.len(), "Received binary message");
                    // 处理二进制消息
                }
                Message::Ping(data) => {
                    info!("Received ping");
                    // Axum 自动处理 pong 响应
                }
                Message::Pong(_) => {
                    info!("Received pong");
                }
                Message::Close(_) => {
                    info!("Client requested close");
                    break;
                }
            }
        }
    });
    
    // 发送消息任务
    let mut send_task = tokio::spawn(async move {
        for i in 0..10 {
            if sender
                .send(Message::Text(format!("Server message {}", i)))
                .await
                .is_err()
            {
                error!("Failed to send message");
                break;
            }
            
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        }
    });
    
    // 等待任务完成
    tokio::select! {
        _ = (&mut recv_task) => send_task.abort(),
        _ = (&mut send_task) => recv_task.abort(),
    }
    
    info!("WebSocket connection closed");
}
```

### 9.2 聊天室实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::broadcast;

#[derive(Clone)]
pub struct ChatState {
    rooms: Arc<Mutex<HashMap<String, broadcast::Sender<String>>>>,
}

impl ChatState {
    pub fn new() -> Self {
        Self {
            rooms: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_or_create_room(&self, room_id: &str) -> broadcast::Sender<String> {
        let mut rooms = self.rooms.lock().unwrap();
        
        rooms.entry(room_id.to_string())
            .or_insert_with(|| broadcast::channel(100).0)
            .clone()
    }
}

pub async fn chat_room_handler(
    ws: WebSocketUpgrade,
    Path(room_id): Path<String>,
    State(chat_state): State<ChatState>,
) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_chat_socket(socket, room_id, chat_state))
}

async fn handle_chat_socket(socket: WebSocket, room_id: String, chat_state: ChatState) {
    let (mut sender, mut receiver) = socket.split();
    
    // 加入聊天室
    let tx = chat_state.get_or_create_room(&room_id);
    let mut rx = tx.subscribe();
    
    info!(room_id = %room_id, "User joined chat room");
    
    // 接收来自客户端的消息
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(Message::Text(text))) = receiver.next().await {
            // 广播消息到房间
            if tx.send(text).is_err() {
                break;
            }
        }
    });
    
    // 发送消息到客户端
    let mut send_task = tokio::spawn(async move {
        while let Ok(msg) = rx.recv().await {
            if sender
                .send(Message::Text(msg))
                .await
                .is_err()
            {
                break;
            }
        }
    });
    
    tokio::select! {
        _ = (&mut recv_task) => send_task.abort(),
        _ = (&mut send_task) => recv_task.abort(),
    }
    
    info!(room_id = %room_id, "User left chat room");
}
```

---

## 10. SSE (Server-Sent Events)

### 10.1 SSE 基础实现

```rust
use axum::{
    response::sse::{Event, Sse},
    extract::State,
};
use tokio_stream::Stream;
use std::time::Duration;
use std::convert::Infallible;

pub async fn sse_handler(
    State(state): State<AppState>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let stream = tokio_stream::wrappers::IntervalStream::new(
        tokio::time::interval(Duration::from_secs(1))
    )
    .map(|_| {
        let event = Event::default()
            .event("message")
            .data(format!("Current time: {}", chrono::Utc::now()));
        
        Ok(event)
    });
    
    Sse::new(stream)
        .keep_alive(
            axum::response::sse::KeepAlive::new()
                .interval(Duration::from_secs(10))
                .text("keep-alive")
        )
}
```

### 10.2 实时日志流

```rust
use tokio::sync::broadcast;

#[derive(Clone)]
pub struct LogStream {
    tx: broadcast::Sender<String>,
}

impl LogStream {
    pub fn new() -> Self {
        let (tx, _) = broadcast::channel(100);
        Self { tx }
    }
    
    pub fn send_log(&self, message: String) {
        let _ = self.tx.send(message);
    }
}

pub async fn log_stream_handler(
    State(log_stream): State<LogStream>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let mut rx = log_stream.tx.subscribe();
    
    let stream = async_stream::stream! {
        while let Ok(msg) = rx.recv().await {
            yield Ok(Event::default().data(msg));
        }
    };
    
    Sse::new(stream)
}
```

### 10.3 数据库变更通知

```rust
pub async fn db_changes_handler(
    State(state): State<AppState>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let stream = async_stream::stream! {
        let mut listener = sqlx::postgres::PgListener::connect_with(&state.db).await.unwrap();
        listener.listen("user_changes").await.unwrap();
        
        while let Some(notification) = listener.recv().await.ok() {
            let event = Event::default()
                .event("user_change")
                .data(notification.payload());
            
            yield Ok(event);
        }
    };
    
    Sse::new(stream)
}
```

---

## 11. 请求验证与序列化

### 11.1 使用 Validator

```rust
use validator::{Validate, ValidationError};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Validate)]
pub struct CreateUserRequest {
    #[validate(length(min = 3, max = 50, message = "Username must be 3-50 characters"))]
    pub username: String,
    
    #[validate(email(message = "Invalid email format"))]
    pub email: String,
    
    #[validate(length(min = 8, message = "Password must be at least 8 characters"))]
    #[validate(custom = "validate_password_complexity")]
    pub password: String,
    
    #[validate(range(min = 18, max = 120, message = "Age must be 18-120"))]
    pub age: Option<u8>,
}

fn validate_password_complexity(password: &str) -> Result<(), ValidationError> {
    let has_uppercase = password.chars().any(|c| c.is_uppercase());
    let has_lowercase = password.chars().any(|c| c.is_lowercase());
    let has_digit = password.chars().any(|c| c.is_numeric());
    
    if has_uppercase && has_lowercase && has_digit {
        Ok(())
    } else {
        Err(ValidationError::new("password_complexity"))
    }
}

pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    // 验证
    payload.validate()?;
    
    // 处理逻辑
}
```

### 11.2 自定义验证提取器

```rust
use axum::{
    async_trait,
    extract::{FromRequest, Request},
    Json,
};

pub struct ValidatedJson<T>(pub T);

#[async_trait]
impl<T, S> FromRequest<S> for ValidatedJson<T>
where
    T: Validate + serde::de::DeserializeOwned,
    S: Send + Sync,
{
    type Rejection = AppError;

    async fn from_request(req: Request, state: &S) -> Result<Self, Self::Rejection> {
        let Json(value) = Json::<T>::from_request(req, state)
            .await
            .map_err(|_| AppError::ValidationError("Invalid JSON".to_string()))?;
        
        value.validate()
            .map_err(|e| AppError::ValidationError(format!("{:?}", e)))?;
        
        Ok(ValidatedJson(value))
    }
}

// 使用
pub async fn create_user(
    State(state): State<AppState>,
    ValidatedJson(payload): ValidatedJson<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    // payload 已经验证过了
}
```

---

## 12. 数据库集成 SQLx

### 12.1 数据库连接池

```rust
use sqlx::{PgPool, postgres::PgPoolOptions};
use std::time::Duration;

pub async fn create_db_pool(database_url: &str) -> anyhow::Result<PgPool> {
    let pool = PgPoolOptions::new()
        .max_connections(20)
        .min_connections(5)
        .acquire_timeout(Duration::from_secs(30))
        .idle_timeout(Some(Duration::from_secs(300)))
        .max_lifetime(Some(Duration::from_secs(1800)))
        .connect(database_url)
        .await?;
    
    Ok(pool)
}
```

### 12.2 CRUD 操作

```rust
// src/db/users.rs
use sqlx::PgPool;
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(sqlx::FromRow, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub password_hash: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

pub async fn create_user(
    pool: &PgPool,
    username: &str,
    email: &str,
    password_hash: &str,
) -> Result<User, sqlx::Error> {
    sqlx::query_as::<_, User>(
        r#"
        INSERT INTO users (id, username, email, password_hash, created_at, updated_at)
        VALUES ($1, $2, $3, $4, NOW(), NOW())
        RETURNING *
        "#
    )
    .bind(Uuid::new_v4())
    .bind(username)
    .bind(email)
    .bind(password_hash)
    .fetch_one(pool)
    .await
}

pub async fn find_user_by_id(
    pool: &PgPool,
    id: Uuid,
) -> Result<User, sqlx::Error> {
    sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
        .bind(id)
        .fetch_one(pool)
        .await
}

pub async fn list_users(
    pool: &PgPool,
    page: i64,
    page_size: i64,
) -> Result<Vec<User>, sqlx::Error> {
    let offset = (page - 1) * page_size;
    
    sqlx::query_as::<_, User>(
        "SELECT * FROM users ORDER BY created_at DESC LIMIT $1 OFFSET $2"
    )
    .bind(page_size)
    .bind(offset)
    .fetch_all(pool)
    .await
}

pub async fn update_user(
    pool: &PgPool,
    id: Uuid,
    username: &str,
    email: &str,
) -> Result<User, sqlx::Error> {
    sqlx::query_as::<_, User>(
        r#"
        UPDATE users
        SET username = $2, email = $3, updated_at = NOW()
        WHERE id = $1
        RETURNING *
        "#
    )
    .bind(id)
    .bind(username)
    .bind(email)
    .fetch_one(pool)
    .await
}

pub async fn delete_user(
    pool: &PgPool,
    id: Uuid,
) -> Result<(), sqlx::Error> {
    sqlx::query("DELETE FROM users WHERE id = $1")
        .bind(id)
        .execute(pool)
        .await?;
    
    Ok(())
}
```

### 12.3 事务处理

```rust
pub async fn transfer_balance(
    pool: &PgPool,
    from_user_id: Uuid,
    to_user_id: Uuid,
    amount: i64,
) -> Result<(), AppError> {
    let mut tx = pool.begin().await?;
    
    // 扣除发送方余额
    sqlx::query(
        "UPDATE accounts SET balance = balance - $1 WHERE user_id = $2 AND balance >= $1"
    )
    .bind(amount)
    .bind(from_user_id)
    .execute(&mut *tx)
    .await?;
    
    // 增加接收方余额
    sqlx::query(
        "UPDATE accounts SET balance = balance + $1 WHERE user_id = $2"
    )
    .bind(amount)
    .bind(to_user_id)
    .execute(&mut *tx)
    .await?;
    
    // 记录交易
    sqlx::query(
        r#"
        INSERT INTO transactions (from_user_id, to_user_id, amount, created_at)
        VALUES ($1, $2, $3, NOW())
        "#
    )
    .bind(from_user_id)
    .bind(to_user_id)
    .bind(amount)
    .execute(&mut *tx)
    .await?;
    
    tx.commit().await?;
    
    Ok(())
}
```

---

## 13. OTLP 分布式追踪集成

### 13.1 OTLP 初始化

```rust
// src/telemetry/otlp.rs
use opentelemetry::{
    global,
    trace::{TracerProvider as _, TraceError},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use anyhow::Result;

pub fn init_otlp_tracing(service_name: &str) -> Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::config()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(
            tracing_subscriber::fmt::layer()
                .with_target(true)
                .with_level(true)
        )
        .with(EnvFilter::from_default_env()
            .add_directive(tracing::Level::INFO.into()))
        .init();
    
    Ok(())
}

pub fn shutdown_otlp_tracing() {
    global::shutdown_tracer_provider();
}
```

### 13.2 HTTP 追踪中间件

```rust
use tower_http::trace::{TraceLayer, DefaultMakeSpan, DefaultOnResponse};
use tower_http::LatencyUnit;

pub fn create_routes(state: AppState) -> Router {
    Router::new()
        .route("/api/users", get(list_users))
        .layer(
            TraceLayer::new_for_http()
                // 为每个请求创建 span
                .make_span_with(DefaultMakeSpan::new()
                    .level(tracing::Level::INFO)
                    .include_headers(true))
                // 响应时记录
                .on_response(DefaultOnResponse::new()
                    .level(tracing::Level::INFO)
                    .latency_unit(LatencyUnit::Millis))
        )
        .with_state(state)
}
```

### 13.3 自定义追踪 Span

```rust
use tracing::{info, error, instrument};

#[instrument(
    skip(state),
    fields(
        otel.kind = "server",
        http.method = "POST",
        http.route = "/api/users"
    )
)]
pub async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    info!(
        username = %payload.username,
        email = %payload.email,
        "Creating user"
    );
    
    // 数据库操作（自动创建子 span）
    let user = create_user_in_db(&state.db, payload).await?;
    
    info!(user_id = %user.id, "User created successfully");
    
    Ok(Json(user))
}

#[instrument(skip(pool))]
async fn create_user_in_db(
    pool: &PgPool,
    payload: CreateUserRequest,
) -> Result<User, AppError> {
    let user = sqlx::query_as::<_, User>(
        "INSERT INTO users (username, email) VALUES ($1, $2) RETURNING *"
    )
    .bind(&payload.username)
    .bind(&payload.email)
    .fetch_one(pool)
    .await?;
    
    Ok(user)
}
```

### 13.4 分布式追踪传播

```rust
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;
use std::collections::HashMap;

// 客户端发送请求
pub async fn call_downstream_service(user_id: &str) -> Result<String, AppError> {
    let client = reqwest::Client::new();
    
    // 提取当前 span 的 trace context
    let cx = tracing::Span::current().context();
    let mut headers = HashMap::new();
    
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut headers);
    });
    
    // 发送请求
    let response = client
        .get(format!("http://downstream-service/users/{}", user_id))
        .headers(headers.into_iter().collect())
        .send()
        .await?;
    
    Ok(response.text().await?)
}
```

---

## 14. 性能优化与最佳实践

### 14.1 连接池优化

```rust
let pool = PgPoolOptions::new()
    // 最大连接数（根据 CPU 核心数调整）
    .max_connections(num_cpus::get() as u32 * 4)
    // 最小连接数（保持热连接）
    .min_connections(5)
    // 获取连接超时
    .acquire_timeout(Duration::from_secs(30))
    // 空闲连接超时
    .idle_timeout(Some(Duration::from_secs(300)))
    // 连接最大生命周期
    .max_lifetime(Some(Duration::from_secs(1800)))
    // 测试连接有效性
    .test_before_acquire(true)
    .connect(database_url)
    .await?;
```

### 14.2 响应压缩

```rust
use tower_http::compression::CompressionLayer;

Router::new()
    .route("/api/users", get(list_users))
    .layer(CompressionLayer::new()
        .gzip(true)
        .br(true)
        .deflate(true))
```

### 14.3 请求超时

```rust
use tower_http::timeout::TimeoutLayer;
use std::time::Duration;

Router::new()
    .route("/api/users", get(list_users))
    .layer(TimeoutLayer::new(Duration::from_secs(30)))
```

### 14.4 并发限制

```rust
use tower::limit::ConcurrencyLimitLayer;

Router::new()
    .route("/api/users", get(list_users))
    .layer(ConcurrencyLimitLayer::new(1000))
```

### 14.5 负载脱落

```rust
use tower::load_shed::LoadShedLayer;

Router::new()
    .route("/api/users", get(list_users))
    .layer(LoadShedLayer::new())
```

---

## 15. 测试策略

### 15.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::StatusCode;
    use axum_test_helper::TestClient;
    
    #[tokio::test]
    async fn test_create_user() {
        let app = create_test_app().await;
        let client = TestClient::new(app);
        
        let response = client
            .post("/api/users")
            .json(&serde_json::json!({
                "username": "testuser",
                "email": "test@example.com"
            }))
            .send()
            .await;
        
        assert_eq!(response.status(), StatusCode::CREATED);
        
        let user: User = response.json().await;
        assert_eq!(user.username, "testuser");
    }
}
```

### 15.2 集成测试

```rust
#[tokio::test]
async fn test_user_lifecycle() {
    let app = create_test_app().await;
    let client = TestClient::new(app);
    
    // 1. 创建用户
    let response = client.post("/api/users")
        .json(&create_user_payload())
        .send()
        .await;
    
    assert_eq!(response.status(), StatusCode::CREATED);
    let user: User = response.json().await;
    
    // 2. 获取用户
    let response = client.get(&format!("/api/users/{}", user.id))
        .send()
        .await;
    
    assert_eq!(response.status(), StatusCode::OK);
    
    // 3. 更新用户
    let response = client.put(&format!("/api/users/{}", user.id))
        .json(&update_user_payload())
        .send()
        .await;
    
    assert_eq!(response.status(), StatusCode::OK);
    
    // 4. 删除用户
    let response = client.delete(&format!("/api/users/{}", user.id))
        .send()
        .await;
    
    assert_eq!(response.status(), StatusCode::NO_CONTENT);
}
```

---

## 16. 部署与监控

### 16.1 Docker Compose

```yaml
version: '3.8'

services:
  axum-app:
    build: .
    ports:
      - "3000:3000"
    environment:
      - DATABASE_URL=postgres://admin:admin123@postgres:5432/appdb
      - JWT_SECRET=your_jwt_secret_here
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
    depends_on:
      - postgres
      - jaeger
    networks:
      - app-network

  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: appdb
      POSTGRES_USER: admin
      POSTGRES_PASSWORD: admin123
    ports:
      - "5432:5432"
    volumes:
      - postgres-data:/var/lib/postgresql/data
    networks:
      - app-network

  jaeger:
    image: jaegertracing/all-in-one:1.60
    ports:
      - "16686:16686"  # UI
      - "4317:4317"    # OTLP gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - app-network

volumes:
  postgres-data:

networks:
  app-network:
    driver: bridge
```

---

## 17. 国际标准对齐

| 标准 | 对齐内容 |
|------|----------|
| **RESTful API** | HTTP 方法、状态码、资源命名 |
| **OpenTelemetry** | 分布式追踪、语义约定 |
| **HTTP/1.1 & HTTP/2** | 协议标准、头部规范 |
| **JWT RFC 7519** | 认证 token 标准 |
| **CORS RFC 7240** | 跨域资源共享 |

---

## 18. 总结

本文档全面覆盖了 **Axum 0.7** 在 Rust 1.90 环境下的所有核心特性和高级用法，包括路由、提取器、状态管理、中间件、错误处理、WebSocket、SSE、数据库集成、OTLP 分布式追踪等，并提供了生产级最佳实践和完整代码示例。

**核心要点**：

- ✅ 基于 Tower 的模块化架构
- ✅ 类型安全的提取器系统
- ✅ 灵活的中间件组合
- ✅ 深度 OTLP 追踪集成
- ✅ 生产级性能优化
- ✅ 完整的测试策略

---

**文档完成**。
