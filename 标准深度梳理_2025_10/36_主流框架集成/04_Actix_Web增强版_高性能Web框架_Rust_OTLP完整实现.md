# Actix-Web 增强版：高性能 Web 框架 Rust 1.90 + OTLP 完整实现指南

## 目录

- [Actix-Web 增强版：高性能 Web 框架 Rust 1.90 + OTLP 完整实现指南](#actix-web-增强版高性能-web-框架-rust-190--otlp-完整实现指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Actix-Web 定位](#11-actix-web-定位)
      - [核心优势](#核心优势)
    - [1.2 与 Axum 的对比](#12-与-axum-的对比)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. Actix-Web 核心架构](#2-actix-web-核心架构)
    - [2.1 三层架构](#21-三层架构)
    - [2.2 Actor 模型集成](#22-actor-模型集成)
  - [3. 基础配置与项目结构](#3-基础配置与项目结构)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 项目结构](#32-项目结构)
    - [3.3 配置管理](#33-配置管理)
  - [4. Actor 模型深度应用](#4-actor-模型深度应用)
    - [4.1 数据库 Actor](#41-数据库-actor)
    - [4.2 缓存 Actor](#42-缓存-actor)
  - [5. 高级路由与请求处理](#5-高级路由与请求处理)
    - [5.1 路由配置](#51-路由配置)
    - [5.2 请求提取器 (Extractors)](#52-请求提取器-extractors)
  - [6. 中间件系统深度解析](#6-中间件系统深度解析)
    - [6.1 认证中间件](#61-认证中间件)
    - [6.2 限流中间件](#62-限流中间件)
    - [6.3 OTLP 追踪中间件](#63-otlp-追踪中间件)
  - [7. 状态管理与依赖注入](#7-状态管理与依赖注入)
    - [7.1 应用状态](#71-应用状态)
  - [8. 数据库集成与连接池优化](#8-数据库集成与连接池优化)
    - [8.1 SQLx 配置优化](#81-sqlx-配置优化)
    - [8.2 数据库迁移](#82-数据库迁移)
  - [9. WebSocket 实时通信](#9-websocket-实时通信)
    - [9.1 WebSocket 处理器](#91-websocket-处理器)
  - [10. 异步流处理与背压控制](#10-异步流处理与背压控制)
    - [10.1 流式响应](#101-流式响应)
    - [10.2 背压控制](#102-背压控制)
  - [11. 性能优化与压测](#11-性能优化与压测)
    - [11.1 性能优化配置](#111-性能优化配置)
    - [11.2 压测脚本](#112-压测脚本)
  - [12. OTLP 分布式追踪深度集成](#12-otlp-分布式追踪深度集成)
    - [12.1 OTLP 初始化](#121-otlp-初始化)
    - [12.2 手动追踪](#122-手动追踪)
  - [13. 错误处理与恢复策略](#13-错误处理与恢复策略)
    - [13.1 自定义错误类型](#131-自定义错误类型)
  - [14. 安全性增强](#14-安全性增强)
    - [14.1 CORS 配置](#141-cors-配置)
    - [14.2 CSRF 保护](#142-csrf-保护)
  - [15. 生产环境部署](#15-生产环境部署)
    - [15.1 Docker 镜像](#151-docker-镜像)
    - [15.2 Docker Compose](#152-docker-compose)
  - [16. 国际标准对标](#16-国际标准对标)
    - [16.1 对标清单](#161-对标清单)
    - [16.2 与国际框架对比](#162-与国际框架对比)
  - [17. 总结与最佳实践](#17-总结与最佳实践)
    - [17.1 核心优势](#171-核心优势)
    - [17.2 最佳实践](#172-最佳实践)
      - [✅ 推荐做法](#-推荐做法)
      - [❌ 避免做法](#-避免做法)
    - [17.3 性能基准](#173-性能基准)
    - [17.4 学习资源](#174-学习资源)
  - [附录：完整示例代码](#附录完整示例代码)
    - [A.1 完整的 main.rs](#a1-完整的-mainrs)

---

## 1. 概述

### 1.1 Actix-Web 定位

**Actix-Web** 是 Rust 生态中最成熟、性能最高的 Web 框架之一，基于 **Actor 模型** 和 **Tokio 异步运行时**构建。它在 TechEmpower 基准测试中多次位居榜首。

#### 核心优势

- **极致性能**：单机百万级 QPS
- **Actor 模型**：天然支持并发隔离
- **类型安全**：编译期保证类型正确
- **灵活中间件**：类似 Express.js 的中间件链
- **生产就绪**：广泛应用于金融、电商等高并发场景

### 1.2 与 Axum 的对比

| 特性 | Actix-Web | Axum |
|------|-----------|------|
| **底层运行时** | Actix System + Tokio | Tokio + Tower |
| **核心模型** | Actor + Async | Service + Layer |
| **性能** | 极致（单机100万+QPS） | 优秀（单机60万+QPS） |
| **学习曲线** | 中等（需理解Actor） | 较低（熟悉Tower即可） |
| **中间件模式** | 自定义Transform | Tower Layer |
| **生态成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **适用场景** | 极高并发、Actor模型 | 微服务、Tower生态 |

### 1.3 国际标准对标

| 标准/最佳实践 | Actix-Web 实现 |
|--------------|---------------|
| **HTTP/1.1, HTTP/2** | 完整支持（通过 actix-http） |
| **OpenAPI/Swagger** | paperclip, utoipa 集成 |
| **OAuth2/JWT** | actix-web-httpauth |
| **OWASP Top 10** | 内置防护（CSRF、XSS、SQL注入） |
| **12-Factor App** | 环境变量、无状态、日志流 |
| **OpenTelemetry** | tracing-opentelemetry 集成 |
| **Prometheus Metrics** | actix-web-prom |

---

## 2. Actix-Web 核心架构

### 2.1 三层架构

```text
┌──────────────────────────────────────────┐
│         Application Layer                │
│  ┌────────────┐  ┌─────────────────┐     │
│  │  HttpServer │─>│  App (Router)   │    │
│  └────────────┘  └─────────────────┘     │
├──────────────────────────────────────────┤
│         Middleware Layer                 │
│  ┌─────────┐ ┌─────────┐ ┌──────────┐    │
│  │ Logger  │→│  Auth   │→│  OTLP    │    │
│  └─────────┘ └─────────┘ └──────────┘    │
├──────────────────────────────────────────┤
│         Handler Layer                    │
│  ┌──────────────┐  ┌──────────────┐      │
│  │  Extractors  │  │  Responders  │      │
│  └──────────────┘  └──────────────┘      │
└──────────────────────────────────────────┘
```

### 2.2 Actor 模型集成

```rust
use actix::prelude::*;
use actix_web::{web, App, HttpServer};

// Actor 定义
struct DatabaseActor {
    pool: sqlx::PgPool,
}

impl Actor for DatabaseActor {
    type Context = Context<Self>;
}

// 消息定义
#[derive(Message)]
#[rtype(result = "Result<User, sqlx::Error>")]
struct GetUser {
    id: i64,
}

// 消息处理
impl Handler<GetUser> for DatabaseActor {
    type Result = ResponseActFuture<Self, Result<User, sqlx::Error>>;

    fn handle(&mut self, msg: GetUser, _: &mut Self::Context) -> Self::Result {
        let pool = self.pool.clone();
        
        Box::pin(
            async move {
                sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", msg.id)
                    .fetch_one(&pool)
                    .await
            }
            .into_actor(self)
        )
    }
}
```

---

## 3. 基础配置与项目结构

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "actix-otlp-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Actix 核心
actix-web = "4.9"
actix-rt = "2.10"
actix = "0.13"
actix-files = "0.6"
actix-cors = "0.7"
actix-session = { version = "0.10", features = ["cookie-session"] }
actix-web-httpauth = "0.8"
actix-web-lab = "0.22"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "uuid", "chrono", "json"] }

# 认证
jsonwebtoken = "9.3"
bcrypt = "0.15"

# 追踪与指标
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"
opentelemetry = { version = "0.25", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["trace", "metrics", "grpc-tonic"] }
opentelemetry-semantic-conventions = "0.25"

# 工具库
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
thiserror = "1.0"
anyhow = "1.0"
dotenv = "0.15"
config = "0.14"
validator = { version = "0.18", features = ["derive"] }

# 缓存
redis = { version = "0.27", features = ["tokio-comp", "connection-manager"] }
moka = { version = "0.12", features = ["future"] }

# 限流
governor = "0.7"

# 测试
[dev-dependencies]
actix-web-test = "0.9"
mockall = "0.13"
```

### 3.2 项目结构

```text
actix-otlp-demo/
├── src/
│   ├── main.rs                    # 应用入口
│   ├── config.rs                  # 配置管理
│   ├── telemetry.rs              # OTLP 初始化
│   ├── actors/                    # Actor 定义
│   │   ├── mod.rs
│   │   ├── db_actor.rs           # 数据库 Actor
│   │   └── cache_actor.rs        # 缓存 Actor
│   ├── handlers/                  # HTTP 处理器
│   │   ├── mod.rs
│   │   ├── user.rs
│   │   └── auth.rs
│   ├── middleware/                # 自定义中间件
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   ├── rate_limit.rs
│   │   └── otlp.rs
│   ├── models/                    # 数据模型
│   │   ├── mod.rs
│   │   └── user.rs
│   ├── services/                  # 业务逻辑
│   │   ├── mod.rs
│   │   └── user_service.rs
│   └── errors.rs                  # 错误定义
├── Cargo.toml
├── .env
└── docker-compose.yml
```

### 3.3 配置管理

```rust
// src/config.rs
use config::{Config, ConfigError, File};
use serde::Deserialize;

#[derive(Debug, Deserialize, Clone)]
pub struct Settings {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub redis: RedisConfig,
    pub jwt: JwtConfig,
    pub otlp: OtlpConfig,
}

#[derive(Debug, Deserialize, Clone)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub keep_alive: usize,
    pub client_timeout: u64,
    pub client_shutdown: u64,
}

#[derive(Debug, Deserialize, Clone)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
    pub connect_timeout: u64,
    pub idle_timeout: u64,
}

#[derive(Debug, Deserialize, Clone)]
pub struct RedisConfig {
    pub url: String,
    pub pool_size: u32,
}

#[derive(Debug, Deserialize, Clone)]
pub struct JwtConfig {
    pub secret: String,
    pub expiration: i64,
}

#[derive(Debug, Deserialize, Clone)]
pub struct OtlpConfig {
    pub endpoint: String,
    pub service_name: String,
}

impl Settings {
    pub fn new() -> Result<Self, ConfigError> {
        let env = std::env::var("RUN_ENV").unwrap_or_else(|_| "development".into());
        
        let s = Config::builder()
            .add_source(File::with_name("config/default"))
            .add_source(File::with_name(&format!("config/{}", env)).required(false))
            .add_source(config::Environment::with_prefix("APP"))
            .build()?;
        
        s.try_deserialize()
    }
}
```

---

## 4. Actor 模型深度应用

### 4.1 数据库 Actor

```rust
// src/actors/db_actor.rs
use actix::prelude::*;
use sqlx::PgPool;
use tracing::{instrument, info, error};
use crate::models::user::User;

pub struct DbActor {
    pool: PgPool,
}

impl DbActor {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

impl Actor for DbActor {
    type Context = Context<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("DbActor started");
    }

    fn stopped(&mut self, _ctx: &mut Self::Context) {
        info!("DbActor stopped");
    }
}

// ========== 消息定义 ==========

#[derive(Message)]
#[rtype(result = "Result<User, sqlx::Error>")]
pub struct GetUserById {
    pub id: i64,
}

#[derive(Message)]
#[rtype(result = "Result<User, sqlx::Error>")]
pub struct CreateUser {
    pub email: String,
    pub password_hash: String,
    pub name: String,
}

#[derive(Message)]
#[rtype(result = "Result<Vec<User>, sqlx::Error>")]
pub struct ListUsers {
    pub limit: i64,
    pub offset: i64,
}

// ========== 消息处理 ==========

impl Handler<GetUserById> for DbActor {
    type Result = ResponseActFuture<Self, Result<User, sqlx::Error>>;

    #[instrument(skip(self, _ctx), fields(user_id = msg.id))]
    fn handle(&mut self, msg: GetUserById, _ctx: &mut Self::Context) -> Self::Result {
        let pool = self.pool.clone();
        
        Box::pin(
            async move {
                info!("Fetching user from database");
                
                let user = sqlx::query_as!(
                    User,
                    r#"
                    SELECT id, email, password_hash, name, created_at, updated_at
                    FROM users
                    WHERE id = $1
                    "#,
                    msg.id
                )
                .fetch_one(&pool)
                .await?;
                
                info!("User fetched successfully");
                Ok(user)
            }
            .into_actor(self)
        )
    }
}

impl Handler<CreateUser> for DbActor {
    type Result = ResponseActFuture<Self, Result<User, sqlx::Error>>;

    #[instrument(skip(self, _ctx, msg), fields(email = %msg.email))]
    fn handle(&mut self, msg: CreateUser, _ctx: &mut Self::Context) -> Self::Result {
        let pool = self.pool.clone();
        
        Box::pin(
            async move {
                info!("Creating new user");
                
                let user = sqlx::query_as!(
                    User,
                    r#"
                    INSERT INTO users (email, password_hash, name)
                    VALUES ($1, $2, $3)
                    RETURNING id, email, password_hash, name, created_at, updated_at
                    "#,
                    msg.email,
                    msg.password_hash,
                    msg.name
                )
                .fetch_one(&pool)
                .await?;
                
                info!("User created successfully");
                Ok(user)
            }
            .into_actor(self)
        )
    }
}

impl Handler<ListUsers> for DbActor {
    type Result = ResponseActFuture<Self, Result<Vec<User>, sqlx::Error>>;

    #[instrument(skip(self, _ctx), fields(limit = msg.limit, offset = msg.offset))]
    fn handle(&mut self, msg: ListUsers, _ctx: &mut Self::Context) -> Self::Result {
        let pool = self.pool.clone();
        
        Box::pin(
            async move {
                info!("Listing users");
                
                let users = sqlx::query_as!(
                    User,
                    r#"
                    SELECT id, email, password_hash, name, created_at, updated_at
                    FROM users
                    ORDER BY created_at DESC
                    LIMIT $1 OFFSET $2
                    "#,
                    msg.limit,
                    msg.offset
                )
                .fetch_all(&pool)
                .await?;
                
                info!("Users listed successfully, count={}", users.len());
                Ok(users)
            }
            .into_actor(self)
        )
    }
}
```

### 4.2 缓存 Actor

```rust
// src/actors/cache_actor.rs
use actix::prelude::*;
use redis::{aio::ConnectionManager, AsyncCommands};
use tracing::{instrument, info, error};
use serde::{Serialize, Deserialize};

pub struct CacheActor {
    conn: ConnectionManager,
}

impl CacheActor {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }
}

impl Actor for CacheActor {
    type Context = Context<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("CacheActor started");
    }
}

// ========== 消息定义 ==========

#[derive(Message)]
#[rtype(result = "Result<Option<String>, redis::RedisError>")]
pub struct Get {
    pub key: String,
}

#[derive(Message)]
#[rtype(result = "Result<(), redis::RedisError>")]
pub struct Set {
    pub key: String,
    pub value: String,
    pub expiration: Option<usize>, // 秒
}

#[derive(Message)]
#[rtype(result = "Result<(), redis::RedisError>")]
pub struct Delete {
    pub key: String,
}

// ========== 消息处理 ==========

impl Handler<Get> for CacheActor {
    type Result = ResponseActFuture<Self, Result<Option<String>, redis::RedisError>>;

    #[instrument(skip(self, _ctx), fields(key = %msg.key))]
    fn handle(&mut self, msg: Get, _ctx: &mut Self::Context) -> Self::Result {
        let mut conn = self.conn.clone();
        
        Box::pin(
            async move {
                info!("Getting key from cache");
                
                let value: Option<String> = conn.get(&msg.key).await?;
                
                if value.is_some() {
                    info!("Cache hit");
                } else {
                    info!("Cache miss");
                }
                
                Ok(value)
            }
            .into_actor(self)
        )
    }
}

impl Handler<Set> for CacheActor {
    type Result = ResponseActFuture<Self, Result<(), redis::RedisError>>;

    #[instrument(skip(self, _ctx), fields(key = %msg.key))]
    fn handle(&mut self, msg: Set, _ctx: &mut Self::Context) -> Self::Result {
        let mut conn = self.conn.clone();
        
        Box::pin(
            async move {
                info!("Setting key in cache");
                
                if let Some(exp) = msg.expiration {
                    conn.set_ex(&msg.key, &msg.value, exp).await?;
                } else {
                    conn.set(&msg.key, &msg.value).await?;
                }
                
                info!("Key set successfully");
                Ok(())
            }
            .into_actor(self)
        )
    }
}

impl Handler<Delete> for CacheActor {
    type Result = ResponseActFuture<Self, Result<(), redis::RedisError>>;

    #[instrument(skip(self, _ctx), fields(key = %msg.key))]
    fn handle(&mut self, msg: Delete, _ctx: &mut Self::Context) -> Self::Result {
        let mut conn = self.conn.clone();
        
        Box::pin(
            async move {
                info!("Deleting key from cache");
                
                conn.del(&msg.key).await?;
                
                info!("Key deleted successfully");
                Ok(())
            }
            .into_actor(self)
        )
    }
}
```

---

## 5. 高级路由与请求处理

### 5.1 路由配置

```rust
// src/main.rs (部分)
use actix_web::{web, App, HttpServer, middleware};
use crate::handlers::{user, auth};

pub fn configure_routes(cfg: &mut web::ServiceConfig) {
    cfg
        // API v1
        .service(
            web::scope("/api/v1")
                // 公开路由
                .service(
                    web::scope("/auth")
                        .route("/register", web::post().to(auth::register))
                        .route("/login", web::post().to(auth::login))
                        .route("/refresh", web::post().to(auth::refresh_token))
                )
                // 受保护路由
                .service(
                    web::scope("/users")
                        .wrap(crate::middleware::auth::AuthMiddleware)
                        .route("", web::get().to(user::list_users))
                        .route("/{id}", web::get().to(user::get_user))
                        .route("", web::post().to(user::create_user))
                        .route("/{id}", web::put().to(user::update_user))
                        .route("/{id}", web::delete().to(user::delete_user))
                )
                // WebSocket
                .route("/ws", web::get().to(user::ws_index))
        )
        // 健康检查
        .service(
            web::scope("/health")
                .route("", web::get().to(health_check))
                .route("/ready", web::get().to(readiness_check))
        );
}

async fn health_check() -> actix_web::Result<impl actix_web::Responder> {
    Ok(web::Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339()
    })))
}

async fn readiness_check(
    db: web::Data<DbActor>,
) -> actix_web::Result<impl actix_web::Responder> {
    // 检查数据库连接
    // ...
    Ok(web::Json(serde_json::json!({
        "status": "ready"
    })))
}
```

### 5.2 请求提取器 (Extractors)

```rust
// src/handlers/user.rs
use actix_web::{web, HttpRequest, HttpResponse, Error};
use actix::Addr;
use validator::Validate;
use serde::{Deserialize, Serialize};
use tracing::instrument;
use crate::actors::db_actor::{DbActor, GetUserById, CreateUser, ListUsers};

// ========== 请求 DTO ==========

#[derive(Debug, Deserialize, Validate)]
pub struct CreateUserRequest {
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8, max = 100))]
    pub password: String,
    
    #[validate(length(min = 2, max = 100))]
    pub name: String,
}

#[derive(Debug, Deserialize, Validate)]
pub struct ListUsersQuery {
    #[validate(range(min = 1, max = 100))]
    pub limit: Option<i64>,
    
    #[validate(range(min = 0))]
    pub offset: Option<i64>,
}

// ========== 响应 DTO ==========

#[derive(Debug, Serialize)]
pub struct UserResponse {
    pub id: i64,
    pub email: String,
    pub name: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl From<crate::models::user::User> for UserResponse {
    fn from(user: crate::models::user::User) -> Self {
        Self {
            id: user.id,
            email: user.email,
            name: user.name,
            created_at: user.created_at,
        }
    }
}

// ========== 处理器 ==========

#[instrument(skip(db_actor))]
pub async fn get_user(
    path: web::Path<i64>,
    db_actor: web::Data<Addr<DbActor>>,
) -> Result<HttpResponse, Error> {
    let user_id = path.into_inner();
    
    let user = db_actor
        .send(GetUserById { id: user_id })
        .await
        .map_err(|e| {
            tracing::error!("Actor mailbox error: {}", e);
            actix_web::error::ErrorInternalServerError("Actor error")
        })?
        .map_err(|e| {
            tracing::error!("Database error: {}", e);
            actix_web::error::ErrorNotFound("User not found")
        })?;
    
    Ok(HttpResponse::Ok().json(UserResponse::from(user)))
}

#[instrument(skip(db_actor))]
pub async fn create_user(
    req: web::Json<CreateUserRequest>,
    db_actor: web::Data<Addr<DbActor>>,
) -> Result<HttpResponse, Error> {
    // 验证请求
    req.validate().map_err(actix_web::error::ErrorBadRequest)?;
    
    // 哈希密码
    let password_hash = bcrypt::hash(&req.password, bcrypt::DEFAULT_COST)
        .map_err(actix_web::error::ErrorInternalServerError)?;
    
    // 创建用户
    let user = db_actor
        .send(CreateUser {
            email: req.email.clone(),
            password_hash,
            name: req.name.clone(),
        })
        .await
        .map_err(|e| {
            tracing::error!("Actor mailbox error: {}", e);
            actix_web::error::ErrorInternalServerError("Actor error")
        })?
        .map_err(|e| {
            tracing::error!("Database error: {}", e);
            actix_web::error::ErrorInternalServerError("Failed to create user")
        })?;
    
    Ok(HttpResponse::Created().json(UserResponse::from(user)))
}

#[instrument(skip(db_actor))]
pub async fn list_users(
    query: web::Query<ListUsersQuery>,
    db_actor: web::Data<Addr<DbActor>>,
) -> Result<HttpResponse, Error> {
    // 验证查询参数
    query.validate().map_err(actix_web::error::ErrorBadRequest)?;
    
    let limit = query.limit.unwrap_or(10);
    let offset = query.offset.unwrap_or(0);
    
    let users = db_actor
        .send(ListUsers { limit, offset })
        .await
        .map_err(|e| {
            tracing::error!("Actor mailbox error: {}", e);
            actix_web::error::ErrorInternalServerError("Actor error")
        })?
        .map_err(|e| {
            tracing::error!("Database error: {}", e);
            actix_web::error::ErrorInternalServerError("Failed to list users")
        })?;
    
    let response: Vec<UserResponse> = users.into_iter().map(UserResponse::from).collect();
    
    Ok(HttpResponse::Ok().json(response))
}
```

---

## 6. 中间件系统深度解析

### 6.1 认证中间件

```rust
// src/middleware/auth.rs
use actix_web::{
    dev::{forward_ready, Service, ServiceRequest, ServiceResponse, Transform},
    Error, HttpMessage, HttpResponse,
};
use futures_util::future::LocalBoxFuture;
use std::future::{ready, Ready};
use jsonwebtoken::{decode, DecodingKey, Validation, Algorithm};
use serde::{Deserialize, Serialize};
use tracing::{instrument, warn};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,      // Subject (user ID)
    pub exp: usize,       // Expiration time
    pub iat: usize,       // Issued at
    pub role: String,     // User role
}

pub struct AuthMiddleware;

impl<S, B> Transform<S, ServiceRequest> for AuthMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = AuthMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(AuthMiddlewareService { service }))
    }
}

pub struct AuthMiddlewareService<S> {
    service: S,
}

impl<S, B> Service<ServiceRequest> for AuthMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;

    forward_ready!(service);

    fn call(&self, req: ServiceRequest) -> Self::Future {
        let auth_header = req
            .headers()
            .get("Authorization")
            .and_then(|h| h.to_str().ok());
        
        let token = match auth_header {
            Some(header) if header.starts_with("Bearer ") => {
                &header[7..]
            }
            _ => {
                warn!("Missing or invalid Authorization header");
                return Box::pin(async move {
                    Err(actix_web::error::ErrorUnauthorized("Missing or invalid token"))
                });
            }
        };
        
        // 验证 JWT
        let jwt_secret = std::env::var("JWT_SECRET").unwrap_or_else(|_| "secret".to_string());
        
        let validation = Validation::new(Algorithm::HS256);
        
        match decode::<Claims>(
            token,
            &DecodingKey::from_secret(jwt_secret.as_bytes()),
            &validation,
        ) {
            Ok(token_data) => {
                // 将 claims 存入请求扩展
                req.extensions_mut().insert(token_data.claims);
                
                let fut = self.service.call(req);
                Box::pin(async move {
                    let res = fut.await?;
                    Ok(res)
                })
            }
            Err(e) => {
                warn!("JWT validation failed: {}", e);
                Box::pin(async move {
                    Err(actix_web::error::ErrorUnauthorized("Invalid token"))
                })
            }
        }
    }
}
```

### 6.2 限流中间件

```rust
// src/middleware/rate_limit.rs
use actix_web::{
    dev::{forward_ready, Service, ServiceRequest, ServiceResponse, Transform},
    Error, HttpResponse,
};
use futures_util::future::LocalBoxFuture;
use std::future::{ready, Ready};
use std::sync::Arc;
use governor::{Quota, RateLimiter, clock::DefaultClock, state::keyed::DashMapStateStore};
use nonzero_ext::*;
use std::net::IpAddr;
use tracing::warn;

pub struct RateLimitMiddleware {
    limiter: Arc<RateLimiter<IpAddr, DashMapStateStore<IpAddr>, DefaultClock>>,
}

impl RateLimitMiddleware {
    pub fn new(requests_per_second: u32) -> Self {
        let quota = Quota::per_second(nonzero!(requests_per_second));
        let limiter = Arc::new(RateLimiter::keyed(quota));
        
        Self { limiter }
    }
}

impl<S, B> Transform<S, ServiceRequest> for RateLimitMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = RateLimitMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(RateLimitMiddlewareService {
            service,
            limiter: self.limiter.clone(),
        }))
    }
}

pub struct RateLimitMiddlewareService<S> {
    service: S,
    limiter: Arc<RateLimiter<IpAddr, DashMapStateStore<IpAddr>, DefaultClock>>,
}

impl<S, B> Service<ServiceRequest> for RateLimitMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;

    forward_ready!(service);

    fn call(&self, req: ServiceRequest) -> Self::Future {
        let conn_info = req.connection_info().clone();
        let peer_addr = conn_info
            .realip_remote_addr()
            .and_then(|addr| addr.parse::<IpAddr>().ok());
        
        if let Some(ip) = peer_addr {
            if self.limiter.check_key(&ip).is_err() {
                warn!("Rate limit exceeded for IP: {}", ip);
                return Box::pin(async move {
                    Err(actix_web::error::ErrorTooManyRequests("Rate limit exceeded"))
                });
            }
        }
        
        let fut = self.service.call(req);
        Box::pin(async move {
            let res = fut.await?;
            Ok(res)
        })
    }
}
```

### 6.3 OTLP 追踪中间件

```rust
// src/middleware/otlp.rs
use actix_web::{
    dev::{forward_ready, Service, ServiceRequest, ServiceResponse, Transform},
    Error,
};
use futures_util::future::LocalBoxFuture;
use std::future::{ready, Ready};
use tracing::{Span, info_span};
use tracing_opentelemetry::OpenTelemetrySpanExt;
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry::global;

pub struct OtlpMiddleware;

impl<S, B> Transform<S, ServiceRequest> for OtlpMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = OtlpMiddlewareService<S>;
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

    forward_ready!(service);

    fn call(&self, req: ServiceRequest) -> Self::Future {
        // 提取 trace context (如果有)
        let parent_cx = extract_trace_context(&req);
        
        // 创建 span
        let span = info_span!(
            "http_request",
            http.method = %req.method(),
            http.target = %req.path(),
            http.scheme = %req.connection_info().scheme(),
            http.host = %req.connection_info().host(),
            http.user_agent = ?req.headers().get("user-agent"),
            http.status_code = tracing::field::Empty,
            otel.kind = "server",
        );
        
        // 设置父 context
        span.set_parent(parent_cx);
        
        let fut = self.service.call(req);
        
        Box::pin(async move {
            let res = fut.await?;
            
            // 记录响应状态码
            span.record("http.status_code", res.status().as_u16());
            
            Ok(res)
        }.instrument(span))
    }
}

fn extract_trace_context(req: &ServiceRequest) -> opentelemetry::Context {
    use opentelemetry::propagation::TextMapPropagator;
    use opentelemetry_sdk::propagation::TraceContextPropagator;
    use std::collections::HashMap;
    
    let propagator = TraceContextPropagator::new();
    
    let headers: HashMap<String, String> = req
        .headers()
        .iter()
        .filter_map(|(name, value)| {
            value.to_str().ok().map(|v| (name.as_str().to_owned(), v.to_owned()))
        })
        .collect();
    
    propagator.extract(&headers)
}
```

---

## 7. 状态管理与依赖注入

### 7.1 应用状态

```rust
// src/main.rs (部分)
use actix::Addr;
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    pub db_actor: Addr<DbActor>,
    pub cache_actor: Addr<CacheActor>,
    pub config: Arc<Settings>,
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化配置
    let settings = Settings::new().expect("Failed to load configuration");
    
    // 初始化 OTLP
    crate::telemetry::init_telemetry(&settings.otlp).expect("Failed to initialize telemetry");
    
    // 初始化数据库连接池
    let pool = sqlx::PgPool::connect(&settings.database.url)
        .await
        .expect("Failed to connect to database");
    
    // 初始化 Redis 连接
    let redis_client = redis::Client::open(settings.redis.url.as_str())
        .expect("Failed to create Redis client");
    let redis_conn = redis::aio::ConnectionManager::new(redis_client)
        .await
        .expect("Failed to connect to Redis");
    
    // 启动 Actor
    let db_actor = DbActor::new(pool.clone()).start();
    let cache_actor = CacheActor::new(redis_conn).start();
    
    // 创建应用状态
    let state = AppState {
        db_actor: db_actor.clone(),
        cache_actor: cache_actor.clone(),
        config: Arc::new(settings.clone()),
    };
    
    // 启动 HTTP 服务器
    HttpServer::new(move || {
        App::new()
            .app_data(web::Data::new(state.clone()))
            .app_data(web::Data::new(db_actor.clone()))
            .app_data(web::Data::new(cache_actor.clone()))
            .wrap(middleware::Logger::default())
            .wrap(OtlpMiddleware)
            .configure(configure_routes)
    })
    .bind((settings.server.host.as_str(), settings.server.port))?
    .workers(settings.server.workers)
    .keep_alive(std::time::Duration::from_secs(settings.server.keep_alive as u64))
    .run()
    .await
}
```

---

## 8. 数据库集成与连接池优化

### 8.1 SQLx 配置优化

```rust
// src/main.rs (数据库初始化部分)
use sqlx::postgres::{PgPoolOptions, PgConnectOptions};
use std::time::Duration;

async fn create_db_pool(config: &DatabaseConfig) -> Result<sqlx::PgPool, sqlx::Error> {
    let connect_options = config.url
        .parse::<PgConnectOptions>()?
        .application_name("actix-otlp-demo");
    
    let pool = PgPoolOptions::new()
        .max_connections(config.max_connections)
        .min_connections(config.min_connections)
        .acquire_timeout(Duration::from_secs(config.connect_timeout))
        .idle_timeout(Duration::from_secs(config.idle_timeout))
        .test_before_acquire(true)  // 健康检查
        .connect_with(connect_options)
        .await?;
    
    Ok(pool)
}
```

### 8.2 数据库迁移

```sql
-- migrations/001_create_users_table.sql
CREATE TABLE IF NOT EXISTS users (
    id BIGSERIAL PRIMARY KEY,
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    name VARCHAR(255) NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_created_at ON users(created_at);

-- 触发器：自动更新 updated_at
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER update_users_updated_at
BEFORE UPDATE ON users
FOR EACH ROW
EXECUTE FUNCTION update_updated_at_column();
```

---

## 9. WebSocket 实时通信

### 9.1 WebSocket 处理器

```rust
// src/handlers/websocket.rs
use actix::{Actor, StreamHandler, AsyncContext, Handler, Message};
use actix_web::{web, Error, HttpRequest, HttpResponse};
use actix_web_actors::ws;
use tracing::{info, warn, instrument};
use serde::{Deserialize, Serialize};

// ========== WebSocket Actor ==========

pub struct WsSession {
    pub id: uuid::Uuid,
    pub user_id: Option<i64>,
}

impl Actor for WsSession {
    type Context = ws::WebsocketContext<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        info!("WebSocket session started: {}", self.id);
    }

    fn stopped(&mut self, ctx: &mut Self::Context) {
        info!("WebSocket session stopped: {}", self.id);
    }
}

// ========== 消息类型 ==========

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
enum WsMessage {
    #[serde(rename = "ping")]
    Ping,
    
    #[serde(rename = "pong")]
    Pong,
    
    #[serde(rename = "chat")]
    Chat {
        user_id: i64,
        message: String,
        timestamp: i64,
    },
    
    #[serde(rename = "notification")]
    Notification {
        title: String,
        body: String,
    },
}

// ========== 处理 WebSocket 消息 ==========

impl StreamHandler<Result<ws::Message, ws::ProtocolError>> for WsSession {
    #[instrument(skip(self, ctx))]
    fn handle(&mut self, msg: Result<ws::Message, ws::ProtocolError>, ctx: &mut Self::Context) {
        match msg {
            Ok(ws::Message::Ping(msg)) => {
                ctx.pong(&msg);
            }
            Ok(ws::Message::Pong(_)) => {}
            Ok(ws::Message::Text(text)) => {
                info!("Received text message: {}", text);
                
                // 解析 JSON
                match serde_json::from_str::<WsMessage>(&text) {
                    Ok(ws_msg) => match ws_msg {
                        WsMessage::Ping => {
                            let pong = WsMessage::Pong;
                            if let Ok(json) = serde_json::to_string(&pong) {
                                ctx.text(json);
                            }
                        }
                        WsMessage::Chat { user_id, message, timestamp } => {
                            // 处理聊天消息
                            info!("Chat message from user {}: {}", user_id, message);
                            
                            // 广播给其他用户 (需要实现消息总线)
                            // ...
                        }
                        _ => {}
                    },
                    Err(e) => {
                        warn!("Failed to parse WebSocket message: {}", e);
                    }
                }
            }
            Ok(ws::Message::Binary(bin)) => {
                info!("Received binary message: {} bytes", bin.len());
            }
            Ok(ws::Message::Close(reason)) => {
                info!("WebSocket close: {:?}", reason);
                ctx.stop();
            }
            _ => ctx.stop(),
        }
    }
}

// ========== HTTP 处理器 ==========

#[instrument(skip(req, stream))]
pub async fn ws_index(
    req: HttpRequest,
    stream: web::Payload,
) -> Result<HttpResponse, Error> {
    let session = WsSession {
        id: uuid::Uuid::new_v4(),
        user_id: None, // 可从 JWT 提取
    };
    
    let resp = ws::start(session, &req, stream)?;
    Ok(resp)
}
```

---

## 10. 异步流处理与背压控制

### 10.1 流式响应

```rust
// src/handlers/stream.rs
use actix_web::{web, HttpResponse, Error};
use futures_util::stream::{self, Stream};
use std::time::Duration;
use tokio::time::sleep;

pub async fn stream_data() -> Result<HttpResponse, Error> {
    let stream = stream::iter(0..100)
        .then(|i| async move {
            sleep(Duration::from_millis(100)).await;
            Ok::<_, actix_web::Error>(web::Bytes::from(format!("Chunk {}\n", i)))
        });
    
    Ok(HttpResponse::Ok()
        .content_type("text/plain")
        .streaming(Box::pin(stream)))
}
```

### 10.2 背压控制

```rust
use tokio::sync::mpsc;
use futures_util::StreamExt;

pub async fn backpressure_example() {
    // 创建有界通道（背压控制）
    let (tx, mut rx) = mpsc::channel::<i32>(10);
    
    // 生产者
    tokio::spawn(async move {
        for i in 0..100 {
            // 如果通道满了，会自动等待
            if tx.send(i).await.is_err() {
                break;
            }
        }
    });
    
    // 消费者
    while let Some(value) = rx.recv().await {
        // 模拟慢速处理
        sleep(Duration::from_millis(50)).await;
        println!("Processed: {}", value);
    }
}
```

---

## 11. 性能优化与压测

### 11.1 性能优化配置

```rust
// config/production.toml
[server]
host = "0.0.0.0"
port = 8080
workers = 8              # 根据 CPU 核心数调整
keep_alive = 75          # HTTP Keep-Alive 超时
client_timeout = 5000    # 客户端超时（毫秒）
client_shutdown = 3000   # 优雅关闭超时

[database]
max_connections = 100
min_connections = 10
connect_timeout = 10
idle_timeout = 600
```

### 11.2 压测脚本

```bash
# 使用 wrk 压测
wrk -t12 -c400 -d30s --latency http://localhost:8080/api/v1/users

# 使用 hey 压测
hey -n 100000 -c 200 -m GET http://localhost:8080/api/v1/users

# 使用 k6 压测
k6 run --vus 100 --duration 30s load_test.js
```

```javascript
// load_test.js (k6)
import http from 'k6/http';
import { check, sleep } from 'k6';

export let options = {
  stages: [
    { duration: '1m', target: 100 },
    { duration: '3m', target: 100 },
    { duration: '1m', target: 200 },
    { duration: '3m', target: 200 },
    { duration: '1m', target: 0 },
  ],
  thresholds: {
    http_req_duration: ['p(95)<500', 'p(99)<1000'],
    http_req_failed: ['rate<0.01'],
  },
};

export default function () {
  let response = http.get('http://localhost:8080/api/v1/users');
  check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });
  sleep(1);
}
```

---

## 12. OTLP 分布式追踪深度集成

### 12.1 OTLP 初始化

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_telemetry(config: &crate::config::OtlpConfig) -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP 追踪导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&config.endpoint)
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", config.service_name.clone()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", std::env::var("ENV").unwrap_or_else(|_| "development".into())),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 创建 OpenTelemetry 层
    let telemetry_layer = OpenTelemetryLayer::new(tracer);
    
    // 创建日志过滤器
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    // 组合订阅者
    tracing_subscriber::registry()
        .with(env_filter)
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer().json())
        .init();
    
    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

### 12.2 手动追踪

```rust
use tracing::{info_span, instrument};
use opentelemetry::trace::{Tracer, TracerProvider};

#[instrument(skip(db_actor))]
async fn complex_operation(db_actor: &Addr<DbActor>) -> Result<(), Error> {
    let span1 = info_span!("database_query");
    let _guard1 = span1.enter();
    
    // 数据库操作
    let user = db_actor.send(GetUserById { id: 1 }).await??;
    
    drop(_guard1);
    
    let span2 = info_span!("cache_update");
    let _guard2 = span2.enter();
    
    // 缓存更新
    // ...
    
    Ok(())
}
```

---

## 13. 错误处理与恢复策略

### 13.1 自定义错误类型

```rust
// src/errors.rs
use actix_web::{error::ResponseError, HttpResponse};
use thiserror::Error;
use serde::Serialize;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
    
    #[error("Redis error: {0}")]
    RedisError(#[from] redis::RedisError),
    
    #[error("Actor error: {0}")]
    ActorError(#[from] actix::MailboxError),
    
    #[error("Validation error: {0}")]
    ValidationError(String),
    
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Unauthorized")]
    Unauthorized,
    
    #[error("Internal server error")]
    InternalError,
}

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    details: Option<String>,
}

impl ResponseError for AppError {
    fn error_response(&self) -> HttpResponse {
        let (status, message) = match self {
            AppError::DatabaseError(e) => {
                tracing::error!("Database error: {}", e);
                (actix_web::http::StatusCode::INTERNAL_SERVER_ERROR, "Database error")
            }
            AppError::RedisError(e) => {
                tracing::error!("Redis error: {}", e);
                (actix_web::http::StatusCode::INTERNAL_SERVER_ERROR, "Cache error")
            }
            AppError::ActorError(e) => {
                tracing::error!("Actor error: {}", e);
                (actix_web::http::StatusCode::INTERNAL_SERVER_ERROR, "Actor communication error")
            }
            AppError::ValidationError(msg) => {
                (actix_web::http::StatusCode::BAD_REQUEST, msg.as_str())
            }
            AppError::NotFound(msg) => {
                (actix_web::http::StatusCode::NOT_FOUND, msg.as_str())
            }
            AppError::Unauthorized => {
                (actix_web::http::StatusCode::UNAUTHORIZED, "Unauthorized")
            }
            AppError::InternalError => {
                (actix_web::http::StatusCode::INTERNAL_SERVER_ERROR, "Internal server error")
            }
        };
        
        HttpResponse::build(status).json(ErrorResponse {
            error: status.canonical_reason().unwrap_or("Unknown").to_string(),
            message: message.to_string(),
            details: None,
        })
    }
}
```

---

## 14. 安全性增强

### 14.1 CORS 配置

```rust
use actix_cors::Cors;

let cors = Cors::default()
    .allowed_origin("https://example.com")
    .allowed_methods(vec!["GET", "POST", "PUT", "DELETE"])
    .allowed_headers(vec![
        actix_web::http::header::AUTHORIZATION,
        actix_web::http::header::CONTENT_TYPE,
    ])
    .max_age(3600);

App::new()
    .wrap(cors)
    // ...
```

### 14.2 CSRF 保护

```rust
use actix_session::{Session, SessionMiddleware, storage::CookieSessionStore};
use actix_web::cookie::Key;

let secret_key = Key::from(&[0; 64]);

App::new()
    .wrap(
        SessionMiddleware::builder(CookieSessionStore::default(), secret_key)
            .cookie_secure(true)  // 仅 HTTPS
            .cookie_http_only(true)
            .cookie_same_site(actix_web::cookie::SameSite::Strict)
            .build()
    )
    // ...
```

---

## 15. 生产环境部署

### 15.1 Docker 镜像

```dockerfile
# Dockerfile
FROM rust:1.90-slim AS builder

WORKDIR /app

# 复制依赖清单
COPY Cargo.toml Cargo.lock ./

# 构建依赖（缓存）
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# ========== 运行时镜像 ==========
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    libpq5 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=builder /app/target/release/actix-otlp-demo .

ENV RUST_LOG=info

EXPOSE 8080

CMD ["./actix-otlp-demo"]
```

### 15.2 Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  actix-app:
    build: .
    ports:
      - "8080:8080"
    environment:
      DATABASE_URL: postgres://postgres:postgres@postgres:5432/actix_db
      REDIS_URL: redis://redis:6379
      OTLP_ENDPOINT: http://jaeger:4317
      JWT_SECRET: your-secret-key
      RUST_LOG: info
    depends_on:
      - postgres
      - redis
      - jaeger

  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: actix_db
      POSTGRES_USER: postgres
      POSTGRES_PASSWORD: postgres
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  jaeger:
    image: jaegertracing/all-in-one:1.57
    ports:
      - "16686:16686"  # UI
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP
    environment:
      COLLECTOR_OTLP_ENABLED: "true"

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      GF_SECURITY_ADMIN_PASSWORD: admin
    volumes:
      - grafana_data:/var/lib/grafana

volumes:
  postgres_data:
  grafana_data:
```

---

## 16. 国际标准对标

### 16.1 对标清单

| 标准分类 | 标准名称 | Actix-Web 实现 |
|----------|----------|----------------|
| **HTTP 规范** | RFC 7230-7235 (HTTP/1.1) | ✅ 完整支持 |
| | RFC 7540 (HTTP/2) | ✅ 通过 actix-http |
| **安全标准** | OWASP Top 10 | ✅ CSRF、XSS、注入防护 |
| | OAuth 2.0 (RFC 6749) | ✅ actix-web-httpauth |
| | JWT (RFC 7519) | ✅ jsonwebtoken |
| **可观测性** | OpenTelemetry 1.x | ✅ 完整集成 |
| | Prometheus Metrics | ✅ actix-web-prom |
| **API 标准** | OpenAPI 3.0 | ✅ utoipa, paperclip |
| | JSON:API | ✅ 手动实现 |
| **架构模式** | 12-Factor App | ✅ 环境变量、无状态、日志 |
| | RESTful API | ✅ 资源路由、HTTP 方法 |
| **并发模型** | Actor Model (Hewitt, 1973) | ✅ Actix Actor System |

### 16.2 与国际框架对比

| 特性 | Actix-Web | Express.js | Spring Boot | ASP.NET Core |
|------|-----------|-----------|-------------|--------------|
| **语言** | Rust | JavaScript | Java | C# |
| **性能 (QPS)** | 1,000,000+ | 30,000 | 80,000 | 150,000 |
| **内存安全** | ✅ 编译期 | ❌ 运行时 | ❌ 运行时 | ❌ 运行时 |
| **并发模型** | Actor + Async | Event Loop | Thread Pool | Thread Pool |
| **生态成熟度** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

---

## 17. 总结与最佳实践

### 17.1 核心优势

1. **极致性能**：单机百万级 QPS，适合高并发场景
2. **Actor 模型**：天然并发隔离，避免锁竞争
3. **类型安全**：编译期保证，减少运行时错误
4. **灵活架构**：中间件、状态管理、依赖注入一应俱全

### 17.2 最佳实践

#### ✅ 推荐做法

- 使用 Actor 隔离状态，避免共享可变状态
- 使用 `#[instrument]` 宏自动追踪函数
- 使用 `validator` crate 验证请求
- 使用连接池优化数据库性能
- 使用 Redis 缓存热点数据
- 使用限流中间件防止滥用
- 使用 OTLP 分布式追踪排查问题

#### ❌ 避免做法

- 不要在 Actor 中执行阻塞操作（使用 `tokio::task::spawn_blocking`）
- 不要在生产环境使用 `.unwrap()` （使用 `?` 或 `match`）
- 不要暴露内部错误信息给客户端
- 不要在中间件中执行重 I/O 操作
- 不要忽略背压控制

### 17.3 性能基准

| 指标 | 值 |
|------|-----|
| **单机 QPS** | 1,000,000+ |
| **P50 延迟** | <1ms |
| **P99 延迟** | <10ms |
| **内存占用** | <100MB（空载） |
| **CPU 利用率** | 95%+（满载） |

### 17.4 学习资源

- **官方文档**: <https://actix.rs/>
- **示例代码**: <https://github.com/actix/examples>
- **性能测试**: <https://www.techempower.com/benchmarks/>
- **Actix Book**: <https://actix.rs/book/actix/>

---

## 附录：完整示例代码

### A.1 完整的 main.rs

```rust
// src/main.rs
use actix_web::{web, App, HttpServer, middleware};
use actix::Actor;
use tracing::info;

mod config;
mod telemetry;
mod actors;
mod handlers;
mod middleware as custom_middleware;
mod models;
mod services;
mod errors;

use config::Settings;
use actors::{db_actor::DbActor, cache_actor::CacheActor};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 加载配置
    let settings = Settings::new().expect("Failed to load configuration");
    
    // 初始化 OTLP
    telemetry::init_telemetry(&settings.otlp).expect("Failed to initialize telemetry");
    
    info!("Starting Actix-Web server...");
    
    // 初始化数据库连接池
    let pool = sqlx::PgPool::connect(&settings.database.url)
        .await
        .expect("Failed to connect to database");
    
    // 初始化 Redis
    let redis_client = redis::Client::open(settings.redis.url.as_str())
        .expect("Failed to create Redis client");
    let redis_conn = redis::aio::ConnectionManager::new(redis_client)
        .await
        .expect("Failed to connect to Redis");
    
    // 启动 Actors
    let db_actor = DbActor::new(pool.clone()).start();
    let cache_actor = CacheActor::new(redis_conn).start();
    
    let bind_address = (settings.server.host.clone(), settings.server.port);
    
    info!("Server listening on {}:{}", settings.server.host, settings.server.port);
    
    // 启动 HTTP 服务器
    HttpServer::new(move || {
        App::new()
            // 注入依赖
            .app_data(web::Data::new(db_actor.clone()))
            .app_data(web::Data::new(cache_actor.clone()))
            // 中间件
            .wrap(middleware::Logger::default())
            .wrap(middleware::Compress::default())
            .wrap(custom_middleware::otlp::OtlpMiddleware)
            // 路由
            .configure(handlers::configure_routes)
    })
    .bind(bind_address)?
    .workers(settings.server.workers)
    .keep_alive(std::time::Duration::from_secs(settings.server.keep_alive as u64))
    .run()
    .await?;
    
    // 优雅关闭
    telemetry::shutdown_telemetry();
    
    Ok(())
}
```

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**Actix-Web 版本**: 4.9  
**OpenTelemetry 版本**: 0.25  

---

**国际标准对齐**:

- ✅ CNCF OpenTelemetry Specification
- ✅ HTTP/1.1, HTTP/2 Standards (RFC 7230-7235, RFC 7540)
- ✅ OWASP Top 10 Security Best Practices
- ✅ 12-Factor App Methodology
- ✅ Actor Model (Hewitt, Bishop, Steiger, 1973)
- ✅ REST Architectural Style (Fielding, 2000)

**参考文献**:

- Actix Framework Official Documentation: <https://actix.rs/>
- OpenTelemetry Rust SDK: <https://github.com/open-telemetry/opentelemetry-rust>
- TechEmpower Benchmarks: <https://www.techempower.com/benchmarks/>
- Actor Model Paper: Hewitt, C., Bishop, P., & Steiger, R. (1973). "A Universal Modular ACTOR Formalism for Artificial Intelligence"
