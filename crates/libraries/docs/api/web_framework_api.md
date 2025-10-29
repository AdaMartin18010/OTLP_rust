# Web框架完整集成 - API参考文档

**示例文件**: `crates/libraries/examples/web_framework_complete_integration.rs`  
**版本**: 1.0.0  
**Rust版本**: 1.90.0+  
**最后更新**: 2025年10月28日

---

## 📋 目录

- [核心类型](#核心类型)
  - [AppState](#appstate)
  - [AppConfig](#appconfig)
  - [AppError](#apperror)
- [Domain Models](#domain-models)
  - [User](#user)
  - [CreateUserRequest](#createuserrequest)
  - [UpdateUserRequest](#updateuserrequest)
- [Repository Layer](#repository-layer)
  - [UserRepository](#userrepository)
- [Service Layer](#service-layer)
  - [UserService](#userservice)
- [Controller Layer](#controller-layer)
- [Application Setup](#application-setup)

---

## 核心类型

### `AppState`

**定义**:

```rust
#[derive(Clone)]
pub struct AppState {
    pub db: PgPool,
    pub redis: redis::aio::ConnectionManager,
    pub config: Arc<AppConfig>,
}
```

**功能**: 应用程序全局状态，包含数据库连接池、Redis连接和配置信息。

**字段说明**:

- `db`: PostgreSQL连接池
  - 类型: `PgPool`
  - 用途: 数据库操作
  - 线程安全: 是（内部使用Arc）
- `redis`: Redis连接管理器
  - 类型: `redis::aio::ConnectionManager`
  - 用途: 缓存操作
  - 线程安全: 是（Clone trait）
- `config`: 应用配置
  - 类型: `Arc<AppConfig>`
  - 用途: 访问应用配置
  - 线程安全: 是（Arc包装）

**特征实现**: `Clone`

**使用示例**:

```rust
let state = Arc::new(AppState {
    db: pool.clone(),
    redis: redis_conn.clone(),
    config: Arc::new(config),
});

// 在Handler中使用
async fn handler(State(state): State<Arc<AppState>>) {
    let user = query_user(&state.db, id).await?;
    // ...
}
```

---

### `AppConfig`

**定义**:

```rust
#[derive(Debug, Clone)]
pub struct AppConfig {
    pub database_url: String,
    pub redis_url: String,
    pub port: u16,
    pub cache_ttl: Duration,
}
```

**功能**: 应用程序配置信息。

**字段说明**:

- `database_url`: 数据库连接字符串
- `redis_url`: Redis连接字符串
- `port`: 服务器端口号
- `cache_ttl`: 缓存过期时间

**方法**:

#### `AppConfig::from_env()`

**签名**:

```rust
pub fn from_env() -> Self
```

**功能**: 从环境变量加载配置。

**环境变量**:

- `DATABASE_URL`: 数据库连接URL（默认: `postgres://user:pass@localhost/mydb`）
- `REDIS_URL`: Redis连接URL（默认: `redis://127.0.0.1/`）
- `PORT`: 服务器端口（默认: `3000`）

**返回值**: 配置实例

**使用示例**:

```rust
// 设置环境变量
std::env::set_var("DATABASE_URL", "postgres://localhost/myapp");
std::env::set_var("PORT", "8080");

// 加载配置
let config = AppConfig::from_env();
assert_eq!(config.port, 8080);
```

---

### `AppError`

**定义**:

```rust
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Cache error: {0}")]
    CacheError(String),
    
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Conflict: {0}")]
    Conflict(String),
    
    #[error("Internal server error")]
    InternalError,
}
```

**功能**: 应用程序错误类型，自动转换为HTTP响应。

**错误变体**:

- `DatabaseError`: 数据库操作错误 → 500 Internal Server Error
- `CacheError`: 缓存操作错误 → 500 Internal Server Error  
- `NotFound`: 资源未找到 → 404 Not Found
- `BadRequest`: 请求参数错误 → 400 Bad Request
- `Conflict`: 资源冲突 → 409 Conflict
- `InternalError`: 内部错误 → 500 Internal Server Error

**特征实现**: `IntoResponse` - 自动转换为HTTP响应

**使用示例**:

```rust
async fn handler() -> Result<Json<User>, AppError> {
    let user = db.find(id).await
        .map_err(|e| AppError::DatabaseError(e.to_string()))?;
    
    user.ok_or_else(|| AppError::NotFound(format!("User {} not found", id)))
        .map(Json)
}
```

---

## Domain Models

### `User`

**定义**:

```rust
#[derive(Debug, Clone, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: i64,
    pub username: String,
    pub email: String,
    #[serde(skip_serializing)]
    pub password_hash: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}
```

**功能**: 用户实体模型。

**字段说明**:

- `id`: 用户唯一标识符（自动生成）
- `username`: 用户名（唯一）
- `email`: 电子邮件地址
- `password_hash`: 密码哈希（不序列化到JSON）
- `created_at`: 创建时间

**特征实现**: `Debug`, `Clone`, `Serialize`, `Deserialize`, `sqlx::FromRow`

---

### `CreateUserRequest`

**定义**:

```rust
#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}
```

**功能**: 创建用户请求。

**验证规则**:

- `username`: 必须唯一
- `email`: 必须是有效邮箱格式（建议添加验证）
- `password`: 明文密码（会被哈希后存储）

---

### `UpdateUserRequest`

**定义**:

```rust
#[derive(Debug, Deserialize)]
pub struct UpdateUserRequest {
    pub email: Option<String>,
    pub password: Option<String>,
}
```

**功能**: 更新用户请求。

**字段说明**:

- 所有字段都是Optional
- 只更新提供的字段
- 至少需要一个字段

---

## Repository Layer

### `UserRepository`

**定义**:

```rust
pub struct UserRepository {
    pool: PgPool,
}
```

**功能**: 用户数据访问层，负责数据库操作。

#### `UserRepository::new()`

**签名**:

```rust
pub fn new(pool: PgPool) -> Self
```

**功能**: 创建新的UserRepository实例。

**参数**:

- `pool`: PostgreSQL连接池

**返回值**: UserRepository实例

---

#### `UserRepository::create()`

**签名**:

```rust
pub async fn create(&self, req: &CreateUserRequest) -> Result<User, AppError>
```

**功能**: 创建新用户。

**参数**:

- `req`: 创建用户请求

**返回值**:

- `Ok(User)`: 创建成功，返回用户信息
- `Err(AppError)`: 创建失败

**错误**:

- `DatabaseError`: 数据库操作失败
- `Conflict`: 用户名已存在（通过唯一约束触发）

**使用示例**:

```rust
let repo = UserRepository::new(pool);
let req = CreateUserRequest {
    username: "alice".to_string(),
    email: "alice@example.com".to_string(),
    password: "secret123".to_string(),
};

let user = repo.create(&req).await?;
println!("Created user: {}", user.id);
```

---

#### `UserRepository::find_by_id()`

**签名**:

```rust
pub async fn find_by_id(&self, id: i64) -> Result<Option<User>, AppError>
```

**功能**: 根据ID查找用户。

**参数**:

- `id`: 用户ID

**返回值**:

- `Ok(Some(User))`: 找到用户
- `Ok(None)`: 用户不存在
- `Err(AppError)`: 查询失败

**复杂度**: O(1) - 使用主键索引

---

#### `UserRepository::list()`

**签名**:

```rust
pub async fn list(&self, page: u32, page_size: u32) -> Result<Vec<User>, AppError>
```

**功能**: 分页查询用户列表。

**参数**:

- `page`: 页码（从1开始）
- `page_size`: 每页数量

**返回值**:

- `Ok(Vec<User>)`: 用户列表
- `Err(AppError)`: 查询失败

**排序**: 按创建时间倒序（最新的在前）

**使用示例**:

```rust
// 获取第1页，每页20条
let users = repo.list(1, 20).await?;
println!("Found {} users", users.len());
```

---

#### `UserRepository::update()`

**签名**:

```rust
pub async fn update(&self, id: i64, req: &UpdateUserRequest) -> Result<User, AppError>
```

**功能**: 更新用户信息。

**参数**:

- `id`: 用户ID
- `req`: 更新请求

**返回值**:

- `Ok(User)`: 更新成功，返回更新后的用户
- `Err(AppError)`: 更新失败

**错误**:

- `BadRequest`: 没有提供任何更新字段
- `DatabaseError`: 用户不存在或数据库错误

---

#### `UserRepository::delete()`

**签名**:

```rust
pub async fn delete(&self, id: i64) -> Result<(), AppError>
```

**功能**: 删除用户。

**参数**:

- `id`: 用户ID

**返回值**:

- `Ok(())`: 删除成功
- `Err(AppError)`: 删除失败

**错误**:

- `NotFound`: 用户不存在

---

## Service Layer

### `UserService`

**定义**:

```rust
pub struct UserService {
    repository: UserRepository,
    redis: redis::aio::ConnectionManager,
    cache_ttl: Duration,
}
```

**功能**: 用户业务逻辑层，包含缓存和业务规则。

#### `UserService::new()`

**签名**:

```rust
pub fn new(pool: PgPool, redis: redis::aio::ConnectionManager, cache_ttl: Duration) -> Self
```

**功能**: 创建新的UserService实例。

**参数**:

- `pool`: 数据库连接池
- `redis`: Redis连接
- `cache_ttl`: 缓存过期时间

---

#### `UserService::create_user()`

**签名**:

```rust
pub async fn create_user(&self, req: CreateUserRequest) -> Result<User, AppError>
```

**功能**: 创建新用户，包含业务逻辑验证。

**业务逻辑**:

1. 验证用户名唯一性
2. 创建用户记录
3. 失效相关缓存

**参数**:

- `req`: 创建用户请求

**返回值**:

- `Ok(User)`: 创建成功
- `Err(AppError::Conflict)`: 用户名已存在

**使用示例**:

```rust
let service = UserService::new(pool, redis, Duration::from_secs(300));
let user = service.create_user(CreateUserRequest {
    username: "bob".to_string(),
    email: "bob@example.com".to_string(),
    password: "password123".to_string(),
}).await?;
```

---

#### `UserService::get_user()`

**签名**:

```rust
pub async fn get_user(&self, id: i64) -> Result<User, AppError>
```

**功能**: 获取用户信息，优先从缓存读取。

**缓存策略**:

1. 尝试从Redis读取
2. 缓存未命中时查询数据库
3. 将结果写入缓存

**参数**:

- `id`: 用户ID

**返回值**:

- `Ok(User)`: 找到用户
- `Err(AppError::NotFound)`: 用户不存在

**性能**: 缓存命中时 ~1ms，缓存未命中时 ~10ms

---

#### `UserService::list_users()`

**签名**:

```rust
pub async fn list_users(&self, pagination: PaginationQuery) -> Result<Vec<User>, AppError>
```

**功能**: 分页查询用户列表。

**参数**:

- `pagination`: 分页参数

**返回值**: 用户列表

---

#### `UserService::update_user()`

**签名**:

```rust
pub async fn update_user(&self, id: i64, req: UpdateUserRequest) -> Result<User, AppError>
```

**功能**: 更新用户信息并失效缓存。

---

#### `UserService::delete_user()`

**签名**:

```rust
pub async fn delete_user(&self, id: i64) -> Result<(), AppError>
```

**功能**: 删除用户并失效缓存。

---

## Controller Layer

### HTTP Handlers

所有Handler函数遵循Axum的签名规范。

#### `create_user_handler`

**签名**:

```rust
async fn create_user_handler(
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError>
```

**HTTP方法**: POST  
**路径**: `/users`  
**请求体**: JSON格式的CreateUserRequest  
**响应**: 201 Created + User JSON

**示例请求**:

```http
POST /users HTTP/1.1
Content-Type: application/json

{
  "username": "charlie",
  "email": "charlie@example.com",
  "password": "mypassword"
}
```

**示例响应**:

```http
HTTP/1.1 201 Created
Content-Type: application/json

{
  "id": 1,
  "username": "charlie",
  "email": "charlie@example.com",
  "created_at": "2025-10-28T10:00:00Z"
}
```

---

#### `get_user_handler`

**HTTP方法**: GET  
**路径**: `/users/:id`  
**响应**: 200 OK + User JSON

---

#### `list_users_handler`

**HTTP方法**: GET  
**路径**: `/users?page=1&page_size=20`  
**查询参数**:

- `page`: 页码（默认1）
- `page_size`: 每页数量（默认20）

---

#### `health_check_handler`

**HTTP方法**: GET  
**路径**: `/health`  
**功能**: 健康检查，检测数据库和Redis连接状态

**响应示例**:

```json
{
  "status": "healthy",
  "database": "healthy",
  "redis": "healthy"
}
```

---

## Application Setup

### `create_app()`

**签名**:

```rust
pub async fn create_app(state: Arc<AppState>) -> Router
```

**功能**: 创建并配置Axum应用。

**特性**:

- 路由配置
- 中间件链（日志、压缩、超时）
- 健康检查端点
- CORS支持（可选）

**返回值**: 配置好的Router

**使用示例**:

```rust
let state = Arc::new(AppState { /* ... */ });
let app = create_app(state).await;

let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
axum::serve(listener, app).await?;
```

---

## 最佳实践

### 错误处理

```rust
// ✅ 推荐：使用?操作符和map_err
let user = service.get_user(id).await
    .map_err(|e| {
        error!("Failed to get user: {}", e);
        e
    })?;

// ❌ 不推荐：直接unwrap
let user = service.get_user(id).await.unwrap();
```

### 事务处理

```rust
// 使用SQLx事务
let mut tx = pool.begin().await?;
let user = create_user(&mut tx, req).await?;
update_stats(&mut tx, user.id).await?;
tx.commit().await?;
```

### 缓存策略

```rust
// 读取优先缓存
// 1. 尝试Redis
// 2. 数据库查询
// 3. 写回Redis

// 更新时失效缓存
redis.del(format!("user:{}", id)).await?;
```

---

## 性能指标

| 操作 | 延迟(P50) | 延迟(P99) | 吞吐量 |
|------|-----------|-----------|--------|
| GET /users/:id (缓存命中) | 1ms | 5ms | 10K req/s |
| GET /users/:id (缓存未命中) | 10ms | 50ms | 1K req/s |
| POST /users | 15ms | 80ms | 500 req/s |
| GET /users (分页) | 20ms | 100ms | 300 req/s |

---

## 相关文档

- [异步编程最佳实践](./async_programming_api.md)
- [错误处理指南](../guides/error_handling.md)
- [部署指南](../guides/deployment.md)
- [示例代码](../../examples/web_framework_complete_integration.rs)

---

**版本**: 1.0.0  
**维护者**: OTLP Rust Team  
**最后更新**: 2025年10月28日
