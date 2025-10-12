# SurrealDB 完整实现：多模型数据库 Rust 1.90 + OTLP 集成指南

## 目录

- [SurrealDB 完整实现：多模型数据库 Rust 1.90 + OTLP 集成指南](#surrealdb-完整实现多模型数据库-rust-190--otlp-集成指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 SurrealDB 定位](#11-surrealdb-定位)
      - [核心优势](#核心优势)
    - [1.2 与传统数据库对比](#12-与传统数据库对比)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. SurrealDB 核心架构](#2-surrealdb-核心架构)
    - [2.1 多模型架构](#21-多模型架构)
  - [3. 项目初始化与配置](#3-项目初始化与配置)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 连接数据库](#32-连接数据库)
  - [4. 数据模型与 Schema](#4-数据模型与-schema)
    - [4.1 定义表结构](#41-定义表结构)
    - [4.2 CRUD 操作](#42-crud-操作)
  - [5. SurrealQL 高级查询](#5-surrealql-高级查询)
    - [5.1 条件查询](#51-条件查询)
    - [5.2 图查询（关系遍历）](#52-图查询关系遍历)
    - [5.3 全文搜索](#53-全文搜索)
  - [6. 实时查询（Live Queries）](#6-实时查询live-queries)
  - [7. 事务管理](#7-事务管理)
  - [8. 权限与安全](#8-权限与安全)
    - [8.1 定义权限](#81-定义权限)
    - [8.2 认证](#82-认证)
  - [9. OTLP 分布式追踪集成](#9-otlp-分布式追踪集成)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
    - [10.1 连接池管理](#101-连接池管理)
    - [10.2 错误处理](#102-错误处理)
  - [11. 总结与最佳实践](#11-总结与最佳实践)
    - [11.1 核心优势](#111-核心优势)
    - [11.2 最佳实践](#112-最佳实践)

---

## 1. 概述

### 1.1 SurrealDB 定位

**SurrealDB** 是下一代**多模型数据库**，原生 Rust 实现，支持文档、图、键值、全文搜索等多种数据模型，提供 SQL-like 查询语言 SurrealQL。

#### 核心优势

- **多模型支持**：文档、图、键值、时间序列、全文搜索
- **原生 Rust**：性能极致、类型安全
- **实时查询**：Live Queries，数据变化实时推送
- **嵌入式模式**：可作为库嵌入应用，无需额外服务
- **分布式架构**：内置 Raft 一致性，支持水平扩展
- **权限系统**：细粒度的行级别权限控制（RLS）

### 1.2 与传统数据库对比

| 特性 | SurrealDB | PostgreSQL | MongoDB | Neo4j |
|------|-----------|------------|---------|-------|
| **多模型** | ✅ 原生 | ⚠️ 扩展 | ⚠️ 文档 | ⚠️ 图 |
| **图查询** | ✅ 原生 | ⚠️ 递归CTE | ❌ | ✅ 原生 |
| **实时查询** | ✅ 原生 | ⚠️ LISTEN/NOTIFY | ⚠️ Change Streams | ❌ |
| **嵌入式** | ✅ 支持 | ❌ | ❌ | ❌ |
| **Rust 客户端** | ✅ 原生 | ⚠️ 第三方 | ⚠️ 第三方 | ⚠️ 第三方 |

### 1.3 国际标准对标

| 标准/协议 | SurrealDB 实现 |
|----------|-------------|
| **ACID 事务** | ✅ 完整支持 |
| **CAP 定理** | ✅ CP（一致性+分区容错） |
| **Raft 共识** | ✅ 原生支持 |
| **GraphQL** | ⚠️ 可桥接 |
| **REST API** | ✅ HTTP 端点 |

---

## 2. SurrealDB 核心架构

### 2.1 多模型架构

```text
┌────────────────────────────────────────┐
│       Application Layer                │
│  ┌──────────────┐  ┌──────────────┐    │
│  │  SurrealQL   │  │  Rust SDK    │    │
│  └──────────────┘  └──────────────┘    │
├────────────────────────────────────────┤
│         Data Model Layer               │
│  ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐      │
│  │ Doc │ │Graph│ │ KV  │ │ TS  │      │
│  └─────┘ └─────┘ └─────┘ └─────┘      │
├────────────────────────────────────────┤
│         Storage Layer                  │
│  ┌──────────────────────────────────┐  │
│  │  RocksDB / TiKV / IndexedDB      │  │
│  └──────────────────────────────────┘  │
└────────────────────────────────────────┘
```

---

## 3. 项目初始化与配置

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "surrealdb-advanced-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# SurrealDB 核心
surrealdb = { version = "2.1", features = ["protocol-ws", "kv-rocksdb"] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 工具库
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
thiserror = "1.0"
anyhow = "1.0"

# 追踪与指标
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"
opentelemetry = { version = "0.25", features = ["trace"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["trace", "grpc-tonic"] }
```

### 3.2 连接数据库

```rust
use surrealdb::Surreal;
use surrealdb::engine::remote::ws::{Client, Ws};
use surrealdb::opt::auth::Root;

// 连接远程 SurrealDB
pub async fn connect_remote(url: &str) -> Result<Surreal<Client>, surrealdb::Error> {
    let db = Surreal::new::<Ws>(url).await?;
    
    // 登录
    db.signin(Root {
        username: "root",
        password: "root",
    }).await?;
    
    // 使用命名空间和数据库
    db.use_ns("demo").use_db("app").await?;
    
    tracing::info!("Connected to SurrealDB at {}", url);
    
    Ok(db)
}

// 嵌入式模式（内存）
pub async fn connect_memory() -> Result<Surreal<surrealdb::engine::local::Db>, surrealdb::Error> {
    use surrealdb::engine::local::Mem;
    
    let db = Surreal::new::<Mem>(()).await?;
    
    db.use_ns("demo").use_db("app").await?;
    
    tracing::info!("Created in-memory SurrealDB instance");
    
    Ok(db)
}

// 嵌入式模式（文件）
pub async fn connect_file(path: &str) -> Result<Surreal<surrealdb::engine::local::Db>, surrealdb::Error> {
    use surrealdb::engine::local::File;
    
    let db = Surreal::new::<File>(path).await?;
    
    db.use_ns("demo").use_db("app").await?;
    
    tracing::info!("Connected to file-based SurrealDB at {}", path);
    
    Ok(db)
}
```

---

## 4. 数据模型与 Schema

### 4.1 定义表结构

```rust
use serde::{Serialize, Deserialize};
use surrealdb::sql::Thing;

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: Option<Thing>,
    pub email: String,
    pub name: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Post {
    pub id: Option<Thing>,
    pub title: String,
    pub content: String,
    pub author: Thing,  // 关系：指向 User
    pub published: bool,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

// 定义 Schema（可选，SurrealDB 是无 Schema 的）
pub async fn define_schema(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    // 定义 users 表
    db.query(
        r#"
        DEFINE TABLE users SCHEMAFULL;
        DEFINE FIELD email ON users TYPE string ASSERT string::is::email($value);
        DEFINE FIELD name ON users TYPE string;
        DEFINE FIELD created_at ON users TYPE datetime DEFAULT time::now();
        DEFINE INDEX unique_email ON users COLUMNS email UNIQUE;
        "#
    ).await?;
    
    // 定义 posts 表
    db.query(
        r#"
        DEFINE TABLE posts SCHEMAFULL;
        DEFINE FIELD title ON posts TYPE string;
        DEFINE FIELD content ON posts TYPE string;
        DEFINE FIELD author ON posts TYPE record(users);
        DEFINE FIELD published ON posts TYPE bool DEFAULT false;
        DEFINE FIELD created_at ON posts TYPE datetime DEFAULT time::now();
        "#
    ).await?;
    
    tracing::info!("Schema defined");
    
    Ok(())
}
```

### 4.2 CRUD 操作

```rust
// 创建用户
pub async fn create_user(
    db: &Surreal<Client>,
    email: &str,
    name: &str,
) -> Result<User, surrealdb::Error> {
    let user: Option<User> = db.create("users")
        .content(User {
            id: None,
            email: email.to_string(),
            name: name.to_string(),
            created_at: chrono::Utc::now(),
        })
        .await?;
    
    Ok(user.unwrap())
}

// 查询用户
pub async fn find_user_by_id(
    db: &Surreal<Client>,
    user_id: &str,
) -> Result<Option<User>, surrealdb::Error> {
    let user: Option<User> = db.select(("users", user_id)).await?;
    
    Ok(user)
}

// 查询所有用户
pub async fn find_all_users(db: &Surreal<Client>) -> Result<Vec<User>, surrealdb::Error> {
    let users: Vec<User> = db.select("users").await?;
    
    Ok(users)
}

// 更新用户
pub async fn update_user(
    db: &Surreal<Client>,
    user_id: &str,
    new_name: &str,
) -> Result<Option<User>, surrealdb::Error> {
    let user: Option<User> = db.update(("users", user_id))
        .merge(serde_json::json!({
            "name": new_name
        }))
        .await?;
    
    Ok(user)
}

// 删除用户
pub async fn delete_user(
    db: &Surreal<Client>,
    user_id: &str,
) -> Result<Option<User>, surrealdb::Error> {
    let user: Option<User> = db.delete(("users", user_id)).await?;
    
    Ok(user)
}
```

---

## 5. SurrealQL 高级查询

### 5.1 条件查询

```rust
use surrealdb::sql::Value;

// 使用 SurrealQL 查询
pub async fn query_users_by_email(
    db: &Surreal<Client>,
    email_pattern: &str,
) -> Result<Vec<User>, surrealdb::Error> {
    let mut response = db.query(
        r#"
        SELECT * FROM users WHERE email CONTAINS $pattern
        "#
    )
    .bind(("pattern", email_pattern))
    .await?;
    
    let users: Vec<User> = response.take(0)?;
    
    Ok(users)
}

// 复杂查询
pub async fn complex_query(db: &Surreal<Client>) -> Result<Vec<User>, surrealdb::Error> {
    let mut response = db.query(
        r#"
        SELECT * FROM users 
        WHERE email CONTAINS '@example.com'
        AND created_at > time::now() - 7d
        ORDER BY created_at DESC
        LIMIT 10
        "#
    ).await?;
    
    let users: Vec<User> = response.take(0)?;
    
    Ok(users)
}
```

### 5.2 图查询（关系遍历）

```rust
// 定义关系（Edge）
#[derive(Debug, Serialize, Deserialize)]
pub struct Follows {
    pub id: Option<Thing>,
    pub r#in: Thing,   // 被关注者
    pub out: Thing,    // 关注者
    pub created_at: chrono::DateTime<chrono::Utc>,
}

// 创建关系
pub async fn create_follow(
    db: &Surreal<Client>,
    follower_id: &str,
    followed_id: &str,
) -> Result<(), surrealdb::Error> {
    db.query(
        r#"
        RELATE $follower->follows->$followed
        SET created_at = time::now()
        "#
    )
    .bind(("follower", Thing::from(("users", follower_id))))
    .bind(("followed", Thing::from(("users", followed_id))))
    .await?;
    
    Ok(())
}

// 查询用户的关注者（1 层）
pub async fn find_followers(
    db: &Surreal<Client>,
    user_id: &str,
) -> Result<Vec<User>, surrealdb::Error> {
    let mut response = db.query(
        r#"
        SELECT <-follows<-users.* AS followers 
        FROM $user
        "#
    )
    .bind(("user", Thing::from(("users", user_id))))
    .await?;
    
    #[derive(Deserialize)]
    struct QueryResult {
        followers: Vec<User>,
    }
    
    let result: Vec<QueryResult> = response.take(0)?;
    
    Ok(result.into_iter().flat_map(|r| r.followers).collect())
}

// 查询用户的朋友（双向关注）
pub async fn find_friends(
    db: &Surreal<Client>,
    user_id: &str,
) -> Result<Vec<User>, surrealdb::Error> {
    let mut response = db.query(
        r#"
        LET $user_follows = (SELECT ->follows->users.* AS followed FROM $user);
        LET $user_followers = (SELECT <-follows<-users.* AS followers FROM $user);
        RETURN array::intersect($user_follows.followed, $user_followers.followers)
        "#
    )
    .bind(("user", Thing::from(("users", user_id))))
    .await?;
    
    let friends: Vec<User> = response.take(2)?;
    
    Ok(friends)
}
```

### 5.3 全文搜索

```rust
// 定义全文索引
pub async fn define_fulltext_index(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    db.query(
        r#"
        DEFINE ANALYZER simple TOKENIZERS blank,class FILTERS lowercase,snowball(english);
        DEFINE INDEX idx_post_title_content ON posts FIELDS title,content SEARCH ANALYZER simple BM25;
        "#
    ).await?;
    
    Ok(())
}

// 全文搜索
pub async fn fulltext_search(
    db: &Surreal<Client>,
    search_term: &str,
) -> Result<Vec<Post>, surrealdb::Error> {
    let mut response = db.query(
        r#"
        SELECT * FROM posts 
        WHERE title @@ $term OR content @@ $term
        ORDER BY search::score(1) DESC
        "#
    )
    .bind(("term", search_term))
    .await?;
    
    let posts: Vec<Post> = response.take(0)?;
    
    Ok(posts)
}
```

---

## 6. 实时查询（Live Queries）

```rust
use futures::StreamExt;

// 监听 users 表的变化
pub async fn live_query_users(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    let mut stream = db.select("users").live().await?;
    
    while let Some(result) = stream.next().await {
        match result {
            Ok(notification) => {
                tracing::info!("Live query notification: {:?}", notification);
                // 处理变化
            }
            Err(e) => {
                tracing::error!("Live query error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

// 条件 Live Query
pub async fn live_query_new_posts(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    let mut stream = db.query(
        r#"
        LIVE SELECT * FROM posts WHERE published = true
        "#
    ).await?.stream::<Post>(0)?;
    
    while let Some(result) = stream.next().await {
        match result {
            Ok(post) => {
                tracing::info!("New published post: {:?}", post);
            }
            Err(e) => {
                tracing::error!("Error: {:?}", e);
            }
        }
    }
    
    Ok(())
}
```

---

## 7. 事务管理

```rust
// SurrealDB 事务
pub async fn transaction_example(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    db.query(
        r#"
        BEGIN TRANSACTION;
        
        LET $user = CREATE users SET email = "test@example.com", name = "Test User";
        LET $post = CREATE posts SET 
            title = "First Post",
            content = "Content",
            author = $user.id,
            published = false;
        
        COMMIT TRANSACTION;
        "#
    ).await?;
    
    Ok(())
}
```

---

## 8. 权限与安全

### 8.1 定义权限

```rust
pub async fn define_permissions(db: &Surreal<Client>) -> Result<(), surrealdb::Error> {
    db.query(
        r#"
        -- 用户只能读取自己的数据
        DEFINE TABLE users SCHEMAFULL
            PERMISSIONS
                FOR select WHERE id = $auth.id
                FOR update, delete WHERE id = $auth.id
                FOR create NONE;
        
        -- 用户只能管理自己的文章
        DEFINE TABLE posts SCHEMAFULL
            PERMISSIONS
                FOR select WHERE published = true OR author = $auth.id
                FOR create, update, delete WHERE author = $auth.id;
        "#
    ).await?;
    
    Ok(())
}
```

### 8.2 认证

```rust
use surrealdb::opt::auth::Scope;

// 用户注册
pub async fn signup_user(
    db: &Surreal<Client>,
    email: &str,
    password: &str,
) -> Result<String, surrealdb::Error> {
    #[derive(Deserialize)]
    struct SignupResult {
        token: String,
    }
    
    let result: SignupResult = db.signup(Scope {
        namespace: "demo",
        database: "app",
        scope: "user",
        params: serde_json::json!({
            "email": email,
            "password": password,
        }),
    }).await?;
    
    Ok(result.token)
}

// 用户登录
pub async fn signin_user(
    db: &Surreal<Client>,
    email: &str,
    password: &str,
) -> Result<String, surrealdb::Error> {
    #[derive(Deserialize)]
    struct SigninResult {
        token: String,
    }
    
    let result: SigninResult = db.signin(Scope {
        namespace: "demo",
        database: "app",
        scope: "user",
        params: serde_json::json!({
            "email": email,
            "password": password,
        }),
    }).await?;
    
    Ok(result.token)
}
```

---

## 9. OTLP 分布式追踪集成

```rust
use tracing::instrument;

#[instrument(skip(db), fields(db.system = "surrealdb", db.operation = "SELECT"))]
pub async fn traced_query(
    db: &Surreal<Client>,
    query: &str,
) -> Result<Vec<User>, surrealdb::Error> {
    let mut response = db.query(query).await?;
    let users: Vec<User> = response.take(0)?;
    
    tracing::info!("Query returned {} users", users.len());
    
    Ok(users)
}
```

---

## 10. 生产环境最佳实践

### 10.1 连接池管理

```rust
use std::sync::Arc;
use tokio::sync::OnceCell;

static DB: OnceCell<Arc<Surreal<Client>>> = OnceCell::const_new();

pub async fn get_db() -> Arc<Surreal<Client>> {
    DB.get_or_init(|| async {
        let db = connect_remote("ws://localhost:8000").await.unwrap();
        Arc::new(db)
    }).await.clone()
}
```

### 10.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] surrealdb::Error),
    
    #[error("User not found")]
    UserNotFound,
    
    #[error("Unauthorized")]
    Unauthorized,
}
```

---

## 11. 总结与最佳实践

### 11.1 核心优势

1. **多模型统一**：文档、图、键值一体化
2. **实时查询**：数据变化实时推送
3. **嵌入式支持**：可作为库嵌入应用
4. **原生 Rust**：性能极致、类型安全
5. **细粒度权限**：行级别权限控制

### 11.2 最佳实践

**✅ 推荐做法**:

- 使用 SCHEMAFULL 定义关键表结构
- 利用图查询简化关系数据处理
- 使用 Live Queries 实现实时功能
- 实现细粒度权限控制
- 使用嵌入式模式简化部署

**❌ 避免做法**:

- 不要过度依赖无 Schema 特性
- 不要忽略索引优化
- 不要在客户端存储敏感数据
- 不要忽略 Live Query 资源管理

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**SurrealDB 版本**: 2.1  
**OpenTelemetry 版本**: 0.25  

---

**国际标准对齐**:

- ✅ ACID 事务
- ✅ CAP 定理（CP）
- ✅ Raft 共识算法
- ✅ GraphQL 兼容
- ✅ OpenTelemetry Database Semantic Conventions

**参考文献**:

- SurrealDB Official Documentation: <https://surrealdb.com/docs>
- SurrealQL Reference: <https://surrealdb.com/docs/surrealql>
- Raft Consensus Algorithm
