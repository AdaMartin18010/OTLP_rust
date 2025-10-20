# SQLx 异步数据库完整集成指南 (Rust 1.90)

## 目录

- [SQLx 异步数据库完整集成指南 (Rust 1.90)](#sqlx-异步数据库完整集成指南-rust-190)
  - [目录](#目录)
  - [1. SQLx 架构与特性](#1-sqlx-架构与特性)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 国际标准对标](#12-国际标准对标)
  - [2. 完整集成实现](#2-完整集成实现)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 数据库配置](#22-数据库配置)
    - [2.3 实体定义](#23-实体定义)
    - [2.4 Repository 实现](#24-repository-实现)
  - [3. 高级查询模式](#3-高级查询模式)
    - [3.1 复杂查询 (JOIN)](#31-复杂查询-join)
    - [3.2 事务处理](#32-事务处理)
    - [3.3 动态查询 (Query Builder)](#33-动态查询-query-builder)
  - [4. 连接池优化](#4-连接池优化)
    - [4.1 监控连接池状态](#41-监控连接池状态)
    - [4.2 健康检查](#42-健康检查)
  - [5. Migration 管理](#5-migration-管理)
    - [5.1 创建 Migration](#51-创建-migration)
    - [5.2 运行 Migration](#52-运行-migration)
  - [6. OTLP 可观测性](#6-otlp-可观测性)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 错误处理](#71-错误处理)
    - [7.2 测试](#72-测试)
  - [总结](#总结)

## 1. SQLx 架构与特性

### 1.1 核心特性

| 特性 | 描述 | 优势 |
|------|------|------|
| **编译时SQL验证** | `query!()` 宏在编译时检查 | 零运行时错误 |
| **异步优先** | 完全基于 `tokio/async-std` | 高性能并发 |
| **数据库无关** | 支持 PostgreSQL, MySQL, SQLite, MSSQL | 可移植性 |
| **类型安全** | Rust 类型 ↔ SQL 类型映射 | 编译时保证 |
| **连接池** | 内置高性能连接池 | 自动管理 |
| **Migration** | 内置迁移工具 | 版本管理 |

### 1.2 国际标准对标

| 标准 | SQLx 实现 | 文档 |
|------|-----------|------|
| **SQL-92** | 完整支持 | [SQL Standard](https://www.iso.org/standard/76583.html) |
| **PostgreSQL Protocol** | 原生实现 | [Postgres Protocol](https://www.postgresql.org/docs/current/protocol.html) |
| **OpenTelemetry** | tracing 集成 | [OTLP Spec](https://opentelemetry.io/docs/specs/otel/) |

---

## 2. 完整集成实现

### 2.1 Cargo.toml

```toml
[dependencies]
# SQLx 核心
sqlx = { version = "0.8", features = [
    "runtime-tokio-rustls",  # 异步运行时 + TLS
    "postgres",              # PostgreSQL 驱动
    "uuid",                  # UUID 类型支持
    "chrono",                # 时间类型支持
    "json",                  # JSON/JSONB 支持
    "macros",                # query! 宏
    "migrate",               # Migration 支持
] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# 类型支持
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

[dev-dependencies]
tokio-test = "0.4"
```

### 2.2 数据库配置

```rust
// src/config.rs
use sqlx::postgres::{PgPoolOptions, PgConnectOptions};
use std::time::Duration;

pub async fn create_pool(database_url: &str) -> anyhow::Result<sqlx::PgPool> {
    let options = database_url.parse::<PgConnectOptions>()?
        .application_name("rust-app")
        .log_statements(tracing::log::LevelFilter::Debug)
        .log_slow_statements(tracing::log::LevelFilter::Warn, Duration::from_secs(1));

    let pool = PgPoolOptions::new()
        .max_connections(50)                       // 最大连接数
        .min_connections(5)                        // 最小连接数
        .acquire_timeout(Duration::from_secs(3))   // 获取连接超时
        .idle_timeout(Duration::from_secs(600))    // 空闲连接超时 (10分钟)
        .max_lifetime(Duration::from_secs(1800))   // 连接最大生存时间 (30分钟)
        .connect_with(options)
        .await?;

    Ok(pool)
}
```

### 2.3 实体定义

```rust
// src/models/user.rs
use sqlx::FromRow;
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize, FromRow)]
pub struct User {
    pub id: Uuid,
    pub email: String,
    pub name: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub metadata: serde_json::Value,  // JSONB 字段
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub email: String,
    pub name: String,
}

#[derive(Debug, Deserialize)]
pub struct UpdateUserRequest {
    pub name: Option<String>,
    pub metadata: Option<serde_json::Value>,
}
```

### 2.4 Repository 实现

```rust
// src/repository/user.rs
use sqlx::PgPool;
use uuid::Uuid;
use tracing::{info, instrument};
use crate::models::{User, CreateUserRequest, UpdateUserRequest};

pub struct UserRepository {
    pool: PgPool,
}

impl UserRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    /// 创建用户 (编译时 SQL 验证)
    #[instrument(skip(self))]
    pub async fn create(&self, req: &CreateUserRequest) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            INSERT INTO users (id, email, name, created_at, updated_at, metadata)
            VALUES ($1, $2, $3, NOW(), NOW(), '{}')
            RETURNING id, email, name, created_at, updated_at, metadata
            "#,
            Uuid::new_v4(),
            req.email,
            req.name
        )
        .fetch_one(&self.pool)
        .await?;

        info!(user_id = %user.id, "User created");
        Ok(user)
    }

    /// 根据 ID 查询用户
    #[instrument(skip(self))]
    pub async fn find_by_id(&self, user_id: Uuid) -> Result<Option<User>, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, email, name, created_at, updated_at, metadata
            FROM users
            WHERE id = $1
            "#,
            user_id
        )
        .fetch_optional(&self.pool)
        .await?;

        Ok(user)
    }

    /// 根据邮箱查询用户
    #[instrument(skip(self))]
    pub async fn find_by_email(&self, email: &str) -> Result<Option<User>, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, email, name, created_at, updated_at, metadata
            FROM users
            WHERE email = $1
            "#,
            email
        )
        .fetch_optional(&self.pool)
        .await?;

        Ok(user)
    }

    /// 列出所有用户 (分页)
    #[instrument(skip(self))]
    pub async fn list(&self, limit: i64, offset: i64) -> Result<Vec<User>, sqlx::Error> {
        let users = sqlx::query_as!(
            User,
            r#"
            SELECT id, email, name, created_at, updated_at, metadata
            FROM users
            ORDER BY created_at DESC
            LIMIT $1 OFFSET $2
            "#,
            limit,
            offset
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(users)
    }

    /// 更新用户
    #[instrument(skip(self))]
    pub async fn update(&self, user_id: Uuid, req: &UpdateUserRequest) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            UPDATE users
            SET 
                name = COALESCE($2, name),
                metadata = COALESCE($3, metadata),
                updated_at = NOW()
            WHERE id = $1
            RETURNING id, email, name, created_at, updated_at, metadata
            "#,
            user_id,
            req.name.as_ref(),
            req.metadata.as_ref()
        )
        .fetch_one(&self.pool)
        .await?;

        info!(user_id = %user.id, "User updated");
        Ok(user)
    }

    /// 删除用户
    #[instrument(skip(self))]
    pub async fn delete(&self, user_id: Uuid) -> Result<bool, sqlx::Error> {
        let result = sqlx::query!(
            r#"
            DELETE FROM users
            WHERE id = $1
            "#,
            user_id
        )
        .execute(&self.pool)
        .await?;

        Ok(result.rows_affected() > 0)
    }

    /// 批量插入 (高性能)
    #[instrument(skip(self, users))]
    pub async fn batch_create(&self, users: &[CreateUserRequest]) -> Result<u64, sqlx::Error> {
        let mut tx = self.pool.begin().await?;

        let mut inserted = 0;
        for user in users {
            sqlx::query!(
                r#"
                INSERT INTO users (id, email, name, created_at, updated_at, metadata)
                VALUES ($1, $2, $3, NOW(), NOW(), '{}')
                "#,
                Uuid::new_v4(),
                user.email,
                user.name
            )
            .execute(&mut *tx)
            .await?;
            inserted += 1;
        }

        tx.commit().await?;
        info!(count = inserted, "Batch users created");

        Ok(inserted)
    }
}
```

---

## 3. 高级查询模式

### 3.1 复杂查询 (JOIN)

```rust
#[derive(Debug, sqlx::FromRow)]
struct UserWithOrders {
    user_id: Uuid,
    user_name: String,
    order_count: i64,
    total_amount: sqlx::types::Decimal,
}

#[instrument(skip(pool))]
async fn get_users_with_orders(pool: &PgPool) -> Result<Vec<UserWithOrders>, sqlx::Error> {
    let result = sqlx::query_as!(
        UserWithOrders,
        r#"
        SELECT 
            u.id as user_id,
            u.name as user_name,
            COUNT(o.id) as "order_count!",
            COALESCE(SUM(o.amount), 0) as "total_amount!"
        FROM users u
        LEFT JOIN orders o ON u.id = o.user_id
        GROUP BY u.id, u.name
        HAVING COUNT(o.id) > 0
        ORDER BY total_amount DESC
        "#
    )
    .fetch_all(pool)
    .await?;

    Ok(result)
}
```

### 3.2 事务处理

```rust
use sqlx::{Postgres, Transaction};

#[instrument(skip(pool))]
async fn transfer_funds(
    pool: &PgPool,
    from_user: Uuid,
    to_user: Uuid,
    amount: sqlx::types::Decimal,
) -> Result<(), sqlx::Error> {
    let mut tx = pool.begin().await?;

    // 1. 扣款
    sqlx::query!(
        r#"
        UPDATE wallets
        SET balance = balance - $1
        WHERE user_id = $2 AND balance >= $1
        "#,
        amount,
        from_user
    )
    .execute(&mut *tx)
    .await?;

    // 2. 入账
    sqlx::query!(
        r#"
        UPDATE wallets
        SET balance = balance + $1
        WHERE user_id = $2
        "#,
        amount,
        to_user
    )
    .execute(&mut *tx)
    .await?;

    // 3. 记录日志
    sqlx::query!(
        r#"
        INSERT INTO transaction_logs (from_user, to_user, amount, created_at)
        VALUES ($1, $2, $3, NOW())
        "#,
        from_user,
        to_user,
        amount
    )
    .execute(&mut *tx)
    .await?;

    tx.commit().await?;

    info!(from = %from_user, to = %to_user, amount = %amount, "Transfer completed");
    Ok(())
}
```

### 3.3 动态查询 (Query Builder)

```rust
use sqlx::QueryBuilder;

#[instrument(skip(pool))]
async fn search_users(
    pool: &PgPool,
    email: Option<&str>,
    name: Option<&str>,
    created_after: Option<DateTime<Utc>>,
) -> Result<Vec<User>, sqlx::Error> {
    let mut query = QueryBuilder::new("SELECT id, email, name, created_at, updated_at, metadata FROM users WHERE 1=1");

    if let Some(email) = email {
        query.push(" AND email LIKE ");
        query.push_bind(format!("%{}%", email));
    }

    if let Some(name) = name {
        query.push(" AND name LIKE ");
        query.push_bind(format!("%{}%", name));
    }

    if let Some(created_after) = created_after {
        query.push(" AND created_at >= ");
        query.push_bind(created_after);
    }

    query.push(" ORDER BY created_at DESC");

    let users = query.build_query_as::<User>()
        .fetch_all(pool)
        .await?;

    Ok(users)
}
```

---

## 4. 连接池优化

### 4.1 监控连接池状态

```rust
use tracing::info;

#[instrument(skip(pool))]
pub async fn monitor_pool(pool: &PgPool) {
    info!(
        active_connections = pool.size(),
        idle_connections = pool.num_idle(),
        "Pool status"
    );
}
```

### 4.2 健康检查

```rust
#[instrument(skip(pool))]
pub async fn health_check(pool: &PgPool) -> Result<(), sqlx::Error> {
    sqlx::query!("SELECT 1 as check")
        .fetch_one(pool)
        .await?;
    Ok(())
}
```

---

## 5. Migration 管理

### 5.1 创建 Migration

```sql
-- migrations/20250111_000001_create_users.sql
CREATE TABLE users (
    id UUID PRIMARY KEY,
    email VARCHAR(255) UNIQUE NOT NULL,
    name VARCHAR(255) NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    metadata JSONB NOT NULL DEFAULT '{}'::jsonb
);

CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_created_at ON users(created_at DESC);
```

### 5.2 运行 Migration

```rust
// src/main.rs
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let pool = create_pool(&database_url).await?;

    // 运行 Migration
    sqlx::migrate!("./migrations")
        .run(&pool)
        .await?;

    tracing::info!("Migrations applied successfully");

    Ok(())
}
```

---

## 6. OTLP 可观测性

```rust
// 自动集成 (SQLx 支持 tracing)
#[instrument(skip(pool))]
async fn query_user(pool: &PgPool, user_id: Uuid) -> Result<User, sqlx::Error> {
    // SQLx 自动生成 Span:
    // - db.statement: "SELECT ..."
    // - db.system: "postgresql"
    // - db.name: "my_database"
    
    let user = sqlx::query_as!(
        User,
        "SELECT * FROM users WHERE id = $1",
        user_id
    )
    .fetch_one(pool)
    .await?;

    Ok(user)
}
```

---

## 7. 最佳实践

### 7.1 错误处理

```rust
#[derive(thiserror::Error, Debug)]
pub enum UserError {
    #[error("User not found: {0}")]
    NotFound(Uuid),

    #[error("Email already exists: {0}")]
    DuplicateEmail(String),

    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
}

impl From<sqlx::Error> for UserError {
    fn from(err: sqlx::Error) -> Self {
        match err {
            sqlx::Error::RowNotFound => UserError::NotFound(Uuid::nil()),
            _ => UserError::Database(err),
        }
    }
}
```

### 7.2 测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_create_user() {
        let pool = create_test_pool().await.unwrap();
        let repo = UserRepository::new(pool);

        let req = CreateUserRequest {
            email: "test@example.com".to_string(),
            name: "Test User".to_string(),
        };

        let user = repo.create(&req).await.unwrap();
        assert_eq!(user.email, req.email);
    }

    async fn create_test_pool() -> anyhow::Result<PgPool> {
        let pool = PgPoolOptions::new()
            .max_connections(1)
            .connect("postgres://test:test@localhost/test_db")
            .await?;

        sqlx::migrate!("./migrations").run(&pool).await?;

        Ok(pool)
    }
}
```

---

## 总结

✅ **编译时 SQL 验证** (零运行时错误)  
✅ **异步高性能** (tokio 集成)  
✅ **类型安全** (Rust ↔ SQL 映射)  
✅ **完整 Migration** (版本管理)  
✅ **深度 OTLP 集成** (自动追踪)  
✅ **生产级连接池** (自动管理)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
