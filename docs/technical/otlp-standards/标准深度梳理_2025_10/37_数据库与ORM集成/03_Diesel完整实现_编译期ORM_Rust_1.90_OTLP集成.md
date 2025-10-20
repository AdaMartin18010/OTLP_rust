# Diesel 完整实现：编译期 ORM Rust 1.90 + OTLP 集成指南

## 目录

- [Diesel 完整实现：编译期 ORM Rust 1.90 + OTLP 集成指南](#diesel-完整实现编译期-orm-rust-190--otlp-集成指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Diesel 定位](#11-diesel-定位)
      - [核心优势](#核心优势)
    - [1.2 与其他 ORM 对比](#12-与其他-orm-对比)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. Diesel 核心架构](#2-diesel-核心架构)
    - [2.1 三层架构](#21-三层架构)
    - [2.2 类型系统](#22-类型系统)
  - [3. 项目初始化与配置](#3-项目初始化与配置)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 Diesel CLI 安装](#32-diesel-cli-安装)
    - [3.3 初始化项目](#33-初始化项目)
  - [4. Schema 定义与代码生成](#4-schema-定义与代码生成)
    - [4.1 自动生成 Schema](#41-自动生成-schema)
    - [4.2 手动定义 Schema](#42-手动定义-schema)
    - [4.3 Model 定义](#43-model-定义)
  - [5. 查询 DSL](#5-查询-dsl)
    - [5.1 基础查询](#51-基础查询)
    - [5.2 条件查询](#52-条件查询)
    - [5.3 JOIN 查询](#53-join-查询)
  - [6. 插入、更新、删除](#6-插入更新删除)
    - [6.1 插入数据](#61-插入数据)
    - [6.2 更新数据](#62-更新数据)
    - [6.3 删除数据](#63-删除数据)
  - [7. 关联查询](#7-关联查询)
    - [7.1 定义关联](#71-定义关联)
    - [7.2 一对多查询](#72-一对多查询)
    - [7.3 多对多查询](#73-多对多查询)
  - [8. 事务管理](#8-事务管理)
    - [8.1 基础事务](#81-基础事务)
    - [8.2 显式事务](#82-显式事务)
  - [9. 迁移管理](#9-迁移管理)
    - [9.1 创建迁移](#91-创建迁移)
    - [9.2 运行迁移](#92-运行迁移)
  - [10. 高级查询模式](#10-高级查询模式)
    - [10.1 原始 SQL](#101-原始-sql)
    - [10.2 子查询](#102-子查询)
    - [10.3 聚合查询](#103-聚合查询)
  - [11. 连接池集成](#11-连接池集成)
    - [11.1 R2D2 连接池](#111-r2d2-连接池)
    - [11.2 连接池管理](#112-连接池管理)
  - [12. 异步支持（实验性）](#12-异步支持实验性)
    - [12.1 diesel-async](#121-diesel-async)
    - [12.2 异步查询示例](#122-异步查询示例)
  - [13. OTLP 分布式追踪集成](#13-otlp-分布式追踪集成)
    - [13.1 OTLP 初始化](#131-otlp-初始化)
    - [13.2 追踪查询](#132-追踪查询)
  - [14. 测试策略](#14-测试策略)
    - [14.1 测试数据库设置](#141-测试数据库设置)
    - [14.2 集成测试](#142-集成测试)
  - [15. 生产环境最佳实践](#15-生产环境最佳实践)
    - [15.1 性能优化](#151-性能优化)
    - [15.2 错误处理](#152-错误处理)
  - [16. 国际标准对标](#16-国际标准对标)
    - [16.1 对标清单](#161-对标清单)
  - [17. 总结与最佳实践](#17-总结与最佳实践)
    - [17.1 核心优势](#171-核心优势)
    - [17.2 最佳实践](#172-最佳实践)

---

## 1. 概述

### 1.1 Diesel 定位

**Diesel** 是 Rust 生态中**类型安全、编译期验证**的 ORM 和查询构建器，提供零成本抽象和防止 SQL 注入的保护。

#### 核心优势

- **编译期类型安全**：SQL 错误在编译时捕获
- **零运行时开销**：无反射、无动态分派
- **强类型 DSL**：类型系统保证查询正确性
- **可组合查询**：查询可以组合和重用
- **防 SQL 注入**：参数化查询自动处理
- **性能极致**：接近手写 SQL 的性能

### 1.2 与其他 ORM 对比

| 特性 | Diesel | SQLx | SeaORM | Prisma |
|------|--------|------|--------|--------|
| **编译期验证** | ✅ 完整 | ✅ 部分 | ❌ 运行时 | ✅ 完整 |
| **异步支持** | ⚠️ 实验性 | ✅ 原生 | ✅ 原生 | ✅ 原生 |
| **查询 DSL** | ✅ 静态 | ⚠️ 编译期 | ✅ 动态 | ✅ 动态 |
| **学习曲线** | 高 | 低 | 中等 | 低 |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **类型安全** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

### 1.3 国际标准对标

| 标准/最佳实践 | Diesel 实现 |
|--------------|-----------|
| **SQL:2016** | ✅ 完整支持 |
| **ACID 事务** | ✅ 完整支持 |
| **参数化查询** | ✅ 完全防护 |
| **连接池标准** | ✅ R2D2 集成 |
| **迁移工具** | ✅ CLI 工具 |
| **Query Builder Pattern** | ✅ 完整实现 |

---

## 2. Diesel 核心架构

### 2.1 三层架构

```text
┌────────────────────────────────────────┐
│       Application Layer                │
│  ┌──────────────┐  ┌──────────────┐    │
│  │  Models      │  │  Repository  │    │
│  └──────────────┘  └──────────────┘    │
├────────────────────────────────────────┤
│         Diesel DSL Layer               │
│  ┌──────────┐  ┌──────────┐            │
│  │  Query   │  │  Schema  │            │
│  └──────────┘  └──────────┘            │
├────────────────────────────────────────┤
│         Connection Layer               │
│  ┌──────────┐  ┌──────────┐            │
│  │  Sync    │  │  R2D2    │            │
│  └──────────┘  └──────────┘            │
└────────────────────────────────────────┘
```

### 2.2 类型系统

```text
┌───────────────┐
│  Schema Macro │
│  table!()     │
└───────┬───────┘
        │
        ▼
┌───────────────┐
│  Table Type   │
│  users::table │
└───────┬───────┘
        │
        ▼
┌───────────────┐
│  Column Types │
│  users::id    │
└───────┬───────┘
        │
        ▼
┌───────────────┐
│  Query Builder│
│  .filter()    │
└───────┬───────┘
        │
        ▼
┌───────────────┐
│  Type Check   │
│  (Compile)    │
└───────────────┘
```

---

## 3. 项目初始化与配置

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "diesel-advanced-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Diesel 核心
diesel = { version = "2.2", features = [
    "postgres",             # PostgreSQL 后端
    "r2d2",                 # 连接池
    "chrono",               # 时间类型
    "uuid",                 # UUID 类型
    "serde_json",           # JSON 类型
    "numeric",              # NUMERIC 类型
] }

# 连接池
r2d2 = "0.8"

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

# 配置
dotenvy = "0.15"

# 异步支持（实验性）
diesel-async = { version = "0.5", features = ["postgres", "tokio"], optional = true }
tokio = { version = "1.40", features = ["full"], optional = true }

[features]
async = ["diesel-async", "tokio"]
```

### 3.2 Diesel CLI 安装

```bash
# 安装 Diesel CLI（PostgreSQL 支持）
cargo install diesel_cli --no-default-features --features postgres

# 或安装支持所有数据库的版本
cargo install diesel_cli
```

### 3.3 初始化项目

```bash
# 设置数据库 URL
echo DATABASE_URL=postgres://postgres:postgres@localhost/diesel_demo > .env

# 初始化 Diesel 项目（创建 migrations 目录和 diesel.toml）
diesel setup

# diesel.toml 会被创建
cat diesel.toml
# [print_schema]
# file = "src/schema.rs"
# custom_type_derives = ["diesel::query_builder::QueryId"]
```

---

## 4. Schema 定义与代码生成

### 4.1 自动生成 Schema

```bash
# 创建数据库表后，生成 schema
diesel print-schema > src/schema.rs

# 或者配置 diesel.toml 自动生成
```

```rust
// src/schema.rs (自动生成)
diesel::table! {
    users (id) {
        id -> Uuid,
        email -> Varchar,
        name -> Varchar,
        password_hash -> Varchar,
        created_at -> Timestamptz,
        updated_at -> Timestamptz,
    }
}

diesel::table! {
    posts (id) {
        id -> Int4,
        title -> Varchar,
        content -> Text,
        user_id -> Uuid,
        published -> Bool,
        created_at -> Timestamptz,
        updated_at -> Timestamptz,
    }
}

diesel::joinable!(posts -> users (user_id));

diesel::allow_tables_to_appear_in_same_query!(
    users,
    posts,
);
```

### 4.2 手动定义 Schema

```rust
// src/schema.rs (手动定义)
use diesel::prelude::*;

diesel::table! {
    users (id) {
        id -> Uuid,
        email -> Varchar,
        name -> Varchar,
        password_hash -> Varchar,
        created_at -> Timestamptz,
        updated_at -> Timestamptz,
    }
}
```

### 4.3 Model 定义

```rust
// src/models.rs
use diesel::prelude::*;
use serde::{Serialize, Deserialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Queryable, Identifiable, Serialize, Deserialize)]
#[diesel(table_name = crate::schema::users)]
pub struct User {
    pub id: Uuid,
    pub email: String,
    pub name: String,
    pub password_hash: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Insertable)]
#[diesel(table_name = crate::schema::users)]
pub struct NewUser {
    pub id: Uuid,
    pub email: String,
    pub name: String,
    pub password_hash: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Queryable, Identifiable, Associations, Serialize, Deserialize)]
#[diesel(belongs_to(User))]
#[diesel(table_name = crate::schema::posts)]
pub struct Post {
    pub id: i32,
    pub title: String,
    pub content: String,
    pub user_id: Uuid,
    pub published: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Insertable)]
#[diesel(table_name = crate::schema::posts)]
pub struct NewPost {
    pub title: String,
    pub content: String,
    pub user_id: Uuid,
    pub published: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}
```

---

## 5. 查询 DSL

### 5.1 基础查询

```rust
use diesel::prelude::*;
use crate::schema::users::dsl::*;
use crate::models::User;

pub fn find_all_users(conn: &mut PgConnection) -> Result<Vec<User>, diesel::result::Error> {
    users.load::<User>(conn)
}

pub fn find_user_by_id(conn: &mut PgConnection, user_id: Uuid) -> Result<User, diesel::result::Error> {
    users.find(user_id).first::<User>(conn)
}

pub fn find_user_by_email(conn: &mut PgConnection, user_email: &str) -> Result<Option<User>, diesel::result::Error> {
    users
        .filter(email.eq(user_email))
        .first::<User>(conn)
        .optional()
}
```

### 5.2 条件查询

```rust
use crate::schema::posts::dsl::*;
use crate::models::Post;

// 多条件查询
pub fn search_posts(
    conn: &mut PgConnection,
    title_pattern: Option<&str>,
    is_published: Option<bool>,
    limit_val: i64,
    offset_val: i64,
) -> Result<Vec<Post>, diesel::result::Error> {
    let mut query = posts.into_boxed();
    
    if let Some(pattern) = title_pattern {
        query = query.filter(title.like(format!("%{}%", pattern)));
    }
    
    if let Some(pub_status) = is_published {
        query = query.filter(published.eq(pub_status));
    }
    
    query
        .order(created_at.desc())
        .limit(limit_val)
        .offset(offset_val)
        .load::<Post>(conn)
}

// 复杂条件查询
pub fn complex_filter(conn: &mut PgConnection) -> Result<Vec<Post>, diesel::result::Error> {
    use diesel::dsl::*;
    
    posts
        .filter(
            published.eq(true).or(
                published.eq(false).and(
                    created_at.gt(now - 7.days())
                )
            )
        )
        .load::<Post>(conn)
}
```

### 5.3 JOIN 查询

```rust
use crate::schema::{users, posts};

// INNER JOIN
pub fn find_posts_with_users(conn: &mut PgConnection) -> Result<Vec<(Post, User)>, diesel::result::Error> {
    posts::table
        .inner_join(users::table)
        .load::<(Post, User)>(conn)
}

// LEFT JOIN
pub fn find_users_with_posts(conn: &mut PgConnection) -> Result<Vec<(User, Option<Post>)>, diesel::result::Error> {
    users::table
        .left_join(posts::table)
        .load::<(User, Option<Post>)>(conn)
}
```

---

## 6. 插入、更新、删除

### 6.1 插入数据

```rust
use diesel::prelude::*;

// 插入单条记录
pub fn create_user(
    conn: &mut PgConnection,
    new_user: &NewUser,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    diesel::insert_into(users)
        .values(new_user)
        .get_result(conn)
}

// 批量插入
pub fn batch_create_users(
    conn: &mut PgConnection,
    new_users: &[NewUser],
) -> Result<Vec<User>, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    diesel::insert_into(users)
        .values(new_users)
        .get_results(conn)
}

// 插入或忽略（ON CONFLICT DO NOTHING）
pub fn insert_or_ignore(
    conn: &mut PgConnection,
    new_user: &NewUser,
) -> Result<usize, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    use diesel::pg::upsert::*;
    
    diesel::insert_into(users)
        .values(new_user)
        .on_conflict_do_nothing()
        .execute(conn)
}

// Upsert（ON CONFLICT DO UPDATE）
pub fn upsert_user(
    conn: &mut PgConnection,
    new_user: &NewUser,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    use diesel::pg::upsert::*;
    
    diesel::insert_into(users)
        .values(new_user)
        .on_conflict(email)
        .do_update()
        .set((
            name.eq(&new_user.name),
            updated_at.eq(chrono::Utc::now()),
        ))
        .get_result(conn)
}
```

### 6.2 更新数据

```rust
// 更新单条记录
pub fn update_user_name(
    conn: &mut PgConnection,
    user_id: Uuid,
    new_name: &str,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    diesel::update(users.find(user_id))
        .set((
            name.eq(new_name),
            updated_at.eq(chrono::Utc::now()),
        ))
        .get_result(conn)
}

// 批量更新
pub fn publish_posts(
    conn: &mut PgConnection,
    post_ids: Vec<i32>,
) -> Result<usize, diesel::result::Error> {
    use crate::schema::posts::dsl::*;
    
    diesel::update(posts.filter(id.eq_any(post_ids)))
        .set(published.eq(true))
        .execute(conn)
}
```

### 6.3 删除数据

```rust
// 删除单条记录
pub fn delete_user(
    conn: &mut PgConnection,
    user_id: Uuid,
) -> Result<usize, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    diesel::delete(users.find(user_id))
        .execute(conn)
}

// 批量删除
pub fn delete_posts(
    conn: &mut PgConnection,
    post_ids: Vec<i32>,
) -> Result<usize, diesel::result::Error> {
    use crate::schema::posts::dsl::*;
    
    diesel::delete(posts.filter(id.eq_any(post_ids)))
        .execute(conn)
}
```

---

## 7. 关联查询

### 7.1 定义关联

```rust
// 已在 Model 中定义
#[derive(Debug, Queryable, Identifiable, Associations)]
#[diesel(belongs_to(User))]
#[diesel(table_name = crate::schema::posts)]
pub struct Post {
    // ...
}
```

### 7.2 一对多查询

```rust
use diesel::prelude::*;
use crate::models::{User, Post};

// 查询用户的所有文章
pub fn find_user_posts(
    conn: &mut PgConnection,
    user_id: Uuid,
) -> Result<Vec<Post>, diesel::result::Error> {
    use crate::schema::{users, posts};
    
    Post::belonging_to(&users::table.find(user_id).first::<User>(conn)?)
        .load::<Post>(conn)
}

// 查询多个用户的文章（分组）
pub fn find_posts_grouped_by_user(
    conn: &mut PgConnection,
    user_ids: Vec<Uuid>,
) -> Result<Vec<(User, Vec<Post>)>, diesel::result::Error> {
    use crate::schema::{users, posts};
    
    let users_list: Vec<User> = users::table
        .filter(users::id.eq_any(user_ids))
        .load::<User>(conn)?;
    
    let posts_list = Post::belonging_to(&users_list)
        .load::<Post>(conn)?
        .grouped_by(&users_list);
    
    Ok(users_list.into_iter().zip(posts_list).collect())
}
```

### 7.3 多对多查询

```rust
// 定义中间表
diesel::table! {
    post_tags (post_id, tag_id) {
        post_id -> Int4,
        tag_id -> Int4,
    }
}

diesel::table! {
    tags (id) {
        id -> Int4,
        name -> Varchar,
    }
}

diesel::joinable!(post_tags -> posts (post_id));
diesel::joinable!(post_tags -> tags (tag_id));

// 查询文章的所有标签
pub fn find_post_tags(
    conn: &mut PgConnection,
    post_id: i32,
) -> Result<Vec<Tag>, diesel::result::Error> {
    use crate::schema::{posts, post_tags, tags};
    
    post_tags::table
        .filter(post_tags::post_id.eq(post_id))
        .inner_join(tags::table)
        .select(tags::all_columns)
        .load::<Tag>(conn)
}
```

---

## 8. 事务管理

### 8.1 基础事务

```rust
use diesel::Connection;

// 自动事务（成功提交，失败回滚）
pub fn create_user_with_profile(
    conn: &mut PgConnection,
    new_user: &NewUser,
    new_profile: &NewProfile,
) -> Result<(User, Profile), diesel::result::Error> {
    conn.transaction::<_, diesel::result::Error, _>(|conn| {
        // 1. 创建用户
        let user = diesel::insert_into(users::table)
            .values(new_user)
            .get_result::<User>(conn)?;
        
        // 2. 创建 Profile
        let profile = diesel::insert_into(profiles::table)
            .values(new_profile)
            .get_result::<Profile>(conn)?;
        
        Ok((user, profile))
    })
}
```

### 8.2 显式事务

```rust
use diesel::connection::AnsiTransactionManager;
use diesel::connection::TransactionManager;

pub fn explicit_transaction(conn: &mut PgConnection) -> Result<(), diesel::result::Error> {
    // 开始事务
    AnsiTransactionManager::begin_transaction(conn)?;
    
    // 执行操作
    match do_some_work(conn) {
        Ok(_) => {
            // 提交
            AnsiTransactionManager::commit_transaction(conn)?;
        }
        Err(e) => {
            // 回滚
            AnsiTransactionManager::rollback_transaction(conn)?;
            return Err(e);
        }
    }
    
    Ok(())
}

fn do_some_work(conn: &mut PgConnection) -> Result<(), diesel::result::Error> {
    // 业务逻辑
    Ok(())
}
```

---

## 9. 迁移管理

### 9.1 创建迁移

```bash
# 创建迁移文件
diesel migration generate create_users_table

# 会生成：
# migrations/2025-10-11-120000_create_users_table/up.sql
# migrations/2025-10-11-120000_create_users_table/down.sql
```

```sql
-- migrations/2025-10-11-120000_create_users_table/up.sql
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";

CREATE TABLE users (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    email VARCHAR(255) UNIQUE NOT NULL,
    name VARCHAR(255) NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);

-- 触发器：自动更新 updated_at
CREATE OR REPLACE FUNCTION update_updated_at()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trigger_users_updated_at
BEFORE UPDATE ON users
FOR EACH ROW
EXECUTE FUNCTION update_updated_at();
```

```sql
-- migrations/2025-10-11-120000_create_users_table/down.sql
DROP TRIGGER IF EXISTS trigger_users_updated_at ON users;
DROP FUNCTION IF EXISTS update_updated_at;
DROP TABLE IF EXISTS users;
```

### 9.2 运行迁移

```bash
# 运行所有待执行的迁移
diesel migration run

# 回滚最后一次迁移
diesel migration revert

# 重做最后一次迁移
diesel migration redo

# 查看迁移状态
diesel migration list

# 从头重建数据库
diesel database reset
```

```rust
// 在代码中运行迁移
embed_migrations!();

pub fn run_migrations(conn: &mut PgConnection) -> Result<(), Box<dyn std::error::Error>> {
    embedded_migrations::run(conn)?;
    tracing::info!("Migrations completed");
    Ok(())
}
```

---

## 10. 高级查询模式

### 10.1 原始 SQL

```rust
use diesel::sql_query;
use diesel::sql_types::{Text, Uuid as SqlUuid};

#[derive(QueryableByName, Debug)]
struct CustomResult {
    #[diesel(sql_type = SqlUuid)]
    pub user_id: Uuid,
    
    #[diesel(sql_type = diesel::sql_types::BigInt)]
    pub post_count: i64,
}

pub fn execute_raw_sql(conn: &mut PgConnection) -> Result<Vec<CustomResult>, diesel::result::Error> {
    sql_query(
        r#"
        SELECT u.id as user_id, COUNT(p.id) as post_count
        FROM users u
        LEFT JOIN posts p ON u.id = p.user_id
        GROUP BY u.id
        HAVING COUNT(p.id) > $1
        "#
    )
    .bind::<diesel::sql_types::BigInt, _>(5)
    .load::<CustomResult>(conn)
}
```

### 10.2 子查询

```rust
use diesel::dsl::*;

pub fn subquery_example(conn: &mut PgConnection) -> Result<Vec<User>, diesel::result::Error> {
    use crate::schema::{users, posts};
    
    // 查询有超过 10 篇文章的用户
    let subquery = posts::table
        .group_by(posts::user_id)
        .having(count(posts::id).gt(10))
        .select(posts::user_id);
    
    users::table
        .filter(users::id.eq_any(subquery))
        .load::<User>(conn)
}
```

### 10.3 聚合查询

```rust
use diesel::dsl::*;

#[derive(QueryableByName, Debug)]
struct Stats {
    #[diesel(sql_type = diesel::sql_types::BigInt)]
    pub total_posts: i64,
    
    #[diesel(sql_type = diesel::sql_types::BigInt)]
    pub published_posts: i64,
}

pub fn post_stats(conn: &mut PgConnection) -> Result<Stats, diesel::result::Error> {
    use crate::schema::posts::dsl::*;
    
    sql_query(
        r#"
        SELECT 
            COUNT(*) as total_posts,
            COUNT(*) FILTER (WHERE published = true) as published_posts
        FROM posts
        "#
    )
    .get_result::<Stats>(conn)
}
```

---

## 11. 连接池集成

### 11.1 R2D2 连接池

```rust
use diesel::r2d2::{self, ConnectionManager, Pool, PooledConnection};
use diesel::PgConnection;

pub type DbPool = Pool<ConnectionManager<PgConnection>>;
pub type DbConnection = PooledConnection<ConnectionManager<PgConnection>>;

pub fn establish_pool(database_url: &str) -> DbPool {
    let manager = ConnectionManager::<PgConnection>::new(database_url);
    
    Pool::builder()
        .max_size(100)
        .min_idle(Some(10))
        .connection_timeout(std::time::Duration::from_secs(10))
        .idle_timeout(Some(std::time::Duration::from_secs(600)))
        .max_lifetime(Some(std::time::Duration::from_secs(1800)))
        .build(manager)
        .expect("Failed to create pool")
}
```

### 11.2 连接池管理

```rust
pub fn get_connection(pool: &DbPool) -> Result<DbConnection, r2d2::Error> {
    pool.get()
}

pub fn pool_status(pool: &DbPool) {
    let state = pool.state();
    tracing::info!(
        "Pool status: connections={}, idle={}",
        state.connections,
        state.idle_connections
    );
}
```

---

## 12. 异步支持（实验性）

### 12.1 diesel-async

```toml
[dependencies]
diesel-async = { version = "0.5", features = ["postgres", "tokio"] }
tokio = { version = "1.40", features = ["full"] }
```

### 12.2 异步查询示例

```rust
use diesel_async::{AsyncPgConnection, RunQueryDsl};

pub async fn async_find_user(
    conn: &mut AsyncPgConnection,
    user_id: Uuid,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    users.find(user_id).first::<User>(conn).await
}

pub async fn async_create_user(
    conn: &mut AsyncPgConnection,
    new_user: &NewUser,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    diesel::insert_into(users)
        .values(new_user)
        .get_result::<User>(conn)
        .await
}
```

---

## 13. OTLP 分布式追踪集成

### 13.1 OTLP 初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "diesel-advanced-demo"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::fmt::layer().json())
        .init();
    
    Ok(())
}
```

### 13.2 追踪查询

```rust
use tracing::instrument;

#[instrument(skip(conn), fields(db.system = "postgresql", db.operation = "SELECT"))]
pub fn traced_find_user(
    conn: &mut PgConnection,
    user_id: Uuid,
) -> Result<User, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    users.find(user_id).first::<User>(conn)
}
```

---

## 14. 测试策略

### 14.1 测试数据库设置

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use diesel::Connection;

    fn setup_test_db() -> PgConnection {
        let database_url = std::env::var("TEST_DATABASE_URL")
            .unwrap_or_else(|_| "postgres://postgres:postgres@localhost/diesel_test".to_string());
        
        let mut conn = PgConnection::establish(&database_url)
            .expect("Failed to connect to test database");
        
        // 运行迁移
        embedded_migrations::run(&mut conn).unwrap();
        
        conn
    }

    #[test]
    fn test_create_user() {
        let mut conn = setup_test_db();
        
        let new_user = NewUser {
            id: Uuid::new_v4(),
            email: "test@example.com".to_string(),
            name: "Test User".to_string(),
            password_hash: "hash".to_string(),
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        let user = create_user(&mut conn, &new_user).unwrap();
        
        assert_eq!(user.email, "test@example.com");
    }
}
```

### 14.2 集成测试

```rust
// tests/integration_test.rs
use diesel::prelude::*;

#[test]
fn test_user_posts_relationship() {
    let mut conn = setup_test_db();
    
    // 创建用户
    let user = create_test_user(&mut conn);
    
    // 创建文章
    let post = create_test_post(&mut conn, user.id);
    
    // 查询用户的文章
    let posts = find_user_posts(&mut conn, user.id).unwrap();
    
    assert_eq!(posts.len(), 1);
    assert_eq!(posts[0].id, post.id);
}
```

---

## 15. 生产环境最佳实践

### 15.1 性能优化

```rust
// 使用 .load() 而非 .get_results() 对于大结果集
pub fn load_large_result_set(conn: &mut PgConnection) -> Result<Vec<User>, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    users.load::<User>(conn)
}

// 使用分页避免加载过多数据
pub fn paginated_query(
    conn: &mut PgConnection,
    page: i64,
    per_page: i64,
) -> Result<Vec<User>, diesel::result::Error> {
    use crate::schema::users::dsl::*;
    
    users
        .limit(per_page)
        .offset((page - 1) * per_page)
        .load::<User>(conn)
}
```

### 15.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] diesel::result::Error),
    
    #[error("Pool error: {0}")]
    Pool(#[from] r2d2::Error),
    
    #[error("User not found: {0}")]
    UserNotFound(Uuid),
}
```

---

## 16. 国际标准对标

### 16.1 对标清单

| 标准分类 | 标准名称 | Diesel 实现 |
|----------|----------|-----------|
| **SQL 标准** | SQL:2016 | ✅ 完整支持 |
| **事务隔离** | ANSI SQL Isolation Levels | ✅ 完整支持 |
| **连接池** | HikariCP 模式 | ✅ R2D2 实现 |
| **参数化查询** | OWASP SQL Injection Prevention | ✅ 完全防护 |
| **迁移工具** | Flyway/Liquibase | ✅ CLI 工具 |

---

## 17. 总结与最佳实践

### 17.1 核心优势

1. **编译期类型安全**：SQL 错误在编译时捕获
2. **零运行时开销**：无反射、无动态分派
3. **强类型 DSL**：类型系统保证查询正确性
4. **性能极致**：接近手写 SQL 的性能

### 17.2 最佳实践

**✅ 推荐做法**:

- 使用连接池管理连接
- 使用迁移工具管理 schema
- 使用 `.optional()` 处理可能不存在的记录
- 使用 `.into_boxed()` 构建动态查询
- 使用批量操作提升性能
- 实现 Repository 模式封装数据访问

**❌ 避免做法**:

- 不要在循环中执行查询（N+1 问题）
- 不要忽略连接池配置
- 不要在事务中执行长时间操作
- 不要忽略索引优化

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**Diesel 版本**: 2.2  
**OpenTelemetry 版本**: 0.25  

---

**国际标准对齐**:

- ✅ SQL:2016 Standard
- ✅ OWASP SQL Injection Prevention
- ✅ OpenTelemetry Database Semantic Conventions
- ✅ Query Builder Pattern

**参考文献**:

- Diesel Official Documentation: <https://diesel.rs/>
- SQL:2016 Standard: ISO/IEC 9075:2016
- OpenTelemetry Database Semantic Conventions
