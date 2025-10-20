# SurrealDB 多模型数据库 - Rust + OTLP 完整集成指南

## 📋 目录

- [SurrealDB 多模型数据库 - Rust + OTLP 完整集成指南](#surrealdb-多模型数据库---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 SurrealDB?](#什么是-surrealdb)
    - [为什么选择 SurrealDB + Rust?](#为什么选择-surrealdb--rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. 多模型架构](#1-多模型架构)
    - [2. SurrealQL 语言](#2-surrealql-语言)
  - [环境准备](#环境准备)
    - [1. 安装 SurrealDB](#1-安装-surrealdb)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. 连接初始化](#1-连接初始化)
    - [2. CRUD 操作](#2-crud-操作)
    - [3. 事务管理](#3-事务管理)
  - [OTLP 追踪集成](#otlp-追踪集成)
    - [1. 查询追踪](#1-查询追踪)
    - [2. 事务追踪](#2-事务追踪)
    - [3. Live Query 追踪](#3-live-query-追踪)
  - [多模型特性](#多模型特性)
    - [1. 文档模型](#1-文档模型)
    - [2. 图模型](#2-图模型)
    - [3. 时序数据](#3-时序数据)
  - [高级特性](#高级特性)
    - [1. Live Query (实时查询)](#1-live-query-实时查询)
    - [2. 权限系统](#2-权限系统)
    - [3. 函数和存储过程](#3-函数和存储过程)
  - [性能优化](#性能优化)
    - [1. 索引策略](#1-索引策略)
    - [2. 批量操作](#2-批量操作)
    - [3. 连接池](#3-连接池)
  - [完整示例](#完整示例)
    - [1. 社交网络应用](#1-社交网络应用)
    - [2. IoT 数据平台](#2-iot-数据平台)
  - [最佳实践](#最佳实践)
    - [1. Schema 设计](#1-schema-设计)
    - [2. 查询优化](#2-查询优化)
    - [3. 监控告警](#3-监控告警)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [SurrealDB vs 其他数据库](#surrealdb-vs-其他数据库)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 SurrealDB?

**SurrealDB** 是用 Rust 编写的新一代多模型数据库:

```text
┌─────────────────────────────────────┐
│         SurrealDB Engine            │
│  ┌──────────────────────────────┐  │
│  │  文档 │ 图 │ 键值 │ 时序    │  │
│  └──────────────────────────────┘  │
│  ┌──────────────────────────────┐  │
│  │  SurrealQL (SQL-like)        │  │
│  │  实时查询 (Live Query)       │  │
│  │  事务 ACID                   │  │
│  └──────────────────────────────┘  │
└─────────────────────────────────────┘
```

**核心特性**:

- **多模型**: 文档、图、键值、时序
- **SurrealQL**: SQL-like 查询语言
- **实时查询**: Live Query 推送更新
- **ACID 事务**: 完整事务支持
- **原生 Rust**: 高性能、内存安全

### 为什么选择 SurrealDB + Rust?

| 优势 | 说明 |
|------|------|
| **同语言** | SurrealDB 和应用都用 Rust,零序列化开销 |
| **多模型** | 一个数据库满足多种需求 |
| **实时** | Live Query 实时推送 |
| **简单** | 无需 ORM,SurrealQL 直观 |
| **高性能** | Rust 原生,极致性能 |

### OTLP 集成价值

```text
应用 → SurrealDB SDK → OTLP → Observability
  ↓         ↓              ↓         ↓
业务逻辑   数据库操作    分布式追踪  性能分析
```

**可追踪操作**:

- Query 执行时间
- Transaction 性能
- Live Query 订阅
- 图遍历深度
- 索引使用情况

---

## 核心概念

### 1. 多模型架构

```text
┌─────────────────────────────────────────┐
│            SurrealDB                    │
│  ┌────────────┐  ┌────────────┐        │
│  │  Document  │  │   Graph    │        │
│  │   Model    │  │   Model    │        │
│  └────────────┘  └────────────┘        │
│  ┌────────────┐  ┌────────────┐        │
│  │ Key-Value  │  │ Time-Series│        │
│  │   Model    │  │   Model    │        │
│  └────────────┘  └────────────┘        │
└─────────────────────────────────────────┘
```

**统一访问层**:

```sql
-- 文档查询
SELECT * FROM users WHERE age > 18;

-- 图遍历
SELECT ->friend->user FROM users:john;

-- 时序数据
SELECT * FROM metrics WHERE time > time::now() - 1h;
```

### 2. SurrealQL 语言

```sql
-- 创建
CREATE users:john SET name = "John", age = 30;

-- 查询
SELECT name, age FROM users WHERE age > 25;

-- 更新
UPDATE users:john SET age = 31;

-- 删除
DELETE users:john;

-- 关系 (图模型)
RELATE users:john->friend->users:jane;

-- Live Query
LIVE SELECT * FROM users;
```

---

## 环境准备

### 1. 安装 SurrealDB

```bash
# macOS / Linux
curl -sSf https://install.surrealdb.com | sh

# Docker
docker run --rm -p 8000:8000 surrealdb/surrealdb:latest \
  start --log trace --user root --pass root

# 启动本地实例
surreal start --log trace --user root --pass root

# 连接测试
surreal sql --conn http://localhost:8000 --user root --pass root --ns test --db test
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "surrealdb-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# SurrealDB SDK
surrealdb = "1.4"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }

# OTLP
opentelemetry = "0.30"
opentelemetry-otlp = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 其他
uuid = { version = "1.8", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. 连接初始化

```rust
// src/surreal.rs
use surrealdb::{
    Surreal,
    engine::remote::ws::{Client, Ws},
    opt::auth::Root,
};
use tracing::{info, instrument};
use anyhow::Result;

pub struct SurrealClientWithTracing {
    db: Surreal<Client>,
}

impl SurrealClientWithTracing {
    #[instrument(skip(url, username, password))]
    pub async fn new(
        url: &str,
        username: &str,
        password: &str,
        namespace: &str,
        database: &str,
    ) -> Result<Self> {
        info!("Connecting to SurrealDB at {}", url);
        
        // 连接到 SurrealDB
        let db = Surreal::new::<Ws>(url).await?;
        
        // 认证
        db.signin(Root {
            username,
            password,
        }).await?;
        
        // 选择命名空间和数据库
        db.use_ns(namespace).use_db(database).await?;
        
        info!("SurrealDB connection established");
        
        Ok(Self { db })
    }
    
    pub fn client(&self) -> &Surreal<Client> {
        &self.db
    }
}
```

### 2. CRUD 操作

```rust
// src/crud.rs
use serde::{Deserialize, Serialize};
use surrealdb::sql::Thing;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Option<Thing>,
    pub name: String,
    pub email: String,
    pub age: u32,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl SurrealClientWithTracing {
    /// 创建用户
    #[instrument(skip(self, user))]
    pub async fn create_user(&self, user: User) -> Result<User> {
        info!("Creating user: {}", user.name);
        
        let created: Vec<User> = self.db
            .create("users")
            .content(user)
            .await?;
        
        Ok(created.into_iter().next().unwrap())
    }
    
    /// 查询用户
    #[instrument(skip(self))]
    pub async fn get_user(&self, id: &str) -> Result<Option<User>> {
        let user: Option<User> = self.db
            .select(("users", id))
            .await?;
        
        Ok(user)
    }
    
    /// 查询所有用户
    #[instrument(skip(self))]
    pub async fn list_users(&self, limit: usize) -> Result<Vec<User>> {
        let users: Vec<User> = self.db
            .query("SELECT * FROM users LIMIT $limit")
            .bind(("limit", limit))
            .await?
            .take(0)?;
        
        info!("Found {} users", users.len());
        Ok(users)
    }
    
    /// 更新用户
    #[instrument(skip(self))]
    pub async fn update_user(&self, id: &str, age: u32) -> Result<User> {
        let updated: Option<User> = self.db
            .update(("users", id))
            .merge(serde_json::json!({ "age": age }))
            .await?;
        
        Ok(updated.unwrap())
    }
    
    /// 删除用户
    #[instrument(skip(self))]
    pub async fn delete_user(&self, id: &str) -> Result<()> {
        let _: Option<User> = self.db
            .delete(("users", id))
            .await?;
        
        info!("User {} deleted", id);
        Ok(())
    }
}
```

### 3. 事务管理

```rust
use surrealdb::opt::Transaction;

impl SurrealClientWithTracing {
    #[instrument(skip(self))]
    pub async fn transfer_money(
        &self,
        from_user: &str,
        to_user: &str,
        amount: f64,
    ) -> Result<()> {
        info!("Starting money transfer: {} -> {} ({})", from_user, to_user, amount);
        
        // 开始事务
        let tx = self.db.begin().await?;
        
        // 扣款
        tx.query(
            "UPDATE users:$from SET balance -= $amount WHERE balance >= $amount"
        )
        .bind(("from", from_user))
        .bind(("amount", amount))
        .await?;
        
        // 入账
        tx.query(
            "UPDATE users:$to SET balance += $amount"
        )
        .bind(("to", to_user))
        .bind(("amount", amount))
        .await?;
        
        // 提交事务
        tx.commit().await?;
        
        info!("Money transfer completed");
        Ok(())
    }
}
```

---

## OTLP 追踪集成

### 1. 查询追踪

```rust
use opentelemetry::{
    global,
    trace::{Span, Tracer},
    KeyValue,
};

impl SurrealClientWithTracing {
    #[instrument(skip(self))]
    pub async fn query_with_tracing(&self, query: &str) -> Result<Vec<User>> {
        let tracer = global::tracer("surrealdb-client");
        
        let mut span = tracer
            .span_builder("surrealdb.query")
            .with_attributes(vec![
                KeyValue::new("db.system", "surrealdb"),
                KeyValue::new("db.operation", "query"),
                KeyValue::new("db.statement", query.to_string()),
            ])
            .start(&tracer);
        
        let start = std::time::Instant::now();
        
        let result: Vec<User> = self.db
            .query(query)
            .await?
            .take(0)?;
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("surrealdb.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("surrealdb.results_count", result.len() as i64));
        
        span.end();
        Ok(result)
    }
}
```

### 2. 事务追踪

```rust
#[instrument(skip(self))]
pub async fn transaction_with_tracing(&self) -> Result<()> {
    let tracer = global::tracer("surrealdb-client");
    
    let mut span = tracer
        .span_builder("surrealdb.transaction")
        .with_attributes(vec![
            KeyValue::new("db.system", "surrealdb"),
            KeyValue::new("db.operation", "transaction"),
        ])
        .start(&tracer);
    
    span.add_event("transaction_begin", vec![]);
    
    let tx = self.db.begin().await?;
    
    // 执行事务操作...
    
    span.add_event("transaction_commit", vec![]);
    tx.commit().await?;
    
    span.end();
    Ok(())
}
```

### 3. Live Query 追踪

```rust
use futures::StreamExt;
use surrealdb::Notification;

#[instrument(skip(self))]
pub async fn live_query_with_tracing(&self, table: &str) -> Result<()> {
    let tracer = global::tracer("surrealdb-client");
    
    let mut span = tracer
        .span_builder("surrealdb.live_query")
        .with_attributes(vec![
            KeyValue::new("surrealdb.table", table.to_string()),
        ])
        .start(&tracer);
    
    // 创建 Live Query
    let mut stream = self.db
        .select(table)
        .live()
        .await?;
    
    span.add_event("live_query_subscribed", vec![]);
    
    let mut event_count = 0;
    
    while let Some(notification) = stream.next().await {
        match notification {
            Ok(Notification::Create(data)) => {
                event_count += 1;
                tracing::info!("Live query event: CREATE");
            }
            Ok(Notification::Update(data)) => {
                event_count += 1;
                tracing::info!("Live query event: UPDATE");
            }
            Ok(Notification::Delete(data)) => {
                event_count += 1;
                tracing::info!("Live query event: DELETE");
            }
            Err(e) => {
                span.record_error(&e);
                break;
            }
        }
    }
    
    span.set_attribute(KeyValue::new("surrealdb.events_received", event_count));
    span.end();
    
    Ok(())
}
```

---

## 多模型特性

### 1. 文档模型

```rust
#[derive(Serialize, Deserialize)]
pub struct Product {
    pub id: Option<Thing>,
    pub name: String,
    pub price: f64,
    pub category: String,
    pub tags: Vec<String>,
    pub metadata: serde_json::Value,
}

#[instrument(skip(self))]
pub async fn create_product(&self, product: Product) -> Result<Product> {
    let created: Vec<Product> = self.db
        .create("products")
        .content(product)
        .await?;
    
    Ok(created.into_iter().next().unwrap())
}

#[instrument(skip(self))]
pub async fn search_products(&self, category: &str) -> Result<Vec<Product>> {
    let products: Vec<Product> = self.db
        .query("SELECT * FROM products WHERE category = $category")
        .bind(("category", category))
        .await?
        .take(0)?;
    
    Ok(products)
}
```

### 2. 图模型

```rust
// 社交网络图模型
#[derive(Serialize, Deserialize)]
pub struct Follow {
    pub id: Option<Thing>,
    pub r#in: Thing,   // from user
    pub out: Thing,  // to user
    pub since: chrono::DateTime<chrono::Utc>,
}

impl SurrealClientWithTracing {
    /// 创建关注关系
    #[instrument(skip(self))]
    pub async fn follow_user(&self, from_id: &str, to_id: &str) -> Result<()> {
        self.db
            .query("RELATE users:$from->follow->users:$to SET since = time::now()")
            .bind(("from", from_id))
            .bind(("to", to_id))
            .await?;
        
        Ok(())
    }
    
    /// 查询关注者
    #[instrument(skip(self))]
    pub async fn get_followers(&self, user_id: &str) -> Result<Vec<User>> {
        let followers: Vec<User> = self.db
            .query("SELECT <-follow<-user AS followers FROM users:$id")
            .bind(("id", user_id))
            .await?
            .take(0)?;
        
        Ok(followers)
    }
    
    /// 查询关注的人
    #[instrument(skip(self))]
    pub async fn get_following(&self, user_id: &str) -> Result<Vec<User>> {
        let following: Vec<User> = self.db
            .query("SELECT ->follow->user AS following FROM users:$id")
            .bind(("id", user_id))
            .await?
            .take(0)?;
        
        Ok(following)
    }
    
    /// 查询共同好友
    #[instrument(skip(self))]
    pub async fn get_mutual_friends(&self, user_id: &str, other_id: &str) -> Result<Vec<User>> {
        let mutual: Vec<User> = self.db
            .query(r#"
                LET $user1_following = (SELECT ->follow->user FROM users:$user1);
                LET $user2_following = (SELECT ->follow->user FROM users:$user2);
                RETURN array::intersect($user1_following, $user2_following);
            "#)
            .bind(("user1", user_id))
            .bind(("user2", other_id))
            .await?
            .take(0)?;
        
        Ok(mutual)
    }
}
```

### 3. 时序数据

```rust
#[derive(Serialize, Deserialize)]
pub struct Metric {
    pub id: Option<Thing>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub metric_name: String,
    pub value: f64,
    pub tags: std::collections::HashMap<String, String>,
}

#[instrument(skip(self))]
pub async fn insert_metrics(&self, metrics: Vec<Metric>) -> Result<()> {
    for metric in metrics {
        self.db
            .create("metrics")
            .content(metric)
            .await?;
    }
    
    Ok(())
}

#[instrument(skip(self))]
pub async fn query_metrics_range(
    &self,
    metric_name: &str,
    start: chrono::DateTime<chrono::Utc>,
    end: chrono::DateTime<chrono::Utc>,
) -> Result<Vec<Metric>> {
    let metrics: Vec<Metric> = self.db
        .query(r#"
            SELECT * FROM metrics 
            WHERE metric_name = $name 
            AND timestamp >= $start 
            AND timestamp <= $end
            ORDER BY timestamp ASC
        "#)
        .bind(("name", metric_name))
        .bind(("start", start))
        .bind(("end", end))
        .await?
        .take(0)?;
    
    Ok(metrics)
}

#[instrument(skip(self))]
pub async fn aggregate_metrics(&self, metric_name: &str, window: &str) -> Result<Vec<AggregatedMetric>> {
    let aggregated: Vec<AggregatedMetric> = self.db
        .query(r#"
            SELECT 
                time::floor(timestamp, $window) AS bucket,
                math::mean(value) AS avg_value,
                math::max(value) AS max_value,
                math::min(value) AS min_value
            FROM metrics
            WHERE metric_name = $name
            GROUP BY bucket
            ORDER BY bucket ASC
        "#)
        .bind(("name", metric_name))
        .bind(("window", window))
        .await?
        .take(0)?;
    
    Ok(aggregated)
}
```

---

## 高级特性

### 1. Live Query (实时查询)

```rust
use tokio::sync::mpsc;

pub struct LiveQueryManager {
    db: Surreal<Client>,
}

impl LiveQueryManager {
    #[instrument(skip(self))]
    pub async fn subscribe_to_users(&self) -> Result<mpsc::Receiver<User>> {
        let (tx, rx) = mpsc::channel(100);
        
        let mut stream = self.db
            .select("users")
            .live()
            .await?;
        
        tokio::spawn(async move {
            while let Some(notification) = stream.next().await {
                match notification {
                    Ok(Notification::Create(user)) => {
                        let _ = tx.send(user).await;
                    }
                    Ok(Notification::Update(user)) => {
                        let _ = tx.send(user).await;
                    }
                    _ => {}
                }
            }
        });
        
        Ok(rx)
    }
}
```

### 2. 权限系统

```sql
-- 定义 Schema
DEFINE TABLE users SCHEMAFULL
    PERMISSIONS 
        FOR select WHERE $auth.id = id OR $auth.role = 'admin'
        FOR create, update WHERE $auth.role = 'admin'
        FOR delete WHERE $auth.role = 'admin';

DEFINE FIELD name ON TABLE users TYPE string;
DEFINE FIELD email ON TABLE users TYPE string ASSERT string::is::email($value);
DEFINE FIELD age ON TABLE users TYPE int ASSERT $value >= 0 AND $value <= 150;

-- 索引
DEFINE INDEX idx_email ON TABLE users COLUMNS email UNIQUE;
```

### 3. 函数和存储过程

```rust
#[instrument(skip(self))]
pub async fn execute_stored_function(&self) -> Result<Vec<User>> {
    // 定义函数
    self.db
        .query(r#"
            DEFINE FUNCTION fn::get_active_users() {
                RETURN SELECT * FROM users WHERE last_login > time::now() - 1w;
            };
        "#)
        .await?;
    
    // 调用函数
    let active_users: Vec<User> = self.db
        .query("RETURN fn::get_active_users()")
        .await?
        .take(0)?;
    
    Ok(active_users)
}
```

---

## 性能优化

### 1. 索引策略

```sql
-- 创建索引
DEFINE INDEX idx_user_email ON TABLE users COLUMNS email UNIQUE;
DEFINE INDEX idx_user_age ON TABLE users COLUMNS age;
DEFINE INDEX idx_product_category ON TABLE products COLUMNS category;

-- 全文索引
DEFINE ANALYZER search TOKENIZERS blank,class FILTERS snowball(english);
DEFINE INDEX idx_product_search ON TABLE products COLUMNS name SEARCH ANALYZER search BM25;
```

```rust
#[instrument(skip(self))]
pub async fn full_text_search(&self, query: &str) -> Result<Vec<Product>> {
    let products: Vec<Product> = self.db
        .query("SELECT * FROM products WHERE name @@ $query")
        .bind(("query", query))
        .await?
        .take(0)?;
    
    Ok(products)
}
```

### 2. 批量操作

```rust
#[instrument(skip(self, users))]
pub async fn batch_create_users(&self, users: Vec<User>) -> Result<()> {
    const BATCH_SIZE: usize = 100;
    
    for chunk in users.chunks(BATCH_SIZE) {
        let _: Vec<User> = self.db
            .create("users")
            .content(chunk)
            .await?;
    }
    
    Ok(())
}
```

### 3. 连接池

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

pub struct SurrealPool {
    connections: Vec<Arc<SurrealClientWithTracing>>,
    semaphore: Arc<Semaphore>,
}

impl SurrealPool {
    pub async fn new(size: usize, url: &str) -> Result<Self> {
        let mut connections = Vec::with_capacity(size);
        
        for _ in 0..size {
            let client = SurrealClientWithTracing::new(
                url,
                "root",
                "root",
                "test",
                "test",
            ).await?;
            connections.push(Arc::new(client));
        }
        
        Ok(Self {
            connections,
            semaphore: Arc::new(Semaphore::new(size)),
        })
    }
    
    pub async fn get(&self) -> Result<Arc<SurrealClientWithTracing>> {
        let _permit = self.semaphore.acquire().await?;
        // 简化实现,实际需要更复杂的连接管理
        Ok(self.connections[0].clone())
    }
}
```

---

## 完整示例

### 1. 社交网络应用

(见上文图模型部分)

### 2. IoT 数据平台

```rust
// src/iot_platform.rs
#[derive(Serialize, Deserialize)]
pub struct Device {
    pub id: Option<Thing>,
    pub device_id: String,
    pub device_type: String,
    pub location: Location,
}

#[derive(Serialize, Deserialize)]
pub struct SensorReading {
    pub id: Option<Thing>,
    pub device_id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub temperature: f64,
    pub humidity: f64,
    pub battery: f64,
}

pub struct IoTPlatform {
    db: SurrealClientWithTracing,
}

impl IoTPlatform {
    #[instrument(skip(self, reading))]
    pub async fn ingest_sensor_data(&self, reading: SensorReading) -> Result<()> {
        self.db.client()
            .create("sensor_readings")
            .content(reading)
            .await?;
        
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn get_device_latest_readings(&self, device_id: &str) -> Result<Vec<SensorReading>> {
        let readings: Vec<SensorReading> = self.db.client()
            .query(r#"
                SELECT * FROM sensor_readings
                WHERE device_id = $device_id
                ORDER BY timestamp DESC
                LIMIT 10
            "#)
            .bind(("device_id", device_id))
            .await?
            .take(0)?;
        
        Ok(readings)
    }
}
```

---

## 最佳实践

### 1. Schema 设计

```rust
// ✅ 好的实践: 使用 SCHEMAFULL
pub async fn create_schema(&self) -> Result<()> {
    self.db.query(r#"
        DEFINE TABLE users SCHEMAFULL
            PERMISSIONS FOR select, create, update, delete WHERE $auth = $this;
        
        DEFINE FIELD name ON TABLE users TYPE string;
        DEFINE FIELD email ON TABLE users TYPE string ASSERT string::is::email($value);
        DEFINE FIELD created_at ON TABLE users TYPE datetime VALUE time::now();
        
        DEFINE INDEX idx_email ON TABLE users COLUMNS email UNIQUE;
    "#).await?;
    
    Ok(())
}
```

### 2. 查询优化

```rust
// ✅ 使用索引
"SELECT * FROM users WHERE email = $email"  // 有索引

// ❌ 避免全表扫描
"SELECT * FROM users WHERE name CONTAINS 'john'"  // 慢
```

### 3. 监控告警

```rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct SurrealMetrics {
    query_duration: Histogram<f64>,
    query_count: Counter<u64>,
}

impl SurrealMetrics {
    pub fn record_query(&self, duration_ms: f64, operation: &str) {
        let attributes = vec![
            KeyValue::new("operation", operation.to_string()),
        ];
        
        self.query_duration.record(duration_ms, &attributes);
        self.query_count.add(1, &attributes);
    }
}
```

---

## 总结

### 核心要点

1. **多模型**: 文档、图、键值、时序统一
2. **SurrealQL**: SQL-like 直观查询
3. **实时查询**: Live Query 推送更新
4. **Rust 原生**: 高性能、内存安全
5. **ACID 事务**: 完整事务支持

### SurrealDB vs 其他数据库

| 特性 | SurrealDB | MongoDB | Neo4j | PostgreSQL |
|------|-----------|---------|-------|------------|
| **多模型** | ✅ 原生 | ⚠️ 文档 | ⚠️ 图 | ⚠️ 关系 |
| **实时查询** | ✅ | ⚠️ Change Streams | ❌ | ❌ |
| **Rust 原生** | ✅ | ❌ | ❌ | ❌ |
| **ACID 事务** | ✅ | ✅ | ✅ | ✅ |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |

### 下一步

- **SurrealQL 高级**: 学习高级查询
- **集群部署**: 生产环境部署
- **性能调优**: 索引和查询优化

---

## 参考资料

- [SurrealDB 官方文档](https://surrealdb.com/docs)
- [SurrealDB Rust SDK](https://github.com/surrealdb/surrealdb.rs)
- [SurrealQL 语法](https://surrealdb.com/docs/surrealql)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**SurrealDB**: 1.4+  
**OpenTelemetry**: 0.30+
