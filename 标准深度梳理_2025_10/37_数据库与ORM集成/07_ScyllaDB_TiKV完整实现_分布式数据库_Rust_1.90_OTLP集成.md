# ScyllaDB & TiKV 分布式数据库 - 完整实现指南

## 目录

- [ScyllaDB \& TiKV 分布式数据库 - 完整实现指南](#scylladb--tikv-分布式数据库---完整实现指南)
  - [目录](#目录)
  - [1. 分布式数据库概述](#1-分布式数据库概述)
    - [1.1 分布式数据库特性对比](#11-分布式数据库特性对比)
    - [1.2 典型应用场景](#12-典型应用场景)
  - [2. ScyllaDB 完整实现](#2-scylladb-完整实现)
    - [2.1 ScyllaDB 概述](#21-scylladb-概述)
    - [2.2 项目设置](#22-项目设置)
      - [Cargo.toml](#cargotoml)
    - [2.3 基础操作](#23-基础操作)
      - [连接与初始化](#连接与初始化)
      - [数据模型](#数据模型)
      - [CRUD 操作](#crud-操作)
    - [2.4 高级功能](#24-高级功能)
      - [Prepared Statements](#prepared-statements)
      - [Batch Operations](#batch-operations)
      - [LWT (Lightweight Transactions)](#lwt-lightweight-transactions)
    - [2.5 OTLP 集成](#25-otlp-集成)
  - [3. TiKV 完整实现](#3-tikv-完整实现)
    - [3.1 TiKV 概述](#31-tikv-概述)
    - [3.2 项目设置](#32-项目设置)
      - [Cargo.toml1](#cargotoml1)
    - [3.3 基础操作](#33-基础操作)
      - [连接与初始化1](#连接与初始化1)
      - [数据模型1](#数据模型1)
      - [CRUD 操作1](#crud-操作1)
    - [3.4 高级功能](#34-高级功能)
      - [分布式事务](#分布式事务)
      - [Scan 范围查询](#scan-范围查询)
      - [悲观事务](#悲观事务)
    - [3.5 OTLP 集成](#35-otlp-集成)
  - [4. 性能对比](#4-性能对比)
    - [4.1 读写延迟](#41-读写延迟)
    - [4.2 吞吐量](#42-吞吐量)
  - [5. 测试策略](#5-测试策略)
    - [5.1 Testcontainers 集成测试](#51-testcontainers-集成测试)
  - [6. 生产实践](#6-生产实践)
    - [6.1 Docker Compose 部署](#61-docker-compose-部署)
  - [7. 国际标准对齐](#7-国际标准对齐)
    - [7.1 ScyllaDB](#71-scylladb)
    - [7.2 TiKV](#72-tikv)
    - [7.3 OpenTelemetry 语义约定](#73-opentelemetry-语义约定)
  - [总结](#总结)
    - [ScyllaDB 优势](#scylladb-优势)
    - [TiKV 优势](#tikv-优势)
    - [选择建议](#选择建议)

---

## 1. 分布式数据库概述

### 1.1 分布式数据库特性对比

| 特性 | ScyllaDB | TiKV | Cassandra | CockroachDB |
|------|----------|------|-----------|-------------|
| **数据模型** | Wide Column | Key-Value | Wide Column | Relational (SQL) |
| **一致性** | Eventual/Strong | Strong (Raft) | Eventual/Strong | Strong (Raft) |
| **编程语言** | C++ | Rust | Java | Go |
| **协议** | CQL (Cassandra) | gRPC | CQL | PostgreSQL |
| **分片策略** | Consistent Hashing | Range-based | Consistent Hashing | Range-based |
| **典型延迟** | < 1ms (P99) | 1-5ms (P99) | 1-10ms (P99) | 5-20ms (P99) |
| **吞吐量** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **适用场景** | 时序数据、IoT | 分布式事务 | 宽表存储 | 分布式 SQL |

### 1.2 典型应用场景

**ScyllaDB**:

- ✅ 时序数据存储（IoT 传感器数据）
- ✅ 高吞吐量写入（日志、事件流）
- ✅ 用户画像（宽表存储）

**TiKV**:

- ✅ 分布式事务（金融系统）
- ✅ 强一致性要求（库存管理）
- ✅ TiDB 底层存储引擎

---

## 2. ScyllaDB 完整实现

### 2.1 ScyllaDB 概述

**ScyllaDB** 是 Cassandra 的 C++ 重写版本，提供：

- **10 倍性能提升**: 相比 Cassandra
- **无垃圾回收**: C++ 实现，避免 JVM GC 停顿
- **自动分片**: Shard-per-Core 架构
- **CQL 兼容**: 完全兼容 Cassandra Query Language
- **P99 延迟 < 1ms**: 优化的 I/O 调度

---

### 2.2 项目设置

#### Cargo.toml

```toml
[package]
name = "scylladb-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# ScyllaDB 驱动
scylla = "0.13"

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# UUID
uuid = { version = "1", features = ["v4", "serde"] }

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

# 错误处理
thiserror = "1"
anyhow = "1"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }

[dev-dependencies]
testcontainers = "0.20"
```

---

### 2.3 基础操作

#### 连接与初始化

```rust
use scylla::{Session, SessionBuilder};
use anyhow::Result;

/// 创建 ScyllaDB 会话
pub async fn create_session() -> Result<Session> {
    let session: Session = SessionBuilder::new()
        .known_node("127.0.0.1:9042")
        .connection_timeout(std::time::Duration::from_secs(10))
        .build()
        .await?;

    tracing::info!("Connected to ScyllaDB");

    Ok(session)
}

/// 初始化 Keyspace 和 Table
pub async fn initialize_schema(session: &Session) -> Result<()> {
    // 1. 创建 Keyspace
    session.query(
        r#"
        CREATE KEYSPACE IF NOT EXISTS my_keyspace
        WITH replication = {
            'class': 'NetworkTopologyStrategy',
            'datacenter1': 3
        }
        "#,
        &[],
    ).await?;

    // 2. 使用 Keyspace
    session.use_keyspace("my_keyspace", false).await?;

    // 3. 创建 Table
    session.query(
        r#"
        CREATE TABLE IF NOT EXISTS users (
            user_id UUID PRIMARY KEY,
            email TEXT,
            name TEXT,
            age INT,
            created_at TIMESTAMP
        )
        "#,
        &[],
    ).await?;

    tracing::info!("Schema initialized");

    Ok(())
}
```

#### 数据模型

```rust
use serde::{Deserialize, Serialize};
use scylla::FromRow;

#[derive(Debug, Clone, Serialize, Deserialize, FromRow)]
pub struct User {
    pub user_id: uuid::Uuid,
    pub email: String,
    pub name: String,
    pub age: Option<i32>,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl User {
    pub fn new(email: String, name: String) -> Self {
        Self {
            user_id: uuid::Uuid::new_v4(),
            email,
            name,
            age: None,
            created_at: chrono::Utc::now(),
        }
    }
}
```

#### CRUD 操作

```rust
use scylla::Session;

/// 插入用户
pub async fn insert_user(session: &Session, user: &User) -> Result<()> {
    session.query(
        r#"
        INSERT INTO users (user_id, email, name, age, created_at)
        VALUES (?, ?, ?, ?, ?)
        "#,
        (
            user.user_id,
            &user.email,
            &user.name,
            user.age,
            user.created_at,
        ),
    ).await?;

    tracing::info!("User inserted: {}", user.user_id);

    Ok(())
}

/// 查询用户
pub async fn get_user(session: &Session, user_id: uuid::Uuid) -> Result<Option<User>> {
    let rows = session.query(
        "SELECT user_id, email, name, age, created_at FROM users WHERE user_id = ?",
        (user_id,),
    ).await?;

    if let Some(rows) = rows.rows {
        if let Some(row) = rows.into_iter().next() {
            let user: User = row.into_typed()?;
            return Ok(Some(user));
        }
    }

    Ok(None)
}

/// 更新用户
pub async fn update_user(session: &Session, user_id: uuid::Uuid, name: &str) -> Result<()> {
    session.query(
        "UPDATE users SET name = ? WHERE user_id = ?",
        (name, user_id),
    ).await?;

    tracing::info!("User updated: {}", user_id);

    Ok(())
}

/// 删除用户
pub async fn delete_user(session: &Session, user_id: uuid::Uuid) -> Result<()> {
    session.query(
        "DELETE FROM users WHERE user_id = ?",
        (user_id,),
    ).await?;

    tracing::info!("User deleted: {}", user_id);

    Ok(())
}
```

---

### 2.4 高级功能

#### Prepared Statements

```rust
use scylla::prepared_statement::PreparedStatement;

/// 使用 Prepared Statement（性能优化）
pub async fn batch_insert_with_prepared(
    session: &Session,
    users: Vec<User>,
) -> Result<()> {
    let prepared: PreparedStatement = session.prepare(
        r#"
        INSERT INTO users (user_id, email, name, age, created_at)
        VALUES (?, ?, ?, ?, ?)
        "#,
    ).await?;

    for user in users {
        session.execute(
            &prepared,
            (
                user.user_id,
                &user.email,
                &user.name,
                user.age,
                user.created_at,
            ),
        ).await?;
    }

    tracing::info!("Batch insert completed");

    Ok(())
}
```

#### Batch Operations

```rust
use scylla::batch::Batch;

/// 批量写入（原子操作）
pub async fn batch_write(session: &Session, users: Vec<User>) -> Result<()> {
    let mut batch = Batch::default();
    batch.append_statement(
        r#"
        INSERT INTO users (user_id, email, name, age, created_at)
        VALUES (?, ?, ?, ?, ?)
        "#,
    );

    let values: Vec<_> = users.iter()
        .map(|user| (
            user.user_id,
            &user.email,
            &user.name,
            user.age,
            user.created_at,
        ))
        .collect();

    session.batch(&batch, values).await?;

    tracing::info!("Batch write completed");

    Ok(())
}
```

#### LWT (Lightweight Transactions)

```rust
/// 条件插入（IF NOT EXISTS）
pub async fn insert_if_not_exists(
    session: &Session,
    user: &User,
) -> Result<bool> {
    let result = session.query(
        r#"
        INSERT INTO users (user_id, email, name, age, created_at)
        VALUES (?, ?, ?, ?, ?)
        IF NOT EXISTS
        "#,
        (
            user.user_id,
            &user.email,
            &user.name,
            user.age,
            user.created_at,
        ),
    ).await?;

    // LWT 返回 [applied] 列
    if let Some(rows) = result.rows {
        if let Some(row) = rows.into_iter().next() {
            let applied: bool = row.columns[0].as_ref()
                .and_then(|c| c.as_boolean())
                .unwrap_or(false);
            return Ok(applied);
        }
    }

    Ok(false)
}
```

---

### 2.5 OTLP 集成

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

#[instrument(skip(session, user), fields(
    db.system = "scylla",
    db.operation = "insert",
    user.id = %user.user_id
))]
pub async fn traced_insert_user(session: &Session, user: &User) -> Result<()> {
    let tracer = global::tracer("scylla-client");
    
    let mut span = tracer
        .span_builder(format!("ScyllaDB Insert"))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "scylla"),
            KeyValue::new("db.operation", "insert"),
            KeyValue::new("db.statement", "INSERT INTO users ..."),
            KeyValue::new("user.id", user.user_id.to_string()),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let result = insert_user(session, user).await;
    
    let duration = start.elapsed();
    
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("db.latency_ms", duration.as_millis() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result
}
```

---

## 3. TiKV 完整实现

### 3.1 TiKV 概述

**TiKV** 是 PingCAP 开源的分布式 Key-Value 数据库，提供：

- **强一致性**: Raft 协议保证
- **分布式事务**: ACID 事务支持（Percolator 模型）
- **水平扩展**: 自动负载均衡
- **Rust 实现**: 高性能、内存安全
- **CNCF 毕业项目**: 云原生生态认证

---

### 3.2 项目设置

#### Cargo.toml1

```toml
[dependencies]
# TiKV 客户端
tikv-client = "0.3"

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 错误处理
thiserror = "1"
anyhow = "1"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
```

---

### 3.3 基础操作

#### 连接与初始化1

```rust
use tikv_client::{TransactionClient, Config};
use anyhow::Result;

/// 创建 TiKV 客户端
pub async fn create_tikv_client() -> Result<TransactionClient> {
    let client = TransactionClient::new(vec!["127.0.0.1:2379"])
        .await?;

    tracing::info!("Connected to TiKV");

    Ok(client)
}
```

#### 数据模型1

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub email: String,
    pub name: String,
}

impl User {
    pub fn key(&self) -> Vec<u8> {
        format!("user:{}", self.id).into_bytes()
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        Ok(serde_json::to_vec(self)?)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(serde_json::from_slice(bytes)?)
    }
}
```

#### CRUD 操作1

```rust
use tikv_client::TransactionClient;

/// 插入数据
pub async fn put_user(client: &TransactionClient, user: &User) -> Result<()> {
    let mut txn = client.begin_optimistic().await?;
    
    txn.put(user.key(), user.to_bytes()?).await?;
    
    txn.commit().await?;

    tracing::info!("User inserted: {}", user.id);

    Ok(())
}

/// 查询数据
pub async fn get_user(client: &TransactionClient, user_id: &str) -> Result<Option<User>> {
    let mut txn = client.begin_optimistic().await?;
    
    let key = format!("user:{}", user_id).into_bytes();
    let value = txn.get(key).await?;

    if let Some(bytes) = value {
        let user = User::from_bytes(&bytes)?;
        return Ok(Some(user));
    }

    Ok(None)
}

/// 删除数据
pub async fn delete_user(client: &TransactionClient, user_id: &str) -> Result<()> {
    let mut txn = client.begin_optimistic().await?;
    
    let key = format!("user:{}", user_id).into_bytes();
    txn.delete(key).await?;
    
    txn.commit().await?;

    tracing::info!("User deleted: {}", user_id);

    Ok(())
}
```

---

### 3.4 高级功能

#### 分布式事务

```rust
/// 转账事务（ACID 保证）
pub async fn transfer_balance(
    client: &TransactionClient,
    from_user_id: &str,
    to_user_id: &str,
    amount: i64,
) -> Result<()> {
    let mut txn = client.begin_optimistic().await?;

    // 1. 读取余额
    let from_key = format!("balance:{}", from_user_id).into_bytes();
    let to_key = format!("balance:{}", to_user_id).into_bytes();

    let from_balance: i64 = txn.get(from_key.clone()).await?
        .and_then(|v| String::from_utf8(v).ok())
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    let to_balance: i64 = txn.get(to_key.clone()).await?
        .and_then(|v| String::from_utf8(v).ok())
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    // 2. 验证余额
    if from_balance < amount {
        return Err(anyhow::anyhow!("Insufficient balance"));
    }

    // 3. 更新余额
    txn.put(from_key, (from_balance - amount).to_string().into_bytes()).await?;
    txn.put(to_key, (to_balance + amount).to_string().into_bytes()).await?;

    // 4. 提交事务
    txn.commit().await?;

    tracing::info!("Transfer completed: {} -> {} ({})", from_user_id, to_user_id, amount);

    Ok(())
}
```

#### Scan 范围查询

```rust
/// 范围扫描
pub async fn scan_users(client: &TransactionClient) -> Result<Vec<User>> {
    let mut txn = client.begin_optimistic().await?;

    let start_key = b"user:".to_vec();
    let end_key = b"user:\xff".to_vec();

    let pairs = txn.scan(start_key..end_key, 100).await?;

    let users: Vec<User> = pairs.into_iter()
        .filter_map(|kv| User::from_bytes(&kv.1).ok())
        .collect();

    Ok(users)
}
```

#### 悲观事务

```rust
/// 悲观事务（避免冲突）
pub async fn pessimistic_update(
    client: &TransactionClient,
    user_id: &str,
    new_name: &str,
) -> Result<()> {
    let mut txn = client.begin_pessimistic().await?;

    let key = format!("user:{}", user_id).into_bytes();

    // 加锁读取
    let value = txn.get(key.clone()).await?
        .ok_or_else(|| anyhow::anyhow!("User not found"))?;

    let mut user = User::from_bytes(&value)?;
    user.name = new_name.to_string();

    txn.put(key, user.to_bytes()?).await?;
    txn.commit().await?;

    Ok(())
}
```

---

### 3.5 OTLP 集成

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

#[instrument(skip(client, user), fields(
    db.system = "tikv",
    db.operation = "put",
    user.id = %user.id
))]
pub async fn traced_put_user(client: &TransactionClient, user: &User) -> Result<()> {
    let tracer = global::tracer("tikv-client");
    
    let mut span = tracer
        .span_builder(format!("TiKV Put"))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "tikv"),
            KeyValue::new("db.operation", "put"),
            KeyValue::new("user.id", user.id.clone()),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let result = put_user(client, user).await;
    
    let duration = start.elapsed();
    
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("db.latency_ms", duration.as_millis() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result
}
```

---

## 4. 性能对比

### 4.1 读写延迟

| 数据库 | 单点读 (P99) | 单点写 (P99) | 扫描 1000 行 |
|--------|--------------|--------------|--------------|
| **ScyllaDB** | < 1ms | < 1ms | 5-10ms |
| **TiKV** | 1-3ms | 2-5ms | 10-20ms |
| **Cassandra** | 2-5ms | 2-5ms | 15-30ms |
| **Redis** | < 0.1ms | < 0.1ms | 1-5ms |

### 4.2 吞吐量

| 数据库 | 写入 QPS | 读取 QPS |
|--------|----------|----------|
| **ScyllaDB** | 1M+ | 2M+ |
| **TiKV** | 100K | 500K |
| **Cassandra** | 500K | 1M |

---

## 5. 测试策略

### 5.1 Testcontainers 集成测试

```rust
#[cfg(test)]
mod tests {
    use testcontainers::{clients::Cli, RunnableImage};
    use testcontainers::images::generic::GenericImage;

    #[tokio::test]
    async fn test_scylladb_crud() {
        let docker = Cli::default();
        
        let scylla_image = GenericImage::new("scylladb/scylla", "5.4")
            .with_exposed_port(9042);

        let container = docker.run(scylla_image);
        let port = container.get_host_port_ipv4(9042);

        let session = SessionBuilder::new()
            .known_node(format!("127.0.0.1:{}", port))
            .build()
            .await
            .unwrap();

        initialize_schema(&session).await.unwrap();

        let user = User::new("test@example.com".to_string(), "Test User".to_string());
        insert_user(&session, &user).await.unwrap();

        let retrieved = get_user(&session, user.user_id).await.unwrap();
        assert!(retrieved.is_some());
    }
}
```

---

## 6. 生产实践

### 6.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  scylla:
    image: scylladb/scylla:5.4
    ports:
      - "9042:9042"
    command: --smp 2 --memory 2G
    healthcheck:
      test: ["CMD", "cqlsh", "-e", "describe cluster"]
      interval: 10s
      timeout: 5s
      retries: 5

  tikv-pd:
    image: pingcap/pd:v7.5.0
    ports:
      - "2379:2379"
    command:
      - --name=pd
      - --client-urls=http://0.0.0.0:2379
      - --peer-urls=http://0.0.0.0:2380
      - --advertise-client-urls=http://tikv-pd:2379
      - --advertise-peer-urls=http://tikv-pd:2380

  tikv:
    image: pingcap/tikv:v7.5.0
    ports:
      - "20160:20160"
    command:
      - --addr=0.0.0.0:20160
      - --advertise-addr=tikv:20160
      - --pd=tikv-pd:2379
    depends_on:
      - tikv-pd
```

---

## 7. 国际标准对齐

### 7.1 ScyllaDB

- ✅ **CQL 3.0**: Cassandra Query Language
- ✅ **Tunable Consistency**: Quorum, Local Quorum, Each Quorum
- ✅ **NetworkTopologyStrategy**: Multi-datacenter replication

### 7.2 TiKV

- ✅ **Raft Consensus**: Strong consistency
- ✅ **Percolator Transaction Model**: Google Percolator
- ✅ **gRPC API**: Protocol Buffers

### 7.3 OpenTelemetry 语义约定

```rust
// Database Semantic Conventions (v1.21.0)
span.set_attribute(KeyValue::new("db.system", "scylla"));
span.set_attribute(KeyValue::new("db.operation", "select"));
span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE user_id = ?"));
span.set_attribute(KeyValue::new("db.name", "my_keyspace"));
```

---

## 总结

### ScyllaDB 优势

1. **极低延迟**: P99 < 1ms
2. **高吞吐量**: 单节点 1M+ QPS
3. **Shard-per-Core**: 无锁架构
4. **CQL 兼容**: 易于从 Cassandra 迁移

### TiKV 优势

1. **强一致性**: Raft 协议保证
2. **分布式事务**: ACID 事务支持
3. **自动负载均衡**: 无需手动分片
4. **Rust 实现**: 高性能、内存安全

### 选择建议

- ✅ **高吞吐量写入** → ScyllaDB
- ✅ **强一致性事务** → TiKV
- ✅ **SQL 查询** → TiDB (基于 TiKV)
- ✅ **时序数据** → ScyllaDB

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
