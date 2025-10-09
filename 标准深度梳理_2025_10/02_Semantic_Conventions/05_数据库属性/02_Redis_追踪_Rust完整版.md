# Redis 追踪 Rust 完整实现指南

## 目录

- [Redis 追踪 Rust 完整实现指南](#redis-追踪-rust-完整实现指南)
  - [目录](#目录)
  - [1. Redis 架构概述](#1-redis-架构概述)
    - [1.1 Redis 核心特性](#11-redis-核心特性)
    - [1.2 Redis 与 OpenTelemetry](#12-redis-与-opentelemetry)
  - [2. Rust 依赖配置](#2-rust-依赖配置)
  - [3. Redis Semantic Conventions](#3-redis-semantic-conventions)
    - [3.1 数据库属性](#31-数据库属性)
    - [3.2 Span 命名规范](#32-span-命名规范)
  - [4. 基础命令追踪](#4-基础命令追踪)
    - [4.1 String 操作追踪](#41-string-操作追踪)
    - [4.2 Hash 操作追踪](#42-hash-操作追踪)
    - [4.3 List 操作追踪](#43-list-操作追踪)
    - [4.4 Set 操作追踪](#44-set-操作追踪)
    - [4.5 Sorted Set 操作追踪](#45-sorted-set-操作追踪)
  - [5. Pipeline 追踪](#5-pipeline-追踪)
  - [6. Transaction 追踪](#6-transaction-追踪)
  - [7. Pub/Sub 追踪](#7-pubsub-追踪)
    - [7.1 Publisher 追踪](#71-publisher-追踪)
    - [7.2 Subscriber 追踪](#72-subscriber-追踪)
  - [8. 连接池追踪](#8-连接池追踪)
  - [9. Cluster 模式追踪](#9-cluster-模式追踪)
  - [10. 错误处理](#10-错误处理)
  - [11. 性能监控](#11-性能监控)
    - [11.1 命令延迟监控](#111-命令延迟监控)
    - [11.2 连接池监控](#112-连接池监控)
  - [12. 完整生产示例](#12-完整生产示例)
  - [总结](#总结)

---

## 1. Redis 架构概述

### 1.1 Redis 核心特性

Redis 是高性能的内存键值数据库：

- **数据结构**：String、Hash、List、Set、Sorted Set、Bitmap、HyperLogLog、Stream
- **持久化**：RDB、AOF
- **集群**：Sentinel、Cluster
- **发布订阅**：Pub/Sub 模式
- **高性能**：内存操作、Pipeline、Transaction

### 1.2 Redis 与 OpenTelemetry

Redis 追踪关注点：

1. **命令追踪**：命令类型、执行时间、键
2. **连接池**：连接获取、复用、超时
3. **Pipeline/Transaction**：批量操作、事务执行
4. **Pub/Sub**：消息发布、订阅

---

## 2. Rust 依赖配置

```toml
[dependencies]
# Redis 客户端
redis = { version = "0.27.6", features = ["tokio-comp", "connection-manager", "cluster", "cluster-async"] }

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 连接池
deadpool = "0.12"
deadpool-redis = "0.18"

[dev-dependencies]
criterion = "0.5"
```

---

## 3. Redis Semantic Conventions

### 3.1 数据库属性

```rust
// Redis 属性常量
pub mod attributes {
    pub const DB_SYSTEM: &str = "db.system";                     // "redis"
    pub const DB_NAME: &str = "db.name";                         // Redis database index
    pub const DB_OPERATION: &str = "db.operation";               // Redis command (GET, SET, HGET, etc.)
    pub const DB_STATEMENT: &str = "db.statement";               // Full command
    pub const DB_REDIS_DATABASE_INDEX: &str = "db.redis.database_index";
    pub const DB_REDIS_KEY: &str = "db.redis.key";
    pub const DB_REDIS_PIPELINE_LENGTH: &str = "db.redis.pipeline.length";
    pub const NET_PEER_NAME: &str = "net.peer.name";            // Redis host
    pub const NET_PEER_PORT: &str = "net.peer.port";            // Redis port
}
```

### 3.2 Span 命名规范

- **基础命令**：`Redis {command}`（如 `Redis GET`, `Redis SET`）
- **Pipeline**：`Redis PIPELINE`
- **Transaction**：`Redis TRANSACTION`
- **Pub/Sub**：`Redis PUBLISH`, `Redis SUBSCRIBE`

---

## 4. 基础命令追踪

### 4.1 String 操作追踪

```rust
use redis::aio::ConnectionManager;
use redis::{AsyncCommands, RedisResult};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};

/// Redis 客户端（支持追踪）
pub struct TracedRedisClient {
    manager: ConnectionManager,
    host: String,
    port: u16,
    db_index: i64,
}

impl TracedRedisClient {
    pub fn new(manager: ConnectionManager, host: String, port: u16, db_index: i64) -> Self {
        Self {
            manager,
            host,
            port,
            db_index,
        }
    }

    /// GET 命令（带追踪）
    pub async fn get_with_trace(&self, key: &str) -> RedisResult<Option<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis GET")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "GET"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("db.redis.database_index", self.db_index),
                KeyValue::new("net.peer.name", self.host.clone()),
                KeyValue::new("net.peer.port", self.port as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let start = std::time::Instant::now();
        let mut conn = self.manager.clone();
        let result: RedisResult<Option<String>> = conn.get(key).await;
        let duration = start.elapsed();

        cx.span().set_attribute(KeyValue::new("db.response_time.ms", duration.as_millis() as i64));

        match &result {
            Ok(Some(value)) => {
                cx.span().add_event("Value retrieved", vec![
                    KeyValue::new("value.length", value.len() as i64),
                ]);
            }
            Ok(None) => {
                cx.span().add_event("Key not found", vec![]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }

    /// SET 命令（带追踪）
    pub async fn set_with_trace(&self, key: &str, value: &str) -> RedisResult<()> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis SET")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SET"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("db.redis.database_index", self.db_index),
                KeyValue::new("net.peer.name", self.host.clone()),
                KeyValue::new("net.peer.port", self.port as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let start = std::time::Instant::now();
        let mut conn = self.manager.clone();
        let result: RedisResult<()> = conn.set(key, value).await;
        let duration = start.elapsed();

        cx.span().set_attributes(vec![
            KeyValue::new("db.response_time.ms", duration.as_millis() as i64),
            KeyValue::new("value.length", value.len() as i64),
        ]);

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// SETEX 命令（带过期时间）
    pub async fn setex_with_trace(&self, key: &str, value: &str, seconds: usize) -> RedisResult<()> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis SETEX")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SETEX"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("db.redis.ttl", seconds as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<()> = conn.set_ex(key, value, seconds).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }
}
```

### 4.2 Hash 操作追踪

```rust
impl TracedRedisClient {
    /// HGET 命令（带追踪）
    pub async fn hget_with_trace(&self, key: &str, field: &str) -> RedisResult<Option<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis HGET")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "HGET"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("db.redis.field", field.to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<Option<String>> = conn.hget(key, field).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// HSET 命令（带追踪）
    pub async fn hset_with_trace(&self, key: &str, field: &str, value: &str) -> RedisResult<()> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis HSET")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "HSET"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("db.redis.field", field.to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<()> = conn.hset(key, field, value).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// HGETALL 命令（带追踪）
    pub async fn hgetall_with_trace(&self, key: &str) -> RedisResult<std::collections::HashMap<String, String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis HGETALL")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "HGETALL"),
                KeyValue::new("db.redis.key", key.to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<std::collections::HashMap<String, String>> = conn.hgetall(key).await;

        match &result {
            Ok(hash) => {
                cx.span().add_event("Hash retrieved", vec![
                    KeyValue::new("field.count", hash.len() as i64),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

### 4.3 List 操作追踪

```rust
impl TracedRedisClient {
    /// LPUSH 命令（带追踪）
    pub async fn lpush_with_trace(&self, key: &str, values: &[String]) -> RedisResult<i64> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis LPUSH")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "LPUSH"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("list.value_count", values.len() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<i64> = conn.lpush(key, values).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// LRANGE 命令（带追踪）
    pub async fn lrange_with_trace(&self, key: &str, start: isize, stop: isize) -> RedisResult<Vec<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis LRANGE")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "LRANGE"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("list.start", start as i64),
                KeyValue::new("list.stop", stop as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<Vec<String>> = conn.lrange(key, start, stop).await;

        match &result {
            Ok(list) => {
                cx.span().add_event("List range retrieved", vec![
                    KeyValue::new("item.count", list.len() as i64),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

### 4.4 Set 操作追踪

```rust
impl TracedRedisClient {
    /// SADD 命令（带追踪）
    pub async fn sadd_with_trace(&self, key: &str, members: &[String]) -> RedisResult<i64> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis SADD")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SADD"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("set.member_count", members.len() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<i64> = conn.sadd(key, members).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// SMEMBERS 命令（带追踪）
    pub async fn smembers_with_trace(&self, key: &str) -> RedisResult<Vec<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis SMEMBERS")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SMEMBERS"),
                KeyValue::new("db.redis.key", key.to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<Vec<String>> = conn.smembers(key).await;

        match &result {
            Ok(members) => {
                cx.span().add_event("Set members retrieved", vec![
                    KeyValue::new("member.count", members.len() as i64),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

### 4.5 Sorted Set 操作追踪

```rust
impl TracedRedisClient {
    /// ZADD 命令（带追踪）
    pub async fn zadd_with_trace(&self, key: &str, member: &str, score: f64) -> RedisResult<i64> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis ZADD")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "ZADD"),
                KeyValue::new("db.redis.key", key.to_string()),
                KeyValue::new("zset.score", score),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<i64> = conn.zadd(key, member, score).await;

        if let Err(e) = &result {
            cx.span().record_error(&**e);
        }

        result
    }

    /// ZRANGE 命令（带追踪）
    pub async fn zrange_with_trace(&self, key: &str, start: isize, stop: isize) -> RedisResult<Vec<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis ZRANGE")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "ZRANGE"),
                KeyValue::new("db.redis.key", key.to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<Vec<String>> = conn.zrange(key, start, stop).await;

        match &result {
            Ok(members) => {
                cx.span().add_event("Sorted set range retrieved", vec![
                    KeyValue::new("member.count", members.len() as i64),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

---

## 5. Pipeline 追踪

```rust
use redis::pipe;

impl TracedRedisClient {
    /// Pipeline 批量操作（带追踪）
    pub async fn pipeline_with_trace(&self, commands: Vec<(&str, Vec<String>)>) -> RedisResult<Vec<String>> {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis PIPELINE")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "PIPELINE"),
                KeyValue::new("db.redis.pipeline.length", commands.len() as i64),
                KeyValue::new("net.peer.name", self.host.clone()),
                KeyValue::new("net.peer.port", self.port as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let start = std::time::Instant::now();
        let mut conn = self.manager.clone();
        let mut pipeline = pipe();

        // 构建 Pipeline
        for (cmd, args) in &commands {
            pipeline.cmd(*cmd).arg(args);
        }

        let result: RedisResult<Vec<String>> = pipeline.query_async(&mut conn).await;
        let duration = start.elapsed();

        cx.span().set_attribute(KeyValue::new("db.response_time.ms", duration.as_millis() as i64));

        match &result {
            Ok(results) => {
                cx.span().add_event("Pipeline executed", vec![
                    KeyValue::new("result.count", results.len() as i64),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

---

## 6. Transaction 追踪

```rust
impl TracedRedisClient {
    /// Transaction 事务操作（带追踪）
    pub async fn transaction_with_trace<F, T>(&self, func: F) -> RedisResult<T>
    where
        F: FnOnce(&mut redis::Pipeline) -> RedisResult<()>,
        T: redis::FromRedisValue,
    {
        let tracer = global::tracer("redis-client");
        let mut span = tracer
            .span_builder("Redis TRANSACTION")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "MULTI"),
                KeyValue::new("net.peer.name", self.host.clone()),
                KeyValue::new("net.peer.port", self.port as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let start = std::time::Instant::now();
        let mut conn = self.manager.clone();
        let mut pipeline = pipe();
        pipeline.atomic();

        func(&mut pipeline)?;

        let result: RedisResult<T> = pipeline.query_async(&mut conn).await;
        let duration = start.elapsed();

        cx.span().set_attribute(KeyValue::new("db.response_time.ms", duration.as_millis() as i64));

        match &result {
            Ok(_) => {
                cx.span().add_event("Transaction committed", vec![]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
                cx.span().add_event("Transaction failed", vec![]);
            }
        }

        result
    }
}
```

---

## 7. Pub/Sub 追踪

### 7.1 Publisher 追踪

```rust
impl TracedRedisClient {
    /// PUBLISH 命令（带追踪）
    pub async fn publish_with_trace(&self, channel: &str, message: &str) -> RedisResult<i64> {
        let tracer = global::tracer("redis-pubsub");
        let mut span = tracer
            .span_builder(format!("Redis PUBLISH {}", channel))
            .with_kind(opentelemetry::trace::SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "PUBLISH"),
                KeyValue::new("messaging.system", "redis"),
                KeyValue::new("messaging.destination.name", channel.to_string()),
                KeyValue::new("messaging.message.payload_size", message.len() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut conn = self.manager.clone();
        let result: RedisResult<i64> = redis::cmd("PUBLISH")
            .arg(channel)
            .arg(message)
            .query_async(&mut conn)
            .await;

        match &result {
            Ok(subscriber_count) => {
                cx.span().add_event("Message published", vec![
                    KeyValue::new("subscriber.count", *subscriber_count),
                ]);
            }
            Err(e) => {
                cx.span().record_error(&**e);
            }
        }

        result
    }
}
```

### 7.2 Subscriber 追踪

```rust
use redis::aio::PubSub;

/// 订阅 Redis Channel（带追踪）
pub async fn subscribe_with_trace(
    client: &redis::Client,
    channels: &[String],
) -> RedisResult<PubSub> {
    let tracer = global::tracer("redis-pubsub");
    let mut span = tracer
        .span_builder("Redis SUBSCRIBE")
        .with_kind(opentelemetry::trace::SpanKind::Consumer)
        .with_attributes(vec![
            KeyValue::new("db.system", "redis"),
            KeyValue::new("db.operation", "SUBSCRIBE"),
            KeyValue::new("messaging.system", "redis"),
            KeyValue::new("channel.count", channels.len() as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let mut pubsub = client.get_async_pubsub().await?;
    pubsub.subscribe(channels).await?;

    cx.span().add_event("Subscribed to channels", vec![]);

    Ok(pubsub)
}
```

---

## 8. 连接池追踪

```rust
use deadpool_redis::{Config, Runtime, Pool};

/// 创建 Redis 连接池（带追踪）
pub async fn create_pool_with_trace(
    redis_url: &str,
    max_size: usize,
) -> Result<Pool, Box<dyn std::error::Error>> {
    let tracer = global::tracer("redis-pool");
    let mut span = tracer
        .span_builder("redis.pool.create")
        .with_attributes(vec![
            KeyValue::new("db.system", "redis"),
            KeyValue::new("pool.max_size", max_size as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let cfg = Config::from_url(redis_url);
    let pool = cfg.create_pool(Some(Runtime::Tokio1))?;

    cx.span().add_event("Connection pool created", vec![]);
    Ok(pool)
}
```

---

## 9. Cluster 模式追踪

```rust
use redis::cluster::ClusterClient;
use redis::cluster_async::ClusterConnection;

/// 创建 Redis Cluster 连接（带追踪）
pub async fn connect_cluster_with_trace(
    nodes: &[String],
) -> RedisResult<ClusterConnection> {
    let tracer = global::tracer("redis-cluster");
    let mut span = tracer
        .span_builder("redis.cluster.connect")
        .with_attributes(vec![
            KeyValue::new("db.system", "redis"),
            KeyValue::new("cluster.node_count", nodes.len() as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let client = ClusterClient::new(nodes.to_vec())?;
    let connection = client.get_async_connection().await?;

    cx.span().add_event("Cluster connection established", vec![]);

    Ok(connection)
}
```

---

## 10. 错误处理

```rust
use std::time::Duration;

/// 带重试的 Redis 命令执行
pub async fn execute_with_retry<F, T>(
    mut operation: F,
    max_retries: u32,
) -> RedisResult<T>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = RedisResult<T>>>>,
{
    let tracer = global::tracer("redis-client");
    let mut span = tracer
        .span_builder("redis.retry")
        .with_attributes(vec![
            KeyValue::new("max_retries", max_retries as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    for attempt in 1..=max_retries {
        match operation().await {
            Ok(result) => {
                cx.span().set_attribute(KeyValue::new("attempt", attempt as i64));
                return Ok(result);
            }
            Err(e) if attempt < max_retries => {
                cx.span().add_event("Retry attempt failed", vec![
                    KeyValue::new("attempt", attempt as i64),
                ]);
                tokio::time::sleep(Duration::from_millis(100 * attempt as u64)).await;
            }
            Err(e) => {
                cx.span().record_error(&e);
                return Err(e);
            }
        }
    }

    unreachable!()
}
```

---

## 11. 性能监控

### 11.1 命令延迟监控

```rust
use opentelemetry::metrics::{Meter, Histogram};

pub struct RedisMetrics {
    command_duration: Histogram<f64>,
    command_payload_size: Histogram<u64>,
}

impl RedisMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            command_duration: meter
                .f64_histogram("redis.command.duration")
                .with_unit("ms")
                .with_description("Redis command execution duration")
                .build(),
            command_payload_size: meter
                .u64_histogram("redis.command.payload_size")
                .with_unit("bytes")
                .with_description("Redis command payload size")
                .build(),
        }
    }

    pub fn record_command(&self, duration: Duration, payload_size: usize, operation: &str) {
        let attrs = &[KeyValue::new("db.operation", operation.to_string())];
        self.command_duration.record(duration.as_secs_f64() * 1000.0, attrs);
        self.command_payload_size.record(payload_size as u64, attrs);
    }
}
```

### 11.2 连接池监控

```rust
use opentelemetry::metrics::{Counter, Gauge};

pub struct PoolMetrics {
    connections_active: Gauge<i64>,
    connections_idle: Gauge<i64>,
    connection_errors: Counter<u64>,
}

impl PoolMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            connections_active: meter
                .i64_gauge("redis.pool.connections.active")
                .with_description("Active connections in pool")
                .build(),
            connections_idle: meter
                .i64_gauge("redis.pool.connections.idle")
                .with_description("Idle connections in pool")
                .build(),
            connection_errors: meter
                .u64_counter("redis.pool.errors")
                .with_description("Connection pool errors")
                .build(),
        }
    }
}
```

---

## 12. 完整生产示例

```rust
use redis::Client;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    global::set_tracer_provider(tracer_provider);

    // 创建 Redis 客户端
    let client = Client::open("redis://127.0.0.1:6379")?;
    let manager = redis::aio::ConnectionManager::new(client.clone()).await?;

    let redis_client = TracedRedisClient::new(
        manager,
        "127.0.0.1".to_string(),
        6379,
        0,
    );

    // String 操作
    redis_client.set_with_trace("user:1000", "John Doe").await?;
    let value = redis_client.get_with_trace("user:1000").await?;
    println!("User: {:?}", value);

    // Hash 操作
    redis_client.hset_with_trace("user:1000:profile", "name", "John").await?;
    redis_client.hset_with_trace("user:1000:profile", "age", "30").await?;
    let profile = redis_client.hgetall_with_trace("user:1000:profile").await?;
    println!("Profile: {:?}", profile);

    // List 操作
    redis_client.lpush_with_trace("tasks", &["task1".to_string(), "task2".to_string()]).await?;
    let tasks = redis_client.lrange_with_trace("tasks", 0, -1).await?;
    println!("Tasks: {:?}", tasks);

    // Pipeline 操作
    let commands = vec![
        ("GET", vec!["user:1000".to_string()]),
        ("HGETALL", vec!["user:1000:profile".to_string()]),
    ];
    let results = redis_client.pipeline_with_trace(commands).await?;
    println!("Pipeline results: {:?}", results);

    // Transaction 操作
    let result: String = redis_client.transaction_with_trace(|pipe| {
        pipe.set("counter", 0)
            .incr("counter", 1)
            .get("counter");
        Ok(())
    }).await?;
    println!("Counter: {}", result);

    // Pub/Sub
    redis_client.publish_with_trace("notifications", "Hello World").await?;

    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}
```

---

## 总结

本指南涵盖了 Redis 与 OpenTelemetry 集成的完整实现：

1. **基础命令追踪**：String、Hash、List、Set、Sorted Set
2. **批量操作**：Pipeline、Transaction
3. **Pub/Sub**：Publisher、Subscriber
4. **连接管理**：连接池、Cluster 模式
5. **错误处理**：重试机制
6. **性能监控**：命令延迟、连接池指标

通过这些实现，您可以在生产环境中获得 Redis 操作的完整可观测性。
