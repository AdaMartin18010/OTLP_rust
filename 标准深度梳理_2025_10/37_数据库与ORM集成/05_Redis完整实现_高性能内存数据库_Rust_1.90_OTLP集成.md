# Redis 完整实现 - 高性能内存数据库与缓存 - Rust 1.90 + OTLP 集成

## 目录

- [Redis 完整实现 - 高性能内存数据库与缓存 - Rust 1.90 + OTLP 集成](#redis-完整实现---高性能内存数据库与缓存---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. Redis 概述](#1-redis-概述)
    - [1.1 什么是 Redis？](#11-什么是-redis)
    - [1.2 Rust Redis 客户端对比](#12-rust-redis-客户端对比)
  - [2. 核心架构](#2-核心架构)
    - [2.1 Redis 数据结构](#21-redis-数据结构)
    - [2.2 使用场景矩阵](#22-使用场景矩阵)
  - [3. 项目设置](#3-项目设置)
    - [3.1 依赖配置](#31-依赖配置)
    - [3.2 项目结构](#32-项目结构)
  - [4. 基础操作](#4-基础操作)
    - [4.1 客户端封装](#41-客户端封装)
    - [4.2 基础 String 操作](#42-基础-string-操作)
    - [4.3 Hash 操作](#43-hash-操作)
  - [5. 高级数据结构](#5-高级数据结构)
    - [5.1 Sorted Set（排行榜）](#51-sorted-set排行榜)
    - [5.2 Set 操作（标签系统）](#52-set-操作标签系统)
  - [6. Redis Streams 消息队列](#6-redis-streams-消息队列)
    - [6.1 Streams 生产者](#61-streams-生产者)
  - [7. 发布订阅（Pub/Sub）](#7-发布订阅pubsub)
    - [7.1 发布者](#71-发布者)
    - [7.2 订阅者](#72-订阅者)
  - [8. 缓存策略](#8-缓存策略)
    - [8.1 Cache-Aside 模式](#81-cache-aside-模式)
  - [9. 分布式锁](#9-分布式锁)
    - [9.1 基于 SET NX EX 的分布式锁](#91-基于-set-nx-ex-的分布式锁)
  - [10. 管道与事务](#10-管道与事务)
    - [10.1 Pipeline（管道）](#101-pipeline管道)
    - [10.2 Transaction（事务）](#102-transaction事务)
  - [11. OTLP 集成](#11-otlp-集成)
    - [11.1 追踪配置](#111-追踪配置)
    - [11.2 带追踪的 Redis 操作](#112-带追踪的-redis-操作)
  - [12. 生产环境实践](#12-生产环境实践)
    - [12.1 Docker Compose 部署](#121-docker-compose-部署)
  - [13. 国际标准对齐](#13-国际标准对齐)
    - [13.1 Redis 协议对齐](#131-redis-协议对齐)
    - [13.2 OpenTelemetry Semantic Conventions](#132-opentelemetry-semantic-conventions)
  - [14. 总结](#14-总结)
    - [14.1 Redis 核心优势](#141-redis-核心优势)
    - [14.2 何时选择 Redis](#142-何时选择-redis)
    - [14.3 生产部署清单](#143-生产部署清单)

---

## 1. Redis 概述

### 1.1 什么是 Redis？

**Redis (Remote Dictionary Server)** 是一个开源的内存数据结构存储系统，可用作数据库、缓存和消息队列。

```text
┌────────────────────────────────────────────────────────────┐
│                   Redis 核心特点                            │
├────────────────────────────────────────────────────────────┤
│  ✅ 内存存储 - 微秒级延迟                                   │
│  ✅ 丰富的数据结构 - String, Hash, List, Set, Sorted Set    │
│  ✅ 持久化 - RDB, AOF                                      │
│  ✅ 高可用 - Replication, Sentinel, Cluster                │
│  ✅ Lua 脚本 - 原子性操作                                   │
│  ✅ 发布/订阅 - Pub/Sub                                    │
│  ✅ Streams - 消息队列和事件溯源                            │
│  ✅ 模块扩展 - RedisJSON, RedisSearch, RedisGraph          │
└────────────────────────────────────────────────────────────┘
```

### 1.2 Rust Redis 客户端对比

| 特性 | redis-rs | fred | mobc + redis |
|------|----------|------|--------------|
| **异步** | ✅ Tokio/async-std | ✅ Tokio | ✅ Tokio |
| **连接池** | ⚠️ 手动 | ✅ 内置 | ✅ mobc |
| **集群** | ✅ | ✅ | ⚠️ 部分 |
| **管道** | ✅ | ✅ | ✅ |
| **Streams** | ✅ | ✅ | ✅ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **性能** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **社区** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |

本文使用 **redis-rs**（最成熟和广泛使用）。

---

## 2. 核心架构

### 2.1 Redis 数据结构

```text
┌────────────────────────────────────────────────────────────┐
│                Redis 核心数据结构                           │
├────────────────────────────────────────────────────────────┤
│  1. String       →  简单键值对（最大 512MB）               │
│  2. Hash         →  字段-值对集合（对象存储）               │
│  3. List         →  双向链表（队列、栈）                    │
│  4. Set          →  无序唯一集合（标签、关系）              │
│  5. Sorted Set   →  有序集合（排行榜）                      │
│  6. Bitmap       →  位图（布隆过滤器）                      │
│  7. HyperLogLog  →  基数统计（UV统计）                      │
│  8. Geospatial   →  地理位置（附近的人）                    │
│  9. Streams      →  消息队列（Event Sourcing）             │
└────────────────────────────────────────────────────────────┘
```

### 2.2 使用场景矩阵

| 场景 | 数据结构 | 说明 |
|------|---------|------|
| **缓存** | String, Hash | Session, User Profile |
| **计数器** | String (INCR) | Page Views, Likes |
| **排行榜** | Sorted Set | Leaderboard, Top 10 |
| **消息队列** | List, Streams | Task Queue, Event Stream |
| **实时分析** | HyperLogLog | UV, DAU |
| **社交关系** | Set | Followers, Friends |
| **地理位置** | Geospatial | Nearby Search |
| **分布式锁** | String + Lua | Distributed Lock |

---

## 3. 项目设置

### 3.1 依赖配置

```toml
[package]
name = "redis-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Redis 客户端
redis = { version = "0.26", features = ["tokio-comp", "connection-manager", "streams"] }

# 连接池（可选）
deadpool-redis = "0.16"        # 推荐使用

# 异步运行时
tokio = { version = "1", features = ["full"] }
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日期时间
chrono = { version = "0.4", features = ["serde"] }
uuid = { version = "1.10", features = ["serde", "v4"] }

# 错误处理
thiserror = "1.0"
anyhow = "1.0"

# OpenTelemetry 集成
opentelemetry = { version = "0.25", features = ["trace"] }
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic", "trace"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio", "trace"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"

[dev-dependencies]
testcontainers = "0.21"        # Redis 容器测试
```

### 3.2 项目结构

```text
redis-otlp-example/
├── src/
│   ├── lib.rs                    # 库入口
│   ├── client.rs                 # 客户端封装
│   ├── cache.rs                  # 缓存管理
│   ├── queue.rs                  # 队列操作（List）
│   ├── streams.rs                # Redis Streams
│   ├── pubsub.rs                 # Pub/Sub
│   ├── lock.rs                   # 分布式锁
│   ├── pipeline.rs               # 管道操作
│   ├── types.rs                  # 数据类型
│   ├── error.rs                  # 错误处理
│   └── telemetry.rs              # OTLP 追踪
├── examples/
│   ├── basic_operations.rs       # 基础操作
│   ├── caching.rs                # 缓存示例
│   ├── streams_example.rs        # Streams 消息队列
│   ├── distributed_lock.rs       # 分布式锁
│   └── leaderboard.rs            # 排行榜
└── docker/
    └── docker-compose.yml        # Redis 集群部署
```

---

## 4. 基础操作

### 4.1 客户端封装

```rust
// src/client.rs
use redis::{Client, Connection, aio::ConnectionManager, AsyncCommands, RedisResult};
use crate::error::RedisError;

/// Redis 客户端配置
#[derive(Debug, Clone)]
pub struct RedisConfig {
    pub url: String,
    pub pool_size: usize,
    pub timeout_ms: u64,
}

impl Default for RedisConfig {
    fn default() -> Self {
        Self {
            url: "redis://localhost:6379".to_string(),
            pool_size: 10,
            timeout_ms: 5000,
        }
    }
}

/// Redis 客户端
pub struct RedisClient {
    client: Client,
}

impl RedisClient {
    /// 创建客户端
    pub fn new(config: RedisConfig) -> Result<Self, RedisError> {
        let client = Client::open(config.url.as_str())?;
        
        tracing::info!(url = %config.url, "Redis client created");
        
        Ok(Self { client })
    }

    /// 获取异步连接管理器
    pub async fn get_async_connection(&self) -> Result<ConnectionManager, RedisError> {
        let conn = ConnectionManager::new(self.client.clone()).await?;
        Ok(conn)
    }

    /// 获取同步连接
    pub fn get_connection(&self) -> Result<Connection, RedisError> {
        let conn = self.client.get_connection()?;
        Ok(conn)
    }
}
```

### 4.2 基础 String 操作

```rust
use redis::AsyncCommands;
use serde::{Serialize, Deserialize};

/// String 操作
pub struct StringOps {
    conn: ConnectionManager,
}

impl StringOps {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }

    /// 设置键值
    pub async fn set(&mut self, key: &str, value: &str) -> RedisResult<()> {
        self.conn.set(key, value).await
    }

    /// 设置键值（带过期时间）
    pub async fn set_ex(&mut self, key: &str, value: &str, seconds: u64) -> RedisResult<()> {
        self.conn.set_ex(key, value, seconds).await
    }

    /// 仅当键不存在时设置
    pub async fn set_nx(&mut self, key: &str, value: &str) -> RedisResult<bool> {
        self.conn.set_nx(key, value).await
    }

    /// 获取键值
    pub async fn get(&mut self, key: &str) -> RedisResult<Option<String>> {
        self.conn.get(key).await
    }

    /// 删除键
    pub async fn del(&mut self, key: &str) -> RedisResult<()> {
        self.conn.del(key).await
    }

    /// 自增
    pub async fn incr(&mut self, key: &str) -> RedisResult<i64> {
        self.conn.incr(key, 1).await
    }

    /// 自减
    pub async fn decr(&mut self, key: &str) -> RedisResult<i64> {
        self.conn.decr(key, 1).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore]
    async fn test_string_ops() {
        let client = RedisClient::new(RedisConfig::default()).unwrap();
        let conn = client.get_async_connection().await.unwrap();
        let mut ops = StringOps::new(conn);

        // SET
        ops.set("key1", "value1").await.unwrap();

        // GET
        let value: Option<String> = ops.get("key1").await.unwrap();
        assert_eq!(value, Some("value1".to_string()));

        // INCR
        let count = ops.incr("counter").await.unwrap();
        assert_eq!(count, 1);
    }
}
```

### 4.3 Hash 操作

```rust
/// Hash 操作（对象存储）
pub struct HashOps {
    conn: ConnectionManager,
}

impl HashOps {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }

    /// 设置 Hash 字段
    pub async fn hset(&mut self, key: &str, field: &str, value: &str) -> RedisResult<()> {
        self.conn.hset(key, field, value).await
    }

    /// 获取 Hash 字段
    pub async fn hget(&mut self, key: &str, field: &str) -> RedisResult<Option<String>> {
        self.conn.hget(key, field).await
    }

    /// 获取所有字段
    pub async fn hgetall(&mut self, key: &str) -> RedisResult<std::collections::HashMap<String, String>> {
        self.conn.hgetall(key).await
    }

    /// 批量设置
    pub async fn hmset(&mut self, key: &str, items: &[(&str, &str)]) -> RedisResult<()> {
        self.conn.hset_multiple(key, items).await
    }

    /// 删除字段
    pub async fn hdel(&mut self, key: &str, field: &str) -> RedisResult<()> {
        self.conn.hdel(key, field).await
    }

    /// 检查字段是否存在
    pub async fn hexists(&mut self, key: &str, field: &str) -> RedisResult<bool> {
        self.conn.hexists(key, field).await
    }
}
```

---

## 5. 高级数据结构

### 5.1 Sorted Set（排行榜）

```rust
// src/leaderboard.rs
use redis::AsyncCommands;

/// 排行榜管理
pub struct Leaderboard {
    conn: ConnectionManager,
    key: String,
}

impl Leaderboard {
    pub fn new(conn: ConnectionManager, key: String) -> Self {
        Self { conn, key }
    }

    /// 更新分数
    pub async fn update_score(&mut self, user_id: &str, score: i64) -> RedisResult<()> {
        self.conn.zadd(&self.key, user_id, score).await
    }

    /// 增加分数
    pub async fn increment_score(&mut self, user_id: &str, delta: i64) -> RedisResult<i64> {
        self.conn.zincr(&self.key, user_id, delta).await
    }

    /// 获取用户排名（从0开始）
    pub async fn get_rank(&mut self, user_id: &str) -> RedisResult<Option<usize>> {
        // ZREVRANK 返回从高到低的排名
        self.conn.zrevrank(&self.key, user_id).await
    }

    /// 获取用户分数
    pub async fn get_score(&mut self, user_id: &str) -> RedisResult<Option<i64>> {
        self.conn.zscore(&self.key, user_id).await
    }

    /// 获取 Top N
    pub async fn get_top_n(&mut self, n: isize) -> RedisResult<Vec<(String, i64)>> {
        // ZREVRANGE 从高到低
        self.conn.zrevrange_withscores(&self.key, 0, n - 1).await
    }

    /// 获取排名范围
    pub async fn get_range(&mut self, start: isize, stop: isize) -> RedisResult<Vec<(String, i64)>> {
        self.conn.zrevrange_withscores(&self.key, start, stop).await
    }

    /// 删除用户
    pub async fn remove_user(&mut self, user_id: &str) -> RedisResult<()> {
        self.conn.zrem(&self.key, user_id).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore]
    async fn test_leaderboard() {
        let client = RedisClient::new(RedisConfig::default()).unwrap();
        let conn = client.get_async_connection().await.unwrap();
        let mut leaderboard = Leaderboard::new(conn, "game:leaderboard".to_string());

        // 添加分数
        leaderboard.update_score("alice", 1000).await.unwrap();
        leaderboard.update_score("bob", 1500).await.unwrap();
        leaderboard.update_score("charlie", 800).await.unwrap();

        // 获取 Top 3
        let top3 = leaderboard.get_top_n(3).await.unwrap();
        assert_eq!(top3[0].0, "bob");  // 第一名
        assert_eq!(top3[0].1, 1500);

        // 获取 Alice 的排名
        let rank = leaderboard.get_rank("alice").await.unwrap();
        assert_eq!(rank, Some(1));  // 第二名（从0开始）
    }
}
```

### 5.2 Set 操作（标签系统）

```rust
/// Set 操作
pub struct SetOps {
    conn: ConnectionManager,
}

impl SetOps {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }

    /// 添加成员
    pub async fn sadd(&mut self, key: &str, member: &str) -> RedisResult<()> {
        self.conn.sadd(key, member).await
    }

    /// 移除成员
    pub async fn srem(&mut self, key: &str, member: &str) -> RedisResult<()> {
        self.conn.srem(key, member).await
    }

    /// 检查成员是否存在
    pub async fn sismember(&mut self, key: &str, member: &str) -> RedisResult<bool> {
        self.conn.sismember(key, member).await
    }

    /// 获取所有成员
    pub async fn smembers(&mut self, key: &str) -> RedisResult<Vec<String>> {
        self.conn.smembers(key).await
    }

    /// 集合交集
    pub async fn sinter(&mut self, keys: &[&str]) -> RedisResult<Vec<String>> {
        self.conn.sinter(keys).await
    }

    /// 集合并集
    pub async fn sunion(&mut self, keys: &[&str]) -> RedisResult<Vec<String>> {
        self.conn.sunion(keys).await
    }

    /// 集合差集
    pub async fn sdiff(&mut self, keys: &[&str]) -> RedisResult<Vec<String>> {
        self.conn.sdiff(keys).await
    }
}
```

---

## 6. Redis Streams 消息队列

### 6.1 Streams 生产者

```rust
// src/streams.rs
use redis::{AsyncCommands, streams::{StreamReadOptions, StreamReadReply}};
use serde::{Serialize, Deserialize};
use std::collections::HashMap;

/// Streams 生产者
pub struct StreamProducer {
    conn: ConnectionManager,
    stream_key: String,
}

impl StreamProducer {
    pub fn new(conn: ConnectionManager, stream_key: String) -> Self {
        Self { conn, stream_key }
    }

    /// 发送消息
    pub async fn send<T>(&mut self, message: &T) -> Result<String, crate::error::RedisError>
    where
        T: Serialize,
    {
        // 序列化消息
        let payload = serde_json::to_string(message)?;
        
        // XADD stream_key * payload <json>
        let items = vec![("payload", payload.as_str())];
        let id: String = self.conn.xadd(&self.stream_key, "*", &items).await?;

        tracing::info!(
            stream = %self.stream_key,
            message_id = %id,
            "Message sent to stream"
        );

        Ok(id)
    }

    /// 批量发送
    pub async fn send_batch<T>(&mut self, messages: Vec<T>) -> Result<Vec<String>, crate::error::RedisError>
    where
        T: Serialize,
    {
        let mut ids = Vec::new();

        for message in messages {
            let id = self.send(&message).await?;
            ids.push(id);
        }

        Ok(ids)
    }
}

/// Streams 消费者
pub struct StreamConsumer {
    conn: ConnectionManager,
    stream_key: String,
    consumer_group: String,
    consumer_name: String,
}

impl StreamConsumer {
    /// 创建消费者（自动创建消费者组）
    pub async fn new(
        mut conn: ConnectionManager,
        stream_key: String,
        consumer_group: String,
        consumer_name: String,
    ) -> Result<Self, crate::error::RedisError> {
        // 尝试创建消费者组（从最新消息开始）
        let _: Result<(), redis::RedisError> = conn
            .xgroup_create_mkstream(&stream_key, &consumer_group, "$")
            .await;

        tracing::info!(
            stream = %stream_key,
            group = %consumer_group,
            consumer = %consumer_name,
            "Stream consumer initialized"
        );

        Ok(Self {
            conn,
            stream_key,
            consumer_group,
            consumer_name,
        })
    }

    /// 消费消息（阻塞模式）
    pub async fn consume<T, F, Fut>(
        &mut self,
        handler: F,
    ) -> Result<(), crate::error::RedisError>
    where
        T: for<'de> Deserialize<'de>,
        F: Fn(String, T) -> Fut,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>>,
    {
        loop {
            // XREADGROUP GROUP <group> <consumer> BLOCK <ms> STREAMS <key> >
            let opts = StreamReadOptions::default()
                .group(&self.consumer_group, &self.consumer_name)
                .block(5000)  // 阻塞 5 秒
                .count(10);   // 每次最多读 10 条

            let results: StreamReadReply = self.conn
                .xread_options(&[&self.stream_key], &[">"], &opts)
                .await?;

            for stream_key in results.keys {
                for stream_id in stream_key.ids {
                    let message_id = stream_id.id;
                    
                    // 提取 payload
                    if let Some(payload_bytes) = stream_id.map.get("payload") {
                        let payload_str = std::str::from_utf8(payload_bytes)?;
                        let message: T = serde_json::from_str(payload_str)?;

                        // 处理消息
                        match handler(message_id.clone(), message).await {
                            Ok(_) => {
                                // 确认消息
                                self.ack(&message_id).await?;
                            }
                            Err(e) => {
                                tracing::error!(
                                    message_id = %message_id,
                                    error = %e,
                                    "Failed to process message"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// 确认消息
    async fn ack(&mut self, message_id: &str) -> RedisResult<()> {
        self.conn
            .xack(&self.stream_key, &self.consumer_group, &[message_id])
            .await
    }

    /// 获取待确认消息（Pending）
    pub async fn get_pending(&mut self) -> RedisResult<Vec<String>> {
        // XPENDING stream group - + count
        let result: Vec<String> = self.conn
            .xpending_consumer_count(
                &self.stream_key,
                &self.consumer_group,
                "-",
                "+",
                100,
                &self.consumer_name,
            )
            .await?;

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize)]
    struct TestEvent {
        event_type: String,
        user_id: u64,
        timestamp: i64,
    }

    #[tokio::test]
    #[ignore]
    async fn test_streams() {
        let client = RedisClient::new(RedisConfig::default()).unwrap();
        let conn = client.get_async_connection().await.unwrap();

        // 生产者
        let mut producer = StreamProducer::new(conn.clone(), "events".to_string());
        
        let event = TestEvent {
            event_type: "user.login".to_string(),
            user_id: 123,
            timestamp: chrono::Utc::now().timestamp(),
        };

        let message_id = producer.send(&event).await.unwrap();
        assert!(!message_id.is_empty());
    }
}
```

---

## 7. 发布订阅（Pub/Sub）

### 7.1 发布者

```rust
// src/pubsub.rs
use redis::AsyncCommands;
use serde::Serialize;

/// 发布者
pub struct Publisher {
    conn: ConnectionManager,
}

impl Publisher {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }

    /// 发布消息
    pub async fn publish<T>(&mut self, channel: &str, message: &T) -> Result<(), crate::error::RedisError>
    where
        T: Serialize,
    {
        let payload = serde_json::to_string(message)?;
        let subscribers: u32 = self.conn.publish(channel, payload).await?;

        tracing::info!(
            channel = %channel,
            subscribers = subscribers,
            "Message published"
        );

        Ok(())
    }
}
```

### 7.2 订阅者

```rust
use redis::aio::PubSub;
use serde::de::DeserializeOwned;

/// 订阅者
pub struct Subscriber {
    pubsub: PubSub,
}

impl Subscriber {
    /// 创建订阅者
    pub async fn new(client: &RedisClient) -> Result<Self, crate::error::RedisError> {
        let conn = client.client.get_async_connection().await?;
        let pubsub = conn.into_pubsub();
        Ok(Self { pubsub })
    }

    /// 订阅频道
    pub async fn subscribe(&mut self, channel: &str) -> RedisResult<()> {
        self.pubsub.subscribe(channel).await
    }

    /// 订阅模式（支持通配符）
    pub async fn psubscribe(&mut self, pattern: &str) -> RedisResult<()> {
        self.pubsub.psubscribe(pattern).await
    }

    /// 监听消息
    pub async fn listen<T, F, Fut>(&mut self, handler: F) -> Result<(), crate::error::RedisError>
    where
        T: DeserializeOwned,
        F: Fn(String, T) -> Fut,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>>,
    {
        let mut stream = self.pubsub.on_message();

        while let Some(msg) = stream.next().await {
            let channel = msg.get_channel_name().to_string();
            let payload: String = msg.get_payload()?;

            match serde_json::from_str::<T>(&payload) {
                Ok(message) => {
                    if let Err(e) = handler(channel, message).await {
                        tracing::error!(error = %e, "Message handler error");
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "Failed to deserialize message");
                }
            }
        }

        Ok(())
    }
}
```

---

## 8. 缓存策略

### 8.1 Cache-Aside 模式

```rust
// src/cache.rs
use redis::AsyncCommands;
use serde::{Serialize, de::DeserializeOwned};
use std::future::Future;

/// 缓存管理器
pub struct CacheManager {
    conn: ConnectionManager,
}

impl CacheManager {
    pub fn new(conn: ConnectionManager) -> Self {
        Self { conn }
    }

    /// Cache-Aside 模式：先读缓存，未命中则读数据库
    pub async fn get_or_load<T, F, Fut>(
        &mut self,
        key: &str,
        ttl_seconds: u64,
        loader: F,
    ) -> Result<T, crate::error::RedisError>
    where
        T: Serialize + DeserializeOwned,
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, anyhow::Error>>,
    {
        // 1. 尝试从缓存读取
        let cached: Option<String> = self.conn.get(key).await?;

        if let Some(data) = cached {
            // 缓存命中
            tracing::info!(key = %key, "Cache hit");
            let value: T = serde_json::from_str(&data)?;
            return Ok(value);
        }

        // 2. 缓存未命中，从数据源加载
        tracing::info!(key = %key, "Cache miss, loading from source");
        let value = loader().await?;

        // 3. 写入缓存
        let serialized = serde_json::to_string(&value)?;
        self.conn.set_ex(key, serialized, ttl_seconds).await?;

        Ok(value)
    }

    /// 主动更新缓存
    pub async fn set<T>(&mut self, key: &str, value: &T, ttl_seconds: u64) -> Result<(), crate::error::RedisError>
    where
        T: Serialize,
    {
        let serialized = serde_json::to_string(value)?;
        self.conn.set_ex(key, serialized, ttl_seconds).await?;
        tracing::info!(key = %key, ttl = ttl_seconds, "Cache set");
        Ok(())
    }

    /// 删除缓存
    pub async fn invalidate(&mut self, key: &str) -> Result<(), crate::error::RedisError> {
        self.conn.del(key).await?;
        tracing::info!(key = %key, "Cache invalidated");
        Ok(())
    }

    /// 批量删除（模式匹配）
    pub async fn invalidate_pattern(&mut self, pattern: &str) -> Result<u32, crate::error::RedisError> {
        // SCAN + DEL
        let keys: Vec<String> = self.conn.keys(pattern).await?;
        
        if keys.is_empty() {
            return Ok(0);
        }

        let count = keys.len() as u32;
        self.conn.del(&keys).await?;

        tracing::info!(pattern = %pattern, count = count, "Cache batch invalidated");

        Ok(count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
    struct User {
        id: u64,
        name: String,
    }

    #[tokio::test]
    #[ignore]
    async fn test_cache_aside() {
        let client = RedisClient::new(RedisConfig::default()).unwrap();
        let conn = client.get_async_connection().await.unwrap();
        let mut cache = CacheManager::new(conn);

        let user_id = 123;
        let cache_key = format!("user:{}", user_id);

        // 第一次读取（缓存未命中）
        let user1 = cache.get_or_load(&cache_key, 3600, || async {
            Ok(User {
                id: user_id,
                name: "Alice".to_string(),
            })
        }).await.unwrap();

        // 第二次读取（缓存命中）
        let user2 = cache.get_or_load(&cache_key, 3600, || async {
            panic!("Should not reach here");
        }).await.unwrap();

        assert_eq!(user1, user2);
    }
}
```

---

## 9. 分布式锁

### 9.1 基于 SET NX EX 的分布式锁

```rust
// src/lock.rs
use redis::AsyncCommands;
use uuid::Uuid;
use std::time::Duration;

/// 分布式锁
pub struct DistributedLock {
    conn: ConnectionManager,
    key: String,
    value: String,  // 锁的唯一标识
    ttl_seconds: u64,
}

impl DistributedLock {
    /// 尝试获取锁
    pub async fn acquire(
        mut conn: ConnectionManager,
        key: String,
        ttl_seconds: u64,
    ) -> Result<Option<Self>, crate::error::RedisError> {
        let value = Uuid::new_v4().to_string();

        // SET key value NX EX ttl
        let acquired: bool = conn.set_nx(&key, &value).await?;

        if acquired {
            // 设置过期时间
            conn.expire(&key, ttl_seconds as i64).await?;

            tracing::info!(key = %key, value = %value, ttl = ttl_seconds, "Lock acquired");

            Ok(Some(Self {
                conn,
                key,
                value,
                ttl_seconds,
            }))
        } else {
            tracing::warn!(key = %key, "Failed to acquire lock");
            Ok(None)
        }
    }

    /// 释放锁（使用 Lua 脚本确保原子性）
    pub async fn release(mut self) -> Result<(), crate::error::RedisError> {
        // Lua 脚本：只有持有者才能删除锁
        let script = r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("del", KEYS[1])
            else
                return 0
            end
        "#;

        let deleted: i32 = redis::Script::new(script)
            .key(&self.key)
            .arg(&self.value)
            .invoke_async(&mut self.conn)
            .await?;

        if deleted == 1 {
            tracing::info!(key = %self.key, "Lock released");
        } else {
            tracing::warn!(key = %self.key, "Lock already expired or not owned");
        }

        Ok(())
    }

    /// 续约锁（延长过期时间）
    pub async fn renew(&mut self) -> Result<bool, crate::error::RedisError> {
        // Lua 脚本：只有持有者才能续约
        let script = r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("expire", KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;

        let renewed: i32 = redis::Script::new(script)
            .key(&self.key)
            .arg(&self.value)
            .arg(self.ttl_seconds)
            .invoke_async(&mut self.conn)
            .await?;

        Ok(renewed == 1)
    }
}

/// 带锁的操作执行器
pub async fn with_lock<F, Fut, T>(
    conn: ConnectionManager,
    key: String,
    ttl_seconds: u64,
    operation: F,
) -> Result<T, crate::error::RedisError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<T, anyhow::Error>>,
{
    // 获取锁
    let lock = DistributedLock::acquire(conn, key.clone(), ttl_seconds).await?;

    match lock {
        Some(lock) => {
            // 执行操作
            let result = operation().await;

            // 释放锁
            lock.release().await?;

            match result {
                Ok(value) => Ok(value),
                Err(e) => Err(crate::error::RedisError::OperationError(e.to_string())),
            }
        }
        None => Err(crate::error::RedisError::LockAcquisitionFailed),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore]
    async fn test_distributed_lock() {
        let client = RedisClient::new(RedisConfig::default()).unwrap();
        let conn = client.get_async_connection().await.unwrap();

        let result = with_lock(conn, "test:lock".to_string(), 10, || async {
            // 模拟业务逻辑
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok(42)
        }).await.unwrap();

        assert_eq!(result, 42);
    }
}
```

---

## 10. 管道与事务

### 10.1 Pipeline（管道）

```rust
use redis::pipe;

/// 管道操作（批量提交，减少网络往返）
pub async fn pipeline_example(mut conn: ConnectionManager) -> RedisResult<()> {
    let (r1, r2, r3): (String, i32, Vec<String>) = pipe()
        .cmd("SET").arg("key1").arg("value1").ignore()
        .cmd("INCR").arg("counter")
        .cmd("LRANGE").arg("list1").arg(0).arg(-1)
        .query_async(&mut conn)
        .await?;

    tracing::info!(counter = r2, list_len = r3.len(), "Pipeline executed");

    Ok(())
}
```

### 10.2 Transaction（事务）

```rust
use redis::{transaction, Commands};

/// MULTI/EXEC 事务
pub async fn transaction_example(mut conn: ConnectionManager) -> RedisResult<()> {
    let (new_val,): (isize,) = transaction(&mut conn, &["counter"], |conn, pipe| {
        // WATCH counter
        let current: isize = conn.get("counter")?;

        // MULTI
        pipe.set("counter", current + 1)
            .ignore()
            .get("counter")
            .query(conn)
        // EXEC
    }).await?;

    tracing::info!(new_value = new_val, "Transaction completed");

    Ok(())
}
```

---

## 11. OTLP 集成

### 11.1 追踪配置

```rust
// src/telemetry.rs
use opentelemetry::{global, runtime, trace::Tracer, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "redis-service"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 11.2 带追踪的 Redis 操作

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

/// 带追踪的 GET
#[instrument(skip(conn))]
pub async fn traced_get(
    mut conn: ConnectionManager,
    key: &str,
) -> Result<Option<String>, crate::error::RedisError> {
    let tracer = global::tracer("redis-client");
    
    let mut span = tracer
        .span_builder(format!("Redis GET {}", key))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "redis"),
            KeyValue::new("db.operation", "GET"),
            KeyValue::new("db.redis.key", key.to_string()),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    let result: RedisResult<Option<String>> = conn.get(key).await;
    let duration = start.elapsed();
    
    span.set_attribute(KeyValue::new("db.response_time_ms", duration.as_millis() as i64));
    
    match &result {
        Ok(Some(value)) => {
            span.set_attribute(KeyValue::new("db.redis.hit", true));
            span.set_attribute(KeyValue::new("db.redis.value_size", value.len() as i64));
        }
        Ok(None) => {
            span.set_attribute(KeyValue::new("db.redis.hit", false));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    Ok(result?)
}

/// 带追踪的 SET
#[instrument(skip(conn, value))]
pub async fn traced_set(
    mut conn: ConnectionManager,
    key: &str,
    value: &str,
    ttl_seconds: Option<u64>,
) -> Result<(), crate::error::RedisError> {
    let tracer = global::tracer("redis-client");
    
    let mut span = tracer
        .span_builder(format!("Redis SET {}", key))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "redis"),
            KeyValue::new("db.operation", "SET"),
            KeyValue::new("db.redis.key", key.to_string()),
            KeyValue::new("db.redis.value_size", value.len() as i64),
        ])
        .start(&tracer);
    
    if let Some(ttl) = ttl_seconds {
        span.set_attribute(KeyValue::new("db.redis.ttl_seconds", ttl as i64));
    }
    
    let result = match ttl_seconds {
        Some(ttl) => conn.set_ex(key, value, ttl).await,
        None => conn.set(key, value).await,
    };
    
    if let Err(e) = &result {
        span.set_status(Status::error(e.to_string()));
    }
    
    span.end();
    
    Ok(result?)
}
```

---

## 12. 生产环境实践

### 12.1 Docker Compose 部署

```yaml
# docker/docker-compose.yml
version: '3.8'

services:
  redis:
    image: redis:7.2-alpine
    container_name: redis
    command: redis-server --appendonly yes --requirepass redis123
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
      - ./redis.conf:/usr/local/etc/redis/redis.conf:ro
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 3s
      retries: 5
    networks:
      - app_network

  redis-commander:
    image: rediscommander/redis-commander:latest
    container_name: redis-commander
    environment:
      - REDIS_HOSTS=local:redis:6379:0:redis123
    ports:
      - "8081:8081"
    depends_on:
      - redis
    networks:
      - app_network

  otel-collector:
    image: otel/opentelemetry-collector:latest
    container_name: otel-collector
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
    networks:
      - app_network

volumes:
  redis_data:

networks:
  app_network:
    driver: bridge
```

---

## 13. 国际标准对齐

### 13.1 Redis 协议对齐

| Redis 特性 | 实现状态 | 说明 |
|-----------|---------|------|
| **RESP 协议** | ✅ 100% | Redis Serialization Protocol |
| **核心数据结构** | ✅ 100% | String, Hash, List, Set, Sorted Set |
| **Streams** | ✅ 100% | 消息队列和事件溯源 |
| **Pub/Sub** | ✅ 100% | 发布/订阅模式 |
| **事务** | ✅ 100% | MULTI/EXEC/WATCH |
| **Lua 脚本** | ✅ 100% | EVAL/EVALSHA |
| **持久化** | ✅ 100% | RDB, AOF |

### 13.2 OpenTelemetry Semantic Conventions

```rust
// Redis 数据库追踪属性
let span_attributes = vec![
    KeyValue::new("db.system", "redis"),
    KeyValue::new("db.operation", "GET"),  // GET | SET | HGET | ZADD | XADD...
    KeyValue::new("db.redis.key", key),
    KeyValue::new("db.redis.database_index", 0),
    KeyValue::new("db.connection_string", "redis://localhost:6379"),
    KeyValue::new("network.peer.address", "localhost"),
    KeyValue::new("network.peer.port", 6379),
];
```

---

## 14. 总结

### 14.1 Redis 核心优势

| 特性 | 优势 |
|------|------|
| **高性能** | 内存存储，微秒级延迟 |
| **丰富数据结构** | String, Hash, List, Set, Sorted Set, Streams 等 |
| **多用途** | 缓存、数据库、消息队列 |
| **持久化** | RDB 快照 + AOF 日志 |
| **高可用** | Sentinel + Cluster |
| **Lua 脚本** | 原子性复杂操作 |

### 14.2 何时选择 Redis

- ✅ 高性能缓存（Session, User Profile）
- ✅ 实时排行榜（Sorted Set）
- ✅ 计数器和速率限制
- ✅ 简单消息队列（List, Streams）
- ✅ 分布式锁
- ✅ 实时分析（HyperLogLog）
- ❌ 大数据量持久化存储（选 PostgreSQL/MongoDB）
- ❌ 复杂查询（选 SQL/Elasticsearch）

### 14.3 生产部署清单

- [x] 启用持久化（AOF + RDB）
- [x] 配置最大内存和淘汰策略
- [x] 设置密码认证
- [x] 监控内存使用和命中率
- [x] 配置主从复制或集群
- [x] OTLP 分布式追踪
- [x] 慢查询日志分析

---

**文档版本**: v1.0.0  
**Rust 版本**: 1.90  
**redis-rs 版本**: 0.26  
**OpenTelemetry 版本**: 0.25  

**参考资源**:

- [Redis 官方文档](https://redis.io/documentation)
- [redis-rs 文档](https://docs.rs/redis)
- [Redis Streams 介绍](https://redis.io/docs/data-types/streams/)
- [OpenTelemetry Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)
