# C11 开发库: 术语表 (Glossary)

**版本**: 1.2.0
**最后更新**: 2025年10月27日
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)
**状态**: 🟢 活跃维护

> **简介**: C11开发库核心术语快速参考，帮助您理解中间件核心概念和Rust 1.92+特性。

---

## 📋 目录

- [C11 开发库: 术语表 (Glossary)](#c11-开发库-术语表-glossary)
  - [📋 目录](#-目录)
  - [术语索引](#术语索引)
  - [📖 数据库相关](#-数据库相关)
    - [1.1 SQL](#11-sql)
    - [1.2 ORM](#12-orm)
    - [1.3 连接池 (Connection Pool)](#13-连接池-connection-pool)
  - [📝 缓存相关](#-缓存相关)
    - [2.1 Redis](#21-redis)
    - [2.2 Pipeline](#22-pipeline)
    - [2.3 Pub/Sub](#23-pubsub)
  - [🔍 消息队列相关](#-消息队列相关)
    - [3.1 Kafka](#31-kafka)
    - [3.2 MQTT](#32-mqtt)
    - [3.3 NATS](#33-nats)
  - [🔧 HTTP中间件](#-http中间件)
    - [4.1 Pingora](#41-pingora)
    - [4.2 反向代理 (Reverse Proxy)](#42-反向代理-reverse-proxy)
  - [⚡ 性能与可观测](#-性能与可观测)
    - [5.1 连接复用](#51-连接复用)
    - [5.2 Tracing](#52-tracing)
  - [🌟 Rust特性](#-rust特性)
    - [6.1 async fn in trait](#61-async-fn-in-trait)
    - [6.2 RPITIT](#62-rpitit)
  - [🔬 相关资源](#-相关资源)
    - [7.1 核心文档](#71-核心文档)
    - [7.2 专题指南](#72-专题指南)
    - [7.3 Rust 1.92特性](#73-rust-192特性)
    - [7.4 实践资源](#74-实践资源)

---

## 术语索引

[C](#连接池-connection-pool) | [K](#kafka) | [M](#mqtt) | [O](#orm) | [P](#pipeline) | [R](#redis) | [S](#sql)

---

## 📖 数据库相关

### 1.1 SQL

**定义**: Structured Query Language，结构化查询语言，用于管理关系数据库。

**Rust支持**:

- PostgreSQL: `tokio-postgres`, `sqlx`
- MySQL: `mysql_async`, `sqlx`
- SQLite: `rusqlite`, `sqlx`

**相关**: [sql.md](./sql.md)

---

### 1.2 ORM

**定义**: Object-Relational Mapping，对象关系映射，将数据库表映射为对象。

**Rust ORM**:

- `Diesel`: 类型安全ORM
- `SeaORM`: 异步ORM
- `sqlx`: 编译时SQL检查（非ORM）

**相关**: [sql.md](./sql.md)

---

### 1.3 连接池 (Connection Pool)

**定义**: 预先创建并维护一组数据库连接，避免频繁建立连接的开销。

**Rust实现**:

- `deadpool`: 通用连接池
- `bb8`: 异步连接池
- `r2d2`: 同步连接池

**配置**:

```rust
Pool::builder(manager)
    .max_size(16)
    .build()?
```

**相关**: [sql.md](./sql.md), [redis.md](./redis.md)

---

## 📝 缓存相关

### 2.1 Redis

**定义**: Remote Dictionary Server，开源的内存数据结构存储，用作数据库、缓存和消息代理。

**数据结构**:

- String: 字符串
- Hash: 哈希表
- List: 列表
- Set: 集合
- Sorted Set: 有序集合

**Rust驱动**: `redis`

**相关**: [redis.md](./redis.md)

---

### 2.2 Pipeline

**定义**: Redis批量操作模式，一次性发送多个命令，减少网络往返。

**示例**:

```rust
use redis::pipe;

let mut pipe = pipe();
pipe.set("key1", "value1");
pipe.set("key2", "value2");
pipe.get("key1");
let results: Vec<String> = pipe.query_async(conn).await?;
```

**性能**: 可提升 10-100倍

**相关**: [redis.md](./redis.md)

---

### 2.3 Pub/Sub

**定义**: 发布/订阅模式，消息生产者发布到频道，订阅者接收消息。

**Redis Pub/Sub**:

```rust
let mut pubsub = client.get_async_connection().await?.into_pubsub();
pubsub.subscribe("channel").await?;

while let Some(msg) = pubsub.on_message().next().await {
    let payload: String = msg.get_payload()?;
    println!("Received: {}", payload);
}
```

**相关**: [redis.md](./redis.md)

---

## 🔍 消息队列相关

### 3.1 Kafka

**定义**: 分布式流处理平台，高吞吐量、持久化的消息队列。

**核心概念**:

- Topic: 主题/队列
- Partition: 分区
- Producer: 生产者
- Consumer: 消费者
- Consumer Group: 消费者组

**Rust驱动**: `rdkafka`

**相关**: [kafka_pingora.md](./kafka_pingora.md)

---

### 3.2 MQTT

**定义**: Message Queuing Telemetry Transport，轻量级消息传输协议，适用于IoT。

**QoS级别**:

- QoS 0: 至多一次
- QoS 1: 至少一次
- QoS 2: 恰好一次

**Rust驱动**: `rumqttc`

**相关**: [mq.md](./mq.md)

---

### 3.3 NATS

**定义**: 高性能云原生消息系统，低延迟、简单易用。

**特点**:

- 发布/订阅
- 请求/响应
- 队列订阅
- JetStream（持久化）

**Rust驱动**: `async-nats`

**相关**: [mq.md](./mq.md)

---

## 🔧 HTTP中间件

### 4.1 Pingora

**定义**: Cloudflare开源的HTTP代理框架，Rust实现。

**功能**:

- 反向代理
- 负载均衡
- HTTP缓存
- TLS终止

**相关**: [pingora.md](./pingora.md)

---

### 4.2 反向代理 (Reverse Proxy)

**定义**: 代理服务器接收客户端请求，转发给后端服务器。

**用途**:

- 负载均衡
- 缓存
- SSL终止
- 安全过滤

**相关**: [pingora.md](./pingora.md)

---

## ⚡ 性能与可观测

### 5.1 连接复用

**定义**: 复用已建立的连接，避免重复建立连接的开销。

**HTTP**: Keep-Alive
**数据库**: 连接池
**Redis**: ConnectionManager

---

### 5.2 Tracing

**定义**: 分布式追踪，记录请求在系统中的流转路径。

**Rust实现**: `tracing` crate

```rust
use tracing::{info, instrument};

#[instrument]
async fn query_database(id: i32) -> Result<User> {
    info!("Querying user {}", id);
    // ...
}
```

**相关**: 启用 `obs` 特性

---

## 🌟 Rust特性

### 6.1 async fn in trait

**定义**: Rust 1.92+ 特性，允许trait方法为async fn。

**示例**:

```rust
trait AsyncDatabase {
    async fn query(&self, sql: &str) -> Result<Vec<Row>>;
}
```

**相关**: [RUST_192_FEATURES_GUIDE.md](./RUST_192_FEATURES_GUIDE.md)

---

### 6.2 RPITIT

**定义**: Return Position Impl Trait in Trait，trait方法返回 `impl Trait`。

**示例**:

```rust
trait Config {
    fn builder() -> impl ConfigBuilder;
}
```

**相关**: [RUST_192_FEATURES_GUIDE.md](./RUST_192_FEATURES_GUIDE.md)

---

## 🔬 相关资源

### 7.1 核心文档

- [00_MASTER_INDEX.md](./00_MASTER_INDEX.md) - 完整文档导航
- [README.md](./README.md) - 项目概述
- [FAQ.md](./FAQ.md) - 常见问题解答

### 7.2 专题指南

- [guides/sql.md](./guides/sql.md) - SQL数据库详细指南
- [guides/redis.md](./guides/redis.md) - Redis缓存详细指南
- [guides/mq.md](./guides/mq.md) - 消息队列详细指南
- [guides/pingora.md](./guides/pingora.md) - HTTP代理详细指南

### 7.3 Rust 1.92特性

- [references/RUST_192_FEATURES_GUIDE.md](./references/RUST_192_FEATURES_GUIDE.md) - Rust 1.92 特性完整指南

### 7.4 实践资源

- [examples/](../examples/) - 示例代码
- [tests/](../tests/) - 测试用例
- [src/](../src/) - 源码实现

---

**版本**: 1.2.0
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)
**最后更新**: 2025年10月27日
**维护者**: C11 Libraries Team
**反馈**: [提交 Issue](https://github.com/your-org/your-repo/issues)

---

> **提示**: 本术语表持续更新中，新术语和概念会不断添加！🦀✨
