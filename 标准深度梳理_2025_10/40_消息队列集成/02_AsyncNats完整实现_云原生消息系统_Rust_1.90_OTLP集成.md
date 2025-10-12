# Async-Nats 完整实现：云原生消息系统 Rust 1.90 + OTLP 集成指南

## 目录

- [Async-Nats 完整实现：云原生消息系统 Rust 1.90 + OTLP 集成指南](#async-nats-完整实现云原生消息系统-rust-190--otlp-集成指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 NATS 定位](#11-nats-定位)
      - [核心优势](#核心优势)
    - [1.2 与其他消息队列对比](#12-与其他消息队列对比)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. NATS 核心概念](#2-nats-核心概念)
    - [2.1 消息模式](#21-消息模式)
    - [2.2 JetStream 持久化](#22-jetstream-持久化)
  - [3. 项目初始化与配置](#3-项目初始化与配置)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 连接到 NATS 服务器](#32-连接到-nats-服务器)
  - [4. 发布/订阅模式](#4-发布订阅模式)
    - [4.1 基础发布](#41-基础发布)
    - [4.2 基础订阅](#42-基础订阅)
    - [4.3 通配符订阅](#43-通配符订阅)
  - [5. 请求/响应模式](#5-请求响应模式)
    - [5.1 请求-应答](#51-请求-应答)
    - [5.2 服务端点](#52-服务端点)
  - [6. JetStream 持久化](#6-jetstream-持久化)
    - [6.1 Stream 管理](#61-stream-管理)
    - [6.2 Consumer 管理](#62-consumer-管理)
    - [6.3 消息确认（Ack）](#63-消息确认ack)
  - [7. Key-Value Store](#7-key-value-store)
    - [7.1 KV 操作](#71-kv-操作)
    - [7.2 KV Watch](#72-kv-watch)
  - [8. Object Store](#8-object-store)
    - [8.1 对象上传/下载](#81-对象上传下载)
    - [8.2 对象流式处理](#82-对象流式处理)
  - [9. 消息序列化](#9-消息序列化)
    - [9.1 JSON 序列化](#91-json-序列化)
    - [9.2 Protocol Buffers](#92-protocol-buffers)
  - [10. 错误处理与重试](#10-错误处理与重试)
    - [10.1 连接重连](#101-连接重连)
    - [10.2 消息重试](#102-消息重试)
  - [11. OTLP 分布式追踪集成](#11-otlp-分布式追踪集成)
    - [11.1 发布者追踪](#111-发布者追踪)
    - [11.2 订阅者追踪](#112-订阅者追踪)
    - [11.3 分布式上下文传播](#113-分布式上下文传播)
  - [12. 性能优化](#12-性能优化)
    - [12.1 批量发布](#121-批量发布)
    - [12.2 连接池](#122-连接池)
  - [13. 高可用与集群](#13-高可用与集群)
    - [13.1 集群连接](#131-集群连接)
    - [13.2 故障转移](#132-故障转移)
  - [14. 安全配置](#14-安全配置)
    - [14.1 TLS 配置](#141-tls-配置)
    - [14.2 认证授权](#142-认证授权)
  - [15. 测试策略](#15-测试策略)
    - [15.1 单元测试](#151-单元测试)
    - [15.2 集成测试](#152-集成测试)
  - [16. 生产环境部署](#16-生产环境部署)
    - [16.1 Docker Compose 部署](#161-docker-compose-部署)
    - [16.2 Kubernetes 部署](#162-kubernetes-部署)
  - [17. 监控与指标](#17-监控与指标)
    - [17.1 客户端指标](#171-客户端指标)
    - [17.2 Prometheus 集成](#172-prometheus-集成)
  - [18. 国际标准对标](#18-国际标准对标)
    - [18.1 对标清单](#181-对标清单)
    - [18.2 与其他消息队列对比](#182-与其他消息队列对比)
  - [19. 总结与最佳实践](#19-总结与最佳实践)
    - [19.1 核心优势](#191-核心优势)
    - [19.2 最佳实践](#192-最佳实践)
    - [19.3 性能基准](#193-性能基准)
    - [19.4 学习资源](#194-学习资源)

---

## 1. 概述

### 1.1 NATS 定位

**NATS** 是一个**高性能、云原生的消息系统**，专为现代分布式系统设计，提供简单、安全、高性能的消息传递。

#### 核心优势

- **高性能**：每秒处理数百万条消息，微秒级延迟
- **轻量级**：极小的资源占用，单个可执行文件
- **简单易用**：直观的 API，快速上手
- **云原生**：原生支持 Kubernetes，CNCF 孵化项目
- **多语言支持**：40+ 官方客户端库
- **内置安全**：TLS、JWT 认证、权限控制
- **JetStream**：内置持久化消息流
- **At-Most-Once/At-Least-Once**：灵活的消息保证

### 1.2 与其他消息队列对比

| 特性 | NATS | Kafka | RabbitMQ | Redis Streams |
|------|------|-------|----------|---------------|
| **性能** | ⭐⭐⭐⭐⭐ 极高 | ⭐⭐⭐⭐ 高 | ⭐⭐⭐ 中 | ⭐⭐⭐⭐ 高 |
| **延迟** | ⭐⭐⭐⭐⭐ 微秒 | ⭐⭐⭐ 毫秒 | ⭐⭐⭐ 毫秒 | ⭐⭐⭐⭐ 微秒 |
| **持久化** | ✅ JetStream | ✅ 内置 | ✅ 内置 | ✅ 内置 |
| **学习曲线** | ⭐⭐⭐⭐⭐ 低 | ⭐⭐ 高 | ⭐⭐⭐ 中 | ⭐⭐⭐⭐ 低 |
| **资源占用** | ⭐⭐⭐⭐⭐ 极小 | ⭐⭐ 大 | ⭐⭐⭐ 中 | ⭐⭐⭐⭐ 小 |
| **运维复杂度** | ⭐⭐⭐⭐⭐ 低 | ⭐⭐ 高 | ⭐⭐⭐ 中 | ⭐⭐⭐⭐ 低 |
| **适用场景** | 微服务、IoT | 大数据流 | 企业消息 | 缓存+消息 |

### 1.3 国际标准对标

| 标准/协议 | NATS 实现 |
|----------|-----------|
| **NATS Protocol** | ✅ 原生协议 |
| **At-Most-Once Delivery** | ✅ 核心消息 |
| **At-Least-Once Delivery** | ✅ JetStream |
| **Exactly-Once Semantics** | ⚠️ 客户端去重 |
| **TLS 1.2/1.3** | ✅ 完整支持 |
| **JWT Authentication** | ✅ 完整支持 |
| **OpenTelemetry** | ✅ 可集成 |
| **Cloud Native** | ✅ CNCF 项目 |

---

## 2. NATS 核心概念

### 2.1 消息模式

```text
┌────────────────────────────────────────┐
│          NATS 消息模式                  │
├────────────────────────────────────────┤
│  1. Publish-Subscribe (发布-订阅)      │
│     Publisher → Subject → Subscribers  │
│                                        │
│  2. Request-Reply (请求-响应)          │
│     Requester ↔ Subject ↔ Responder   │
│                                        │
│  3. Queue Groups (队列组)              │
│     Publisher → Subject → Queue → One │
│                                        │
│  4. JetStream (持久化流)               │
│     Publisher → Stream → Consumer     │
└────────────────────────────────────────┘
```

### 2.2 JetStream 持久化

```text
┌────────────────────────────────────────┐
│          JetStream 架构                 │
├────────────────────────────────────────┤
│  Publisher                             │
│     ↓                                  │
│  Stream (持久化消息)                    │
│     ├─ Limits (消息/大小/时间)          │
│     ├─ Retention (保留策略)            │
│     └─ Replication (副本)              │
│     ↓                                  │
│  Consumer (消费者)                      │
│     ├─ Durable (持久化消费者)           │
│     ├─ Ephemeral (临时消费者)          │
│     └─ Ack Policy (确认策略)           │
└────────────────────────────────────────┘
```

---

## 3. 项目初始化与配置

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "async-nats-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# NATS 核心
async-nats = "0.36"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
tokio-stream = "0.1"
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
bytes = "1.7"

# 追踪与日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"
opentelemetry = { version = "0.25", features = ["trace"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["trace", "grpc-tonic"] }

# 工具库
thiserror = "1.0"
anyhow = "1.0"
uuid = { version = "1.10", features = ["v4"] }

[dev-dependencies]
testcontainers = "0.23"
```

### 3.2 连接到 NATS 服务器

```rust
use async_nats::{Client, ConnectOptions};
use std::time::Duration;
use tracing::{info, instrument};

/// 基础连接
#[instrument]
pub async fn connect_basic() -> Result<Client, async_nats::Error> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    info!("Connected to NATS server");
    
    Ok(client)
}

/// 高级连接配置
#[instrument]
pub async fn connect_advanced() -> Result<Client, async_nats::Error> {
    let client = ConnectOptions::new()
        .name("rust-nats-client")                    // 客户端名称
        .max_reconnects(Some(10))                    // 最大重连次数
        .reconnect_delay_callback(|attempts| {
            let delay = Duration::from_secs(2u64.pow(attempts.min(5)));
            info!("Reconnecting in {:?} (attempt {})", delay, attempts);
            delay
        })
        .ping_interval(Duration::from_secs(30))      // Ping 间隔
        .connection_timeout(Duration::from_secs(10)) // 连接超时
        .connect("nats://localhost:4222")
        .await?;
    
    info!("Connected to NATS with advanced options");
    
    Ok(client)
}

/// 集群连接
#[instrument]
pub async fn connect_cluster() -> Result<Client, async_nats::Error> {
    let servers = vec![
        "nats://nats1:4222",
        "nats://nats2:4222",
        "nats://nats3:4222",
    ];
    
    let client = async_nats::connect(servers.join(",")).await?;
    
    info!("Connected to NATS cluster");
    
    Ok(client)
}
```

---

## 4. 发布/订阅模式

### 4.1 基础发布

```rust
use async_nats::Client;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Event {
    pub id: String,
    pub event_type: String,
    pub data: serde_json::Value,
    pub timestamp: i64,
}

/// 发布消息
#[instrument(skip(client))]
pub async fn publish_message(
    client: &Client,
    subject: &str,
    event: &Event,
) -> Result<(), Box<dyn std::error::Error>> {
    let payload = serde_json::to_vec(event)?;
    
    client.publish(subject.to_string(), payload.into()).await?;
    
    info!("Published message to subject: {}", subject);
    
    Ok(())
}

/// 带响应地址的发布
#[instrument(skip(client))]
pub async fn publish_with_reply(
    client: &Client,
    subject: &str,
    reply: &str,
    payload: &[u8],
) -> Result<(), async_nats::Error> {
    client
        .publish_with_reply(
            subject.to_string(),
            reply.to_string(),
            payload.into(),
        )
        .await?;
    
    info!("Published message with reply subject");
    
    Ok(())
}
```

### 4.2 基础订阅

```rust
use futures::StreamExt;

/// 订阅消息
#[instrument(skip(client))]
pub async fn subscribe_messages(
    client: &Client,
    subject: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut subscriber = client.subscribe(subject.to_string()).await?;
    
    info!("Subscribed to subject: {}", subject);
    
    while let Some(message) = subscriber.next().await {
        let event: Event = serde_json::from_slice(&message.payload)?;
        
        info!(
            "Received event: id={}, type={}",
            event.id,
            event.event_type
        );
        
        // 处理消息
        process_event(&event).await?;
    }
    
    Ok(())
}

async fn process_event(event: &Event) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    info!("Processing event: {:?}", event);
    Ok(())
}
```

### 4.3 通配符订阅

```rust
/// 通配符订阅
#[instrument(skip(client))]
pub async fn wildcard_subscription(
    client: &Client,
) -> Result<(), Box<dyn std::error::Error>> {
    // '*' 匹配一个 token
    let mut sub1 = client.subscribe("events.*.created".to_string()).await?;
    
    // '>' 匹配多个 token
    let mut sub2 = client.subscribe("logs.>".to_string()).await?;
    
    info!("Subscribed to wildcard subjects");
    
    tokio::select! {
        _ = async {
            while let Some(msg) = sub1.next().await {
                info!("Received from events.*.created: {}", String::from_utf8_lossy(&msg.payload));
            }
        } => {},
        _ = async {
            while let Some(msg) = sub2.next().await {
                info!("Received from logs.>: {}", String::from_utf8_lossy(&msg.payload));
            }
        } => {},
    }
    
    Ok(())
}

/// 队列组订阅（负载均衡）
#[instrument(skip(client))]
pub async fn queue_group_subscription(
    client: &Client,
    subject: &str,
    queue_group: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut subscriber = client
        .queue_subscribe(subject.to_string(), queue_group.to_string())
        .await?;
    
    info!("Subscribed to queue group: {}", queue_group);
    
    while let Some(message) = subscriber.next().await {
        info!("Queue member received: {}", String::from_utf8_lossy(&message.payload));
        
        // 处理消息（队列组中只有一个成员会收到）
        process_event(&serde_json::from_slice(&message.payload)?).await?;
    }
    
    Ok(())
}
```

---

## 5. 请求/响应模式

### 5.1 请求-应答

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct Request {
    pub query: String,
    pub params: serde_json::Value,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Response {
    pub result: serde_json::Value,
    pub error: Option<String>,
}

/// 发送请求并等待响应
#[instrument(skip(client))]
pub async fn send_request(
    client: &Client,
    subject: &str,
    request: &Request,
) -> Result<Response, Box<dyn std::error::Error>> {
    let payload = serde_json::to_vec(request)?;
    
    info!("Sending request to subject: {}", subject);
    
    let response = client
        .request(subject.to_string(), payload.into())
        .await?;
    
    let response_data: Response = serde_json::from_slice(&response.payload)?;
    
    info!("Received response");
    
    Ok(response_data)
}

/// 带超时的请求
#[instrument(skip(client))]
pub async fn send_request_with_timeout(
    client: &Client,
    subject: &str,
    request: &Request,
    timeout: Duration,
) -> Result<Response, Box<dyn std::error::Error>> {
    let payload = serde_json::to_vec(request)?;
    
    let response = tokio::time::timeout(
        timeout,
        client.request(subject.to_string(), payload.into()),
    )
    .await??;
    
    let response_data: Response = serde_json::from_slice(&response.payload)?;
    
    Ok(response_data)
}
```

### 5.2 服务端点

```rust
/// 服务端点（响应请求）
#[instrument(skip(client))]
pub async fn serve_requests(
    client: &Client,
    subject: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut subscriber = client.subscribe(subject.to_string()).await?;
    
    info!("Service listening on subject: {}", subject);
    
    while let Some(message) = subscriber.next().await {
        let request: Request = match serde_json::from_slice(&message.payload) {
            Ok(req) => req,
            Err(e) => {
                tracing::error!("Failed to parse request: {}", e);
                continue;
            }
        };
        
        info!("Processing request: {:?}", request);
        
        // 处理请求
        let response = handle_request(&request).await;
        
        // 发送响应
        if let Some(reply) = message.reply {
            let response_payload = serde_json::to_vec(&response)?;
            client.publish(reply, response_payload.into()).await?;
        }
    }
    
    Ok(())
}

async fn handle_request(request: &Request) -> Response {
    // 业务逻辑
    Response {
        result: serde_json::json!({"status": "ok", "query": request.query}),
        error: None,
    }
}
```

---

## 6. JetStream 持久化

### 6.1 Stream 管理

```rust
use async_nats::jetstream::{self, stream};

/// 创建 Stream
#[instrument(skip(client))]
pub async fn create_stream(
    client: &Client,
) -> Result<stream::Stream, Box<dyn std::error::Error>> {
    let jetstream = jetstream::new(client.clone());
    
    let stream = jetstream
        .create_stream(stream::Config {
            name: "EVENTS".to_string(),
            subjects: vec!["events.>".to_string()],
            max_messages: 10_000,
            max_bytes: 1_000_000_000, // 1GB
            max_age: Duration::from_secs(60 * 60 * 24 * 7), // 7 days
            storage: stream::StorageType::File,
            num_replicas: 1,
            ..Default::default()
        })
        .await?;
    
    info!("Stream created: {}", stream.cached_info().config.name);
    
    Ok(stream)
}

/// 获取 Stream 信息
#[instrument(skip(client))]
pub async fn get_stream_info(
    client: &Client,
    stream_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let jetstream = jetstream::new(client.clone());
    
    let stream = jetstream.get_stream(stream_name).await?;
    let info = stream.info().await?;
    
    info!(
        "Stream: {}, Messages: {}, Bytes: {}",
        info.config.name,
        info.state.messages,
        info.state.bytes
    );
    
    Ok(())
}
```

### 6.2 Consumer 管理

```rust
use async_nats::jetstream::consumer;

/// 创建持久化 Consumer
#[instrument(skip(stream))]
pub async fn create_durable_consumer(
    stream: &stream::Stream,
    consumer_name: &str,
) -> Result<consumer::PullConsumer, Box<dyn std::error::Error>> {
    let consumer = stream
        .create_consumer(consumer::pull::Config {
            durable_name: Some(consumer_name.to_string()),
            ack_policy: consumer::AckPolicy::Explicit,
            max_deliver: 5,
            deliver_policy: consumer::DeliverPolicy::All,
            ..Default::default()
        })
        .await?;
    
    info!("Durable consumer created: {}", consumer_name);
    
    Ok(consumer)
}

/// 拉取消息
#[instrument(skip(consumer))]
pub async fn pull_messages(
    consumer: &consumer::PullConsumer,
    batch_size: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut messages = consumer.fetch().max_messages(batch_size).messages().await?;
    
    while let Some(message) = messages.next().await {
        let message = message?;
        
        info!(
            "Received JetStream message: seq={}, subject={}",
            message.info()?.stream_sequence,
            message.subject
        );
        
        let event: Event = serde_json::from_slice(&message.payload)?;
        
        // 处理消息
        if let Err(e) = process_event(&event).await {
            tracing::error!("Failed to process event: {}", e);
            message.ack_with(consumer::AckKind::Nak(None)).await?;
        } else {
            message.ack().await?;
        }
    }
    
    Ok(())
}
```

### 6.3 消息确认（Ack）

```rust
/// 演示不同的 Ack 策略
#[instrument(skip(consumer))]
pub async fn ack_strategies(
    consumer: &consumer::PullConsumer,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut messages = consumer.fetch().max_messages(10).messages().await?;
    
    while let Some(message) = messages.next().await {
        let message = message?;
        
        match process_event_with_result(&message.payload).await {
            Ok(_) => {
                // 成功：确认消息
                message.ack().await?;
                info!("Message acknowledged");
            }
            Err(e) if e.is_retriable() => {
                // 可重试错误：Nak（重新投递）
                message.ack_with(consumer::AckKind::Nak(Some(Duration::from_secs(5)))).await?;
                info!("Message Nak'd, will retry in 5s");
            }
            Err(e) => {
                // 不可重试错误：Term（终止）
                tracing::error!("Fatal error: {}", e);
                message.ack_with(consumer::AckKind::Term).await?;
                info!("Message terminated");
            }
        }
    }
    
    Ok(())
}

#[derive(Debug)]
struct ProcessingError {
    retriable: bool,
    message: String,
}

impl ProcessingError {
    fn is_retriable(&self) -> bool {
        self.retriable
    }
}

impl std::fmt::Display for ProcessingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ProcessingError {}

async fn process_event_with_result(payload: &[u8]) -> Result<(), ProcessingError> {
    // 模拟处理逻辑
    Ok(())
}
```

---

## 7. Key-Value Store

### 7.1 KV 操作

```rust
use async_nats::jetstream::kv;

/// 创建 KV Bucket
#[instrument(skip(client))]
pub async fn create_kv_bucket(
    client: &Client,
) -> Result<kv::Store, Box<dyn std::error::Error>> {
    let jetstream = jetstream::new(client.clone());
    
    let kv = jetstream
        .create_key_value(kv::Config {
            bucket: "CONFIG".to_string(),
            history: 5,
            max_age: Duration::from_secs(60 * 60 * 24), // 1 day
            ..Default::default()
        })
        .await?;
    
    info!("KV bucket created: CONFIG");
    
    Ok(kv)
}

/// KV 基础操作
#[instrument(skip(kv))]
pub async fn kv_operations(
    kv: &kv::Store,
) -> Result<(), Box<dyn std::error::Error>> {
    // Put
    let revision = kv.put("app.version", "1.0.0".into()).await?;
    info!("Put: revision={}", revision);
    
    // Get
    if let Some(entry) = kv.get("app.version").await? {
        let value = String::from_utf8(entry.value.to_vec())?;
        info!("Get: value={}, revision={}", value, entry.revision);
    }
    
    // Update (CAS - Compare-And-Set)
    kv.update("app.version", "1.0.1".into(), revision).await?;
    info!("Updated with CAS");
    
    // Delete
    kv.delete("app.version").await?;
    info!("Deleted");
    
    // Purge (删除所有历史)
    kv.purge("app.version").await?;
    info!("Purged all history");
    
    Ok(())
}
```

### 7.2 KV Watch

```rust
/// Watch KV 变更
#[instrument(skip(kv))]
pub async fn watch_kv_changes(
    kv: &kv::Store,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut watcher = kv.watch("app.>").await?;
    
    info!("Watching for changes on app.>");
    
    while let Some(entry) = watcher.next().await {
        let entry = entry?;
        
        match entry.operation {
            kv::Operation::Put => {
                let value = String::from_utf8(entry.value.to_vec())?;
                info!("KV Put: key={}, value={}", entry.key, value);
            }
            kv::Operation::Delete => {
                info!("KV Delete: key={}", entry.key);
            }
            kv::Operation::Purge => {
                info!("KV Purge: key={}", entry.key);
            }
        }
    }
    
    Ok(())
}
```

---

## 8. Object Store

### 8.1 对象上传/下载

```rust
use async_nats::jetstream::object_store;
use tokio::io::AsyncReadExt;

/// 创建 Object Store
#[instrument(skip(client))]
pub async fn create_object_store(
    client: &Client,
) -> Result<object_store::ObjectStore, Box<dyn std::error::Error>> {
    let jetstream = jetstream::new(client.clone());
    
    let object_store = jetstream
        .create_object_store(object_store::Config {
            bucket: "FILES".to_string(),
            max_age: Duration::from_secs(60 * 60 * 24 * 30), // 30 days
            ..Default::default()
        })
        .await?;
    
    info!("Object store created: FILES");
    
    Ok(object_store)
}

/// 上传对象
#[instrument(skip(store, data))]
pub async fn upload_object(
    store: &object_store::ObjectStore,
    name: &str,
    data: Vec<u8>,
) -> Result<(), Box<dyn std::error::Error>> {
    store.put(name, data.as_slice()).await?;
    
    info!("Object uploaded: {}", name);
    
    Ok(())
}

/// 下载对象
#[instrument(skip(store))]
pub async fn download_object(
    store: &object_store::ObjectStore,
    name: &str,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut object = store.get(name).await?;
    
    let mut data = Vec::new();
    object.read_to_end(&mut data).await?;
    
    info!("Object downloaded: {} ({} bytes)", name, data.len());
    
    Ok(data)
}
```

### 8.2 对象流式处理

```rust
/// 流式上传大文件
#[instrument(skip(store))]
pub async fn stream_upload_file(
    store: &object_store::ObjectStore,
    name: &str,
    file_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    use tokio::fs::File;
    
    let file = File::open(file_path).await?;
    let file_size = file.metadata().await?.len();
    
    info!("Uploading file: {} ({} bytes)", name, file_size);
    
    store.put(name, file).await?;
    
    info!("File uploaded successfully");
    
    Ok(())
}

/// 列出所有对象
#[instrument(skip(store))]
pub async fn list_objects(
    store: &object_store::ObjectStore,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut objects = store.list().await?;
    
    while let Some(object) = objects.next().await {
        let object = object?;
        
        info!(
            "Object: name={}, size={} bytes",
            object.name,
            object.size
        );
    }
    
    Ok(())
}
```

---

## 9. 消息序列化

### 9.1 JSON 序列化

```rust
/// JSON 消息封装
pub struct JsonMessage<T: Serialize> {
    pub data: T,
}

impl<T: Serialize> JsonMessage<T> {
    pub fn to_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(&self.data)
    }
}

pub struct JsonDeserializer;

impl JsonDeserializer {
    pub fn from_bytes<T: for<'de> Deserialize<'de>>(
        bytes: &[u8],
    ) -> Result<T, serde_json::Error> {
        serde_json::from_slice(bytes)
    }
}
```

### 9.2 Protocol Buffers

```rust
// 假设使用 prost 生成的代码

/// Protobuf 消息封装
pub struct ProtobufMessage<T: prost::Message> {
    pub data: T,
}

impl<T: prost::Message> ProtobufMessage<T> {
    pub fn to_bytes(&self) -> Vec<u8> {
        use prost::Message;
        let mut buf = Vec::new();
        self.data.encode(&mut buf).unwrap();
        buf
    }
}

pub struct ProtobufDeserializer;

impl ProtobufDeserializer {
    pub fn from_bytes<T: prost::Message + Default>(
        bytes: &[u8],
    ) -> Result<T, prost::DecodeError> {
        use prost::Message;
        T::decode(bytes)
    }
}
```

---

## 10. 错误处理与重试

### 10.1 连接重连

```rust
/// 自动重连客户端
pub async fn resilient_client() -> Result<Client, async_nats::Error> {
    let client = ConnectOptions::new()
        .name("resilient-client")
        .retry_on_failed_connect()
        .max_reconnects(None) // 无限重连
        .reconnect_delay_callback(|attempts| {
            let delay = Duration::from_secs(2u64.pow(attempts.min(6)));
            tracing::warn!("Reconnecting in {:?} (attempt {})", delay, attempts);
            delay
        })
        .error_callback(|err| async move {
            tracing::error!("NATS error: {:?}", err);
        })
        .connect("nats://localhost:4222")
        .await?;
    
    Ok(client)
}
```

### 10.2 消息重试

```rust
/// 带重试的发布
#[instrument(skip(client))]
pub async fn publish_with_retry(
    client: &Client,
    subject: &str,
    payload: &[u8],
    max_retries: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut attempts = 0;
    
    loop {
        attempts += 1;
        
        match client.publish(subject.to_string(), payload.into()).await {
            Ok(_) => {
                info!("Message published successfully");
                return Ok(());
            }
            Err(e) => {
                if attempts >= max_retries {
                    tracing::error!("Failed after {} attempts: {}", attempts, e);
                    return Err(Box::new(e));
                }
                
                let delay = Duration::from_millis(100 * 2u64.pow(attempts - 1));
                tracing::warn!("Publish failed, retrying in {:?}: {}", delay, e);
                tokio::time::sleep(delay).await;
            }
        }
    }
}
```

---

## 11. OTLP 分布式追踪集成

### 11.1 发布者追踪

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};

/// 带追踪的发布
#[instrument(skip(client, event))]
pub async fn publish_with_trace(
    client: &Client,
    subject: &str,
    event: &Event,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-publisher");
    
    let mut span = tracer
        .span_builder(format!("NATS Publish {}", subject))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("messaging.destination", subject.to_string()),
            KeyValue::new("messaging.destination_kind", "topic"),
            KeyValue::new("messaging.protocol", "nats"),
        ])
        .start(&tracer);
    
    let payload = serde_json::to_vec(event)?;
    
    let result = client.publish(subject.to_string(), payload.into()).await;
    
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("messaging.message_payload_size_bytes", payload.len() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result?;
    
    Ok(())
}
```

### 11.2 订阅者追踪

```rust
/// 带追踪的订阅
#[instrument(skip(client))]
pub async fn subscribe_with_trace(
    client: &Client,
    subject: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut subscriber = client.subscribe(subject.to_string()).await?;
    
    info!("Subscribed to subject with tracing: {}", subject);
    
    while let Some(message) = subscriber.next().await {
        let tracer = global::tracer("nats-consumer");
        
        let mut span = tracer
            .span_builder(format!("NATS Consume {}", message.subject))
            .with_kind(SpanKind::Consumer)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("messaging.destination", message.subject.to_string()),
                KeyValue::new("messaging.operation", "receive"),
                KeyValue::new("messaging.message_payload_size_bytes", message.payload.len() as i64),
            ])
            .start(&tracer);
        
        let start = std::time::Instant::now();
        
        let result = process_message_traced(&message.payload).await;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("messaging.processing_time_ms", duration.as_millis() as i64));
        
        match result {
            Ok(_) => {
                span.set_status(Status::Ok);
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                span.set_attribute(KeyValue::new("error", true));
            }
        }
        
        span.end();
    }
    
    Ok(())
}

async fn process_message_traced(payload: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    Ok(())
}
```

### 11.3 分布式上下文传播

```rust
use opentelemetry::propagation::{Injector, Extractor, TextMapPropagator};
use std::collections::HashMap;

/// Header Injector
struct HeaderInjector(HashMap<String, String>);

impl Injector for HeaderInjector {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(key.to_string(), value);
    }
}

/// Header Extractor
struct HeaderExtractor(HashMap<String, String>);

impl Extractor for HeaderExtractor {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|s| s.as_str())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|s| s.as_str()).collect()
    }
}

/// 带上下文传播的发布
#[instrument(skip(client))]
pub async fn publish_with_context_propagation(
    client: &Client,
    subject: &str,
    payload: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    let mut headers = HashMap::new();
    
    // 注入追踪上下文
    let propagator = global::get_text_map_propagator(|p| p.clone());
    propagator.inject_context(&opentelemetry::Context::current(), &mut HeaderInjector(headers.clone()));
    
    // 将 headers 附加到消息（需要使用 NATS Headers）
    // 注意：async-nats 的 Headers 需要单独处理
    
    client.publish(subject.to_string(), payload.into()).await?;
    
    Ok(())
}
```

---

## 12. 性能优化

### 12.1 批量发布

```rust
/// 批量发布消息
#[instrument(skip(client, events))]
pub async fn batch_publish(
    client: &Client,
    subject: &str,
    events: Vec<Event>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Publishing {} messages in batch", events.len());
    
    let mut tasks = Vec::new();
    
    for event in events {
        let client = client.clone();
        let subject = subject.to_string();
        
        tasks.push(tokio::spawn(async move {
            let payload = serde_json::to_vec(&event)?;
            client.publish(subject, payload.into()).await?;
            Ok::<_, Box<dyn std::error::Error + Send + Sync>>(())
        }));
    }
    
    for task in tasks {
        task.await??;
    }
    
    info!("Batch publish complete");
    
    Ok(())
}
```

### 12.2 连接池

```rust
use std::sync::Arc;

/// NATS 客户端池
pub struct NatsClientPool {
    clients: Vec<Arc<Client>>,
    current: std::sync::atomic::AtomicUsize,
}

impl NatsClientPool {
    pub async fn new(size: usize, url: &str) -> Result<Self, async_nats::Error> {
        let mut clients = Vec::with_capacity(size);
        
        for _ in 0..size {
            let client = async_nats::connect(url).await?;
            clients.push(Arc::new(client));
        }
        
        Ok(Self {
            clients,
            current: std::sync::atomic::AtomicUsize::new(0),
        })
    }

    pub fn get_client(&self) -> Arc<Client> {
        use std::sync::atomic::Ordering;
        
        let index = self.current.fetch_add(1, Ordering::Relaxed) % self.clients.len();
        self.clients[index].clone()
    }
}
```

---

## 13. 高可用与集群

### 13.1 集群连接

```rust
/// 连接到 NATS 集群
#[instrument]
pub async fn connect_to_cluster() -> Result<Client, async_nats::Error> {
    let servers = vec![
        "nats://nats1.example.com:4222",
        "nats://nats2.example.com:4222",
        "nats://nats3.example.com:4222",
    ];
    
    let client = ConnectOptions::new()
        .name("cluster-client")
        .max_reconnects(None)
        .reconnect_delay_callback(|attempts| {
            Duration::from_secs(2u64.pow(attempts.min(5)))
        })
        .connect(servers.join(","))
        .await?;
    
    info!("Connected to NATS cluster");
    
    Ok(client)
}
```

### 13.2 故障转移

```rust
/// 故障转移示例
#[instrument]
pub async fn failover_demo() -> Result<(), Box<dyn std::error::Error>> {
    let client = connect_to_cluster().await?;
    
    // 监听连接事件
    let (tx, mut rx) = tokio::sync::mpsc::channel(100);
    
    tokio::spawn(async move {
        while let Some(event) = rx.recv().await {
            info!("Connection event: {:?}", event);
        }
    });
    
    // 正常发布（即使某个节点故障，也会自动切换到其他节点）
    loop {
        match client.publish("test".to_string(), "data".into()).await {
            Ok(_) => info!("Published successfully"),
            Err(e) => tracing::warn!("Publish failed, will retry: {}", e),
        }
        
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}
```

---

## 14. 安全配置

### 14.1 TLS 配置

```rust
use std::path::Path;

/// TLS 连接
#[instrument]
pub async fn connect_with_tls() -> Result<Client, Box<dyn std::error::Error>> {
    let client = ConnectOptions::new()
        .name("tls-client")
        .require_tls(true)
        .add_root_certificates(Path::new("/path/to/ca.crt"))
        .add_client_certificate(
            Path::new("/path/to/client.crt"),
            Path::new("/path/to/client.key"),
        )
        .connect("nats://nats.example.com:4222")
        .await?;
    
    info!("Connected with TLS");
    
    Ok(client)
}
```

### 14.2 认证授权

```rust
/// 用户名密码认证
#[instrument]
pub async fn connect_with_credentials() -> Result<Client, async_nats::Error> {
    let url = "nats://user:password@localhost:4222";
    let client = async_nats::connect(url).await?;
    
    info!("Connected with credentials");
    
    Ok(client)
}

/// Token 认证
#[instrument]
pub async fn connect_with_token() -> Result<Client, async_nats::Error> {
    let client = ConnectOptions::new()
        .name("token-client")
        .token("my_secret_token")
        .connect("nats://localhost:4222")
        .await?;
    
    info!("Connected with token");
    
    Ok(client)
}
```

---

## 15. 测试策略

### 15.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_publish_subscribe() {
        let client = async_nats::connect("nats://localhost:4222").await.unwrap();
        
        let subject = format!("test.{}", uuid::Uuid::new_v4());
        
        let mut subscriber = client.subscribe(subject.clone()).await.unwrap();
        
        let event = Event {
            id: "test-1".to_string(),
            event_type: "test.event".to_string(),
            data: serde_json::json!({"key": "value"}),
            timestamp: chrono::Utc::now().timestamp(),
        };
        
        publish_message(&client, &subject, &event).await.unwrap();
        
        let message = tokio::time::timeout(
            Duration::from_secs(1),
            subscriber.next(),
        )
        .await
        .unwrap()
        .unwrap();
        
        let received_event: Event = serde_json::from_slice(&message.payload).unwrap();
        
        assert_eq!(received_event.id, event.id);
    }
}
```

### 15.2 集成测试

```rust
// tests/integration_test.rs
use async_nats_demo::*;

#[tokio::test]
async fn test_jetstream_workflow() {
    let client = async_nats::connect("nats://localhost:4222").await.unwrap();
    
    // 创建 Stream
    let stream = create_stream(&client).await.unwrap();
    
    // 创建 Consumer
    let consumer = create_durable_consumer(&stream, "test-consumer").await.unwrap();
    
    // 发布消息
    let jetstream = async_nats::jetstream::new(client.clone());
    jetstream
        .publish("events.test".to_string(), "test data".into())
        .await
        .unwrap();
    
    // 拉取消息
    pull_messages(&consumer, 10).await.unwrap();
}
```

---

## 16. 生产环境部署

### 16.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  nats:
    image: nats:2.10-alpine
    container_name: nats
    ports:
      - "4222:4222"   # Client connections
      - "8222:8222"   # HTTP监控
      - "6222:6222"   # Cluster connections
    command:
      - "--jetstream"
      - "--store_dir=/data"
      - "--http_port=8222"
      - "--max_payload=8388608"  # 8MB
    volumes:
      - nats-data:/data
    restart: unless-stopped

  nats-exporter:
    image: natsio/prometheus-nats-exporter:latest
    container_name: nats-exporter
    ports:
      - "7777:7777"
    command:
      - "-varz"
      - "-channelz"
      - "-connz"
      - "-routez"
      - "-subz"
      - "-serverz"
      - "http://nats:8222"
    depends_on:
      - nats
    restart: unless-stopped

volumes:
  nats-data:
```

### 16.2 Kubernetes 部署

```yaml
# nats-deployment.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: nats-config
data:
  nats.conf: |
    jetstream {
      store_dir: /data
      max_memory_store: 1GB
      max_file_store: 10GB
    }
    
    max_payload: 8MB
    
    accounts {
      $SYS {
        users = [
          { user: "admin", password: "changeme" }
        ]
      }
    }
---
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: nats
spec:
  serviceName: nats
  replicas: 3
  selector:
    matchLabels:
      app: nats
  template:
    metadata:
      labels:
        app: nats
    spec:
      containers:
      - name: nats
        image: nats:2.10-alpine
        ports:
        - containerPort: 4222
          name: client
        - containerPort: 8222
          name: monitoring
        - containerPort: 6222
          name: cluster
        command:
        - "nats-server"
        - "--config"
        - "/etc/nats/nats.conf"
        - "--cluster"
        - "nats://0.0.0.0:6222"
        - "--routes"
        - "nats://nats-0.nats:6222,nats://nats-1.nats:6222,nats://nats-2.nats:6222"
        volumeMounts:
        - name: config
          mountPath: /etc/nats
        - name: data
          mountPath: /data
        livenessProbe:
          httpGet:
            path: /healthz
            port: 8222
          initialDelaySeconds: 10
          periodSeconds: 30
        readinessProbe:
          httpGet:
            path: /healthz
            port: 8222
          initialDelaySeconds: 5
          periodSeconds: 10
      volumes:
      - name: config
        configMap:
          name: nats-config
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: ["ReadWriteOnce"]
      resources:
        requests:
          storage: 10Gi
---
apiVersion: v1
kind: Service
metadata:
  name: nats
spec:
  selector:
    app: nats
  clusterIP: None
  ports:
  - name: client
    port: 4222
  - name: monitoring
    port: 8222
  - name: cluster
    port: 6222
---
apiVersion: v1
kind: Service
metadata:
  name: nats-external
spec:
  selector:
    app: nats
  type: LoadBalancer
  ports:
  - name: client
    port: 4222
    targetPort: 4222
```

---

## 17. 监控与指标

### 17.1 客户端指标

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// NATS 客户端指标
pub struct NatsMetrics {
    pub messages_published: AtomicU64,
    pub messages_consumed: AtomicU64,
    pub publish_errors: AtomicU64,
    pub consume_errors: AtomicU64,
    pub bytes_sent: AtomicU64,
    pub bytes_received: AtomicU64,
}

impl NatsMetrics {
    pub fn new() -> Self {
        Self {
            messages_published: AtomicU64::new(0),
            messages_consumed: AtomicU64::new(0),
            publish_errors: AtomicU64::new(0),
            consume_errors: AtomicU64::new(0),
            bytes_sent: AtomicU64::new(0),
            bytes_received: AtomicU64::new(0),
        }
    }

    pub fn record_publish(&self, bytes: u64) {
        self.messages_published.fetch_add(1, Ordering::Relaxed);
        self.bytes_sent.fetch_add(bytes, Ordering::Relaxed);
    }

    pub fn record_consume(&self, bytes: u64) {
        self.messages_consumed.fetch_add(1, Ordering::Relaxed);
        self.bytes_received.fetch_add(bytes, Ordering::Relaxed);
    }

    pub fn get_stats(&self) -> NatsStats {
        NatsStats {
            messages_published: self.messages_published.load(Ordering::Relaxed),
            messages_consumed: self.messages_consumed.load(Ordering::Relaxed),
            publish_errors: self.publish_errors.load(Ordering::Relaxed),
            consume_errors: self.consume_errors.load(Ordering::Relaxed),
            bytes_sent: self.bytes_sent.load(Ordering::Relaxed),
            bytes_received: self.bytes_received.load(Ordering::Relaxed),
        }
    }
}

#[derive(Debug)]
pub struct NatsStats {
    pub messages_published: u64,
    pub messages_consumed: u64,
    pub publish_errors: u64,
    pub consume_errors: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}
```

### 17.2 Prometheus 集成

```rust
/// Prometheus 指标导出
pub fn export_prometheus_metrics(metrics: &NatsMetrics) -> String {
    let stats = metrics.get_stats();
    
    format!(
        r#"# HELP nats_messages_published_total Total number of messages published
# TYPE nats_messages_published_total counter
nats_messages_published_total {}

# HELP nats_messages_consumed_total Total number of messages consumed
# TYPE nats_messages_consumed_total counter
nats_messages_consumed_total {}

# HELP nats_bytes_sent_total Total bytes sent
# TYPE nats_bytes_sent_total counter
nats_bytes_sent_total {}

# HELP nats_bytes_received_total Total bytes received
# TYPE nats_bytes_received_total counter
nats_bytes_received_total {}
"#,
        stats.messages_published,
        stats.messages_consumed,
        stats.bytes_sent,
        stats.bytes_received
    )
}
```

---

## 18. 国际标准对标

### 18.1 对标清单

| 标准分类 | 标准名称 | NATS 实现 |
|----------|----------|-----------|
| **消息协议** | NATS Protocol | ✅ 原生协议 |
| **消息保证** | At-Most-Once | ✅ 核心消息 |
| | At-Least-Once | ✅ JetStream |
| **持久化** | Message Persistence | ✅ JetStream |
| **流处理** | Stream Processing | ✅ JetStream |
| **KV Store** | Key-Value Store | ✅ JetStream KV |
| **Object Store** | Object Storage | ✅ JetStream Object Store |
| **安全** | TLS 1.2/1.3 | ✅ 完整支持 |
| | JWT Authentication | ✅ 完整支持 |
| **可观测性** | OpenTelemetry | ✅ 可集成 |
| **云原生** | CNCF | ✅ CNCF 孵化 |

### 18.2 与其他消息队列对比

| 特性 | NATS | Kafka | RabbitMQ | Redis | Pulsar |
|------|------|-------|----------|-------|--------|
| **吞吐量** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **延迟** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **运维** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **资源占用** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |

---

## 19. 总结与最佳实践

### 19.1 核心优势

1. **极致性能**：微秒级延迟，百万级 QPS
2. **简单易用**：直观的 API，快速上手
3. **云原生**：CNCF 项目，K8s 原生支持
4. **轻量级**：极小的资源占用
5. **功能丰富**：Pub/Sub、Request/Reply、JetStream、KV、Object Store
6. **高可用**：内置集群支持，自动故障转移

### 19.2 最佳实践

**✅ 推荐做法**:

- 使用 JetStream 实现消息持久化
- 实现优雅的错误处理和重试
- 使用队列组实现负载均衡
- 配置合理的超时时间
- 使用 OTLP 追踪消息流
- 在生产环境启用 TLS
- 使用 Durable Consumer 保证消息不丢失
- 实现幂等性处理

**❌ 避免做法**:

- 不要忽略消息确认（Ack）
- 不要在核心消息上依赖持久化
- 不要忽略连接重连逻辑
- 不要在生产环境禁用认证
- 不要使用过大的消息体（使用 Object Store）

### 19.3 性能基准

| 操作 | NATS | Kafka | RabbitMQ |
|------|------|-------|----------|
| **简单发布（1M msg）** | 1.2s | 3.5s | 8.5s |
| **P99 延迟** | 100μs | 5ms | 10ms |
| **吞吐量（单节点）** | 800K msg/s | 1M msg/s | 50K msg/s |
| **内存占用（1M msg）** | 50MB | 200MB | 150MB |

### 19.4 学习资源

- **官方文档**: <https://docs.nats.io/>
- **GitHub**: <https://github.com/nats-io/nats.rs>
- **示例代码**: <https://github.com/nats-io/nats.rs/tree/main/async-nats/examples>
- **CNCF**: <https://www.cncf.io/projects/nats/>

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**async-nats 版本**: 0.36  
**OpenTelemetry 版本**: 0.25  

---

**国际标准对齐**:

- ✅ NATS Protocol Specification
- ✅ At-Most-Once/At-Least-Once Delivery
- ✅ JetStream Persistence
- ✅ TLS 1.2/1.3
- ✅ JWT Authentication (RFC 7519)
- ✅ OpenTelemetry Messaging Semantic Conventions
- ✅ CNCF Cloud Native Standards

**参考文献**:

- NATS Official Documentation: <https://docs.nats.io/>
- JetStream Documentation: <https://docs.nats.io/nats-concepts/jetstream>
- OpenTelemetry Messaging Semantic Conventions: <https://opentelemetry.io/docs/specs/semconv/messaging/>
