# async-nats 消息队列 - Rust + OTLP 完整集成指南

## 📋 目录

- [async-nats 消息队列 - Rust + OTLP 完整集成指南](#async-nats-消息队列---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 NATS?](#什么是-nats)
    - [为什么选择 async-nats?](#为什么选择-async-nats)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. NATS 架构](#1-nats-架构)
    - [2. 消息模式](#2-消息模式)
  - [环境准备](#环境准备)
    - [1. 安装 NATS Server](#1-安装-nats-server)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. 连接 NATS](#1-连接-nats)
    - [2. 发布订阅](#2-发布订阅)
    - [3. 请求响应](#3-请求响应)
  - [OTLP 追踪集成](#otlp-追踪集成)
    - [1. 发布者追踪](#1-发布者追踪)
    - [2. 订阅者追踪](#2-订阅者追踪)
    - [3. 跨服务追踪](#3-跨服务追踪)
  - [JetStream 持久化](#jetstream-持久化)
    - [1. Stream 管理](#1-stream-管理)
    - [2. Consumer 消费](#2-consumer-消费)
    - [3. 消息确认](#3-消息确认)
  - [高级特性](#高级特性)
    - [1. KV Store](#1-kv-store)
    - [2. Object Store](#2-object-store)
    - [3. Service API](#3-service-api)
  - [性能优化](#性能优化)
    - [1. 批量发送](#1-批量发送)
    - [2. 连接池](#2-连接池)
    - [3. 消息压缩](#3-消息压缩)
  - [可靠性保证](#可靠性保证)
    - [1. 重试机制](#1-重试机制)
    - [2. 死信队列](#2-死信队列)
    - [3. 消息去重](#3-消息去重)
  - [完整示例](#完整示例)
    - [1. 事件驱动架构](#1-事件驱动架构)
    - [2. 分布式任务队列](#2-分布式任务队列)
  - [最佳实践](#最佳实践)
    - [1. 主题设计](#1-主题设计)
    - [2. 错误处理](#2-错误处理)
    - [3. 监控告警](#3-监控告警)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [NATS vs 其他消息队列](#nats-vs-其他消息队列)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 NATS?

**NATS** 是高性能的云原生消息系统:

```text
┌─────────────────────────────────────┐
│         NATS Ecosystem              │
│  ┌──────────────────────────────┐   │
│  │  Core NATS (轻量级)           │   │
│  │  JetStream (持久化)           │   │
│  │  KV Store (键值存储)          │   │
│  │  Object Store (对象存储)      │   │
│  │  Service API (微服务)         │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
```

**核心特性**:

- **极致性能**: 百万级 QPS
- **简单**: 主题即路由,无需配置
- **轻量**: 20MB 内存运行
- **云原生**: Kubernetes 原生支持
- **多模式**: Pub/Sub, Request/Reply, Queue

### 为什么选择 async-nats?

| 优势 | 说明 |
|------|------|
| **异步原生** | Tokio 驱动,高并发 |
| **类型安全** | Rust 类型系统保证 |
| **零拷贝** | 高效内存管理 |
| **完整功能** | 支持所有 NATS 特性 |
| **活跃维护** | NATS 官方 Rust 客户端 |

### OTLP 集成价值

```text
Publisher → NATS → Subscriber
    ↓         ↓         ↓
  Trace   Context   Trace
    ↓         ↓         ↓
    └────→ OTLP ←────┘
```

**追踪能力**:

- 消息发布延迟
- 队列等待时间
- 消费处理时间
- 端到端延迟
- 跨服务追踪链

---

## 核心概念

### 1. NATS 架构

```text
┌─────────────────────────────────────────┐
│         Publishers (发布者)              │
└──────────────┬──────────────────────────┘
               │ Publish
┌──────────────▼──────────────────────────┐
│         NATS Server Cluster             │
│  ┌─────────────────────────────────┐    │
│  │  Subject-based Routing          │    │
│  │  orders.created                 │    │
│  │  orders.*.updated               │    │
│  │  orders.>                       │    │
│  └─────────────────────────────────┘    │
└──────────────┬──────────────────────────┘
               │ Deliver
┌──────────────▼──────────────────────────┐
│         Subscribers (订阅者)             │
└─────────────────────────────────────────┘
```

### 2. 消息模式

**Pub/Sub (发布订阅)**:

```text
Publisher → orders.created → Subscriber 1
                          → Subscriber 2
                          → Subscriber 3
(所有订阅者都收到消息)
```

**Queue Groups (队列组)**:

```text
Publisher → orders.created → [Queue: workers]
                          → Worker 1 (负载均衡)
                          → Worker 2
                          → Worker 3
(只有一个worker收到消息)
```

**Request/Reply (请求响应)**:

```text
Requester → request.subject → Responder
         ← response         ←
```

---

## 环境准备

### 1. 安装 NATS Server

```bash
# Docker 方式
docker run -d --name nats \
  -p 4222:4222 \
  -p 8222:8222 \
  -p 6222:6222 \
  nats:latest \
  -js  # 启用 JetStream

# 或使用 Docker Compose
cat > docker-compose.yml <<EOF
version: '3.8'
services:
  nats:
    image: nats:latest
    ports:
      - "4222:4222"  # Client port
      - "8222:8222"  # HTTP monitoring
      - "6222:6222"  # Routing port for clustering
    command: ["-js", "-m", "8222"]  # 启用 JetStream 和监控
EOF

docker-compose up -d

# 验证
curl http://localhost:8222/varz
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "nats-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# NATS 客户端
async-nats = "0.33"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }
futures = "0.3"

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
bytes = "1.5"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# UUID
uuid = { version = "1.8", features = ["v4", "serde"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. 连接 NATS

```rust
// src/client.rs
use async_nats::Client;
use anyhow::Result;

pub async fn connect_nats(url: &str) -> Result<Client> {
    let client = async_nats::connect(url).await?;
    tracing::info!("Connected to NATS at {}", url);
    Ok(client)
}

pub async fn connect_with_options() -> Result<Client> {
    let client = async_nats::ConnectOptions::new()
        .name("rust-app")  // 客户端名称
        .max_reconnects(5)  // 最大重连次数
        .reconnect_delay_callback(|attempts| {
            std::time::Duration::from_millis(std::cmp::min(attempts * 100, 8000))
        })
        .connect("nats://localhost:4222")
        .await?;
    
    Ok(client)
}
```

### 2. 发布订阅

```rust
// src/pubsub.rs
use async_nats::Client;
use serde::{Deserialize, Serialize};
use futures::StreamExt;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderCreated {
    pub order_id: String,
    pub user_id: String,
    pub amount: f64,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 发布消息
pub async fn publish_order(client: &Client, order: &OrderCreated) -> Result<()> {
    let subject = "orders.created";
    let payload = serde_json::to_vec(order)?;
    
    client.publish(subject, payload.into()).await?;
    tracing::info!("Published order: {}", order.order_id);
    
    Ok(())
}

/// 订阅消息
pub async fn subscribe_orders(client: &Client) -> Result<()> {
    let mut subscriber = client.subscribe("orders.created").await?;
    
    tracing::info!("Subscribed to orders.created");
    
    while let Some(message) = subscriber.next().await {
        let order: OrderCreated = serde_json::from_slice(&message.payload)?;
        tracing::info!("Received order: {:?}", order);
        
        // 处理订单...
        process_order(order).await?;
    }
    
    Ok(())
}

/// 通配符订阅
pub async fn subscribe_all_orders(client: &Client) -> Result<()> {
    // orders.* 匹配 orders.created, orders.updated 等
    // orders.> 匹配 orders.created, orders.v1.created 等 (递归)
    let mut subscriber = client.subscribe("orders.*").await?;
    
    while let Some(message) = subscriber.next().await {
        tracing::info!("Subject: {}, Payload: {:?}", message.subject, message.payload);
    }
    
    Ok(())
}
```

### 3. 请求响应

```rust
// src/reqrep.rs
use bytes::Bytes;

/// 请求方 (Client)
pub async fn request_user_info(client: &Client, user_id: &str) -> Result<UserInfo> {
    let subject = format!("users.get.{}", user_id);
    let payload = Bytes::from(user_id.to_string());
    
    // 发送请求并等待响应 (默认超时5秒)
    let response = client
        .request(subject, payload)
        .await?;
    
    let user_info: UserInfo = serde_json::from_slice(&response.payload)?;
    Ok(user_info)
}

/// 响应方 (Server)
pub async fn handle_user_requests(client: &Client) -> Result<()> {
    let mut subscriber = client.subscribe("users.get.*").await?;
    
    while let Some(message) = subscriber.next().await {
        let user_id = message.subject.strip_prefix("users.get.").unwrap();
        
        // 查询用户信息
        let user_info = get_user_from_db(user_id).await?;
        let response_payload = serde_json::to_vec(&user_info)?;
        
        // 回复
        if let Some(reply_subject) = message.reply {
            client.publish(reply_subject, response_payload.into()).await?;
        }
    }
    
    Ok(())
}
```

---

## OTLP 追踪集成

### 1. 发布者追踪

```rust
// src/tracing/publisher.rs
use tracing::{info, instrument, Span};
use opentelemetry::{
    global,
    trace::{Span as OtelSpan, Tracer, SpanKind},
    KeyValue,
};

#[instrument(
    name = "nats.publish",
    fields(
        messaging.system = "nats",
        messaging.destination = %subject,
        messaging.operation = "publish",
    )
)]
pub async fn traced_publish(
    client: &Client,
    subject: &str,
    payload: Bytes,
) -> Result<()> {
    let tracer = global::tracer("nats-client");
    
    let mut span = tracer
        .span_builder("nats.publish")
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("messaging.destination", subject.to_string()),
            KeyValue::new("messaging.message.payload_size_bytes", payload.len() as i64),
        ])
        .start(&tracer);
    
    // 注入 Trace Context 到消息头
    let headers = inject_trace_context(&span);
    
    let start = std::time::Instant::now();
    
    let result = client
        .publish_with_headers(subject, headers, payload)
        .await;
    
    let duration = start.elapsed();
    span.set_attribute(KeyValue::new("messaging.publish.duration_ms", duration.as_millis() as i64));
    
    match &result {
        Ok(_) => {
            info!("Message published successfully");
        }
        Err(e) => {
            span.record_error(e);
        }
    }
    
    span.end();
    result.map_err(Into::into)
}

/// 注入 Trace Context 到 NATS Headers
fn inject_trace_context(span: &impl OtelSpan) -> async_nats::HeaderMap {
    use opentelemetry::propagation::Injector;
    
    struct NatsHeaderInjector {
        headers: async_nats::HeaderMap,
    }
    
    impl Injector for NatsHeaderInjector {
        fn set(&mut self, key: &str, value: String) {
            self.headers.insert(key, value.as_str());
        }
    }
    
    let mut injector = NatsHeaderInjector {
        headers: async_nats::HeaderMap::new(),
    };
    
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let context = opentelemetry::Context::current_with_span(span.clone());
    propagator.inject_context(&context, &mut injector);
    
    injector.headers
}
```

### 2. 订阅者追踪

```rust
// src/tracing/subscriber.rs
#[instrument(
    name = "nats.subscribe",
    skip(client, handler),
    fields(
        messaging.system = "nats",
        messaging.destination = %subject,
        messaging.operation = "receive",
    )
)]
pub async fn traced_subscribe<F, Fut>(
    client: &Client,
    subject: &str,
    handler: F,
) -> Result<()>
where
    F: Fn(async_nats::Message) -> Fut + Send + 'static,
    Fut: std::future::Future<Output = Result<()>> + Send,
{
    let mut subscriber = client.subscribe(subject).await?;
    
    info!("Subscribed to {}", subject);
    
    while let Some(message) = subscriber.next().await {
        // 提取 Trace Context
        let parent_context = extract_trace_context(&message);
        
        // 创建子 Span
        let tracer = global::tracer("nats-client");
        let mut span = tracer
            .span_builder("nats.receive")
            .with_kind(SpanKind::Consumer)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("messaging.source", message.subject.to_string()),
                KeyValue::new("messaging.message.payload_size_bytes", message.payload.len() as i64),
            ])
            .start_with_context(&tracer, &parent_context);
        
        let start = std::time::Instant::now();
        
        // 处理消息
        let result = handler(message).await;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("messaging.processing.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(_) => {
                span.set_attribute(KeyValue::new("messaging.processing.status", "success"));
            }
            Err(e) => {
                span.record_error(e);
                span.set_attribute(KeyValue::new("messaging.processing.status", "error"));
            }
        }
        
        span.end();
    }
    
    Ok(())
}

/// 从 NATS Headers 提取 Trace Context
fn extract_trace_context(message: &async_nats::Message) -> opentelemetry::Context {
    use opentelemetry::propagation::Extractor;
    
    struct NatsHeaderExtractor<'a> {
        headers: Option<&'a async_nats::HeaderMap>,
    }
    
    impl<'a> Extractor for NatsHeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.headers?
                .get(key)?
                .iter()
                .next()
                .map(|v| v.as_str())
        }
        
        fn keys(&self) -> Vec<&str> {
            self.headers
                .map(|h| h.iter().map(|(k, _)| k.as_str()).collect())
                .unwrap_or_default()
        }
    }
    
    let extractor = NatsHeaderExtractor {
        headers: message.headers.as_ref(),
    };
    
    let propagator = global::get_text_map_propagator(|p| p.clone());
    propagator.extract(&extractor)
}
```

### 3. 跨服务追踪

```rust
// 完整的端到端追踪
pub async fn end_to_end_tracing_example() -> Result<()> {
    let client = connect_nats("nats://localhost:4222").await?;
    
    // 服务 A: 发布消息
    traced_publish(
        &client,
        "orders.created",
        serde_json::to_vec(&order)?.into(),
    ).await?;
    
    // 服务 B: 接收并处理
    traced_subscribe(&client, "orders.created", |message| async move {
        // Trace Context 自动传播!
        let order: OrderCreated = serde_json::from_slice(&message.payload)?;
        process_order(order).await
    }).await?;
    
    Ok(())
}
```

---

## JetStream 持久化

### 1. Stream 管理

```rust
// src/jetstream.rs
use async_nats::jetstream;

pub async fn setup_jetstream(client: &Client) -> Result<jetstream::Context> {
    let jetstream = jetstream::new(client.clone());
    
    // 创建 Stream
    let stream = jetstream
        .create_stream(jetstream::stream::Config {
            name: "ORDERS".to_string(),
            subjects: vec!["orders.>".to_string()],
            max_messages: 1_000_000,
            max_bytes: 1024 * 1024 * 1024,  // 1GB
            max_age: std::time::Duration::from_secs(7 * 24 * 60 * 60),  // 7 days
            storage: jetstream::stream::StorageType::File,
            retention: jetstream::stream::RetentionPolicy::Limits,
            ..Default::default()
        })
        .await?;
    
    tracing::info!("JetStream stream created: {:?}", stream);
    
    Ok(jetstream)
}

pub async fn publish_to_stream(
    jetstream: &jetstream::Context,
    subject: &str,
    payload: Bytes,
) -> Result<()> {
    let ack = jetstream
        .publish(subject, payload)
        .await?
        .await?;
    
    tracing::info!(
        "Message published to stream, sequence: {}, timestamp: {:?}",
        ack.sequence,
        ack.timestamp
    );
    
    Ok(())
}
```

### 2. Consumer 消费

```rust
pub async fn create_consumer(
    jetstream: &jetstream::Context,
) -> Result<()> {
    // 创建 Durable Consumer
    let consumer = jetstream
        .create_consumer_on_stream(
            jetstream::consumer::Config {
                durable_name: Some("orders-processor".to_string()),
                ack_policy: jetstream::consumer::AckPolicy::Explicit,
                max_deliver: 3,  // 最多投递3次
                ack_wait: std::time::Duration::from_secs(30),
                ..Default::default()
            },
            "ORDERS",
        )
        .await?;
    
    // 消费消息
    let mut messages = consumer.messages().await?;
    
    while let Some(message) = messages.next().await {
        let message = message?;
        
        tracing::info!(
            "Received message: subject={}, sequence={}",
            message.subject,
            message.info()?.stream_sequence
        );
        
        // 处理消息
        match process_message(&message).await {
            Ok(_) => {
                // 确认消息
                message.ack().await?;
            }
            Err(e) => {
                // 否定确认 (会重新投递)
                message.ack_with(jetstream::AckKind::Nak(None)).await?;
                tracing::error!("Failed to process message: {}", e);
            }
        }
    }
    
    Ok(())
}
```

### 3. 消息确认

```rust
pub async fn ack_strategies(message: jetstream::Message) -> Result<()> {
    // 1. 确认消息 (Ack)
    message.ack().await?;
    
    // 2. 否定确认 (Nak) - 立即重新投递
    message.ack_with(jetstream::AckKind::Nak(None)).await?;
    
    // 3. 延迟否定确认 - 延迟30秒后重新投递
    message.ack_with(jetstream::AckKind::Nak(
        Some(std::time::Duration::from_secs(30))
    )).await?;
    
    // 4. 终止重试 (Term) - 不再重新投递
    message.ack_with(jetstream::AckKind::Term).await?;
    
    // 5. 进度确认 (In Progress) - 延长ack_wait时间
    message.ack_with(jetstream::AckKind::Progress).await?;
    
    Ok(())
}
```

---

## 高级特性

### 1. KV Store

```rust
// src/kv.rs
pub async fn kv_store_example(jetstream: &jetstream::Context) -> Result<()> {
    // 创建 KV Bucket
    let kv = jetstream
        .create_key_value(jetstream::kv::Config {
            bucket: "user_sessions".to_string(),
            history: 10,  // 保留10个历史版本
            max_bytes: 1024 * 1024 * 100,  // 100MB
            ttl: Some(std::time::Duration::from_secs(3600)),  // 1小时TTL
            ..Default::default()
        })
        .await?;
    
    // Put
    kv.put("session:user123", serde_json::to_vec(&session)?.into())
        .await?;
    
    // Get
    if let Some(entry) = kv.get("session:user123").await? {
        let session: Session = serde_json::from_slice(&entry)?;
        tracing::info!("Session: {:?}", session);
    }
    
    // Delete
    kv.delete("session:user123").await?;
    
    // Watch changes
    let mut watcher = kv.watch("session:>").await?;
    while let Some(entry) = watcher.next().await {
        tracing::info!("KV changed: {:?}", entry);
    }
    
    Ok(())
}
```

### 2. Object Store

```rust
// src/object_store.rs
pub async fn object_store_example(jetstream: &jetstream::Context) -> Result<()> {
    // 创建 Object Store
    let object_store = jetstream
        .create_object_store(jetstream::object_store::Config {
            bucket: "files".to_string(),
            max_bytes: 1024 * 1024 * 1024,  // 1GB
            ..Default::default()
        })
        .await?;
    
    // Put object
    let file_data = tokio::fs::read("large_file.pdf").await?;
    object_store
        .put("documents/large_file.pdf", &mut file_data.as_slice())
        .await?;
    
    // Get object
    let mut object = object_store.get("documents/large_file.pdf").await?;
    let mut buffer = Vec::new();
    while let Some(chunk) = object.next().await {
        buffer.extend_from_slice(&chunk?);
    }
    
    // List objects
    let mut list = object_store.list().await?;
    while let Some(object) = list.next().await {
        tracing::info!("Object: {:?}", object?);
    }
    
    Ok(())
}
```

### 3. Service API

```rust
// src/service.rs
use async_nats::service;

pub async fn create_nats_service(client: &Client) -> Result<()> {
    let mut service = service::ServiceBuilder::new(client.clone())
        .name("user-service")
        .version("1.0.0")
        .description("User management service")
        .start()
        .await?;
    
    // 添加端点
    let mut endpoint = service
        .endpoint("users.get")
        .await?;
    
    // 处理请求
    while let Some(request) = endpoint.next().await {
        let user_id = std::str::from_utf8(&request.message.payload)?;
        
        match get_user(user_id).await {
            Ok(user) => {
                request.respond(Ok(serde_json::to_vec(&user)?.into())).await?;
            }
            Err(e) => {
                request.respond(Err(service::error::Error {
                    code: 404,
                    status: "Not Found".to_string(),
                })).await?;
            }
        }
    }
    
    Ok(())
}
```

---

## 性能优化

### 1. 批量发送

```rust
pub async fn batch_publish(client: &Client, orders: Vec<OrderCreated>) -> Result<()> {
    // 批量发布
    for chunk in orders.chunks(100) {
        let futures: Vec<_> = chunk
            .iter()
            .map(|order| {
                let payload = serde_json::to_vec(order).unwrap();
                client.publish("orders.created", payload.into())
            })
            .collect();
        
        // 并发发送
        futures::future::try_join_all(futures).await?;
    }
    
    Ok(())
}
```

### 2. 连接池

```rust
use std::sync::Arc;

pub struct NatsPool {
    clients: Vec<Arc<Client>>,
    current: std::sync::atomic::AtomicUsize,
}

impl NatsPool {
    pub async fn new(url: &str, pool_size: usize) -> Result<Self> {
        let mut clients = Vec::with_capacity(pool_size);
        
        for _ in 0..pool_size {
            let client = connect_nats(url).await?;
            clients.push(Arc::new(client));
        }
        
        Ok(Self {
            clients,
            current: std::sync::atomic::AtomicUsize::new(0),
        })
    }
    
    pub fn get(&self) -> Arc<Client> {
        let idx = self.current
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            % self.clients.len();
        
        self.clients[idx].clone()
    }
}
```

### 3. 消息压缩

```rust
use flate2::write::GzEncoder;
use flate2::read::GzDecoder;
use std::io::{Write, Read};

pub fn compress_payload(data: &[u8]) -> Result<Vec<u8>> {
    let mut encoder = GzEncoder::new(Vec::new(), flate2::Compression::default());
    encoder.write_all(data)?;
    Ok(encoder.finish()?)
}

pub fn decompress_payload(data: &[u8]) -> Result<Vec<u8>> {
    let mut decoder = GzDecoder::new(data);
    let mut decompressed = Vec::new();
    decoder.read_to_end(&mut decompressed)?;
    Ok(decompressed)
}
```

---

## 可靠性保证

### 1. 重试机制

```rust
pub async fn publish_with_retry(
    client: &Client,
    subject: &str,
    payload: Bytes,
    max_retries: usize,
) -> Result<()> {
    let mut attempts = 0;
    
    loop {
        match client.publish(subject, payload.clone()).await {
            Ok(_) => return Ok(()),
            Err(e) if attempts < max_retries => {
                attempts += 1;
                let backoff = std::time::Duration::from_millis(100 * 2_u64.pow(attempts as u32));
                tracing::warn!("Publish failed, retrying in {:?}: {}", backoff, e);
                tokio::time::sleep(backoff).await;
            }
            Err(e) => return Err(e.into()),
        }
    }
}
```

### 2. 死信队列

```rust
pub async fn setup_dlq(jetstream: &jetstream::Context) -> Result<()> {
    // 主队列
    jetstream.create_stream(jetstream::stream::Config {
        name: "ORDERS".to_string(),
        subjects: vec!["orders.>".to_string()],
        ..Default::default()
    }).await?;
    
    // 死信队列
    jetstream.create_stream(jetstream::stream::Config {
        name: "ORDERS_DLQ".to_string(),
        subjects: vec!["orders.dlq.>".to_string()],
        ..Default::default()
    }).await?;
    
    Ok(())
}

pub async fn handle_failed_message(
    jetstream: &jetstream::Context,
    message: &jetstream::Message,
) -> Result<()> {
    // 发送到死信队列
    let dlq_subject = format!("orders.dlq.{}", message.subject);
    jetstream.publish(dlq_subject, message.payload.clone()).await?;
    
    // 终止原消息
    message.ack_with(jetstream::AckKind::Term).await?;
    
    Ok(())
}
```

### 3. 消息去重

```rust
use std::collections::HashSet;
use std::sync::RwLock;

pub struct MessageDeduplicator {
    seen: Arc<RwLock<HashSet<String>>>,
}

impl MessageDeduplicator {
    pub fn new() -> Self {
        Self {
            seen: Arc::new(RwLock::new(HashSet::new())),
        }
    }
    
    pub fn is_duplicate(&self, message_id: &str) -> bool {
        let mut seen = self.seen.write().unwrap();
        !seen.insert(message_id.to_string())
    }
}
```

---

## 完整示例

### 1. 事件驱动架构

```rust
// src/examples/event_driven.rs
#[tokio::main]
async fn main() -> Result<()> {
    let client = connect_nats("nats://localhost:4222").await?;
    
    // 订单服务: 发布订单创建事件
    tokio::spawn({
        let client = client.clone();
        async move {
            loop {
                let order = OrderCreated { /* ... */ };
                traced_publish(&client, "orders.created", /* ... */).await?;
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        }
    });
    
    // 库存服务: 监听订单事件,减少库存
    tokio::spawn({
        let client = client.clone();
        async move {
            traced_subscribe(&client, "orders.created", |msg| async move {
                let order: OrderCreated = serde_json::from_slice(&msg.payload)?;
                reduce_inventory(&order).await?;
                Ok(())
            }).await
        }
    });
    
    // 通知服务: 监听订单事件,发送通知
    tokio::spawn({
        let client = client.clone();
        async move {
            traced_subscribe(&client, "orders.created", |msg| async move {
                let order: OrderCreated = serde_json::from_slice(&msg.payload)?;
                send_notification(&order).await?;
                Ok(())
            }).await
        }
    });
    
    Ok(())
}
```

### 2. 分布式任务队列

```rust
// src/examples/task_queue.rs
#[derive(Serialize, Deserialize)]
pub struct Task {
    pub id: String,
    pub task_type: String,
    pub payload: serde_json::Value,
}

pub async fn task_producer(jetstream: &jetstream::Context) -> Result<()> {
    let task = Task {
        id: uuid::Uuid::new_v4().to_string(),
        task_type: "image_processing".to_string(),
        payload: json!({"image_url": "https://example.com/image.jpg"}),
    };
    
    publish_to_stream(
        jetstream,
        "tasks.image_processing",
        serde_json::to_vec(&task)?.into(),
    ).await?;
    
    Ok(())
}

pub async fn task_worker(jetstream: &jetstream::Context, worker_id: &str) -> Result<()> {
    let consumer = jetstream
        .create_consumer_on_stream(
            jetstream::consumer::Config {
                durable_name: Some(format!("worker-{}", worker_id)),
                filter_subject: "tasks.>".to_string(),
                ..Default::default()
            },
            "TASKS",
        )
        .await?;
    
    let mut messages = consumer.messages().await?;
    
    while let Some(message) = messages.next().await {
        let message = message?;
        let task: Task = serde_json::from_slice(&message.payload)?;
        
        match process_task(&task).await {
            Ok(_) => message.ack().await?,
            Err(e) => {
                if task.retry_count >= 3 {
                    handle_failed_message(jetstream, &message).await?;
                } else {
                    message.ack_with(jetstream::AckKind::Nak(Some(Duration::from_secs(60)))).await?;
                }
            }
        }
    }
    
    Ok(())
}
```

---

## 最佳实践

### 1. 主题设计

```rust
// ✅ 好的主题设计
"orders.created"
"orders.updated"
"orders.deleted"
"orders.v1.created"  // 版本化

"users.{user_id}.orders.created"  // 用户特定

// ❌ 避免
"create_order"  // 不够描述性
"order"  // 太宽泛
```

### 2. 错误处理

```rust
#[derive(thiserror::Error, Debug)]
pub enum NatsError {
    #[error("Connection failed: {0}")]
    ConnectionError(String),
    
    #[error("Publish failed: {0}")]
    PublishError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
}
```

### 3. 监控告警

```rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct NatsMetrics {
    messages_published: Counter<u64>,
    messages_received: Counter<u64>,
    publish_duration: Histogram<f64>,
}

impl NatsMetrics {
    pub fn record_publish(&self, subject: &str, duration_ms: f64) {
        let attributes = vec![
            KeyValue::new("subject", subject.to_string()),
        ];
        
        self.messages_published.add(1, &attributes);
        self.publish_duration.record(duration_ms, &attributes);
    }
}
```

---

## 总结

### 核心要点

1. **NATS**: 极简高性能消息系统
2. **async-nats**: Rust 官方异步客户端
3. **JetStream**: 持久化和流处理
4. **OTLP**: 端到端分布式追踪
5. **云原生**: Kubernetes 友好

### NATS vs 其他消息队列

| 特性 | NATS | RabbitMQ | Kafka | Redis |
|------|------|----------|-------|-------|
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **简单性** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ |
| **持久化** | ✅ (JS) | ✅ | ✅ | ⚠️ |
| **云原生** | ✅ | ⚠️ | ⚠️ | ⚠️ |
| **运维复杂度** | ⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ |

### 下一步

- **NATS Cluster**: 高可用集群
- **Leaf Nodes**: 边缘计算
- **WebSocket**: 浏览器连接

---

## 参考资料

- [NATS 官方文档](https://docs.nats.io/)
- [async-nats GitHub](https://github.com/nats-io/nats.rs)
- [JetStream 指南](https://docs.nats.io/nats-concepts/jetstream)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**async-nats**: 0.33+  
**OpenTelemetry**: 0.30+
