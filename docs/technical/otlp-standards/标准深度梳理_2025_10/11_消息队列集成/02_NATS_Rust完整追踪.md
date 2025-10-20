# NATS Rust 完整追踪实现指南

## 目录

- [NATS Rust 完整追踪实现指南](#nats-rust-完整追踪实现指南)
  - [目录](#目录)
  - [1. NATS 架构概述](#1-nats-架构概述)
    - [1.1 NATS 核心特性](#11-nats-核心特性)
    - [1.2 NATS 与 OpenTelemetry](#12-nats-与-opentelemetry)
  - [2. Rust 依赖配置](#2-rust-依赖配置)
  - [3. NATS Semantic Conventions](#3-nats-semantic-conventions)
    - [3.1 消息属性](#31-消息属性)
    - [3.2 Span 命名规范](#32-span-命名规范)
  - [4. NATS Publisher 追踪](#4-nats-publisher-追踪)
    - [4.1 基础发布追踪](#41-基础发布追踪)
    - [4.2 Request-Reply 追踪](#42-request-reply-追踪)
    - [4.3 批量发布追踪](#43-批量发布追踪)
  - [5. NATS Subscriber 追踪](#5-nats-subscriber-追踪)
    - [5.1 基础订阅追踪](#51-基础订阅追踪)
    - [5.2 Queue Group 订阅追踪](#52-queue-group-订阅追踪)
    - [5.3 JetStream Consumer 追踪](#53-jetstream-consumer-追踪)
  - [6. JetStream 追踪](#6-jetstream-追踪)
    - [6.1 Stream 创建追踪](#61-stream-创建追踪)
    - [6.2 消息持久化追踪](#62-消息持久化追踪)
    - [6.3 Consumer 管理追踪](#63-consumer-管理追踪)
  - [7. Context Propagation](#7-context-propagation)
    - [7.1 Header 注入](#71-header-注入)
    - [7.2 Header 提取](#72-header-提取)
  - [8. 错误处理与重试](#8-错误处理与重试)
    - [8.1 连接错误处理](#81-连接错误处理)
    - [8.2 发布重试机制](#82-发布重试机制)
  - [9. 性能监控](#9-性能监控)
    - [9.1 延迟监控](#91-延迟监控)
    - [9.2 吞吐量监控](#92-吞吐量监控)
  - [10. 完整生产示例](#10-完整生产示例)
  - [总结](#总结)

---

## 1. NATS 架构概述

### 1.1 NATS 核心特性

NATS 是一个高性能、轻量级的云原生消息系统：

- **发布-订阅模式**：Subject-based 消息路由
- **Request-Reply**：同步请求响应模式
- **Queue Groups**：负载均衡订阅者
- **JetStream**：持久化、流式存储
- **高性能**：纳秒级延迟

### 1.2 NATS 与 OpenTelemetry

NATS 追踪关注点：

1. **消息发布**：发送延迟、失败率
2. **消息订阅**：处理延迟、吞吐量
3. **Context 传播**：跨服务追踪链
4. **JetStream 操作**：持久化、Ack 延迟

---

## 2. Rust 依赖配置

```toml
[dependencies]
# NATS 客户端
async-nats = "0.37.0"

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace"] }
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

[dev-dependencies]
criterion = "0.5"
```

---

## 3. NATS Semantic Conventions

### 3.1 消息属性

```rust
// NATS 消息属性常量
pub mod attributes {
    pub const MESSAGING_SYSTEM: &str = "messaging.system";           // "nats"
    pub const MESSAGING_DESTINATION: &str = "messaging.destination.name";  // Subject
    pub const MESSAGING_OPERATION: &str = "messaging.operation";     // "publish" | "receive"
    pub const MESSAGING_MESSAGE_ID: &str = "messaging.message.id";
    pub const MESSAGING_CONVERSATION_ID: &str = "messaging.conversation_id";
    pub const NATS_REPLY_TO: &str = "nats.reply_to";
    pub const NATS_STREAM: &str = "nats.jetstream.stream";
    pub const NATS_CONSUMER: &str = "nats.jetstream.consumer";
    pub const NATS_QUEUE_GROUP: &str = "nats.queue_group";
}
```

### 3.2 Span 命名规范

- **发布操作**：`{subject} publish`
- **订阅操作**：`{subject} receive`
- **请求操作**：`{subject} request`
- **JetStream 操作**：`{stream}/{subject} publish`

---

## 4. NATS Publisher 追踪

### 4.1 基础发布追踪

```rust
use async_nats::Client;
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::{global, Context, KeyValue};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub payload: String,
}

/// NATS 发布器（支持 OpenTelemetry 追踪）
pub struct TracedPublisher {
    client: Client,
}

impl TracedPublisher {
    pub fn new(client: Client) -> Self {
        Self { client }
    }

    /// 发布消息（带追踪）
    pub async fn publish_with_trace(
        &self,
        subject: &str,
        message: &Message,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("nats-publisher");
        let mut span = tracer
            .span_builder(format!("{} publish", subject))
            .with_kind(SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("messaging.destination.name", subject.to_string()),
                KeyValue::new("messaging.operation", "publish"),
                KeyValue::new("messaging.message.id", message.id.clone()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 序列化消息
        let payload = serde_json::to_vec(message)?;

        // 注入 OpenTelemetry Context 到 NATS Headers
        let mut headers = async_nats::HeaderMap::new();
        inject_trace_context(&cx, &mut headers);

        // 发布消息
        let result = self
            .client
            .publish_with_headers(subject.to_string(), headers, payload.into())
            .await;

        match result {
            Ok(_) => {
                cx.span().add_event("Message published successfully", vec![]);
                Ok(())
            }
            Err(e) => {
                cx.span().record_error(&e);
                cx.span().add_event("Message publish failed", vec![
                    KeyValue::new("error.type", format!("{:?}", e)),
                ]);
                Err(Box::new(e))
            }
        }
    }
}

/// 注入 Trace Context 到 NATS Headers
fn inject_trace_context(cx: &Context, headers: &mut async_nats::HeaderMap) {
    use opentelemetry::propagation::{TextMapPropagator, Injector};

    struct NatsHeaderInjector<'a>(&'a mut async_nats::HeaderMap);

    impl<'a> Injector for NatsHeaderInjector<'a> {
        fn set(&mut self, key: &str, value: String) {
            if let Ok(header_name) = async_nats::HeaderName::from_bytes(key.as_bytes()) {
                if let Ok(header_value) = async_nats::HeaderValue::from_str(&value) {
                    self.0.insert(header_name, header_value);
                }
            }
        }
    }

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(cx, &mut NatsHeaderInjector(headers));
}
```

### 4.2 Request-Reply 追踪

```rust
impl TracedPublisher {
    /// Request-Reply 模式（带追踪）
    pub async fn request_with_trace(
        &self,
        subject: &str,
        request: &Message,
        timeout: std::time::Duration,
    ) -> Result<Message, Box<dyn std::error::Error>> {
        let tracer = global::tracer("nats-publisher");
        let mut span = tracer
            .span_builder(format!("{} request", subject))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("messaging.destination.name", subject.to_string()),
                KeyValue::new("messaging.operation", "request"),
                KeyValue::new("messaging.message.id", request.id.clone()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 序列化请求
        let payload = serde_json::to_vec(request)?;

        // 注入 Context
        let mut headers = async_nats::HeaderMap::new();
        inject_trace_context(&cx, &mut headers);

        // 发送请求并等待响应
        let start = std::time::Instant::now();
        let response = tokio::time::timeout(
            timeout,
            self.client.request_with_headers(
                subject.to_string(),
                headers,
                payload.into(),
            ),
        )
        .await??;

        let duration = start.elapsed();

        // 记录响应信息
        cx.span().add_event("Response received", vec![
            KeyValue::new("response.size", response.payload.len() as i64),
            KeyValue::new("duration.ms", duration.as_millis() as i64),
        ]);

        // 解析响应
        let reply: Message = serde_json::from_slice(&response.payload)?;
        Ok(reply)
    }
}
```

### 4.3 批量发布追踪

```rust
impl TracedPublisher {
    /// 批量发布消息
    pub async fn batch_publish_with_trace(
        &self,
        subject: &str,
        messages: Vec<Message>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("nats-publisher");
        let mut span = tracer
            .span_builder(format!("{} batch_publish", subject))
            .with_kind(SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("messaging.destination.name", subject.to_string()),
                KeyValue::new("messaging.batch.message_count", messages.len() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut success_count = 0;
        let mut failure_count = 0;

        for message in messages {
            match self.publish_with_trace(subject, &message).await {
                Ok(_) => success_count += 1,
                Err(e) => {
                    failure_count += 1;
                    cx.span().add_event("Batch item failed", vec![
                        KeyValue::new("message.id", message.id),
                        KeyValue::new("error.type", format!("{:?}", e)),
                    ]);
                }
            }
        }

        cx.span().set_attributes(vec![
            KeyValue::new("batch.success_count", success_count),
            KeyValue::new("batch.failure_count", failure_count),
        ]);

        Ok(())
    }
}
```

---

## 5. NATS Subscriber 追踪

### 5.1 基础订阅追踪

```rust
use async_nats::Subscriber;
use futures::StreamExt;

/// NATS 订阅器（支持 OpenTelemetry 追踪）
pub struct TracedSubscriber {
    subscriber: Subscriber,
}

impl TracedSubscriber {
    pub fn new(subscriber: Subscriber) -> Self {
        Self { subscriber }
    }

    /// 处理订阅消息（带追踪）
    pub async fn process_messages<F, Fut>(
        mut self,
        mut handler: F,
    ) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(Message, Context) -> Fut,
        Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
    {
        while let Some(msg) = self.subscriber.next().await {
            let tracer = global::tracer("nats-subscriber");

            // 提取 Trace Context
            let parent_cx = extract_trace_context(&msg.headers);

            let mut span = tracer
                .span_builder(format!("{} receive", msg.subject))
                .with_kind(SpanKind::Consumer)
                .with_attributes(vec![
                    KeyValue::new("messaging.system", "nats"),
                    KeyValue::new("messaging.destination.name", msg.subject.to_string()),
                    KeyValue::new("messaging.operation", "receive"),
                    KeyValue::new("messaging.message.payload_size", msg.payload.len() as i64),
                ])
                .start_with_context(&tracer, &parent_cx);

            let cx = parent_cx.with_span(span);
            let _guard = cx.attach();

            // 解析消息
            match serde_json::from_slice::<Message>(&msg.payload) {
                Ok(message) => {
                    cx.span().set_attribute(KeyValue::new("messaging.message.id", message.id.clone()));

                    // 调用处理函数
                    if let Err(e) = handler(message, cx.clone()).await {
                        cx.span().record_error(&*e);
                        cx.span().add_event("Message processing failed", vec![]);
                    } else {
                        cx.span().add_event("Message processed successfully", vec![]);
                    }
                }
                Err(e) => {
                    cx.span().record_error(&e);
                    cx.span().add_event("Message deserialization failed", vec![]);
                }
            }
        }

        Ok(())
    }
}

/// 从 NATS Headers 提取 Trace Context
fn extract_trace_context(headers: &Option<async_nats::HeaderMap>) -> Context {
    use opentelemetry::propagation::{TextMapPropagator, Extractor};

    struct NatsHeaderExtractor<'a>(Option<&'a async_nats::HeaderMap>);

    impl<'a> Extractor for NatsHeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.and_then(|headers| {
                headers.get(key).and_then(|v| v.as_str().ok())
            })
        }

        fn keys(&self) -> Vec<&str> {
            self.0.map(|headers| {
                headers.iter().map(|(k, _)| k.as_str()).collect()
            }).unwrap_or_default()
        }
    }

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.extract(&NatsHeaderExtractor(headers.as_ref()))
}
```

### 5.2 Queue Group 订阅追踪

```rust
/// Queue Group 订阅（负载均衡）
pub async fn subscribe_queue_group_with_trace(
    client: &Client,
    subject: &str,
    queue_group: &str,
) -> Result<TracedSubscriber, Box<dyn std::error::Error>> {
    let subscriber = client
        .queue_subscribe(subject.to_string(), queue_group.to_string())
        .await?;

    // 记录订阅启动
    let tracer = global::tracer("nats-subscriber");
    let span = tracer
        .span_builder("queue_group_subscribe")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("messaging.destination.name", subject.to_string()),
            KeyValue::new("nats.queue_group", queue_group.to_string()),
        ])
        .start(&tracer);

    span.end();

    Ok(TracedSubscriber::new(subscriber))
}
```

### 5.3 JetStream Consumer 追踪

```rust
use async_nats::jetstream::{consumer::PullConsumer, Context as JsContext};

/// JetStream Consumer 追踪
pub struct TracedJetStreamConsumer {
    consumer: PullConsumer,
    stream_name: String,
}

impl TracedJetStreamConsumer {
    pub fn new(consumer: PullConsumer, stream_name: String) -> Self {
        Self { consumer, stream_name }
    }

    /// 拉取并处理消息
    pub async fn fetch_with_trace(
        &mut self,
        batch_size: usize,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("nats-jetstream");
        let mut span = tracer
            .span_builder("jetstream.fetch")
            .with_attributes(vec![
                KeyValue::new("messaging.system", "nats"),
                KeyValue::new("nats.jetstream.stream", self.stream_name.clone()),
                KeyValue::new("batch.size", batch_size as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut messages = self.consumer.fetch().max_messages(batch_size).messages().await?;

        let mut processed = 0;
        while let Some(msg) = messages.next().await {
            let msg = msg?;

            // 提取 Context
            let parent_cx = extract_trace_context(&msg.headers);
            let mut msg_span = tracer
                .span_builder(format!("{} receive", msg.subject))
                .with_kind(SpanKind::Consumer)
                .start_with_context(&tracer, &parent_cx);

            // 处理消息...
            msg.ack().await?;
            processed += 1;

            msg_span.end();
        }

        cx.span().set_attribute(KeyValue::new("batch.processed", processed));
        Ok(())
    }
}
```

---

## 6. JetStream 追踪

### 6.1 Stream 创建追踪

```rust
use async_nats::jetstream::stream::Config as StreamConfig;

/// 创建 JetStream Stream（带追踪）
pub async fn create_stream_with_trace(
    jetstream: &JsContext,
    config: StreamConfig,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-jetstream");
    let mut span = tracer
        .span_builder("jetstream.create_stream")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("nats.jetstream.stream", config.name.clone()),
            KeyValue::new("nats.jetstream.subjects", format!("{:?}", config.subjects)),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let result = jetstream.create_stream(config).await;

    match result {
        Ok(_) => {
            cx.span().add_event("Stream created successfully", vec![]);
            Ok(())
        }
        Err(e) => {
            cx.span().record_error(&e);
            Err(Box::new(e))
        }
    }
}
```

### 6.2 消息持久化追踪

```rust
/// JetStream 发布（持久化消息）
pub async fn publish_jetstream_with_trace(
    jetstream: &JsContext,
    subject: &str,
    message: &Message,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-jetstream");
    let mut span = tracer
        .span_builder(format!("{} publish", subject))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("messaging.destination.name", subject.to_string()),
            KeyValue::new("nats.jetstream.persistence", "true"),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let payload = serde_json::to_vec(message)?;

    let mut headers = async_nats::HeaderMap::new();
    inject_trace_context(&cx, &mut headers);

    let ack = jetstream
        .publish_with_headers(subject.to_string(), headers, payload.into())
        .await?
        .await?;

    cx.span().add_event("Message persisted", vec![
        KeyValue::new("nats.stream", ack.stream),
        KeyValue::new("nats.sequence", ack.sequence as i64),
    ]);

    Ok(())
}
```

### 6.3 Consumer 管理追踪

```rust
use async_nats::jetstream::consumer::pull::Config as ConsumerConfig;

/// 创建 Consumer（带追踪）
pub async fn create_consumer_with_trace(
    stream: &async_nats::jetstream::stream::Stream,
    config: ConsumerConfig,
) -> Result<PullConsumer, Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-jetstream");
    let mut span = tracer
        .span_builder("jetstream.create_consumer")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "nats"),
            KeyValue::new("nats.jetstream.stream", stream.cached_info().config.name.clone()),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let consumer = stream.create_consumer(config).await?;

    cx.span().add_event("Consumer created successfully", vec![]);
    Ok(consumer)
}
```

---

## 7. Context Propagation

### 7.1 Header 注入

已在 `inject_trace_context` 函数中实现：

```rust
fn inject_trace_context(cx: &Context, headers: &mut async_nats::HeaderMap) {
    // 使用 W3C Trace Context Propagator
    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(cx, &mut NatsHeaderInjector(headers));
}
```

### 7.2 Header 提取

已在 `extract_trace_context` 函数中实现：

```rust
fn extract_trace_context(headers: &Option<async_nats::HeaderMap>) -> Context {
    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.extract(&NatsHeaderExtractor(headers.as_ref()))
}
```

---

## 8. 错误处理与重试

### 8.1 连接错误处理

```rust
use async_nats::ConnectOptions;
use std::time::Duration;

/// 创建 NATS 连接（带重试）
pub async fn connect_with_retry(
    urls: &[String],
    max_retries: u32,
) -> Result<Client, Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-client");
    let mut span = tracer
        .span_builder("nats.connect")
        .with_attributes(vec![
            KeyValue::new("nats.urls", format!("{:?}", urls)),
            KeyValue::new("max_retries", max_retries as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let options = ConnectOptions::new()
        .connection_timeout(Duration::from_secs(5))
        .retry_on_initial_connect()
        .max_reconnects(max_retries as usize);

    for attempt in 1..=max_retries {
        match async_nats::connect_with_options(urls.join(","), options.clone()).await {
            Ok(client) => {
                cx.span().add_event("Connected successfully", vec![
                    KeyValue::new("attempt", attempt as i64),
                ]);
                return Ok(client);
            }
            Err(e) if attempt < max_retries => {
                cx.span().add_event("Connection attempt failed", vec![
                    KeyValue::new("attempt", attempt as i64),
                    KeyValue::new("error", format!("{:?}", e)),
                ]);
                tokio::time::sleep(Duration::from_secs(2_u64.pow(attempt - 1))).await;
            }
            Err(e) => {
                cx.span().record_error(&e);
                return Err(Box::new(e));
            }
        }
    }

    unreachable!()
}
```

### 8.2 发布重试机制

```rust
/// 带重试的发布
pub async fn publish_with_retry(
    publisher: &TracedPublisher,
    subject: &str,
    message: &Message,
    max_retries: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("nats-publisher");
    let mut span = tracer
        .span_builder(format!("{} publish_with_retry", subject))
        .with_attributes(vec![
            KeyValue::new("max_retries", max_retries as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    for attempt in 1..=max_retries {
        match publisher.publish_with_trace(subject, message).await {
            Ok(_) => {
                cx.span().set_attribute(KeyValue::new("attempt", attempt as i64));
                return Ok(());
            }
            Err(e) if attempt < max_retries => {
                cx.span().add_event("Publish attempt failed", vec![
                    KeyValue::new("attempt", attempt as i64),
                ]);
                tokio::time::sleep(Duration::from_millis(100 * attempt as u64)).await;
            }
            Err(e) => {
                cx.span().record_error(&*e);
                return Err(e);
            }
        }
    }

    unreachable!()
}
```

---

## 9. 性能监控

### 9.1 延迟监控

```rust
use opentelemetry::metrics::{Meter, Counter, Histogram};

pub struct NatsMetrics {
    publish_duration: Histogram<f64>,
    receive_duration: Histogram<f64>,
    message_size: Histogram<u64>,
}

impl NatsMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            publish_duration: meter
                .f64_histogram("nats.publish.duration")
                .with_unit("ms")
                .with_description("NATS publish duration")
                .build(),
            receive_duration: meter
                .f64_histogram("nats.receive.duration")
                .with_unit("ms")
                .with_description("NATS receive duration")
                .build(),
            message_size: meter
                .u64_histogram("nats.message.size")
                .with_unit("bytes")
                .with_description("NATS message size")
                .build(),
        }
    }

    pub fn record_publish(&self, duration: Duration, size: usize) {
        self.publish_duration.record(duration.as_secs_f64() * 1000.0, &[]);
        self.message_size.record(size as u64, &[]);
    }

    pub fn record_receive(&self, duration: Duration, size: usize) {
        self.receive_duration.record(duration.as_secs_f64() * 1000.0, &[]);
        self.message_size.record(size as u64, &[]);
    }
}
```

### 9.2 吞吐量监控

```rust
pub struct ThroughputMetrics {
    messages_published: Counter<u64>,
    messages_received: Counter<u64>,
    bytes_published: Counter<u64>,
    bytes_received: Counter<u64>,
}

impl ThroughputMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            messages_published: meter
                .u64_counter("nats.messages.published")
                .with_description("Total messages published")
                .build(),
            messages_received: meter
                .u64_counter("nats.messages.received")
                .with_description("Total messages received")
                .build(),
            bytes_published: meter
                .u64_counter("nats.bytes.published")
                .with_description("Total bytes published")
                .build(),
            bytes_received: meter
                .u64_counter("nats.bytes.received")
                .with_description("Total bytes received")
                .build(),
        }
    }

    pub fn record_publish(&self, message_size: usize) {
        self.messages_published.add(1, &[]);
        self.bytes_published.add(message_size as u64, &[]);
    }

    pub fn record_receive(&self, message_size: usize) {
        self.messages_received.add(1, &[]);
        self.bytes_received.add(message_size as u64, &[]);
    }
}
```

---

## 10. 完整生产示例

```rust
use async_nats::jetstream::stream::Config as StreamConfig;
use async_nats::jetstream::consumer::pull::Config as ConsumerConfig;
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

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

    // 连接 NATS
    let urls = vec!["nats://localhost:4222".to_string()];
    let client = connect_with_retry(&urls, 3).await?;

    // 创建 JetStream Context
    let jetstream = async_nats::jetstream::new(client.clone());

    // 创建 Stream
    let stream_config = StreamConfig {
        name: "ORDERS".to_string(),
        subjects: vec!["orders.>".to_string()],
        ..Default::default()
    };
    create_stream_with_trace(&jetstream, stream_config).await?;

    // 发布消息
    let publisher = TracedPublisher::new(client.clone());
    let message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        payload: "Order #12345".to_string(),
    };

    publish_jetstream_with_trace(&jetstream, "orders.new", &message).await?;

    // 创建 Consumer
    let stream = jetstream.get_stream("ORDERS").await?;
    let consumer_config = ConsumerConfig {
        durable_name: Some("order-processor".to_string()),
        ..Default::default()
    };
    let consumer = create_consumer_with_trace(&stream, consumer_config).await?;

    // 订阅并处理消息
    let mut traced_consumer = TracedJetStreamConsumer::new(consumer, "ORDERS".to_string());
    traced_consumer.fetch_with_trace(10).await?;

    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}
```

---

## 总结

本指南涵盖了 NATS 与 OpenTelemetry 集成的完整实现：

1. **发布追踪**：基础发布、Request-Reply、批量发布
2. **订阅追踪**：基础订阅、Queue Groups、JetStream Consumer
3. **JetStream**：Stream 创建、消息持久化、Consumer 管理
4. **Context 传播**：W3C Trace Context 注入/提取
5. **错误处理**：连接重试、发布重试
6. **性能监控**：延迟、吞吐量、消息大小

通过这些实现，您可以在生产环境中获得 NATS 消息系统的完整可观测性。
