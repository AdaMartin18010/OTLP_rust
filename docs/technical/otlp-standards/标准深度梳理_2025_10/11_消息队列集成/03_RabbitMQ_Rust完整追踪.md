# RabbitMQ Rust 完整追踪实现指南

## 目录

- [RabbitMQ Rust 完整追踪实现指南](#rabbitmq-rust-完整追踪实现指南)
  - [目录](#目录)
  - [1. RabbitMQ 架构概述](#1-rabbitmq-架构概述)
    - [1.1 RabbitMQ 核心概念](#11-rabbitmq-核心概念)
    - [1.2 RabbitMQ 与 OpenTelemetry](#12-rabbitmq-与-opentelemetry)
  - [2. Rust 依赖配置](#2-rust-依赖配置)
  - [3. RabbitMQ Semantic Conventions](#3-rabbitmq-semantic-conventions)
    - [3.1 消息属性](#31-消息属性)
    - [3.2 Span 命名规范](#32-span-命名规范)
  - [4. Connection 与 Channel 追踪](#4-connection-与-channel-追踪)
    - [4.1 连接池追踪](#41-连接池追踪)
    - [4.2 Channel 创建追踪](#42-channel-创建追踪)
  - [5. Producer 追踪](#5-producer-追踪)
    - [5.1 基础发布追踪](#51-基础发布追踪)
    - [5.2 Confirm 模式追踪](#52-confirm-模式追踪)
    - [5.3 批量发布追踪](#53-批量发布追踪)
  - [6. Consumer 追踪](#6-consumer-追踪)
    - [6.1 基础消费追踪](#61-基础消费追踪)
    - [6.2 Manual Ack 追踪](#62-manual-ack-追踪)
    - [6.3 Prefetch 优化追踪](#63-prefetch-优化追踪)
  - [7. Exchange 与 Queue 管理](#7-exchange-与-queue-管理)
    - [7.1 Exchange 声明追踪](#71-exchange-声明追踪)
    - [7.2 Queue 声明追踪](#72-queue-声明追踪)
    - [7.3 Binding 追踪](#73-binding-追踪)
  - [8. Context Propagation](#8-context-propagation)
    - [8.1 AMQP Properties 注入](#81-amqp-properties-注入)
    - [8.2 Headers 提取](#82-headers-提取)
  - [9. 错误处理与重试](#9-错误处理与重试)
    - [9.1 连接断开重连](#91-连接断开重连)
    - [9.2 Dead Letter Queue](#92-dead-letter-queue)
    - [9.3 消息重试机制](#93-消息重试机制)
  - [10. 性能监控](#10-性能监控)
    - [10.1 发布延迟监控](#101-发布延迟监控)
    - [10.2 队列指标监控](#102-队列指标监控)
  - [11. 完整生产示例](#11-完整生产示例)
  - [总结](#总结)

---

## 1. RabbitMQ 架构概述

### 1.1 RabbitMQ 核心概念

RabbitMQ 是基于 AMQP 协议的消息代理：

- **Connection**：TCP 连接
- **Channel**：虚拟连接，共享 TCP 连接
- **Exchange**：消息路由器（direct、topic、fanout、headers）
- **Queue**：消息存储队列
- **Binding**：Exchange 与 Queue 的绑定规则
- **Routing Key**：消息路由键

### 1.2 RabbitMQ 与 OpenTelemetry

RabbitMQ 追踪关注点：

1. **Producer 追踪**：发布延迟、Confirm 确认
2. **Consumer 追踪**：消费延迟、Ack/Nack
3. **Context 传播**：通过 AMQP Headers
4. **队列监控**：队列深度、消费速率

---

## 2. Rust 依赖配置

```toml
[dependencies]
# RabbitMQ 客户端
lapin = "2.5.0"

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

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }

# 连接池
deadpool = "0.12"
deadpool-lapin = "0.12"

[dev-dependencies]
criterion = "0.5"
```

---

## 3. RabbitMQ Semantic Conventions

### 3.1 消息属性

```rust
// RabbitMQ 消息属性常量
pub mod attributes {
    pub const MESSAGING_SYSTEM: &str = "messaging.system";                    // "rabbitmq"
    pub const MESSAGING_DESTINATION: &str = "messaging.destination.name";     // Exchange name
    pub const MESSAGING_DESTINATION_KIND: &str = "messaging.destination_kind"; // "queue" | "exchange"
    pub const MESSAGING_OPERATION: &str = "messaging.operation";              // "publish" | "receive"
    pub const MESSAGING_MESSAGE_ID: &str = "messaging.message.id";
    pub const MESSAGING_CONVERSATION_ID: &str = "messaging.conversation_id";
    pub const RABBITMQ_ROUTING_KEY: &str = "messaging.rabbitmq.routing_key";
    pub const RABBITMQ_EXCHANGE_TYPE: &str = "messaging.rabbitmq.exchange_type"; // direct, topic, fanout
    pub const RABBITMQ_DELIVERY_TAG: &str = "messaging.rabbitmq.delivery_tag";
    pub const RABBITMQ_CONSUMER_TAG: &str = "messaging.rabbitmq.consumer_tag";
    pub const RABBITMQ_REDELIVERED: &str = "messaging.rabbitmq.redelivered";
}
```

### 3.2 Span 命名规范

- **发布操作**：`{exchange} publish`
- **消费操作**：`{queue} receive`
- **队列声明**：`{queue} declare`
- **Exchange 声明**：`{exchange} declare`

---

## 4. Connection 与 Channel 追踪

### 4.1 连接池追踪

```rust
use deadpool_lapin::{Manager, Pool, Runtime};
use lapin::ConnectionProperties;
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::{global, Context, KeyValue};

/// 创建 RabbitMQ 连接池（带追踪）
pub async fn create_pool_with_trace(
    amqp_url: &str,
    max_size: usize,
) -> Result<Pool, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-pool");
    let mut span = tracer
        .span_builder("rabbitmq.pool.create")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("pool.max_size", max_size as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let manager = Manager::new(amqp_url, ConnectionProperties::default());
    let pool = Pool::builder(manager)
        .max_size(max_size)
        .runtime(Runtime::Tokio1)
        .build()?;

    cx.span().add_event("Connection pool created", vec![]);
    Ok(pool)
}

/// 从连接池获取连接
pub async fn get_connection_with_trace(
    pool: &Pool,
) -> Result<deadpool_lapin::Object, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-pool");
    let mut span = tracer
        .span_builder("rabbitmq.pool.get")
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let start = std::time::Instant::now();
    let connection = pool.get().await?;
    let duration = start.elapsed();

    cx.span().add_event("Connection acquired", vec![
        KeyValue::new("duration.ms", duration.as_millis() as i64),
    ]);

    Ok(connection)
}
```

### 4.2 Channel 创建追踪

```rust
use lapin::{Connection, Channel};

/// 创建 Channel（带追踪）
pub async fn create_channel_with_trace(
    connection: &Connection,
) -> Result<Channel, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-channel");
    let mut span = tracer
        .span_builder("rabbitmq.channel.create")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let channel = connection.create_channel().await?;

    cx.span().add_event("Channel created", vec![
        KeyValue::new("channel.id", channel.id() as i64),
    ]);

    Ok(channel)
}
```

---

## 5. Producer 追踪

### 5.1 基础发布追踪

```rust
use lapin::{
    BasicProperties, Channel,
    options::{BasicPublishOptions, ExchangeDeclareOptions},
    types::FieldTable,
    ExchangeKind,
};
use opentelemetry::trace::{SpanKind, Span};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub payload: String,
}

/// RabbitMQ Producer（支持追踪）
pub struct TracedProducer {
    channel: Channel,
}

impl TracedProducer {
    pub fn new(channel: Channel) -> Self {
        Self { channel }
    }

    /// 发布消息到 Exchange（带追踪）
    pub async fn publish_with_trace(
        &self,
        exchange: &str,
        routing_key: &str,
        message: &Message,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("rabbitmq-producer");
        let mut span = tracer
            .span_builder(format!("{} publish", exchange))
            .with_kind(SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("messaging.system", "rabbitmq"),
                KeyValue::new("messaging.destination.name", exchange.to_string()),
                KeyValue::new("messaging.destination_kind", "exchange"),
                KeyValue::new("messaging.operation", "publish"),
                KeyValue::new("messaging.rabbitmq.routing_key", routing_key.to_string()),
                KeyValue::new("messaging.message.id", message.id.clone()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 序列化消息
        let payload = serde_json::to_vec(message)?;

        // 创建 AMQP Properties 并注入 Trace Context
        let properties = inject_trace_context(&cx, message);

        // 发布消息
        let result = self
            .channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                &payload,
                properties,
            )
            .await?;

        // 等待 Confirm（如果启用了 Confirm 模式）
        result.await?;

        cx.span().add_event("Message published successfully", vec![
            KeyValue::new("payload.size", payload.len() as i64),
        ]);

        Ok(())
    }
}

/// 注入 Trace Context 到 AMQP Properties
fn inject_trace_context(cx: &Context, message: &Message) -> BasicProperties {
    use opentelemetry::propagation::{TextMapPropagator, Injector};
    use std::collections::HashMap;

    // 创建 Headers Map
    let mut headers_map: HashMap<String, String> = HashMap::new();

    struct HeaderInjector<'a>(&'a mut HashMap<String, String>);

    impl<'a> Injector for HeaderInjector<'a> {
        fn set(&mut self, key: &str, value: String) {
            self.0.insert(key.to_string(), value);
        }
    }

    // 注入 Trace Context
    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(cx, &mut HeaderInjector(&mut headers_map));

    // 转换为 AMQP FieldTable
    let mut field_table = FieldTable::default();
    for (key, value) in headers_map {
        field_table.insert(key.into(), lapin::types::AMQPValue::LongString(value.into()));
    }

    BasicProperties::default()
        .with_message_id(message.id.clone().into())
        .with_content_type("application/json".into())
        .with_headers(field_table)
}
```

### 5.2 Confirm 模式追踪

```rust
use lapin::options::ConfirmSelectOptions;

impl TracedProducer {
    /// 启用 Confirm 模式
    pub async fn enable_confirm_mode(&self) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("rabbitmq-producer");
        let mut span = tracer
            .span_builder("rabbitmq.confirm.enable")
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        self.channel.confirm_select(ConfirmSelectOptions::default()).await?;

        cx.span().add_event("Confirm mode enabled", vec![]);
        Ok(())
    }

    /// 发布消息并等待 Confirm
    pub async fn publish_with_confirm(
        &self,
        exchange: &str,
        routing_key: &str,
        message: &Message,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("rabbitmq-producer");
        let mut span = tracer
            .span_builder(format!("{} publish_confirm", exchange))
            .with_kind(SpanKind::Producer)
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let start = std::time::Instant::now();

        // 发布消息
        let payload = serde_json::to_vec(message)?;
        let properties = inject_trace_context(&cx, message);

        let confirm = self
            .channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                &payload,
                properties,
            )
            .await?;

        // 等待 Broker Confirm
        confirm.await?;

        let duration = start.elapsed();

        cx.span().add_event("Message confirmed by broker", vec![
            KeyValue::new("confirm.duration.ms", duration.as_millis() as i64),
        ]);

        Ok(())
    }
}
```

### 5.3 批量发布追踪

```rust
impl TracedProducer {
    /// 批量发布消息
    pub async fn batch_publish_with_trace(
        &self,
        exchange: &str,
        routing_key: &str,
        messages: Vec<Message>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("rabbitmq-producer");
        let mut span = tracer
            .span_builder(format!("{} batch_publish", exchange))
            .with_kind(SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("messaging.batch.message_count", messages.len() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut confirms = Vec::new();
        let mut success_count = 0;
        let mut failure_count = 0;

        for message in messages {
            let payload = serde_json::to_vec(&message)?;
            let properties = inject_trace_context(&cx, &message);

            match self
                .channel
                .basic_publish(
                    exchange,
                    routing_key,
                    BasicPublishOptions::default(),
                    &payload,
                    properties,
                )
                .await
            {
                Ok(confirm) => {
                    confirms.push(confirm);
                    success_count += 1;
                }
                Err(e) => {
                    failure_count += 1;
                    cx.span().add_event("Batch item failed", vec![
                        KeyValue::new("message.id", message.id),
                        KeyValue::new("error", format!("{:?}", e)),
                    ]);
                }
            }
        }

        // 等待所有 Confirm
        for confirm in confirms {
            confirm.await?;
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

## 6. Consumer 追踪

### 6.1 基础消费追踪

```rust
use lapin::{
    Consumer,
    options::{BasicConsumeOptions, QueueDeclareOptions},
};
use futures::StreamExt;

/// RabbitMQ Consumer（支持追踪）
pub struct TracedConsumer {
    consumer: Consumer,
}

impl TracedConsumer {
    pub fn new(consumer: Consumer) -> Self {
        Self { consumer }
    }

    /// 处理消费消息（带追踪）
    pub async fn process_messages<F, Fut>(
        mut self,
        mut handler: F,
    ) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(Message, Context) -> Fut,
        Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
    {
        while let Some(delivery) = self.consumer.next().await {
            let delivery = delivery?;
            let tracer = global::tracer("rabbitmq-consumer");

            // 提取 Trace Context
            let parent_cx = extract_trace_context(&delivery.properties);

            let mut span = tracer
                .span_builder(format!("{} receive", delivery.routing_key))
                .with_kind(SpanKind::Consumer)
                .with_attributes(vec![
                    KeyValue::new("messaging.system", "rabbitmq"),
                    KeyValue::new("messaging.operation", "receive"),
                    KeyValue::new("messaging.rabbitmq.routing_key", delivery.routing_key.to_string()),
                    KeyValue::new("messaging.rabbitmq.delivery_tag", delivery.delivery_tag as i64),
                    KeyValue::new("messaging.rabbitmq.redelivered", delivery.redelivered),
                    KeyValue::new("messaging.message.payload_size", delivery.data.len() as i64),
                ])
                .start_with_context(&tracer, &parent_cx);

            let cx = parent_cx.with_span(span);
            let _guard = cx.attach();

            // 解析消息
            match serde_json::from_slice::<Message>(&delivery.data) {
                Ok(message) => {
                    cx.span().set_attribute(KeyValue::new("messaging.message.id", message.id.clone()));

                    // 调用处理函数
                    if let Err(e) = handler(message, cx.clone()).await {
                        cx.span().record_error(&*e);
                        cx.span().add_event("Message processing failed", vec![]);

                        // Nack 消息
                        delivery
                            .nack(lapin::options::BasicNackOptions {
                                requeue: true,
                                multiple: false,
                            })
                            .await?;
                    } else {
                        cx.span().add_event("Message processed successfully", vec![]);

                        // Ack 消息
                        delivery.ack(lapin::options::BasicAckOptions::default()).await?;
                    }
                }
                Err(e) => {
                    cx.span().record_error(&e);
                    cx.span().add_event("Message deserialization failed", vec![]);

                    // Reject 消息（不重新入队）
                    delivery
                        .nack(lapin::options::BasicNackOptions {
                            requeue: false,
                            multiple: false,
                        })
                        .await?;
                }
            }
        }

        Ok(())
    }
}

/// 从 AMQP Properties 提取 Trace Context
fn extract_trace_context(properties: &BasicProperties) -> Context {
    use opentelemetry::propagation::{TextMapPropagator, Extractor};
    use std::collections::HashMap;

    struct HeaderExtractor(HashMap<String, String>);

    impl Extractor for HeaderExtractor {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.get(key).map(|v| v.as_str())
        }

        fn keys(&self) -> Vec<&str> {
            self.0.keys().map(|k| k.as_str()).collect()
        }
    }

    // 从 AMQP Headers 提取
    let mut headers_map = HashMap::new();
    if let Some(headers) = &properties.headers() {
        for (key, value) in headers.inner() {
            if let lapin::types::AMQPValue::LongString(s) = value {
                headers_map.insert(key.to_string(), s.to_string());
            }
        }
    }

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.extract(&HeaderExtractor(headers_map))
}
```

### 6.2 Manual Ack 追踪

```rust
/// 手动 Ack Consumer
pub async fn create_consumer_with_manual_ack(
    channel: &Channel,
    queue: &str,
) -> Result<TracedConsumer, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-consumer");
    let mut span = tracer
        .span_builder("rabbitmq.consumer.create")
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("queue.name", queue.to_string()),
            KeyValue::new("consumer.auto_ack", false),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let consumer = channel
        .basic_consume(
            queue,
            "traced-consumer",
            BasicConsumeOptions {
                no_ack: false,  // Manual Ack
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;

    cx.span().add_event("Consumer created", vec![
        KeyValue::new("consumer.tag", consumer.tag().to_string()),
    ]);

    Ok(TracedConsumer::new(consumer))
}
```

### 6.3 Prefetch 优化追踪

```rust
use lapin::options::BasicQosOptions;

/// 设置 Prefetch Count（带追踪）
pub async fn set_prefetch_with_trace(
    channel: &Channel,
    prefetch_count: u16,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-consumer");
    let mut span = tracer
        .span_builder("rabbitmq.qos.set")
        .with_attributes(vec![
            KeyValue::new("prefetch.count", prefetch_count as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    channel
        .basic_qos(prefetch_count, BasicQosOptions::default())
        .await?;

    cx.span().add_event("Prefetch count set", vec![]);
    Ok(())
}
```

---

## 7. Exchange 与 Queue 管理

### 7.1 Exchange 声明追踪

```rust
/// 声明 Exchange（带追踪）
pub async fn declare_exchange_with_trace(
    channel: &Channel,
    exchange: &str,
    exchange_type: ExchangeKind,
    durable: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-admin");
    let mut span = tracer
        .span_builder(format!("{} declare", exchange))
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("messaging.destination.name", exchange.to_string()),
            KeyValue::new("messaging.rabbitmq.exchange_type", format!("{:?}", exchange_type)),
            KeyValue::new("exchange.durable", durable),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    channel
        .exchange_declare(
            exchange,
            exchange_type,
            ExchangeDeclareOptions {
                durable,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;

    cx.span().add_event("Exchange declared", vec![]);
    Ok(())
}
```

### 7.2 Queue 声明追踪

```rust
use lapin::options::QueueDeclareOptions;

/// 声明 Queue（带追踪）
pub async fn declare_queue_with_trace(
    channel: &Channel,
    queue: &str,
    durable: bool,
    exclusive: bool,
) -> Result<lapin::Queue, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-admin");
    let mut span = tracer
        .span_builder(format!("{} declare", queue))
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("queue.name", queue.to_string()),
            KeyValue::new("queue.durable", durable),
            KeyValue::new("queue.exclusive", exclusive),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let queue_info = channel
        .queue_declare(
            queue,
            QueueDeclareOptions {
                durable,
                exclusive,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;

    cx.span().add_event("Queue declared", vec![
        KeyValue::new("queue.message_count", queue_info.message_count() as i64),
        KeyValue::new("queue.consumer_count", queue_info.consumer_count() as i64),
    ]);

    Ok(queue_info)
}
```

### 7.3 Binding 追踪

```rust
use lapin::options::QueueBindOptions;

/// 绑定 Queue 到 Exchange（带追踪）
pub async fn bind_queue_with_trace(
    channel: &Channel,
    queue: &str,
    exchange: &str,
    routing_key: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-admin");
    let mut span = tracer
        .span_builder(format!("{}->{} bind", exchange, queue))
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("queue.name", queue.to_string()),
            KeyValue::new("exchange.name", exchange.to_string()),
            KeyValue::new("routing.key", routing_key.to_string()),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    channel
        .queue_bind(
            queue,
            exchange,
            routing_key,
            QueueBindOptions::default(),
            FieldTable::default(),
        )
        .await?;

    cx.span().add_event("Queue bound to exchange", vec![]);
    Ok(())
}
```

---

## 8. Context Propagation

Context 传播已在 `inject_trace_context` 和 `extract_trace_context` 函数中实现。

### 8.1 AMQP Properties 注入

```rust
// 已在 inject_trace_context 函数中实现
// 使用 BasicProperties.headers 传递 W3C Trace Context
```

### 8.2 Headers 提取

```rust
// 已在 extract_trace_context 函数中实现
// 从 BasicProperties.headers 提取 W3C Trace Context
```

---

## 9. 错误处理与重试

### 9.1 连接断开重连

```rust
use std::time::Duration;

/// 创建带自动重连的连接
pub async fn connect_with_retry(
    amqp_url: &str,
    max_retries: u32,
) -> Result<Connection, Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-client");
    let mut span = tracer
        .span_builder("rabbitmq.connect")
        .with_attributes(vec![
            KeyValue::new("max_retries", max_retries as i64),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    for attempt in 1..=max_retries {
        match Connection::connect(amqp_url, ConnectionProperties::default()).await {
            Ok(connection) => {
                cx.span().add_event("Connected successfully", vec![
                    KeyValue::new("attempt", attempt as i64),
                ]);
                return Ok(connection);
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

### 9.2 Dead Letter Queue

```rust
/// 声明带 DLX 的 Queue
pub async fn declare_queue_with_dlx(
    channel: &Channel,
    queue: &str,
    dlx_exchange: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("rabbitmq-admin");
    let mut span = tracer
        .span_builder(format!("{} declare_with_dlx", queue))
        .start(&tracer);

    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    let mut args = FieldTable::default();
    args.insert("x-dead-letter-exchange".into(), lapin::types::AMQPValue::LongString(dlx_exchange.into()));

    channel
        .queue_declare(
            queue,
            QueueDeclareOptions {
                durable: true,
                ..Default::default()
            },
            args,
        )
        .await?;

    cx.span().add_event("Queue with DLX declared", vec![
        KeyValue::new("dlx.exchange", dlx_exchange.to_string()),
    ]);

    Ok(())
}
```

### 9.3 消息重试机制

```rust
/// 带重试的消息处理
pub async fn process_with_retry<F, Fut>(
    message: Message,
    cx: Context,
    max_retries: u32,
    mut handler: F,
) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnMut(Message) -> Fut,
    Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>
{
    for attempt in 1..=max_retries {
        cx.span().add_event("Processing attempt", vec![
            KeyValue::new("attempt", attempt as i64),
        ]);

        match handler(message.clone()).await {
            Ok(_) => {
                cx.span().add_event("Processing succeeded", vec![
                    KeyValue::new("attempt", attempt as i64),
                ]);
                return Ok(());
            }
            Err(e) if attempt < max_retries => {
                cx.span().add_event("Processing attempt failed", vec![
                    KeyValue::new("attempt", attempt as i64),
                    KeyValue::new("error", format!("{:?}", e)),
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

## 10. 性能监控

### 10.1 发布延迟监控

```rust
use opentelemetry::metrics::{Meter, Histogram};

pub struct RabbitMQMetrics {
    publish_duration: Histogram<f64>,
    consume_duration: Histogram<f64>,
    message_size: Histogram<u64>,
}

impl RabbitMQMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            publish_duration: meter
                .f64_histogram("rabbitmq.publish.duration")
                .with_unit("ms")
                .with_description("RabbitMQ publish duration")
                .build(),
            consume_duration: meter
                .f64_histogram("rabbitmq.consume.duration")
                .with_unit("ms")
                .with_description("RabbitMQ consume duration")
                .build(),
            message_size: meter
                .u64_histogram("rabbitmq.message.size")
                .with_unit("bytes")
                .with_description("RabbitMQ message size")
                .build(),
        }
    }

    pub fn record_publish(&self, duration: Duration, size: usize) {
        self.publish_duration.record(duration.as_secs_f64() * 1000.0, &[]);
        self.message_size.record(size as u64, &[]);
    }

    pub fn record_consume(&self, duration: Duration, size: usize) {
        self.consume_duration.record(duration.as_secs_f64() * 1000.0, &[]);
        self.message_size.record(size as u64, &[]);
    }
}
```

### 10.2 队列指标监控

```rust
use opentelemetry::metrics::{Counter, Gauge};

pub struct QueueMetrics {
    messages_published: Counter<u64>,
    messages_consumed: Counter<u64>,
    messages_redelivered: Counter<u64>,
    queue_depth: Gauge<i64>,
}

impl QueueMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            messages_published: meter
                .u64_counter("rabbitmq.messages.published")
                .with_description("Total messages published")
                .build(),
            messages_consumed: meter
                .u64_counter("rabbitmq.messages.consumed")
                .with_description("Total messages consumed")
                .build(),
            messages_redelivered: meter
                .u64_counter("rabbitmq.messages.redelivered")
                .with_description("Total messages redelivered")
                .build(),
            queue_depth: meter
                .i64_gauge("rabbitmq.queue.depth")
                .with_description("Current queue depth")
                .build(),
        }
    }
}
```

---

## 11. 完整生产示例

```rust
use deadpool_lapin::Pool;

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

    // 创建连接池
    let amqp_url = "amqp://guest:guest@localhost:5672/%2f";
    let pool = create_pool_with_trace(amqp_url, 10).await?;

    // 获取连接和 Channel
    let connection = get_connection_with_trace(&pool).await?;
    let channel = create_channel_with_trace(&connection).await?;

    // 启用 Confirm 模式
    let producer = TracedProducer::new(channel.clone());
    producer.enable_confirm_mode().await?;

    // 声明 Exchange 和 Queue
    declare_exchange_with_trace(&channel, "orders", ExchangeKind::Direct, true).await?;
    declare_queue_with_trace(&channel, "order-processing", true, false).await?;
    bind_queue_with_trace(&channel, "order-processing", "orders", "new").await?;

    // 发布消息
    let message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        payload: "Order #12345".to_string(),
    };
    producer.publish_with_confirm("orders", "new", &message).await?;

    // 创建 Consumer 并处理消息
    set_prefetch_with_trace(&channel, 10).await?;
    let consumer = create_consumer_with_manual_ack(&channel, "order-processing").await?;

    consumer
        .process_messages(|msg, cx| async move {
            println!("Processing message: {:?}", msg);
            // 业务逻辑...
            Ok(())
        })
        .await?;

    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}
```

---

## 总结

本指南涵盖了 RabbitMQ 与 OpenTelemetry 集成的完整实现：

1. **连接管理**：连接池、Channel 创建
2. **Producer 追踪**：基础发布、Confirm 模式、批量发布
3. **Consumer 追踪**：Manual Ack、Prefetch 优化
4. **管理操作**：Exchange/Queue 声明、Binding
5. **Context 传播**：通过 AMQP Properties 传递 W3C Trace Context
6. **错误处理**：连接重试、DLX、消息重试
7. **性能监控**：发布/消费延迟、队列深度

通过这些实现，您可以在生产环境中获得 RabbitMQ 消息系统的完整可观测性。
