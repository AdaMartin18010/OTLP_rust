# Kafka - Rust 完整追踪

> **Rust版本**: 1.90+  
> **rdkafka**: 0.36.2  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [Kafka - Rust 完整追踪](#kafka---rust-完整追踪)
  - [目录](#目录)
  - [1. Kafka 追踪概述](#1-kafka-追踪概述)
    - [Kafka 语义约定](#kafka-语义约定)
  - [2. 依赖配置](#2-依赖配置)
  - [3. Producer 追踪](#3-producer-追踪)
    - [3.1 基础 Producer](#31-基础-producer)
    - [3.2 批量发送](#32-批量发送)
  - [4. Consumer 追踪](#4-consumer-追踪)
    - [4.1 基础 Consumer](#41-基础-consumer)
  - [5. Context 传播](#5-context-传播)
    - [5.1 端到端追踪](#51-端到端追踪)
  - [6. 批量处理追踪](#6-批量处理追踪)
    - [6.1 批量消费](#61-批量消费)
  - [7. 错误处理](#7-错误处理)
    - [7.1 重试机制](#71-重试机制)
  - [8. 性能监控](#8-性能监控)
    - [8.1 指标收集](#81-指标收集)
  - [9. 完整示例](#9-完整示例)

---

## 1. Kafka 追踪概述

### Kafka 语义约定

```rust
use opentelemetry_semantic_conventions::trace::{
    MESSAGING_SYSTEM,
    MESSAGING_DESTINATION,
    MESSAGING_DESTINATION_KIND,
    MESSAGING_OPERATION,
    MESSAGING_MESSAGE_ID,
    MESSAGING_KAFKA_PARTITION,
};

/// Kafka Span 属性
#[derive(Debug)]
pub struct KafkaAttributes {
    pub system: String,              // "kafka"
    pub destination: String,         // topic name
    pub destination_kind: String,    // "topic"
    pub operation: String,           // "publish" or "receive"
    pub partition: Option<i32>,
    pub message_key: Option<String>,
    pub consumer_group: Option<String>,
}

impl KafkaAttributes {
    pub fn producer(topic: &str, partition: i32) -> Self {
        Self {
            system: "kafka".to_string(),
            destination: topic.to_string(),
            destination_kind: "topic".to_string(),
            operation: "publish".to_string(),
            partition: Some(partition),
            message_key: None,
            consumer_group: None,
        }
    }
    
    pub fn consumer(topic: &str, group: &str) -> Self {
        Self {
            system: "kafka".to_string(),
            destination: topic.to_string(),
            destination_kind: "topic".to_string(),
            operation: "receive".to_string(),
            partition: None,
            message_key: None,
            consumer_group: Some(group.to_string()),
        }
    }
}
```

---

## 2. 依赖配置

```toml
[dependencies]
# Kafka
rdkafka = { version = "0.36", features = ["cmake-build", "ssl", "tracing"] }

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# Tracing
tracing = "0.1"
tracing-opentelemetry = "0.31"
tracing-subscriber = "0.3"

# Async runtime
tokio = { version = "1.47", features = ["full"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

---

## 3. Producer 追踪

### 3.1 基础 Producer

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;
use opentelemetry::propagation::{Injector, TextMapPropagator};
use opentelemetry::global;

/// 带追踪的 Kafka Producer
pub struct TracedKafkaProducer {
    producer: FutureProducer,
}

impl TracedKafkaProducer {
    /// 创建 Producer
    pub fn new(brokers: &str) -> Result<Self, rdkafka::error::KafkaError> {
        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .set("compression.type", "lz4")
            .create()?;
        
        Ok(Self { producer })
    }
    
    /// 发送消息 (带追踪)
    #[tracing::instrument(skip(self, payload))]
    pub async fn send_message(
        &self,
        topic: &str,
        key: Option<&str>,
        payload: &[u8],
    ) -> Result<(i32, i64), Box<dyn std::error::Error>> {
        let span = tracing::Span::current();
        
        // 设置 Kafka 属性
        span.record("messaging.system", "kafka");
        span.record("messaging.destination", topic);
        span.record("messaging.operation", "publish");
        
        // 创建消息
        let mut record = FutureRecord::to(topic)
            .payload(payload);
        
        if let Some(k) = key {
            record = record.key(k);
            span.record("messaging.message.key", k);
        }
        
        // 注入追踪 context 到 headers
        let mut headers = rdkafka::message::OwnedHeaders::new();
        inject_trace_context(&mut headers);
        record = record.headers(headers);
        
        // 发送消息
        let start = std::time::Instant::now();
        let result = self.producer.send(record, std::time::Duration::from_secs(5)).await;
        let duration = start.elapsed();
        
        match result {
            Ok((partition, offset)) => {
                span.record("messaging.kafka.partition", partition);
                span.record("messaging.kafka.offset", offset);
                span.record("duration_ms", duration.as_millis() as i64);
                
                tracing::info!(
                    partition,
                    offset,
                    duration_ms = duration.as_millis(),
                    "Message sent successfully"
                );
                
                Ok((partition, offset))
            }
            Err((e, _)) => {
                tracing::error!("Failed to send message: {:?}", e);
                Err(Box::new(e))
            }
        }
    }
}

/// 注入追踪 context 到 Kafka headers
fn inject_trace_context(headers: &mut rdkafka::message::OwnedHeaders) {
    struct KafkaHeaderInjector<'a>(&'a mut rdkafka::message::OwnedHeaders);
    
    impl<'a> Injector for KafkaHeaderInjector<'a> {
        fn set(&mut self, key: &str, value: String) {
            self.0.insert(rdkafka::message::Header {
                key,
                value: Some(&value.as_bytes()),
            });
        }
    }
    
    let context = opentelemetry::Context::current();
    let mut injector = KafkaHeaderInjector(headers);
    
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&context, &mut injector);
    });
}
```

### 3.2 批量发送

```rust
impl TracedKafkaProducer {
    /// 批量发送消息
    #[tracing::instrument(skip(self, messages))]
    pub async fn send_batch(
        &self,
        topic: &str,
        messages: Vec<(Option<String>, Vec<u8>)>,
    ) -> Result<Vec<(i32, i64)>, Box<dyn std::error::Error>> {
        tracing::info!(count = messages.len(), "Sending batch of messages");
        
        let mut results = Vec::with_capacity(messages.len());
        
        for (key, payload) in messages {
            let result = self.send_message(
                topic,
                key.as_deref(),
                &payload,
            ).await?;
            
            results.push(result);
        }
        
        tracing::info!(count = results.len(), "Batch sent successfully");
        
        Ok(results)
    }
}
```

---

## 4. Consumer 追踪

### 4.1 基础 Consumer

```rust
use rdkafka::consumer::{StreamConsumer, Consumer};
use rdkafka::Message;
use opentelemetry::propagation::{Extractor, TextMapPropagator};

/// 带追踪的 Kafka Consumer
pub struct TracedKafkaConsumer {
    consumer: StreamConsumer,
}

impl TracedKafkaConsumer {
    /// 创建 Consumer
    pub fn new(
        brokers: &str,
        group_id: &str,
        topics: &[&str],
    ) -> Result<Self, rdkafka::error::KafkaError> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("group.id", group_id)
            .set("enable.auto.commit", "true")
            .set("auto.offset.reset", "earliest")
            .create()?;
        
        consumer.subscribe(topics)?;
        
        Ok(Self { consumer })
    }
    
    /// 处理消息 (带追踪)
    #[tracing::instrument(skip(self, handler))]
    pub async fn consume_messages<F, Fut>(
        &self,
        mut handler: F,
    ) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(Vec<u8>) -> Fut,
        Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
    {
        use rdkafka::consumer::MessageStream;
        use futures::StreamExt;
        
        let mut stream = self.consumer.stream();
        
        while let Some(message) = stream.next().await {
            match message {
                Ok(msg) => {
                    // 提取追踪 context
                    let parent_context = extract_trace_context(&msg);
                    let _guard = parent_context.attach();
                    
                    // 创建 span
                    let span = tracing::info_span!(
                        "kafka.receive",
                        messaging.system = "kafka",
                        messaging.destination = msg.topic(),
                        messaging.operation = "receive",
                        messaging.kafka.partition = msg.partition(),
                        messaging.kafka.offset = msg.offset(),
                    );
                    
                    let _enter = span.enter();
                    
                    // 处理消息
                    if let Some(payload) = msg.payload() {
                        tracing::debug!(size = payload.len(), "Processing message");
                        
                        match handler(payload.to_vec()).await {
                            Ok(_) => {
                                tracing::info!("Message processed successfully");
                            }
                            Err(e) => {
                                tracing::error!("Error processing message: {}", e);
                            }
                        }
                    }
                }
                Err(e) => {
                    tracing::error!("Kafka error: {}", e);
                }
            }
        }
        
        Ok(())
    }
}

/// 从 Kafka headers 提取追踪 context
fn extract_trace_context(msg: &impl Message) -> opentelemetry::Context {
    struct KafkaHeaderExtractor<'a>(&'a dyn Message);
    
    impl<'a> Extractor for KafkaHeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.headers()?.iter().find_map(|header| {
                if header.key == key {
                    header.value.and_then(|v| std::str::from_utf8(v).ok())
                } else {
                    None
                }
            })
        }
        
        fn keys(&self) -> Vec<&str> {
            self.0.headers()
                .map(|h| h.iter().map(|h| h.key).collect())
                .unwrap_or_default()
        }
    }
    
    let extractor = KafkaHeaderExtractor(msg);
    
    global::get_text_map_propagator(|propagator| {
        propagator.extract(&extractor)
    })
}
```

---

## 5. Context 传播

### 5.1 端到端追踪

```rust
/// 完整的 Producer -> Consumer 追踪示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    init_telemetry().await?;
    
    // 创建 producer
    let producer = TracedKafkaProducer::new("localhost:9092")?;
    
    // 在 span 中发送消息
    let _span = tracing::info_span!("send_order").entered();
    
    let order = serde_json::json!({
        "order_id": "12345",
        "amount": 99.99,
    });
    
    producer.send_message(
        "orders",
        Some("12345"),
        order.to_string().as_bytes(),
    ).await?;
    
    // 创建 consumer
    let consumer = TracedKafkaConsumer::new(
        "localhost:9092",
        "order-processor",
        &["orders"],
    )?;
    
    // 处理消息 (trace context 自动传播)
    consumer.consume_messages(|payload| async move {
        let order: serde_json::Value = serde_json::from_slice(&payload)?;
        
        tracing::info!("Processing order: {:?}", order);
        
        // 业务逻辑
        process_order(order).await?;
        
        Ok(())
    }).await?;
    
    Ok(())
}

#[tracing::instrument]
async fn process_order(order: serde_json::Value) -> Result<(), Box<dyn std::error::Error>> {
    // 订单处理逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    tracing::info!("Order processed");
    
    Ok(())
}
```

---

## 6. 批量处理追踪

### 6.1 批量消费

```rust
impl TracedKafkaConsumer {
    /// 批量消费消息
    #[tracing::instrument(skip(self, handler))]
    pub async fn consume_batch<F, Fut>(
        &self,
        batch_size: usize,
        timeout: std::time::Duration,
        mut handler: F,
    ) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(Vec<Vec<u8>>) -> Fut,
        Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
    {
        use rdkafka::consumer::MessageStream;
        use futures::StreamExt;
        
        let mut stream = self.consumer.stream();
        let mut batch = Vec::with_capacity(batch_size);
        let mut last_process = std::time::Instant::now();
        
        while let Some(message) = stream.next().await {
            if let Ok(msg) = message {
                if let Some(payload) = msg.payload() {
                    batch.push(payload.to_vec());
                    
                    // 达到批量大小或超时，处理批次
                    if batch.len() >= batch_size || last_process.elapsed() > timeout {
                        let _span = tracing::info_span!(
                            "process_batch",
                            count = batch.len()
                        ).entered();
                        
                        handler(std::mem::take(&mut batch)).await?;
                        
                        last_process = std::time::Instant::now();
                    }
                }
            }
        }
        
        Ok(())
    }
}
```

---

## 7. 错误处理

### 7.1 重试机制

```rust
use std::time::Duration;

impl TracedKafkaProducer {
    /// 带重试的发送
    #[tracing::instrument(skip(self, payload))]
    pub async fn send_with_retry(
        &self,
        topic: &str,
        key: Option<&str>,
        payload: &[u8],
        max_retries: usize,
    ) -> Result<(i32, i64), Box<dyn std::error::Error>> {
        let mut attempts = 0;
        let mut delay = Duration::from_millis(100);
        
        loop {
            match self.send_message(topic, key, payload).await {
                Ok(result) => return Ok(result),
                Err(e) if attempts < max_retries => {
                    attempts += 1;
                    tracing::warn!(
                        attempt = attempts,
                        max_retries,
                        "Retrying after error: {}",
                        e
                    );
                    
                    tokio::time::sleep(delay).await;
                    delay *= 2; // 指数退避
                }
                Err(e) => {
                    tracing::error!("Failed after {} attempts", attempts + 1);
                    return Err(e);
                }
            }
        }
    }
}
```

---

## 8. 性能监控

### 8.1 指标收集

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct KafkaMetrics {
    messages_sent: Counter<u64>,
    messages_received: Counter<u64>,
    send_duration: Histogram<f64>,
    receive_duration: Histogram<f64>,
}

impl KafkaMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            messages_sent: meter
                .u64_counter("kafka.messages.sent")
                .with_description("Total messages sent")
                .init(),
            
            messages_received: meter
                .u64_counter("kafka.messages.received")
                .with_description("Total messages received")
                .init(),
            
            send_duration: meter
                .f64_histogram("kafka.send.duration")
                .with_unit("ms")
                .init(),
            
            receive_duration: meter
                .f64_histogram("kafka.receive.duration")
                .with_unit("ms")
                .init(),
        }
    }
    
    pub fn record_send(&self, duration: Duration) {
        self.messages_sent.add(1, &[]);
        self.send_duration.record(duration.as_secs_f64() * 1000.0, &[]);
    }
    
    pub fn record_receive(&self, duration: Duration) {
        self.messages_received.add(1, &[]);
        self.receive_duration.record(duration.as_secs_f64() * 1000.0, &[]);
    }
}
```

---

## 9. 完整示例

**生产级 Kafka 集成**:

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化
    init_telemetry().await?;
    
    // Producer 任务
    let producer_handle = tokio::spawn(async move {
        let producer = TracedKafkaProducer::new("localhost:9092").unwrap();
        
        for i in 0..100 {
            let message = format!("Message {}", i);
            
            producer.send_with_retry(
                "test-topic",
                Some(&format!("key-{}", i)),
                message.as_bytes(),
                3,
            ).await.unwrap();
            
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    // Consumer 任务
    let consumer_handle = tokio::spawn(async move {
        let consumer = TracedKafkaConsumer::new(
            "localhost:9092",
            "test-group",
            &["test-topic"],
        ).unwrap();
        
        consumer.consume_messages(|payload| async move {
            let message = String::from_utf8(payload)?;
            tracing::info!("Received: {}", message);
            Ok(())
        }).await.unwrap();
    });
    
    // 等待完成
    tokio::try_join!(producer_handle, consumer_handle)?;
    
    Ok(())
}
```

---

**相关文档**:

- [NATS 追踪](02_NATS_Rust完整追踪.md)
- [Context Propagation](../04_核心组件/04_Context_Propagation详解_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
