# Rdkafka 完整实现：高性能消息队列 Rust 1.90 + OTLP 完整实现指南

## 目录

- [Rdkafka 完整实现：高性能消息队列 Rust 1.90 + OTLP 完整实现指南](#rdkafka-完整实现高性能消息队列-rust-190--otlp-完整实现指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Rdkafka 定位](#11-rdkafka-定位)
      - [核心优势](#核心优势)
    - [1.2 Kafka 核心概念](#12-kafka-核心概念)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. Rdkafka 核心架构](#2-rdkafka-核心架构)
    - [2.1 三层架构](#21-三层架构)
    - [2.2 消息流程](#22-消息流程)
  - [3. 项目初始化与配置](#3-项目初始化与配置)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 环境配置](#32-环境配置)
  - [4. 生产者实现](#4-生产者实现)
    - [4.1 基础生产者](#41-基础生产者)
    - [4.2 幂等性生产者](#42-幂等性生产者)
    - [4.3 批量发送](#43-批量发送)
    - [4.4 序列化消息](#44-序列化消息)
  - [5. 消费者实现](#5-消费者实现)
    - [5.1 基础消费者](#51-基础消费者)
    - [5.2 反序列化消息](#52-反序列化消息)
    - [5.3 批量消费](#53-批量消费)
  - [6. 消息序列化与反序列化](#6-消息序列化与反序列化)
    - [6.1 JSON 序列化](#61-json-序列化)
    - [6.2 Bincode 序列化（更高性能）](#62-bincode-序列化更高性能)
    - [6.3 Schema Registry 集成（Avro）](#63-schema-registry-集成avro)
  - [7. 事务消息](#7-事务消息)
    - [7.1 事务生产者](#71-事务生产者)
    - [7.2 事务消费者（Consume-Transform-Produce）](#72-事务消费者consume-transform-produce)
  - [8. Exactly-Once 语义](#8-exactly-once-语义)
    - [8.1 配置](#81-配置)
  - [9. 错误处理与重试](#9-错误处理与重试)
    - [9.1 生产者错误处理](#91-生产者错误处理)
    - [9.2 消费者错误处理](#92-消费者错误处理)
  - [10. 性能优化](#10-性能优化)
    - [10.1 生产者优化](#101-生产者优化)
    - [10.2 消费者优化](#102-消费者优化)
  - [11. 监控与指标](#11-监控与指标)
    - [11.1 生产者统计](#111-生产者统计)
    - [11.2 自定义指标](#112-自定义指标)
  - [12. OTLP 分布式追踪集成](#12-otlp-分布式追踪集成)
    - [12.1 OTLP 初始化](#121-otlp-初始化)
    - [12.2 追踪生产者](#122-追踪生产者)
    - [12.3 追踪消费者](#123-追踪消费者)
  - [13. 死信队列](#13-死信队列)
    - [13.1 实现死信队列](#131-实现死信队列)
  - [14. 测试策略](#14-测试策略)
    - [14.1 集成测试（使用 Testcontainers）](#141-集成测试使用-testcontainers)
  - [15. 生产环境部署](#15-生产环境部署)
    - [15.1 Docker Compose](#151-docker-compose)
  - [16. 国际标准对标](#16-国际标准对标)
    - [16.1 对标清单](#161-对标清单)
  - [17. 总结与最佳实践](#17-总结与最佳实践)
    - [17.1 最佳实践](#171-最佳实践)
      - [✅ 推荐做法](#-推荐做法)
      - [❌ 避免做法](#-避免做法)

---

## 1. 概述

### 1.1 Rdkafka 定位

**Rdkafka** 是 Rust 生态中 Kafka 客户端的事实标准，基于 **librdkafka** (C 库) 封装，提供高性能、零拷贝的消息队列访问。

#### 核心优势

- **极致性能**：基于 librdkafka，吞吐量百万级/秒
- **零拷贝**：直接操作底层内存，减少分配
- **功能完整**：Producer、Consumer、Streaming、事务、幂等性
- **生产就绪**：广泛应用于金融、电商、物联网
- **异步支持**：完整的 Tokio 集成

### 1.2 Kafka 核心概念

```text
┌─────────────────────────────────────────┐
│             Kafka Cluster               │
│  ┌───────────┐  ┌───────────┐           │
│  │ Broker 1  │  │ Broker 2  │           │
│  └───────────┘  └───────────┘           │
├─────────────────────────────────────────┤
│              Topics                     │
│  ┌─────────────────────────────────┐    │
│  │  Topic: orders                  │    │
│  │  ┌─────────┐ ┌─────────┐        │    │
│  │  │ Part 0  │ │ Part 1  │ ...    │    │
│  │  └─────────┘ └─────────┘        │    │
│  └─────────────────────────────────┘    │
└─────────────────────────────────────────┘

┌─────────────┐         ┌─────────────┐
│  Producer   │────────>│  Consumer   │
└─────────────┘         └─────────────┘
```

### 1.3 国际标准对标

| 标准/协议 | Rdkafka 实现 |
|----------|-------------|
| **Kafka Protocol** | ✅ 完整支持 |
| **SASL/SCRAM** | ✅ 认证支持 |
| **SSL/TLS** | ✅ 加密支持 |
| **Exactly-Once** | ✅ 完整支持 |
| **Transactions** | ✅ 完整支持 |
| **Idempotent Producer** | ✅ 完整支持 |

---

## 2. Rdkafka 核心架构

### 2.1 三层架构

```text
┌────────────────────────────────────────┐
│       Application Layer                │
│  ┌──────────────┐  ┌──────────────┐    │
│  │  Producer    │  │  Consumer    │    │
│  └──────────────┘  └──────────────┘    │
├────────────────────────────────────────┤
│         Rdkafka Layer                  │
│  ┌──────────┐  ┌──────────┐            │
│  │  Async   │  │  Sync    │            │
│  └──────────┘  └──────────┘            │
├────────────────────────────────────────┤
│         Librdkafka (C)                 │
│  ┌──────────────────────────────────┐  │
│  │  Network, Protocol, Compression  │  │
│  └──────────────────────────────────┘  │
└────────────────────────────────────────┘
```

### 2.2 消息流程

```text
Producer:
┌──────────────┐
│ Create Msg   │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Serialize    │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Send to      │
│ Kafka        │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Wait ACK     │
└──────────────┘

Consumer:
┌──────────────┐
│ Poll Message │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Deserialize  │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Process      │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Commit       │
│ Offset       │
└──────────────┘
```

---

## 3. 项目初始化与配置

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "rdkafka-advanced-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Kafka 客户端
rdkafka = { version = "0.36", features = ["cmake-build", "ssl", "sasl", "zstd", "gssapi"] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
bincode = "1.3"

# 工具库
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
thiserror = "1.0"
anyhow = "1.0"

# 追踪与指标
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"
opentelemetry = { version = "0.25", features = ["trace"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["trace", "grpc-tonic"] }
opentelemetry-semantic-conventions = "0.25"

# 配置
config = "0.14"
dotenvy = "0.15"

# 测试
[dev-dependencies]
testcontainers = "0.21"
```

### 3.2 环境配置

```bash
# .env
KAFKA_BROKERS=localhost:9092
KAFKA_TOPIC=orders
KAFKA_GROUP_ID=order-processor
KAFKA_SECURITY_PROTOCOL=PLAINTEXT

# 如果使用 SASL
KAFKA_SASL_MECHANISM=SCRAM-SHA-512
KAFKA_SASL_USERNAME=user
KAFKA_SASL_PASSWORD=password

# OTLP
OTLP_ENDPOINT=http://localhost:4317
SERVICE_NAME=rdkafka-advanced-demo
```

---

## 4. 生产者实现

### 4.1 基础生产者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::util::Timeout;
use std::time::Duration;
use tracing::{info, error};

pub fn create_producer(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("message.timeout.ms", "30000")
        .set("queue.buffering.max.messages", "100000")
        .set("queue.buffering.max.kbytes", "1048576")
        .set("batch.num.messages", "10000")
        .set("compression.type", "lz4")
        .create()?;
    
    Ok(producer)
}

pub async fn send_message(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let record = FutureRecord::to(topic)
        .key(key)
        .payload(payload);
    
    let delivery_status = producer.send(record, Timeout::After(Duration::from_secs(10))).await;
    
    match delivery_status {
        Ok((partition, offset)) => {
            info!("Message delivered to partition {} at offset {}", partition, offset);
            Ok(())
        }
        Err((e, _)) => {
            error!("Failed to deliver message: {:?}", e);
            Err(Box::new(e))
        }
    }
}
```

### 4.2 幂等性生产者

```rust
pub fn create_idempotent_producer(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", brokers)
        
        // 启用幂等性
        .set("enable.idempotence", "true")
        
        // 幂等性要求的配置
        .set("max.in.flight.requests.per.connection", "5")
        .set("retries", "2147483647")  // 最大重试
        .set("acks", "all")             // 所有副本确认
        
        // 性能优化
        .set("linger.ms", "10")
        .set("batch.size", "16384")
        
        .create()?;
    
    Ok(producer)
}
```

### 4.3 批量发送

```rust
use futures::future::join_all;

pub async fn send_batch(
    producer: &FutureProducer,
    topic: &str,
    messages: Vec<(String, String)>,  // (key, payload)
) -> Result<(), Box<dyn std::error::Error>> {
    let futures = messages
        .into_iter()
        .map(|(key, payload)| {
            let record = FutureRecord::to(topic)
                .key(&key)
                .payload(&payload);
            
            producer.send(record, Timeout::After(Duration::from_secs(10)))
        });
    
    let results = join_all(futures).await;
    
    let mut errors = Vec::new();
    
    for (i, result) in results.into_iter().enumerate() {
        match result {
            Ok((partition, offset)) => {
                info!("Message {} delivered to partition {} at offset {}", i, partition, offset);
            }
            Err((e, _)) => {
                error!("Message {} failed: {:?}", i, e);
                errors.push(e);
            }
        }
    }
    
    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!("{} messages failed", errors.len()).into())
    }
}
```

### 4.4 序列化消息

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct OrderMessage {
    pub order_id: uuid::Uuid,
    pub user_id: u64,
    pub amount: f64,
    pub currency: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub async fn send_order(
    producer: &FutureProducer,
    topic: &str,
    order: OrderMessage,
) -> Result<(), Box<dyn std::error::Error>> {
    let key = order.order_id.to_string();
    let payload = serde_json::to_string(&order)?;
    
    send_message(producer, topic, &key, &payload).await
}
```

---

## 5. 消费者实现

### 5.1 基础消费者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{StreamConsumer, Consumer};
use rdkafka::Message;
use futures::StreamExt;

pub fn create_consumer(brokers: &str, group_id: &str) -> Result<StreamConsumer, rdkafka::error::KafkaError> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("group.id", group_id)
        .set("enable.auto.commit", "false")  // 手动提交
        .set("auto.offset.reset", "earliest")
        .set("session.timeout.ms", "30000")
        .set("heartbeat.interval.ms", "3000")
        .create()?;
    
    Ok(consumer)
}

pub async fn consume_messages(
    consumer: &StreamConsumer,
    topics: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                let key = m.key().map(|k| String::from_utf8_lossy(k).to_string());
                let payload = m.payload().map(|p| String::from_utf8_lossy(p).to_string());
                
                info!(
                    "Received message: topic={}, partition={}, offset={}, key={:?}",
                    m.topic(),
                    m.partition(),
                    m.offset(),
                    key
                );
                
                // 处理消息
                if let Some(payload) = payload {
                    process_message(payload).await?;
                }
                
                // 手动提交
                consumer.commit_message(&m, rdkafka::consumer::CommitMode::Async)?;
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn process_message(payload: String) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    info!("Processing message: {}", payload);
    Ok(())
}
```

### 5.2 反序列化消息

```rust
pub async fn consume_orders(
    consumer: &StreamConsumer,
    topics: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                if let Some(payload) = m.payload() {
                    match serde_json::from_slice::<OrderMessage>(payload) {
                        Ok(order) => {
                            info!("Processing order: {:?}", order);
                            
                            // 业务逻辑
                            handle_order(order).await?;
                            
                            // 提交偏移量
                            consumer.commit_message(&m, rdkafka::consumer::CommitMode::Async)?;
                        }
                        Err(e) => {
                            error!("Failed to deserialize message: {:?}", e);
                            // 发送到死信队列
                            send_to_dlq(&m).await?;
                        }
                    }
                }
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn handle_order(order: OrderMessage) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    Ok(())
}

async fn send_to_dlq(message: &impl Message) -> Result<(), Box<dyn std::error::Error>> {
    // 发送到死信队列
    Ok(())
}
```

### 5.3 批量消费

```rust
use rdkafka::consumer::Consumer;
use rdkafka::message::BorrowedMessage;

pub async fn batch_consume(
    consumer: &StreamConsumer,
    topics: &[&str],
    batch_size: usize,
    batch_timeout: Duration,
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;
    
    let mut message_stream = consumer.stream();
    let mut batch = Vec::new();
    let mut last_batch_time = tokio::time::Instant::now();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                batch.push(m);
                
                // 达到批量大小或超时
                if batch.len() >= batch_size || last_batch_time.elapsed() >= batch_timeout {
                    process_batch(&batch).await?;
                    
                    // 批量提交偏移量
                    if let Some(last_msg) = batch.last() {
                        consumer.commit_message(last_msg, rdkafka::consumer::CommitMode::Async)?;
                    }
                    
                    batch.clear();
                    last_batch_time = tokio::time::Instant::now();
                }
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn process_batch(messages: &[BorrowedMessage<'_>]) -> Result<(), Box<dyn std::error::Error>> {
    info!("Processing batch of {} messages", messages.len());
    
    for msg in messages {
        if let Some(payload) = msg.payload() {
            if let Ok(order) = serde_json::from_slice::<OrderMessage>(payload) {
                handle_order(order).await?;
            }
        }
    }
    
    Ok(())
}
```

---

## 6. 消息序列化与反序列化

### 6.1 JSON 序列化

```rust
use serde::{Serialize, Deserialize};

pub trait MessageCodec: Sized {
    fn encode(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>>;
    fn decode(data: &[u8]) -> Result<Self, Box<dyn std::error::Error>>;
}

impl<T: Serialize + for<'de> Deserialize<'de>> MessageCodec for T {
    fn encode(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        Ok(serde_json::to_vec(self)?)
    }
    
    fn decode(data: &[u8]) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(serde_json::from_slice(data)?)
    }
}
```

### 6.2 Bincode 序列化（更高性能）

```rust
pub struct BincodeCodec;

impl BincodeCodec {
    pub fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        Ok(bincode::serialize(value)?)
    }
    
    pub fn decode<'a, T: Deserialize<'a>>(data: &'a [u8]) -> Result<T, Box<dyn std::error::Error>> {
        Ok(bincode::deserialize(data)?)
    }
}
```

### 6.3 Schema Registry 集成（Avro）

```rust
// 需要额外依赖: schema_registry_converter
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct OrderAvro {
    pub order_id: String,
    pub user_id: i64,
    pub amount: f64,
}

// 使用 Schema Registry 编码/解码
// pub async fn encode_avro(order: &OrderAvro) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
//     // 与 Schema Registry 交互
//     // ...
//     Ok(vec![])
// }
```

---

## 7. 事务消息

### 7.1 事务生产者

```rust
use rdkafka::producer::Producer;

pub fn create_transactional_producer(
    brokers: &str,
    transactional_id: &str,
) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", brokers)
        
        // 事务配置
        .set("transactional.id", transactional_id)
        .set("enable.idempotence", "true")
        .set("acks", "all")
        
        .create()?;
    
    // 初始化事务
    producer.init_transactions(Timeout::After(Duration::from_secs(10)))?;
    
    Ok(producer)
}

pub async fn send_transactional_messages(
    producer: &FutureProducer,
    topic: &str,
    messages: Vec<(String, String)>,
) -> Result<(), Box<dyn std::error::Error>> {
    // 开始事务
    producer.begin_transaction()?;
    
    // 发送消息
    for (key, payload) in messages {
        let record = FutureRecord::to(topic)
            .key(&key)
            .payload(&payload);
        
        match producer.send(record, Timeout::After(Duration::from_secs(10))).await {
            Ok(_) => {}
            Err((e, _)) => {
                error!("Failed to send message: {:?}", e);
                
                // 回滚事务
                producer.abort_transaction(Timeout::After(Duration::from_secs(10)))?;
                
                return Err(Box::new(e));
            }
        }
    }
    
    // 提交事务
    producer.commit_transaction(Timeout::After(Duration::from_secs(10)))?;
    
    info!("Transaction committed successfully");
    
    Ok(())
}
```

### 7.2 事务消费者（Consume-Transform-Produce）

```rust
use rdkafka::consumer::CommitMode;

pub async fn transactional_consume_produce(
    consumer: &StreamConsumer,
    producer: &FutureProducer,
    input_topic: &str,
    output_topic: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(&[input_topic])?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                // 开始事务
                producer.begin_transaction()?;
                
                // 处理消息
                if let Some(payload) = m.payload() {
                    let input_data = String::from_utf8_lossy(payload);
                    let output_data = transform(input_data.to_string()).await?;
                    
                    // 发送到输出主题
                    let record = FutureRecord::to(output_topic)
                        .key(m.key().unwrap_or(b""))
                        .payload(&output_data);
                    
                    match producer.send(record, Timeout::After(Duration::from_secs(10))).await {
                        Ok(_) => {
                            // 提交消费者偏移量到事务
                            producer.send_offsets_to_transaction(
                                &consumer.position()?,
                                consumer.group_metadata().as_ref(),
                                Timeout::After(Duration::from_secs(10)),
                            )?;
                            
                            // 提交事务
                            producer.commit_transaction(Timeout::After(Duration::from_secs(10)))?;
                        }
                        Err((e, _)) => {
                            error!("Failed to send transformed message: {:?}", e);
                            
                            // 回滚事务
                            producer.abort_transaction(Timeout::After(Duration::from_secs(10)))?;
                        }
                    }
                }
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn transform(input: String) -> Result<String, Box<dyn std::error::Error>> {
    // 转换逻辑
    Ok(input.to_uppercase())
}
```

---

## 8. Exactly-Once 语义

### 8.1 配置

```rust
// 生产者
pub fn create_exactly_once_producer(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("transactional.id", "my-transactional-id")
        .set("enable.idempotence", "true")
        .set("acks", "all")
        .set("retries", "2147483647")
        .set("max.in.flight.requests.per.connection", "5")
        .create()
}

// 消费者
pub fn create_exactly_once_consumer(brokers: &str, group_id: &str) -> Result<StreamConsumer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("group.id", group_id)
        .set("enable.auto.commit", "false")
        .set("isolation.level", "read_committed")  // 只读已提交的消息
        .create()
}
```

---

## 9. 错误处理与重试

### 9.1 生产者错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum KafkaProducerError {
    #[error("Kafka error: {0}")]
    Kafka(#[from] rdkafka::error::KafkaError),
    
    #[error("Timeout sending message")]
    Timeout,
    
    #[error("Serialization error: {0}")]
    Serialization(String),
}

pub async fn send_with_retry(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
    max_retries: usize,
) -> Result<(), KafkaProducerError> {
    let mut attempts = 0;
    
    loop {
        let record = FutureRecord::to(topic)
            .key(key)
            .payload(payload);
        
        match producer.send(record, Timeout::After(Duration::from_secs(10))).await {
            Ok((partition, offset)) => {
                info!("Message delivered to partition {} at offset {}", partition, offset);
                return Ok(());
            }
            Err((e, _)) => {
                attempts += 1;
                
                if attempts >= max_retries {
                    error!("Failed to send message after {} attempts", max_retries);
                    return Err(KafkaProducerError::Kafka(e));
                }
                
                error!("Attempt {} failed: {:?}, retrying...", attempts, e);
                
                tokio::time::sleep(Duration::from_millis(100 * 2_u64.pow(attempts as u32))).await;
            }
        }
    }
}
```

### 9.2 消费者错误处理

```rust
pub async fn consume_with_error_handling(
    consumer: &StreamConsumer,
    topics: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                let result = tokio::time::timeout(
                    Duration::from_secs(30),
                    process_message_safe(&m),
                ).await;
                
                match result {
                    Ok(Ok(_)) => {
                        // 成功处理
                        consumer.commit_message(&m, CommitMode::Async)?;
                    }
                    Ok(Err(e)) => {
                        // 处理失败
                        error!("Failed to process message: {:?}", e);
                        
                        // 发送到死信队列
                        send_to_dlq(&m).await?;
                        
                        // 仍然提交偏移量（避免重复消费）
                        consumer.commit_message(&m, CommitMode::Async)?;
                    }
                    Err(_) => {
                        // 超时
                        error!("Message processing timed out");
                        
                        send_to_dlq(&m).await?;
                        consumer.commit_message(&m, CommitMode::Async)?;
                    }
                }
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn process_message_safe(message: &impl Message) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    Ok(())
}
```

---

## 10. 性能优化

### 10.1 生产者优化

```rust
pub fn create_high_throughput_producer(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        
        // 批量配置
        .set("batch.size", "1000000")              // 1MB
        .set("linger.ms", "100")                   // 等待 100ms 积累消息
        .set("batch.num.messages", "10000")        // 批量消息数
        
        // 缓冲区配置
        .set("queue.buffering.max.messages", "1000000")
        .set("queue.buffering.max.kbytes", "1048576")  // 1GB
        
        // 压缩
        .set("compression.type", "lz4")            // 或 zstd, snappy
        .set("compression.level", "3")
        
        // 网络配置
        .set("socket.send.buffer.bytes", "1048576")  // 1MB
        .set("socket.receive.buffer.bytes", "1048576")
        
        .create()
}
```

### 10.2 消费者优化

```rust
pub fn create_high_throughput_consumer(brokers: &str, group_id: &str) -> Result<StreamConsumer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("group.id", group_id)
        
        // 批量拉取
        .set("fetch.min.bytes", "1048576")         // 1MB
        .set("fetch.wait.max.ms", "500")
        .set("max.partition.fetch.bytes", "10485760")  // 10MB
        
        // 网络配置
        .set("socket.receive.buffer.bytes", "1048576")
        
        // 会话配置
        .set("session.timeout.ms", "30000")
        .set("heartbeat.interval.ms", "3000")
        
        .create()
}
```

---

## 11. 监控与指标

### 11.1 生产者统计

```rust
use rdkafka::statistics::Statistics;

pub fn create_producer_with_stats(brokers: &str) -> Result<FutureProducer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", brokers)
        .set("statistics.interval.ms", "5000")  // 每 5 秒报告统计
        .create()
}

// 在回调中处理统计信息
// producer.set_statistics_callback(|stats| {
//     // 处理统计信息
// });
```

### 11.2 自定义指标

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

pub struct KafkaMetrics {
    pub messages_sent: Arc<AtomicU64>,
    pub messages_failed: Arc<AtomicU64>,
    pub bytes_sent: Arc<AtomicU64>,
}

impl KafkaMetrics {
    pub fn new() -> Self {
        Self {
            messages_sent: Arc::new(AtomicU64::new(0)),
            messages_failed: Arc::new(AtomicU64::new(0)),
            bytes_sent: Arc::new(AtomicU64::new(0)),
        }
    }
    
    pub fn record_sent(&self, bytes: u64) {
        self.messages_sent.fetch_add(1, Ordering::Relaxed);
        self.bytes_sent.fetch_add(bytes, Ordering::Relaxed);
    }
    
    pub fn record_failed(&self) {
        self.messages_failed.fetch_add(1, Ordering::Relaxed);
    }
}
```

---

## 12. OTLP 分布式追踪集成

### 12.1 OTLP 初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "rdkafka-advanced-demo"),
                    KeyValue::new("messaging.system", "kafka"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::fmt::layer().json())
        .init();
    
    Ok(())
}
```

### 12.2 追踪生产者

```rust
use tracing::{instrument, info, Span};

#[instrument(skip(producer), fields(
    messaging.system = "kafka",
    messaging.destination = topic,
    messaging.operation = "send"
))]
pub async fn traced_send(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let record = FutureRecord::to(topic)
        .key(key)
        .payload(payload);
    
    match producer.send(record, Timeout::After(Duration::from_secs(10))).await {
        Ok((partition, offset)) => {
            Span::current().record("messaging.kafka.partition", partition);
            Span::current().record("messaging.kafka.offset", offset as i64);
            
            info!("Message sent successfully");
            Ok(())
        }
        Err((e, _)) => {
            Err(Box::new(e))
        }
    }
}
```

### 12.3 追踪消费者

```rust
#[instrument(skip(consumer), fields(
    messaging.system = "kafka",
    messaging.operation = "receive"
))]
pub async fn traced_consume(
    consumer: &StreamConsumer,
    topics: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                let span = tracing::info_span!(
                    "process_message",
                    messaging.destination = m.topic(),
                    messaging.kafka.partition = m.partition(),
                    messaging.kafka.offset = m.offset(),
                );
                
                let _enter = span.enter();
                
                info!("Processing message");
                
                // 处理消息
                if let Some(payload) = m.payload() {
                    process_message(String::from_utf8_lossy(payload).to_string()).await?;
                }
                
                consumer.commit_message(&m, CommitMode::Async)?;
            }
            Err(e) => {
                error!("Kafka error: {:?}", e);
            }
        }
    }
    
    Ok(())
}
```

---

## 13. 死信队列

### 13.1 实现死信队列

```rust
pub async fn send_to_dead_letter_queue(
    producer: &FutureProducer,
    original_topic: &str,
    message: &impl Message,
    error: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let dlq_topic = format!("{}.dlq", original_topic);
    
    let mut headers = rdkafka::message::OwnedHeaders::new();
    headers = headers
        .insert(rdkafka::message::Header {
            key: "original_topic",
            value: Some(original_topic),
        })
        .insert(rdkafka::message::Header {
            key: "error",
            value: Some(error),
        })
        .insert(rdkafka::message::Header {
            key: "timestamp",
            value: Some(&chrono::Utc::now().to_rfc3339()),
        });
    
    let record = FutureRecord::to(&dlq_topic)
        .key(message.key().unwrap_or(b""))
        .payload(message.payload().unwrap_or(b""))
        .headers(headers);
    
    producer.send(record, Timeout::After(Duration::from_secs(10))).await
        .map_err(|(e, _)| Box::new(e) as Box<dyn std::error::Error>)?;
    
    info!("Message sent to DLQ: {}", dlq_topic);
    
    Ok(())
}
```

---

## 14. 测试策略

### 14.1 集成测试（使用 Testcontainers）

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use testcontainers::{clients, images::kafka::Kafka};

    #[tokio::test]
    async fn test_produce_consume() {
        let docker = clients::Cli::default();
        let kafka_container = docker.run(Kafka::default());
        
        let bootstrap_servers = format!(
            "localhost:{}",
            kafka_container.get_host_port_ipv4(9093)
        );
        
        // 创建生产者
        let producer = create_producer(&bootstrap_servers).unwrap();
        
        // 发送消息
        send_message(&producer, "test-topic", "key1", "value1").await.unwrap();
        
        // 创建消费者
        let consumer = create_consumer(&bootstrap_servers, "test-group").unwrap();
        consumer.subscribe(&["test-topic"]).unwrap();
        
        // 消费消息
        // ...
    }
}
```

---

## 15. 生产环境部署

### 15.1 Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  zookeeper:
    image: confluentinc/cp-zookeeper:7.6.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181
    ports:
      - "2181:2181"

  kafka:
    image: confluentinc/cp-kafka:7.6.0
    depends_on:
      - zookeeper
    ports:
      - "9092:9092"
      - "9093:9093"
    environment:
      KAFKA_BROKER_ID: 1
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://kafka:9092,PLAINTEXT_HOST://localhost:9093
      KAFKA_LISTENER_SECURITY_PROTOCOL_MAP: PLAINTEXT:PLAINTEXT,PLAINTEXT_HOST:PLAINTEXT
      KAFKA_INTER_BROKER_LISTENER_NAME: PLAINTEXT
      KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR: 1

  jaeger:
    image: jaegertracing/all-in-one:1.57
    ports:
      - "16686:16686"
      - "4317:4317"
```

---

## 16. 国际标准对标

### 16.1 对标清单

| 标准 | Rdkafka 实现 |
|------|-------------|
| **Kafka Protocol** | ✅ 完整支持 |
| **Exactly-Once Semantics** | ✅ 完整支持 |
| **Transactions** | ✅ 完整支持 |
| **SASL/SCRAM** | ✅ 完整支持 |
| **SSL/TLS** | ✅ 完整支持 |
| **Apache Avro** | ⚠️ 需额外库 |

---

## 17. 总结与最佳实践

### 17.1 最佳实践

#### ✅ 推荐做法

- 使用幂等性生产者
- 手动提交偏移量
- 实现死信队列
- 使用 OTLP 追踪
- 批量发送/消费
- 设置合理的超时
- 监控关键指标

#### ❌ 避免做法

- 不要忽略错误处理
- 不要使用自动提交偏移量
- 不要在循环中创建生产者/消费者
- 不要忽略序列化错误

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**Rdkafka 版本**: 0.36  

**国际标准对齐**:

- ✅ Apache Kafka Protocol
- ✅ Exactly-Once Semantics (EOS)
- ✅ OpenTelemetry Messaging Semantic Conventions
