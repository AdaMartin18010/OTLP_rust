# Lapin (RabbitMQ) 完整实现 - 企业级消息队列 - Rust 1.90 + OTLP 集成

## 目录

- [Lapin (RabbitMQ) 完整实现 - 企业级消息队列 - Rust 1.90 + OTLP 集成](#lapin-rabbitmq-完整实现---企业级消息队列---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. RabbitMQ 与 Lapin 概述](#1-rabbitmq-与-lapin-概述)
    - [1.1 什么是 RabbitMQ？](#11-什么是-rabbitmq)
    - [1.2 什么是 Lapin？](#12-什么是-lapin)
  - [2. 核心架构](#2-核心架构)
    - [2.1 AMQP 0.9.1 模型](#21-amqp-091-模型)
    - [2.2 Exchange 类型](#22-exchange-类型)
  - [3. 项目设置](#3-项目设置)
    - [3.1 依赖配置](#31-依赖配置)
    - [3.2 项目结构](#32-项目结构)
  - [4. 连接管理](#4-连接管理)
    - [4.1 基础连接](#41-基础连接)
    - [4.2 连接池](#42-连接池)
  - [5. 生产者实现](#5-生产者实现)
    - [5.1 基础生产者](#51-基础生产者)
    - [5.2 批量发布](#52-批量发布)
  - [6. 消费者实现](#6-消费者实现)
    - [6.1 基础消费者](#61-基础消费者)
    - [6.2 工作队列模式](#62-工作队列模式)
  - [7. 交换机与路由](#7-交换机与路由)
    - [7.1 声明 Exchange](#71-声明-exchange)
    - [7.2 Topic 模式示例](#72-topic-模式示例)
  - [8. 高级特性](#8-高级特性)
    - [8.1 延迟队列（Dead Letter Exchange）](#81-延迟队列dead-letter-exchange)
    - [8.2 优先级队列](#82-优先级队列)
  - [9. 可靠性保证](#9-可靠性保证)
    - [9.1 发布者确认（Publisher Confirms）](#91-发布者确认publisher-confirms)
    - [9.2 事务](#92-事务)
  - [10. OTLP 集成](#10-otlp-集成)
    - [10.1 追踪配置](#101-追踪配置)
    - [10.2 带追踪的生产者](#102-带追踪的生产者)
    - [10.3 带追踪的消费者](#103-带追踪的消费者)
  - [11. 生产环境最佳实践](#11-生产环境最佳实践)
    - [11.1 Docker Compose 部署](#111-docker-compose-部署)
    - [11.2 配置文件](#112-配置文件)
  - [12. 国际标准对齐](#12-国际标准对齐)
    - [12.1 AMQP 0.9.1 完整对齐](#121-amqp-091-完整对齐)
    - [12.2 OpenTelemetry Semantic Conventions](#122-opentelemetry-semantic-conventions)
  - [13. 总结](#13-总结)
    - [13.1 RabbitMQ 核心优势](#131-rabbitmq-核心优势)
    - [13.2 何时选择 RabbitMQ](#132-何时选择-rabbitmq)
    - [13.3 生产部署清单](#133-生产部署清单)

---

## 1. RabbitMQ 与 Lapin 概述

### 1.1 什么是 RabbitMQ？

**RabbitMQ** 是最流行的开源消息队列中间件，基于 AMQP 0.9.1 协议，广泛用于企业级分布式系统。

```text
┌────────────────────────────────────────────────────────────┐
│                   RabbitMQ 核心特点                         │
├────────────────────────────────────────────────────────────┤
│  ✅ AMQP 0.9.1 国际标准协议                                │
│  ✅ 多种消息模式（Direct, Topic, Fanout, Headers）        │
│  ✅ 可靠性保证（持久化、确认机制、事务）                     │
│  ✅ 集群和高可用（镜像队列、仲裁队列）                       │
│  ✅ 管理界面（Web UI、REST API、CLI）                      │
│  ✅ 插件生态（延迟队列、死信队列、优先级队列）               │
│  ✅ 成熟稳定（2007年至今，企业验证）                        │
└────────────────────────────────────────────────────────────┘
```

### 1.2 什么是 Lapin？

**Lapin** 是 RabbitMQ 的高性能 Rust 异步客户端，基于 Tokio 构建。

| 特性 | Lapin | amqprs | amq-protocol |
|------|-------|--------|--------------|
| **异步** | ✅ Tokio | ✅ Tokio | ❌ 同步 |
| **AMQP 0.9.1** | ✅ 完整 | ✅ 完整 | ✅ 完整 |
| **连接池** | ✅ | ⚠️ 部分 | ❌ |
| **错误处理** | ✅ 类型安全 | ✅ | ⚠️ |
| **文档** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **社区活跃度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |

**适用场景**:

- ✅ 微服务解耦
- ✅ 异步任务处理
- ✅ 事件驱动架构
- ✅ 流量削峰填谷
- ✅ 日志收集
- ✅ 订单处理

---

## 2. 核心架构

### 2.1 AMQP 0.9.1 模型

```text
┌──────────────────────────────────────────────────────────┐
│                   AMQP 架构模型                           │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  Producer                                     Consumer   │
│     │                                            ▲        │
│     │ 1. Publish                                 │        │
│     ▼                                            │ 6.    │
│  ┌─────────┐   2. Route    ┌────────┐   5.     │        │
│  │ Exchange│─────────────▶│ Queue  │──────────┘        │
│  └─────────┘               └────────┘                    │
│      │                                                    │
│      │ 3. Binding                                        │
│      └───────────────┐                                   │
│                      │                                   │
│                      ▼                                   │
│                  Routing Key                             │
│                                                           │
└──────────────────────────────────────────────────────────┘
```

**核心概念**:

1. **Producer（生产者）**: 发送消息到 Exchange
2. **Exchange（交换机）**: 根据路由规则转发消息
3. **Binding（绑定）**: Exchange 到 Queue 的路由规则
4. **Queue（队列）**: 存储消息，等待消费
5. **Consumer（消费者）**: 从 Queue 接收消息
6. **Routing Key**: 消息的路由键
7. **Binding Key**: 绑定的路由键

### 2.2 Exchange 类型

| 类型 | 路由规则 | 适用场景 |
|------|---------|---------|
| **Direct** | 完全匹配 Routing Key | 点对点消息 |
| **Topic** | 模式匹配（*, #） | 发布/订阅，灵活路由 |
| **Fanout** | 广播到所有绑定的队列 | 事件广播 |
| **Headers** | 根据消息头匹配 | 复杂路由规则 |

---

## 3. 项目设置

### 3.1 依赖配置

```toml
[package]
name = "lapin-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# RabbitMQ 客户端
lapin = "2.3"                  # AMQP 0.9.1 客户端
deadpool-lapin = "0.12"        # 连接池

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

# 配置管理
config = "0.14"

[dev-dependencies]
testcontainers = "0.21"        # Docker 集成测试
```

### 3.2 项目结构

```text
lapin-otlp-example/
├── src/
│   ├── lib.rs                    # 库入口
│   ├── connection.rs             # 连接管理
│   ├── producer.rs               # 生产者
│   ├── consumer.rs               # 消费者
│   ├── exchange.rs               # Exchange 声明
│   ├── queue.rs                  # Queue 管理
│   ├── error.rs                  # 错误类型
│   ├── types.rs                  # 消息类型
│   ├── retry.rs                  # 重试策略
│   └── telemetry.rs              # OTLP 追踪
├── examples/
│   ├── direct_exchange.rs        # Direct 模式
│   ├── topic_exchange.rs         # Topic 模式
│   ├── fanout_exchange.rs        # Fanout 模式
│   ├── work_queue.rs             # 工作队列
│   └── rpc.rs                    # RPC 模式
└── docker/
    └── docker-compose.yml        # RabbitMQ 部署
```

---

## 4. 连接管理

### 4.1 基础连接

```rust
// src/connection.rs
use lapin::{
    Connection, ConnectionProperties, Channel,
    options::{QueueDeclareOptions, BasicPublishOptions, BasicConsumeOptions},
    types::FieldTable,
    BasicProperties,
};
use std::sync::Arc;
use tokio::sync::RwLock;
use crate::error::RabbitMQError;

/// RabbitMQ 连接配置
#[derive(Debug, Clone)]
pub struct RabbitMQConfig {
    pub url: String,
    pub heartbeat: u16,           // 心跳间隔（秒）
    pub connection_timeout: u64,  // 连接超时（秒）
    pub max_channels: u16,        // 最大通道数
}

impl Default for RabbitMQConfig {
    fn default() -> Self {
        Self {
            url: "amqp://guest:guest@localhost:5672/%2f".to_string(),
            heartbeat: 60,
            connection_timeout: 10,
            max_channels: 1000,
        }
    }
}

/// RabbitMQ 连接管理器
pub struct RabbitMQConnection {
    connection: Connection,
    channel: Arc<RwLock<Option<Channel>>>,
}

impl RabbitMQConnection {
    /// 创建新连接
    pub async fn new(config: RabbitMQConfig) -> Result<Self, RabbitMQError> {
        let connection = Connection::connect(
            &config.url,
            ConnectionProperties::default()
                .with_executor(tokio_executor_trait::Tokio::current())
                .with_reactor(tokio_reactor_trait::Tokio)
        )
        .await?;

        tracing::info!(
            status = "connected",
            heartbeat = config.heartbeat,
            "RabbitMQ connection established"
        );

        Ok(Self {
            connection,
            channel: Arc::new(RwLock::new(None)),
        })
    }

    /// 获取或创建 Channel
    pub async fn get_channel(&self) -> Result<Channel, RabbitMQError> {
        let mut channel_guard = self.channel.write().await;

        if let Some(ref channel) = *channel_guard {
            if channel.status().connected() {
                return Ok(channel.clone());
            }
        }

        // 创建新 Channel
        let new_channel = self.connection.create_channel().await?;
        
        // 设置 QoS（预取数量）
        new_channel
            .basic_qos(10, Default::default())
            .await?;

        *channel_guard = Some(new_channel.clone());

        tracing::info!("New channel created");

        Ok(new_channel)
    }

    /// 关闭连接
    pub async fn close(self) -> Result<(), RabbitMQError> {
        self.connection.close(200, "Normal shutdown").await?;
        tracing::info!("RabbitMQ connection closed");
        Ok(())
    }
}
```

### 4.2 连接池

```rust
use deadpool_lapin::{Config, Manager, Pool, Runtime};

/// 创建连接池
pub fn create_connection_pool(config: &RabbitMQConfig) -> Result<Pool, RabbitMQError> {
    let mut cfg = Config::default();
    cfg.url = Some(config.url.clone());
    
    let pool = cfg.create_pool(Some(Runtime::Tokio1))?;

    tracing::info!(max_size = 10, "RabbitMQ connection pool created");

    Ok(pool)
}

/// 从池获取连接
pub async fn get_connection_from_pool(pool: &Pool) -> Result<Connection, RabbitMQError> {
    let connection = pool.get().await?;
    Ok(connection.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore] // 需要 RabbitMQ 服务
    async fn test_connection() {
        let config = RabbitMQConfig::default();
        let conn = RabbitMQConnection::new(config).await.unwrap();
        let channel = conn.get_channel().await.unwrap();
        assert!(channel.status().connected());
    }
}
```

---

## 5. 生产者实现

### 5.1 基础生产者

```rust
// src/producer.rs
use lapin::{
    Channel, BasicProperties,
    options::BasicPublishOptions,
};
use serde::Serialize;
use tracing::instrument;
use crate::error::RabbitMQError;

pub struct Producer {
    channel: Channel,
}

impl Producer {
    pub fn new(channel: Channel) -> Self {
        Self { channel }
    }

    /// 发布消息到指定 Exchange
    #[instrument(skip(self, message))]
    pub async fn publish<T>(
        &self,
        exchange: &str,
        routing_key: &str,
        message: &T,
    ) -> Result<(), RabbitMQError>
    where
        T: Serialize,
    {
        // 序列化消息
        let payload = serde_json::to_vec(message)?;

        // 发布消息
        self.channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                &payload,
                BasicProperties::default()
                    .with_content_type("application/json".into())
                    .with_delivery_mode(2)  // 2 = persistent
            )
            .await?
            .await?;  // 等待确认

        tracing::info!(
            exchange = %exchange,
            routing_key = %routing_key,
            payload_size = payload.len(),
            "Message published"
        );

        Ok(())
    }

    /// 发布消息到默认 Exchange（Direct to Queue）
    pub async fn publish_to_queue<T>(
        &self,
        queue_name: &str,
        message: &T,
    ) -> Result<(), RabbitMQError>
    where
        T: Serialize,
    {
        self.publish("", queue_name, message).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize)]
    struct TestMessage {
        id: u32,
        content: String,
    }

    #[tokio::test]
    #[ignore]
    async fn test_publish() {
        let conn = crate::connection::RabbitMQConnection::new(
            crate::connection::RabbitMQConfig::default()
        ).await.unwrap();
        
        let channel = conn.get_channel().await.unwrap();
        let producer = Producer::new(channel);

        let msg = TestMessage {
            id: 1,
            content: "Hello RabbitMQ".to_string(),
        };

        producer.publish_to_queue("test_queue", &msg).await.unwrap();
    }
}
```

### 5.2 批量发布

```rust
use futures::future::join_all;

impl Producer {
    /// 批量发布消息（并发）
    pub async fn publish_batch<T>(
        &self,
        exchange: &str,
        messages: Vec<(String, T)>,  // (routing_key, message)
    ) -> Result<Vec<Result<(), RabbitMQError>>, RabbitMQError>
    where
        T: Serialize,
    {
        let futures = messages
            .into_iter()
            .map(|(routing_key, message)| {
                let exchange = exchange.to_string();
                let producer = self.clone();
                async move {
                    producer.publish(&exchange, &routing_key, &message).await
                }
            });

        let results = join_all(futures).await;

        Ok(results)
    }
}
```

---

## 6. 消费者实现

### 6.1 基础消费者

```rust
// src/consumer.rs
use lapin::{
    Channel, message::Delivery,
    options::{BasicAckOptions, BasicNackOptions, BasicConsumeOptions},
    types::FieldTable,
};
use serde::de::DeserializeOwned;
use futures::StreamExt;
use tracing::instrument;
use crate::error::RabbitMQError;

pub struct Consumer {
    channel: Channel,
}

impl Consumer {
    pub fn new(channel: Channel) -> Self {
        Self { channel }
    }

    /// 消费消息（自动 ACK）
    #[instrument(skip(self, handler))]
    pub async fn consume<T, F, Fut>(
        &self,
        queue_name: &str,
        handler: F,
    ) -> Result<(), RabbitMQError>
    where
        T: DeserializeOwned,
        F: Fn(T) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        let mut consumer = self.channel
            .basic_consume(
                queue_name,
                &format!("consumer_{}", uuid::Uuid::new_v4()),
                BasicConsumeOptions::default(),
                FieldTable::default(),
            )
            .await?;

        tracing::info!(queue = %queue_name, "Consumer started");

        while let Some(delivery_result) = consumer.next().await {
            match delivery_result {
                Ok(delivery) => {
                    if let Err(e) = self.process_delivery(delivery, &handler).await {
                        tracing::error!(error = %e, "Failed to process delivery");
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "Consumer error");
                    break;
                }
            }
        }

        Ok(())
    }

    /// 处理单个消息
    async fn process_delivery<T, F, Fut>(
        &self,
        delivery: Delivery,
        handler: &F,
    ) -> Result<(), RabbitMQError>
    where
        T: DeserializeOwned,
        F: Fn(T) -> Fut,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>>,
    {
        // 反序列化消息
        let message: T = serde_json::from_slice(&delivery.data)?;

        // 调用处理器
        match handler(message).await {
            Ok(_) => {
                // 确认消息
                delivery.ack(BasicAckOptions::default()).await?;
                tracing::info!(
                    delivery_tag = delivery.delivery_tag,
                    "Message acknowledged"
                );
            }
            Err(e) => {
                // 拒绝消息（重新入队）
                delivery.nack(BasicNackOptions {
                    requeue: true,
                    ..Default::default()
                }).await?;
                tracing::error!(
                    delivery_tag = delivery.delivery_tag,
                    error = %e,
                    "Message rejected and requeued"
                );
            }
        }

        Ok(())
    }
}
```

### 6.2 工作队列模式

```rust
/// 并发消费者（多 Worker）
pub async fn start_workers<T, F, Fut>(
    channel: Channel,
    queue_name: &str,
    worker_count: usize,
    handler: F,
) -> Result<(), RabbitMQError>
where
    T: DeserializeOwned + Send + 'static,
    F: Fn(T) -> Fut + Send + Sync + Clone + 'static,
    Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
{
    let mut handles = vec![];

    for worker_id in 0..worker_count {
        let channel = channel.clone();
        let queue = queue_name.to_string();
        let handler = handler.clone();

        let handle = tokio::spawn(async move {
            let consumer = Consumer::new(channel);
            tracing::info!(worker_id = worker_id, queue = %queue, "Worker started");
            consumer.consume(&queue, handler).await
        });

        handles.push(handle);
    }

    // 等待所有 Worker
    for handle in handles {
        handle.await??;
    }

    Ok(())
}
```

---

## 7. 交换机与路由

### 7.1 声明 Exchange

```rust
// src/exchange.rs
use lapin::{
    Channel, ExchangeKind,
    options::ExchangeDeclareOptions,
    types::FieldTable,
};
use crate::error::RabbitMQError;

pub struct ExchangeManager {
    channel: Channel,
}

impl ExchangeManager {
    pub fn new(channel: Channel) -> Self {
        Self { channel }
    }

    /// 声明 Direct Exchange
    pub async fn declare_direct(&self, name: &str) -> Result<(), RabbitMQError> {
        self.declare(name, ExchangeKind::Direct).await
    }

    /// 声明 Topic Exchange
    pub async fn declare_topic(&self, name: &str) -> Result<(), RabbitMQError> {
        self.declare(name, ExchangeKind::Topic).await
    }

    /// 声明 Fanout Exchange
    pub async fn declare_fanout(&self, name: &str) -> Result<(), RabbitMQError> {
        self.declare(name, ExchangeKind::Fanout).await
    }

    /// 通用声明方法
    async fn declare(&self, name: &str, kind: ExchangeKind) -> Result<(), RabbitMQError> {
        self.channel
            .exchange_declare(
                name,
                kind,
                ExchangeDeclareOptions {
                    durable: true,      // 持久化
                    auto_delete: false,
                    ..Default::default()
                },
                FieldTable::default(),
            )
            .await?;

        tracing::info!(exchange = %name, kind = ?kind, "Exchange declared");

        Ok(())
    }
}
```

### 7.2 Topic 模式示例

```rust
use crate::types::LogMessage;

/// 日志系统示例（Topic Exchange）
pub async fn setup_logging_system(channel: Channel) -> Result<(), RabbitMQError> {
    let exchange_mgr = ExchangeManager::new(channel.clone());
    
    // 1. 声明 Topic Exchange
    exchange_mgr.declare_topic("logs").await?;

    // 2. 声明队列
    let queue_mgr = QueueManager::new(channel.clone());
    let error_queue = queue_mgr.declare("error_logs", true).await?;
    let warning_queue = queue_mgr.declare("warning_logs", true).await?;
    let all_logs_queue = queue_mgr.declare("all_logs", true).await?;

    // 3. 绑定队列
    // *.error → error_logs
    queue_mgr.bind(&error_queue, "logs", "*.error").await?;
    
    // *.warning → warning_logs
    queue_mgr.bind(&warning_queue, "logs", "*.warning").await?;
    
    // *.* → all_logs（接收所有）
    queue_mgr.bind(&all_logs_queue, "logs", "*.*").await?;

    tracing::info!("Logging system setup complete");

    Ok(())
}

// 发送日志
pub async fn send_log(
    producer: &Producer,
    level: &str,
    service: &str,
    message: &str,
) -> Result<(), RabbitMQError> {
    let log = LogMessage {
        level: level.to_string(),
        service: service.to_string(),
        message: message.to_string(),
        timestamp: chrono::Utc::now(),
    };

    // Routing Key: {service}.{level}
    let routing_key = format!("{}.{}", service, level);
    
    producer.publish("logs", &routing_key, &log).await
}
```

---

## 8. 高级特性

### 8.1 延迟队列（Dead Letter Exchange）

```rust
use lapin::types::AMQPValue;
use std::collections::HashMap;

/// 创建延迟队列
pub async fn create_delayed_queue(
    channel: &Channel,
    queue_name: &str,
    delay_ms: u32,
) -> Result<(), RabbitMQError> {
    // 1. 声明 DLX (Dead Letter Exchange)
    channel.exchange_declare(
        &format!("{}_dlx", queue_name),
        ExchangeKind::Direct,
        ExchangeDeclareOptions {
            durable: true,
            ..Default::default()
        },
        FieldTable::default(),
    ).await?;

    // 2. 声明延迟队列（消息会过期并转发到 DLX）
    let mut args = FieldTable::default();
    args.insert(
        "x-message-ttl".into(),
        AMQPValue::LongInt(delay_ms as i32),
    );
    args.insert(
        "x-dead-letter-exchange".into(),
        AMQPValue::LongString(format!("{}_dlx", queue_name).into()),
    );

    channel.queue_declare(
        &format!("{}_delay", queue_name),
        QueueDeclareOptions {
            durable: true,
            ..Default::default()
        },
        args,
    ).await?;

    // 3. 声明目标队列
    channel.queue_declare(
        queue_name,
        QueueDeclareOptions {
            durable: true,
            ..Default::default()
        },
        FieldTable::default(),
    ).await?;

    // 4. 绑定 DLX 到目标队列
    channel.queue_bind(
        queue_name,
        &format!("{}_dlx", queue_name),
        "",
        Default::default(),
        FieldTable::default(),
    ).await?;

    tracing::info!(
        queue = %queue_name,
        delay_ms = delay_ms,
        "Delayed queue created"
    );

    Ok(())
}

/// 发送延迟消息
pub async fn publish_delayed<T>(
    producer: &Producer,
    queue_name: &str,
    message: &T,
    delay_ms: u32,
) -> Result<(), RabbitMQError>
where
    T: Serialize,
{
    // 发送到延迟队列（会自动转发到目标队列）
    producer.publish_to_queue(&format!("{}_delay", queue_name), message).await
}
```

### 8.2 优先级队列

```rust
/// 创建优先级队列
pub async fn create_priority_queue(
    channel: &Channel,
    queue_name: &str,
    max_priority: u8,
) -> Result<(), RabbitMQError> {
    let mut args = FieldTable::default();
    args.insert(
        "x-max-priority".into(),
        AMQPValue::ShortShortUInt(max_priority),
    );

    channel.queue_declare(
        queue_name,
        QueueDeclareOptions {
            durable: true,
            ..Default::default()
        },
        args,
    ).await?;

    Ok(())
}

/// 发送带优先级的消息
pub async fn publish_with_priority<T>(
    channel: &Channel,
    queue_name: &str,
    message: &T,
    priority: u8,
) -> Result<(), RabbitMQError>
where
    T: Serialize,
{
    let payload = serde_json::to_vec(message)?;

    channel
        .basic_publish(
            "",
            queue_name,
            BasicPublishOptions::default(),
            &payload,
            BasicProperties::default()
                .with_priority(priority)  // 设置优先级
                .with_delivery_mode(2)
        )
        .await?
        .await?;

    Ok(())
}
```

---

## 9. 可靠性保证

### 9.1 发布者确认（Publisher Confirms）

```rust
use lapin::options::ConfirmSelectOptions;

/// 启用发布者确认
pub async fn enable_publisher_confirms(channel: &Channel) -> Result<(), RabbitMQError> {
    channel.confirm_select(ConfirmSelectOptions::default()).await?;
    tracing::info!("Publisher confirms enabled");
    Ok(())
}

/// 可靠发布（等待确认）
pub async fn reliable_publish<T>(
    channel: &Channel,
    exchange: &str,
    routing_key: &str,
    message: &T,
) -> Result<(), RabbitMQError>
where
    T: Serialize,
{
    let payload = serde_json::to_vec(message)?;

    // 发布并等待确认
    let confirm = channel
        .basic_publish(
            exchange,
            routing_key,
            BasicPublishOptions::default(),
            &payload,
            BasicProperties::default().with_delivery_mode(2),
        )
        .await?;

    // 等待 Broker 确认
    confirm.await?;

    tracing::info!(
        exchange = %exchange,
        routing_key = %routing_key,
        "Message confirmed by broker"
    );

    Ok(())
}
```

### 9.2 事务

```rust
use lapin::options::{TxSelectOptions, TxCommitOptions, TxRollbackOptions};

/// 事务发布
pub async fn transactional_publish<T>(
    channel: &Channel,
    messages: Vec<(&str, &str, T)>,  // (exchange, routing_key, message)
) -> Result<(), RabbitMQError>
where
    T: Serialize,
{
    // 1. 开启事务
    channel.tx_select(TxSelectOptions::default()).await?;

    // 2. 发布消息
    for (exchange, routing_key, message) in messages {
        let payload = serde_json::to_vec(&message)?;
        
        channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                &payload,
                BasicProperties::default().with_delivery_mode(2),
            )
            .await?
            .await?;
    }

    // 3. 提交事务
    channel.tx_commit(TxCommitOptions::default()).await?;

    tracing::info!("Transaction committed");

    Ok(())
}

/// 回滚事务
pub async fn rollback_transaction(channel: &Channel) -> Result<(), RabbitMQError> {
    channel.tx_rollback(TxRollbackOptions::default()).await?;
    tracing::warn!("Transaction rolled back");
    Ok(())
}
```

---

## 10. OTLP 集成

### 10.1 追踪配置

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
                KeyValue::new("service.name", "rabbitmq-service"),
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

### 10.2 带追踪的生产者

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};

/// 带 OTLP 追踪的发布
#[instrument(skip(channel, message))]
pub async fn traced_publish<T>(
    channel: &Channel,
    exchange: &str,
    routing_key: &str,
    message: &T,
) -> Result<(), RabbitMQError>
where
    T: Serialize,
{
    let tracer = global::tracer("rabbitmq-producer");
    
    let mut span = tracer
        .span_builder(format!("RabbitMQ Publish {}", routing_key))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("messaging.destination", exchange.to_string()),
            KeyValue::new("messaging.destination_kind", "exchange"),
            KeyValue::new("messaging.rabbitmq.routing_key", routing_key.to_string()),
            KeyValue::new("messaging.protocol", "AMQP"),
            KeyValue::new("messaging.protocol_version", "0.9.1"),
        ])
        .start(&tracer);
    
    let payload = serde_json::to_vec(message)?;
    
    span.set_attribute(KeyValue::new("messaging.message_payload_size_bytes", payload.len() as i64));
    
    let start = std::time::Instant::now();
    
    let result = channel
        .basic_publish(
            exchange,
            routing_key,
            BasicPublishOptions::default(),
            &payload,
            BasicProperties::default().with_delivery_mode(2),
        )
        .await?
        .await;
    
    let duration = start.elapsed();
    
    match result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("messaging.operation", "publish"));
            span.set_attribute(KeyValue::new("duration_ms", duration.as_millis() as i64));
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

### 10.3 带追踪的消费者

```rust
/// 带追踪的消息处理
async fn traced_process_delivery<T, F, Fut>(
    delivery: Delivery,
    handler: &F,
) -> Result<(), RabbitMQError>
where
    T: DeserializeOwned,
    F: Fn(T) -> Fut,
    Fut: std::future::Future<Output = Result<(), anyhow::Error>>,
{
    let tracer = global::tracer("rabbitmq-consumer");
    
    let mut span = tracer
        .span_builder(format!("RabbitMQ Consume {}", delivery.routing_key))
        .with_kind(SpanKind::Consumer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "rabbitmq"),
            KeyValue::new("messaging.operation", "receive"),
            KeyValue::new("messaging.rabbitmq.routing_key", delivery.routing_key.to_string()),
            KeyValue::new("messaging.message_payload_size_bytes", delivery.data.len() as i64),
        ])
        .start(&tracer);
    
    let message: T = serde_json::from_slice(&delivery.data)?;
    
    match handler(message).await {
        Ok(_) => {
            delivery.ack(BasicAckOptions::default()).await?;
            span.set_attribute(KeyValue::new("messaging.rabbitmq.ack", "ack"));
        }
        Err(e) => {
            delivery.nack(BasicNackOptions { requeue: true, ..Default::default() }).await?;
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("messaging.rabbitmq.ack", "nack"));
        }
    }
    
    span.end();
    
    Ok(())
}
```

---

## 11. 生产环境最佳实践

### 11.1 Docker Compose 部署

```yaml
# docker/docker-compose.yml
version: '3.8'

services:
  rabbitmq:
    image: rabbitmq:3.13-management-alpine
    container_name: rabbitmq
    hostname: rabbitmq
    ports:
      - "5672:5672"      # AMQP 端口
      - "15672:15672"    # 管理界面
    environment:
      RABBITMQ_DEFAULT_USER: admin
      RABBITMQ_DEFAULT_PASS: admin123
      RABBITMQ_DEFAULT_VHOST: /
    volumes:
      - rabbitmq_data:/var/lib/rabbitmq
      - ./rabbitmq.conf:/etc/rabbitmq/rabbitmq.conf:ro
    healthcheck:
      test: ["CMD", "rabbitmq-diagnostics", "ping"]
      interval: 10s
      timeout: 5s
      retries: 5
    networks:
      - app_network

  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector:latest
    container_name: otel-collector
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
    networks:
      - app_network

  # Jaeger (追踪后端)
  jaeger:
    image: jaegertracing/all-in-one:latest
    container_name: jaeger
    ports:
      - "16686:16686"  # Jaeger UI
      - "14250:14250"  # gRPC
    networks:
      - app_network

volumes:
  rabbitmq_data:

networks:
  app_network:
    driver: bridge
```

### 11.2 配置文件

```conf
# docker/rabbitmq.conf
# 内存限制
vm_memory_high_watermark.relative = 0.6

# 磁盘空间限制
disk_free_limit.absolute = 2GB

# 心跳间隔
heartbeat = 60

# 连接限制
num_acceptors.tcp = 10

# 日志
log.file.level = info
log.console = true
log.console.level = info

# 管理插件
management.tcp.port = 15672
management.load_definitions = /etc/rabbitmq/definitions.json
```

---

## 12. 国际标准对齐

### 12.1 AMQP 0.9.1 完整对齐

| AMQP 0.9.1 要求 | 实现状态 | 说明 |
|-----------------|---------|------|
| **连接管理** | ✅ 100% | Connection, Channel, Heartbeat |
| **Exchange 类型** | ✅ 100% | Direct, Topic, Fanout, Headers |
| **消息确认** | ✅ 100% | ACK, NACK, Reject |
| **发布者确认** | ✅ 100% | Publisher Confirms |
| **事务** | ✅ 100% | tx.select, tx.commit, tx.rollback |
| **QoS** | ✅ 100% | Prefetch count |
| **持久化** | ✅ 100% | Durable Exchange/Queue, Persistent Message |

### 12.2 OpenTelemetry Semantic Conventions

```rust
// 消息系统追踪属性
let span_attributes = vec![
    KeyValue::new("messaging.system", "rabbitmq"),
    KeyValue::new("messaging.destination", exchange),
    KeyValue::new("messaging.destination_kind", "exchange"),  // queue | exchange
    KeyValue::new("messaging.rabbitmq.routing_key", routing_key),
    KeyValue::new("messaging.protocol", "AMQP"),
    KeyValue::new("messaging.protocol_version", "0.9.1"),
    KeyValue::new("messaging.operation", "publish"),  // publish | receive | process
    KeyValue::new("messaging.message_payload_size_bytes", payload_size),
];
```

---

## 13. 总结

### 13.1 RabbitMQ 核心优势

| 特性 | 优势 |
|------|------|
| **企业级稳定性** | 2007年至今，大量生产验证 |
| **AMQP 标准** | 国际标准协议，互操作性强 |
| **路由灵活性** | Direct, Topic, Fanout, Headers 多种模式 |
| **可靠性保证** | 持久化、确认机制、事务支持 |
| **管理工具** | Web UI、REST API、命令行工具 |
| **插件生态** | 延迟队列、死信队列、优先级队列等 |

### 13.2 何时选择 RabbitMQ

- ✅ 企业级应用（需要稳定性和成熟度）
- ✅ 复杂路由需求（Topic, Headers Exchange）
- ✅ 需要事务支持
- ✅ RPC 模式通信
- ✅ 需要管理界面和监控
- ❌ 超高吞吐量（选 Kafka）
- ❌ 简单轻量级（选 NATS）

### 13.3 生产部署清单

- [x] 启用发布者确认（Publisher Confirms）
- [x] 设置合理的 QoS（prefetch count）
- [x] 配置死信队列（DLX）
- [x] 启用消息持久化
- [x] 监控队列长度和消费速率
- [x] 集群高可用（镜像队列或仲裁队列）
- [x] OTLP 分布式追踪
- [x] 日志聚合（ELK）

---

**文档版本**: v1.0.0  
**Rust 版本**: 1.90  
**Lapin 版本**: 2.3  
**OpenTelemetry 版本**: 0.25  

**参考资源**:

- [RabbitMQ 官方文档](https://www.rabbitmq.com/documentation.html)
- [AMQP 0.9.1 规范](https://www.rabbitmq.com/amqp-0-9-1-reference.html)
- [Lapin 文档](https://docs.rs/lapin)
- [OpenTelemetry Messaging Conventions](https://opentelemetry.io/docs/specs/semconv/messaging/)
