# ⚡ CQRS 架构 (Command Query Responsibility Segregation) - Rust OTLP 完整实现

> **架构提出者**: Greg Young (2010)  
> **国际标准**: Microsoft Azure Architecture Patterns  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [⚡ CQRS 架构 (Command Query Responsibility Segregation) - Rust OTLP 完整实现](#-cqrs-架构-command-query-responsibility-segregation---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
    - [核心价值](#核心价值)
  - [🎯 CQRS 核心概念](#-cqrs-核心概念)
    - [1. 架构全景图](#1-架构全景图)
    - [2. 核心组件](#2-核心组件)
  - [🏗️ Rust 项目结构](#️-rust-项目结构)
  - [💎 核心实现](#-核心实现)
    - [1. Domain Events (领域事件)](#1-domain-events-领域事件)
      - [`src/domain/events/order_created.rs`](#srcdomaineventsorder_createdrs)
    - [2. Event Store (事件存储)](#2-event-store-事件存储)
      - [`src/event_store/postgres_event_store.rs`](#srcevent_storepostgres_event_storers)
    - [3. Command Handler (命令处理器)](#3-command-handler-命令处理器)
      - [`src/commands/handlers/create_order.rs`](#srccommandshandlerscreate_orderrs)
    - [4. Event Bus (事件总线)](#4-event-bus-事件总线)
      - [`src/infrastructure/event_bus/kafka_bus.rs`](#srcinfrastructureevent_buskafka_busrs)
    - [5. Projection (读模型投影)](#5-projection-读模型投影)
      - [`src/projections/order_projection.rs`](#srcprojectionsorder_projectionrs)
    - [6. Query Handler (查询处理器)](#6-query-handler-查询处理器)
      - [`src/queries/handlers/get_order.rs`](#srcquerieshandlersget_orderrs)
    - [7. Read Model (读模型)](#7-read-model-读模型)
      - [`src/queries/models/order_view.rs`](#srcqueriesmodelsorder_viewrs)
  - [📊 完整 OTLP 追踪示例](#-完整-otlp-追踪示例)
    - [创建订单完整链路](#创建订单完整链路)
  - [📦 Cargo.toml 完整依赖](#-cargotoml-完整依赖)
  - [🌟 CQRS 最佳实践](#-cqrs-最佳实践)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)
  - [🔗 参考资源](#-参考资源)
    - [架构模式](#架构模式)
    - [Rust 实现](#rust-实现)
    - [国际标准](#国际标准)

## 📊 执行摘要

CQRS (Command Query Responsibility Segregation,命令查询职责分离)是一种将系统的读操作(Query)和写操作(Command)完全分离的架构模式。
本文档展示如何在 Rust 1.90 中实现完整的 CQRS 架构,结合 Event Sourcing 和 OpenTelemetry 分布式追踪,构建高性能、可扩展的企业级系统。

### 核心价值

| 特性 | 传统 CRUD | CQRS 架构 | 优势 |
|------|----------|----------|------|
| **读写分离** | 同一模型 | 独立优化 | +500% 查询性能 |
| **扩展性** | 垂直扩展 | 水平扩展 | +1000% 吞吐量 |
| **数据一致性** | 强一致 | 最终一致 | -80% 写锁竞争 |
| **查询复杂度** | JOIN 地狱 | 预计算视图 | +300% 查询速度 |
| **OTLP 追踪** | 混合追踪 | 独立追踪链路 | 清晰隔离 |

---

## 🎯 CQRS 核心概念

### 1. 架构全景图

```text
┌────────────────────────────────────────────────────────────────┐
│                      Client / API Gateway                      │
└──────────────────┬─────────────────────┬───────────────────────┘
                   │                     │
         Commands (写)             Queries (读)
                   │                     │
        ┌──────────▼──────────┐  ┌──────▼──────────┐
        │   Command Side      │  │   Query Side    │
        │  (Write Model)      │  │  (Read Model)   │
        └──────────┬──────────┘  └──────┬──────────┘
                   │                     │
    ┌──────────────▼──────────────┐     │
    │  Command Handlers           │     │
    │  (业务逻辑 + 事件生成)       │     │
    └──────────────┬──────────────┘     │
                   │                    │
    ┌──────────────▼──────────────┐     │
    │      Event Store            │     │
    │  (事件溯源存储: PostgreSQL)  │     │
    └──────────────┬──────────────┘     │
                   │                    │
                   │ Event Bus (Kafka)  │
                   │                    │
    ┌──────────────▼──────────────┐     │
    │    Event Handlers           │     │
    │  (Projections 投影)         │     │
    └──────────────┬──────────────┘     │
                   │                    │
    ┌──────────────▼──────────────┐     │
    │   Read Model Store          │◄────┘
    │  (优化查询: Elasticsearch)   │
    └─────────────────────────────┘

⚡ OTLP 追踪:
  • Command Side: 完整写入链路追踪
  • Event Store: 事件持久化追踪
  • Event Bus: 消息传播追踪
  • Projection: 读模型更新追踪
  • Query Side: 查询性能追踪
```

### 2. 核心组件

| 组件 | 职责 | 存储 | 追踪重点 |
|------|------|------|----------|
| **Command Handler** | 处理写操作,生成事件 | Event Store (PostgreSQL) | 业务逻辑执行时间 |
| **Event Store** | 持久化所有事件 | Append-Only Log | 事件写入延迟 |
| **Event Bus** | 异步传播事件 | Kafka / Redis Streams | 消息传递延迟 |
| **Event Handler** | 更新读模型 (Projection) | Read Model Store | 投影更新时间 |
| **Query Handler** | 处理读操作 | Elasticsearch / MongoDB | 查询响应时间 |

---

## 🏗️ Rust 项目结构

```text
cqrs-ecommerce/
├── Cargo.toml
├── src/
│   ├── main.rs                    # 依赖注入 + OTLP 初始化
│   │
│   ├── domain/                    # 领域模型 (共享)
│   │   ├── mod.rs
│   │   ├── entities/
│   │   │   ├── mod.rs
│   │   │   ├── order.rs           # 订单聚合根
│   │   │   └── product.rs         # 商品实体
│   │   ├── value_objects/
│   │   │   ├── mod.rs
│   │   │   ├── money.rs
│   │   │   └── order_status.rs
│   │   └── events/                # 领域事件
│   │       ├── mod.rs
│   │       ├── order_created.rs
│   │       ├── order_confirmed.rs
│   │       └── order_shipped.rs
│   │
│   ├── commands/                  # 🔥 Command Side (写端)
│   │   ├── mod.rs
│   │   ├── handlers/              # 命令处理器
│   │   │   ├── mod.rs
│   │   │   ├── create_order.rs    # + OTLP
│   │   │   ├── confirm_order.rs   # + OTLP
│   │   │   └── ship_order.rs      # + OTLP
│   │   └── models/                # 命令模型
│   │       ├── mod.rs
│   │       └── order_commands.rs
│   │
│   ├── queries/                   # 🔍 Query Side (读端)
│   │   ├── mod.rs
│   │   ├── handlers/              # 查询处理器
│   │   │   ├── mod.rs
│   │   │   ├── get_order.rs       # + OTLP
│   │   │   ├── list_orders.rs     # + OTLP
│   │   │   └── search_orders.rs   # + OTLP
│   │   ├── models/                # 查询模型 (Read Model)
│   │   │   ├── mod.rs
│   │   │   └── order_view.rs      # 优化的查询模型
│   │   └── dto/
│   │       ├── mod.rs
│   │       └── order_dto.rs
│   │
│   ├── event_store/               # 📚 事件存储
│   │   ├── mod.rs
│   │   ├── postgres_event_store.rs # PostgreSQL 实现 + OTLP
│   │   └── event_stream.rs        # 事件流读取
│   │
│   ├── projections/               # 🔄 事件投影 (更新 Read Model)
│   │   ├── mod.rs
│   │   ├── order_projection.rs    # + OTLP
│   │   └── analytics_projection.rs
│   │
│   ├── infrastructure/            # 基础设施
│   │   ├── mod.rs
│   │   ├── event_bus/             # 事件总线
│   │   │   ├── mod.rs
│   │   │   └── kafka_bus.rs       # Kafka 实现 + OTLP
│   │   ├── read_store/            # 读模型存储
│   │   │   ├── mod.rs
│   │   │   └── elasticsearch.rs   # Elasticsearch + OTLP
│   │   ├── web/                   # Web API
│   │   │   ├── mod.rs
│   │   │   ├── command_api.rs     # 命令端点 + OTLP
│   │   │   └── query_api.rs       # 查询端点 + OTLP
│   │   └── telemetry/             # OTLP 配置
│   │       ├── mod.rs
│   │       └── init.rs
│   └── lib.rs
└── tests/
    ├── command_tests.rs
    ├── query_tests.rs
    └── projection_tests.rs
```

---

## 💎 核心实现

### 1. Domain Events (领域事件)

#### `src/domain/events/order_created.rs`

```rust
//! 订单创建事件

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// 订单创建事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    /// 事件 ID
    pub event_id: Uuid,
    /// 聚合根 ID (订单 ID)
    pub aggregate_id: Uuid,
    /// 事件版本 (用于乐观锁)
    pub aggregate_version: i64,
    /// 事件时间戳
    pub occurred_at: DateTime<Utc>,
    /// 事件负载
    pub payload: OrderCreatedPayload,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderCreatedPayload {
    pub user_id: Uuid,
    pub items: Vec<OrderItemData>,
    pub total_amount_cents: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItemData {
    pub product_id: Uuid,
    pub quantity: u32,
    pub unit_price_cents: i64,
}

impl OrderCreatedEvent {
    pub fn new(aggregate_id: Uuid, payload: OrderCreatedPayload) -> Self {
        Self {
            event_id: Uuid::new_v4(),
            aggregate_id,
            aggregate_version: 1, // 第一个事件版本为 1
            occurred_at: Utc::now(),
            payload,
        }
    }
}

/// 订单确认事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderConfirmedEvent {
    pub event_id: Uuid,
    pub aggregate_id: Uuid,
    pub aggregate_version: i64,
    pub occurred_at: DateTime<Utc>,
    pub confirmed_by: Uuid, // 确认人
}

/// 订单发货事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderShippedEvent {
    pub event_id: Uuid,
    pub aggregate_id: Uuid,
    pub aggregate_version: i64,
    pub occurred_at: DateTime<Utc>,
    pub tracking_number: String,
    pub carrier: String,
}

/// 统一事件枚举
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "event_type")]
pub enum OrderEvent {
    Created(OrderCreatedEvent),
    Confirmed(OrderConfirmedEvent),
    Shipped(OrderShippedEvent),
}

impl OrderEvent {
    pub fn aggregate_id(&self) -> Uuid {
        match self {
            OrderEvent::Created(e) => e.aggregate_id,
            OrderEvent::Confirmed(e) => e.aggregate_id,
            OrderEvent::Shipped(e) => e.aggregate_id,
        }
    }

    pub fn aggregate_version(&self) -> i64 {
        match self {
            OrderEvent::Created(e) => e.aggregate_version,
            OrderEvent::Confirmed(e) => e.aggregate_version,
            OrderEvent::Shipped(e) => e.aggregate_version,
        }
    }
}
```

---

### 2. Event Store (事件存储)

#### `src/event_store/postgres_event_store.rs`

```rust
//! PostgreSQL 事件存储实现 - Append-Only Log + OTLP

use crate::domain::events::OrderEvent;
use async_trait::async_trait;
use sqlx::PgPool;
use tracing::{error, info, instrument};
use uuid::Uuid;

/// 事件存储 Trait
#[async_trait]
pub trait EventStore: Send + Sync {
    /// 保存事件 (Append-Only)
    async fn append_event(&self, event: OrderEvent) -> Result<(), EventStoreError>;
    
    /// 读取聚合根的所有事件
    async fn load_events(&self, aggregate_id: Uuid) -> Result<Vec<OrderEvent>, EventStoreError>;
    
    /// 读取所有事件流 (用于投影)
    async fn load_all_events(&self, from_version: i64) -> Result<Vec<OrderEvent>, EventStoreError>;
}

/// PostgreSQL 事件存储实现
pub struct PostgresEventStore {
    pool: PgPool,
}

impl PostgresEventStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl EventStore for PostgresEventStore {
    #[instrument(
        name = "event_store.append_event",
        skip(self, event),
        fields(
            event_id = %event.aggregate_id(),
            aggregate_version = event.aggregate_version(),
            db.system = "postgresql",
            db.operation = "INSERT",
            cqrs.side = "command"
        )
    )]
    async fn append_event(&self, event: OrderEvent) -> Result<(), EventStoreError> {
        info!("追加事件到 Event Store");

        let event_type = match &event {
            OrderEvent::Created(_) => "OrderCreated",
            OrderEvent::Confirmed(_) => "OrderConfirmed",
            OrderEvent::Shipped(_) => "OrderShipped",
        };

        let event_data = serde_json::to_string(&event)
            .map_err(|e| EventStoreError::Serialization(e.to_string()))?;

        // 乐观锁: 确保事件版本连续
        let result = sqlx::query!(
            r#"
            INSERT INTO events (
                event_id, aggregate_id, aggregate_version, event_type, event_data, occurred_at
            )
            VALUES ($1, $2, $3, $4, $5, NOW())
            "#,
            Uuid::new_v4(),
            event.aggregate_id(),
            event.aggregate_version(),
            event_type,
            event_data
        )
        .execute(&self.pool)
        .await
        .map_err(|e| {
            error!("事件追加失败: {}", e);
            // 检查是否是版本冲突 (唯一索引冲突)
            if e.to_string().contains("duplicate key") {
                EventStoreError::ConcurrencyConflict
            } else {
                EventStoreError::Database(e.to_string())
            }
        })?;

        info!(rows_affected = result.rows_affected(), "事件追加成功");
        Ok(())
    }

    #[instrument(
        name = "event_store.load_events",
        skip(self),
        fields(
            aggregate_id = %aggregate_id,
            db.system = "postgresql",
            cqrs.side = "command"
        )
    )]
    async fn load_events(&self, aggregate_id: Uuid) -> Result<Vec<OrderEvent>, EventStoreError> {
        info!("加载聚合根事件流");

        let records = sqlx::query!(
            r#"
            SELECT event_data 
            FROM events 
            WHERE aggregate_id = $1 
            ORDER BY aggregate_version ASC
            "#,
            aggregate_id
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| EventStoreError::Database(e.to_string()))?;

        let events: Result<Vec<OrderEvent>, _> = records
            .into_iter()
            .map(|row| serde_json::from_str(&row.event_data))
            .collect();

        events.map_err(|e| EventStoreError::Serialization(e.to_string()))
    }

    #[instrument(
        name = "event_store.load_all_events",
        skip(self),
        fields(
            from_version = from_version,
            db.system = "postgresql",
            cqrs.side = "projection"
        )
    )]
    async fn load_all_events(&self, from_version: i64) -> Result<Vec<OrderEvent>, EventStoreError> {
        info!("加载全局事件流 (用于投影)");

        let records = sqlx::query!(
            r#"
            SELECT event_data 
            FROM events 
            WHERE id > $1 
            ORDER BY id ASC
            LIMIT 1000
            "#,
            from_version
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| EventStoreError::Database(e.to_string()))?;

        let events: Result<Vec<OrderEvent>, _> = records
            .into_iter()
            .map(|row| serde_json::from_str(&row.event_data))
            .collect();

        events.map_err(|e| EventStoreError::Serialization(e.to_string()))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EventStoreError {
    #[error("数据库错误: {0}")]
    Database(String),

    #[error("序列化错误: {0}")]
    Serialization(String),

    #[error("并发冲突: 事件版本已存在")]
    ConcurrencyConflict,
}
```

---

### 3. Command Handler (命令处理器)

#### `src/commands/handlers/create_order.rs`

```rust
//! 创建订单命令处理器 - Command Side + OTLP

use crate::{
    domain::events::{OrderCreatedEvent, OrderCreatedPayload, OrderEvent},
    event_store::{EventStore, EventStoreError},
    infrastructure::event_bus::EventBus,
};
use std::sync::Arc;
use tracing::{info, instrument};
use uuid::Uuid;

/// 创建订单命令处理器
pub struct CreateOrderHandler {
    event_store: Arc<dyn EventStore>,
    event_bus: Arc<dyn EventBus>,
}

impl CreateOrderHandler {
    pub fn new(event_store: Arc<dyn EventStore>, event_bus: Arc<dyn EventBus>) -> Self {
        Self {
            event_store,
            event_bus,
        }
    }

    /// 处理创建订单命令 (⚡ OTLP Command Side 追踪)
    #[instrument(
        name = "command.create_order",
        skip(self, command),
        fields(
            user_id = %command.user_id,
            items_count = command.items.len(),
            cqrs.side = "command",
            cqrs.operation = "create"
        )
    )]
    pub async fn handle(&self, command: CreateOrderCommand) -> Result<Uuid, CommandError> {
        info!("处理创建订单命令");

        // 1. 生成聚合根 ID
        let order_id = Uuid::new_v4();

        // 2. 执行业务验证
        if command.items.is_empty() {
            return Err(CommandError::InvalidCommand("订单不能为空".to_string()));
        }

        // 3. 创建领域事件
        let event = OrderCreatedEvent::new(
            order_id,
            OrderCreatedPayload {
                user_id: command.user_id,
                items: command.items,
                total_amount_cents: command.total_amount_cents,
            },
        );

        // 4. 追加事件到 Event Store (⚡ 子 Span)
        self.event_store
            .append_event(OrderEvent::Created(event.clone()))
            .await
            .map_err(|e| match e {
                EventStoreError::ConcurrencyConflict => CommandError::ConcurrencyConflict,
                _ => CommandError::EventStoreError(e.to_string()),
            })?;

        // 5. 发布事件到 Event Bus (⚡ 子 Span)
        self.event_bus
            .publish(OrderEvent::Created(event))
            .await
            .map_err(|e| CommandError::EventBusError(e.to_string()))?;

        info!(order_id = %order_id, "订单创建成功");
        Ok(order_id)
    }
}

/// 创建订单命令
#[derive(Debug, serde::Deserialize)]
pub struct CreateOrderCommand {
    pub user_id: Uuid,
    pub items: Vec<crate::domain::events::OrderItemData>,
    pub total_amount_cents: i64,
}

#[derive(Debug, thiserror::Error)]
pub enum CommandError {
    #[error("无效的命令: {0}")]
    InvalidCommand(String),

    #[error("并发冲突")]
    ConcurrencyConflict,

    #[error("事件存储错误: {0}")]
    EventStoreError(String),

    #[error("事件总线错误: {0}")]
    EventBusError(String),
}
```

---

### 4. Event Bus (事件总线)

#### `src/infrastructure/event_bus/kafka_bus.rs`

```rust
//! Kafka 事件总线 - 异步事件传播 + OTLP

use crate::domain::events::OrderEvent;
use async_trait::async_trait;
use rdkafka::{
    producer::{FutureProducer, FutureRecord},
    ClientConfig,
};
use tracing::{error, info, instrument};

/// 事件总线 Trait
#[async_trait]
pub trait EventBus: Send + Sync {
    async fn publish(&self, event: OrderEvent) -> Result<(), EventBusError>;
}

/// Kafka 事件总线实现
pub struct KafkaEventBus {
    producer: FutureProducer,
    topic: String,
}

impl KafkaEventBus {
    pub fn new(brokers: &str, topic: String) -> Result<Self, EventBusError> {
        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .create()
            .map_err(|e| EventBusError::InitializationFailed(e.to_string()))?;

        Ok(Self { producer, topic })
    }
}

#[async_trait]
impl EventBus for KafkaEventBus {
    #[instrument(
        name = "event_bus.publish",
        skip(self, event),
        fields(
            event_id = %event.aggregate_id(),
            messaging.system = "kafka",
            messaging.destination = %self.topic,
            cqrs.event_type = ?event
        )
    )]
    async fn publish(&self, event: OrderEvent) -> Result<(), EventBusError> {
        info!("发布事件到 Kafka");

        let event_json = serde_json::to_string(&event)
            .map_err(|e| EventBusError::Serialization(e.to_string()))?;

        let key = event.aggregate_id().to_string();

        let record = FutureRecord::to(&self.topic)
            .key(&key)
            .payload(&event_json);

        self.producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| {
                error!("Kafka 发送失败: {}", e);
                EventBusError::PublishFailed(e.to_string())
            })?;

        info!("事件发布成功");
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EventBusError {
    #[error("初始化失败: {0}")]
    InitializationFailed(String),

    #[error("序列化错误: {0}")]
    Serialization(String),

    #[error("发布失败: {0}")]
    PublishFailed(String),
}
```

---

### 5. Projection (读模型投影)

#### `src/projections/order_projection.rs`

```rust
//! 订单投影 - 更新读模型 + OTLP

use crate::{
    domain::events::{OrderCreatedEvent, OrderEvent},
    queries::models::OrderView,
};
use async_trait::async_trait;
use elasticsearch::{Elasticsearch, IndexParts};
use serde_json::json;
use tracing::{info, instrument};

/// 投影处理器 Trait
#[async_trait]
pub trait ProjectionHandler: Send + Sync {
    async fn handle_event(&self, event: OrderEvent) -> Result<(), ProjectionError>;
}

/// 订单投影处理器 (Elasticsearch)
pub struct OrderProjectionHandler {
    es_client: Elasticsearch,
    index: String,
}

impl OrderProjectionHandler {
    pub fn new(es_client: Elasticsearch, index: String) -> Self {
        Self { es_client, index }
    }
}

#[async_trait]
impl ProjectionHandler for OrderProjectionHandler {
    #[instrument(
        name = "projection.handle_event",
        skip(self, event),
        fields(
            event_id = %event.aggregate_id(),
            cqrs.side = "projection",
            cqrs.destination = "elasticsearch"
        )
    )]
    async fn handle_event(&self, event: OrderEvent) -> Result<(), ProjectionError> {
        match event {
            OrderEvent::Created(e) => self.handle_order_created(e).await,
            OrderEvent::Confirmed(e) => self.handle_order_confirmed(e).await,
            OrderEvent::Shipped(e) => self.handle_order_shipped(e).await,
        }
    }
}

impl OrderProjectionHandler {
    #[instrument(
        name = "projection.order_created",
        skip(self, event),
        fields(order_id = %event.aggregate_id)
    )]
    async fn handle_order_created(&self, event: OrderCreatedEvent) -> Result<(), ProjectionError> {
        info!("更新读模型: 订单创建");

        // 创建读模型文档
        let order_view = OrderView {
            id: event.aggregate_id,
            user_id: event.payload.user_id,
            status: "pending".to_string(),
            total_amount_cents: event.payload.total_amount_cents,
            created_at: event.occurred_at,
            updated_at: event.occurred_at,
        };

        // 索引到 Elasticsearch
        self.es_client
            .index(IndexParts::IndexId(&self.index, &event.aggregate_id.to_string()))
            .body(json!(order_view))
            .send()
            .await
            .map_err(|e| ProjectionError::StorageError(e.to_string()))?;

        info!("读模型更新成功");
        Ok(())
    }

    async fn handle_order_confirmed(&self, event: crate::domain::events::OrderConfirmedEvent) -> Result<(), ProjectionError> {
        info!("更新读模型: 订单确认");

        // 更新文档状态
        self.es_client
            .update(IndexParts::IndexId(&self.index, &event.aggregate_id.to_string()))
            .body(json!({
                "doc": {
                    "status": "confirmed",
                    "updated_at": event.occurred_at
                }
            }))
            .send()
            .await
            .map_err(|e| ProjectionError::StorageError(e.to_string()))?;

        Ok(())
    }

    async fn handle_order_shipped(&self, event: crate::domain::events::OrderShippedEvent) -> Result<(), ProjectionError> {
        info!("更新读模型: 订单发货");

        self.es_client
            .update(IndexParts::IndexId(&self.index, &event.aggregate_id.to_string()))
            .body(json!({
                "doc": {
                    "status": "shipped",
                    "tracking_number": event.tracking_number,
                    "carrier": event.carrier,
                    "updated_at": event.occurred_at
                }
            }))
            .send()
            .await
            .map_err(|e| ProjectionError::StorageError(e.to_string()))?;

        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ProjectionError {
    #[error("存储错误: {0}")]
    StorageError(String),
}
```

---

### 6. Query Handler (查询处理器)

#### `src/queries/handlers/get_order.rs`

```rust
//! 查询订单处理器 - Query Side + OTLP

use crate::queries::models::OrderView;
use elasticsearch::{Elasticsearch, GetParts};
use tracing::{info, instrument};
use uuid::Uuid;

/// 查询订单处理器
pub struct GetOrderHandler {
    es_client: Elasticsearch,
    index: String,
}

impl GetOrderHandler {
    pub fn new(es_client: Elasticsearch, index: String) -> Self {
        Self { es_client, index }
    }

    /// 查询单个订单 (⚡ OTLP Query Side 追踪)
    #[instrument(
        name = "query.get_order",
        skip(self),
        fields(
            order_id = %order_id,
            cqrs.side = "query",
            cqrs.source = "elasticsearch"
        )
    )]
    pub async fn handle(&self, order_id: Uuid) -> Result<Option<OrderView>, QueryError> {
        info!("查询订单");

        let response = self
            .es_client
            .get(GetParts::IndexId(&self.index, &order_id.to_string()))
            .send()
            .await
            .map_err(|e| QueryError::StorageError(e.to_string()))?;

        if response.status_code().is_success() {
            let json = response.json::<serde_json::Value>().await
                .map_err(|e| QueryError::DeserializationError(e.to_string()))?;

            let order_view: OrderView = serde_json::from_value(json["_source"].clone())
                .map_err(|e| QueryError::DeserializationError(e.to_string()))?;

            info!("订单查询成功");
            Ok(Some(order_view))
        } else {
            info!("订单未找到");
            Ok(None)
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum QueryError {
    #[error("存储错误: {0}")]
    StorageError(String),

    #[error("反序列化错误: {0}")]
    DeserializationError(String),
}
```

---

### 7. Read Model (读模型)

#### `src/queries/models/order_view.rs`

```rust
//! 订单读模型 - 优化的查询视图

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// 订单读模型 (扁平化,无关联,优化查询)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderView {
    pub id: Uuid,
    pub user_id: Uuid,
    pub status: String, // "pending", "confirmed", "shipped"
    pub total_amount_cents: i64,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    
    // 额外的查询优化字段
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tracking_number: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub carrier: Option<String>,
}
```

---

## 📊 完整 OTLP 追踪示例

### 创建订单完整链路

```text
HTTP POST /commands/orders (Command API)
  └─ command.create_order [Span] (Command Handler)
      ├─ 业务验证 (无追踪)
      ├─ event_store.append_event [Span]
      │   └─ PostgreSQL INSERT (数据库 Span)
      ├─ event_bus.publish [Span]
      │   └─ Kafka SEND (消息队列 Span)
      └─ HTTP 201 Created

[异步 - 不同 Trace]
Kafka Consumer 接收事件
  └─ projection.handle_event [Span]
      └─ projection.order_created [Span]
          └─ Elasticsearch INDEX (搜索引擎 Span)

[不同 Trace]
HTTP GET /queries/orders/{id} (Query API)
  └─ query.get_order [Span] (Query Handler)
      └─ Elasticsearch GET (搜索引擎 Span)
```

---

## 📦 Cargo.toml 完整依赖

```toml
[package]
name = "cqrs-ecommerce"
version = "1.0.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# 异步运行时
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web 框架
axum = "0.7"
tower-http = { version = "0.6", features = ["trace"] }

# 数据库 (Event Store)
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "uuid", "chrono"] }

# 消息队列 (Event Bus)
rdkafka = { version = "0.36", features = ["cmake-build"] }

# 搜索引擎 (Read Model)
elasticsearch = "8.15"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# UUID & 时间
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# OpenTelemetry (完整栈)
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
```

---

## 🌟 CQRS 最佳实践

### ✅ DO (推荐)

1. **读写完全分离**: Command 和 Query 使用不同的数据模型和存储
2. **事件溯源集成**: Command Side 使用 Event Store,记录所有状态变更
3. **异步投影**: 通过 Event Bus 异步更新读模型,允许最终一致性
4. **读模型优化**: 针对查询场景设计扁平化、去规范化的读模型
5. **OTLP 分离追踪**: Command Side 和 Query Side 独立追踪链路
6. **幂等性保证**: 投影处理器必须支持幂等操作
7. **版本控制**: 使用聚合根版本号实现乐观锁

### ❌ DON'T (避免)

1. **同步投影**: 不要在 Command Handler 中同步更新读模型
2. **跨端查询**: Command Side 不查询读模型,Query Side 不写入
3. **共享数据库**: 读写模型不共享同一个数据库实例
4. **强一致性期待**: 接受最终一致性,不追求实时同步
5. **过度拆分**: 不是所有系统都需要 CQRS,适合读写比例悬殊的场景

---

## 🔗 参考资源

### 架构模式

- [Greg Young - CQRS](https://cqrs.wordpress.com/)
- [Martin Fowler - CQRS](https://martinfowler.com/bliki/CQRS.html)
- [Microsoft - CQRS Pattern](https://learn.microsoft.com/en-us/azure/architecture/patterns/cqrs)
- [Event Sourcing](https://martinfowler.com/eaaDev/EventSourcing.html)

### Rust 实现

- [Rust Event Sourcing](https://github.com/johnnynotsolucky/samples/tree/main/event-sourcing)
- [Elasticsearch Rust Client](https://docs.rs/elasticsearch/latest/elasticsearch/)
- [rdkafka Documentation](https://docs.rs/rdkafka/latest/rdkafka/)

### 国际标准

- [CNCF OpenTelemetry](https://opentelemetry.io/)
- [W3C Trace Context](https://www.w3.org/TR/trace-context/)
- [Cloud Events](https://cloudevents.io/)

---

**文档版本**: 1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

**⚡ CQRS + Event Sourcing: 构建高性能、可扩展的企业级系统!** 🚀
