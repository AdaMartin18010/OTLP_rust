# CQRS 架构 (Command Query Responsibility Segregation) - Rust OTLP 读写分离追踪

> **架构模式**: CQRS (Command Query Responsibility Segregation)  
> **提出者**: Greg Young (2010)  
> **国际标准**: 微软 Azure 推荐模式, CNCF 事件驱动架构  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **更新日期**: 2025年10月11日

---

## 📋 目录

- [CQRS 架构 (Command Query Responsibility Segregation) - Rust OTLP 读写分离追踪](#cqrs-架构-command-query-responsibility-segregation---rust-otlp-读写分离追踪)
  - [📋 目录](#-目录)
  - [🏛️ 架构概述](#️-架构概述)
    - [什么是 CQRS?](#什么是-cqrs)
      - [核心思想](#核心思想)
    - [国际标准对标](#国际标准对标)
  - [🎯 核心概念](#-核心概念)
    - [1. Command (命令) - 写操作](#1-command-命令---写操作)
    - [2. Query (查询) - 读操作](#2-query-查询---读操作)
    - [3. Write Model vs Read Model](#3-write-model-vs-read-model)
    - [4. Event Bus (事件总线)](#4-event-bus-事件总线)
  - [🆚 CQRS vs 传统 CRUD](#-cqrs-vs-传统-crud)
    - [传统 CRUD 的问题](#传统-crud-的问题)
    - [CQRS 的优势](#cqrs-的优势)
  - [🔄 Event Sourcing 集成](#-event-sourcing-集成)
    - [什么是 Event Sourcing?](#什么是-event-sourcing)
  - [🦀 Rust 实现设计](#-rust-实现设计)
    - [项目结构](#项目结构)
  - [🔭 OTLP 读写分离追踪](#-otlp-读写分离追踪)
    - [策略: Command 端 vs Query 端追踪](#策略-command-端-vs-query-端追踪)
  - [📦 完整订单系统示例](#-完整订单系统示例)
    - [1. 领域层 (Domain Layer)](#1-领域层-domain-layer)
      - [1.1 聚合根 (Aggregate Root)](#11-聚合根-aggregate-root)
      - [1.2 领域事件 (Domain Events)](#12-领域事件-domain-events)
    - [2. Write Side (Command 端)](#2-write-side-command-端)
      - [2.1 Command Handler](#21-command-handler)
      - [2.2 Event Store (PostgreSQL)](#22-event-store-postgresql)
    - [3. Read Side (Query 端)](#3-read-side-query-端)
      - [3.1 Read Model](#31-read-model)
      - [3.2 Projection (投影)](#32-projection-投影)
      - [3.3 Elasticsearch Repository](#33-elasticsearch-repository)
      - [3.4 Query Handler](#34-query-handler)
  - [⏱️ 最终一致性处理](#️-最终一致性处理)
    - [问题: 读模型可能滞后](#问题-读模型可能滞后)
    - [解决方案](#解决方案)
      - [方案 1: 版本号 + 重试](#方案-1-版本号--重试)
      - [方案 2: Command 返回完整结果](#方案-2-command-返回完整结果)
  - [🚀 性能优化](#-性能优化)
    - [1. 读模型缓存](#1-读模型缓存)
  - [📦 生产部署](#-生产部署)
    - [Cargo.toml](#cargotoml)
    - [Docker Compose](#docker-compose)
  - [✅ 最佳实践](#-最佳实践)
    - [CQRS 设计](#cqrs-设计)
    - [OTLP 集成](#otlp-集成)

---

## 🏛️ 架构概述

### 什么是 CQRS?

**CQRS** (Command Query Responsibility Segregation) 是一种架构模式，将**写操作 (Command)** 和**读操作 (Query)** 分离到不同的模型中。

#### 核心思想

```text
传统 CRUD (统一模型):
┌─────────────┐
│   Client    │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Service    │ (读写使用同一模型)
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Database   │ (单一数据库)
└─────────────┘


CQRS (读写分离):
                  ┌─────────────┐
                  │   Client    │
                  └──────┬──────┘
                         │
         ┌───────────────┴───────────────┐
         │                               │
    写操作 (Command)                 读操作 (Query)
         ▼                               ▼
┌────────────────┐              ┌────────────────┐
│ Command Handler│              │  Query Handler │
│  (业务逻辑)     │              │  (数据查询)     │
└────────┬───────┘              └────────┬───────┘
         │                               │
         ▼                               ▼
┌────────────────┐   Event Bus  ┌────────────────┐
│   Write Model  │─────────────→│   Read Model   │
│  (PostgreSQL)  │   同步/异步   │ (Elasticsearch)│
└────────────────┘              └────────────────┘
```

---

### 国际标准对标

| 标准/框架 | 提出者/组织 | 年份 | CQRS 对标 |
|----------|-----------|------|-----------|
| **CQRS Pattern** | Greg Young | 2010 | ✅ 本架构 |
| **Event Sourcing** | Martin Fowler | 2005 | ✅ 完美搭档 |
| **Microsoft Azure Architecture** | Microsoft | 2017 | ✅ 推荐模式 |
| **DDD (Domain-Driven Design)** | Eric Evans | 2003 | ✅ 聚合根分离 |
| **Event-Driven Architecture** | CNCF | - | ✅ 事件驱动 |
| **Microservices Patterns** | Chris Richardson | 2018 | ✅ 服务拆分 |

---

## 🎯 核心概念

### 1. Command (命令) - 写操作

**特点**:

- 改变系统状态
- 有副作用
- 返回操作结果 (成功/失败)
- 需要验证业务规则

**示例**:

- `CreateOrder` - 创建订单
- `CancelOrder` - 取消订单
- `UpdateInventory` - 更新库存

```rust
// Command 定义
pub struct CreateOrderCommand {
    pub customer_id: CustomerId,
    pub items: Vec<OrderItem>,
    pub shipping_address: Address,
}

// Command Handler
#[async_trait]
pub trait CommandHandler<C>: Send + Sync {
    type Result;
    async fn handle(&self, command: C) -> Result<Self::Result>;
}
```

---

### 2. Query (查询) - 读操作

**特点**:

- 不改变系统状态
- 无副作用 (幂等)
- 返回数据
- 可以缓存
- 可以优化索引

**示例**:

- `GetOrderById` - 查询订单详情
- `ListOrdersByCustomer` - 查询客户订单列表
- `SearchOrders` - 搜索订单

```rust
// Query 定义
pub struct GetOrderByIdQuery {
    pub order_id: OrderId,
}

// Query Handler
#[async_trait]
pub trait QueryHandler<Q>: Send + Sync {
    type Result;
    async fn handle(&self, query: Q) -> Result<Self::Result>;
}
```

---

### 3. Write Model vs Read Model

| 维度 | Write Model (写模型) | Read Model (读模型) |
|------|---------------------|-------------------|
| **目的** | 保证业务规则一致性 | 快速查询 |
| **数据库** | PostgreSQL (ACID) | Elasticsearch (搜索) |
| **数据结构** | 规范化 (3NF) | 反规范化 (扁平) |
| **一致性** | 强一致性 | 最终一致性 |
| **性能** | 写优化 | 读优化 |
| **索引** | 主键、外键 | 全文索引、聚合 |

---

### 4. Event Bus (事件总线)

连接 Write Model 和 Read Model 的桥梁：

```text
Write Model                Event Bus              Read Model
    │                          │                      │
    │  1. 写入数据              │                      │
    ▼                          │                      │
┌─────────┐                   │                      │
│ Postgres│                   │                      │
└────┬────┘                   │                      │
     │                         │                      │
     │  2. 发布事件             ▼                      │
     └──────────────→  ┌──────────────┐              │
                       │    Kafka     │              │
                       │  (Event Bus) │              │
                       └──────┬───────┘              │
                              │  3. 消费事件          │
                              └──────────────────────▼
                                              ┌──────────────┐
                                              │Elasticsearch │
                                              │ (更新索引)   │
                                              └──────────────┘
```

---

## 🆚 CQRS vs 传统 CRUD

### 传统 CRUD 的问题

```rust
// 传统 CRUD: 读写使用同一模型
pub struct Order {
    pub id: OrderId,
    pub customer: Customer,         // ❌ 查询时需要 JOIN
    pub items: Vec<OrderItem>,      // ❌ 查询时需要 JOIN
    pub shipping_address: Address,  // ❌ 查询时需要 JOIN
    pub status: OrderStatus,
    // ... 还有很多字段
}

// 查询订单列表: 需要多表 JOIN, 性能差
SELECT o.*, c.*, oi.*, a.*
FROM orders o
JOIN customers c ON o.customer_id = c.id
JOIN order_items oi ON o.id = oi.order_id
JOIN addresses a ON o.address_id = a.id
WHERE c.id = ?;  -- 慢!
```

### CQRS 的优势

```rust
// Write Model: 规范化,保证一致性
pub struct Order {
    pub id: OrderId,
    pub customer_id: CustomerId,    // ✅ 只存 ID
    pub items: Vec<OrderItem>,
    pub address_id: AddressId,      // ✅ 只存 ID
    pub status: OrderStatus,
}

// Read Model: 反规范化,查询优化
pub struct OrderReadModel {
    pub id: OrderId,
    pub customer_name: String,      // ✅ 直接存名字
    pub customer_email: String,     // ✅ 直接存邮箱
    pub item_names: Vec<String>,    // ✅ 直接存商品名
    pub total_amount: f64,          // ✅ 预计算总金额
    pub address_full: String,       // ✅ 完整地址字符串
    pub status: String,
    pub created_at: DateTime<Utc>,
}

// 查询订单列表: 无需 JOIN, 直接查询
SELECT * FROM order_read_models WHERE customer_name LIKE ?;  -- 快!
```

---

## 🔄 Event Sourcing 集成

### 什么是 Event Sourcing?

将所有状态变化存储为**事件序列**，而非存储当前状态。

```text
传统方式 (State-Oriented):
┌──────────────────────┐
│ 订单表 (当前状态)     │
├──────────────────────┤
│ ID: 001              │
│ Status: SHIPPED      │  ← 只存最终状态,丢失历史
│ Amount: $100         │
└──────────────────────┘


Event Sourcing (Event-Oriented):
┌───────────────────────────────┐
│ 事件流 (完整历史)              │
├───────────────────────────────┤
│ 1. OrderCreated               │
│ 2. ItemAdded (Item1)          │
│ 3. ItemAdded (Item2)          │
│ 4. PaymentProcessed ($100)    │
│ 5. OrderShipped               │  ← 保存所有历史
└───────────────────────────────┘
       │
       │ 重放事件 (Replay)
       ▼
┌──────────────────────┐
│ 当前状态 (重建)       │
│ Status: SHIPPED      │
│ Amount: $100         │
└──────────────────────┘
```

---

## 🦀 Rust 实现设计

### 项目结构

```text
cqrs-order-service/
├── Cargo.toml
├── src/
│   ├── main.rs
│   │
│   ├── domain/                        # 领域层
│   │   ├── mod.rs
│   │   ├── aggregates/
│   │   │   └── order.rs               # 订单聚合根
│   │   ├── commands/
│   │   │   ├── mod.rs
│   │   │   ├── create_order.rs        # 创建订单命令
│   │   │   └── cancel_order.rs        # 取消订单命令
│   │   ├── events/
│   │   │   ├── mod.rs
│   │   │   ├── order_created.rs       # 订单创建事件
│   │   │   └── order_cancelled.rs     # 订单取消事件
│   │   └── value_objects/
│   │       ├── order_id.rs
│   │       └── money.rs
│   │
│   ├── write/                         # 写端 (Command Side)
│   │   ├── mod.rs
│   │   ├── handlers/
│   │   │   ├── mod.rs
│   │   │   ├── create_order_handler.rs
│   │   │   └── cancel_order_handler.rs
│   │   ├── repositories/
│   │   │   └── order_repository.rs    # PostgreSQL 写库
│   │   └── event_store/
│   │       └── postgres_event_store.rs # 事件存储
│   │
│   ├── read/                          # 读端 (Query Side)
│   │   ├── mod.rs
│   │   ├── models/
│   │   │   └── order_read_model.rs    # 读模型
│   │   ├── handlers/
│   │   │   ├── get_order_handler.rs
│   │   │   └── list_orders_handler.rs
│   │   ├── repositories/
│   │   │   └── order_read_repo.rs     # Elasticsearch 读库
│   │   └── projections/
│   │       └── order_projection.rs    # 投影 (事件→读模型)
│   │
│   ├── infrastructure/                # 基础设施层
│   │   ├── mod.rs
│   │   ├── web/
│   │   │   ├── command_controller.rs  # 命令 HTTP 端点
│   │   │   └── query_controller.rs    # 查询 HTTP 端点
│   │   ├── event_bus/
│   │   │   ├── kafka_producer.rs      # Kafka 生产者
│   │   │   └── kafka_consumer.rs      # Kafka 消费者
│   │   └── telemetry/
│   │       └── init.rs                # OTLP 初始化
│   │
│   └── config/
│       └── app_config.rs
│
└── tests/
    ├── integration/
    └── e2e/
```

---

## 🔭 OTLP 读写分离追踪

### 策略: Command 端 vs Query 端追踪

```text
┌─────────────────────────────────────────────────────────┐
│                    Command Side (写端)                   │
│  ✅ 完整业务逻辑追踪                                      │
│  - Command Handler (#[instrument])                      │
│  - 业务规则验证                                          │
│  - 事件发布                                              │
│  - 数据库写入 (PostgreSQL)                               │
│  - Kafka 事件发送                                        │
└──────────────────────┬──────────────────────────────────┘
                       │
                       │ 事件流 (Kafka)
                       │ Trace Context 传播
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│                    Query Side (读端)                     │
│  ✅ 投影处理追踪                                         │
│  - Event Consumer (#[instrument])                       │
│  - Projection 更新                                      │
│  - Elasticsearch 索引更新                                │
│  ✅ 查询追踪                                            │
│  - Query Handler (#[instrument])                        │
│  - Elasticsearch 查询                                   │
└─────────────────────────────────────────────────────────┘

关键点:
1. Command → Event: 通过 Kafka 传递 Trace Context
2. Event → Projection: 继续追踪链路
3. Query: 独立追踪 (可选关联到 Command)
```

---

## 📦 完整订单系统示例

### 1. 领域层 (Domain Layer)

#### 1.1 聚合根 (Aggregate Root)

```rust
// domain/aggregates/order.rs
use crate::domain::events::OrderEvent;
use crate::domain::value_objects::{OrderId, CustomerId, Money};
use chrono::{DateTime, Utc};

/// 订单聚合根
/// 
/// 负责:
/// 1. 业务规则验证
/// 2. 生成领域事件
/// 3. 重放事件 (Event Sourcing)
#[derive(Debug, Clone)]
pub struct OrderAggregate {
    // 状态
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    total_amount: Money,
    status: OrderStatus,
    created_at: DateTime<Utc>,
    
    // 事件溯源
    version: u64,                    // 版本号 (用于乐观锁)
    uncommitted_events: Vec<OrderEvent>,  // 未提交的事件
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

impl OrderAggregate {
    /// 创建订单 (Command)
    pub fn create(
        customer_id: CustomerId,
        items: Vec<OrderItem>,
    ) -> Result<Self, DomainError> {
        // 业务规则验证
        if items.is_empty() {
            return Err(DomainError::EmptyOrder);
        }
        
        let total_amount = Self::calculate_total(&items);
        
        if total_amount.amount() < 10.0 {
            return Err(DomainError::BelowMinimumAmount);
        }
        
        // 创建事件
        let event = OrderEvent::OrderCreated {
            order_id: OrderId::new(),
            customer_id,
            items: items.clone(),
            total_amount,
            created_at: Utc::now(),
        };
        
        // 应用事件
        let mut aggregate = Self::default();
        aggregate.apply(event.clone());
        aggregate.uncommitted_events.push(event);
        
        Ok(aggregate)
    }
    
    /// 取消订单 (Command)
    pub fn cancel(&mut self, reason: String) -> Result<(), DomainError> {
        // 业务规则
        match self.status {
            OrderStatus::Delivered => {
                return Err(DomainError::CannotCancelDeliveredOrder);
            }
            OrderStatus::Cancelled => {
                return Err(DomainError::AlreadyCancelled);
            }
            _ => {}
        }
        
        // 创建事件
        let event = OrderEvent::OrderCancelled {
            order_id: self.id,
            reason,
            cancelled_at: Utc::now(),
        };
        
        // 应用事件
        self.apply(event.clone());
        self.uncommitted_events.push(event);
        
        Ok(())
    }
    
    /// 应用事件 (修改聚合根状态)
    fn apply(&mut self, event: OrderEvent) {
        match event {
            OrderEvent::OrderCreated {
                order_id,
                customer_id,
                items,
                total_amount,
                created_at,
            } => {
                self.id = order_id;
                self.customer_id = customer_id;
                self.items = items;
                self.total_amount = total_amount;
                self.status = OrderStatus::Pending;
                self.created_at = created_at;
                self.version += 1;
            }
            OrderEvent::OrderCancelled { .. } => {
                self.status = OrderStatus::Cancelled;
                self.version += 1;
            }
            // ... 其他事件
        }
    }
    
    /// 从事件流重建聚合根 (Event Sourcing)
    pub fn from_events(events: Vec<OrderEvent>) -> Result<Self, DomainError> {
        let mut aggregate = Self::default();
        
        for event in events {
            aggregate.apply(event);
        }
        
        Ok(aggregate)
    }
    
    /// 获取未提交的事件
    pub fn uncommitted_events(&self) -> &[OrderEvent] {
        &self.uncommitted_events
    }
    
    /// 清空未提交的事件 (保存后调用)
    pub fn clear_uncommitted_events(&mut self) {
        self.uncommitted_events.clear();
    }
    
    fn calculate_total(items: &[OrderItem]) -> Money {
        items.iter()
            .map(|item| item.unit_price.multiply(item.quantity))
            .fold(Money::zero(), |acc, price| acc.add(&price))
    }
}

impl Default for OrderAggregate {
    fn default() -> Self {
        Self {
            id: OrderId::default(),
            customer_id: CustomerId::default(),
            items: Vec::new(),
            total_amount: Money::zero(),
            status: OrderStatus::Pending,
            created_at: Utc::now(),
            version: 0,
            uncommitted_events: Vec::new(),
        }
    }
}
```

#### 1.2 领域事件 (Domain Events)

```rust
// domain/events/order_event.rs
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 订单领域事件
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum OrderEvent {
    OrderCreated {
        order_id: OrderId,
        customer_id: CustomerId,
        items: Vec<OrderItem>,
        total_amount: Money,
        created_at: DateTime<Utc>,
    },
    OrderConfirmed {
        order_id: OrderId,
        confirmed_at: DateTime<Utc>,
    },
    OrderShipped {
        order_id: OrderId,
        tracking_number: String,
        shipped_at: DateTime<Utc>,
    },
    OrderDelivered {
        order_id: OrderId,
        delivered_at: DateTime<Utc>,
    },
    OrderCancelled {
        order_id: OrderId,
        reason: String,
        cancelled_at: DateTime<Utc>,
    },
}

impl OrderEvent {
    pub fn order_id(&self) -> OrderId {
        match self {
            Self::OrderCreated { order_id, .. } => *order_id,
            Self::OrderConfirmed { order_id, .. } => *order_id,
            Self::OrderShipped { order_id, .. } => *order_id,
            Self::OrderDelivered { order_id, .. } => *order_id,
            Self::OrderCancelled { order_id, .. } => *order_id,
        }
    }
    
    pub fn event_type(&self) -> &str {
        match self {
            Self::OrderCreated { .. } => "OrderCreated",
            Self::OrderConfirmed { .. } => "OrderConfirmed",
            Self::OrderShipped { .. } => "OrderShipped",
            Self::OrderDelivered { .. } => "OrderDelivered",
            Self::OrderCancelled { .. } => "OrderCancelled",
        }
    }
}
```

---

### 2. Write Side (Command 端)

#### 2.1 Command Handler

```rust
// write/handlers/create_order_handler.rs
use crate::domain::aggregates::OrderAggregate;
use crate::domain::commands::CreateOrderCommand;
use crate::write::repositories::OrderRepository;
use crate::infrastructure::event_bus::EventBus;
use std::sync::Arc;
use tracing::{instrument, info, error};

/// 创建订单命令处理器
/// 
/// Command Side: 完整业务逻辑追踪
pub struct CreateOrderHandler<R: OrderRepository, E: EventBus> {
    order_repo: Arc<R>,
    event_bus: Arc<E>,
}

impl<R: OrderRepository, E: EventBus> CreateOrderHandler<R, E> {
    pub fn new(order_repo: Arc<R>, event_bus: Arc<E>) -> Self {
        Self {
            order_repo,
            event_bus,
        }
    }
    
    #[instrument(
        name = "create_order_command_handler",
        skip(self, command),
        fields(
            command_type = "CreateOrder",
            customer_id = %command.customer_id,
            item_count = command.items.len(),
            otel.kind = "internal",
        )
    )]
    pub async fn handle(
        &self,
        command: CreateOrderCommand,
    ) -> Result<OrderId, CommandError> {
        info!("🛍️ Handling CreateOrder command");
        
        // Step 1: 创建聚合根 (业务规则验证)
        let mut aggregate = OrderAggregate::create(
            command.customer_id,
            command.items,
        )
        .map_err(|e| {
            error!(error = ?e, "❌ Business rule validation failed");
            CommandError::DomainError(e)
        })?;
        
        let order_id = aggregate.id();
        info!(order_id = %order_id, "✅ Order aggregate created");
        
        // Step 2: 持久化到事件存储 (Event Store)
        let events = aggregate.uncommitted_events().to_vec();
        
        self.order_repo
            .save_events(order_id, events.clone(), aggregate.version())
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to save events");
                CommandError::RepositoryError(e)
            })?;
        
        info!(
            order_id = %order_id,
            event_count = events.len(),
            "💾 Events saved to event store"
        );
        
        aggregate.clear_uncommitted_events();
        
        // Step 3: 发布事件到 Event Bus (Kafka)
        for event in events {
            self.event_bus
                .publish(event.clone())
                .await
                .map_err(|e| {
                    error!(error = ?e, "❌ Failed to publish event");
                    CommandError::EventBusError(e)
                })?;
            
            info!(
                event_type = event.event_type(),
                "📤 Event published to Kafka"
            );
        }
        
        info!(order_id = %order_id, "🎉 CreateOrder command completed");
        
        Ok(order_id)
    }
}
```

#### 2.2 Event Store (PostgreSQL)

```rust
// write/event_store/postgres_event_store.rs
use crate::domain::events::OrderEvent;
use crate::domain::value_objects::OrderId;
use sqlx::PgPool;
use tracing::{instrument, info, error};

/// PostgreSQL 事件存储
/// 
/// 表结构:
/// CREATE TABLE event_store (
///     id BIGSERIAL PRIMARY KEY,
///     aggregate_id UUID NOT NULL,
///     aggregate_type VARCHAR(255) NOT NULL,
///     event_type VARCHAR(255) NOT NULL,
///     event_data JSONB NOT NULL,
///     version BIGINT NOT NULL,
///     created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
///     UNIQUE(aggregate_id, version)
/// );
pub struct PostgresEventStore {
    pool: PgPool,
}

impl PostgresEventStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    #[instrument(
        name = "save_events_to_event_store",
        skip(self, events),
        fields(
            db.system = "postgresql",
            db.table = "event_store",
            aggregate_id = %aggregate_id,
            event_count = events.len(),
            version = version,
            otel.kind = "client",
        )
    )]
    pub async fn save_events(
        &self,
        aggregate_id: OrderId,
        events: Vec<OrderEvent>,
        version: u64,
    ) -> Result<(), EventStoreError> {
        info!("💾 Saving events to event store");
        
        // 开启事务
        let mut tx = self.pool.begin().await.map_err(|e| {
            error!(error = ?e, "❌ Failed to begin transaction");
            EventStoreError::DatabaseError(e.to_string())
        })?;
        
        for (i, event) in events.iter().enumerate() {
            let event_version = version - events.len() as u64 + i as u64 + 1;
            
            let event_data = serde_json::to_value(event).map_err(|e| {
                error!(error = ?e, "❌ Failed to serialize event");
                EventStoreError::SerializationError(e.to_string())
            })?;
            
            sqlx::query!(
                r#"
                INSERT INTO event_store (aggregate_id, aggregate_type, event_type, event_data, version)
                VALUES ($1, $2, $3, $4, $5)
                "#,
                aggregate_id.as_uuid(),
                "Order",
                event.event_type(),
                event_data,
                event_version as i64,
            )
            .execute(&mut *tx)
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to insert event");
                EventStoreError::DatabaseError(e.to_string())
            })?;
            
            info!(
                event_type = event.event_type(),
                version = event_version,
                "✅ Event saved"
            );
        }
        
        // 提交事务
        tx.commit().await.map_err(|e| {
            error!(error = ?e, "❌ Failed to commit transaction");
            EventStoreError::DatabaseError(e.to_string())
        })?;
        
        info!(
            aggregate_id = %aggregate_id,
            event_count = events.len(),
            "🎉 All events saved successfully"
        );
        
        Ok(())
    }
    
    #[instrument(
        name = "load_events_from_event_store",
        skip(self),
        fields(
            db.system = "postgresql",
            db.table = "event_store",
            aggregate_id = %aggregate_id,
            otel.kind = "client",
        )
    )]
    pub async fn load_events(
        &self,
        aggregate_id: OrderId,
    ) -> Result<Vec<OrderEvent>, EventStoreError> {
        info!(aggregate_id = %aggregate_id, "🔍 Loading events from event store");
        
        let rows = sqlx::query!(
            r#"
            SELECT event_data
            FROM event_store
            WHERE aggregate_id = $1
            ORDER BY version ASC
            "#,
            aggregate_id.as_uuid(),
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Failed to load events");
            EventStoreError::DatabaseError(e.to_string())
        })?;
        
        let mut events = Vec::new();
        
        for row in rows {
            let event: OrderEvent = serde_json::from_value(row.event_data).map_err(|e| {
                error!(error = ?e, "❌ Failed to deserialize event");
                EventStoreError::SerializationError(e.to_string())
            })?;
            
            events.push(event);
        }
        
        info!(
            aggregate_id = %aggregate_id,
            event_count = events.len(),
            "✅ Events loaded successfully"
        );
        
        Ok(events)
    }
}
```

---

### 3. Read Side (Query 端)

#### 3.1 Read Model

```rust
// read/models/order_read_model.rs
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 订单读模型
/// 
/// 特点:
/// 1. 反规范化 (所有数据扁平化)
/// 2. 优化查询 (无需 JOIN)
/// 3. 可以有多个读模型 (不同视图)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderReadModel {
    // 基本信息
    pub id: String,                      // Order ID
    pub customer_id: String,
    pub customer_name: String,           // ✅ 反规范化
    pub customer_email: String,          // ✅ 反规范化
    
    // 订单项信息
    pub item_names: Vec<String>,         // ✅ 反规范化
    pub item_quantities: Vec<u32>,       // ✅ 反规范化
    pub total_amount: f64,               // ✅ 预计算
    pub currency: String,
    
    // 状态信息
    pub status: String,
    pub tracking_number: Option<String>,
    
    // 时间信息
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub shipped_at: Option<DateTime<Utc>>,
    pub delivered_at: Option<DateTime<Utc>>,
    
    // 搜索优化字段
    pub search_text: String,             // ✅ 全文搜索字段
}

impl OrderReadModel {
    /// 从领域事件构建读模型
    pub fn from_created_event(
        event: &OrderCreatedEvent,
        customer_name: String,
        customer_email: String,
    ) -> Self {
        let item_names: Vec<String> = event.items.iter()
            .map(|item| item.product_name.clone())
            .collect();
        
        let item_quantities: Vec<u32> = event.items.iter()
            .map(|item| item.quantity)
            .collect();
        
        // 构建搜索文本 (用于全文搜索)
        let search_text = format!(
            "{} {} {} {}",
            event.order_id,
            customer_name,
            customer_email,
            item_names.join(" ")
        );
        
        Self {
            id: event.order_id.to_string(),
            customer_id: event.customer_id.to_string(),
            customer_name,
            customer_email,
            item_names,
            item_quantities,
            total_amount: event.total_amount.amount(),
            currency: event.total_amount.currency().to_string(),
            status: "Pending".to_string(),
            tracking_number: None,
            created_at: event.created_at,
            updated_at: event.created_at,
            shipped_at: None,
            delivered_at: None,
            search_text,
        }
    }
    
    /// 更新状态 (基于事件)
    pub fn apply_event(&mut self, event: &OrderEvent) {
        match event {
            OrderEvent::OrderShipped { tracking_number, shipped_at, .. } => {
                self.status = "Shipped".to_string();
                self.tracking_number = Some(tracking_number.clone());
                self.shipped_at = Some(*shipped_at);
                self.updated_at = *shipped_at;
            }
            OrderEvent::OrderDelivered { delivered_at, .. } => {
                self.status = "Delivered".to_string();
                self.delivered_at = Some(*delivered_at);
                self.updated_at = *delivered_at;
            }
            OrderEvent::OrderCancelled { cancelled_at, .. } => {
                self.status = "Cancelled".to_string();
                self.updated_at = *cancelled_at;
            }
            _ => {}
        }
    }
}
```

#### 3.2 Projection (投影)

```rust
// read/projections/order_projection.rs
use crate::domain::events::OrderEvent;
use crate::read::models::OrderReadModel;
use crate::read::repositories::OrderReadRepository;
use std::sync::Arc;
use tracing::{instrument, info, error, warn};

/// 订单投影
/// 
/// 负责:
/// 1. 监听事件 (从 Kafka 消费)
/// 2. 更新读模型 (写入 Elasticsearch)
pub struct OrderProjection<R: OrderReadRepository> {
    read_repo: Arc<R>,
    customer_service: Arc<dyn CustomerService>,  // 获取客户信息
}

impl<R: OrderReadRepository> OrderProjection<R> {
    pub fn new(
        read_repo: Arc<R>,
        customer_service: Arc<dyn CustomerService>,
    ) -> Self {
        Self {
            read_repo,
            customer_service,
        }
    }
    
    /// 处理订单事件 (更新读模型)
    #[instrument(
        name = "order_projection_handle_event",
        skip(self, event),
        fields(
            projection = "OrderProjection",
            event_type = event.event_type(),
            order_id = %event.order_id(),
            otel.kind = "internal",
        )
    )]
    pub async fn handle(&self, event: OrderEvent) -> Result<(), ProjectionError> {
        info!(
            event_type = event.event_type(),
            order_id = %event.order_id(),
            "📥 Handling event in projection"
        );
        
        match event {
            OrderEvent::OrderCreated {
                ref order_id,
                ref customer_id,
                ref items,
                ref total_amount,
                created_at,
            } => {
                // 获取客户信息 (可能需要调用其他服务)
                let customer = self.customer_service
                    .get_customer(*customer_id)
                    .await
                    .map_err(|e| {
                        error!(error = ?e, "❌ Failed to get customer info");
                        ProjectionError::CustomerServiceError(e)
                    })?;
                
                // 构建读模型
                let read_model = OrderReadModel::from_created_event(
                    &event,
                    customer.name,
                    customer.email,
                );
                
                // 保存到 Elasticsearch
                self.read_repo
                    .save(&read_model)
                    .await
                    .map_err(|e| {
                        error!(error = ?e, "❌ Failed to save read model");
                        ProjectionError::RepositoryError(e)
                    })?;
                
                info!(order_id = %order_id, "✅ Read model created");
            }
            
            _ => {
                // 其他事件: 更新已有读模型
                let order_id = event.order_id();
                
                let mut read_model = self.read_repo
                    .find_by_id(order_id)
                    .await
                    .map_err(|e| {
                        error!(error = ?e, "❌ Failed to find read model");
                        ProjectionError::RepositoryError(e)
                    })?
                    .ok_or_else(|| {
                        warn!(order_id = %order_id, "⚠️ Read model not found");
                        ProjectionError::ReadModelNotFound(order_id)
                    })?;
                
                // 应用事件
                read_model.apply_event(&event);
                
                // 更新 Elasticsearch
                self.read_repo
                    .update(&read_model)
                    .await
                    .map_err(|e| {
                        error!(error = ?e, "❌ Failed to update read model");
                        ProjectionError::RepositoryError(e)
                    })?;
                
                info!(order_id = %order_id, "✅ Read model updated");
            }
        }
        
        info!(
            event_type = event.event_type(),
            "🎉 Event handled successfully"
        );
        
        Ok(())
    }
}
```

#### 3.3 Elasticsearch Repository

```rust
// read/repositories/elasticsearch_order_read_repo.rs
use crate::read::models::OrderReadModel;
use elasticsearch::{Elasticsearch, IndexParts, SearchParts};
use serde_json::json;
use tracing::{instrument, info, error};

pub struct ElasticsearchOrderReadRepository {
    client: Elasticsearch,
    index: String,
}

impl ElasticsearchOrderReadRepository {
    pub fn new(client: Elasticsearch, index: String) -> Self {
        Self { client, index }
    }
    
    #[instrument(
        name = "elasticsearch_save_order",
        skip(self, order),
        fields(
            db.system = "elasticsearch",
            db.operation = "INDEX",
            db.index = %self.index,
            order_id = %order.id,
            otel.kind = "client",
        )
    )]
    pub async fn save(&self, order: &OrderReadModel) -> Result<(), ReadRepoError> {
        info!(order_id = %order.id, "📝 Indexing order to Elasticsearch");
        
        let response = self.client
            .index(IndexParts::IndexId(&self.index, &order.id))
            .body(order)
            .send()
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to index document");
                ReadRepoError::ElasticsearchError(e.to_string())
            })?;
        
        if !response.status_code().is_success() {
            error!(status = response.status_code().as_u16(), "❌ Indexing failed");
            return Err(ReadRepoError::ElasticsearchError(
                format!("Status code: {}", response.status_code())
            ));
        }
        
        info!(order_id = %order.id, "✅ Order indexed successfully");
        Ok(())
    }
    
    #[instrument(
        name = "elasticsearch_search_orders",
        skip(self),
        fields(
            db.system = "elasticsearch",
            db.operation = "SEARCH",
            db.index = %self.index,
            customer_id = %customer_id,
            otel.kind = "client",
        )
    )]
    pub async fn find_by_customer_id(
        &self,
        customer_id: CustomerId,
    ) -> Result<Vec<OrderReadModel>, ReadRepoError> {
        info!(customer_id = %customer_id, "🔍 Searching orders in Elasticsearch");
        
        let response = self.client
            .search(SearchParts::Index(&[&self.index]))
            .body(json!({
                "query": {
                    "term": {
                        "customer_id": customer_id.to_string()
                    }
                },
                "sort": [
                    { "created_at": "desc" }
                ],
                "size": 100
            }))
            .send()
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Search failed");
                ReadRepoError::ElasticsearchError(e.to_string())
            })?;
        
        let json = response.json::<serde_json::Value>().await.map_err(|e| {
            error!(error = ?e, "❌ Failed to parse response");
            ReadRepoError::ElasticsearchError(e.to_string())
        })?;
        
        let hits = json["hits"]["hits"].as_array()
            .ok_or_else(|| ReadRepoError::ElasticsearchError("Invalid response".to_string()))?;
        
        let orders: Vec<OrderReadModel> = hits.iter()
            .filter_map(|hit| {
                serde_json::from_value(hit["_source"].clone()).ok()
            })
            .collect();
        
        info!(
            customer_id = %customer_id,
            order_count = orders.len(),
            "✅ Found {} orders",
            orders.len()
        );
        
        Ok(orders)
    }
}
```

#### 3.4 Query Handler

```rust
// read/handlers/list_orders_handler.rs
use crate::read::models::OrderReadModel;
use crate::read::repositories::OrderReadRepository;
use std::sync::Arc;
use tracing::{instrument, info};

pub struct ListOrdersHandler<R: OrderReadRepository> {
    read_repo: Arc<R>,
}

impl<R: OrderReadRepository> ListOrdersHandler<R> {
    pub fn new(read_repo: Arc<R>) -> Self {
        Self { read_repo }
    }
    
    #[instrument(
        name = "list_orders_query_handler",
        skip(self),
        fields(
            query_type = "ListOrdersByCustomer",
            customer_id = %customer_id,
            otel.kind = "internal",
        )
    )]
    pub async fn handle(
        &self,
        customer_id: CustomerId,
    ) -> Result<Vec<OrderReadModel>, QueryError> {
        info!(customer_id = %customer_id, "🔍 Handling ListOrders query");
        
        let orders = self.read_repo
            .find_by_customer_id(customer_id)
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Query failed");
                QueryError::RepositoryError(e)
            })?;
        
        info!(
            customer_id = %customer_id,
            order_count = orders.len(),
            "✅ Query completed"
        );
        
        Ok(orders)
    }
}
```

---

## ⏱️ 最终一致性处理

### 问题: 读模型可能滞后

```text
时间线:
T1: Command → 写入 PostgreSQL ✅
T2: Event → 发送到 Kafka ✅
T3: (网络延迟...)
T4: Projection → 更新 Elasticsearch ✅
T5: Query → 读取 Elasticsearch (可能读到旧数据)
```

### 解决方案

#### 方案 1: 版本号 + 重试

```rust
pub async fn get_order_with_retry(
    &self,
    order_id: OrderId,
    expected_version: u64,
    max_retries: u32,
) -> Result<OrderReadModel> {
    for attempt in 0..max_retries {
        if let Some(order) = self.read_repo.find_by_id(order_id).await? {
            if order.version >= expected_version {
                return Ok(order);
            }
        }
        
        // 等待投影更新
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    Err(QueryError::EventualConsistencyTimeout)
}
```

#### 方案 2: Command 返回完整结果

```rust
// Command 返回足够信息,避免立即查询
pub struct CreateOrderResponse {
    pub order_id: OrderId,
    pub status: String,
    pub total_amount: Money,
    pub estimated_delivery: DateTime<Utc>,  // ✅ 包含关键信息
}
```

---

## 🚀 性能优化

### 1. 读模型缓存

```rust
use redis::AsyncCommands;

pub struct CachedOrderReadRepository<R: OrderReadRepository> {
    inner: Arc<R>,
    redis: redis::Client,
    ttl: usize,  // 缓存时间 (秒)
}

impl<R: OrderReadRepository> CachedOrderReadRepository<R> {
    pub async fn find_by_id(&self, id: OrderId) -> Result<Option<OrderReadModel>> {
        let cache_key = format!("order:read:{}", id);
        
        // 1. 尝试从缓存读取
        let mut conn = self.redis.get_async_connection().await?;
        
        if let Some(cached): Option<String> = conn.get(&cache_key).await.ok() {
            info!(order_id = %id, "✅ Cache HIT");
            return Ok(Some(serde_json::from_str(&cached)?));
        }
        
        info!(order_id = %id, "⚠️ Cache MISS");
        
        // 2. 从 Elasticsearch 读取
        let order = self.inner.find_by_id(id).await?;
        
        // 3. 写入缓存
        if let Some(ref o) = order {
            let json = serde_json::to_string(o)?;
            let _: () = conn.set_ex(&cache_key, json, self.ttl).await?;
            info!(order_id = %id, ttl = self.ttl, "💾 Cached");
        }
        
        Ok(order)
    }
}
```

---

## 📦 生产部署

### Cargo.toml

```toml
[package]
name = "cqrs-order-service"
version = "1.0.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Async runtime
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web framework
axum = { version = "0.7", features = ["macros"] }

# Database (Write Side)
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "macros"] }

# Elasticsearch (Read Side)
elasticsearch = "8.15"

# Kafka (Event Bus)
rdkafka = { version = "0.36", features = ["tokio"] }

# Redis (Cache)
redis = { version = "0.27", features = ["tokio-comp", "connection-manager"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Error handling
anyhow = "1.0"
thiserror = "2.0"

# UUID & Time
uuid = { version = "1.11", features = ["serde", "v4"] }
chrono = { version = "0.4", features = ["serde"] }

# Tracing & OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-otlp = "0.16"
```

---

### Docker Compose

```yaml
version: '3.9'

services:
  # Command Side - PostgreSQL
  postgres:
    image: postgres:16-alpine
    environment:
      POSTGRES_PASSWORD: password
      POSTGRES_DB: orders_write
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  # Query Side - Elasticsearch
  elasticsearch:
    image: elasticsearch:8.15.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    ports:
      - "9200:9200"
    volumes:
      - es_data:/usr/share/elasticsearch/data

  # Event Bus - Kafka
  zookeeper:
    image: confluentinc/cp-zookeeper:7.7.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181

  kafka:
    image: confluentinc/cp-kafka:7.7.0
    depends_on:
      - zookeeper
    ports:
      - "9092:9092"
    environment:
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://kafka:9092
      KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR: 1

  # Cache - Redis
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  # CQRS Order Service
  order-service:
    build: .
    ports:
      - "8080:8080"
    environment:
      - WRITE_DB_URL=postgres://postgres:password@postgres:5432/orders_write
      - READ_ES_URL=http://elasticsearch:9200
      - KAFKA_BROKERS=kafka:9092
      - REDIS_URL=redis://redis:6379
      - OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - elasticsearch
      - kafka
      - redis
      - otel-collector

  # OTLP Collector
  otel-collector:
    image: otel/opentelemetry-collector:0.111.0
    command: ["--config=/etc/otel-config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel-config.yaml
    ports:
      - "4317:4317"

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"
    environment:
      - COLLECTOR_OTLP_ENABLED=true

volumes:
  postgres_data:
  es_data:
```

---

## ✅ 最佳实践

### CQRS 设计

- [x] **严格分离**: Command 和 Query 完全独立
- [x] **不同数据库**: 写用 PostgreSQL, 读用 Elasticsearch
- [x] **事件驱动**: 通过事件同步读写模型
- [x] **最终一致性**: 接受读模型可能滞后
- [x] **Event Sourcing**: 结合事件溯源存储完整历史

### OTLP 集成

- [x] **Command Side**: 完整业务逻辑追踪
- [x] **Event Bus**: 追踪上下文通过 Kafka 传播
- [x] **Projection**: 投影处理追踪
- [x] **Query Side**: 查询性能追踪
- [x] **关联分析**: Command → Event → Projection → Query 完整链路

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

---

**📊 CQRS 架构 - 构建高性能、可扩展的读写分离系统！**
