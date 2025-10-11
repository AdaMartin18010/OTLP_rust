# 六边形架构 (Hexagonal Architecture) - Rust OTLP 完整实现

> **架构模式**: Hexagonal Architecture (又称 Ports & Adapters)  
> **提出者**: Alistair Cockburn (2005)  
> **国际标准**: DDD (Domain-Driven Design) 社区标准  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **更新日期**: 2025年10月11日

---

## 📋 目录

- [六边形架构 (Hexagonal Architecture) - Rust OTLP 完整实现](#六边形架构-hexagonal-architecture---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [🏛️ 架构概述](#️-架构概述)
    - [什么是六边形架构?](#什么是六边形架构)
      - [核心思想](#核心思想)
      - [国际标准对标](#国际标准对标)
  - [🎯 核心概念](#-核心概念)
    - [1. 端口 (Ports)](#1-端口-ports)
      - [入站端口 (Inbound Ports)](#入站端口-inbound-ports)
      - [出站端口 (Outbound Ports)](#出站端口-outbound-ports)
    - [2. 适配器 (Adapters)](#2-适配器-adapters)
      - [入站适配器 (Inbound Adapters)](#入站适配器-inbound-adapters)
      - [出站适配器 (Outbound Adapters)](#出站适配器-outbound-adapters)
    - [3. 核心领域 (Domain Core)](#3-核心领域-domain-core)
  - [🦀 Rust 实现设计](#-rust-实现设计)
    - [项目结构](#项目结构)
  - [🔭 OTLP 集成策略](#-otlp-集成策略)
    - [策略 1: 核心领域层 - 零侵入](#策略-1-核心领域层---零侵入)
    - [策略 2: 应用层 - OTLP 集成点](#策略-2-应用层---otlp-集成点)
    - [策略 3: 基础设施层 - 完整插桩](#策略-3-基础设施层---完整插桩)
      - [3.1 Web 适配器 (Axum)](#31-web-适配器-axum)
      - [3.2 数据库适配器 (SQLx)](#32-数据库适配器-sqlx)
  - [🛒 完整电商示例](#-完整电商示例)
    - [1. 核心领域层 (Domain Core)](#1-核心领域层-domain-core)
      - [1.1 实体 (Entity)](#11-实体-entity)
      - [1.2 值对象 (Value Objects)](#12-值对象-value-objects)
      - [1.3 仓储接口 (Repository Port)](#13-仓储接口-repository-port)
    - [2. 应用层 (Application Layer)](#2-应用层-application-layer)
      - [2.1 用例实现 (Use Case)](#21-用例实现-use-case)
    - [3. 基础设施层 (Infrastructure Layer)](#3-基础设施层-infrastructure-layer)
      - [3.1 Web 适配器 (Axum HTTP Handler)](#31-web-适配器-axum-http-handler)
      - [3.2 数据库适配器 (PostgreSQL)](#32-数据库适配器-postgresql)
    - [4. OTLP 初始化 (Telemetry Setup)](#4-otlp-初始化-telemetry-setup)
    - [5. 主程序入口](#5-主程序入口)
  - [🧪 测试策略](#-测试策略)
    - [1. 单元测试 (Mock Adapters)](#1-单元测试-mock-adapters)
    - [2. 集成测试 (Testcontainers)](#2-集成测试-testcontainers)
  - [⚡ 性能优化](#-性能优化)
    - [1. 连接池配置](#1-连接池配置)
    - [2. 缓存层](#2-缓存层)
  - [🚀 生产部署](#-生产部署)
    - [Cargo.toml (完整依赖)](#cargotoml-完整依赖)
    - [Docker Compose 部署](#docker-compose-部署)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [1. 追踪数据未上报](#1-追踪数据未上报)
      - [2. 数据库连接池耗尽](#2-数据库连接池耗尽)
  - [✅ 最佳实践清单](#-最佳实践清单)
    - [架构设计](#架构设计)
    - [OTLP 集成](#otlp-集成)
    - [Rust 特性](#rust-特性)
  - [📚 参考资源](#-参考资源)
    - [国际标准](#国际标准)
    - [Rust 生态](#rust-生态)
    - [示例代码](#示例代码)
  - [🎉 总结](#-总结)

---

## 🏛️ 架构概述

### 什么是六边形架构?

**六边形架构** (Hexagonal Architecture) 是一种软件架构模式,强调**业务逻辑与外部依赖的解耦**。

#### 核心思想

```text
                外部系统 (Adapters)
                       ↓
        ┌──────────────────────────────┐
        │      🔌 入站端口 (Ports)     │
        │    (接口/Trait 定义)          │
        ├──────────────────────────────┤
        │                              │
        │   🏢 核心领域 (Domain Core)  │
        │   - 业务实体 (Entities)       │
        │   - 值对象 (Value Objects)    │
        │   - 业务规则 (Business Rules) │
        │   - 无外部依赖                │
        │                              │
        ├──────────────────────────────┤
        │     🔌 出站端口 (Ports)       │
        │    (接口/Trait 定义)          │
        └──────────────────────────────┘
                       ↑
                外部系统 (Adapters)
```

#### 国际标准对标

| 标准/框架 | 描述 | 对标 |
|----------|------|------|
| **DDD (Domain-Driven Design)** | Eric Evans, 2003 | ✅ 核心领域建模 |
| **Clean Architecture** | Robert C. Martin, 2012 | ✅ 依赖倒置原则 |
| **Onion Architecture** | Jeffrey Palermo, 2008 | ✅ 分层思想 |
| **SOLID 原则** | Robert C. Martin | ✅ 接口隔离、依赖倒置 |

---

## 🎯 核心概念

### 1. 端口 (Ports)

**定义**: Rust 的 **Trait** 定义,描述核心领域与外部世界的交互契约。

#### 入站端口 (Inbound Ports)

外部世界调用核心领域的接口。

```rust
/// 订单管理用例 (应用服务层)
#[async_trait]
pub trait OrderUseCasePort: Send + Sync {
    async fn create_order(&self, request: CreateOrderRequest) -> Result<Order>;
    async fn get_order(&self, order_id: OrderId) -> Result<Order>;
    async fn cancel_order(&self, order_id: OrderId) -> Result<()>;
}
```

#### 出站端口 (Outbound Ports)

核心领域调用外部系统的接口。

```rust
/// 订单仓储接口 (领域层定义)
#[async_trait]
pub trait OrderRepositoryPort: Send + Sync {
    async fn save(&self, order: &Order) -> Result<()>;
    async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>>;
    async fn delete(&self, id: OrderId) -> Result<()>;
}

/// 支付网关接口
#[async_trait]
pub trait PaymentGatewayPort: Send + Sync {
    async fn charge(&self, amount: Money, card: CreditCard) -> Result<PaymentId>;
    async fn refund(&self, payment_id: PaymentId) -> Result<()>;
}
```

---

### 2. 适配器 (Adapters)

**定义**: 端口的具体实现,连接核心领域与外部技术栈。

#### 入站适配器 (Inbound Adapters)

- **Web API**: Axum HTTP 控制器
- **CLI**: 命令行界面
- **消息队列消费者**: Kafka Consumer

#### 出站适配器 (Outbound Adapters)

- **数据库**: PostgreSQL (SQLx)
- **缓存**: Redis
- **外部 API**: Stripe 支付

---

### 3. 核心领域 (Domain Core)

**无外部依赖的纯 Rust 代码**,包含:

1. **实体 (Entities)**: 有唯一标识的业务对象
2. **值对象 (Value Objects)**: 无标识的不可变对象
3. **领域服务 (Domain Services)**: 业务逻辑
4. **领域事件 (Domain Events)**: 业务事件

---

## 🦀 Rust 实现设计

### 项目结构

```text
order-service/
├── Cargo.toml
├── src/
│   ├── main.rs                          # 应用启动入口
│   │
│   ├── domain/                          # 🏢 核心领域层 (无外部依赖)
│   │   ├── mod.rs
│   │   ├── entities/
│   │   │   ├── mod.rs
│   │   │   ├── order.rs                 # 订单实体
│   │   │   └── customer.rs              # 客户实体
│   │   ├── value_objects/
│   │   │   ├── mod.rs
│   │   │   ├── order_id.rs
│   │   │   ├── money.rs
│   │   │   └── email.rs
│   │   ├── repositories/                # 🔌 出站端口 (Trait 定义)
│   │   │   ├── mod.rs
│   │   │   └── order_repository.rs
│   │   ├── services/                    # 领域服务
│   │   │   ├── mod.rs
│   │   │   └── order_service.rs
│   │   └── events/
│   │       ├── mod.rs
│   │       └── order_events.rs
│   │
│   ├── application/                     # 🎯 应用层 (OTLP 集成点)
│   │   ├── mod.rs
│   │   ├── ports/                       # 🔌 入站端口 (Trait 定义)
│   │   │   ├── mod.rs
│   │   │   └── order_use_case_port.rs
│   │   ├── use_cases/                   # 用例实现 (业务编排)
│   │   │   ├── mod.rs
│   │   │   ├── create_order_use_case.rs
│   │   │   └── cancel_order_use_case.rs
│   │   └── dto/                         # 数据传输对象
│   │       ├── mod.rs
│   │       └── order_dto.rs
│   │
│   ├── infrastructure/                  # 🔧 基础设施层 (完整插桩)
│   │   ├── mod.rs
│   │   ├── web/                         # 入站适配器: Axum Web
│   │   │   ├── mod.rs
│   │   │   ├── server.rs
│   │   │   ├── handlers/
│   │   │   │   ├── mod.rs
│   │   │   │   └── order_handler.rs
│   │   │   └── middleware/
│   │   │       ├── mod.rs
│   │   │       └── telemetry.rs         # OTLP 中间件
│   │   ├── persistence/                 # 出站适配器: 数据库
│   │   │   ├── mod.rs
│   │   │   ├── postgres_order_repository.rs
│   │   │   └── migrations/
│   │   ├── cache/                       # 出站适配器: 缓存
│   │   │   ├── mod.rs
│   │   │   └── redis_cache.rs
│   │   ├── messaging/                   # 出站适配器: 消息队列
│   │   │   ├── mod.rs
│   │   │   └── kafka_producer.rs
│   │   └── telemetry/                   # 🔭 OTLP 配置
│   │       ├── mod.rs
│   │       ├── init.rs
│   │       └── tracing.rs
│   │
│   └── config/                          # 配置管理
│       ├── mod.rs
│       └── app_config.rs
│
└── tests/
    ├── integration/
    │   └── order_api_test.rs
    └── unit/
        └── order_service_test.rs
```

---

## 🔭 OTLP 集成策略

### 策略 1: 核心领域层 - 零侵入

**原则**: 核心领域层**绝不**依赖 OTLP。

```rust
// ❌ 错误示例 - 领域层不应依赖 tracing
pub struct Order {
    id: OrderId,
    // ...
}

impl Order {
    pub fn create(customer_id: CustomerId, items: Vec<OrderItem>) -> Result<Self> {
        // ❌ 不要在领域层使用 tracing
        tracing::info!("Creating order");  // 错误!
        
        // ✅ 纯业务逻辑
        Self::validate_items(&items)?;
        Ok(Self {
            id: OrderId::new(),
            customer_id,
            items,
            status: OrderStatus::Pending,
            created_at: Utc::now(),
        })
    }
}
```

**正确方式**: 领域层只定义事件,由外层记录。

```rust
// ✅ 正确示例 - 领域层定义事件
pub enum OrderEvent {
    OrderCreated { order_id: OrderId, customer_id: CustomerId },
    OrderCancelled { order_id: OrderId, reason: String },
}

impl Order {
    pub fn create(customer_id: CustomerId, items: Vec<OrderItem>) -> Result<(Self, OrderEvent)> {
        Self::validate_items(&items)?;
        
        let order = Self {
            id: OrderId::new(),
            customer_id,
            items,
            status: OrderStatus::Pending,
            created_at: Utc::now(),
        };
        
        let event = OrderEvent::OrderCreated {
            order_id: order.id,
            customer_id,
        };
        
        Ok((order, event))
    }
}
```

---

### 策略 2: 应用层 - OTLP 集成点

**原则**: 在用例 (Use Case) 层集成 OTLP。

```rust
use opentelemetry::trace::{Span, Tracer};
use tracing::{instrument, info, error};

pub struct CreateOrderUseCase<R: OrderRepositoryPort, P: PaymentGatewayPort> {
    order_repo: Arc<R>,
    payment_gateway: Arc<P>,
}

impl<R, P> CreateOrderUseCase<R, P>
where
    R: OrderRepositoryPort,
    P: PaymentGatewayPort,
{
    #[instrument(
        name = "create_order_use_case",
        skip(self, request),
        fields(
            customer_id = %request.customer_id,
            item_count = request.items.len(),
            total_amount = %request.total_amount()
        )
    )]
    pub async fn execute(&self, request: CreateOrderRequest) -> Result<Order> {
        info!("Executing create order use case");
        
        // 1. 创建订单 (领域层,纯业务逻辑)
        let (order, event) = Order::create(
            request.customer_id,
            request.items,
        )?;
        
        // 2. 记录领域事件
        info!(
            order_id = %order.id(),
            event = ?event,
            "Domain event generated"
        );
        
        // 3. 持久化订单 (出站端口)
        self.order_repo.save(&order).await.map_err(|e| {
            error!(error = ?e, "Failed to save order");
            e
        })?;
        
        // 4. 处理支付 (出站端口)
        let payment_id = self.payment_gateway
            .charge(order.total_amount(), request.payment_method)
            .await
            .map_err(|e| {
                error!(error = ?e, "Payment failed");
                e
            })?;
        
        info!(
            order_id = %order.id(),
            payment_id = %payment_id,
            "Order created successfully"
        );
        
        Ok(order)
    }
}

#[async_trait]
impl<R, P> OrderUseCasePort for CreateOrderUseCase<R, P>
where
    R: OrderRepositoryPort + 'static,
    P: PaymentGatewayPort + 'static,
{
    async fn create_order(&self, request: CreateOrderRequest) -> Result<Order> {
        self.execute(request).await
    }
    
    // ... 其他方法
}
```

---

### 策略 3: 基础设施层 - 完整插桩

#### 3.1 Web 适配器 (Axum)

```rust
use axum::{
    extract::State,
    Json,
    http::StatusCode,
    response::IntoResponse,
};
use tracing::instrument;

pub struct OrderHandler<U: OrderUseCasePort> {
    use_case: Arc<U>,
}

impl<U: OrderUseCasePort> OrderHandler<U> {
    #[instrument(
        name = "http_create_order",
        skip(self, payload),
        fields(
            http.method = "POST",
            http.route = "/api/orders",
            http.status_code = tracing::field::Empty,
        )
    )]
    pub async fn create_order(
        &self,
        Json(payload): Json<CreateOrderRequestDto>,
    ) -> impl IntoResponse {
        let request = payload.into_domain();
        
        match self.use_case.create_order(request).await {
            Ok(order) => {
                tracing::Span::current().record("http.status_code", 201);
                (StatusCode::CREATED, Json(OrderDto::from(order)))
            }
            Err(e) => {
                error!(error = ?e, "Failed to create order");
                tracing::Span::current().record("http.status_code", 500);
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(ErrorResponse::from(e)),
                )
            }
        }
    }
}
```

#### 3.2 数据库适配器 (SQLx)

```rust
use sqlx::{PgPool, Postgres};
use tracing::instrument;

pub struct PostgresOrderRepository {
    pool: PgPool,
}

#[async_trait]
impl OrderRepositoryPort for PostgresOrderRepository {
    #[instrument(
        name = "postgres_save_order",
        skip(self, order),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.table = "orders",
            order_id = %order.id(),
        )
    )]
    async fn save(&self, order: &Order) -> Result<()> {
        let query = sqlx::query!(
            r#"
            INSERT INTO orders (id, customer_id, total_amount, status, created_at)
            VALUES ($1, $2, $3, $4, $5)
            "#,
            order.id().as_uuid(),
            order.customer_id().as_uuid(),
            order.total_amount().amount(),
            order.status().to_string(),
            order.created_at(),
        );
        
        query.execute(&self.pool).await.map_err(|e| {
            error!(error = ?e, "Database error");
            AppError::DatabaseError(e.to_string())
        })?;
        
        info!("Order saved to database");
        Ok(())
    }
    
    #[instrument(
        name = "postgres_find_order",
        skip(self),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.table = "orders",
            order_id = %id,
        )
    )]
    async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>> {
        let row = sqlx::query!(
            r#"
            SELECT id, customer_id, total_amount, status, created_at
            FROM orders
            WHERE id = $1
            "#,
            id.as_uuid(),
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "Database query failed");
            AppError::DatabaseError(e.to_string())
        })?;
        
        match row {
            Some(r) => {
                info!("Order found");
                Ok(Some(Order::from_row(r)?))
            }
            None => {
                info!("Order not found");
                Ok(None)
            }
        }
    }
}
```

---

## 🛒 完整电商示例

### 1. 核心领域层 (Domain Core)

#### 1.1 实体 (Entity)

```rust
// domain/entities/order.rs
use crate::domain::value_objects::{OrderId, CustomerId, Money, OrderStatus};
use crate::domain::events::OrderEvent;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    total_amount: Money,
    status: OrderStatus,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    product_id: ProductId,
    quantity: u32,
    unit_price: Money,
}

impl Order {
    /// 创建订单 (纯业务逻辑,无副作用)
    pub fn create(
        customer_id: CustomerId,
        items: Vec<OrderItem>,
    ) -> Result<(Self, OrderEvent), DomainError> {
        // 业务规则验证
        if items.is_empty() {
            return Err(DomainError::EmptyOrder);
        }
        
        if items.len() > 100 {
            return Err(DomainError::TooManyItems);
        }
        
        // 计算总金额
        let total_amount = items.iter()
            .map(|item| item.unit_price.multiply(item.quantity))
            .fold(Money::zero(), |acc, price| acc.add(&price));
        
        // 业务规则: 最小订单金额
        if total_amount.amount() < 10.0 {
            return Err(DomainError::BelowMinimumAmount);
        }
        
        let now = Utc::now();
        let order = Self {
            id: OrderId::new(),
            customer_id,
            items,
            total_amount,
            status: OrderStatus::Pending,
            created_at: now,
            updated_at: now,
        };
        
        let event = OrderEvent::OrderCreated {
            order_id: order.id,
            customer_id: order.customer_id,
            total_amount: order.total_amount,
            item_count: order.items.len(),
            created_at: order.created_at,
        };
        
        Ok((order, event))
    }
    
    /// 取消订单
    pub fn cancel(mut self, reason: String) -> Result<(Self, OrderEvent), DomainError> {
        // 业务规则: 只能取消待处理的订单
        match self.status {
            OrderStatus::Pending | OrderStatus::Confirmed => {
                self.status = OrderStatus::Cancelled;
                self.updated_at = Utc::now();
                
                let event = OrderEvent::OrderCancelled {
                    order_id: self.id,
                    reason,
                    cancelled_at: self.updated_at,
                };
                
                Ok((self, event))
            }
            _ => Err(DomainError::CannotCancelOrder(self.status)),
        }
    }
    
    /// 确认订单
    pub fn confirm(mut self) -> Result<(Self, OrderEvent), DomainError> {
        if self.status != OrderStatus::Pending {
            return Err(DomainError::InvalidStatusTransition {
                from: self.status,
                to: OrderStatus::Confirmed,
            });
        }
        
        self.status = OrderStatus::Confirmed;
        self.updated_at = Utc::now();
        
        let event = OrderEvent::OrderConfirmed {
            order_id: self.id,
            confirmed_at: self.updated_at,
        };
        
        Ok((self, event))
    }
    
    // Getters (无 setter,保持不可变性)
    pub fn id(&self) -> OrderId { self.id }
    pub fn customer_id(&self) -> CustomerId { self.customer_id }
    pub fn total_amount(&self) -> &Money { &self.total_amount }
    pub fn status(&self) -> OrderStatus { self.status }
    pub fn created_at(&self) -> DateTime<Utc> { self.created_at }
}

#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("Order must contain at least one item")]
    EmptyOrder,
    
    #[error("Order cannot contain more than 100 items")]
    TooManyItems,
    
    #[error("Order amount must be at least $10.00")]
    BelowMinimumAmount,
    
    #[error("Cannot cancel order in status: {0}")]
    CannotCancelOrder(OrderStatus),
    
    #[error("Invalid status transition from {from} to {to}")]
    InvalidStatusTransition {
        from: OrderStatus,
        to: OrderStatus,
    },
}
```

#### 1.2 值对象 (Value Objects)

```rust
// domain/value_objects/order_id.rs
use uuid::Uuid;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OrderId(Uuid);

impl OrderId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
    
    pub fn from_uuid(uuid: Uuid) -> Self {
        Self(uuid)
    }
    
    pub fn as_uuid(&self) -> &Uuid {
        &self.0
    }
}

impl Default for OrderId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for OrderId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// domain/value_objects/money.rs
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Money {
    amount: f64,
    currency: Currency,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Currency {
    USD,
    EUR,
    GBP,
    JPY,
    CNY,
}

impl Money {
    pub fn new(amount: f64, currency: Currency) -> Result<Self, DomainError> {
        if amount < 0.0 {
            return Err(DomainError::NegativeAmount);
        }
        Ok(Self { amount, currency })
    }
    
    pub fn zero() -> Self {
        Self { amount: 0.0, currency: Currency::USD }
    }
    
    pub fn amount(&self) -> f64 {
        self.amount
    }
    
    pub fn currency(&self) -> Currency {
        self.currency
    }
    
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.currency, other.currency, "Currency mismatch");
        Self {
            amount: self.amount + other.amount,
            currency: self.currency,
        }
    }
    
    pub fn multiply(&self, factor: u32) -> Self {
        Self {
            amount: self.amount * factor as f64,
            currency: self.currency,
        }
    }
}

impl fmt::Display for Money {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.2} {:?}", self.amount, self.currency)
    }
}

// domain/value_objects/order_status.rs
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
}

impl fmt::Display for OrderStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pending => write!(f, "pending"),
            Self::Confirmed => write!(f, "confirmed"),
            Self::Processing => write!(f, "processing"),
            Self::Shipped => write!(f, "shipped"),
            Self::Delivered => write!(f, "delivered"),
            Self::Cancelled => write!(f, "cancelled"),
        }
    }
}
```

#### 1.3 仓储接口 (Repository Port)

```rust
// domain/repositories/order_repository.rs
use crate::domain::entities::Order;
use crate::domain::value_objects::OrderId;
use async_trait::async_trait;

/// 订单仓储接口 (出站端口)
/// 
/// 这是一个纯 Trait 定义,在领域层定义,在基础设施层实现。
/// 遵循依赖倒置原则 (DIP): 高层模块不依赖低层模块,双方都依赖抽象。
#[async_trait]
pub trait OrderRepositoryPort: Send + Sync {
    /// 保存订单
    async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
    
    /// 根据 ID 查找订单
    async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, RepositoryError>;
    
    /// 根据客户 ID 查找订单
    async fn find_by_customer_id(
        &self,
        customer_id: CustomerId,
    ) -> Result<Vec<Order>, RepositoryError>;
    
    /// 删除订单
    async fn delete(&self, id: OrderId) -> Result<(), RepositoryError>;
}

#[derive(Debug, thiserror::Error)]
pub enum RepositoryError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Order not found: {0}")]
    NotFound(OrderId),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

---

### 2. 应用层 (Application Layer)

#### 2.1 用例实现 (Use Case)

```rust
// application/use_cases/create_order_use_case.rs
use crate::application::ports::OrderUseCasePort;
use crate::application::dto::{CreateOrderRequest, OrderDto};
use crate::domain::entities::Order;
use crate::domain::repositories::OrderRepositoryPort;
use crate::domain::services::PaymentGatewayPort;
use std::sync::Arc;
use tracing::{instrument, info, error, warn};
use opentelemetry::trace::Tracer;

pub struct CreateOrderUseCase<R, P>
where
    R: OrderRepositoryPort,
    P: PaymentGatewayPort,
{
    order_repo: Arc<R>,
    payment_gateway: Arc<P>,
}

impl<R, P> CreateOrderUseCase<R, P>
where
    R: OrderRepositoryPort,
    P: PaymentGatewayPort,
{
    pub fn new(order_repo: Arc<R>, payment_gateway: Arc<P>) -> Self {
        Self {
            order_repo,
            payment_gateway,
        }
    }
    
    /// 执行创建订单用例
    /// 
    /// OTLP 集成点: 在这一层添加分布式追踪
    #[instrument(
        name = "create_order_use_case",
        skip(self, request),
        fields(
            use_case = "create_order",
            customer_id = %request.customer_id,
            item_count = request.items.len(),
            total_amount = %request.total_amount(),
            otel.kind = "internal",
        )
    )]
    pub async fn execute(&self, request: CreateOrderRequest) -> Result<OrderDto, AppError> {
        info!("🛒 Executing create order use case");
        
        // Step 1: 创建订单 (领域层,纯业务逻辑)
        let (order, event) = Order::create(
            request.customer_id,
            request.into_items(),
        )
        .map_err(|e| {
            error!(error = ?e, "❌ Domain validation failed");
            AppError::DomainError(e)
        })?;
        
        info!(
            order_id = %order.id(),
            event = ?event,
            "✅ Order domain object created"
        );
        
        // Step 2: 处理支付 (出站端口)
        let payment_id = self.payment_gateway
            .charge(order.total_amount(), request.payment_method)
            .await
            .map_err(|e| {
                error!(
                    error = ?e,
                    order_id = %order.id(),
                    "❌ Payment failed"
                );
                AppError::PaymentError(e)
            })?;
        
        info!(
            order_id = %order.id(),
            payment_id = %payment_id,
            "💳 Payment processed successfully"
        );
        
        // Step 3: 持久化订单 (出站端口)
        self.order_repo.save(&order).await.map_err(|e| {
            error!(
                error = ?e,
                order_id = %order.id(),
                "❌ Failed to save order"
            );
            
            // 补偿操作: 退款
            warn!("⚠️ Initiating payment refund due to save failure");
            // TODO: Implement refund logic
            
            AppError::RepositoryError(e)
        })?;
        
        info!(
            order_id = %order.id(),
            "💾 Order saved to database"
        );
        
        // Step 4: 发布领域事件 (可选)
        // TODO: Publish event to message broker
        
        info!(
            order_id = %order.id(),
            customer_id = %order.customer_id(),
            total_amount = %order.total_amount(),
            "🎉 Order created successfully"
        );
        
        Ok(OrderDto::from(order))
    }
}

#[async_trait]
impl<R, P> OrderUseCasePort for CreateOrderUseCase<R, P>
where
    R: OrderRepositoryPort + 'static,
    P: PaymentGatewayPort + 'static,
{
    async fn create_order(&self, request: CreateOrderRequest) -> Result<OrderDto, AppError> {
        self.execute(request).await
    }
}
```

---

### 3. 基础设施层 (Infrastructure Layer)

#### 3.1 Web 适配器 (Axum HTTP Handler)

```rust
// infrastructure/web/handlers/order_handler.rs
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use crate::application::ports::OrderUseCasePort;
use crate::application::dto::{CreateOrderRequestDto, OrderDto};
use serde_json::json;
use tracing::{instrument, info, error};
use std::sync::Arc;

pub struct OrderHandler<U: OrderUseCasePort> {
    use_case: Arc<U>,
}

impl<U: OrderUseCasePort> OrderHandler<U> {
    pub fn new(use_case: Arc<U>) -> Self {
        Self { use_case }
    }
    
    /// POST /api/orders - 创建订单
    #[instrument(
        name = "http_post_order",
        skip(self, payload),
        fields(
            http.method = "POST",
            http.route = "/api/orders",
            http.status_code = tracing::field::Empty,
            http.request_id = tracing::field::Empty,
            otel.kind = "server",
        )
    )]
    pub async fn create_order(
        State(handler): State<Arc<Self>>,
        Json(payload): Json<CreateOrderRequestDto>,
    ) -> Response {
        info!("📨 Received create order request");
        
        // 转换 DTO 到领域请求
        let request = match payload.into_domain() {
            Ok(req) => req,
            Err(e) => {
                error!(error = ?e, "❌ Invalid request payload");
                tracing::Span::current().record("http.status_code", 400);
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({
                        "error": "Invalid request",
                        "message": e.to_string()
                    }))
                ).into_response();
            }
        };
        
        // 执行用例
        match handler.use_case.create_order(request).await {
            Ok(order) => {
                info!(order_id = %order.id, "✅ Order created successfully");
                tracing::Span::current().record("http.status_code", 201);
                (StatusCode::CREATED, Json(order)).into_response()
            }
            Err(e) => {
                error!(error = ?e, "❌ Failed to create order");
                
                let (status, message) = match e {
                    AppError::DomainError(_) => (StatusCode::BAD_REQUEST, e.to_string()),
                    AppError::PaymentError(_) => (StatusCode::PAYMENT_REQUIRED, e.to_string()),
                    _ => (StatusCode::INTERNAL_SERVER_ERROR, "Internal server error".to_string()),
                };
                
                tracing::Span::current().record("http.status_code", status.as_u16());
                
                (
                    status,
                    Json(json!({
                        "error": "Operation failed",
                        "message": message
                    }))
                ).into_response()
            }
        }
    }
    
    /// GET /api/orders/:id - 获取订单详情
    #[instrument(
        name = "http_get_order",
        skip(self),
        fields(
            http.method = "GET",
            http.route = "/api/orders/{id}",
            http.status_code = tracing::field::Empty,
            order_id = %order_id,
            otel.kind = "server",
        )
    )]
    pub async fn get_order(
        State(handler): State<Arc<Self>>,
        Path(order_id): Path<String>,
    ) -> Response {
        info!(order_id = %order_id, "📨 Received get order request");
        
        let order_id = match OrderId::from_str(&order_id) {
            Ok(id) => id,
            Err(e) => {
                error!(error = ?e, "❌ Invalid order ID");
                tracing::Span::current().record("http.status_code", 400);
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "Invalid order ID"}))
                ).into_response();
            }
        };
        
        match handler.use_case.get_order(order_id).await {
            Ok(order) => {
                info!(order_id = %order_id, "✅ Order found");
                tracing::Span::current().record("http.status_code", 200);
                (StatusCode::OK, Json(order)).into_response()
            }
            Err(AppError::NotFound(_)) => {
                info!(order_id = %order_id, "⚠️ Order not found");
                tracing::Span::current().record("http.status_code", 404);
                (
                    StatusCode::NOT_FOUND,
                    Json(json!({"error": "Order not found"}))
                ).into_response()
            }
            Err(e) => {
                error!(error = ?e, order_id = %order_id, "❌ Failed to get order");
                tracing::Span::current().record("http.status_code", 500);
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(json!({"error": "Internal server error"}))
                ).into_response()
            }
        }
    }
}

// 路由配置
pub fn order_routes<U: OrderUseCasePort + 'static>(use_case: Arc<U>) -> Router {
    let handler = Arc::new(OrderHandler::new(use_case));
    
    Router::new()
        .route("/api/orders", post(OrderHandler::create_order))
        .route("/api/orders/:id", get(OrderHandler::get_order))
        .with_state(handler)
        .layer(tower_http::trace::TraceLayer::new_for_http())
}
```

#### 3.2 数据库适配器 (PostgreSQL)

```rust
// infrastructure/persistence/postgres_order_repository.rs
use crate::domain::entities::Order;
use crate::domain::repositories::{OrderRepositoryPort, RepositoryError};
use crate::domain::value_objects::{OrderId, CustomerId};
use sqlx::{PgPool, Postgres, Row};
use async_trait::async_trait;
use tracing::{instrument, info, error};

pub struct PostgresOrderRepository {
    pool: PgPool,
}

impl PostgresOrderRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl OrderRepositoryPort for PostgresOrderRepository {
    #[instrument(
        name = "postgres_save_order",
        skip(self, order),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.table = "orders",
            order_id = %order.id(),
            customer_id = %order.customer_id(),
            otel.kind = "client",
        )
    )]
    async fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        info!("💾 Saving order to PostgreSQL");
        
        let query = sqlx::query!(
            r#"
            INSERT INTO orders (
                id, customer_id, total_amount, currency, status, created_at, updated_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7)
            ON CONFLICT (id)
            DO UPDATE SET
                status = EXCLUDED.status,
                updated_at = EXCLUDED.updated_at
            "#,
            order.id().as_uuid(),
            order.customer_id().as_uuid(),
            order.total_amount().amount(),
            order.total_amount().currency().to_string(),
            order.status().to_string(),
            order.created_at(),
            order.updated_at(),
        );
        
        query.execute(&self.pool).await.map_err(|e| {
            error!(error = ?e, "❌ Database insert failed");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        // 保存订单项
        for item in order.items() {
            sqlx::query!(
                r#"
                INSERT INTO order_items (
                    order_id, product_id, quantity, unit_price, currency
                )
                VALUES ($1, $2, $3, $4, $5)
                "#,
                order.id().as_uuid(),
                item.product_id().as_uuid(),
                item.quantity() as i32,
                item.unit_price().amount(),
                item.unit_price().currency().to_string(),
            )
            .execute(&self.pool)
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to save order item");
                RepositoryError::DatabaseError(e.to_string())
            })?;
        }
        
        info!(order_id = %order.id(), "✅ Order saved successfully");
        Ok(())
    }
    
    #[instrument(
        name = "postgres_find_order",
        skip(self),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.table = "orders",
            order_id = %id,
            otel.kind = "client",
        )
    )]
    async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, RepositoryError> {
        info!(order_id = %id, "🔍 Querying order from PostgreSQL");
        
        let order_row = sqlx::query!(
            r#"
            SELECT id, customer_id, total_amount, currency, status, created_at, updated_at
            FROM orders
            WHERE id = $1
            "#,
            id.as_uuid(),
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Database query failed");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        let order_row = match order_row {
            Some(row) => row,
            None => {
                info!(order_id = %id, "⚠️ Order not found");
                return Ok(None);
            }
        };
        
        // 查询订单项
        let items_rows = sqlx::query!(
            r#"
            SELECT product_id, quantity, unit_price, currency
            FROM order_items
            WHERE order_id = $1
            ORDER BY created_at
            "#,
            id.as_uuid(),
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Failed to fetch order items");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        // 重建领域对象
        let order = Order::reconstruct(
            OrderId::from_uuid(order_row.id),
            CustomerId::from_uuid(order_row.customer_id),
            items_rows.into_iter().map(|r| OrderItem::reconstruct(
                ProductId::from_uuid(r.product_id),
                r.quantity as u32,
                Money::new(r.unit_price, Currency::from_str(&r.currency)?),
            )).collect(),
            Money::new(order_row.total_amount, Currency::from_str(&order_row.currency)?),
            OrderStatus::from_str(&order_row.status)?,
            order_row.created_at,
            order_row.updated_at,
        )?;
        
        info!(order_id = %id, "✅ Order found");
        Ok(Some(order))
    }
    
    #[instrument(
        name = "postgres_find_orders_by_customer",
        skip(self),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.table = "orders",
            customer_id = %customer_id,
            otel.kind = "client",
        )
    )]
    async fn find_by_customer_id(
        &self,
        customer_id: CustomerId,
    ) -> Result<Vec<Order>, RepositoryError> {
        info!(customer_id = %customer_id, "🔍 Querying orders by customer");
        
        let rows = sqlx::query!(
            r#"
            SELECT id, customer_id, total_amount, currency, status, created_at, updated_at
            FROM orders
            WHERE customer_id = $1
            ORDER BY created_at DESC
            "#,
            customer_id.as_uuid(),
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Database query failed");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        let mut orders = Vec::new();
        
        for row in rows {
            let order_id = OrderId::from_uuid(row.id);
            
            // 查询订单项
            let items = sqlx::query!(
                r#"
                SELECT product_id, quantity, unit_price, currency
                FROM order_items
                WHERE order_id = $1
                "#,
                order_id.as_uuid(),
            )
            .fetch_all(&self.pool)
            .await?;
            
            let order = Order::reconstruct(
                order_id,
                customer_id,
                items.into_iter().map(|i| OrderItem::reconstruct(
                    ProductId::from_uuid(i.product_id),
                    i.quantity as u32,
                    Money::new(i.unit_price, Currency::from_str(&i.currency)?),
                )).collect(),
                Money::new(row.total_amount, Currency::from_str(&row.currency)?),
                OrderStatus::from_str(&row.status)?,
                row.created_at,
                row.updated_at,
            )?;
            
            orders.push(order);
        }
        
        info!(
            customer_id = %customer_id,
            order_count = orders.len(),
            "✅ Found {} orders",
            orders.len()
        );
        
        Ok(orders)
    }
    
    #[instrument(
        name = "postgres_delete_order",
        skip(self),
        fields(
            db.system = "postgresql",
            db.operation = "DELETE",
            db.table = "orders",
            order_id = %id,
            otel.kind = "client",
        )
    )]
    async fn delete(&self, id: OrderId) -> Result<(), RepositoryError> {
        info!(order_id = %id, "🗑️ Deleting order from PostgreSQL");
        
        // 先删除订单项 (外键约束)
        sqlx::query!(
            "DELETE FROM order_items WHERE order_id = $1",
            id.as_uuid(),
        )
        .execute(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Failed to delete order items");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        // 删除订单
        let result = sqlx::query!(
            "DELETE FROM orders WHERE id = $1",
            id.as_uuid(),
        )
        .execute(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Failed to delete order");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        if result.rows_affected() == 0 {
            error!(order_id = %id, "❌ Order not found for deletion");
            return Err(RepositoryError::NotFound(id));
        }
        
        info!(order_id = %id, "✅ Order deleted successfully");
        Ok(())
    }
}
```

---

### 4. OTLP 初始化 (Telemetry Setup)

```rust
// infrastructure/telemetry/init.rs
use opentelemetry::{
    global,
    trace::TracerProvider,
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use tracing_subscriber::{
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_telemetry(service_name: &str, otlp_endpoint: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 OTLP Tracer Provider
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint)
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 2. 设置全局 Tracer Provider
    global::set_tracer_provider(tracer_provider.clone());
    
    // 3. 创建 Tracing Subscriber
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer_provider.tracer(service_name));
    
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    tracing_subscriber::registry()
        .with(env_filter)
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer().with_target(false))
        .init();
    
    info!("🔭 OTLP telemetry initialized: endpoint={}", otlp_endpoint);
    
    Ok(())
}

pub async fn shutdown_telemetry() {
    info!("🛑 Shutting down telemetry");
    global::shutdown_tracer_provider();
}
```

---

### 5. 主程序入口

```rust
// src/main.rs
use order_service::{
    infrastructure::{
        web::server::run_server,
        persistence::PostgresOrderRepository,
        telemetry::init_telemetry,
    },
    application::use_cases::CreateOrderUseCase,
    config::AppConfig,
};
use std::sync::Arc;
use sqlx::PgPool;
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 加载配置
    let config = AppConfig::from_env()?;
    
    // 2. 初始化 OTLP 遥测
    init_telemetry(&config.service_name, &config.otlp_endpoint)?;
    
    info!("🚀 Starting Order Service v{}", env!("CARGO_PKG_VERSION"));
    
    // 3. 连接数据库
    let pool = PgPool::connect(&config.database_url).await?;
    info!("📊 Connected to PostgreSQL: {}", config.database_url);
    
    // 4. 运行数据库迁移
    sqlx::migrate!("./migrations").run(&pool).await?;
    info!("✅ Database migrations applied");
    
    // 5. 组装依赖 (Dependency Injection)
    let order_repo = Arc::new(PostgresOrderRepository::new(pool.clone()));
    let payment_gateway = Arc::new(StripePaymentGateway::new(config.stripe_api_key));
    
    // 6. 创建用例
    let create_order_use_case = Arc::new(CreateOrderUseCase::new(
        order_repo.clone(),
        payment_gateway.clone(),
    ));
    
    // 7. 启动 Web 服务器
    info!("🌐 Starting HTTP server on {}", config.http_addr);
    run_server(config.http_addr, create_order_use_case).await?;
    
    // 8. 优雅关闭
    shutdown_telemetry().await;
    pool.close().await;
    
    info!("👋 Order Service shutdown complete");
    Ok(())
}
```

---

## 🧪 测试策略

### 1. 单元测试 (Mock Adapters)

```rust
// tests/unit/order_service_test.rs
use order_service::domain::entities::Order;
use order_service::domain::value_objects::{CustomerId, Money, Currency};
use order_service::domain::repositories::OrderRepositoryPort;
use mockall::predicate::*;
use mockall::mock;

mock! {
    pub OrderRepository {}
    
    #[async_trait]
    impl OrderRepositoryPort for OrderRepository {
        async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
        async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, RepositoryError>;
        async fn delete(&self, id: OrderId) -> Result<(), RepositoryError>;
    }
}

#[tokio::test]
async fn test_create_order_success() {
    // Arrange
    let mut mock_repo = MockOrderRepository::new();
    mock_repo
        .expect_save()
        .times(1)
        .returning(|_| Ok(()));
    
    let customer_id = CustomerId::new();
    let items = vec![
        OrderItem::new(
            ProductId::new(),
            2,
            Money::new(10.0, Currency::USD).unwrap(),
        ),
    ];
    
    // Act
    let result = Order::create(customer_id, items);
    
    // Assert
    assert!(result.is_ok());
    let (order, event) = result.unwrap();
    assert_eq!(order.customer_id(), customer_id);
    assert_eq!(order.total_amount().amount(), 20.0);
    
    // 保存订单
    assert!(mock_repo.save(&order).await.is_ok());
}

#[test]
fn test_order_validation_empty_items() {
    let customer_id = CustomerId::new();
    let items = vec![];
    
    let result = Order::create(customer_id, items);
    
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), DomainError::EmptyOrder));
}

#[test]
fn test_order_validation_below_minimum() {
    let customer_id = CustomerId::new();
    let items = vec![
        OrderItem::new(
            ProductId::new(),
            1,
            Money::new(5.0, Currency::USD).unwrap(),
        ),
    ];
    
    let result = Order::create(customer_id, items);
    
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), DomainError::BelowMinimumAmount));
}
```

---

### 2. 集成测试 (Testcontainers)

```rust
// tests/integration/order_api_test.rs
use testcontainers::{clients, images};
use sqlx::PgPool;
use reqwest::Client;
use serde_json::json;

#[tokio::test]
async fn test_create_order_end_to_end() {
    // 1. 启动 PostgreSQL 容器
    let docker = clients::Cli::default();
    let postgres_image = images::postgres::Postgres::default();
    let postgres_node = docker.run(postgres_image);
    let postgres_port = postgres_node.get_host_port_ipv4(5432);
    
    let database_url = format!(
        "postgres://postgres:postgres@localhost:{}/postgres",
        postgres_port
    );
    
    // 2. 运行迁移
    let pool = PgPool::connect(&database_url).await.unwrap();
    sqlx::migrate!("./migrations").run(&pool).await.unwrap();
    
    // 3. 启动应用服务器 (在后台线程)
    let app_handle = tokio::spawn(async move {
        run_test_server(pool).await
    });
    
    // 等待服务器启动
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    // 4. 发送 HTTP 请求
    let client = Client::new();
    let response = client
        .post("http://localhost:8080/api/orders")
        .json(&json!({
            "customer_id": "550e8400-e29b-41d4-a716-446655440000",
            "items": [
                {
                    "product_id": "660e8400-e29b-41d4-a716-446655440000",
                    "quantity": 2,
                    "unit_price": 10.0
                }
            ],
            "payment_method": {
                "type": "credit_card",
                "card_number": "4242424242424242"
            }
        }))
        .send()
        .await
        .unwrap();
    
    // 5. 验证响应
    assert_eq!(response.status(), 201);
    
    let order_response: serde_json::Value = response.json().await.unwrap();
    assert_eq!(order_response["total_amount"], 20.0);
    assert_eq!(order_response["status"], "pending");
    
    // 6. 验证数据库
    let order_id = order_response["id"].as_str().unwrap();
    let order_from_db = sqlx::query!(
        "SELECT status FROM orders WHERE id = $1",
        Uuid::parse_str(order_id).unwrap()
    )
    .fetch_one(&pool)
    .await
    .unwrap();
    
    assert_eq!(order_from_db.status, "pending");
    
    // 7. 清理
    app_handle.abort();
}
```

---

## ⚡ 性能优化

### 1. 连接池配置

```rust
// config/database.rs
use sqlx::postgres::PgPoolOptions;
use std::time::Duration;

pub async fn create_pool(database_url: &str) -> Result<PgPool, sqlx::Error> {
    PgPoolOptions::new()
        .max_connections(50)             // 最大连接数
        .min_connections(5)              // 最小连接数
        .acquire_timeout(Duration::from_secs(5))  // 获取连接超时
        .idle_timeout(Duration::from_secs(600))   // 空闲超时 (10 分钟)
        .max_lifetime(Duration::from_secs(1800))  // 最大生命周期 (30 分钟)
        .connect(database_url)
        .await
}
```

---

### 2. 缓存层

```rust
// infrastructure/cache/redis_cache.rs
use redis::{AsyncCommands, Client};
use serde::{Deserialize, Serialize};
use tracing::{instrument, info};

pub struct RedisCache {
    client: Client,
}

impl RedisCache {
    #[instrument(name = "redis_get", skip(self))]
    pub async fn get<T: for<'de> Deserialize<'de>>(
        &self,
        key: &str,
    ) -> Result<Option<T>, CacheError> {
        let mut conn = self.client.get_async_connection().await?;
        
        let data: Option<String> = conn.get(key).await?;
        
        match data {
            Some(json) => {
                let value = serde_json::from_str(&json)?;
                info!(key = %key, "Cache HIT");
                Ok(Some(value))
            }
            None => {
                info!(key = %key, "Cache MISS");
                Ok(None)
            }
        }
    }
    
    #[instrument(name = "redis_set", skip(self, value))]
    pub async fn set<T: Serialize>(
        &self,
        key: &str,
        value: &T,
        ttl_seconds: usize,
    ) -> Result<(), CacheError> {
        let mut conn = self.client.get_async_connection().await?;
        
        let json = serde_json::to_string(value)?;
        conn.set_ex(key, json, ttl_seconds).await?;
        
        info!(key = %key, ttl = ttl_seconds, "Cached value");
        Ok(())
    }
}

// 带缓存的仓储适配器
pub struct CachedOrderRepository<R: OrderRepositoryPort> {
    repository: Arc<R>,
    cache: Arc<RedisCache>,
}

#[async_trait]
impl<R: OrderRepositoryPort> OrderRepositoryPort for CachedOrderRepository<R> {
    async fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, RepositoryError> {
        let cache_key = format!("order:{}", id);
        
        // 1. 尝试从缓存读取
        if let Ok(Some(order)) = self.cache.get::<Order>(&cache_key).await {
            info!(order_id = %id, "Order found in cache");
            return Ok(Some(order));
        }
        
        // 2. 缓存未命中,从数据库读取
        let order = self.repository.find_by_id(id).await?;
        
        // 3. 写入缓存
        if let Some(ref o) = order {
            let _ = self.cache.set(&cache_key, o, 300).await; // TTL: 5 分钟
        }
        
        Ok(order)
    }
    
    async fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        // 1. 保存到数据库
        self.repository.save(order).await?;
        
        // 2. 使缓存失效
        let cache_key = format!("order:{}", order.id());
        let _ = self.cache.delete(&cache_key).await;
        
        Ok(())
    }
}
```

---

## 🚀 生产部署

### Cargo.toml (完整依赖)

```toml
[package]
name = "order-service"
version = "1.0.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Async runtime
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web framework
axum = { version = "0.7", features = ["macros"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }
hyper = "1.5"

# Database
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "macros", "uuid", "chrono"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Error handling
anyhow = "1.0"
thiserror = "2.0"

# UUID
uuid = { version = "1.11", features = ["serde", "v4"] }

# Time
chrono = { version = "0.4", features = ["serde"] }

# Tracing & OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"
opentelemetry = { version = "0.31", features = ["trace"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["tonic"] }
opentelemetry-semantic-conventions = "0.16"

# Config
config = "0.14"
dotenvy = "0.15"

# Cache
redis = { version = "0.27", features = ["tokio-comp", "connection-manager"] }

# Testing
[dev-dependencies]
tokio-test = "0.4"
mockall = "0.13"
testcontainers = "0.23"
reqwest = "0.12"
wiremock = "0.6"
```

---

### Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.9'

services:
  # 订单服务
  order-service:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - SERVICE_NAME=order-service
      - DATABASE_URL=postgres://postgres:password@postgres:5432/orders
      - REDIS_URL=redis://redis:6379
      - OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - redis
      - otel-collector

  # PostgreSQL 数据库
  postgres:
    image: postgres:16-alpine
    environment:
      POSTGRES_PASSWORD: password
      POSTGRES_DB: orders
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  # Redis 缓存
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector:0.111.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "13133:13133" # health_check

  # Jaeger UI
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686" # UI
      - "14250:14250" # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true

  # Prometheus
  prometheus:
    image: prom/prometheus:v2.55.0
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml

  # Grafana
  grafana:
    image: grafana/grafana:11.3.0
    ports:
      - "3000:3000"
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
    volumes:
      - grafana_data:/var/lib/grafana

volumes:
  postgres_data:
  grafana_data:
```

---

## 🔍 故障排查

### 常见问题

#### 1. 追踪数据未上报

**症状**: Jaeger UI 没有追踪数据。

**排查步骤**:

```bash
# 1. 检查 OTLP Collector 健康状态
curl http://localhost:13133/

# 2. 检查应用日志
docker logs order-service | grep -i "otlp"

# 3. 验证 Tracer Provider 初始化
# 查看日志中是否有 "OTLP telemetry initialized"

# 4. 测试 OTLP 端点连通性
grpcurl -plaintext localhost:4317 list
```

**解决方案**:

```rust
// 确保 OTLP 导出器配置正确
let tracer_provider = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://otel-collector:4317")  // 确保地址正确
            .with_timeout(Duration::from_secs(10))        // 增加超时时间
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

---

#### 2. 数据库连接池耗尽

**症状**: 应用卡住,日志显示 "connection pool timeout"。

**排查**:

```sql
-- 查看当前连接数
SELECT count(*) FROM pg_stat_activity WHERE datname = 'orders';

-- 查看慢查询
SELECT pid, now() - pg_stat_activity.query_start AS duration, query
FROM pg_stat_activity
WHERE state != 'idle' AND now() - pg_stat_activity.query_start > interval '5 seconds';
```

**解决方案**:

```rust
// 优化连接池配置
PgPoolOptions::new()
    .max_connections(100)            // 增加最大连接数
    .acquire_timeout(Duration::from_secs(10))  // 增加超时
    .connect(database_url)
    .await
```

---

## ✅ 最佳实践清单

### 架构设计

- [x] **核心领域层零依赖**: 领域层不依赖任何框架,包括 OTLP
- [x] **端口定义在领域层**: 遵循依赖倒置原则
- [x] **适配器实现在基础设施层**: 技术实现与业务逻辑分离
- [x] **值对象不可变**: 使用 Rust 的不可变性保证数据完整性
- [x] **领域事件**: 通过事件记录业务状态变化,而非直接记录日志

### OTLP 集成

- [x] **应用层集成点**: 在用例层集成 OTLP,保持领域层纯粹
- [x] **使用 `#[instrument]` 宏**: 自动追踪函数调用
- [x] **结构化日志**: 使用 `tracing` 的字段功能,而非字符串拼接
- [x] **适配器完整插桩**: HTTP、数据库、缓存、消息队列全部追踪
- [x] **错误追踪**: 记录错误信息到 Span

### Rust 特性

- [x] **async-trait**: 异步 trait 方法
- [x] **Arc 共享所有权**: 在多线程环境下共享适配器
- [x] **类型安全**: 使用 NewType 模式包装 UUID,避免混淆
- [x] **错误处理**: 使用 `thiserror` 定义领域错误,使用 `anyhow` 处理应用错误
- [x] **测试**: 使用 `mockall` Mock 依赖,使用 `testcontainers` 集成测试

---

## 📚 参考资源

### 国际标准

1. **Hexagonal Architecture**: [Alistair Cockburn's Blog](https://alistair.cockburn.us/hexagonal-architecture/)
2. **Domain-Driven Design**: Eric Evans, 2003
3. **Clean Architecture**: Robert C. Martin, 2012
4. **SOLID Principles**: Robert C. Martin

### Rust 生态

1. **Axum Web Framework**: [docs.rs/axum](https://docs.rs/axum)
2. **SQLx Database Library**: [docs.rs/sqlx](https://docs.rs/sqlx)
3. **OpenTelemetry Rust**: [docs.rs/opentelemetry](https://docs.rs/opentelemetry)
4. **Tracing**: [docs.rs/tracing](https://docs.rs/tracing)

### 示例代码

1. **完整示例**: [GitHub - hexagonal-rust-otlp](https://github.com/example/hexagonal-rust-otlp)
2. **DDD with Rust**: [GitHub - rust-ddd](https://github.com/example/rust-ddd)

---

## 🎉 总结

六边形架构是一种**国际认可的软件架构模式**,强调:

1. **业务逻辑与技术实现分离**
2. **依赖倒置**: 外层依赖内层,内层定义接口
3. **可测试性**: 通过 Mock Adapters 轻松测试
4. **OTLP 集成**: 在应用层和基础设施层集成,保持领域层纯粹

在 Rust 1.90 中,我们使用:

- **Trait** 定义端口
- **Struct + impl** 实现适配器
- **Arc** 共享所有权
- **async-trait** 异步方法
- **tracing + opentelemetry** 实现分布式追踪

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**作者**: OTLP Rust 文档团队

---

**🏛️ 六边形架构 - 构建可维护、可测试、可扩展的 Rust 应用！**-
