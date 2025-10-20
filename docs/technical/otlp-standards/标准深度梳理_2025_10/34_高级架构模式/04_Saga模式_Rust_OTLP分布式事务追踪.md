# Saga 模式 (分布式事务) - Rust OTLP 完整实现

> **国际标准对标**: Saga Pattern (Hector Garcia-Molina & Kenneth Salem, 1987)  
> **现代实践**: Microservices Patterns (Chris Richardson, 2018)  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **完整示例**: 电商下单流程 (订单→支付→库存→物流)

---

## 📋 目录

- [Saga 模式 (分布式事务) - Rust OTLP 完整实现](#saga-模式-分布式事务---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [🏛️ Saga 模式概述](#️-saga-模式概述)
    - [什么是 Saga?](#什么是-saga)
      - [分布式事务的挑战](#分布式事务的挑战)
    - [国际标准对标](#国际标准对标)
  - [🎯 核心概念](#-核心概念)
    - [1. Saga 事务](#1-saga-事务)
    - [2. 补偿事务 (Compensating Transaction)](#2-补偿事务-compensating-transaction)
    - [3. Saga 执行协调器](#3-saga-执行协调器)
  - [🔄 两种实现模式](#-两种实现模式)
    - [1. Orchestration (编排)](#1-orchestration-编排)
    - [2. Choreography (编舞)](#2-choreography-编舞)
    - [对比](#对比)
  - [🦀 Rust 实现设计](#-rust-实现设计)
    - [项目结构](#项目结构)
  - [🔭 OTLP 分布式追踪策略](#-otlp-分布式追踪策略)
    - [Saga 追踪的特殊性](#saga-追踪的特殊性)
  - [📦 完整电商下单示例 (Orchestration)](#-完整电商下单示例-orchestration)
    - [1. Saga 定义](#1-saga-定义)
      - [1.1 Saga 步骤](#11-saga-步骤)
      - [1.2 Saga 状态机](#12-saga-状态机)
    - [2. 服务实现](#2-服务实现)
      - [2.1 订单服务](#21-订单服务)
      - [2.2 支付服务](#22-支付服务)
      - [2.3 库存服务](#23-库存服务)
      - [2.4 物流服务](#24-物流服务)
    - [3. Saga 协调器 (Orchestrator)](#3-saga-协调器-orchestrator)
    - [4. Saga 执行引擎](#4-saga-执行引擎)
  - [🎭 Choreography 实现](#-choreography-实现)
    - [事件驱动架构](#事件驱动架构)
  - [⚠️ 故障处理与补偿](#️-故障处理与补偿)
    - [补偿策略](#补偿策略)
  - [🚀 生产部署](#-生产部署)
    - [Cargo.toml](#cargotoml)
    - [Docker Compose](#docker-compose)
  - [✅ 最佳实践](#-最佳实践)
    - [Saga 设计](#saga-设计)
    - [OTLP 集成](#otlp-集成)
    - [故障恢复](#故障恢复)

---

## 🏛️ Saga 模式概述

### 什么是 Saga?

**Saga** 是一种管理分布式事务的设计模式,通过一系列**本地事务**和**补偿事务**来保证**最终一致性**。

#### 分布式事务的挑战

```text
传统 ACID 事务 (单体应用):
┌─────────────────────────────────┐
│  BEGIN TRANSACTION              │
│  1. 创建订单                     │
│  2. 扣减库存                     │
│  3. 扣款                         │
│  4. 创建物流                     │
│  COMMIT / ROLLBACK              │
└─────────────────────────────────┘
✅ 强一致性 (两阶段提交)

微服务架构:
┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐
│ 订单服务  │  │ 支付服务  │  │ 库存服务  │  │ 物流服务  │
└──────────┘  └──────────┘  └──────────┘  └──────────┘
❌ 无法使用两阶段提交 (性能差、阻塞、单点故障)
✅ Saga 模式 (最终一致性)
```

### 国际标准对标

| 标准/来源 | 内容 |
|----------|------|
| **原始论文** | Hector Garcia-Molina & Kenneth Salem (1987) "Sagas" |
| **微服务模式** | Chris Richardson "Microservices Patterns" (2018) |
| **AWS** | [Saga Pattern for Microservices](https://aws.amazon.com/blogs/compute/implementing-saga-pattern/) |
| **Microsoft** | [Saga distributed transactions pattern](https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/saga/saga) |
| **Google Cloud** | [Distributed transactions with Saga pattern](https://cloud.google.com/architecture/distributed-transactions-saga) |

---

## 🎯 核心概念

### 1. Saga 事务

```rust
/// Saga 由一系列本地事务组成
/// T1, T2, T3, ..., Tn
/// 
/// 如果所有事务成功:
///   T1 -> T2 -> T3 -> ... -> Tn (成功)
/// 
/// 如果 Ti 失败:
///   T1 -> T2 -> ... -> Ti (失败)
///   执行补偿: C(i-1) -> C(i-2) -> ... -> C1
```

### 2. 补偿事务 (Compensating Transaction)

```rust
/// 每个正向事务 Ti 都有对应的补偿事务 Ci
/// 
/// 示例:
/// - T: 创建订单    -> C: 取消订单
/// - T: 扣减库存    -> C: 恢复库存
/// - T: 扣款        -> C: 退款
/// - T: 创建物流单  -> C: 取消物流
```

**关键特性**:

- 补偿事务必须**幂等** (可重复执行)
- 补偿事务**不一定**完全回滚 (可能是业务逆操作)
- 补偿事务**必须成功** (需要重试机制)

### 3. Saga 执行协调器

```text
Orchestrator (编排器):
┌─────────────────────────────────────────┐
│        Saga Orchestrator                │
│  ┌─────────────────────────────────┐    │
│  │  1. 执行 T1                      │   │
│  │  2. 执行 T2                      │   │
│  │  3. 执行 T3 (失败!)              │   │
│  │  4. 补偿 C2                      │   │
│  │  5. 补偿 C1                      │   │
│  └─────────────────────────────────┘    │
└─────────────────────────────────────────┘
```

---

## 🔄 两种实现模式

### 1. Orchestration (编排)

**中心化协调器**:

```text
          Orchestrator
               │
     ┌─────────┼─────────┬─────────┐
     │         │         │         │
     ▼         ▼         ▼         ▼
  订单服务  支付服务  库存服务  物流服务
```

**特点**:

- ✅ 集中式控制 (易于理解和调试)
- ✅ 明确的执行顺序
- ✅ 易于实现复杂流程
- ❌ 单点故障 (Orchestrator 挂了)
- ❌ 服务间耦合

### 2. Choreography (编舞)

**去中心化事件驱动**:

```text
订单服务 --[OrderCreated]--> 支付服务
                                  │
                         [PaymentCompleted]
                                  │
                                  ▼
                             库存服务
                                  │
                         [StockReserved]
                                  │
                                  ▼
                             物流服务
```

**特点**:

- ✅ 松耦合 (服务独立)
- ✅ 无单点故障
- ✅ 高可用
- ❌ 难以理解整体流程
- ❌ 难以调试和监控
- ❌ 循环依赖风险

### 对比

| 维度 | Orchestration | Choreography |
|------|---------------|--------------|
| **复杂度** | 低 (集中式) | 高 (分布式) |
| **可维护性** | 高 | 低 |
| **耦合度** | 高 | 低 |
| **单点故障** | 是 | 否 |
| **适用场景** | 复杂业务流程 | 简单事件驱动 |

**推荐**: **Orchestration** (本文重点实现)

---

## 🦀 Rust 实现设计

### 项目结构

```text
saga_example/
├── src/
│   ├── domain/           # 领域模型
│   │   ├── order.rs
│   │   ├── payment.rs
│   │   ├── inventory.rs
│   │   └── shipping.rs
│   ├── saga/             # Saga 核心
│   │   ├── definition.rs      # Saga 定义
│   │   ├── orchestrator.rs    # Orchestrator
│   │   ├── executor.rs        # 执行引擎
│   │   └── compensator.rs     # 补偿引擎
│   ├── services/         # 业务服务
│   │   ├── order_service.rs
│   │   ├── payment_service.rs
│   │   ├── inventory_service.rs
│   │   └── shipping_service.rs
│   └── main.rs
└── Cargo.toml
```

---

## 🔭 OTLP 分布式追踪策略

### Saga 追踪的特殊性

```text
Trace 视图:
┌────────────────────────────────────────────────────────────────┐
│ Saga: PlaceOrder (trace_id: abc123)                            │
│ ┌────────────────────────────────────────────────────────────┐ │
│ │ Step 1: CreateOrder (span_id: 001)                         │ │
│ │   ├─ OrderService.create()                                 │ │
│ │   └─ DB Insert                                             │ │
│ ├────────────────────────────────────────────────────────────┤ │
│ │ Step 2: ProcessPayment (span_id: 002, parent: 001)         │ │
│ │   ├─ PaymentService.charge()                               │ │
│ │   └─ External API Call                                     │ │
│ ├────────────────────────────────────────────────────────────┤ │
│ │Step 3: ReserveStock (span_id: 003, parent: 001) ❌ FAILED  │ │
│ │   ├─ InventoryService.reserve()                            │ │
│ │   └─ Error: OutOfStock                                     │ │
│ ├────────────────────────────────────────────────────────────┤ │
│ │ Compensation 2: RefundPayment (span_id: 004, parent: 001)  │ │
│ │   ├─ PaymentService.refund()                               │ │
│ │   └─ Compensate: span_id=002                               │ │
│ ├────────────────────────────────────────────────────────────┤ │
│ │ Compensation 1: CancelOrder (span_id: 005, parent: 001)    │ │
│ │   ├─ OrderService.cancel()                                 │ │
│ │   └─ Compensate: span_id=001                               │ │
│ └────────────────────────────────────────────────────────────┘ │
│ Status: FAILED (compensated)                                   │
└────────────────────────────────────────────────────────────────┘
```

**关键追踪点**:

1. **Saga Root Span**: 整个 Saga 的根 Span
2. **Step Spans**: 每个步骤的 Span (parent = root)
3. **Compensation Spans**: 补偿事务的 Span (关联原 Span)
4. **Custom Attributes**: `saga.step`, `saga.status`, `saga.compensate_for`

---

## 📦 完整电商下单示例 (Orchestration)

### 1. Saga 定义

#### 1.1 Saga 步骤

```rust
// src/saga/definition.rs
use async_trait::async_trait;
use tracing::{instrument, Span};
use anyhow::Result;
use serde::{Deserialize, Serialize};

/// Saga 执行上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SagaContext {
    pub saga_id: String,
    pub order_id: String,
    pub user_id: String,
    pub amount: f64,
    pub items: Vec<OrderItem>,
    
    // 运行时数据
    pub payment_id: Option<String>,
    pub reservation_id: Option<String>,
    pub shipping_id: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub sku: String,
    pub quantity: u32,
    pub price: f64,
}

/// Saga 步骤结果
#[derive(Debug)]
pub enum StepResult {
    Success(SagaContext),
    Failed(String),
}

/// Saga 步骤 Trait
#[async_trait]
pub trait SagaStep: Send + Sync {
    /// 步骤名称
    fn name(&self) -> &str;
    
    /// 执行正向事务
    async fn execute(&self, ctx: SagaContext) -> Result<SagaContext>;
    
    /// 执行补偿事务
    async fn compensate(&self, ctx: SagaContext) -> Result<()>;
}

/// Saga 定义
pub struct SagaDefinition {
    pub name: String,
    pub steps: Vec<Box<dyn SagaStep>>,
}

impl SagaDefinition {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            steps: Vec::new(),
        }
    }
    
    pub fn add_step(mut self, step: Box<dyn SagaStep>) -> Self {
        self.steps.push(step);
        self
    }
}
```

#### 1.2 Saga 状态机

```rust
// src/saga/definition.rs (续)
use std::fmt;

/// Saga 状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SagaStatus {
    Started,
    Running { current_step: usize },
    Compensating { failed_step: usize },
    Completed,
    Failed,
    Compensated,
}

impl fmt::Display for SagaStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Started => write!(f, "STARTED"),
            Self::Running { current_step } => write!(f, "RUNNING[step={}]", current_step),
            Self::Compensating { failed_step } => write!(f, "COMPENSATING[failed_at={}]", failed_step),
            Self::Completed => write!(f, "COMPLETED"),
            Self::Failed => write!(f, "FAILED"),
            Self::Compensated => write!(f, "COMPENSATED"),
        }
    }
}

/// Saga 状态转换
impl SagaStatus {
    pub fn start() -> Self {
        Self::Started
    }
    
    pub fn run(step: usize) -> Self {
        Self::Running { current_step: step }
    }
    
    pub fn compensate(failed_step: usize) -> Self {
        Self::Compensating { failed_step }
    }
    
    pub fn complete() -> Self {
        Self::Completed
    }
    
    pub fn fail() -> Self {
        Self::Failed
    }
    
    pub fn compensated() -> Self {
        Self::Compensated
    }
}
```

---

### 2. 服务实现

#### 2.1 订单服务

```rust
// src/services/order_service.rs
use crate::domain::order::Order;
use crate::saga::definition::{SagaContext, SagaStep, StepResult};
use async_trait::async_trait;
use tracing::{instrument, info, error};
use anyhow::{Result, Context as _};
use sqlx::PgPool;
use uuid::Uuid;

pub struct OrderService {
    db: PgPool,
}

impl OrderService {
    pub fn new(db: PgPool) -> Self {
        Self { db }
    }
    
    #[instrument(skip(self), fields(otel.kind = "server", service.name = "order-service"))]
    pub async fn create_order(&self, ctx: &SagaContext) -> Result<String> {
        info!(
            saga_id = %ctx.saga_id,
            user_id = %ctx.user_id,
            amount = ctx.amount,
            "Creating order"
        );
        
        let order_id = Uuid::new_v4().to_string();
        
        sqlx::query!(
            r#"
            INSERT INTO orders (id, user_id, amount, status, created_at)
            VALUES ($1, $2, $3, 'PENDING', NOW())
            "#,
            order_id,
            ctx.user_id,
            ctx.amount
        )
        .execute(&self.db)
        .await
        .context("Failed to create order")?;
        
        info!(order_id = %order_id, "Order created successfully");
        Ok(order_id)
    }
    
    #[instrument(skip(self), fields(otel.kind = "server"))]
    pub async fn cancel_order(&self, order_id: &str) -> Result<()> {
        info!(order_id = %order_id, "Cancelling order");
        
        sqlx::query!(
            r#"UPDATE orders SET status = 'CANCELLED' WHERE id = $1"#,
            order_id
        )
        .execute(&self.db)
        .await
        .context("Failed to cancel order")?;

        info!(order_id = %order_id, "Order cancelled");
        Ok(())
    }
}

/// Step 1: 创建订单
pub struct CreateOrderStep {
    service: OrderService,
}

impl CreateOrderStep {
    pub fn new(service: OrderService) -> Self {
        Self { service }
    }
}

#[async_trait]
impl SagaStep for CreateOrderStep {
    fn name(&self) -> &str {
        "CreateOrder"
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "create_order",
            saga.id = %ctx.saga_id,
            order.id = %ctx.order_id
        )
    )]
    async fn execute(&self, mut ctx: SagaContext) -> Result<SagaContext> {
        let order_id = self.service.create_order(&ctx).await?;
        ctx.order_id = order_id;
        Ok(ctx)
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "cancel_order",
            saga.compensate_for = "create_order",
            order.id = %ctx.order_id
        )
    )]
    async fn compensate(&self, ctx: SagaContext) -> Result<()> {
        self.service.cancel_order(&ctx.order_id).await
    }
}
```

#### 2.2 支付服务

```rust
// src/services/payment_service.rs
use crate::saga::definition::{SagaContext, SagaStep};
use async_trait::async_trait;
use tracing::{instrument, info};
use anyhow::{Result, bail};
use uuid::Uuid;

pub struct PaymentService {
    // 模拟外部支付 API
}

impl PaymentService {
    pub fn new() -> Self {
        Self {}
    }
    
    #[instrument(skip(self), fields(otel.kind = "client", peer.service = "payment-gateway"))]
    pub async fn charge(&self, user_id: &str, amount: f64) -> Result<String> {
        info!(user_id = %user_id, amount = amount, "Processing payment");
        
        // 模拟支付 API 调用
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        let payment_id = Uuid::new_v4().to_string();
        info!(payment_id = %payment_id, "Payment successful");
        Ok(payment_id)
    }
    
    #[instrument(skip(self), fields(otel.kind = "client"))]
    pub async fn refund(&self, payment_id: &str) -> Result<()> {
        info!(payment_id = %payment_id, "Processing refund");
        
        // 模拟退款 API 调用
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        info!(payment_id = %payment_id, "Refund successful");
        Ok(())
    }
}

/// Step 2: 处理支付
pub struct ProcessPaymentStep {
    service: PaymentService,
}

impl ProcessPaymentStep {
    pub fn new(service: PaymentService) -> Self {
        Self { service }
    }
}

#[async_trait]
impl SagaStep for ProcessPaymentStep {
    fn name(&self) -> &str {
        "ProcessPayment"
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "process_payment",
            saga.id = %ctx.saga_id,
            payment.amount = ctx.amount
        )
    )]
    async fn execute(&self, mut ctx: SagaContext) -> Result<SagaContext> {
        let payment_id = self.service.charge(&ctx.user_id, ctx.amount).await?;
        ctx.payment_id = Some(payment_id);
        Ok(ctx)
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "refund_payment",
            saga.compensate_for = "process_payment",
            payment.id = ?ctx.payment_id
        )
    )]
    async fn compensate(&self, ctx: SagaContext) -> Result<()> {
        if let Some(payment_id) = ctx.payment_id {
            self.service.refund(&payment_id).await?;
        }
        Ok(())
    }
}
```

#### 2.3 库存服务

```rust
// src/services/inventory_service.rs
use crate::saga::definition::{SagaContext, SagaStep};
use async_trait::async_trait;
use tracing::{instrument, info, warn};
use anyhow::{Result, bail};
use uuid::Uuid;

pub struct InventoryService {
    // 模拟库存系统
}

impl InventoryService {
    pub fn new() -> Self {
        Self {}
    }
    
    #[instrument(skip(self), fields(otel.kind = "server"))]
    pub async fn reserve_stock(&self, ctx: &SagaContext) -> Result<String> {
        info!(items = ?ctx.items, "Reserving stock");
        
        // 模拟库存检查 (10% 概率缺货,用于演示补偿)
        if rand::random::<f64>() < 0.1 {
            warn!("Stock insufficient");
            bail!("Stock insufficient for items");
        }
        
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        let reservation_id = Uuid::new_v4().to_string();
        info!(reservation_id = %reservation_id, "Stock reserved");
        Ok(reservation_id)
    }
    
    #[instrument(skip(self), fields(otel.kind = "server"))]
    pub async fn release_stock(&self, reservation_id: &str) -> Result<()> {
        info!(reservation_id = %reservation_id, "Releasing stock");
        
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        info!(reservation_id = %reservation_id, "Stock released");
    Ok(())
}
}

/// Step 3: 预留库存
pub struct ReserveStockStep {
    service: InventoryService,
}

impl ReserveStockStep {
    pub fn new(service: InventoryService) -> Self {
        Self { service }
    }
}

#[async_trait]
impl SagaStep for ReserveStockStep {
    fn name(&self) -> &str {
        "ReserveStock"
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "reserve_stock",
            saga.id = %ctx.saga_id,
            items.count = ctx.items.len()
        )
    )]
    async fn execute(&self, mut ctx: SagaContext) -> Result<SagaContext> {
        let reservation_id = self.service.reserve_stock(&ctx).await?;
        ctx.reservation_id = Some(reservation_id);
        Ok(ctx)
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "release_stock",
            saga.compensate_for = "reserve_stock",
            reservation.id = ?ctx.reservation_id
        )
    )]
    async fn compensate(&self, ctx: SagaContext) -> Result<()> {
        if let Some(reservation_id) = ctx.reservation_id {
            self.service.release_stock(&reservation_id).await?;
        }
        Ok(())
    }
}
```

#### 2.4 物流服务

```rust
// src/services/shipping_service.rs
use crate::saga::definition::{SagaContext, SagaStep};
use async_trait::async_trait;
use tracing::{instrument, info};
use anyhow::Result;
use uuid::Uuid;

pub struct ShippingService {}

impl ShippingService {
    pub fn new() -> Self {
        Self {}
    }
    
    #[instrument(skip(self), fields(otel.kind = "server"))]
    pub async fn create_shipment(&self, ctx: &SagaContext) -> Result<String> {
        info!(order_id = %ctx.order_id, "Creating shipment");
        
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        let shipping_id = Uuid::new_v4().to_string();
        info!(shipping_id = %shipping_id, "Shipment created");
        Ok(shipping_id)
    }
    
    #[instrument(skip(self), fields(otel.kind = "server"))]
    pub async fn cancel_shipment(&self, shipping_id: &str) -> Result<()> {
        info!(shipping_id = %shipping_id, "Cancelling shipment");
        
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        info!(shipping_id = %shipping_id, "Shipment cancelled");
        Ok(())
    }
}

/// Step 4: 创建物流
pub struct CreateShipmentStep {
    service: ShippingService,
}

impl CreateShipmentStep {
    pub fn new(service: ShippingService) -> Self {
        Self { service }
    }
}

#[async_trait]
impl SagaStep for CreateShipmentStep {
    fn name(&self) -> &str {
        "CreateShipment"
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "create_shipment",
            saga.id = %ctx.saga_id
        )
    )]
    async fn execute(&self, mut ctx: SagaContext) -> Result<SagaContext> {
        let shipping_id = self.service.create_shipment(&ctx).await?;
        ctx.shipping_id = Some(shipping_id);
        Ok(ctx)
    }
    
    #[instrument(
        skip(self, ctx),
        fields(
            saga.step = "cancel_shipment",
            saga.compensate_for = "create_shipment",
            shipping.id = ?ctx.shipping_id
        )
    )]
    async fn compensate(&self, ctx: SagaContext) -> Result<()> {
        if let Some(shipping_id) = ctx.shipping_id {
            self.service.cancel_shipment(&shipping_id).await?;
        }
        Ok(())
    }
}
```

---

### 3. Saga 协调器 (Orchestrator)

```rust
// src/saga/orchestrator.rs
use crate::saga::definition::{SagaDefinition, SagaContext, SagaStatus};
use tracing::{instrument, info, warn, error, Span};
use anyhow::{Result, Context as _};
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry::KeyValue;

pub struct SagaOrchestrator {
    definition: SagaDefinition,
}

impl SagaOrchestrator {
    pub fn new(definition: SagaDefinition) -> Self {
        Self { definition }
    }
    
    /// 执行 Saga
    #[instrument(
        skip(self, ctx),
        fields(
            saga.name = %self.definition.name,
            saga.id = %ctx.saga_id,
            saga.steps = self.definition.steps.len()
        )
    )]
    pub async fn execute(&self, ctx: SagaContext) -> Result<SagaContext> {
        let mut current_ctx = ctx;
        let mut executed_steps = Vec::new();
        let mut status = SagaStatus::start();
        
        // 记录 Saga 开始
        info!(
            saga_name = %self.definition.name,
            saga_id = %current_ctx.saga_id,
            "Saga started"
        );
        Span::current().set_attribute(KeyValue::new("saga.status", status.to_string()));
        
        // 执行所有步骤
        for (idx, step) in self.definition.steps.iter().enumerate() {
            status = SagaStatus::run(idx);
            Span::current().set_attribute(KeyValue::new("saga.status", status.to_string()));
            
            info!(
                step = idx,
                step_name = step.name(),
                "Executing step"
            );
            
            match step.execute(current_ctx.clone()).await {
                Ok(new_ctx) => {
                    current_ctx = new_ctx;
                    executed_steps.push((idx, step.as_ref()));
                    
                    info!(
                        step = idx,
                        step_name = step.name(),
                        "Step completed successfully"
                    );
                }
                Err(e) => {
                    error!(
                        step = idx,
                        step_name = step.name(),
                        error = %e,
                        "Step failed, starting compensation"
                    );
                    
                    status = SagaStatus::compensate(idx);
                    Span::current().set_attribute(KeyValue::new("saga.status", status.to_string()));
                    Span::current().set_attribute(KeyValue::new("saga.error", e.to_string()));
                    
                    // 补偿已执行的步骤
                    self.compensate(executed_steps, &current_ctx).await?;
                    
                    status = SagaStatus::compensated();
                    Span::current().set_attribute(KeyValue::new("saga.status", status.to_string()));
                    
                    return Err(e.context(format!("Saga failed at step {}: {}", idx, step.name())));
                }
            }
        }
        
        // 所有步骤成功
        status = SagaStatus::complete();
        Span::current().set_attribute(KeyValue::new("saga.status", status.to_string()));
        
        info!(
            saga_name = %self.definition.name,
            saga_id = %current_ctx.saga_id,
            "Saga completed successfully"
        );
        
        Ok(current_ctx)
    }
    
    /// 补偿已执行的步骤 (逆序)
    #[instrument(skip(self, executed_steps, ctx), fields(steps = executed_steps.len()))]
    async fn compensate(
        &self,
        executed_steps: Vec<(usize, &dyn crate::saga::definition::SagaStep)>,
        ctx: &SagaContext,
    ) -> Result<()> {
        info!("Starting compensation for {} steps", executed_steps.len());
        
        // 逆序补偿
        for (idx, step) in executed_steps.into_iter().rev() {
            warn!(
                step = idx,
                step_name = step.name(),
                "Compensating step"
            );
            
            match step.compensate(ctx.clone()).await {
                Ok(_) => {
                    info!(
                        step = idx,
                        step_name = step.name(),
                        "Compensation successful"
                    );
                }
                Err(e) => {
                    error!(
                        step = idx,
                        step_name = step.name(),
                        error = %e,
                        "Compensation failed - MANUAL INTERVENTION REQUIRED"
                    );
                    // ⚠️ 补偿失败需要人工介入或重试机制
                    // 这里可以发送告警、写入死信队列等
                }
            }
        }
        
        info!("Compensation completed");
        Ok(())
    }
}
```

---

### 4. Saga 执行引擎

```rust
// src/saga/executor.rs
use crate::saga::definition::SagaContext;
use crate::saga::orchestrator::SagaOrchestrator;
use tracing::{instrument, info};
use anyhow::Result;
use std::sync::Arc;

/// Saga 执行引擎
pub struct SagaExecutor {
    orchestrator: Arc<SagaOrchestrator>,
}

impl SagaExecutor {
    pub fn new(orchestrator: SagaOrchestrator) -> Self {
        Self {
            orchestrator: Arc::new(orchestrator),
        }
    }
    
    /// 异步执行 Saga
    #[instrument(skip(self, ctx), fields(saga.id = %ctx.saga_id))]
    pub async fn execute(&self, ctx: SagaContext) -> Result<SagaContext> {
        info!(saga_id = %ctx.saga_id, "Starting saga execution");
        
        let result = self.orchestrator.execute(ctx).await;
        
        match &result {
            Ok(final_ctx) => {
                info!(
                    saga_id = %final_ctx.saga_id,
                    "Saga execution completed successfully"
                );
            }
            Err(e) => {
                info!(error = %e, "Saga execution failed and compensated");
            }
        }
        
        result
    }
}
```

---

## 🎭 Choreography 实现

### 事件驱动架构

```rust
// src/saga/choreography.rs
use serde::{Deserialize, Serialize};
use tracing::{instrument, info};

/// 领域事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DomainEvent {
    OrderCreated {
        order_id: String,
        user_id: String,
        amount: f64,
    },
    PaymentCompleted {
        order_id: String,
        payment_id: String,
    },
    PaymentFailed {
        order_id: String,
        reason: String,
    },
    StockReserved {
        order_id: String,
        reservation_id: String,
    },
    StockReservationFailed {
        order_id: String,
        reason: String,
    },
    ShipmentCreated {
        order_id: String,
        shipping_id: String,
    },
}

/// 订单服务 - 事件处理器
pub struct OrderEventHandler {}

impl OrderEventHandler {
    #[instrument(skip(self))]
    pub async fn on_order_created(&self, event: DomainEvent) {
        if let DomainEvent::OrderCreated { order_id, user_id, amount } = event {
            info!(order_id = %order_id, "Order created, publishing event");
            
            // 发布事件到消息队列 (Kafka/RabbitMQ)
            // event_bus.publish("order.created", event).await
        }
    }
}

/// 支付服务 - 事件处理器
pub struct PaymentEventHandler {}

impl PaymentEventHandler {
    #[instrument(skip(self))]
    pub async fn on_order_created(&self, event: DomainEvent) {
        if let DomainEvent::OrderCreated { order_id, amount, .. } = event {
            info!(order_id = %order_id, "Received OrderCreated, processing payment");
            
            // 处理支付
            // match payment_service.charge(...).await {
            //     Ok(payment_id) => publish(PaymentCompleted),
            //     Err(e) => publish(PaymentFailed)
            // }
        }
    }
}

/// 库存服务 - 事件处理器
pub struct InventoryEventHandler {}

impl InventoryEventHandler {
    #[instrument(skip(self))]
    pub async fn on_payment_completed(&self, event: DomainEvent) {
        if let DomainEvent::PaymentCompleted { order_id, .. } = event {
            info!(order_id = %order_id, "Received PaymentCompleted, reserving stock");
            
            // 预留库存
            // match inventory_service.reserve(...).await {
            //     Ok(reservation_id) => publish(StockReserved),
            //     Err(e) => publish(StockReservationFailed) -> 触发补偿
            // }
        }
    }
    
    #[instrument(skip(self))]
    pub async fn on_payment_failed(&self, event: DomainEvent) {
        if let DomainEvent::PaymentFailed { order_id, .. } = event {
            info!(order_id = %order_id, "Received PaymentFailed, cancelling order");
            // 取消订单
        }
    }
}
```

**Choreography 的挑战**:

- ❌ 难以追踪整体 Saga 执行状态
- ❌ 循环依赖 (A → B → A)
- ❌ 难以调试和监控

**推荐**: 使用 **Orchestration** 模式

---

## ⚠️ 故障处理与补偿

### 补偿策略

```rust
// src/saga/compensator.rs
use tracing::{instrument, warn, error};
use anyhow::Result;
use std::time::Duration;

/// 补偿重试策略
pub struct CompensationRetry {
    max_retries: u32,
    backoff: Duration,
}

impl CompensationRetry {
    pub fn new(max_retries: u32, backoff: Duration) -> Self {
        Self { max_retries, backoff }
    }
    
    /// 执行补偿 (带重试)
    #[instrument(skip(self, compensate_fn), fields(max_retries = self.max_retries))]
    pub async fn execute<F, Fut>(&self, compensate_fn: F) -> Result<()>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<()>>,
    {
        let mut attempt = 0;
        
        loop {
            attempt += 1;
            
            match compensate_fn().await {
                Ok(_) => {
                    if attempt > 1 {
                        warn!(attempt = attempt, "Compensation succeeded after retry");
                    }
                    return Ok(());
                }
                Err(e) if attempt >= self.max_retries => {
                    error!(
                        attempt = attempt,
                        error = %e,
                        "Compensation failed after max retries"
                    );
                    return Err(e);
                }
                Err(e) => {
                    warn!(
                        attempt = attempt,
                        max_retries = self.max_retries,
                        error = %e,
                        "Compensation failed, retrying..."
                    );
                    tokio::time::sleep(self.backoff * attempt).await;
                }
            }
        }
    }
}

/// 死信队列 (补偿失败后)
pub struct DeadLetterQueue {}

impl DeadLetterQueue {
    #[instrument]
    pub async fn send_failed_compensation(&self, saga_id: &str, step: &str, error: &str) {
        error!(
            saga_id = %saga_id,
            step = step,
            error = error,
            "Sending to DLQ - MANUAL INTERVENTION REQUIRED"
        );
        
        // 发送到死信队列 (Kafka/RabbitMQ)
        // 或者发送告警 (PagerDuty/Slack)
    }
}
```

**补偿失败处理**:

1. **自动重试** (指数退避)
2. **死信队列** (人工介入)
3. **告警** (PagerDuty/Slack)
4. **补偿日志** (审计)

---

## 🚀 生产部署

### Cargo.toml

```toml
[package]
name = "saga_example"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Async Runtime
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web Framework
axum = "0.7"

# Database
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "uuid", "chrono"] }

# OpenTelemetry (OTLP)
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Error Handling
anyhow = "1.0"
thiserror = "2.0"

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }

# Random (for demo)
rand = "0.8"

# Message Queue (optional)
rdkafka = { version = "0.36", features = ["tokio"], optional = true }

[features]
default = []
choreography = ["rdkafka"]

[dev-dependencies]
mockall = "0.13"
```

### Docker Compose

```yaml
# docker-compose.yml
version: '3.9'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: saga_db
      POSTGRES_USER: saga_user
      POSTGRES_PASSWORD: saga_pass
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data
      - ./init.sql:/docker-entrypoint-initdb.d/init.sql

  jaeger:
    image: jaegertracing/all-in-one:1.62
    environment:
      COLLECTOR_OTLP_ENABLED: true
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP

  saga-app:
    build: .
    environment:
      DATABASE_URL: postgres://saga_user:saga_pass@postgres:5432/saga_db
      OTLP_ENDPOINT: http://jaeger:4317
      RUST_LOG: info,saga_example=debug
  ports:
      - "8080:8080"
    depends_on:
      - postgres
      - jaeger

volumes:
  postgres_data:
```

**数据库初始化** (`init.sql`):

```sql
-- init.sql
CREATE TABLE IF NOT EXISTS orders (
    id VARCHAR(255) PRIMARY KEY,
    user_id VARCHAR(255) NOT NULL,
    amount DECIMAL(10, 2) NOT NULL,
    status VARCHAR(50) NOT NULL,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE INDEX idx_orders_user_id ON orders(user_id);
CREATE INDEX idx_orders_status ON orders(status);
```

---

## ✅ 最佳实践

### Saga 设计

1. **幂等性** ✅
   - 所有正向事务和补偿事务必须幂等
   - 使用唯一 ID (saga_id, request_id)

2. **补偿必须成功** ✅
   - 补偿失败需要重试机制
   - 最终写入死信队列 + 人工介入

3. **避免循环依赖** ✅
   - Orchestration 模式天然避免
   - Choreography 需要设计事件流向图

4. **超时处理** ✅

   ```rust
   tokio::time::timeout(
       Duration::from_secs(30),
       step.execute(ctx)
   ).await??;
   ```

### OTLP 集成

1. **Saga Root Span** ✅

   ```rust
   #[instrument(
       name = "saga.place_order",
       fields(
           saga.id = %ctx.saga_id,
           saga.type = "orchestration"
       )
   )]
   ```

2. **Step Spans** ✅
   - 每个步骤独立 Span (parent = root)
   - 记录 `saga.step`, `saga.step_index`

3. **Compensation Spans** ✅

   ```rust
       fields(
       saga.step = "compensate",
       saga.compensate_for = "step_name",
       saga.original_span_id = "xxx"
   )
   ```

4. **Custom Events** ✅

   ```rust
   Span::current().add_event(
       "saga.step.failed",
       vec![
           KeyValue::new("error", error.to_string()),
           KeyValue::new("retry_count", 3)
       ]
   );
   ```

### 故障恢复

1. **状态持久化** ✅
   - 将 Saga 状态写入数据库
   - 支持崩溃后恢复

2. **重试策略** ✅
   - 指数退避
   - 最大重试次数

3. **监控告警** ✅
   - Saga 失败率
   - 补偿成功率
   - 执行时长

---

**📊 Saga 模式 - 构建可靠的分布式事务系统！**

**下一篇**: `Actix-web 4.9 OTLP 完整集成指南` (Week 2)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0
