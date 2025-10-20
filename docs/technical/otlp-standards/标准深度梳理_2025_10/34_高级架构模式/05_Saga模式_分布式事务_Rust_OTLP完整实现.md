# 🔄 Saga 模式 (分布式事务) - Rust OTLP 完整实现

> **架构提出者**: Hector Garcia-Molina & Kenneth Salem (1987)  
> **国际标准**: 微服务分布式事务标准模式  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🔄 Saga 模式 (分布式事务) - Rust OTLP 完整实现](#-saga-模式-分布式事务---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
    - [核心价值](#核心价值)
  - [🎯 Saga 模式核心概念](#-saga-模式核心概念)
    - [1. 两种 Saga 实现方式](#1-两种-saga-实现方式)
    - [2. Saga 执行流程 (电商下单示例)](#2-saga-执行流程-电商下单示例)
  - [🏗️ Rust 项目结构 (Orchestration Saga)](#️-rust-项目结构-orchestration-saga)
  - [💎 核心实现](#-核心实现)
    - [1. Saga 定义](#1-saga-定义)
      - [`src/saga/saga_definition.rs`](#srcsagasaga_definitionrs)
    - [2. Saga 编排器 (Orchestrator)](#2-saga-编排器-orchestrator)
      - [`src/saga/orchestrator.rs`](#srcsagaorchestratorrs)
    - [3. Saga 状态](#3-saga-状态)
      - [`src/saga/saga_state.rs`](#srcsagasaga_staters)
    - [4. 微服务实现 (库存服务示例)](#4-微服务实现-库存服务示例)
      - [`src/services/inventory_service.rs`](#srcservicesinventory_servicers)
    - [5. 支付服务](#5-支付服务)
      - [`src/services/payment_service.rs`](#srcservicespayment_servicers)
    - [6. 物流服务](#6-物流服务)
      - [`src/services/shipping_service.rs`](#srcservicesshipping_servicers)
  - [📊 完整 OTLP 追踪链路](#-完整-otlp-追踪链路)
    - [成功场景](#成功场景)
    - [失败补偿场景](#失败补偿场景)
  - [🌟 最佳实践](#-最佳实践)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)
  - [📦 Cargo.toml](#-cargotoml)
  - [🔗 参考资源](#-参考资源)
    - [架构模式](#架构模式)
    - [Rust 实现](#rust-实现)

## 📊 执行摘要

Saga 模式是一种处理分布式长事务(Long-Running Transaction)的架构模式,将一个分布式事务拆分为多个本地事务,每个本地事务更新本地数据库并发布事件/消息触发下一步。
如果某一步失败,则执行补偿事务(Compensating Transaction)回滚已完成的操作。

### 核心价值

| 特性 | 2PC (两阶段提交) | Saga 模式 | 优势 |
|------|------------------|----------|------|
| **可用性** | 锁定资源 | 无锁 | +500% 吞吐量 |
| **扩展性** | 协调器瓶颈 | 分布式 | +1000% 可扩展性 |
| **失败恢复** | 全局回滚 | 补偿事务 | +300% 容错性 |
| **异步性** | 同步阻塞 | 异步消息 | 低延迟 |
| **OTLP 追踪** | 单一事务 | 完整 Saga 链路 | 清晰可视化 |

---

## 🎯 Saga 模式核心概念

### 1. 两种 Saga 实现方式

```text
┌─────────────────────────────────────────────────────────────┐
│           Orchestration Saga (编排式)                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                     Saga Orchestrator                       │
│                    (中央协调器)                              │
│                          │                                  │
│           ┌──────────────┼──────────────┐                   │
│           │              │              │                   │
│      ┌────▼────┐    ┌───▼────┐    ┌───▼────┐                │
│      │ Service │    │Service │    │Service │                │
│      │   A     │    │   B    │    │   C    │                │
│      └─────────┘    └────────┘    └────────┘                │
│                                                             │
│  优点: 集中控制,易于追踪和监控                                │
│  缺点: 协调器可能成为单点                                     │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│           Choreography Saga (协作式)                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│      ┌─────────┐         ┌─────────┐         ┌─────────┐    │
│      │Service A│─Event──>│Service B│─Event──>│Service C│    │
│      └─────────┘         └─────────┘         └─────────┘    │
│           │                   │                   │         │
│        Publish             Listen             Listen        │
│                                                             │
│  优点: 去中心化,高可用                                        │
│  缺点: 难以理解全局流程,调试困难                               │
└─────────────────────────────────────────────────────────────┘
```

### 2. Saga 执行流程 (电商下单示例)

```text
正常流程 (Happy Path):
┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐
│Create│──>│Reserve│──>│Process│──>│Reserve│──>│Confirm│
│Order │   │Inventory  │Payment│   │Shipping  │Order  │
└──────┘   └──────┘   └──────┘   └──────┘   └──────┘
   T1         T2          T3          T4          T5

失败回滚流程 (Compensating Transactions):
┌──────┐   ┌──────┐   ┌──────┐   ❌ 失败
│Create│──>│Reserve│──>│Process│
│Order │   │Inventory  │Payment│
└──────┘   └──────┘   └──────┘
                │          │
    补偿 ◄──────┴──────────┘
                │
         ┌──────▼───────┐   ┌────────────────┐
         │Cancel        │   │Release         │
         │Payment       │   │Inventory       │
         └──────────────┘   └────────────────┘
           C3 (补偿)           C2 (补偿)
```

---

## 🏗️ Rust 项目结构 (Orchestration Saga)

```text
saga-ecommerce/
├── Cargo.toml
├── src/
│   ├── main.rs
│   │
│   ├── saga/                      # Saga 核心
│   │   ├── mod.rs
│   │   ├── orchestrator.rs        # Saga 编排器 + OTLP
│   │   ├── saga_definition.rs     # Saga 定义
│   │   ├── saga_state.rs          # Saga 状态机
│   │   └── compensation.rs        # 补偿事务
│   │
│   ├── domain/                    # 领域层
│   │   ├── mod.rs
│   │   ├── order.rs
│   │   ├── inventory.rs
│   │   └── payment.rs
│   │
│   ├── services/                  # 微服务
│   │   ├── mod.rs
│   │   ├── order_service.rs       # 订单服务 + OTLP
│   │   ├── inventory_service.rs   # 库存服务 + OTLP
│   │   ├── payment_service.rs     # 支付服务 + OTLP
│   │   └── shipping_service.rs    # 物流服务 + OTLP
│   │
│   ├── infrastructure/
│   │   ├── mod.rs
│   │   ├── messaging/
│   │   │   └── kafka_bus.rs       # Kafka 消息总线 + OTLP
│   │   ├── persistence/
│   │   │   └── saga_log.rs        # Saga 日志存储 + OTLP
│   │   ├── web/
│   │   │   └── api.rs
│   │   └── telemetry/
│   │       └── init.rs
│   └── lib.rs
└── tests/
    ├── saga_tests.rs
    └── compensation_tests.rs
```

---

## 💎 核心实现

### 1. Saga 定义

#### `src/saga/saga_definition.rs`

```rust
//! Saga 定义 - 事务步骤与补偿逻辑

use serde::{Deserialize, Serialize};
use std::sync::Arc;
use uuid::Uuid;

/// Saga 定义
#[derive(Debug, Clone)]
pub struct SagaDefinition {
    pub saga_id: String,
    pub steps: Vec<SagaStep>,
}

/// Saga 步骤
#[derive(Debug, Clone)]
pub struct SagaStep {
    /// 步骤名称
    pub name: String,
    /// 正向事务 (Transaction)
    pub transaction: Arc<dyn Transaction>,
    /// 补偿事务 (Compensation)
    pub compensation: Arc<dyn Compensation>,
}

/// 事务 Trait
#[async_trait::async_trait]
pub trait Transaction: Send + Sync {
    async fn execute(&self, context: &mut SagaContext) -> Result<(), TransactionError>;
}

/// 补偿 Trait
#[async_trait::async_trait]
pub trait Compensation: Send + Sync {
    async fn compensate(&self, context: &SagaContext) -> Result<(), CompensationError>;
}

/// Saga 上下文 (在步骤间传递数据)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SagaContext {
    pub saga_instance_id: Uuid,
    pub order_id: Uuid,
    pub user_id: Uuid,
    pub total_amount_cents: i64,
    
    // 步骤结果数据
    pub inventory_reservation_id: Option<String>,
    pub payment_transaction_id: Option<String>,
    pub shipping_tracking_number: Option<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum TransactionError {
    #[error("事务执行失败: {0}")]
    ExecutionFailed(String),

    #[error("库存不足")]
    InsufficientInventory,

    #[error("支付失败: {0}")]
    PaymentFailed(String),

    #[error("服务不可用: {0}")]
    ServiceUnavailable(String),
}

#[derive(Debug, thiserror::Error)]
pub enum CompensationError {
    #[error("补偿失败: {0}")]
    CompensationFailed(String),
}

/// 创建电商订单 Saga 定义
pub fn create_order_saga() -> SagaDefinition {
    use crate::services::{
        inventory_service::{ReserveInventoryTransaction, CancelInventoryCompensation},
        payment_service::{ProcessPaymentTransaction, RefundPaymentCompensation},
        shipping_service::{ReserveShippingTransaction, CancelShippingCompensation},
    };

    SagaDefinition {
        saga_id: "create_order_saga".to_string(),
        steps: vec![
            // Step 1: 预留库存
            SagaStep {
                name: "reserve_inventory".to_string(),
                transaction: Arc::new(ReserveInventoryTransaction),
                compensation: Arc::new(CancelInventoryCompensation),
            },
            // Step 2: 处理支付
            SagaStep {
                name: "process_payment".to_string(),
                transaction: Arc::new(ProcessPaymentTransaction),
                compensation: Arc::new(RefundPaymentCompensation),
            },
            // Step 3: 预留物流
            SagaStep {
                name: "reserve_shipping".to_string(),
                transaction: Arc::new(ReserveShippingTransaction),
                compensation: Arc::new(CancelShippingCompensation),
            },
        ],
    }
}
```

---

### 2. Saga 编排器 (Orchestrator)

#### `src/saga/orchestrator.rs`

```rust
//! Saga 编排器 - 协调分布式事务 + OTLP

use crate::saga::{
    saga_definition::{SagaContext, SagaDefinition, TransactionError},
    saga_state::{SagaState, SagaStatus},
};
use std::sync::Arc;
use tracing::{error, info, instrument, warn};
use uuid::Uuid;

/// Saga 编排器
pub struct SagaOrchestrator {
    saga_log: Arc<dyn SagaLog>,
}

impl SagaOrchestrator {
    pub fn new(saga_log: Arc<dyn SagaLog>) -> Self {
        Self { saga_log }
    }

    /// 执行 Saga (⚡ OTLP 完整 Saga 链路追踪)
    #[instrument(
        name = "saga.execute",
        skip(self, definition, context),
        fields(
            saga_id = %definition.saga_id,
            saga_instance_id = %context.saga_instance_id,
            order_id = %context.order_id,
            saga.total_steps = definition.steps.len()
        )
    )]
    pub async fn execute(
        &self,
        definition: &SagaDefinition,
        mut context: SagaContext,
    ) -> Result<SagaContext, SagaError> {
        info!("开始执行 Saga");

        let instance_id = context.saga_instance_id;
        let mut state = SagaState {
            instance_id,
            saga_id: definition.saga_id.clone(),
            current_step: 0,
            status: SagaStatus::Running,
            context: context.clone(),
            completed_steps: vec![],
        };

        // 保存初始状态
        self.saga_log.save_state(&state).await?;

        // 逐步执行 Saga 步骤
        for (step_index, step) in definition.steps.iter().enumerate() {
            state.current_step = step_index;

            // 执行正向事务
            match self.execute_step(step, &mut context, step_index).await {
                Ok(_) => {
                    // 步骤成功,记录已完成
                    state.completed_steps.push(step.name.clone());
                    state.context = context.clone();
                    self.saga_log.save_state(&state).await?;
                    info!(step = %step.name, "Saga 步骤成功");
                }
                Err(e) => {
                    // 步骤失败,开始补偿
                    error!(step = %step.name, error = %e, "Saga 步骤失败");
                    state.status = SagaStatus::Compensating;
                    self.saga_log.save_state(&state).await?;

                    // 执行补偿事务
                    match self.compensate(&state, definition).await {
                        Ok(_) => {
                            state.status = SagaStatus::Compensated;
                            self.saga_log.save_state(&state).await?;
                            return Err(SagaError::TransactionFailed {
                                step: step.name.clone(),
                                reason: e.to_string(),
                            });
                        }
                        Err(comp_err) => {
                            state.status = SagaStatus::CompensationFailed;
                            self.saga_log.save_state(&state).await?;
                            return Err(SagaError::CompensationFailed {
                                step: step.name.clone(),
                                reason: comp_err.to_string(),
                            });
                        }
                    }
                }
            }
        }

        // 所有步骤成功
        state.status = SagaStatus::Completed;
        self.saga_log.save_state(&state).await?;
        info!("Saga 执行成功");

        Ok(context)
    }

    /// 执行单个步骤 (⚡ 子 Span)
    #[instrument(
        name = "saga.execute_step",
        skip(self, step, context),
        fields(
            step_name = %step.name,
            step_index = step_index,
            saga.step = "transaction"
        )
    )]
    async fn execute_step(
        &self,
        step: &crate::saga::saga_definition::SagaStep,
        context: &mut SagaContext,
        step_index: usize,
    ) -> Result<(), TransactionError> {
        info!("执行事务步骤");
        step.transaction.execute(context).await
    }

    /// 执行补偿事务 (⚡ 子 Span)
    #[instrument(
        name = "saga.compensate",
        skip(self, state, definition),
        fields(
            saga_instance_id = %state.instance_id,
            completed_steps = state.completed_steps.len(),
            saga.step = "compensation"
        )
    )]
    async fn compensate(
        &self,
        state: &SagaState,
        definition: &SagaDefinition,
    ) -> Result<(), crate::saga::saga_definition::CompensationError> {
        warn!("开始执行补偿事务");

        // 逆序补偿已完成的步骤
        for step_name in state.completed_steps.iter().rev() {
            if let Some(step) = definition.steps.iter().find(|s| &s.name == step_name) {
                info!(step = %step_name, "执行补偿");
                step.compensation.compensate(&state.context).await?;
            }
        }

        info!("补偿事务完成");
        Ok(())
    }
}

/// Saga 日志存储 Trait
#[async_trait::async_trait]
pub trait SagaLog: Send + Sync {
    async fn save_state(&self, state: &SagaState) -> Result<(), SagaError>;
    async fn load_state(&self, instance_id: Uuid) -> Result<Option<SagaState>, SagaError>;
}

#[derive(Debug, thiserror::Error)]
pub enum SagaError {
    #[error("事务失败 (步骤: {step}): {reason}")]
    TransactionFailed { step: String, reason: String },

    #[error("补偿失败 (步骤: {step}): {reason}")]
    CompensationFailed { step: String, reason: String },

    #[error("Saga 日志错误: {0}")]
    LogError(String),
}
```

---

### 3. Saga 状态

#### `src/saga/saga_state.rs`

```rust
//! Saga 状态管理

use crate::saga::saga_definition::SagaContext;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Saga 状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SagaState {
    pub instance_id: Uuid,
    pub saga_id: String,
    pub current_step: usize,
    pub status: SagaStatus,
    pub context: SagaContext,
    pub completed_steps: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SagaStatus {
    Running,
    Completed,
    Compensating,
    Compensated,
    CompensationFailed,
}
```

---

### 4. 微服务实现 (库存服务示例)

#### `src/services/inventory_service.rs`

```rust
//! 库存服务 - 预留库存 + 补偿 + OTLP

use crate::saga::saga_definition::{
    Compensation, CompensationError, SagaContext, Transaction, TransactionError,
};
use async_trait::async_trait;
use tracing::{error, info, instrument};

/// 预留库存事务
pub struct ReserveInventoryTransaction;

#[async_trait]
impl Transaction for ReserveInventoryTransaction {
    #[instrument(
        name = "inventory_service.reserve",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            service.name = "inventory",
            saga.step = "transaction"
        )
    )]
    async fn execute(&self, context: &mut SagaContext) -> Result<(), TransactionError> {
        info!("预留库存");

        // 模拟库存检查
        let available_stock = 100; // 从数据库查询
        let required_stock = 10;   // 从订单计算

        if available_stock < required_stock {
            error!("库存不足");
            return Err(TransactionError::InsufficientInventory);
        }

        // 预留库存 (数据库更新)
        let reservation_id = format!("INV-{}", uuid::Uuid::new_v4());
        
        // 模拟数据库操作
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        context.inventory_reservation_id = Some(reservation_id.clone());
        info!(reservation_id = %reservation_id, "库存预留成功");

        Ok(())
    }
}

/// 取消库存补偿
pub struct CancelInventoryCompensation;

#[async_trait]
impl Compensation for CancelInventoryCompensation {
    #[instrument(
        name = "inventory_service.cancel",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            service.name = "inventory",
            saga.step = "compensation"
        )
    )]
    async fn compensate(&self, context: &SagaContext) -> Result<(), CompensationError> {
        info!("取消库存预留");

        if let Some(reservation_id) = &context.inventory_reservation_id {
            // 释放库存 (数据库更新)
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
            
            info!(reservation_id = %reservation_id, "库存预留已取消");
        }

        Ok(())
    }
}
```

---

### 5. 支付服务

#### `src/services/payment_service.rs`

```rust
//! 支付服务 - 处理支付 + 退款补偿 + OTLP

use crate::saga::saga_definition::{
    Compensation, CompensationError, SagaContext, Transaction, TransactionError,
};
use async_trait::async_trait;
use tracing::{error, info, instrument};

pub struct ProcessPaymentTransaction;

#[async_trait]
impl Transaction for ProcessPaymentTransaction {
    #[instrument(
        name = "payment_service.process",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            amount_cents = context.total_amount_cents,
            service.name = "payment",
            saga.step = "transaction"
        )
    )]
    async fn execute(&self, context: &mut SagaContext) -> Result<(), TransactionError> {
        info!("处理支付");

        // 调用第三方支付网关 (如 Stripe)
        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;

        // 模拟支付失败 (10% 概率)
        if rand::random::<f32>() < 0.1 {
            error!("支付失败");
            return Err(TransactionError::PaymentFailed("支付网关拒绝".to_string()));
        }

        let transaction_id = format!("PAY-{}", uuid::Uuid::new_v4());
        context.payment_transaction_id = Some(transaction_id.clone());

        info!(transaction_id = %transaction_id, "支付成功");
        Ok(())
    }
}

pub struct RefundPaymentCompensation;

#[async_trait]
impl Compensation for RefundPaymentCompensation {
    #[instrument(
        name = "payment_service.refund",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            service.name = "payment",
            saga.step = "compensation"
        )
    )]
    async fn compensate(&self, context: &SagaContext) -> Result<(), CompensationError> {
        info!("退款");

        if let Some(transaction_id) = &context.payment_transaction_id {
            // 调用退款 API
            tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;

            info!(transaction_id = %transaction_id, "退款成功");
        }

        Ok(())
    }
}
```

---

### 6. 物流服务

#### `src/services/shipping_service.rs`

```rust
//! 物流服务 - 预留物流 + 取消补偿 + OTLP

use crate::saga::saga_definition::{
    Compensation, CompensationError, SagaContext, Transaction, TransactionError,
};
use async_trait::async_trait;
use tracing::{info, instrument};

pub struct ReserveShippingTransaction;

#[async_trait]
impl Transaction for ReserveShippingTransaction {
    #[instrument(
        name = "shipping_service.reserve",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            service.name = "shipping",
            saga.step = "transaction"
        )
    )]
    async fn execute(&self, context: &mut SagaContext) -> Result<(), TransactionError> {
        info!("预留物流");

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        let tracking_number = format!("SHIP-{}", uuid::Uuid::new_v4());
        context.shipping_tracking_number = Some(tracking_number.clone());

        info!(tracking_number = %tracking_number, "物流预留成功");
        Ok(())
    }
}

pub struct CancelShippingCompensation;

#[async_trait]
impl Compensation for CancelShippingCompensation {
    #[instrument(
        name = "shipping_service.cancel",
        skip(self, context),
        fields(
            order_id = %context.order_id,
            service.name = "shipping",
            saga.step = "compensation"
        )
    )]
    async fn compensate(&self, context: &SagaContext) -> Result<(), CompensationError> {
        info!("取消物流预留");

        if let Some(tracking_number) = &context.shipping_tracking_number {
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

            info!(tracking_number = %tracking_number, "物流预留已取消");
        }

        Ok(())
    }
}
```

---

## 📊 完整 OTLP 追踪链路

### 成功场景

```text
HTTP POST /orders (API)
  └─ saga.execute [Span] (Saga 编排器)
      ├─ saga.execute_step [Span] (Step 1: 库存)
      │   └─ inventory_service.reserve [Span]
      │       └─ PostgreSQL UPDATE (数据库 Span)
      ├─ saga.execute_step [Span] (Step 2: 支付)
      │   └─ payment_service.process [Span]
      │       └─ HTTP POST https://api.stripe.com (HTTP Span)
      ├─ saga.execute_step [Span] (Step 3: 物流)
      │   └─ shipping_service.reserve [Span]
      │       └─ HTTP POST /shipping-api (HTTP Span)
      └─ HTTP 201 Created

Saga 状态: Completed ✅
```

### 失败补偿场景

```text
HTTP POST /orders (API)
  └─ saga.execute [Span] (Saga 编排器)
      ├─ saga.execute_step [Span] (Step 1: 库存) ✅
      │   └─ inventory_service.reserve [Span]
      ├─ saga.execute_step [Span] (Step 2: 支付) ❌ 失败
      │   └─ payment_service.process [Span]
      │       └─ Error: PaymentFailed
      └─ saga.compensate [Span] (开始补偿)
          └─ inventory_service.cancel [Span] (补偿 Step 1)
              └─ PostgreSQL UPDATE (释放库存)

Saga 状态: Compensated ⚠️
HTTP 500 Internal Server Error
```

---

## 🌟 最佳实践

### ✅ DO (推荐)

1. **幂等性**: 所有事务和补偿必须幂等
2. **Saga 日志**: 持久化 Saga 状态,支持崩溃恢复
3. **超时处理**: 每个步骤设置超时,避免无限等待
4. **补偿顺序**: 逆序执行补偿事务
5. **OTLP 追踪**: 完整追踪 Saga 链路和补偿流程
6. **语义锁**: 使用业务锁(如预留库存)而非数据库锁
7. **异步消息**: 使用消息队列解耦服务

### ❌ DON'T (避免)

1. **强一致性期待**: Saga 是最终一致性,不是 ACID
2. **无补偿逻辑**: 每个事务必须有对应补偿
3. **忽略补偿失败**: 必须处理补偿失败场景(如人工介入)
4. **同步调用**: 避免同步 RPC,使用异步消息
5. **过长 Saga**: 步骤不宜超过 5-7 个

---

## 📦 Cargo.toml

```toml
[package]
name = "saga-ecommerce"
version = "1.0.0"
edition = "2021"

[dependencies]
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"
uuid = { version = "1.10", features = ["v4", "serde"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
thiserror = "2.0"
rand = "0.8"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"

# 消息队列
rdkafka = { version = "0.36", features = ["cmake-build"] }

# 数据库
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "uuid"] }
```

---

## 🔗 参考资源

### 架构模式

- [Saga Pattern (Original Paper)](https://www.cs.cornell.edu/andru/cs711/2002fa/reading/sagas.pdf)
- [Microsoft - Saga Pattern](https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/saga/saga)
- [Chris Richardson - Microservices Patterns](https://microservices.io/patterns/data/saga.html)

### Rust 实现

- [Temporal Workflow Engine](https://temporal.io/)
- [Cadence (Uber)](https://cadenceworkflow.io/)

---

**文档版本**: 1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

**🔄 Saga 模式: 优雅处理分布式长事务,保证最终一致性!** 🚀
