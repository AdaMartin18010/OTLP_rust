//! Saga 事务模式演示示例
//!
//! 本示例展示如何使用 Saga 模式处理分布式事务，包括：
//! - 事务步骤定义
//! - 自动补偿机制
//! - 成功和失败场景
//!
//! # 运行示例
//!
//! ```bash
//! cargo run --example saga_transaction_demo
//! ```

use async_trait::async_trait;
use reliability::distributed_systems::transaction::{
    DistributedTransaction, SagaConfig, SagaCoordinator, SagaOrchestrationMode, StepResult,
    TransactionContext, TransactionStep,
};
use reliability::error_handling::{ErrorContext, ErrorSeverity, UnifiedError};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    println!("=== Saga 事务模式演示 ===\n");

    // 示例 1: 成功的 Saga 事务
    demo_1_successful_saga().await?;

    println!("\n{}", "=".repeat(70));

    // 示例 2: 失败并自动补偿
    demo_2_compensation_saga().await?;

    println!("\n{}", "=".repeat(70));

    // 示例 3: 电商订单场景
    demo_3_ecommerce_order().await?;

    Ok(())
}

/// 示例 1: 成功的 Saga 事务
async fn demo_1_successful_saga() -> Result<(), UnifiedError> {
    println!("📝 示例 1: 成功的 Saga 事务\n");

    let config = SagaConfig {
        orchestration_mode: SagaOrchestrationMode::Orchestration,
        auto_compensate: true,
        max_retries: 3,
        parallel_execution: false,
        timeout_ms: 5000,
    };

    let mut coordinator = SagaCoordinator::new(config);

    // 添加事务步骤
    coordinator.add_step(Box::new(Step1Success));
    coordinator.add_step(Box::new(Step2Success));
    coordinator.add_step(Box::new(Step3Success));

    println!("🎯 场景: 简单的三步骤事务\n");
    println!("步骤:");
    println!("  1. Step1Success - 执行步骤 1");
    println!("  2. Step2Success - 执行步骤 2");
    println!("  3. Step3Success - 执行步骤 3");

    println!("\n开始执行...\n");

    // 开始事务
    let tx_id = coordinator.begin().await?;
    println!("📋 事务 ID: {:?}", tx_id);

    // 提交事务
    match coordinator.commit(&tx_id).await {
        Ok(_) => {
            println!("\n✅ 事务成功提交！");
            println!("   所有步骤都执行成功");
        }
        Err(e) => {
            println!("\n❌ 事务失败: {}", e);
        }
    }

    Ok(())
}

/// 示例 2: 失败并自动补偿
async fn demo_2_compensation_saga() -> Result<(), UnifiedError> {
    println!("📝 示例 2: 失败并自动补偿\n");

    let config = SagaConfig {
        orchestration_mode: SagaOrchestrationMode::Orchestration,
        auto_compensate: true,
        max_retries: 3,
        parallel_execution: false,
        timeout_ms: 5000,
    };

    let mut coordinator = SagaCoordinator::new(config);

    // 添加步骤，其中 Step2 会失败
    coordinator.add_step(Box::new(Step1Success));
    coordinator.add_step(Box::new(Step2Failure)); // 这一步会失败
    coordinator.add_step(Box::new(Step3Success));

    println!("🎯 场景: 中间步骤失败，触发补偿\n");
    println!("步骤:");
    println!("  1. Step1Success - 执行成功 ✅");
    println!("  2. Step2Failure - 执行失败 ❌ (触发补偿)");
    println!("  3. Step3Success - 不会执行");

    println!("\n开始执行...\n");

    let tx_id = coordinator.begin().await?;

    match coordinator.commit(&tx_id).await {
        Ok(_) => {
            println!("\n✅ 事务成功");
        }
        Err(e) => {
            println!("\n⚠️  事务执行失败: {}", e);
            println!("\n🔄 自动补偿流程:");
            println!("   1. 检测到 Step2 失败");
            println!("   2. 回滚 Step1 (调用 compensate)");
            println!("   3. 事务状态: 已回滚");
            println!("\n✅ 系统恢复到事务前状态");
        }
    }

    Ok(())
}

/// 示例 3: 电商订单场景
async fn demo_3_ecommerce_order() -> Result<(), UnifiedError> {
    println!("📝 示例 3: 电商订单 Saga 事务\n");

    println!("🛒 场景: 用户下单购买商品\n");

    // 共享状态
    let shared_state = Arc::new(RwLock::new(OrderState {
        user_balance: 1000,
        inventory: 50,
        order_created: false,
        payment_processed: false,
        inventory_reduced: false,
    }));

    let config = SagaConfig {
        orchestration_mode: SagaOrchestrationMode::Orchestration,
        auto_compensate: true,
        max_retries: 3,
        parallel_execution: false,
        timeout_ms: 5000,
    };

    let mut coordinator = SagaCoordinator::new(config);

    // 添加订单处理步骤
    coordinator.add_step(Box::new(CreateOrderStep::new(shared_state.clone())));
    coordinator.add_step(Box::new(ProcessPaymentStep::new(shared_state.clone(), 100)));
    coordinator.add_step(Box::new(ReduceInventoryStep::new(shared_state.clone(), 1)));

    println!("初始状态:");
    {
        let state = shared_state.read().await;
        println!("  用户余额: ${}", state.user_balance);
        println!("  商品库存: {}", state.inventory);
    }

    println!("\n事务步骤:");
    println!("  1. 创建订单");
    println!("  2. 处理支付 ($100)");
    println!("  3. 减少库存 (1件)");

    println!("\n开始执行...\n");

    let tx_id = coordinator.begin().await?;

    match coordinator.commit(&tx_id).await {
        Ok(_) => {
            println!("\n✅ 订单处理成功！\n");

            let state = shared_state.read().await;
            println!("最终状态:");
            println!("  用户余额: ${}", state.user_balance);
            println!("  商品库存: {}", state.inventory);
            println!("  订单状态: 已创建");
            println!("  支付状态: 已完成");
        }
        Err(e) => {
            println!("\n❌ 订单处理失败: {}", e);
            println!("\n已自动回滚所有操作");

            let state = shared_state.read().await;
            println!("\n回滚后状态:");
            println!("  用户余额: ${}", state.user_balance);
            println!("  商品库存: {}", state.inventory);
        }
    }

    println!("\n💡 Saga 模式优势:");
    println!("  ✅ 最终一致性");
    println!("  ✅ 自动补偿机制");
    println!("  ✅ 适合长事务");
    println!("  ✅ 无需分布式锁");

    Ok(())
}

// ============================================================================
// 简单的测试步骤
// ============================================================================

struct Step1Success;
struct Step2Success;
struct Step3Success;
struct Step2Failure;

#[async_trait]
impl TransactionStep for Step1Success {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  ▶ Step1Success: 执行中...");
        println!("  ✅ Step1Success: 完成");
        Ok(StepResult::Success {
            data: HashMap::new(),
        })
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  ◀ Step1Success: 补偿回滚");
        Ok(())
    }

    fn name(&self) -> &str {
        "Step1Success"
    }
}

#[async_trait]
impl TransactionStep for Step2Success {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  ▶ Step2Success: 执行中...");
        println!("  ✅ Step2Success: 完成");
        Ok(StepResult::Success {
            data: HashMap::new(),
        })
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  ◀ Step2Success: 补偿回滚");
        Ok(())
    }

    fn name(&self) -> &str {
        "Step2Success"
    }
}

#[async_trait]
impl TransactionStep for Step3Success {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  ▶ Step3Success: 执行中...");
        println!("  ✅ Step3Success: 完成");
        Ok(StepResult::Success {
            data: HashMap::new(),
        })
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  ◀ Step3Success: 补偿回滚");
        Ok(())
    }

    fn name(&self) -> &str {
        "Step3Success"
    }
}

#[async_trait]
impl TransactionStep for Step2Failure {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  ▶ Step2Failure: 执行中...");
        println!("  ❌ Step2Failure: 失败！");
        Err(UnifiedError::new(
            "Simulated failure in Step2",
            ErrorSeverity::Medium,
            "saga",
            ErrorContext::new(
                "saga",
                "Step2Failure::execute",
                file!(),
                line!(),
                ErrorSeverity::Medium,
                "saga_demo",
            ),
        ))
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  ◀ Step2Failure: 补偿回滚");
        Ok(())
    }

    fn name(&self) -> &str {
        "Step2Failure"
    }
}

// ============================================================================
// 电商订单场景的步骤实现
// ============================================================================

#[derive(Debug)]
struct OrderState {
    user_balance: i32,
    inventory: i32,
    order_created: bool,
    payment_processed: bool,
    inventory_reduced: bool,
}

struct CreateOrderStep {
    state: Arc<RwLock<OrderState>>,
}

impl CreateOrderStep {
    fn new(state: Arc<RwLock<OrderState>>) -> Self {
        Self { state }
    }
}

#[async_trait]
impl TransactionStep for CreateOrderStep {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  📝 创建订单...");
        let mut state = self.state.write().await;
        state.order_created = true;
        println!("  ✅ 订单创建成功");
        Ok(StepResult::Success {
            data: HashMap::new(),
        })
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  🔄 取消订单...");
        let mut state = self.state.write().await;
        state.order_created = false;
        println!("  ✅ 订单已取消");
        Ok(())
    }

    fn name(&self) -> &str {
        "CreateOrder"
    }
}

struct ProcessPaymentStep {
    state: Arc<RwLock<OrderState>>,
    amount: i32,
}

impl ProcessPaymentStep {
    fn new(state: Arc<RwLock<OrderState>>, amount: i32) -> Self {
        Self { state, amount }
    }
}

#[async_trait]
impl TransactionStep for ProcessPaymentStep {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  💳 处理支付 ${}...", self.amount);

        let mut state = self.state.write().await;

        if state.user_balance >= self.amount {
            state.user_balance -= self.amount;
            state.payment_processed = true;
            println!("  ✅ 支付成功，剩余余额: ${}", state.user_balance);
            Ok(StepResult::Success {
                data: HashMap::new(),
            })
        } else {
            println!("  ❌ 余额不足");
            Err(UnifiedError::new(
                "Insufficient balance",
                ErrorSeverity::High,
                "payment",
                ErrorContext::new(
                    "payment",
                    "ProcessPaymentStep::execute",
                    file!(),
                    line!(),
                    ErrorSeverity::High,
                    "saga_demo",
                ),
            ))
        }
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  🔄 退款 ${}...", self.amount);
        let mut state = self.state.write().await;
        state.user_balance += self.amount;
        state.payment_processed = false;
        println!("  ✅ 退款成功，余额: ${}", state.user_balance);
        Ok(())
    }

    fn name(&self) -> &str {
        "ProcessPayment"
    }
}

struct ReduceInventoryStep {
    state: Arc<RwLock<OrderState>>,
    quantity: i32,
}

impl ReduceInventoryStep {
    fn new(state: Arc<RwLock<OrderState>>, quantity: i32) -> Self {
        Self { state, quantity }
    }
}

#[async_trait]
impl TransactionStep for ReduceInventoryStep {
    async fn execute(&mut self, _ctx: &TransactionContext) -> Result<StepResult, UnifiedError> {
        println!("  📦 减少库存 {}件...", self.quantity);

        let mut state = self.state.write().await;

        if state.inventory >= self.quantity {
            state.inventory -= self.quantity;
            state.inventory_reduced = true;
            println!("  ✅ 库存已减少，剩余: {}", state.inventory);
            Ok(StepResult::Success {
                data: HashMap::new(),
            })
        } else {
            println!("  ❌ 库存不足");
            Err(UnifiedError::new(
                "Insufficient inventory",
                ErrorSeverity::High,
                "inventory",
                ErrorContext::new(
                    "inventory",
                    "ReduceInventoryStep::execute",
                    file!(),
                    line!(),
                    ErrorSeverity::High,
                    "saga_demo",
                ),
            ))
        }
    }

    async fn compensate(&mut self, _ctx: &TransactionContext) -> Result<(), UnifiedError> {
        println!("  🔄 恢复库存 {}件...", self.quantity);
        let mut state = self.state.write().await;
        state.inventory += self.quantity;
        state.inventory_reduced = false;
        println!("  ✅ 库存已恢复，总库存: {}", state.inventory);
        Ok(())
    }

    fn name(&self) -> &str {
        "ReduceInventory"
    }
}
