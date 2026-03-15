//! # 电商微服务场景示例
//!
//! 展示在电商系统中如何使用 OTLP Rust 进行分布式链路追踪：
//! - 用户服务 (User Service)
//! - 订单服务 (Order Service)
//! - 支付服务 (Payment Service)
//! - 库存服务 (Inventory Service)
//! - 物流服务 (Shipping Service)

use anyhow::Result;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{sleep, Duration};
use uuid::Uuid;

/// ============================================
/// 核心遥测基础设施
/// ============================================

/// 分布式上下文 - 在微服务间传递
#[derive(Clone, Debug)]
pub struct TraceContext {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub baggage: HashMap<String, String>,
}

impl TraceContext {
    pub fn new() -> Self {
        Self {
            trace_id: Uuid::new_v4().to_string(),
            span_id: Uuid::new_v4().to_string(),
            parent_span_id: None,
            baggage: HashMap::new(),
        }
    }

    pub fn child(&self) -> Self {
        Self {
            trace_id: self.trace_id.clone(),
            span_id: Uuid::new_v4().to_string(),
            parent_span_id: Some(self.span_id.clone()),
            baggage: self.baggage.clone(),
        }
    }

    pub fn with_baggage(mut self, key: &str, value: &str) -> Self {
        self.baggage.insert(key.to_string(), value.to_string());
        self
    }
}

/// 跨度表示
#[derive(Clone, Debug)]
pub struct Span {
    pub context: TraceContext,
    pub operation_name: String,
    pub service_name: String,
    pub start_time: std::time::SystemTime,
    pub end_time: Option<std::time::SystemTime>,
    pub tags: HashMap<String, String>,
    pub logs: Vec<LogEntry>,
    pub status: SpanStatus,
}

#[derive(Clone, Debug)]
pub struct LogEntry {
    pub timestamp: std::time::SystemTime,
    pub message: String,
    pub fields: HashMap<String, String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SpanStatus {
    Ok,
    Error(String),
    Unknown,
}

impl Span {
    pub fn new(ctx: TraceContext, operation: &str, service: &str) -> Self {
        Self {
            context: ctx,
            operation_name: operation.to_string(),
            service_name: service.to_string(),
            start_time: std::time::SystemTime::now(),
            end_time: None,
            tags: HashMap::new(),
            logs: Vec::new(),
            status: SpanStatus::Unknown,
        }
    }

    pub fn tag(mut self, key: &str, value: &str) -> Self {
        self.tags.insert(key.to_string(), value.to_string());
        self
    }

    pub fn log(mut self, message: &str) -> Self {
        self.logs.push(LogEntry {
            timestamp: std::time::SystemTime::now(),
            message: message.to_string(),
            fields: HashMap::new(),
        });
        self
    }

    pub fn finish(mut self) -> Self {
        self.end_time = Some(std::time::SystemTime::now());
        self.status = SpanStatus::Ok;
        self
    }

    pub fn finish_with_error(mut self, error: &str) -> Self {
        self.end_time = Some(std::time::SystemTime::now());
        self.status = SpanStatus::Error(error.to_string());
        self
    }
}

/// 跨度导出器
#[derive(Clone)]
pub struct SpanExporter {
    sender: mpsc::UnboundedSender<Span>,
}

impl SpanExporter {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<Span>) {
        let (sender, receiver) = mpsc::unbounded_channel();
        (Self { sender }, receiver)
    }

    pub fn export(&self, span: Span) -> Result<()> {
        self.sender
            .send(span)
            .map_err(|_| anyhow::anyhow!("Failed to send span"))
    }
}

/// ============================================
/// 电商微服务实现
/// ============================================

/// 用户服务
pub struct UserService {
    exporter: SpanExporter,
    users_db: Arc<RwLock<HashMap<String, User>>>,
}

#[derive(Clone)]
struct User {
    id: String,
    name: String,
    email: String,
}

impl UserService {
    pub fn new(exporter: SpanExporter) -> Self {
        let mut users = HashMap::new();
        users.insert(
            "user_001".to_string(),
            User {
                id: "user_001".to_string(),
                name: "张三".to_string(),
                email: "zhangsan@example.com".to_string(),
            },
        );

        Self {
            exporter,
            users_db: Arc::new(RwLock::new(users)),
        }
    }

    pub async fn get_user(&self, ctx: TraceContext, user_id: &str) -> Result<User> {
        let span = Span::new(ctx.child(), "get_user", "user-service")
            .tag("user.id", user_id)
            .log("Querying user from database");

        // 模拟数据库查询延迟
        sleep(Duration::from_millis(10)).await;

        let db = self.users_db.read().await;
        match db.get(user_id) {
            Some(user) => {
                let span = span
                    .tag("user.found", "true")
                    .tag("user.name", &user.name)
                    .finish();
                self.exporter.export(span)?;
                Ok(user.clone())
            }
            None => {
                let span = span
                    .tag("user.found", "false")
                    .finish_with_error("User not found");
                self.exporter.export(span)?;
                Err(anyhow::anyhow!("User not found: {}", user_id))
            }
        }
    }

    pub async fn validate_user(&self, ctx: TraceContext, user_id: &str) -> Result<bool> {
        let span = Span::new(ctx.child(), "validate_user", "user-service")
            .tag("user.id", user_id);

        sleep(Duration::from_millis(5)).await;

        let db = self.users_db.read().await;
        let is_valid = db.contains_key(user_id);

        let span = span
            .tag("validation.result", &is_valid.to_string())
            .finish();
        self.exporter.export(span)?;

        Ok(is_valid)
    }
}

/// 库存服务
pub struct InventoryService {
    exporter: SpanExporter,
    inventory: Arc<RwLock<HashMap<String, i32>>>,
}

impl InventoryService {
    pub fn new(exporter: SpanExporter) -> Self {
        let mut inventory = HashMap::new();
        inventory.insert("SKU_001".to_string(), 100);
        inventory.insert("SKU_002".to_string(), 50);
        inventory.insert("SKU_003".to_string(), 0);

        Self {
            exporter,
            inventory: Arc::new(RwLock::new(inventory)),
        }
    }

    pub async fn check_availability(&self, ctx: TraceContext, sku: &str, quantity: i32) -> Result<bool> {
        let span = Span::new(ctx.child(), "check_availability", "inventory-service")
            .tag("sku", sku)
            .tag("requested_quantity", &quantity.to_string());

        sleep(Duration::from_millis(15)).await;

        let inventory = self.inventory.read().await;
        let available = inventory.get(sku).copied().unwrap_or(0);
        let can_fulfill = available >= quantity;

        let span = span
            .tag("available_quantity", &available.to_string())
            .tag("can_fulfill", &can_fulfill.to_string())
            .finish();
        self.exporter.export(span)?;

        Ok(can_fulfill)
    }

    pub async fn reserve_inventory(&self, ctx: TraceContext, sku: &str, quantity: i32) -> Result<String> {
        let span = Span::new(ctx.child(), "reserve_inventory", "inventory-service")
            .tag("sku", sku)
            .tag("quantity", &quantity.to_string());

        sleep(Duration::from_millis(20)).await;

        let mut inventory = self.inventory.write().await;
        let available = inventory.get(sku).copied().unwrap_or(0);

        if available >= quantity {
            inventory.insert(sku.to_string(), available - quantity);
            let reservation_id = Uuid::new_v4().to_string();
            let span = span
                .tag("reservation.id", &reservation_id)
                .tag("reservation.success", "true")
                .finish();
            self.exporter.export(span)?;
            Ok(reservation_id)
        } else {
            let span = span
                .tag("reservation.success", "false")
                .finish_with_error("Insufficient inventory");
            self.exporter.export(span)?;
            Err(anyhow::anyhow!("Insufficient inventory for SKU: {}", sku))
        }
    }

    pub async fn release_inventory(&self, ctx: TraceContext, sku: &str, quantity: i32) -> Result<()> {
        let span = Span::new(ctx.child(), "release_inventory", "inventory-service")
            .tag("sku", sku)
            .tag("quantity", &quantity.to_string());

        let mut inventory = self.inventory.write().await;
        let current = inventory.get(sku).copied().unwrap_or(0);
        inventory.insert(sku.to_string(), current + quantity);

        let span = span.finish();
        self.exporter.export(span)?;

        Ok(())
    }
}

/// 支付服务
pub struct PaymentService {
    exporter: SpanExporter,
    payments: Arc<RwLock<Vec<PaymentTransaction>>>,
}

#[derive(Clone)]
struct PaymentTransaction {
    id: String,
    order_id: String,
    amount: f64,
    status: PaymentStatus,
}

#[derive(Clone)]
enum PaymentStatus {
    Pending,
    Completed,
    Failed(String),
}

impl PaymentService {
    pub fn new(exporter: SpanExporter) -> Self {
        Self {
            exporter,
            payments: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn process_payment(
        &self,
        ctx: TraceContext,
        order_id: &str,
        amount: f64,
        payment_method: &str,
    ) -> Result<String> {
        let span = Span::new(ctx.child(), "process_payment", "payment-service")
            .tag("order.id", order_id)
            .tag("payment.amount", &amount.to_string())
            .tag("payment.method", payment_method)
            .log("Initializing payment gateway");

        // 模拟支付网关调用
        sleep(Duration::from_millis(100)).await;

        // 模拟成功率 90%
        let success = rand::random::<f32>() > 0.1;

        let mut payments = self.payments.write().await;
        let transaction_id = Uuid::new_v4().to_string();

        if success {
            payments.push(PaymentTransaction {
                id: transaction_id.clone(),
                order_id: order_id.to_string(),
                amount,
                status: PaymentStatus::Completed,
            });

            let span = span
                .tag("transaction.id", &transaction_id)
                .tag("payment.status", "completed")
                .log("Payment processed successfully")
                .finish();
            self.exporter.export(span)?;

            Ok(transaction_id)
        } else {
            payments.push(PaymentTransaction {
                id: transaction_id.clone(),
                order_id: order_id.to_string(),
                amount,
                status: PaymentStatus::Failed("Insufficient funds".to_string()),
            });

            let span = span
                .tag("transaction.id", &transaction_id)
                .tag("payment.status", "failed")
                .log("Payment failed: Insufficient funds")
                .finish_with_error("Payment declined");
            self.exporter.export(span)?;

            Err(anyhow::anyhow!("Payment processing failed"))
        }
    }
}

/// 订单服务 - 编排其他服务
pub struct OrderService {
    exporter: SpanExporter,
    user_service: UserService,
    inventory_service: InventoryService,
    payment_service: PaymentService,
    orders: Arc<RwLock<HashMap<String, Order>>>,
}

#[derive(Clone)]
struct Order {
    id: String,
    user_id: String,
    items: Vec<OrderItem>,
    total_amount: f64,
    status: OrderStatus,
}

#[derive(Clone)]
struct OrderItem {
    sku: String,
    quantity: i32,
    price: f64,
}

#[derive(Clone)]
enum OrderStatus {
    Created,
    PaymentPending,
    PaymentCompleted,
    InventoryReserved,
    Confirmed,
    Failed(String),
}

impl OrderService {
    pub fn new(
        exporter: SpanExporter,
        user_service: UserService,
        inventory_service: InventoryService,
        payment_service: PaymentService,
    ) -> Self {
        Self {
            exporter,
            user_service,
            inventory_service,
            payment_service,
            orders: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn create_order(
        &self,
        ctx: TraceContext,
        user_id: &str,
        items: Vec<(String, i32, f64)>, // (sku, quantity, price)
    ) -> Result<String> {
        let root_span = Span::new(ctx.child(), "create_order", "order-service")
            .tag("user.id", user_id)
            .tag("item.count", &items.len().to_string());

        // 1. 验证用户
        let user_ctx = ctx.child().with_baggage("flow", "user_validation");
        let user = match self.user_service.get_user(user_ctx, user_id).await {
            Ok(u) => u,
            Err(e) => {
                let span = root_span.finish_with_error(&e.to_string());
                self.exporter.export(span)?;
                return Err(e);
            }
        };

        // 2. 检查库存
        let inventory_ctx = ctx.child().with_baggage("flow", "inventory_check");
        for (sku, quantity, _) in &items {
            if !self
                .inventory_service
                .check_availability(inventory_ctx.clone(), sku, *quantity)
                .await?
            {
                let span = root_span
                    .clone()
                    .log(&format!("Inventory check failed for SKU: {}", sku))
                    .finish_with_error("Out of stock");
                self.exporter.export(span)?;
                return Err(anyhow::anyhow!("SKU {} is out of stock", sku));
            }
        }

        // 3. 创建订单
        let order_id = Uuid::new_v4().to_string();
        let total_amount: f64 = items.iter().map(|(_, qty, price)| *qty as f64 * price).sum();

        let order_items: Vec<OrderItem> = items
            .iter()
            .map(|(sku, qty, price)| OrderItem {
                sku: sku.clone(),
                quantity: *qty,
                price: *price,
            })
            .collect();

        let order = Order {
            id: order_id.clone(),
            user_id: user_id.to_string(),
            items: order_items.clone(),
            total_amount,
            status: OrderStatus::Created,
        };

        self.orders.write().await.insert(order_id.clone(), order);

        let span = root_span
            .clone()
            .tag("order.id", &order_id)
            .tag("order.amount", &total_amount.to_string())
            .tag("user.name", &user.name)
            .log("Order created");

        // 4. 预留库存
        let reserve_ctx = ctx.child().with_baggage("flow", "inventory_reservation");
        for item in &order_items {
            if let Err(e) = self
                .inventory_service
                .reserve_inventory(reserve_ctx.clone(), &item.sku, item.quantity)
                .await
            {
                // 回滚已预留的库存
                for rollback_item in order_items.iter().take_while(|i| i.sku != item.sku) {
                    let _ = self
                        .inventory_service
                        .release_inventory(reserve_ctx.clone(), &rollback_item.sku, rollback_item.quantity)
                        .await;
                }

                let span = span.finish_with_error(&e.to_string());
                self.exporter.export(span)?;
                return Err(e);
            }
        }

        // 5. 处理支付
        let payment_ctx = ctx.child().with_baggage("flow", "payment_processing");
        match self
            .payment_service
            .process_payment(payment_ctx, &order_id, total_amount, "credit_card")
            .await
        {
            Ok(transaction_id) => {
                let final_span = span
                    .tag("payment.transaction_id", &transaction_id)
                    .tag("order.status", "confirmed")
                    .log("Order confirmed")
                    .finish();
                self.exporter.export(final_span)?;

                Ok(order_id)
            }
            Err(e) => {
                // 支付失败，释放库存
                for item in &order_items {
                    let _ = self
                        .inventory_service
                        .release_inventory(reserve_ctx.clone(), &item.sku, item.quantity)
                        .await;
                }

                let span = span
                    .log("Payment failed, inventory released")
                    .finish_with_error(&e.to_string());
                self.exporter.export(span)?;

                Err(e)
            }
        }
    }
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== 电商微服务分布式追踪示例 ===\n");

    // 创建导出器和接收器
    let (exporter, mut receiver) = SpanExporter::new();

    // 启动后台任务处理导出的跨度
    let processor_handle = tokio::spawn(async move {
        let mut span_count = 0;
        while let Some(span) = receiver.recv().await {
            span_count += 1;
            println!(
                "[EXPORT] {}: {}.{} - {:?}",
                span.context.trace_id[..8].to_string(),
                span.service_name,
                span.operation_name,
                span.status
            );
        }
        span_count
    });

    // 创建服务实例
    let user_service = UserService::new(exporter.clone());
    let inventory_service = InventoryService::new(exporter.clone());
    let payment_service = PaymentService::new(exporter.clone());
    let order_service = OrderService::new(
        exporter.clone(),
        user_service,
        inventory_service,
        payment_service,
    );

    // 场景1: 成功的订单
    println!("--- 场景1: 成功的订单 ---");
    let ctx = TraceContext::new().with_baggage("scenario", "success");
    let items = vec![
        ("SKU_001".to_string(), 2, 29.99),
        ("SKU_002".to_string(), 1, 49.99),
    ];

    match order_service.create_order(ctx, "user_001", items).await {
        Ok(order_id) => println!("✅ Order created successfully: {}\n", order_id),
        Err(e) => println!("❌ Order failed: {}\n", e),
    }

    sleep(Duration::from_millis(100)).await;

    // 场景2: 库存不足
    println!("--- 场景2: 库存不足 (SKU_003 库存为0) ---");
    let ctx = TraceContext::new().with_baggage("scenario", "out_of_stock");
    let items = vec![("SKU_003".to_string(), 1, 99.99)];

    match order_service.create_order(ctx, "user_001", items).await {
        Ok(order_id) => println!("✅ Order created: {}\n", order_id),
        Err(e) => println!("❌ Expected failure: {}\n", e),
    }

    sleep(Duration::from_millis(100)).await;

    // 场景3: 用户不存在
    println!("--- 场景3: 用户不存在 ---");
    let ctx = TraceContext::new().with_baggage("scenario", "invalid_user");
    let items = vec![("SKU_001".to_string(), 1, 29.99)];

    match order_service.create_order(ctx, "nonexistent_user", items).await {
        Ok(order_id) => println!("✅ Order created: {}\n", order_id),
        Err(e) => println!("❌ Expected failure: {}\n", e),
    }

    // 关闭导出器并等待处理完成
    drop(order_service);
    drop(exporter);

    println!("--- 等待所有跨度处理完成 ---");
    match processor_handle.await {
        Ok(count) => println!("\n总计导出的跨度数: {}", count),
        Err(e) => println!("处理器错误: {}", e),
    }

    println!("\n=== 示例完成 ===");
    Ok(())
}
