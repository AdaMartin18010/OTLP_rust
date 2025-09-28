# 语义模型应用示例

## 概述

本文档通过具体的代码示例和实际应用场景，展示如何在OpenTelemetry Protocol (OTLP)中应用语义模型。每个示例都包含完整的代码实现和详细说明。

## 1. 基础语义模型示例

### 1.1 简单的HTTP请求跟踪

```rust
use opentelemetry::{trace::Tracer, KeyValue};
use opentelemetry_semantic_conventions as semconv;

// 创建一个简单的HTTP请求跟踪
pub fn trace_http_request() {
    let tracer = opentelemetry::global::tracer("http-service");
    
    let _span = tracer
        .span_builder("HTTP GET /api/users")
        .with_attributes(vec![
            KeyValue::new(semconv::trace::HTTP_METHOD, "GET"),
            KeyValue::new(semconv::trace::HTTP_URL, "https://api.example.com/api/users"),
            KeyValue::new(semconv::trace::HTTP_ROUTE, "/api/users"),
            KeyValue::new(semconv::trace::HTTP_STATUS_CODE, 200),
            KeyValue::new("user.id", "12345"),
        ])
        .start(&tracer);
    
    // 执行HTTP请求逻辑
    println!("处理HTTP请求...");
}
```

### 1.2 数据库操作跟踪

```rust
use opentelemetry::{trace::Tracer, KeyValue};
use opentelemetry_semantic_conventions as semconv;

// 创建一个数据库查询跟踪
pub fn trace_database_query() {
    let tracer = opentelemetry::global::tracer("database-service");
    
    let _span = tracer
        .span_builder("SELECT users")
        .with_attributes(vec![
            KeyValue::new(semconv::trace::DB_SYSTEM, "postgresql"),
            KeyValue::new(semconv::trace::DB_NAME, "ecommerce"),
            KeyValue::new(semconv::trace::DB_OPERATION, "SELECT"),
            KeyValue::new(semconv::trace::DB_STATEMENT, "SELECT * FROM users WHERE active = true"),
            KeyValue::new(semconv::trace::DB_TABLE, "users"),
        ])
        .start(&tracer);
    
    // 执行数据库查询逻辑
    println!("执行数据库查询...");
}
```

## 2. 微服务语义模型示例

### 2.1 用户服务

```rust
use opentelemetry::{trace::Tracer, KeyValue, Context};
use opentelemetry_semantic_conventions as semconv;

pub struct UserService {
    tracer: Tracer,
}

impl UserService {
    pub fn new() -> Self {
        Self {
            tracer: opentelemetry::global::tracer("user-service"),
        }
    }
    
    // 用户注册
    pub fn register_user(&self, email: &str, password: &str) -> Result<String, String> {
        let span = self.tracer
            .span_builder("user.register")
            .with_attributes(vec![
                KeyValue::new("user.email", email.to_string()),
                KeyValue::new("operation.type", "user_registration"),
                KeyValue::new("service.name", "user-service"),
                KeyValue::new("service.version", "v1.0.0"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 验证输入
        self.validate_input(email, password)?;
        
        // 检查重复
        self.check_duplicate(email)?;
        
        // 创建用户
        let user_id = self.create_user(email, password)?;
        
        // 发送欢迎邮件
        self.send_welcome_email(email)?;
        
        Ok(user_id)
    }
    
    fn validate_input(&self, email: &str, password: &str) -> Result<(), String> {
        let span = self.tracer
            .span_builder("user.validate_input")
            .with_attributes(vec![
                KeyValue::new("validation.type", "input_validation"),
                KeyValue::new("user.email", email.to_string()),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 验证逻辑
        if email.is_empty() || password.is_empty() {
            return Err("输入不能为空".to_string());
        }
        
        if !email.contains('@') {
            return Err("邮箱格式不正确".to_string());
        }
        
        Ok(())
    }
    
    fn check_duplicate(&self, email: &str) -> Result<(), String> {
        let span = self.tracer
            .span_builder("user.check_duplicate")
            .with_attributes(vec![
                KeyValue::new("db.operation", "SELECT"),
                KeyValue::new("db.table", "users"),
                KeyValue::new("user.email", email.to_string()),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 检查重复逻辑
        println!("检查用户是否已存在: {}", email);
        Ok(())
    }
    
    fn create_user(&self, email: &str, password: &str) -> Result<String, String> {
        let span = self.tracer
            .span_builder("user.create")
            .with_attributes(vec![
                KeyValue::new("db.operation", "INSERT"),
                KeyValue::new("db.table", "users"),
                KeyValue::new("user.email", email.to_string()),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 创建用户逻辑
        let user_id = format!("user_{}", uuid::Uuid::new_v4());
        println!("创建用户: {} -> {}", email, user_id);
        Ok(user_id)
    }
    
    fn send_welcome_email(&self, email: &str) -> Result<(), String> {
        let span = self.tracer
            .span_builder("email.send_welcome")
            .with_attributes(vec![
                KeyValue::new("email.type", "welcome"),
                KeyValue::new("email.recipient", email.to_string()),
                KeyValue::new("service.name", "email-service"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 发送邮件逻辑
        println!("发送欢迎邮件到: {}", email);
        Ok(())
    }
}
```

### 2.2 订单服务

```rust
use opentelemetry::{trace::Tracer, KeyValue, Context};
use opentelemetry_semantic_conventions as semconv;

pub struct OrderService {
    tracer: Tracer,
}

impl OrderService {
    pub fn new() -> Self {
        Self {
            tracer: opentelemetry::global::tracer("order-service"),
        }
    }
    
    // 创建订单
    pub fn create_order(&self, user_id: &str, items: &[OrderItem]) -> Result<String, String> {
        let span = self.tracer
            .span_builder("order.create")
            .with_attributes(vec![
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("order.item_count", items.len() as i64),
                KeyValue::new("operation.type", "order_creation"),
                KeyValue::new("service.name", "order-service"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 验证订单
        self.validate_order(user_id, items)?;
        
        // 检查库存
        self.check_inventory(items)?;
        
        // 计算价格
        let total_price = self.calculate_price(items)?;
        
        // 创建订单
        let order_id = self.create_order_record(user_id, items, total_price)?;
        
        // 更新库存
        self.update_inventory(items)?;
        
        Ok(order_id)
    }
    
    fn validate_order(&self, user_id: &str, items: &[OrderItem]) -> Result<(), String> {
        let span = self.tracer
            .span_builder("order.validate")
            .with_attributes(vec![
                KeyValue::new("validation.type", "order_validation"),
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("order.item_count", items.len() as i64),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        if items.is_empty() {
            return Err("订单不能为空".to_string());
        }
        
        for item in items {
            if item.quantity <= 0 {
                return Err("商品数量必须大于0".to_string());
            }
        }
        
        Ok(())
    }
    
    fn check_inventory(&self, items: &[OrderItem]) -> Result<(), String> {
        let span = self.tracer
            .span_builder("inventory.check")
            .with_attributes(vec![
                KeyValue::new("db.operation", "SELECT"),
                KeyValue::new("db.table", "inventory"),
                KeyValue::new("inventory.item_count", items.len() as i64),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        for item in items {
            println!("检查库存: 商品ID {}, 需要数量 {}", item.product_id, item.quantity);
        }
        
        Ok(())
    }
    
    fn calculate_price(&self, items: &[OrderItem]) -> Result<f64, String> {
        let span = self.tracer
            .span_builder("order.calculate_price")
            .with_attributes(vec![
                KeyValue::new("calculation.type", "price_calculation"),
                KeyValue::new("order.item_count", items.len() as i64),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        let mut total = 0.0;
        for item in items {
            total += item.price * item.quantity as f64;
        }
        
        span.set_attribute(KeyValue::new("order.total_price", total));
        
        Ok(total)
    }
    
    fn create_order_record(&self, user_id: &str, items: &[OrderItem], total_price: f64) -> Result<String, String> {
        let span = self.tracer
            .span_builder("order.create_record")
            .with_attributes(vec![
                KeyValue::new("db.operation", "INSERT"),
                KeyValue::new("db.table", "orders"),
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("order.total_price", total_price),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        let order_id = format!("order_{}", uuid::Uuid::new_v4());
        println!("创建订单记录: {} -> {}", user_id, order_id);
        Ok(order_id)
    }
    
    fn update_inventory(&self, items: &[OrderItem]) -> Result<(), String> {
        let span = self.tracer
            .span_builder("inventory.update")
            .with_attributes(vec![
                KeyValue::new("db.operation", "UPDATE"),
                KeyValue::new("db.table", "inventory"),
                KeyValue::new("inventory.item_count", items.len() as i64),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        for item in items {
            println!("更新库存: 商品ID {}, 减少数量 {}", item.product_id, item.quantity);
        }
        
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct OrderItem {
    pub product_id: String,
    pub quantity: u32,
    pub price: f64,
}
```

## 3. 指标和日志语义模型示例

### 3.1 性能指标

```rust
use opentelemetry::{metrics::Meter, KeyValue};
use opentelemetry_semantic_conventions as semconv;

pub struct PerformanceMetrics {
    meter: Meter,
    request_duration: opentelemetry::metrics::Histogram<f64>,
    request_count: opentelemetry::metrics::Counter<u64>,
    error_count: opentelemetry::metrics::Counter<u64>,
}

impl PerformanceMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("performance-metrics");
        
        Self {
            request_duration: meter
                .f64_histogram("http_request_duration")
                .with_description("HTTP请求持续时间")
                .with_unit("ms")
                .init(),
            
            request_count: meter
                .u64_counter("http_requests_total")
                .with_description("HTTP请求总数")
                .init(),
            
            error_count: meter
                .u64_counter("http_errors_total")
                .with_description("HTTP错误总数")
                .init(),
        }
    }
    
    // 记录HTTP请求指标
    pub fn record_http_request(&self, method: &str, route: &str, status_code: u16, duration_ms: f64) {
        let attributes = vec![
            KeyValue::new(semconv::trace::HTTP_METHOD, method.to_string()),
            KeyValue::new(semconv::trace::HTTP_ROUTE, route.to_string()),
            KeyValue::new(semconv::trace::HTTP_STATUS_CODE, status_code as i64),
            KeyValue::new("service.name", "api-service".to_string()),
        ];
        
        // 记录请求持续时间
        self.request_duration.record(duration_ms, &attributes);
        
        // 记录请求计数
        self.request_count.add(1, &attributes);
        
        // 如果是错误状态码，记录错误计数
        if status_code >= 400 {
            self.error_count.add(1, &attributes);
        }
    }
    
    // 记录数据库操作指标
    pub fn record_db_operation(&self, operation: &str, table: &str, duration_ms: f64, success: bool) {
        let attributes = vec![
            KeyValue::new(semconv::trace::DB_OPERATION, operation.to_string()),
            KeyValue::new(semconv::trace::DB_TABLE, table.to_string()),
            KeyValue::new("db.success", success),
            KeyValue::new("service.name", "database-service".to_string()),
        ];
        
        // 记录数据库操作持续时间
        self.request_duration.record(duration_ms, &attributes);
        
        // 记录操作计数
        self.request_count.add(1, &attributes);
        
        // 如果操作失败，记录错误计数
        if !success {
            self.error_count.add(1, &attributes);
        }
    }
}
```

### 3.2 结构化日志

```rust
use opentelemetry::{trace::Tracer, KeyValue};
use serde_json::{json, Value};

pub struct StructuredLogger {
    tracer: Tracer,
}

impl StructuredLogger {
    pub fn new() -> Self {
        Self {
            tracer: opentelemetry::global::tracer("structured-logger"),
        }
    }
    
    // 记录信息日志
    pub fn info(&self, message: &str, attributes: Vec<KeyValue>) {
        let span = self.tracer
            .span_builder("log.info")
            .with_attributes(attributes.clone())
            .start(&self.tracer);
        
        let _guard = opentelemetry::Context::current_with_span(span);
        
        let log_data = json!({
            "level": "INFO",
            "message": message,
            "timestamp": chrono::Utc::now().to_rfc3339(),
            "attributes": self.attributes_to_json(attributes),
        });
        
        println!("{}", serde_json::to_string_pretty(&log_data).unwrap());
    }
    
    // 记录错误日志
    pub fn error(&self, message: &str, error: &str, attributes: Vec<KeyValue>) {
        let span = self.tracer
            .span_builder("log.error")
            .with_attributes(attributes.clone())
            .start(&self.tracer);
        
        let _guard = opentelemetry::Context::current_with_span(span);
        
        let log_data = json!({
            "level": "ERROR",
            "message": message,
            "error": error,
            "timestamp": chrono::Utc::now().to_rfc3339(),
            "attributes": self.attributes_to_json(attributes),
        });
        
        eprintln!("{}", serde_json::to_string_pretty(&log_data).unwrap());
    }
    
    // 记录业务事件日志
    pub fn business_event(&self, event_type: &str, user_id: &str, details: Value) {
        let attributes = vec![
            KeyValue::new("event.type", event_type.to_string()),
            KeyValue::new("user.id", user_id.to_string()),
            KeyValue::new("service.name", "business-service".to_string()),
        ];
        
        let span = self.tracer
            .span_builder("business.event")
            .with_attributes(attributes.clone())
            .start(&self.tracer);
        
        let _guard = opentelemetry::Context::current_with_span(span);
        
        let log_data = json!({
            "level": "INFO",
            "event_type": event_type,
            "user_id": user_id,
            "details": details,
            "timestamp": chrono::Utc::now().to_rfc3339(),
            "attributes": self.attributes_to_json(attributes),
        });
        
        println!("{}", serde_json::to_string_pretty(&log_data).unwrap());
    }
    
    fn attributes_to_json(&self, attributes: Vec<KeyValue>) -> Value {
        let mut map = serde_json::Map::new();
        
        for attr in attributes {
            let value = match attr.value {
                opentelemetry::Value::String(s) => Value::String(s),
                opentelemetry::Value::Bool(b) => Value::Bool(b),
                opentelemetry::Value::I64(i) => Value::Number(i.into()),
                opentelemetry::Value::F64(f) => Value::Number(serde_json::Number::from_f64(f).unwrap_or(0.into())),
                opentelemetry::Value::Array(_) => Value::Null, // 简化处理
            };
            map.insert(attr.key.to_string(), value);
        }
        
        Value::Object(map)
    }
}
```

## 4. 完整应用示例

### 4.1 电商系统完整示例

```rust
use opentelemetry::{trace::Tracer, KeyValue, Context};
use opentelemetry_semantic_conventions as semconv;

pub struct ECommerceSystem {
    user_service: UserService,
    order_service: OrderService,
    performance_metrics: PerformanceMetrics,
    logger: StructuredLogger,
}

impl ECommerceSystem {
    pub fn new() -> Self {
        Self {
            user_service: UserService::new(),
            order_service: OrderService::new(),
            performance_metrics: PerformanceMetrics::new(),
            logger: StructuredLogger::new(),
        }
    }
    
    // 处理用户购买流程
    pub fn process_user_purchase(&self, user_id: &str, product_id: &str, quantity: u32) -> Result<String, String> {
        let tracer = opentelemetry::global::tracer("ecommerce-system");
        
        let span = tracer
            .span_builder("ecommerce.purchase")
            .with_attributes(vec![
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("product.id", product_id.to_string()),
                KeyValue::new("order.quantity", quantity as i64),
                KeyValue::new("business.operation", "user_purchase"),
            ])
            .start(&tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 记录业务事件
        self.logger.business_event(
            "purchase_started",
            user_id,
            json!({
                "product_id": product_id,
                "quantity": quantity
            })
        );
        
        // 1. 验证用户
        self.validate_user(user_id)?;
        
        // 2. 检查商品
        let product_price = self.check_product(product_id, quantity)?;
        
        // 3. 创建订单
        let order_items = vec![OrderItem {
            product_id: product_id.to_string(),
            quantity,
            price: product_price,
        }];
        
        let order_id = self.order_service.create_order(user_id, &order_items)?;
        
        // 4. 处理支付
        self.process_payment(user_id, order_id, product_price * quantity as f64)?;
        
        // 记录成功事件
        self.logger.business_event(
            "purchase_completed",
            user_id,
            json!({
                "order_id": order_id,
                "product_id": product_id,
                "quantity": quantity,
                "total_price": product_price * quantity as f64
            })
        );
        
        Ok(order_id)
    }
    
    fn validate_user(&self, user_id: &str) -> Result<(), String> {
        let span = self.tracer
            .span_builder("user.validate")
            .with_attributes(vec![
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("validation.type", "user_validation"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 验证用户逻辑
        println!("验证用户: {}", user_id);
        Ok(())
    }
    
    fn check_product(&self, product_id: &str, quantity: u32) -> Result<f64, String> {
        let span = self.tracer
            .span_builder("product.check")
            .with_attributes(vec![
                KeyValue::new("product.id", product_id.to_string()),
                KeyValue::new("product.quantity", quantity as i64),
                KeyValue::new("db.operation", "SELECT"),
                KeyValue::new("db.table", "products"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 检查商品逻辑
        let price = 99.99; // 模拟价格
        println!("检查商品: {} 数量: {} 价格: {}", product_id, quantity, price);
        Ok(price)
    }
    
    fn process_payment(&self, user_id: &str, order_id: &str, amount: f64) -> Result<(), String> {
        let span = self.tracer
            .span_builder("payment.process")
            .with_attributes(vec![
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("order.id", order_id.to_string()),
                KeyValue::new("payment.amount", amount),
                KeyValue::new("payment.method", "credit_card"),
            ])
            .start(&self.tracer);
        
        let _guard = Context::current_with_span(span);
        
        // 处理支付逻辑
        println!("处理支付: 用户 {} 订单 {} 金额 {}", user_id, order_id, amount);
        Ok(())
    }
}

// 主函数示例
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OpenTelemetry
    let _tracer = opentelemetry::global::tracer("ecommerce-app");
    
    // 创建电商系统
    let ecommerce = ECommerceSystem::new();
    
    // 处理用户购买
    let result = ecommerce.process_user_purchase("user123", "product456", 2);
    
    match result {
        Ok(order_id) => println!("订单创建成功: {}", order_id),
        Err(error) => println!("订单创建失败: {}", error),
    }
    
    Ok(())
}
```

## 5. 总结

通过这些具体的代码示例，我们可以看到语义模型在实际应用中的价值：

1. **清晰的跟踪**: 每个操作都有明确的语义标签，便于理解和调试
2. **统一的格式**: 所有服务使用相同的语义约定，确保数据一致性
3. **丰富的上下文**: 通过属性提供丰富的上下文信息
4. **自动化分析**: 系统可以自动识别和分析不同类型的操作

在实际项目中，建议：

1. 从简单的语义模型开始
2. 逐步扩展到更复杂的场景
3. 遵循OpenTelemetry的标准语义约定
4. 根据业务需求定制语义标签

---

*本文档通过具体的代码示例展示了语义模型的实际应用，帮助开发者更好地理解和实现语义模型。*
