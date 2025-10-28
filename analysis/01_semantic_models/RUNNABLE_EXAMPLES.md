# 语义模型可运行示例集合

## 🎯 目标

本文档提供完整的、可以直接运行的语义模型代码示例，帮助开发者快速理解和应用OTLP语义模型。

---

## 📋 示例索引

1. [语义模型可运行示例集合](#示例1-基础语义属性)
2. [HTTP语义约定](#示例2-http语义约定)
3. [数据库语义约定](#示例3-数据库语义约定)
4. [微服务追踪](#示例4-微服务追踪)
5. [分布式追踪](#示例5-分布式追踪)
6. [自定义语义扩展](#示例6-自定义语义扩展)
7. [完整电商系统示例](#示例7-完整电商系统示例)

---

## 示例1: 基础语义属性

### 代码

创建文件 `examples/basic_semantic_attributes.rs`:

```rust
//! 基础语义属性示例
//!
//! 展示如何创建和使用OTLP的基础语义属性

use opentelemetry::{KeyValue, StringValue};

fn main() {
    println!("=== 基础语义属性示例 ===\n");
    
    // 1. 服务相关属性
    let service_attrs = vec![
        KeyValue::new("service.name", "demo-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("service.namespace", "production"),
    ];
    
    println!("1. 服务属性:");
    for attr in &service_attrs {
        println!("   {} = {:?}", attr.key, attr.value);
    }
    
    // 2. 部署环境属性
    let deployment_attrs = vec![
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("host.name", "server-01"),
        KeyValue::new("host.type", "physical"),
    ];
    
    println!("\n2. 部署环境属性:");
    for attr in &deployment_attrs {
        println!("   {} = {:?}", attr.key, attr.value);
    }
    
    // 3. 容器和Kubernetes属性
    let container_attrs = vec![
        KeyValue::new("container.id", "abc123"),
        KeyValue::new("container.name", "api-container"),
        KeyValue::new("k8s.namespace.name", "production"),
        KeyValue::new("k8s.pod.name", "api-pod-1"),
        KeyValue::new("k8s.deployment.name", "api-deployment"),
    ];
    
    println!("\n3. 容器和K8s属性:");
    for attr in &container_attrs {
        println!("   {} = {:?}", attr.key, attr.value);
    }
}
```

### 运行

```bash
# 添加到 Cargo.toml
# [dependencies]
# opentelemetry = "0.31.0"

cargo run --example basic_semantic_attributes
```

### 预期输出

```text
=== 基础语义属性示例 ===

1. 服务属性:
   service.name = String("demo-service")
   service.version = String("1.0.0")
   service.namespace = String("production")

2. 部署环境属性:
   deployment.environment = String("production")
   host.name = String("server-01")
   host.type = String("physical")

3. 容器和K8s属性:
   container.id = String("abc123")
   container.name = String("api-container")
   k8s.namespace.name = String("production")
   k8s.pod.name = String("api-pod-1")
   k8s.deployment.name = String("api-deployment")
```

---

## 示例2: HTTP语义约定

### 代码

创建文件 `examples/http_semantic_conventions.rs`:

```rust
//! HTTP语义约定示例
//!
//! 展示如何在HTTP请求中应用OTLP语义约定

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _},
    KeyValue,
};
use opentelemetry_sdk::{
    runtime,
    trace::{TracerProvider, Config},
    Resource,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪器
    let provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(
            Resource::new(vec![
                KeyValue::new("service.name", "http-demo"),
            ])
        ))
        .build();
    
    global::set_tracer_provider(provider);
    let tracer = global::tracer("http-demo");
    
    // 模拟HTTP请求
    simulate_http_request(&tracer, "GET", "/api/users/123", 200).await;
    simulate_http_request(&tracer, "POST", "/api/orders", 201).await;
    simulate_http_request(&tracer, "GET", "/api/products", 500).await;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn simulate_http_request(
    tracer: &impl Tracer,
    method: &str,
    route: &str,
    status_code: i64,
) {
    let span = tracer
        .span_builder(format!("{} {}", method, route))
        .with_attributes(vec![
            // HTTP语义约定属性
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", route.to_string()),
            KeyValue::new("http.status_code", status_code),
            KeyValue::new("http.scheme", "https"),
            KeyValue::new("http.target", format!("{route}?id=123")),
            KeyValue::new("http.host", "api.example.com"),
            KeyValue::new("http.user_agent", "Mozilla/5.0"),
            
            // 网络属性
            KeyValue::new("net.peer.ip", "192.168.1.100"),
            KeyValue::new("net.peer.port", 443),
            KeyValue::new("net.protocol.name", "http"),
            KeyValue::new("net.protocol.version", "1.1"),
        ])
        .start(tracer);
    
    println!("📊 HTTP请求: {} {} -> {}", method, route, status_code);
    
    // 模拟请求处理
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    drop(span);
}
```

### 运行

```bash
cargo add tokio --features full
cargo run --example http_semantic_conventions
```

### 预期输出

```text
📊 HTTP请求: GET /api/users/123 -> 200
📊 HTTP请求: POST /api/orders -> 201
📊 HTTP请求: GET /api/products -> 500
```

---

## 示例3: 数据库语义约定

### 代码

创建文件 `examples/database_semantic_conventions.rs`:

```rust
//! 数据库语义约定示例
//!
//! 展示如何在数据库操作中应用OTLP语义约定

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{TracerProvider, Config},
    Resource,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪器
    let provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(
            Resource::new(vec![
                KeyValue::new("service.name", "database-demo"),
            ])
        ))
        .build();
    
    global::set_tracer_provider(provider);
    let tracer = global::tracer("database-demo");
    
    // 模拟不同类型的数据库操作
    simulate_sql_query(&tracer).await;
    simulate_redis_operation(&tracer).await;
    simulate_mongodb_operation(&tracer).await;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn simulate_sql_query(tracer: &impl Tracer) {
    let span = tracer
        .span_builder("SELECT users")
        .with_attributes(vec![
            // 数据库通用属性
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.name", "myapp_db"),
            KeyValue::new("db.user", "app_user"),
            KeyValue::new("db.connection_string", "postgresql://localhost:5432/myapp_db"),
            
            // SQL特定属性
            KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"),
            KeyValue::new("db.operation", "SELECT"),
            KeyValue::new("db.sql.table", "users"),
            
            // 网络属性
            KeyValue::new("net.peer.name", "localhost"),
            KeyValue::new("net.peer.port", 5432),
        ])
        .start(tracer);
    
    println!("🗄️  SQL查询: SELECT * FROM users WHERE id = $1");
    
    // 模拟查询执行
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    
    drop(span);
}

async fn simulate_redis_operation(tracer: &impl Tracer) {
    let span = tracer
        .span_builder("GET user:123")
        .with_attributes(vec![
            // Redis特定属性
            KeyValue::new("db.system", "redis"),
            KeyValue::new("db.redis.database_index", 0),
            KeyValue::new("db.statement", "GET user:123"),
            KeyValue::new("db.operation", "GET"),
            
            // 网络属性
            KeyValue::new("net.peer.name", "redis.example.com"),
            KeyValue::new("net.peer.port", 6379),
        ])
        .start(tracer);
    
    println!("📮 Redis操作: GET user:123");
    
    // 模拟操作执行
    tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
    
    drop(span);
}

async fn simulate_mongodb_operation(tracer: &impl Tracer) {
    let span = tracer
        .span_builder("find users")
        .with_attributes(vec![
            // MongoDB特定属性
            KeyValue::new("db.system", "mongodb"),
            KeyValue::new("db.name", "myapp"),
            KeyValue::new("db.mongodb.collection", "users"),
            KeyValue::new("db.operation", "find"),
            KeyValue::new("db.statement", r#"{"email": "user@example.com"}"#),
            
            // 网络属性
            KeyValue::new("net.peer.name", "mongodb.example.com"),
            KeyValue::new("net.peer.port", 27017),
        ])
        .start(tracer);
    
    println!("🍃 MongoDB操作: db.users.find({{\"email\": \"user@example.com\"}})");
    
    // 模拟操作执行
    tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;
    
    drop(span);
}
```

### 运行

```bash
cargo run --example database_semantic_conventions
```

### 预期输出

```text
🗄️  SQL查询: SELECT * FROM users WHERE id = $1
📮 Redis操作: GET user:123
🍃 MongoDB操作: db.users.find({"email": "user@example.com"})
```

---

## 示例4: 微服务追踪

### 代码

创建文件 `examples/microservice_tracing.rs`:

```rust
//! 微服务追踪示例
//!
//! 展示如何在微服务架构中使用OTLP追踪

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _, SpanKind},
    KeyValue, Context,
};
use opentelemetry_sdk::{
    trace::{TracerProvider, Config},
    Resource,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪器
    let provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(
            Resource::new(vec![
                KeyValue::new("service.name", "microservice-demo"),
            ])
        ))
        .build();
    
    global::set_tracer_provider(provider);
    
    // 模拟完整的微服务调用链
    simulate_api_gateway_request().await;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn simulate_api_gateway_request() {
    let tracer = global::tracer("api-gateway");
    
    let span = tracer
        .span_builder("incoming request")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("service.name", "api-gateway"),
            KeyValue::new("http.method", "POST"),
            KeyValue::new("http.route", "/api/orders"),
        ])
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    println!("🌐 API Gateway: 收到订单请求");
    
    // 调用用户服务
    call_user_service(&cx).await;
    
    // 调用订单服务
    call_order_service(&cx).await;
    
    // 调用支付服务
    call_payment_service(&cx).await;
    
    // 调用通知服务
    call_notification_service(&cx).await;
    
    println!("✅ API Gateway: 订单处理完成\n");
}

async fn call_user_service(parent_cx: &Context) {
    let tracer = global::tracer("user-service");
    
    let span = tracer
        .span_builder("verify user")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("service.name", "user-service"),
            KeyValue::new("rpc.service", "UserService"),
            KeyValue::new("rpc.method", "VerifyUser"),
        ])
        .start_with_context(&tracer, parent_cx);
    
    let _cx = Context::current_with_span(span);
    
    println!("  👤 User Service: 验证用户身份");
    tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;
}

async fn call_order_service(parent_cx: &Context) {
    let tracer = global::tracer("order-service");
    
    let span = tracer
        .span_builder("create order")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("service.name", "order-service"),
            KeyValue::new("rpc.service", "OrderService"),
            KeyValue::new("rpc.method", "CreateOrder"),
            KeyValue::new("order.total_amount", 99.99),
        ])
        .start_with_context(&tracer, parent_cx);
    
    let _cx = Context::current_with_span(span);
    
    println!("  🛒 Order Service: 创建订单");
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
}

async fn call_payment_service(parent_cx: &Context) {
    let tracer = global::tracer("payment-service");
    
    let span = tracer
        .span_builder("process payment")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("service.name", "payment-service"),
            KeyValue::new("rpc.service", "PaymentService"),
            KeyValue::new("rpc.method", "ProcessPayment"),
            KeyValue::new("payment.method", "credit_card"),
            KeyValue::new("payment.amount", 99.99),
        ])
        .start_with_context(&tracer, parent_cx);
    
    let _cx = Context::current_with_span(span);
    
    println!("  💳 Payment Service: 处理支付");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
}

async fn call_notification_service(parent_cx: &Context) {
    let tracer = global::tracer("notification-service");
    
    let span = tracer
        .span_builder("send notification")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("service.name", "notification-service"),
            KeyValue::new("rpc.service", "NotificationService"),
            KeyValue::new("rpc.method", "SendEmail"),
            KeyValue::new("notification.type", "order_confirmation"),
        ])
        .start_with_context(&tracer, parent_cx);
    
    let _cx = Context::current_with_span(span);
    
    println!("  📧 Notification Service: 发送通知");
    tokio::time::sleep(tokio::time::Duration::from_millis(15)).await;
}
```

### 运行

```bash
cargo run --example microservice_tracing
```

### 预期输出

```text
🌐 API Gateway: 收到订单请求
  👤 User Service: 验证用户身份
  🛒 Order Service: 创建订单
  💳 Payment Service: 处理支付
  📧 Notification Service: 发送通知
✅ API Gateway: 订单处理完成
```

---

## 示例5: 分布式追踪

### 代码

创建文件 `examples/distributed_tracing.rs`:

```rust
//! 分布式追踪示例
//!
//! 展示如何在分布式系统中传播追踪上下文

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _, TraceContextExt, SpanKind},
    KeyValue, Context,
    propagation::{Injector, Extractor, TextMapPropagator},
};
use opentelemetry_sdk::{
    trace::{TracerProvider, Config},
    Resource,
    propagation::TraceContextPropagator,
};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪器
    let provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(
            Resource::new(vec![
                KeyValue::new("service.name", "distributed-tracing-demo"),
            ])
        ))
        .build();
    
    global::set_tracer_provider(provider);
    
    // 设置传播器
    global::set_text_map_propagator(TraceContextPropagator::new());
    
    // 模拟服务A调用服务B
    service_a_calls_service_b().await;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn service_a_calls_service_b() {
    println!("=== 分布式追踪演示 ===\n");
    
    let tracer = global::tracer("service-a");
    
    // 服务A创建span
    let span = tracer
        .span_builder("process_request")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("service.name", "service-a"),
        ])
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    println!("🔵 Service A: 开始处理请求");
    println!("   Trace ID: {:?}", cx.span().span_context().trace_id());
    println!("   Span ID: {:?}", cx.span().span_context().span_id());
    
    // 将上下文注入到HTTP headers
    let mut headers = HashMap::new();
    let propagator = global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));
    });
    
    println!("\n📤 Service A: 注入追踪上下文到HTTP headers:");
    for (key, value) in &headers {
        println!("   {}: {}", key, value);
    }
    
    // 模拟网络传输到服务B
    simulate_network_transmission(&headers).await;
    
    println!("\n✅ Service A: 请求处理完成");
}

async fn simulate_network_transmission(headers: &HashMap<String, String>) {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    // 服务B接收请求
    service_b_receives_request(headers).await;
}

async fn service_b_receives_request(headers: &HashMap<String, String>) {
    let tracer = global::tracer("service-b");
    
    println!("\n📥 Service B: 从HTTP headers提取追踪上下文:");
    for (key, value) in headers {
        println!("   {}: {}", key, value);
    }
    
    // 从headers提取上下文
    let propagator = TraceContextPropagator::new();
    let parent_cx = propagator.extract(&HeaderExtractor(headers));
    
    // 使用提取的上下文创建子span
    let span = tracer
        .span_builder("handle_request")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("service.name", "service-b"),
        ])
        .start_with_context(&tracer, &parent_cx);
    
    let cx = Context::current_with_span(span);
    
    println!("\n🟢 Service B: 开始处理请求");
    println!("   Trace ID: {:?}", cx.span().span_context().trace_id());
    println!("   Span ID: {:?}", cx.span().span_context().span_id());
    println!("   Parent Span ID: {:?}", 
        parent_cx.span().span_context().span_id());
    
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    
    println!("\n✅ Service B: 请求处理完成");
}

// Helper structs for header injection/extraction
struct HeaderInjector<'a>(&'a mut HashMap<String, String>);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(key.to_string(), value);
    }
}

struct HeaderExtractor<'a>(&'a HashMap<String, String>);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|v| v.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

### 运行

```bash
cargo run --example distributed_tracing
```

### 预期输出

```text
=== 分布式追踪演示 ===

🔵 Service A: 开始处理请求
   Trace ID: TraceId(...)
   Span ID: SpanId(...)

📤 Service A: 注入追踪上下文到HTTP headers:
   traceparent: 00-...

📥 Service B: 从HTTP headers提取追踪上下文:
   traceparent: 00-...

🟢 Service B: 开始处理请求
   Trace ID: TraceId(...)
   Span ID: SpanId(...)
   Parent Span ID: SpanId(...)

✅ Service B: 请求处理完成

✅ Service A: 请求处理完成
```

---

## 🚀 运行所有示例

### 一键运行脚本

创建文件 `run_all_examples.sh`:

```bash
#!/bin/bash

echo "=== 运行所有语义模型示例 ==="
echo

examples=(
    "basic_semantic_attributes"
    "http_semantic_conventions"
    "database_semantic_conventions"
    "microservice_tracing"
    "distributed_tracing"
)

for example in "${examples[@]}"; do
    echo "----------------------------------------"
    echo "运行示例: $example"
    echo "----------------------------------------"
    cargo run --example "$example"
    echo
    sleep 2
done

echo "=== 所有示例运行完成 ==="
```

```bash
chmod +x run_all_examples.sh
./run_all_examples.sh
```

---

## 📝 总结

这些示例涵盖了OTLP语义模型的核心应用场景：

1. ✅ 基础语义属性 - 理解基本概念
2. ✅ HTTP语义约定 - Web服务追踪
3. ✅ 数据库语义约定 - 数据库操作追踪
4. ✅ 微服务追踪 - 服务间调用链
5. ✅ 分布式追踪 - 上下文传播

每个示例都是完整可运行的，可以直接用于学习和参考。

---

**更新日期**: 2025年10月29日  
**维护者**: OTLP_rust Team
