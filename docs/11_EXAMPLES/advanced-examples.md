# 🚀 高级示例

**版本**: 1.0  
**最后更新**: 2025年10月26日  
**难度**: ⭐⭐⭐ 高级  
**预计时间**: 5-8小时  
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 高级示例 - 微服务、分布式追踪、性能优化和生产环境配置。

---

## 📋 目录

- [🚀 高级示例](#-高级示例)
  - [📋 目录](#-目录)
  - [🎯 高级示例概览](#-高级示例概览)
    - [示例复杂度](#示例复杂度)
    - [前置要求](#前置要求)
  - [🏗️ 微服务架构示例](#️-微服务架构示例)
    - [服务架构设计](#服务架构设计)
  - [🔗 分布式追踪示例](#-分布式追踪示例)
    - [跨服务上下文传播](#跨服务上下文传播)
  - [📊 高级指标收集](#-高级指标收集)
    - [自定义指标和聚合](#自定义指标和聚合)
  - [🔧 自定义导出器](#-自定义导出器)
    - [实现自定义后端](#实现自定义后端)
  - [⚡ 性能优化示例](#-性能优化示例)
    - [高性能配置和优化](#高性能配置和优化)
  - [🛡️ 可靠性框架集成](#️-可靠性框架集成)
    - [集成可靠性框架](#集成可靠性框架)
  - [🏭 生产环境配置](#-生产环境配置)
    - [完整生产配置](#完整生产配置)
  - [🚀 下一步](#-下一步)
    - [进阶学习路径](#进阶学习路径)
    - [实践项目](#实践项目)
    - [相关资源](#相关资源)

---

## 🎯 高级示例概览

### 示例复杂度

| 示例 | 难度 | 预计时间 | 主要技术 |
|------|------|----------|----------|
| 微服务架构 | ⭐⭐⭐⭐ | 45分钟 | 服务发现、负载均衡 |
| 分布式追踪 | ⭐⭐⭐⭐ | 40分钟 | 跨服务追踪、上下文传播 |
| 高级指标收集 | ⭐⭐⭐ | 30分钟 | 自定义指标、聚合 |
| 自定义导出器 | ⭐⭐⭐⭐⭐ | 60分钟 | 协议扩展、自定义后端 |
| 性能优化 | ⭐⭐⭐⭐ | 35分钟 | 批处理、连接池、压缩 |
| 可靠性框架集成 | ⭐⭐⭐⭐ | 50分钟 | 断路器、重试、超时 |
| 生产环境配置 | ⭐⭐⭐⭐⭐ | 60分钟 | 完整生产配置 |

### 前置要求

- ✅ 完成基础示例学习
- ✅ 了解 Rust 异步编程
- ✅ 熟悉 OpenTelemetry 概念
- ✅ 具备微服务架构经验

---

## 🏗️ 微服务架构示例

### 服务架构设计

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::trace::{Tracer, SpanKind, StatusCode};
use std::collections::HashMap;
use std::time::Duration;

// 微服务架构示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🏗️ 微服务架构示例");
    
    // 创建服务发现客户端
    let service_discovery = ServiceDiscovery::new()
        .with_consul_endpoint("http://localhost:8500")
        .with_service_registry(true);
    
    // 创建负载均衡器
    let load_balancer = LoadBalancer::new()
        .with_strategy(LoadBalancingStrategy::RoundRobin)
        .with_health_check_interval(Duration::from_secs(30));
    
    // 创建 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("microservices-demo")
        .with_service_discovery(service_discovery)
        .with_load_balancer(load_balancer)
        .build()
        .await?;
    
    // 模拟微服务调用链
    simulate_microservice_call_chain(&client).await?;
    
    Ok(())
}

// 模拟微服务调用链
async fn simulate_microservice_call_chain(
    client: &EnhancedOtlpClient,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = client.tracer("api-gateway");
    
    // API Gateway 层
    let mut gateway_span = tracer.start_with_kind("api-gateway-request", SpanKind::Server);
    gateway_span.set_attribute("service.name", "api-gateway");
    gateway_span.set_attribute("http.method", "POST");
    gateway_span.set_attribute("http.url", "/api/v1/orders");
    
    // 调用用户服务
    let user_service_result = call_user_service(&client, &gateway_span).await?;
    
    // 调用订单服务
    let order_service_result = call_order_service(&client, &gateway_span).await?;
    
    // 调用支付服务
    let payment_service_result = call_payment_service(&client, &gateway_span).await?;
    
    // 调用通知服务
    let notification_service_result = call_notification_service(&client, &gateway_span).await?;
    
    // 完成网关 Span
    if user_service_result && order_service_result && payment_service_result && notification_service_result {
        gateway_span.set_status(StatusCode::Ok, "All services completed successfully".to_string());
    } else {
        gateway_span.set_status(StatusCode::Error, "Some services failed".to_string());
    }
    gateway_span.end();
    
    Ok(())
}

// 用户服务调用
async fn call_user_service(
    client: &EnhancedOtlpClient,
    parent_span: &Span,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("user-service");
    let mut span = tracer.start_with_kind("user-service-validate", SpanKind::Client);
    
    span.set_attribute("service.name", "user-service");
    span.set_attribute("operation", "validate_user");
    span.set_attribute("user.id", "12345");
    
    // 模拟服务调用
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    // 模拟偶尔的失败
    let success = rand::random::<f64>() > 0.1;
    
    if success {
        span.set_status(StatusCode::Ok, "User validation successful".to_string());
        println!("✅ 用户服务调用成功");
    } else {
        span.set_status(StatusCode::Error, "User validation failed".to_string());
        println!("❌ 用户服务调用失败");
    }
    
    span.end();
    Ok(success)
}

// 订单服务调用
async fn call_order_service(
    client: &EnhancedOtlpClient,
    parent_span: &Span,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("order-service");
    let mut span = tracer.start_with_kind("order-service-create", SpanKind::Client);
    
    span.set_attribute("service.name", "order-service");
    span.set_attribute("operation", "create_order");
    span.set_attribute("order.amount", 99.99);
    
    // 模拟服务调用
    tokio::time::sleep(Duration::from_millis(80)).await;
    
    let success = rand::random::<f64>() > 0.05;
    
    if success {
        span.set_status(StatusCode::Ok, "Order creation successful".to_string());
        println!("✅ 订单服务调用成功");
    } else {
        span.set_status(StatusCode::Error, "Order creation failed".to_string());
        println!("❌ 订单服务调用失败");
    }
    
    span.end();
    Ok(success)
}

// 支付服务调用
async fn call_payment_service(
    client: &EnhancedOtlpClient,
    parent_span: &Span,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("payment-service");
    let mut span = tracer.start_with_kind("payment-service-process", SpanKind::Client);
    
    span.set_attribute("service.name", "payment-service");
    span.set_attribute("operation", "process_payment");
    span.set_attribute("payment.method", "credit_card");
    span.set_attribute("payment.amount", 99.99);
    
    // 模拟服务调用
    tokio::time::sleep(Duration::from_millis(120)).await;
    
    let success = rand::random::<f64>() > 0.08;
    
    if success {
        span.set_status(StatusCode::Ok, "Payment processing successful".to_string());
        println!("✅ 支付服务调用成功");
    } else {
        span.set_status(StatusCode::Error, "Payment processing failed".to_string());
        println!("❌ 支付服务调用失败");
    }
    
    span.end();
    Ok(success)
}

// 通知服务调用
async fn call_notification_service(
    client: &EnhancedOtlpClient,
    parent_span: &Span,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("notification-service");
    let mut span = tracer.start_with_kind("notification-service-send", SpanKind::Client);
    
    span.set_attribute("service.name", "notification-service");
    span.set_attribute("operation", "send_notification");
    span.set_attribute("notification.type", "email");
    
    // 模拟服务调用
    tokio::time::sleep(Duration::from_millis(30)).await;
    
    let success = rand::random::<f64>() > 0.02;
    
    if success {
        span.set_status(StatusCode::Ok, "Notification sent successfully".to_string());
        println!("✅ 通知服务调用成功");
    } else {
        span.set_status(StatusCode::Error, "Notification sending failed".to_string());
        println!("❌ 通知服务调用失败");
    }
    
    span.end();
    Ok(success)
}
```

---

## 🔗 分布式追踪示例

### 跨服务上下文传播

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::trace::{Tracer, SpanKind, StatusCode, TraceContext};
use opentelemetry::propagation::{TextMapPropagator, TraceContextPropagator};
use std::collections::HashMap;

// 分布式追踪示例
async fn distributed_tracing_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔗 分布式追踪示例");
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("distributed-tracing-demo")
        .with_trace_context_propagation(true)
        .build()
        .await?;
    
    let tracer = client.tracer("main-service");
    
    // 创建根 Span
    let mut root_span = tracer.start_with_kind("distributed-operation", SpanKind::Server);
    root_span.set_attribute("service.name", "main-service");
    root_span.set_attribute("operation.id", "distributed-op-001");
    
    // 提取追踪上下文
    let trace_context = root_span.context();
    
    // 模拟跨服务调用
    let service_a_result = call_service_a(&client, &trace_context).await?;
    let service_b_result = call_service_b(&client, &trace_context).await?;
    let service_c_result = call_service_c(&client, &trace_context).await?;
    
    // 完成根 Span
    if service_a_result && service_b_result && service_c_result {
        root_span.set_status(StatusCode::Ok, "All distributed operations completed".to_string());
    } else {
        root_span.set_status(StatusCode::Error, "Some distributed operations failed".to_string());
    }
    root_span.end();
    
    Ok(())
}

// 服务 A 调用
async fn call_service_a(
    client: &EnhancedOtlpClient,
    parent_context: &TraceContext,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("service-a");
    
    // 使用父上下文创建子 Span
    let mut span = tracer.start_with_context("service-a-operation", SpanKind::Client, parent_context);
    span.set_attribute("service.name", "service-a");
    span.set_attribute("operation", "data_processing");
    
    // 模拟处理时间
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 模拟子操作
    let sub_operation_result = perform_sub_operation(&tracer, &span.context()).await?;
    
    if sub_operation_result {
        span.set_status(StatusCode::Ok, "Service A operation successful".to_string());
        println!("✅ 服务 A 操作成功");
    } else {
        span.set_status(StatusCode::Error, "Service A operation failed".to_string());
        println!("❌ 服务 A 操作失败");
    }
    
    span.end();
    Ok(sub_operation_result)
}

// 服务 B 调用
async fn call_service_b(
    client: &EnhancedOtlpClient,
    parent_context: &TraceContext,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("service-b");
    
    let mut span = tracer.start_with_context("service-b-operation", SpanKind::Client, parent_context);
    span.set_attribute("service.name", "service-b");
    span.set_attribute("operation", "external_api_call");
    
    // 模拟外部 API 调用
    tokio::time::sleep(Duration::from_millis(150)).await;
    
    let success = rand::random::<f64>() > 0.1;
    
    if success {
        span.set_status(StatusCode::Ok, "Service B operation successful".to_string());
        println!("✅ 服务 B 操作成功");
    } else {
        span.set_status(StatusCode::Error, "Service B operation failed".to_string());
        println!("❌ 服务 B 操作失败");
    }
    
    span.end();
    Ok(success)
}

// 服务 C 调用
async fn call_service_c(
    client: &EnhancedOtlpClient,
    parent_context: &TraceContext,
) -> Result<bool, Box<dyn std::error::Error>> {
    let tracer = client.tracer("service-c");
    
    let mut span = tracer.start_with_context("service-c-operation", SpanKind::Client, parent_context);
    span.set_attribute("service.name", "service-c");
    span.set_attribute("operation", "database_operation");
    
    // 模拟数据库操作
    tokio::time::sleep(Duration::from_millis(80)).await;
    
    let success = rand::random::<f64>() > 0.05;
    
    if success {
        span.set_status(StatusCode::Ok, "Service C operation successful".to_string());
        println!("✅ 服务 C 操作成功");
    } else {
        span.set_status(StatusCode::Error, "Service C operation failed".to_string());
        println!("❌ 服务 C 操作失败");
    }
    
    span.end();
    Ok(success)
}

// 子操作示例
async fn perform_sub_operation(
    tracer: &Tracer,
    parent_context: &TraceContext,
) -> Result<bool, Box<dyn std::error::Error>> {
    let mut span = tracer.start_with_context("sub-operation", SpanKind::Internal, parent_context);
    span.set_attribute("operation.type", "data_transformation");
    
    // 模拟数据处理
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    let success = rand::random::<f64>() > 0.15;
    
    if success {
        span.set_status(StatusCode::Ok, "Sub operation successful".to_string());
    } else {
        span.set_status(StatusCode::Error, "Sub operation failed".to_string());
    }
    
    span.end();
    Ok(success)
}
```

---

## 📊 高级指标收集

### 自定义指标和聚合

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::metrics::{Meter, Counter, Histogram, Gauge, Unit};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, AtomicF64, Ordering};

// 高级指标收集示例
async fn advanced_metrics_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("📊 高级指标收集示例");
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("advanced-metrics-demo")
        .with_custom_metrics_enabled(true)
        .build()
        .await?;
    
    let meter = client.meter("advanced-metrics");
    
    // 创建复杂指标
    let metrics_collector = AdvancedMetricsCollector::new(&meter);
    
    // 模拟业务操作
    for i in 0..100 {
        metrics_collector.record_user_action("login", "web").await;
        metrics_collector.record_transaction(150.0 + i as f64, "credit_card").await;
        metrics_collector.record_api_call("/api/users", 200, Duration::from_millis(50 + i)).await;
        
        if i % 10 == 0 {
            metrics_collector.update_system_health(0.8 + (i as f64 * 0.001)).await;
        }
        
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    
    // 获取聚合指标
    let aggregated_metrics = metrics_collector.get_aggregated_metrics().await?;
    println!("📈 聚合指标: {:?}", aggregated_metrics);
    
    Ok(())
}

// 高级指标收集器
struct AdvancedMetricsCollector {
    meter: Meter,
    
    // 用户行为指标
    user_actions: Counter<u64>,
    user_sessions: Counter<u64>,
    
    // 交易指标
    transaction_count: Counter<u64>,
    transaction_amount: Histogram<f64>,
    transaction_volume: Gauge<f64>,
    
    // API 指标
    api_requests: Counter<u64>,
    api_response_time: Histogram<f64>,
    api_error_rate: Gauge<f64>,
    
    // 系统健康指标
    system_health: Gauge<f64>,
    active_users: Gauge<u64>,
    
    // 内部计数器
    total_transactions: AtomicU64,
    total_revenue: AtomicF64,
}

impl AdvancedMetricsCollector {
    fn new(meter: &Meter) -> Self {
        Self {
            meter: meter.clone(),
            
            user_actions: meter
                .u64_counter("user_actions_total")
                .with_description("Total user actions")
                .with_unit(Unit::new("1"))
                .init(),
            
            user_sessions: meter
                .u64_counter("user_sessions_total")
                .with_description("Total user sessions")
                .with_unit(Unit::new("1"))
                .init(),
            
            transaction_count: meter
                .u64_counter("transactions_total")
                .with_description("Total transactions")
                .with_unit(Unit::new("1"))
                .init(),
            
            transaction_amount: meter
                .f64_histogram("transaction_amount")
                .with_description("Transaction amount distribution")
                .with_unit(Unit::new("USD"))
                .init(),
            
            transaction_volume: meter
                .f64_gauge("transaction_volume_total")
                .with_description("Total transaction volume")
                .with_unit(Unit::new("USD"))
                .init(),
            
            api_requests: meter
                .u64_counter("api_requests_total")
                .with_description("Total API requests")
                .with_unit(Unit::new("1"))
                .init(),
            
            api_response_time: meter
                .f64_histogram("api_response_time_seconds")
                .with_description("API response time")
                .with_unit(Unit::new("s"))
                .init(),
            
            api_error_rate: meter
                .f64_gauge("api_error_rate")
                .with_description("API error rate")
                .with_unit(Unit::new("1"))
                .init(),
            
            system_health: meter
                .f64_gauge("system_health_score")
                .with_description("System health score")
                .with_unit(Unit::new("1"))
                .init(),
            
            active_users: meter
                .u64_gauge("active_users")
                .with_description("Number of active users")
                .with_unit(Unit::new("1"))
                .init(),
            
            total_transactions: AtomicU64::new(0),
            total_revenue: AtomicF64::new(0.0),
        }
    }
    
    async fn record_user_action(&self, action: &str, platform: &str) {
        let mut attributes = HashMap::new();
        attributes.insert("action".to_string(), action.into());
        attributes.insert("platform".to_string(), platform.into());
        
        self.user_actions.add(1, &attributes);
        
        // 更新活跃用户数
        self.active_users.record(100 + rand::random::<u64>() % 50, &attributes);
    }
    
    async fn record_transaction(&self, amount: f64, method: &str) {
        let mut attributes = HashMap::new();
        attributes.insert("method".to_string(), method.into());
        attributes.insert("currency".to_string(), "USD".into());
        
        self.transaction_count.add(1, &attributes);
        self.transaction_amount.record(amount, &attributes);
        
        // 更新总交易量和收入
        let total_transactions = self.total_transactions.fetch_add(1, Ordering::Relaxed) + 1;
        let total_revenue = self.total_revenue.fetch_add(amount, Ordering::Relaxed) + amount;
        
        self.transaction_volume.record(total_revenue, &attributes);
    }
    
    async fn record_api_call(&self, endpoint: &str, status_code: u16, response_time: Duration) {
        let mut attributes = HashMap::new();
        attributes.insert("endpoint".to_string(), endpoint.into());
        attributes.insert("status_code".to_string(), status_code.to_string().into());
        
        self.api_requests.add(1, &attributes);
        self.api_response_time.record(response_time.as_secs_f64(), &attributes);
        
        // 计算错误率
        let error_rate = if status_code >= 400 { 1.0 } else { 0.0 };
        self.api_error_rate.record(error_rate, &attributes);
    }
    
    async fn update_system_health(&self, health_score: f64) {
        let mut attributes = HashMap::new();
        attributes.insert("component".to_string(), "overall".into());
        
        self.system_health.record(health_score, &attributes);
    }
    
    async fn get_aggregated_metrics(&self) -> Result<AggregatedMetrics, Box<dyn std::error::Error>> {
        Ok(AggregatedMetrics {
            total_transactions: self.total_transactions.load(Ordering::Relaxed),
            total_revenue: self.total_revenue.load(Ordering::Relaxed),
            avg_transaction_amount: self.total_revenue.load(Ordering::Relaxed) / 
                                  self.total_transactions.load(Ordering::Relaxed) as f64,
            system_health_score: 0.85, // 模拟值
        })
    }
}

#[derive(Debug)]
struct AggregatedMetrics {
    total_transactions: u64,
    total_revenue: f64,
    avg_transaction_amount: f64,
    system_health_score: f64,
}
```

---

## 🔧 自定义导出器

### 实现自定义后端

```rust
use otlp::core::{Exporter, ExportResult};
use otlp::data::{SpanData, MetricData, LogData};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

// 自定义导出器示例
async fn custom_exporter_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔧 自定义导出器示例");
    
    // 创建自定义导出器
    let custom_exporter = CustomExporter::new()
        .with_endpoint("http://custom-backend:8080/api/v1/telemetry")
        .with_auth_token("your-auth-token")
        .with_batch_size(100)
        .with_timeout(Duration::from_secs(30));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("custom-exporter-demo")
        .with_custom_exporter(Box::new(custom_exporter))
        .build()
        .await?;
    
    // 使用自定义导出器
    let tracer = client.tracer("custom-exporter-test");
    let mut span = tracer.start("custom-exporter-operation");
    span.set_attribute("exporter.type", "custom");
    span.end();
    
    Ok(())
}

// 自定义导出器实现
struct CustomExporter {
    endpoint: String,
    auth_token: String,
    batch_size: usize,
    timeout: Duration,
    client: reqwest::Client,
}

impl CustomExporter {
    fn new() -> Self {
        Self {
            endpoint: String::new(),
            auth_token: String::new(),
            batch_size: 100,
            timeout: Duration::from_secs(30),
            client: reqwest::Client::new(),
        }
    }
    
    fn with_endpoint(mut self, endpoint: &str) -> Self {
        self.endpoint = endpoint.to_string();
        self
    }
    
    fn with_auth_token(mut self, token: &str) -> Self {
        self.auth_token = token.to_string();
        self
    }
    
    fn with_batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }
    
    fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}

#[async_trait]
impl Exporter for CustomExporter {
    async fn export_spans(&self, spans: Vec<SpanData>) -> Result<ExportResult, Box<dyn std::error::Error>> {
        println!("📤 导出 {} 个 Span 到自定义后端", spans.len());
        
        // 转换 Span 数据格式
        let custom_spans: Vec<CustomSpan> = spans.into_iter().map(|span| {
            CustomSpan {
                trace_id: span.trace_id,
                span_id: span.span_id,
                parent_span_id: span.parent_span_id,
                name: span.name,
                start_time: span.start_time,
                end_time: span.end_time,
                attributes: span.attributes,
                events: span.events,
                status: span.status,
            }
        }).collect();
        
        // 发送到自定义后端
        let response = self.client
            .post(&format!("{}/spans", self.endpoint))
            .header("Authorization", format!("Bearer {}", self.auth_token))
            .header("Content-Type", "application/json")
            .json(&custom_spans)
            .timeout(self.timeout)
            .send()
            .await?;
        
        if response.status().is_success() {
            println!("✅ Span 导出成功");
            Ok(ExportResult::Success)
        } else {
            println!("❌ Span 导出失败: {}", response.status());
            Ok(ExportResult::Failure)
        }
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<ExportResult, Box<dyn std::error::Error>> {
        println!("📊 导出 {} 个指标到自定义后端", metrics.len());
        
        // 转换指标数据格式
        let custom_metrics: Vec<CustomMetric> = metrics.into_iter().map(|metric| {
            CustomMetric {
                name: metric.name,
                value: metric.value,
                timestamp: metric.timestamp,
                labels: metric.labels,
                metric_type: metric.metric_type,
            }
        }).collect();
        
        // 发送到自定义后端
        let response = self.client
            .post(&format!("{}/metrics", self.endpoint))
            .header("Authorization", format!("Bearer {}", self.auth_token))
            .header("Content-Type", "application/json")
            .json(&custom_metrics)
            .timeout(self.timeout)
            .send()
            .await?;
        
        if response.status().is_success() {
            println!("✅ 指标导出成功");
            Ok(ExportResult::Success)
        } else {
            println!("❌ 指标导出失败: {}", response.status());
            Ok(ExportResult::Failure)
        }
    }
    
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<ExportResult, Box<dyn std::error::Error>> {
        println!("📝 导出 {} 条日志到自定义后端", logs.len());
        
        // 转换日志数据格式
        let custom_logs: Vec<CustomLog> = logs.into_iter().map(|log| {
            CustomLog {
                timestamp: log.timestamp,
                level: log.severity,
                message: log.body,
                attributes: log.attributes,
                resource: log.resource,
            }
        }).collect();
        
        // 发送到自定义后端
        let response = self.client
            .post(&format!("{}/logs", self.endpoint))
            .header("Authorization", format!("Bearer {}", self.auth_token))
            .header("Content-Type", "application/json")
            .json(&custom_logs)
            .timeout(self.timeout)
            .send()
            .await?;
        
        if response.status().is_success() {
            println!("✅ 日志导出成功");
            Ok(ExportResult::Success)
        } else {
            println!("❌ 日志导出失败: {}", response.status());
            Ok(ExportResult::Failure)
        }
    }
}

// 自定义数据格式
#[derive(Serialize)]
struct CustomSpan {
    trace_id: String,
    span_id: String,
    parent_span_id: Option<String>,
    name: String,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, String>,
    events: Vec<SpanEvent>,
    status: SpanStatus,
}

#[derive(Serialize)]
struct CustomMetric {
    name: String,
    value: f64,
    timestamp: u64,
    labels: HashMap<String, String>,
    metric_type: String,
}

#[derive(Serialize)]
struct CustomLog {
    timestamp: u64,
    level: String,
    message: String,
    attributes: HashMap<String, String>,
    resource: Option<HashMap<String, String>>,
}
```

---

## ⚡ 性能优化示例

### 高性能配置和优化

```rust
use otlp::core::EnhancedOtlpClient;
use otlp::config::*;
use std::time::Duration;
use tokio::task;

// 性能优化示例
async fn performance_optimization_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("⚡ 性能优化示例");
    
    // 高性能配置
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("performance-demo")
        
        // 连接优化
        .with_grpc_transport()
        .with_compression(Compression::Gzip)
        .with_connection_pool_config(ConnectionPoolConfig {
            max_connections: 200,
            min_connections: 20,
            connection_timeout: Duration::from_secs(5),
            idle_timeout: Duration::from_secs(300),
            keep_alive: true,
        })
        
        // 批处理优化
        .with_batch_config(BatchConfig {
            max_batch_size: 2000,
            batch_timeout: Duration::from_millis(100),
            max_queue_size: 50000,
            strategy: BatchStrategy::Hybrid,
        })
        
        // 重试优化
        .with_retry_config(RetryConfig {
            max_attempts: 3,
            initial_interval: Duration::from_millis(100),
            max_interval: Duration::from_secs(5),
            multiplier: 2.0,
            randomization_factor: 0.1,
            retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
        })
        
        // 内存优化
        .with_memory_pool_config(MemoryPoolConfig {
            initial_size: 1024 * 1024,      // 1MB
            max_size: 100 * 1024 * 1024,     // 100MB
            chunk_size: 64 * 1024,          // 64KB
            growth_factor: 2.0,
            gc_threshold: 0.8,
        })
        
        // 零拷贝优化
        .with_zero_copy_enabled(true)
        
        .build()
        .await?;
    
    // 性能测试
    let performance_test = PerformanceTest::new(client);
    performance_test.run_concurrent_test(1000).await?;
    performance_test.run_throughput_test(10000).await?;
    performance_test.run_latency_test(1000).await?;
    
    Ok(())
}

// 性能测试工具
struct PerformanceTest {
    client: EnhancedOtlpClient,
}

impl PerformanceTest {
    fn new(client: EnhancedOtlpClient) -> Self {
        Self { client }
    }
    
    // 并发测试
    async fn run_concurrent_test(&self, concurrent_requests: usize) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔄 运行并发测试: {} 个并发请求", concurrent_requests);
        
        let start_time = std::time::Instant::now();
        let tracer = self.client.tracer("concurrent-test");
        
        let tasks: Vec<_> = (0..concurrent_requests)
            .map(|i| {
                let tracer = tracer.clone();
                task::spawn(async move {
                    let mut span = tracer.start("concurrent-operation");
                    span.set_attribute("request.id", i);
                    
                    // 模拟工作负载
                    tokio::time::sleep(Duration::from_millis(10)).await;
                    
                    span.end();
                })
            })
            .collect();
        
        futures::future::join_all(tasks).await;
        
        let duration = start_time.elapsed();
        let throughput = concurrent_requests as f64 / duration.as_secs_f64();
        
        println!("✅ 并发测试完成:");
        println!("  总时间: {:?}", duration);
        println!("  吞吐量: {:.2} req/s", throughput);
        
        Ok(())
    }
    
    // 吞吐量测试
    async fn run_throughput_test(&self, total_requests: usize) -> Result<(), Box<dyn std::error::Error>> {
        println!("📊 运行吞吐量测试: {} 个请求", total_requests);
        
        let start_time = std::time::Instant::now();
        let tracer = self.client.tracer("throughput-test");
        
        for i in 0..total_requests {
            let mut span = tracer.start("throughput-operation");
            span.set_attribute("request.id", i);
            
            // 模拟工作负载
            tokio::time::sleep(Duration::from_millis(1)).await;
            
            span.end();
            
            if i % 1000 == 0 {
                println!("  处理了 {} 个请求", i);
            }
        }
        
        let duration = start_time.elapsed();
        let throughput = total_requests as f64 / duration.as_secs_f64();
        
        println!("✅ 吞吐量测试完成:");
        println!("  总时间: {:?}", duration);
        println!("  吞吐量: {:.2} req/s", throughput);
        
        Ok(())
    }
    
    // 延迟测试
    async fn run_latency_test(&self, sample_size: usize) -> Result<(), Box<dyn std::error::Error>> {
        println!("⏱️ 运行延迟测试: {} 个样本", sample_size);
        
        let tracer = self.client.tracer("latency-test");
        let mut latencies = Vec::new();
        
        for i in 0..sample_size {
            let start_time = std::time::Instant::now();
            
            let mut span = tracer.start("latency-operation");
            span.set_attribute("sample.id", i);
            
            // 模拟工作负载
            tokio::time::sleep(Duration::from_millis(5)).await;
            
            span.end();
            
            let latency = start_time.elapsed();
            latencies.push(latency);
        }
        
        // 计算延迟统计
        latencies.sort();
        let p50 = latencies[sample_size / 2];
        let p95 = latencies[(sample_size * 95) / 100];
        let p99 = latencies[(sample_size * 99) / 100];
        let avg = latencies.iter().sum::<Duration>() / latencies.len() as u32;
        
        println!("✅ 延迟测试完成:");
        println!("  平均延迟: {:?}", avg);
        println!("  P50延迟: {:?}", p50);
        println!("  P95延迟: {:?}", p95);
        println!("  P99延迟: {:?}", p99);
        
        Ok(())
    }
}
```

---

## 🛡️ 可靠性框架集成

### 集成可靠性框架

```rust
use otlp::core::EnhancedOtlpClient;
use reliability::prelude::*;
use std::time::Duration;

// 可靠性框架集成示例
async fn reliability_framework_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("🛡️ 可靠性框架集成示例");
    
    // 初始化可靠性框架
    reliability::init().await?;
    
    // 创建 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("reliability-demo")
        .with_reliability_framework_integration(true)
        .build()
        .await?;
    
    // 创建可靠性组件
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(10));
    let retry_policy = RetryPolicy::new()
        .with_max_attempts(3)
        .with_initial_delay(Duration::from_millis(100))
        .with_max_delay(Duration::from_secs(5))
        .with_backoff_multiplier(2.0);
    let timeout = Timeout::new(Duration::from_secs(30));
    let bulkhead = Bulkhead::new(10);
    
    // 模拟不可靠的服务调用
    for i in 0..20 {
        println!("🔄 执行操作 {}", i + 1);
        
        let result = circuit_breaker
            .execute_with_retry(&retry_policy, || {
                timeout.execute(|| {
                    bulkhead.execute(|| unreliable_service_call(i + 1))
                })
            })
            .await;
        
        match result {
            Ok(response) => println!("✅ 操作成功: {}", response),
            Err(e) => println!("❌ 操作失败: {}", e),
        }
        
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    
    // 获取可靠性指标
    let reliability_metrics = reliability::get_metrics().await?;
    println!("📊 可靠性指标: {:?}", reliability_metrics);
    
    // 关闭可靠性框架
    reliability::shutdown().await?;
    
    Ok(())
}

// 不可靠的服务调用
async fn unreliable_service_call(attempt: u32) -> Result<String, UnifiedError> {
    // 模拟各种失败情况
    let failure_rate = match attempt {
        1..=5 => 0.1,    // 前5次失败率10%
        6..=10 => 0.3,   // 中间5次失败率30%
        11..=15 => 0.5,  // 后5次失败率50%
        _ => 0.2,        // 其余失败率20%
    };
    
    if rand::random::<f64>() < failure_rate {
        let error_type = rand::random::<u32>() % 4;
        match error_type {
            0 => Err(UnifiedError::Network("Network timeout".to_string())),
            1 => Err(UnifiedError::Timeout("Operation timeout".to_string())),
            2 => Err(UnifiedError::System("Internal server error".to_string())),
            _ => Err(UnifiedError::Business("Business logic error".to_string())),
        }
    } else {
        Ok(format!("Service call {} succeeded", attempt))
    }
}

// 健康检查集成
async fn health_check_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("🏥 健康检查集成示例");
    
    // 创建健康检查器
    let health_checker = HealthChecker::new()
        .with_check_interval(Duration::from_secs(30))
        .with_timeout(Duration::from_secs(5))
        .with_retry_count(3);
    
    // 添加健康检查
    health_checker.add_check("database", check_database_health).await?;
    health_checker.add_check("external_api", check_external_api_health).await?;
    health_checker.add_check("cache", check_cache_health).await?;
    
    // 启动健康检查
    health_checker.start().await?;
    
    // 模拟运行
    tokio::time::sleep(Duration::from_secs(60)).await;
    
    // 获取健康状态
    let health_status = health_checker.get_health_status().await?;
    println!("🏥 健康状态: {:?}", health_status);
    
    Ok(())
}

// 健康检查函数
async fn check_database_health() -> Result<(), UnifiedError> {
    // 模拟数据库健康检查
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    if rand::random::<f64>() < 0.1 {
        Err(UnifiedError::System("Database connection failed".to_string()))
    } else {
        Ok(())
    }
}

async fn check_external_api_health() -> Result<(), UnifiedError> {
    // 模拟外部API健康检查
    tokio::time::sleep(Duration::from_millis(200)).await;
    
    if rand::random::<f64>() < 0.05 {
        Err(UnifiedError::Network("External API unavailable".to_string()))
    } else {
        Ok(())
    }
}

async fn check_cache_health() -> Result<(), UnifiedError> {
    // 模拟缓存健康检查
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    if rand::random::<f64>() < 0.02 {
        Err(UnifiedError::System("Cache service down".to_string()))
    } else {
        Ok(())
    }
}
```

---

## 🏭 生产环境配置

### 完整生产配置

```rust
use otlp::core::EnhancedOtlpClient;
use otlp::config::*;
use std::time::Duration;

// 生产环境配置示例
async fn production_configuration_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("🏭 生产环境配置示例");
    
    // 生产环境配置
    let production_config = ProductionConfig {
        // 基础配置
        endpoint: "http://otel-collector:4317".to_string(),
        service_name: "production-app".to_string(),
        service_version: "1.0.0".to_string(),
        environment: "production".to_string(),
        
        // 传输配置
        transport: TransportConfig {
            protocol: TransportProtocol::Grpc,
            compression: Compression::Gzip,
            tls_config: Some(TlsConfig {
                enabled: true,
                cert_file: "/etc/ssl/certs/client.crt".to_string(),
                key_file: "/etc/ssl/private/client.key".to_string(),
                ca_file: "/etc/ssl/certs/ca.crt".to_string(),
            }),
        },
        
        // 连接配置
        connection: ConnectionConfig {
            connect_timeout: Duration::from_secs(10),
            request_timeout: Duration::from_secs(60),
            keep_alive_timeout: Duration::from_secs(60),
            max_idle_connections: 100,
            max_connections: 200,
        },
        
        // 批处理配置
        batch: BatchConfig {
            max_batch_size: 1000,
            batch_timeout: Duration::from_millis(200),
            max_queue_size: 50000,
            strategy: BatchStrategy::Hybrid,
        },
        
        // 重试配置
        retry: RetryConfig {
            max_attempts: 3,
            initial_interval: Duration::from_millis(100),
            max_interval: Duration::from_secs(5),
            multiplier: 2.0,
            randomization_factor: 0.1,
            retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
        },
        
        // 监控配置
        monitoring: MonitoringConfig {
            enable_performance_metrics: true,
            enable_resource_metrics: true,
            enable_custom_metrics: true,
            metrics_export_interval: Duration::from_secs(10),
            health_check_endpoint: Some("http://localhost:8080/health".to_string()),
        },
        
        // 安全配置
        security: SecurityConfig {
            enable_authentication: true,
            auth_token: "your-production-token".to_string(),
            enable_encryption: true,
            encryption_key: "your-encryption-key".to_string(),
        },
        
        // 日志配置
        logging: LoggingConfig {
            log_level: LogLevel::Info,
            enable_structured_logging: true,
            enable_log_aggregation: true,
            log_format: LogFormat::Json,
        },
    };
    
    // 创建生产客户端
    let client = EnhancedOtlpClient::with_production_config(production_config).await?;
    
    // 启动生产监控
    start_production_monitoring(&client).await?;
    
    // 模拟生产负载
    simulate_production_load(&client).await?;
    
    Ok(())
}

// 生产监控
async fn start_production_monitoring(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    println!("📊 启动生产监控");
    
    // 启动性能监控
    let performance_monitor = client.get_performance_monitor().await?;
    performance_monitor.start().await?;
    
    // 启动健康检查
    let health_checker = client.get_health_checker().await?;
    health_checker.start().await?;
    
    // 启动告警
    let alert_manager = client.get_alert_manager().await?;
    alert_manager.start().await?;
    
    println!("✅ 生产监控启动完成");
    Ok(())
}

// 模拟生产负载
async fn simulate_production_load(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    println!("🔄 模拟生产负载");
    
    let tracer = client.tracer("production-component");
    let meter = client.meter("production-metrics");
    
    // 创建指标
    let request_counter = meter.u64_counter("requests_total").init();
    let response_time_histogram = meter.f64_histogram("response_time_seconds").init();
    let error_counter = meter.u64_counter("errors_total").init();
    
    // 模拟持续负载
    for i in 0..1000 {
        let start_time = std::time::Instant::now();
        
        let mut span = tracer.start("production-operation");
        span.set_attribute("request.id", i);
        span.set_attribute("user.id", format!("user-{}", i % 100));
        
        // 模拟业务逻辑
        let result = simulate_business_operation(i).await;
        
        let duration = start_time.elapsed();
        
        // 记录指标
        let mut attributes = HashMap::new();
        attributes.insert("method".to_string(), "POST".into());
        attributes.insert("endpoint".to_string(), "/api/v1/data".into());
        
        request_counter.add(1, &attributes);
        response_time_histogram.record(duration.as_secs_f64(), &attributes);
        
        if result.is_err() {
            error_counter.add(1, &attributes);
            span.set_status(StatusCode::Error, "Operation failed".to_string());
        } else {
            span.set_status(StatusCode::Ok, "Operation successful".to_string());
        }
        
        span.end();
        
        // 控制负载频率
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        if i % 100 == 0 {
            println!("  处理了 {} 个请求", i);
        }
    }
    
    println!("✅ 生产负载模拟完成");
    Ok(())
}

// 模拟业务操作
async fn simulate_business_operation(request_id: u32) -> Result<String, Box<dyn std::error::Error>> {
    // 模拟处理时间
    let processing_time = Duration::from_millis(50 + (request_id % 100));
    tokio::time::sleep(processing_time).await;
    
    // 模拟偶尔的失败
    if rand::random::<f64>() < 0.05 {
        Err("Business operation failed".into())
    } else {
        Ok(format!("Operation {} completed", request_id))
    }
}

// 生产配置结构
#[derive(Debug)]
struct ProductionConfig {
    endpoint: String,
    service_name: String,
    service_version: String,
    environment: String,
    transport: TransportConfig,
    connection: ConnectionConfig,
    batch: BatchConfig,
    retry: RetryConfig,
    monitoring: MonitoringConfig,
    security: SecurityConfig,
    logging: LoggingConfig,
}

#[derive(Debug)]
struct TransportConfig {
    protocol: TransportProtocol,
    compression: Compression,
    tls_config: Option<TlsConfig>,
}

#[derive(Debug)]
struct ConnectionConfig {
    connect_timeout: Duration,
    request_timeout: Duration,
    keep_alive_timeout: Duration,
    max_idle_connections: usize,
    max_connections: usize,
}

#[derive(Debug)]
struct SecurityConfig {
    enable_authentication: bool,
    auth_token: String,
    enable_encryption: bool,
    encryption_key: String,
}

#[derive(Debug)]
struct LoggingConfig {
    log_level: LogLevel,
    enable_structured_logging: bool,
    enable_log_aggregation: bool,
    log_format: LogFormat,
}

#[derive(Debug)]
enum TransportProtocol {
    Http,
    Grpc,
}

#[derive(Debug)]
struct TlsConfig {
    enabled: bool,
    cert_file: String,
    key_file: String,
    ca_file: String,
}

#[derive(Debug)]
enum LogFormat {
    Json,
    Text,
}
```

---

## 🚀 下一步

### 进阶学习路径

1. **微服务架构**: 深入学习微服务监控和追踪
2. **性能优化**: 掌握高级性能调优技术
3. **可靠性工程**: 学习故障注入和混沌工程
4. **生产运维**: 掌握生产环境部署和运维

### 实践项目

1. **构建监控系统**: 创建完整的监控和告警系统
2. **性能基准测试**: 建立性能基准和回归测试
3. **故障演练**: 实施混沌工程和故障演练
4. **生产部署**: 部署到生产环境并持续优化

### 相关资源

- 📖 [性能优化指南](../guides/performance-optimization.md)
- 📊 [监控配置指南](../guides/monitoring.md)
- 🛡️ [可靠性框架文档](../api/reliability.md)
- 🚀 [部署指南](../guides/deployment.md)

---

*最后更新: 2025年10月20日*  
*版本: 1.0.0*
