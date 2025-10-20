# Honeycomb 完整实现指南

## 目录

- [Honeycomb 完整实现指南](#honeycomb-完整实现指南)
  - [目录](#目录)
  - [1. Honeycomb 概述](#1-honeycomb-概述)
    - [1.1 什么是 Honeycomb?](#11-什么是-honeycomb)
    - [1.2 核心概念](#12-核心概念)
    - [1.3 为什么选择 Honeycomb?](#13-为什么选择-honeycomb)
  - [2. 架构设计](#2-架构设计)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
    - [3.2 环境变量](#32-环境变量)
  - [4. OpenTelemetry 集成](#4-opentelemetry-集成)
    - [4.1 Honeycomb OTLP Exporter](#41-honeycomb-otlp-exporter)
    - [4.2 自定义属性](#42-自定义属性)
  - [5. 高维度数据](#5-高维度数据)
    - [5.1 丰富的上下文](#51-丰富的上下文)
    - [5.2 动态采样](#52-动态采样)
  - [6. BubbleUp 分析](#6-bubbleup-分析)
    - [6.1 异常检测](#61-异常检测)
    - [6.2 根因分析](#62-根因分析)
  - [7. SLO 监控](#7-slo-监控)
    - [7.1 定义 SLO](#71-定义-slo)
    - [7.2 SLI 指标](#72-sli-指标)
  - [8. 分布式追踪](#8-分布式追踪)
    - [8.1 完整事务追踪](#81-完整事务追踪)
    - [8.2 Span 关联](#82-span-关联)
  - [9. 查询与可视化](#9-查询与可视化)
    - [9.1 查询语言](#91-查询语言)
    - [9.2 自定义仪表板](#92-自定义仪表板)
  - [10. 生产实践](#10-生产实践)
    - [10.1 Docker Compose](#101-docker-compose)
    - [10.2 Kubernetes](#102-kubernetes)
  - [11. 国际标准对齐](#11-国际标准对齐)
  - [总结](#总结)
    - [Honeycomb 核心优势](#honeycomb-核心优势)
    - [适用场景](#适用场景)
    - [性能基准](#性能基准)

---

## 1. Honeycomb 概述

### 1.1 什么是 Honeycomb?

**Honeycomb** 是现代观察性数据平台,专注于:

- **高维度分析**: 无限制的自定义属性
- **快速查询**: 亚秒级查询响应
- **BubbleUp**: AI 驱动的异常检测
- **SLO 监控**: 服务质量目标管理

### 1.2 核心概念

| 概念 | 描述 |
|------|------|
| **Dataset** | 事件集合 (类似数据库表) |
| **Event** | 单个观察数据点 |
| **Trace** | 跨服务的事务追踪 |
| **BubbleUp** | 自动异常分析 |
| **SLO** | 服务级别目标 |
| **Burn Alerts** | SLO 预算消耗告警 |

### 1.3 为什么选择 Honeycomb?

- ✅ **无限维度**: 不受预定义维度限制
- ✅ **快速分析**: 实时查询和探索
- ✅ **智能分析**: BubbleUp 自动发现异常
- ✅ **SLO 驱动**: 以用户体验为中心
- ✅ **开发者友好**: 直观的查询界面

---

## 2. 架构设计

```text
┌───────────────────────────────────────────────────────┐
│              Honeycomb 架构                            │
├───────────────────────────────────────────────────────┤
│                                                        │
│  ┌─────────────────┐                                  │
│  │   Rust App      │                                  │
│  │  (OpenTelemetry)│                                  │
│  └────────┬────────┘                                  │
│           │                                            │
│           │ OTLP/gRPC or HTTP                         │
│           │                                            │
│           ▼                                            │
│  ┌─────────────────┐                                  │
│  │  OTLP Endpoint  │                                  │
│  │  (api.honeycomb │                                  │
│  │   .io/v1/traces)│                                  │
│  └────────┬────────┘                                  │
│           │                                            │
│           ▼                                            │
│  ┌──────────────────────────────────┐                │
│  │     Honeycomb Platform           │                │
│  │  ┌────────┐  ┌──────────────┐   │                │
│  │  │Dataset │  │   BubbleUp   │   │                │
│  │  │        │  │  (异常检测)   │   │                │
│  │  └────────┘  └──────────────┘   │                │
│  │  ┌────────┐  ┌──────────────┐   │                │
│  │  │ Traces │  │  SLO Monitor │   │                │
│  │  │        │  │              │   │                │
│  │  └────────┘  └──────────────┘   │                │
│  │  ┌────────┐  ┌──────────────┐   │                │
│  │  │ Query  │  │  Dashboard   │   │                │
│  │  │ Engine │  │              │   │                │
│  │  └────────┘  └──────────────┘   │                │
│  └──────────────────────────────────┘                │
│                                                        │
└───────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "honeycomb-rust-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# 异步运行时
tokio = { version = "1", features = ["full"] }

# Web 框架
axum = "0.7"
tower = "0.5"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic", "http-proto"] }
opentelemetry-semantic-conventions = "0.25"

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 错误处理
anyhow = "1"
thiserror = "1"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 环境变量
dotenvy = "0.15"
```

### 3.2 环境变量

```bash
# .env
HONEYCOMB_API_KEY=your_api_key_here
HONEYCOMB_DATASET=rust-app
SERVICE_NAME=rust-app
DEPLOYMENT_ENVIRONMENT=production
RUST_LOG=info
```

---

## 4. OpenTelemetry 集成

### 4.1 Honeycomb OTLP Exporter

```rust
use opentelemetry::{
    global, trace::TracerProvider, KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{Config, Sampler},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化 Honeycomb 遥测
pub fn init_honeycomb_telemetry() -> anyhow::Result<()> {
    // 获取环境变量
    let api_key = std::env::var("HONEYCOMB_API_KEY")
        .expect("HONEYCOMB_API_KEY not set");
    let dataset = std::env::var("HONEYCOMB_DATASET")
        .unwrap_or_else(|_| "rust-app".to_string());
    let service_name = std::env::var("SERVICE_NAME")
        .unwrap_or_else(|_| "rust-app".to_string());
    let environment = std::env::var("DEPLOYMENT_ENVIRONMENT")
        .unwrap_or_else(|_| "production".to_string());

    // 1. 配置 OTLP Tracer (Honeycomb)
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("https://api.honeycomb.io/v1/traces")
                .with_headers(std::collections::HashMap::from([
                    ("x-honeycomb-team".to_string(), api_key.clone()),
                    ("x-honeycomb-dataset".to_string(), dataset.clone()),
                ])),
        )
        .with_trace_config(
            Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.clone()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", environment.clone()),
                    KeyValue::new("library.language", "rust"),
                    KeyValue::new("library.name", "opentelemetry"),
                    KeyValue::new("library.version", "0.25.0"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    // 2. 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!(
        service.name = %service_name,
        dataset = %dataset,
        deployment.environment = %environment,
        "Honeycomb telemetry initialized"
    );

    Ok(())
}

/// 优雅关闭
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
    tracing::info!("Telemetry shutdown complete");
}
```

### 4.2 自定义属性

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer}, KeyValue};
use tracing::instrument;

/// 添加丰富的上下文属性
#[instrument(skip(pool), fields(
    // HTTP 属性
    http.method = "POST",
    http.route = "/api/orders",
    http.status_code = tracing::field::Empty,
    
    // 业务属性
    order.id = tracing::field::Empty,
    order.total = tracing::field::Empty,
    order.items_count = tracing::field::Empty,
    
    // 用户属性
    user.id = %user_id,
    user.tier = tracing::field::Empty,
    user.region = tracing::field::Empty,
    
    // 系统属性
    db.query_count = 0,
    cache.hit_rate = tracing::field::Empty,
    
    // 性能属性
    duration_ms = tracing::field::Empty,
))]
pub async fn create_order(
    user_id: String,
    items: Vec<OrderItem>,
    pool: sqlx::PgPool,
) -> Result<Order, AppError> {
    let tracer = global::tracer("order-service");
    let span = tracing::Span::current();
    
    // 记录业务属性
    span.record("order.items_count", items.len());
    
    // 查询用户信息
    let user = fetch_user(&pool, &user_id).await?;
    span.record("user.tier", &user.tier.as_str());
    span.record("user.region", &user.region.as_str());
    
    // 创建订单
    let start = std::time::Instant::now();
    let order = create_order_in_db(&pool, &user_id, items).await?;
    let duration = start.elapsed();
    
    // 记录性能和结果
    span.record("order.id", &order.id.to_string());
    span.record("order.total", order.total_amount);
    span.record("http.status_code", 201);
    span.record("duration_ms", duration.as_millis() as i64);
    
    Ok(order)
}
```

---

## 5. 高维度数据

### 5.1 丰富的上下文

```rust
/// 添加无限维度的上下文属性
#[instrument(skip(request))]
pub async fn process_payment(request: PaymentRequest) -> Result<PaymentResult, AppError> {
    let span = tracing::Span::current();
    
    // 支付相关属性
    span.record("payment.method", &request.payment_method);
    span.record("payment.amount", request.amount);
    span.record("payment.currency", &request.currency);
    
    // 风险评估属性
    span.record("risk.score", calculate_risk_score(&request));
    span.record("risk.level", &get_risk_level(&request));
    span.record("fraud.check_passed", true);
    
    // 地理位置属性
    span.record("geo.country", &request.billing_country);
    span.record("geo.city", &request.billing_city);
    
    // 设备信息属性
    span.record("device.type", &request.device_type);
    span.record("device.os", &request.device_os);
    span.record("device.browser", &request.browser);
    
    // 3D Secure 属性
    span.record("3ds.enabled", request.requires_3ds);
    span.record("3ds.version", "2.0");
    
    // A/B 测试属性
    span.record("experiment.id", &request.experiment_id);
    span.record("experiment.variant", &request.variant);
    
    // 业务属性
    span.record("merchant.id", &request.merchant_id);
    span.record("merchant.category", &request.merchant_category);
    
    // 处理支付
    let result = process_payment_internal(&request).await?;
    
    // 记录结果
    span.record("payment.status", &result.status);
    span.record("payment.transaction_id", &result.transaction_id);
    span.record("payment.processor", &result.processor);
    
    Ok(result)
}

/// 计算风险分数
fn calculate_risk_score(request: &PaymentRequest) -> f64 {
    // 风险评估逻辑
    let mut score = 0.0;
    
    if request.amount > 1000.0 {
        score += 0.3;
    }
    
    if request.billing_country != request.shipping_country {
        score += 0.2;
    }
    
    if request.is_first_purchase {
        score += 0.1;
    }
    
    score
}
```

### 5.2 动态采样

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};
use rand::Rng;

/// Honeycomb 动态采样器
pub struct HoneycombSampler {
    base_sample_rate: u32,
}

impl HoneycombSampler {
    pub fn new(base_sample_rate: u32) -> Self {
        Self { base_sample_rate }
    }
    
    /// 计算采样率 (基于属性)
    fn calculate_sample_rate(&self, attributes: &opentelemetry::trace::OrderedMap<opentelemetry::Key, opentelemetry::Value>) -> u32 {
        // 错误总是采样
        if attributes.get(&opentelemetry::Key::from_static_str("error")).is_some() {
            return 1;
        }
        
        // 慢请求降低采样率
        if let Some(duration) = attributes.get(&opentelemetry::Key::from_static_str("duration_ms")) {
            if let Some(duration_val) = duration.as_i64() {
                if duration_val > 1000 {
                    return self.base_sample_rate / 10; // 高采样
                }
            }
        }
        
        // 特定用户段采样
        if let Some(user_tier) = attributes.get(&opentelemetry::Key::from_static_str("user.tier")) {
            if user_tier.as_str() == Some("premium") {
                return self.base_sample_rate / 2; // 中采样
            }
        }
        
        self.base_sample_rate
    }
}

impl Sampler for HoneycombSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::trace::SpanContext>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &opentelemetry::trace::OrderedMap<opentelemetry::Key, opentelemetry::Value>,
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        let sample_rate = self.calculate_sample_rate(attributes);
        
        // 采样决策
        let mut rng = rand::thread_rng();
        let random: u32 = rng.gen_range(0..sample_rate);
        
        let decision = if random == 0 {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        // 添加采样率属性
        let mut sample_attributes = vec![
            KeyValue::new("SampleRate", sample_rate as i64),
        ];
        
        SamplingResult {
            decision,
            attributes: sample_attributes,
            trace_state: Default::default(),
        }
    }
}
```

---

## 6. BubbleUp 分析

### 6.1 异常检测

```rust
/// 为 BubbleUp 添加丰富的上下文
#[instrument(skip(pool))]
pub async fn checkout_flow(
    user_id: String,
    cart_id: String,
    pool: sqlx::PgPool,
) -> Result<CheckoutResult, AppError> {
    let span = tracing::Span::current();
    
    // 添加所有可能相关的属性
    span.record("user.id", &user_id);
    span.record("cart.id", &cart_id);
    
    // 步骤 1: 验证购物车
    let cart = validate_cart(&pool, &cart_id).await?;
    span.record("cart.items_count", cart.items.len());
    span.record("cart.total", cart.total_amount);
    
    // 步骤 2: 检查库存
    let inventory_result = check_inventory(&pool, &cart).await?;
    span.record("inventory.available", inventory_result.all_available);
    span.record("inventory.check_duration_ms", inventory_result.duration_ms);
    
    // 步骤 3: 应用优惠券
    if let Some(coupon) = cart.coupon {
        span.record("coupon.code", &coupon.code);
        span.record("coupon.discount_amount", coupon.discount);
        span.record("coupon.type", &coupon.coupon_type);
    }
    
    // 步骤 4: 处理支付
    let payment_result = process_payment_for_checkout(&cart).await?;
    span.record("payment.method", &payment_result.method);
    span.record("payment.processor", &payment_result.processor);
    span.record("payment.duration_ms", payment_result.duration_ms);
    
    // 步骤 5: 创建订单
    let order = create_order_from_cart(&pool, &cart, &payment_result).await?;
    span.record("order.id", &order.id.to_string());
    span.record("order.status", &order.status);
    
    Ok(CheckoutResult {
        order_id: order.id,
        total_amount: order.total_amount,
    })
}
```

### 6.2 根因分析

```rust
/// 为根因分析添加详细的错误上下文
#[instrument(skip(pool))]
pub async fn process_order_with_context(
    order_id: String,
    pool: sqlx::PgPool,
) -> Result<(), AppError> {
    let span = tracing::Span::current();
    
    match process_order_internal(&pool, &order_id).await {
        Ok(_) => {
            span.record("success", true);
            Ok(())
        }
        Err(e) => {
            // 添加详细的错误上下文
            span.record("error", true);
            span.record("error.type", &format!("{:?}", e));
            span.record("error.message", &e.to_string());
            
            // 添加错误相关的系统状态
            span.record("system.db_connections", pool.size());
            span.record("system.memory_usage_mb", get_memory_usage());
            span.record("system.cpu_usage_percent", get_cpu_usage());
            
            // 添加业务上下文
            if let Ok(order) = fetch_order(&pool, &order_id).await {
                span.record("order.status", &order.status);
                span.record("order.retry_count", order.retry_count);
                span.record("order.created_minutes_ago", order.age_minutes());
            }
            
            // 添加依赖服务状态
            span.record("dependency.payment_service_healthy", check_payment_service().await);
            span.record("dependency.inventory_service_healthy", check_inventory_service().await);
            
            Err(e)
        }
    }
}
```

---

## 7. SLO 监控

### 7.1 定义 SLO

```rust
/// SLO 配置
pub struct SloConfig {
    pub name: String,
    pub target_percentage: f64,
    pub time_window_days: u32,
}

impl SloConfig {
    /// API 可用性 SLO (99.9%)
    pub fn api_availability() -> Self {
        Self {
            name: "API Availability".to_string(),
            target_percentage: 99.9,
            time_window_days: 30,
        }
    }
    
    /// API 延迟 SLO (P95 < 200ms)
    pub fn api_latency_p95() -> Self {
        Self {
            name: "API Latency P95".to_string(),
            target_percentage: 95.0,
            time_window_days: 30,
        }
    }
    
    /// 支付成功率 SLO (99.5%)
    pub fn payment_success_rate() -> Self {
        Self {
            name: "Payment Success Rate".to_string(),
            target_percentage: 99.5,
            time_window_days: 7,
        }
    }
}
```

### 7.2 SLI 指标

```rust
use opentelemetry::{global, metrics::{Counter, Histogram}};

/// SLI 指标收集器
pub struct SliMetrics {
    request_total: Counter<u64>,
    request_success: Counter<u64>,
    request_duration: Histogram<f64>,
}

impl SliMetrics {
    pub fn new() -> Self {
        let meter = global::meter("sli-metrics");
        
        Self {
            request_total: meter
                .u64_counter("http.requests.total")
                .with_description("Total HTTP requests")
                .init(),
            
            request_success: meter
                .u64_counter("http.requests.success")
                .with_description("Successful HTTP requests (2xx/3xx)")
                .init(),
            
            request_duration: meter
                .f64_histogram("http.request.duration")
                .with_description("HTTP request duration in seconds")
                .with_unit("s")
                .init(),
        }
    }
    
    /// 记录请求
    pub fn record_request(&self, path: &str, method: &str, status: u16, duration_ms: u64) {
        let attributes = vec![
            KeyValue::new("http.path", path.to_string()),
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status as i64),
        ];
        
        // 总请求数
        self.request_total.add(1, &attributes);
        
        // 成功请求数
        if status >= 200 && status < 400 {
            self.request_success.add(1, &attributes);
        }
        
        // 请求延迟
        self.request_duration.record(
            duration_ms as f64 / 1000.0,
            &attributes,
        );
    }
}
```

---

## 8. 分布式追踪

### 8.1 完整事务追踪

```rust
/// 端到端事务追踪
#[instrument(skip(pool, producer))]
pub async fn process_order_transaction(
    order_id: String,
    pool: sqlx::PgPool,
    producer: rdkafka::producer::FutureProducer,
) -> Result<(), AppError> {
    let tracer = global::tracer("order-transaction");
    let span = tracing::Span::current();
    
    span.record("transaction.id", &order_id);
    span.record("transaction.type", "order_processing");
    
    // 步骤 1: 锁定库存
    let inventory_span = tracer
        .span_builder("Lock Inventory")
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(inventory_span).attach();
    
    lock_inventory(&pool, &order_id).await?;
    
    // 步骤 2: 扣款
    let payment_span = tracer
        .span_builder("Process Payment")
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(payment_span).attach();
    
    let payment_result = charge_payment(&order_id).await?;
    
    // 步骤 3: 创建订单
    let order_span = tracer
        .span_builder("Create Order")
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(order_span).attach();
    
    create_order_record(&pool, &order_id, &payment_result).await?;
    
    // 步骤 4: 发送通知
    let notification_span = tracer
        .span_builder("Send Notification")
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(notification_span).attach();
    
    publish_order_event(&producer, &order_id).await?;
    
    span.record("transaction.status", "completed");
    span.record("transaction.steps_count", 4);
    
    Ok(())
}
```

### 8.2 Span 关联

```rust
/// 跨服务 Span 关联
#[instrument]
pub async fn call_external_service(order_id: &str) -> Result<ExternalResponse, AppError> {
    let tracer = global::tracer("http-client");
    
    let span = tracer
        .span_builder("Call External Service")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    let cx = opentelemetry::Context::current_with_span(span);
    
    // 注入 Trace Context
    let mut headers = reqwest::header::HeaderMap::new();
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut opentelemetry_http::HeaderInjector(&mut headers));
    });
    
    let client = reqwest::Client::new();
    let response = client
        .post("https://external-service.com/api/process")
        .headers(headers)
        .json(&serde_json::json!({
            "order_id": order_id
        }))
        .send()
        .await?;
    
    let result: ExternalResponse = response.json().await?;
    
    Ok(result)
}
```

---

## 9. 查询与可视化

### 9.1 查询语言

```javascript
// Honeycomb 查询示例 (在 UI 中使用)

// 1. P95 延迟 (按端点)
QUERY:
  VISUALIZE: HEATMAP(duration_ms)
  GROUP BY: http.route
  WHERE: span.kind = "server"
  LIMIT: 100

// 2. 错误率 (按服务)
QUERY:
  VISUALIZE: COUNT
  GROUP BY: service.name
  WHERE: error = true
  CALCULATE: RATE_AVG(1m)

// 3. 慢查询 (数据库)
QUERY:
  VISUALIZE: P95(db.duration_ms)
  GROUP BY: db.statement
  WHERE: db.duration_ms > 100
  ORDER BY: P95(db.duration_ms) DESC

// 4. 用户旅程分析
QUERY:
  VISUALIZE: COUNT
  GROUP BY: user.id, trace.trace_id
  WHERE: http.route IN ["/checkout", "/payment", "/confirm"]
  CALCULATE: COUNT_DISTINCT(trace.trace_id)
```

### 9.2 自定义仪表板

```rust
/// 为仪表板生成有用的属性
#[instrument]
pub async fn dashboard_friendly_instrumentation(
    request: ApiRequest,
) -> Result<ApiResponse, AppError> {
    let span = tracing::Span::current();
    
    // 仪表板维度属性
    span.record("service.name", "api-gateway");
    span.record("service.tier", "production");
    span.record("service.region", "us-west-2");
    
    // 时间维度
    span.record("time.hour", chrono::Local::now().hour());
    span.record("time.day_of_week", chrono::Local::now().weekday().to_string());
    
    // 业务维度
    span.record("business.tenant_id", &request.tenant_id);
    span.record("business.feature_flag", &request.feature_flag);
    
    // 性能维度
    let start = std::time::Instant::now();
    let result = process_request(request).await?;
    let duration = start.elapsed();
    
    span.record("perf.duration_ms", duration.as_millis() as i64);
    span.record("perf.is_cached", result.from_cache);
    span.record("perf.cache_hit_rate", calculate_cache_hit_rate());
    
    Ok(result)
}
```

---

## 10. 生产实践

### 10.1 Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    environment:
      HONEYCOMB_API_KEY: ${HONEYCOMB_API_KEY}
      HONEYCOMB_DATASET: rust-app
      SERVICE_NAME: rust-app
      DEPLOYMENT_ENVIRONMENT: production
      RUST_LOG: info
    ports:
      - "8080:8080"
    depends_on:
      - postgres
    restart: unless-stopped

  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: app_db
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
    volumes:
      - postgres_data:/var/lib/postgresql/data

volumes:
  postgres_data:
```

### 10.2 Kubernetes

```yaml
# kubernetes/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: rust-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: HONEYCOMB_API_KEY
          valueFrom:
            secretKeyRef:
              name: honeycomb-secrets
              key: api-key
        - name: HONEYCOMB_DATASET
          value: "rust-app"
        - name: SERVICE_NAME
          value: "rust-app"
        - name: DEPLOYMENT_ENVIRONMENT
          value: "production"
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"

---
apiVersion: v1
kind: Secret
metadata:
  name: honeycomb-secrets
type: Opaque
data:
  api-key: <base64-encoded-key>
```

---

## 11. 国际标准对齐

- ✅ **OpenTelemetry Protocol**: OTLP/gRPC and HTTP
- ✅ **W3C Trace Context**: 分布式追踪上下文传播
- ✅ **OpenTelemetry Semantic Conventions**: 标准属性命名
- ✅ **SLO/SLI 标准**: Google SRE 最佳实践

---

## 总结

### Honeycomb 核心优势

1. **无限维度**: 不受预定义维度限制
2. **快速查询**: 亚秒级查询响应
3. **BubbleUp**: AI 驱动的异常检测
4. **SLO 监控**: 以用户体验为中心
5. **开发者友好**: 直观的查询界面

### 适用场景

- ✅ 高维度数据分析
- ✅ 复杂问题根因分析
- ✅ SLO 驱动的可靠性工程
- ✅ 微服务架构
- ✅ 开发者自助调试

### 性能基准

- **查询延迟**: < 1 秒
- **数据保留**: 60 天 (可扩展)
- **采样率**: 动态采样
- **事件大小**: 最大 100 KB/事件

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
