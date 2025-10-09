# Rust OTLP 30分钟快速入门

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **学习时间**: 30分钟  
> **难度**: ⭐⭐ 初级  
> **最后更新**: 2025年10月9日

---

## 🎯 学习目标

完成本教程后，你将能够：

1. ✅ 在 Rust 项目中配置 OpenTelemetry
2. ✅ 创建和发送 Traces (分布式追踪)
3. ✅ 记录 Metrics (指标)
4. ✅ 集成 Logs (日志)
5. ✅ 将数据导出到 OTLP Collector

---

## 📋 前置要求

- Rust 1.75+ (推荐 1.90+)
- Docker (用于运行 OTLP Collector)
- 基本的 Rust async/await 知识

---

## 🚀 第1步: 项目设置 (5分钟)

### 创建新项目

```bash
cargo new otlp-quickstart
cd otlp-quickstart
```

### 添加依赖

编辑 `Cargo.toml`:

```toml
[package]
name = "otlp-quickstart"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic"] }
opentelemetry-semantic-conventions = "0.31"

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.32"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具
anyhow = "1.0"
```

### 启动 OTLP Collector

创建 `docker-compose.yml`:

```yaml
version: '3'
services:
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC receiver
      - "4318:4318"    # OTLP HTTP receiver
    environment:
      - COLLECTOR_OTLP_ENABLED=true
```

启动服务:

```bash
docker-compose up -d
```

访问 Jaeger UI: <http://localhost:16686>

---

## 📊 第2步: 基础追踪 (Traces) (10分钟)

### 初始化 Tracer

创建 `src/main.rs`:

```rust
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _, TraceContextExt},
    KeyValue,
};
use opentelemetry_sdk::{runtime, Resource};
use opentelemetry_otlp::WithExportConfig;
use anyhow::Result;

/// 初始化 OpenTelemetry
fn init_tracer() -> Result<opentelemetry_sdk::trace::TracerProvider> {
    let provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "otlp-quickstart"),
                    KeyValue::new("service.version", "0.1.0"),
                ]))
        )
        .install_batch(runtime::Tokio)?;
    
    Ok(provider)
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 tracer
    let provider = init_tracer()?;
    global::set_tracer_provider(provider.clone());
    
    // 获取 tracer
    let tracer = global::tracer("main");
    
    // 创建 root span
    let span = tracer.start("main");
    let cx = opentelemetry::Context::current_with_span(span);
    let _guard = cx.attach();
    
    println!("🚀 OpenTelemetry initialized!");
    
    // 执行业务逻辑
    process_order().await?;
    
    // 关闭 tracer (flush 数据)
    global::shutdown_tracer_provider();
    
    println!("✅ Traces sent! Check Jaeger UI at http://localhost:16686");
    
    Ok(())
}

/// 业务逻辑示例
async fn process_order() -> Result<()> {
    let tracer = global::tracer("business");
    
    // 创建子 span
    let mut span = tracer.start("process_order");
    span.set_attribute(KeyValue::new("order.id", "12345"));
    span.set_attribute(KeyValue::new("order.amount", 99.99));
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let _guard = cx.attach();
    
    // 模拟业务逻辑
    validate_order().await?;
    charge_payment().await?;
    send_confirmation().await?;
    
    println!("📦 Order processed successfully!");
    
    Ok(())
}

async fn validate_order() -> Result<()> {
    let tracer = global::tracer("business");
    let span = tracer.start("validate_order");
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}

async fn charge_payment() -> Result<()> {
    let tracer = global::tracer("business");
    let span = tracer.start("charge_payment");
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}

async fn send_confirmation() -> Result<()> {
    let tracer = global::tracer("business");
    let span = tracer.start("send_confirmation");
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    Ok(())
}
```

### 运行程序

```bash
cargo run
```

### 查看追踪数据

1. 打开 Jaeger UI: <http://localhost:16686>
2. 选择服务: `otlp-quickstart`
3. 点击 "Find Traces"
4. 查看 span 树状结构

---

## 📈 第3步: 添加 Metrics (5分钟)

### 初始化 Meter

在 `main.rs` 中添加:

```rust
use opentelemetry::metrics::{Meter, MeterProvider as _};

/// 初始化 Metrics
fn init_metrics() -> Result<opentelemetry_sdk::metrics::MeterProvider> {
    let provider = opentelemetry_otlp::new_pipeline()
        .metrics(runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-quickstart"),
        ]))
        .build()?;
    
    Ok(provider)
}

/// 记录指标示例
async fn record_metrics() -> Result<()> {
    let meter = global::meter("metrics-example");
    
    // Counter: 累加计数器
    let order_counter = meter
        .u64_counter("orders.total")
        .with_description("Total number of orders")
        .init();
    
    // Histogram: 直方图 (用于延迟等)
    let order_duration = meter
        .f64_histogram("orders.duration")
        .with_unit("ms")
        .with_description("Order processing duration")
        .init();
    
    // UpDownCounter: 可增可减的计数器
    let active_orders = meter
        .i64_up_down_counter("orders.active")
        .with_description("Number of active orders")
        .init();
    
    // 记录指标
    order_counter.add(1, &[KeyValue::new("status", "success")]);
    order_duration.record(156.78, &[]);
    active_orders.add(1, &[]);
    
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    active_orders.add(-1, &[]);
    
    println!("📊 Metrics recorded!");
    
    Ok(())
}
```

更新 `main()`:

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 tracer 和 metrics
    let tracer_provider = init_tracer()?;
    let metrics_provider = init_metrics()?;
    
    global::set_tracer_provider(tracer_provider.clone());
    global::set_meter_provider(metrics_provider.clone());
    
    // 业务逻辑
    process_order().await?;
    record_metrics().await?;
    
    // 关闭
    global::shutdown_tracer_provider();
    metrics_provider.shutdown()?;
    
    Ok(())
}
```

---

## 📝 第4步: 集成 Logs (5分钟)

### 使用 tracing 集成

```rust
use tracing::{info, warn, error, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 Logging
fn init_logging() -> Result<()> {
    let tracer = global::tracer("logging");
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    Ok(())
}

/// 使用 #[instrument] 自动追踪函数
#[instrument(
    name = "process_order",
    fields(order.id = %order_id)
)]
async fn process_order_with_logs(order_id: &str) -> Result<()> {
    info!("Processing order: {}", order_id);
    
    // 验证订单
    validate_order_with_logs(order_id).await?;
    
    // 支付
    charge_payment_with_logs(order_id).await?;
    
    info!("Order {} completed successfully", order_id);
    
    Ok(())
}

#[instrument]
async fn validate_order_with_logs(order_id: &str) -> Result<()> {
    info!("Validating order: {}", order_id);
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}

#[instrument]
async fn charge_payment_with_logs(order_id: &str) -> Result<()> {
    info!("Charging payment for order: {}", order_id);
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // 模拟错误
    if order_id == "error" {
        error!("Payment failed for order: {}", order_id);
        return Err(anyhow::anyhow!("Payment failed"));
    }
    
    Ok(())
}
```

---

## 🌐 第5步: HTTP 服务集成 (5分钟)

### 添加 Axum 依赖

在 `Cargo.toml` 中添加:

```toml
axum = "0.8"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }
```

### 创建 HTTP 服务

```rust
use axum::{
    routing::get,
    Router,
    extract::Path,
    http::StatusCode,
    response::IntoResponse,
};
use tower_http::trace::TraceLayer;

async fn start_server() -> Result<()> {
    let app = Router::new()
        .route("/", get(root))
        .route("/order/:id", get(get_order))
        .route("/health", get(health_check))
        .layer(TraceLayer::new_for_http());
    
    println!("🌐 Server listening on http://localhost:3000");
    
    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

async fn root() -> &'static str {
    "Welcome to OTLP Quickstart!"
}

#[instrument(name = "get_order_handler", fields(order_id = %id))]
async fn get_order(Path(id): Path<String>) -> impl IntoResponse {
    info!("Fetching order: {}", id);
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    (StatusCode::OK, format!("Order {} details", id))
}

async fn health_check() -> &'static str {
    "OK"
}
```

---

## 🎨 第6步: 完整示例

### 完整的 `main.rs`

```rust
use opentelemetry::{global, trace::{Tracer, TraceContextExt}, KeyValue};
use opentelemetry_sdk::{runtime, Resource};
use opentelemetry_otlp::WithExportConfig;
use tracing::{info, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use axum::{routing::get, Router, extract::Path, http::StatusCode};
use tower_http::trace::TraceLayer;
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 初始化 OpenTelemetry
    init_telemetry()?;
    
    info!("🚀 Application started");
    
    // 2. 启动 HTTP 服务器
    let app = Router::new()
        .route("/", get(|| async { "OTLP Quickstart" }))
        .route("/order/:id", get(get_order))
        .layer(TraceLayer::new_for_http());
    
    println!("🌐 Server: http://localhost:3000");
    println!("📊 Jaeger: http://localhost:16686");
    
    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

/// 初始化所有遥测组件
fn init_telemetry() -> Result<()> {
    // Tracer
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "otlp-quickstart"),
                    KeyValue::new("service.version", "0.1.0"),
                ]))
        )
        .install_batch(runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider);
    
    // Logging with tracing
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer())
        .init();
    
    Ok(())
}

#[instrument(name = "GET /order/:id", fields(order_id = %id))]
async fn get_order(Path(id): Path<String>) -> (StatusCode, String) {
    info!("Fetching order details");
    
    // 创建子 span
    let tracer = global::tracer("handlers");
    let span = tracer.start("database.query");
    let _cx = opentelemetry::Context::current_with_span(span);
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    (StatusCode::OK, format!("Order {} found", id))
}
```

---

## 🧪 测试

### 发送请求

```bash
# 根路径
curl http://localhost:3000/

# 获取订单
curl http://localhost:3000/order/12345
curl http://localhost:3000/order/67890
curl http://localhost:3000/order/abcde
```

### 查看追踪

1. 打开 Jaeger: <http://localhost:16686>
2. 选择服务: `otlp-quickstart`
3. 点击 "Find Traces"
4. 查看请求链路

---

## 🎓 下一步学习

### 进阶主题

1. **Context 传播**: [Context Propagation详解](../04_核心组件/04_Context_Propagation详解_Rust完整版.md)
2. **数据库追踪**: [数据库集成](../02_Semantic_Conventions/02_追踪属性/03_数据库_Rust完整版.md)
3. **消息队列**: [Kafka追踪](../02_Semantic_Conventions/03_消息队列属性/01_Kafka_Rust.md)
4. **性能优化**: [Rust性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)

### 推荐资源

- 📖 [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
- 📖 [Rust SDK 文档](https://docs.rs/opentelemetry/)
- 💻 [示例仓库](https://github.com/open-telemetry/opentelemetry-rust)

---

## ❓ 常见问题

### Q: 为什么看不到追踪数据？

**A**: 检查以下几点：

1. OTLP Collector 是否运行: `docker ps`
2. 端口是否正确: `4317` (gRPC) 或 `4318` (HTTP)
3. 是否调用了 `global::shutdown_tracer_provider()`

### Q: 如何调试连接问题？

**A**: 启用调试日志:

```rust
std::env::set_var("RUST_LOG", "opentelemetry=debug");
env_logger::init();
```

### Q: 生产环境如何配置？

**A**: 使用环境变量:

```bash
export OTEL_EXPORTER_OTLP_ENDPOINT="http://my-collector:4317"
export OTEL_SERVICE_NAME="my-service"
export OTEL_RESOURCE_ATTRIBUTES="deployment.environment=production"
```

---

## 📦 完整项目结构

```text
otlp-quickstart/
├── Cargo.toml
├── docker-compose.yml
├── src/
│   └── main.rs
└── README.md
```

---

## ✅ 总结

恭喜！你已经完成了 Rust OTLP 快速入门。你现在知道如何：

- ✅ 配置 OpenTelemetry SDK
- ✅ 创建和发送 Traces
- ✅ 记录 Metrics
- ✅ 集成 Logs
- ✅ 在 HTTP 服务中使用追踪

**下一步**: 探索 [完整实战案例](../06_实战案例/00_Rust微服务完整实战_2025最新版.md) 了解生产级实现！

---

**学习时间**: ✅ 30分钟完成  
**项目地址**: [GitHub](https://github.com/your-repo/otlp-quickstart)  
**问题反馈**: 通过 Issues 提交

**祝学习顺利！** 🎉
