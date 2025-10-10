# Rust OTLP 30分钟快速入门

> **从零开始**: 30分钟内掌握 Rust OpenTelemetry  
> **适合人群**: Rust 初学者 & OpenTelemetry 新手  
> **最后更新**: 2025年10月10日

---

## 📚 目录

- [Rust OTLP 30分钟快速入门](#rust-otlp-30分钟快速入门)
  - [📚 目录](#-目录)
  - [🎯 学习目标](#-学习目标)
  - [⏱️ 时间规划](#️-时间规划)
  - [📦 环境准备 (5分钟)](#-环境准备-5分钟)
    - [1. 安装 Rust](#1-安装-rust)
    - [2. 创建项目](#2-创建项目)
    - [3. 添加依赖](#3-添加依赖)
  - [🚀 第一个追踪程序 (10分钟)](#-第一个追踪程序-10分钟)
    - [Step 1: 初始化 Tracer](#step-1-初始化-tracer)
    - [Step 2: 创建 Span](#step-2-创建-span)
    - [Step 3: 完整示例](#step-3-完整示例)
    - [Step 4: 运行程序](#step-4-运行程序)
  - [📊 添加 Metrics (5分钟)](#-添加-metrics-5分钟)
    - [Metrics 完整示例](#metrics-完整示例)
  - [🌐 HTTP 服务追踪 (10分钟)](#-http-服务追踪-10分钟)
    - [HTTP 服务器示例](#http-服务器示例)
    - [测试 HTTP 追踪](#测试-http-追踪)
  - [🔍 查看追踪数据](#-查看追踪数据)
    - [使用 Jaeger](#使用-jaeger)
    - [查看 Traces](#查看-traces)
  - [💡 核心概念速查](#-核心概念速查)
    - [Trace 追踪](#trace-追踪)
    - [Span 范围](#span-范围)
    - [Metrics 指标](#metrics-指标)
    - [Logs 日志](#logs-日志)
  - [🎨 最佳实践](#-最佳实践)
    - [✅ DO (推荐做法)](#-do-推荐做法)
    - [❌ DON'T (避免做法)](#-dont-避免做法)
  - [🐛 常见问题](#-常见问题)
    - [Q1: 为什么看不到追踪数据？](#q1-为什么看不到追踪数据)
    - [Q2: 如何调试 OpenTelemetry？](#q2-如何调试-opentelemetry)
    - [Q3: 性能影响有多大？](#q3-性能影响有多大)
  - [📚 下一步学习](#-下一步学习)
  - [🔗 快速链接](#-快速链接)
    - [官方文档](#官方文档)
    - [示例代码](#示例代码)
    - [社区](#社区)
  - [🎉 恭喜](#-恭喜)

---

## 🎯 学习目标

完成本教程后，你将学会：

- ✅ 搭建 Rust OpenTelemetry 开发环境
- ✅ 创建和管理 Span（追踪单元）
- ✅ 记录 Metrics（性能指标）
- ✅ 在 HTTP 服务中集成 OpenTelemetry
- ✅ 在 Jaeger 中查看追踪数据

---

## ⏱️ 时间规划

| 阶段 | 时间 | 内容 |
|------|------|------|
| 🛠️ 环境准备 | 5分钟 | 安装工具、创建项目 |
| 🚀 第一个程序 | 10分钟 | 基础追踪实现 |
| 📊 Metrics | 5分钟 | 添加性能指标 |
| 🌐 HTTP 追踪 | 10分钟 | 实战 Web 服务 |

---

## 📦 环境准备 (5分钟)

### 1. 安装 Rust

```bash
# macOS / Linux
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Windows
# 访问 https://rustup.rs/ 下载安装器

# 验证安装
rustc --version
cargo --version
```

### 2. 创建项目

```bash
# 创建新项目
cargo new otlp-quickstart
cd otlp-quickstart

# 测试项目
cargo run
# 输出: Hello, world!
```

### 3. 添加依赖

编辑 `Cargo.toml`：

```toml
[package]
name = "otlp-quickstart"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio", "trace", "metrics"] }

# OTLP 导出器
opentelemetry-otlp = { version = "0.15", features = ["tonic", "metrics"] }

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 日志 (可选)
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.23"

# 实用工具
anyhow = "1.0"
```

安装依赖：

```bash
cargo build
```

---

## 🚀 第一个追踪程序 (10分钟)

### Step 1: 初始化 Tracer

创建 `src/main.rs`：

```rust
use opentelemetry::{global, trace::{Tracer, TracerProvider as _}, KeyValue};
use opentelemetry_sdk::{trace as sdktrace, Resource};
use anyhow::Result;

fn init_tracer() -> Result<sdktrace::Tracer> {
    // 1. 创建资源 (标识你的服务)
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "quickstart-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);

    // 2. 创建 OTLP 导出器 (发送到 Jaeger/Collector)
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317") // Jaeger gRPC endpoint
        .build_span_exporter()?;

    // 3. 创建 TracerProvider
    let tracer_provider = sdktrace::TracerProvider::builder()
        .with_config(sdktrace::Config::default().with_resource(resource))
        .with_batch_exporter(otlp_exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    // 4. 获取 Tracer
    let tracer = tracer_provider.tracer("quickstart");
    
    // 5. 设置为全局 Tracer
    global::set_tracer_provider(tracer_provider);
    
    Ok(tracer)
}
```

### Step 2: 创建 Span

```rust
use opentelemetry::trace::{Span, Status};

async fn do_work() {
    let tracer = global::tracer("quickstart");
    
    // 创建一个 Span
    let mut span = tracer
        .span_builder("do_work")
        .start(&tracer);
    
    // 添加属性
    span.set_attribute(KeyValue::new("work.type", "example"));
    span.set_attribute(KeyValue::new("work.id", 12345));
    
    // 模拟工作
    println!("Working...");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // 设置状态
    span.set_status(Status::Ok);
    
    // Span 自动在作用域结束时关闭
}
```

### Step 3: 完整示例

```rust
use opentelemetry::{global, trace::{Tracer, TracerProvider as _, Span, Status}, KeyValue};
use opentelemetry_sdk::{trace as sdktrace, Resource};
use anyhow::Result;

fn init_tracer() -> Result<sdktrace::Tracer> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "quickstart-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);

    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;

    let tracer_provider = sdktrace::TracerProvider::builder()
        .with_config(sdktrace::Config::default().with_resource(resource))
        .with_batch_exporter(otlp_exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    let tracer = tracer_provider.tracer("quickstart");
    global::set_tracer_provider(tracer_provider);
    
    Ok(tracer)
}

async fn do_work() {
    let tracer = global::tracer("quickstart");
    
    let mut span = tracer
        .span_builder("do_work")
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("work.type", "example"));
    span.set_attribute(KeyValue::new("work.id", 12345));
    
    println!("✅ Working...");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    span.set_status(Status::Ok);
    println!("✅ Work completed!");
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 tracer
    init_tracer()?;
    
    println!("🚀 Starting quickstart...");
    
    // 执行工作
    do_work().await;
    
    // 确保数据被发送
    global::shutdown_tracer_provider();
    
    println!("🎉 Done!");
    Ok(())
}
```

### Step 4: 运行程序

**启动 Jaeger**（用于接收追踪数据）：

```bash
# 使用 Docker 运行 Jaeger
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 4317:4317 \
  -p 4318:4318 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest
```

**运行你的程序**：

```bash
cargo run
```

**输出**：

```text
🚀 Starting quickstart...
✅ Working...
✅ Work completed!
🎉 Done!
```

---

## 📊 添加 Metrics (5分钟)

Metrics 用于记录性能指标（如请求数、延迟、CPU 使用率）。

### Metrics 完整示例

```rust
use opentelemetry::{global, metrics::MeterProvider, KeyValue};
use opentelemetry_sdk::metrics::{MeterProvider as SdkMeterProvider, PeriodicReader};
use std::time::Duration;

fn init_metrics() -> Result<SdkMeterProvider> {
    // 创建 OTLP Metrics 导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::selectors::simple::histogram(vec![])),
            Box::new(opentelemetry_sdk::metrics::aggregators::stateless::temporality_cumulative()),
        )?;

    // 创建 Periodic Reader
    let reader = PeriodicReader::builder(otlp_exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(30))
        .build();

    // 创建 MeterProvider
    let meter_provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .build();

    global::set_meter_provider(meter_provider.clone());
    
    Ok(meter_provider)
}

async fn record_metrics() {
    let meter = global::meter("quickstart");
    
    // 创建 Counter (计数器)
    let request_counter = meter
        .u64_counter("requests.total")
        .with_description("Total number of requests")
        .init();
    
    // 创建 Histogram (直方图)
    let latency_histogram = meter
        .f64_histogram("request.latency")
        .with_description("Request latency in seconds")
        .with_unit("s")
        .init();
    
    // 记录指标
    for i in 0..10 {
        let labels = [
            KeyValue::new("method", "GET"),
            KeyValue::new("status", "200"),
        ];
        
        request_counter.add(1, &labels);
        latency_histogram.record(0.1 * (i as f64), &labels);
        
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    println!("📊 Metrics recorded!");
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 tracer 和 metrics
    init_tracer()?;
    init_metrics()?;
    
    println!("🚀 Starting with metrics...");
    
    // 记录指标
    record_metrics().await;
    
    // 清理
    global::shutdown_tracer_provider();
    
    println!("🎉 Done!");
    Ok(())
}
```

---

## 🌐 HTTP 服务追踪 (10分钟)

让我们创建一个真实的 HTTP 服务，并集成 OpenTelemetry。

**添加 HTTP 依赖**到 `Cargo.toml`：

```toml
[dependencies]
# ... 之前的依赖 ...

# HTTP 框架
axum = "0.7"
tower = "0.4"
tower-http = { version = "0.5", features = ["trace"] }
```

### HTTP 服务器示例

```rust
use axum::{
    routing::get,
    Router,
    extract::Path,
    response::Json,
};
use opentelemetry::{global, trace::{Tracer, Span, Status}, KeyValue};
use serde_json::{json, Value};
use std::net::SocketAddr;

// 初始化函数 (同上)
fn init_tracer() -> Result<sdktrace::Tracer> {
    // ... (同前面的代码)
}

// HTTP 处理函数
async fn hello_handler(Path(name): Path<String>) -> Json<Value> {
    let tracer = global::tracer("quickstart");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("handle_hello")
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("http.route", "/hello/:name"));
    span.set_attribute(KeyValue::new("user.name", name.clone()));
    
    // 模拟处理
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    let response = json!({
        "message": format!("Hello, {}!", name),
        "timestamp": chrono::Utc::now().to_rfc3339()
    });
    
    span.set_status(Status::Ok);
    
    Json(response)
}

async fn health_check() -> &'static str {
    "OK"
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    init_tracer()?;
    
    // 构建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/hello/:name", get(hello_handler));
    
    // 启动服务器
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    println!("🚀 Server listening on http://{}", addr);
    println!("📍 Try: http://localhost:3000/hello/World");
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

### 测试 HTTP 追踪

**启动服务器**：

```bash
cargo run
```

**发送请求**：

```bash
# 健康检查
curl http://localhost:3000/health

# Hello 请求
curl http://localhost:3000/hello/World
curl http://localhost:3000/hello/Rust
curl http://localhost:3000/hello/OpenTelemetry
```

**输出**：

```json
{
  "message": "Hello, World!",
  "timestamp": "2025-10-10T12:00:00Z"
}
```

---

## 🔍 查看追踪数据

### 使用 Jaeger

1. **打开 Jaeger UI**：

   ```text
   http://localhost:16686
   ```

2. **选择服务**：
   - Service: `quickstart-service`

3. **点击 "Find Traces"**

### 查看 Traces

你会看到：

- **Service 名称**: `quickstart-service`
- **Operation**: `handle_hello`, `do_work`
- **Span 详情**:
  - Duration (持续时间)
  - Attributes (属性)
    - `http.route`: `/hello/:name`
    - `user.name`: `World`
  - Status: `OK`

---

## 💡 核心概念速查

### Trace 追踪

```rust
// Trace = 完整的请求链路
// 一个 Trace 包含多个 Span
```

### Span 范围

```rust
// Span = 单个操作单元
let mut span = tracer.span_builder("operation_name").start(&tracer);

// 添加属性
span.set_attribute(KeyValue::new("key", "value"));

// 设置状态
span.set_status(Status::Ok);

// Span 自动结束
```

### Metrics 指标

```rust
// Counter: 只增计数器
let counter = meter.u64_counter("requests").init();
counter.add(1, &labels);

// Histogram: 分布统计
let histogram = meter.f64_histogram("latency").init();
histogram.record(0.123, &labels);

// Gauge: 瞬时值
let gauge = meter.i64_gauge("active_connections").init();
gauge.record(42, &labels);
```

### Logs 日志

```rust
// 集成 tracing crate
use tracing::{info, error};

info!("Request received");
error!("Processing failed");
```

---

## 🎨 最佳实践

### ✅ DO (推荐做法)

```rust
// 1. 使用有意义的 Span 名称
span_builder("handle_user_request")  // ✅ 好
span_builder("operation")            // ❌ 差

// 2. 添加上下文属性
span.set_attribute(KeyValue::new("user.id", user_id));
span.set_attribute(KeyValue::new("order.id", order_id));

// 3. 设置 Span 状态
span.set_status(Status::Ok);  // 成功
span.set_status(Status::error("Database timeout"));  // 失败

// 4. 使用资源标识服务
Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
    KeyValue::new("service.version", "1.0.0"),
    KeyValue::new("deployment.environment", "production"),
]);

// 5. 记录异常
span.record_exception(&error);
```

### ❌ DON'T (避免做法)

```rust
// 1. 不要在循环中创建 Tracer
for item in items {
    let tracer = global::tracer("my-tracer");  // ❌ 每次都创建
}

// 2. 不要忘记关闭 TracerProvider
// ❌ 缺少这行会导致数据丢失
global::shutdown_tracer_provider();

// 3. 不要记录敏感信息
span.set_attribute(KeyValue::new("password", password));  // ❌ 危险！
span.set_attribute(KeyValue::new("credit_card", cc));     // ❌ 危险！

// 4. 不要创建过多 Span
for i in 0..1000000 {
    let span = tracer.span_builder("tiny_op").start(&tracer);  // ❌ 开销巨大
}
```

---

## 🐛 常见问题

### Q1: 为什么看不到追踪数据？

**A**: 检查以下几点：

1. Jaeger 是否启动？

   ```bash
   docker ps | grep jaeger
   ```

2. 端口是否正确？
   - gRPC: `4317`
   - HTTP: `4318`
   - UI: `16686`

3. 是否调用了 `shutdown_tracer_provider()`？

   ```rust
   global::shutdown_tracer_provider();  // 必须调用！
   ```

### Q2: 如何调试 OpenTelemetry？

**A**: 启用日志：

```rust
use tracing_subscriber;

fn main() {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    // 你的代码...
}
```

### Q3: 性能影响有多大？

**A**:

- **生产环境**: 通常 < 1% CPU 开销
- **采样率**: 可配置（如 10% 采样）
- **批量导出**: 减少网络开销

```rust
// 配置采样率
use opentelemetry_sdk::trace::Sampler;

let tracer_provider = TracerProvider::builder()
    .with_config(
        Config::default()
            .with_sampler(Sampler::TraceIdRatioBased(0.1))  // 10% 采样
    )
    .build();
```

---

## 📚 下一步学习

完成快速入门后，建议学习：

1. **中级教程**:
   - 📖 `02_Rust_OTLP_常见模式.md` - 设计模式
   - 📖 数据库追踪 (PostgreSQL, MongoDB)
   - 📖 分布式追踪（跨服务传播）

2. **高级主题**:
   - 📖 自定义 Exporter
   - 📖 性能优化技巧
   - 📖 生产环境部署

3. **实战项目**:
   - 🛠️ 微服务系统完整追踪
   - 🛠️ gRPC 服务监控
   - 🛠️ Kafka 消息追踪

---

## 🔗 快速链接

### 官方文档

- **OpenTelemetry Rust**: <https://github.com/open-telemetry/opentelemetry-rust>
- **OpenTelemetry 规范**: <https://opentelemetry.io/docs/specs/>
- **Jaeger 文档**: <https://www.jaegertracing.io/docs/>

### 示例代码

- **官方示例**: <https://github.com/open-telemetry/opentelemetry-rust/tree/main/examples>
- **完整项目模板**: `33_教程与示例/完整项目模板/`

### 社区

- **Discord**: <https://discord.gg/opentelemetry>
- **GitHub Discussions**: <https://github.com/open-telemetry/opentelemetry-rust/discussions>

---

## 🎉 恭喜

你已经完成了 Rust OpenTelemetry 快速入门！

**你学会了**:

- ✅ 创建 Tracer 和 Span
- ✅ 记录 Metrics
- ✅ HTTP 服务追踪
- ✅ 在 Jaeger 中查看数据

**下一步**: 尝试将 OpenTelemetry 集成到你的实际项目中！

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
