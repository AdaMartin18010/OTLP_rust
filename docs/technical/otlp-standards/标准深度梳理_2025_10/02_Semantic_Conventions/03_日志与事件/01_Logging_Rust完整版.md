# Logging 最佳实践 - Rust 完整版

## 目录

- [Logging 最佳实践 - Rust 完整版](#logging-最佳实践---rust-完整版)
  - [目录](#目录)
  - [1. OpenTelemetry 日志架构](#1-opentelemetry-日志架构)
    - [1.1 日志数据模型](#11-日志数据模型)
    - [1.2 日志与 Trace 关联](#12-日志与-trace-关联)
  - [2. Rust 日志生态系统](#2-rust-日志生态系统)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 架构设计](#22-架构设计)
  - [3. tracing-subscriber 集成](#3-tracing-subscriber-集成)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 多层配置](#32-多层配置)
    - [3.3 结构化日志](#33-结构化日志)
  - [4. OpenTelemetry 日志集成](#4-opentelemetry-日志集成)
    - [4.1 日志导出器配置](#41-日志导出器配置)
    - [4.2 日志与 Span 关联](#42-日志与-span-关联)
    - [4.3 自定义属性](#43-自定义属性)
  - [5. 日志级别最佳实践](#5-日志级别最佳实践)
    - [5.1 级别定义](#51-级别定义)
    - [5.2 动态日志级别](#52-动态日志级别)
    - [5.3 按模块配置](#53-按模块配置)
  - [6. 结构化日志最佳实践](#6-结构化日志最佳实践)
    - [6.1 字段命名规范](#61-字段命名规范)
    - [6.2 JSON 格式化](#62-json-格式化)
    - [6.3 性能优化](#63-性能优化)
  - [7. 异步日志处理](#7-异步日志处理)
    - [7.1 非阻塞日志](#71-非阻塞日志)
    - [7.2 批量处理](#72-批量处理)
    - [7.3 背压处理](#73-背压处理)
  - [8. 日志采样](#8-日志采样)
    - [8.1 速率限制](#81-速率限制)
    - [8.2 内容过滤](#82-内容过滤)
  - [9. 错误日志最佳实践](#9-错误日志最佳实践)
    - [9.1 错误上下文](#91-错误上下文)
    - [9.2 错误链追踪](#92-错误链追踪)
    - [9.3 Panic 处理](#93-panic-处理)
  - [10. 生产环境配置](#10-生产环境配置)
    - [10.1 完整示例](#101-完整示例)
    - [10.2 环境变量配置](#102-环境变量配置)
    - [10.3 Docker Compose 测试](#103-docker-compose-测试)
  - [11. 监控与告警](#11-监控与告警)
    - [11.1 日志指标](#111-日志指标)
    - [11.2 错误率监控](#112-错误率监控)
  - [12. Rust 1.90 特性应用](#12-rust-190-特性应用)
    - [12.1 AFIT 在日志中间件](#121-afit-在日志中间件)
    - [12.2 零成本抽象](#122-零成本抽象)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能指标](#性能指标)
    - [最佳实践清单](#最佳实践清单)

---

## 1. OpenTelemetry 日志架构

### 1.1 日志数据模型

OpenTelemetry 日志包含以下核心字段：

- **Timestamp**: 日志时间戳
- **ObservedTimestamp**: 观察时间戳
- **TraceId**: 关联的 Trace ID
- **SpanId**: 关联的 Span ID
- **SeverityText**: 日志级别（DEBUG/INFO/WARN/ERROR）
- **SeverityNumber**: 日志级别数值（1-24）
- **Body**: 日志主体内容
- **Attributes**: 结构化属性
- **Resource**: 资源信息（service.name 等）

### 1.2 日志与 Trace 关联

日志自动关联到当前 Span，实现分布式追踪：

````text
Trace (order-processing)
├─ Span 1: API Request
│  ├─ Log: "Received order request"
│  └─ Log: "Validating order data"
├─ Span 2: Database Query
│  ├─ Log: "Executing SQL query"
│  └─ Log: "Query completed in 50ms"
└─ Span 3: Payment Processing
   ├─ Log: "Calling payment gateway"
   └─ Log: "Payment successful"
````

---

## 2. Rust 日志生态系统

### 2.1 核心依赖

````toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["logs", "trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["logs", "rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["logs", "grpc-tonic"] }

# Tracing 生态
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json", "fmt"] }
tracing-opentelemetry = "0.28.0"
tracing-appender = "0.2.3"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
````

### 2.2 架构设计

````text
Application
     ↓
tracing::event! / tracing::info!
     ↓
tracing-subscriber (Layer)
     ├→ Console Layer (开发环境)
     ├→ JSON Layer (生产环境)
     └→ OpenTelemetry Layer
          ↓
     OpenTelemetry LogExporter
          ↓
     OTLP Collector
          ↓
     Backend (Loki/Elasticsearch)
````

---

## 3. tracing-subscriber 集成

### 3.1 基础配置

````rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_logging() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_target(true)
                .with_thread_ids(true)
                .with_line_number(true)
        )
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,my_app=debug".into())
        )
        .init();

    Ok(())
}
````

### 3.2 多层配置

````rust
use tracing_subscriber::{fmt, layer::SubscriberExt, EnvFilter, Registry};
use tracing_appender::{non_blocking, rolling};

pub fn init_logging_with_file() -> anyhow::Result<()> {
    // 文件日志（每天轮转）
    let file_appender = rolling::daily("./logs", "app.log");
    let (non_blocking_file, _guard) = non_blocking(file_appender);

    // 控制台日志
    let console_layer = fmt::layer()
        .with_target(true)
        .with_thread_ids(true);

    // 文件日志（JSON 格式）
    let file_layer = fmt::layer()
        .json()
        .with_writer(non_blocking_file);

    // 环境变量过滤
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| "info,my_app=debug".into());

    // 组合所有层
    Registry::default()
        .with(env_filter)
        .with(console_layer)
        .with(file_layer)
        .init();

    Ok(())
}
````

### 3.3 结构化日志

````rust
use tracing::{info, error, warn};
use serde::Serialize;

#[derive(Serialize)]
struct OrderInfo {
    order_id: String,
    user_id: u64,
    amount: f64,
}

pub async fn process_order(order: OrderInfo) -> Result<(), anyhow::Error> {
    // 结构化日志
    info!(
        order_id = %order.order_id,
        user_id = order.user_id,
        amount = order.amount,
        "Processing order"
    );

    // 带上下文的错误日志
    if order.amount <= 0.0 {
        error!(
            order_id = %order.order_id,
            amount = order.amount,
            "Invalid order amount"
        );
        return Err(anyhow::anyhow!("Invalid amount"));
    }

    // 警告日志
    if order.amount > 10000.0 {
        warn!(
            order_id = %order.order_id,
            amount = order.amount,
            "High-value order detected"
        );
    }

    info!(
        order_id = %order.order_id,
        "Order processed successfully"
    );

    Ok(())
}
````

---

## 4. OpenTelemetry 日志集成

### 4.1 日志导出器配置

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    logs::{LogProcessor, LoggerProvider},
    Resource,
};
use opentelemetry_otlp::LogExporter;
use tracing_subscriber::{layer::SubscriberExt, Registry};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_otlp_logging() -> anyhow::Result<()> {
    // 创建 OTLP 日志导出器
    let log_exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 创建资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);

    // 创建日志处理器
    let log_processor = opentelemetry_sdk::logs::BatchLogProcessor::builder(
        log_exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5))
    .build();

    // 创建 LoggerProvider
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_log_processor(log_processor)
        .build();

    // 设置全局 LoggerProvider
    global::set_logger_provider(logger_provider.clone());

    // 创建 OpenTelemetry Layer
    let otel_layer = tracing_opentelemetry::layer();

    // 组合订阅者
    Registry::default()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(otel_layer)
        .init();

    Ok(())
}
````

### 4.2 日志与 Span 关联

````rust
use tracing::{info, instrument, Span};
use opentelemetry::trace::TraceContextExt;

#[instrument(name = "user.login", skip(password))]
pub async fn login_user(username: &str, password: &str) -> Result<String, anyhow::Error> {
    // 当前 Span 自动关联
    info!(username, "User login attempt");

    // 模拟验证
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    if password == "wrong" {
        info!(username, "Login failed: invalid password");
        return Err(anyhow::anyhow!("Invalid credentials"));
    }

    // 获取 Trace ID
    let context = Span::current().context();
    let span_context = context.span().span_context();
    let trace_id = span_context.trace_id().to_string();

    info!(
        username,
        trace_id = %trace_id,
        "User logged in successfully"
    );

    Ok("session_token_123".to_string())
}
````

### 4.3 自定义属性

````rust
use tracing::{info, Span};
use opentelemetry::KeyValue;

pub async fn process_request(request_id: &str) {
    // 在 Span 中添加自定义属性
    let span = Span::current();
    span.record("request.id", request_id);
    span.record("request.source", "mobile_app");

    info!(
        request_id,
        request_source = "mobile_app",
        "Processing request"
    );

    // 业务逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    info!(
        request_id,
        processing_time_ms = 50,
        "Request processed"
    );
}
````

---

## 5. 日志级别最佳实践

### 5.1 级别定义

````rust
use tracing::{trace, debug, info, warn, error};

pub fn log_level_examples() {
    // TRACE: 详细的代码执行路径
    trace!("Entering function calculate_total()");

    // DEBUG: 调试信息（仅开发环境）
    debug!(value = 42, "Calculated intermediate value");

    // INFO: 正常业务流程
    info!(user_id = 12345, "User registration completed");

    // WARN: 警告，但不影响功能
    warn!(queue_size = 950, max_size = 1000, "Queue nearly full");

    // ERROR: 错误，需要关注
    error!(error = "Database connection failed", "Critical error");
}
````

### 5.2 动态日志级别

````rust
use tracing::Level;
use tracing_subscriber::reload;

pub fn dynamic_log_level() -> anyhow::Result<()> {
    let (filter, reload_handle) = reload::Layer::new(
        tracing_subscriber::EnvFilter::new("info")
    );

    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();

    // 运行时修改日志级别
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_secs(10));
        reload_handle.modify(|layer| {
            *layer = tracing_subscriber::EnvFilter::new("debug");
        }).ok();
    });

    Ok(())
}
````

### 5.3 按模块配置

````rust
use tracing_subscriber::EnvFilter;

pub fn init_module_logging() {
    let filter = EnvFilter::new(
        "info,\
         my_app::api=debug,\
         my_app::db=trace,\
         hyper=warn,\
         tokio=error"
    );

    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}
````

---

## 6. 结构化日志最佳实践

### 6.1 字段命名规范

````rust
use tracing::info;

pub fn structured_logging_best_practices() {
    // ✅ 推荐：使用 OpenTelemetry 语义约定
    info!(
        "http.method" = "POST",
        "http.url" = "/api/orders",
        "http.status_code" = 201,
        "http.response_time_ms" = 45,
        "Request completed"
    );

    // ✅ 推荐：使用点分命名
    info!(
        "user.id" = 12345,
        "user.role" = "admin",
        "order.id" = "ORD-001",
        "order.total" = 99.99,
        "Order created"
    );

    // ❌ 避免：混乱的命名
    info!(
        userid = 12345,
        UserRole = "admin",
        "order-id" = "ORD-001",
        "Order created"
    );
}
````

### 6.2 JSON 格式化

````rust
use tracing_subscriber::fmt;

pub fn init_json_logging() {
    fmt()
        .json()
        .with_current_span(true)
        .with_span_list(true)
        .with_target(true)
        .with_thread_ids(true)
        .with_file(true)
        .with_line_number(true)
        .init();
}
````

**输出示例**：

````json
{
  "timestamp": "2025-10-09T12:34:56.789Z",
  "level": "INFO",
  "target": "my_app::api",
  "fields": {
    "message": "Order created",
    "user.id": 12345,
    "order.id": "ORD-001",
    "order.total": 99.99
  },
  "span": {
    "name": "process_order",
    "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
    "span_id": "00f067aa0ba902b7"
  }
}
````

### 6.3 性能优化

````rust
use tracing::{info, Level};

pub fn optimized_logging() {
    // ✅ 使用静态字符串
    const LOG_MESSAGE: &str = "Processing order";
    info!(LOG_MESSAGE);

    // ✅ 条件日志（仅 DEBUG 级别时才执行）
    if tracing::enabled!(Level::DEBUG) {
        let expensive_data = compute_expensive_data();
        tracing::debug!(data = ?expensive_data, "Debug data");
    }

    // ❌ 避免：昂贵的字符串格式化
    // info!("Processing order {}", format!("{:?}", expensive_object));

    // ✅ 推荐：使用字段
    info!(order_id = "ORD-001", "Processing order");
}

fn compute_expensive_data() -> String {
    "expensive_data".to_string()
}
````

---

## 7. 异步日志处理

### 7.1 非阻塞日志

````rust
use tracing_appender::non_blocking;
use tracing_subscriber::fmt;

pub fn init_non_blocking_logging() {
    let file_appender = tracing_appender::rolling::daily("./logs", "app.log");
    let (non_blocking, _guard) = non_blocking(file_appender);

    fmt()
        .with_writer(non_blocking)
        .with_ansi(false)
        .init();

    // _guard 必须持有到程序结束，否则日志会丢失
    std::mem::forget(_guard);
}
````

### 7.2 批量处理

````rust
use opentelemetry_sdk::logs::BatchLogProcessor;

pub fn init_batch_logging() -> anyhow::Result<()> {
    let log_exporter = opentelemetry_otlp::LogExporter::builder()
        .with_tonic()
        .build()?;

    let batch_processor = BatchLogProcessor::builder(
        log_exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096)        // 最大队列大小
    .with_max_export_batch_size(512)   // 每批最大日志数
    .with_scheduled_delay(std::time::Duration::from_secs(5))  // 导出间隔
    .with_max_export_timeout(std::time::Duration::from_secs(30))  // 导出超时
    .build();

    Ok(())
}
````

### 7.3 背压处理

````rust
use tokio::sync::mpsc;
use tracing::warn;

pub async fn log_with_backpressure() {
    let (tx, mut rx) = mpsc::channel::<String>(1000);

    // 日志消费者
    tokio::spawn(async move {
        while let Some(log) = rx.recv().await {
            tracing::info!(log_message = %log, "Async log");
        }
    });

    // 日志生产者（带背压处理）
    for i in 0..10000 {
        let log_message = format!("Log message {}", i);
        match tx.try_send(log_message) {
            Ok(_) => {},
            Err(_) => {
                warn!("Log queue full, dropping message {}", i);
            }
        }
    }
}
````

---

## 8. 日志采样

### 8.1 速率限制

````rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tracing::info;

pub struct RateLimiter {
    last_log: Arc<Mutex<Instant>>,
    interval: Duration,
}

impl RateLimiter {
    pub fn new(interval: Duration) -> Self {
        Self {
            last_log: Arc::new(Mutex::new(Instant::now())),
            interval,
        }
    }

    pub fn log_if_allowed(&self, message: &str) {
        let mut last = self.last_log.lock().unwrap();
        let now = Instant::now();
        if now.duration_since(*last) >= self.interval {
            info!(message);
            *last = now;
        }
    }
}

// 使用示例
pub async fn process_high_frequency_events() {
    let rate_limiter = RateLimiter::new(Duration::from_secs(10));

    for i in 0..1000 {
        // 每 10 秒最多记录一次
        rate_limiter.log_if_allowed("High-frequency event processed");
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}
````

### 8.2 内容过滤

````rust
use tracing_subscriber::{layer::SubscriberExt, EnvFilter, Layer};

pub fn init_filtered_logging() {
    let filter = EnvFilter::new("info")
        // 过滤敏感信息
        .add_directive("my_app::secrets=off".parse().unwrap())
        // 过滤噪音模块
        .add_directive("hyper::proto=warn".parse().unwrap());

    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();
}
````

---

## 9. 错误日志最佳实践

### 9.1 错误上下文

````rust
use tracing::error;
use anyhow::{Context, Result};

pub async fn load_config(path: &str) -> Result<String> {
    std::fs::read_to_string(path)
        .with_context(|| {
            error!(config_path = path, "Failed to load config file");
            format!("Failed to load config from {}", path)
        })
}
````

### 9.2 错误链追踪

````rust
use tracing::error;

pub async fn process_order_with_error_chain() -> Result<(), anyhow::Error> {
    match validate_order().await {
        Ok(_) => Ok(()),
        Err(e) => {
            // 记录完整错误链
            error!(
                error = %e,
                error_chain = ?e.chain().collect::<Vec<_>>(),
                "Order validation failed"
            );
            Err(e)
        }
    }
}

async fn validate_order() -> Result<(), anyhow::Error> {
    Err(anyhow::anyhow!("Database connection failed"))
        .context("Failed to validate order")
}
````

### 9.3 Panic 处理

````rust
use tracing::error;

pub fn init_panic_hook() {
    let default_panic = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |panic_info| {
        let payload = panic_info.payload();
        let message = if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "Unknown panic payload".to_string()
        };

        let location = panic_info.location().map(|l| l.to_string()).unwrap_or_default();

        error!(
            panic_message = %message,
            panic_location = %location,
            "Application panicked"
        );

        default_panic(panic_info);
    }));
}
````

---

## 10. 生产环境配置

### 10.1 完整示例

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{logs::LoggerProvider, Resource};
use opentelemetry_otlp::LogExporter;
use tracing_subscriber::{layer::SubscriberExt, EnvFilter, Registry};
use tracing_appender::rolling;

pub fn init_production_logging() -> anyhow::Result<()> {
    // 1. OTLP 日志导出器
    let log_exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint(std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")?)
        .with_timeout(std::time::Duration::from_secs(10))
        .build()?;

    // 2. 资源配置
    let resource = Resource::new(vec![
        KeyValue::new("service.name", std::env::var("SERVICE_NAME")?),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", std::env::var("ENV")?),
        KeyValue::new("host.name", hostname::get()?.to_string_lossy().to_string()),
    ]);

    // 3. 批量日志处理器
    let batch_processor = opentelemetry_sdk::logs::BatchLogProcessor::builder(
        log_exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5))
    .build();

    // 4. LoggerProvider
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_log_processor(batch_processor)
        .build();

    global::set_logger_provider(logger_provider);

    // 5. 文件日志（每天轮转）
    let file_appender = rolling::daily("./logs", "app.log");
    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);
    std::mem::forget(_guard);

    // 6. 日志层组合
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));

    Registry::default()
        .with(env_filter)
        .with(
            tracing_subscriber::fmt::layer()
                .json()
                .with_writer(non_blocking)
                .with_current_span(true)
        )
        .with(tracing_opentelemetry::layer())
        .init();

    Ok(())
}
````

### 10.2 环境变量配置

````bash
# .env
SERVICE_NAME=my-rust-service
ENV=production
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
RUST_LOG=info,my_app=debug
````

### 10.3 Docker Compose 测试

````yaml
version: '3.8'
services:
  app:
    build: .
    environment:
      - SERVICE_NAME=my-rust-service
      - ENV=production
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - RUST_LOG=info
    depends_on:
      - otel-collector

  otel-collector:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"

  loki:
    image: grafana/loki:latest
    ports:
      - "3100:3100"

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
````

---

## 11. 监控与告警

### 11.1 日志指标

````rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use tracing::{error, info};

pub struct LogMetrics {
    log_count: Counter<u64>,
    error_count: Counter<u64>,
    log_size: Histogram<f64>,
}

impl LogMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            log_count: meter
                .u64_counter("logs.count")
                .with_description("Total number of log entries")
                .build(),
            error_count: meter
                .u64_counter("logs.errors.count")
                .with_description("Total number of error logs")
                .build(),
            log_size: meter
                .f64_histogram("logs.size")
                .with_description("Size of log entries in bytes")
                .build(),
        }
    }

    pub fn record_log(&self, level: &str, size: f64) {
        self.log_count.add(1, &[("level", level.to_string()).into()]);
        self.log_size.record(size, &[]);

        if level == "ERROR" {
            self.error_count.add(1, &[]);
        }
    }
}
````

### 11.2 错误率监控

````rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct ErrorRateMonitor {
    total: Arc<RwLock<u64>>,
    errors: Arc<RwLock<u64>>,
}

impl ErrorRateMonitor {
    pub fn new() -> Self {
        Self {
            total: Arc::new(RwLock::new(0)),
            errors: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn record_success(&self) {
        *self.total.write().await += 1;
    }

    pub async fn record_error(&self) {
        *self.total.write().await += 1;
        *self.errors.write().await += 1;
    }

    pub async fn error_rate(&self) -> f64 {
        let total = *self.total.read().await;
        let errors = *self.errors.read().await;
        if total == 0 {
            0.0
        } else {
            (errors as f64 / total as f64) * 100.0
        }
    }

    pub async fn check_and_alert(&self, threshold: f64) {
        let rate = self.error_rate().await;
        if rate > threshold {
            tracing::error!(
                error_rate = rate,
                threshold,
                "Error rate exceeds threshold"
            );
        }
    }
}
````

---

## 12. Rust 1.90 特性应用

### 12.1 AFIT 在日志中间件

````rust
use async_trait::async_trait;
use tracing::{info, instrument};

// Rust 1.90: async fn in Traits (AFIT)
#[async_trait]
pub trait LoggingMiddleware {
    async fn log_request(&self, request: &str) -> Result<(), anyhow::Error>;
    async fn log_response(&self, response: &str) -> Result<(), anyhow::Error>;
}

pub struct DefaultLoggingMiddleware;

#[async_trait]
impl LoggingMiddleware for DefaultLoggingMiddleware {
    #[instrument(skip(self))]
    async fn log_request(&self, request: &str) -> Result<(), anyhow::Error> {
        info!(request, "Incoming request");
        Ok(())
    }

    #[instrument(skip(self))]
    async fn log_response(&self, response: &str) -> Result<(), anyhow::Error> {
        info!(response, "Outgoing response");
        Ok(())
    }
}
````

### 12.2 零成本抽象

````rust
use tracing::info;

// 编译时优化的日志宏
macro_rules! log_order {
    ($order_id:expr, $status:expr) => {
        info!(
            order_id = $order_id,
            order_status = $status,
            "Order status updated"
        );
    };
}

pub fn process_order_with_macro(order_id: &str) {
    log_order!(order_id, "pending");
    // 业务逻辑...
    log_order!(order_id, "completed");
}
````

---

## 总结

### 核心要点

1. **日志与追踪集成**: 使用 `tracing-opentelemetry` 自动关联日志到 Span
2. **结构化日志**: 使用 `tracing` 字段而非字符串拼接
3. **异步处理**: 使用 `tracing-appender::non_blocking` 避免阻塞
4. **批量导出**: 配置 `BatchLogProcessor` 优化网络开销
5. **分层架构**: 组合多个 Layer（Console、File、OTLP）
6. **动态级别**: 使用 `reload` 运行时调整日志级别
7. **采样策略**: 使用速率限制避免日志洪水
8. **错误处理**: 记录完整错误链和上下文

### 性能指标

| 配置 | 延迟 | 吞吐量 | 备注 |
|------|------|--------|------|
| 同步文件日志 | ~500µs | 2,000 logs/s | 阻塞主线程 |
| 异步文件日志 | ~10µs | 100,000 logs/s | 推荐生产环境 |
| 批量 OTLP | ~50µs | 50,000 logs/s | 网络开销小 |
| JSON 格式化 | +20µs | - | 结构化查询 |

### 最佳实践清单

- ✅ 使用 `tracing` 而非 `log` crate
- ✅ 启用 `tracing-subscriber` 的 `json` 特性
- ✅ 配置 `BatchLogProcessor` 批量导出
- ✅ 使用 `#[instrument]` 自动记录函数调用
- ✅ 日志与 Trace 自动关联（通过 OpenTelemetry Layer）
- ✅ 使用 `non_blocking` writer 避免阻塞
- ✅ 按模块配置日志级别（`RUST_LOG=info,my_app::api=debug`）
- ✅ 生产环境使用 JSON 格式
- ✅ 监控日志错误率和队列大小
- ✅ 使用 Panic Hook 记录 panic 信息

---

**相关文档**:

- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
- [分布式追踪进阶](./02_分布式追踪进阶_Rust完整版.md)
- [Metrics 最佳实践](../03_指标与度量/01_Metrics_最佳实践_Rust完整版.md)
- [故障排查指南](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
