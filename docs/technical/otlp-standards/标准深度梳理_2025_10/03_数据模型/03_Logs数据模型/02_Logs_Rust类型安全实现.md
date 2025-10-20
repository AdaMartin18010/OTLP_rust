# OpenTelemetry Logs - Rust 类型安全实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [OpenTelemetry Logs - Rust 类型安全实现](#opentelemetry-logs---rust-类型安全实现)
  - [目录](#目录)
  - [概述](#概述)
    - [Rust Logs 特性](#rust-logs-特性)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [LogRecord 类型定义](#logrecord-类型定义)
    - [1. Severity 级别](#1-severity-级别)
    - [2. LogRecord 结构](#2-logrecord-结构)
    - [3. Body 类型](#3-body-类型)
  - [Logs SDK 集成](#logs-sdk-集成)
    - [1. Logger 初始化](#1-logger-初始化)
    - [2. 基础日志记录](#2-基础日志记录)
  - [与 Tracing 生态集成](#与-tracing-生态集成)
    - [1. Tracing 桥接](#1-tracing-桥接)
    - [2. 结构化日志](#2-结构化日志)
  - [日志与 Trace 关联](#日志与-trace-关联)
    - [1. 自动关联](#1-自动关联)
    - [2. 手动关联](#2-手动关联)
  - [日志处理器](#日志处理器)
    - [1. 批处理器](#1-批处理器)
    - [2. 过滤器](#2-过滤器)
  - [日志导出器](#日志导出器)
    - [1. OTLP 导出器](#1-otlp-导出器)
    - [2. 自定义导出器](#2-自定义导出器)
  - [高级特性](#高级特性)
    - [1. 日志采样](#1-日志采样)
    - [2. 日志丰富](#2-日志丰富)
  - [最佳实践](#最佳实践)
    - [1. 日志级别选择](#1-日志级别选择)
    - [2. 性能优化](#2-性能优化)
    - [3. 安全考虑](#3-安全考虑)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Rust Logs 特性

- **类型安全**: 编译时保证日志字段正确性
- **零拷贝**: 高效的日志序列化
- **异步优先**: 非阻塞日志记录
- **与 Trace 集成**: 自动关联 TraceContext
- **结构化日志**: 强类型结构化数据

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "otlp-logs-rust"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["logs"] }
opentelemetry_sdk = { version = "0.31.0", features = ["logs", "rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json", "logs"] }

# Tracing 生态
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29.0"
tracing-log = "0.2.0"

# 日志框架
log = "0.4.22"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.138"

# 时间处理
chrono = "0.4.39"
```

---

## LogRecord 类型定义

### 1. Severity 级别

```rust
use std::fmt;

/// OpenTelemetry 日志严重性级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Severity {
    /// Trace: 细粒度调试信息 (1-4)
    Trace = 1,
    Trace2 = 2,
    Trace3 = 3,
    Trace4 = 4,
    
    /// Debug: 调试信息 (5-8)
    Debug = 5,
    Debug2 = 6,
    Debug3 = 7,
    Debug4 = 8,
    
    /// Info: 一般信息 (9-12)
    Info = 9,
    Info2 = 10,
    Info3 = 11,
    Info4 = 12,
    
    /// Warn: 警告信息 (13-16)
    Warn = 13,
    Warn2 = 14,
    Warn3 = 15,
    Warn4 = 16,
    
    /// Error: 错误信息 (17-20)
    Error = 17,
    Error2 = 18,
    Error3 = 19,
    Error4 = 20,
    
    /// Fatal: 致命错误 (21-24)
    Fatal = 21,
    Fatal2 = 22,
    Fatal3 = 23,
    Fatal4 = 24,
}

impl Severity {
    /// 从 tracing Level 转换
    pub fn from_tracing_level(level: &tracing::Level) -> Self {
        match *level {
            tracing::Level::TRACE => Self::Trace,
            tracing::Level::DEBUG => Self::Debug,
            tracing::Level::INFO => Self::Info,
            tracing::Level::WARN => Self::Warn,
            tracing::Level::ERROR => Self::Error,
        }
    }

    /// 转换为字符串
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Trace | Self::Trace2 | Self::Trace3 | Self::Trace4 => "TRACE",
            Self::Debug | Self::Debug2 | Self::Debug3 | Self::Debug4 => "DEBUG",
            Self::Info | Self::Info2 | Self::Info3 | Self::Info4 => "INFO",
            Self::Warn | Self::Warn2 | Self::Warn3 | Self::Warn4 => "WARN",
            Self::Error | Self::Error2 | Self::Error3 | Self::Error4 => "ERROR",
            Self::Fatal | Self::Fatal2 | Self::Fatal3 | Self::Fatal4 => "FATAL",
        }
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
```

### 2. LogRecord 结构

```rust
use opentelemetry::{KeyValue, trace::{TraceId, SpanId, TraceFlags}};
use std::time::SystemTime;
use std::collections::HashMap;

/// OpenTelemetry LogRecord
#[derive(Debug, Clone)]
pub struct LogRecord {
    /// 时间戳
    pub timestamp: SystemTime,
    
    /// 观测时间戳（可选）
    pub observed_timestamp: Option<SystemTime>,
    
    /// 严重性级别
    pub severity_number: Severity,
    
    /// 严重性文本
    pub severity_text: String,
    
    /// 日志内容（核心）
    pub body: LogBody,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
    
    /// TraceContext（用于关联）
    pub trace_id: Option<TraceId>,
    pub span_id: Option<SpanId>,
    pub trace_flags: Option<TraceFlags>,
}

impl LogRecord {
    /// 创建新的 LogRecord
    pub fn new(severity: Severity, body: LogBody) -> Self {
        Self {
            timestamp: SystemTime::now(),
            observed_timestamp: None,
            severity_number: severity,
            severity_text: severity.to_string(),
            body,
            attributes: Vec::new(),
            trace_id: None,
            span_id: None,
            trace_flags: None,
        }
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }

    /// 设置 TraceContext
    pub fn with_trace_context(
        mut self,
        trace_id: TraceId,
        span_id: SpanId,
        trace_flags: TraceFlags,
    ) -> Self {
        self.trace_id = Some(trace_id);
        self.span_id = Some(span_id);
        self.trace_flags = Some(trace_flags);
        self
    }

    /// 判断是否与 Trace 关联
    pub fn is_trace_linked(&self) -> bool {
        self.trace_id.is_some() && self.span_id.is_some()
    }
}
```

### 3. Body 类型

```rust
use serde_json::Value as JsonValue;

/// 日志内容类型
#[derive(Debug, Clone)]
pub enum LogBody {
    /// 字符串类型
    String(String),
    
    /// 布尔类型
    Bool(bool),
    
    /// 整数类型
    Int(i64),
    
    /// 浮点类型
    Double(f64),
    
    /// 字节数组
    Bytes(Vec<u8>),
    
    /// 键值对数组（结构化日志）
    Map(HashMap<String, LogBody>),
    
    /// 数组
    Array(Vec<LogBody>),
}

impl LogBody {
    /// 转换为 JSON
    pub fn to_json(&self) -> JsonValue {
        match self {
            Self::String(s) => JsonValue::String(s.clone()),
            Self::Bool(b) => JsonValue::Bool(*b),
            Self::Int(i) => JsonValue::Number((*i).into()),
            Self::Double(d) => JsonValue::Number(
                serde_json::Number::from_f64(*d).unwrap_or(serde_json::Number::from(0))
            ),
            Self::Bytes(b) => JsonValue::String(base64::encode(b)),
            Self::Map(m) => {
                let mut map = serde_json::Map::new();
                for (k, v) in m {
                    map.insert(k.clone(), v.to_json());
                }
                JsonValue::Object(map)
            }
            Self::Array(a) => JsonValue::Array(a.iter().map(|v| v.to_json()).collect()),
        }
    }
}

impl From<String> for LogBody {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

impl From<&str> for LogBody {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<i64> for LogBody {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl From<f64> for LogBody {
    fn from(d: f64) -> Self {
        Self::Double(d)
    }
}

impl From<bool> for LogBody {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}
```

---

## Logs SDK 集成

### 1. Logger 初始化

```rust
use opentelemetry::global;
use opentelemetry_sdk::{runtime, logs::LoggerProvider};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化日志系统
pub fn init_logging() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry Logger Provider
    let logger_provider = opentelemetry_otlp::new_pipeline()
        .logging()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/logs"),
        )
        .with_resource(opentelemetry_sdk::Resource::new(vec![
            opentelemetry::KeyValue::new("service.name", "rust-log-service"),
            opentelemetry::KeyValue::new("service.version", "1.0.0"),
        ]))
        .install_batch(runtime::Tokio)?;

    // 设置全局 Logger Provider
    global::set_logger_provider(logger_provider.clone());

    // 初始化 tracing-subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer())
        .init();

    Ok(())
}
```

### 2. 基础日志记录

```rust
use tracing::{trace, debug, info, warn, error};

/// 基础日志示例
pub fn basic_logging_example() {
    // Trace 级别
    trace!("Entering function");
    
    // Debug 级别
    debug!(user_id = "123", "Processing user request");
    
    // Info 级别
    info!(
        order_id = "ORD-456",
        amount = 99.99,
        "Order created successfully"
    );
    
    // Warn 级别
    warn!(
        retry_count = 3,
        "High retry count detected"
    );
    
    // Error 级别
    error!(
        error_code = "DB_CONNECTION_FAILED",
        details = "Connection timeout after 30s",
        "Database connection failed"
    );
}
```

---

## 与 Tracing 生态集成

### 1. Tracing 桥接

```rust
use tracing::{info_span, Instrument};

/// 在 Span 上下文中记录日志
pub async fn logging_with_span() {
    let span = info_span!(
        "process_order",
        order_id = "ORD-789",
        user_id = "USER-123"
    );

    async {
        info!("Order processing started");
        
        // 模拟处理
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        info!(items_count = 5, "Order items validated");
        
        warn!(inventory_low = true, "Low inventory detected");
        
        info!("Order processing completed");
    }
    .instrument(span)
    .await;
}
```

### 2. 结构化日志

```rust
use serde::{Serialize, Deserialize};
use tracing::info;

#[derive(Debug, Serialize, Deserialize)]
pub struct OrderEvent {
    pub order_id: String,
    pub user_id: String,
    pub total_amount: f64,
    pub items_count: u32,
    pub status: String,
}

/// 结构化日志记录
pub fn structured_logging(event: &OrderEvent) {
    info!(
        order_id = %event.order_id,
        user_id = %event.user_id,
        total_amount = event.total_amount,
        items_count = event.items_count,
        status = %event.status,
        event_type = "order_created",
        "Order event recorded"
    );
}
```

---

## 日志与 Trace 关联

### 1. 自动关联

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry::global;
use tracing::{info, instrument};

/// 日志自动关联 Trace
#[instrument]
pub async fn auto_trace_linking() {
    info!("This log is automatically linked to the current span");
    
    // 嵌套 Span
    do_work().await;
}

#[instrument]
async fn do_work() {
    info!("Nested span - log also linked");
}
```

### 2. 手动关联

```rust
use opentelemetry::trace::{SpanContext, TraceContextExt};
use tracing::Span;

/// 手动关联 TraceContext
pub fn manual_trace_linking() {
    let current_span = Span::current();
    
    // 获取当前 SpanContext
    let cx = opentelemetry::Context::current();
    let span_context = cx.span().span_context();
    
    if span_context.is_valid() {
        info!(
            trace_id = %span_context.trace_id(),
            span_id = %span_context.span_id(),
            "Manually linked log to trace"
        );
    }
}
```

---

## 日志处理器

### 1. 批处理器

```rust
use opentelemetry_sdk::logs::{BatchLogProcessor, LoggerProvider};
use opentelemetry_sdk::runtime;
use std::time::Duration;

/// 创建批处理日志处理器
pub fn create_batch_processor() -> Result<LoggerProvider, Box<dyn std::error::Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .http()
        .with_endpoint("http://localhost:4318/v1/logs")
        .build_log_exporter()?;

    let batch_config = opentelemetry_sdk::logs::BatchConfigBuilder::default()
        .with_max_queue_size(4096)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .build();

    let processor = BatchLogProcessor::builder(exporter, runtime::Tokio)
        .with_batch_config(batch_config)
        .build();

    let provider = LoggerProvider::builder()
        .with_log_processor(processor)
        .build();

    Ok(provider)
}
```

### 2. 过滤器

```rust
use tracing_subscriber::filter::{EnvFilter, LevelFilter};

/// 创建日志过滤器
pub fn create_log_filter() -> EnvFilter {
    EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy()
        .add_directive("my_app=debug".parse().unwrap())
        .add_directive("tokio=info".parse().unwrap())
        .add_directive("hyper=warn".parse().unwrap())
}

/// 应用过滤器
pub fn init_with_filter() {
    let filter = create_log_filter();
    
    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();
}
```

---

## 日志导出器

### 1. OTLP 导出器

```rust
use opentelemetry_otlp::{WithExportConfig, Protocol};

/// HTTP OTLP 导出器
pub fn create_http_exporter() -> Result<(), Box<dyn std::error::Error>> {
    let _ = opentelemetry_otlp::new_pipeline()
        .logging()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/logs")
                .with_protocol(Protocol::HttpBinary)
                .with_timeout(Duration::from_secs(10)),
        )
        .install_batch(runtime::Tokio)?;

    Ok(())
}

/// gRPC OTLP 导出器
pub fn create_grpc_exporter() -> Result<(), Box<dyn std::error::Error>> {
    let _ = opentelemetry_otlp::new_pipeline()
        .logging()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(runtime::Tokio)?;

    Ok(())
}
```

### 2. 自定义导出器

```rust
use opentelemetry_sdk::export::logs::{LogData, LogExporter};
use async_trait::async_trait;

/// 自定义日志导出器
pub struct CustomLogExporter {
    // 自定义字段
}

#[async_trait]
impl LogExporter for CustomLogExporter {
    async fn export(&mut self, batch: Vec<LogData>) -> opentelemetry::logs::LogResult<()> {
        for log in batch {
            // 自定义导出逻辑
            println!("Exporting log: {:?}", log);
        }
        Ok(())
    }
}
```

---

## 高级特性

### 1. 日志采样

```rust
use rand::Rng;

/// 简单采样器
pub struct LogSampler {
    sample_rate: f64, // 0.0 ~ 1.0
}

impl LogSampler {
    pub fn new(sample_rate: f64) -> Self {
        Self {
            sample_rate: sample_rate.clamp(0.0, 1.0),
        }
    }

    pub fn should_sample(&self) -> bool {
        let mut rng = rand::thread_rng();
        rng.gen::<f64>() < self.sample_rate
    }
}

/// 带采样的日志
pub fn sampled_logging(sampler: &LogSampler) {
    if sampler.should_sample() {
        info!("This log is sampled");
    }
}
```

### 2. 日志丰富

```rust
use tracing::Subscriber;
use tracing_subscriber::layer::{Context, Layer};

/// 日志丰富 Layer
pub struct LogEnrichmentLayer {
    environment: String,
    version: String,
}

impl LogEnrichmentLayer {
    pub fn new(environment: String, version: String) -> Self {
        Self {
            environment,
            version,
        }
    }
}

impl<S: Subscriber> Layer<S> for LogEnrichmentLayer {
    fn on_event(
        &self,
        event: &tracing::Event<'_>,
        _ctx: Context<'_, S>,
    ) {
        // 为每个日志添加额外的上下文
        event.record("environment", &self.environment.as_str());
        event.record("version", &self.version.as_str());
    }
}
```

---

## 最佳实践

### 1. 日志级别选择

```rust
// ✅ 推荐
trace!("Function entry/exit");
debug!(variable = ?some_var, "Debug variable state");
info!("Important business event");
warn!("Recoverable issue detected");
error!(error = %e, "Critical error occurred");

// ❌ 避免
info!("x = {}", x); // 应该用 debug!
error!("User logged in"); // 应该用 info!
```

### 2. 性能优化

```rust
use tracing::enabled;

// ✅ 避免不必要的格式化
if enabled!(tracing::Level::DEBUG) {
    let expensive_data = calculate_expensive_debug_info();
    debug!(data = ?expensive_data, "Debug info");
}

// ✅ 使用结构化字段而非字符串格式化
info!(
    user_id = user.id,
    order_id = order.id,
    "Order created"
);
```

### 3. 安全考虑

```rust
use tracing::field;

// ❌ 不要记录敏感信息
error!(password = %password, "Login failed"); // 危险！

// ✅ 脱敏处理
info!(
    user_id = user.id,
    email = %mask_email(&user.email),
    "User login"
);

fn mask_email(email: &str) -> String {
    if let Some(at_pos) = email.find('@') {
        let (local, domain) = email.split_at(at_pos);
        format!("{}***@{}", &local[..2.min(local.len())], &domain[1..])
    } else {
        "***".to_string()
    }
}
```

---

## 完整示例

### main.rs

```rust
use anyhow::Result;
use opentelemetry::global;
use tracing::{info, warn, error, instrument};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志系统
    init_logging()?;

    info!("Application started");

    // 业务逻辑
    process_order("ORD-123", "USER-456").await?;

    // 关闭
    global::shutdown_logger_provider();

    Ok(())
}

#[instrument]
async fn process_order(order_id: &str, user_id: &str) -> Result<()> {
    info!(
        order_id = order_id,
        user_id = user_id,
        "Processing order"
    );

    // 模拟处理
    validate_order(order_id).await?;
    charge_payment(order_id).await?;
    send_notification(user_id).await?;

    info!("Order processed successfully");

    Ok(())
}

#[instrument]
async fn validate_order(order_id: &str) -> Result<()> {
    info!("Validating order");
    
    // 模拟验证逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Ok(())
}

#[instrument]
async fn charge_payment(order_id: &str) -> Result<()> {
    warn!(order_id = order_id, "Payment gateway slow");
    
    // 模拟支付
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    Ok(())
}

#[instrument]
async fn send_notification(user_id: &str) -> Result<()> {
    info!("Sending notification");
    
    // 模拟发送
    tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    
    Ok(())
}
```

---

## 总结

本文档提供了 OpenTelemetry Logs 在 Rust 1.90 环境下的完整类型安全实现：

1. ✅ **类型定义**: 完整的 Severity、LogRecord、LogBody 类型
2. ✅ **SDK 集成**: Logger Provider 和 Exporter 配置
3. ✅ **Tracing 集成**: 与 tracing 生态无缝集成
4. ✅ **Trace 关联**: 自动和手动关联 TraceContext
5. ✅ **日志处理**: 批处理、过滤、采样、丰富
6. ✅ **最佳实践**: 性能优化、安全考虑、日志级别选择

通过本文档的指导，您可以构建高性能、类型安全、可观测性强的 Rust 日志系统。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
