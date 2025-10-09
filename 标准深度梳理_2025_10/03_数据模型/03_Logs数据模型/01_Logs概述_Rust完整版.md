# OpenTelemetry Logs 数据模型 - Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月9日

---

## 目录

- [1. Rust 中的 Logs 概述](#1-rust-中的-logs-概述)
- [2. LogRecord 核心结构](#2-logrecord-核心结构)
- [3. Rust 类型安全实现](#3-rust-类型安全实现)
- [4. 与 tracing 集成](#4-与-tracing-集成)
- [5. 日志与 Trace 关联](#5-日志与-trace-关联)
- [6. 日志框架集成](#6-日志框架集成)
- [7. 异步日志处理](#7-异步日志处理)
- [8. 结构化日志](#8-结构化日志)
- [9. 日志导出与后端](#9-日志导出与后端)
- [10. 性能优化](#10-性能优化)
- [11. 测试与验证](#11-测试与验证)
- [12. 最佳实践](#12-最佳实践)

---

## 1. Rust 中的 Logs 概述

### 1.1 什么是 OpenTelemetry Logs

**定义**：

```text
OpenTelemetry Logs: 标准化的日志数据模型

Rust 实现特点:
1. 类型安全
   - Severity: 枚举类型保证合法值
   - Body: 泛型 AnyValue 支持多种类型

2. 零成本抽象
   - 编译时优化
   - 无运行时开销

3. 并发安全
   - Send + Sync 保证
   - Arc<RwLock<_>> 线程安全

4. 生命周期管理
   - RAII 自动清理
   - Drop trait 资源回收

5. 异步友好
   - async/await 集成
   - 批量导出优化
```

### 1.2 依赖配置

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "logs"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic", "logs"] }
opentelemetry-semantic-conventions = "0.31"

# 日志集成
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 错误处理
anyhow = "1.0"
thiserror = "1.0"
```

### 1.3 初始化 Logs

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    logs::{LoggerProvider, Logger},
    Resource,
};
use opentelemetry_otlp::LogExporter;
use opentelemetry_semantic_conventions::resource::{SERVICE_NAME, SERVICE_VERSION};
use anyhow::Result;

/// 初始化 OpenTelemetry Logs
///
/// # 功能
/// - 创建 OTLP Exporter (gRPC)
/// - 配置 BatchLogProcessor
/// - 注册全局 LoggerProvider
/// - 设置 Resource 属性
pub async fn init_logs() -> Result<LoggerProvider> {
    // 1. 创建 OTLP Exporter
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 2. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, "rust-logs-service"),
        KeyValue::new(SERVICE_VERSION, "1.0.0"),
    ]);

    // 3. 创建 LoggerProvider
    let provider = LoggerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_resource(resource)
        .build();

    // 4. 注册全局 LoggerProvider
    global::set_logger_provider(provider.clone());

    Ok(provider)
}

/// 优雅关闭 Logs
pub async fn shutdown_logs(provider: LoggerProvider) -> Result<()> {
    provider.shutdown()?;
    Ok(())
}
```

---

## 2. LogRecord 核心结构

### 2.1 LogRecord Rust 实现

```rust
use opentelemetry::logs::{LogRecord, Logger, Severity};
use opentelemetry::{global, KeyValue};
use std::time::SystemTime;

/// LogRecord 基础示例
pub fn basic_log_example() {
    let logger = global::logger("my-app");

    // 创建 LogRecord
    let mut log_record = LogRecord::default();
    log_record.set_timestamp(SystemTime::now());
    log_record.set_observed_timestamp(SystemTime::now());
    log_record.set_severity_number(Severity::Info);
    log_record.set_severity_text("INFO");
    log_record.set_body("User login successful".into());
    log_record.set_attributes(vec![
        KeyValue::new("user.id", "user-123"),
        KeyValue::new("user.email", "user@example.com"),
    ]);

    // 发送日志
    logger.emit(log_record);
}
```

### 2.2 Severity 枚举

```rust
use opentelemetry::logs::Severity;

/// Severity 级别映射
///
/// OpenTelemetry 定义了 24 个严重性级别，分为 6 个范围
pub fn severity_examples() {
    let trace = Severity::Trace;   // 1
    let debug = Severity::Debug;   // 5
    let info = Severity::Info;     // 9
    let warn = Severity::Warn;     // 13
    let error = Severity::Error;   // 17
    let fatal = Severity::Fatal;   // 21

    // 使用示例
    let mut log_record = LogRecord::default();
    log_record.set_severity_number(info);
    log_record.set_severity_text("INFO");
}

/// 从字符串转换
pub fn severity_from_str(level: &str) -> Severity {
    match level.to_uppercase().as_str() {
        "TRACE" => Severity::Trace,
        "DEBUG" => Severity::Debug,
        "INFO" => Severity::Info,
        "WARN" => Severity::Warn,
        "ERROR" => Severity::Error,
        "FATAL" => Severity::Fatal,
        _ => Severity::Info,
    }
}
```

### 2.3 Body 类型

```rust
use opentelemetry::logs::AnyValue;
use std::collections::HashMap;

/// Body 支持的类型
pub fn body_type_examples() {
    // 1. String
    let body_string: AnyValue = "Error occurred".into();

    // 2. i64
    let body_int: AnyValue = 12345i64.into();

    // 3. f64
    let body_float: AnyValue = 3.14159f64.into();

    // 4. bool
    let body_bool: AnyValue = true.into();

    // 5. Vec<AnyValue> (Array)
    let body_array: AnyValue = vec![
        AnyValue::String("item1".into()),
        AnyValue::String("item2".into()),
    ].into();

    // 6. HashMap<String, AnyValue> (Map)
    let mut map = HashMap::new();
    map.insert("event".to_string(), AnyValue::String("order_created".into()));
    map.insert("order_id".to_string(), AnyValue::String("ORD-12345".into()));
    map.insert("amount".to_string(), AnyValue::Double(99.99));
    let body_map: AnyValue = map.into();
}
```

---

## 3. Rust 类型安全实现

### 3.1 类型安全的日志包装器

```rust
use opentelemetry::logs::{LogRecord, Logger, Severity};
use opentelemetry::{global, KeyValue, trace::{TraceContextExt, TraceId, SpanId}};
use std::time::SystemTime;

/// 类型安全的日志记录器
pub struct TypedLogger {
    logger: Logger,
    service_name: String,
}

impl TypedLogger {
    pub fn new(service_name: impl Into<String>) -> Self {
        let service_name = service_name.into();
        let logger = global::logger(&service_name);
        Self { logger, service_name }
    }

    /// 记录 Info 级别日志
    pub fn info(&self, message: impl Into<String>, attributes: Vec<KeyValue>) {
        self.log(Severity::Info, "INFO", message, attributes);
    }

    /// 记录 Warn 级别日志
    pub fn warn(&self, message: impl Into<String>, attributes: Vec<KeyValue>) {
        self.log(Severity::Warn, "WARN", message, attributes);
    }

    /// 记录 Error 级别日志
    pub fn error(&self, message: impl Into<String>, attributes: Vec<KeyValue>) {
        self.log(Severity::Error, "ERROR", message, attributes);
    }

    /// 通用日志记录
    fn log(
        &self,
        severity: Severity,
        severity_text: &str,
        message: impl Into<String>,
        mut attributes: Vec<KeyValue>,
    ) {
        let mut log_record = LogRecord::default();
        log_record.set_timestamp(SystemTime::now());
        log_record.set_observed_timestamp(SystemTime::now());
        log_record.set_severity_number(severity);
        log_record.set_severity_text(severity_text);
        log_record.set_body(message.into().into());

        // 添加服务名
        attributes.push(KeyValue::new("service.name", self.service_name.clone()));

        log_record.set_attributes(attributes);

        self.logger.emit(log_record);
    }
}

/// 使用示例
fn example_typed_logger() {
    let logger = TypedLogger::new("my-service");

    logger.info("User logged in", vec![
        KeyValue::new("user.id", "user-123"),
        KeyValue::new("user.email", "user@example.com"),
    ]);

    logger.error("Database connection failed", vec![
        KeyValue::new("error.type", "ConnectionError"),
        KeyValue::new("db.name", "postgres"),
    ]);
}
```

### 3.2 结构化日志宏

```rust
/// 结构化日志宏
#[macro_export]
macro_rules! log_structured {
    ($logger:expr, $severity:expr, $message:expr, $($key:expr => $value:expr),*) => {
        {
            let mut attributes = Vec::new();
            $(
                attributes.push(KeyValue::new($key, $value));
            )*
            
            let mut log_record = LogRecord::default();
            log_record.set_timestamp(SystemTime::now());
            log_record.set_severity_number($severity);
            log_record.set_body($message.into());
            log_record.set_attributes(attributes);
            
            $logger.emit(log_record);
        }
    };
}

/// 使用示例
fn example_structured_macro() {
    let logger = global::logger("my-app");

    log_structured!(
        logger,
        Severity::Info,
        "Order created",
        "order.id" => "ORD-12345",
        "user.id" => "user-123",
        "amount" => 99.99
    );
}
```

---

## 4. 与 tracing 集成

### 4.1 tracing-opentelemetry 集成

```rust
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use tracing_opentelemetry::OpenTelemetryLayer;
use opentelemetry_sdk::trace::TracerProvider;
use anyhow::Result;

/// 初始化 tracing 与 OpenTelemetry 集成
pub async fn init_tracing_with_otel() -> Result<()> {
    // 1. 初始化 OpenTelemetry Tracer (用于关联)
    let tracer_provider = init_tracer_provider().await?;
    let tracer = tracer_provider.tracer("my-service");

    // 2. 初始化 OpenTelemetry Logs
    let _logger_provider = init_logs().await?;

    // 3. 创建 tracing subscriber
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let otel_layer = OpenTelemetryLayer::new(tracer);

    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt::layer().json())
        .with(otel_layer)
        .init();

    Ok(())
}

/// 使用 tracing 宏记录日志
pub async fn example_tracing_logs() {
    // 自动关联 Span
    tracing::info!(
        user.id = "user-123",
        user.email = "user@example.com",
        "User logged in"
    );

    tracing::error!(
        error.type = "DatabaseError",
        db.name = "postgres",
        "Connection failed"
    );
}
```

### 4.2 tracing Span 自动关联

```rust
use tracing::{info, instrument};
use opentelemetry::trace::{TraceContextExt, Tracer};

/// 自动关联 Trace 的函数
#[instrument]
pub async fn process_order(order_id: String) -> Result<(), anyhow::Error> {
    // 日志自动关联当前 Span
    info!(order.id = %order_id, "Processing order");

    // 执行业务逻辑
    validate_order(&order_id).await?;
    save_order(&order_id).await?;

    info!(order.id = %order_id, "Order processed successfully");

    Ok(())
}

#[instrument]
async fn validate_order(order_id: &str) -> Result<(), anyhow::Error> {
    info!("Validating order");
    // 验证逻辑...
    Ok(())
}

#[instrument]
async fn save_order(order_id: &str) -> Result<(), anyhow::Error> {
    info!("Saving order to database");
    // 保存逻辑...
    Ok(())
}
```

---

## 5. 日志与 Trace 关联

### 5.1 自动关联 TraceContext

```rust
use opentelemetry::logs::{LogRecord, Logger};
use opentelemetry::trace::{TraceContextExt, Span};
use opentelemetry::{global, Context, KeyValue};
use std::time::SystemTime;

/// 带 TraceContext 的日志记录器
pub struct ContextualLogger {
    logger: Logger,
}

impl ContextualLogger {
    pub fn new() -> Self {
        Self {
            logger: global::logger("contextual"),
        }
    }

    /// 记录关联 Trace 的日志
    pub fn log_with_context(
        &self,
        ctx: &Context,
        severity: opentelemetry::logs::Severity,
        message: impl Into<String>,
        attributes: Vec<KeyValue>,
    ) {
        let span = ctx.span();
        let span_context = span.span_context();

        let mut log_record = LogRecord::default();
        log_record.set_timestamp(SystemTime::now());
        log_record.set_severity_number(severity);
        log_record.set_body(message.into().into());
        log_record.set_attributes(attributes);

        // 关联 TraceContext
        if span_context.is_valid() {
            log_record.set_trace_context(
                span_context.trace_id(),
                span_context.span_id(),
                Some(span_context.trace_flags()),
            );
        }

        self.logger.emit(log_record);
    }
}

/// 使用示例
pub async fn example_contextual_logging() {
    let tracer = global::tracer("my-app");
    let logger = ContextualLogger::new();

    let span = tracer.start("process_request");
    let ctx = Context::current_with_span(span);

    logger.log_with_context(
        &ctx,
        opentelemetry::logs::Severity::Info,
        "Processing request",
        vec![KeyValue::new("request.id", "req-123")],
    );
}
```

### 5.2 手动注入 TraceContext

```rust
use opentelemetry::trace::{TraceId, SpanId, TraceFlags};
use opentelemetry::logs::LogRecord;

/// 手动设置 TraceContext
pub fn log_with_manual_trace_context(
    logger: &opentelemetry::logs::Logger,
    trace_id: TraceId,
    span_id: SpanId,
    message: &str,
) {
    let mut log_record = LogRecord::default();
    log_record.set_timestamp(SystemTime::now());
    log_record.set_severity_number(opentelemetry::logs::Severity::Info);
    log_record.set_body(message.into());
    
    // 手动设置 TraceContext
    log_record.set_trace_context(
        trace_id,
        span_id,
        Some(TraceFlags::SAMPLED),
    );

    logger.emit(log_record);
}
```

---

## 6. 日志框架集成

### 6.1 slog 集成

```rust
use slog::{Drain, Logger, Record, OwnedKVList, Key};
use opentelemetry::logs::{LogRecord as OtelLogRecord, Severity};
use std::sync::Arc;

/// slog 到 OpenTelemetry 的桥接
pub struct OtelDrain {
    logger: opentelemetry::logs::Logger,
}

impl OtelDrain {
    pub fn new(logger: opentelemetry::logs::Logger) -> Self {
        Self { logger }
    }
}

impl Drain for OtelDrain {
    type Ok = ();
    type Err = slog::Never;

    fn log(&self, record: &Record, _values: &OwnedKVList) -> Result<Self::Ok, Self::Err> {
        let severity = match record.level() {
            slog::Level::Trace => Severity::Trace,
            slog::Level::Debug => Severity::Debug,
            slog::Level::Info => Severity::Info,
            slog::Level::Warning => Severity::Warn,
            slog::Level::Error => Severity::Error,
            slog::Level::Critical => Severity::Fatal,
        };

        let mut log_record = OtelLogRecord::default();
        log_record.set_timestamp(SystemTime::now());
        log_record.set_severity_number(severity);
        log_record.set_body(record.msg().to_string().into());

        self.logger.emit(log_record);

        Ok(())
    }
}
```

### 6.2 log crate 集成

```rust
use log::{Log, Metadata, Record as LogRecord, Level};
use opentelemetry::logs::{LogRecord as OtelLogRecord, Severity, Logger};
use opentelemetry::global;

/// log crate 到 OpenTelemetry 的桥接
pub struct OtelLogBridge {
    logger: Logger,
}

impl OtelLogBridge {
    pub fn new() -> Self {
        Self {
            logger: global::logger("log-bridge"),
        }
    }

    pub fn init() {
        log::set_boxed_logger(Box::new(Self::new())).unwrap();
        log::set_max_level(log::LevelFilter::Trace);
    }
}

impl Log for OtelLogBridge {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Trace
    }

    fn log(&self, record: &LogRecord) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let severity = match record.level() {
            Level::Error => Severity::Error,
            Level::Warn => Severity::Warn,
            Level::Info => Severity::Info,
            Level::Debug => Severity::Debug,
            Level::Trace => Severity::Trace,
        };

        let mut otel_record = OtelLogRecord::default();
        otel_record.set_timestamp(SystemTime::now());
        otel_record.set_severity_number(severity);
        otel_record.set_severity_text(record.level().as_str());
        otel_record.set_body(record.args().to_string().into());

        // 添加代码位置属性
        if let (Some(file), Some(line)) = (record.file(), record.line()) {
            otel_record.set_attributes(vec![
                opentelemetry::KeyValue::new("code.filepath", file.to_string()),
                opentelemetry::KeyValue::new("code.lineno", line as i64),
            ]);
        }

        self.logger.emit(otel_record);
    }

    fn flush(&self) {}
}

/// 使用示例
fn example_log_crate() {
    OtelLogBridge::init();

    log::info!("Application started");
    log::error!("Error occurred");
}
```

---

## 7. 异步日志处理

### 7.1 批量日志处理器

```rust
use opentelemetry_sdk::logs::{BatchLogProcessor, LoggerProvider};
use opentelemetry_otlp::LogExporter;
use std::time::Duration;

/// 配置批量日志处理器
pub async fn init_batch_log_processor() -> Result<LoggerProvider, anyhow::Error> {
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 批量处理器配置
    let batch_config = opentelemetry_sdk::logs::BatchConfigBuilder::default()
        .with_max_queue_size(4096)           // 最大队列大小
        .with_max_export_batch_size(512)     // 单次导出最大批量
        .with_scheduled_delay(Duration::from_secs(5)) // 导出间隔
        .with_max_export_timeout(Duration::from_secs(30)) // 导出超时
        .build();

    let provider = LoggerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_config(
            opentelemetry_sdk::logs::Config::default()
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "my-service"),
                ]))
        )
        .build();

    Ok(provider)
}
```

### 7.2 异步日志记录

```rust
use tokio::sync::mpsc;
use opentelemetry::logs::{LogRecord, Logger};

/// 异步日志队列
pub struct AsyncLogQueue {
    tx: mpsc::UnboundedSender<LogRecord>,
}

impl AsyncLogQueue {
    pub fn new(logger: Logger) -> Self {
        let (tx, mut rx) = mpsc::unbounded_channel::<LogRecord>();

        // 后台任务：批量发送日志
        tokio::spawn(async move {
            let mut buffer = Vec::new();

            loop {
                tokio::select! {
                    Some(record) = rx.recv() => {
                        buffer.push(record);
                        
                        // 批量发送
                        if buffer.len() >= 100 {
                            for record in buffer.drain(..) {
                                logger.emit(record);
                            }
                        }
                    }
                    _ = tokio::time::sleep(Duration::from_secs(1)) => {
                        // 定时刷新
                        for record in buffer.drain(..) {
                            logger.emit(record);
                        }
                    }
                }
            }
        });

        Self { tx }
    }

    /// 异步发送日志
    pub fn log(&self, record: LogRecord) {
        let _ = self.tx.send(record);
    }
}
```

---

## 8. 结构化日志

### 8.1 JSON Body

```rust
use serde_json::json;
use opentelemetry::logs::{LogRecord, AnyValue};
use std::collections::HashMap;

/// 结构化 JSON 日志
pub fn log_json_body(logger: &opentelemetry::logs::Logger) {
    // 使用 serde_json 构建
    let event = json!({
        "event": "order_created",
        "order_id": "ORD-12345",
        "user_id": "user-123",
        "amount": 99.99,
        "currency": "USD",
        "items": [
            {"id": "item-1", "quantity": 2},
            {"id": "item-2", "quantity": 1}
        ]
    });

    let mut log_record = LogRecord::default();
    log_record.set_timestamp(SystemTime::now());
    log_record.set_severity_number(opentelemetry::logs::Severity::Info);
    log_record.set_body(event.to_string().into());

    logger.emit(log_record);
}

/// 使用 HashMap 构建结构化日志
pub fn log_structured_map(logger: &opentelemetry::logs::Logger) {
    let mut map = HashMap::new();
    map.insert("event".to_string(), AnyValue::String("order_created".into()));
    map.insert("order_id".to_string(), AnyValue::String("ORD-12345".into()));
    map.insert("amount".to_string(), AnyValue::Double(99.99));

    let body: AnyValue = map.into();

    let mut log_record = LogRecord::default();
    log_record.set_timestamp(SystemTime::now());
    log_record.set_severity_number(opentelemetry::logs::Severity::Info);
    log_record.set_body(body);

    logger.emit(log_record);
}
```

---

## 9. 日志导出与后端

### 9.1 OTLP gRPC Exporter

```rust
use opentelemetry_otlp::{LogExporter, WithExportConfig};
use opentelemetry_sdk::logs::LoggerProvider;
use std::time::Duration;

/// OTLP gRPC 导出配置
pub async fn init_otlp_grpc_exporter() -> Result<LoggerProvider, anyhow::Error> {
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build()?;

    let provider = LoggerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    Ok(provider)
}
```

### 9.2 OTLP HTTP Exporter

```rust
use opentelemetry_otlp::{LogExporter, Protocol, WithExportConfig};

/// OTLP HTTP/JSON 导出配置
pub async fn init_otlp_http_exporter() -> Result<LoggerProvider, anyhow::Error> {
    let exporter = LogExporter::builder()
        .with_http()
        .with_endpoint("http://localhost:4318/v1/logs")
        .with_protocol(Protocol::HttpBinary) // 或 HttpJson
        .with_timeout(Duration::from_secs(10))
        .build()?;

    let provider = LoggerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    Ok(provider)
}
```

---

## 10. 性能优化

### 10.1 采样日志

```rust
use opentelemetry::logs::{LogRecord, Logger, Severity};
use rand::Rng;

/// 日志采样器
pub struct LogSampler {
    logger: Logger,
    debug_sample_rate: f64, // DEBUG 日志采样率
}

impl LogSampler {
    pub fn new(logger: Logger, debug_sample_rate: f64) -> Self {
        Self {
            logger,
            debug_sample_rate,
        }
    }

    /// 采样日志
    pub fn log(&self, severity: Severity, message: impl Into<String>) {
        // INFO 及以上级别：全量
        // DEBUG 及以下：采样
        let should_log = match severity {
            Severity::Trace | Severity::Debug => {
                rand::thread_rng().gen::<f64>() < self.debug_sample_rate
            }
            _ => true,
        };

        if should_log {
            let mut log_record = LogRecord::default();
            log_record.set_timestamp(SystemTime::now());
            log_record.set_severity_number(severity);
            log_record.set_body(message.into().into());

            self.logger.emit(log_record);
        }
    }
}

/// 使用示例
fn example_log_sampling() {
    let logger = global::logger("my-app");
    let sampler = LogSampler::new(logger, 0.1); // DEBUG 日志 10% 采样

    sampler.log(Severity::Debug, "Debug message"); // 10% 概率记录
    sampler.log(Severity::Info, "Info message");   // 100% 记录
}
```

### 10.2 属性限制

```rust
/// 限制日志属性数量和大小
pub struct AttributeLimiter {
    max_attributes: usize,
    max_attribute_value_length: usize,
}

impl AttributeLimiter {
    pub fn new(max_attributes: usize, max_attribute_value_length: usize) -> Self {
        Self {
            max_attributes,
            max_attribute_value_length,
        }
    }

    /// 限制属性
    pub fn limit(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .take(self.max_attributes)
            .map(|kv| {
                let key = kv.key;
                let value = match kv.value {
                    opentelemetry::Value::String(s) => {
                        if s.len() > self.max_attribute_value_length {
                            let truncated = s.chars().take(self.max_attribute_value_length).collect::<String>();
                            opentelemetry::Value::String(truncated.into())
                        } else {
                            opentelemetry::Value::String(s)
                        }
                    }
                    other => other,
                };
                KeyValue::new(key, value)
            })
            .collect()
    }
}
```

---

## 11. 测试与验证

### 11.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::testing::logs::InMemoryLogsExporter;

    #[tokio::test]
    async fn test_log_emission() {
        let exporter = InMemoryLogsExporter::default();
        let provider = LoggerProvider::builder()
            .with_simple_exporter(exporter.clone())
            .build();

        let logger = provider.logger("test");

        let mut log_record = LogRecord::default();
        log_record.set_severity_number(Severity::Info);
        log_record.set_body("Test message".into());

        logger.emit(log_record);

        provider.force_flush();

        let logs = exporter.get_emitted_logs().unwrap();
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0].record.body, Some("Test message".into()));
    }
}
```

---

## 12. 最佳实践

### 12.1 DO's

```text
✅ 使用结构化日志 (JSON, HashMap)
✅ 自动关联 TraceContext
✅ 使用 tracing crate 自动关联 Span
✅ 采样 DEBUG 日志，全量 INFO+ 日志
✅ 限制属性数量和大小
✅ 使用批量处理器
✅ 异步导出，不阻塞主流程
✅ 为日志添加上下文属性 (user_id, request_id)
✅ 使用语义约定命名属性
✅ 脱敏 PII 数据
```

### 12.2 DON'Ts

```text
❌ 不要记录敏感信息 (密码, Token, 信用卡号)
❌ 不要在热路径中同步写日志
❌ 不要过度记录 DEBUG 日志 (导致存储爆炸)
❌ 不要忽略错误日志的堆栈跟踪
❌ 不要在循环中频繁记录日志
❌ 不要使用高基数属性 (ip_address, user_id 在日志 body 中可以, 但不要作为属性)
❌ 不要忘记调用 shutdown()
❌ 不要混用多个 LoggerProvider
```

---

**文档状态**: ✅ 完成  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**相关文档**: [SpanContext](../01_Traces数据模型/02_SpanContext_Rust完整版.md), [Metrics概述](../02_Metrics数据模型/01_Metrics概述_Rust完整版.md)
