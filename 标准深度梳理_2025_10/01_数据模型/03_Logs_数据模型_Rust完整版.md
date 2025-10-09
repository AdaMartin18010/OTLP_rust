# Logs 数据模型 - Rust 完整版

## 目录

- [Logs 数据模型 - Rust 完整版](#logs-数据模型---rust-完整版)
  - [目录](#目录)
  - [1. Logs 数据模型概述](#1-logs-数据模型概述)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 数据流](#12-数据流)
  - [2. Log Record 结构](#2-log-record-结构)
    - [2.1 核心字段](#21-核心字段)
    - [2.2 Severity Number](#22-severity-number)
    - [2.3 Body 类型](#23-body-类型)
  - [3. Rust 实现](#3-rust-实现)
    - [3.1 tracing 集成](#31-tracing-集成)
    - [3.2 OpenTelemetry Logs Bridge](#32-opentelemetry-logs-bridge)
    - [3.3 自定义 Logger](#33-自定义-logger)
  - [4. 日志与 Trace 关联](#4-日志与-trace-关联)
    - [4.1 自动关联](#41-自动关联)
    - [4.2 TraceId/SpanId 传递](#42-traceidspanid-传递)
  - [5. Resource 和 Scope](#5-resource-和-scope)
    - [5.1 Resource 属性](#51-resource-属性)
    - [5.2 InstrumentationScope](#52-instrumentationscope)
  - [6. OTLP 导出格式](#6-otlp-导出格式)
    - [6.1 Protobuf 定义](#61-protobuf-定义)
    - [6.2 Rust 导出](#62-rust-导出)
  - [7. 日志级别映射](#7-日志级别映射)
    - [7.1 Rust 日志级别](#71-rust-日志级别)
    - [7.2 级别转换](#72-级别转换)
  - [8. 结构化日志](#8-结构化日志)
    - [8.1 字段类型](#81-字段类型)
    - [8.2 JSON 序列化](#82-json-序列化)
  - [9. 完整示例](#9-完整示例)
    - [9.1 基础日志记录](#91-基础日志记录)
    - [9.2 错误日志](#92-错误日志)
    - [9.3 业务日志](#93-业务日志)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 日志内容](#101-日志内容)
    - [10.2 性能优化](#102-性能优化)
    - [10.3 安全性](#103-安全性)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [数据模型对比](#数据模型对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Logs 数据模型概述

### 1.1 核心概念

````text
LogRecord (日志记录):
├─ Timestamp: 日志时间戳
├─ ObservedTimestamp: 观察时间戳
├─ TraceId: 关联的 Trace ID (16 bytes)
├─ SpanId: 关联的 Span ID (8 bytes)
├─ TraceFlags: Trace 标志 (1 byte)
├─ SeverityText: 日志级别文本 (INFO/ERROR)
├─ SeverityNumber: 日志级别数值 (1-24)
├─ Body: 日志主体内容 (字符串/结构化)
├─ Attributes: 结构化属性 (键值对)
└─ Resource: 资源信息 (service.name, host.name)
````

### 1.2 数据流

````text
Application
    ↓
tracing::info!("User login", user_id = 12345)
    ↓
tracing-subscriber (Layer)
    ↓
OpenTelemetry Logs Bridge
    ↓
LogRecord (with TraceId/SpanId)
    ↓
BatchLogProcessor
    ↓
OTLP Exporter
    ↓
Backend (Loki/Elasticsearch/CloudWatch)
````

---

## 2. Log Record 结构

### 2.1 核心字段

````rust
pub struct LogRecord {
    pub timestamp: SystemTime,
    pub observed_timestamp: SystemTime,
    pub trace_id: Option<TraceId>,
    pub span_id: Option<SpanId>,
    pub trace_flags: Option<TraceFlags>,
    pub severity_text: Option<String>,
    pub severity_number: Option<SeverityNumber>,
    pub body: Option<AnyValue>,
    pub attributes: Vec<KeyValue>,
    pub dropped_attributes_count: u32,
}
````

### 2.2 Severity Number

**OpenTelemetry 定义** (1-24):

| 级别 | SeverityNumber | SeverityText | 说明 |
|------|---------------|--------------|------|
| TRACE | 1-4 | TRACE, TRACE2, TRACE3, TRACE4 | 详细追踪 |
| DEBUG | 5-8 | DEBUG, DEBUG2, DEBUG3, DEBUG4 | 调试信息 |
| INFO | 9-12 | INFO, INFO2, INFO3, INFO4 | 一般信息 |
| WARN | 13-16 | WARN, WARN2, WARN3, WARN4 | 警告 |
| ERROR | 17-20 | ERROR, ERROR2, ERROR3, ERROR4 | 错误 |
| FATAL | 21-24 | FATAL, FATAL2, FATAL3, FATAL4 | 致命错误 |

**Rust 枚举**:

````rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeverityNumber {
    Trace = 1,
    Trace2 = 2,
    Trace3 = 3,
    Trace4 = 4,
    Debug = 5,
    Debug2 = 6,
    Debug3 = 7,
    Debug4 = 8,
    Info = 9,
    Info2 = 10,
    Info3 = 11,
    Info4 = 12,
    Warn = 13,
    Warn2 = 14,
    Warn3 = 15,
    Warn4 = 16,
    Error = 17,
    Error2 = 18,
    Error3 = 19,
    Error4 = 20,
    Fatal = 21,
    Fatal2 = 22,
    Fatal3 = 23,
    Fatal4 = 24,
}
````

### 2.3 Body 类型

**AnyValue** 支持多种类型:

````rust
pub enum AnyValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    Array(Vec<AnyValue>),
    Map(Vec<(String, AnyValue)>),
    Bytes(Vec<u8>),
}
````

**示例**:

````rust
// 字符串 Body
AnyValue::String("User login successful".to_string())

// 结构化 Body (Map)
AnyValue::Map(vec![
    ("event".to_string(), AnyValue::String("user.login".to_string())),
    ("user_id".to_string(), AnyValue::Int(12345)),
    ("success".to_string(), AnyValue::Bool(true)),
])
````

---

## 3. Rust 实现

### 3.1 tracing 集成

````toml
[dependencies]
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28.0"
opentelemetry = { version = "0.31.0", features = ["logs"] }
opentelemetry_sdk = { version = "0.31.0", features = ["logs", "rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["logs"] }
````

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    logs::{LogProcessor, LoggerProvider},
    Resource,
};
use opentelemetry_otlp::LogExporter;
use tracing_subscriber::{layer::SubscriberExt, Registry};

pub fn init_logging() -> anyhow::Result<()> {
    // 1. 创建 OTLP 日志导出器
    let log_exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 2. 创建资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);

    // 3. 创建批量日志处理器
    let batch_processor = opentelemetry_sdk::logs::BatchLogProcessor::builder(
        log_exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5))
    .build();

    // 4. 创建 LoggerProvider
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_log_processor(batch_processor)
        .build();

    // 5. 设置全局 LoggerProvider
    global::set_logger_provider(logger_provider.clone());

    // 6. 初始化 tracing-subscriber
    Registry::default()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer())
        .init();

    Ok(())
}
````

### 3.2 OpenTelemetry Logs Bridge

````rust
use tracing::{info, error, warn, debug, Span};
use opentelemetry::trace::TraceContextExt;

#[tracing::instrument(name = "process_order")]
pub async fn process_order(order_id: &str) -> Result<(), anyhow::Error> {
    let span = Span::current();
    
    // 日志自动关联到 Span
    info!(order_id, "Processing order");

    // 获取 TraceId 和 SpanId
    let context = span.context();
    let span_context = context.span().span_context();
    let trace_id = span_context.trace_id().to_string();
    let span_id = span_context.span_id().to_string();

    info!(
        order_id,
        trace_id = %trace_id,
        span_id = %span_id,
        "Order validation started"
    );

    match validate_order(order_id).await {
        Ok(_) => {
            info!(order_id, "Order validated successfully");
            Ok(())
        }
        Err(e) => {
            error!(
                order_id,
                error = %e,
                "Order validation failed"
            );
            Err(e)
        }
    }
}

async fn validate_order(order_id: &str) -> Result<(), anyhow::Error> {
    debug!(order_id, "Validating order");
    Ok(())
}
````

### 3.3 自定义 Logger

````rust
use opentelemetry::{
    logs::{Logger, LogRecord, Severity},
    KeyValue,
};

pub fn custom_log(logger: &dyn Logger) {
    let mut log_record = LogRecord::default();
    
    log_record
        .set_severity_text("INFO")
        .set_severity_number(Severity::Info)
        .set_body("Custom log message".into())
        .add_attribute(KeyValue::new("user.id", 12345))
        .add_attribute(KeyValue::new("action", "login"));

    logger.emit(log_record);
}
````

---

## 4. 日志与 Trace 关联

### 4.1 自动关联

使用 `tracing-opentelemetry`，日志会自动关联到当前 Span：

````rust
use tracing::{info, instrument, Span};

#[instrument(name = "api.create_user")]
pub async fn create_user(username: &str) -> Result<String, anyhow::Error> {
    // 这些日志会自动包含 trace_id 和 span_id
    info!(username, "Creating user");
    
    // 模拟数据库操作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    info!(username, "User created successfully");
    
    Ok("user_123".to_string())
}
````

**日志输出** (JSON 格式):

````json
{
  "timestamp": "2025-10-09T12:34:56.789Z",
  "level": "INFO",
  "target": "my_app::api",
  "fields": {
    "message": "Creating user",
    "username": "alice"
  },
  "span": {
    "name": "api.create_user",
    "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
    "span_id": "00f067aa0ba902b7"
  }
}
````

### 4.2 TraceId/SpanId 传递

````rust
use opentelemetry::trace::TraceContextExt;
use tracing::Span;

pub fn log_with_trace_context() {
    let span = Span::current();
    let context = span.context();
    let span_context = context.span().span_context();

    let trace_id = span_context.trace_id();
    let span_id = span_context.span_id();

    tracing::info!(
        trace_id = %trace_id,
        span_id = %span_id,
        "Log with explicit trace context"
    );
}
````

---

## 5. Resource 和 Scope

### 5.1 Resource 属性

````rust
use opentelemetry::{KeyValue, Resource};

pub fn create_log_resource() -> Resource {
    Resource::new(vec![
        // 服务信息
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("service.namespace", "production"),
        
        // 主机信息
        KeyValue::new("host.name", hostname::get().unwrap().to_string_lossy().to_string()),
        KeyValue::new("host.arch", std::env::consts::ARCH),
        
        // 进程信息
        KeyValue::new("process.pid", std::process::id().to_string()),
        KeyValue::new("process.executable.name", std::env::current_exe().ok().and_then(|p| p.file_name().map(|n| n.to_string_lossy().to_string())).unwrap_or_default()),
        
        // SDK 信息
        KeyValue::new("telemetry.sdk.name", "opentelemetry"),
        KeyValue::new("telemetry.sdk.language", "rust"),
        KeyValue::new("telemetry.sdk.version", "0.31.0"),
    ])
}
````

### 5.2 InstrumentationScope

````rust
pub struct InstrumentationScope {
    pub name: String,
    pub version: Option<String>,
    pub schema_url: Option<String>,
    pub attributes: Vec<KeyValue>,
}

// 示例
InstrumentationScope {
    name: "my_app::api".to_string(),
    version: Some("1.0.0".to_string()),
    schema_url: Some("https://opentelemetry.io/schemas/1.20.0".to_string()),
    attributes: vec![
        KeyValue::new("module", "api"),
    ],
}
````

---

## 6. OTLP 导出格式

### 6.1 Protobuf 定义

````protobuf
message LogsData {
  repeated ResourceLogs resource_logs = 1;
}

message ResourceLogs {
  Resource resource = 1;
  repeated ScopeLogs scope_logs = 2;
  string schema_url = 3;
}

message ScopeLogs {
  InstrumentationScope scope = 1;
  repeated LogRecord log_records = 2;
  string schema_url = 3;
}

message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 2;
  SeverityNumber severity_number = 3;
  string severity_text = 4;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;
  bytes span_id = 10;
}
````

### 6.2 Rust 导出

````rust
use opentelemetry_otlp::{LogExporter, WithExportConfig};
use opentelemetry_sdk::logs::LoggerProvider;

pub fn init_otlp_logs() -> anyhow::Result<()> {
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(10))
        .build()?;

    let processor = opentelemetry_sdk::logs::BatchLogProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096)
    .build();

    let provider = LoggerProvider::builder()
        .with_log_processor(processor)
        .with_resource(create_log_resource())
        .build();

    opentelemetry::global::set_logger_provider(provider);
    Ok(())
}
````

---

## 7. 日志级别映射

### 7.1 Rust 日志级别

| Rust Level | OpenTelemetry SeverityNumber | SeverityText |
|------------|------------------------------|--------------|
| TRACE | 1 | TRACE |
| DEBUG | 5 | DEBUG |
| INFO | 9 | INFO |
| WARN | 13 | WARN |
| ERROR | 17 | ERROR |

### 7.2 级别转换

````rust
use tracing::Level;
use opentelemetry::logs::Severity;

pub fn level_to_severity(level: Level) -> Severity {
    match level {
        Level::TRACE => Severity::Trace,
        Level::DEBUG => Severity::Debug,
        Level::INFO => Severity::Info,
        Level::WARN => Severity::Warn,
        Level::ERROR => Severity::Error,
    }
}
````

---

## 8. 结构化日志

### 8.1 字段类型

````rust
use tracing::info;
use serde::Serialize;

#[derive(Serialize)]
struct UserEvent {
    user_id: u64,
    action: String,
    timestamp: u64,
}

pub fn structured_logging() {
    // 字符串字段
    info!(username = "alice", "User login");

    // 整数字段
    info!(user_id = 12345, "User action");

    // 浮点数字段
    info!(response_time_ms = 45.5, "Request completed");

    // 布尔字段
    info!(success = true, "Operation result");

    // 结构体字段
    let event = UserEvent {
        user_id: 12345,
        action: "login".to_string(),
        timestamp: 1696867200,
    };
    info!(event = ?event, "User event");
}
````

### 8.2 JSON 序列化

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

**输出示例**:

````json
{
  "timestamp": "2025-10-09T12:34:56.789Z",
  "level": "INFO",
  "target": "my_app::api",
  "fields": {
    "message": "User login",
    "username": "alice",
    "user_id": 12345
  },
  "span": {
    "name": "api.login",
    "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
    "span_id": "00f067aa0ba902b7"
  },
  "spans": [
    {
      "name": "http.request",
      "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
      "span_id": "00f067aa0ba902b7"
    }
  ]
}
````

---

## 9. 完整示例

### 9.1 基础日志记录

````rust
use tracing::{info, debug, warn, error, instrument};

#[instrument(name = "api.process_request")]
pub async fn process_request(request_id: &str) -> Result<(), anyhow::Error> {
    info!(request_id, "Processing request");

    debug!(request_id, "Validating request");
    
    // 业务逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    info!(request_id, processing_time_ms = 100, "Request completed");

    Ok(())
}
````

### 9.2 错误日志

````rust
use tracing::{error, instrument};
use anyhow::Context;

#[instrument(name = "db.query_user")]
pub async fn query_user(user_id: u64) -> Result<User, anyhow::Error> {
    match database_query(user_id).await {
        Ok(user) => Ok(user),
        Err(e) => {
            error!(
                user_id,
                error = %e,
                error_chain = ?e.chain().collect::<Vec<_>>(),
                "Database query failed"
            );
            Err(e).context("Failed to query user")
        }
    }
}

async fn database_query(user_id: u64) -> Result<User, anyhow::Error> {
    Ok(User { id: user_id, name: "Alice".to_string() })
}

#[derive(Debug)]
struct User {
    id: u64,
    name: String,
}
````

### 9.3 业务日志

````rust
use tracing::{info, instrument};
use serde::Serialize;

#[derive(Serialize)]
struct OrderCreatedEvent {
    order_id: String,
    user_id: u64,
    amount: f64,
    items: u32,
}

#[instrument(name = "order.create")]
pub async fn create_order(order: OrderCreatedEvent) -> Result<String, anyhow::Error> {
    // 业务日志
    info!(
        order_id = %order.order_id,
        user_id = order.user_id,
        amount = order.amount,
        items = order.items,
        "Order created"
    );

    // 审计日志
    info!(
        event_type = "order.created",
        order_id = %order.order_id,
        user_id = order.user_id,
        timestamp = chrono::Utc::now().timestamp(),
        "Audit: Order creation"
    );

    Ok(order.order_id)
}
````

---

## 10. 最佳实践

### 10.1 日志内容

````rust
// ✅ 推荐: 结构化字段
info!(
    user_id = 12345,
    action = "login",
    ip_address = "192.168.1.100",
    "User login successful"
);

// ❌ 避免: 字符串拼接
info!("User 12345 login from 192.168.1.100");

// ✅ 推荐: 明确的字段名
info!(
    order_id = "ORD-001",
    amount = 99.99,
    currency = "USD",
    "Order created"
);

// ❌ 避免: 模糊的字段名
info!(id = "ORD-001", value = 99.99, "Order");
````

### 10.2 性能优化

````rust
use tracing::{info, Level, enabled};

pub fn optimized_logging() {
    // ✅ 推荐: 条件日志
    if enabled!(Level::DEBUG) {
        let expensive_data = compute_expensive_data();
        tracing::debug!(data = ?expensive_data, "Debug info");
    }

    // ✅ 推荐: 使用静态字符串
    const LOG_MESSAGE: &str = "Processing order";
    info!(LOG_MESSAGE);

    // ❌ 避免: 昂贵的格式化
    // info!("Processing order {}", format!("{:?}", expensive_object));
}

fn compute_expensive_data() -> String {
    "expensive_data".to_string()
}
````

### 10.3 安全性

````rust
use tracing::info;

pub fn secure_logging(username: &str, password: &str) {
    // ✅ 推荐: 不记录敏感信息
    info!(username, "User login attempt");

    // ❌ 危险: 记录密码
    // info!(username, password, "User login");

    // ✅ 推荐: 记录密码哈希 (如果需要)
    let password_hash = format!("{:x}", md5::compute(password));
    info!(username, password_hash, "User login");
}
````

---

## 总结

### 核心要点

1. **LogRecord 结构**: 包含 Timestamp、TraceId、SpanId、Severity、Body、Attributes
2. **SeverityNumber**: 1-24 的数值范围，对应 TRACE/DEBUG/INFO/WARN/ERROR/FATAL
3. **日志与 Trace 关联**: 使用 `tracing-opentelemetry` 自动关联日志到 Span
4. **结构化日志**: 使用键值对字段而非字符串拼接
5. **Resource**: 服务级别元数据 (service.name, host.name)
6. **OTLP 导出**: 使用 BatchLogProcessor 批量导出日志

### 数据模型对比

| OpenTelemetry | Rust tracing | 说明 |
|---------------|--------------|------|
| LogRecord | Event | 单条日志记录 |
| SeverityNumber | Level | 日志级别 |
| Body | message | 日志主体 |
| Attributes | fields | 结构化字段 |
| TraceId | SpanContext.trace_id | 关联 Trace |
| SpanId | SpanContext.span_id | 关联 Span |
| Resource | - | 服务元数据 |

### 最佳实践清单

- ✅ 使用结构化日志（键值对字段）
- ✅ 日志自动关联到 Span (TraceId/SpanId)
- ✅ 使用 JSON 格式便于查询
- ✅ 配置 BatchLogProcessor 批量导出
- ✅ 不记录敏感信息 (密码、Token)
- ✅ 使用语义化字段名 (user.id, order.amount)
- ✅ 条件日志 (仅 DEBUG 级别时执行)
- ✅ 记录错误链 (`e.chain()`)
- ✅ 设置 Resource 属性 (service.name)
- ✅ 使用 `#[instrument]` 自动记录函数调用

---

**相关文档**:

- [Logging 最佳实践](../02_Semantic_Conventions/03_日志与事件/01_Logging_Rust完整版.md)
- [Traces 数据模型](./01_Traces_数据模型_Rust完整版.md)
- [Metrics 数据模型](./02_Metrics_数据模型_Rust完整版.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
