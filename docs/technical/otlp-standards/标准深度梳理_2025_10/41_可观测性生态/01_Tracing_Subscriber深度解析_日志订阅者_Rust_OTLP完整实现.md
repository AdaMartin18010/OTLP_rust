# Tracing-Subscriber 深度解析：日志订阅者 Rust 1.90 + OTLP 完整实现指南

## 目录

- [Tracing-Subscriber 深度解析：日志订阅者 Rust 1.90 + OTLP 完整实现指南](#tracing-subscriber-深度解析日志订阅者-rust-190--otlp-完整实现指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Tracing-Subscriber 定位](#11-tracing-subscriber-定位)
      - [核心优势](#核心优势)
    - [1.2 与其他日志库对比](#12-与其他日志库对比)
    - [1.3 国际标准对标](#13-国际标准对标)
  - [2. Tracing-Subscriber 核心架构](#2-tracing-subscriber-核心架构)
    - [2.1 Layer 模式](#21-layer-模式)
    - [2.2 事件流程](#22-事件流程)
  - [3. 项目初始化与配置](#3-项目初始化与配置)
    - [3.1 依赖配置（Cargo.toml）](#31-依赖配置cargotoml)
    - [3.2 基础初始化](#32-基础初始化)
  - [4. Layer 模式深度解析](#4-layer-模式深度解析)
    - [4.1 自定义 Layer](#41-自定义-layer)
    - [4.2 条件 Layer](#42-条件-layer)
  - [5. 日志格式化器](#5-日志格式化器)
    - [5.1 紧凑格式](#51-紧凑格式)
    - [5.2 完整格式](#52-完整格式)
    - [5.3 Pretty 格式](#53-pretty-格式)
    - [5.4 自定义格式化](#54-自定义格式化)
  - [6. 过滤器系统](#6-过滤器系统)
    - [6.1 环境变量过滤器](#61-环境变量过滤器)
    - [6.2 动态过滤器](#62-动态过滤器)
    - [6.3 基于字段的过滤](#63-基于字段的过滤)
  - [7. 多层订阅者组合](#7-多层订阅者组合)
    - [7.1 多输出层](#71-多输出层)
    - [7.2 按模块分层](#72-按模块分层)
  - [8. JSON 结构化日志](#8-json-结构化日志)
    - [8.1 基础 JSON 格式](#81-基础-json-格式)
    - [8.2 扁平化 JSON](#82-扁平化-json)
    - [8.3 自定义 JSON 字段](#83-自定义-json-字段)
  - [9. 异步日志写入](#9-异步日志写入)
    - [9.1 非阻塞日志](#91-非阻塞日志)
    - [9.2 批量日志写入](#92-批量日志写入)
  - [10. 日志轮转与归档](#10-日志轮转与归档)
    - [10.1 按时间轮转](#101-按时间轮转)
    - [10.2 按大小轮转](#102-按大小轮转)
  - [11. OpenTelemetry 集成](#11-opentelemetry-集成)
    - [11.1 完整集成](#111-完整集成)
    - [11.2 Span 追踪](#112-span-追踪)
  - [12. 性能优化](#12-性能优化)
    - [12.1 过滤性能优化](#121-过滤性能优化)
    - [12.2 批量日志](#122-批量日志)
  - [13. 生产环境最佳实践](#13-生产环境最佳实践)
    - [13.1 完整配置示例](#131-完整配置示例)
  - [14. 国际标准对标](#14-国际标准对标)
    - [14.1 对标清单](#141-对标清单)
  - [15. 总结与最佳实践](#15-总结与最佳实践)
    - [15.1 最佳实践](#151-最佳实践)
      - [✅ 推荐做法](#-推荐做法)
      - [❌ 避免做法](#-避免做法)

---

## 1. 概述

### 1.1 Tracing-Subscriber 定位

**Tracing-Subscriber** 是 Rust `tracing` 生态的订阅者实现库，提供灵活的日志收集、过滤、格式化和输出功能。

#### 核心优势

- **Layer 模式**：可组合的订阅者层
- **零成本抽象**：编译期优化，无运行时开销
- **结构化日志**：JSON、键值对、字段支持
- **异步支持**：非阻塞日志写入
- **灵活过滤**：动态过滤、环境变量控制
- **OpenTelemetry 集成**：完整的分布式追踪支持

### 1.2 与其他日志库对比

| 特性 | tracing-subscriber | log4rs | slog | env_logger |
|------|-------------------|---------|------|------------|
| **结构化日志** | ✅ 原生 | ⚠️ 有限 | ✅ 原生 | ❌ |
| **异步支持** | ✅ | ✅ | ⚠️ 部分 | ❌ |
| **Layer模式** | ✅ | ❌ | ✅ | ❌ |
| **动态过滤** | ✅ | ✅ | ✅ | ⚠️ 有限 |
| **OpenTelemetry** | ✅ | ❌ | ❌ | ❌ |

### 1.3 国际标准对标

| 标准 | Tracing-Subscriber 实现 |
|------|------------------------|
| **OpenTelemetry Logs** | ✅ 完整支持 |
| **Structured Logging** | ✅ JSON、键值对 |
| **Log Levels (RFC 5424)** | ✅ TRACE, DEBUG, INFO, WARN, ERROR |
| **Context Propagation** | ✅ Span Context |

---

## 2. Tracing-Subscriber 核心架构

### 2.1 Layer 模式

```text
┌──────────────────────────────────────┐
│         Registry (Root)              │
│  ┌────────────────────────────────┐  │
│  │  Layer 1 (Fmt Layer)           │  │
│  └────────────────────────────────┘  │
│  ┌────────────────────────────────┐  │
│  │  Layer 2 (OpenTelemetry Layer) │  │
│  └────────────────────────────────┘  │
│  ┌────────────────────────────────┐  │
│  │  Layer 3 (Filter Layer)        │  │
│  └────────────────────────────────┘  │
└──────────────────────────────────────┘

Event/Span ──> Registry ──> Layer 1 ──> Layer 2 ──> Layer 3
```

### 2.2 事件流程

```text
┌─────────────┐
│ tracing::   │
│ info!()     │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Registry   │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Filters    │  ←── EnvFilter
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Layers     │  ←── Fmt, OpenTelemetry, Custom
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Output     │  ←── stdout, file, network
└─────────────┘
```

---

## 3. 项目初始化与配置

### 3.1 依赖配置（Cargo.toml）

```toml
[package]
name = "tracing-subscriber-demo"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Tracing 核心
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = [
    "env-filter",        # 环境变量过滤器
    "json",              # JSON 格式化
    "fmt",               # 文本格式化
    "ansi",              # ANSI 颜色
    "registry",          # Registry 支持
    "local-time",        # 本地时间
] }
tracing-appender = "0.2"  # 文件日志、日志轮转

# OpenTelemetry 集成
tracing-opentelemetry = "0.26"
opentelemetry = { version = "0.25", features = ["trace", "logs"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio", "logs"] }
opentelemetry-otlp = { version = "0.25", features = ["trace", "logs", "grpc-tonic"] }
opentelemetry-semantic-conventions = "0.25"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# 工具库
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
chrono = "0.4"
```

### 3.2 基础初始化

```rust
use tracing_subscriber::{
    fmt,
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

pub fn init_tracing() {
    // 创建环境过滤器
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    // 创建格式化层
    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true);
    
    // 组合并初始化
    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();
}

fn main() {
    init_tracing();
    
    tracing::info!("Application started");
    tracing::debug!("Debug message");
    tracing::warn!("Warning message");
    tracing::error!("Error message");
}
```

---

## 4. Layer 模式深度解析

### 4.1 自定义 Layer

```rust
use tracing::{span, Subscriber};
use tracing_subscriber::layer::{Context, Layer};
use std::sync::atomic::{AtomicU64, Ordering};

pub struct MetricsLayer {
    event_count: AtomicU64,
}

impl MetricsLayer {
    pub fn new() -> Self {
        Self {
            event_count: AtomicU64::new(0),
        }
    }
    
    pub fn get_event_count(&self) -> u64 {
        self.event_count.load(Ordering::Relaxed)
    }
}

impl<S: Subscriber> Layer<S> for MetricsLayer {
    fn on_event(&self, event: &tracing::Event<'_>, _ctx: Context<'_, S>) {
        // 统计事件数量
        self.event_count.fetch_add(1, Ordering::Relaxed);
        
        // 访问元数据
        let metadata = event.metadata();
        println!("Event: level={}, target={}", metadata.level(), metadata.target());
    }
    
    fn on_enter(&self, id: &span::Id, _ctx: Context<'_, S>) {
        println!("Entering span: {:?}", id);
    }
    
    fn on_exit(&self, id: &span::Id, _ctx: Context<'_, S>) {
        println!("Exiting span: {:?}", id);
    }
}

// 使用自定义 Layer
pub fn init_with_custom_layer() {
    let metrics_layer = MetricsLayer::new();
    
    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(metrics_layer)
        .with(fmt::layer())
        .init();
}
```

### 4.2 条件 Layer

```rust
use tracing_subscriber::layer::Filter;

pub struct LevelFilter {
    max_level: tracing::Level,
}

impl<S: Subscriber> Filter<S> for LevelFilter {
    fn enabled(&self, meta: &tracing::Metadata<'_>, _ctx: &Context<'_, S>) -> bool {
        meta.level() <= &self.max_level
    }
}

pub fn init_with_conditional_layer() {
    let filter = LevelFilter {
        max_level: tracing::Level::INFO,
    };
    
    tracing_subscriber::registry()
        .with(fmt::layer().with_filter(filter))
        .init();
}
```

---

## 5. 日志格式化器

### 5.1 紧凑格式

```rust
pub fn init_compact_format() {
    tracing_subscriber::fmt()
        .compact()
        .with_target(false)
        .with_thread_ids(false)
        .with_line_number(false)
        .init();
}

// 输出示例:
// 2025-10-11T10:30:45Z INFO Application started
```

### 5.2 完整格式

```rust
pub fn init_full_format() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::TRACE)
        .with_target(true)
        .with_thread_ids(true)
        .with_thread_names(true)
        .with_line_number(true)
        .with_file(true)
        .with_ansi(true)
        .init();
}

// 输出示例:
// 2025-10-11T10:30:45.123456Z  INFO ThreadId(01) my_app::main:15: Application started
```

### 5.3 Pretty 格式

```rust
pub fn init_pretty_format() {
    tracing_subscriber::fmt()
        .pretty()
        .with_ansi(true)
        .init();
}

// 输出示例:
//   2025-10-11T10:30:45.123456Z  INFO my_app::main
//     at src/main.rs:15
//     Application started
```

### 5.4 自定义格式化

```rust
use tracing_subscriber::fmt::format::{self, FormatEvent, FormatFields};
use tracing_subscriber::fmt::FmtContext;
use std::fmt;

pub struct CustomFormatter;

impl<S, N> FormatEvent<S, N> for CustomFormatter
where
    S: tracing::Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        writer: format::Writer<'_>,
        event: &tracing::Event<'_>,
    ) -> fmt::Result {
        let metadata = event.metadata();
        
        // 自定义格式: [LEVEL] target - message
        write!(
            writer,
            "[{}] {} - ",
            metadata.level(),
            metadata.target()
        )?;
        
        // 写入字段
        ctx.field_format().format_fields(writer.by_ref(), event)?;
        
        writeln!(writer)
    }
}

pub fn init_custom_format() {
    tracing_subscriber::fmt()
        .event_format(CustomFormatter)
        .init();
}
```

---

## 6. 过滤器系统

### 6.1 环境变量过滤器

```rust
use tracing_subscriber::EnvFilter;

pub fn init_env_filter() {
    // 从环境变量 RUST_LOG 读取
    // 示例: RUST_LOG=debug,my_crate::module=trace
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}

// 使用示例:
// RUST_LOG=debug cargo run
// RUST_LOG=my_app=trace,sqlx=debug cargo run
```

### 6.2 动态过滤器

```rust
pub fn init_dynamic_filter() {
    let filter = EnvFilter::new("info")
        .add_directive("my_app::api=debug".parse().unwrap())
        .add_directive("sqlx=warn".parse().unwrap())
        .add_directive("tokio=info".parse().unwrap());
    
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}
```

### 6.3 基于字段的过滤

```rust
use tracing_subscriber::filter::filter_fn;

pub fn init_field_filter() {
    let filter = filter_fn(|metadata| {
        // 只记录包含 "user_id" 字段的事件
        metadata.fields().iter().any(|f| f.name() == "user_id")
    });
    
    tracing_subscriber::fmt()
        .with_filter(filter)
        .init();
}
```

---

## 7. 多层订阅者组合

### 7.1 多输出层

```rust
use tracing_appender::rolling::{RollingFileAppender, Rotation};
use tracing_subscriber::fmt::writer::MakeWriterExt;

pub fn init_multi_output() {
    // 文件日志（每天轮转）
    let file_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "logs",
        "app.log"
    );
    
    // 错误日志单独输出
    let error_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "logs",
        "error.log"
    );
    
    // 创建多个层
    let stdout_layer = fmt::layer()
        .with_writer(std::io::stdout);
    
    let file_layer = fmt::layer()
        .with_writer(file_appender)
        .with_ansi(false);
    
    let error_layer = fmt::layer()
        .with_writer(error_appender.with_max_level(tracing::Level::ERROR))
        .with_ansi(false);
    
    // 组合
    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(stdout_layer)
        .with(file_layer)
        .with(error_layer)
        .init();
}
```

### 7.2 按模块分层

```rust
pub fn init_module_specific_layers() {
    // API 模块的日志层
    let api_layer = fmt::layer()
        .with_writer(std::io::stdout)
        .with_filter(EnvFilter::new("my_app::api=debug"));
    
    // 数据库模块的日志层
    let db_layer = fmt::layer()
        .with_writer(std::io::stdout)
        .with_filter(EnvFilter::new("my_app::db=trace"));
    
    // 通用日志层
    let general_layer = fmt::layer()
        .with_writer(std::io::stdout)
        .with_filter(EnvFilter::new("info"));
    
    tracing_subscriber::registry()
        .with(api_layer)
        .with(db_layer)
        .with(general_layer)
        .init();
}
```

---

## 8. JSON 结构化日志

### 8.1 基础 JSON 格式

```rust
pub fn init_json_logging() {
    tracing_subscriber::fmt()
        .json()
        .with_current_span(true)
        .with_span_list(true)
        .init();
}

// 输出示例:
// {
//   "timestamp": "2025-10-11T10:30:45.123456Z",
//   "level": "INFO",
//   "target": "my_app::main",
//   "fields": {
//     "message": "Application started"
//   },
//   "span": {
//     "name": "request",
//     "user_id": 123
//   }
// }
```

### 8.2 扁平化 JSON

```rust
pub fn init_flatten_json() {
    tracing_subscriber::fmt()
        .json()
        .flatten_event(true)
        .with_current_span(false)
        .init();
}

// 输出示例:
// {
//   "timestamp": "2025-10-11T10:30:45.123456Z",
//   "level": "INFO",
//   "target": "my_app::main",
//   "message": "Application started",
//   "user_id": 123
// }
```

### 8.3 自定义 JSON 字段

```rust
use serde_json::json;

pub fn log_with_custom_fields() {
    tracing::info!(
        user_id = 123,
        action = "login",
        ip = "192.168.1.1",
        "User logged in"
    );
}

// 输出:
// {
//   "level": "INFO",
//   "message": "User logged in",
//   "user_id": 123,
//   "action": "login",
//   "ip": "192.168.1.1"
// }
```

---

## 9. 异步日志写入

### 9.1 非阻塞日志

```rust
use tracing_appender::non_blocking::{NonBlocking, WorkerGuard};

pub fn init_non_blocking_logging() -> WorkerGuard {
    let file_appender = tracing_appender::rolling::daily("logs", "app.log");
    
    // 创建非阻塞写入器
    let (non_blocking, guard) = tracing_appender::non_blocking(file_appender);
    
    tracing_subscriber::fmt()
        .with_writer(non_blocking)
        .init();
    
    // 返回 guard，必须保持存活
    guard
}

#[tokio::main]
async fn main() {
    let _guard = init_non_blocking_logging();
    
    // 应用逻辑
    for i in 0..10000 {
        tracing::info!(iteration = i, "Processing item");
    }
    
    // _guard 在这里被 drop，确保所有日志被写入
}
```

### 9.2 批量日志写入

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::io::Write;

pub struct BatchWriter {
    buffer: Arc<Mutex<Vec<String>>>,
    batch_size: usize,
}

impl BatchWriter {
    pub fn new(batch_size: usize) -> Self {
        Self {
            buffer: Arc::new(Mutex::new(Vec::with_capacity(batch_size))),
            batch_size,
        }
    }
    
    pub async fn write(&self, log: String) {
        let mut buffer = self.buffer.lock().await;
        buffer.push(log);
        
        if buffer.len() >= self.batch_size {
            self.flush(&mut buffer).await;
        }
    }
    
    async fn flush(&self, buffer: &mut Vec<String>) {
        // 批量写入文件或网络
        for log in buffer.drain(..) {
            // 写入逻辑
        }
    }
}
```

---

## 10. 日志轮转与归档

### 10.1 按时间轮转

```rust
use tracing_appender::rolling::{RollingFileAppender, Rotation};

pub fn init_daily_rotation() {
    let file_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "logs",
        "app.log"
    );
    
    tracing_subscriber::fmt()
        .with_writer(file_appender)
        .with_ansi(false)
        .init();
}

pub fn init_hourly_rotation() {
    let file_appender = RollingFileAppender::new(
        Rotation::HOURLY,
        "logs",
        "app.log"
    );
    
    tracing_subscriber::fmt()
        .with_writer(file_appender)
        .with_ansi(false)
        .init();
}
```

### 10.2 按大小轮转

```rust
// 需要额外依赖: rolling-file
use rolling_file::BasicRollingFileAppender;

pub fn init_size_based_rotation() {
    let file_appender = BasicRollingFileAppender::new(
        "logs/app.log",
        rolling_file::RollingConditionBasic::new()
            .daily()
            .max_size(10 * 1024 * 1024), // 10MB
        9 // 保留 9 个旧文件
    ).unwrap();
    
    // 使用 file_appender
}
```

---

## 11. OpenTelemetry 集成

### 11.1 完整集成

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_with_otlp() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP 追踪导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "my-app"),
                    KeyValue::new("service.version", "1.0.0"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 创建 OpenTelemetry 层
    let telemetry_layer = OpenTelemetryLayer::new(tracer);
    
    // 组合订阅者
    tracing_subscriber::registry()
        .with(EnvFilter::new("info"))
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer().json())
        .init();
    
    Ok(())
}

pub fn shutdown_otlp() {
    global::shutdown_tracer_provider();
}
```

### 11.2 Span 追踪

```rust
use tracing::{info_span, instrument};

#[instrument]
async fn process_request(user_id: u64) {
    let span = info_span!("database_query", user_id = user_id);
    let _enter = span.enter();
    
    // 数据库操作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    tracing::info!("Query completed");
}
```

---

## 12. 性能优化

### 12.1 过滤性能优化

```rust
// ❌ 低效：每次都评估
pub fn inefficient_logging() {
    for i in 0..1000000 {
        tracing::trace!("Processing item {}", i);  // 即使不记录，也会格式化字符串
    }
}

// ✅ 高效：使用 enabled! 宏
pub fn efficient_logging() {
    for i in 0..1000000 {
        if tracing::enabled!(tracing::Level::TRACE) {
            tracing::trace!("Processing item {}", i);
        }
    }
}
```

### 12.2 批量日志

```rust
pub fn batch_logging() {
    let items: Vec<_> = (0..1000).collect();
    
    // ❌ 低效：每个项都记录
    for item in &items {
        tracing::debug!(item = item, "Processing");
    }
    
    // ✅ 高效：批量记录
    tracing::debug!(
        count = items.len(),
        first = items.first(),
        last = items.last(),
        "Processed batch"
    );
}
```

---

## 13. 生产环境最佳实践

### 13.1 完整配置示例

```rust
use tracing_appender::rolling::{RollingFileAppender, Rotation};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_production_logging() -> Result<(), Box<dyn std::error::Error>> {
    // 文件日志（每天轮转）
    let file_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "logs",
        "app.log"
    );
    let (non_blocking_file, _guard) = tracing_appender::non_blocking(file_appender);
    
    // 错误日志单独输出
    let error_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "logs",
        "error.log"
    );
    let (non_blocking_error, _error_guard) = tracing_appender::non_blocking(error_appender);
    
    // 环境过滤器
    let env_filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    // JSON 文件层
    let file_layer = fmt::layer()
        .json()
        .with_writer(non_blocking_file)
        .with_ansi(false);
    
    // 错误文件层
    let error_layer = fmt::layer()
        .json()
        .with_writer(non_blocking_error)
        .with_ansi(false)
        .with_filter(tracing_subscriber::filter::LevelFilter::ERROR);
    
    // 控制台层（仅生产环境调试）
    let console_layer = if std::env::var("ENABLE_CONSOLE_LOGS").is_ok() {
        Some(fmt::layer().compact())
    } else {
        None
    };
    
    // OpenTelemetry 层
    let otlp_layer = if let Ok(endpoint) = std::env::var("OTLP_ENDPOINT") {
        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint(endpoint)
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)?;
        
        Some(tracing_opentelemetry::layer().with_tracer(tracer))
    } else {
        None
    };
    
    // 组合所有层
    let registry = tracing_subscriber::registry()
        .with(env_filter)
        .with(file_layer)
        .with(error_layer);
    
    let registry = if let Some(console) = console_layer {
        registry.with(console)
    } else {
        registry
    };
    
    if let Some(otlp) = otlp_layer {
        registry.with(otlp).init();
    } else {
        registry.init();
    }
    
    Ok(())
}
```

---

## 14. 国际标准对标

### 14.1 对标清单

| 标准 | Tracing-Subscriber 实现 |
|------|------------------------|
| **RFC 5424 (Syslog)** | ✅ Log Levels |
| **OpenTelemetry Logs** | ✅ 完整支持 |
| **Structured Logging** | ✅ JSON、键值对 |
| **Context Propagation** | ✅ Span Context |

---

## 15. 总结与最佳实践

### 15.1 最佳实践

#### ✅ 推荐做法

- 使用 Layer 模式组合多个输出
- 使用非阻塞日志写入
- 使用日志轮转
- 集成 OpenTelemetry
- 使用结构化日志（JSON）
- 动态过滤器控制日志级别

#### ❌ 避免做法

- 不要在热路径中记录 TRACE 级别
- 不要忽略日志文件大小
- 不要在生产环境使用同步写入
- 不要记录敏感信息（密码、密钥）

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90  
**Tracing-Subscriber 版本**: 0.3  

**国际标准对齐**:

- ✅ OpenTelemetry Logs
- ✅ RFC 5424 (Syslog Levels)
- ✅ Structured Logging Best Practices
