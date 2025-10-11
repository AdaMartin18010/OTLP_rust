# 📋 Logs 概述 Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [📋 Logs 概述 Rust 完整版](#-logs-概述-rust-完整版)
  - [📋 目录](#-目录)
  - [1. Logs 概述](#1-logs-概述)
    - [1.1 什么是 OpenTelemetry Logs？](#11-什么是-opentelemetry-logs)
    - [1.2 核心概念](#12-核心概念)
    - [1.3 Logs vs Traces vs Metrics](#13-logs-vs-traces-vs-metrics)
  - [2. OpenTelemetry Logs 架构](#2-opentelemetry-logs-架构)
    - [2.1 日志处理流程](#21-日志处理流程)
    - [2.2 LogRecord 结构](#22-logrecord-结构)
  - [3. Rust 日志生态系统](#3-rust-日志生态系统)
    - [3.1 核心库对比](#31-核心库对比)
    - [3.2 推荐组合](#32-推荐组合)
  - [4. OpenTelemetry + tracing 集成](#4-opentelemetry--tracing-集成)
    - [4.1 基本配置](#41-基本配置)
    - [4.2 完整集成（Logs + Traces）](#42-完整集成logs--traces)
  - [5. 结构化日志](#5-结构化日志)
    - [5.1 基本结构化日志](#51-基本结构化日志)
    - [5.2 使用 Span 上下文](#52-使用-span-上下文)
    - [5.3 动态字段](#53-动态字段)
  - [6. 日志级别与过滤](#6-日志级别与过滤)
    - [6.1 日志级别](#61-日志级别)
    - [6.2 环境变量过滤](#62-环境变量过滤)
    - [6.3 代码中配置过滤器](#63-代码中配置过滤器)
    - [6.4 动态过滤](#64-动态过滤)
  - [7. 分布式追踪集成](#7-分布式追踪集成)
    - [7.1 日志与 Span 关联](#71-日志与-span-关联)
    - [7.2 手动关联 TraceContext](#72-手动关联-tracecontext)
    - [7.3 提取 Trace 信息到日志](#73-提取-trace-信息到日志)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 日志内容规范](#81-日志内容规范)
    - [8.2 日志级别选择](#82-日志级别选择)
    - [8.3 敏感信息处理](#83-敏感信息处理)
    - [8.4 性能考虑](#84-性能考虑)
  - [9. 性能优化](#9-性能优化)
    - [9.1 批量日志导出](#91-批量日志导出)
    - [9.2 异步日志](#92-异步日志)
    - [9.3 采样](#93-采样)
  - [10. 实战案例](#10-实战案例)
    - [10.1 Web 服务日志](#101-web-服务日志)
    - [10.2 数据库操作日志](#102-数据库操作日志)
    - [10.3 错误追踪](#103-错误追踪)
  - [🔗 参考资源](#-参考资源)

---

## 1. Logs 概述

### 1.1 什么是 OpenTelemetry Logs？

**OpenTelemetry Logs** 是 OpenTelemetry 三大信号（Traces、Metrics、Logs）之一，提供了统一的日志收集和导出标准。

### 1.2 核心概念

| 概念 | 说明 | 示例 |
|------|------|------|
| **LogRecord** | 单条日志记录 | 包含时间戳、级别、消息、属性 |
| **Severity** | 日志严重级别 | TRACE, DEBUG, INFO, WARN, ERROR, FATAL |
| **Body** | 日志内容 | 文本消息或结构化数据 |
| **Attributes** | 附加元数据 | `user.id`, `http.status_code` |
| **Resource** | 日志来源 | `service.name`, `host.name` |
| **TraceContext** | 追踪关联 | 关联到 Trace 和 Span |

### 1.3 Logs vs Traces vs Metrics

```text
Logs:    事件记录（What happened?）
         ├─ 详细的事件描述
         ├─ 上下文信息
         └─ 问题诊断

Traces:  请求追踪（How long? What path?）
         ├─ 请求链路
         ├─ 性能分析
         └─ 依赖关系

Metrics: 数值度量（How many? How much?）
         ├─ 聚合统计
         ├─ 趋势分析
         └─ 告警触发
```

---

## 2. OpenTelemetry Logs 架构

### 2.1 日志处理流程

```text
Application
    │
    ├─ tracing::info!("message")
    │       │
    │       ▼
    ├─ tracing Subscriber
    │       │
    │       ▼
    ├─ OpenTelemetry Layer
    │       │
    │       ▼
    ├─ LogRecord
    │       │
    │       ▼
    ├─ LogRecordProcessor
    │       │
    │       ▼
    ├─ LogRecordExporter
    │       │
    │       ▼
    └─ OTLP Collector
```

### 2.2 LogRecord 结构

```rust
use opentelemetry::logs::{LogRecord, Severity};
use opentelemetry::KeyValue;
use std::time::SystemTime;

pub struct LogRecord {
    /// 时间戳
    pub timestamp: SystemTime,
    
    /// 观察时间戳
    pub observed_timestamp: SystemTime,
    
    /// 严重级别
    pub severity_number: Severity,
    
    /// 严重级别文本
    pub severity_text: Option<String>,
    
    /// 日志内容
    pub body: Option<String>,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
    
    /// Trace 上下文
    pub trace_context: Option<TraceContext>,
}
```

---

## 3. Rust 日志生态系统

### 3.1 核心库对比

| 库 | 特点 | 使用场景 |
|---|------|----------|
| **log** | 最基础的日志 facade | 库开发 |
| **tracing** | 结构化日志 + 追踪 | 现代应用 |
| **slog** | 高性能结构化日志 | 性能关键应用 |
| **env_logger** | 简单的日志实现 | 快速原型 |
| **tracing-subscriber** | tracing 订阅者 | 生产环境 |

### 3.2 推荐组合

**生产环境推荐**：

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31.0"
opentelemetry = "0.31.0"
opentelemetry-otlp = "0.31.0"
```

---

## 4. OpenTelemetry + tracing 集成

### 4.1 基本配置

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use opentelemetry::global;
use opentelemetry_sdk::logs::LoggerProvider;

fn init_logging() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OpenTelemetry Logs
    let logger_provider = LoggerProvider::builder()
        .with_simple_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .build();
    
    global::set_logger_provider(logger_provider);
    
    // 2. 初始化 tracing
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_target(true)
                .with_thread_ids(true)
                .with_line_number(true)
        )
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_logging()?;
    
    tracing::info!("Application started");
    tracing::debug!(user = "alice", "User logged in");
    tracing::warn!(retry = 3, "Retry attempt");
    tracing::error!(error = %err, "Failed to process request");
    
    Ok(())
}
```

### 4.2 完整集成（Logs + Traces）

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config as TraceConfig, TracerProvider},
    logs::LoggerProvider,
    Resource,
};
use tracing_subscriber::layer::SubscriberExt;

fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // 共享 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);
    
    // 1. Traces
    let tracer_provider = TracerProvider::builder()
        .with_config(TraceConfig::default().with_resource(resource.clone()))
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();
    
    global::set_tracer_provider(tracer_provider.clone());
    
    // 2. Logs
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();
    
    global::set_logger_provider(logger_provider);
    
    // 3. tracing Subscriber
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer_provider.tracer("my-service"));
    
    tracing_subscriber::registry()
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}
```

---

## 5. 结构化日志

### 5.1 基本结构化日志

```rust
use tracing::{info, warn, error};

// 简单日志
info!("User logged in");

// 带字段的结构化日志
info!(
    user.id = 123,
    user.name = "Alice",
    "User logged in"
);

// 带多个字段
warn!(
    attempt = 3,
    max_retries = 5,
    delay_ms = 1000,
    "Retry attempt"
);

// 带错误信息
error!(
    error = %err,
    error.type = err.type_name(),
    "Failed to process request"
);
```

### 5.2 使用 Span 上下文

```rust
use tracing::{info_span, instrument};

#[instrument(fields(user.id = %user_id))]
async fn process_user(user_id: u64) -> Result<(), Error> {
    info!("Starting user processing");  // 自动包含 user.id
    
    let span = info_span!("database_query", table = "users");
    let _enter = span.enter();
    
    info!("Querying database");  // 自动包含 table 字段
    
    let user = fetch_user(user_id).await?;
    
    info!(user.name = %user.name, "User fetched");
    
    Ok(())
}
```

### 5.3 动态字段

```rust
use tracing::Span;

async fn dynamic_logging() {
    let span = tracing::info_span!("request");
    let _enter = span.enter();
    
    // 稍后添加字段
    span.record("status", &"processing");
    
    // 条件记录
    if let Some(user_id) = get_user_id() {
        span.record("user.id", &user_id);
    }
    
    tracing::info!("Request processed");
}
```

---

## 6. 日志级别与过滤

### 6.1 日志级别

```rust
use tracing::{trace, debug, info, warn, error};

fn logging_levels() {
    trace!("Very detailed information");  // TRACE
    debug!("Debugging information");      // DEBUG
    info!("General information");         // INFO
    warn!("Warning message");             // WARN
    error!("Error occurred");             // ERROR
}
```

### 6.2 环境变量过滤

```bash
# 只显示 INFO 及以上
export RUST_LOG=info

# 特定模块的级别
export RUST_LOG=my_app=debug,hyper=info

# 多个目标
export RUST_LOG=my_app::api=trace,my_app::db=debug,info

# 更复杂的过滤
export RUST_LOG="my_app::api[{user.id=123}]=trace,info"
```

### 6.3 代码中配置过滤器

```rust
use tracing_subscriber::EnvFilter;

fn init_with_filter() {
    let filter = EnvFilter::new("info")
        .add_directive("my_app::api=debug".parse().unwrap())
        .add_directive("hyper=warn".parse().unwrap());
    
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}
```

### 6.4 动态过滤

```rust
use tracing_subscriber::reload;

fn dynamic_filter_example() {
    let (filter, reload_handle) = reload::Layer::new(EnvFilter::new("info"));
    
    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    // 运行时修改过滤器
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(60)).await;
        reload_handle.modify(|filter| *filter = EnvFilter::new("debug")).ok();
    });
}
```

---

## 7. 分布式追踪集成

### 7.1 日志与 Span 关联

```rust
use tracing::{info, instrument};
use opentelemetry::global;

#[instrument]
async fn handle_request(request_id: String) -> Result<(), Error> {
    info!("Handling request");  // 自动关联到 Span
    
    let result = process_request().await;
    
    match result {
        Ok(_) => info!("Request completed successfully"),
        Err(e) => error!(error = %e, "Request failed"),
    }
    
    Ok(())
}
```

### 7.2 手动关联 TraceContext

```rust
use opentelemetry::{
    trace::{TraceContextExt, Tracer},
    Context,
};

async fn manual_correlation() {
    let tracer = global::tracer("my-service");
    let span = tracer.start("operation");
    let cx = Context::current_with_span(span);
    
    let _guard = cx.attach();
    
    // 这些日志会自动包含 trace_id 和 span_id
    tracing::info!("Operation started");
    tracing::debug!("Processing step 1");
    tracing::info!("Operation completed");
}
```

### 7.3 提取 Trace 信息到日志

```rust
use tracing::{info, Span};
use opentelemetry::trace::SpanContext;

fn log_with_trace_info() {
    let current_span = Span::current();
    
    // 获取 SpanContext
    if let Some(span_context) = get_span_context(&current_span) {
        info!(
            trace_id = %span_context.trace_id(),
            span_id = %span_context.span_id(),
            "Processing with trace context"
        );
    }
}
```

---

## 8. 最佳实践

### 8.1 日志内容规范

**✅ 好的实践**：

```rust
// 清晰的消息
info!("User authentication successful");

// 结构化字段
info!(
    user.id = user_id,
    user.email = %email,
    auth.method = "oauth2",
    "User authenticated"
);

// 包含上下文
error!(
    error = %err,
    request.id = %request_id,
    retry.count = retry_count,
    "Failed to process request"
);
```

**❌ 不好的实践**：

```rust
// 消息不清晰
info!("Done");

// 缺少上下文
error!("Error");

// 过度详细
trace!("{:?}", massive_struct);  // 可能输出 MB 级数据

// 敏感信息
info!(password = password, "User login");  // ❌ 泄露密码
```

### 8.2 日志级别选择

| 级别 | 使用场景 | 示例 |
|------|---------|------|
| **TRACE** | 极详细的调试信息 | 函数进入/退出、变量值 |
| **DEBUG** | 调试信息 | 中间计算结果、状态变化 |
| **INFO** | 一般信息 | 请求开始/完成、配置加载 |
| **WARN** | 警告信息 | 重试、降级、非致命错误 |
| **ERROR** | 错误信息 | 处理失败、异常情况 |

### 8.3 敏感信息处理

```rust
use tracing::field::{Field, Visit};

struct SensitiveRedactor;

impl Visit for SensitiveRedactor {
    fn record_str(&mut self, field: &Field, value: &str) {
        if field.name().contains("password") || field.name().contains("token") {
            println!("{}=[REDACTED]", field.name());
        } else {
            println!("{}={}", field.name(), value);
        }
    }
}

// 或使用自定义格式化
fn safe_log_user(user: &User) {
    info!(
        user.id = user.id,
        user.email = %mask_email(&user.email),
        "User information"
    );
}

fn mask_email(email: &str) -> String {
    if let Some(at) = email.find('@') {
        format!("{}***@{}", &email[..1], &email[at+1..])
    } else {
        "***".to_string()
    }
}
```

### 8.4 性能考虑

```rust
// ✅ 延迟计算
debug!(expensive_calculation = ?compute_expensive(), "Debug info");

// ✅ 条件日志
if tracing::enabled!(tracing::Level::DEBUG) {
    let expensive_value = compute_expensive();
    debug!(?expensive_value, "Expensive debug info");
}

// ❌ 总是计算
debug!("Value: {}", expensive_calculation());  // 即使不输出也会计算
```

---

## 9. 性能优化

### 9.1 批量日志导出

```rust
use opentelemetry_sdk::logs::{BatchLogProcessor, Config};

fn init_batch_logging() -> Result<(), Box<dyn std::error::Error>> {
    let config = Config::default()
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5));
    
    let processor = BatchLogProcessor::builder(
        opentelemetry_otlp::new_exporter().tonic(),
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_batch_config(config)
    .build();
    
    let logger_provider = LoggerProvider::builder()
        .with_log_processor(processor)
        .build();
    
    global::set_logger_provider(logger_provider);
    
    Ok(())
}
```

### 9.2 异步日志

```rust
use tracing_subscriber::fmt::format::FmtSpan;

fn init_async_logging() {
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_ansi(false)  // 禁用颜色减少开销
        .with_span_events(FmtSpan::CLOSE)  // 只在 Span 结束时记录
        .init();
}
```

### 9.3 采样

```rust
use tracing_subscriber::filter::LevelFilter;

fn init_sampled_logging() {
    let filter = EnvFilter::new("info")
        // 高频路径降级
        .add_directive("my_app::hot_path=warn".parse().unwrap());
    
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}
```

---

## 10. 实战案例

### 10.1 Web 服务日志

```rust
use axum::{
    Router,
    routing::get,
    middleware::{self, Next},
    response::Response,
    http::Request,
};
use tracing::{info, instrument};

#[instrument(skip(request, next))]
async fn logging_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let method = request.method().clone();
    let uri = request.uri().clone();
    let start = std::time::Instant::now();
    
    info!(
        http.method = %method,
        http.uri = %uri,
        "Request started"
    );
    
    let response = next.run(request).await;
    
    let duration = start.elapsed();
    let status = response.status();
    
    info!(
        http.method = %method,
        http.uri = %uri,
        http.status_code = status.as_u16(),
        duration_ms = duration.as_millis() as u64,
        "Request completed"
    );
    
    response
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    let app = Router::new()
        .route("/", get(|| async { "Hello" }))
        .layer(middleware::from_fn(logging_middleware));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

### 10.2 数据库操作日志

```rust
use sqlx::{PgPool, Row};
use tracing::{info, error, instrument};

pub struct LoggedDatabase {
    pool: PgPool,
}

impl LoggedDatabase {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    #[instrument(skip(self, query))]
    pub async fn execute(&self, query: &str) -> Result<u64, sqlx::Error> {
        info!(db.statement = query, "Executing query");
        
        let start = std::time::Instant::now();
        let result = sqlx::query(query).execute(&self.pool).await;
        let duration = start.elapsed();
        
        match &result {
            Ok(result) => {
                info!(
                    db.statement = query,
                    db.rows_affected = result.rows_affected(),
                    duration_ms = duration.as_millis() as u64,
                    "Query executed successfully"
                );
            }
            Err(e) => {
                error!(
                    error = %e,
                    db.statement = query,
                    duration_ms = duration.as_millis() as u64,
                    "Query failed"
                );
            }
        }
        
        result.map(|r| r.rows_affected())
    }
}
```

### 10.3 错误追踪

```rust
use thiserror::Error;
use tracing::{error, warn};

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    #[error("Not found: {0}")]
    NotFound(String),
}

#[instrument]
async fn handle_error_example() -> Result<(), AppError> {
    match risky_operation().await {
        Ok(result) => {
            info!("Operation succeeded");
            Ok(result)
        }
        Err(e) => {
            error!(
                error = %e,
                error.type = ?std::any::type_name_of_val(&e),
                "Operation failed"
            );
            Err(e)
        }
    }
}

// 带重试的错误处理
#[instrument(skip(f))]
async fn retry_with_logging<F, T, E>(
    f: F,
    max_attempts: usize,
) -> Result<T, E>
where
    F: Fn() -> std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    for attempt in 1..=max_attempts {
        match f().await {
            Ok(result) => {
                if attempt > 1 {
                    info!(attempt, "Retry succeeded");
                }
                return Ok(result);
            }
            Err(e) => {
                if attempt < max_attempts {
                    warn!(
                        error = %e,
                        attempt,
                        max_attempts,
                        "Retry attempt failed"
                    );
                } else {
                    error!(
                        error = %e,
                        attempt,
                        "All retry attempts exhausted"
                    );
                    return Err(e);
                }
            }
        }
    }
    unreachable!()
}
```

---

## 🔗 参考资源

- [OpenTelemetry Logs Specification](https://opentelemetry.io/docs/specs/otel/logs/)
- [tracing Documentation](https://docs.rs/tracing/)
- [tracing-subscriber Documentation](https://docs.rs/tracing-subscriber/)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry/)
- [Rust OTLP 快速入门](../../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../../README.md) | [📊 Metrics](../02_Metrics数据模型/README.md) | [🔍 Traces](../01_Traces数据模型/README.md)
