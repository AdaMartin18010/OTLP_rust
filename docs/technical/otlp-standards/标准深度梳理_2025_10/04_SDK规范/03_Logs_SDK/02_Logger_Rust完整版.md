# Logger - Rust 完整实现指南

## 📋 目录

- [Logger - Rust 完整实现指南](#logger---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Logger 的职责](#logger-的职责)
    - [1. **LogRecord 创建**](#1-logrecord-创建)
    - [2. **作用域管理**](#2-作用域管理)
  - [Rust 实现](#rust-实现)
    - [基础用法](#基础用法)
      - [**创建 Logger**](#创建-logger)
      - [**完整 LogRecord 示例**](#完整-logrecord-示例)
    - [结构化日志](#结构化日志)
      - [**属性最佳实践**](#属性最佳实践)
      - [**嵌套结构（JSON）**](#嵌套结构json)
    - [严重等级](#严重等级)
      - [**标准等级映射**](#标准等级映射)
    - [与 tracing 集成](#与-tracing-集成)
      - [**tracing 宏与 OpenTelemetry 映射**](#tracing-宏与-opentelemetry-映射)
    - [上下文传播](#上下文传播)
      - [**自动关联 Trace 和 Span**](#自动关联-trace-和-span)
  - [高级模式](#高级模式)
    - [**条件日志：避免无效记录**](#条件日志避免无效记录)
    - [**采样控制**](#采样控制)
    - [**异常记录**](#异常记录)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**tracing 集成**](#tracing-集成)
    - [**工具库**](#工具库)
  - [总结](#总结)

---

## 核心概念

**Logger** 是记录日志的接口，由 LoggerProvider 管理。每个 Logger 由 **instrumentation_scope** 唯一标识：

```rust
let logger = global::logger_with_scope(
    "my-library",      // 库名
    Some("1.0.0"),     // 版本
    Some("https://schema"), // Schema URL
    None               // 属性
);
```

**关键特性**：

- **LogRecord 工厂**：创建结构化日志记录
- **作用域隔离**：不同库的日志互不干扰
- **上下文关联**：自动关联 Trace/Span

```text
┌───────────────────────────────────────────────┐
│            LoggerProvider                     │
│  ┌────────────────────────────────────────┐   │
│  │ Logger("http-server", "2.0.0")         │   │
│  │   └─ emit(LogRecord: INFO "Request")   │   │
│  ├────────────────────────────────────────┤   │
│  │ Logger("database", "1.5.0")            │   │
│  │   └─ emit(LogRecord: ERROR "Timeout")  │   │
│  └────────────────────────────────────────┘   │
└───────────────────────────────────────────────┘
```

---

## Logger 的职责

### 1. **LogRecord 创建**

- **Severity**：TRACE → DEBUG → INFO → WARN → ERROR → FATAL
- **Body**：日志消息（字符串或结构化数据）
- **Attributes**：键值对（如 `user_id`、`request_id`）
- **Context**：关联 Trace ID 和 Span ID

### 2. **作用域管理**

- 每个 Logger 关联一个 **instrumentation_scope**
- 后端可按 Logger 过滤/聚合日志
- 支持库版本升级时的平滑迁移

---

## Rust 实现

### 基础用法

#### **创建 Logger**

```rust
use opentelemetry::{global, logs::{Logger, LogRecord}, KeyValue};

#[tokio::main]
async fn main() {
    // 方式 1: 简单名称
    let logger = global::logger("my-service");

    // 方式 2: 带版本号
    let logger = global::logger_with_scope(
        "my-service",
        Some("1.2.3"),
        None,
        None
    );

    // 记录日志
    logger.emit(
        LogRecord::builder()
            .with_severity_text("INFO")
            .with_severity_number(9) // INFO = 9
            .with_body("Application started successfully")
            .build()
    );
}
```

---

#### **完整 LogRecord 示例**

```rust
use opentelemetry::logs::{LogRecord, Severity};

let logger = global::logger("http-server");

logger.emit(
    LogRecord::builder()
        .with_timestamp(std::time::SystemTime::now())
        .with_severity_number(Severity::Info as i32)
        .with_severity_text("INFO")
        .with_body("HTTP request received")
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.target", "/api/users"),
            KeyValue::new("http.status_code", 200),
            KeyValue::new("response_time_ms", 45),
        ])
        .with_trace_context(/* 当前 Trace Context */)
        .build()
);
```

---

### 结构化日志

#### **属性最佳实践**

```rust
// ✅ 结构化属性（推荐）
logger.emit(
    LogRecord::builder()
        .with_severity_text("ERROR")
        .with_body("Database connection failed")
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.connection.string", "postgres://localhost"),
            KeyValue::new("error.type", "ConnectionTimeout"),
            KeyValue::new("retry_count", 3),
        ])
        .build()
);

// ❌ 非结构化（不推荐）
logger.emit(
    LogRecord::builder()
        .with_severity_text("ERROR")
        .with_body("Database connection failed: postgresql at postgres://localhost, retry 3 times")
        .build()
);
```

---

#### **嵌套结构（JSON）**

```rust
use serde_json::json;

logger.emit(
    LogRecord::builder()
        .with_severity_text("INFO")
        .with_body(json!({
            "event": "user_login",
            "user": {
                "id": 12345,
                "email": "user@example.com"
            },
            "metadata": {
                "ip": "192.168.1.1",
                "user_agent": "Mozilla/5.0"
            }
        }).to_string())
        .build()
);
```

---

### 严重等级

#### **标准等级映射**

| 等级 | Severity Number | 使用场景 |
|------|----------------|---------|
| TRACE | 1-4 | 详细调试信息 |
| DEBUG | 5-8 | 调试信息 |
| INFO | 9-12 | 常规信息 |
| WARN | 13-16 | 警告信息 |
| ERROR | 17-20 | 错误信息 |
| FATAL | 21-24 | 致命错误 |

```rust
use opentelemetry::logs::Severity;

// 方式 1: 使用枚举
logger.emit(
    LogRecord::builder()
        .with_severity_number(Severity::Error as i32)
        .with_severity_text("ERROR")
        .with_body("Critical failure")
        .build()
);

// 方式 2: 直接使用数字
logger.emit(
    LogRecord::builder()
        .with_severity_number(17)  // ERROR
        .with_severity_text("ERROR")
        .with_body("Critical failure")
        .build()
);
```

---

### 与 tracing 集成

**推荐方式：使用 `tracing` 宏自动生成 OpenTelemetry 日志**

```rust
use tracing::{info, warn, error, debug};
use tracing_subscriber::{layer::SubscriberExt, Registry};
use opentelemetry_appender_tracing::layer::OpenTelemetryTracingBridge;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 LoggerProvider
    let provider = init_logger_provider().await?;
    global::set_logger_provider(provider.clone());

    // 2. 桥接 tracing 到 OpenTelemetry
    let otel_layer = OpenTelemetryTracingBridge::new(&provider);
    
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer())
        .with(otel_layer);
    
    tracing::subscriber::set_global_default(subscriber)?;

    // 3. 使用 tracing 宏（自动转换为 OpenTelemetry 日志）
    info!("Server started on port 8080");
    
    debug!(
        user_id = 123,
        action = "login",
        "User authentication attempt"
    );
    
    warn!(
        retry_count = 3,
        "API rate limit approaching"
    );
    
    error!(
        error = %std::io::Error::new(std::io::ErrorKind::Other, "Network error"),
        "Failed to connect to database"
    );

    provider.shutdown()?;
    Ok(())
}
```

---

#### **tracing 宏与 OpenTelemetry 映射**

| tracing 宏 | OpenTelemetry Severity | Severity Number |
|-----------|------------------------|----------------|
| `trace!()` | TRACE | 1 |
| `debug!()` | DEBUG | 5 |
| `info!()` | INFO | 9 |
| `warn!()` | WARN | 13 |
| `error!()` | ERROR | 17 |

---

### 上下文传播

#### **自动关联 Trace 和 Span**

```rust
use opentelemetry::trace::{Tracer, TracerProvider as _};
use tracing::instrument;

#[instrument]
async fn process_payment(amount: f64) {
    // tracing 自动关联当前 Span
    info!(
        amount = amount,
        currency = "USD",
        "Processing payment"
    );
    
    // 模拟支付处理
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    info!("Payment completed successfully");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Tracer 和 Logger
    let tracer = global::tracer("payment-service");
    
    // 创建 Span
    let span = tracer.start("payment-transaction");
    let _guard = span.enter();
    
    // 日志会自动携带 Span ID 和 Trace ID
    process_payment(99.99).await;
    
    Ok(())
}
```

**导出的日志将包含**：

```json
{
  "timestamp": "2025-10-10T12:00:00Z",
  "severity": "INFO",
  "body": "Processing payment",
  "attributes": {
    "amount": 99.99,
    "currency": "USD"
  },
  "trace_id": "a1b2c3d4e5f6g7h8i9j0",
  "span_id": "1a2b3c4d5e6f7g8h"
}
```

---

## 高级模式

### **条件日志：避免无效记录**

```rust
let logger = global::logger("app");

async fn handle_request(status: u16) {
    // 仅在错误时记录
    if status >= 400 {
        logger.emit(
            LogRecord::builder()
                .with_severity_text(if status >= 500 { "ERROR" } else { "WARN" })
                .with_body(format!("HTTP {} response", status))
                .with_attributes(vec![
                    KeyValue::new("http.status_code", status as i64),
                ])
                .build()
        );
    }
}
```

---

### **采样控制**

```rust
use rand::Rng;

fn should_log_debug() -> bool {
    // 仅记录 10% 的 DEBUG 日志
    rand::thread_rng().gen_bool(0.1)
}

if should_log_debug() {
    debug!("Detailed debug information");
}
```

---

### **异常记录**

```rust
fn handle_error(err: &dyn std::error::Error) {
    error!(
        error.type = err.to_string(),
        error.message = %err,
        backtrace = ?std::backtrace::Backtrace::capture(),
        "Unhandled exception"
    );
}

// 使用示例
match risky_operation() {
    Ok(_) => info!("Operation succeeded"),
    Err(e) => handle_error(&e),
}
```

---

## 最佳实践

### ✅ **推荐**

1. **使用 tracing 宏**：比直接调用 Logger API 更简洁
2. **结构化属性**：使用 `with_attributes()` 而非嵌入文本
3. **语义约定**：遵循 OpenTelemetry 标准属性名

   ```rust
   use opentelemetry_semantic_conventions as semconv;
   KeyValue::new(semconv::trace::HTTP_REQUEST_METHOD, "GET")
   ```

4. **合适的严重等级**：
   - DEBUG：开发调试
   - INFO：业务事件
   - WARN：可恢复错误
   - ERROR：需要人工介入的错误
5. **关联 Trace**：使用 `#[instrument]` 自动关联
6. **避免敏感信息**：不记录密码、令牌、信用卡号
7. **低频 TRACE/DEBUG**：生产环境应禁用或采样

### ❌ **避免**

1. **非结构化日志**：难以查询和分析
2. **高基数属性**：如完整 URL、UUID
3. **过度记录**：每秒数千条 DEBUG 日志
4. **阻塞操作**：Logger 应快速返回
5. **忽略错误**：日志导出失败应有降级方案

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-semantic-conventions = "0.16"
```

### **tracing 集成**

```toml
tracing = "0.1"
tracing-subscriber = "0.3"
opentelemetry-appender-tracing = "0.5"
```

### **工具库**

```toml
serde_json = "1.0"         # JSON 序列化
rand = "0.8"               # 采样控制
```

---

## 总结

| 功能 | 实现方式 |
|------|---------|
| 基础日志 | `logger.emit(LogRecord::builder()...)` |
| 结构化属性 | `with_attributes(vec![KeyValue::new(...)])` |
| 严重等级 | `with_severity_number()` + `with_severity_text()` |
| tracing 集成 | `OpenTelemetryTracingBridge` |
| 上下文关联 | `#[instrument]` 自动关联 Trace |
| 条件记录 | `if` 判断 + 采样控制 |

**下一步**：[03_LogRecordProcessor_Rust完整版.md](./03_LogRecordProcessor_Rust完整版.md) - 学习日志处理器的配置
