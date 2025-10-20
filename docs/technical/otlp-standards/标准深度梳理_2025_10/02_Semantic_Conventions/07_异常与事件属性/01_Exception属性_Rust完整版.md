# Exception 异常属性 - Rust 完整实现

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月10日

---

## 目录

- [Exception 异常属性 - Rust 完整实现](#exception-异常属性---rust-完整实现)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 异常属性的作用](#11-异常属性的作用)
    - [1.2 Rust 错误处理优势](#12-rust-错误处理优势)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
  - [3. 异常事件属性](#3-异常事件属性)
    - [3.1 标准属性定义](#31-标准属性定义)
    - [3.2 异常属性结构体](#32-异常属性结构体)
  - [4. RecordException 实现](#4-recordexception-实现)
    - [4.1 基础实现](#41-基础实现)
    - [4.2 Trait 扩展](#42-trait-扩展)
    - [4.3 自动错误记录](#43-自动错误记录)
  - [5. 与 Rust 错误类型集成](#5-与-rust-错误类型集成)
    - [5.1 std::error::Error](#51-stderrorerror)
    - [5.2 anyhow::Error](#52-anyhowerror)
    - [5.3 thiserror](#53-thiserror)
    - [5.4 自定义错误类型](#54-自定义错误类型)
  - [6. 异常 Span 状态](#6-异常-span-状态)
    - [6.1 状态码映射](#61-状态码映射)
    - [6.2 完整异常处理模式](#62-完整异常处理模式)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 何时记录异常](#71-何时记录异常)
    - [7.2 敏感信息处理](#72-敏感信息处理)
    - [7.3 多次异常记录](#73-多次异常记录)
    - [7.4 异常与 Span Status](#74-异常与-span-status)
  - [8. 完整示例](#8-完整示例)
    - [8.1 HTTP 客户端异常处理](#81-http-客户端异常处理)
    - [8.2 数据库操作异常处理](#82-数据库操作异常处理)
    - [8.3 批处理异常处理](#83-批处理异常处理)
  - [9. 高级特性](#9-高级特性)
    - [9.1 Panic 处理](#91-panic-处理)
    - [9.2 错误链追踪](#92-错误链追踪)
    - [9.3 自定义异常事件](#93-自定义异常事件)
  - [10. 性能优化](#10-性能优化)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Rust Crates](#rust-crates)

---

## 1. 概述

### 1.1 异常属性的作用

**异常属性**用于记录Span执行过程中发生的异常信息，包括异常类型、消息、堆栈跟踪等。

**核心特性**:

```text
✅ 标准化异常记录
✅ 自动堆栈跟踪捕获
✅ 支持多次异常记录
✅ 与Span状态集成
✅ Rust 类型安全保证
```

### 1.2 Rust 错误处理优势

```rust
// Rust 的错误处理哲学
// ✅ Result<T, E> 类型明确表示可能失败
// ✅ ? 运算符优雅地传播错误
// ✅ 编译期强制错误处理
// ✅ 零成本抽象
// ✅ 与 OTLP 完美集成
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "exception-handling-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 运行时
tokio = { version = "1", features = ["full"] }

# HTTP 客户端 (示例)
reqwest = "0.12"

# 数据库 (示例)
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-rustls"] }
```

### 2.2 核心导入

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, TraceContextExt},
    KeyValue,
};
use opentelemetry_sdk::trace::TracerProvider;
use std::error::Error;
use std::fmt;

// 语义约定常量
pub mod exception_conventions {
    pub const EXCEPTION_TYPE: &str = "exception.type";
    pub const EXCEPTION_MESSAGE: &str = "exception.message";
    pub const EXCEPTION_STACKTRACE: &str = "exception.stacktrace";
    pub const EXCEPTION_ESCAPED: &str = "exception.escaped";
    pub const EXCEPTION_EVENT_NAME: &str = "exception";
}
```

---

## 3. 异常事件属性

### 3.1 标准属性定义

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `exception.type` | string | ✅ | 异常类型/类名 | `std::io::Error`, `anyhow::Error` |
| `exception.message` | string | ❌ | 异常消息 | `Connection refused` |
| `exception.stacktrace` | string | ❌ | 堆栈跟踪 | `at main.rs:42` |
| `exception.escaped` | boolean | ❌ | 异常是否逃逸出Span边界 | `true` / `false` |

### 3.2 异常属性结构体

```rust
use std::backtrace::Backtrace;

/// 异常属性
#[derive(Debug, Clone)]
pub struct ExceptionAttributes {
    /// 异常类型 (必需)
    pub exception_type: String,
    
    /// 异常消息 (可选)
    pub exception_message: Option<String>,
    
    /// 堆栈跟踪 (可选)
    pub exception_stacktrace: Option<String>,
    
    /// 是否逃逸出 Span 边界 (可选)
    pub exception_escaped: bool,
}

impl ExceptionAttributes {
    /// 从任意错误创建
    pub fn from_error<E: Error>(error: &E) -> Self {
        Self {
            exception_type: std::any::type_name::<E>().to_string(),
            exception_message: Some(error.to_string()),
            exception_stacktrace: None,
            exception_escaped: false,
        }
    }
    
    /// 从错误创建并标记为逃逸
    pub fn from_error_escaped<E: Error>(error: &E) -> Self {
        Self {
            exception_type: std::any::type_name::<E>().to_string(),
            exception_message: Some(error.to_string()),
            exception_stacktrace: None,
            exception_escaped: true,
        }
    }
    
    /// 添加堆栈跟踪
    pub fn with_backtrace(mut self, backtrace: Backtrace) -> Self {
        self.exception_stacktrace = Some(backtrace.to_string());
        self
    }
    
    /// 标记为逃逸
    pub fn escaped(mut self) -> Self {
        self.exception_escaped = true;
        self
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                exception_conventions::EXCEPTION_TYPE,
                self.exception_type.clone(),
            ),
            KeyValue::new(
                exception_conventions::EXCEPTION_ESCAPED,
                self.exception_escaped,
            ),
        ];
        
        if let Some(ref message) = self.exception_message {
            attributes.push(KeyValue::new(
                exception_conventions::EXCEPTION_MESSAGE,
                message.clone(),
            ));
        }
        
        if let Some(ref stacktrace) = self.exception_stacktrace {
            attributes.push(KeyValue::new(
                exception_conventions::EXCEPTION_STACKTRACE,
                stacktrace.clone(),
            ));
        }
        
        attributes
    }
}
```

---

## 4. RecordException 实现

### 4.1 基础实现

```rust
/// 记录异常的辅助函数
pub fn record_exception<E: Error>(
    span: &mut opentelemetry::trace::BoxedSpan,
    error: &E,
    escaped: bool,
) {
    let exception = if escaped {
        ExceptionAttributes::from_error_escaped(error)
    } else {
        ExceptionAttributes::from_error(error)
    };
    
    // 记录异常事件
    span.add_event(
        exception_conventions::EXCEPTION_EVENT_NAME,
        exception.to_key_values(),
    );
    
    // 设置 Span 状态为 Error
    span.set_status(Status::error(error.to_string()));
}
```

### 4.2 Trait 扩展

```rust
/// 为 Span 添加异常记录扩展方法
pub trait SpanExceptionExt {
    /// 记录异常 (非逃逸)
    fn record_exception<E: Error>(&mut self, error: &E);
    
    /// 记录逃逸异常
    fn record_exception_escaped<E: Error>(&mut self, error: &E);
    
    /// 记录异常并设置状态
    fn record_exception_with_status<E: Error>(&mut self, error: &E, escaped: bool);
    
    /// 记录异常 (带堆栈跟踪)
    fn record_exception_with_backtrace<E: Error>(
        &mut self,
        error: &E,
        backtrace: Backtrace,
        escaped: bool,
    );
}

impl SpanExceptionExt for opentelemetry::trace::BoxedSpan {
    fn record_exception<E: Error>(&mut self, error: &E) {
        let exception = ExceptionAttributes::from_error(error);
        self.add_event(
            exception_conventions::EXCEPTION_EVENT_NAME,
            exception.to_key_values(),
        );
        self.set_status(Status::error(error.to_string()));
    }
    
    fn record_exception_escaped<E: Error>(&mut self, error: &E) {
        let exception = ExceptionAttributes::from_error_escaped(error);
        self.add_event(
            exception_conventions::EXCEPTION_EVENT_NAME,
            exception.to_key_values(),
        );
        self.set_status(Status::error(error.to_string()));
    }
    
    fn record_exception_with_status<E: Error>(&mut self, error: &E, escaped: bool) {
        if escaped {
            self.record_exception_escaped(error);
        } else {
            self.record_exception(error);
        }
    }
    
    fn record_exception_with_backtrace<E: Error>(
        &mut self,
        error: &E,
        backtrace: Backtrace,
        escaped: bool,
    ) {
        let exception = if escaped {
            ExceptionAttributes::from_error_escaped(error)
        } else {
            ExceptionAttributes::from_error(error)
        }.with_backtrace(backtrace);
        
        self.add_event(
            exception_conventions::EXCEPTION_EVENT_NAME,
            exception.to_key_values(),
        );
        self.set_status(Status::error(error.to_string()));
    }
}
```

### 4.3 自动错误记录

```rust
/// 自动记录 Result 中的错误
pub trait ResultExceptionExt<T, E> {
    /// 如果是 Err，记录异常并返回 Result
    fn record_err_to_span(self, span: &mut opentelemetry::trace::BoxedSpan) -> Result<T, E>;
}

impl<T, E: Error> ResultExceptionExt<T, E> for Result<T, E> {
    fn record_err_to_span(self, span: &mut opentelemetry::trace::BoxedSpan) -> Result<T, E> {
        if let Err(ref e) = self {
            span.record_exception(e);
        }
        self
    }
}

// 使用示例
async fn example_auto_record() -> anyhow::Result<()> {
    let tracer = global::tracer("example");
    let mut span = tracer
        .span_builder("operation")
        .start(&tracer);
    
    // 自动记录错误
    let result = risky_operation()
        .await
        .record_err_to_span(&mut span)?;
    
    span.set_status(Status::Ok);
    span.end();
    
    Ok(result)
}

async fn risky_operation() -> anyhow::Result<String> {
    // 可能失败的操作
    Ok("success".to_string())
}
```

---

## 5. 与 Rust 错误类型集成

### 5.1 std::error::Error

```rust
use std::io;

fn example_std_error() -> Result<(), io::Error> {
    let tracer = global::tracer("example");
    let mut span = tracer
        .span_builder("read_file")
        .start(&tracer);
    
    match std::fs::read_to_string("/nonexistent") {
        Ok(content) => {
            span.set_status(Status::Ok);
            Ok(())
        }
        Err(e) => {
            // std::io::Error 实现了 Error trait
            span.record_exception(&e);
            Err(e)
        }
    }
}
```

### 5.2 anyhow::Error

```rust
use anyhow::{Result, Context};

async fn example_anyhow() -> Result<()> {
    let tracer = global::tracer("example");
    let mut span = tracer
        .span_builder("complex_operation")
        .start(&tracer);
    
    // anyhow 提供丰富的错误上下文
    let result = perform_operation()
        .await
        .context("Failed to perform operation");
    
    match result {
        Ok(value) => {
            span.set_status(Status::Ok);
            Ok(value)
        }
        Err(e) => {
            // 记录 anyhow::Error (包含完整错误链)
            span.record_exception(&e);
            
            // 可选：记录错误链
            span.add_event(
                "error_chain",
                vec![KeyValue::new("chain", format!("{:?}", e))],
            );
            
            Err(e)
        }
    }
}

async fn perform_operation() -> Result<String> {
    Ok("result".to_string())
}
```

### 5.3 thiserror

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),
    
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("Business logic error: {0}")]
    Business(String),
}

async fn example_thiserror() -> Result<(), AppError> {
    let tracer = global::tracer("example");
    let mut span = tracer
        .span_builder("app_operation")
        .start(&tracer);
    
    match app_logic().await {
        Ok(()) => {
            span.set_status(Status::Ok);
            Ok(())
        }
        Err(e) => {
            // 记录类型化的错误
            span.record_exception(&e);
            
            // 添加错误类型信息
            let error_kind = match e {
                AppError::Io(_) => "io",
                AppError::Http(_) => "http",
                AppError::Database(_) => "database",
                AppError::Business(_) => "business",
            };
            
            span.set_attribute(KeyValue::new("error.kind", error_kind));
            
            Err(e)
        }
    }
}

async fn app_logic() -> Result<(), AppError> {
    Ok(())
}
```

### 5.4 自定义错误类型

```rust
/// 自定义错误类型
#[derive(Debug)]
pub struct CustomError {
    pub kind: ErrorKind,
    pub message: String,
    pub source: Option<Box<dyn Error + Send + Sync>>,
}

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    Network,
    Timeout,
    InvalidData,
    NotFound,
}

impl fmt::Display for CustomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.message)
    }
}

impl Error for CustomError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.source.as_ref().map(|e| &**e as &(dyn Error + 'static))
    }
}

impl CustomError {
    /// 转换为 OTLP 异常属性
    pub fn to_exception_attributes(&self, escaped: bool) -> ExceptionAttributes {
        ExceptionAttributes {
            exception_type: format!("CustomError::{:?}", self.kind),
            exception_message: Some(self.message.clone()),
            exception_stacktrace: self.source.as_ref().map(|s| format!("{:?}", s)),
            exception_escaped: escaped,
        }
    }
}

// 为自定义错误类型扩展 Span
pub trait SpanCustomErrorExt {
    fn record_custom_error(&mut self, error: &CustomError, escaped: bool);
}

impl SpanCustomErrorExt for opentelemetry::trace::BoxedSpan {
    fn record_custom_error(&mut self, error: &CustomError, escaped: bool) {
        let exception = error.to_exception_attributes(escaped);
        self.add_event(
            exception_conventions::EXCEPTION_EVENT_NAME,
            exception.to_key_values(),
        );
        
        // 添加额外的错误类型信息
        self.set_attribute(KeyValue::new(
            "error.kind",
            format!("{:?}", error.kind),
        ));
        
        self.set_status(Status::error(error.to_string()));
    }
}
```

---

## 6. 异常 Span 状态

### 6.1 状态码映射

| 情况 | StatusCode | 描述 |
|------|------------|------|
| 无异常 | `Ok` | 操作成功完成 |
| 有异常 | `Error` | 操作因异常失败 |
| 未设置 | `Unset` | 状态未明确（默认） |

```rust
/// Span 状态设置
pub fn set_span_status_from_result<T, E: Error>(
    span: &mut opentelemetry::trace::BoxedSpan,
    result: &Result<T, E>,
) {
    match result {
        Ok(_) => {
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.record_exception(e);
            span.set_status(Status::error(e.to_string()));
        }
    }
}
```

### 6.2 完整异常处理模式

```rust
use std::panic::{catch_unwind, AssertUnwindSafe};

/// 完整的异常处理 wrapper
pub async fn with_exception_handling<F, T, E>(
    span_name: &str,
    operation: F,
) -> Result<T, E>
where
    F: std::future::Future<Output = Result<T, E>>,
    E: Error + 'static,
{
    let tracer = global::tracer("exception-handler");
    let mut span = tracer
        .span_builder(span_name)
        .start(&tracer);
    
    // 执行操作
    let result = operation.await;
    
    // 根据结果设置 Span 状态
    match &result {
        Ok(_) => {
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.record_exception_escaped(e);
        }
    }
    
    span.end();
    result
}

// 使用示例
async fn example_with_wrapper() -> anyhow::Result<String> {
    with_exception_handling("my_operation", async {
        risky_operation().await
    }).await
}
```

---

## 7. 最佳实践

### 7.1 何时记录异常

```rust
/// 异常记录决策指南
pub mod best_practices {
    /// ✅ 应该记录的错误
    pub fn should_record_error(error: &dyn Error) -> bool {
        // 1. 影响操作结果的错误
        // 2. 外部依赖失败
        // 3. 超时和取消
        // 4. 资源耗尽
        true
    }
    
    /// ❌ 不应记录的"错误"
    pub fn should_not_record() {
        // 1. 正常的业务流程（如"用户未找到"）
        //    -> 使用 Option::None 而不是 Error
        // 2. 预期的验证错误
        //    -> 返回业务结果而不是异常
        // 3. 调试日志
        //    -> 使用 tracing::debug! 而不是 exception
    }
}

// 实现示例
#[derive(Debug)]
pub enum BusinessResult<T> {
    Success(T),
    NotFound,
    ValidationError(String),
}

pub async fn find_user(id: u64) -> BusinessResult<User> {
    // ✅ 使用业务结果而不是异常
    match database_lookup(id).await {
        Some(user) => BusinessResult::Success(user),
        None => BusinessResult::NotFound, // 不记录为异常
    }
}

#[derive(Debug)]
pub struct User {
    pub id: u64,
    pub name: String,
}

async fn database_lookup(id: u64) -> Option<User> {
    Some(User { id, name: "test".to_string() })
}
```

### 7.2 敏感信息处理

```rust
/// 安全的错误消息处理
pub mod security {
    use opentelemetry::KeyValue;
    use sha2::{Sha256, Digest};
    
    /// 哈希敏感信息
    pub fn hash_sensitive_info(info: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(info.as_bytes());
        format!("{:x}", hasher.finalize())
    }
    
    /// 清理错误消息
    pub fn sanitize_error_message(message: &str) -> String {
        // 移除敏感信息
        message
            .replace("password=", "password=***")
            .replace("token=", "token=***")
            .replace("secret=", "secret=***")
    }
}

// 使用示例
fn example_sensitive_handling(span: &mut opentelemetry::trace::BoxedSpan) {
    let error_message = "Authentication failed for user@example.com with password=secret123";
    
    // ❌ 不要直接记录
    // span.add_event("error", vec![KeyValue::new("message", error_message)]);
    
    // ✅ 清理后记录
    let safe_message = security::sanitize_error_message(error_message);
    span.add_event(
        "error",
        vec![KeyValue::new("message", safe_message)],
    );
}
```

### 7.3 多次异常记录

```rust
/// 批处理中记录多个异常
pub async fn batch_process_with_exceptions(items: Vec<Item>) -> Vec<Result<(), AppError>> {
    let tracer = global::tracer("batch-processor");
    let mut span = tracer
        .span_builder("batch_process")
        .start(&tracer);
    
    let mut results = Vec::new();
    let mut error_count = 0;
    
    for (index, item) in items.iter().enumerate() {
        match process_item(item).await {
            Ok(()) => {
                results.push(Ok(()));
            }
            Err(e) => {
                // 为每个失败项记录异常
                let exception = ExceptionAttributes::from_error(&e);
                span.add_event(
                    "item_failed",
                    vec![
                        KeyValue::new("item_index", index as i64),
                        KeyValue::new("error", e.to_string()),
                    ],
                );
                
                error_count += 1;
                results.push(Err(e));
            }
        }
    }
    
    // 设置总体状态
    span.set_attribute(KeyValue::new("total_items", items.len() as i64));
    span.set_attribute(KeyValue::new("failed_items", error_count));
    
    if error_count > 0 {
        span.set_status(Status::error(format!("{} items failed", error_count)));
    } else {
        span.set_status(Status::Ok);
    }
    
    span.end();
    results
}

#[derive(Debug)]
pub struct Item {
    pub id: u64,
}

async fn process_item(item: &Item) -> Result<(), AppError> {
    Ok(())
}
```

### 7.4 异常与 Span Status

```rust
/// Span 状态管理规则
pub mod status_rules {
    use opentelemetry::trace::{Status, BoxedSpan};
    use std::error::Error;
    
    /// 规则 1: 记录异常时应设置 Error 状态
    pub fn rule_1_record_with_status<E: Error>(
        span: &mut BoxedSpan,
        error: &E,
    ) {
        // ✅ 正确
        span.record_exception(error);
        span.set_status(Status::error(error.to_string()));
    }
    
    /// 规则 2: Error 状态不一定需要异常记录
    pub fn rule_2_error_without_exception(span: &mut BoxedSpan, http_code: u16) {
        if http_code >= 500 {
            // HTTP 500 错误，但不是 Rust 异常
            span.set_status(Status::error(format!("HTTP {}", http_code)));
            // 不调用 record_exception
        }
    }
    
    /// 规则 3: 多个异常通常只设置一次 Error 状态
    pub fn rule_3_multiple_exceptions(span: &mut BoxedSpan) {
        // 记录多个异常事件
        // span.add_event("exception_1", ...);
        // span.add_event("exception_2", ...);
        
        // 但只设置一次状态
        span.set_status(Status::error("Multiple errors occurred"));
    }
}
```

---

## 8. 完整示例

### 8.1 HTTP 客户端异常处理

```rust
use reqwest::Client;
use std::time::Duration;

pub async fn http_get_with_exception_handling(
    url: &str,
) -> anyhow::Result<reqwest::Response> {
    let tracer = global::tracer("http-client");
    
    let mut span = tracer
        .span_builder("HTTP GET")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 添加基础属性
    span.set_attribute(KeyValue::new("http.url", url));
    span.set_attribute(KeyValue::new("http.method", "GET"));
    
    // 创建客户端
    let client = Client::builder()
        .timeout(Duration::from_secs(10))
        .build()?;
    
    // 执行请求
    let result = client.get(url).send().await;
    
    match result {
        Ok(response) => {
            let status = response.status();
            span.set_attribute(KeyValue::new(
                "http.status_code",
                status.as_u16() as i64,
            ));
            
            if status.is_server_error() {
                // HTTP 5xx 错误
                span.set_status(Status::error(format!("HTTP {}", status)));
                span.add_event(
                    "http_server_error",
                    vec![KeyValue::new("status_code", status.as_u16() as i64)],
                );
            } else if status.is_client_error() {
                // HTTP 4xx 错误
                span.set_status(Status::error(format!("HTTP {}", status)));
            } else {
                span.set_status(Status::Ok);
            }
            
            span.end();
            Ok(response)
        }
        Err(e) => {
            // 网络错误或超时
            span.record_exception_escaped(&e);
            
            // 添加错误类型信息
            if e.is_timeout() {
                span.set_attribute(KeyValue::new("error.type", "timeout"));
            } else if e.is_connect() {
                span.set_attribute(KeyValue::new("error.type", "connection"));
            }
            
            span.end();
            Err(e.into())
        }
    }
}
```

### 8.2 数据库操作异常处理

```rust
use sqlx::{PgPool, Row};

pub async fn database_query_with_exception_handling(
    pool: &PgPool,
    user_id: i64,
) -> anyhow::Result<User> {
    let tracer = global::tracer("database");
    
    let mut span = tracer
        .span_builder("db_query")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 数据库属性
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    
    // 执行查询
    let start_time = std::time::Instant::now();
    let result = sqlx::query_as::<_, User>("SELECT id, name FROM users WHERE id = $1")
        .bind(user_id)
        .fetch_one(pool)
        .await;
    
    let duration = start_time.elapsed();
    span.set_attribute(KeyValue::new(
        "db.query_duration_ms",
        duration.as_millis() as i64,
    ));
    
    match result {
        Ok(user) => {
            span.set_attribute(KeyValue::new("db.rows_returned", 1));
            span.set_status(Status::Ok);
            span.end();
            Ok(user)
        }
        Err(e) => {
            // 记录数据库异常
            span.record_exception_escaped(&e);
            
            // 分类数据库错误
            match &e {
                sqlx::Error::RowNotFound => {
                    span.set_attribute(KeyValue::new("error.type", "not_found"));
                }
                sqlx::Error::PoolTimedOut => {
                    span.set_attribute(KeyValue::new("error.type", "pool_timeout"));
                }
                _ => {
                    span.set_attribute(KeyValue::new("error.type", "database"));
                }
            }
            
            span.end();
            Err(e.into())
        }
    }
}

// 自定义 FromRow 实现
#[derive(Debug)]
pub struct User {
    pub id: i64,
    pub name: String,
}

impl<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> for User {
    fn from_row(row: &'r sqlx::postgres::PgRow) -> Result<Self, sqlx::Error> {
        Ok(User {
            id: row.try_get("id")?,
            name: row.try_get("name")?,
        })
    }
}
```

### 8.3 批处理异常处理

```rust
pub async fn batch_process_users(
    user_ids: Vec<i64>,
    pool: &PgPool,
) -> BatchResult {
    let tracer = global::tracer("batch-processor");
    
    let mut span = tracer
        .span_builder("batch_process_users")
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("batch.size", user_ids.len() as i64));
    
    let mut success_count = 0;
    let mut error_count = 0;
    let mut errors = Vec::new();
    
    for (index, user_id) in user_ids.iter().enumerate() {
        match process_user(*user_id, pool).await {
            Ok(()) => {
                success_count += 1;
            }
            Err(e) => {
                error_count += 1;
                
                // 为每个失败记录异常事件
                span.add_event(
                    "user_process_failed",
                    vec![
                        KeyValue::new("user_id", *user_id),
                        KeyValue::new("index", index as i64),
                        KeyValue::new("error", e.to_string()),
                    ],
                );
                
                errors.push(UserProcessError {
                    user_id: *user_id,
                    error: e.to_string(),
                });
            }
        }
    }
    
    // 设置批处理结果属性
    span.set_attribute(KeyValue::new("batch.success_count", success_count));
    span.set_attribute(KeyValue::new("batch.error_count", error_count));
    span.set_attribute(KeyValue::new(
        "batch.success_rate",
        (success_count as f64 / user_ids.len() as f64),
    ));
    
    // 设置状态
    if error_count > 0 {
        span.set_status(Status::error(format!(
            "{}/{} items failed",
            error_count,
            user_ids.len()
        )));
    } else {
        span.set_status(Status::Ok);
    }
    
    span.end();
    
    BatchResult {
        success_count,
        error_count,
        errors,
    }
}

#[derive(Debug)]
pub struct BatchResult {
    pub success_count: usize,
    pub error_count: usize,
    pub errors: Vec<UserProcessError>,
}

#[derive(Debug)]
pub struct UserProcessError {
    pub user_id: i64,
    pub error: String,
}

async fn process_user(user_id: i64, pool: &PgPool) -> anyhow::Result<()> {
    // 处理用户逻辑
    Ok(())
}
```

---

## 9. 高级特性

### 9.1 Panic 处理

```rust
use std::panic::{catch_unwind, AssertUnwindSafe};

/// 捕获 panic 并记录为异常
pub fn with_panic_handling<F, T>(
    span_name: &str,
    operation: F,
) -> Result<T, Box<dyn Error + Send + Sync>>
where
    F: FnOnce() -> T + std::panic::UnwindSafe,
{
    let tracer = global::tracer("panic-handler");
    let mut span = tracer
        .span_builder(span_name)
        .start(&tracer);
    
    let result = catch_unwind(operation);
    
    match result {
        Ok(value) => {
            span.set_status(Status::Ok);
            span.end();
            Ok(value)
        }
        Err(panic_info) => {
            // 记录 panic 为异常
            let panic_message = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "Unknown panic".to_string()
            };
            
            let exception = ExceptionAttributes {
                exception_type: "panic".to_string(),
                exception_message: Some(panic_message.clone()),
                exception_stacktrace: None,
                exception_escaped: true,
            };
            
            span.add_event(
                exception_conventions::EXCEPTION_EVENT_NAME,
                exception.to_key_values(),
            );
            
            span.set_status(Status::error("Panic occurred"));
            span.end();
            
            Err(panic_message.into())
        }
    }
}
```

### 9.2 错误链追踪

```rust
/// 记录完整的错误链
pub fn record_error_chain<E: Error>(
    span: &mut opentelemetry::trace::BoxedSpan,
    error: &E,
) {
    // 记录顶层异常
    span.record_exception(error);
    
    // 遍历错误链
    let mut source = error.source();
    let mut depth = 0;
    
    while let Some(e) = source {
        depth += 1;
        span.add_event(
            format!("error_source_{}", depth),
            vec![
                KeyValue::new("depth", depth),
                KeyValue::new("type", std::any::type_name_of_val(e)),
                KeyValue::new("message", e.to_string()),
            ],
        );
        
        source = e.source();
        
        // 防止无限循环
        if depth > 10 {
            break;
        }
    }
    
    span.set_attribute(KeyValue::new("error.chain_depth", depth));
}
```

### 9.3 自定义异常事件

```rust
/// 自定义异常事件类型
pub struct CustomExceptionEvent {
    pub name: String,
    pub severity: Severity,
    pub attributes: Vec<KeyValue>,
}

#[derive(Debug, Clone, Copy)]
pub enum Severity {
    Low,
    Medium,
    High,
    Critical,
}

impl CustomExceptionEvent {
    pub fn record_to_span(self, span: &mut opentelemetry::trace::BoxedSpan) {
        let mut attributes = self.attributes;
        attributes.push(KeyValue::new(
            "severity",
            format!("{:?}", self.severity),
        ));
        
        span.add_event(&self.name, attributes);
    }
}
```

---

## 10. 性能优化

```rust
/// 性能优化建议
pub mod performance {
    use once_cell::sync::Lazy;
    
    /// 1. 避免在热路径中记录异常
    pub fn avoid_hot_path_exceptions() {
        // ❌ 不要在循环中频繁记录
        // for item in items {
        //     if let Err(e) = process(item) {
        //         span.record_exception(&e); // 热路径!
        //     }
        // }
        
        // ✅ 批量记录或汇总
        // 记录错误计数而不是每个错误
    }
    
    /// 2. 缓存常用的异常属性
    static COMMON_ERROR_ATTRS: Lazy<Vec<KeyValue>> = Lazy::new(|| {
        vec![
            KeyValue::new("service.name", "my-service"),
            KeyValue::new("environment", "production"),
        ]
    });
    
    /// 3. 使用采样减少开销
    pub fn should_record_exception(error: &dyn std::error::Error) -> bool {
        // 实现采样逻辑
        // 例如：只记录 10% 的某类错误
        true
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Exception Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/exceptions/>
2. **OpenTelemetry Rust SDK**: <https://github.com/open-telemetry/opentelemetry-rust>
3. **Rust Error Handling**: <https://doc.rust-lang.org/book/ch09-00-error-handling.html>

### Rust Crates

1. **anyhow**: <https://github.com/dtolnay/anyhow>
2. **thiserror**: <https://github.com/dtolnay/thiserror>
3. **tracing**: <https://github.com/tokio-rs/tracing>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
