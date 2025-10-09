# Tracer - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [Tracer - Rust 完整实现指南](#tracer---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 Tracer](#11-什么是-tracer)
    - [1.2 Tracer 在架构中的位置](#12-tracer-在架构中的位置)
  - [2. Tracer 核心概念](#2-tracer-核心概念)
    - [2.1 Tracer 接口](#21-tracer-接口)
    - [2.2 获取 Tracer](#22-获取-tracer)
  - [3. 创建 Span](#3-创建-span)
    - [3.1 基础 Span 创建](#31-基础-span-创建)
    - [3.2 使用 SpanBuilder](#32-使用-spanbuilder)
    - [3.3 创建子 Span](#33-创建子-span)
    - [3.4 创建根 Span（新 Trace）](#34-创建根-span新-trace)
  - [4. Span 上下文管理](#4-span-上下文管理)
    - [4.1 获取当前 Span](#41-获取当前-span)
    - [4.2 设置当前 Span](#42-设置当前-span)
    - [4.3 嵌套 Span 上下文](#43-嵌套-span-上下文)
  - [5. Span 属性设置](#5-span-属性设置)
    - [5.1 在创建时设置属性](#51-在创建时设置属性)
    - [5.2 动态设置属性](#52-动态设置属性)
    - [5.3 使用语义约定](#53-使用语义约定)
  - [6. 事件与链接](#6-事件与链接)
    - [6.1 添加事件](#61-添加事件)
    - [6.2 添加链接](#62-添加链接)
  - [7. 错误处理](#7-错误处理)
    - [7.1 记录错误](#71-记录错误)
    - [7.2 异常事件详情](#72-异常事件详情)
  - [8. 异步追踪](#8-异步追踪)
    - [8.1 在异步函数中使用 Tracer](#81-在异步函数中使用-tracer)
    - [8.2 跨 tokio::spawn 传递上下文](#82-跨-tokiospawn-传递上下文)
    - [8.3 使用 #\[instrument\] 宏（tracing 集成）](#83-使用-instrument-宏tracing-集成)
  - [9. 与 tracing 集成](#9-与-tracing-集成)
    - [9.1 集成 tracing-opentelemetry](#91-集成-tracing-opentelemetry)
    - [9.2 使用 tracing 宏](#92-使用-tracing-宏)
    - [9.3 在 tracing Span 中添加 OpenTelemetry 属性](#93-在-tracing-span-中添加-opentelemetry-属性)
  - [10. 完整示例](#10-完整示例)
    - [10.1 HTTP 服务器示例](#101-http-服务器示例)
    - [10.2 微服务调用示例](#102-微服务调用示例)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 Span 命名](#111-span-命名)
    - [11.2 Span 粒度](#112-span-粒度)
    - [11.3 错误处理](#113-错误处理)
    - [11.4 资源释放](#114-资源释放)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [推荐模式](#推荐模式)

---

## 1. 概述

### 1.1 什么是 Tracer

`Tracer` 是创建 Span 的工厂，负责：

- **创建 Span**：根 Span、子 Span
- **管理上下文**：当前活动 Span
- **应用配置**：Sampler、Resource、SpanProcessor
- **标识来源**：Instrumentation Library

### 1.2 Tracer 在架构中的位置

```text
TracerProvider
  └─> Tracer (name: "my-component", version: "1.0.0")
        ├─> start_span("operation-1") -> Span
        ├─> start_span("operation-2") -> Span
        └─> start_with_context(...) -> Span
```

---

## 2. Tracer 核心概念

### 2.1 Tracer 接口

```rust
use opentelemetry::trace::{Tracer, Span, SpanBuilder};

pub trait Tracer {
    type Span: Span + Send + Sync;
    
    /// 创建一个新的 SpanBuilder
    fn span_builder(&self, name: impl Into<Cow<'static, str>>) -> SpanBuilder;
    
    /// 启动一个新的 Span（不自动设置为当前）
    fn start(&self, name: impl Into<Cow<'static, str>>) -> Self::Span {
        self.span_builder(name).start(self)
    }
    
    /// 启动一个新的 Span 并设置为当前
    fn start_with_context(
        &self,
        name: impl Into<Cow<'static, str>>,
        parent_cx: &Context,
    ) -> Self::Span {
        self.span_builder(name).start_with_context(self, parent_cx)
    }
}
```

### 2.2 获取 Tracer

```rust
use opentelemetry::global;

// 从全局 TracerProvider 获取
let tracer = global::tracer("my-component");

// 从具体 TracerProvider 获取
let provider = create_tracer_provider();
let tracer = provider.tracer("my-component");

// 带版本
let tracer = provider.versioned_tracer(
    "my-component",
    Some("1.0.0"),
    None,
    None,
);
```

---

## 3. 创建 Span

### 3.1 基础 Span 创建

```rust
use opentelemetry::global;
use opentelemetry::trace::{Tracer, TraceContextExt};

fn basic_span_usage() {
    let tracer = global::tracer("my-component");
    
    // 创建简单 Span
    let span = tracer.start("my-operation");
    
    // 执行业务逻辑
    // ...
    
    // Span 自动在 drop 时结束
    drop(span);
}
```

### 3.2 使用 SpanBuilder

```rust
use opentelemetry::trace::{SpanBuilder, SpanKind, Status};
use opentelemetry::KeyValue;

fn advanced_span_creation() {
    let tracer = global::tracer("my-component");
    
    let span = tracer
        .span_builder("my-operation")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "/api/users"),
        ])
        .start(&tracer);
    
    // ... 业务逻辑 ...
    
    span.end();
}
```

### 3.3 创建子 Span

```rust
use opentelemetry::{Context, global};
use opentelemetry::trace::{Tracer, TraceContextExt};

fn parent_child_spans() {
    let tracer = global::tracer("my-component");
    
    // 创建父 Span
    let parent_span = tracer.start("parent-operation");
    let parent_cx = Context::current_with_span(parent_span);
    
    // 创建子 Span（使用父上下文）
    let child_span = tracer
        .start_with_context("child-operation", &parent_cx);
    
    // ... 业务逻辑 ...
    
    drop(child_span);
    drop(parent_cx);
}
```

### 3.4 创建根 Span（新 Trace）

```rust
fn create_root_span() {
    let tracer = global::tracer("my-component");
    
    // 使用空上下文创建根 Span
    let root_cx = Context::new();
    let span = tracer.start_with_context("root-operation", &root_cx);
    
    // ... 业务逻辑 ...
}
```

---

## 4. Span 上下文管理

### 4.1 获取当前 Span

```rust
use opentelemetry::{Context, trace::TraceContextExt};

fn get_current_span() {
    let cx = Context::current();
    let span = cx.span();
    
    println!("Current TraceId: {:?}", span.span_context().trace_id());
    println!("Current SpanId: {:?}", span.span_context().span_id());
}
```

### 4.2 设置当前 Span

```rust
use opentelemetry::Context;

fn set_current_span() {
    let tracer = global::tracer("my-component");
    let span = tracer.start("my-operation");
    
    // 将 Span 设置为当前
    let cx = Context::current_with_span(span);
    
    // 在闭包中使用该上下文
    cx.with_value(|cx| {
        // 此处 Span 是当前活动 Span
        perform_operation();
    });
}
```

### 4.3 嵌套 Span 上下文

```rust
fn nested_span_contexts() {
    let tracer = global::tracer("my-component");
    
    let outer_span = tracer.start("outer");
    let outer_cx = Context::current_with_span(outer_span);
    
    outer_cx.with_value(|cx| {
        // 外层 Span 是当前 Span
        
        let inner_span = tracer.start_with_context("inner", cx);
        let inner_cx = Context::current_with_span(inner_span);
        
        inner_cx.with_value(|_| {
            // 内层 Span 是当前 Span
            perform_operation();
        });
    });
}
```

---

## 5. Span 属性设置

### 5.1 在创建时设置属性

```rust
use opentelemetry::KeyValue;

fn set_attributes_on_creation() {
    let tracer = global::tracer("my-component");
    
    let span = tracer
        .span_builder("http-request")
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "/api/users"),
            KeyValue::new("http.status_code", 200),
        ])
        .start(&tracer);
}
```

### 5.2 动态设置属性

```rust
fn set_attributes_dynamically() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    // 业务逻辑执行中设置属性
    span.set_attribute(KeyValue::new("user.id", "12345"));
    span.set_attribute(KeyValue::new("result.count", 42));
}
```

### 5.3 使用语义约定

```rust
use opentelemetry_semantic_conventions as semconv;

fn use_semantic_conventions() {
    let tracer = global::tracer("my-component");
    
    let span = tracer
        .span_builder("http-request")
        .with_attributes(vec![
            KeyValue::new(semconv::trace::HTTP_METHOD, "GET"),
            KeyValue::new(semconv::trace::HTTP_URL, "https://api.example.com/users"),
            KeyValue::new(semconv::trace::HTTP_STATUS_CODE, 200),
        ])
        .start(&tracer);
}
```

---

## 6. 事件与链接

### 6.1 添加事件

```rust
use opentelemetry::trace::Event;
use std::time::SystemTime;

fn add_events() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    // 添加简单事件
    span.add_event("processing started", vec![]);
    
    // 添加带属性的事件
    span.add_event(
        "user logged in",
        vec![
            KeyValue::new("user.id", "12345"),
            KeyValue::new("login.method", "oauth"),
        ],
    );
    
    // 添加带时间戳的事件
    span.add_event_with_timestamp(
        "cache miss",
        SystemTime::now(),
        vec![KeyValue::new("cache.key", "user:12345")],
    );
}
```

### 6.2 添加链接

```rust
use opentelemetry::trace::{Link, SpanContext, TraceId, SpanId};

fn add_links() {
    let tracer = global::tracer("my-component");
    
    // 假设从其他系统接收到的 TraceId/SpanId
    let remote_trace_id = TraceId::from_hex("4bf92f3577b34da6a3ce929d0e0e4736").unwrap();
    let remote_span_id = SpanId::from_hex("00f067aa0ba902b7").unwrap();
    
    let remote_span_context = SpanContext::new(
        remote_trace_id,
        remote_span_id,
        Default::default(),
        true,
        Default::default(),
    );
    
    let span = tracer
        .span_builder("operation")
        .with_links(vec![
            Link::new(remote_span_context, vec![
                KeyValue::new("link.type", "follows-from"),
            ]),
        ])
        .start(&tracer);
}
```

---

## 7. 错误处理

### 7.1 记录错误

```rust
use opentelemetry::trace::Status;

fn record_error() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    match perform_operation() {
        Ok(result) => {
            span.set_status(Status::Ok);
        }
        Err(e) => {
            // 设置错误状态
            span.set_status(Status::error(e.to_string()));
            
            // 记录异常事件
            span.record_error(&e);
        }
    }
}

fn perform_operation() -> Result<(), Box<dyn std::error::Error>> {
    // 模拟业务逻辑
    Err("something went wrong".into())
}
```

### 7.2 异常事件详情

```rust
fn record_detailed_error() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    match perform_operation() {
        Err(e) => {
            span.add_event(
                "exception",
                vec![
                    KeyValue::new("exception.type", std::any::type_name_of_val(&e)),
                    KeyValue::new("exception.message", e.to_string()),
                    KeyValue::new("exception.stacktrace", format!("{:?}", e)),
                ],
            );
            span.set_status(Status::error("Operation failed"));
        }
        _ => {}
    }
}
```

---

## 8. 异步追踪

### 8.1 在异步函数中使用 Tracer

```rust
use opentelemetry::{Context, global};
use opentelemetry::trace::{Tracer, TraceContextExt};

async fn async_operation() {
    let tracer = global::tracer("my-component");
    
    let span = tracer.start("async-operation");
    let cx = Context::current_with_span(span);
    
    // 在异步任务中附加上下文
    cx.with_value(|_| async {
        // 异步操作
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        // 创建子 Span
        let child_span = tracer.start_with_context("child-async", &Context::current());
        // ...
    }).await;
}
```

### 8.2 跨 tokio::spawn 传递上下文

```rust
use opentelemetry::Context;

async fn spawn_with_context() {
    let tracer = global::tracer("my-component");
    let span = tracer.start("parent-operation");
    let cx = Context::current_with_span(span);
    
    // 捕获当前上下文
    let cx_clone = cx.clone();
    
    tokio::spawn(async move {
        // 在新任务中恢复上下文
        let _guard = cx_clone.attach();
        
        let tracer = global::tracer("my-component");
        let child_span = tracer.start_with_context("spawned-operation", &Context::current());
        
        // 异步业务逻辑
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    }).await.unwrap();
}
```

### 8.3 使用 #[instrument] 宏（tracing 集成）

```rust
use tracing::instrument;

#[instrument]
async fn instrumented_async_fn(user_id: u64) -> Result<String, Box<dyn std::error::Error>> {
    // 自动创建 Span，包含 user_id 属性
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(format!("User: {}", user_id))
}
```

---

## 9. 与 tracing 集成

### 9.1 集成 tracing-opentelemetry

```rust
use opentelemetry::global;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

fn setup_tracing_integration() {
    // 初始化 OpenTelemetry
    let provider = create_tracer_provider();
    global::set_tracer_provider(provider);
    
    // 获取 Tracer
    let tracer = global::tracer("my-service");
    
    // 创建 tracing-opentelemetry 层
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    // 初始化 tracing-subscriber
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
}
```

### 9.2 使用 tracing 宏

```rust
use tracing::{info, instrument, span, Level};

#[instrument]
fn traced_function(user_id: u64) {
    info!("Processing user {}", user_id);
    
    // 手动创建子 Span
    let span = span!(Level::INFO, "database_query");
    let _enter = span.enter();
    
    // 数据库操作
    query_database(user_id);
}

fn query_database(user_id: u64) {
    // ...
}
```

### 9.3 在 tracing Span 中添加 OpenTelemetry 属性

```rust
use tracing::{info_span, Span};
use tracing_opentelemetry::OpenTelemetrySpanExt;

fn add_otel_attributes() {
    let span = info_span!("operation");
    let _enter = span.enter();
    
    // 使用 OpenTelemetry 扩展添加属性
    Span::current().set_attribute("custom.attribute", "value");
}
```

---

## 10. 完整示例

### 10.1 HTTP 服务器示例

```rust
use axum::{Router, routing::get, Extension};
use opentelemetry::{global, KeyValue};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind, Status};
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化追踪
    let provider = create_tracer_provider().await?;
    global::set_tracer_provider(provider);
    
    let tracer = global::tracer("my-http-service");
    
    // 构建路由
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .layer(Extension(Arc::new(tracer)));
    
    // 启动服务器
    axum::Server::bind(&"0.0.0.0:3000".parse()?)
        .serve(app.into_make_service())
        .await?;
    
    Ok(())
}

async fn get_user(
    axum::extract::Path(user_id): axum::extract::Path<u64>,
    Extension(tracer): Extension<Arc<dyn Tracer + Send + Sync>>,
) -> String {
    let mut span = tracer
        .span_builder("GET /users/:id")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.route", "/users/:id"),
            KeyValue::new("user.id", user_id as i64),
        ])
        .start(&**tracer);
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    
    // 执行业务逻辑
    let result = cx.with_value(|_| async {
        fetch_user_from_db(user_id, &**tracer).await
    }).await;
    
    match result {
        Ok(user) => {
            span.set_attribute(KeyValue::new("http.status_code", 200));
            span.set_status(Status::Ok);
            user
        }
        Err(e) => {
            span.set_attribute(KeyValue::new("http.status_code", 500));
            span.set_status(Status::error(e.to_string()));
            format!("Error: {}", e)
        }
    }
}

async fn fetch_user_from_db(
    user_id: u64,
    tracer: &dyn Tracer,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut span = tracer
        .start_with_context("db.query", &opentelemetry::Context::current());
    
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"));
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Ok(format!("User {}", user_id))
}
```

### 10.2 微服务调用示例

```rust
use opentelemetry::global;
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::propagation::{Injector, TextMapPropagator};
use reqwest::header::HeaderMap;

async fn call_downstream_service(user_id: u64) -> Result<String, Box<dyn std::error::Error>> {
    let tracer = global::tracer("my-service");
    
    // 创建客户端 Span
    let mut span = tracer
        .span_builder("HTTP GET /downstream/api")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "http://downstream-service/api"),
        ])
        .start(&tracer);
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    
    // 注入追踪上下文到 HTTP Headers
    let mut headers = HeaderMap::new();
    let propagator = opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));
    });
    
    // 发起 HTTP 请求
    let client = reqwest::Client::new();
    let response = client
        .get("http://downstream-service/api")
        .headers(headers)
        .send()
        .await?;
    
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    
    let body = response.text().await?;
    Ok(body)
}

struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}
```

---

## 11. 最佳实践

### 11.1 Span 命名

✅ **使用描述性名称**

```rust
// ✅ 好的命名
let span = tracer.start("HTTP GET /api/users");
let span = tracer.start("database.query.users.select");

// ❌ 避免的命名
let span = tracer.start("operation");
let span = tracer.start("fn1");
```

✅ **使用操作类型 + 资源**

```rust
// HTTP: 方法 + 路由
let span = tracer.start("POST /api/users");

// 数据库: 操作 + 表
let span = tracer.start("SELECT users");

// RPC: 服务 + 方法
let span = tracer.start("UserService.GetUser");
```

### 11.2 Span 粒度

✅ **适当的粒度**

```rust
// ✅ 推荐：每个重要操作一个 Span
fn process_order(order_id: u64) {
    let tracer = global::tracer("order-service");
    
    let parent_span = tracer.start("process_order");
    let cx = Context::current_with_span(parent_span);
    
    // 子操作
    cx.with_value(|_| {
        let span1 = tracer.start_with_context("validate_order", &Context::current());
        // ...
        
        let span2 = tracer.start_with_context("charge_payment", &Context::current());
        // ...
        
        let span3 = tracer.start_with_context("update_inventory", &Context::current());
        // ...
    });
}

// ❌ 避免：过度细粒度
fn over_instrumented() {
    let span1 = tracer.start("add_numbers");
    let result = 1 + 2;  // 太细粒度
    drop(span1);
}
```

### 11.3 错误处理

✅ **始终记录错误**

```rust
match perform_operation() {
    Ok(_) => {
        span.set_status(Status::Ok);
    }
    Err(e) => {
        span.record_error(&e);
        span.set_status(Status::error(e.to_string()));
    }
}
```

### 11.4 资源释放

✅ **确保 Span 正确结束**

```rust
// ✅ 使用 drop 显式结束
let span = tracer.start("operation");
// ... 业务逻辑 ...
drop(span);

// ✅ 或使用作用域
{
    let span = tracer.start("operation");
    // ... 业务逻辑 ...
}  // Span 在此自动结束
```

---

## 总结

### 核心要点

1. **Tracer 是 Span 的工厂**：从 TracerProvider 获取 Tracer
2. **使用 SpanBuilder 配置 Span**：设置 kind、attributes、links
3. **正确管理上下文**：parent-child 关系通过 Context 传递
4. **记录错误**：使用 `record_error()` 和 `set_status()`
5. **异步环境注意上下文传递**：使用 `Context::attach()`
6. **集成 tracing 简化使用**：使用 `#[instrument]` 宏

### 推荐模式

```rust
// HTTP 请求处理模板
async fn handle_request(tracer: &dyn Tracer) -> Result<Response, Error> {
    let mut span = tracer
        .span_builder("operation_name")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            // 设置初始属性
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span.clone());
    
    let result = cx.with_value(|_| async {
        // 业务逻辑
    }).await;
    
    match result {
        Ok(response) => {
            span.set_status(Status::Ok);
            Ok(response)
        }
        Err(e) => {
            span.record_error(&e);
            span.set_status(Status::error(e.to_string()));
            Err(e)
        }
    }
}
```

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
