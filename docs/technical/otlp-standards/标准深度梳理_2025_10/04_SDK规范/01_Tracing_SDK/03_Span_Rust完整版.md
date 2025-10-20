# Span - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [Span - Rust 完整实现指南](#span---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 Span](#11-什么是-span)
    - [1.2 Span 结构](#12-span-结构)
  - [2. Span 生命周期](#2-span-生命周期)
    - [2.1 创建 Span](#21-创建-span)
    - [2.2 手动结束 Span](#22-手动结束-span)
    - [2.3 Span 作用域管理](#23-span-作用域管理)
  - [3. Span 属性](#3-span-属性)
    - [3.1 设置属性](#31-设置属性)
    - [3.2 属性类型](#32-属性类型)
    - [3.3 属性命名约定](#33-属性命名约定)
    - [3.4 属性限制](#34-属性限制)
  - [4. Span 事件](#4-span-事件)
    - [4.1 添加事件](#41-添加事件)
    - [4.2 记录异常](#42-记录异常)
    - [4.3 事件与日志的区别](#43-事件与日志的区别)
  - [5. Span 链接](#5-span-链接)
    - [5.1 创建链接](#51-创建链接)
    - [5.2 链接的使用场景](#52-链接的使用场景)
  - [6. Span 状态](#6-span-状态)
    - [6.1 状态类型](#61-状态类型)
    - [6.2 状态设置规则](#62-状态设置规则)
    - [6.3 HTTP 状态码映射](#63-http-状态码映射)
  - [7. SpanContext](#7-spancontext)
    - [7.1 获取 SpanContext](#71-获取-spancontext)
    - [7.2 SpanContext 字段](#72-spancontext-字段)
    - [7.3 提取和注入 SpanContext](#73-提取和注入-spancontext)
  - [8. Span 类型 (SpanKind)](#8-span-类型-spankind)
    - [8.1 SpanKind 枚举](#81-spankind-枚举)
    - [8.2 使用场景](#82-使用场景)
    - [8.3 SpanKind 与父子关系](#83-spankind-与父子关系)
  - [9. 完整示例](#9-完整示例)
    - [9.1 完整的 HTTP 请求处理](#91-完整的-http-请求处理)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 Span 生命周期](#101-span-生命周期)
    - [10.2 属性设置时机](#102-属性设置时机)
    - [10.3 事件 vs 属性](#103-事件-vs-属性)
    - [10.4 错误处理](#104-错误处理)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [生命周期checklist](#生命周期checklist)

---

## 1. 概述

### 1.1 什么是 Span

Span 代表分布式追踪中的一个操作单元，包含：

- **名称**：操作的描述
- **时间范围**：开始和结束时间
- **属性**：键值对元数据
- **事件**：时间戳标记的日志点
- **链接**：与其他 Span 的关系
- **状态**：操作的最终状态
- **上下文**：TraceId, SpanId, TraceFlags

### 1.2 Span 结构

```rust
pub struct Span {
    span_context: SpanContext,
    name: Cow<'static, str>,
    start_time: SystemTime,
    end_time: Option<SystemTime>,
    attributes: Vec<KeyValue>,
    events: Vec<Event>,
    links: Vec<Link>,
    status: Status,
    span_kind: SpanKind,
}
```

---

## 2. Span 生命周期

### 2.1 创建 Span

```rust
use opentelemetry::global;
use opentelemetry::trace::Tracer;

fn create_span() {
    let tracer = global::tracer("my-component");
    
    // 开始时间自动记录
    let span = tracer.start("my-operation");
    
    // 执行业务逻辑
    perform_operation();
    
    // 结束时间在 drop 时自动记录
    drop(span);
}
```

### 2.2 手动结束 Span

```rust
fn manual_end_span() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("my-operation");
    
    // 业务逻辑
    perform_operation();
    
    // 显式结束 Span
    span.end();
    
    // 或者指定结束时间
    span.end_with_timestamp(std::time::SystemTime::now());
}
```

### 2.3 Span 作用域管理

```rust
fn span_scope() {
    let tracer = global::tracer("my-component");
    
    {
        let _span = tracer.start("operation");
        // Span 在作用域内有效
        perform_operation();
    }  // Span 自动结束
    
    // Span 已结束
}
```

---

## 3. Span 属性

### 3.1 设置属性

```rust
use opentelemetry::KeyValue;

fn set_attributes() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    // 单个属性
    span.set_attribute(KeyValue::new("user.id", "12345"));
    span.set_attribute(KeyValue::new("request.size", 1024));
    span.set_attribute(KeyValue::new("cache.hit", true));
    
    // 批量设置
    span.set_attributes(vec![
        KeyValue::new("http.method", "GET"),
        KeyValue::new("http.url", "/api/users"),
    ]);
}
```

### 3.2 属性类型

```rust
use opentelemetry::Value;

fn attribute_types() {
    let mut span = tracer.start("operation");
    
    // 字符串
    span.set_attribute(KeyValue::new("string_attr", "value"));
    
    // 整数
    span.set_attribute(KeyValue::new("int_attr", 42i64));
    
    // 浮点数
    span.set_attribute(KeyValue::new("float_attr", 3.14));
    
    // 布尔值
    span.set_attribute(KeyValue::new("bool_attr", true));
    
    // 数组
    span.set_attribute(KeyValue::new("array_attr", vec!["a", "b", "c"]));
}
```

### 3.3 属性命名约定

```rust
use opentelemetry_semantic_conventions as semconv;

fn semantic_attributes() {
    let mut span = tracer.start("http-request");
    
    // 使用语义约定常量
    span.set_attribute(KeyValue::new(semconv::trace::HTTP_METHOD, "GET"));
    span.set_attribute(KeyValue::new(semconv::trace::HTTP_URL, "https://api.example.com"));
    span.set_attribute(KeyValue::new(semconv::trace::HTTP_STATUS_CODE, 200));
    
    // 自定义属性使用命名空间
    span.set_attribute(KeyValue::new("myapp.user.id", "12345"));
    span.set_attribute(KeyValue::new("myapp.feature.name", "checkout"));
}
```

### 3.4 属性限制

```rust
// 配置属性限制
let config = Config::default()
    .with_max_attributes_per_span(128)  // 最多 128 个属性
    .with_max_attribute_value_length(512);  // 属性值最多 512 字符
```

---

## 4. Span 事件

### 4.1 添加事件

```rust
fn add_events() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    // 简单事件
    span.add_event("processing started", vec![]);
    
    // 带属性的事件
    span.add_event(
        "cache lookup",
        vec![
            KeyValue::new("cache.key", "user:12345"),
            KeyValue::new("cache.hit", false),
        ],
    );
    
    // 带时间戳的事件
    span.add_event_with_timestamp(
        "retry attempt",
        std::time::SystemTime::now(),
        vec![KeyValue::new("retry.attempt", 2)],
    );
}
```

### 4.2 记录异常

```rust
use opentelemetry::trace::Status;

fn record_exception() {
    let tracer = global::tracer("my-component");
    let mut span = tracer.start("operation");
    
    match perform_operation() {
        Ok(_) => {
            span.set_status(Status::Ok);
        }
        Err(e) => {
            // 自动添加 exception 事件
            span.record_error(&e);
            span.set_status(Status::error(e.to_string()));
        }
    }
}

fn perform_operation() -> Result<(), Box<dyn std::error::Error>> {
    Err("operation failed".into())
}
```

### 4.3 事件与日志的区别

```text
事件 (Events):
- 附加到 Span
- 有结构化属性
- 包含时间戳
- 用于记录 Span 内的重要时间点

日志 (Logs):
- 独立的遥测信号
- 可以不关联 Span
- 适合长文本消息
- 用于应用程序的输出
```

---

## 5. Span 链接

### 5.1 创建链接

```rust
use opentelemetry::trace::{Link, SpanContext, TraceId, SpanId};

fn create_links() {
    let tracer = global::tracer("my-component");
    
    // 创建远程 SpanContext
    let remote_trace_id = TraceId::from_hex("4bf92f3577b34da6a3ce929d0e0e4736").unwrap();
    let remote_span_id = SpanId::from_hex("00f067aa0ba902b7").unwrap();
    
    let remote_context = SpanContext::new(
        remote_trace_id,
        remote_span_id,
        Default::default(),
        true,  // is_sampled
        Default::default(),
    );
    
    // 创建带链接的 Span
    let span = tracer
        .span_builder("operation")
        .with_links(vec![
            Link::new(remote_context, vec![
                KeyValue::new("link.type", "follows-from"),
            ]),
        ])
        .start(&tracer);
}
```

### 5.2 链接的使用场景

```rust
// 场景 1: 批处理 - 链接到多个输入 Trace
fn batch_processing() {
    let tracer = global::tracer("batch-processor");
    
    let input_traces = vec![
        get_trace_context_from_message(1),
        get_trace_context_from_message(2),
        get_trace_context_from_message(3),
    ];
    
    let links: Vec<Link> = input_traces
        .into_iter()
        .map(|ctx| Link::new(ctx, vec![]))
        .collect();
    
    let span = tracer
        .span_builder("process_batch")
        .with_links(links)
        .start(&tracer);
}

// 场景 2: 异步消息处理
fn async_message_processing() {
    let tracer = global::tracer("message-processor");
    
    // 从消息头提取原始 Trace 上下文
    let original_context = extract_context_from_message_headers();
    
    // 创建新 Trace，但链接到原始 Trace
    let span = tracer
        .span_builder("process_message")
        .with_links(vec![
            Link::new(original_context, vec![
                KeyValue::new("message.queue", "orders"),
            ]),
        ])
        .start(&tracer);
}
```

---

## 6. Span 状态

### 6.1 状态类型

```rust
use opentelemetry::trace::Status;

fn span_status() {
    let mut span = tracer.start("operation");
    
    // 未设置（默认）
    span.set_status(Status::Unset);
    
    // 成功
    span.set_status(Status::Ok);
    
    // 错误（带描述）
    span.set_status(Status::error("Operation failed: timeout"));
}
```

### 6.2 状态设置规则

```rust
fn status_rules() {
    let mut span = tracer.start("operation");
    
    // ✅ 成功情况：设置 Ok
    if operation_succeeded() {
        span.set_status(Status::Ok);
    }
    
    // ✅ 错误情况：设置 error
    if let Err(e) = operation() {
        span.set_status(Status::error(e.to_string()));
        span.record_error(&e);
    }
    
    // ❌ 不要为正常情况设置 Unset
    // Unset 是默认值，应保持不变直到确定最终状态
}
```

### 6.3 HTTP 状态码映射

```rust
fn http_status_mapping(status_code: u16) {
    let mut span = tracer.start("http-request");
    
    span.set_attribute(KeyValue::new("http.status_code", status_code as i64));
    
    match status_code {
        200..=399 => {
            // 2xx, 3xx: 成功
            span.set_status(Status::Ok);
        }
        400..=499 => {
            // 4xx: 客户端错误（不设置 error 状态）
            span.set_status(Status::Unset);
        }
        500..=599 => {
            // 5xx: 服务器错误
            span.set_status(Status::error(format!("HTTP {}", status_code)));
        }
        _ => {
            span.set_status(Status::Unset);
        }
    }
}
```

---

## 7. SpanContext

### 7.1 获取 SpanContext

```rust
use opentelemetry::trace::{TraceContextExt, SpanContext};

fn get_span_context() {
    let tracer = global::tracer("my-component");
    let span = tracer.start("operation");
    
    let span_context: &SpanContext = span.span_context();
    
    println!("TraceId: {:?}", span_context.trace_id());
    println!("SpanId: {:?}", span_context.span_id());
    println!("Is Sampled: {}", span_context.is_sampled());
    println!("Is Remote: {}", span_context.is_remote());
}
```

### 7.2 SpanContext 字段

```rust
pub struct SpanContext {
    trace_id: TraceId,        // 128-bit Trace ID
    span_id: SpanId,          // 64-bit Span ID
    trace_flags: TraceFlags,  // 8-bit flags (采样等)
    is_remote: bool,          // 是否来自远程系统
    trace_state: TraceState,  // W3C Trace State
}
```

### 7.3 提取和注入 SpanContext

```rust
use opentelemetry::propagation::{Injector, Extractor, TextMapPropagator};
use std::collections::HashMap;

// 注入到 HTTP Headers
fn inject_context(span: &Span) {
    let mut headers = HashMap::new();
    let cx = opentelemetry::Context::current_with_span(span.clone());
    
    opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut HashMapInjector(&mut headers));
    });
    
    // headers 现在包含 traceparent, tracestate 等
}

// 从 HTTP Headers 提取
fn extract_context(headers: &HashMap<String, String>) -> opentelemetry::Context {
    opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.extract(&HashMapExtractor(headers))
    })
}

struct HashMapInjector<'a>(&'a mut HashMap<String, String>);
impl<'a> Injector for HashMapInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(key.to_string(), value);
    }
}

struct HashMapExtractor<'a>(&'a HashMap<String, String>);
impl<'a> Extractor for HashMapExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|v| v.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

---

## 8. Span 类型 (SpanKind)

### 8.1 SpanKind 枚举

```rust
pub enum SpanKind {
    Internal,  // 内部操作（默认）
    Server,    // 服务器端请求处理
    Client,    // 客户端请求发起
    Producer,  // 消息生产者
    Consumer,  // 消息消费者
}
```

### 8.2 使用场景

```rust
use opentelemetry::trace::SpanKind;

// Internal: 内部函数调用
fn internal_operation() {
    let span = tracer
        .span_builder("calculate")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
}

// Server: HTTP 服务器端
async fn handle_http_request() {
    let span = tracer
        .span_builder("GET /api/users")
        .with_kind(SpanKind::Server)
        .start(&tracer);
}

// Client: HTTP 客户端
async fn call_external_api() {
    let span = tracer
        .span_builder("GET https://api.example.com")
        .with_kind(SpanKind::Client)
        .start(&tracer);
}

// Producer: 发送消息到队列
async fn send_message() {
    let span = tracer
        .span_builder("send kafka.orders")
        .with_kind(SpanKind::Producer)
        .start(&tracer);
}

// Consumer: 从队列接收消息
async fn receive_message() {
    let span = tracer
        .span_builder("receive kafka.orders")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
}
```

### 8.3 SpanKind 与父子关系

```text
┌───────────────┐
│ Client Span   │ (SpanKind::Client)
└───────┬───────┘
        │ HTTP Request
        ▼
┌───────────────┐
│ Server Span   │ (SpanKind::Server)
└───────┬───────┘
        │
        ▼
┌───────────────┐
│ Internal Span │ (SpanKind::Internal)
└───────────────┘
```

---

## 9. 完整示例

### 9.1 完整的 HTTP 请求处理

```rust
use opentelemetry::global;
use opentelemetry::trace::{Tracer, SpanKind, Status, TraceContextExt};
use opentelemetry::{KeyValue, Context};
use opentelemetry_semantic_conventions as semconv;

async fn handle_user_request(user_id: u64) -> Result<String, Box<dyn std::error::Error>> {
    let tracer = global::tracer("user-service");
    
    // 创建 Server Span
    let mut span = tracer
        .span_builder("GET /users/:id")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new(semconv::trace::HTTP_METHOD, "GET"),
            KeyValue::new(semconv::trace::HTTP_ROUTE, "/users/:id"),
            KeyValue::new("user.id", user_id as i64),
        ])
        .start(&tracer);
    
    let cx = Context::current_with_span(span.clone());
    
    // 执行业务逻辑
    let result = cx.with_value(|_| async {
        // 事件：开始处理
        span.add_event("request processing started", vec![]);
        
        // 数据库查询
        let user = match fetch_from_database(user_id, &tracer).await {
            Ok(user) => {
                span.add_event(
                    "user fetched from database",
                    vec![KeyValue::new("user.name", user.clone())],
                );
                user
            }
            Err(e) => {
                span.add_event(
                    "database error",
                    vec![KeyValue::new("error.message", e.to_string())],
                );
                return Err(e);
            }
        };
        
        // 缓存更新
        if let Err(e) = update_cache(user_id, &user, &tracer).await {
            span.add_event(
                "cache update failed",
                vec![KeyValue::new("error.message", e.to_string())],
            );
            // 缓存失败不影响主流程
        }
        
        Ok(user)
    }).await;
    
    // 设置最终状态和属性
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new(semconv::trace::HTTP_STATUS_CODE, 200));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.set_attribute(KeyValue::new(semconv::trace::HTTP_STATUS_CODE, 500));
            span.record_error(e.as_ref());
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    result
}

async fn fetch_from_database(
    user_id: u64,
    tracer: &dyn Tracer,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut span = tracer
        .start_with_context("db.query", &Context::current());
    
    span.set_attributes(vec![
        KeyValue::new(semconv::trace::DB_SYSTEM, "postgresql"),
        KeyValue::new(semconv::trace::DB_STATEMENT, "SELECT * FROM users WHERE id = $1"),
        KeyValue::new("db.user_id", user_id as i64),
    ]);
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Ok(format!("User-{}", user_id))
}

async fn update_cache(
    user_id: u64,
    user_data: &str,
    tracer: &dyn Tracer,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut span = tracer
        .start_with_context("cache.set", &Context::current());
    
    span.set_attributes(vec![
        KeyValue::new("cache.system", "redis"),
        KeyValue::new("cache.key", format!("user:{}", user_id)),
    ]);
    
    // 模拟缓存更新
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    Ok(())
}
```

---

## 10. 最佳实践

### 10.1 Span 生命周期

✅ **确保 Span 被正确结束**

```rust
// ✅ 推荐：使用作用域或显式 drop
{
    let span = tracer.start("operation");
    perform_work();
}  // 自动结束

// ✅ 推荐：显式调用 end()
let mut span = tracer.start("operation");
perform_work();
span.end();

// ❌ 避免：忘记结束 Span
let span = tracer.start("operation");
std::mem::forget(span);  // Span 永远不会结束！
```

### 10.2 属性设置时机

✅ **在创建时设置已知属性，动态属性后续设置**

```rust
// ✅ 推荐
let mut span = tracer
    .span_builder("operation")
    .with_attributes(vec![
        KeyValue::new("static.attr", "value"),  // 创建时已知
    ])
    .start(&tracer);

// 运行时动态设置
let result_count = perform_query();
span.set_attribute(KeyValue::new("result.count", result_count));
```

### 10.3 事件 vs 属性

```rust
// ✅ 属性：描述 Span 的静态特征
span.set_attribute(KeyValue::new("http.method", "GET"));

// ✅ 事件：记录 Span 内的时间点
span.add_event("cache miss", vec![]);
span.add_event("retry attempt", vec![KeyValue::new("attempt", 2)]);
```

### 10.4 错误处理

✅ **总是记录错误详情**

```rust
match operation() {
    Err(e) => {
        // 1. 记录异常事件
        span.record_error(&e);
        
        // 2. 设置错误状态
        span.set_status(Status::error(e.to_string()));
        
        // 3. 添加额外上下文
        span.set_attribute(KeyValue::new("error.type", "DatabaseError"));
    }
    Ok(_) => {
        span.set_status(Status::Ok);
    }
}
```

---

## 总结

### 核心要点

1. **Span 代表一个操作单元**：有明确的开始和结束时间
2. **属性描述 Span 特征**：静态元数据，数量有限
3. **事件记录时间点**：Span 内部的重要时刻
4. **链接连接多个 Trace**：用于批处理、异步消息等场景
5. **状态标识最终结果**：Ok/Error/Unset
6. **SpanKind 描述操作类型**：Server/Client/Producer/Consumer/Internal

### 生命周期checklist

- [ ] Span 是否正确开始？
- [ ] 是否设置了合适的 SpanKind？
- [ ] 是否设置了必要的属性？
- [ ] 是否记录了重要的事件？
- [ ] 错误是否被正确记录？
- [ ] 是否设置了最终状态？
- [ ] Span 是否被正确结束？

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
