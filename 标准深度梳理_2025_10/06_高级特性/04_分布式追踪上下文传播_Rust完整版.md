# 分布式追踪上下文传播 - Rust 完整版

## 目录

- [分布式追踪上下文传播 - Rust 完整版](#分布式追踪上下文传播---rust-完整版)
  - [目录](#目录)
  - [1. 上下文传播概述](#1-上下文传播概述)
    - [1.1 为什么需要上下文传播](#11-为什么需要上下文传播)
    - [1.2 传播机制](#12-传播机制)
  - [2. W3C Trace Context 标准](#2-w3c-trace-context-标准)
    - [2.1 traceparent Header 格式](#21-traceparent-header-格式)
    - [2.2 Rust 实现](#22-rust-实现)
    - [2.3 tracestate Header 格式](#23-tracestate-header-格式)
  - [3. 跨服务传播](#3-跨服务传播)
    - [3.1 HTTP 客户端注入](#31-http-客户端注入)
    - [3.2 HTTP 服务器提取](#32-http-服务器提取)
  - [4. 跨异步边界传播](#4-跨异步边界传播)
    - [4.1 Task-Local Context](#41-task-local-context)
    - [4.2 显式传播](#42-显式传播)
  - [5. 跨消息队列传播](#5-跨消息队列传播)
    - [5.1 Kafka Producer 注入](#51-kafka-producer-注入)
    - [5.2 Kafka Consumer 提取](#52-kafka-consumer-提取)
  - [6. Baggage 传播](#6-baggage-传播)
    - [6.1 Baggage 使用](#61-baggage-使用)
    - [6.2 Baggage 传播器](#62-baggage-传播器)
  - [7. 自定义传播器](#7-自定义传播器)
    - [7.1 组合传播器](#71-组合传播器)
  - [8. 完整示例](#8-完整示例)
    - [8.1 微服务链路追踪](#81-微服务链路追踪)
  - [总结](#总结)

---

## 1. 上下文传播概述

**上下文传播（Context Propagation）** 是分布式追踪的核心机制，确保 Trace 在服务间保持连续性。

### 1.1 为什么需要上下文传播

```text
服务 A                服务 B                服务 C
  │                     │                     │
  ├─ Span A1            │                     │
  │   TraceID: 123      │                     │
  │   SpanID: A1        │                     │
  │                     │                     │
  │─────HTTP────────────>│                     │
  │   Header:           │                     │
  │   traceparent: 123-A1│                    │
  │                     │                     │
  │                     ├─ Span B1            │
  │                     │   TraceID: 123      │
  │                     │   SpanID: B1        │
  │                     │   ParentID: A1      │
  │                     │                     │
  │                     │───────HTTP──────────>│
  │                     │   Header:           │
  │                     │   traceparent: 123-B1│
  │                     │                     │
  │                     │                     ├─ Span C1
  │                     │                     │   TraceID: 123
  │                     │                     │   SpanID: C1
  │                     │                     │   ParentID: B1

关键：TraceID=123 贯穿整个调用链
```

### 1.2 传播机制

```rust
use opentelemetry::{
    propagation::{TextMapPropagator, Injector, Extractor},
    Context,
};

pub trait ContextPropagator {
    /// 注入上下文到载体（HTTP Header、Message Metadata）
    fn inject(&self, context: &Context, carrier: &mut dyn Injector);
    
    /// 从载体提取上下文
    fn extract(&self, carrier: &dyn Extractor) -> Context;
}
```

---

## 2. W3C Trace Context 标准

### 2.1 traceparent Header 格式

```text
traceparent: {version}-{trace-id}-{parent-id}-{trace-flags}

示例:
traceparent: 00-0af7651916cd43dd8448eb211c80319c-00f067aa0ba902b7-01

解析:
- version:     00 (固定)
- trace-id:    0af7651916cd43dd8448eb211c80319c (32 hex 字符)
- parent-id:   00f067aa0ba902b7 (16 hex 字符)
- trace-flags: 01 (8 bit, 01=sampled)
```

### 2.2 Rust 实现

```rust
use opentelemetry::trace::{TraceId, SpanId, TraceFlags, TraceState};

pub struct TraceParent {
    pub version: u8,
    pub trace_id: TraceId,
    pub parent_id: SpanId,
    pub trace_flags: TraceFlags,
}

impl TraceParent {
    pub fn parse(value: &str) -> Result<Self, String> {
        let parts: Vec<&str> = value.split('-').collect();
        
        if parts.len() != 4 {
            return Err("Invalid traceparent format".to_string());
        }
        
        let version = u8::from_str_radix(parts[0], 16)
            .map_err(|e| format!("Invalid version: {}", e))?;
        
        if version != 0 {
            return Err("Unsupported version".to_string());
        }
        
        let trace_id_bytes = hex::decode(parts[1])
            .map_err(|e| format!("Invalid trace-id: {}", e))?;
        let trace_id = TraceId::from_bytes(
            trace_id_bytes.try_into().map_err(|_| "Invalid trace-id length")?
        );
        
        let parent_id_bytes = hex::decode(parts[2])
            .map_err(|e| format!("Invalid parent-id: {}", e))?;
        let parent_id = SpanId::from_bytes(
            parent_id_bytes.try_into().map_err(|_| "Invalid parent-id length")?
        );
        
        let flags = u8::from_str_radix(parts[3], 16)
            .map_err(|e| format!("Invalid trace-flags: {}", e))?;
        let trace_flags = TraceFlags::new(flags);
        
        Ok(Self {
            version,
            trace_id,
            parent_id,
            trace_flags,
        })
    }
    
    pub fn to_string(&self) -> String {
        format!(
            "{:02x}-{}-{}-{:02x}",
            self.version,
            hex::encode(self.trace_id.to_bytes()),
            hex::encode(self.parent_id.to_bytes()),
            self.trace_flags.to_u8(),
        )
    }
}
```

### 2.3 tracestate Header 格式

```text
tracestate: key1=value1,key2=value2

示例:
tracestate: rojo=00f067aa0ba902b7,congo=t61rcWkgMzE

规则:
- 多个 key=value 对，逗号分隔
- 最多 32 个条目
- 每个条目最多 128 字符
- key 必须是小写字母、数字、下划线、连字符、@
```

```rust
use std::collections::HashMap;

pub struct TraceState {
    entries: HashMap<String, String>,
}

impl TraceState {
    pub fn parse(value: &str) -> Result<Self, String> {
        let mut entries = HashMap::new();
        
        for pair in value.split(',') {
            let parts: Vec<&str> = pair.split('=').collect();
            if parts.len() != 2 {
                continue;
            }
            
            let key = parts[0].trim();
            let value = parts[1].trim();
            
            if Self::is_valid_key(key) && value.len() <= 256 {
                entries.insert(key.to_string(), value.to_string());
            }
        }
        
        Ok(Self { entries })
    }
    
    pub fn to_string(&self) -> String {
        self.entries
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join(",")
    }
    
    fn is_valid_key(key: &str) -> bool {
        key.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_' || c == '-' || c == '@')
    }
}
```

---

## 3. 跨服务传播

### 3.1 HTTP 客户端注入

```rust
use reqwest::Client;
use opentelemetry::{global, Context as OtelContext};
use opentelemetry::propagation::TextMapPropagator;
use std::collections::HashMap;

pub async fn http_call_with_trace(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    // 1. 获取当前上下文
    let cx = OtelContext::current();
    
    // 2. 准备 HTTP Headers
    let mut headers = HashMap::new();
    
    // 3. 注入上下文到 Headers
    let propagator = global::get_text_map_propagator(|p| p.clone());
    propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));
    
    // 4. 发送 HTTP 请求
    let client = Client::new();
    let mut request = client.get(url);
    
    for (key, value) in headers {
        request = request.header(key, value);
    }
    
    let response = request.send().await?;
    let body = response.text().await?;
    
    Ok(body)
}

// Header Injector
struct HeaderInjector<'a>(&'a mut HashMap<String, String>);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(key.to_string(), value);
    }
}
```

### 3.2 HTTP 服务器提取

```rust
use axum::{
    extract::Request,
    http::HeaderMap,
    middleware::{self, Next},
    response::Response,
};
use opentelemetry::{global, trace::TraceContextExt};

pub async fn trace_middleware(
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Response {
    // 1. 从 Headers 提取上下文
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let parent_cx = propagator.extract(&HeaderExtractor(&headers));
    
    // 2. 创建新 Span
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(opentelemetry::trace::SpanKind::Server)
        .start_with_context(&tracer, &parent_cx);
    
    // 3. 将上下文注入 Request
    let cx = parent_cx.with_span(span);
    request.extensions_mut().insert(cx.clone());
    
    // 4. 处理请求
    let response = next.run(request).await;
    
    // 5. 结束 Span
    cx.span().end();
    
    response
}

// Header Extractor
struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

---

## 4. 跨异步边界传播

### 4.1 Task-Local Context

```rust
use opentelemetry::Context;

#[tokio::main]
async fn main() {
    // 创建 Span
    let tracer = global::tracer("async-app");
    let span = tracer.start("parent-operation");
    let cx = Context::current_with_span(span);
    
    // 跨 tokio::spawn 传播上下文
    let _guard = cx.attach();
    
    tokio::spawn(async {
        // 这里自动继承父上下文
        let cx = Context::current();
        let span = cx.span();
        span.set_attribute(KeyValue::new("child", "true"));
        
        child_operation().await;
    }).await.unwrap();
}

async fn child_operation() {
    let cx = Context::current();
    let tracer = global::tracer("async-app");
    let span = tracer.start_with_context("child-operation", &cx);
    
    // 执行操作
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    span.end();
}
```

### 4.2 显式传播

```rust
use opentelemetry::Context;

pub async fn explicit_propagation() {
    let tracer = global::tracer("app");
    let span = tracer.start("parent");
    let cx = Context::current_with_span(span);
    
    // 显式传递上下文
    let result = process_with_context(cx.clone()).await;
    
    cx.span().end();
}

async fn process_with_context(cx: Context) -> String {
    let tracer = global::tracer("app");
    let span = tracer.start_with_context("child", &cx);
    let new_cx = cx.with_span(span);
    
    // 使用新上下文
    let _guard = new_cx.attach();
    
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    new_cx.span().end();
    "result".to_string()
}
```

---

## 5. 跨消息队列传播

### 5.1 Kafka Producer 注入

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;
use opentelemetry::{global, Context};
use std::collections::HashMap;

pub async fn send_message_with_trace(
    topic: &str,
    key: &str,
    value: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // 1. 获取当前上下文
    let cx = Context::current();
    
    // 2. 注入到 Kafka Headers
    let mut headers_map = HashMap::new();
    let propagator = global::get_text_map_propagator(|p| p.clone());
    propagator.inject_context(&cx, &mut HeaderInjector(&mut headers_map));
    
    // 3. 转换为 Kafka Headers
    let mut kafka_headers = rdkafka::message::OwnedHeaders::new();
    for (key, value) in headers_map {
        kafka_headers = kafka_headers.insert(rdkafka::message::Header {
            key: &key,
            value: Some(value.as_bytes()),
        });
    }
    
    // 4. 发送消息
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()?;
    
    let record = FutureRecord::to(topic)
        .key(key)
        .payload(value)
        .headers(kafka_headers);
    
    producer.send(record, Duration::from_secs(0)).await
        .map_err(|(e, _)| e)?;
    
    Ok(())
}
```

### 5.2 Kafka Consumer 提取

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;

pub async fn consume_message_with_trace() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("group.id", "my-group")
        .set("bootstrap.servers", "localhost:9092")
        .create()?;
    
    consumer.subscribe(&["my-topic"])?;
    
    loop {
        match consumer.recv().await {
            Ok(msg) => {
                // 1. 提取上下文
                let mut headers_map = HashMap::new();
                if let Some(headers) = msg.headers() {
                    for header in headers.iter() {
                        if let Some(value) = header.value {
                            headers_map.insert(
                                header.key.to_string(),
                                String::from_utf8_lossy(value).to_string(),
                            );
                        }
                    }
                }
                
                let propagator = global::get_text_map_propagator(|p| p.clone());
                let parent_cx = propagator.extract(&MapExtractor(&headers_map));
                
                // 2. 创建新 Span
                let tracer = global::tracer("kafka-consumer");
                let span = tracer
                    .span_builder("process-message")
                    .with_kind(opentelemetry::trace::SpanKind::Consumer)
                    .start_with_context(&tracer, &parent_cx);
                
                let cx = parent_cx.with_span(span);
                let _guard = cx.attach();
                
                // 3. 处理消息
                if let Some(payload) = msg.payload() {
                    process_message(payload).await?;
                }
                
                cx.span().end();
            }
            Err(e) => {
                eprintln!("Kafka error: {}", e);
            }
        }
    }
}

async fn process_message(payload: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    // 处理消息逻辑
    Ok(())
}

struct MapExtractor<'a>(&'a HashMap<String, String>);

impl<'a> Extractor for MapExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|s| s.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|s| s.as_str()).collect()
    }
}
```

---

## 6. Baggage 传播

### 6.1 Baggage 使用

```rust
use opentelemetry::baggage::BaggageExt;
use opentelemetry::KeyValue;

pub async fn use_baggage() {
    // 1. 设置 Baggage
    let cx = Context::current()
        .with_baggage(vec![
            KeyValue::new("user_id", "12345"),
            KeyValue::new("environment", "production"),
        ]);
    
    let _guard = cx.attach();
    
    // 2. 在子服务中读取 Baggage
    call_downstream_service().await;
}

async fn call_downstream_service() {
    let cx = Context::current();
    
    // 读取 Baggage
    if let Some(user_id) = cx.baggage().get("user_id") {
        println!("User ID: {}", user_id);
    }
    
    if let Some(env) = cx.baggage().get("environment") {
        println!("Environment: {}", env);
    }
}
```

### 6.2 Baggage 传播器

```rust
use opentelemetry::propagation::text_map_propagator::FieldIter;

pub struct BaggagePropagator;

impl TextMapPropagator for BaggagePropagator {
    fn inject_context(&self, cx: &Context, injector: &mut dyn Injector) {
        let baggage = cx.baggage();
        
        let baggage_str = baggage
            .iter()
            .map(|(k, v)| format!("{}={}", k.as_str(), v.as_str()))
            .collect::<Vec<_>>()
            .join(",");
        
        if !baggage_str.is_empty() {
            injector.set("baggage", baggage_str);
        }
    }
    
    fn extract_with_context(&self, cx: &Context, extractor: &dyn Extractor) -> Context {
        if let Some(baggage_str) = extractor.get("baggage") {
            let mut baggage_values = Vec::new();
            
            for pair in baggage_str.split(',') {
                let parts: Vec<&str> = pair.split('=').collect();
                if parts.len() == 2 {
                    baggage_values.push(KeyValue::new(parts[0].to_string(), parts[1].to_string()));
                }
            }
            
            return cx.with_baggage(baggage_values);
        }
        
        cx.clone()
    }
    
    fn fields(&self) -> FieldIter<'_> {
        FieldIter::new(&["baggage"])
    }
}
```

---

## 7. 自定义传播器

### 7.1 组合传播器

```rust
pub struct CompositePropagator {
    propagators: Vec<Box<dyn TextMapPropagator + Send + Sync>>,
}

impl CompositePropagator {
    pub fn new(propagators: Vec<Box<dyn TextMapPropagator + Send + Sync>>) -> Self {
        Self { propagators }
    }
}

impl TextMapPropagator for CompositePropagator {
    fn inject_context(&self, cx: &Context, injector: &mut dyn Injector) {
        for propagator in &self.propagators {
            propagator.inject_context(cx, injector);
        }
    }
    
    fn extract_with_context(&self, cx: &Context, extractor: &dyn Extractor) -> Context {
        let mut current_cx = cx.clone();
        
        for propagator in &self.propagators {
            current_cx = propagator.extract_with_context(&current_cx, extractor);
        }
        
        current_cx
    }
    
    fn fields(&self) -> FieldIter<'_> {
        // 合并所有字段
        todo!()
    }
}
```

---

## 8. 完整示例

### 8.1 微服务链路追踪

```rust
use axum::{Router, routing::get};
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::TracerProvider;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 TracerProvider
    let provider = TracerProvider::builder().build();
    global::set_tracer_provider(provider);
    
    // 2. 启动服务 A（前端）
    tokio::spawn(async {
        start_service_a().await;
    });
    
    // 3. 启动服务 B（后端）
    tokio::spawn(async {
        start_service_b().await;
    });
    
    tokio::signal::ctrl_c().await?;
    Ok(())
}

async fn start_service_a() {
    let app = Router::new()
        .route("/", get(handle_request_a))
        .layer(middleware::from_fn(trace_middleware));
    
    axum::serve(
        tokio::net::TcpListener::bind("0.0.0.0:8080").await.unwrap(),
        app,
    )
    .await
    .unwrap();
}

async fn handle_request_a() -> String {
    let tracer = global::tracer("service-a");
    let span = tracer.start("handle-request");
    let cx = Context::current_with_span(span);
    let _guard = cx.attach();
    
    // 调用服务 B
    let result = http_call_with_trace("http://localhost:8081/data").await.unwrap();
    
    cx.span().add_event("Received response from service-b", vec![
        KeyValue::new("response_length", result.len() as i64),
    ]);
    
    cx.span().end();
    
    format!("Service A: {}", result)
}

async fn start_service_b() {
    let app = Router::new()
        .route("/data", get(handle_request_b))
        .layer(middleware::from_fn(trace_middleware));
    
    axum::serve(
        tokio::net::TcpListener::bind("0.0.0.0:8081").await.unwrap(),
        app,
    )
    .await
    .unwrap();
}

async fn handle_request_b() -> String {
    let tracer = global::tracer("service-b");
    let span = tracer.start("fetch-data");
    let cx = Context::current_with_span(span);
    let _guard = cx.attach();
    
    // 模拟数据库查询
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    cx.span().set_attribute(KeyValue::new("db.query", "SELECT * FROM users"));
    cx.span().end();
    
    "Data from service B".to_string()
}
```

---

## 总结

分布式追踪上下文传播是 OTLP 系统的**核心能力**，Rust 实现时需要：

1. **标准协议**：实现 W3C Trace Context（traceparent/tracestate）
2. **HTTP 传播**：请求头注入与提取
3. **异步传播**：Task-Local Context 或显式传递
4. **消息队列传播**：Kafka/RabbitMQ Headers
5. **Baggage 传播**：业务上下文数据
6. **组合传播器**：支持多种传播协议

通过完善的上下文传播机制，可以实现跨服务、跨协议的完整链路追踪。
