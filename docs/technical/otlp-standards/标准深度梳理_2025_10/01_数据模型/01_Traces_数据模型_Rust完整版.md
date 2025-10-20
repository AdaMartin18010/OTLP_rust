# Traces 数据模型 - Rust 完整版

## 目录

- [Traces 数据模型 - Rust 完整版](#traces-数据模型---rust-完整版)
  - [目录](#目录)
  - [1. Trace 数据模型概述](#1-trace-数据模型概述)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 数据结构](#12-数据结构)
  - [2. Span 结构详解](#2-span-结构详解)
    - [2.1 SpanContext](#21-spancontext)
    - [2.2 Span 属性](#22-span-属性)
    - [2.3 Span Kind](#23-span-kind)
  - [3. Rust 实现](#3-rust-实现)
    - [3.1 创建 Span](#31-创建-span)
    - [3.2 Span 属性](#32-span-属性)
    - [3.3 Span Events](#33-span-events)
  - [4. Span 关系](#4-span-关系)
    - [4.1 父子关系](#41-父子关系)
    - [4.2 Span Links](#42-span-links)
  - [5. SpanContext 传播](#5-spancontext-传播)
    - [5.1 W3C Trace Context](#51-w3c-trace-context)
    - [5.2 自定义传播](#52-自定义传播)
  - [6. 时间戳与持续时间](#6-时间戳与持续时间)
    - [6.1 时间戳格式](#61-时间戳格式)
    - [6.2 Duration 计算](#62-duration-计算)
  - [7. Resource 资源](#7-resource-资源)
    - [7.1 Resource 属性](#71-resource-属性)
    - [7.2 自动检测资源](#72-自动检测资源)
  - [8. Trace State](#8-trace-state)
    - [8.1 Trace State 格式](#81-trace-state-格式)
    - [8.2 Rust 实现](#82-rust-实现)
  - [9. OTLP 导出格式](#9-otlp-导出格式)
    - [9.1 Protobuf 定义](#91-protobuf-定义)
    - [9.2 Rust 导出](#92-rust-导出)
  - [10. 完整示例](#10-完整示例)
    - [10.1 微服务追踪](#101-微服务追踪)
    - [10.2 查询 Trace](#102-查询-trace)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [数据模型规范](#数据模型规范)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Trace 数据模型概述

### 1.1 核心概念

````text
Trace: 完整的分布式调用链
├─ TraceId: 唯一标识符 (16 bytes / 32 hex chars)
├─ Spans: Span 集合
└─ Resource: 资源信息 (service.name, host.name)

Span: 单个操作单元
├─ SpanContext: 上下文 (trace_id, span_id, trace_flags)
├─ Attributes: 键值对属性
├─ Events: 时间点事件
├─ Links: 关联其他 Span
├─ Status: 操作状态 (Ok/Error)
└─ Kind: Span 类型 (Server/Client/Internal/Producer/Consumer)
````

### 1.2 数据结构

````rust
use opentelemetry::trace::{SpanId, TraceId, TraceFlags, TraceState};

pub struct SpanContext {
    pub trace_id: TraceId,        // 16 bytes
    pub span_id: SpanId,           // 8 bytes
    pub trace_flags: TraceFlags,   // 1 byte (sampled: 0x01)
    pub is_remote: bool,
    pub trace_state: TraceState,
}

pub struct Span {
    pub context: SpanContext,
    pub name: String,
    pub kind: SpanKind,
    pub start_time: SystemTime,
    pub end_time: Option<SystemTime>,
    pub attributes: Vec<KeyValue>,
    pub events: Vec<Event>,
    pub links: Vec<Link>,
    pub status: Status,
    pub parent_span_id: Option<SpanId>,
}
````

---

## 2. Span 结构详解

### 2.1 SpanContext

````rust
use opentelemetry::trace::{SpanContext, TraceId, SpanId, TraceFlags};

pub fn create_span_context() -> SpanContext {
    let trace_id = TraceId::from_hex("4bf92f3577b34da6a3ce929d0e0e4736").unwrap();
    let span_id = SpanId::from_hex("00f067aa0ba902b7").unwrap();

    SpanContext::new(
        trace_id,
        span_id,
        TraceFlags::SAMPLED,  // 0x01 = sampled
        false,                 // is_remote
        TraceState::default(),
    )
}

pub fn print_span_context(ctx: &SpanContext) {
    println!("Trace ID: {}", ctx.trace_id());
    println!("Span ID: {}", ctx.span_id());
    println!("Is Sampled: {}", ctx.is_sampled());
    println!("Is Remote: {}", ctx.is_remote());
}
````

**输出示例**:

````text
Trace ID: 4bf92f3577b34da6a3ce929d0e0e4736
Span ID: 00f067aa0ba902b7
Is Sampled: true
Is Remote: false
````

### 2.2 Span 属性

````rust
use opentelemetry::{KeyValue, Value};

pub fn span_attributes() -> Vec<KeyValue> {
    vec![
        // 字符串
        KeyValue::new("http.method", "POST"),
        KeyValue::new("http.url", "/api/orders"),

        // 整数
        KeyValue::new("http.status_code", 200),
        KeyValue::new("http.response_size_bytes", 1024),

        // 浮点数
        KeyValue::new("http.duration_ms", 45.5),

        // 布尔值
        KeyValue::new("http.cached", true),

        // 数组
        KeyValue::new("http.headers", Value::Array(
            vec![
                Value::String("Content-Type: application/json".into()),
                Value::String("Authorization: Bearer token".into()),
            ].into()
        )),
    ]
}
````

### 2.3 Span Kind

````rust
use opentelemetry::trace::SpanKind;

pub fn span_kind_examples() {
    // SERVER: 接收请求的服务器端 Span
    let server_span_kind = SpanKind::Server;

    // CLIENT: 发起请求的客户端 Span
    let client_span_kind = SpanKind::Client;

    // INTERNAL: 内部操作 Span (不涉及网络)
    let internal_span_kind = SpanKind::Internal;

    // PRODUCER: 消息生产者 Span (Kafka/RabbitMQ)
    let producer_span_kind = SpanKind::Producer;

    // CONSUMER: 消息消费者 Span
    let consumer_span_kind = SpanKind::Consumer;
}
````

**使用场景**:

| SpanKind | 场景 | 示例 |
|----------|------|------|
| SERVER | 接收 HTTP/gRPC 请求 | Axum 服务器端 |
| CLIENT | 发起 HTTP/gRPC 请求 | Reqwest 客户端 |
| INTERNAL | 函数调用、业务逻辑 | 数据处理函数 |
| PRODUCER | 发布消息到队列 | Kafka Producer |
| CONSUMER | 消费队列消息 | Kafka Consumer |

---

## 3. Rust 实现

### 3.1 创建 Span

````rust
use opentelemetry::global;
use opentelemetry::trace::{Tracer, SpanKind};

pub fn create_manual_span() {
    let tracer = global::tracer("my-service");

    let span = tracer
        .span_builder("database.query")
        .with_kind(SpanKind::Internal)
        .with_attributes(vec![
            opentelemetry::KeyValue::new("db.system", "postgresql"),
            opentelemetry::KeyValue::new("db.name", "mydb"),
            opentelemetry::KeyValue::new("db.operation", "SELECT"),
        ])
        .start(&tracer);

    // 使用 Span
    let _guard = span.attach();
    tracing::info!("Executing database query");

    // Span 自动结束 (Drop)
}
````

### 3.2 Span 属性

````rust
use tracing::{info, info_span, Span};

pub fn add_span_attributes() {
    let span = info_span!(
        "http.request",
        "http.method" = "POST",
        "http.url" = "/api/orders",
        "http.status_code" = tracing::field::Empty,  // 稍后设置
    );

    let _enter = span.enter();

    // 执行业务逻辑
    let status_code = 201;

    // 动态设置属性
    span.record("http.status_code", status_code);

    info!(status_code, "Request completed");
}
````

### 3.3 Span Events

````rust
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::global;
use tracing::Span;

pub fn add_span_events() {
    let span = Span::current();
    let context = span.context();
    let otel_span = context.span();

    // 添加事件
    otel_span.add_event(
        "cache.miss",
        vec![
            opentelemetry::KeyValue::new("cache.key", "user:12345"),
        ],
    );

    // 业务逻辑...
    tracing::info!("Cache miss, fetching from database");

    // 添加另一个事件
    otel_span.add_event(
        "db.query.start",
        vec![
            opentelemetry::KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"),
        ],
    );
}
````

---

## 4. Span 关系

### 4.1 父子关系

````rust
use tracing::{info, info_span, Instrument};

pub async fn parent_child_spans() {
    // 父 Span
    let parent_span = info_span!("parent_operation");

    async {
        info!("Parent operation started");

        // 子 Span 1
        child_operation_1().await;

        // 子 Span 2
        child_operation_2().await;

        info!("Parent operation completed");
    }
    .instrument(parent_span)
    .await;
}

#[tracing::instrument(name = "child_operation_1")]
async fn child_operation_1() {
    info!("Child 1 executing");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}

#[tracing::instrument(name = "child_operation_2")]
async fn child_operation_2() {
    info!("Child 2 executing");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
````

**Trace 结构**:

````text
Trace (trace_id: abc123)
└─ Span 1: parent_operation [parent_span_id: null]
   ├─ Span 2: child_operation_1 [parent_span_id: span1_id]
   └─ Span 3: child_operation_2 [parent_span_id: span1_id]
````

### 4.2 Span Links

````rust
use opentelemetry::trace::{Tracer, TraceContextExt, Link};
use opentelemetry::global;
use tracing::Span;

pub async fn span_with_links() {
    let tracer = global::tracer("my-service");

    // Span A
    let span_a = tracer.span_builder("operation_a").start(&tracer);
    let context_a = opentelemetry::Context::current_with_span(span_a);

    // Span B (链接到 Span A)
    let span_b = tracer
        .span_builder("operation_b")
        .with_links(vec![
            Link::new(
                context_a.span().span_context().clone(),
                vec![opentelemetry::KeyValue::new("link.type", "related")],
            )
        ])
        .start(&tracer);

    let _guard = span_b.attach();
    tracing::info!("Operation B with link to Operation A");
}
````

**使用场景**:

- 异步任务关联：消息发布者和消费者
- 批处理关联：多个输入 Span 关联到一个输出 Span
- 重试关联：原始 Span 和重试 Span

---

## 5. SpanContext 传播

### 5.1 W3C Trace Context

**HTTP Header 格式**:

````text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
             │  │                                │                  │
             │  └─ trace_id (32 hex)            └─ span_id (16 hex)│
             └─ version                                             └─ flags (01=sampled)

tracestate: vendor1=value1,vendor2=value2
````

**Rust 注入**:

````rust
use opentelemetry::global;
use opentelemetry::propagation::Injector;
use reqwest::header::HeaderMap;

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

pub async fn inject_context() {
    let mut headers = HeaderMap::new();

    // 注入追踪上下文
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut HeaderInjector(&mut headers),
        );
    });

    // 发送 HTTP 请求
    let client = reqwest::Client::new();
    let response = client
        .get("http://service-b:8080/api/data")
        .headers(headers)
        .send()
        .await;
}
````

### 5.2 自定义传播

````rust
use opentelemetry::{
    propagation::{Extractor, Injector, TextMapPropagator},
    Context,
};

pub struct CustomPropagator;

impl TextMapPropagator for CustomPropagator {
    fn inject_context(&self, context: &Context, injector: &mut dyn Injector) {
        if let Some(span) = context.span().span_context() {
            injector.set(
                "x-trace-id",
                span.trace_id().to_string(),
            );
            injector.set(
                "x-span-id",
                span.span_id().to_string(),
            );
            injector.set(
                "x-sampled",
                if span.is_sampled() { "1" } else { "0" }.to_string(),
            );
        }
    }

    fn extract_with_context(
        &self,
        cx: &Context,
        extractor: &dyn Extractor,
    ) -> Context {
        // 自定义提取逻辑
        cx.clone()
    }

    fn fields(&self) -> Vec<String> {
        vec![
            "x-trace-id".to_string(),
            "x-span-id".to_string(),
            "x-sampled".to_string(),
        ]
    }
}
````

---

## 6. 时间戳与持续时间

### 6.1 时间戳格式

````rust
use std::time::{SystemTime, Duration};
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::global;

pub fn span_with_timestamps() {
    let tracer = global::tracer("my-service");

    // 手动设置开始时间
    let start_time = SystemTime::now();
    let span = tracer
        .span_builder("operation")
        .with_start_time(start_time)
        .start(&tracer);

    let _guard = span.attach();

    // 业务逻辑...
    std::thread::sleep(Duration::from_millis(100));

    // Span 结束时自动记录 end_time
}
````

### 6.2 Duration 计算

````rust
use tracing::{info, Span};
use std::time::Instant;

pub async fn measure_duration() {
    let start = Instant::now();
    let span = Span::current();

    // 执行操作
    expensive_operation().await;

    let duration = start.elapsed();
    span.record("duration_ms", duration.as_millis() as u64);

    info!(duration_ms = duration.as_millis(), "Operation completed");
}

async fn expensive_operation() {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
````

---

## 7. Resource 资源

### 7.1 Resource 属性

````rust
use opentelemetry::{KeyValue, Resource};
use opentelemetry_sdk::trace::TracerProvider;

pub fn create_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("service.namespace", "production"),
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("host.name", hostname::get().unwrap().to_string_lossy().to_string()),
        KeyValue::new("process.pid", std::process::id().to_string()),
        KeyValue::new("telemetry.sdk.name", "opentelemetry"),
        KeyValue::new("telemetry.sdk.language", "rust"),
        KeyValue::new("telemetry.sdk.version", "0.31.0"),
    ])
}

pub fn init_with_resource() -> anyhow::Result<()> {
    let resource = create_resource();

    let provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .build();

    opentelemetry::global::set_tracer_provider(provider);
    Ok(())
}
````

### 7.2 自动检测资源

````toml
[dependencies]
opentelemetry-resource-detectors = "0.31.0"
````

````rust
use opentelemetry::Resource;
use opentelemetry_resource_detectors::{
    EnvResourceDetector,
    OsResourceDetector,
    ProcessResourceDetector,
};

pub fn auto_detect_resource() -> Resource {
    let env_resource = EnvResourceDetector::new().detect(std::time::Duration::from_secs(5));
    let os_resource = OsResourceDetector.detect(std::time::Duration::from_secs(5));
    let process_resource = ProcessResourceDetector.detect(std::time::Duration::from_secs(5));

    env_resource
        .merge(&os_resource)
        .merge(&process_resource)
}
````

---

## 8. Trace State

### 8.1 Trace State 格式

````text
tracestate: vendor1=value1,vendor2=opaque_value
            │       │       │       │
            │       │       │       └─ 不透明值
            │       │       └─ 供应商2键值对
            │       └─ 供应商1值
            └─ 供应商1键
````

### 8.2 Rust 实现

````rust
use opentelemetry::trace::TraceState;

pub fn create_trace_state() -> TraceState {
    let mut state = TraceState::default();

    // 添加键值对
    state = state.insert("vendor1", "value1").unwrap();
    state = state.insert("vendor2", "opaque_value").unwrap();

    // 读取值
    if let Some(value) = state.get("vendor1") {
        println!("vendor1 = {}", value);
    }

    state
}
````

---

## 9. OTLP 导出格式

### 9.1 Protobuf 定义

````protobuf
message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  bytes parent_span_id = 4;
  string name = 5;
  SpanKind kind = 6;
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
  repeated KeyValue attributes = 9;
  repeated Event events = 10;
  repeated Link links = 11;
  Status status = 12;
}

message ResourceSpans {
  Resource resource = 1;
  repeated ScopeSpans scope_spans = 2;
}
````

### 9.2 Rust 导出

````rust
use opentelemetry_otlp::{WithExportConfig, ExportConfig};
use opentelemetry_sdk::trace::TracerProvider;

pub fn init_otlp_exporter() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
                .with_timeout(std::time::Duration::from_secs(10))
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(create_resource())
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    opentelemetry::global::set_tracer_provider(tracer.provider().unwrap());
    Ok(())
}
````

---

## 10. 完整示例

### 10.1 微服务追踪

````rust
use opentelemetry::{global, KeyValue};
use tracing::{info, instrument, Span};

#[instrument(name = "api.create_order", skip(order))]
pub async fn create_order(order: Order) -> Result<String, anyhow::Error> {
    let span = Span::current();
    span.record("order.id", &order.id.as_str());
    span.record("order.amount", order.amount);

    info!(order_id = %order.id, "Creating order");

    // 1. 验证订单
    validate_order(&order).await?;

    // 2. 扣减库存
    deduct_inventory(&order.product_id).await?;

    // 3. 创建支付
    let payment_id = create_payment(&order).await?;

    info!(order_id = %order.id, payment_id = %payment_id, "Order created successfully");

    Ok(order.id)
}

#[instrument(name = "order.validate")]
async fn validate_order(order: &Order) -> Result<(), anyhow::Error> {
    info!(order_id = %order.id, "Validating order");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}

#[instrument(name = "inventory.deduct")]
async fn deduct_inventory(product_id: &str) -> Result<(), anyhow::Error> {
    info!(product_id, "Deducting inventory");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}

#[instrument(name = "payment.create")]
async fn create_payment(order: &Order) -> Result<String, anyhow::Error> {
    info!(order_id = %order.id, amount = order.amount, "Creating payment");
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    Ok("payment_123".to_string())
}

#[derive(Debug)]
pub struct Order {
    pub id: String,
    pub product_id: String,
    pub amount: f64,
}
````

### 10.2 查询 Trace

**Jaeger UI 查询**:

````bash
# 按 Trace ID 查询
curl "http://localhost:16686/api/traces/4bf92f3577b34da6a3ce929d0e0e4736"

# 按服务名和时间范围查询
curl "http://localhost:16686/api/traces?service=my-rust-service&start=1633024800000000&end=1633111200000000&limit=20"

# 按标签查询
curl "http://localhost:16686/api/traces?service=my-rust-service&tags={\"http.status_code\":\"500\"}"
````

**Trace JSON 输出**:

````json
{
  "data": [{
    "traceID": "4bf92f3577b34da6a3ce929d0e0e4736",
    "spans": [{
      "traceID": "4bf92f3577b34da6a3ce929d0e0e4736",
      "spanID": "00f067aa0ba902b7",
      "operationName": "api.create_order",
      "startTime": 1633024800000000,
      "duration": 350000,
      "tags": [
        {"key": "order.id", "type": "string", "value": "ORD-001"},
        {"key": "order.amount", "type": "float64", "value": 99.99},
        {"key": "span.kind", "type": "string", "value": "server"}
      ],
      "logs": [{
        "timestamp": 1633024800050000,
        "fields": [
          {"key": "event", "value": "order.validate.start"}
        ]
      }]
    }]
  }]
}
````

---

## 总结

### 核心要点

1. **TraceId**: 16 字节唯一标识符，关联整个分布式调用链
2. **SpanId**: 8 字节唯一标识符，标识单个 Span
3. **Span Kind**: 区分 SERVER/CLIENT/INTERNAL/PRODUCER/CONSUMER
4. **Span 关系**: 父子关系 (parent_span_id) 和 Links (关联关系)
5. **SpanContext 传播**: W3C Trace Context (traceparent/tracestate)
6. **Resource**: 服务级别元数据 (service.name, service.version)
7. **Status**: Span 状态 (Ok/Error)
8. **Events**: Span 内的时间点事件

### 数据模型规范

| 字段 | 类型 | 长度 | 示例 |
|------|------|------|------|
| trace_id | bytes | 16 bytes | `4bf92f3577b34da6a3ce929d0e0e4736` |
| span_id | bytes | 8 bytes | `00f067aa0ba902b7` |
| trace_flags | byte | 1 byte | `0x01` (sampled) |
| parent_span_id | bytes | 8 bytes | `0020000000000001` |
| name | string | - | `api.create_order` |
| kind | enum | - | `SERVER` (1) |
| start_time | fixed64 | 8 bytes | Unix nano (1633024800000000000) |
| end_time | fixed64 | 8 bytes | Unix nano |

### 最佳实践清单

- ✅ 使用 W3C Trace Context 传播 SpanContext
- ✅ 正确设置 Span Kind (SERVER/CLIENT/INTERNAL/PRODUCER/CONSUMER)
- ✅ 使用语义化的 Span Name (`http.request`, `db.query`)
- ✅ 记录标准化属性 (`http.method`, `db.system`)
- ✅ 父子 Span 使用 `parent_span_id` 关联
- ✅ 异步关联使用 Span Links
- ✅ 设置 Resource 属性 (`service.name`, `service.version`)
- ✅ 使用 Span Events 记录关键时间点
- ✅ 错误时设置 Status 为 Error
- ✅ 使用 TraceState 传递供应商特定信息

---

**相关文档**:

- [分布式追踪进阶](../02_Semantic_Conventions/03_日志与事件/02_分布式追踪进阶_Rust完整版.md)
- [Context Propagation 详解](../04_核心组件/04_Context_Propagation详解_Rust完整版.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
- [OTLP 协议详解](../04_核心组件/01_OTLP协议详解_Rust完整版.md)
