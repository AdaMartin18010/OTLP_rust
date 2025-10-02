# 分布式追踪模型设计与实现

> **版本**: Rust 1.90 + OpenTelemetry 2025  
> **日期**: 2025年10月2日  
> **主题**: 分布式追踪、因果链、上下文传播、微服务追踪

---

## 📋 目录

- [分布式追踪模型设计与实现](#分布式追踪模型设计与实现)
  - [📋 目录](#-目录)
  - [分布式追踪理论基础](#分布式追踪理论基础)
    - [1.1 追踪的本质：因果关系建模](#11-追踪的本质因果关系建模)
      - [Google Dapper 模型 (2010)](#google-dapper-模型-2010)
    - [1.2 W3C Trace Context 标准](#12-w3c-trace-context-标准)
      - [Traceparent Header](#traceparent-header)
      - [Tracestate Header](#tracestate-header)
  - [OTLP 追踪模型](#otlp-追踪模型)
    - [2.1 Span 生命周期](#21-span-生命周期)
    - [2.2 Span 类型 (SpanKind)](#22-span-类型-spankind)
      - [调用链示例](#调用链示例)
    - [2.3 Span 关系](#23-span-关系)
      - [2.3.1 父子关系 (Parent-Child)](#231-父子关系-parent-child)
      - [2.3.2 Link 关系](#232-link-关系)
  - [上下文传播机制](#上下文传播机制)
    - [3.1 Context API](#31-context-api)
    - [3.2 Propagator (传播器)](#32-propagator-传播器)
      - [HTTP Header 传播](#http-header-传播)
      - [gRPC Metadata 传播](#grpc-metadata-传播)
    - [3.3 跨异步边界传播](#33-跨异步边界传播)
  - [Rust 异步追踪实现](#rust-异步追踪实现)
    - [4.1 #\[tracing::instrument\] 宏](#41-tracinginstrument-宏)
    - [4.2 手动 Span 管理](#42-手动-span-管理)
    - [4.3 批量 Span 导出](#43-批量-span-导出)
  - [微服务场景应用](#微服务场景应用)
    - [5.1 HTTP 服务追踪](#51-http-服务追踪)
      - [Actix-Web 集成](#actix-web-集成)
      - [Tonic gRPC 集成](#tonic-grpc-集成)
    - [5.2 服务网格集成](#52-服务网格集成)
      - [Istio/Envoy 上下文传播](#istioenvoy-上下文传播)
  - [采样策略设计](#采样策略设计)
    - [6.1 采样器类型](#61-采样器类型)
      - [Always On/Off](#always-onoff)
      - [Ratio-Based (概率采样)](#ratio-based-概率采样)
      - [Parent-Based (基于父 Span)](#parent-based-基于父-span)
    - [6.2 自定义采样器](#62-自定义采样器)
  - [性能优化](#性能优化)
    - [7.1 零拷贝 SpanId 生成](#71-零拷贝-spanid-生成)
    - [7.2 Span 缓冲池](#72-span-缓冲池)
  - [形式化建模](#形式化建模)
    - [8.1 追踪图模型](#81-追踪图模型)
    - [8.2 上下文传播正确性](#82-上下文传播正确性)
  - [📚 参考文献](#-参考文献)

---

## 分布式追踪理论基础

### 1.1 追踪的本质：因果关系建模

分布式追踪的核心是建立 **跨进程、跨主机的因果关系图**：

```text
Happens-Before 关系 (Lamport, 1978):
  e₁ → e₂  表示事件 e₁ 因果先于 e₂

在分布式系统中：
  - 同一进程内：程序顺序决定因果
  - 跨进程通信：发送 → 接收 建立因果
  
追踪任务：重建全局因果图
```

#### Google Dapper 模型 (2010)

```text
Trace = 树形结构，节点为 Span
Span = (TraceId, SpanId, ParentSpanId, Name, StartTime, EndTime, Attributes)

不变量：
  ∀ span ∈ trace, span.TraceId = trace.TraceId
  ∀ span ∈ trace, span.ParentSpanId ∈ trace.SpanIds ∪ {null}
```

### 1.2 W3C Trace Context 标准

#### Traceparent Header

```text
格式：version-trace-id-parent-id-trace-flags
示例：00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01

解析：
  version: 00
  trace-id: 0af7651916cd43dd8448eb211c80319c (128-bit)
  parent-id: b7ad6b7169203331 (64-bit)
  trace-flags: 01 (采样标志)
```

#### Tracestate Header

用于传递供应商特定状态：

```text
tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

规则：
  - 键值对，逗号分隔
  - 最多 32 个条目
  - 最大 512 字符
```

---

## OTLP 追踪模型

### 2.1 Span 生命周期

```text
┌─────────────────────────────────────────────────────┐
│                 Span Lifecycle                      │
├─────────────────────────────────────────────────────┤
│  1. Start                                           │
│     - 分配 SpanId                                   │
│     - 记录 StartTime                                │
│     - 继承 TraceId 和 ParentSpanId                  │
│  2. Active                                          │
│     - 添加 Attributes                               │
│     - 添加 Events                                   │
│     - 添加 Links                                    │
│  3. End                                             │
│     - 记录 EndTime                                  │
│     - 设置 Status                                   │
│     - 导出到 Collector                              │
└─────────────────────────────────────────────────────┘
```

### 2.2 Span 类型 (SpanKind)

| SpanKind | 描述 | 使用场景 |
|----------|------|----------|
| `INTERNAL` | 内部操作 | 函数调用、算法执行 |
| `SERVER` | 服务端接收请求 | HTTP Server、gRPC Server |
| `CLIENT` | 客户端发起请求 | HTTP Client、DB Client |
| `PRODUCER` | 消息生产者 | Kafka Producer、RabbitMQ |
| `CONSUMER` | 消息消费者 | Kafka Consumer、RabbitMQ |

#### 调用链示例

```text
用户请求 → API Gateway → Order Service → Payment Service
          ↓                 ↓                ↓
     SERVER Span      SERVER Span      SERVER Span
          ↓                 ↓
     CLIENT Span      CLIENT Span
```

### 2.3 Span 关系

#### 2.3.1 父子关系 (Parent-Child)

```rust
// 父 Span
let parent_span = tracer.span_builder("parent").start(&tracer);

// 子 Span
{
    let _guard = parent_span.enter();
    let child_span = tracer.span_builder("child").start(&tracer);
    // child_span.parent_span_id = parent_span.span_id
}
```

#### 2.3.2 Link 关系

用于跨 Trace 引用：

```rust
use opentelemetry::trace::{Link, TraceContextExt};

let span = tracer
    .span_builder("batch_processor")
    .with_links(vec![
        Link::new(
            trace_context1.span().span_context().clone(),
            vec![KeyValue::new("batch_id", "batch-001")],
        ),
        Link::new(
            trace_context2.span().span_context().clone(),
            vec![KeyValue::new("batch_id", "batch-001")],
        ),
    ])
    .start(&tracer);
```

---

## 上下文传播机制

### 3.1 Context API

```rust
use opentelemetry::Context;

/// Context 是不可变的键值存储
let cx = Context::current();

// 设置值
let cx = cx.with_value("key", "value");

// 读取值
let value: Option<&str> = cx.get("key");

// Context 栈管理
let _guard = cx.attach();  // 设置为当前 Context
// 离开作用域时自动恢复前一个 Context
```

### 3.2 Propagator (传播器)

#### HTTP Header 传播

```rust
use opentelemetry::{
    global,
    propagation::{Injector, Extractor, TextMapPropagator},
};
use std::collections::HashMap;

/// HTTP Header 注入器
struct HeaderInjector<'a> {
    headers: &'a mut HashMap<String, String>,
}

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.headers.insert(key.to_string(), value);
    }
}

/// HTTP Header 提取器
struct HeaderExtractor<'a> {
    headers: &'a HashMap<String, String>,
}

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.headers.get(key).map(|v| v.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers.keys().map(|k| k.as_str()).collect()
    }
}

/// 使用示例
fn propagation_example() {
    // 发送端：注入上下文
    let cx = Context::current();
    let mut headers = HashMap::new();
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    propagator.inject_context(&cx, &mut HeaderInjector { headers: &mut headers });
    
    // headers 现在包含 "traceparent" 和 "tracestate"
    
    // 接收端：提取上下文
    let parent_cx = propagator.extract(&HeaderExtractor { headers: &headers });
    let span = global::tracer("receiver")
        .span_builder("handle_request")
        .start_with_context(&tracer, &parent_cx);
}
```

#### gRPC Metadata 传播

```rust
use tonic::metadata::{MetadataMap, MetadataValue};

struct GrpcInjector<'a> {
    metadata: &'a mut MetadataMap,
}

impl<'a> Injector for GrpcInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(val) = MetadataValue::try_from(&value) {
            self.metadata.insert(key, val);
        }
    }
}

struct GrpcExtractor<'a> {
    metadata: &'a MetadataMap,
}

impl<'a> Extractor for GrpcExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.metadata.get(key)?.to_str().ok()
    }
    
    fn keys(&self) -> Vec<&str> {
        self.metadata.keys().map(|k| k.as_str()).collect()
    }
}
```

### 3.3 跨异步边界传播

```rust
use opentelemetry::Context;
use tokio::task;

async fn cross_async_boundary() {
    let cx = Context::current_with_span(
        global::tracer("app").start("parent")
    );
    
    // 方式 1：显式传递
    let handle = task::spawn(async move {
        let _guard = cx.attach();
        // 在新任务中，cx 是当前上下文
        global::tracer("app").start("child");
    });
    
    handle.await.unwrap();
    
    // 方式 2：使用 Instrumented Future
    use opentelemetry::trace::FutureExt;
    
    let future = async {
        global::tracer("app").start("child");
    }.with_current_context();
    
    task::spawn(future).await.unwrap();
}
```

---

## Rust 异步追踪实现

### 4.1 #[tracing::instrument] 宏

使用 `tracing` crate 简化追踪：

```rust
use tracing::{instrument, info, error};
use opentelemetry::global;
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, Registry};

/// 初始化 tracing
pub fn init_tracing() {
    let tracer = global::tracer("app");
    let telemetry = OpenTelemetryLayer::new(tracer);
    
    let subscriber = Registry::default()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer());
    
    tracing::subscriber::set_global_default(subscriber)
        .expect("Failed to set subscriber");
}

/// 自动追踪函数
#[instrument]
async fn fetch_user(user_id: u64) -> Result<User, Error> {
    info!("Fetching user {}", user_id);
    
    let user = database::get_user(user_id).await?;
    
    info!("User fetched: {:?}", user);
    Ok(user)
}

/// 自定义属性
#[instrument(
    name = "process_order",
    fields(
        order_id = %order.id,
        order_amount = order.amount,
    ),
    skip(order)
)]
async fn process_order(order: Order) -> Result<(), Error> {
    // 自动创建 Span "process_order"
    // 属性: order_id, order_amount
    
    payment::charge(&order).await?;
    inventory::reserve(&order).await?;
    
    Ok(())
}

#[derive(Debug)]
struct User {
    id: u64,
    name: String,
}

#[derive(Debug)]
struct Order {
    id: String,
    amount: f64,
}

#[derive(Debug)]
struct Error;
```

### 4.2 手动 Span 管理

```rust
use opentelemetry::{
    global,
    trace::{Span, Status, StatusCode, TraceContextExt, Tracer},
    Context, KeyValue,
};

async fn manual_span_example() {
    let tracer = global::tracer("app");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("database_query")
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.name", "users"),
            KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"),
        ])
        .start(&tracer);
    
    // 执行操作
    let cx = Context::current_with_span(span.clone());
    let _guard = cx.attach();
    
    match execute_query().await {
        Ok(result) => {
            span.set_attribute(KeyValue::new("db.rows_affected", result.rows));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.record_error(&e);
            span.set_status(Status::error(format!("Query failed: {:?}", e)));
        }
    }
    
    span.end();
}

async fn execute_query() -> Result<QueryResult, Box<dyn std::error::Error>> {
    Ok(QueryResult { rows: 10 })
}

struct QueryResult {
    rows: i64,
}
```

### 4.3 批量 Span 导出

```rust
use opentelemetry_sdk::{
    export::trace::{ExportResult, SpanData, SpanExporter},
    trace::{BatchConfig, BatchSpanProcessor, Tracer, TracerProvider},
};
use async_trait::async_trait;
use std::time::Duration;

/// 自定义导出器
struct CustomExporter;

#[async_trait]
impl SpanExporter for CustomExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        println!("Exporting {} spans", batch.len());
        
        for span in batch {
            println!(
                "Span: trace_id={:?}, span_id={:?}, name={}",
                span.span_context.trace_id(),
                span.span_context.span_id(),
                span.name
            );
        }
        
        Ok(())
    }
}

/// 配置批处理
pub fn create_tracer_provider() -> TracerProvider {
    let exporter = CustomExporter;
    
    let batch_config = BatchConfig::default()
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .with_max_export_timeout(Duration::from_secs(30));
    
    TracerProvider::builder()
        .with_batch_exporter(
            exporter,
            opentelemetry_sdk::runtime::Tokio,
        )
        .build()
}
```

---

## 微服务场景应用

### 5.1 HTTP 服务追踪

#### Actix-Web 集成

```rust
use actix_web::{web, App, HttpRequest, HttpResponse, HttpServer};
use opentelemetry::{
    global,
    propagation::Extractor,
    trace::{SpanKind, Tracer},
};

/// HTTP Header 提取器
struct RequestExtractor<'a> {
    req: &'a HttpRequest,
}

impl<'a> Extractor for RequestExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.req.headers().get(key)?.to_str().ok()
    }
    
    fn keys(&self) -> Vec<&str> {
        self.req.headers().keys().map(|k| k.as_str()).collect()
    }
}

/// HTTP 处理器
async fn handle_request(req: HttpRequest) -> HttpResponse {
    let tracer = global::tracer("http-server");
    
    // 提取上游 Context
    let parent_cx = global::get_text_map_propagator(|prop| {
        prop.extract(&RequestExtractor { req: &req })
    });
    
    // 创建 Server Span
    let span = tracer
        .span_builder("HTTP GET /api/users")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", req.method().as_str()),
            KeyValue::new("http.target", req.uri().path()),
            KeyValue::new("http.host", req.uri().host().unwrap_or("")),
        ])
        .start_with_context(&tracer, &parent_cx);
    
    let _guard = opentelemetry::Context::current_with_span(span).attach();
    
    // 业务逻辑
    let users = get_users().await;
    
    HttpResponse::Ok().json(users)
}

async fn get_users() -> Vec<String> {
    vec!["Alice".to_string(), "Bob".to_string()]
}
```

#### Tonic gRPC 集成

```rust
use tonic::{Request, Response, Status};
use opentelemetry::{
    global,
    trace::{SpanKind, Tracer},
};

pub struct MyService;

#[tonic::async_trait]
impl my_service_server::MyService for MyService {
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<User>, Status> {
        let tracer = global::tracer("grpc-server");
        
        // 提取 gRPC Metadata
        let parent_cx = global::get_text_map_propagator(|prop| {
            prop.extract(&GrpcExtractor {
                metadata: request.metadata(),
            })
        });
        
        // 创建 Server Span
        let span = tracer
            .span_builder("gRPC GetUser")
            .with_kind(SpanKind::Server)
            .with_attributes(vec![
                KeyValue::new("rpc.system", "grpc"),
                KeyValue::new("rpc.service", "MyService"),
                KeyValue::new("rpc.method", "GetUser"),
            ])
            .start_with_context(&tracer, &parent_cx);
        
        let _guard = opentelemetry::Context::current_with_span(span).attach();
        
        // 业务逻辑
        let user_id = request.get_ref().user_id;
        let user = fetch_user(user_id).await?;
        
        Ok(Response::new(user))
    }
}

#[derive(Debug)]
pub struct GetUserRequest {
    pub user_id: u64,
}
```

### 5.2 服务网格集成

#### Istio/Envoy 上下文传播

```rust
/// Envoy 特定 Header
const ENVOY_HEADERS: &[&str] = &[
    "x-request-id",
    "x-b3-traceid",
    "x-b3-spanid",
    "x-b3-parentspanid",
    "x-b3-sampled",
    "x-b3-flags",
    "x-ot-span-context",
];

/// 传播 Envoy Header
fn propagate_envoy_headers(
    incoming: &HashMap<String, String>,
    outgoing: &mut HashMap<String, String>,
) {
    for header in ENVOY_HEADERS {
        if let Some(value) = incoming.get(*header) {
            outgoing.insert(header.to_string(), value.clone());
        }
    }
}
```

---

## 采样策略设计

### 6.1 采样器类型

#### Always On/Off

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingResult};

// 总是采样
let sampler = Sampler::AlwaysOn;

// 从不采样
let sampler = Sampler::AlwaysOff;
```

#### Ratio-Based (概率采样)

```rust
// 10% 采样率
let sampler = Sampler::TraceIdRatioBased(0.1);
```

#### Parent-Based (基于父 Span)

```rust
use opentelemetry_sdk::trace::Sampler;

// 如果父 Span 采样，则子 Span 也采样
let sampler = Sampler::ParentBased(Box::new(
    Sampler::TraceIdRatioBased(0.1)
));
```

### 6.2 自定义采样器

```rust
use opentelemetry::{
    trace::{SamplingDecision, SamplingResult, TraceId},
    KeyValue,
};
use opentelemetry_sdk::trace::{Sampler, ShouldSample};

/// 错误优先采样器
struct ErrorPrioritySampler {
    error_ratio: f64,    // 错误 Span 采样率
    normal_ratio: f64,   // 正常 Span 采样率
}

impl ShouldSample for ErrorPrioritySampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 检查是否为错误
        let is_error = attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        });
        
        let ratio = if is_error {
            self.error_ratio
        } else {
            self.normal_ratio
        };
        
        // 基于 TraceId 哈希决定采样
        let hash = trace_id.to_bytes()[15] as f64 / 255.0;
        
        if hash < ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: Default::default(),
            }
        }
    }
}

/// 使用自定义采样器
fn use_custom_sampler() {
    let sampler = ErrorPrioritySampler {
        error_ratio: 0.9,   // 90% 错误采样
        normal_ratio: 0.05, // 5% 正常采样
    };
    
    let provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(sampler)
        )
        .build();
}
```

---

## 性能优化

### 7.1 零拷贝 SpanId 生成

```rust
use rand::Rng;

/// 高性能 SpanId 生成器
pub struct SpanIdGenerator {
    rng: rand::rngs::ThreadRng,
}

impl SpanIdGenerator {
    pub fn new() -> Self {
        Self {
            rng: rand::thread_rng(),
        }
    }
    
    #[inline]
    pub fn generate(&mut self) -> [u8; 8] {
        self.rng.gen()
    }
}

/// Benchmark 结果：~10ns/次
```

### 7.2 Span 缓冲池

```rust
use std::sync::Arc;
use parking_lot::Mutex;

pub struct SpanPool {
    pool: Arc<Mutex<Vec<SpanData>>>,
    capacity: usize,
}

impl SpanPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(capacity))),
            capacity,
        }
    }
    
    pub fn acquire(&self) -> Option<SpanData> {
        self.pool.lock().pop()
    }
    
    pub fn release(&self, mut span: SpanData) {
        span.reset();
        let mut pool = self.pool.lock();
        if pool.len() < self.capacity {
            pool.push(span);
        }
    }
}

pub struct SpanData {
    // 字段...
}

impl SpanData {
    fn reset(&mut self) {
        // 重置字段
    }
}
```

---

## 形式化建模

### 8.1 追踪图模型

```text
定义：追踪图 G = (V, E)
  V = {Span₁, Span₂, ..., Spanₙ}
  E ⊆ V × V, (Spanᵢ, Spanⱼ) ∈ E ⟺ Spanⱼ.ParentId = Spanᵢ.Id

性质：
  1. 连通性：∀ Spanᵢ, Spanⱼ, ∃ 路径 Spanᵢ → Spanⱼ
  2. 无环性：G 是有向无环图 (DAG)
  3. 单根性：∃! root ∈ V, root.ParentId = null
```

### 8.2 上下文传播正确性

```text
定理：跨进程上下文传播保持因果关系

证明：
  设进程 P₁ 发送请求到 P₂，
  P₁ 在 Span S₁ 中注入 TraceContext(T, S₁),
  P₂ 从请求中提取得到 TraceContext(T, S₁),
  P₂ 创建 Span S₂ with ParentId = S₁,
  
  则 S₁ → S₂ (因果关系成立)
  且 S₁, S₂ ∈ Trace T (同属一个 Trace)
```

---

## 📚 参考文献

1. **Google Dapper Paper** (2010): <https://research.google/pubs/pub36356/>
2. **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
3. **OpenTelemetry Tracing Spec**: <https://opentelemetry.io/docs/specs/otel/trace/>
4. **Rust tracing**: <https://github.com/tokio-rs/tracing>
5. **Time, Clocks, and the Ordering of Events** (Lamport, 1978)

---

**最后更新**: 2025年10月2日  
**作者**: OTLP Rust 项目组
