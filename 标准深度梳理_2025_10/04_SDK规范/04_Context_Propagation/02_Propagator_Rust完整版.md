# Propagator - Rust 完整实现指南

## 📋 目录

- [Propagator - Rust 完整实现指南](#propagator---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Propagator 类型](#propagator-类型)
  - [Rust 实现](#rust-实现)
    - [TextMapPropagator](#textmappropagator)
    - [HTTP 集成](#http-集成)
      - [**HTTP 客户端（inject）**](#http-客户端inject)
      - [**HTTP 服务端（extract）**](#http-服务端extract)
    - [gRPC 集成](#grpc-集成)
      - [**gRPC 客户端（inject）**](#grpc-客户端inject)
      - [**gRPC 服务端（extract）**](#grpc-服务端extract)
    - [消息队列集成](#消息队列集成)
      - [**Kafka Producer（inject）**](#kafka-producerinject)
      - [**Kafka Consumer（extract）**](#kafka-consumerextract)
  - [复合 Propagator](#复合-propagator)
  - [自定义 Propagator](#自定义-propagator)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**HTTP 集成**](#http-集成-1)
    - [**gRPC 集成**](#grpc-集成-1)
    - [**消息队列**](#消息队列)
  - [总结](#总结)

---

## 核心概念

**Propagator** 负责在分布式系统的服务间传播 Context：

```text
┌────────────────────────────────────────────────┐
│              Service A                         │
│  Context ──→ Propagator.inject()               │
│                  ↓                             │
│       HTTP Header / gRPC Metadata              │
└────────────────────────────────────────────────┘
                  ↓ (网络传输)
┌────────────────────────────────────────────────┐
│              Service B                         │
│       HTTP Header / gRPC Metadata              │
│                  ↓                             │
│  Propagator.extract() ──→ Context              │
└────────────────────────────────────────────────┘
```

**关键操作**：

- **inject()**：将 Context 注入到 Carrier（如 HTTP Header）
- **extract()**：从 Carrier 提取 Context

---

## Propagator 类型

| Propagator | 标准 | 传输格式 | 使用场景 |
|-----------|------|---------|---------|
| **TraceContextPropagator** | W3C Trace Context | `traceparent`/`tracestate` | HTTP/gRPC（推荐）|
| **BaggagePropagator** | W3C Baggage | `baggage` | 传播业务数据 |
| **Composite** | - | 组合多个 | 同时支持多种格式 |
| **Jaeger** | Jaeger | `uber-trace-id` | Jaeger 生态 |
| **B3** | Zipkin | `X-B3-TraceId` | Zipkin 生态 |

---

## Rust 实现

### TextMapPropagator

**基础接口**：

```rust
use opentelemetry::{
    Context,
    propagation::{TextMapPropagator, Injector, Extractor},
};
use std::collections::HashMap;

// 1. 创建 Propagator
let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();

// 2. Inject：Context → Carrier
let cx = Context::current();
let mut carrier = HashMap::new();
propagator.inject_context(&cx, &mut carrier);

// carrier 现在包含:
// {
//     "traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
// }

// 3. Extract：Carrier → Context
let extractor = carrier;
let cx = propagator.extract(&extractor);

// 现在可以使用提取的 Context
let span = cx.span();
println!("Trace ID: {:?}", span.span_context().trace_id());
```

---

### HTTP 集成

#### **HTTP 客户端（inject）**

```rust
use reqwest::header::HeaderMap;
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();
    
    // 1. 创建 Span
    let tracer = global::tracer("http-client");
    let span = tracer.start("outgoing-request");
    let cx = Context::current_with_span(span);
    
    // 2. 注入 Context 到 HTTP Header
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    let mut headers = HeaderMap::new();
    
    propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));
    
    // 3. 发送请求
    let response = client
        .get("http://example.com/api")
        .headers(headers)
        .send()
        .await?;
    
    println!("Response: {:?}", response.status());
    Ok(())
}

// Injector 实现
struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> opentelemetry::propagation::Injector for HeaderInjector<'a> {
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

#### **HTTP 服务端（extract）**

```rust
use axum::{
    extract::Request,
    http::HeaderMap,
    middleware::{self, Next},
    response::Response,
    Router,
};
use opentelemetry::trace::{TraceContextExt, Tracer, TracerProvider};

async fn tracing_middleware(
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Response {
    // 1. 从 HTTP Header 提取 Context
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    let parent_cx = propagator.extract(&HeaderExtractor(&headers));
    
    // 2. 创建新 Span 作为子 Span
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder("incoming-request")
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    // 3. 在 Context 作用域内处理请求
    let response = cx.attach(|| async {
        next.run(request).await
    }).await;
    
    response
}

// Extractor 实现
struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> opentelemetry::propagation::Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api", axum::routing::get(handler))
        .layer(middleware::from_fn(tracing_middleware));
    
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}

async fn handler() -> &'static str {
    // 自动使用传播的 Context
    tracing::info!("Handling request");
    "OK"
}
```

---

### gRPC 集成

#### **gRPC 客户端（inject）**

```rust
use tonic::{Request, metadata::MetadataMap};

async fn grpc_client_with_context() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("grpc-client");
    let span = tracer.start("grpc-call");
    let cx = Context::current_with_span(span);
    
    // 1. 创建请求
    let mut request = Request::new(MyRequest { /* ... */ });
    
    // 2. 注入 Context 到 Metadata
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    propagator.inject_context(&cx, &mut MetadataInjector(request.metadata_mut()));
    
    // 3. 发送请求
    let mut client = MyServiceClient::connect("http://localhost:50051").await?;
    let response = client.my_method(request).await?;
    
    Ok(())
}

struct MetadataInjector<'a>(&'a mut MetadataMap);

impl<'a> opentelemetry::propagation::Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.0.insert(key, val);
            }
        }
    }
}
```

---

#### **gRPC 服务端（extract）**

```rust
use tonic::{Request, Response, Status};

#[tonic::async_trait]
impl MyService for MyServiceImpl {
    async fn my_method(&self, request: Request<MyRequest>) -> Result<Response<MyResponse>, Status> {
        // 1. 从 Metadata 提取 Context
        let propagator = global::get_text_map_propagator(|prop| prop.clone());
        let parent_cx = propagator.extract(&MetadataExtractor(request.metadata()));
        
        // 2. 创建子 Span
        let tracer = global::tracer("grpc-server");
        let span = tracer
            .span_builder("grpc-method")
            .with_parent_context(parent_cx)
            .start(&tracer);
        
        let cx = Context::current_with_span(span);
        
        // 3. 在 Context 作用域内处理
        let result = cx.attach(|| async {
            process_request(request.into_inner()).await
        }).await?;
        
        Ok(Response::new(result))
    }
}

struct MetadataExtractor<'a>(&'a tonic::metadata::MetadataMap);

impl<'a> opentelemetry::propagation::Extractor for MetadataExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

---

### 消息队列集成

#### **Kafka Producer（inject）**

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::message::OwnedHeaders;

async fn kafka_produce_with_context(producer: &FutureProducer) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("kafka-producer");
    let span = tracer.start("kafka-send");
    let cx = Context::current_with_span(span);
    
    // 1. 注入 Context 到 Kafka Headers
    let mut headers = OwnedHeaders::new();
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    propagator.inject_context(&cx, &mut KafkaHeaderInjector(&mut headers));
    
    // 2. 发送消息
    let record = FutureRecord::to("my-topic")
        .payload("message payload")
        .key("message-key")
        .headers(headers);
    
    producer.send(record, Duration::from_secs(0)).await?;
    Ok(())
}

struct KafkaHeaderInjector<'a>(&'a mut OwnedHeaders);

impl<'a> opentelemetry::propagation::Injector for KafkaHeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(rdkafka::message::Header {
            key,
            value: Some(&value),
        });
    }
}
```

---

#### **Kafka Consumer（extract）**

```rust
use rdkafka::consumer::{StreamConsumer, Consumer};
use rdkafka::Message;

async fn kafka_consume_with_context(consumer: &StreamConsumer) {
    loop {
        match consumer.recv().await {
            Ok(message) => {
                // 1. 从 Kafka Headers 提取 Context
                let propagator = global::get_text_map_propagator(|prop| prop.clone());
                let parent_cx = propagator.extract(&KafkaHeaderExtractor(message.headers()));
                
                // 2. 创建子 Span
                let tracer = global::tracer("kafka-consumer");
                let span = tracer
                    .span_builder("kafka-receive")
                    .with_parent_context(parent_cx)
                    .start(&tracer);
                
                let cx = Context::current_with_span(span);
                
                // 3. 处理消息
                cx.attach(|| async {
                    process_message(message.payload()).await;
                }).await;
            }
            Err(e) => eprintln!("Kafka error: {}", e),
        }
    }
}

struct KafkaHeaderExtractor<'a>(Option<&'a rdkafka::message::Headers>);

impl<'a> opentelemetry::propagation::Extractor for KafkaHeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.and_then(|headers| {
            headers.iter().find(|h| h.key == key).and_then(|h| {
                h.value.and_then(|v| std::str::from_utf8(v).ok())
            })
        })
    }

    fn keys(&self) -> Vec<&str> {
        self.0.map(|headers| {
            headers.iter().map(|h| h.key).collect()
        }).unwrap_or_default()
    }
}
```

---

## 复合 Propagator

**同时支持多种传播格式**：

```rust
use opentelemetry_sdk::propagation::{
    TraceContextPropagator,
    BaggagePropagator,
    TextMapCompositePropagator,
};

fn init_composite_propagator() {
    let propagator = TextMapCompositePropagator::new(vec![
        Box::new(TraceContextPropagator::new()),  // W3C Trace Context
        Box::new(BaggagePropagator::new()),       // W3C Baggage
    ]);
    
    global::set_text_map_propagator(propagator);
}

// 使用时会同时注入/提取两种格式
let cx = Context::current();
let mut carrier = HashMap::new();
global::get_text_map_propagator(|prop| {
    prop.inject_context(&cx, &mut carrier);
});

// carrier 包含:
// {
//     "traceparent": "00-...",
//     "baggage": "key1=value1,key2=value2"
// }
```

---

## 自定义 Propagator

**实现自定义传播格式**：

```rust
use opentelemetry::propagation::{TextMapPropagator, Injector, Extractor};

struct CustomPropagator;

impl TextMapPropagator for CustomPropagator {
    fn inject_context(&self, cx: &Context, injector: &mut dyn Injector) {
        let span = cx.span();
        let span_context = span.span_context();
        
        // 自定义格式：custom-trace-id
        injector.set(
            "custom-trace-id",
            format!("{:x}", span_context.trace_id()),
        );
        
        injector.set(
            "custom-span-id",
            format!("{:x}", span_context.span_id()),
        );
    }

    fn extract_with_context(&self, cx: &Context, extractor: &dyn Extractor) -> Context {
        if let Some(trace_id_str) = extractor.get("custom-trace-id") {
            if let Some(span_id_str) = extractor.get("custom-span-id") {
                // 解析并创建 SpanContext
                // ...
            }
        }
        cx.clone()
    }

    fn fields(&self) -> Vec<String> {
        vec![
            "custom-trace-id".to_string(),
            "custom-span-id".to_string(),
        ]
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **使用 W3C Trace Context**：现代服务间通信的标准
2. **Composite Propagator**：同时支持 TraceContext + Baggage
3. **中间件集成**：
   - HTTP：Axum/Actix middleware
   - gRPC：Interceptor
   - Kafka：自定义 wrapper
4. **错误处理**：extract 失败时创建新 root span
5. **全局配置**：使用 `global::set_text_map_propagator`

### ❌ **避免**

1. **忘记 inject**：导致 Trace 断链
2. **忘记 extract**：下游服务无法关联
3. **混用多种格式**：应使用 Composite
4. **忽略 fields()**：自定义 Propagator 应返回所有字段名

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
```

### **HTTP 集成**

```toml
reqwest = "0.12"
axum = "0.7"
hyper = "1.0"
```

### **gRPC 集成**

```toml
tonic = "0.12"
```

### **消息队列**

```toml
rdkafka = "0.36"        # Kafka
lapin = "2.5"           # RabbitMQ
```

---

## 总结

| 场景 | Propagator | Inject | Extract |
|------|-----------|--------|---------|
| HTTP 客户端 | TraceContextPropagator | Header | - |
| HTTP 服务端 | TraceContextPropagator | - | Header |
| gRPC 客户端 | TraceContextPropagator | Metadata | - |
| gRPC 服务端 | TraceContextPropagator | - | Metadata |
| Kafka Producer | TraceContextPropagator | Message Headers | - |
| Kafka Consumer | TraceContextPropagator | - | Message Headers |

**下一步**：[03_W3C_TraceContext_Rust完整版.md](./03_W3C_TraceContext_Rust完整版.md) - 深入 W3C Trace Context 规范
