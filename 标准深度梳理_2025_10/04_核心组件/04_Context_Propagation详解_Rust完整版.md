# Context Propagation 详解 - Rust 1.90 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry SDK**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月9日  
> **文档状态**: ✅ 生产就绪

---

## 目录

- [Context Propagation 详解 - Rust 1.90 完整实现](#context-propagation-详解---rust-190-完整实现)
  - [目录](#目录)
  - [1. Context概念](#1-context概念)
    - [1.1 什么是Context](#11-什么是context)
    - [1.2 Context在Rust中的实现](#12-context在rust中的实现)
  - [2. W3C Trace Context标准](#2-w3c-trace-context标准)
    - [2.1 Traceparent Header](#21-traceparent-header)
    - [2.2 Tracestate Header](#22-tracestate-header)
  - [3. HTTP传播实现](#3-http传播实现)
    - [3.1 Reqwest客户端传播](#31-reqwest客户端传播)
    - [3.2 Axum服务器提取](#32-axum服务器提取)
    - [3.3 完整HTTP中间件](#33-完整http中间件)
  - [4. gRPC传播实现](#4-grpc传播实现)
    - [4.1 Tonic客户端传播](#41-tonic客户端传播)
    - [4.2 Tonic服务器提取](#42-tonic服务器提取)
  - [5. 异步Context传播](#5-异步context传播)
    - [5.1 Tokio任务中传播](#51-tokio任务中传播)
    - [5.2 Stream中传播](#52-stream中传播)
    - [5.3 Future组合中传播](#53-future组合中传播)
  - [6. Baggage传播](#6-baggage传播)
    - [6.1 Baggage API](#61-baggage-api)
    - [6.2 跨服务传递业务数据](#62-跨服务传递业务数据)
  - [7. 自定义Propagator](#7-自定义propagator)
  - [8. 生产环境最佳实践](#8-生产环境最佳实践)
  - [9. 故障排查](#9-故障排查)

---

## 1. Context概念

### 1.1 什么是Context

**Context定义**:

```rust
use opentelemetry::Context;

/// Context是不可变的键值存储
/// 用于在调用链中传播信息
/// 
/// Context包含:
/// - Span上下文 (TraceId, SpanId, TraceFlags)
/// - Baggage (键值对)
/// - 其他传播数据

// 创建新Context
let cx = Context::new();

// 从当前Context派生
let parent_cx = Context::current();
let child_cx = parent_cx.with_value(key, value);
```

### 1.2 Context在Rust中的实现

**Context存储**:

```rust
use opentelemetry::{Context, trace::{TraceContextExt, Span}};

/// 1. ThreadLocal存储 (同步代码)
fn sync_function() {
    let cx = Context::current();  // 从ThreadLocal获取
    
    cx.span().add_event("Processing", vec![]);
}

/// 2. 异步Context传播
async fn async_function() {
    // tracing crate自动传播context
    let _span = tracing::info_span!("async_op").entered();
    
    // 在span内部，context自动传播到子调用
    sub_function().await;
}

/// 3. 手动Context传播
async fn manual_propagation() {
    let cx = Context::current();
    
    tokio::task::spawn(async move {
        // 手动附加context
        let _guard = cx.attach();
        
        // 现在context可用
        do_work().await;
    });
}
```

---

## 2. W3C Trace Context标准

### 2.1 Traceparent Header

**格式定义**:

```text
traceparent: 00-{trace-id}-{span-id}-{trace-flags}

示例:
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01

字段解析:
- 00: 版本号
- 4bf92f3577b34da6a3ce929d0e0e4736: TraceId (32 hex chars)
- 00f067aa0ba902b7: SpanId (16 hex chars)  
- 01: TraceFlags (01=sampled, 00=not sampled)
```

**Rust实现**:

```rust
use opentelemetry::trace::{SpanContext, TraceId, SpanId, TraceFlags, TraceState};

/// 解析traceparent header
pub fn parse_traceparent(header: &str) -> Result<SpanContext, String> {
    let parts: Vec<&str> = header.split('-').collect();
    
    if parts.len() != 4 {
        return Err("Invalid traceparent format".to_string());
    }
    
    // 解析version
    if parts[0] != "00" {
        return Err("Unsupported version".to_string());
    }
    
    // 解析trace_id
    let trace_id = TraceId::from_hex(parts[1])
        .map_err(|e| format!("Invalid trace_id: {}", e))?;
    
    // 解析span_id
    let span_id = SpanId::from_hex(parts[2])
        .map_err(|e| format!("Invalid span_id: {}", e))?;
    
    // 解析flags
    let flags = u8::from_str_radix(parts[3], 16)
        .map_err(|e| format!("Invalid flags: {}", e))?;
    
    let span_context = SpanContext::new(
        trace_id,
        span_id,
        TraceFlags::new(flags),
        false,  // is_remote
        TraceState::default(),
    );
    
    Ok(span_context)
}

/// 生成traceparent header
pub fn format_traceparent(span_context: &SpanContext) -> String {
    format!(
        "00-{}-{}-{:02x}",
        span_context.trace_id(),
        span_context.span_id(),
        span_context.trace_flags().to_u8()
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parse_traceparent() {
        let header = "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01";
        let ctx = parse_traceparent(header).unwrap();
        
        assert_eq!(
            ctx.trace_id().to_string(),
            "4bf92f3577b34da6a3ce929d0e0e4736"
        );
        assert_eq!(
            ctx.span_id().to_string(),
            "00f067aa0ba902b7"
        );
        assert!(ctx.is_sampled());
    }
}
```

### 2.2 Tracestate Header

**格式定义**:

```text
tracestate: vendor1=value1,vendor2=value2

示例:
tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

规则:
- 最多32个vendor
- 每个vendor最多256字符
- 逗号分隔
```

**Rust实现**:

```rust
use opentelemetry::trace::TraceState;

/// 解析tracestate header
pub fn parse_tracestate(header: &str) -> TraceState {
    let mut state = TraceState::default();
    
    for entry in header.split(',') {
        if let Some((key, value)) = entry.split_once('=') {
            state = state.insert(key.trim(), value.trim()).unwrap_or(state);
        }
    }
    
    state
}

/// 生成tracestate header
pub fn format_tracestate(state: &TraceState) -> String {
    state.header()
}
```

---

## 3. HTTP传播实现

### 3.1 Reqwest客户端传播

**自动注入Context到HTTP请求**:

```rust
use reqwest::{Client, Request};
use opentelemetry::{global, propagation::Injector};
use opentelemetry_http::HeaderInjector;

/// HTTP请求注入器
struct ReqwestInjector<'a> {
    headers: &'a mut reqwest::header::HeaderMap,
}

impl<'a> Injector for ReqwestInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.headers.insert(name, val);
            }
        }
    }
}

/// 带追踪的HTTP客户端
pub struct TracedClient {
    client: Client,
}

impl TracedClient {
    pub fn new() -> Self {
        Self {
            client: Client::new(),
        }
    }
    
    /// 发送带追踪的请求
    pub async fn get(&self, url: &str) -> Result<reqwest::Response, reqwest::Error> {
        let mut request = self.client.get(url).build()?;
        
        // 注入trace context
        let propagator = global::get_text_map_propagator(|propagator| {
            let cx = Context::current();
            let mut injector = ReqwestInjector {
                headers: request.headers_mut(),
            };
            propagator.inject_context(&cx, &mut injector);
        });
        
        self.client.execute(request).await
    }
    
    /// 通用请求方法
    pub async fn execute_traced(
        &self,
        mut request: Request,
    ) -> Result<reqwest::Response, reqwest::Error> {
        // 注入context
        global::get_text_map_propagator(|propagator| {
            let cx = Context::current();
            let mut injector = ReqwestInjector {
                headers: request.headers_mut(),
            };
            propagator.inject_context(&cx, &mut injector);
        });
        
        self.client.execute(request).await
    }
}

/// 使用示例
#[tracing::instrument]
async fn call_external_service() -> Result<String, Box<dyn std::error::Error>> {
    let client = TracedClient::new();
    
    // context自动传播到HTTP请求
    let response = client.get("https://api.example.com/users").await?;
    
    let body = response.text().await?;
    
    Ok(body)
}
```

### 3.2 Axum服务器提取

**从HTTP请求提取Context**:

```rust
use axum::{
    extract::{Request, FromRequestParts},
    middleware::{self, Next},
    response::Response,
    http::request::Parts,
};
use opentelemetry::{global, propagation::Extractor};

/// HTTP请求提取器
struct HeaderExtractor<'a> {
    headers: &'a axum::http::HeaderMap,
}

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.headers.get(key)?.to_str().ok()
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers
            .keys()
            .map(|k| k.as_str())
            .collect()
    }
}

/// Trace Context中间件
pub async fn trace_context_middleware(
    request: Request,
    next: Next,
) -> Response {
    // 从请求头提取context
    let parent_cx = global::get_text_map_propagator(|propagator| {
        let extractor = HeaderExtractor {
            headers: request.headers(),
        };
        propagator.extract(&extractor)
    });
    
    // 创建新span
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    // 在context中执行请求
    let response = {
        let _guard = cx.attach();
        next.run(request).await
    };
    
    response
}

/// 应用中间件
pub fn create_router() -> axum::Router {
    axum::Router::new()
        .route("/users", axum::routing::get(get_users))
        .layer(middleware::from_fn(trace_context_middleware))
}
```

### 3.3 完整HTTP中间件

**生产级HTTP追踪中间件**:

```rust
use axum::{
    body::Body,
    http::{Request, Response, StatusCode},
    middleware::Next,
};
use opentelemetry::trace::{SpanKind, Status, TraceContextExt};
use tracing::{info, error};
use std::time::Instant;

pub async fn tracing_middleware(
    request: Request<Body>,
    next: Next,
) -> Result<Response<Body>, StatusCode> {
    let start = Instant::now();
    
    // 提取parent context
    let parent_cx = global::get_text_map_propagator(|propagator| {
        let extractor = HeaderExtractor {
            headers: request.headers(),
        };
        propagator.extract(&extractor)
    });
    
    // 创建server span
    let tracer = global::tracer("http-server");
    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(SpanKind::Server)
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    // 设置HTTP属性
    span.set_attribute(opentelemetry_semantic_conventions::trace::HTTP_METHOD.string(
        request.method().to_string()
    ));
    span.set_attribute(opentelemetry_semantic_conventions::trace::HTTP_TARGET.string(
        request.uri().path().to_string()
    ));
    span.set_attribute(opentelemetry_semantic_conventions::trace::HTTP_SCHEME.string(
        request.uri().scheme_str().unwrap_or("http").to_string()
    ));
    
    let cx = Context::current_with_span(span.clone());
    
    // 执行请求
    let response = {
        let _guard = cx.attach();
        next.run(request).await
    };
    
    // 记录响应
    let duration = start.elapsed();
    let status_code = response.status();
    
    span.set_attribute(opentelemetry_semantic_conventions::trace::HTTP_STATUS_CODE.i64(
        status_code.as_u16() as i64
    ));
    
    if status_code.is_server_error() {
        span.set_status(Status::error("Server error"));
        error!(status = %status_code, duration_ms = %duration.as_millis(), "Request failed");
    } else {
        span.set_status(Status::Ok);
        info!(status = %status_code, duration_ms = %duration.as_millis(), "Request completed");
    }
    
    span.end();
    
    Ok(response)
}
```

---

## 4. gRPC传播实现

### 4.1 Tonic客户端传播

**gRPC客户端中间件**:

```rust
use tonic::{Request, Status, metadata::MetadataMap};
use opentelemetry::{global, propagation::Injector};

/// Metadata注入器
struct MetadataInjector<'a> {
    metadata: &'a mut MetadataMap,
}

impl<'a> Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.metadata.insert(key, val);
            }
        }
    }
}

/// 带追踪的gRPC客户端
pub struct TracedGrpcClient<T> {
    inner: T,
}

impl<T> TracedGrpcClient<T>
where
    T: tonic::client::GrpcService<tonic::body::BoxBody>,
{
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
    
    /// 拦截器 - 注入trace context
    pub fn inject_context<B>(mut request: Request<B>) -> Result<Request<B>, Status> {
        global::get_text_map_propagator(|propagator| {
            let cx = Context::current();
            let mut injector = MetadataInjector {
                metadata: request.metadata_mut(),
            };
            propagator.inject_context(&cx, &mut injector);
        });
        
        Ok(request)
    }
}

/// 使用示例
use tonic::transport::Channel;

#[tracing::instrument]
async fn call_grpc_service() -> Result<(), Box<dyn std::error::Error>> {
    let channel = Channel::from_static("http://localhost:50051")
        .connect()
        .await?;
    
    // 创建客户端 + 拦截器
    let mut client = proto::user_service_client::UserServiceClient::with_interceptor(
        channel,
        TracedGrpcClient::inject_context,
    );
    
    // context自动传播
    let request = proto::GetUserRequest { id: 123 };
    let response = client.get_user(request).await?;
    
    Ok(())
}
```

### 4.2 Tonic服务器提取

**gRPC服务器中间件**:

```rust
use tonic::{Request, Response, Status};
use opentelemetry::propagation::Extractor;

/// Metadata提取器
struct MetadataExtractor<'a> {
    metadata: &'a tonic::metadata::MetadataMap,
}

impl<'a> Extractor for MetadataExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.metadata.get(key)?.to_str().ok()
    }
    
    fn keys(&self) -> Vec<&str> {
        self.metadata
            .keys()
            .map(|k| k.as_str())
            .collect()
    }
}

/// gRPC服务器拦截器
pub async fn extract_context_interceptor(
    request: Request<()>,
) -> Result<Request<()>, Status> {
    // 提取parent context
    let parent_cx = global::get_text_map_propagator(|propagator| {
        let extractor = MetadataExtractor {
            metadata: request.metadata(),
        };
        propagator.extract(&extractor)
    });
    
    // 创建server span
    let tracer = global::tracer("grpc-server");
    let span = tracer
        .span_builder("grpc.request")
        .with_kind(SpanKind::Server)
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    let _guard = cx.attach();
    
    Ok(request)
}

/// 使用在service中
#[tonic::async_trait]
impl proto::user_service_server::UserService for MyUserService {
    #[tracing::instrument(skip(self))]
    async fn get_user(
        &self,
        request: Request<proto::GetUserRequest>,
    ) -> Result<Response<proto::User>, Status> {
        // context已经通过拦截器提取
        
        let user_id = request.into_inner().id;
        
        // 调用业务逻辑（context自动传播）
        let user = self.fetch_user(user_id).await
            .map_err(|e| Status::internal(e.to_string()))?;
        
        Ok(Response::new(user))
    }
}
```

---

## 5. 异步Context传播

### 5.1 Tokio任务中传播

**跨任务传播Context**:

```rust
use opentelemetry::Context;

/// ❌ 错误：Context不会自动传播到spawn的任务
async fn bad_example() {
    let _span = tracing::info_span!("parent").entered();
    
    tokio::spawn(async {
        // ❌ 这里context丢失！
        do_work().await;
    });
}

/// ✅ 正确：手动传播Context
async fn good_example() {
    let _span = tracing::info_span!("parent").entered();
    
    let cx = Context::current();
    
    tokio::spawn(async move {
        let _guard = cx.attach();
        
        // ✅ context正确传播
        do_work().await;
    });
}

/// ✅ 更好：使用tracing-futures
use tracing_futures::Instrument;

async fn best_example() {
    let span = tracing::info_span!("parent");
    
    tokio::spawn(
        async {
            do_work().await;
        }.instrument(span)  // 自动传播
    );
}
```

### 5.2 Stream中传播

**Stream处理中的Context**:

```rust
use futures::stream::{Stream, StreamExt};

#[tracing::instrument(skip(stream))]
async fn process_stream<S>(stream: S) -> Result<(), Error>
where
    S: Stream<Item = Event> + Unpin,
{
    let cx = Context::current();
    
    stream
        .then(|event| {
            let cx = cx.clone();
            async move {
                let _guard = cx.attach();
                
                // 在正确的context中处理事件
                process_event(event).await
            }
        })
        .collect::<Vec<_>>()
        .await;
    
    Ok(())
}

/// 使用Instrument trait
use tracing_futures::Instrument;

async fn process_stream_instrumented<S>(mut stream: S) -> Result<(), Error>
where
    S: Stream<Item = Event> + Unpin,
{
    let span = tracing::info_span!("process_stream");
    
    while let Some(event) = stream.next().instrument(span.clone()).await {
        process_event(event).await?;
    }
    
    Ok(())
}
```

### 5.3 Future组合中传播

**join!/select!中的Context**:

```rust
use tokio::try_join;

#[tracing::instrument]
async fn fetch_multiple_resources() -> Result<(User, Order, Product), Error> {
    let cx = Context::current();
    
    // 方式1: 每个future手动附加context
    let (user, order, product) = try_join!(
        async {
            let _guard = cx.attach();
            fetch_user().await
        },
        async {
            let _guard = cx.attach();
            fetch_order().await
        },
        async {
            let _guard = cx.attach();
            fetch_product().await
        },
    )?;
    
    Ok((user, order, product))
}

/// 方式2: 使用Instrument
async fn fetch_multiple_with_instrument() -> Result<(User, Order, Product), Error> {
    let span = tracing::Span::current();
    
    let (user, order, product) = try_join!(
        fetch_user().instrument(span.clone()),
        fetch_order().instrument(span.clone()),
        fetch_product().instrument(span.clone()),
    )?;
    
    Ok((user, order, product))
}
```

---

## 6. Baggage传播

### 6.1 Baggage API

**Baggage基本操作**:

```rust
use opentelemetry::baggage::{BaggageExt, KeyValueMetadata};
use opentelemetry::{Context, KeyValue};

/// 添加Baggage
pub fn add_baggage() {
    let cx = Context::current();
    
    // 添加单个baggage
    let cx = cx.with_baggage(vec![
        KeyValue::new("user.id", "12345"),
        KeyValue::new("tenant.id", "acme-corp"),
        KeyValue::new("request.priority", "high"),
    ]);
    
    // 附加context
    let _guard = cx.attach();
    
    // 在所有子调用中可用
    downstream_function();
}

/// 读取Baggage
pub fn read_baggage() {
    let cx = Context::current();
    
    if let Some(user_id) = cx.baggage().get("user.id") {
        tracing::info!("Processing request for user: {}", user_id.as_str());
    }
}

/// Baggage迭代
pub fn iterate_baggage() {
    let cx = Context::current();
    
    for (key, value) in cx.baggage() {
        tracing::debug!("Baggage: {} = {}", key.as_str(), value.as_str());
    }
}
```

### 6.2 跨服务传递业务数据

**使用Baggage传递租户ID等元数据**:

```rust
/// 服务A: 设置baggage
#[tracing::instrument]
async fn service_a_handler(user_id: i64, tenant_id: String) -> Result<(), Error> {
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("user.id", user_id.to_string()),
        KeyValue::new("tenant.id", tenant_id),
        KeyValue::new("request.source", "mobile-app"),
    ]);
    
    let _guard = cx.attach();
    
    // 调用服务B（baggage自动传播）
    call_service_b().await?;
    
    Ok(())
}

/// 服务B: 读取baggage
#[tracing::instrument]
async fn service_b_handler() -> Result<(), Error> {
    let cx = Context::current();
    
    // 从baggage获取租户ID
    let tenant_id = cx.baggage()
        .get("tenant.id")
        .map(|v| v.as_str().to_string())
        .ok_or_else(|| Error::MissingTenant)?;
    
    // 基于租户ID路由数据库
    let db = get_tenant_database(&tenant_id);
    
    // ...
    
    Ok(())
}

/// HTTP中间件提取baggage
pub async fn baggage_middleware(
    request: Request,
    next: Next,
) -> Response {
    // Baggage自动从HTTP headers提取 (通过W3C Baggage Propagator)
    
    // 可以在处理器中访问
    let response = next.run(request).await;
    
    response
}
```

---

## 7. 自定义Propagator

**实现自定义传播格式**:

```rust
use opentelemetry::propagation::{Injector, Extractor, TextMapPropagator};
use opentelemetry::Context;

/// 自定义传播器
pub struct CustomPropagator;

impl TextMapPropagator for CustomPropagator {
    fn inject_context(&self, cx: &Context, injector: &mut dyn Injector) {
        let span = cx.span();
        let span_context = span.span_context();
        
        if !span_context.is_valid() {
            return;
        }
        
        // 注入自定义格式
        injector.set(
            "x-custom-trace-id",
            span_context.trace_id().to_string(),
        );
        injector.set(
            "x-custom-span-id",
            span_context.span_id().to_string(),
        );
        injector.set(
            "x-custom-sampled",
            if span_context.is_sampled() { "1" } else { "0" }.to_string(),
        );
    }
    
    fn extract_with_context(&self, cx: &Context, extractor: &dyn Extractor) -> Context {
        let trace_id = extractor.get("x-custom-trace-id")
            .and_then(|s| TraceId::from_hex(s).ok());
        
        let span_id = extractor.get("x-custom-span-id")
            .and_then(|s| SpanId::from_hex(s).ok());
        
        let sampled = extractor.get("x-custom-sampled")
            .map(|s| s == "1")
            .unwrap_or(false);
        
        if let (Some(trace_id), Some(span_id)) = (trace_id, span_id) {
            let span_context = SpanContext::new(
                trace_id,
                span_id,
                if sampled { TraceFlags::SAMPLED } else { TraceFlags::default() },
                true,  // is_remote
                TraceState::default(),
            );
            
            cx.with_remote_span_context(span_context)
        } else {
            cx.clone()
        }
    }
    
    fn fields(&self) -> FieldIter<'_> {
        FieldIter::new(&["x-custom-trace-id", "x-custom-span-id", "x-custom-sampled"])
    }
}

/// 注册自定义propagator
pub fn setup_custom_propagator() {
    global::set_text_map_propagator(CustomPropagator);
}
```

---

## 8. 生产环境最佳实践

**Context传播最佳实践**:

```text
1. 使用标准Propagator
   ✅ W3C Trace Context (默认)
   ✅ W3C Baggage
   ✅ Jaeger (兼容性)

2. Baggage使用
   ✅ 只存储小量数据 (<1KB)
   ✅ 避免敏感信息
   ✅ 设置合理的baggage限制

3. 异步传播
   ✅ 使用tracing-futures
   ✅ 手动传播用Context::current()
   ✅ 验证context正确传播

4. 性能考虑
   ✅ 避免过多baggage
   ✅ 缓存tracer引用
   ✅ 使用批处理导出

5. 错误处理
   ✅ 优雅降级
   ✅ 记录传播失败
   ✅ 不要阻塞业务逻辑

6. 测试
   ✅ 测试跨服务传播
   ✅ 验证采样决策传播
   ✅ 测试baggage正确性
```

---

## 9. 故障排查

**常见问题和解决方案**:

```rust
/// 问题1: Span不连续（断链）
/// 原因: tokio::spawn没有传播context
/// 解决:
async fn fix_broken_trace() {
    let cx = Context::current();
    tokio::spawn(async move {
        let _guard = cx.attach();
        // ...
    });
}

/// 问题2: Baggage丢失
/// 原因: 没有配置Baggage Propagator
/// 解决:
use opentelemetry::global;
use opentelemetry_sdk::propagation::BaggagePropagator;

global::set_text_map_propagator(
    opentelemetry_sdk::propagation::TraceContextPropagator::new()
        .with_baggage(BaggagePropagator::new())
);

/// 问题3: 性能下降
/// 原因: Baggage过大
/// 解决: 限制baggage大小
const MAX_BAGGAGE_SIZE: usize = 8192;  // 8KB

fn validate_baggage(key: &str, value: &str) -> Result<(), Error> {
    if key.len() + value.len() > MAX_BAGGAGE_SIZE {
        return Err(Error::BaggageTooLarge);
    }
    Ok(())
}
```

---

**相关文档**:

- [Rust同步异步编程集成](05_Rust同步异步编程集成.md)
- [HTTP客户端追踪](08_HTTP_客户端追踪_Reqwest_中间件完整版.md)
- [gRPC传输层](../01_OTLP核心协议/02_传输层_gRPC_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
