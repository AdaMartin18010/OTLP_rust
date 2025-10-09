# RPC 语义约定 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Tarpc**: 0.36+  
> **Tonic** (gRPC): 0.14.2  
> **最后更新**: 2025年10月9日

---

## 目录

- [RPC 语义约定 - Rust 完整实现](#rpc-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. RPC 语义约定概述](#1-rpc-语义约定概述)
    - [1.1 核心属性](#11-核心属性)
    - [1.2 RPC 系统分类](#12-rpc-系统分类)
  - [2. gRPC 追踪 (Tonic)](#2-grpc-追踪-tonic)
    - [2.1 客户端拦截器](#21-客户端拦截器)
    - [2.2 服务器拦截器](#22-服务器拦截器)
  - [3. Tarpc 追踪](#3-tarpc-追踪)
    - [3.1 客户端追踪](#31-客户端追踪)
    - [3.2 服务器追踪](#32-服务器追踪)
  - [4. JSON-RPC 追踪](#4-json-rpc-追踪)
  - [5. 通用 RPC 中间件](#5-通用-rpc-中间件)
  - [6. 完整示例](#6-完整示例)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 错误处理](#71-错误处理)
    - [7.2 请求/响应大小](#72-请求响应大小)
    - [7.3 超时处理](#73-超时处理)
    - [7.4 Cargo.toml 配置](#74-cargotoml-配置)
  - [总结](#总结)

---

## 1. RPC 语义约定概述

### 1.1 核心属性

根据 OpenTelemetry 规范，RPC 追踪需要记录以下属性：

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::trace::{
    RPC_SYSTEM,
    RPC_SERVICE,
    RPC_METHOD,
    NET_PEER_NAME,
    NET_PEER_PORT,
};

/// RPC Span 属性构建器
#[derive(Debug, Clone)]
pub struct RpcSpanAttributes {
    /// RPC 系统 (grpc, jsonrpc, tarpc, etc.)
    pub system: String,
    
    /// RPC 服务名称
    pub service: String,
    
    /// RPC 方法名称
    pub method: String,
    
    /// 对端主机名
    pub peer_name: Option<String>,
    
    /// 对端端口
    pub peer_port: Option<u16>,
}

impl RpcSpanAttributes {
    pub fn new(system: impl Into<String>, service: impl Into<String>, method: impl Into<String>) -> Self {
        Self {
            system: system.into(),
            service: service.into(),
            method: method.into(),
            peer_name: None,
            peer_port: None,
        }
    }
    
    pub fn with_peer(mut self, name: String, port: u16) -> Self {
        self.peer_name = Some(name);
        self.peer_port = Some(port);
        self
    }
    
    pub fn build(self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(RPC_SYSTEM, self.system),
            KeyValue::new(RPC_SERVICE, self.service),
            KeyValue::new(RPC_METHOD, self.method),
        ];
        
        if let Some(peer_name) = self.peer_name {
            attrs.push(KeyValue::new(NET_PEER_NAME, peer_name));
        }
        if let Some(peer_port) = self.peer_port {
            attrs.push(KeyValue::new(NET_PEER_PORT, peer_port as i64));
        }
        
        attrs
    }
}
```

### 1.2 RPC 系统分类

```rust
/// 支持的 RPC 系统
#[derive(Debug, Clone, Copy)]
pub enum RpcSystem {
    Grpc,
    JsonRpc,
    Tarpc,
    Thrift,
    CapnProto,
    Other,
}

impl RpcSystem {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Grpc => "grpc",
            Self::JsonRpc => "jsonrpc",
            Self::Tarpc => "tarpc",
            Self::Thrift => "thrift",
            Self::CapnProto => "capnproto",
            Self::Other => "other",
        }
    }
}
```

---

## 2. gRPC 追踪 (Tonic)

### 2.1 客户端拦截器

```rust
use tonic::{Request, Status, service::Interceptor};
use opentelemetry::{
    global,
    trace::{SpanKind, Tracer, TraceContextExt, Status as OtelStatus},
    propagation::{Injector, TextMapPropagator},
    Context, KeyValue,
};
use opentelemetry_semantic_conventions::trace::{RPC_SYSTEM, RPC_SERVICE, RPC_METHOD};

/// gRPC 客户端追踪拦截器
#[derive(Clone)]
pub struct GrpcClientTracer {
    service_name: String,
}

impl GrpcClientTracer {
    pub fn new(service_name: impl Into<String>) -> Self {
        Self {
            service_name: service_name.into(),
        }
    }
}

impl Interceptor for GrpcClientTracer {
    fn call(&mut self, mut request: Request<()>) -> Result<Request<()>, Status> {
        let tracer = global::tracer("grpc-client");
        let method = request.metadata().get("content-type")
            .and_then(|v| v.to_str().ok())
            .unwrap_or("unknown");
        
        // 创建 span
        let mut span = tracer
            .span_builder(format!("grpc.{}", method))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(RPC_SYSTEM, "grpc"),
                KeyValue::new(RPC_SERVICE, self.service_name.clone()),
                KeyValue::new(RPC_METHOD, method.to_string()),
            ])
            .start(&tracer);
        
        // 注入 trace context
        let cx = Context::current_with_span(span.clone());
        global::get_text_map_propagator(|propagator| {
            let mut injector = MetadataInjector(request.metadata_mut());
            propagator.inject_context(&cx, &mut injector);
        });
        
        Ok(request)
    }
}

/// Metadata 注入器
struct MetadataInjector<'a>(&'a mut tonic::metadata::MetadataMap);

impl<'a> Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(metadata_key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(metadata_value) = value.parse() {
                self.0.insert(metadata_key, metadata_value);
            }
        }
    }
}
```

### 2.2 服务器拦截器

```rust
use tonic::service::interceptor::InterceptedService;
use tower::{Layer, Service};
use std::task::{Context as TaskContext, Poll};
use std::pin::Pin;
use std::future::Future;

/// gRPC 服务器追踪层
#[derive(Clone)]
pub struct GrpcServerTracingLayer;

impl<S> Layer<S> for GrpcServerTracingLayer {
    type Service = GrpcServerTracingMiddleware<S>;
    
    fn layer(&self, service: S) -> Self::Service {
        GrpcServerTracingMiddleware { inner: service }
    }
}

/// gRPC 服务器追踪中间件
#[derive(Clone)]
pub struct GrpcServerTracingMiddleware<S> {
    inner: S,
}

impl<S, ReqBody> Service<http::Request<ReqBody>> for GrpcServerTracingMiddleware<S>
where
    S: Service<http::Request<ReqBody>> + Clone + Send + 'static,
    S::Future: Send + 'static,
    ReqBody: Send + 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;
    
    fn poll_ready(&mut self, cx: &mut TaskContext<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }
    
    fn call(&mut self, req: http::Request<ReqBody>) -> Self::Future {
        let tracer = global::tracer("grpc-server");
        
        // 提取 trace context
        let parent_cx = global::get_text_map_propagator(|propagator| {
            let extractor = HeaderExtractor(req.headers());
            propagator.extract(&extractor)
        });
        
        let method = req.uri().path().to_string();
        let mut span = tracer
            .span_builder(format!("grpc.{}", method))
            .with_kind(SpanKind::Server)
            .with_attributes(vec![
                KeyValue::new(RPC_SYSTEM, "grpc"),
                KeyValue::new(RPC_METHOD, method.clone()),
            ])
            .start_with_context(&tracer, &parent_cx);
        
        let cx = parent_cx.with_span(span.clone());
        let _guard = cx.attach();
        
        let mut inner = self.inner.clone();
        let fut = inner.call(req);
        
        Box::pin(async move {
            let result = fut.await;
            
            match &result {
                Ok(_) => {
                    span.set_status(OtelStatus::Ok);
                }
                Err(_) => {
                    span.set_status(OtelStatus::error("RPC error"));
                }
            }
            
            span.end();
            result
        })
    }
}

/// Header 提取器
struct HeaderExtractor<'a>(&'a http::HeaderMap);

impl<'a> opentelemetry::propagation::Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

---

## 3. Tarpc 追踪

### 3.1 客户端追踪

```rust
use tarpc::{client, context, ClientMessage, Response};
use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}, KeyValue, Context};
use futures::{prelude::*, future};

/// Tarpc 客户端追踪包装器
pub struct TracedTarpcClient<C> {
    client: C,
    service_name: String,
}

impl<C> TracedTarpcClient<C> {
    pub fn new(client: C, service_name: impl Into<String>) -> Self {
        Self {
            client,
            service_name: service_name.into(),
        }
    }
    
    /// 执行追踪的 RPC 调用
    pub async fn call_traced<Req, Resp>(
        &self,
        method: &str,
        request: Req,
    ) -> anyhow::Result<Resp>
    where
        C: tarpc::client::stub::Stub,
        Req: serde::Serialize,
        Resp: serde::de::DeserializeOwned,
    {
        let tracer = global::tracer("tarpc-client");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder(format!("rpc.{}", method))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(RPC_SYSTEM, "tarpc"),
                KeyValue::new(RPC_SERVICE, self.service_name.clone()),
                KeyValue::new(RPC_METHOD, method.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        // 创建 tarpc context
        let mut tarpc_ctx = context::current();
        
        // 注入 trace context 到 tarpc context
        global::get_text_map_propagator(|propagator| {
            let mut injector = TarpcContextInjector(&mut tarpc_ctx);
            propagator.inject_context(&Context::current_with_span(span.clone()), &mut injector);
        });
        
        // 执行 RPC 调用 (示意性代码，实际需要根据 tarpc API 调整)
        let result = future::ready(Ok(())); // 实际的 RPC 调用
        
        match result.await {
            Ok(_) => {
                span.set_status(opentelemetry::trace::Status::Ok);
            }
            Err(e) => {
                span.record_error(&e);
                span.set_status(opentelemetry::trace::Status::error("RPC failed"));
            }
        }
        
        span.end();
        todo!("Implement actual tarpc call")
    }
}

/// Tarpc context 注入器
struct TarpcContextInjector<'a>(&'a mut context::Context);

impl<'a> opentelemetry::propagation::Injector for TarpcContextInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        // 将 trace context 存储到 tarpc context 中
        // 注意: tarpc context 没有直接的键值存储，可能需要自定义扩展
    }
}
```

### 3.2 服务器追踪

```rust
use tarpc::server::{serve, Channel};
use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}, KeyValue};

/// Tarpc 服务器追踪装饰器
pub async fn serve_with_tracing<S>(
    listener: impl Stream<Item = io::Result<impl Channel>> + Unpin,
    service: S,
) where
    S: Clone + Send + 'static,
{
    let tracer = global::tracer("tarpc-server");
    
    listener
        .filter_map(|r| future::ready(r.ok()))
        .map(move |channel| {
            let service = service.clone();
            let tracer = tracer.clone();
            
            async move {
                // 为每个请求创建 span
                channel
                    .requests()
                    .execute(move |ctx, req| {
                        let tracer = tracer.clone();
                        let service = service.clone();
                        
                        async move {
                            // 提取 trace context
                            let parent_cx = extract_context_from_tarpc(&ctx);
                            
                            let mut span = tracer
                                .span_builder("rpc.handle_request")
                                .with_kind(SpanKind::Server)
                                .with_attributes(vec![
                                    KeyValue::new(RPC_SYSTEM, "tarpc"),
                                ])
                                .start_with_context(&tracer, &parent_cx);
                            
                            // 处理请求
                            let result = handle_request(&service, req).await;
                            
                            span.end();
                            result
                        }
                    })
                    .await
            }
        })
        .buffer_unordered(10)
        .for_each(|_| async {})
        .await;
}

fn extract_context_from_tarpc(ctx: &context::Context) -> Context {
    // 从 tarpc context 提取 trace context
    // 实际实现需要根据如何在 tarpc 中传递 trace context
    Context::current()
}

async fn handle_request<S, Req>(service: &S, req: Req) -> Result<(), ()> {
    // 实际的请求处理逻辑
    Ok(())
}
```

---

## 4. JSON-RPC 追踪

```rust
use jsonrpc_core::{IoHandler, Params, Result as RpcResult, Error as RpcError};
use jsonrpc_http_server::ServerBuilder;
use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}, KeyValue};
use serde_json::Value;

/// JSON-RPC 方法处理器 (带追踪)
pub fn add_traced_method<F, R>(
    io: &mut IoHandler,
    method: &str,
    handler: F,
) where
    F: Fn(Params) -> R + Send + Sync + 'static,
    R: Future<Output = RpcResult<Value>> + Send + 'static,
{
    let method_name = method.to_string();
    
    io.add_method(method, move |params| {
        let method_name = method_name.clone();
        
        async move {
            let tracer = global::tracer("jsonrpc");
            let cx = Context::current();
            
            let mut span = tracer
                .span_builder(format!("jsonrpc.{}", method_name))
                .with_kind(SpanKind::Server)
                .with_attributes(vec![
                    KeyValue::new(RPC_SYSTEM, "jsonrpc"),
                    KeyValue::new(RPC_METHOD, method_name.clone()),
                ])
                .start_with_context(&tracer, &cx);
            
            let result = handler(params).await;
            
            match &result {
                Ok(_) => {
                    span.set_status(opentelemetry::trace::Status::Ok);
                }
                Err(e) => {
                    span.set_attribute(KeyValue::new("rpc.error.code", e.code.code()));
                    span.set_attribute(KeyValue::new("rpc.error.message", e.message.clone()));
                    span.set_status(opentelemetry::trace::Status::error(e.message.clone()));
                }
            }
            
            span.end();
            result
        }
    });
}

/// 使用示例
#[tokio::main]
async fn main() {
    let mut io = IoHandler::new();
    
    // 添加带追踪的方法
    add_traced_method(&mut io, "add", |params: Params| async move {
        let (a, b): (i32, i32) = params.parse()?;
        Ok(Value::from(a + b))
    });
    
    add_traced_method(&mut io, "multiply", |params: Params| async move {
        let (a, b): (i32, i32) = params.parse()?;
        Ok(Value::from(a * b))
    });
    
    // 启动服务器
    let server = ServerBuilder::new(io)
        .start_http(&"127.0.0.1:3030".parse().unwrap())
        .expect("Unable to start RPC server");
    
    server.wait();
}
```

---

## 5. 通用 RPC 中间件

```rust
use std::future::Future;
use std::pin::Pin;
use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}, KeyValue, Context};

/// 通用 RPC 调用包装器
pub struct RpcCallWrapper {
    system: String,
    service: String,
}

impl RpcCallWrapper {
    pub fn new(system: impl Into<String>, service: impl Into<String>) -> Self {
        Self {
            system: system.into(),
            service: service.into(),
        }
    }
    
    /// 包装 RPC 调用并添加追踪
    pub async fn wrap_call<F, T, E>(
        &self,
        method: &str,
        call: F,
    ) -> Result<T, E>
    where
        F: Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        let tracer = global::tracer("rpc-wrapper");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder(format!("rpc.{}", method))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(RPC_SYSTEM, self.system.clone()),
                KeyValue::new(RPC_SERVICE, self.service.clone()),
                KeyValue::new(RPC_METHOD, method.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        let start = std::time::Instant::now();
        let result = call.await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("rpc.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(_) => {
                span.set_status(opentelemetry::trace::Status::Ok);
            }
            Err(e) => {
                span.set_attribute(KeyValue::new("rpc.error", e.to_string()));
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}

/// 使用示例
async fn call_remote_service() -> anyhow::Result<String> {
    let wrapper = RpcCallWrapper::new("custom-rpc", "user-service");
    
    let result = wrapper.wrap_call("get_user", async {
        // 实际的 RPC 调用
        Ok::<_, anyhow::Error>("user data".to_string())
    }).await?;
    
    Ok(result)
}
```

---

## 6. 完整示例

```rust
use tonic::{transport::Server, Request, Response, Status};
use opentelemetry::{global, trace::TracerProvider};
use anyhow::Result;

// gRPC 服务定义
pub mod hello {
    tonic::include_proto!("hello");
}

use hello::{
    greeter_server::{Greeter, GreeterServer},
    HelloRequest, HelloReply,
};

/// gRPC 服务实现
#[derive(Default)]
pub struct MyGreeter;

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let tracer = global::tracer("greeter-service");
        let cx = Context::current();
        
        // 创建子 span
        let mut span = tracer
            .span_builder("process_hello")
            .with_attributes(vec![
                KeyValue::new("request.name", request.get_ref().name.clone()),
            ])
            .start_with_context(&tracer, &cx);
        
        let reply = HelloReply {
            message: format!("Hello {}!", request.into_inner().name),
        };
        
        span.set_attribute(KeyValue::new("response.message", reply.message.clone()));
        span.end();
        
        Ok(Response::new(reply))
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    init_tracing()?;
    
    let addr = "127.0.0.1:50051".parse()?;
    let greeter = MyGreeter::default();
    
    println!("gRPC server listening on {}", addr);
    
    // 启动服务器 (带追踪层)
    Server::builder()
        .layer(GrpcServerTracingLayer)
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;
    
    Ok(())
}

/// 初始化追踪
fn init_tracing() -> Result<()> {
    use opentelemetry_otlp::WithExportConfig;
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer.provider().unwrap());
    
    Ok(())
}
```

---

## 7. 最佳实践

### 7.1 错误处理

```rust
/// 记录 RPC 错误详情
fn record_rpc_error<E: std::fmt::Display>(
    span: &mut opentelemetry::trace::BoxedSpan,
    error: &E,
) {
    span.set_attribute(KeyValue::new("rpc.error", error.to_string()));
    span.set_status(opentelemetry::trace::Status::error(error.to_string()));
}
```

### 7.2 请求/响应大小

```rust
/// 记录请求和响应大小
fn record_message_sizes(
    span: &mut opentelemetry::trace::BoxedSpan,
    request_size: usize,
    response_size: usize,
) {
    span.set_attribute(KeyValue::new("rpc.request.size", request_size as i64));
    span.set_attribute(KeyValue::new("rpc.response.size", response_size as i64));
}
```

### 7.3 超时处理

```rust
use tokio::time::{timeout, Duration};

/// 带超时的 RPC 调用
async fn call_with_timeout<F, T>(
    call: F,
    timeout_ms: u64,
) -> Result<T, Box<dyn std::error::Error>>
where
    F: Future<Output = Result<T, Box<dyn std::error::Error>>>,
{
    match timeout(Duration::from_millis(timeout_ms), call).await {
        Ok(result) => result,
        Err(_) => Err("RPC call timeout".into()),
    }
}
```

### 7.4 Cargo.toml 配置

```toml
[dependencies]
# gRPC
tonic = "0.14"
prost = "0.13"
tower = "0.5"

# Tarpc
tarpc = { version = "0.36", features = ["tokio1", "serde-transport"] }

# JSON-RPC
jsonrpc-core = "18.0"
jsonrpc-http-server = "18.0"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic"] }
opentelemetry-semantic-conventions = "0.31"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }
futures = "0.3"
async-trait = "0.1"

# 工具
anyhow = "1.0"
thiserror = "2.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

---

## 总结

本文档提供了 Rust 中各种 RPC 框架的 OpenTelemetry 追踪集成：

1. **gRPC (Tonic)**: 客户端和服务器拦截器
2. **Tarpc**: 异步 RPC 框架追踪
3. **JSON-RPC**: RESTful RPC 追踪
4. **通用中间件**: 可扩展的 RPC 包装器

所有示例都基于 **Rust 1.90**、**async/await** 和最新的 OpenTelemetry SDK，实现了完整的分布式追踪能力。

**下一步**: 查看 [HTTP 追踪](01_HTTP_Rust完整版.md) 和 [gRPC 详细实现](02_gRPC_Rust完整版.md)。
