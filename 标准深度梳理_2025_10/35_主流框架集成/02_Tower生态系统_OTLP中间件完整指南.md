# Tower 生态系统 OTLP 中间件完整指南

> **框架地位**: 🏗️ Tokio 官方标准 + Linkerd2/Hyper/Tonic 核心基础  
> **生态影响**: Axum/Tonic/Hyper 的底层中间件抽象  
> **Tower 版本**: 0.5.1  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **完整示例**: Layer + Service + Middleware 三位一体

---

## 📋 目录

- [Tower 生态系统 OTLP 中间件完整指南](#tower-生态系统-otlp-中间件完整指南)
  - [📋 目录](#-目录)
  - [🌟 Tower 概述](#-tower-概述)
    - [什么是 Tower?](#什么是-tower)
    - [国际标准对标](#国际标准对标)
  - [🎯 核心概念](#-核心概念)
    - [1. Service Trait](#1-service-trait)
    - [2. Layer 模式](#2-layer-模式)
    - [3. 中间件组合](#3-中间件组合)
  - [🔭 OTLP 集成策略](#-otlp-集成策略)
    - [三层集成](#三层集成)
  - [📦 完整 OTLP Layer 实现](#-完整-otlp-layer-实现)
    - [1. 基础 OTLP Service](#1-基础-otlp-service)
    - [2. OTLP Layer](#2-otlp-layer)
    - [3. 追踪传播 (W3C Trace Context)](#3-追踪传播-w3c-trace-context)
  - [🔌 与主流框架集成](#-与主流框架集成)
    - [1. Axum 集成](#1-axum-集成)
    - [2. Tonic (gRPC) 集成](#2-tonic-grpc-集成)
    - [3. Hyper 集成](#3-hyper-集成)
  - [🏗️ 高级中间件模式](#️-高级中间件模式)
    - [1. 超时中间件 + OTLP](#1-超时中间件--otlp)
    - [2. 限流中间件 + OTLP](#2-限流中间件--otlp)
    - [3. 重试中间件 + OTLP](#3-重试中间件--otlp)
  - [📊 性能优化](#-性能优化)
    - [1. 零分配优化](#1-零分配优化)
    - [2. Span 采样](#2-span-采样)
  - [🧪 测试策略](#-测试策略)
    - [单元测试](#单元测试)
  - [🚀 生产部署](#-生产部署)
    - [Cargo.toml](#cargotoml)
    - [完整示例应用](#完整示例应用)
  - [✅ 最佳实践](#-最佳实践)
    - [Tower 设计](#tower-设计)
    - [OTLP 集成](#otlp-集成)
    - [性能优化](#性能优化)

---

## 🌟 Tower 概述

### 什么是 Tower?

**Tower** 是 Rust 异步生态的中间件抽象层,定义了 `Service` trait 和 `Layer` 模式,是 **Tokio、Hyper、Tonic、Axum** 等框架的核心基础。

```text
Tower 生态架构:
┌─────────────────────────────────────────────┐
│             Application Layer               │
│  ┌────────┐  ┌────────┐  ┌────────┐         │
│  │ Axum   │  │ Tonic  │  │ Hyper  │         │
│  └────┬───┘  └────┬───┘  └────┬───┘         │
│       │           │            │            │
│  ┌────▼───────────▼────────────▼─────┐      │
│  │         Tower Middleware           │     │
│  │  - Service Trait                   │     │
│  │  - Layer Pattern                   │     │
│  │  - Combinator (and_then, map_err)  │     │
│  └────────────────┬───────────────────┘     │
│                   │                         │
│  ┌────────────────▼───────────────────┐     │
│  │          Tokio Runtime             │     │
│  └────────────────────────────────────┘     │
└─────────────────────────────────────────────┘
```

**核心价值**:

- ✅ **统一抽象**: 所有异步服务统一接口
- ✅ **可组合**: 中间件自由组合
- ✅ **零成本**: 编译时内联,无运行时开销
- ✅ **类型安全**: 编译期保证
- ✅ **生态标准**: Linkerd2 (服务网格) 的核心

### 国际标准对标

| 标准/来源 | 内容 |
|----------|------|
| **官方文档** | [tower.rs](https://docs.rs/tower/latest/tower/) |
| **GitHub** | [tower-rs/tower](https://github.com/tower-rs/tower) (3.7k stars) |
| **Linkerd2** | [Service Mesh](https://linkerd.io) - 使用 Tower 实现 |
| **比较对象** | Java Servlet Filter, Go Middleware, Node.js Middleware |
| **论文** | [Composable Async Services](https://docs.rs/tower/latest/tower/#background) |

---

## 🎯 核心概念

### 1. Service Trait

```rust
/// Tower Service Trait (核心抽象)
pub trait Service<Request> {
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;
    
    /// 服务是否准备好处理请求
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    
    /// 处理请求
    fn call(&mut self, req: Request) -> Self::Future;
}
```

**示例**:

```rust
use tower::Service;
use std::task::{Context, Poll};
use std::future::Future;
use std::pin::Pin;

/// 简单的 Echo 服务
struct EchoService;

impl Service<String> for EchoService {
    type Response = String;
    type Error = std::io::Error;
    type Future = Pin<Box<dyn Future<Output = Result<String, std::io::Error>>>>;
    
    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }
    
    fn call(&mut self, req: String) -> Self::Future {
        Box::pin(async move { Ok(format!("Echo: {}", req)) })
    }
}
```

### 2. Layer 模式

```rust
/// Tower Layer (中间件构造器)
pub trait Layer<S> {
    type Service;
    
    /// 包装内层服务,返回新服务
    fn layer(&self, inner: S) -> Self::Service;
}
```

**示例**:

```rust
use tower::Layer;

/// 日志 Layer
struct LogLayer;

impl<S> Layer<S> for LogLayer {
    type Service = LogService<S>;
    
    fn layer(&self, inner: S) -> Self::Service {
        LogService { inner }
    }
}

/// 日志 Service (包装内层服务)
struct LogService<S> {
    inner: S,
}

impl<S, Request> Service<Request> for LogService<S>
where
    S: Service<Request>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = S::Future;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }
    
    fn call(&mut self, req: Request) -> Self::Future {
        println!("Request received");
        self.inner.call(req)
    }
}
```

### 3. 中间件组合

```rust
use tower::ServiceBuilder;

// 链式组合多个中间件
let service = ServiceBuilder::new()
    .layer(TimeoutLayer::new(Duration::from_secs(30)))
    .layer(RateLimitLayer::new(100))
    .layer(OtlpLayer::new())
    .service(my_service);
```

---

## 🔭 OTLP 集成策略

### 三层集成

```text
Request Flow:
┌─────────────────────────────────────────────┐
│  1. OtlpLayer (最外层)                      │
│     ├─ 提取 Trace Context                   │
│     ├─ 创建 Root Span                       │
│     └─ 注入到 Request Extensions            │
│     ↓                                       │
│  2. Business Layers (业务中间件)            │
│     ├─ Timeout                              │
│     ├─ RateLimit                            │
│     ├─ Retry                                │
│     └─ (自动继承 Span Context)              │
│     ↓                                       │
│  3. Inner Service (内层服务)                │
│     ├─ Handler (#[instrument])              │
│     ├─ Database (sqlx auto-tracing)         │
│     └─ External Call (http client tracing)  │
└─────────────────────────────────────────────┘
```

---

## 📦 完整 OTLP Layer 实现

### 1. 基础 OTLP Service

```rust
// src/tower_otlp/service.rs
use tower::Service;
use std::task::{Context, Poll};
use std::pin::Pin;
use std::future::Future;
use tracing::{instrument, Span};
use opentelemetry::trace::{TraceContextExt, Tracer, SpanKind};
use opentelemetry::KeyValue;

/// OTLP Service (包装内层服务)
pub struct OtlpService<S> {
    inner: S,
}

impl<S> OtlpService<S> {
    pub fn new(inner: S) -> Self {
        Self { inner }
    }
}

impl<S, Request> Service<Request> for OtlpService<S>
where
    S: Service<Request>,
    S::Future: 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }
    
    fn call(&mut self, req: Request) -> Self::Future {
        // 创建 Span
        let span = tracing::info_span!(
            "tower.service",
            otel.kind = ?SpanKind::Server,
            tower.layer = "otlp"
        );
        
        let fut = self.inner.call(req);
        
        Box::pin(async move {
            let _enter = span.enter();
            let start = std::time::Instant::now();
            
            let result = fut.await;
            let duration = start.elapsed();
            
            span.record("duration_ms", duration.as_millis() as u64);
            
            match &result {
                Ok(_) => {
                    span.record("status", "success");
                }
                Err(_) => {
                    span.record("status", "error");
                }
            }
            
            result
        })
    }
}
```

### 2. OTLP Layer

```rust
// src/tower_otlp/layer.rs
use tower::Layer;
use super::service::OtlpService;

/// OTLP Layer (构造器)
#[derive(Clone)]
pub struct OtlpLayer;

impl OtlpLayer {
    pub fn new() -> Self {
        Self
    }
}

impl<S> Layer<S> for OtlpLayer {
    type Service = OtlpService<S>;
    
    fn layer(&self, inner: S) -> Self::Service {
        OtlpService::new(inner)
    }
}

impl Default for OtlpLayer {
    fn default() -> Self {
        Self::new()
    }
}
```

### 3. 追踪传播 (W3C Trace Context)

```rust
// src/tower_otlp/propagation.rs
use http::{Request, Response};
use opentelemetry::propagation::{Extractor, Injector};
use opentelemetry::global;
use std::collections::HashMap;

/// HTTP Header Extractor (提取 Trace Context)
pub struct HeaderExtractor<'a> {
    headers: &'a http::HeaderMap,
}

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.headers.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers.keys().map(|k| k.as_str()).collect()
    }
}

/// HTTP Header Injector (注入 Trace Context)
pub struct HeaderInjector<'a> {
    headers: &'a mut http::HeaderMap,
}

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(header_value) = http::HeaderValue::from_str(&value) {
            self.headers.insert(
                http::HeaderName::from_bytes(key.as_bytes()).unwrap(),
                header_value,
            );
        }
    }
}

/// HTTP OTLP Service (完整追踪传播)
pub struct HttpOtlpService<S> {
    inner: S,
}

impl<S, B> Service<Request<B>> for HttpOtlpService<S>
where
    S: Service<Request<B>>,
    S::Future: 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }
    
    fn call(&mut self, req: Request<B>) -> Self::Future {
        use opentelemetry::trace::TraceContextExt;
        
        // 提取上游 Trace Context
        let parent_cx = global::get_text_map_propagator(|propagator| {
            propagator.extract(&HeaderExtractor {
                headers: req.headers(),
            })
        });
        
        // 创建 Span (继承上游 Context)
        let span = tracing::info_span!(
            "http.request",
            otel.kind = ?SpanKind::Server,
            http.method = %req.method(),
            http.target = %req.uri().path(),
        );
        
        // 附加 Parent Context
        span.set_parent(parent_cx);
        
        let fut = self.inner.call(req);
        
        Box::pin(async move {
            let _enter = span.enter();
            fut.await
        })
    }
}
```

---

## 🔌 与主流框架集成

### 1. Axum 集成

```rust
// src/examples/axum_tower.rs
use axum::{Router, routing::get, Json};
use tower::ServiceBuilder;
use tower_http::trace::TraceLayer;
use crate::tower_otlp::OtlpLayer;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api/users", get(list_users))
        .layer(
            ServiceBuilder::new()
                .layer(OtlpLayer::new())              // OTLP 追踪
                .layer(TraceLayer::new_for_http())    // HTTP 日志
        );
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}

async fn list_users() -> Json<Vec<String>> {
    Json(vec!["Alice".to_string(), "Bob".to_string()])
}
```

### 2. Tonic (gRPC) 集成

```rust
// src/examples/tonic_tower.rs
use tonic::{transport::Server, Request, Response, Status};
use tower::ServiceBuilder;
use crate::tower_otlp::OtlpLayer;

// Proto 定义
pub mod hello {
    tonic::include_proto!("hello");
}

use hello::{
    greeter_server::{Greeter, GreeterServer},
    HelloRequest, HelloReply,
};

#[derive(Default)]
pub struct MyGreeter;

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let name = &request.get_ref().name;
        
        Ok(Response::new(HelloReply {
            message: format!("Hello, {}!", name),
        }))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "0.0.0.0:50051".parse()?;
    
    Server::builder()
        .layer(OtlpLayer::new())  // OTLP 追踪
        .add_service(GreeterServer::new(MyGreeter::default()))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 3. Hyper 集成

```rust
// src/examples/hyper_tower.rs
use hyper::{Body, Request, Response, Server};
use hyper::service::{make_service_fn, service_fn};
use tower::{Service, ServiceBuilder};
use crate::tower_otlp::OtlpLayer;

async fn handle(_req: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    Ok(Response::new(Body::from("Hello, Hyper!")))
}

#[tokio::main]
async fn main() {
    let addr = ([0, 0, 0, 0], 8080).into();
    
    let make_svc = make_service_fn(|_conn| {
        // 为每个连接创建服务
        let service = ServiceBuilder::new()
            .layer(OtlpLayer::new())
            .service_fn(handle);
        
        async { Ok::<_, hyper::Error>(service) }
    });
    
    let server = Server::bind(&addr).serve(make_svc);
    
    server.await.unwrap();
}
```

---

## 🏗️ 高级中间件模式

### 1. 超时中间件 + OTLP

```rust
// src/middleware/timeout.rs
use tower::timeout::Timeout;
use tower::ServiceBuilder;
use std::time::Duration;
use crate::tower_otlp::OtlpLayer;

/// 超时中间件 (带 OTLP 追踪)
pub fn timeout_with_tracing<S>(
    service: S,
    duration: Duration,
) -> impl Service<
    Request,
    Response = S::Response,
    Error = tower::BoxError,
>
where
    S: Service<Request> + Send + 'static,
    S::Future: Send,
{
    ServiceBuilder::new()
        .layer(OtlpLayer::new())                    // 先追踪
        .layer(tower::timeout::TimeoutLayer::new(duration))  // 后超时
        .service(service)
}
```

**使用**:

```rust
use tower::ServiceExt;

let service = timeout_with_tracing(
    my_service,
    Duration::from_secs(30),
);

// 如果超时,Span 会记录 timeout 事件
```

### 2. 限流中间件 + OTLP

```rust
// src/middleware/rate_limit.rs
use tower::limit::RateLimit;
use tower::ServiceBuilder;
use std::time::Duration;
use crate::tower_otlp::OtlpLayer;

/// 限流中间件 (带 OTLP 追踪)
pub fn rate_limit_with_tracing<S>(
    service: S,
    num: u64,
    per: Duration,
) -> impl Service<
    Request,
    Response = S::Response,
    Error = S::Error,
>
where
    S: Service<Request> + Send + 'static,
{
    ServiceBuilder::new()
        .layer(OtlpLayer::new())
        .layer(tower::limit::RateLimitLayer::new(num, per))
        .service(service)
}
```

### 3. 重试中间件 + OTLP

```rust
// src/middleware/retry.rs
use tower::retry::{Retry, RetryLayer, Policy};
use tower::ServiceBuilder;
use std::task::{Context, Poll};
use crate::tower_otlp::OtlpLayer;

/// 重试策略
#[derive(Clone)]
pub struct RetryPolicy {
    max_retries: usize,
}

impl<Req, Res, E> Policy<Req, Res, E> for RetryPolicy
where
    Req: Clone,
{
    type Future = futures_util::future::Ready<Self>;
    
    fn retry(&self, _req: &Req, result: Result<&Res, &E>) -> Option<Self::Future> {
        match result {
            Ok(_) => None,  // 成功,不重试
            Err(_) if self.max_retries > 0 => {
                // 重试 (减少次数)
                Some(futures_util::future::ready(RetryPolicy {
                    max_retries: self.max_retries - 1,
                }))
            }
            Err(_) => None,  // 达到最大重试次数
        }
    }
    
    fn clone_request(&self, req: &Req) -> Option<Req> {
        Some(req.clone())
    }
}

/// 重试中间件 (带 OTLP 追踪)
pub fn retry_with_tracing<S>(
    service: S,
    max_retries: usize,
) -> Retry<RetryPolicy, S>
where
    S: Service<Request> + Clone,
    Request: Clone,
{
    let policy = RetryPolicy { max_retries };
    
    // OTLP Layer 会自动记录每次重试
    ServiceBuilder::new()
        .layer(OtlpLayer::new())
        .layer(RetryLayer::new(policy))
        .service(service)
}
```

---

## 📊 性能优化

### 1. 零分配优化

```rust
// 使用 &mut self 避免克隆
impl<S, Request> Service<Request> for OtlpService<S>
where
    S: Service<Request>,
{
    fn call(&mut self, req: Request) -> Self::Future {
        // ✅ 借用 self,无需克隆
        let fut = self.inner.call(req);
        
        Box::pin(async move {
            // 异步执行
            fut.await
        })
    }
}
```

### 2. Span 采样

```rust
// src/tower_otlp/sampling.rs
use opentelemetry::trace::{TraceContextExt, Sampler, SamplingResult};

/// 自定义采样器 (1% 采样)
pub struct CustomSampler;

impl Sampler for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 1% 采样
        if trace_id.to_bytes()[0] % 100 == 0 {
            SamplingResult {
                decision: opentelemetry::trace::SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: opentelemetry::trace::SamplingDecision::Drop,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        }
    }
}
```

---

## 🧪 测试策略

### 单元测试

```rust
// tests/tower_otlp_test.rs
use tower::{Service, ServiceExt};
use tower_otlp::OtlpLayer;

#[tokio::test]
async fn test_otlp_layer() {
    // Mock Service
    let service = tower::service_fn(|req: String| async move {
        Ok::<_, std::io::Error>(format!("Response: {}", req))
    });
    
    // 包装 OTLP Layer
    let mut service = OtlpLayer::new().layer(service);
    
    // 调用
    let response = service
        .ready()
        .await
        .unwrap()
        .call("test".to_string())
        .await
        .unwrap();
    
    assert_eq!(response, "Response: test");
}
```

---

## 🚀 生产部署

### Cargo.toml

```toml
[package]
name = "tower-otlp-example"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Tower 核心
tower = "0.5"
tower-http = "0.6"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# Async Runtime
tokio = { version = "1.41", features = ["full"] }
futures-util = "0.3"

# HTTP (可选)
axum = { version = "0.7", optional = true }
hyper = { version = "1.5", optional = true }
http = "1.1"

# gRPC (可选)
tonic = { version = "0.12", optional = true }
prost = { version = "0.13", optional = true }

[features]
default = []
axum-support = ["axum"]
tonic-support = ["tonic", "prost"]
hyper-support = ["hyper"]
```

### 完整示例应用

```rust
// src/main.rs
use axum::{Router, routing::get, Json};
use tower::ServiceBuilder;
use tower_http::timeout::TimeoutLayer;
use tower_http::limit::RateLimitLayer;
use std::time::Duration;
use tracing::info;

mod tower_otlp;
use tower_otlp::OtlpLayer;

#[tokio::main]
async fn main() {
    // 初始化 OTLP
    init_otlp().unwrap();
    
    info!("Starting Tower OTLP example on http://0.0.0.0:8080");
    
    // 构建应用 (中间件从下往上执行)
    let app = Router::new()
        .route("/api/users", get(list_users))
        .route("/health", get(health_check))
        .layer(
            ServiceBuilder::new()
                // 1. 最外层: OTLP 追踪
                .layer(OtlpLayer::new())
                // 2. 超时控制
                .layer(TimeoutLayer::new(Duration::from_secs(30)))
                // 3. 限流控制
                .layer(RateLimitLayer::new(100, Duration::from_secs(1)))
        );
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}

async fn list_users() -> Json<Vec<String>> {
    info!("Listing users");
    Json(vec!["Alice".to_string(), "Bob".to_string()])
}

async fn health_check() -> &'static str {
    "OK"
}

fn init_otlp() -> anyhow::Result<()> {
    use opentelemetry::trace::TracerProvider;
    use opentelemetry_sdk::trace::{self, Sampler};
    use opentelemetry_otlp::WithExportConfig;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint)
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "tower-otlp-example"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info,tower=debug"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer.tracer("tower-otlp")))
        .init();
    
    info!("OTLP initialized");
    Ok(())
}
```

---

## ✅ 最佳实践

### Tower 设计

1. **Layer 优于直接包装** ✅

   ```rust
   // ✅ Good: 使用 Layer
   ServiceBuilder::new()
       .layer(OtlpLayer::new())
       .service(my_service)
   
   // ❌ Bad: 直接包装
   OtlpService::new(my_service)
   ```

2. **中间件顺序** ✅

   ```rust
   // 执行顺序: 从下往上
   ServiceBuilder::new()
       .layer(Layer3)  // 最后执行
       .layer(Layer2)
       .layer(Layer1)  // 最先执行
       .service(service)
   ```

3. **避免过度包装** ✅
   - 每层包装都有微小开销
   - 合并相似功能的 Layer

### OTLP 集成

1. **追踪传播** ✅
   - 提取上游 Trace Context (W3C)
   - 注入下游 Trace Context

2. **Span 层次** ✅

   ```rust
   Root Span (HTTP Request)
     ├─ Child Span (Business Logic)
     │   ├─ Grand Child (Database)
     │   └─ Grand Child (External API)
     └─ Sibling Span (Response Processing)
   ```

3. **属性记录** ✅
   - `otel.kind` (Server/Client/Internal)
   - `http.method`, `http.status_code`
   - `duration_ms`, `error`

### 性能优化

1. **采样策略** ✅
   - 生产环境 1%-10% 采样
   - 错误请求 100% 采样

2. **异步优化** ✅
   - 使用 `Box::pin` 包装 Future
   - 避免阻塞 `poll_ready`

3. **零分配** ✅
   - 借用而非克隆
   - 复用 Buffer

---

**🏗️ Tower - 构建可组合的异步服务中间件！**

**下一篇**: `Tonic gRPC OTLP 完整集成指南` (Week 2)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**Tower**: 0.5.1  
**OpenTelemetry**: 0.31.0
