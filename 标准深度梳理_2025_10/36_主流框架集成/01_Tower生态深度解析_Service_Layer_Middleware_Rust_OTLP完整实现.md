# Tower 生态深度解析 - Service, Layer, Middleware - Rust 1.90 + OTLP 完整实现

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90  
> **Tower 版本**: 0.5  
> **OpenTelemetry**: 0.31.0  
> **对标标准**: Rust Async Ecosystem, Tokio Stack, CNCF Observability

---

## 📑 目录

- [Tower 生态深度解析 - Service, Layer, Middleware - Rust 1.90 + OTLP 完整实现](#tower-生态深度解析---service-layer-middleware---rust-190--otlp-完整实现)
  - [📑 目录](#-目录)
  - [1. Tower 生态概述](#1-tower-生态概述)
    - [1.1 什么是 Tower?](#11-什么是-tower)
    - [1.2 Tower 核心概念](#12-tower-核心概念)
    - [1.3 为什么使用 Tower?](#13-为什么使用-tower)
  - [2. 核心抽象: Service Trait](#2-核心抽象-service-trait)
    - [2.1 Service Trait 深度解析](#21-service-trait-深度解析)
    - [2.2 实现自定义 Service](#22-实现自定义-service)
    - [2.3 ServiceExt Trait (扩展方法)](#23-serviceext-trait-扩展方法)
  - [3. Layer 模式详解](#3-layer-模式详解)
    - [3.1 Layer Trait 原理](#31-layer-trait-原理)
    - [3.2 实现自定义 Layer](#32-实现自定义-layer)
    - [3.3 ServiceBuilder (组合多个 Layer)](#33-servicebuilder-组合多个-layer)
  - [4. 中间件开发](#4-中间件开发)
    - [4.1 Timeout 中间件](#41-timeout-中间件)
    - [4.2 Retry 中间件](#42-retry-中间件)
  - [5. Tower-HTTP 深度应用](#5-tower-http-深度应用)
    - [5.1 Tower-HTTP 中间件](#51-tower-http-中间件)
  - [6. OTLP 追踪集成](#6-otlp-追踪集成)
    - [6.1 OTLP Tracing Layer](#61-otlp-tracing-layer)
    - [6.2 完整的 OTLP 配置](#62-完整的-otlp-配置)
  - [7. 完整示例: HTTP 服务栈](#7-完整示例-http-服务栈)
    - [7.1 项目结构](#71-项目结构)
    - [7.2 完整的 HTTP 服务](#72-完整的-http-服务)
  - [8. 性能优化与最佳实践](#8-性能优化与最佳实践)
    - [8.1 最佳实践](#81-最佳实践)
    - [8.2 性能优化](#82-性能优化)
  - [9. 部署与监控](#9-部署与监控)
    - [9.1 Docker Compose 部署](#91-docker-compose-部署)
    - [9.2 Prometheus Metrics](#92-prometheus-metrics)
  - [10. 与 Axum 集成](#10-与-axum-集成)
    - [10.1 Axum + Tower 完整示例](#101-axum--tower-完整示例)
  - [📚 参考资料](#-参考资料)
  - [✅ 总结](#-总结)
    - [Tower 核心价值](#tower-核心价值)

---

## 1. Tower 生态概述

### 1.1 什么是 Tower?

**Tower** 是 Rust 异步生态的核心库,提供了模块化、可组合的异步服务抽象。它是 Tokio 生态的重要组成部分。

```text
┌─────────────────────────────────────────────────────────────┐
│              Tower 生态架构                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────┐                    │
│  │         Application Code            │                    │
│  │      (Axum, Tonic, Hyper)           │                    │
│  └─────────────┬───────────────────────┘                    │
│                │                                            │
│  ┌─────────────▼───────────────────────┐                    │
│  │      Tower Middleware Stack         │                    │
│  │  ┌───────────────────────────────┐  │                    │
│  │  │  Timeout (5s)                 │  │                    │
│  │  └──────────┬────────────────────┘  │                    │
│  │  ┌──────────▼────────────────────┐  │                    │
│  │  │  RateLimit (100 req/s)        │  │                    │
│  │  └──────────┬────────────────────┘  │                    │
│  │  ┌──────────▼────────────────────┐  │                    │
│  │  │  Retry (3 attempts)           │  │                    │
│  │  └──────────┬────────────────────┘  │                    │
│  │  ┌──────────▼────────────────────┐  │                    │
│  │  │  Tracing (OTLP)               │  │                    │
│  │  └──────────┬────────────────────┘  │                    │
│  └─────────────┼───────────────────────┘                    │
│                │                                            │
│  ┌─────────────▼───────────────────────┐                    │
│  │      Tower Service Trait            │                    │
│  │   fn call(&mut self, Request)       │                    │
│  │     -> Future<Output = Response>    │                    │
│  └─────────────┬───────────────────────┘                    │
│                │                                            │
│  ┌─────────────▼───────────────────────┐                    │
│  │      Underlying Service             │                    │
│  │   (HTTP Client, gRPC, Database)     │                    │
│  └─────────────────────────────────────┘                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 Tower 核心概念

```rust
/// Tower 的三个核心抽象
pub mod tower_concepts {
    /// 1. Service Trait
    /// 定义了一个异步服务的统一接口
    pub trait Service<Request> {
        type Response;
        type Error;
        type Future: Future<Output = Result<Self::Response, Self::Error>>;

        fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
        fn call(&mut self, req: Request) -> Self::Future;
    }

    /// 2. Layer Trait
    /// 用于包装 Service,添加额外功能 (类似装饰器模式)
    pub trait Layer<S> {
        type Service;
        fn layer(&self, inner: S) -> Self::Service;
    }

    /// 3. MakeService
    /// 用于创建 Service 实例 (每个连接一个 Service)
    pub trait MakeService<Target, Request> {
        type Response;
        type Error;
        type Service: Service<Request, Response = Self::Response, Error = Self::Error>;
        type MakeError;
        type Future: Future<Output = Result<Self::Service, Self::MakeError>>;

        fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::MakeError>>;
        fn make_service(&mut self, target: Target) -> Self::Future;
    }
}
```

### 1.3 为什么使用 Tower?

| 特性 | 说明 | 优势 |
|------|------|------|
| **模块化** | 每个中间件是独立的 `Layer` | 易于组合和重用 |
| **类型安全** | 编译期验证中间件顺序和类型 | 避免运行时错误 |
| **零成本抽象** | 编译器内联优化 | 性能与手写代码相当 |
| **生态完整** | Axum, Tonic, Hyper 均基于 Tower | 学习一次,到处使用 |
| **异步原生** | 完整的 `async/await` 支持 | 高并发性能 |

---

## 2. 核心抽象: Service Trait

### 2.1 Service Trait 深度解析

```rust
// Tower Service Trait 完整定义
use std::task::{Context, Poll};
use std::future::Future;

pub trait Service<Request> {
    /// 响应类型
    type Response;

    /// 错误类型
    type Error;

    /// 异步 Future 类型
    type Future: Future<Output = Result<Self::Response, Self::Error>>;

    /// 检查服务是否准备好接受请求
    /// • 用于背压 (backpressure) 控制
    /// • 返回 Poll::Ready(Ok(())) 表示可以接受请求
    /// • 返回 Poll::Pending 表示服务繁忙,需要稍后重试
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;

    /// 处理请求
    /// • 只有在 poll_ready 返回 Ready 后才应该调用
    /// • 返回一个 Future,异步处理请求
    fn call(&mut self, req: Request) -> Self::Future;
}
```

### 2.2 实现自定义 Service

```rust
// examples/custom_service.rs
use tower::Service;
use std::task::{Context, Poll};
use std::future::Future;
use std::pin::Pin;

/// 简单的 Echo Service (返回请求内容)
#[derive(Clone)]
pub struct EchoService;

impl Service<String> for EchoService {
    type Response = String;
    type Error = std::io::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        // 始终准备就绪
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: String) -> Self::Future {
        Box::pin(async move {
            // 异步处理 (示例: 延迟 100ms)
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
            Ok(format!("Echo: {}", req))
        })
    }
}

#[tokio::main]
async fn main() {
    let mut service = EchoService;

    // 使用 Service
    let response = service.call("Hello Tower!".to_string()).await.unwrap();
    println!("{}", response); // 输出: Echo: Hello Tower!
}
```

### 2.3 ServiceExt Trait (扩展方法)

```rust
// Tower 提供的 ServiceExt 扩展方法
use tower::ServiceExt;

#[tokio::main]
async fn main() {
    let mut service = EchoService;

    // 1. ready() - 等待服务就绪
    let ready_service = service.ready().await.unwrap();

    // 2. oneshot() - 调用一次并消费 Service
    let response = service.oneshot("Hello".to_string()).await.unwrap();

    // 3. call_all() - 批量调用
    let requests = vec!["a".to_string(), "b".to_string()];
    let responses = service.call_all(futures::stream::iter(requests)).await;

    // 4. map_response() - 转换响应
    let mapped_service = service.map_response(|response: String| response.to_uppercase());

    // 5. map_err() - 转换错误
    let error_mapped_service = service.map_err(|e| format!("Error: {}", e));

    // 6. and_then() - 链式调用
    let chained_service = service.and_then(|response| async move {
        Ok(format!("Processed: {}", response))
    });
}
```

---

## 3. Layer 模式详解

### 3.1 Layer Trait 原理

```rust
// Layer Trait 定义
pub trait Layer<S> {
    /// 包装后的 Service 类型
    type Service;

    /// 包装内部 Service,返回新的 Service
    fn layer(&self, inner: S) -> Self::Service;
}
```

**Layer 模式 = 装饰器模式 (Decorator Pattern)**-

```text
┌─────────────────────────────────────────────────────────────┐
│              Layer 包装示意图                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌───────────────────────────────────────────┐              │
│  │         Timeout Layer                     │              │
│  │  ┌─────────────────────────────────────┐  │              │
│  │  │      RateLimit Layer                │  │              │
│  │  │  ┌───────────────────────────────┐  │  │              │
│  │  │  │    Tracing Layer              │  │  │              │
│  │  │  │  ┌─────────────────────────┐  │  │  │              │
│  │  │  │  │  Original Service       │  │  │  │              │
│  │  │  │  │  (HTTP Handler)         │  │  │  │              │
│  │  │  │  └─────────────────────────┘  │  │  │              │
│  │  │  └───────────────────────────────┘  │  │              │
│  │  └─────────────────────────────────────┘  │              │
│  └───────────────────────────────────────────┘              │
│                                                             │
│  请求流: Client → Timeout → RateLimit → Tracing → Handler   │
│  响应流: Handler → Tracing → RateLimit → Timeout → Client   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 实现自定义 Layer

```rust
// examples/custom_layer.rs
use tower::{Layer, Service};
use std::task::{Context, Poll};
use std::future::Future;
use std::pin::Pin;

/// 日志 Layer (记录请求和响应)
#[derive(Clone)]
pub struct LogLayer;

impl<S> Layer<S> for LogLayer {
    type Service = LogService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        LogService { inner }
    }
}

/// 日志 Service (包装内部 Service)
#[derive(Clone)]
pub struct LogService<S> {
    inner: S,
}

impl<S, Request> Service<Request> for LogService<S>
where
    S: Service<Request>,
    Request: std::fmt::Debug,
    S::Response: std::fmt::Debug,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = LogFuture<S::Future>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request) -> Self::Future {
        println!("📥 Request: {:?}", req);
        let future = self.inner.call(req);
        LogFuture { future }
    }
}

/// 日志 Future (包装内部 Future)
pin_project_lite::pin_project! {
    pub struct LogFuture<F> {
        #[pin]
        future: F,
    }
}

impl<F, T, E> Future for LogFuture<F>
where
    F: Future<Output = Result<T, E>>,
    T: std::fmt::Debug,
{
    type Output = Result<T, E>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        match this.future.poll(cx) {
            Poll::Ready(Ok(response)) => {
                println!("📤 Response: {:?}", response);
                Poll::Ready(Ok(response))
            }
            Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
            Poll::Pending => Poll::Pending,
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    use tower::ServiceBuilder;

    let service = ServiceBuilder::new()
        .layer(LogLayer) // 添加日志层
        .service(EchoService);

    let response = service.oneshot("Hello".to_string()).await.unwrap();
    // 输出:
    // 📥 Request: "Hello"
    // 📤 Response: "Echo: Hello"
}
```

### 3.3 ServiceBuilder (组合多个 Layer)

```rust
// ServiceBuilder 链式组合
use tower::ServiceBuilder;
use tower::timeout::TimeoutLayer;
use tower::limit::RateLimitLayer;
use std::time::Duration;

let service = ServiceBuilder::new()
    // Layer 从上到下应用 (洋葱模型)
    .layer(TimeoutLayer::new(Duration::from_secs(5)))     // 最外层
    .layer(RateLimitLayer::new(100, Duration::from_secs(1))) // 中间层
    .layer(LogLayer)                                      // 内层
    .service(EchoService);                                // 核心服务

// 请求流: Request → Timeout → RateLimit → Log → EchoService
// 响应流: EchoService → Log → RateLimit → Timeout → Response
```

---

## 4. 中间件开发

### 4.1 Timeout 中间件

```rust
// src/middleware/timeout.rs
use tower::{Layer, Service};
use std::task::{Context, Poll};
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use tokio::time::Sleep;

/// Timeout Layer
#[derive(Clone)]
pub struct TimeoutLayer {
    timeout: Duration,
}

impl TimeoutLayer {
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }
}

impl<S> Layer<S> for TimeoutLayer {
    type Service = TimeoutService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        TimeoutService {
            inner,
            timeout: self.timeout,
        }
    }
}

/// Timeout Service
#[derive(Clone)]
pub struct TimeoutService<S> {
    inner: S,
    timeout: Duration,
}

impl<S, Request> Service<Request> for TimeoutService<S>
where
    S: Service<Request>,
    S::Error: From<TimeoutError>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = TimeoutFuture<S::Future>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request) -> Self::Future {
        let future = self.inner.call(req);
        let sleep = tokio::time::sleep(self.timeout);

        TimeoutFuture { future, sleep }
    }
}

pin_project_lite::pin_project! {
    pub struct TimeoutFuture<F> {
        #[pin]
        future: F,
        #[pin]
        sleep: Sleep,
    }
}

impl<F, T, E> Future for TimeoutFuture<F>
where
    F: Future<Output = Result<T, E>>,
    E: From<TimeoutError>,
{
    type Output = Result<T, E>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        // 先检查内部 Future
        if let Poll::Ready(result) = this.future.poll(cx) {
            return Poll::Ready(result);
        }

        // 再检查超时
        match this.sleep.poll(cx) {
            Poll::Ready(_) => Poll::Ready(Err(TimeoutError.into())),
            Poll::Pending => Poll::Pending,
        }
    }
}

#[derive(Debug)]
pub struct TimeoutError;

impl std::fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Request timeout")
    }
}

impl std::error::Error for TimeoutError {}
```

### 4.2 Retry 中间件

```rust
// src/middleware/retry.rs
use tower::{Layer, Service, retry::Policy};
use std::task::{Context, Poll};

/// Retry Layer
#[derive(Clone)]
pub struct RetryLayer<P> {
    policy: P,
}

impl<P: Clone> RetryLayer<P> {
    pub fn new(policy: P) -> Self {
        Self { policy }
    }
}

impl<P, S> Layer<S> for RetryLayer<P>
where
    P: Policy<S::Request, S::Response, S::Error> + Clone,
    S: Service,
{
    type Service = tower::retry::Retry<P, S>;

    fn layer(&self, inner: S) -> Self::Service {
        tower::retry::Retry::new(self.policy.clone(), inner)
    }
}

/// 重试策略: 固定次数重试
#[derive(Clone)]
pub struct FixedRetryPolicy {
    remaining_attempts: usize,
}

impl FixedRetryPolicy {
    pub fn new(max_attempts: usize) -> Self {
        Self {
            remaining_attempts: max_attempts,
        }
    }
}

impl<Req, Res, E> Policy<Req, Res, E> for FixedRetryPolicy
where
    Req: Clone,
{
    type Future = std::future::Ready<Self>;

    fn retry(&self, _req: &Req, result: Result<&Res, &E>) -> Option<Self::Future> {
        match result {
            Ok(_) => None, // 成功,不重试
            Err(_) if self.remaining_attempts > 0 => {
                // 失败且还有重试次数
                let policy = Self {
                    remaining_attempts: self.remaining_attempts - 1,
                };
                Some(std::future::ready(policy))
            }
            Err(_) => None, // 失败且无重试次数
        }
    }

    fn clone_request(&self, req: &Req) -> Option<Req> {
        Some(req.clone())
    }
}
```

---

## 5. Tower-HTTP 深度应用

### 5.1 Tower-HTTP 中间件

```toml
# Cargo.toml
[dependencies]
tower-http = { version = "0.6", features = [
    "trace",         # 追踪中间件
    "cors",          # CORS 中间件
    "compression-gzip", # Gzip 压缩
    "request-id",    # 请求 ID
    "timeout",       # 超时
    "limit",         # 限流
] }
```

```rust
// 使用 tower-http 中间件
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
    request_id::{MakeRequestId, RequestId, PropagateRequestIdLayer, SetRequestIdLayer},
    timeout::TimeoutLayer,
    limit::RequestBodyLimitLayer,
};
use tower::ServiceBuilder;
use axum::Router;
use std::time::Duration;

fn create_middleware_stack<S>(service: S) -> impl Service
where
    S: Service<Request<Body>> + Clone + Send + 'static,
{
    ServiceBuilder::new()
        // 1. 请求 ID 生成
        .layer(SetRequestIdLayer::x_request_id(MakeRequestUuid))
        .layer(PropagateRequestIdLayer::x_request_id())
        
        // 2. 追踪
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(|request: &Request<Body>| {
                    let request_id = request
                        .headers()
                        .get("x-request-id")
                        .and_then(|v| v.to_str().ok())
                        .unwrap_or("unknown");

                    tracing::info_span!(
                        "http_request",
                        method = %request.method(),
                        uri = %request.uri(),
                        request_id = %request_id,
                    )
                })
                .on_response(|response: &Response<_>, latency: Duration, _span: &Span| {
                    tracing::info!(
                        status = %response.status(),
                        latency_ms = %latency.as_millis(),
                        "response"
                    );
                })
        )
        
        // 3. CORS
        .layer(
            CorsLayer::new()
                .allow_origin(tower_http::cors::Any)
                .allow_methods(vec![Method::GET, Method::POST])
                .allow_headers(vec![header::CONTENT_TYPE])
        )
        
        // 4. Gzip 压缩
        .layer(CompressionLayer::new())
        
        // 5. 请求体大小限制 (10MB)
        .layer(RequestBodyLimitLayer::new(10 * 1024 * 1024))
        
        // 6. 超时
        .layer(TimeoutLayer::new(Duration::from_secs(30)))
        
        .service(service)
}

// UUID 请求 ID 生成器
#[derive(Clone)]
struct MakeRequestUuid;

impl MakeRequestId for MakeRequestUuid {
    fn make_request_id<B>(&mut self, _request: &Request<B>) -> Option<RequestId> {
        let uuid = uuid::Uuid::new_v4().to_string();
        Some(RequestId::new(uuid.parse().unwrap()))
    }
}
```

---

## 6. OTLP 追踪集成

### 6.1 OTLP Tracing Layer

```rust
// src/middleware/otlp_tracing.rs
use tower::{Layer, Service};
use tracing::{info_span, Span};
use opentelemetry::trace::{Tracer, SpanKind};
use std::task::{Context, Poll};

/// OTLP Tracing Layer
#[derive(Clone)]
pub struct OtlpTracingLayer;

impl<S> Layer<S> for OtlpTracingLayer {
    type Service = OtlpTracingService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        OtlpTracingService { inner }
    }
}

pub struct OtlpTracingService<S> {
    inner: S,
}

impl<S, Request> Service<Request> for OtlpTracingService<S>
where
    S: Service<Request>,
    Request: std::fmt::Debug,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = tracing::instrument::Instrumented<S::Future>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request) -> Self::Future {
        let span = info_span!(
            "tower_service.call",
            otel.kind = "server",
            service.name = "tower-service",
        );

        self.inner.call(req).instrument(span)
    }
}
```

### 6.2 完整的 OTLP 配置

```rust
// src/telemetry/mod.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{RandomIdGenerator, Sampler, Tracer},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_telemetry(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    global::set_tracer_provider(tracer.provider().unwrap());

    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

---

## 7. 完整示例: HTTP 服务栈

### 7.1 项目结构

```text
tower-http-service/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── middleware/
│   │   ├── mod.rs
│   │   ├── timeout.rs
│   │   ├── retry.rs
│   │   └── otlp_tracing.rs
│   ├── handlers/
│   │   └── mod.rs
│   └── telemetry/
│       └── mod.rs
└── docker-compose.yml
```

### 7.2 完整的 HTTP 服务

```rust
// src/main.rs
use axum::{routing::get, Router, response::IntoResponse};
use tower::ServiceBuilder;
use tower_http::{trace::TraceLayer, cors::CorsLayer};
use std::time::Duration;

mod middleware;
mod handlers;
mod telemetry;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OTLP
    telemetry::init_telemetry("tower-http-service")?;

    // 2. 创建路由
    let app = Router::new()
        .route("/", get(handlers::index))
        .route("/slow", get(handlers::slow_handler))
        .route("/error", get(handlers::error_handler))
        // 3. 应用中间件栈
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CorsLayer::permissive())
                .layer(middleware::timeout::TimeoutLayer::new(Duration::from_secs(5)))
                .layer(middleware::otlp_tracing::OtlpTracingLayer)
        );

    // 4. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    println!("🚀 Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;

    Ok(())
}
```

```rust
// src/handlers/mod.rs
use axum::response::IntoResponse;
use tracing::info;

pub async fn index() -> impl IntoResponse {
    info!("Handling index request");
    "Hello Tower!"
}

pub async fn slow_handler() -> impl IntoResponse {
    info!("Handling slow request");
    tokio::time::sleep(std::time::Duration::from_secs(2)).await;
    "Slow response"
}

pub async fn error_handler() -> impl IntoResponse {
    info!("Handling error request");
    (axum::http::StatusCode::INTERNAL_SERVER_ERROR, "Error!")
}
```

---

## 8. 性能优化与最佳实践

### 8.1 最佳实践

```rust
/// ✅ DO: Tower 最佳实践

// 1. 使用 ServiceBuilder 链式组合
// ✅ 正确: 清晰的中间件顺序
let service = ServiceBuilder::new()
    .layer(TimeoutLayer::new(Duration::from_secs(5)))
    .layer(RateLimitLayer::new(100, Duration::from_secs(1)))
    .layer(TraceLayer::new_for_http())
    .service(handler);

// ❌ 错误: 手动嵌套 (难以维护)
let service = TimeoutService::new(
    RateLimitService::new(
        TraceService::new(handler)
    )
);


// 2. 实现 Clone for Service (支持多线程)
// ✅ 正确
#[derive(Clone)]
pub struct MyService {
    inner: Arc<SomeInnerState>,
}


// 3. 使用 BoxCloneService 擦除类型
// ✅ 正确: 简化复杂类型签名
use tower::util::BoxCloneService;

pub type HttpService = BoxCloneService<
    Request<Body>,
    Response<Body>,
    Box<dyn std::error::Error + Send + Sync>,
>;


// 4. 合理使用 poll_ready (背压控制)
// ✅ 正确
impl<Request> Service<Request> for MyService {
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        // 检查内部资源是否可用
        if self.connection_pool.is_full() {
            return Poll::Pending; // 背压: 告知调用方稍后重试
        }
        Poll::Ready(Ok(()))
    }
}
```

### 8.2 性能优化

```rust
/// 性能优化技巧

// 1. 避免不必要的 Box<dyn Future>
// ❌ 慢: Box allocation
type Future = Pin<Box<dyn Future<Output = Result<T, E>> + Send>>;

// ✅ 快: 使用具体类型 (编译器内联)
type Future = impl Future<Output = Result<T, E>>;


// 2. 使用 Buffer Layer 减少 poll_ready 调用
use tower::buffer::BufferLayer;

let service = ServiceBuilder::new()
    .layer(BufferLayer::new(1024)) // 缓冲 1024 个请求
    .service(expensive_service);


// 3. 使用 ConcurrencyLimit 控制并发
use tower::limit::ConcurrencyLimitLayer;

let service = ServiceBuilder::new()
    .layer(ConcurrencyLimitLayer::new(100)) // 最多 100 个并发请求
    .service(handler);
```

---

## 9. 部署与监控

### 9.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  tower-service:
    build: .
    ports:
      - "3000:3000"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://jaeger:4317
    depends_on:
      - jaeger

  jaeger:
    image: jaegertracing/all-in-one:1.60
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC
```

### 9.2 Prometheus Metrics

```rust
// src/middleware/metrics.rs
use metrics::{counter, histogram};
use tower::{Layer, Service};

#[derive(Clone)]
pub struct MetricsLayer;

impl<S> Layer<S> for MetricsLayer {
    type Service = MetricsService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        MetricsService { inner }
    }
}

pub struct MetricsService<S> {
    inner: S,
}

impl<S, Request> Service<Request> for MetricsService<S>
where
    S: Service<Request>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = /* ... */;

    fn call(&mut self, req: Request) -> Self::Future {
        counter!("tower_requests_total").increment(1);
        let start = std::time::Instant::now();

        let future = self.inner.call(req);

        async move {
            let result = future.await;
            let latency = start.elapsed().as_secs_f64();
            histogram!("tower_request_duration_seconds").record(latency);
            result
        }
    }
}
```

---

## 10. 与 Axum 集成

### 10.1 Axum + Tower 完整示例

```rust
// Axum 原生支持 Tower 中间件
use axum::{routing::get, Router};
use tower::ServiceBuilder;
use tower_http::trace::TraceLayer;

let app = Router::new()
    .route("/", get(|| async { "Hello!" }))
    .layer(
        ServiceBuilder::new()
            .layer(TraceLayer::new_for_http())
            .layer(TimeoutLayer::new(Duration::from_secs(10)))
    );
```

---

## 📚 参考资料

1. **Tower Documentation**
   - <https://docs.rs/tower/>

2. **Tokio Tutorial**
   - <https://tokio.rs/tokio/tutorial>

3. **tower-http**
   - <https://docs.rs/tower-http/>

---

## ✅ 总结

### Tower 核心价值

1. **模块化**: 可组合的中间件
2. **类型安全**: 编译期验证
3. **零成本抽象**: 高性能
4. **生态完整**: Axum/Tonic 基础

---

**文档状态**: ✅ 生产就绪  
**最后更新**: 2025-10-11  
**维护者**: OTLP Rust Team
