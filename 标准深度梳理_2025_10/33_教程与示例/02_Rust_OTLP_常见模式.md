# 🎯 Rust OTLP 常见模式与最佳实践

> **目标读者**: Rust OTLP 中级开发者  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🎯 Rust OTLP 常见模式与最佳实践](#-rust-otlp-常见模式与最佳实践)
  - [📋 目录](#-目录)
  - [1. 初始化模式](#1-初始化模式)
    - [1.1 单例 TracerProvider 模式](#11-单例-tracerprovider-模式)
    - [1.2 延迟初始化模式](#12-延迟初始化模式)
    - [1.3 多环境配置模式](#13-多环境配置模式)
  - [2. Span 创建模式](#2-span-创建模式)
    - [2.1 作用域 Span 模式](#21-作用域-span-模式)
    - [2.2 异步函数追踪模式](#22-异步函数追踪模式)
    - [2.3 条件追踪模式](#23-条件追踪模式)
  - [3. 错误处理模式](#3-错误处理模式)
    - [3.1 Result 集成模式](#31-result-集成模式)
    - [3.2 错误传播模式](#32-错误传播模式)
    - [3.3 Panic 捕获模式](#33-panic-捕获模式)
  - [4. 上下文传播模式](#4-上下文传播模式)
    - [4.1 HTTP 客户端传播模式](#41-http-客户端传播模式)
    - [4.2 HTTP 服务端提取模式](#42-http-服务端提取模式)
    - [4.3 跨线程传播模式](#43-跨线程传播模式)
  - [5. 中间件集成模式](#5-中间件集成模式)
    - [5.1 Axum 中间件模式](#51-axum-中间件模式)
    - [5.2 Tonic 拦截器模式](#52-tonic-拦截器模式)
    - [5.3 Tower Layer 模式](#53-tower-layer-模式)
  - [6. Metrics 模式](#6-metrics-模式)
    - [6.1 静态 Metrics 模式](#61-静态-metrics-模式)
    - [6.2 动态 Metrics 模式](#62-动态-metrics-模式)
    - [6.3 Histogram 桶配置模式](#63-histogram-桶配置模式)
  - [7. 批处理与性能优化模式](#7-批处理与性能优化模式)
    - [7.1 批量导出模式](#71-批量导出模式)
    - [7.2 采样策略模式](#72-采样策略模式)
    - [7.3 属性缓存模式](#73-属性缓存模式)
  - [8. 测试模式](#8-测试模式)
    - [8.1 Mock Exporter 模式](#81-mock-exporter-模式)
    - [8.2 测试断言模式](#82-测试断言模式)
    - [8.3 集成测试模式](#83-集成测试模式)
  - [9. 生产部署模式](#9-生产部署模式)
    - [9.1 优雅关闭模式](#91-优雅关闭模式)
    - [9.2 健康检查模式](#92-健康检查模式)
    - [9.3 配置热重载模式](#93-配置热重载模式)
  - [10. 高级模式](#10-高级模式)
    - [10.1 自定义 Processor 模式](#101-自定义-processor-模式)
    - [10.2 多后端导出模式](#102-多后端导出模式)
    - [10.3 动态采样模式](#103-动态采样模式)
  - [🔗 参考资源](#-参考资源)

---

## 1. 初始化模式

### 1.1 单例 TracerProvider 模式

**问题**: 需要在整个应用中共享同一个 TracerProvider 实例。

**解决方案**: 使用 `OnceCell` 或 `lazy_static` 实现单例模式。

```rust
use opentelemetry::global;
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_otlp::WithExportConfig;
use std::sync::OnceLock;

static TRACER_PROVIDER: OnceLock<SdkTracerProvider> = OnceLock::new();

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    let provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    TRACER_PROVIDER.set(provider.clone()).ok();
    global::set_tracer_provider(provider);
    
    Ok(())
}

pub fn get_tracer() -> opentelemetry::trace::BoxedTracer {
    global::tracer("my-service")
}

// 使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    let tracer = get_tracer();
    let span = tracer.start("main");
    // 业务逻辑
    drop(span);
    
    Ok(())
}
```

**优点**:

- ✅ 全局单一实例
- ✅ 线程安全
- ✅ 延迟初始化

---

### 1.2 延迟初始化模式

**问题**: 需要在运行时动态配置 TracerProvider。

**解决方案**: 使用 Builder 模式和配置结构。

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{Config, TracerProvider};
use opentelemetry_otlp::WithExportConfig;

#[derive(Clone)]
pub struct TelemetryConfig {
    pub service_name: String,
    pub otlp_endpoint: String,
    pub sample_rate: f64,
}

impl TelemetryConfig {
    pub fn from_env() -> Self {
        Self {
            service_name: std::env::var("OTEL_SERVICE_NAME")
                .unwrap_or_else(|_| "my-service".to_string()),
            otlp_endpoint: std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            sample_rate: std::env::var("OTEL_TRACES_SAMPLER_ARG")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1.0),
        }
    }
}

pub struct TelemetryBuilder {
    config: TelemetryConfig,
}

impl TelemetryBuilder {
    pub fn new(config: TelemetryConfig) -> Self {
        Self { config }
    }

    pub fn build(self) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint(&self.config.otlp_endpoint)
            )
            .with_trace_config(
                Config::default()
                    .with_sampler(opentelemetry_sdk::trace::Sampler::TraceIdRatioBased(
                        self.config.sample_rate
                    ))
                    .with_resource(opentelemetry_sdk::Resource::new(vec![
                        opentelemetry::KeyValue::new("service.name", self.config.service_name.clone()),
                    ]))
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)?;

        global::set_tracer_provider(tracer);
        Ok(())
    }
}

// 使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = TelemetryConfig::from_env();
    TelemetryBuilder::new(config).build()?;
    
    Ok(())
}
```

---

### 1.3 多环境配置模式

**问题**: 不同环境（开发、测试、生产）需要不同的配置。

**解决方案**: 使用环境枚举和配置工厂。

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;

#[derive(Clone, Copy, Debug)]
pub enum Environment {
    Development,
    Staging,
    Production,
}

impl Environment {
    pub fn from_env() -> Self {
        match std::env::var("ENV").as_deref() {
            Ok("production") => Self::Production,
            Ok("staging") => Self::Staging,
            _ => Self::Development,
        }
    }
}

pub fn init_for_env(env: Environment) -> Result<(), Box<dyn std::error::Error>> {
    match env {
        Environment::Development => {
            // 开发环境：使用 stdout exporter
            let tracer = opentelemetry_stdout::new_pipeline()
                .install_simple();
            global::set_tracer_provider(tracer);
        }
        Environment::Staging => {
            // 测试环境：采样率 50%
            let tracer = opentelemetry_otlp::new_pipeline()
                .tracing()
                .with_trace_config(
                    opentelemetry_sdk::trace::Config::default()
                        .with_sampler(opentelemetry_sdk::trace::Sampler::TraceIdRatioBased(0.5))
                )
                .install_batch(opentelemetry_sdk::runtime::Tokio)?;
            global::set_tracer_provider(tracer);
        }
        Environment::Production => {
            // 生产环境：完整配置
            let tracer = opentelemetry_otlp::new_pipeline()
                .tracing()
                .with_trace_config(
                    opentelemetry_sdk::trace::Config::default()
                        .with_sampler(opentelemetry_sdk::trace::Sampler::ParentBased(
                            Box::new(opentelemetry_sdk::trace::Sampler::TraceIdRatioBased(0.1))
                        ))
                )
                .install_batch(opentelemetry_sdk::runtime::Tokio)?;
            global::set_tracer_provider(tracer);
        }
    }
    Ok(())
}
```

---

## 2. Span 创建模式

### 2.1 作用域 Span 模式

**问题**: 需要确保 Span 正确结束，即使发生错误。

**解决方案**: 使用 RAII 模式和作用域守卫。

```rust
use opentelemetry::trace::{Tracer, Span};

pub struct SpanGuard {
    span: opentelemetry::trace::BoxedSpan,
}

impl SpanGuard {
    pub fn new(tracer: &dyn Tracer, name: &str) -> Self {
        Self {
            span: tracer.start(name),
        }
    }

    pub fn span(&mut self) -> &mut opentelemetry::trace::BoxedSpan {
        &mut self.span
    }
}

impl Drop for SpanGuard {
    fn drop(&mut self) {
        self.span.end();
    }
}

// 使用
fn process_request(tracer: &dyn Tracer) -> Result<(), Box<dyn std::error::Error>> {
    let mut guard = SpanGuard::new(tracer, "process_request");
    
    guard.span().set_attribute(opentelemetry::KeyValue::new("user.id", 123));
    
    // 即使这里发生错误,Span 也会正确结束
    risky_operation()?;
    
    Ok(())
} // Span 自动结束
```

---

### 2.2 异步函数追踪模式

**问题**: 需要在异步函数中正确追踪 Span。

**解决方案**: 使用 `tracing` crate 的 `#[instrument]` 宏。

```rust
use tracing::instrument;
use opentelemetry::global;

#[instrument(skip(db))]
async fn get_user(db: &Database, user_id: u64) -> Result<User, Error> {
    tracing::info!("Fetching user");
    
    let user = db.query_user(user_id).await?;
    
    tracing::info!(username = %user.name, "User fetched successfully");
    
    Ok(user)
}

#[instrument(fields(http.method = "GET", http.route = "/users/{id}"))]
async fn handle_request(user_id: u64) -> Result<Response, Error> {
    let user = get_user(&database, user_id).await?;
    
    Ok(Response::json(user))
}
```

---

### 2.3 条件追踪模式

**问题**: 只在特定条件下创建 Span。

**解决方案**: 使用条件包装器。

```rust
use opentelemetry::trace::{Tracer, Span, SpanKind};

pub struct ConditionalSpan {
    span: Option<opentelemetry::trace::BoxedSpan>,
}

impl ConditionalSpan {
    pub fn new(tracer: &dyn Tracer, name: &str, should_trace: bool) -> Self {
        let span = if should_trace {
            Some(tracer.start(name))
        } else {
            None
        };
        
        Self { span }
    }

    pub fn set_attribute(&mut self, kv: opentelemetry::KeyValue) {
        if let Some(span) = &mut self.span {
            span.set_attribute(kv);
        }
    }

    pub fn record_error(&mut self, err: &dyn std::error::Error) {
        if let Some(span) = &mut self.span {
            span.record_error(err);
        }
    }
}

// 使用
fn process_item(tracer: &dyn Tracer, item: &Item, debug_mode: bool) {
    let mut span = ConditionalSpan::new(
        tracer,
        "process_item",
        debug_mode || item.is_important()
    );
    
    span.set_attribute(opentelemetry::KeyValue::new("item.id", item.id));
    
    // 处理逻辑
}
```

---

## 3. 错误处理模式

### 3.1 Result 集成模式

**问题**: 需要自动追踪错误到 Span。

**解决方案**: 使用 Result 扩展 trait。

```rust
use opentelemetry::trace::Span;

pub trait SpanResultExt<T, E> {
    fn record_err_to_span(self, span: &mut dyn Span) -> Result<T, E>;
}

impl<T, E: std::error::Error> SpanResultExt<T, E> for Result<T, E> {
    fn record_err_to_span(self, span: &mut dyn Span) -> Result<T, E> {
        if let Err(ref e) = self {
            span.record_error(e);
            span.set_status(opentelemetry::trace::Status::Error {
                description: e.to_string().into(),
            });
        }
        self
    }
}

// 使用
#[instrument]
async fn fetch_data() -> Result<Data, Error> {
    let mut span = tracing::Span::current();
    
    let result = risky_operation()
        .await
        .record_err_to_span(&mut span)?;
    
    Ok(result)
}
```

---

### 3.2 错误传播模式

**问题**: 在多层调用中保持错误上下文。

**解决方案**: 使用 `thiserror` 和 Span 链。

```rust
use thiserror::Error;
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::Context;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] DatabaseError),
    
    #[error("Network error: {0}")]
    Network(#[from] NetworkError),
    
    #[error("Business logic error: {0}")]
    BusinessLogic(String),
}

impl AppError {
    pub fn record_to_current_span(&self) {
        let cx = Context::current();
        let span = cx.span();
        span.record_error(self);
        
        // 添加错误类型属性
        span.set_attribute(opentelemetry::KeyValue::new(
            "error.type",
            match self {
                AppError::Database(_) => "database",
                AppError::Network(_) => "network",
                AppError::BusinessLogic(_) => "business_logic",
            }
        ));
    }
}

#[instrument]
async fn process_order(order_id: u64) -> Result<(), AppError> {
    save_to_database(order_id)
        .await
        .map_err(|e| {
            let app_err = AppError::from(e);
            app_err.record_to_current_span();
            app_err
        })?;
    
    Ok(())
}
```

---

### 3.3 Panic 捕获模式

**问题**: 需要捕获和追踪 panic。

**解决方案**: 使用 `catch_unwind` 和 panic hook。

```rust
use std::panic::{catch_unwind, AssertUnwindSafe};
use opentelemetry::trace::{Tracer, Span};

pub fn with_panic_tracking<F, R>(
    tracer: &dyn Tracer,
    name: &str,
    f: F,
) -> Result<R, Box<dyn std::any::Any + Send>>
where
    F: FnOnce() -> R + std::panic::UnwindSafe,
{
    let mut span = tracer.start(name);
    
    let result = catch_unwind(AssertUnwindSafe(|| f()));
    
    match &result {
        Ok(_) => {
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err(panic_info) => {
            let panic_msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "Unknown panic".to_string()
            };
            
            span.set_status(opentelemetry::trace::Status::Error {
                description: panic_msg.into(),
            });
            span.set_attribute(opentelemetry::KeyValue::new("error.type", "panic"));
        }
    }
    
    span.end();
    result
}

// 使用
fn risky_function() {
    let tracer = global::tracer("my-service");
    
    let result = with_panic_tracking(&tracer, "risky_operation", || {
        // 可能会 panic 的代码
        process_data();
    });
    
    match result {
        Ok(_) => println!("Success"),
        Err(_) => println!("Panic occurred"),
    }
}
```

---

## 4. 上下文传播模式

### 4.1 HTTP 客户端传播模式

**问题**: 需要在 HTTP 请求中传播 tracing context。

**解决方案**: 使用 Propagator 和 HTTP headers。

```rust
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use std::collections::HashMap;

pub async fn make_traced_request(
    client: &reqwest::Client,
    url: &str,
) -> Result<reqwest::Response, reqwest::Error> {
    let cx = opentelemetry::Context::current();
    
    // 提取 trace context 到 headers
    let mut injector = HashMap::new();
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut injector);
    });
    
    // 转换为 reqwest headers
    let mut headers = HeaderMap::new();
    for (key, value) in injector {
        headers.insert(
            HeaderName::from_bytes(key.as_bytes()).unwrap(),
            HeaderValue::from_str(&value).unwrap(),
        );
    }
    
    client.get(url)
        .headers(headers)
        .send()
        .await
}

// 使用
#[instrument]
async fn call_external_service() -> Result<Data, Error> {
    let client = reqwest::Client::new();
    let response = make_traced_request(&client, "https://api.example.com/data").await?;
    
    Ok(response.json().await?)
}
```

---

### 4.2 HTTP 服务端提取模式

**问题**: 需要从 HTTP 请求中提取 tracing context。

**解决方案**: 使用 Axum extractor。

```rust
use axum::{
    extract::Request,
    http::HeaderMap,
    middleware::Next,
    response::Response,
};
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;
use std::collections::HashMap;

pub async fn trace_propagation_middleware(
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Response {
    // 从 headers 提取 context
    let mut extractor = HashMap::new();
    for (key, value) in headers.iter() {
        if let Ok(v) = value.to_str() {
            extractor.insert(key.as_str().to_string(), v.to_string());
        }
    }
    
    let parent_cx = global::get_text_map_propagator(|propagator| {
        propagator.extract(&extractor)
    });
    
    // 设置为当前 context
    let _guard = parent_cx.attach();
    
    next.run(request).await
}

// 在 Axum 中使用
use axum::{Router, routing::get};

fn app() -> Router {
    Router::new()
        .route("/users/:id", get(get_user))
        .layer(axum::middleware::from_fn(trace_propagation_middleware))
}
```

---

### 4.3 跨线程传播模式

**问题**: 需要在不同线程间传播 tracing context。

**解决方案**: 显式传递 Context。

```rust
use opentelemetry::Context;
use std::thread;

#[instrument]
fn spawn_traced_thread<F>(name: &str, f: F) -> thread::JoinHandle<()>
where
    F: FnOnce() + Send + 'static,
{
    let cx = Context::current();
    let name = name.to_string();
    
    thread::spawn(move || {
        let _guard = cx.attach();
        
        let tracer = global::tracer("worker");
        let mut span = tracer.start(&name);
        
        f();
        
        span.end();
    })
}

// 使用
#[instrument]
fn process_in_background() {
    let handle = spawn_traced_thread("background-task", || {
        // 这里的操作会被追踪,并链接到父 Span
        perform_work();
    });
    
    handle.join().unwrap();
}
```

---

## 5. 中间件集成模式

### 5.1 Axum 中间件模式

**问题**: 需要为所有 Axum 路由添加追踪。

**解决方案**: 创建 tracing 中间件层。

```rust
use axum::{
    body::Body,
    extract::Request,
    http::{StatusCode, Uri},
    middleware::Next,
    response::Response,
};
use opentelemetry::trace::{Tracer, SpanKind, Status};
use opentelemetry::global;

pub async fn tracing_middleware(
    uri: Uri,
    request: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("http-server");
    
    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), uri.path()))
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    span.set_attribute(opentelemetry::KeyValue::new("http.method", request.method().to_string()));
    span.set_attribute(opentelemetry::KeyValue::new("http.target", uri.path().to_string()));
    
    let response = next.run(request).await;
    
    span.set_attribute(opentelemetry::KeyValue::new("http.status_code", response.status().as_u16() as i64));
    
    if response.status().is_server_error() {
        span.set_status(Status::Error {
            description: "Server error".into(),
        });
    }
    
    span.end();
    
    response
}

// 使用
use axum::Router;

fn app() -> Router {
    Router::new()
        .route("/users", get(list_users))
        .layer(axum::middleware::from_fn(tracing_middleware))
}
```

---

### 5.2 Tonic 拦截器模式

**问题**: 需要为 gRPC 服务添加追踪。

**解决方案**: 实现 Tonic Interceptor。

```rust
use tonic::{Request, Status};
use opentelemetry::global;
use opentelemetry::trace::{Tracer, SpanKind};

#[derive(Clone)]
pub struct TracingInterceptor;

impl tonic::service::Interceptor for TracingInterceptor {
    fn call(&mut self, mut request: Request<()>) -> Result<Request<()>, Status> {
        let tracer = global::tracer("grpc-server");
        
        let span = tracer
            .span_builder("grpc.request")
            .with_kind(SpanKind::Server)
            .start(&tracer);
        
        // 存储 span 到 request extensions
        request.extensions_mut().insert(span);
        
        Ok(request)
    }
}

// 使用
use tonic::transport::Server;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    Server::builder()
        .add_service(
            MyServiceServer::with_interceptor(
                MyService::default(),
                TracingInterceptor,
            )
        )
        .serve("[::1]:50051".parse()?)
        .await?;
    
    Ok(())
}
```

---

### 5.3 Tower Layer 模式

**问题**: 需要创建可重用的 tracing 层。

**解决方案**: 实现 Tower Layer 和 Service。

```rust
use tower::{Layer, Service};
use std::task::{Context, Poll};
use opentelemetry::trace::{Tracer, Span};

#[derive(Clone)]
pub struct TracingLayer<T> {
    tracer: T,
}

impl<T: Tracer> TracingLayer<T> {
    pub fn new(tracer: T) -> Self {
        Self { tracer }
    }
}

impl<S, T: Tracer + Clone> Layer<S> for TracingLayer<T> {
    type Service = TracingService<S, T>;

    fn layer(&self, inner: S) -> Self::Service {
        TracingService {
            inner,
            tracer: self.tracer.clone(),
        }
    }
}

pub struct TracingService<S, T> {
    inner: S,
    tracer: T,
}

impl<S, T, Request> Service<Request> for TracingService<S, T>
where
    S: Service<Request>,
    T: Tracer,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = S::Future;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request) -> Self::Future {
        let _span = self.tracer.start("service.call");
        self.inner.call(req)
    }
}
```

---

## 6. Metrics 模式

### 6.1 静态 Metrics 模式

**问题**: 需要在应用启动时创建 Metrics。

**解决方案**: 使用 `lazy_static` 或 `OnceCell`。

```rust
use opentelemetry::global;
use opentelemetry::metrics::{Counter, Histogram};
use std::sync::OnceLock;

static HTTP_REQUESTS: OnceLock<Counter<u64>> = OnceLock::new();
static REQUEST_DURATION: OnceLock<Histogram<f64>> = OnceLock::new();

pub fn init_metrics() {
    let meter = global::meter("my-service");
    
    HTTP_REQUESTS.set(
        meter
            .u64_counter("http.requests")
            .with_description("Total HTTP requests")
            .init()
    ).ok();
    
    REQUEST_DURATION.set(
        meter
            .f64_histogram("http.request.duration")
            .with_description("HTTP request duration in seconds")
            .with_unit("s")
            .init()
    ).ok();
}

pub fn record_request(method: &str, status: u16, duration: f64) {
    if let Some(counter) = HTTP_REQUESTS.get() {
        counter.add(1, &[
            opentelemetry::KeyValue::new("http.method", method.to_string()),
            opentelemetry::KeyValue::new("http.status_code", status as i64),
        ]);
    }
    
    if let Some(histogram) = REQUEST_DURATION.get() {
        histogram.record(duration, &[
            opentelemetry::KeyValue::new("http.method", method.to_string()),
        ]);
    }
}
```

---

### 6.2 动态 Metrics 模式

**问题**: 需要在运行时动态创建 Metrics。

**解决方案**: 使用 Metrics 工厂模式。

```rust
use opentelemetry::global;
use opentelemetry::metrics::Counter;
use std::collections::HashMap;
use std::sync::Mutex;

pub struct MetricsFactory {
    counters: Mutex<HashMap<String, Counter<u64>>>,
}

impl MetricsFactory {
    pub fn new() -> Self {
        Self {
            counters: Mutex::new(HashMap::new()),
        }
    }

    pub fn get_or_create_counter(&self, name: &str) -> Counter<u64> {
        let mut counters = self.counters.lock().unwrap();
        
        counters.entry(name.to_string())
            .or_insert_with(|| {
                let meter = global::meter("my-service");
                meter.u64_counter(name).init()
            })
            .clone()
    }

    pub fn increment(&self, name: &str, attributes: &[opentelemetry::KeyValue]) {
        let counter = self.get_or_create_counter(name);
        counter.add(1, attributes);
    }
}

// 使用
lazy_static::lazy_static! {
    static ref METRICS: MetricsFactory = MetricsFactory::new();
}

fn track_event(event_type: &str) {
    METRICS.increment(
        &format!("events.{}", event_type),
        &[opentelemetry::KeyValue::new("type", event_type.to_string())]
    );
}
```

---

### 6.3 Histogram 桶配置模式

**问题**: 需要为 Histogram 配置合适的桶边界。

**解决方案**: 使用预定义的桶配置策略。

```rust
use opentelemetry::global;
use opentelemetry::metrics::Histogram;

pub enum BucketStrategy {
    Latency,      // ms: [5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10000]
    DataSize,     // bytes: [1024, 4096, 16384, 65536, 262144, 1048576, 4194304]
    Custom(Vec<f64>),
}

impl BucketStrategy {
    pub fn boundaries(&self) -> Vec<f64> {
        match self {
            BucketStrategy::Latency => vec![
                5.0, 10.0, 25.0, 50.0, 100.0, 250.0, 500.0, 
                1000.0, 2500.0, 5000.0, 10000.0
            ],
            BucketStrategy::DataSize => vec![
                1024.0, 4096.0, 16384.0, 65536.0, 262144.0, 
                1048576.0, 4194304.0
            ],
            BucketStrategy::Custom(boundaries) => boundaries.clone(),
        }
    }
}

pub fn create_histogram(
    name: &str,
    strategy: BucketStrategy,
) -> Histogram<f64> {
    let meter = global::meter("my-service");
    
    // Note: OpenTelemetry Rust SDK 0.31.0 doesn't support custom boundaries yet
    // This is a conceptual example
    meter
        .f64_histogram(name)
        .with_description("Custom histogram")
        .init()
}

// 使用
fn track_latency() {
    let histogram = create_histogram("http.latency", BucketStrategy::Latency);
    
    let start = std::time::Instant::now();
    // 执行操作
    let duration = start.elapsed().as_millis() as f64;
    
    histogram.record(duration, &[]);
}
```

---

## 7. 批处理与性能优化模式

### 7.1 批量导出模式

**问题**: 需要批量导出 Span 以提高性能。

**解决方案**: 配置 BatchSpanProcessor。

```rust
use opentelemetry_sdk::trace::{BatchConfig, BatchSpanProcessor};
use opentelemetry_sdk::runtime::Tokio;
use std::time::Duration;

pub fn create_batch_exporter() -> Result<(), Box<dyn std::error::Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let batch_config = BatchConfig::default()
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_millis(5000))
        .with_max_export_timeout(Duration::from_secs(30));
    
    let processor = BatchSpanProcessor::builder(exporter, Tokio)
        .with_batch_config(batch_config)
        .build();
    
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_span_processor(processor)
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
    
    Ok(())
}
```

---

### 7.2 采样策略模式

**问题**: 需要根据不同条件采样 Span。

**解决方案**: 实现自定义 Sampler。

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};
use opentelemetry::trace::{TraceContextExt, SpanKind, TraceId, Link};
use opentelemetry::Context;

pub struct AdaptiveSampler {
    default_rate: f64,
    error_rate: f64,
}

impl AdaptiveSampler {
    pub fn new(default_rate: f64) -> Self {
        Self {
            default_rate,
            error_rate: 1.0, // 总是采样错误
        }
    }
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查是否是错误相关的 Span
        let is_error = attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        });
        
        let sampling_rate = if is_error {
            self.error_rate
        } else {
            self.default_rate
        };
        
        let decision = if sampling_rate >= 1.0 {
            SamplingDecision::RecordAndSample
        } else if sampling_rate <= 0.0 {
            SamplingDecision::Drop
        } else {
            // 基于 trace_id 的确定性采样
            let threshold = (sampling_rate * u64::MAX as f64) as u64;
            let trace_id_bytes = trace_id.to_bytes();
            let trace_id_u64 = u64::from_be_bytes([
                trace_id_bytes[0], trace_id_bytes[1], trace_id_bytes[2], trace_id_bytes[3],
                trace_id_bytes[4], trace_id_bytes[5], trace_id_bytes[6], trace_id_bytes[7],
            ]);
            
            if trace_id_u64 < threshold {
                SamplingDecision::RecordAndSample
            } else {
                SamplingDecision::Drop
            }
        };
        
        SamplingResult {
            decision,
            attributes: vec![],
            trace_state: None,
        }
    }
}

// 使用
fn setup_adaptive_sampling() {
    let sampler = AdaptiveSampler::new(0.1); // 10% 默认采样率
    
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(sampler)
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
}
```

---

### 7.3 属性缓存模式

**问题**: 需要优化重复属性的创建开销。

**解决方案**: 使用静态属性缓存。

```rust
use opentelemetry::KeyValue;
use std::sync::OnceLock;

pub struct AttributeCache {
    method_get: OnceLock<KeyValue>,
    method_post: OnceLock<KeyValue>,
    status_200: OnceLock<KeyValue>,
    status_404: OnceLock<KeyValue>,
    status_500: OnceLock<KeyValue>,
}

impl AttributeCache {
    const fn new() -> Self {
        Self {
            method_get: OnceLock::new(),
            method_post: OnceLock::new(),
            status_200: OnceLock::new(),
            status_404: OnceLock::new(),
            status_500: OnceLock::new(),
        }
    }

    pub fn method_get(&self) -> &KeyValue {
        self.method_get.get_or_init(|| {
            KeyValue::new("http.method", "GET")
        })
    }

    pub fn method_post(&self) -> &KeyValue {
        self.method_post.get_or_init(|| {
            KeyValue::new("http.method", "POST")
        })
    }

    pub fn status_code(&self, code: u16) -> KeyValue {
        match code {
            200 => self.status_200.get_or_init(|| {
                KeyValue::new("http.status_code", 200)
            }).clone(),
            404 => self.status_404.get_or_init(|| {
                KeyValue::new("http.status_code", 404)
            }).clone(),
            500 => self.status_500.get_or_init(|| {
                KeyValue::new("http.status_code", 500)
            }).clone(),
            _ => KeyValue::new("http.status_code", code as i64),
        }
    }
}

static ATTRIBUTES: AttributeCache = AttributeCache::new();

// 使用
fn record_http_metrics(method: &str, status: u16) {
    let attrs = vec![
        match method {
            "GET" => ATTRIBUTES.method_get().clone(),
            "POST" => ATTRIBUTES.method_post().clone(),
            _ => KeyValue::new("http.method", method.to_string()),
        },
        ATTRIBUTES.status_code(status),
    ];
    
    // 使用 attrs...
}
```

---

## 8. 测试模式

### 8.1 Mock Exporter 模式

**问题**: 需要在测试中验证 telemetry 数据。

**解决方案**: 实现内存 Exporter。

```rust
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub struct InMemoryExporter {
    spans: Arc<Mutex<Vec<SpanData>>>,
}

impl InMemoryExporter {
    pub fn new() -> Self {
        Self {
            spans: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub fn get_spans(&self) -> Vec<SpanData> {
        self.spans.lock().unwrap().clone()
    }

    pub fn clear(&self) {
        self.spans.lock().unwrap().clear();
    }
}

#[async_trait::async_trait]
impl SpanExporter for InMemoryExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry_sdk::export::trace::ExportResult {
        self.spans.lock().unwrap().extend(batch);
        Ok(())
    }
}

// 使用在测试中
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_span_creation() {
        let exporter = InMemoryExporter::new();
        
        let provider = opentelemetry_sdk::trace::TracerProvider::builder()
            .with_simple_exporter(exporter.clone())
            .build();
        
        let tracer = provider.tracer("test");
        
        let span = tracer.start("test_span");
        drop(span);
        
        provider.force_flush();
        
        let spans = exporter.get_spans();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].name, "test_span");
    }
}
```

---

### 8.2 测试断言模式

**问题**: 需要验证 Span 的属性和状态。

**解决方案**: 创建测试辅助函数。

```rust
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry::trace::Status;

pub struct SpanAsserter<'a> {
    span: &'a SpanData,
}

impl<'a> SpanAsserter<'a> {
    pub fn new(span: &'a SpanData) -> Self {
        Self { span }
    }

    pub fn has_name(self, name: &str) -> Self {
        assert_eq!(self.span.name, name, "Span name mismatch");
        self
    }

    pub fn has_attribute(self, key: &str, value: &str) -> Self {
        let found = self.span.attributes.iter()
            .any(|kv| kv.key.as_str() == key && kv.value.as_str() == value);
        assert!(found, "Attribute {}={} not found", key, value);
        self
    }

    pub fn has_status(self, status: Status) -> Self {
        assert_eq!(self.span.status, status, "Status mismatch");
        self
    }

    pub fn has_error(self) -> Self {
        assert!(matches!(self.span.status, Status::Error { .. }), "Span is not in error state");
        self
    }
}

// 使用
#[tokio::test]
async fn test_error_tracking() {
    let exporter = InMemoryExporter::new();
    // ... setup ...
    
    let spans = exporter.get_spans();
    SpanAsserter::new(&spans[0])
        .has_name("failing_operation")
        .has_attribute("error", "true")
        .has_error();
}
```

---

### 8.3 集成测试模式

**问题**: 需要测试与实际 OTLP Collector 的集成。

**解决方案**: 使用 testcontainers。

```rust
#[cfg(test)]
mod integration_tests {
    use testcontainers::{clients, images::generic::GenericImage, Container};
    use std::time::Duration;

    async fn start_jaeger() -> Container<'static, GenericImage> {
        let docker = clients::Cli::default();
        
        docker.run(
            GenericImage::new("jaegertracing/all-in-one", "latest")
                .with_exposed_port(4317)
                .with_exposed_port(16686)
                .with_env_var("COLLECTOR_OTLP_ENABLED", "true")
        )
    }

    #[tokio::test]
    async fn test_otlp_export() {
        let container = start_jaeger().await;
        let port = container.get_host_port_ipv4(4317);
        
        // 配置 exporter
        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint(format!("http://localhost:{}", port))
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)
            .unwrap();
        
        opentelemetry::global::set_tracer_provider(tracer);
        
        // 创建 span
        let tracer = opentelemetry::global::tracer("test");
        let span = tracer.start("integration_test");
        drop(span);
        
        // 等待导出
        tokio::time::sleep(Duration::from_secs(2)).await;
        
        // 验证 span 已导出（通过 Jaeger API）
        let client = reqwest::Client::new();
        let response = client
            .get(format!("http://localhost:{}/api/traces?service=test", 
                container.get_host_port_ipv4(16686)))
            .send()
            .await
            .unwrap();
        
        assert!(response.status().is_success());
    }
}
```

---

## 9. 生产部署模式

### 9.1 优雅关闭模式

**问题**: 需要确保在关闭时导出所有未完成的 Span。

**解决方案**: 实现优雅关闭逻辑。

```rust
use opentelemetry::global;
use tokio::signal;
use std::time::Duration;

pub async fn run_with_graceful_shutdown<F, Fut>(
    app: F
) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
{
    // 设置 CTRL+C 处理
    let (shutdown_tx, mut shutdown_rx) = tokio::sync::mpsc::channel(1);
    
    tokio::spawn(async move {
        signal::ctrl_c().await.expect("Failed to listen for CTRL+C");
        shutdown_tx.send(()).await.ok();
    });
    
    // 运行应用
    let app_handle = tokio::spawn(app());
    
    // 等待关闭信号
    tokio::select! {
        _ = shutdown_rx.recv() => {
            println!("Received shutdown signal");
        }
        result = app_handle => {
            return result?;
        }
    }
    
    // 优雅关闭 telemetry
    println!("Flushing telemetry data...");
    
    // 强制刷新所有 provider
    global::shutdown_tracer_provider();
    
    // 等待一段时间确保数据导出
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    println!("Shutdown complete");
    Ok(())
}

// 使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    run_with_graceful_shutdown(|| async {
        // 应用逻辑
        run_server().await
    }).await
}
```

---

### 9.2 健康检查模式

**问题**: 需要监控 telemetry 系统的健康状态。

**解决方案**: 实现健康检查端点。

```rust
use axum::{Router, routing::get, Json};
use serde::Serialize;

#[derive(Serialize)]
pub struct HealthStatus {
    pub telemetry: TelemetryHealth,
}

#[derive(Serialize)]
pub struct TelemetryHealth {
    pub tracing: bool,
    pub metrics: bool,
    pub last_export: Option<String>,
}

pub async fn health_check() -> Json<HealthStatus> {
    // 检查 tracer 是否可用
    let tracing_healthy = !opentelemetry::global::tracer("health-check")
        .start("test")
        .span_context()
        .is_valid();
    
    // 检查 metrics 是否可用
    let metrics_healthy = {
        let meter = opentelemetry::global::meter("health-check");
        let counter = meter.u64_counter("test").init();
        counter.add(1, &[]);
        true
    };
    
    Json(HealthStatus {
        telemetry: TelemetryHealth {
            tracing: tracing_healthy,
            metrics: metrics_healthy,
            last_export: Some(chrono::Utc::now().to_rfc3339()),
        },
    })
}

// 使用
fn app() -> Router {
    Router::new()
        .route("/health", get(health_check))
}
```

---

### 9.3 配置热重载模式

**问题**: 需要在不重启应用的情况下更改配置。

**解决方案**: 使用配置监听器。

```rust
use tokio::sync::RwLock;
use std::sync::Arc;

pub struct TelemetryConfig {
    pub sample_rate: f64,
    pub enabled: bool,
}

pub struct ConfigurableTracer {
    config: Arc<RwLock<TelemetryConfig>>,
}

impl ConfigurableTracer {
    pub fn new(config: TelemetryConfig) -> Self {
        Self {
            config: Arc::new(RwLock::new(config)),
        }
    }

    pub async fn should_trace(&self) -> bool {
        let config = self.config.read().await;
        config.enabled && rand::random::<f64>() < config.sample_rate
    }

    pub async fn update_config(&self, new_config: TelemetryConfig) {
        let mut config = self.config.write().await;
        *config = new_config;
        println!("Telemetry config updated");
    }
}

// 使用
lazy_static::lazy_static! {
    static ref TRACER_CONFIG: ConfigurableTracer = ConfigurableTracer::new(
        TelemetryConfig {
            sample_rate: 1.0,
            enabled: true,
        }
    );
}

#[instrument(skip_all)]
async fn handle_request() -> Result<(), Error> {
    if !TRACER_CONFIG.should_trace().await {
        return Ok(()); // 跳过追踪
    }
    
    // 正常追踪逻辑
    Ok(())
}
```

---

## 10. 高级模式

### 10.1 自定义 Processor 模式

**问题**: 需要在导出前修改或过滤 Span。

**解决方案**: 实现自定义 SpanProcessor。

```rust
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry_sdk::trace::{SpanProcessor, Context};
use opentelemetry::trace::Span;

pub struct FilteringProcessor<P> {
    inner: P,
    filter: Box<dyn Fn(&SpanData) -> bool + Send + Sync>,
}

impl<P: SpanProcessor> FilteringProcessor<P> {
    pub fn new<F>(inner: P, filter: F) -> Self
    where
        F: Fn(&SpanData) -> bool + Send + Sync + 'static,
    {
        Self {
            inner,
            filter: Box::new(filter),
        }
    }
}

impl<P: SpanProcessor> SpanProcessor for FilteringProcessor<P> {
    fn on_start(&self, span: &mut opentelemetry_sdk::trace::Span, cx: &Context) {
        self.inner.on_start(span, cx);
    }

    fn on_end(&self, span: SpanData) {
        if (self.filter)(&span) {
            self.inner.on_end(span);
        }
    }

    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.shutdown()
    }
}

// 使用
fn setup_filtered_tracing() {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .build_span_exporter()
        .unwrap();
    
    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio
    ).build();
    
    // 只导出持续时间超过 100ms 的 Span
    let filtering_processor = FilteringProcessor::new(
        batch_processor,
        |span| {
            let duration = span.end_time - span.start_time;
            duration.as_millis() > 100
        }
    );
    
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_span_processor(filtering_processor)
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
}
```

---

### 10.2 多后端导出模式

**问题**: 需要同时导出到多个后端。

**解决方案**: 使用多个 Processor。

```rust
use opentelemetry_sdk::trace::TracerProvider;

pub fn setup_multi_backend() -> Result<(), Box<dyn std::error::Error>> {
    // OTLP Exporter
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let otlp_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        otlp_exporter,
        opentelemetry_sdk::runtime::Tokio
    ).build();
    
    // Jaeger Exporter
    let jaeger_exporter = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("my-service")
        .build_sync_agent_exporter()?;
    
    let jaeger_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        jaeger_exporter,
        opentelemetry_sdk::runtime::Tokio
    ).build();
    
    // 组合多个 processor
    let provider = TracerProvider::builder()
        .with_span_processor(otlp_processor)
        .with_span_processor(jaeger_processor)
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
    
    Ok(())
}
```

---

### 10.3 动态采样模式

**问题**: 需要根据系统负载动态调整采样率。

**解决方案**: 实现自适应采样器。

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};
use opentelemetry::trace::{TraceId, SpanKind, Link};
use opentelemetry::Context;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

pub struct AdaptiveRateSampler {
    current_rate: Arc<AtomicU64>,
    request_count: Arc<AtomicU64>,
    max_requests_per_second: u64,
}

impl AdaptiveRateSampler {
    pub fn new(max_requests_per_second: u64) -> Self {
        let sampler = Self {
            current_rate: Arc::new(AtomicU64::new(f64::to_bits(1.0))),
            request_count: Arc::new(AtomicU64::new(0)),
            max_requests_per_second,
        };
        
        // 启动后台任务调整采样率
        let current_rate = sampler.current_rate.clone();
        let request_count = sampler.request_count.clone();
        let max_rps = max_requests_per_second;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));
            loop {
                interval.tick().await;
                
                let count = request_count.swap(0, Ordering::Relaxed);
                
                // 根据实际请求量调整采样率
                let new_rate = if count > max_rps {
                    (max_rps as f64 / count as f64).min(1.0)
                } else {
                    1.0
                };
                
                current_rate.store(f64::to_bits(new_rate), Ordering::Relaxed);
                
                println!("Adaptive sampling: rate={:.2}, rps={}", new_rate, count);
            }
        });
        
        sampler
    }
    
    fn get_current_rate(&self) -> f64 {
        f64::from_bits(self.current_rate.load(Ordering::Relaxed))
    }
}

impl Sampler for AdaptiveRateSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        self.request_count.fetch_add(1, Ordering::Relaxed);
        
        let rate = self.get_current_rate();
        
        let threshold = (rate * u64::MAX as f64) as u64;
        let trace_id_bytes = trace_id.to_bytes();
        let trace_id_u64 = u64::from_be_bytes([
            trace_id_bytes[0], trace_id_bytes[1], trace_id_bytes[2], trace_id_bytes[3],
            trace_id_bytes[4], trace_id_bytes[5], trace_id_bytes[6], trace_id_bytes[7],
        ]);
        
        let decision = if trace_id_u64 < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            attributes: vec![],
            trace_state: None,
        }
    }
}
```

---

## 🔗 参考资源

- [OpenTelemetry Rust 官方文档](https://docs.rs/opentelemetry/)
- [Rust OTLP 快速入门](./01_Rust_OTLP_30分钟快速入门.md)
- [Rust OTLP 最佳实践](../17_最佳实践清单/Rust_OTLP_最佳实践Checklist.md)
- [Rust 开发环境配置](../31_开发工具链/01_Rust开发环境配置.md)
- [Cargo 工具链集成](../31_开发工具链/02_Cargo工具链集成指南.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [📚 快速入门](./01_Rust_OTLP_30分钟快速入门.md) | [❓ FAQ](./03_Rust_OTLP_FAQ.md)
