# HTTP 客户端追踪 - Reqwest 中间件完整实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - reqwest: 0.12.23
> - reqwest-middleware: 0.4.0
> - reqwest-retry: 0.7.1
> - reqwest-tracing: 0.5.6
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [HTTP 客户端追踪 - Reqwest 中间件完整实现](#http-客户端追踪---reqwest-中间件完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [Reqwest 特性](#reqwest-特性)
    - [中间件架构](#中间件架构)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [HTTP 语义约定](#http-语义约定)
    - [OpenTelemetry 属性](#opentelemetry-属性)
    - [Rust 实现](#rust-实现)
  - [基础追踪集成](#基础追踪集成)
    - [简单客户端](#简单客户端)
  - [中间件模式](#中间件模式)
    - [Middleware Trait](#middleware-trait)
  - [追踪中间件实现](#追踪中间件实现)
    - [OpenTelemetry 追踪中间件](#opentelemetry-追踪中间件)
  - [重试中间件](#重试中间件)
    - [重试策略](#重试策略)
  - [缓存中间件](#缓存中间件)
    - [HTTP 缓存](#http-缓存)
  - [认证中间件](#认证中间件)
    - [Bearer Token 认证](#bearer-token-认证)
  - [性能监控](#性能监控)
    - [请求延迟监控中间件](#请求延迟监控中间件)
  - [最佳实践](#最佳实践)
    - [1. 组合中间件](#1-组合中间件)
    - [2. 错误处理](#2-错误处理)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Reqwest 特性

- **异步 HTTP 客户端**: 基于 Tokio 的高性能客户端
- **HTTP/1.1 和 HTTP/2**: 自动协议协商
- **中间件支持**: 可组合的请求/响应处理链
- **连接池**: 自动管理 TCP 连接
- **TLS 支持**: RustLS 或 OpenSSL

### 中间件架构

```text
Request → Middleware 1 → Middleware 2 → HTTP Client → Server
                                                        ↓
Response ← Middleware 1 ← Middleware 2 ←────────────────┘
```

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "reqwest-otlp-middleware"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Reqwest 核心
reqwest = { version = "0.12.23", features = ["json", "rustls-tls", "stream", "gzip"] }
reqwest-middleware = "0.4.0"
reqwest-retry = "0.7.1"
reqwest-tracing = "0.5.6"

# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json"] }
opentelemetry-http = "0.13.0"

# Tracing 生态
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
async-trait = "0.1.87"

# HTTP
http = "1.2.0"
http-body-util = "0.1.2"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.138"

# 错误处理
thiserror = "2.0.9"
anyhow = "1.0.95"

# 工具
url = "2.5.4"
bytes = "1.10.0"

[dev-dependencies]
criterion = { version = "0.6.0", features = ["async_tokio"] }
mockito = "1.6.1"
tokio-test = "0.4.4"
```

---

## HTTP 语义约定

### OpenTelemetry 属性

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `http.request.method` | string | ✅ | HTTP 方法 | `GET`, `POST` |
| `http.request.body.size` | integer | ❌ | 请求体大小（字节） | `1024` |
| `http.response.status_code` | integer | ✅ | HTTP 状态码 | `200`, `404` |
| `http.response.body.size` | integer | ❌ | 响应体大小（字节） | `2048` |
| `http.route` | string | ❌ | HTTP 路由模板 | `/users/{id}` |
| `url.full` | string | ✅ | 完整 URL | `https://api.example.com/v1/users` |
| `url.scheme` | string | ✅ | URL 协议 | `https` |
| `url.path` | string | ✅ | URL 路径 | `/v1/users` |
| `url.query` | string | ❌ | 查询字符串 | `?page=1&limit=10` |
| `server.address` | string | ✅ | 服务器地址 | `api.example.com` |
| `server.port` | integer | ✅ | 服务器端口 | `443` |
| `network.protocol.version` | string | ❌ | HTTP 版本 | `1.1`, `2` |
| `user_agent.original` | string | ❌ | User-Agent | `reqwest/0.12.23` |

### Rust 实现

```rust
use opentelemetry::KeyValue;
use reqwest::{Request, Response};
use tracing::Span;

/// HTTP 追踪属性
#[derive(Debug, Clone)]
pub struct HttpAttributes {
    pub method: String,
    pub url: String,
    pub scheme: String,
    pub path: String,
    pub query: Option<String>,
    pub host: String,
    pub port: u16,
    pub status_code: Option<u16>,
    pub request_size: Option<usize>,
    pub response_size: Option<usize>,
}

impl HttpAttributes {
    /// 从 Request 创建
    pub fn from_request(request: &Request) -> Self {
        let url = request.url();

        Self {
            method: request.method().to_string(),
            url: url.to_string(),
            scheme: url.scheme().to_string(),
            path: url.path().to_string(),
            query: url.query().map(String::from),
            host: url.host_str().unwrap_or("unknown").to_string(),
            port: url.port().unwrap_or_else(|| {
                if url.scheme() == "https" { 443 } else { 80 }
            }),
            status_code: None,
            request_size: None,
            response_size: None,
        }
    }

    /// 更新响应信息
    pub fn update_from_response(&mut self, response: &Response) {
        self.status_code = Some(response.status().as_u16());
        self.response_size = response
            .headers()
            .get("content-length")
            .and_then(|v| v.to_str().ok())
            .and_then(|v| v.parse().ok());
    }

    /// 转换为 OpenTelemetry KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("http.request.method", self.method.clone()),
            KeyValue::new("url.full", self.url.clone()),
            KeyValue::new("url.scheme", self.scheme.clone()),
            KeyValue::new("url.path", self.path.clone()),
            KeyValue::new("server.address", self.host.clone()),
            KeyValue::new("server.port", self.port as i64),
        ];

        if let Some(query) = &self.query {
            attrs.push(KeyValue::new("url.query", query.clone()));
        }

        if let Some(status) = self.status_code {
            attrs.push(KeyValue::new("http.response.status_code", status as i64));
        }

        if let Some(req_size) = self.request_size {
            attrs.push(KeyValue::new("http.request.body.size", req_size as i64));
        }

        if let Some(resp_size) = self.response_size {
            attrs.push(KeyValue::new("http.response.body.size", resp_size as i64));
        }

        attrs
    }

    /// 记录到 tracing Span
    pub fn record_to_span(&self, span: &Span) {
        span.record("http.request.method", self.method.as_str());
        span.record("url.full", self.url.as_str());
        span.record("url.scheme", self.scheme.as_str());
        span.record("url.path", self.path.as_str());
        span.record("server.address", self.host.as_str());
        span.record("server.port", self.port);

        if let Some(status) = self.status_code {
            span.record("http.response.status_code", status);
        }

        if let Some(req_size) = self.request_size {
            span.record("http.request.body.size", req_size as u64);
        }

        if let Some(resp_size) = self.response_size {
            span.record("http.response.body.size", resp_size as u64);
        }
    }
}
```

---

## 基础追踪集成

### 简单客户端

```rust
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{error, info, instrument};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
}

/// 带追踪的 HTTP 客户端
pub struct TracedHttpClient {
    client: Client,
}

impl TracedHttpClient {
    pub fn new() -> Result<Self, reqwest::Error> {
        let client = Client::builder()
            .user_agent("traced-client/1.0")
            .timeout(std::time::Duration::from_secs(30))
            .build()?;

        Ok(Self { client })
    }

    /// GET 请求
    #[instrument(
        skip(self),
        fields(
            http.request.method = "GET",
            url.full = %url
        )
    )]
    pub async fn get(&self, url: &str) -> Result<String, reqwest::Error> {
        info!("Sending GET request");

        let response = self.client.get(url).send().await?;

        let status = response.status();
        let body = response.text().await?;

        info!(
            status = status.as_u16(),
            body_size = body.len(),
            "GET request completed"
        );

        Ok(body)
    }

    /// POST 请求
    #[instrument(
        skip(self, body),
        fields(
            http.request.method = "POST",
            url.full = %url
        )
    )]
    pub async fn post<T: Serialize>(
        &self,
        url: &str,
        body: &T,
    ) -> Result<String, reqwest::Error> {
        info!("Sending POST request");

        let response = self.client.post(url).json(body).send().await?;

        let status = response.status();
        let response_body = response.text().await?;

        info!(
            status = status.as_u16(),
            body_size = response_body.len(),
            "POST request completed"
        );

        Ok(response_body)
    }

    /// GET JSON
    #[instrument(
        skip(self),
        fields(
            http.request.method = "GET",
            url.full = %url
        )
    )]
    pub async fn get_json<T: for<'de> Deserialize<'de>>(
        &self,
        url: &str,
    ) -> Result<T, reqwest::Error> {
        info!("Sending GET request for JSON");

        let response = self.client.get(url).send().await?;

        let status = response.status();

        if !status.is_success() {
            error!(status = status.as_u16(), "Request failed");
        }

        let data = response.json::<T>().await?;

        info!("JSON response received");

        Ok(data)
    }
}
```

---

## 中间件模式

### Middleware Trait

```rust
use async_trait::async_trait;
use reqwest::{Request, Response};
use reqwest_middleware::{Middleware, Next, Result};

/// 自定义中间件特质
#[async_trait]
pub trait CustomMiddleware: Send + Sync {
    async fn handle(
        &self,
        req: Request,
        next: Next<'_>,
    ) -> Result<Response>;
}
```

---

## 追踪中间件实现

### OpenTelemetry 追踪中间件

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer}, Context};
use opentelemetry_http::HeaderInjector;
use std::time::Instant;
use tracing::{error, info, info_span, Instrument};

/// OpenTelemetry 追踪中间件
#[derive(Clone)]
pub struct TracingMiddleware {
    tracer_name: String,
}

impl TracingMiddleware {
    pub fn new(tracer_name: impl Into<String>) -> Self {
        Self {
            tracer_name: tracer_name.into(),
        }
    }
}

#[async_trait]
impl Middleware for TracingMiddleware {
    async fn handle(
        &self,
        mut req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        let start = Instant::now();

        // 创建 HTTP 追踪属性
        let mut attrs = HttpAttributes::from_request(&req);

        // 创建 Span
        let span = info_span!(
            "http_client_request",
            "otel.kind" = "client",
            "http.request.method" = %attrs.method,
            "url.full" = %attrs.url,
            "server.address" = %attrs.host,
            "server.port" = attrs.port,
        );

        let _enter = span.enter();

        // 注入追踪上下文到 HTTP 头
        let cx = Context::current();
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(&cx, &mut HeaderInjector(req.headers_mut()));
        });

        info!("Sending HTTP request");

        // 发送请求
        let result = next.run(req, extensions).await;

        let duration = start.elapsed();

        match result {
            Ok(response) => {
                attrs.update_from_response(&response);

                let status = response.status();

                info!(
                    status = status.as_u16(),
                    duration_ms = duration.as_millis() as u64,
                    "HTTP request completed"
                );

                // 记录属性到 Span
                attrs.record_to_span(&tracing::Span::current());

                Ok(response)
            }
            Err(e) => {
                error!(
                    error = %e,
                    duration_ms = duration.as_millis() as u64,
                    "HTTP request failed"
                );

                tracing::Span::current().record("error", true);
                tracing::Span::current().record("error.message", &e.to_string());

                Err(e)
            }
        }
    }
}
```

---

## 重试中间件

### 重试策略

```rust
use reqwest_retry::{RetryTransientMiddleware, policies::ExponentialBackoff};
use std::time::Duration;

/// 创建重试中间件
pub fn create_retry_middleware(max_retries: u32) -> RetryTransientMiddleware<ExponentialBackoff> {
    let retry_policy = ExponentialBackoff::builder()
        .retry_bounds(Duration::from_millis(100), Duration::from_secs(30))
        .build_with_max_retries(max_retries);

    RetryTransientMiddleware::new_with_policy(retry_policy)
}

/// 自定义重试中间件（带追踪）
pub struct TracedRetryMiddleware {
    max_retries: u32,
}

impl TracedRetryMiddleware {
    pub fn new(max_retries: u32) -> Self {
        Self { max_retries }
    }
}

#[async_trait]
impl Middleware for TracedRetryMiddleware {
    async fn handle(
        &self,
        req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        let mut retries = 0;

        loop {
            // 克隆请求（因为可能需要重试）
            let req_clone = req.try_clone()
                .ok_or_else(|| reqwest_middleware::Error::Middleware(
                    anyhow::anyhow!("Request body not cloneable")
                ))?;

            match next.run(req_clone, extensions).await {
                Ok(response) => {
                    if retries > 0 {
                        info!(
                            retry_count = retries,
                            status = response.status().as_u16(),
                            "Request succeeded after retries"
                        );
                    }
                    return Ok(response);
                }
                Err(e) if retries < self.max_retries && is_retryable(&e) => {
                    retries += 1;
                    let backoff = Duration::from_millis(100 * 2u64.pow(retries));

                    tracing::warn!(
                        error = %e,
                        retry = retries,
                        backoff_ms = backoff.as_millis() as u64,
                        "Request failed, retrying"
                    );

                    tokio::time::sleep(backoff).await;
                }
                Err(e) => {
                    if retries > 0 {
                        error!(
                            error = %e,
                            retry_count = retries,
                            "Request failed after all retries"
                        );
                    }
                    return Err(e);
                }
            }
        }
    }
}

fn is_retryable(error: &reqwest_middleware::Error) -> bool {
    match error {
        reqwest_middleware::Error::Reqwest(e) => {
            e.is_timeout() || e.is_connect()
        }
        _ => false,
    }
}
```

---

## 缓存中间件

### HTTP 缓存

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 简单内存缓存中间件
pub struct CacheMiddleware {
    cache: Arc<RwLock<HashMap<String, CachedResponse>>>,
    ttl: Duration,
}

#[derive(Clone)]
struct CachedResponse {
    body: bytes::Bytes,
    status: http::StatusCode,
    headers: http::HeaderMap,
    cached_at: Instant,
}

impl CacheMiddleware {
    pub fn new(ttl: Duration) -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
            ttl,
        }
    }

    fn cache_key(req: &Request) -> String {
        format!("{} {}", req.method(), req.url())
    }
}

#[async_trait]
impl Middleware for CacheMiddleware {
    async fn handle(
        &self,
        req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        // 只缓存 GET 请求
        if req.method() != http::Method::GET {
            return next.run(req, extensions).await;
        }

        let cache_key = Self::cache_key(&req);

        // 检查缓存
        {
            let cache = self.cache.read().await;
            if let Some(cached) = cache.get(&cache_key) {
                let age = cached.cached_at.elapsed();
                if age < self.ttl {
                    info!(
                        url = %req.url(),
                        age_ms = age.as_millis() as u64,
                        "Serving from cache"
                    );

                    // 构建响应（注意：这是简化版本，实际需要更完善的实现）
                    let mut response = http::Response::new(cached.body.clone());
                    *response.status_mut() = cached.status;
                    *response.headers_mut() = cached.headers.clone();

                    return Ok(response.into());
                }
            }
        }

        // 缓存未命中，发送请求
        info!(url = %req.url(), "Cache miss, fetching from server");

        let response = next.run(req, extensions).await?;

        // 缓存成功响应
        if response.status().is_success() {
            let status = response.status();
            let headers = response.headers().clone();

            // 读取响应体
            let body_bytes = response.bytes().await?;

            let cached = CachedResponse {
                body: body_bytes.clone(),
                status,
                headers: headers.clone(),
                cached_at: Instant::now(),
            };

            // 存入缓存
            {
                let mut cache = self.cache.write().await;
                cache.insert(cache_key, cached);
            }

            info!("Response cached");

            // 重建响应
            let mut new_response = http::Response::new(body_bytes);
            *new_response.status_mut() = status;
            *new_response.headers_mut() = headers;

            Ok(new_response.into())
        } else {
            Ok(response)
        }
    }
}
```

---

## 认证中间件

### Bearer Token 认证

```rust
/// Bearer Token 认证中间件
pub struct AuthMiddleware {
    token: String,
}

impl AuthMiddleware {
    pub fn new(token: impl Into<String>) -> Self {
        Self {
            token: token.into(),
        }
    }
}

#[async_trait]
impl Middleware for AuthMiddleware {
    async fn handle(
        &self,
        mut req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        // 添加 Authorization 头
        req.headers_mut().insert(
            http::header::AUTHORIZATION,
            http::HeaderValue::from_str(&format!("Bearer {}", self.token))
                .map_err(|e| reqwest_middleware::Error::Middleware(anyhow::anyhow!(e)))?,
        );

        info!("Added Bearer token to request");

        next.run(req, extensions).await
    }
}

/// API Key 认证中间件
pub struct ApiKeyMiddleware {
    api_key: String,
    header_name: String,
}

impl ApiKeyMiddleware {
    pub fn new(api_key: impl Into<String>, header_name: impl Into<String>) -> Self {
        Self {
            api_key: api_key.into(),
            header_name: header_name.into(),
        }
    }
}

#[async_trait]
impl Middleware for ApiKeyMiddleware {
    async fn handle(
        &self,
        mut req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        req.headers_mut().insert(
            http::HeaderName::from_bytes(self.header_name.as_bytes())
                .map_err(|e| reqwest_middleware::Error::Middleware(anyhow::anyhow!(e)))?,
            http::HeaderValue::from_str(&self.api_key)
                .map_err(|e| reqwest_middleware::Error::Middleware(anyhow::anyhow!(e)))?,
        );

        info!(header = %self.header_name, "Added API key to request");

        next.run(req, extensions).await
    }
}
```

---

## 性能监控

### 请求延迟监控中间件

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 性能监控中间件
pub struct MetricsMiddleware {
    total_requests: Arc<AtomicU64>,
    total_errors: Arc<AtomicU64>,
    total_duration_ms: Arc<AtomicU64>,
}

impl MetricsMiddleware {
    pub fn new() -> Self {
        Self {
            total_requests: Arc::new(AtomicU64::new(0)),
            total_errors: Arc::new(AtomicU64::new(0)),
            total_duration_ms: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn get_metrics(&self) -> Metrics {
        let requests = self.total_requests.load(Ordering::Relaxed);
        let errors = self.total_errors.load(Ordering::Relaxed);
        let duration_ms = self.total_duration_ms.load(Ordering::Relaxed);

        Metrics {
            total_requests: requests,
            total_errors: errors,
            avg_duration_ms: if requests > 0 {
                duration_ms / requests
            } else {
                0
            },
        }
    }
}

#[derive(Debug)]
pub struct Metrics {
    pub total_requests: u64,
    pub total_errors: u64,
    pub avg_duration_ms: u64,
}

#[async_trait]
impl Middleware for MetricsMiddleware {
    async fn handle(
        &self,
        req: Request,
        extensions: &mut http::Extensions,
        next: Next<'_>,
    ) -> Result<Response> {
        let start = Instant::now();

        self.total_requests.fetch_add(1, Ordering::Relaxed);

        let result = next.run(req, extensions).await;

        let duration = start.elapsed();
        self.total_duration_ms.fetch_add(duration.as_millis() as u64, Ordering::Relaxed);

        if result.is_err() {
            self.total_errors.fetch_add(1, Ordering::Relaxed);
        }

        result
    }
}
```

---

## 最佳实践

### 1. 组合中间件

```rust
use reqwest_middleware::ClientBuilder;

pub fn create_production_client() -> reqwest_middleware::ClientWithMiddleware {
    let reqwest_client = reqwest::Client::builder()
        .timeout(Duration::from_secs(30))
        .pool_max_idle_per_host(10)
        .user_agent("my-app/1.0")
        .build()
        .expect("Failed to build reqwest client");

    ClientBuilder::new(reqwest_client)
        // 追踪中间件（最外层）
        .with(TracingMiddleware::new("http-client"))
        // 重试中间件
        .with(create_retry_middleware(3))
        // 认证中间件
        .with(AuthMiddleware::new("your-token-here"))
        // 缓存中间件
        .with(CacheMiddleware::new(Duration::from_secs(60)))
        // 性能监控中间件（最内层）
        .with(MetricsMiddleware::new())
        .build()
}
```

### 2. 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum HttpClientError {
    #[error("Request failed: {0}")]
    RequestError(#[from] reqwest::Error),

    #[error("Middleware error: {0}")]
    MiddlewareError(#[from] reqwest_middleware::Error),

    #[error("Timeout after {0} seconds")]
    Timeout(u64),

    #[error("Too many redirects")]
    TooManyRedirects,

    #[error("Server error: {status}")]
    ServerError { status: u16 },
}
```

---

## 完整示例

### main.rs

```rust
use anyhow::Result;
use opentelemetry::global;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};
use opentelemetry_otlp::WithExportConfig;
use tracing::info;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces"),
        )
        .with_trace_config(
            sdktrace::Config::default()
                .with_resource(Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "http-client-demo"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("Starting HTTP client demo");

    // 创建带中间件的客户端
    let client = create_production_client();

    // 发送请求
    let response = client
        .get("https://api.example.com/users")
        .send()
        .await?;

    info!(
        status = response.status().as_u16(),
        "Request completed"
    );

    let body = response.text().await?;
    info!(body_size = body.len(), "Response received");

    // 关闭追踪
    global::shutdown_tracer_provider();

    Ok(())
}
```

---

## 总结

本文档提供了 Reqwest HTTP 客户端在 Rust 1.90 环境下的完整 OpenTelemetry 追踪集成方案：

1. ✅ **HTTP 语义约定**: 完整实现 OpenTelemetry HTTP 语义约定
2. ✅ **追踪中间件**: 自动注入追踪上下文到 HTTP 头
3. ✅ **重试中间件**: 指数退避重试策略
4. ✅ **缓存中间件**: 内存缓存 GET 请求
5. ✅ **认证中间件**: Bearer Token 和 API Key 支持
6. ✅ **性能监控**: 请求延迟和错误率统计
7. ✅ **最佳实践**: 中间件组合和错误处理

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT
