# Reqwest HTTP 客户端追踪 Rust 完整实现指南

## 目录

- [Reqwest HTTP 客户端追踪 Rust 完整实现指南](#reqwest-http-客户端追踪-rust-完整实现指南)
  - [目录](#目录)
  - [1. Reqwest 架构概述](#1-reqwest-架构概述)
    - [1.1 Reqwest 核心特性](#11-reqwest-核心特性)
    - [1.2 Reqwest 与 OpenTelemetry](#12-reqwest-与-opentelemetry)
  - [2. Rust 依赖配置](#2-rust-依赖配置)
  - [3. HTTP Client Semantic Conventions](#3-http-client-semantic-conventions)
    - [3.1 HTTP 属性](#31-http-属性)
    - [3.2 Span 命名规范](#32-span-命名规范)
  - [4. 基础 HTTP 请求追踪](#4-基础-http-请求追踪)
    - [4.1 GET 请求追踪](#41-get-请求追踪)
    - [4.2 POST 请求追踪](#42-post-请求追踪)
    - [4.3 PUT/PATCH/DELETE 追踪](#43-putpatchdelete-追踪)
  - [5. 中间件实现](#5-中间件实现)
    - [5.1 追踪中间件](#51-追踪中间件)
    - [5.2 Context Propagation](#52-context-propagation)
  - [6. 高级特性追踪](#6-高级特性追踪)
    - [6.1 Stream 响应追踪](#61-stream-响应追踪)
    - [6.2 Multipart 上传追踪](#62-multipart-上传追踪)
    - [6.3 WebSocket 追踪](#63-websocket-追踪)
  - [7. 错误处理](#7-错误处理)
    - [7.1 超时处理](#71-超时处理)
    - [7.2 重试机制](#72-重试机制)
    - [7.3 连接池错误](#73-连接池错误)
  - [8. 性能监控](#8-性能监控)
    - [8.1 请求延迟监控](#81-请求延迟监控)
    - [8.2 吞吐量监控](#82-吞吐量监控)
    - [8.3 连接池监控](#83-连接池监控)
  - [9. 安全与认证](#9-安全与认证)
    - [9.1 Bearer Token 追踪](#91-bearer-token-追踪)
    - [9.2 API Key 追踪](#92-api-key-追踪)
    - [9.3 OAuth2 追踪](#93-oauth2-追踪)
  - [10. 完整生产示例](#10-完整生产示例)
  - [总结](#总结)

---

## 1. Reqwest 架构概述

### 1.1 Reqwest 核心特性

Reqwest 是 Rust 生态中最流行的 HTTP 客户端：

- **异步/同步**：基于 Tokio 的异步支持
- **连接池**：自动管理 HTTP 连接
- **中间件**：可扩展的请求/响应处理
- **TLS 支持**：rustls 或 native-tls
- **HTTP/2**：默认支持 HTTP/2

### 1.2 Reqwest 与 OpenTelemetry

Reqwest 追踪关注点：

1. **请求追踪**：HTTP 方法、URL、状态码、延迟
2. **Context 传播**：W3C Trace Context 注入到 HTTP Headers
3. **错误追踪**：网络错误、超时、服务器错误
4. **性能监控**：请求延迟、吞吐量、连接池状态

---

## 2. Rust 依赖配置

```toml
[dependencies]
# HTTP 客户端
reqwest = { version = "0.12.14", features = ["json", "stream", "multipart", "rustls-tls"] }

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic"] }
opentelemetry-http = "0.31.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# URL 处理
url = "2.5"

[dev-dependencies]
criterion = "0.5"
wiremock = "0.6"
```

---

## 3. HTTP Client Semantic Conventions

### 3.1 HTTP 属性

```rust
// HTTP Client 属性常量
pub mod attributes {
    // HTTP 基础属性
    pub const HTTP_METHOD: &str = "http.method";                     // GET, POST, etc.
    pub const HTTP_URL: &str = "http.url";                           // Full URL
    pub const HTTP_TARGET: &str = "http.target";                     // Path + query
    pub const HTTP_HOST: &str = "http.host";                         // Host header
    pub const HTTP_SCHEME: &str = "http.scheme";                     // http, https
    pub const HTTP_STATUS_CODE: &str = "http.status_code";           // 200, 404, etc.
    pub const HTTP_USER_AGENT: &str = "http.user_agent";
    pub const HTTP_REQUEST_CONTENT_LENGTH: &str = "http.request_content_length";
    pub const HTTP_RESPONSE_CONTENT_LENGTH: &str = "http.response_content_length";

    // Network 属性
    pub const NET_PEER_NAME: &str = "net.peer.name";                // Server hostname
    pub const NET_PEER_PORT: &str = "net.peer.port";                // Server port
    pub const NET_PROTOCOL_NAME: &str = "net.protocol.name";        // http
    pub const NET_PROTOCOL_VERSION: &str = "net.protocol.version";  // 1.1, 2

    // Error 属性
    pub const ERROR_TYPE: &str = "error.type";
}
```

### 3.2 Span 命名规范

- **HTTP 请求**：`HTTP {method}`（如 `HTTP GET`, `HTTP POST`）
- 或者更详细：`{method} {path}`（如 `GET /api/users`）

---

## 4. 基础 HTTP 请求追踪

### 4.1 GET 请求追踪

```rust
use reqwest::{Client, Response};
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind, Span};
use opentelemetry::{global, Context, KeyValue};
use url::Url;

/// Reqwest 客户端（支持追踪）
pub struct TracedClient {
    client: Client,
}

impl TracedClient {
    pub fn new() -> Self {
        Self {
            client: Client::builder()
                .timeout(std::time::Duration::from_secs(30))
                .pool_max_idle_per_host(10)
                .build()
                .expect("Failed to create HTTP client"),
        }
    }

    /// GET 请求（带追踪）
    pub async fn get_with_trace(&self, url: &str) -> Result<Response, Box<dyn std::error::Error>> {
        let parsed_url = Url::parse(url)?;
        let tracer = global::tracer("reqwest-client");

        let mut span = tracer
            .span_builder(format!("HTTP GET"))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "GET"),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.target", parsed_url.path().to_string()),
                KeyValue::new("http.scheme", parsed_url.scheme().to_string()),
                KeyValue::new("net.peer.name", parsed_url.host_str().unwrap_or("").to_string()),
                KeyValue::new("net.peer.port", parsed_url.port().unwrap_or(443) as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 构建请求并注入 Trace Context
        let mut request = self.client.get(url);
        request = inject_trace_context(request, &cx);

        // 发送请求
        let start = std::time::Instant::now();
        let result = request.send().await;
        let duration = start.elapsed();

        match result {
            Ok(response) => {
                let status = response.status();
                let content_length = response.content_length().unwrap_or(0);

                cx.span().set_attributes(vec![
                    KeyValue::new("http.status_code", status.as_u16() as i64),
                    KeyValue::new("http.response_content_length", content_length as i64),
                    KeyValue::new("http.duration.ms", duration.as_millis() as i64),
                ]);

                if status.is_success() {
                    cx.span().add_event("Request succeeded", vec![]);
                } else if status.is_client_error() || status.is_server_error() {
                    cx.span().add_event("Request failed", vec![
                        KeyValue::new("error.type", "http_error"),
                    ]);
                }

                Ok(response)
            }
            Err(e) => {
                cx.span().record_error(&e);
                cx.span().set_attribute(KeyValue::new("error.type", classify_error(&e)));
                Err(Box::new(e))
            }
        }
    }
}

/// 注入 Trace Context 到 HTTP Headers
fn inject_trace_context(
    request: reqwest::RequestBuilder,
    cx: &Context,
) -> reqwest::RequestBuilder {
    use opentelemetry::propagation::{TextMapPropagator, Injector};
    use std::collections::HashMap;

    struct ReqwestInjector {
        headers: HashMap<String, String>,
    }

    impl Injector for ReqwestInjector {
        fn set(&mut self, key: &str, value: String) {
            self.headers.insert(key.to_string(), value);
        }
    }

    let mut injector = ReqwestInjector {
        headers: HashMap::new(),
    };

    let propagator = opentelemetry_sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(cx, &mut injector);

    // 添加 Headers 到请求
    let mut request = request;
    for (key, value) in injector.headers {
        request = request.header(key, value);
    }

    request
}

/// 分类错误类型
fn classify_error(error: &reqwest::Error) -> &'static str {
    if error.is_timeout() {
        "timeout"
    } else if error.is_connect() {
        "connection_error"
    } else if error.is_request() {
        "request_error"
    } else if error.is_decode() {
        "decode_error"
    } else {
        "unknown_error"
    }
}
```

### 4.2 POST 请求追踪

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

impl TracedClient {
    /// POST 请求（带追踪）
    pub async fn post_json_with_trace<T: Serialize>(
        &self,
        url: &str,
        body: &T,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let parsed_url = Url::parse(url)?;
        let tracer = global::tracer("reqwest-client");

        let body_json = serde_json::to_string(body)?;
        let body_size = body_json.len();

        let mut span = tracer
            .span_builder(format!("HTTP POST"))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "POST"),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.target", parsed_url.path().to_string()),
                KeyValue::new("http.scheme", parsed_url.scheme().to_string()),
                KeyValue::new("net.peer.name", parsed_url.host_str().unwrap_or("").to_string()),
                KeyValue::new("net.peer.port", parsed_url.port().unwrap_or(443) as i64),
                KeyValue::new("http.request_content_length", body_size as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 构建请求
        let mut request = self.client.post(url).json(body);
        request = inject_trace_context(request, &cx);

        // 发送请求
        let start = std::time::Instant::now();
        let result = request.send().await;
        let duration = start.elapsed();

        match result {
            Ok(response) => {
                let status = response.status();

                cx.span().set_attributes(vec![
                    KeyValue::new("http.status_code", status.as_u16() as i64),
                    KeyValue::new("http.duration.ms", duration.as_millis() as i64),
                ]);

                if status.is_success() {
                    cx.span().add_event("POST request succeeded", vec![]);
                } else {
                    cx.span().add_event("POST request failed", vec![]);
                }

                Ok(response)
            }
            Err(e) => {
                cx.span().record_error(&e);
                Err(Box::new(e))
            }
        }
    }
}
```

### 4.3 PUT/PATCH/DELETE 追踪

```rust
impl TracedClient {
    /// PUT 请求（带追踪）
    pub async fn put_json_with_trace<T: Serialize>(
        &self,
        url: &str,
        body: &T,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        self.request_with_trace("PUT", url, Some(body)).await
    }

    /// PATCH 请求（带追踪）
    pub async fn patch_json_with_trace<T: Serialize>(
        &self,
        url: &str,
        body: &T,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        self.request_with_trace("PATCH", url, Some(body)).await
    }

    /// DELETE 请求（带追踪）
    pub async fn delete_with_trace(&self, url: &str) -> Result<Response, Box<dyn std::error::Error>> {
        self.request_with_trace::<()>("DELETE", url, None).await
    }

    /// 通用请求方法
    async fn request_with_trace<T: Serialize>(
        &self,
        method: &str,
        url: &str,
        body: Option<&T>,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let parsed_url = Url::parse(url)?;
        let tracer = global::tracer("reqwest-client");

        let mut span = tracer
            .span_builder(format!("HTTP {}", method))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.target", parsed_url.path().to_string()),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut request = match method {
            "PUT" => self.client.put(url),
            "PATCH" => self.client.patch(url),
            "DELETE" => self.client.delete(url),
            _ => return Err("Unsupported method".into()),
        };

        if let Some(body) = body {
            request = request.json(body);
        }

        request = inject_trace_context(request, &cx);

        let start = std::time::Instant::now();
        let result = request.send().await;
        let duration = start.elapsed();

        match result {
            Ok(response) => {
                cx.span().set_attributes(vec![
                    KeyValue::new("http.status_code", response.status().as_u16() as i64),
                    KeyValue::new("http.duration.ms", duration.as_millis() as i64),
                ]);
                Ok(response)
            }
            Err(e) => {
                cx.span().record_error(&e);
                Err(Box::new(e))
            }
        }
    }
}
```

---

## 5. 中间件实现

### 5.1 追踪中间件

```rust
use reqwest::Request;

/// HTTP 客户端中间件 Trait
pub trait Middleware: Send + Sync {
    fn process(&self, request: Request, cx: &Context) -> Request;
}

/// OpenTelemetry 追踪中间件
pub struct TracingMiddleware;

impl Middleware for TracingMiddleware {
    fn process(&self, request: Request, cx: &Context) -> Request {
        inject_trace_context(reqwest::RequestBuilder::from_parts(
            request.method().clone(),
            request.url().clone(),
        ), cx)
        .build()
        .unwrap()
    }
}
```

### 5.2 Context Propagation

Context 传播已在 `inject_trace_context` 函数中实现，使用 W3C Trace Context 标准。

---

## 6. 高级特性追踪

### 6.1 Stream 响应追踪

```rust
use futures::StreamExt;

impl TracedClient {
    /// 下载大文件（Stream 模式，带追踪）
    pub async fn download_stream_with_trace(
        &self,
        url: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP GET (Stream)")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "GET"),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.streaming", true),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let response = self.get_with_trace(url).await?;
        let mut stream = response.bytes_stream();

        let mut total_bytes = 0_u64;
        while let Some(chunk) = stream.next().await {
            let chunk = chunk?;
            total_bytes += chunk.len() as u64;
            // 处理 chunk...
        }

        cx.span().set_attribute(KeyValue::new("http.response_content_length", total_bytes as i64));
        cx.span().add_event("Stream download completed", vec![]);

        Ok(())
    }
}
```

### 6.2 Multipart 上传追踪

```rust
use reqwest::multipart;

impl TracedClient {
    /// 上传文件（Multipart，带追踪）
    pub async fn upload_multipart_with_trace(
        &self,
        url: &str,
        file_path: &str,
        field_name: &str,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP POST (Multipart)")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "POST"),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.multipart", true),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // 读取文件
        let file_content = tokio::fs::read(file_path).await?;
        let file_size = file_content.len();

        // 构建 Multipart Form
        let part = multipart::Part::bytes(file_content)
            .file_name(std::path::Path::new(file_path)
                .file_name()
                .unwrap()
                .to_string_lossy()
                .to_string());

        let form = multipart::Form::new().part(field_name, part);

        // 发送请求
        let mut request = self.client.post(url).multipart(form);
        request = inject_trace_context(request, &cx);

        let start = std::time::Instant::now();
        let result = request.send().await;
        let duration = start.elapsed();

        match result {
            Ok(response) => {
                cx.span().set_attributes(vec![
                    KeyValue::new("http.status_code", response.status().as_u16() as i64),
                    KeyValue::new("http.duration.ms", duration.as_millis() as i64),
                    KeyValue::new("file.size", file_size as i64),
                ]);
                Ok(response)
            }
            Err(e) => {
                cx.span().record_error(&e);
                Err(Box::new(e))
            }
        }
    }
}
```

### 6.3 WebSocket 追踪

```rust
// WebSocket 通常使用 tokio-tungstenite，这里展示概念
// 实际实现需要 tokio-tungstenite + tracing
```

---

## 7. 错误处理

### 7.1 超时处理

```rust
use std::time::Duration;

impl TracedClient {
    /// 带自定义超时的请求
    pub async fn get_with_timeout(
        &self,
        url: &str,
        timeout: Duration,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP GET (Timeout)")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.timeout.ms", timeout.as_millis() as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let client = Client::builder().timeout(timeout).build()?;

        match tokio::time::timeout(timeout, client.get(url).send()).await {
            Ok(Ok(response)) => {
                cx.span().add_event("Request completed within timeout", vec![]);
                Ok(response)
            }
            Ok(Err(e)) => {
                cx.span().record_error(&e);
                Err(Box::new(e))
            }
            Err(_) => {
                let err = std::io::Error::new(std::io::ErrorKind::TimedOut, "Request timeout");
                cx.span().record_error(&err);
                cx.span().add_event("Request timed out", vec![]);
                Err(Box::new(err))
            }
        }
    }
}
```

### 7.2 重试机制

```rust
impl TracedClient {
    /// 带重试的 GET 请求
    pub async fn get_with_retry(
        &self,
        url: &str,
        max_retries: u32,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP GET (Retry)")
            .with_attributes(vec![
                KeyValue::new("http.max_retries", max_retries as i64),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        for attempt in 1..=max_retries {
            match self.get_with_trace(url).await {
                Ok(response) if response.status().is_success() => {
                    cx.span().set_attribute(KeyValue::new("http.attempt", attempt as i64));
                    return Ok(response);
                }
                Ok(response) if attempt < max_retries => {
                    cx.span().add_event("Retry due to HTTP error", vec![
                        KeyValue::new("attempt", attempt as i64),
                        KeyValue::new("status_code", response.status().as_u16() as i64),
                    ]);
                    tokio::time::sleep(Duration::from_millis(100 * attempt as u64)).await;
                }
                Ok(response) => {
                    return Ok(response);
                }
                Err(e) if attempt < max_retries => {
                    cx.span().add_event("Retry due to error", vec![
                        KeyValue::new("attempt", attempt as i64),
                    ]);
                    tokio::time::sleep(Duration::from_millis(100 * attempt as u64)).await;
                }
                Err(e) => {
                    cx.span().record_error(&*e);
                    return Err(e);
                }
            }
        }

        unreachable!()
    }
}
```

### 7.3 连接池错误

```rust
impl TracedClient {
    /// 监控连接池状态
    pub fn log_pool_status(&self) {
        let tracer = global::tracer("reqwest-client");
        let span = tracer
            .span_builder("HTTP Pool Status")
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        // Reqwest 不直接暴露连接池状态，但可以通过 Metrics 监控
        cx.span().add_event("Pool status checked", vec![]);
    }
}
```

---

## 8. 性能监控

### 8.1 请求延迟监控

```rust
use opentelemetry::metrics::{Meter, Histogram};

pub struct HttpMetrics {
    request_duration: Histogram<f64>,
    request_size: Histogram<u64>,
    response_size: Histogram<u64>,
}

impl HttpMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            request_duration: meter
                .f64_histogram("http.client.duration")
                .with_unit("ms")
                .with_description("HTTP request duration")
                .build(),
            request_size: meter
                .u64_histogram("http.client.request.size")
                .with_unit("bytes")
                .with_description("HTTP request body size")
                .build(),
            response_size: meter
                .u64_histogram("http.client.response.size")
                .with_unit("bytes")
                .with_description("HTTP response body size")
                .build(),
        }
    }

    pub fn record_request(
        &self,
        duration: Duration,
        method: &str,
        status: u16,
        req_size: usize,
        resp_size: usize,
    ) {
        let attrs = &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status as i64),
        ];

        self.request_duration.record(duration.as_secs_f64() * 1000.0, attrs);
        self.request_size.record(req_size as u64, attrs);
        self.response_size.record(resp_size as u64, attrs);
    }
}
```

### 8.2 吞吐量监控

```rust
use opentelemetry::metrics::Counter;

pub struct ThroughputMetrics {
    requests_total: Counter<u64>,
    requests_failed: Counter<u64>,
}

impl ThroughputMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("http.client.requests.total")
                .with_description("Total HTTP requests")
                .build(),
            requests_failed: meter
                .u64_counter("http.client.requests.failed")
                .with_description("Failed HTTP requests")
                .build(),
        }
    }

    pub fn record_request(&self, method: &str, success: bool) {
        let attrs = &[KeyValue::new("http.method", method.to_string())];
        self.requests_total.add(1, attrs);

        if !success {
            self.requests_failed.add(1, attrs);
        }
    }
}
```

### 8.3 连接池监控

```rust
use opentelemetry::metrics::Gauge;

pub struct PoolMetrics {
    connections_active: Gauge<i64>,
    connections_idle: Gauge<i64>,
}

impl PoolMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            connections_active: meter
                .i64_gauge("http.client.connections.active")
                .with_description("Active HTTP connections")
                .build(),
            connections_idle: meter
                .i64_gauge("http.client.connections.idle")
                .with_description("Idle HTTP connections")
                .build(),
        }
    }
}
```

---

## 9. 安全与认证

### 9.1 Bearer Token 追踪

```rust
impl TracedClient {
    /// 带 Bearer Token 的请求
    pub async fn get_with_bearer_token(
        &self,
        url: &str,
        token: &str,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP GET (Bearer Auth)")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.auth.type", "bearer"),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut request = self.client
            .get(url)
            .bearer_auth(token);

        request = inject_trace_context(request, &cx);

        let response = request.send().await?;
        Ok(response)
    }
}
```

### 9.2 API Key 追踪

```rust
impl TracedClient {
    /// 带 API Key 的请求
    pub async fn get_with_api_key(
        &self,
        url: &str,
        api_key: &str,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        let tracer = global::tracer("reqwest-client");
        let mut span = tracer
            .span_builder("HTTP GET (API Key)")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.auth.type", "api_key"),
            ])
            .start(&tracer);

        let cx = Context::current_with_span(span);
        let _guard = cx.attach();

        let mut request = self.client
            .get(url)
            .header("X-API-Key", api_key);

        request = inject_trace_context(request, &cx);

        let response = request.send().await?;
        Ok(response)
    }
}
```

### 9.3 OAuth2 追踪

```rust
// OAuth2 集成通常使用 oauth2 crate
// 这里展示基本概念
impl TracedClient {
    /// 带 OAuth2 Token 的请求
    pub async fn get_with_oauth2(
        &self,
        url: &str,
        access_token: &str,
    ) -> Result<Response, Box<dyn std::error::Error>> {
        self.get_with_bearer_token(url, access_token).await
    }
}
```

---

## 10. 完整生产示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    global::set_tracer_provider(tracer_provider);

    // 创建 Traced HTTP 客户端
    let client = TracedClient::new();

    // GET 请求
    let response = client.get_with_trace("https://api.github.com/users/rust-lang").await?;
    let body = response.text().await?;
    println!("Response: {}", body);

    // POST 请求
    let user_request = CreateUserRequest {
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
    };
    let response = client
        .post_json_with_trace("https://jsonplaceholder.typicode.com/users", &user_request)
        .await?;
    println!("Status: {}", response.status());

    // 带重试的请求
    let response = client
        .get_with_retry("https://api.github.com/users/rust-lang", 3)
        .await?;
    println!("Retry response status: {}", response.status());

    // Stream 下载
    client
        .download_stream_with_trace("https://releases.ubuntu.com/22.04/ubuntu-22.04-desktop-amd64.iso")
        .await?;

    // Multipart 上传
    client
        .upload_multipart_with_trace(
            "https://httpbin.org/post",
            "example.txt",
            "file",
        )
        .await?;

    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}
```

---

## 总结

本指南涵盖了 Reqwest HTTP 客户端与 OpenTelemetry 集成的完整实现：

1. **基础请求追踪**：GET、POST、PUT、PATCH、DELETE
2. **Context 传播**：W3C Trace Context 注入到 HTTP Headers
3. **高级特性**：Stream 下载、Multipart 上传
4. **错误处理**：超时、重试、连接池错误
5. **性能监控**：请求延迟、吞吐量、连接池状态
6. **安全认证**：Bearer Token、API Key、OAuth2

通过这些实现，您可以在生产环境中获得 HTTP 客户端的完整可观测性。
