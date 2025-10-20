# HTTP 语义约定 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Axum**: 0.8.7  
> **Reqwest**: 0.12.23  
> **最后更新**: 2025年10月9日

---

## 目录

- [HTTP 语义约定 - Rust 完整实现](#http-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. HTTP 语义约定概述](#1-http-语义约定概述)
  - [2. HTTP 客户端追踪 (Reqwest)](#2-http-客户端追踪-reqwest)
  - [3. HTTP 服务器追踪 (Axum)](#3-http-服务器追踪-axum)
  - [4. 完整示例](#4-完整示例)

---

## 1. HTTP 语义约定概述

根据 OpenTelemetry 规范，HTTP 追踪需要记录以下属性：

```rust
use opentelemetry_semantic_conventions::trace::{
    HTTP_METHOD,
    HTTP_URL,
    HTTP_TARGET,
    HTTP_HOST,
    HTTP_SCHEME,
    HTTP_STATUS_CODE,
    HTTP_REQUEST_CONTENT_LENGTH,
    HTTP_RESPONSE_CONTENT_LENGTH,
    HTTP_USER_AGENT,
};

/// HTTP 客户端 Span 属性
pub struct HttpClientAttributes {
    pub method: String,           // GET, POST, etc.
    pub url: String,              // 完整URL
    pub status_code: u16,         // 200, 404, etc.
    pub request_size: Option<u64>,
    pub response_size: Option<u64>,
}

/// HTTP 服务器 Span 属性
pub struct HttpServerAttributes {
    pub method: String,           // GET, POST, etc.
    pub target: String,           // /api/users
    pub scheme: String,           // http, https
    pub status_code: u16,         // 200, 404, etc.
    pub client_ip: Option<String>,
}
```

---

## 2. HTTP 客户端追踪 (Reqwest)

**完整的 Reqwest 客户端集成**:

```rust
use reqwest::{Client, Request, Response};
use opentelemetry::{global, trace::{SpanKind, Status, TraceContextExt, Tracer}};
use opentelemetry_semantic_conventions::trace::*;

pub struct TracedHttpClient {
    client: Client,
    tracer: opentelemetry::trace::Tracer,
}

impl TracedHttpClient {
    pub fn new() -> Self {
        Self {
            client: Client::new(),
            tracer: global::tracer("http-client"),
        }
    }
    
    /// 发送带追踪的 GET 请求
    #[tracing::instrument(skip(self))]
    pub async fn get(&self, url: &str) -> Result<Response, reqwest::Error> {
        let mut span = self.tracer
            .span_builder(format!("HTTP GET"))
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 设置 HTTP 属性
        span.set_attribute(HTTP_METHOD.string("GET"));
        span.set_attribute(HTTP_URL.string(url.to_string()));
        
        let cx = opentelemetry::Context::current_with_span(span);
        let _guard = cx.attach();
        
        // 发送请求
        let response = self.client.get(url).send().await?;
        
        // 记录响应
        let status = response.status();
        cx.span().set_attribute(HTTP_STATUS_CODE.i64(status.as_u16() as i64));
        
        if status.is_server_error() || status.is_client_error() {
            cx.span().set_status(Status::error(format!("HTTP {}", status)));
        } else {
            cx.span().set_status(Status::Ok);
        }
        
        Ok(response)
    }
    
    /// 通用请求方法
    #[tracing::instrument(skip(self, request))]
    pub async fn execute(&self, request: Request) -> Result<Response, reqwest::Error> {
        let method = request.method().to_string();
        let url = request.url().to_string();
        
        let mut span = self.tracer
            .span_builder(format!("HTTP {}", method))
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        span.set_attribute(HTTP_METHOD.string(method));
        span.set_attribute(HTTP_URL.string(url));
        
        // 注入 trace context
        let cx = opentelemetry::Context::current_with_span(span);
        
        let response = {
            let _guard = cx.attach();
            self.client.execute(request).await?
        };
        
        cx.span().set_attribute(HTTP_STATUS_CODE.i64(response.status().as_u16() as i64));
        
        Ok(response)
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = TracedHttpClient::new();
    
    // 自动追踪 HTTP 请求
    let response = client.get("https://api.example.com/users").await?;
    
    println!("Status: {}", response.status());
    
    Ok(())
}
```

---

## 3. HTTP 服务器追踪 (Axum)

**Axum 服务器中间件**:

```rust
use axum::{
    Router,
    middleware::{self, Next},
    http::{Request, Response, StatusCode},
    body::Body,
};
use opentelemetry::{global, trace::{SpanKind, Status, TraceContextExt}};
use std::time::Instant;

/// HTTP 追踪中间件
pub async fn tracing_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Result<Response<Body>, StatusCode> {
    let start = Instant::now();
    
    let method = request.method().to_string();
    let uri = request.uri().to_string();
    let version = format!("{:?}", request.version());
    
    // 创建 server span
    let tracer = global::tracer("http-server");
    let mut span = tracer
        .span_builder(format!("{} {}", method, uri))
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 设置 HTTP 属性
    span.set_attribute(HTTP_METHOD.string(method.clone()));
    span.set_attribute(HTTP_TARGET.string(uri.clone()));
    span.set_attribute(HTTP_SCHEME.string(
        request.uri().scheme_str().unwrap_or("http").to_string()
    ));
    
    // 记录 User-Agent
    if let Some(user_agent) = request.headers().get("user-agent") {
        if let Ok(ua) = user_agent.to_str() {
            span.set_attribute(HTTP_USER_AGENT.string(ua.to_string()));
        }
    }
    
    let cx = opentelemetry::Context::current_with_span(span);
    
    // 执行请求
    let response = {
        let _guard = cx.attach();
        next.run(request).await
    };
    
    // 记录响应
    let duration = start.elapsed();
    let status = response.status();
    
    cx.span().set_attribute(HTTP_STATUS_CODE.i64(status.as_u16() as i64));
    cx.span().set_attribute(KeyValue::new("http.duration_ms", duration.as_millis() as i64));
    
    if status.is_server_error() {
        cx.span().set_status(Status::error("Server error"));
    } else if status.is_client_error() {
        cx.span().set_status(Status::error("Client error"));
    } else {
        cx.span().set_status(Status::Ok);
    }
    
    tracing::info!(
        method = %method,
        uri = %uri,
        status = %status,
        duration_ms = %duration.as_millis(),
        "Request completed"
    );
    
    Ok(response)
}

/// 应用中间件
pub fn create_app() -> Router {
    Router::new()
        .route("/", axum::routing::get(root_handler))
        .route("/users", axum::routing::get(list_users))
        .route("/users/:id", axum::routing::get(get_user))
        .layer(middleware::from_fn(tracing_middleware))
}

async fn root_handler() -> &'static str {
    "Hello, World!"
}

async fn list_users() -> &'static str {
    "List of users"
}

async fn get_user(axum::extract::Path(id): axum::extract::Path<u64>) -> String {
    format!("User {}", id)
}
```

---

## 4. 完整示例

**客户端 + 服务器完整示例**:

```rust
use axum::{Router, routing::get};
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{trace::{self, TracerProvider}, Resource};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

/// 初始化 OpenTelemetry
async fn init_telemetry() -> TracerProvider {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()
        .expect("Failed to create exporter");
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "http-example"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    provider
}

/// HTTP 服务器
async fn start_server() {
    let app = create_app();
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    tracing::info!("Server listening on {}", listener.local_addr().unwrap());
    
    axum::serve(listener, app).await.unwrap();
}

/// HTTP 客户端测试
async fn test_client() {
    let client = TracedHttpClient::new();
    
    // 测试请求
    match client.get("http://localhost:3000/users").await {
        Ok(response) => {
            tracing::info!("Response: {}", response.status());
        }
        Err(e) => {
            tracing::error!("Request failed: {}", e);
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    let provider = init_telemetry().await;
    
    // 启动服务器
    tokio::spawn(start_server());
    
    // 等待服务器启动
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    // 测试客户端
    test_client().await;
    
    // 等待追踪数据导出
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 关闭
    provider.shutdown()?;
    
    Ok(())
}
```

---

**相关文档**:

- [gRPC 语义约定 Rust实现](02_gRPC_Rust完整版.md)
- [HTTP客户端追踪 Reqwest中间件](../../04_核心组件/08_HTTP_客户端追踪_Reqwest_中间件完整版.md)
- [Context Propagation详解](../../04_核心组件/04_Context_Propagation详解_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
