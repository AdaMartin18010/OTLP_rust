# OTLP传输层 - HTTP Rust 实现详解

> **Rust版本**: 1.90+  
> **Hyper**: 1.7.0  
> **Reqwest**: 0.12.23  
> **OpenTelemetry**: 0.31.0  
> **Tokio**: 1.47.1  
> **协议版本**: HTTP/1.1 和 HTTP/2  
> **OTLP版本**: v1.0.0 (Stable)  
> **默认端口**: 4318  
> **最后更新**: 2025年10月8日

---

## 目录

- [OTLP传输层 - HTTP Rust 实现详解](#otlp传输层---http-rust-实现详解)
  - [目录](#目录)
  - [1. Rust HTTP 概述](#1-rust-http-概述)
    - [1.1 Hyper vs Reqwest](#11-hyper-vs-reqwest)
    - [1.2 特性对比](#12-特性对比)
  - [2. 依赖配置](#2-依赖配置)
  - [3. HTTP 客户端实现 (Reqwest)](#3-http-客户端实现-reqwest)
    - [3.1 基础客户端](#31-基础客户端)
    - [3.2 Protobuf 编码](#32-protobuf-编码)
    - [3.3 JSON 编码](#33-json-编码)
    - [3.4 压缩支持](#34-压缩支持)
  - [4. HTTP 服务器实现 (Hyper)](#4-http-服务器实现-hyper)
    - [4.1 基础服务器](#41-基础服务器)
    - [4.2 路由处理](#42-路由处理)
    - [4.3 Axum 集成](#43-axum-集成)
  - [5. 高级特性](#5-高级特性)
    - [5.1 TLS 配置](#51-tls-配置)
    - [5.2 认证和授权](#52-认证和授权)
    - [5.3 CORS 支持](#53-cors-支持)
    - [5.4 中间件](#54-中间件)
  - [6. 错误处理](#6-错误处理)
    - [6.1 HTTP 状态码映射](#61-http-状态码映射)
    - [6.2 重试机制](#62-重试机制)
    - [6.3 超时处理](#63-超时处理)
  - [7. 性能优化](#7-性能优化)
    - [7.1 连接池](#71-连接池)
    - [7.2 批处理](#72-批处理)
    - [7.3 零拷贝优化](#73-零拷贝优化)
  - [8. 监控和可观测性](#8-监控和可观测性)
  - [9. 生产环境最佳实践](#9-生产环境最佳实践)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [Rust 特性](#rust-特性)

---

## 1. Rust HTTP 概述

### 1.1 Hyper vs Reqwest

```text
Hyper (底层 HTTP 库):
✅ 纯 Rust 实现
✅ 零拷贝 HTTP/1.1 和 HTTP/2
✅ 异步优先设计
✅ 可自定义性强
❌ API 相对底层
❌ 需要手动处理连接池

Reqwest (高级 HTTP 客户端):
✅ 基于 Hyper 构建
✅ 简洁易用的 API
✅ 内置连接池
✅ 自动处理重定向
✅ Cookie 管理
✅ 代理支持
✅ JSON 序列化集成
```

### 1.2 特性对比

| 特性 | Hyper | Reqwest | 推荐场景 |
|-----|-------|---------|---------|
| 易用性 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Reqwest |
| 性能 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Hyper (底层优化) |
| 灵活性 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Hyper |
| 连接池 | 需手动 | 内置 | Reqwest |
| 客户端 | ✅ | ✅ | 都支持 |
| 服务器 | ✅ | ❌ | Hyper (或 Axum) |

**推荐方案**:

- **客户端**: Reqwest (简洁、成熟)
- **服务器**: Axum (基于 Hyper，高级抽象)

---

## 2. 依赖配置

```toml
[dependencies]
# HTTP 客户端 - Reqwest 0.12.23
reqwest = { version = "0.12.23", features = [
    "json",             # JSON 序列化
    "rustls-tls",       # RustLS TLS 支持 (推荐)
    "stream",           # 流式处理
    "gzip",             # Gzip 压缩
    "brotli",           # Brotli 压缩
    "deflate",          # Deflate 压缩
] }

# HTTP 底层库 - Hyper 1.7.0
hyper = { version = "1.7.0", features = ["full", "http2"] }
hyper-util = "0.1.18"
hyper-rustls = "0.28.2"
http = "1.3.2"
http-body-util = "0.1.4"

# Web 框架 - Axum 0.8.7 (服务器)
axum = { version = "0.8.7", features = ["macros", "multipart", "tracing"] }
tower = "0.5.3"
tower-http = { version = "0.6.7", features = ["cors", "trace", "compression-gzip"] }

# OpenTelemetry - 0.31.0
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json", "http-proto", "trace", "metrics", "logs"] }
opentelemetry-proto = { version = "0.31.0", features = ["gen-tonic", "trace", "metrics", "logs"] }

# 异步运行时 - Tokio 1.47.1
tokio = { version = "1.47.1", features = ["full"] }

# TLS - RustLS
rustls = { version = "0.23.33", features = ["ring"] }
tokio-rustls = "0.26.5"
rustls-pemfile = "2.2.1"

# 数据序列化
bytes = "1.10.1"
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"
prost = "0.14.1"

# 错误处理
anyhow = "1.0.100"
thiserror = "2.0.17"

# 追踪
tracing = "0.1.41"
tracing-subscriber = "0.3.20"
```

---

## 3. HTTP 客户端实现 (Reqwest)

### 3.1 基础客户端

```rust
use reqwest::{Client, ClientBuilder, header};
use std::time::Duration;
use anyhow::Result;

/// HTTP 客户端配置
#[derive(Clone, Debug)]
pub struct HttpClientConfig {
    pub endpoint: String,
    pub timeout: Duration,
    pub connect_timeout: Duration,
    pub pool_idle_timeout: Option<Duration>,
    pub pool_max_idle_per_host: usize,
    pub user_agent: String,
    pub compression: bool,
}

impl Default for HttpClientConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4318".to_string(),
            timeout: Duration::from_secs(10),
            connect_timeout: Duration::from_secs(5),
            pool_idle_timeout: Some(Duration::from_secs(90)),
            pool_max_idle_per_host: 10,
            user_agent: format!("otlp-rust-client/{}", env!("CARGO_PKG_VERSION")),
            compression: true,
        }
    }
}

/// 创建 HTTP 客户端
pub fn create_http_client(config: &HttpClientConfig) -> Result<Client> {
    let mut builder = ClientBuilder::new()
        .timeout(config.timeout)
        .connect_timeout(config.connect_timeout)
        .pool_max_idle_per_host(config.pool_max_idle_per_host)
        .user_agent(&config.user_agent);
    
    // 连接池空闲超时
    if let Some(idle_timeout) = config.pool_idle_timeout {
        builder = builder.pool_idle_timeout(idle_timeout);
    }
    
    // 启用压缩
    if config.compression {
        builder = builder.gzip(true).brotli(true).deflate(true);
    }
    
    // HTTP/2 优先
    builder = builder.http2_prior_knowledge();
    
    let client = builder.build()?;
    
    Ok(client)
}

/// HTTP OTLP 客户端 - 异步实现
pub struct HttpOtlpClient {
    client: Client,
    config: HttpClientConfig,
}

impl HttpOtlpClient {
    /// 创建新的客户端
    pub fn new(config: HttpClientConfig) -> Result<Self> {
        let client = create_http_client(&config)?;
        
        Ok(Self { client, config })
    }
    
    /// 获取 Traces 端点
    pub fn traces_endpoint(&self) -> String {
        format!("{}/v1/traces", self.config.endpoint)
    }
    
    /// 获取 Metrics 端点
    pub fn metrics_endpoint(&self) -> String {
        format!("{}/v1/metrics", self.config.endpoint)
    }
    
    /// 获取 Logs 端点
    pub fn logs_endpoint(&self) -> String {
        format!("{}/v1/logs", self.config.endpoint)
    }
}
```

### 3.2 Protobuf 编码

```rust
use opentelemetry_proto::tonic::collector::trace::v1::{
    ExportTraceServiceRequest, ExportTraceServiceResponse,
};
use prost::Message;

impl HttpOtlpClient {
    /// 导出 Traces - Protobuf 编码
    pub async fn export_traces_proto(
        &self,
        request: ExportTraceServiceRequest,
    ) -> Result<ExportTraceServiceResponse> {
        // 编码为 Protobuf 二进制
        let mut buf = Vec::new();
        request.encode(&mut buf)?;
        
        // 发送 HTTP POST 请求
        let response = self.client
            .post(self.traces_endpoint())
            .header(header::CONTENT_TYPE, "application/x-protobuf")
            .body(buf)
            .send()
            .await?;
        
        // 检查响应状态
        if !response.status().is_success() {
            let status = response.status();
            let body = response.text().await?;
            return Err(anyhow::anyhow!(
                "HTTP request failed with status {}: {}",
                status,
                body
            ));
        }
        
        // 解码响应
        let bytes = response.bytes().await?;
        let proto_response = ExportTraceServiceResponse::decode(bytes)?;
        
        Ok(proto_response)
    }
    
    /// 带重试的导出
    pub async fn export_traces_proto_with_retry(
        &self,
        request: ExportTraceServiceRequest,
        max_retries: u32,
    ) -> Result<ExportTraceServiceResponse> {
        let mut last_error = None;
        let mut backoff = Duration::from_millis(100);
        
        for attempt in 0..=max_retries {
            match self.export_traces_proto(request.clone()).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    last_error = Some(e);
                    
                    if attempt < max_retries {
                        tracing::warn!(
                            "Export attempt {} failed, retrying in {:?}",
                            attempt + 1,
                            backoff
                        );
                        tokio::time::sleep(backoff).await;
                        backoff *= 2; // 指数退避
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}
```

### 3.3 JSON 编码

```rust
use serde::{Deserialize, Serialize};

/// JSON 请求/响应类型 (需要根据实际 Proto 定义)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonTraceRequest {
    #[serde(rename = "resourceSpans")]
    pub resource_spans: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonTraceResponse {
    #[serde(rename = "partialSuccess", skip_serializing_if = "Option::is_none")]
    pub partial_success: Option<serde_json::Value>,
}

impl HttpOtlpClient {
    /// 导出 Traces - JSON 编码
    pub async fn export_traces_json(
        &self,
        request: JsonTraceRequest,
    ) -> Result<JsonTraceResponse> {
        let response = self.client
            .post(self.traces_endpoint())
            .header(header::CONTENT_TYPE, "application/json")
            .json(&request)
            .send()
            .await?;
        
        if !response.status().is_success() {
            let status = response.status();
            let body = response.text().await?;
            return Err(anyhow::anyhow!(
                "HTTP request failed with status {}: {}",
                status,
                body
            ));
        }
        
        let json_response = response.json::<JsonTraceResponse>().await?;
        
        Ok(json_response)
    }
}
```

### 3.4 压缩支持

```rust
use bytes::Bytes;
use flate2::write::GzEncoder;
use flate2::Compression;
use std::io::Write;

impl HttpOtlpClient {
    /// 导出 Traces - 带 Gzip 压缩
    pub async fn export_traces_compressed(
        &self,
        request: ExportTraceServiceRequest,
    ) -> Result<ExportTraceServiceResponse> {
        // 编码为 Protobuf
        let mut buf = Vec::new();
        request.encode(&mut buf)?;
        
        // Gzip 压缩
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&buf)?;
        let compressed = encoder.finish()?;
        
        tracing::debug!(
            "Compression ratio: {:.2}%",
            (compressed.len() as f64 / buf.len() as f64) * 100.0
        );
        
        // 发送压缩数据
        let response = self.client
            .post(self.traces_endpoint())
            .header(header::CONTENT_TYPE, "application/x-protobuf")
            .header(header::CONTENT_ENCODING, "gzip")
            .body(compressed)
            .send()
            .await?;
        
        if !response.status().is_success() {
            return Err(anyhow::anyhow!(
                "HTTP request failed with status {}",
                response.status()
            ));
        }
        
        let bytes = response.bytes().await?;
        let proto_response = ExportTraceServiceResponse::decode(bytes)?;
        
        Ok(proto_response)
    }
}
```

---

## 4. HTTP 服务器实现 (Hyper)

### 4.1 基础服务器

```rust
use hyper::{Body, Request, Response, Server, StatusCode};
use hyper::service::{make_service_fn, service_fn};
use std::convert::Infallible;
use std::net::SocketAddr;

/// HTTP 服务器配置
pub struct HttpServerConfig {
    pub addr: SocketAddr,
    pub max_body_size: usize,
}

impl Default for HttpServerConfig {
    fn default() -> Self {
        Self {
            addr: "127.0.0.1:4318".parse().unwrap(),
            max_body_size: 4 * 1024 * 1024, // 4MB
        }
    }
}

/// 处理 HTTP 请求
async fn handle_request(req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let path = req.uri().path();
    
    match (req.method(), path) {
        (&hyper::Method::POST, "/v1/traces") => {
            handle_traces(req).await
        }
        (&hyper::Method::POST, "/v1/metrics") => {
            handle_metrics(req).await
        }
        (&hyper::Method::POST, "/v1/logs") => {
            handle_logs(req).await
        }
        _ => {
            Ok(Response::builder()
                .status(StatusCode::NOT_FOUND)
                .body(Body::from("Not Found"))
                .unwrap())
        }
    }
}

/// 处理 Traces 请求
async fn handle_traces(req: Request<Body>) -> Result<Response<Body>, Infallible> {
    // 读取请求体
    let body_bytes = match hyper::body::to_bytes(req.into_body()).await {
        Ok(bytes) => bytes,
        Err(e) => {
            tracing::error!("Failed to read request body: {}", e);
            return Ok(Response::builder()
                .status(StatusCode::BAD_REQUEST)
                .body(Body::from("Bad Request"))
                .unwrap());
        }
    };
    
    // 解码 Protobuf
    match ExportTraceServiceRequest::decode(body_bytes) {
        Ok(request) => {
            tracing::info!(
                "Received {} resource spans",
                request.resource_spans.len()
            );
            
            // 处理数据...
            
            // 返回成功响应
            let response = ExportTraceServiceResponse {
                partial_success: None,
            };
            
            let mut buf = Vec::new();
            response.encode(&mut buf).unwrap();
            
            Ok(Response::builder()
                .status(StatusCode::OK)
                .header(header::CONTENT_TYPE, "application/x-protobuf")
                .body(Body::from(buf))
                .unwrap())
        }
        Err(e) => {
            tracing::error!("Failed to decode request: {}", e);
            Ok(Response::builder()
                .status(StatusCode::BAD_REQUEST)
                .body(Body::from("Invalid Protobuf"))
                .unwrap())
        }
    }
}

// 类似的 handle_metrics 和 handle_logs 实现...

async fn handle_metrics(req: Request<Body>) -> Result<Response<Body>, Infallible> {
    // 类似 handle_traces
    Ok(Response::new(Body::from("OK")))
}

async fn handle_logs(req: Request<Body>) -> Result<Response<Body>, Infallible> {
    // 类似 handle_traces
    Ok(Response::new(Body::from("OK")))
}

/// 启动 HTTP 服务器 - 异步
pub async fn run_http_server(config: HttpServerConfig) -> Result<()> {
    let make_svc = make_service_fn(|_conn| async {
        Ok::<_, Infallible>(service_fn(handle_request))
    });
    
    let server = Server::bind(&config.addr).serve(make_svc);
    
    tracing::info!("HTTP server listening on {}", config.addr);
    
    server.await?;
    
    Ok(())
}
```

### 4.2 路由处理

```rust
use std::collections::HashMap;

/// 简单路由器
pub struct Router {
    routes: HashMap<String, Box<dyn Fn(Request<Body>) -> Response<Body> + Send + Sync>>,
}

impl Router {
    pub fn new() -> Self {
        Self {
            routes: HashMap::new(),
        }
    }
    
    pub fn route<F>(&mut self, path: String, handler: F)
    where
        F: Fn(Request<Body>) -> Response<Body> + Send + Sync + 'static,
    {
        self.routes.insert(path, Box::new(handler));
    }
    
    pub fn handle(&self, req: Request<Body>) -> Response<Body> {
        let path = req.uri().path().to_string();
        
        if let Some(handler) = self.routes.get(&path) {
            handler(req)
        } else {
            Response::builder()
                .status(StatusCode::NOT_FOUND)
                .body(Body::from("Not Found"))
                .unwrap()
        }
    }
}
```

### 4.3 Axum 集成

```rust
use axum::{
    Router,
    extract::State,
    http::StatusCode,
    response::IntoResponse,
    routing::post,
};
use bytes::Bytes;

/// Axum 服务器状态
#[derive(Clone)]
struct AppState {
    // 共享状态
}

/// Traces 处理器 - Axum
async fn axum_handle_traces(
    State(state): State<AppState>,
    body: Bytes,
) -> impl IntoResponse {
    match ExportTraceServiceRequest::decode(body) {
        Ok(request) => {
            tracing::info!(
                "Received {} resource spans",
                request.resource_spans.len()
            );
            
            // 处理数据...
            
            let response = ExportTraceServiceResponse {
                partial_success: None,
            };
            
            let mut buf = Vec::new();
            response.encode(&mut buf).unwrap();
            
            (StatusCode::OK, buf)
        }
        Err(e) => {
            tracing::error!("Failed to decode request: {}", e);
            (StatusCode::BAD_REQUEST, vec![])
        }
    }
}

/// 启动 Axum 服务器
pub async fn run_axum_server(addr: SocketAddr) -> Result<()> {
    let state = AppState {};
    
    let app = Router::new()
        .route("/v1/traces", post(axum_handle_traces))
        .route("/v1/metrics", post(axum_handle_metrics))
        .route("/v1/logs", post(axum_handle_logs))
        .with_state(state)
        .layer(
            tower::ServiceBuilder::new()
                .layer(tower_http::trace::TraceLayer::new_for_http())
                .layer(tower_http::compression::CompressionLayer::new())
        );
    
    tracing::info!("Axum server listening on {}", addr);
    
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;
    
    Ok(())
}

// 类似的 axum_handle_metrics 和 axum_handle_logs...
async fn axum_handle_metrics(State(_): State<AppState>, _body: Bytes) -> impl IntoResponse {
    StatusCode::OK
}

async fn axum_handle_logs(State(_): State<AppState>, _body: Bytes) -> impl IntoResponse {
    StatusCode::OK
}
```

---

## 5. 高级特性

### 5.1 TLS 配置

```rust
use rustls::{Certificate, PrivateKey, ServerConfig};
use tokio_rustls::TlsAcceptor;
use std::sync::Arc;

/// 加载 TLS 配置 - 异步
pub async fn load_tls_config(
    cert_path: &str,
    key_path: &str,
) -> Result<ServerConfig> {
    // 加载证书
    let cert_file = tokio::fs::File::open(cert_path).await?;
    let mut cert_reader = tokio::io::BufReader::new(cert_file);
    let certs = rustls_pemfile::certs(&mut cert_reader)?
        .into_iter()
        .map(Certificate)
        .collect();
    
    // 加载私钥
    let key_file = tokio::fs::File::open(key_path).await?;
    let mut key_reader = tokio::io::BufReader::new(key_file);
    let keys = rustls_pemfile::pkcs8_private_keys(&mut key_reader)?;
    let key = PrivateKey(keys[0].clone());
    
    // 创建 TLS 配置
    let config = ServerConfig::builder()
        .with_safe_defaults()
        .with_no_client_auth()
        .with_single_cert(certs, key)?;
    
    Ok(config)
}

/// 带 TLS 的客户端
pub fn create_https_client(config: &HttpClientConfig) -> Result<Client> {
    let client = ClientBuilder::new()
        .use_rustls_tls()
        .timeout(config.timeout)
        .build()?;
    
    Ok(client)
}
```

### 5.2 认证和授权

```rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
};

/// Bearer Token 认证中间件
pub async fn auth_middleware(
    req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let auth_header = req
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|h| h.to_str().ok());
    
    if let Some(auth) = auth_header {
        if auth.starts_with("Bearer ") {
            let token = &auth[7..];
            
            // 验证 token
            if validate_token(token) {
                return Ok(next.run(req).await);
            }
        }
    }
    
    Err(StatusCode::UNAUTHORIZED)
}

fn validate_token(token: &str) -> bool {
    // 实际的 token 验证逻辑
    !token.is_empty()
}

/// API Key 认证
pub async fn api_key_middleware(
    req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let api_key = req
        .headers()
        .get("x-api-key")
        .and_then(|h| h.to_str().ok());
    
    if let Some(key) = api_key {
        if validate_api_key(key) {
            return Ok(next.run(req).await);
        }
    }
    
    Err(StatusCode::UNAUTHORIZED)
}

fn validate_api_key(key: &str) -> bool {
    // 实际的 API key 验证逻辑
    !key.is_empty()
}
```

### 5.3 CORS 支持

```rust
use tower_http::cors::{CorsLayer, Any};

/// 创建 CORS 层
pub fn create_cors_layer() -> CorsLayer {
    CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([hyper::Method::POST, hyper::Method::GET])
        .allow_headers(Any)
}

/// 带 CORS 的 Axum 应用
pub fn app_with_cors() -> Router {
    Router::new()
        .route("/v1/traces", post(axum_handle_traces))
        .layer(create_cors_layer())
}
```

### 5.4 中间件

```rust
use std::time::Instant;

/// 日志中间件
pub async fn logging_middleware(
    req: Request,
    next: Next,
) -> Response {
    let method = req.method().clone();
    let uri = req.uri().clone();
    let start = Instant::now();
    
    let response = next.run(req).await;
    
    let duration = start.elapsed();
    
    tracing::info!(
        "{} {} - {} ({:?})",
        method,
        uri,
        response.status(),
        duration
    );
    
    response
}

/// 指标中间件
pub async fn metrics_middleware(
    req: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    
    let response = next.run(req).await;
    
    let duration = start.elapsed();
    
    // 记录指标
    REQUESTS_TOTAL.add(1, &[]);
    REQUEST_DURATION.record(duration.as_secs_f64(), &[]);
    
    response
}
```

---

## 6. 错误处理

### 6.1 HTTP 状态码映射

```rust
use hyper::StatusCode;

/// 自定义错误类型
#[derive(thiserror::Error, Debug)]
pub enum HttpOtlpError {
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Unauthorized")]
    Unauthorized,
    
    #[error("Timeout")]
    Timeout,
    
    #[error("Server error: {0}")]
    ServerError(String),
    
    #[error("Network error: {0}")]
    Network(String),
}

impl HttpOtlpError {
    pub fn status_code(&self) -> StatusCode {
        match self {
            Self::BadRequest(_) => StatusCode::BAD_REQUEST,
            Self::Unauthorized => StatusCode::UNAUTHORIZED,
            Self::Timeout => StatusCode::REQUEST_TIMEOUT,
            Self::ServerError(_) => StatusCode::INTERNAL_SERVER_ERROR,
            Self::Network(_) => StatusCode::BAD_GATEWAY,
        }
    }
}

impl IntoResponse for HttpOtlpError {
    fn into_response(self) -> Response {
        let status = self.status_code();
        let body = self.to_string();
        
        Response::builder()
            .status(status)
            .body(Body::from(body))
            .unwrap()
    }
}
```

### 6.2 重试机制

```rust
/// 指数退避重试配置
#[derive(Clone, Debug)]
pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_backoff: Duration,
    pub max_backoff: Duration,
    pub multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff: Duration::from_millis(100),
            max_backoff: Duration::from_secs(30),
            multiplier: 2.0,
        }
    }
}

/// 带重试的 HTTP 请求
pub async fn retry_request<F, Fut, T>(
    operation: F,
    config: &RetryConfig,
) -> Result<T>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let mut backoff = config.initial_backoff;
    let mut last_error = None;
    
    for attempt in 0..=config.max_retries {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                last_error = Some(e);
                
                if attempt < config.max_retries {
                    tracing::warn!(
                        "Request failed (attempt {}), retrying in {:?}",
                        attempt + 1,
                        backoff
                    );
                    
                    tokio::time::sleep(backoff).await;
                    backoff = std::cmp::min(
                        Duration::from_secs_f64(backoff.as_secs_f64() * config.multiplier),
                        config.max_backoff
                    );
                }
            }
        }
    }
    
    Err(last_error.unwrap())
}
```

### 6.3 超时处理

```rust
/// 带超时的请求
pub async fn request_with_timeout<T>(
    operation: impl std::future::Future<Output = Result<T>>,
    timeout: Duration,
) -> Result<T> {
    match tokio::time::timeout(timeout, operation).await {
        Ok(result) => result,
        Err(_) => Err(anyhow::anyhow!("Request timeout")),
    }
}
```

---

## 7. 性能优化

### 7.1 连接池

```rust
// Reqwest 自动管理连接池，可以配置参数

pub fn create_optimized_client() -> Result<Client> {
    let client = ClientBuilder::new()
        .pool_idle_timeout(Duration::from_secs(90))
        .pool_max_idle_per_host(20)          // 每个主机最多20个空闲连接
        .tcp_nodelay(true)                    // 禁用 Nagle 算法
        .tcp_keepalive(Duration::from_secs(60)) // TCP Keep-Alive
        .build()?;
    
    Ok(client)
}
```

### 7.2 批处理

```rust
use tokio::sync::mpsc;
use tokio::time::{interval, Duration};

/// 批处理导出器
pub struct BatchHttpExporter {
    sender: mpsc::Sender<ExportTraceServiceRequest>,
}

impl BatchHttpExporter {
    pub fn new(
        client: HttpOtlpClient,
        batch_size: usize,
        flush_interval: Duration,
    ) -> Self {
        let (tx, mut rx) = mpsc::channel(1000);
        
        tokio::spawn(async move {
            let mut batch = Vec::new();
            let mut ticker = interval(flush_interval);
            
            loop {
                tokio::select! {
                    Some(request) = rx.recv() => {
                        batch.push(request);
                        
                        if batch.len() >= batch_size {
                            flush_batch(&client, &mut batch).await;
                        }
                    }
                    _ = ticker.tick() => {
                        if !batch.is_empty() {
                            flush_batch(&client, &mut batch).await;
                        }
                    }
                }
            }
        });
        
        Self { sender: tx }
    }
    
    pub async fn export(&self, request: ExportTraceServiceRequest) -> Result<()> {
        self.sender.send(request).await?;
        Ok(())
    }
}

async fn flush_batch(
    client: &HttpOtlpClient,
    batch: &mut Vec<ExportTraceServiceRequest>,
) {
    // 合并批次
    let merged = merge_trace_requests(batch.drain(..));
    
    // 导出
    if let Err(e) = client.export_traces_proto(merged).await {
        tracing::error!("Batch export failed: {}", e);
    }
}

fn merge_trace_requests(
    requests: impl Iterator<Item = ExportTraceServiceRequest>,
) -> ExportTraceServiceRequest {
    let mut merged = ExportTraceServiceRequest {
        resource_spans: vec![],
    };
    
    for request in requests {
        merged.resource_spans.extend(request.resource_spans);
    }
    
    merged
}
```

### 7.3 零拷贝优化

```rust
use bytes::Bytes;

/// 零拷贝 HTTP 请求
pub async fn export_zero_copy(
    client: &Client,
    endpoint: &str,
    data: Bytes,  // 使用 Bytes 避免拷贝
) -> Result<Bytes> {
    let response = client
        .post(endpoint)
        .header(header::CONTENT_TYPE, "application/x-protobuf")
        .body(data)  // 直接使用 Bytes，无需拷贝
        .send()
        .await?;
    
    let bytes = response.bytes().await?;
    Ok(bytes)
}
```

---

## 8. 监控和可观测性

```rust
use opentelemetry::metrics::{Counter, Histogram};

/// HTTP 客户端指标
pub struct HttpMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    request_size: Histogram<u64>,
    response_size: Histogram<u64>,
    errors_total: Counter<u64>,
}

impl HttpMetrics {
    pub fn new() -> Self {
        let meter = global::meter("http-client");
        
        Self {
            requests_total: meter
                .u64_counter("http.client.requests.total")
                .init(),
            request_duration: meter
                .f64_histogram("http.client.request.duration")
                .with_unit("ms")
                .init(),
            request_size: meter
                .u64_histogram("http.client.request.size")
                .with_unit("bytes")
                .init(),
            response_size: meter
                .u64_histogram("http.client.response.size")
                .with_unit("bytes")
                .init(),
            errors_total: meter
                .u64_counter("http.client.errors.total")
                .init(),
        }
    }
    
    pub fn record_request(
        &self,
        duration_ms: f64,
        status: u16,
        request_size: u64,
        response_size: u64,
    ) {
        self.requests_total.add(1, &[
            KeyValue::new("status", status as i64),
        ]);
        self.request_duration.record(duration_ms, &[]);
        self.request_size.record(request_size, &[]);
        self.response_size.record(response_size, &[]);
    }
}
```

---

## 9. 生产环境最佳实践

```rust
/// 生产级 HTTP 客户端配置
pub fn production_http_config() -> HttpClientConfig {
    HttpClientConfig {
        endpoint: std::env::var("OTLP_HTTP_ENDPOINT")
            .unwrap_or_else(|_| "https://otlp.example.com:4318".to_string()),
        timeout: Duration::from_secs(30),
        connect_timeout: Duration::from_secs(10),
        pool_idle_timeout: Some(Duration::from_secs(90)),
        pool_max_idle_per_host: 20,
        user_agent: format!(
            "otlp-rust-client/{} ({})",
            env!("CARGO_PKG_VERSION"),
            std::env::consts::OS
        ),
        compression: true,
    }
}
```

**最佳实践清单**:

```text
✅ 使用 HTTPS/TLS 加密
✅ 实现指数退避重试
✅ 配置合理的超时
✅ 使用连接池
✅ 实现批处理
✅ 启用压缩 (Gzip/Brotli)
✅ 监控 HTTP 指标
✅ 添加认证和授权
✅ CORS 配置 (服务器)
✅ 零拷贝数据传输
✅ HTTP/2 优先
✅ 错误处理和日志
✅ 类型安全的 Rust 实现
✅ 异步 I/O 避免阻塞
```

---

## 10. 参考资源

### 官方文档

- [Reqwest](https://docs.rs/reqwest/)
- [Hyper](https://hyper.rs/)
- [Axum](https://docs.rs/axum/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)

### Rust 特性

- [Tokio](https://tokio.rs/)
- [Async Book](https://rust-lang.github.io/async-book/)
- [Rust 1.90](https://blog.rust-lang.org/2024/11/28/Rust-1.90.0.html)

---

**最后更新**: 2025年10月8日  
**维护者**: OTLP Rust团队  
**许可证**: MIT OR Apache-2.0
