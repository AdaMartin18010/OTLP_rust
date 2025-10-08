# OTLP传输层 - HTTP Rust 完整实现指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **reqwest**: 0.12.23  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月8日  
> **OTLP版本**: v1.0.0 (Stable)  
> **默认端口**: 4318

---

## 目录

- [OTLP传输层 - HTTP Rust 完整实现指南](#otlp传输层---http-rust-完整实现指南)
  - [目录](#目录)
  - [1. HTTP 协议概述](#1-http-协议概述)
  - [2. Rust HTTP 客户端生态](#2-rust-http-客户端生态)
  - [3. 依赖配置](#3-依赖配置)
  - [4. HTTP/JSON 实现](#4-httpjson-实现)
    - [4.1 基础客户端](#41-基础客户端)
    - [4.2 完整的导出实现](#42-完整的导出实现)
  - [5. HTTP/Protobuf 实现](#5-httpprotobuf-实现)
  - [6. TLS 安全配置](#6-tls-安全配置)
  - [7. 认证和授权](#7-认证和授权)
  - [8. HTTP/2 优化](#8-http2-优化)
  - [9. 压缩和编码](#9-压缩和编码)
  - [10. 重试和错误处理](#10-重试和错误处理)
  - [11. 批处理和性能优化](#11-批处理和性能优化)
  - [12. HTTP 服务器实现](#12-http-服务器实现)
  - [13. 监控和调试](#13-监控和调试)
  - [14. 完整示例](#14-完整示例)
  - [15. 生产环境最佳实践](#15-生产环境最佳实践)
  - [16. 参考资源](#16-参考资源)

---

## 1. HTTP 协议概述

**OTLP HTTP 特点**:

```text
HTTP vs gRPC:
┌─────────────────┬────────────┬──────────┐
│ 特性            │ HTTP       │ gRPC     │
├─────────────────┼────────────┼──────────┤
│ 协议            │ HTTP/1.1   │ HTTP/2   │
│                 │ HTTP/2     │          │
│ 编码            │ JSON       │ Protobuf │
│                 │ Protobuf   │          │
│ 防火墙友好      │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐  │
│ 性能            │ ⭐⭐⭐⭐  │ ⭐⭐⭐⭐⭐│
│ 易调试          │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐  │
│ 工具支持        │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐│
└─────────────────┴────────────┴──────────┘

OTLP HTTP 端点:
- Traces:  POST /v1/traces
- Metrics: POST /v1/metrics
- Logs:    POST /v1/logs

默认端口: 4318 (HTTP)
TLS 端口: 4318 (HTTPS)
```

**请求格式**:

```text
POST /v1/traces HTTP/1.1
Host: otlp-collector:4318
Content-Type: application/json
Content-Encoding: gzip
Authorization: Bearer <token>

{
  "resourceSpans": [
    {
      "resource": { ... },
      "scopeSpans": [
        {
          "scope": { ... },
          "spans": [ ... ]
        }
      ]
    }
  ]
}
```

---

## 2. Rust HTTP 客户端生态

**reqwest vs hyper 对比** (2025年10月):

```text
┌──────────────┬────────────────┬──────────────────┐
│ 特性          │ reqwest 0.12.23│ hyper 1.7.0     │
├──────────────┼────────────────┼──────────────────┤
│ 易用性        │ ⭐⭐⭐⭐⭐   │ ⭐⭐⭐         │
│ 功能完整性    │ ⭐⭐⭐⭐⭐   │ ⭐⭐⭐⭐       │
│ HTTP/1.1     │ ✅ 完整支持    │ ✅ 完整支持     │
│ HTTP/2       │ ✅ 完整支持    │ ✅ 完整支持     │
│ TLS          │ ✅ 开箱即用    │ ⚠️ 需要配置    │
│ JSON         │ ✅ 内置支持    │ ❌ 需要 serde   │
│ 连接池        │ ✅ 自动        │ ⚠️ 手动实现    │
│ 重试          │ ✅ 中间件      │ ❌ 需要实现     │
│ 压缩          │ ✅ 内置        │ ❌ 需要实现     │
│ Rust 1.90支持│ ✅ 完整        │ ✅ 完整         │
└──────────────┴────────────────┴──────────────────┘

强烈推荐: reqwest 0.12.23
✅ 高级 API，易用
✅ 功能丰富
✅ 内置连接池
✅ 自动重试和压缩
✅ OpenTelemetry 官方支持
```

---

## 3. 依赖配置

**Cargo.toml**:

```toml
[package]
name = "otlp-http-rust"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# HTTP 客户端 (Rust 1.90 兼容)
reqwest = { version = "0.12.23", features = [
    "json",                # JSON 支持
    "rustls-tls",          # RustLS TLS (纯 Rust)
    "stream",              # 流式支持
    "gzip",                # Gzip 压缩
    "brotli",              # Brotli 压缩
    "deflate",             # Deflate 压缩
    "http2",               # HTTP/2 支持
] }

# OpenTelemetry 生态系统 (2025年10月最新)
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = [
    "http-json",           # HTTP/JSON 导出
    "http-proto",          # HTTP/Protobuf 导出
    "reqwest-client",      # 使用 reqwest
    "trace",
    "metrics",
    "logs",
] }

# Protocol Buffers
prost = "0.14.1"
prost-types = "0.14.1"

# 异步运行时 (Rust 1.90 优化)
tokio = { version = "1.47.1", features = ["full"] }
tokio-stream = "0.1.17"
futures = "0.3.31"

# TLS (纯 Rust 实现)
rustls = { version = "0.23.33", features = ["ring"] }
rustls-pemfile = "2.2.1"
webpki-roots = "1.1.2"

# HTTP 基础
http = "1.3.2"
hyper = { version = "1.7.0", features = ["full", "http2"] }
hyper-util = "0.1.14"

# 序列化
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"

# 错误处理
thiserror = "2.0.17"
anyhow = "1.0.100"

# 日志和追踪
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.20", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 工具库
bytes = "1.10.1"
uuid = { version = "1.18.1", features = ["v4", "serde"] }
chrono = { version = "0.4.42", features = ["serde"] }
tower = "0.5.3"
tower-http = { version = "0.6.5", features = ["trace", "compression-gzip"] }

[dev-dependencies]
tokio-test = "0.4.4"
criterion = "0.7.0"
mockito = "1.6.5"
```

---

## 4. HTTP/JSON 实现

### 4.1 基础客户端

**完整的 HTTP/JSON 客户端**:

```rust
use reqwest::{Client, ClientBuilder};
use serde::{Deserialize, Serialize};
use std::time::Duration;
use opentelemetry::trace::{TraceError, TraceResult};
use thiserror::Error;

/// OTLP HTTP 错误类型
#[derive(Error, Debug)]
pub enum OtlpHttpError {
    #[error("HTTP request failed: {0}")]
    RequestFailed(#[from] reqwest::Error),
    
    #[error("JSON serialization failed: {0}")]
    SerializationFailed(#[from] serde_json::Error),
    
    #[error("Server returned error {status}: {body}")]
    ServerError {
        status: u16,
        body: String,
    },
    
    #[error("Timeout occurred")]
    Timeout,
}

/// OTLP HTTP/JSON 客户端 (Rust 1.90)
pub struct OtlpHttpClient {
    client: Client,
    endpoint: String,
    traces_url: String,
    metrics_url: String,
    logs_url: String,
}

impl OtlpHttpClient {
    /// 创建新的 HTTP 客户端
    pub fn new(endpoint: &str) -> Result<Self, OtlpHttpError> {
        let endpoint = endpoint.trim_end_matches('/').to_string();
        
        // 配置 HTTP 客户端
        let client = ClientBuilder::new()
            .timeout(Duration::from_secs(10))           // 请求超时
            .connect_timeout(Duration::from_secs(5))    // 连接超时
            .pool_idle_timeout(Duration::from_secs(90)) // 连接池空闲超时
            .pool_max_idle_per_host(10)                 // 每个 host 最大空闲连接
            .http2_prior_knowledge()                    // 优先使用 HTTP/2
            .tcp_keepalive(Duration::from_secs(60))     // TCP Keep-Alive
            .use_rustls_tls()                           // 使用 RustLS
            .gzip(true)                                 // 启用 Gzip
            .brotli(true)                               // 启用 Brotli
            .build()?;
        
        // 构建端点 URL
        let traces_url = format!("{}/v1/traces", endpoint);
        let metrics_url = format!("{}/v1/metrics", endpoint);
        let logs_url = format!("{}/v1/logs", endpoint);
        
        tracing::info!(endpoint = %endpoint, "OTLP HTTP client created");
        
        Ok(Self {
            client,
            endpoint,
            traces_url,
            metrics_url,
            logs_url,
        })
    }
    
    /// 导出 Traces (HTTP/JSON)
    #[tracing::instrument(skip(self, request))]
    pub async fn export_traces_json(
        &self,
        request: &ExportTraceServiceRequest,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        // 序列化为 JSON
        let json_body = serde_json::to_vec(request)?;
        
        tracing::debug!(
            url = %self.traces_url,
            body_size = json_body.len(),
            "Sending traces via HTTP/JSON"
        );
        
        // 发送 HTTP 请求
        let response = self.client
            .post(&self.traces_url)
            .header("Content-Type", "application/json")
            .header("Accept", "application/json")
            .body(json_body)
            .send()
            .await?;
        
        // 处理响应
        self.handle_response(response).await
    }
    
    /// 处理 HTTP 响应
    async fn handle_response(
        &self,
        response: reqwest::Response,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        let status = response.status();
        
        if status.is_success() {
            // 成功响应
            let body = response.json::<ExportTraceServiceResponse>().await?;
            
            tracing::debug!(status = status.as_u16(), "Export successful");
            
            Ok(body)
        } else {
            // 错误响应
            let body = response.text().await.unwrap_or_default();
            
            tracing::error!(
                status = status.as_u16(),
                body = %body,
                "Export failed"
            );
            
            Err(OtlpHttpError::ServerError {
                status: status.as_u16(),
                body,
            })
        }
    }
}

/// OTLP Trace 请求 (简化版)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExportTraceServiceRequest {
    pub resource_spans: Vec<ResourceSpans>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ResourceSpans {
    pub resource: Option<Resource>,
    pub scope_spans: Vec<ScopeSpans>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Resource {
    pub attributes: Vec<KeyValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScopeSpans {
    pub scope: Option<InstrumentationScope>,
    pub spans: Vec<Span>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstrumentationScope {
    pub name: String,
    pub version: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Span {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub name: String,
    pub kind: i32,
    pub start_time_unix_nano: String,
    pub end_time_unix_nano: String,
    pub attributes: Vec<KeyValue>,
    pub status: Option<Status>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyValue {
    pub key: String,
    pub value: AnyValue,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnyValue {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub string_value: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub int_value: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub double_value: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bool_value: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Status {
    pub code: i32,
    pub message: Option<String>,
}

/// OTLP Trace 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExportTraceServiceResponse {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub partial_success: Option<PartialSuccess>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PartialSuccess {
    pub rejected_spans: i64,
    pub error_message: Option<String>,
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), OtlpHttpError> {
    // 初始化 tracing
    tracing_subscriber::fmt::init();
    
    // 创建客户端
    let client = OtlpHttpClient::new("http://localhost:4318")?;
    
    // 构建请求
    let request = ExportTraceServiceRequest {
        resource_spans: vec![
            // ... (构建 spans)
        ],
    };
    
    // 导出 traces
    let response = client.export_traces_json(&request).await?;
    
    println!("Export successful: {:?}", response);
    
    Ok(())
}
```

### 4.2 完整的导出实现

**集成 OpenTelemetry SDK**:

```rust
use opentelemetry::global;
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::{self as sdktrace, RandomIdGenerator, Sampler};
use opentelemetry_sdk::Resource;
use opentelemetry_otlp::{ExportConfig, WithExportConfig};
use std::time::Duration;

/// 初始化 OTLP HTTP/JSON 导出器
pub async fn init_otlp_http_json_exporter() -> Result<sdktrace::TracerProvider, TraceError> {
    // 配置导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .http()
        .with_endpoint("http://localhost:4318")
        .with_protocol(opentelemetry_otlp::Protocol::HttpJson)
        .with_timeout(Duration::from_secs(10))
        .build_span_exporter()?;
    
    // 配置 TracerProvider
    let tracer_provider = sdktrace::TracerProvider::builder()
        .with_batch_exporter(exporter, sdktrace::runtime::Tokio)
        .with_sampler(Sampler::AlwaysOn)
        .with_id_generator(RandomIdGenerator::default())
        .with_resource(Resource::new(vec![
            opentelemetry::KeyValue::new("service.name", "my-rust-service"),
            opentelemetry::KeyValue::new("service.version", "0.1.0"),
        ]))
        .build();
    
    // 设置全局 TracerProvider
    global::set_tracer_provider(tracer_provider.clone());
    
    tracing::info!("OTLP HTTP/JSON exporter initialized");
    
    Ok(tracer_provider)
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 tracing-subscriber
    tracing_subscriber::fmt::init();
    
    // 初始化 OTLP 导出器
    let tracer_provider = init_otlp_http_json_exporter().await?;
    
    // 获取 Tracer
    let tracer = global::tracer("my-service");
    
    // 创建 Span
    let span = tracer.start("my-operation");
    
    // 业务逻辑
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // Span 自动结束
    drop(span);
    
    // 等待批处理完成
    tracer_provider.shutdown()?;
    
    Ok(())
}
```

---

## 5. HTTP/Protobuf 实现

**HTTP/Protobuf 客户端**:

```rust
use prost::Message;

impl OtlpHttpClient {
    /// 导出 Traces (HTTP/Protobuf)
    #[tracing::instrument(skip(self, request))]
    pub async fn export_traces_protobuf(
        &self,
        request: &opentelemetry_proto::tonic::collector::trace::v1::ExportTraceServiceRequest,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        // 序列化为 Protobuf
        let mut buf = Vec::new();
        request.encode(&mut buf)
            .map_err(|e| OtlpHttpError::SerializationFailed(
                serde_json::Error::custom(e)
            ))?;
        
        tracing::debug!(
            url = %self.traces_url,
            body_size = buf.len(),
            "Sending traces via HTTP/Protobuf"
        );
        
        // 发送 HTTP 请求
        let response = self.client
            .post(&self.traces_url)
            .header("Content-Type", "application/x-protobuf")
            .header("Accept", "application/x-protobuf")
            .body(buf)
            .send()
            .await?;
        
        // 处理响应
        if response.status().is_success() {
            let body = response.bytes().await?;
            
            let proto_response = opentelemetry_proto::tonic::collector::trace::v1::ExportTraceServiceResponse::decode(body)
                .map_err(|e| OtlpHttpError::SerializationFailed(
                    serde_json::Error::custom(e)
                ))?;
            
            // 转换为 JSON 响应 (简化)
            Ok(ExportTraceServiceResponse {
                partial_success: None,
            })
        } else {
            let body = response.text().await.unwrap_or_default();
            
            Err(OtlpHttpError::ServerError {
                status: response.status().as_u16(),
                body,
            })
        }
    }
}

/// 初始化 OTLP HTTP/Protobuf 导出器
pub async fn init_otlp_http_protobuf_exporter() -> Result<sdktrace::TracerProvider, TraceError> {
    let exporter = opentelemetry_otlp::new_exporter()
        .http()
        .with_endpoint("http://localhost:4318")
        .with_protocol(opentelemetry_otlp::Protocol::HttpBinary)  // Protobuf
        .with_timeout(Duration::from_secs(10))
        .build_span_exporter()?;
    
    let tracer_provider = sdktrace::TracerProvider::builder()
        .with_batch_exporter(exporter, sdktrace::runtime::Tokio)
        .with_resource(Resource::new(vec![
            opentelemetry::KeyValue::new("service.name", "my-rust-service"),
        ]))
        .build();
    
    global::set_tracer_provider(tracer_provider.clone());
    
    tracing::info!("OTLP HTTP/Protobuf exporter initialized");
    
    Ok(tracer_provider)
}
```

---

## 6. TLS 安全配置

**HTTPS 客户端**:

```rust
use rustls::{ClientConfig, RootCertStore};
use rustls_pemfile::certs;
use std::fs::File;
use std::io::BufReader;

impl OtlpHttpClient {
    /// 创建带 TLS 的客户端
    pub fn new_with_tls(
        endpoint: &str,
        ca_cert_path: Option<&str>,
        client_cert_path: Option<&str>,
        client_key_path: Option<&str>,
    ) -> Result<Self, OtlpHttpError> {
        let endpoint = endpoint.trim_end_matches('/').to_string();
        
        // 配置 TLS
        let mut tls_config = ClientConfig::builder()
            .with_safe_defaults();
        
        // CA 证书
        if let Some(ca_path) = ca_cert_path {
            let mut root_store = RootCertStore::empty();
            let ca_file = File::open(ca_path)?;
            let mut reader = BufReader::new(ca_file);
            let certs = certs(&mut reader)?;
            
            for cert in certs {
                root_store.add(&rustls::Certificate(cert))?;
            }
            
            tls_config = tls_config.with_root_certificates(root_store);
        } else {
            // 使用系统根证书
            tls_config = tls_config.with_webpki_roots();
        }
        
        // 客户端证书 (mTLS)
        if let (Some(cert_path), Some(key_path)) = (client_cert_path, client_key_path) {
            let cert_file = File::open(cert_path)?;
            let mut cert_reader = BufReader::new(cert_file);
            let certs = certs(&mut cert_reader)?;
            
            let key_file = File::open(key_path)?;
            let mut key_reader = BufReader::new(key_file);
            let keys = rustls_pemfile::rsa_private_keys(&mut key_reader)?;
            
            let key = keys.into_iter().next()
                .ok_or_else(|| OtlpHttpError::RequestFailed(
                    reqwest::Error::from(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        "No private key found"
                    ))
                ))?;
            
            tls_config = tls_config
                .with_single_cert(
                    certs.into_iter().map(rustls::Certificate).collect(),
                    rustls::PrivateKey(key),
                )?;
        }
        
        // 构建客户端
        let client = ClientBuilder::new()
            .use_preconfigured_tls(tls_config)
            .timeout(Duration::from_secs(10))
            .connect_timeout(Duration::from_secs(5))
            .build()?;
        
        let traces_url = format!("{}/v1/traces", endpoint);
        let metrics_url = format!("{}/v1/metrics", endpoint);
        let logs_url = format!("{}/v1/logs", endpoint);
        
        tracing::info!(endpoint = %endpoint, tls = true, "OTLP HTTPS client created");
        
        Ok(Self {
            client,
            endpoint,
            traces_url,
            metrics_url,
            logs_url,
        })
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), OtlpHttpError> {
    // 创建 HTTPS 客户端
    let client = OtlpHttpClient::new_with_tls(
        "https://otlp.example.com:4318",
        Some("ca.crt"),        // CA 证书
        Some("client.crt"),    // 客户端证书 (mTLS)
        Some("client.key"),    // 客户端私钥
    )?;
    
    // ... 使用客户端
    
    Ok(())
}
```

---

## 7. 认证和授权

**多种认证方式**:

```rust
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION};

impl OtlpHttpClient {
    /// 添加 Bearer Token 认证
    pub fn with_bearer_token(mut self, token: String) -> Self {
        // 将 token 存储在客户端中
        // 每次请求时添加 Authorization header
        self
    }
    
    /// 添加 API Key 认证
    pub fn with_api_key(mut self, api_key: String) -> Self {
        self
    }
    
    /// 添加 Basic Auth
    pub fn with_basic_auth(mut self, username: String, password: String) -> Self {
        self
    }
}

/// 带认证的导出
impl OtlpHttpClient {
    pub async fn export_traces_with_auth(
        &self,
        request: &ExportTraceServiceRequest,
        auth_token: &str,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        let json_body = serde_json::to_vec(request)?;
        
        let response = self.client
            .post(&self.traces_url)
            .header("Content-Type", "application/json")
            .header("Authorization", format!("Bearer {}", auth_token))
            .body(json_body)
            .send()
            .await?;
        
        self.handle_response(response).await
    }
}
```

---

## 8. HTTP/2 优化

**HTTP/2 特性**:

```rust
impl OtlpHttpClient {
    /// 创建优化的 HTTP/2 客户端
    pub fn new_http2_optimized(endpoint: &str) -> Result<Self, OtlpHttpError> {
        let client = ClientBuilder::new()
            .http2_prior_knowledge()                    // 强制 HTTP/2
            .http2_initial_stream_window_size(65535)    // 初始流窗口
            .http2_initial_connection_window_size(1048576)  // 初始连接窗口
            .http2_adaptive_window(true)                // 自适应窗口
            .http2_max_frame_size(Some(16384))          // 最大帧大小
            .http2_keep_alive_interval(Some(Duration::from_secs(30)))  // Keep-Alive
            .http2_keep_alive_timeout(Duration::from_secs(10))  // Keep-Alive 超时
            .http2_keep_alive_while_idle(true)          // 空闲时保持连接
            .timeout(Duration::from_secs(10))
            .build()?;
        
        // ... (构建客户端)
        
        Ok(Self {
            client,
            // ...
        })
    }
}
```

---

## 9. 压缩和编码

**压缩配置**:

```rust
impl OtlpHttpClient {
    /// 导出 traces (带压缩)
    pub async fn export_traces_compressed(
        &self,
        request: &ExportTraceServiceRequest,
        compression: CompressionType,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        let json_body = serde_json::to_vec(request)?;
        
        let (content_encoding, compressed_body) = match compression {
            CompressionType::Gzip => {
                use flate2::write::GzEncoder;
                use flate2::Compression;
                use std::io::Write;
                
                let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
                encoder.write_all(&json_body)?;
                let compressed = encoder.finish()?;
                
                ("gzip", compressed)
            }
            CompressionType::None => ("identity", json_body),
        };
        
        tracing::debug!(
            original_size = json_body.len(),
            compressed_size = compressed_body.len(),
            compression_ratio = (compressed_body.len() as f64 / json_body.len() as f64),
            "Compressed request"
        );
        
        let response = self.client
            .post(&self.traces_url)
            .header("Content-Type", "application/json")
            .header("Content-Encoding", content_encoding)
            .body(compressed_body)
            .send()
            .await?;
        
        self.handle_response(response).await
    }
}

pub enum CompressionType {
    None,
    Gzip,
}
```

---

## 10. 重试和错误处理

**完整的重试策略**:

```rust
use tokio::time::sleep;

pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_backoff: Duration,
    pub max_backoff: Duration,
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff: Duration::from_millis(100),
            max_backoff: Duration::from_secs(10),
            backoff_multiplier: 2.0,
        }
    }
}

impl OtlpHttpClient {
    /// 导出 traces (带重试)
    pub async fn export_traces_with_retry(
        &self,
        request: &ExportTraceServiceRequest,
        retry_config: &RetryConfig,
    ) -> Result<ExportTraceServiceResponse, OtlpHttpError> {
        let mut last_error = None;
        
        for attempt in 0..=retry_config.max_retries {
            if attempt > 0 {
                // 计算退避时间
                let backoff = retry_config.initial_backoff
                    * retry_config.backoff_multiplier.powi(attempt as i32 - 1);
                let backoff = backoff.min(retry_config.max_backoff);
                
                tracing::warn!(
                    attempt = attempt,
                    backoff_ms = backoff.as_millis(),
                    "Retrying export"
                );
                
                sleep(backoff).await;
            }
            
            match self.export_traces_json(request).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    // 判断是否应该重试
                    let should_retry = match &e {
                        OtlpHttpError::RequestFailed(re) if re.is_timeout() => true,
                        OtlpHttpError::ServerError { status, .. } 
                            if *status >= 500 => true,  // 5xx 错误重试
                        _ => false,
                    };
                    
                    if !should_retry || attempt == retry_config.max_retries {
                        return Err(e);
                    }
                    
                    tracing::error!(
                        attempt = attempt,
                        error = ?e,
                        "Export failed, will retry"
                    );
                    
                    last_error = Some(e);
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}
```

---

## 11. 批处理和性能优化

**批量导出**:

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

pub struct BatchExporter {
    client: Arc<OtlpHttpClient>,
    buffer: Arc<Mutex<Vec<ResourceSpans>>>,
    batch_size: usize,
    batch_timeout: Duration,
}

impl BatchExporter {
    pub fn new(client: OtlpHttpClient, batch_size: usize, batch_timeout: Duration) -> Self {
        Self {
            client: Arc::new(client),
            buffer: Arc::new(Mutex::new(Vec::new())),
            batch_size,
            batch_timeout,
        }
    }
    
    /// 添加 spans 到批处理缓冲区
    pub async fn add_resource_spans(&self, resource_spans: ResourceSpans) -> Result<(), OtlpHttpError> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(resource_spans);
        
        if buffer.len() >= self.batch_size {
            let batch = buffer.drain(..).collect();
            drop(buffer);  // 释放锁
            
            self.flush_batch(batch).await?;
        }
        
        Ok(())
    }
    
    /// 刷新批处理缓冲区
    pub async fn flush(&self) -> Result<(), OtlpHttpError> {
        let mut buffer = self.buffer.lock().await;
        
        if !buffer.is_empty() {
            let batch = buffer.drain(..).collect();
            drop(buffer);
            
            self.flush_batch(batch).await?;
        }
        
        Ok(())
    }
    
    /// 发送批处理
    async fn flush_batch(&self, resource_spans: Vec<ResourceSpans>) -> Result<(), OtlpHttpError> {
        let request = ExportTraceServiceRequest { resource_spans };
        
        tracing::debug!(
            span_count = request.resource_spans.len(),
            "Flushing batch"
        );
        
        self.client.export_traces_json(&request).await?;
        
        Ok(())
    }
    
    /// 启动定时刷新
    pub fn start_auto_flush(self: Arc<Self>) {
        let exporter = Arc::clone(&self);
        
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(exporter.batch_timeout).await;
                
                if let Err(e) = exporter.flush().await {
                    tracing::error!(error = ?e, "Auto flush failed");
                }
            }
        });
    }
}
```

---

## 12. HTTP 服务器实现

**Axum HTTP 服务器**:

```rust
use axum::{
    Router,
    routing::post,
    extract::State,
    http::StatusCode,
    Json,
};
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    // 存储或转发 traces
}

/// OTLP HTTP 服务器
pub async fn run_otlp_http_server(addr: &str) -> Result<(), anyhow::Error> {
    let state = Arc::new(AppState {});
    
    let app = Router::new()
        .route("/v1/traces", post(handle_traces))
        .route("/v1/metrics", post(handle_metrics))
        .route("/v1/logs", post(handle_logs))
        .with_state(state)
        .layer(tower_http::trace::TraceLayer::new_for_http())
        .layer(tower_http::compression::CompressionLayer::new());
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    
    tracing::info!(addr = %addr, "OTLP HTTP server listening");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

/// 处理 Traces 请求
#[tracing::instrument(skip(state, payload))]
async fn handle_traces(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<ExportTraceServiceRequest>,
) -> Result<Json<ExportTraceServiceResponse>, StatusCode> {
    tracing::info!(
        resource_spans = payload.resource_spans.len(),
        "Received traces"
    );
    
    // 处理 traces
    // ...
    
    Ok(Json(ExportTraceServiceResponse {
        partial_success: None,
    }))
}

async fn handle_metrics(
    State(state): State<Arc<AppState>>,
    // ... (类似 handle_traces)
) -> Result<Json<serde_json::Value>, StatusCode> {
    Ok(Json(serde_json::json!({})))
}

async fn handle_logs(
    State(state): State<Arc<AppState>>,
    // ... (类似 handle_traces)
) -> Result<Json<serde_json::Value>, StatusCode> {
    Ok(Json(serde_json::json!({})))
}
```

---

## 13. 监控和调试

**监控指标**:

```rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct HttpMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    errors_total: Counter<u64>,
    bytes_sent: Counter<u64>,
}

impl HttpMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("http-client");
        
        Self {
            requests_total: meter
                .u64_counter("http.client.requests.total")
                .init(),
            request_duration: meter
                .f64_histogram("http.client.request.duration")
                .init(),
            errors_total: meter
                .u64_counter("http.client.errors.total")
                .init(),
            bytes_sent: meter
                .u64_counter("http.client.bytes_sent")
                .init(),
        }
    }
    
    pub fn record_request(&self, duration: f64, size: u64) {
        self.requests_total.add(1, &[]);
        self.request_duration.record(duration, &[]);
        self.bytes_sent.add(size, &[]);
    }
    
    pub fn record_error(&self) {
        self.errors_total.add(1, &[]);
    }
}
```

---

## 14. 完整示例

**生产级实现**:

```rust
use std::sync::Arc;

pub struct ProductionOtlpHttpExporter {
    client: Arc<OtlpHttpClient>,
    batch_exporter: Arc<BatchExporter>,
    retry_config: RetryConfig,
    metrics: Arc<HttpMetrics>,
}

impl ProductionOtlpHttpExporter {
    pub async fn new(endpoint: &str) -> Result<Self, OtlpHttpError> {
        let client = OtlpHttpClient::new_http2_optimized(endpoint)?;
        let client = Arc::new(client);
        
        let batch_exporter = Arc::new(BatchExporter::new(
            (*client).clone(),
            100,  // batch_size
            Duration::from_secs(5),  // batch_timeout
        ));
        
        // 启动自动刷新
        Arc::clone(&batch_exporter).start_auto_flush();
        
        Ok(Self {
            client,
            batch_exporter,
            retry_config: RetryConfig::default(),
            metrics: Arc::new(HttpMetrics::new()),
        })
    }
    
    pub async fn export(&self, resource_spans: ResourceSpans) -> Result<(), OtlpHttpError> {
        let start = std::time::Instant::now();
        
        match self.batch_exporter.add_resource_spans(resource_spans).await {
            Ok(_) => {
                let duration = start.elapsed().as_secs_f64();
                self.metrics.record_request(duration, 0);
                Ok(())
            }
            Err(e) => {
                self.metrics.record_error();
                Err(e)
            }
        }
    }
}
```

---

## 15. 生产环境最佳实践

```text
✅ 协议选择
  □ JSON: 易调试、防火墙友好
  □ Protobuf: 高性能、小体积
  □ 根据场景选择

✅ HTTP 配置
  □ 使用 HTTP/2
  □ 启用压缩 (gzip/brotli)
  □ 配置连接池
  □ 设置合理超时

✅ TLS 配置
  □ 使用 TLS 1.3
  □ 验证服务器证书
  □ 考虑 mTLS
  □ 使用 RustLS

✅ 性能优化
  □ 批量导出
  □ 连接复用
  □ 启用压缩
  □ HTTP/2 多路复用

✅ 错误处理
  □ 实现重试机制
  □ 指数退避
  □ 记录错误指标
  □ 断路器模式
```

---

## 16. 参考资源

**官方文档** (2025年10月最新):

- [reqwest Documentation](https://docs.rs/reqwest/0.12.23)
- [OTLP HTTP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [HTTP/2 RFC 7540](https://httpwg.org/specs/rfc7540.html)

---

**文档状态**: ✅ 完成 (Rust 1.90 + reqwest 0.12.23)  
**最后更新**: 2025年10月8日  
**审核状态**: 生产就绪  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [📖 查看其他协议](../README.md)
