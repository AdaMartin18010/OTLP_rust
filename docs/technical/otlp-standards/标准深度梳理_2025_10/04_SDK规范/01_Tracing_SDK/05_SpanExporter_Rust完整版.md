# SpanExporter - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [SpanExporter - Rust 完整实现指南](#spanexporter---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 SpanExporter](#11-什么是-spanexporter)
  - [2. SpanExporter 接口](#2-spanexporter-接口)
    - [2.1 Trait 定义](#21-trait-定义)
  - [3. OTLP Exporter](#3-otlp-exporter)
    - [3.1 gRPC 传输](#31-grpc-传输)
    - [3.2 HTTP/JSON 传输](#32-httpjson-传输)
    - [3.3 TLS 配置](#33-tls-配置)
  - [4. Jaeger Exporter](#4-jaeger-exporter)
    - [4.1 基础配置](#41-基础配置)
  - [5. Zipkin Exporter](#5-zipkin-exporter)
    - [5.1 基础配置](#51-基础配置)
  - [6. Stdout Exporter](#6-stdout-exporter)
    - [6.1 基础用法](#61-基础用法)
    - [6.2 完整示例](#62-完整示例)
  - [7. 自定义 Exporter](#7-自定义-exporter)
    - [7.1 实现简单的日志 Exporter](#71-实现简单的日志-exporter)
    - [7.2 实现 HTTP POST Exporter](#72-实现-http-post-exporter)
  - [8. 完整示例](#8-完整示例)
    - [8.1 生产环境 OTLP Exporter](#81-生产环境-otlp-exporter)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 Exporter 选择](#91-exporter-选择)
    - [9.2 错误处理](#92-错误处理)
    - [9.3 超时配置](#93-超时配置)
  - [总结](#总结)
    - [核心要点](#核心要点)

---

## 1. 概述

### 1.1 什么是 SpanExporter

`SpanExporter` 负责将 Span 数据导出到后端系统，如：

- OpenTelemetry Collector (OTLP)
- Jaeger
- Zipkin
- Prometheus
- 自定义后端

---

## 2. SpanExporter 接口

### 2.1 Trait 定义

```rust
use opentelemetry_sdk::export::trace::SpanData;

#[async_trait::async_trait]
pub trait SpanExporter: Send + Sync {
    /// 导出 Span 批次
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()>;
    
    /// 关闭并清理资源
    fn shutdown(&mut self);
}
```

---

## 3. OTLP Exporter

### 3.1 gRPC 传输

```rust
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

async fn create_otlp_grpc_exporter() -> anyhow::Result<impl opentelemetry_sdk::export::trace::SpanExporter> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(3))
        .with_metadata(vec![("api-key".into(), "secret".into())])
        .build_span_exporter()?;
    
    Ok(exporter)
}
```

### 3.2 HTTP/JSON 传输

```rust
async fn create_otlp_http_exporter() -> anyhow::Result<impl opentelemetry_sdk::export::trace::SpanExporter> {
    let exporter = opentelemetry_otlp::new_exporter()
        .http()
        .with_endpoint("http://localhost:4318/v1/traces")
        .with_timeout(Duration::from_secs(3))
        .with_headers(vec![("Authorization".into(), "Bearer token".into())])
        .build_span_exporter()?;
    
    Ok(exporter)
}
```

### 3.3 TLS 配置

```rust
use opentelemetry_otlp::TonicExporterBuilder;

async fn create_otlp_tls_exporter() -> anyhow::Result<impl opentelemetry_sdk::export::trace::SpanExporter> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("https://otel-collector:4317")
        .with_tls_config(
            tonic::transport::ClientTlsConfig::new()
                .ca_certificate(tonic::transport::Certificate::from_pem(CA_CERT))
                .domain_name("otel-collector"),
        )
        .build_span_exporter()?;
    
    Ok(exporter)
}

const CA_CERT: &str = include_str!("../certs/ca.pem");
```

---

## 4. Jaeger Exporter

### 4.1 基础配置

```toml
[dependencies]
opentelemetry-jaeger = "0.21"
```

```rust
use opentelemetry_jaeger::JaegerExporter;

fn create_jaeger_exporter() -> anyhow::Result<JaegerExporter> {
    let exporter = opentelemetry_jaeger::new_agent_pipeline()
        .with_endpoint("localhost:6831")
        .with_service_name("my-rust-service")
        .build_exporter()?;
    
    Ok(exporter)
}
```

---

## 5. Zipkin Exporter

### 5.1 基础配置

```toml
[dependencies]
opentelemetry-zipkin = "0.20"
```

```rust
use opentelemetry_zipkin::ZipkinExporter;

fn create_zipkin_exporter() -> anyhow::Result<ZipkinExporter> {
    let exporter = opentelemetry_zipkin::new_pipeline()
        .with_service_name("my-rust-service")
        .with_collector_endpoint("http://localhost:9411/api/v2/spans")
        .build_exporter()?;
    
    Ok(exporter)
}
```

---

## 6. Stdout Exporter

### 6.1 基础用法

```rust
use opentelemetry_stdout::SpanExporter as StdoutExporter;

fn create_stdout_exporter() -> StdoutExporter {
    StdoutExporter::default()
}
```

### 6.2 完整示例

```rust
use opentelemetry_sdk::trace::{TracerProvider, SimpleSpanProcessor};

fn setup_stdout_tracing() {
    let exporter = StdoutExporter::default();
    let processor = SimpleSpanProcessor::new(Box::new(exporter));
    
    let provider = TracerProvider::builder()
        .with_span_processor(processor)
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
}
```

---

## 7. 自定义 Exporter

### 7.1 实现简单的日志 Exporter

```rust
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};
use async_trait::async_trait;

pub struct LogExporter;

#[async_trait]
impl SpanExporter for LogExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()> {
        for span in batch {
            println!(
                "[TRACE] {} (TraceID: {:?}, SpanID: {:?})",
                span.name,
                span.span_context.trace_id(),
                span.span_context.span_id()
            );
        }
        Ok(())
    }
    
    fn shutdown(&mut self) {
        println!("LogExporter shutdown");
    }
}
```

### 7.2 实现 HTTP POST Exporter

```rust
use reqwest::Client;
use serde_json::json;

pub struct HttpExporter {
    client: Client,
    endpoint: String,
}

impl HttpExporter {
    pub fn new(endpoint: String) -> Self {
        Self {
            client: Client::new(),
            endpoint,
        }
    }
}

#[async_trait]
impl SpanExporter for HttpExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()> {
        let payload = json!({
            "spans": batch.iter().map(|span| {
                json!({
                    "name": span.name,
                    "trace_id": format!("{:?}", span.span_context.trace_id()),
                    "span_id": format!("{:?}", span.span_context.span_id()),
                })
            }).collect::<Vec<_>>()
        });
        
        self.client
            .post(&self.endpoint)
            .json(&payload)
            .send()
            .await
            .map_err(|e| opentelemetry::trace::TraceError::from(e.to_string()))?;
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        // 清理资源
    }
}
```

---

## 8. 完整示例

### 8.1 生产环境 OTLP Exporter

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{TracerProvider, BatchSpanProcessor};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建 OTLP Exporter
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
            .unwrap_or_else(|_| "http://localhost:4317".to_string()))
        .with_timeout(Duration::from_secs(3))
        .build_span_exporter()?;
    
    // 创建 Batch Processor
    let batch_processor = BatchSpanProcessor::builder(
        otlp_exporter,
        opentelemetry_sdk::runtime::Tokio
    )
    .with_max_queue_size(4096)
    .with_scheduled_delay(Duration::from_secs(2))
    .build();
    
    // 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_span_processor(batch_processor)
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 使用
    let tracer = global::tracer("my-service");
    let span = tracer.start("operation");
    // ...
    drop(span);
    
    // 关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    Ok(())
}
```

---

## 9. 最佳实践

### 9.1 Exporter 选择

```text
生产环境推荐:
✅ OTLP Exporter (gRPC)
  - 标准协议
  - 高性能
  - 支持 Traces/Metrics/Logs

开发/调试:
✅ Stdout Exporter
  - 本地调试
  - 无需外部依赖
```

### 9.2 错误处理

```rust
#[async_trait]
impl SpanExporter for ResilientExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()> {
        for attempt in 1..=3 {
            match self.inner_export(&batch).await {
                Ok(_) => return Ok(()),
                Err(e) if attempt < 3 => {
                    eprintln!("Export failed (attempt {}): {}", attempt, e);
                    tokio::time::sleep(Duration::from_secs(1)).await;
                }
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
    
    fn shutdown(&mut self) {
        // ...
    }
}
```

### 9.3 超时配置

```rust
// 设置合理的超时时间
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_timeout(Duration::from_secs(3))  // 3秒超时
    .build_span_exporter()?;
```

---

## 总结

### 核心要点

1. **OTLP Exporter**: 首选，支持 gRPC/HTTP
2. **Stdout Exporter**: 调试工具
3. **自定义 Exporter**: 实现 `SpanExporter` trait
4. **错误处理**: 实现重试机制
5. **超时配置**: 避免阻塞

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
