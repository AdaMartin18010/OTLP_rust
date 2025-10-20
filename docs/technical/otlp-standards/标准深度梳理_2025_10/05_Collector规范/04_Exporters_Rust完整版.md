# Collector Exporters - Rust 完整版

## 目录

- [Collector Exporters - Rust 完整版](#collector-exporters---rust-完整版)
  - [目录](#目录)
  - [1. Exporter 概述](#1-exporter-概述)
    - [1.1 核心职责](#11-核心职责)
    - [1.2 Exporter 接口定义](#12-exporter-接口定义)
  - [2. OTLP Exporter](#2-otlp-exporter)
    - [2.1 gRPC OTLP Exporter](#21-grpc-otlp-exporter)
    - [2.2 HTTP/JSON OTLP Exporter](#22-httpjson-otlp-exporter)
  - [3. Jaeger Exporter](#3-jaeger-exporter)
    - [3.1 Jaeger Thrift HTTP Exporter](#31-jaeger-thrift-http-exporter)
  - [4. Prometheus Exporter](#4-prometheus-exporter)
    - [4.1 HTTP Server 实现](#41-http-server-实现)
  - [5. Logging Exporter](#5-logging-exporter)
    - [5.1 实现](#51-实现)
  - [6. 自定义 Exporter 开发](#6-自定义-exporter-开发)
    - [6.1 Elasticsearch Exporter](#61-elasticsearch-exporter)
    - [6.2 InfluxDB Exporter](#62-influxdb-exporter)
  - [7. Exporter 可靠性设计](#7-exporter-可靠性设计)
    - [7.1 重试机制](#71-重试机制)
    - [7.2 超时控制](#72-超时控制)
    - [7.3 降级策略](#73-降级策略)
  - [8. 完整示例](#8-完整示例)
    - [8.1 多 Exporter 并行导出](#81-多-exporter-并行导出)
  - [总结](#总结)

---

## 1. Exporter 概述

**Exporter** 是 Collector 的数据出口，负责将处理后的遥测数据发送到后端存储系统。

### 1.1 核心职责

```text
Processor → [Exporter] → 后端存储
               ↓
          重试/降级/缓存
```

**关键功能**：

- **协议转换**：OTLP → Jaeger、Zipkin、Prometheus
- **网络传输**：gRPC、HTTP、TCP
- **可靠性保障**：重试、超时、降级
- **批量发送**：减少网络开销

### 1.2 Exporter 接口定义

```rust
use async_trait::async_trait;
use opentelemetry::trace::TraceError;
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};
use std::sync::Arc;

#[async_trait]
pub trait CollectorExporter: Send + Sync {
    /// Exporter 名称
    fn name(&self) -> &str;
    
    /// 导出 Traces
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError>;
    
    /// 导出 Metrics
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError>;
    
    /// 导出 Logs
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<(), ExporterError>;
    
    /// 关闭 Exporter
    async fn shutdown(&self) -> Result<(), ExporterError>;
}

#[derive(Debug, thiserror::Error)]
pub enum ExporterError {
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Backend error: {0}")]
    BackendError(String),
    
    #[error("Timeout")]
    Timeout,
}
```

---

## 2. OTLP Exporter

使用 OTLP 协议（gRPC/HTTP）导出数据。

### 2.1 gRPC OTLP Exporter

```rust
use tonic::transport::{Channel, ClientTlsConfig};
use opentelemetry_proto::tonic::collector::trace::v1::{
    trace_service_client::TraceServiceClient,
    ExportTraceServiceRequest,
};
use opentelemetry_proto::tonic::trace::v1::{ResourceSpans, ScopeSpans, Span};

pub struct OtlpGrpcExporter {
    client: TraceServiceClient<Channel>,
    endpoint: String,
}

impl OtlpGrpcExporter {
    pub async fn new(endpoint: String) -> Result<Self, ExporterError> {
        let channel = Channel::from_shared(endpoint.clone())
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?
            .connect()
            .await
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        let client = TraceServiceClient::new(channel);
        
        Ok(Self { client, endpoint })
    }
    
    pub async fn new_with_tls(
        endpoint: String,
        cert_path: &str,
        key_path: &str,
    ) -> Result<Self, ExporterError> {
        use std::fs;
        
        let cert = fs::read_to_string(cert_path)
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        let key = fs::read_to_string(key_path)
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        let identity = tonic::transport::Identity::from_pem(cert, key);
        
        let tls_config = ClientTlsConfig::new()
            .identity(identity);
        
        let channel = Channel::from_shared(endpoint.clone())
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?
            .tls_config(tls_config)
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?
            .connect()
            .await
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        let client = TraceServiceClient::new(channel);
        
        Ok(Self { client, endpoint })
    }
}

#[async_trait]
impl CollectorExporter for OtlpGrpcExporter {
    fn name(&self) -> &str {
        "otlp_grpc"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        // 转换为 OTLP 格式
        let resource_spans = convert_to_resource_spans(spans);
        
        let request = ExportTraceServiceRequest {
            resource_spans,
        };
        
        let mut client = self.client.clone();
        
        client.export(request)
            .await
            .map_err(|e| ExporterError::BackendError(e.to_string()))?;
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        // 实现类似逻辑
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        // 实现类似逻辑
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}

fn convert_to_resource_spans(spans: Vec<SpanData>) -> Vec<ResourceSpans> {
    // 实现 SpanData → ResourceSpans 转换
    todo!()
}
```

### 2.2 HTTP/JSON OTLP Exporter

```rust
use reqwest::Client;
use serde_json::json;

pub struct OtlpHttpExporter {
    client: Client,
    endpoint: String,
}

impl OtlpHttpExporter {
    pub fn new(endpoint: String) -> Self {
        Self {
            client: Client::new(),
            endpoint,
        }
    }
}

#[async_trait]
impl CollectorExporter for OtlpHttpExporter {
    fn name(&self) -> &str {
        "otlp_http"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        let payload = json!({
            "resourceSpans": convert_to_json(spans),
        });
        
        let response = self.client
            .post(format!("{}/v1/traces", self.endpoint))
            .header("Content-Type", "application/json")
            .json(&payload)
            .send()
            .await
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        if !response.status().is_success() {
            return Err(ExporterError::BackendError(format!(
                "Status: {}",
                response.status()
            )));
        }
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}

fn convert_to_json(spans: Vec<SpanData>) -> serde_json::Value {
    // 实现转换
    json!([])
}
```

---

## 3. Jaeger Exporter

导出到 Jaeger 后端（支持 Agent 和 Collector 模式）。

### 3.1 Jaeger Thrift HTTP Exporter

```rust
use reqwest::Client;

pub struct JaegerExporter {
    client: Client,
    endpoint: String,
}

impl JaegerExporter {
    pub fn new(endpoint: String) -> Self {
        Self {
            client: Client::new(),
            endpoint,
        }
    }
}

#[async_trait]
impl CollectorExporter for JaegerExporter {
    fn name(&self) -> &str {
        "jaeger"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        // 转换为 Jaeger Thrift 格式
        let batch = convert_to_jaeger_batch(spans);
        
        let response = self.client
            .post(format!("{}/api/traces", self.endpoint))
            .header("Content-Type", "application/x-thrift")
            .body(serialize_thrift(&batch))
            .send()
            .await
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        if !response.status().is_success() {
            return Err(ExporterError::BackendError(format!(
                "Status: {}",
                response.status()
            )));
        }
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        Err(ExporterError::BackendError("Not supported".to_string()))
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        Err(ExporterError::BackendError("Not supported".to_string()))
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}

fn convert_to_jaeger_batch(spans: Vec<SpanData>) -> JaegerBatch {
    // 实现转换
    todo!()
}

fn serialize_thrift(batch: &JaegerBatch) -> Vec<u8> {
    // 使用 thrift crate 序列化
    todo!()
}
```

---

## 4. Prometheus Exporter

以 Prometheus 格式暴露 Metrics（Pull 模式）。

### 4.1 HTTP Server 实现

```rust
use axum::{routing::get, Router};
use prometheus::{Encoder, TextEncoder, Registry};
use std::sync::Arc;

pub struct PrometheusExporter {
    registry: Arc<Registry>,
    endpoint: String,
}

impl PrometheusExporter {
    pub fn new(endpoint: String) -> Self {
        let registry = Registry::new();
        Self {
            registry: Arc::new(registry),
            endpoint,
        }
    }
    
    pub async fn start(&self) -> Result<(), ExporterError> {
        let registry = self.registry.clone();
        
        let app = Router::new()
            .route("/metrics", get(move || {
                let registry = registry.clone();
                async move {
                    let encoder = TextEncoder::new();
                    let metric_families = registry.gather();
                    let mut buffer = Vec::new();
                    encoder.encode(&metric_families, &mut buffer).unwrap();
                    String::from_utf8(buffer).unwrap()
                }
            }));
        
        tokio::spawn(async move {
            axum::serve(
                tokio::net::TcpListener::bind(&self.endpoint).await.unwrap(),
                app,
            )
            .await
            .unwrap();
        });
        
        Ok(())
    }
}

#[async_trait]
impl CollectorExporter for PrometheusExporter {
    fn name(&self) -> &str {
        "prometheus"
    }
    
    async fn export_traces(&self, _spans: Vec<SpanData>) -> Result<(), ExporterError> {
        Err(ExporterError::BackendError("Not supported".to_string()))
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        // 将 Metrics 注册到 Registry
        for metric in metrics {
            // 根据 Metric 类型创建对应的 Prometheus Collector
        }
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        Err(ExporterError::BackendError("Not supported".to_string()))
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}
```

---

## 5. Logging Exporter

将遥测数据输出到日志（用于调试）。

### 5.1 实现

```rust
use tracing::{info, warn};

pub struct LoggingExporter {
    pretty_print: bool,
}

impl LoggingExporter {
    pub fn new(pretty_print: bool) -> Self {
        Self { pretty_print }
    }
}

#[async_trait]
impl CollectorExporter for LoggingExporter {
    fn name(&self) -> &str {
        "logging"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        for span in spans {
            if self.pretty_print {
                info!("Span: {:#?}", span);
            } else {
                info!("Span: {:?}", span);
            }
        }
        Ok(())
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        for metric in metrics {
            info!("Metric: {:?}", metric);
        }
        Ok(())
    }
    
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<(), ExporterError> {
        for log in logs {
            info!("Log: {:?}", log);
        }
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}
```

---

## 6. 自定义 Exporter 开发

### 6.1 Elasticsearch Exporter

```rust
use elasticsearch::{Elasticsearch, IndexParts};
use serde_json::json;

pub struct ElasticsearchExporter {
    client: Elasticsearch,
    index_prefix: String,
}

impl ElasticsearchExporter {
    pub fn new(url: &str, index_prefix: String) -> Result<Self, ExporterError> {
        let transport = elasticsearch::http::transport::Transport::single_node(url)
            .map_err(|e| ExporterError::NetworkError(e.to_string()))?;
        
        let client = Elasticsearch::new(transport);
        
        Ok(Self { client, index_prefix })
    }
}

#[async_trait]
impl CollectorExporter for ElasticsearchExporter {
    fn name(&self) -> &str {
        "elasticsearch"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        let index_name = format!("{}-traces", self.index_prefix);
        
        for span in spans {
            let doc = json!({
                "trace_id": format!("{:?}", span.span_context.trace_id()),
                "span_id": format!("{:?}", span.span_context.span_id()),
                "name": span.name,
                "start_time": span.start_time,
                "end_time": span.end_time,
                "attributes": span.attributes,
            });
            
            self.client
                .index(IndexParts::Index(&index_name))
                .body(doc)
                .send()
                .await
                .map_err(|e| ExporterError::BackendError(e.to_string()))?;
        }
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        // 实现类似逻辑
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        // 实现类似逻辑
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}
```

### 6.2 InfluxDB Exporter

```rust
use influxdb::{Client, InfluxDbWriteable, Timestamp};

#[derive(InfluxDbWriteable)]
struct SpanMetric {
    time: Timestamp,
    #[influxdb(tag)]
    trace_id: String,
    #[influxdb(tag)]
    span_id: String,
    duration_ms: f64,
    #[influxdb(tag)]
    service_name: String,
}

pub struct InfluxDbExporter {
    client: Client,
}

impl InfluxDbExporter {
    pub fn new(url: &str, database: &str) -> Self {
        let client = Client::new(url, database);
        Self { client }
    }
}

#[async_trait]
impl CollectorExporter for InfluxDbExporter {
    fn name(&self) -> &str {
        "influxdb"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        for span in spans {
            let metric = SpanMetric {
                time: Timestamp::from(span.start_time),
                trace_id: format!("{:?}", span.span_context.trace_id()),
                span_id: format!("{:?}", span.span_context.span_id()),
                duration_ms: (span.end_time - span.start_time).as_millis() as f64,
                service_name: "my-service".to_string(),
            };
            
            self.client
                .query(metric.into_query("spans"))
                .await
                .map_err(|e| ExporterError::BackendError(e.to_string()))?;
        }
        
        Ok(())
    }
    
    async fn export_metrics(&self, _metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn export_logs(&self, _logs: Vec<LogData>) -> Result<(), ExporterError> {
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        Ok(())
    }
}
```

---

## 7. Exporter 可靠性设计

### 7.1 重试机制

```rust
use tokio::time::{sleep, Duration};

pub struct RetryExporter<E: CollectorExporter> {
    inner: E,
    max_retries: usize,
    initial_backoff: Duration,
}

impl<E: CollectorExporter> RetryExporter<E> {
    pub fn new(inner: E, max_retries: usize, initial_backoff: Duration) -> Self {
        Self {
            inner,
            max_retries,
            initial_backoff,
        }
    }
}

#[async_trait]
impl<E: CollectorExporter> CollectorExporter for RetryExporter<E> {
    fn name(&self) -> &str {
        self.inner.name()
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        let mut attempt = 0;
        let mut backoff = self.initial_backoff;
        
        loop {
            match self.inner.export_traces(spans.clone()).await {
                Ok(_) => return Ok(()),
                Err(e) => {
                    attempt += 1;
                    if attempt >= self.max_retries {
                        return Err(e);
                    }
                    
                    warn!("Export failed (attempt {}): {}, retrying in {:?}", attempt, e, backoff);
                    sleep(backoff).await;
                    backoff *= 2;  // 指数退避
                }
            }
        }
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        // 类似实现
        self.inner.export_metrics(metrics).await
    }
    
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<(), ExporterError> {
        self.inner.export_logs(logs).await
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        self.inner.shutdown().await
    }
}
```

### 7.2 超时控制

```rust
use tokio::time::timeout;

pub struct TimeoutExporter<E: CollectorExporter> {
    inner: E,
    timeout: Duration,
}

impl<E: CollectorExporter> TimeoutExporter<E> {
    pub fn new(inner: E, timeout: Duration) -> Self {
        Self { inner, timeout }
    }
}

#[async_trait]
impl<E: CollectorExporter> CollectorExporter for TimeoutExporter<E> {
    fn name(&self) -> &str {
        self.inner.name()
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        timeout(self.timeout, self.inner.export_traces(spans))
            .await
            .map_err(|_| ExporterError::Timeout)?
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        timeout(self.timeout, self.inner.export_metrics(metrics))
            .await
            .map_err(|_| ExporterError::Timeout)?
    }
    
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<(), ExporterError> {
        timeout(self.timeout, self.inner.export_logs(logs))
            .await
            .map_err(|_| ExporterError::Timeout)?
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        self.inner.shutdown().await
    }
}
```

### 7.3 降级策略

```rust
pub struct FallbackExporter {
    primary: Arc<dyn CollectorExporter>,
    fallback: Arc<dyn CollectorExporter>,
}

impl FallbackExporter {
    pub fn new(
        primary: Arc<dyn CollectorExporter>,
        fallback: Arc<dyn CollectorExporter>,
    ) -> Self {
        Self { primary, fallback }
    }
}

#[async_trait]
impl CollectorExporter for FallbackExporter {
    fn name(&self) -> &str {
        "fallback"
    }
    
    async fn export_traces(&self, spans: Vec<SpanData>) -> Result<(), ExporterError> {
        match self.primary.export_traces(spans.clone()).await {
            Ok(_) => Ok(()),
            Err(e) => {
                warn!("Primary exporter failed: {}, using fallback", e);
                self.fallback.export_traces(spans).await
            }
        }
    }
    
    async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<(), ExporterError> {
        match self.primary.export_metrics(metrics.clone()).await {
            Ok(_) => Ok(()),
            Err(e) => {
                warn!("Primary exporter failed: {}, using fallback", e);
                self.fallback.export_metrics(metrics).await
            }
        }
    }
    
    async fn export_logs(&self, logs: Vec<LogData>) -> Result<(), ExporterError> {
        match self.primary.export_logs(logs.clone()).await {
            Ok(_) => Ok(()),
            Err(e) => {
                warn!("Primary exporter failed: {}, using fallback", e);
                self.fallback.export_logs(logs).await
            }
        }
    }
    
    async fn shutdown(&self) -> Result<(), ExporterError> {
        self.primary.shutdown().await?;
        self.fallback.shutdown().await
    }
}
```

---

## 8. 完整示例

### 8.1 多 Exporter 并行导出

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建多个 Exporters
    let otlp_exporter = Arc::new(
        OtlpGrpcExporter::new("http://backend:4317".to_string()).await?
    );
    
    let jaeger_exporter = Arc::new(
        JaegerExporter::new("http://jaeger:14268".to_string())
    );
    
    let logging_exporter = Arc::new(
        LoggingExporter::new(true)
    );
    
    // 2. 添加可靠性包装
    let otlp_with_retry = Arc::new(RetryExporter::new(
        (*otlp_exporter).clone(),
        3,
        Duration::from_secs(1),
    ));
    
    let otlp_with_timeout = Arc::new(TimeoutExporter::new(
        (*otlp_with_retry).clone(),
        Duration::from_secs(30),
    ));
    
    // 3. 并行导出
    let spans = vec![/* ... */];
    
    let results = futures::future::join_all(vec![
        otlp_with_timeout.export_traces(spans.clone()),
        jaeger_exporter.export_traces(spans.clone()),
        logging_exporter.export_traces(spans.clone()),
    ]).await;
    
    for (idx, result) in results.iter().enumerate() {
        match result {
            Ok(_) => println!("Exporter {} succeeded", idx),
            Err(e) => eprintln!("Exporter {} failed: {}", idx, e),
        }
    }
    
    Ok(())
}
```

---

## 总结

Exporter 是 Collector 的**数据出口**，Rust 实现时需要注意：

1. **协议适配**：支持多种后端协议（OTLP、Jaeger、Prometheus）
2. **可靠性**：重试、超时、降级
3. **性能优化**：批量发送、连接池、压缩
4. **错误处理**：网络异常、后端错误的优雅处理
5. **可观测性**：导出成功率、延迟、队列深度

通过模块化设计和可靠性包装，可以构建高可用的数据导出管道。
