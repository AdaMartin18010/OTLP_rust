# Collector Receivers - Rust 完整版

## 目录

- [Collector Receivers - Rust 完整版](#collector-receivers---rust-完整版)
  - [目录](#目录)
  - [1. Receiver 概述](#1-receiver-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 Receiver 接口定义](#12-receiver-接口定义)
  - [2. OTLP Receiver](#2-otlp-receiver)
    - [2.1 gRPC Receiver 实现](#21-grpc-receiver-实现)
    - [2.2 HTTP/JSON Receiver 实现](#22-httpjson-receiver-实现)
    - [2.3 TLS 支持](#23-tls-支持)
  - [3. Jaeger Receiver](#3-jaeger-receiver)
    - [3.1 Thrift HTTP Receiver](#31-thrift-http-receiver)
  - [4. Prometheus Receiver](#4-prometheus-receiver)
    - [4.1 Scrape 实现](#41-scrape-实现)
  - [5. 自定义 Receiver 开发](#5-自定义-receiver-开发)
    - [5.1 Kafka Receiver 示例](#51-kafka-receiver-示例)
  - [6. Receiver 性能优化](#6-receiver-性能优化)
    - [6.1 连接池管理](#61-连接池管理)
    - [6.2 请求速率限制](#62-请求速率限制)
    - [6.3 内存压力控制](#63-内存压力控制)
  - [7. 完整示例](#7-完整示例)
    - [7.1 多协议 Receiver 集成](#71-多协议-receiver-集成)
  - [总结](#总结)

---

## 1. Receiver 概述

**Receiver** 是 Collector 的数据入口，负责接收来自不同数据源的遥测数据。

### 1.1 核心特性

```text
┌──────────────┐
│  应用程序     │
└──────┬───────┘
       │ (Push)
       ↓
┌──────────────┐
│   Receiver   │ ← Pull (Prometheus)
└──────┬───────┘
       │
       ↓
   Processor
```

**两种模式**：

- **Push**：应用主动推送数据（OTLP、Jaeger、Zipkin）
- **Pull**：Collector 主动抓取数据（Prometheus）

### 1.2 Receiver 接口定义

```rust
use async_trait::async_trait;
use opentelemetry::trace::TraceError;
use opentelemetry_sdk::export::trace::SpanData;
use std::sync::Arc;

#[async_trait]
pub trait Receiver: Send + Sync {
    /// Receiver 名称
    fn name(&self) -> &str;
    
    /// 启动 Receiver
    async fn start(&mut self) -> Result<(), ReceiverError>;
    
    /// 停止 Receiver（优雅关闭）
    async fn shutdown(&mut self) -> Result<(), ReceiverError>;
    
    /// 获取数据管道
    fn pipeline(&self) -> Arc<dyn DataPipeline>;
}

#[derive(Debug, thiserror::Error)]
pub enum ReceiverError {
    #[error("Failed to bind address: {0}")]
    BindError(String),
    
    #[error("Protocol error: {0}")]
    ProtocolError(String),
    
    #[error("Shutdown error: {0}")]
    ShutdownError(String),
}
```

---

## 2. OTLP Receiver

OTLP Receiver 支持 **gRPC** 和 **HTTP/JSON** 两种协议。

### 2.1 gRPC Receiver 实现

```rust
use tonic::{transport::Server, Request, Response, Status};
use opentelemetry_proto::tonic::collector::trace::v1::{
    trace_service_server::{TraceService, TraceServiceServer},
    ExportTraceServiceRequest, ExportTraceServiceResponse,
};
use opentelemetry_proto::tonic::collector::metrics::v1::{
    metrics_service_server::{MetricsService, MetricsServiceServer},
    ExportMetricsServiceRequest, ExportMetricsServiceResponse,
};
use opentelemetry_proto::tonic::collector::logs::v1::{
    logs_service_server::{LogsService, LogsServiceServer},
    ExportLogsServiceRequest, ExportLogsServiceResponse,
};
use tokio::sync::mpsc;
use std::net::SocketAddr;

pub struct OtlpGrpcReceiver {
    endpoint: SocketAddr,
    trace_tx: mpsc::Sender<ExportTraceServiceRequest>,
    metrics_tx: mpsc::Sender<ExportMetricsServiceRequest>,
    logs_tx: mpsc::Sender<ExportLogsServiceRequest>,
    shutdown_tx: tokio::sync::watch::Sender<bool>,
}

impl OtlpGrpcReceiver {
    pub fn new(
        endpoint: SocketAddr,
        buffer_size: usize,
    ) -> (
        Self,
        mpsc::Receiver<ExportTraceServiceRequest>,
        mpsc::Receiver<ExportMetricsServiceRequest>,
        mpsc::Receiver<ExportLogsServiceRequest>,
    ) {
        let (trace_tx, trace_rx) = mpsc::channel(buffer_size);
        let (metrics_tx, metrics_rx) = mpsc::channel(buffer_size);
        let (logs_tx, logs_rx) = mpsc::channel(buffer_size);
        let (shutdown_tx, _) = tokio::sync::watch::channel(false);
        
        (
            Self {
                endpoint,
                trace_tx,
                metrics_tx,
                logs_tx,
                shutdown_tx,
            },
            trace_rx,
            metrics_rx,
            logs_rx,
        )
    }
}

#[async_trait]
impl Receiver for OtlpGrpcReceiver {
    fn name(&self) -> &str {
        "otlp_grpc"
    }
    
    async fn start(&mut self) -> Result<(), ReceiverError> {
        let trace_service = OtlpTraceServiceImpl {
            tx: self.trace_tx.clone(),
        };
        let metrics_service = OtlpMetricsServiceImpl {
            tx: self.metrics_tx.clone(),
        };
        let logs_service = OtlpLogsServiceImpl {
            tx: self.logs_tx.clone(),
        };
        
        let mut shutdown_rx = self.shutdown_tx.subscribe();
        
        tokio::spawn(async move {
            Server::builder()
                .add_service(TraceServiceServer::new(trace_service))
                .add_service(MetricsServiceServer::new(metrics_service))
                .add_service(LogsServiceServer::new(logs_service))
                .serve_with_shutdown(endpoint, async move {
                    let _ = shutdown_rx.changed().await;
                })
                .await
                .unwrap();
        });
        
        Ok(())
    }
    
    async fn shutdown(&mut self) -> Result<(), ReceiverError> {
        self.shutdown_tx.send(true)
            .map_err(|e| ReceiverError::ShutdownError(e.to_string()))?;
        Ok(())
    }
    
    fn pipeline(&self) -> Arc<dyn DataPipeline> {
        todo!()
    }
}

// Trace Service 实现
struct OtlpTraceServiceImpl {
    tx: mpsc::Sender<ExportTraceServiceRequest>,
}

#[tonic::async_trait]
impl TraceService for OtlpTraceServiceImpl {
    async fn export(
        &self,
        request: Request<ExportTraceServiceRequest>,
    ) -> Result<Response<ExportTraceServiceResponse>, Status> {
        let req = request.into_inner();
        
        // 发送到处理管道
        self.tx.send(req)
            .await
            .map_err(|_| Status::internal("Pipeline channel closed"))?;
        
        Ok(Response::new(ExportTraceServiceResponse {
            partial_success: None,
        }))
    }
}

// Metrics Service 实现
struct OtlpMetricsServiceImpl {
    tx: mpsc::Sender<ExportMetricsServiceRequest>,
}

#[tonic::async_trait]
impl MetricsService for OtlpMetricsServiceImpl {
    async fn export(
        &self,
        request: Request<ExportMetricsServiceRequest>,
    ) -> Result<Response<ExportMetricsServiceResponse>, Status> {
        let req = request.into_inner();
        
        self.tx.send(req)
            .await
            .map_err(|_| Status::internal("Pipeline channel closed"))?;
        
        Ok(Response::new(ExportMetricsServiceResponse {
            partial_success: None,
        }))
    }
}

// Logs Service 实现
struct OtlpLogsServiceImpl {
    tx: mpsc::Sender<ExportLogsServiceRequest>,
}

#[tonic::async_trait]
impl LogsService for OtlpLogsServiceImpl {
    async fn export(
        &self,
        request: Request<ExportLogsServiceRequest>,
    ) -> Result<Response<ExportLogsServiceResponse>, Status> {
        let req = request.into_inner();
        
        self.tx.send(req)
            .await
            .map_err(|_| Status::internal("Pipeline channel closed"))?;
        
        Ok(Response::new(ExportLogsServiceResponse {
            partial_success: None,
        }))
    }
}
```

### 2.2 HTTP/JSON Receiver 实现

```rust
use axum::{
    extract::State,
    http::StatusCode,
    response::IntoResponse,
    routing::post,
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

#[derive(Clone)]
pub struct OtlpHttpReceiver {
    endpoint: SocketAddr,
    trace_tx: mpsc::Sender<TracePayload>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct TracePayload {
    pub resource_spans: Vec<ResourceSpan>,
}

impl OtlpHttpReceiver {
    pub fn new(endpoint: SocketAddr, buffer_size: usize) -> (Self, mpsc::Receiver<TracePayload>) {
        let (trace_tx, trace_rx) = mpsc::channel(buffer_size);
        (Self { endpoint, trace_tx }, trace_rx)
    }
}

#[async_trait]
impl Receiver for OtlpHttpReceiver {
    fn name(&self) -> &str {
        "otlp_http"
    }
    
    async fn start(&mut self) -> Result<(), ReceiverError> {
        let app = Router::new()
            .route("/v1/traces", post(handle_traces))
            .route("/v1/metrics", post(handle_metrics))
            .route("/v1/logs", post(handle_logs))
            .with_state(self.clone());
        
        tokio::spawn(async move {
            axum::serve(
                tokio::net::TcpListener::bind(self.endpoint).await.unwrap(),
                app,
            )
            .await
            .unwrap();
        });
        
        Ok(())
    }
    
    async fn shutdown(&mut self) -> Result<(), ReceiverError> {
        Ok(())
    }
    
    fn pipeline(&self) -> Arc<dyn DataPipeline> {
        todo!()
    }
}

async fn handle_traces(
    State(receiver): State<OtlpHttpReceiver>,
    Json(payload): Json<TracePayload>,
) -> impl IntoResponse {
    match receiver.trace_tx.send(payload).await {
        Ok(_) => (StatusCode::OK, ""),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Pipeline error"),
    }
}

async fn handle_metrics(/* ... */) -> impl IntoResponse {
    // 类似实现
    (StatusCode::OK, "")
}

async fn handle_logs(/* ... */) -> impl IntoResponse {
    // 类似实现
    (StatusCode::OK, "")
}
```

### 2.3 TLS 支持

```rust
use tonic::transport::{Identity, ServerTlsConfig};
use std::fs;

pub fn configure_tls(
    cert_path: &str,
    key_path: &str,
) -> Result<ServerTlsConfig, Box<dyn std::error::Error>> {
    let cert = fs::read_to_string(cert_path)?;
    let key = fs::read_to_string(key_path)?;
    
    let identity = Identity::from_pem(cert, key);
    
    let tls_config = ServerTlsConfig::new()
        .identity(identity);
    
    Ok(tls_config)
}

// 在 Server 中使用
async fn start_with_tls() -> Result<(), Box<dyn std::error::Error>> {
    let tls_config = configure_tls("cert.pem", "key.pem")?;
    
    Server::builder()
        .tls_config(tls_config)?
        .add_service(TraceServiceServer::new(service))
        .serve("0.0.0.0:4317".parse()?)
        .await?;
    
    Ok(())
}
```

---

## 3. Jaeger Receiver

接收 Jaeger 格式的 Trace 数据（Thrift over HTTP/UDP）。

### 3.1 Thrift HTTP Receiver

```rust
use axum::{extract::State, http::StatusCode, routing::post, Router};
use bytes::Bytes;

pub struct JaegerReceiver {
    endpoint: SocketAddr,
    tx: mpsc::Sender<JaegerBatch>,
}

#[derive(Debug)]
pub struct JaegerBatch {
    pub spans: Vec<JaegerSpan>,
}

#[async_trait]
impl Receiver for JaegerReceiver {
    fn name(&self) -> &str {
        "jaeger"
    }
    
    async fn start(&mut self) -> Result<(), ReceiverError> {
        let app = Router::new()
            .route("/api/traces", post(handle_jaeger_batch))
            .with_state(self.clone());
        
        tokio::spawn(async move {
            axum::serve(
                tokio::net::TcpListener::bind(self.endpoint).await.unwrap(),
                app,
            )
            .await
            .unwrap();
        });
        
        Ok(())
    }
    
    async fn shutdown(&mut self) -> Result<(), ReceiverError> {
        Ok(())
    }
    
    fn pipeline(&self) -> Arc<dyn DataPipeline> {
        todo!()
    }
}

async fn handle_jaeger_batch(
    State(receiver): State<JaegerReceiver>,
    body: Bytes,
) -> StatusCode {
    // 解析 Thrift 格式
    match parse_thrift_batch(&body) {
        Ok(batch) => {
            if receiver.tx.send(batch).await.is_ok() {
                StatusCode::OK
            } else {
                StatusCode::INTERNAL_SERVER_ERROR
            }
        }
        Err(_) => StatusCode::BAD_REQUEST,
    }
}

fn parse_thrift_batch(data: &[u8]) -> Result<JaegerBatch, Box<dyn std::error::Error>> {
    // 使用 thrift crate 解析
    todo!()
}
```

---

## 4. Prometheus Receiver

**Pull 模式**：Collector 主动抓取 Prometheus 格式的 Metrics。

### 4.1 Scrape 实现

```rust
use reqwest::Client;
use std::time::Duration;
use tokio::time::interval;

pub struct PrometheusReceiver {
    targets: Vec<String>,
    scrape_interval: Duration,
    tx: mpsc::Sender<MetricsPayload>,
}

impl PrometheusReceiver {
    pub fn new(
        targets: Vec<String>,
        scrape_interval: Duration,
        buffer_size: usize,
    ) -> (Self, mpsc::Receiver<MetricsPayload>) {
        let (tx, rx) = mpsc::channel(buffer_size);
        (Self { targets, scrape_interval, tx }, rx)
    }
}

#[async_trait]
impl Receiver for PrometheusReceiver {
    fn name(&self) -> &str {
        "prometheus"
    }
    
    async fn start(&mut self) -> Result<(), ReceiverError> {
        let targets = self.targets.clone();
        let tx = self.tx.clone();
        let scrape_interval = self.scrape_interval;
        
        tokio::spawn(async move {
            let client = Client::new();
            let mut ticker = interval(scrape_interval);
            
            loop {
                ticker.tick().await;
                
                for target in &targets {
                    match scrape_target(&client, target).await {
                        Ok(metrics) => {
                            let _ = tx.send(metrics).await;
                        }
                        Err(e) => {
                            eprintln!("Failed to scrape {}: {}", target, e);
                        }
                    }
                }
            }
        });
        
        Ok(())
    }
    
    async fn shutdown(&mut self) -> Result<(), ReceiverError> {
        Ok(())
    }
    
    fn pipeline(&self) -> Arc<dyn DataPipeline> {
        todo!()
    }
}

async fn scrape_target(
    client: &Client,
    target: &str,
) -> Result<MetricsPayload, Box<dyn std::error::Error>> {
    let response = client.get(target).send().await?;
    let text = response.text().await?;
    
    // 解析 Prometheus 文本格式
    parse_prometheus_format(&text)
}

fn parse_prometheus_format(text: &str) -> Result<MetricsPayload, Box<dyn std::error::Error>> {
    // 使用 prometheus-parser crate
    todo!()
}
```

---

## 5. 自定义 Receiver 开发

### 5.1 Kafka Receiver 示例

```rust
use rdkafka::{
    consumer::{Consumer, StreamConsumer},
    ClientConfig, Message,
};

pub struct KafkaReceiver {
    brokers: String,
    topic: String,
    group_id: String,
    tx: mpsc::Sender<KafkaMessage>,
}

impl KafkaReceiver {
    pub fn new(
        brokers: String,
        topic: String,
        group_id: String,
        buffer_size: usize,
    ) -> (Self, mpsc::Receiver<KafkaMessage>) {
        let (tx, rx) = mpsc::channel(buffer_size);
        (Self { brokers, topic, group_id, tx }, rx)
    }
}

#[async_trait]
impl Receiver for KafkaReceiver {
    fn name(&self) -> &str {
        "kafka"
    }
    
    async fn start(&mut self) -> Result<(), ReceiverError> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("group.id", &self.group_id)
            .set("bootstrap.servers", &self.brokers)
            .set("enable.auto.commit", "false")
            .create()
            .map_err(|e| ReceiverError::ProtocolError(e.to_string()))?;
        
        consumer.subscribe(&[&self.topic])
            .map_err(|e| ReceiverError::ProtocolError(e.to_string()))?;
        
        let tx = self.tx.clone();
        
        tokio::spawn(async move {
            loop {
                match consumer.recv().await {
                    Ok(msg) => {
                        if let Some(payload) = msg.payload() {
                            let kafka_msg = KafkaMessage {
                                payload: payload.to_vec(),
                                topic: msg.topic().to_string(),
                                partition: msg.partition(),
                                offset: msg.offset(),
                            };
                            
                            let _ = tx.send(kafka_msg).await;
                        }
                    }
                    Err(e) => {
                        eprintln!("Kafka error: {}", e);
                    }
                }
            }
        });
        
        Ok(())
    }
    
    async fn shutdown(&mut self) -> Result<(), ReceiverError> {
        Ok(())
    }
    
    fn pipeline(&self) -> Arc<dyn DataPipeline> {
        todo!()
    }
}

#[derive(Debug)]
pub struct KafkaMessage {
    pub payload: Vec<u8>,
    pub topic: String,
    pub partition: i32,
    pub offset: i64,
}
```

---

## 6. Receiver 性能优化

### 6.1 连接池管理

```rust
use tokio::sync::Semaphore;

pub struct ConnectionLimiter {
    semaphore: Arc<Semaphore>,
}

impl ConnectionLimiter {
    pub fn new(max_connections: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_connections)),
        }
    }
    
    pub async fn acquire(&self) -> Result<SemaphorePermit, ReceiverError> {
        self.semaphore.acquire()
            .await
            .map_err(|e| ReceiverError::ProtocolError(e.to_string()))
    }
}
```

### 6.2 请求速率限制

```rust
use governor::{Quota, RateLimiter};
use std::num::NonZeroU32;

pub struct RateLimitedReceiver {
    receiver: Arc<dyn Receiver>,
    limiter: Arc<RateLimiter<String, governor::state::InMemoryState, governor::clock::DefaultClock>>,
}

impl RateLimitedReceiver {
    pub fn new(receiver: Arc<dyn Receiver>, requests_per_sec: u32) -> Self {
        let quota = Quota::per_second(NonZeroU32::new(requests_per_sec).unwrap());
        let limiter = Arc::new(RateLimiter::direct(quota));
        
        Self { receiver, limiter }
    }
    
    pub async fn handle_request(&self, client_id: String) -> Result<(), ReceiverError> {
        self.limiter.until_key_ready(&client_id).await;
        // 处理请求
        Ok(())
    }
}
```

### 6.3 内存压力控制

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct MemoryMonitor {
    current_usage: Arc<AtomicUsize>,
    max_usage: usize,
}

impl MemoryMonitor {
    pub fn new(max_usage_mb: usize) -> Self {
        Self {
            current_usage: Arc::new(AtomicUsize::new(0)),
            max_usage: max_usage_mb * 1024 * 1024,
        }
    }
    
    pub fn can_accept(&self, data_size: usize) -> bool {
        let current = self.current_usage.load(Ordering::Relaxed);
        current + data_size <= self.max_usage
    }
    
    pub fn add(&self, size: usize) {
        self.current_usage.fetch_add(size, Ordering::Relaxed);
    }
    
    pub fn release(&self, size: usize) {
        self.current_usage.fetch_sub(size, Ordering::Relaxed);
    }
}
```

---

## 7. 完整示例

### 7.1 多协议 Receiver 集成

```rust
use std::sync::Arc;
use tokio::sync::mpsc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建共享数据管道
    let (tx, mut rx) = mpsc::channel::<TelemetryData>(10000);
    
    // 2. 启动 OTLP gRPC Receiver
    let (mut otlp_grpc, otlp_trace_rx, _, _) = OtlpGrpcReceiver::new(
        "0.0.0.0:4317".parse()?,
        1000,
    );
    otlp_grpc.start().await?;
    
    // 3. 启动 OTLP HTTP Receiver
    let (mut otlp_http, otlp_http_rx) = OtlpHttpReceiver::new(
        "0.0.0.0:4318".parse()?,
        1000,
    );
    otlp_http.start().await?;
    
    // 4. 启动 Prometheus Receiver
    let (mut prom, prom_rx) = PrometheusReceiver::new(
        vec!["http://app1:9090/metrics".to_string()],
        Duration::from_secs(15),
        1000,
    );
    prom.start().await?;
    
    // 5. 统一处理所有数据
    tokio::spawn(async move {
        while let Some(data) = rx.recv().await {
            // 发送到 Processor
            println!("Received: {:?}", data);
        }
    });
    
    // 6. 等待信号
    tokio::signal::ctrl_c().await?;
    
    // 7. 优雅关闭
    otlp_grpc.shutdown().await?;
    otlp_http.shutdown().await?;
    prom.shutdown().await?;
    
    Ok(())
}

#[derive(Debug)]
enum TelemetryData {
    Trace(Vec<SpanData>),
    Metrics(MetricsPayload),
    Logs(LogsPayload),
}
```

---

## 总结

Receiver 是 Collector 的**数据入口**，Rust 实现时需要注意：

1. **异步网络 I/O**：使用 `tokio` + `tonic`/`axum`
2. **背压控制**：使用 `mpsc::channel` + `Semaphore`
3. **协议转换**：支持多种协议（OTLP、Jaeger、Prometheus）
4. **TLS 支持**：生产环境必须加密传输
5. **可观测性**：Receiver 自身的监控指标（接收速率、错误率、队列深度）

通过模块化设计，可以灵活组合不同的 Receivers，满足多样化的数据采集需求。
