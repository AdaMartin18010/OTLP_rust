# OpenTelemetry Collector 架构 - Rust 完整版

## 目录

- [OpenTelemetry Collector 架构 - Rust 完整版](#opentelemetry-collector-架构---rust-完整版)
  - [目录](#目录)
  - [1. Collector 架构概述](#1-collector-架构概述)
    - [1.1 核心价值](#11-核心价值)
    - [1.2 架构分层](#12-架构分层)
  - [2. 核心组件](#2-核心组件)
    - [2.1 Receivers（接收器）](#21-receivers接收器)
    - [2.2 Processors（处理器）](#22-processors处理器)
    - [2.3 Exporters（导出器）](#23-exporters导出器)
    - [2.4 Extensions（扩展）](#24-extensions扩展)
  - [3. 数据流处理模型](#3-数据流处理模型)
    - [3.1 Pipeline 配置](#31-pipeline-配置)
    - [3.2 数据流图](#32-数据流图)
  - [4. Collector 部署模式](#4-collector-部署模式)
    - [4.1 Agent 模式（边车模式）](#41-agent-模式边车模式)
    - [4.2 Gateway 模式（网关模式）](#42-gateway-模式网关模式)
    - [4.3 混合模式](#43-混合模式)
  - [5. Rust 实现架构](#5-rust-实现架构)
    - [5.1 核心依赖](#51-核心依赖)
    - [5.2 Receiver 抽象](#52-receiver-抽象)
    - [5.3 OTLP Receiver 实现](#53-otlp-receiver-实现)
    - [5.4 Processor 抽象](#54-processor-抽象)
    - [5.5 Batch Processor 实现](#55-batch-processor-实现)
    - [5.6 Pipeline 编排](#56-pipeline-编排)
  - [6. 性能优化与最佳实践](#6-性能优化与最佳实践)
    - [6.1 零拷贝优化](#61-零拷贝优化)
    - [6.2 异步批处理](#62-异步批处理)
    - [6.3 背压处理](#63-背压处理)
    - [6.4 配置热更新](#64-配置热更新)
  - [7. 完整示例](#7-完整示例)
    - [7.1 简单的 Collector 实现](#71-简单的-collector-实现)
    - [7.2 生产级配置](#72-生产级配置)
  - [总结](#总结)

---

## 1. Collector 架构概述

OpenTelemetry Collector 是一个**独立的进程**，用于接收、处理和导出遥测数据（Traces、Metrics、Logs）。它充当数据管道的中心枢纽。

### 1.1 核心价值

```text
应用程序 → Exporter → Collector → 后端存储
                        ↓
                   统一处理层
                (过滤/转换/聚合)
```

**优势**：

- **解耦**：应用程序无需直连后端
- **弹性**：缓冲、重试、降级
- **灵活性**：多数据源、多后端
- **统一处理**：采样、过滤、脱敏

### 1.2 架构分层

```text
┌─────────────────────────────────────────┐
│         Extensions（扩展）               │
│   (健康检查/pprof/zpages/认证)           │
└─────────────────────────────────────────┘
           ↓
┌─────────────────────────────────────────┐
│         Receivers（接收器）              │
│   OTLP/Jaeger/Zipkin/Prometheus         │
└─────────────────────────────────────────┘
           ↓
┌─────────────────────────────────────────┐
│        Processors（处理器）              │
│   Batch/Filter/Transform/Attributes      │
└─────────────────────────────────────────┘
           ↓
┌─────────────────────────────────────────┐
│         Exporters（导出器）              │
│   OTLP/Jaeger/Prometheus/Logging        │
└─────────────────────────────────────────┘
```

---

## 2. 核心组件

### 2.1 Receivers（接收器）

接收来自不同数据源的遥测数据。

**特点**：

- **Pull 模式**：主动抓取（如 Prometheus）
- **Push 模式**：被动接收（如 OTLP、Jaeger）
- **协议支持**：gRPC、HTTP、TCP、UDP

### 2.2 Processors（处理器）

对数据进行转换、过滤、增强。

**常用 Processors**：

- `batch`：批量处理，减少网络开销
- `filter`：按规则过滤数据
- `attributes`：修改/添加/删除属性
- `resource`：修改 Resource 信息
- `transform`：复杂数据转换

### 2.3 Exporters（导出器）

将处理后的数据发送到后端存储。

**支持的后端**：

- Jaeger、Zipkin、Prometheus
- InfluxDB、Elasticsearch
- 云服务（AWS X-Ray、Google Cloud Trace）

### 2.4 Extensions（扩展）

提供非核心功能。

**示例**：

- `health_check`：健康检查端点
- `pprof`：Go 性能分析
- `zpages`：调试页面
- `oauth2client`：OAuth2 认证

---

## 3. 数据流处理模型

### 3.1 Pipeline 配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  attributes:
    actions:
      - key: environment
        value: production
        action: insert

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      cert_file: /certs/cert.pem
      key_file: /certs/key.pem

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, attributes]
      exporters: [otlp]
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

### 3.2 数据流图

```text
OTLP Receiver (gRPC:4317)
      ↓
[Batch Processor]
      ↓
[Attributes Processor]
      ↓
OTLP Exporter (backend:4317)
```

---

## 4. Collector 部署模式

### 4.1 Agent 模式（边车模式）

每个应用程序节点运行一个 Collector 实例。

```text
App1 → Collector1 → 中心 Collector
App2 → Collector2 → 中心 Collector
```

**优势**：

- 低延迟
- 本地缓冲
- 减轻应用负担

### 4.2 Gateway 模式（网关模式）

集中式 Collector 接收所有数据。

```text
App1 ↘
App2 → 中心 Collector → 后端存储
App3 ↗
```

**优势**：

- 统一处理
- 降低后端负载
- 集中采样/过滤

### 4.3 混合模式

Agent + Gateway 两层架构。

```text
App → Agent Collector → Gateway Collector → 后端
```

**优势**：

- Agent 负责本地缓冲、初步采样
- Gateway 负责全局聚合、高级处理

---

## 5. Rust 实现架构

### 5.1 核心依赖

```toml
[dependencies]
tokio = { version = "1.40", features = ["full"] }
tonic = "0.12"  # gRPC
axum = "0.7"    # HTTP server
tower = "0.5"   # 中间件
serde = { version = "1.0", features = ["derive"] }
serde_yaml = "0.9"
opentelemetry = "0.24"
opentelemetry-otlp = "0.17"
opentelemetry_sdk = "0.24"
async-trait = "0.1"
```

### 5.2 Receiver 抽象

```rust
use async_trait::async_trait;
use opentelemetry::trace::TraceError;
use opentelemetry_sdk::export::trace::SpanData;

#[async_trait]
pub trait Receiver: Send + Sync {
    /// 启动 Receiver
    async fn start(&mut self) -> Result<(), TraceError>;
    
    /// 停止 Receiver
    async fn shutdown(&mut self) -> Result<(), TraceError>;
    
    /// 接收数据（非阻塞）
    async fn receive(&self) -> Vec<SpanData>;
}
```

### 5.3 OTLP Receiver 实现

```rust
use tonic::{transport::Server, Request, Response, Status};
use opentelemetry_proto::tonic::collector::trace::v1::{
    trace_service_server::{TraceService, TraceServiceServer},
    ExportTraceServiceRequest, ExportTraceServiceResponse,
};
use tokio::sync::mpsc;

pub struct OtlpReceiver {
    endpoint: String,
    tx: mpsc::Sender<ExportTraceServiceRequest>,
}

impl OtlpReceiver {
    pub fn new(endpoint: String, buffer_size: usize) -> (Self, mpsc::Receiver<ExportTraceServiceRequest>) {
        let (tx, rx) = mpsc::channel(buffer_size);
        (Self { endpoint, tx }, rx)
    }
}

#[async_trait]
impl Receiver for OtlpReceiver {
    async fn start(&mut self) -> Result<(), TraceError> {
        let service = OtlpTraceService {
            tx: self.tx.clone(),
        };
        
        Server::builder()
            .add_service(TraceServiceServer::new(service))
            .serve(self.endpoint.parse().unwrap())
            .await
            .map_err(|e| TraceError::Other(Box::new(e)))
    }
    
    async fn shutdown(&mut self) -> Result<(), TraceError> {
        // 优雅关闭
        Ok(())
    }
    
    async fn receive(&self) -> Vec<SpanData> {
        // 从 channel 接收数据
        vec![]
    }
}

struct OtlpTraceService {
    tx: mpsc::Sender<ExportTraceServiceRequest>,
}

#[tonic::async_trait]
impl TraceService for OtlpTraceService {
    async fn export(
        &self,
        request: Request<ExportTraceServiceRequest>,
    ) -> Result<Response<ExportTraceServiceResponse>, Status> {
        // 发送到处理队列
        self.tx.send(request.into_inner())
            .await
            .map_err(|_| Status::internal("channel closed"))?;
        
        Ok(Response::new(ExportTraceServiceResponse {
            partial_success: None,
        }))
    }
}
```

### 5.4 Processor 抽象

```rust
use async_trait::async_trait;

#[async_trait]
pub trait Processor: Send + Sync {
    /// 处理单个 Span
    async fn process(&self, span: SpanData) -> Option<SpanData>;
    
    /// 批量处理
    async fn process_batch(&self, spans: Vec<SpanData>) -> Vec<SpanData> {
        let mut result = Vec::new();
        for span in spans {
            if let Some(processed) = self.process(span).await {
                result.push(processed);
            }
        }
        result
    }
}
```

### 5.5 Batch Processor 实现

```rust
use std::time::Duration;
use tokio::time::interval;

pub struct BatchProcessor {
    max_batch_size: usize,
    timeout: Duration,
    buffer: tokio::sync::Mutex<Vec<SpanData>>,
}

impl BatchProcessor {
    pub fn new(max_batch_size: usize, timeout: Duration) -> Self {
        Self {
            max_batch_size,
            timeout,
            buffer: tokio::sync::Mutex::new(Vec::with_capacity(max_batch_size)),
        }
    }
    
    pub async fn add(&self, span: SpanData) -> Option<Vec<SpanData>> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(span);
        
        if buffer.len() >= self.max_batch_size {
            Some(buffer.drain(..).collect())
        } else {
            None
        }
    }
    
    pub async fn flush(&self) -> Vec<SpanData> {
        let mut buffer = self.buffer.lock().await;
        buffer.drain(..).collect()
    }
    
    pub async fn start_timer<F>(&self, mut flush_fn: F)
    where
        F: FnMut(Vec<SpanData>) + Send + 'static,
    {
        let mut ticker = interval(self.timeout);
        loop {
            ticker.tick().await;
            let batch = self.flush().await;
            if !batch.is_empty() {
                flush_fn(batch);
            }
        }
    }
}
```

### 5.6 Pipeline 编排

```rust
use std::sync::Arc;

pub struct Pipeline {
    receivers: Vec<Arc<dyn Receiver>>,
    processors: Vec<Arc<dyn Processor>>,
    exporters: Vec<Arc<dyn SpanExporter>>,
}

impl Pipeline {
    pub fn builder() -> PipelineBuilder {
        PipelineBuilder::default()
    }
    
    pub async fn run(self) -> Result<(), TraceError> {
        // 启动所有 Receivers
        for receiver in &self.receivers {
            // 启动逻辑
        }
        
        // 数据处理循环
        loop {
            // 1. 从 Receiver 接收数据
            let mut spans = Vec::new();
            for receiver in &self.receivers {
                spans.extend(receiver.receive().await);
            }
            
            // 2. 通过 Processors 处理
            for processor in &self.processors {
                spans = processor.process_batch(spans).await;
            }
            
            // 3. 通过 Exporters 导出
            for exporter in &self.exporters {
                exporter.export(spans.clone()).await?;
            }
        }
    }
}

#[derive(Default)]
pub struct PipelineBuilder {
    receivers: Vec<Arc<dyn Receiver>>,
    processors: Vec<Arc<dyn Processor>>,
    exporters: Vec<Arc<dyn SpanExporter>>,
}

impl PipelineBuilder {
    pub fn with_receiver(mut self, receiver: Arc<dyn Receiver>) -> Self {
        self.receivers.push(receiver);
        self
    }
    
    pub fn with_processor(mut self, processor: Arc<dyn Processor>) -> Self {
        self.processors.push(processor);
        self
    }
    
    pub fn with_exporter(mut self, exporter: Arc<dyn SpanExporter>) -> Self {
        self.exporters.push(exporter);
        self
    }
    
    pub fn build(self) -> Pipeline {
        Pipeline {
            receivers: self.receivers,
            processors: self.processors,
            exporters: self.exporters,
        }
    }
}
```

---

## 6. 性能优化与最佳实践

### 6.1 零拷贝优化

```rust
use bytes::Bytes;

pub struct ZeroCopySpan {
    // 使用 Bytes 避免拷贝
    raw_data: Bytes,
}
```

### 6.2 异步批处理

```rust
use tokio::sync::mpsc;

pub async fn batch_handler(
    mut rx: mpsc::Receiver<SpanData>,
    exporter: Arc<dyn SpanExporter>,
) {
    let mut batch = Vec::with_capacity(1024);
    let mut ticker = interval(Duration::from_secs(10));
    
    loop {
        tokio::select! {
            Some(span) = rx.recv() => {
                batch.push(span);
                if batch.len() >= 1024 {
                    let _ = exporter.export(batch.drain(..).collect()).await;
                }
            }
            _ = ticker.tick() => {
                if !batch.is_empty() {
                    let _ = exporter.export(batch.drain(..).collect()).await;
                }
            }
        }
    }
}
```

### 6.3 背压处理

```rust
use tokio::sync::Semaphore;

pub struct RateLimitedReceiver {
    receiver: Arc<dyn Receiver>,
    semaphore: Arc<Semaphore>,
}

impl RateLimitedReceiver {
    pub async fn receive_with_backpressure(&self) -> Vec<SpanData> {
        let _permit = self.semaphore.acquire().await.unwrap();
        self.receiver.receive().await
    }
}
```

### 6.4 配置热更新

```rust
use notify::{Watcher, RecursiveMode, watcher};
use std::sync::RwLock;

pub struct ConfigManager {
    config: Arc<RwLock<CollectorConfig>>,
}

impl ConfigManager {
    pub fn watch_config(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let config = self.config.clone();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut watcher = watcher(tx, Duration::from_secs(2))?;
        
        watcher.watch(path, RecursiveMode::NonRecursive)?;
        
        tokio::spawn(async move {
            for event in rx {
                if let Ok(_) = event {
                    // 重新加载配置
                    let new_config = CollectorConfig::load(path).unwrap();
                    *config.write().unwrap() = new_config;
                }
            }
        });
        
        Ok(())
    }
}
```

---

## 7. 完整示例

### 7.1 简单的 Collector 实现

```rust
use opentelemetry::trace::TraceError;
use opentelemetry_sdk::export::trace::SpanExporter;
use std::sync::Arc;
use tokio::sync::mpsc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 OTLP Receiver
    let (receiver, mut rx) = OtlpReceiver::new(
        "0.0.0.0:4317".to_string(),
        10000,
    );
    
    // 2. 创建 Batch Processor
    let batch_processor = Arc::new(BatchProcessor::new(
        1024,
        Duration::from_secs(10),
    ));
    
    // 3. 创建 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://backend:4317")
        .build_span_exporter()?;
    
    // 4. 启动数据处理循环
    tokio::spawn(async move {
        while let Some(request) = rx.recv().await {
            for resource_span in request.resource_spans {
                for scope_span in resource_span.scope_spans {
                    for span in scope_span.spans {
                        // 转换为 SpanData
                        let span_data = convert_proto_span_to_span_data(span);
                        
                        // 批处理
                        if let Some(batch) = batch_processor.add(span_data).await {
                            let _ = exporter.export(batch).await;
                        }
                    }
                }
            }
        }
    });
    
    // 5. 启动定时刷新
    let batch_processor_clone = batch_processor.clone();
    let exporter_clone = exporter.clone();
    tokio::spawn(async move {
        batch_processor_clone.start_timer(move |batch| {
            let exporter = exporter_clone.clone();
            tokio::spawn(async move {
                let _ = exporter.export(batch).await;
            });
        }).await;
    });
    
    // 6. 启动 Receiver
    let mut receiver = receiver;
    receiver.start().await?;
    
    Ok(())
}

fn convert_proto_span_to_span_data(
    span: opentelemetry_proto::tonic::trace::v1::Span
) -> SpanData {
    // 实现协议转换
    todo!()
}
```

### 7.2 生产级配置

```yaml
# collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4
        max_concurrent_streams: 100
        keepalive:
          server_parameters:
            max_connection_idle: 11s
            max_connection_age: 60s
            time: 30s
            timeout: 10s
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - http://localhost:*

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  attributes:
    actions:
      - key: environment
        value: production
        action: upsert
      - key: sensitive_data
        action: delete

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      cert_file: /certs/cert.pem
      key_file: /certs/key.pem
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000

extensions:
  health_check:
    endpoint: :13133
  pprof:
    endpoint: :1777
  zpages:
    endpoint: :55679

service:
  extensions: [health_check, pprof, zpages]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, attributes]
      exporters: [otlp]
```

---

## 总结

OpenTelemetry Collector 架构的核心是 **Receiver → Processor → Exporter** 的管道模型。Rust 实现时需要：

1. **异步优先**：使用 `tokio` + `async/await`
2. **零拷贝**：使用 `Bytes`、`Arc` 避免数据拷贝
3. **背压控制**：使用 `Semaphore`、`mpsc::channel` 限流
4. **批处理**：减少网络开销
5. **可观测性**：Collector 自身的监控（健康检查、指标）

通过模块化设计，Collector 可以灵活组合不同的 Receivers、Processors 和 Exporters，满足各种复杂的生产环境需求。
