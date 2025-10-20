# Rust OTLP Collector 自定义扩展开发完整指南

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025-10-08  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Rust OTLP Collector 自定义扩展开发完整指南](#rust-otlp-collector-自定义扩展开发完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [OpenTelemetry Collector 架构](#opentelemetry-collector-架构)
    - [扩展点](#扩展点)
    - [依赖库](#依赖库)
  - [Collector 架构](#collector-架构)
    - [核心组件接口](#核心组件接口)
    - [Pipeline 组装](#pipeline-组装)
  - [自定义 Receiver](#自定义-receiver)
    - [场景 1: HTTP JSON Receiver](#场景-1-http-json-receiver)
    - [场景 2: Kafka Receiver](#场景-2-kafka-receiver)
  - [自定义 Processor](#自定义-processor)
    - [场景 1: 属性过滤 Processor](#场景-1-属性过滤-processor)
    - [场景 2: 采样 Processor](#场景-2-采样-processor)
    - [场景 3: 批处理 Processor](#场景-3-批处理-processor)
  - [自定义 Exporter](#自定义-exporter)
    - [场景 1: Elasticsearch Exporter](#场景-1-elasticsearch-exporter)
    - [场景 2: ClickHouse Exporter](#场景-2-clickhouse-exporter)
    - [场景 3: S3 Exporter（冷存储）](#场景-3-s3-exporter冷存储)
  - [扩展注册](#扩展注册)
    - [组件注册表](#组件注册表)
  - [配置管理](#配置管理)
    - [YAML 配置](#yaml-配置)
    - [配置加载](#配置加载)
  - [测试与调试](#测试与调试)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [调试工具](#调试工具)
  - [性能优化](#性能优化)
    - [1. 零拷贝优化](#1-零拷贝优化)
    - [2. 批量处理](#2-批量处理)
    - [3. 异步并发](#3-异步并发)
  - [部署与发布](#部署与发布)
    - [Docker 镜像](#docker-镜像)
    - [Kubernetes Deployment](#kubernetes-deployment)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 可观测性](#2-可观测性)
    - [3. 资源管理](#3-资源管理)
    - [4. 配置验证](#4-配置验证)
  - [总结](#总结)
    - [完整性检查表](#完整性检查表)
    - [核心要点](#核心要点)
    - [扩展资源](#扩展资源)

---

## 概述

### OpenTelemetry Collector 架构

OpenTelemetry Collector 是一个与供应商无关的代理，用于接收、处理和导出遥测数据。

```text
┌─────────────┐      ┌──────────────┐      ┌──────────────┐
│  Receivers  │ ──▶ │  Processors  │ ──▶  │  Exporters   │
└─────────────┘      └──────────────┘      └──────────────┘
      ▲                     ▲                      │
      │                     │                      ▼
   数据源              处理/过滤/转换          目标后端
```

### 扩展点

1. **Receiver**: 接收遥测数据
2. **Processor**: 处理和转换数据
3. **Exporter**: 导出数据到后端
4. **Extension**: 额外功能（健康检查、pprof等）

### 依赖库

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-proto = "0.31.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
async-trait = "0.1.87"
futures = "0.3.31"

# 序列化
serde = { version = "1.0.217", features = ["derive"] }
serde_json = "1.0.137"
prost = "0.13.4"
tonic = { version = "0.14.2", features = ["transport"] }

# 配置
config = "0.14.1"
toml = "0.8.19"

# 错误处理
thiserror = "2.0.12"
anyhow = "1.0.98"

# 日志和追踪
tracing = "0.1.41"
tracing-subscriber = "0.3.19"

[dev-dependencies]
criterion = "0.5.1"
mockall = "0.13.1"
```

---

## Collector 架构

### 核心组件接口

```rust
// src/receiver.rs
use async_trait::async_trait;
use opentelemetry::trace::SpanData;
use std::error::Error;

/// Receiver trait - 接收遥测数据
#[async_trait]
pub trait Receiver: Send + Sync {
    /// 启动 Receiver
    async fn start(&self) -> Result<(), Box<dyn Error>>;
    
    /// 停止 Receiver
    async fn shutdown(&self) -> Result<(), Box<dyn Error>>;
    
    /// 接收 Span 数据
    async fn receive_spans(&self) -> Result<Vec<SpanData>, Box<dyn Error>>;
}

// src/processor.rs
#[async_trait]
pub trait Processor: Send + Sync {
    /// 处理 Span 数据
    async fn process(&self, spans: Vec<SpanData>) -> Result<Vec<SpanData>, Box<dyn Error>>;
    
    /// 关闭 Processor
    async fn shutdown(&self) -> Result<(), Box<dyn Error>>;
}

// src/exporter.rs
#[async_trait]
pub trait Exporter: Send + Sync {
    /// 导出 Span 数据
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>>;
    
    /// 关闭 Exporter
    async fn shutdown(&self) -> Result<(), Box<dyn Error>>;
}
```

### Pipeline 组装

```rust
// src/pipeline.rs
use std::sync::Arc;
use tokio::sync::mpsc;

pub struct Pipeline {
    receiver: Arc<dyn Receiver>,
    processors: Vec<Arc<dyn Processor>>,
    exporter: Arc<dyn Exporter>,
}

impl Pipeline {
    pub fn new(
        receiver: Arc<dyn Receiver>,
        processors: Vec<Arc<dyn Processor>>,
        exporter: Arc<dyn Exporter>,
    ) -> Self {
        Self {
            receiver,
            processors,
            exporter,
        }
    }

    pub async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let (tx, mut rx) = mpsc::channel::<Vec<SpanData>>(100);

        // 启动 Receiver
        let receiver = self.receiver.clone();
        let tx_clone = tx.clone();
        tokio::spawn(async move {
            loop {
                match receiver.receive_spans().await {
                    Ok(spans) if !spans.is_empty() => {
                        if tx_clone.send(spans).await.is_err() {
                            break;
                        }
                    }
                    Ok(_) => continue,
                    Err(e) => {
                        tracing::error!("Receiver error: {}", e);
                        break;
                    }
                }
            }
        });

        // 处理和导出
        while let Some(mut spans) = rx.recv().await {
            // 应用所有 Processor
            for processor in &self.processors {
                spans = processor.process(spans).await?;
            }

            // 导出
            if !spans.is_empty() {
                self.exporter.export(spans).await?;
            }
        }

        Ok(())
    }

    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.receiver.shutdown().await?;
        
        for processor in &self.processors {
            processor.shutdown().await?;
        }
        
        self.exporter.shutdown().await?;
        
        Ok(())
    }
}
```

---

## 自定义 Receiver

### 场景 1: HTTP JSON Receiver

```rust
// src/receivers/http_json_receiver.rs
use axum::{
    Router,
    routing::post,
    extract::Json,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Debug, Deserialize)]
struct JsonSpan {
    trace_id: String,
    span_id: String,
    name: String,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, String>,
}

pub struct HttpJsonReceiver {
    addr: SocketAddr,
    buffer: Arc<Mutex<Vec<SpanData>>>,
    shutdown_tx: tokio::sync::watch::Sender<bool>,
}

impl HttpJsonReceiver {
    pub fn new(addr: SocketAddr) -> Self {
        let (shutdown_tx, _) = tokio::sync::watch::channel(false);
        
        Self {
            addr,
            buffer: Arc::new(Mutex::new(Vec::new())),
            shutdown_tx,
        }
    }

    async fn handle_traces(
        Json(spans): Json<Vec<JsonSpan>>,
        buffer: Arc<Mutex<Vec<SpanData>>>,
    ) -> StatusCode {
        let converted_spans: Vec<SpanData> = spans
            .into_iter()
            .filter_map(|s| convert_json_span(s).ok())
            .collect();

        buffer.lock().await.extend(converted_spans);
        
        StatusCode::OK
    }
}

#[async_trait]
impl Receiver for HttpJsonReceiver {
    async fn start(&self) -> Result<(), Box<dyn Error>> {
        let buffer = self.buffer.clone();
        let mut shutdown_rx = self.shutdown_tx.subscribe();

        let app = Router::new()
            .route("/v1/traces", post(move |payload| {
                Self::handle_traces(payload, buffer.clone())
            }));

        let listener = tokio::net::TcpListener::bind(self.addr).await?;
        
        tokio::spawn(async move {
            axum::serve(listener, app)
                .with_graceful_shutdown(async move {
                    let _ = shutdown_rx.changed().await;
                })
                .await
                .unwrap();
        });

        tracing::info!("HTTP JSON Receiver started on {}", self.addr);
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        self.shutdown_tx.send(true)?;
        Ok(())
    }

    async fn receive_spans(&self) -> Result<Vec<SpanData>, Box<dyn Error>> {
        let mut buffer = self.buffer.lock().await;
        let spans = buffer.drain(..).collect();
        Ok(spans)
    }
}

fn convert_json_span(json: JsonSpan) -> Result<SpanData, Box<dyn Error>> {
    // 转换逻辑
    let trace_id = TraceId::from_hex(&json.trace_id)?;
    let span_id = SpanId::from_hex(&json.span_id)?;
    
    let mut builder = SpanData::builder()
        .with_trace_id(trace_id)
        .with_span_id(span_id)
        .with_name(json.name)
        .with_start_time(SystemTime::UNIX_EPOCH + Duration::from_secs(json.start_time))
        .with_end_time(SystemTime::UNIX_EPOCH + Duration::from_secs(json.end_time));

    for (key, value) in json.attributes {
        builder = builder.with_attribute(key, value);
    }

    Ok(builder.build())
}
```

### 场景 2: Kafka Receiver

```rust
// src/receivers/kafka_receiver.rs
use rdkafka::{
    consumer::{Consumer, StreamConsumer},
    ClientConfig,
    Message,
};
use std::time::Duration;

pub struct KafkaReceiver {
    consumer: StreamConsumer,
    topics: Vec<String>,
    buffer: Arc<Mutex<Vec<SpanData>>>,
}

impl KafkaReceiver {
    pub fn new(
        brokers: &str,
        group_id: &str,
        topics: Vec<String>,
    ) -> Result<Self, Box<dyn Error>> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("group.id", group_id)
            .set("enable.auto.commit", "true")
            .set("auto.offset.reset", "earliest")
            .create()?;

        Ok(Self {
            consumer,
            topics,
            buffer: Arc::new(Mutex::new(Vec::new())),
        })
    }

    async fn consume_messages(&self) -> Result<(), Box<dyn Error>> {
        use rdkafka::message::BorrowedMessage;
        use futures::StreamExt;

        let mut stream = self.consumer.stream();

        while let Some(message) = stream.next().await {
            match message {
                Ok(m) => {
                    if let Some(payload) = m.payload() {
                        // 解析 Protobuf 或 JSON
                        match self.parse_span(payload) {
                            Ok(span) => {
                                self.buffer.lock().await.push(span);
                            }
                            Err(e) => {
                                tracing::error!("Failed to parse span: {}", e);
                            }
                        }
                    }
                }
                Err(e) => {
                    tracing::error!("Kafka error: {}", e);
                }
            }
        }

        Ok(())
    }

    fn parse_span(&self, payload: &[u8]) -> Result<SpanData, Box<dyn Error>> {
        // 使用 prost 解析 Protobuf
        use prost::Message;
        let proto_span = opentelemetry_proto::tonic::trace::v1::Span::decode(payload)?;
        
        // 转换为 SpanData
        convert_proto_to_span_data(proto_span)
    }
}

#[async_trait]
impl Receiver for KafkaReceiver {
    async fn start(&self) -> Result<(), Box<dyn Error>> {
        self.consumer.subscribe(&self.topics.iter().map(|s| s.as_str()).collect::<Vec<_>>())?;
        
        let receiver = self.clone();
        tokio::spawn(async move {
            if let Err(e) = receiver.consume_messages().await {
                tracing::error!("Kafka receiver error: {}", e);
            }
        });

        tracing::info!("Kafka Receiver started, topics: {:?}", self.topics);
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        // Kafka consumer 会自动清理
        Ok(())
    }

    async fn receive_spans(&self) -> Result<Vec<SpanData>, Box<dyn Error>> {
        let mut buffer = self.buffer.lock().await;
        let spans = buffer.drain(..).collect();
        Ok(spans)
    }
}
```

---

## 自定义 Processor

### 场景 1: 属性过滤 Processor

```rust
// src/processors/attribute_filter_processor.rs
use regex::Regex;
use std::collections::HashSet;

pub struct AttributeFilterProcessor {
    /// 要删除的属性名称
    remove_attributes: HashSet<String>,
    /// 要保留的属性名称（如果设置，只保留这些）
    keep_attributes: Option<HashSet<String>>,
    /// 基于正则表达式删除
    remove_patterns: Vec<Regex>,
}

impl AttributeFilterProcessor {
    pub fn new(
        remove: Vec<String>,
        keep: Option<Vec<String>>,
        remove_patterns: Vec<String>,
    ) -> Result<Self, Box<dyn Error>> {
        let patterns: Result<Vec<_>, _> = remove_patterns
            .into_iter()
            .map(|p| Regex::new(&p))
            .collect();

        Ok(Self {
            remove_attributes: remove.into_iter().collect(),
            keep_attributes: keep.map(|k| k.into_iter().collect()),
            remove_patterns: patterns?,
        })
    }

    fn should_remove_attribute(&self, key: &str) -> bool {
        // 检查是否在删除列表中
        if self.remove_attributes.contains(key) {
            return true;
        }

        // 检查是否匹配删除模式
        if self.remove_patterns.iter().any(|re| re.is_match(key)) {
            return true;
        }

        // 如果设置了保留列表，检查是否在其中
        if let Some(keep) = &self.keep_attributes {
            return !keep.contains(key);
        }

        false
    }
}

#[async_trait]
impl Processor for AttributeFilterProcessor {
    async fn process(&self, spans: Vec<SpanData>) -> Result<Vec<SpanData>, Box<dyn Error>> {
        let processed: Vec<SpanData> = spans
            .into_iter()
            .map(|span| {
                let filtered_attributes: Vec<_> = span
                    .attributes()
                    .iter()
                    .filter(|(key, _)| !self.should_remove_attribute(key))
                    .cloned()
                    .collect();

                SpanData::builder()
                    .with_trace_id(span.trace_id())
                    .with_span_id(span.span_id())
                    .with_name(span.name())
                    .with_attributes(filtered_attributes)
                    .with_start_time(span.start_time())
                    .with_end_time(span.end_time())
                    .build()
            })
            .collect();

        Ok(processed)
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_remove_specific_attributes() {
        let processor = AttributeFilterProcessor::new(
            vec!["password".to_string(), "secret".to_string()],
            None,
            vec![],
        ).unwrap();

        let span = create_test_span_with_attributes(vec![
            ("username", "test_user"),
            ("password", "secret123"),
            ("api_key", "abc123"),
        ]);

        let result = processor.process(vec![span]).await.unwrap();
        
        assert_eq!(result.len(), 1);
        assert!(!result[0].attributes().iter().any(|(k, _)| k == "password"));
    }

    #[tokio::test]
    async fn test_keep_only_allowlist() {
        let processor = AttributeFilterProcessor::new(
            vec![],
            Some(vec!["http.method".to_string(), "http.status_code".to_string()]),
            vec![],
        ).unwrap();

        let span = create_test_span_with_attributes(vec![
            ("http.method", "GET"),
            ("http.status_code", "200"),
            ("custom.field", "value"),
        ]);

        let result = processor.process(vec![span]).await.unwrap();
        
        assert_eq!(result[0].attributes().len(), 2);
    }

    #[tokio::test]
    async fn test_regex_pattern_removal() {
        let processor = AttributeFilterProcessor::new(
            vec![],
            None,
            vec![r"^internal\..*".to_string()],
        ).unwrap();

        let span = create_test_span_with_attributes(vec![
            ("http.method", "GET"),
            ("internal.debug", "value"),
            ("internal.trace_id", "123"),
        ]);

        let result = processor.process(vec![span]).await.unwrap();
        
        let remaining: Vec<_> = result[0]
            .attributes()
            .iter()
            .map(|(k, _)| k.as_str())
            .collect();
        
        assert!(remaining.contains(&"http.method"));
        assert!(!remaining.iter().any(|k| k.starts_with("internal.")));
    }
}
```

### 场景 2: 采样 Processor

```rust
// src/processors/sampling_processor.rs
use rand::Rng;

pub enum SamplingStrategy {
    /// 固定采样率 (0.0 - 1.0)
    Probabilistic(f64),
    /// 基于速率限制 (每秒 N 个)
    RateLimiting { rate: u32 },
    /// 基于属性
    AttributeBased { key: String, values: Vec<String> },
}

pub struct SamplingProcessor {
    strategy: SamplingStrategy,
    rate_limiter: Option<tokio::sync::Semaphore>,
}

impl SamplingProcessor {
    pub fn new(strategy: SamplingStrategy) -> Self {
        let rate_limiter = match &strategy {
            SamplingStrategy::RateLimiting { rate } => {
                Some(tokio::sync::Semaphore::new(*rate as usize))
            }
            _ => None,
        };

        Self {
            strategy,
            rate_limiter,
        }
    }

    fn should_sample(&self, span: &SpanData) -> bool {
        match &self.strategy {
            SamplingStrategy::Probabilistic(rate) => {
                let mut rng = rand::thread_rng();
                rng.gen::<f64>() < *rate
            }
            SamplingStrategy::RateLimiting { .. } => {
                // 通过信号量控制
                self.rate_limiter
                    .as_ref()
                    .unwrap()
                    .try_acquire()
                    .is_ok()
            }
            SamplingStrategy::AttributeBased { key, values } => {
                span.attributes()
                    .iter()
                    .any(|(k, v)| k == key && values.contains(&v.to_string()))
            }
        }
    }
}

#[async_trait]
impl Processor for SamplingProcessor {
    async fn process(&self, spans: Vec<SpanData>) -> Result<Vec<SpanData>, Box<dyn Error>> {
        let sampled: Vec<SpanData> = spans
            .into_iter()
            .filter(|span| self.should_sample(span))
            .collect();

        tracing::debug!("Sampled {} spans", sampled.len());
        Ok(sampled)
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_probabilistic_sampling() {
        let processor = SamplingProcessor::new(SamplingStrategy::Probabilistic(0.5));
        
        let spans: Vec<SpanData> = (0..1000)
            .map(|i| create_test_span(&format!("span_{}", i)))
            .collect();

        let result = processor.process(spans).await.unwrap();
        
        // 应该大约采样 50%
        assert!(result.len() > 400 && result.len() < 600);
    }

    #[tokio::test]
    async fn test_attribute_based_sampling() {
        let processor = SamplingProcessor::new(SamplingStrategy::AttributeBased {
            key: "http.status_code".to_string(),
            values: vec!["500".to_string(), "503".to_string()],
        });

        let spans = vec![
            create_span_with_status(200),
            create_span_with_status(500),  // 采样
            create_span_with_status(404),
            create_span_with_status(503),  // 采样
        ];

        let result = processor.process(spans).await.unwrap();
        
        assert_eq!(result.len(), 2);
    }
}
```

### 场景 3: 批处理 Processor

```rust
// src/processors/batch_processor.rs
use std::time::Duration;
use tokio::time::Instant;

pub struct BatchProcessor {
    /// 最大批次大小
    max_batch_size: usize,
    /// 最大等待时间
    max_wait_time: Duration,
    /// 累积的 Spans
    buffer: Arc<Mutex<Vec<SpanData>>>,
    /// 最后刷新时间
    last_flush: Arc<Mutex<Instant>>,
}

impl BatchProcessor {
    pub fn new(max_batch_size: usize, max_wait_time: Duration) -> Self {
        Self {
            max_batch_size,
            max_wait_time,
            buffer: Arc::new(Mutex::new(Vec::with_capacity(max_batch_size))),
            last_flush: Arc::new(Mutex::new(Instant::now())),
        }
    }

    async fn should_flush(&self, current_size: usize) -> bool {
        if current_size >= self.max_batch_size {
            return true;
        }

        let last_flush = self.last_flush.lock().await;
        last_flush.elapsed() >= self.max_wait_time
    }
}

#[async_trait]
impl Processor for BatchProcessor {
    async fn process(&self, spans: Vec<SpanData>) -> Result<Vec<SpanData>, Box<dyn Error>> {
        let mut buffer = self.buffer.lock().await;
        buffer.extend(spans);

        if self.should_flush(buffer.len()).await {
            let batched = buffer.drain(..).collect::<Vec<_>>();
            *self.last_flush.lock().await = Instant::now();
            
            tracing::debug!("Flushing batch of {} spans", batched.len());
            Ok(batched)
        } else {
            Ok(vec![])
        }
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        // 刷新剩余数据
        let buffer = self.buffer.lock().await;
        if !buffer.is_empty() {
            tracing::info!("Flushing {} remaining spans", buffer.len());
        }
        Ok(())
    }
}
```

---

## 自定义 Exporter

### 场景 1: Elasticsearch Exporter

```rust
// src/exporters/elasticsearch_exporter.rs
use elasticsearch::{Elasticsearch, http::transport::Transport};

pub struct ElasticsearchExporter {
    client: Elasticsearch,
    index_prefix: String,
}

impl ElasticsearchExporter {
    pub async fn new(
        url: &str,
        index_prefix: String,
    ) -> Result<Self, Box<dyn Error>> {
        let transport = Transport::single_node(url)?;
        let client = Elasticsearch::new(transport);

        Ok(Self {
            client,
            index_prefix,
        })
    }

    fn get_index_name(&self) -> String {
        let now = chrono::Utc::now();
        format!("{}-{}", self.index_prefix, now.format("%Y.%m.%d"))
    }

    fn span_to_json(&self, span: &SpanData) -> serde_json::Value {
        json!({
            "trace_id": span.trace_id().to_hex(),
            "span_id": span.span_id().to_hex(),
            "name": span.name(),
            "start_time": span.start_time(),
            "end_time": span.end_time(),
            "duration_ns": span.end_time().duration_since(span.start_time()).unwrap().as_nanos(),
            "attributes": span.attributes(),
            "@timestamp": chrono::Utc::now(),
        })
    }
}

#[async_trait]
impl Exporter for ElasticsearchExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
        use elasticsearch::BulkParts;

        let mut body: Vec<serde_json::Value> = Vec::with_capacity(spans.len() * 2);
        let index_name = self.get_index_name();

        for span in spans {
            // Bulk API 格式
            body.push(json!({
                "index": {
                    "_index": index_name,
                }
            }));
            body.push(self.span_to_json(&span));
        }

        let response = self.client
            .bulk(BulkParts::None)
            .body(body)
            .send()
            .await?;

        if response.status_code().is_success() {
            tracing::debug!("Exported {} spans to Elasticsearch", spans.len());
            Ok(())
        } else {
            let error = response.text().await?;
            Err(format!("Elasticsearch export failed: {}", error).into())
        }
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}
```

### 场景 2: ClickHouse Exporter

```rust
// src/exporters/clickhouse_exporter.rs
use clickhouse::Client;

pub struct ClickHouseExporter {
    client: Client,
    table: String,
}

impl ClickHouseExporter {
    pub fn new(url: &str, database: &str, table: String) -> Result<Self, Box<dyn Error>> {
        let client = Client::default()
            .with_url(url)
            .with_database(database);

        Ok(Self { client, table })
    }

    async fn ensure_table_exists(&self) -> Result<(), Box<dyn Error>> {
        let create_table_sql = format!(
            r#"
            CREATE TABLE IF NOT EXISTS {} (
                trace_id String,
                span_id String,
                parent_span_id String,
                name String,
                start_time DateTime64(9),
                end_time DateTime64(9),
                duration_ns UInt64,
                span_kind String,
                attributes Map(String, String),
                events Array(Tuple(name String, timestamp DateTime64(9), attributes Map(String, String))),
                INDEX idx_trace_id trace_id TYPE bloom_filter GRANULARITY 4
            ) ENGINE = MergeTree()
            ORDER BY (start_time, trace_id, span_id)
            PARTITION BY toYYYYMM(start_time)
            TTL start_time + INTERVAL 30 DAY
            "#,
            self.table
        );

        self.client.query(&create_table_sql).execute().await?;
        Ok(())
    }
}

#[async_trait]
impl Exporter for ClickHouseExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
        self.ensure_table_exists().await?;

        let mut insert = self.client.insert(&self.table)?;

        for span in spans {
            insert.write(&(
                span.trace_id().to_hex(),
                span.span_id().to_hex(),
                span.parent_span_id().map(|id| id.to_hex()).unwrap_or_default(),
                span.name().to_string(),
                span.start_time(),
                span.end_time(),
                span.end_time().duration_since(span.start_time()).unwrap().as_nanos() as u64,
                format!("{:?}", span.span_kind()),
                // 属性转换为 Map
                span.attributes()
                    .iter()
                    .map(|(k, v)| (k.clone(), v.to_string()))
                    .collect::<HashMap<_, _>>(),
            )).await?;
        }

        insert.end().await?;
        
        tracing::debug!("Exported {} spans to ClickHouse", spans.len());
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}
```

### 场景 3: S3 Exporter（冷存储）

```rust
// src/exporters/s3_exporter.rs
use aws_sdk_s3::Client as S3Client;
use bytes::Bytes;
use flate2::write::GzEncoder;
use flate2::Compression;

pub struct S3Exporter {
    client: S3Client,
    bucket: String,
    prefix: String,
}

impl S3Exporter {
    pub async fn new(
        bucket: String,
        prefix: String,
    ) -> Result<Self, Box<dyn Error>> {
        let config = aws_config::load_from_env().await;
        let client = S3Client::new(&config);

        Ok(Self {
            client,
            bucket,
            prefix,
        })
    }

    fn generate_s3_key(&self) -> String {
        let now = chrono::Utc::now();
        format!(
            "{}/year={}/month={:02}/day={:02}/traces-{}.json.gz",
            self.prefix,
            now.year(),
            now.month(),
            now.day(),
            now.timestamp()
        )
    }

    fn compress_spans(&self, spans: &[SpanData]) -> Result<Vec<u8>, Box<dyn Error>> {
        use std::io::Write;
        
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        
        for span in spans {
            let json = serde_json::to_string(span)?;
            writeln!(encoder, "{}", json)?;
        }
        
        Ok(encoder.finish()?)
    }
}

#[async_trait]
impl Exporter for S3Exporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
        let key = self.generate_s3_key();
        let data = self.compress_spans(&spans)?;

        self.client
            .put_object()
            .bucket(&self.bucket)
            .key(&key)
            .body(Bytes::from(data).into())
            .content_type("application/gzip")
            .content_encoding("gzip")
            .send()
            .await?;

        tracing::info!("Exported {} spans to s3://{}/{}", spans.len(), self.bucket, key);
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}
```

---

## 扩展注册

### 组件注册表

```rust
// src/registry.rs
use std::collections::HashMap;
use std::sync::Arc;

pub struct ComponentRegistry {
    receivers: HashMap<String, Box<dyn Fn() -> Arc<dyn Receiver>>>,
    processors: HashMap<String, Box<dyn Fn() -> Arc<dyn Processor>>>,
    exporters: HashMap<String, Box<dyn Fn() -> Arc<dyn Exporter>>>,
}

impl ComponentRegistry {
    pub fn new() -> Self {
        Self {
            receivers: HashMap::new(),
            processors: HashMap::new(),
            exporters: HashMap::new(),
        }
    }

    pub fn register_receiver<F>(&mut self, name: &str, factory: F)
    where
        F: Fn() -> Arc<dyn Receiver> + 'static,
    {
        self.receivers.insert(name.to_string(), Box::new(factory));
    }

    pub fn register_processor<F>(&mut self, name: &str, factory: F)
    where
        F: Fn() -> Arc<dyn Processor> + 'static,
    {
        self.processors.insert(name.to_string(), Box::new(factory));
    }

    pub fn register_exporter<F>(&mut self, name: &str, factory: F)
    where
        F: Fn() -> Arc<dyn Exporter> + 'static,
    {
        self.exporters.insert(name.to_string(), Box::new(factory));
    }

    pub fn create_receiver(&self, name: &str) -> Option<Arc<dyn Receiver>> {
        self.receivers.get(name).map(|f| f())
    }

    pub fn create_processor(&self, name: &str) -> Option<Arc<dyn Processor>> {
        self.processors.get(name).map(|f| f())
    }

    pub fn create_exporter(&self, name: &str) -> Option<Arc<dyn Exporter>> {
        self.exporters.get(name).map(|f| f())
    }
}

// 全局注册表
lazy_static! {
    pub static ref GLOBAL_REGISTRY: Mutex<ComponentRegistry> = 
        Mutex::new(ComponentRegistry::new());
}

// 注册宏
#[macro_export]
macro_rules! register_components {
    () => {
        pub fn register_all_components() {
            let mut registry = GLOBAL_REGISTRY.lock().unwrap();
            
            // 注册 Receivers
            registry.register_receiver("http_json", || {
                Arc::new(HttpJsonReceiver::new("0.0.0.0:8080".parse().unwrap()))
            });
            
            registry.register_receiver("kafka", || {
                Arc::new(KafkaReceiver::new(
                    "localhost:9092",
                    "otlp-collector",
                    vec!["traces".to_string()],
                ).unwrap())
            });

            // 注册 Processors
            registry.register_processor("attribute_filter", || {
                Arc::new(AttributeFilterProcessor::new(
                    vec!["password".to_string()],
                    None,
                    vec![],
                ).unwrap())
            });
            
            registry.register_processor("sampling", || {
                Arc::new(SamplingProcessor::new(
                    SamplingStrategy::Probabilistic(0.1)
                ))
            });

            // 注册 Exporters
            registry.register_exporter("elasticsearch", || {
                Arc::new(tokio::runtime::Runtime::new().unwrap().block_on(
                    ElasticsearchExporter::new("http://localhost:9200", "traces".to_string())
                ).unwrap())
            });
            
            registry.register_exporter("clickhouse", || {
                Arc::new(ClickHouseExporter::new(
                    "http://localhost:8123",
                    "default",
                    "spans".to_string(),
                ).unwrap())
            });
        }
    };
}
```

---

## 配置管理

### YAML 配置

```yaml
# config/collector.yaml
receivers:
  http_json:
    endpoint: 0.0.0.0:8080
  
  kafka:
    brokers: localhost:9092
    group_id: otlp-collector
    topics:
      - traces

processors:
  attribute_filter:
    remove:
      - password
      - secret
      - api_key
    remove_patterns:
      - "^internal\\..*"
  
  sampling:
    strategy: probabilistic
    rate: 0.1
  
  batch:
    max_batch_size: 1000
    max_wait_time: 10s

exporters:
  elasticsearch:
    url: http://localhost:9200
    index_prefix: traces
  
  clickhouse:
    url: http://localhost:8123
    database: default
    table: spans
  
  s3:
    bucket: my-traces-bucket
    prefix: traces

pipelines:
  traces:
    receivers:
      - http_json
      - kafka
    processors:
      - attribute_filter
      - sampling
      - batch
    exporters:
      - elasticsearch
      - clickhouse
      - s3
```

### 配置加载

```rust
// src/config.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Deserialize, Serialize)]
pub struct CollectorConfig {
    pub receivers: HashMap<String, ReceiverConfig>,
    pub processors: HashMap<String, ProcessorConfig>,
    pub exporters: HashMap<String, ExporterConfig>,
    pub pipelines: HashMap<String, PipelineConfig>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ReceiverConfig {
    HttpJson { endpoint: String },
    Kafka { brokers: String, group_id: String, topics: Vec<String> },
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ProcessorConfig {
    AttributeFilter {
        remove: Vec<String>,
        remove_patterns: Vec<String>,
    },
    Sampling {
        strategy: String,
        rate: f64,
    },
    Batch {
        max_batch_size: usize,
        max_wait_time: String,
    },
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ExporterConfig {
    Elasticsearch { url: String, index_prefix: String },
    ClickHouse { url: String, database: String, table: String },
    S3 { bucket: String, prefix: String },
}

#[derive(Debug, Deserialize, Serialize)]
pub struct PipelineConfig {
    pub receivers: Vec<String>,
    pub processors: Vec<String>,
    pub exporters: Vec<String>,
}

impl CollectorConfig {
    pub fn from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        let config: CollectorConfig = serde_yaml::from_str(&content)?;
        Ok(config)
    }

    pub fn build_pipeline(&self, name: &str) -> Result<Pipeline, Box<dyn std::error::Error>> {
        let pipeline_config = self.pipelines.get(name)
            .ok_or(format!("Pipeline '{}' not found", name))?;

        // 创建 Receiver
        let receiver_name = &pipeline_config.receivers[0];
        let receiver = self.create_receiver(receiver_name)?;

        // 创建 Processors
        let processors: Result<Vec<_>, _> = pipeline_config.processors
            .iter()
            .map(|name| self.create_processor(name))
            .collect();
        let processors = processors?;

        // 创建 Exporter
        let exporter_name = &pipeline_config.exporters[0];
        let exporter = self.create_exporter(exporter_name)?;

        Ok(Pipeline::new(receiver, processors, exporter))
    }

    fn create_receiver(&self, name: &str) -> Result<Arc<dyn Receiver>, Box<dyn std::error::Error>> {
        let config = self.receivers.get(name)
            .ok_or(format!("Receiver '{}' not found", name))?;

        match config {
            ReceiverConfig::HttpJson { endpoint } => {
                Ok(Arc::new(HttpJsonReceiver::new(endpoint.parse()?)))
            }
            ReceiverConfig::Kafka { brokers, group_id, topics } => {
                Ok(Arc::new(KafkaReceiver::new(brokers, group_id, topics.clone())?))
            }
        }
    }

    fn create_processor(&self, name: &str) -> Result<Arc<dyn Processor>, Box<dyn std::error::Error>> {
        let config = self.processors.get(name)
            .ok_or(format!("Processor '{}' not found", name))?;

        match config {
            ProcessorConfig::AttributeFilter { remove, remove_patterns } => {
                Ok(Arc::new(AttributeFilterProcessor::new(
                    remove.clone(),
                    None,
                    remove_patterns.clone(),
                )?))
            }
            ProcessorConfig::Sampling { strategy, rate } => {
                let sampling_strategy = match strategy.as_str() {
                    "probabilistic" => SamplingStrategy::Probabilistic(*rate),
                    _ => return Err("Unknown sampling strategy".into()),
                };
                Ok(Arc::new(SamplingProcessor::new(sampling_strategy)))
            }
            ProcessorConfig::Batch { max_batch_size, max_wait_time } => {
                let duration = parse_duration(max_wait_time)?;
                Ok(Arc::new(BatchProcessor::new(*max_batch_size, duration)))
            }
        }
    }

    fn create_exporter(&self, name: &str) -> Result<Arc<dyn Exporter>, Box<dyn std::error::Error>> {
        let config = self.exporters.get(name)
            .ok_or(format!("Exporter '{}' not found", name))?;

        match config {
            ExporterConfig::Elasticsearch { url, index_prefix } => {
                Ok(Arc::new(tokio::runtime::Runtime::new()?.block_on(
                    ElasticsearchExporter::new(url, index_prefix.clone())
                )?))
            }
            ExporterConfig::ClickHouse { url, database, table } => {
                Ok(Arc::new(ClickHouseExporter::new(url, database, table.clone())?))
            }
            ExporterConfig::S3 { bucket, prefix } => {
                Ok(Arc::new(tokio::runtime::Runtime::new()?.block_on(
                    S3Exporter::new(bucket.clone(), prefix.clone())
                )?))
            }
        }
    }
}

fn parse_duration(s: &str) -> Result<Duration, Box<dyn std::error::Error>> {
    let re = regex::Regex::new(r"^(\d+)(s|ms|m|h)$")?;
    let captures = re.captures(s)
        .ok_or("Invalid duration format")?;
    
    let value: u64 = captures[1].parse()?;
    let unit = &captures[2];
    
    let duration = match unit {
        "s" => Duration::from_secs(value),
        "ms" => Duration::from_millis(value),
        "m" => Duration::from_secs(value * 60),
        "h" => Duration::from_secs(value * 3600),
        _ => return Err("Unknown duration unit".into()),
    };
    
    Ok(duration)
}
```

---

## 测试与调试

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use mockall::predicate::*;

    #[tokio::test]
    async fn test_pipeline_flow() {
        // 创建 Mock 组件
        let mut mock_receiver = MockReceiver::new();
        let mut mock_processor = MockProcessor::new();
        let mut mock_exporter = MockExporter::new();

        // 设置期望
        mock_receiver
            .expect_receive_spans()
            .returning(|| Ok(vec![create_test_span("test")]));

        mock_processor
            .expect_process()
            .withf(|spans| spans.len() == 1)
            .returning(|spans| Ok(spans));

        mock_exporter
            .expect_export()
            .withf(|spans| spans.len() == 1)
            .returning(|_| Ok(()));

        // 测试 Pipeline
        let pipeline = Pipeline::new(
            Arc::new(mock_receiver),
            vec![Arc::new(mock_processor)],
            Arc::new(mock_exporter),
        );

        // 验证流程
        // ...
    }
}
```

### 集成测试

```bash
# 启动测试环境
docker-compose up -d elasticsearch redis kafka

# 运行集成测试
cargo test --test '*' --features integration-tests
```

### 调试工具

```rust
// src/debug.rs
pub struct DebugExporter {
    output: Box<dyn Write + Send>,
}

impl DebugExporter {
    pub fn stdout() -> Self {
        Self {
            output: Box::new(std::io::stdout()),
        }
    }

    pub fn file(path: &str) -> Result<Self, Box<dyn Error>> {
        let file = std::fs::File::create(path)?;
        Ok(Self {
            output: Box::new(file),
        })
    }
}

#[async_trait]
impl Exporter for DebugExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
        for span in spans {
            writeln!(
                self.output,
                "[DEBUG] Span: {} (trace={}, span={})",
                span.name(),
                span.trace_id().to_hex(),
                span.span_id().to_hex()
            )?;
        }
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }
}
```

---

## 性能优化

### 1. 零拷贝优化

```rust
use bytes::Bytes;

pub struct ZeroCopyExporter {
    buffer: Arc<Mutex<Vec<Bytes>>>,
}

impl ZeroCopyExporter {
    async fn export_zero_copy(&self, data: Bytes) -> Result<(), Box<dyn Error>> {
        // 直接使用 Bytes，避免拷贝
        self.send_to_backend(data).await
    }
}
```

### 2. 批量处理

```rust
// 批量导出，减少网络往返
async fn export_batch(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
    const BATCH_SIZE: usize = 1000;
    
    for chunk in spans.chunks(BATCH_SIZE) {
        self.export_chunk(chunk).await?;
    }
    
    Ok(())
}
```

### 3. 异步并发

```rust
use futures::stream::{self, StreamExt};

async fn export_concurrent(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
    const CONCURRENCY: usize = 10;
    
    stream::iter(spans)
        .map(|span| self.export_single(span))
        .buffer_unordered(CONCURRENCY)
        .collect::<Vec<_>>()
        .await;
    
    Ok(())
}
```

---

## 部署与发布

### Docker 镜像

```dockerfile
# Dockerfile
FROM rust:1.90 as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/otlp-collector /usr/local/bin/

EXPOSE 8080 4317

CMD ["otlp-collector", "--config", "/etc/collector/config.yaml"]
```

### Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-collector
  template:
    metadata:
      labels:
        app: otlp-collector
    spec:
      containers:
      - name: collector
        image: my-registry/otlp-collector:latest
        ports:
        - containerPort: 8080
          name: http
        - containerPort: 4317
          name: grpc
        volumeMounts:
        - name: config
          mountPath: /etc/collector
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
      volumes:
      - name: config
        configMap:
          name: collector-config
```

---

## 最佳实践

### 1. 错误处理

```rust
// ✅ 使用 thiserror
#[derive(Debug, thiserror::Error)]
pub enum CollectorError {
    #[error("Receiver error: {0}")]
    ReceiverError(String),
    
    #[error("Processor error: {0}")]
    ProcessorError(String),
    
    #[error("Exporter error: {0}")]
    ExporterError(String),
    
    #[error("Configuration error: {0}")]
    ConfigError(String),
}
```

### 2. 可观测性

```rust
// 为 Collector 本身添加追踪
#[tracing::instrument(skip(self))]
async fn export(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn Error>> {
    tracing::info!(span_count = spans.len(), "Exporting spans");
    
    let start = std::time::Instant::now();
    let result = self.do_export(spans).await;
    let duration = start.elapsed();
    
    tracing::info!(duration_ms = duration.as_millis(), "Export completed");
    
    result
}
```

### 3. 资源管理

```rust
// 使用 Drop trait 确保资源清理
impl Drop for CustomReceiver {
    fn drop(&mut self) {
        tracing::info!("Shutting down receiver");
        // 清理资源
    }
}
```

### 4. 配置验证

```rust
impl CollectorConfig {
    pub fn validate(&self) -> Result<(), ValidationError> {
        // 验证 Pipeline 引用的组件都存在
        for (name, pipeline) in &self.pipelines {
            for receiver in &pipeline.receivers {
                if !self.receivers.contains_key(receiver) {
                    return Err(ValidationError::MissingReceiver {
                        pipeline: name.clone(),
                        receiver: receiver.clone(),
                    });
                }
            }
        }
        
        Ok(())
    }
}
```

---

## 总结

### 完整性检查表

- [x] **Receiver 开发**: HTTP JSON + Kafka 示例
- [x] **Processor 开发**: 属性过滤 + 采样 + 批处理
- [x] **Exporter 开发**: Elasticsearch + ClickHouse + S3
- [x] **组件注册**: 注册表和工厂模式
- [x] **配置管理**: YAML 配置和动态加载
- [x] **测试**: 单元测试 + 集成测试
- [x] **性能优化**: 零拷贝 + 批处理 + 并发
- [x] **部署**: Docker + Kubernetes

### 核心要点

```text
✅ 遵循 OpenTelemetry 规范
✅ 使用 Rust 异步编程模式
✅ 实现可插拔架构
✅ 提供完整的配置管理
✅ 确保高性能和低开销
✅ 提供良好的可观测性
```

### 扩展资源

- [OpenTelemetry Collector Builder](https://github.com/open-telemetry/opentelemetry-collector-builder)
- [Collector Contrib](https://github.com/open-telemetry/opentelemetry-collector-contrib)
- [Rust OpenTelemetry](https://github.com/open-telemetry/opentelemetry-rust)

---

**文档作者**: OTLP Rust Team  
**创建日期**: 2025-10-08  
**许可证**: MIT OR Apache-2.0  
**相关文档**:

- [测试框架](../21_测试框架/01_Rust_OTLP端到端测试完整框架.md)
- [性能基准测试](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)
- [Kubernetes部署](../19_容器化与Kubernetes/01_Rust_OTLP_Kubernetes完整部署指南.md)
