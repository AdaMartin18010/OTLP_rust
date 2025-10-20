# 自定义 Exporter - Rust 完整版

## 目录

- [自定义 Exporter - Rust 完整版](#自定义-exporter---rust-完整版)
  - [目录](#目录)
  - [1. Exporter 概述](#1-exporter-概述)
    - [1.1 什么是 Exporter](#11-什么是-exporter)
    - [1.2 使用场景](#12-使用场景)
  - [2. SpanExporter Trait](#2-spanexporter-trait)
    - [2.1 Trait 定义](#21-trait-定义)
    - [2.2 基础实现](#22-基础实现)
  - [3. 完整示例](#3-完整示例)
    - [3.1 文件 Exporter](#31-文件-exporter)
    - [3.2 数据库 Exporter](#32-数据库-exporter)
    - [3.3 Kafka Exporter](#33-kafka-exporter)
  - [4. 批处理优化](#4-批处理优化)
    - [4.1 批量导出](#41-批量导出)
    - [4.2 批处理配置](#42-批处理配置)
  - [5. 错误处理](#5-错误处理)
    - [5.1 重试机制](#51-重试机制)
    - [5.2 降级策略](#52-降级策略)
  - [6. 性能优化](#6-性能优化)
    - [6.1 异步导出](#61-异步导出)
    - [6.2 内存池](#62-内存池)
  - [7. 监控与调试](#7-监控与调试)
    - [7.1 Exporter 指标](#71-exporter-指标)
    - [7.2 日志输出](#72-日志输出)
  - [8. 测试](#8-测试)
    - [8.1 单元测试](#81-单元测试)
    - [8.2 集成测试](#82-集成测试)
  - [9. 生产环境配置](#9-生产环境配置)
    - [9.1 超时配置](#91-超时配置)
    - [9.2 资源限制](#92-资源限制)
  - [10. 完整项目示例](#10-完整项目示例)
    - [10.1 Redis Exporter](#101-redis-exporter)
    - [10.2 S3 Exporter](#102-s3-exporter)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Exporter 对比](#exporter-对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Exporter 概述

### 1.1 什么是 Exporter

````text
Exporter 定义:
- 将 Telemetry 数据导出到外部系统
- 实现 SpanExporter trait
- 支持批量导出

内置 Exporter:
1. OTLP Exporter (gRPC/HTTP)
2. Jaeger Exporter
3. Zipkin Exporter
4. Stdout Exporter (调试)

自定义 Exporter 场景:
- 导出到自定义后端
- 数据预处理/过滤
- 多目标导出
- 特定格式转换
````

### 1.2 使用场景

````text
自定义 Exporter 使用场景:

1. 文件导出
   - JSON/CSV 格式
   - 日志文件
   - 数据归档

2. 数据库导出
   - PostgreSQL
   - ClickHouse
   - Elasticsearch

3. 消息队列
   - Kafka
   - RabbitMQ
   - Redis Streams

4. 对象存储
   - AWS S3
   - GCS
   - Azure Blob

5. 自定义后端
   - 内部监控系统
   - 数据仓库
   - 分析平台
````

---

## 2. SpanExporter Trait

### 2.1 Trait 定义

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;

/// SpanExporter Trait
#[async_trait]
pub trait SpanExporter: Send + Sync + std::fmt::Debug {
    /// 导出一批 Span
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult;
    
    /// 关闭 Exporter
    fn shutdown(&mut self) {}
}
````

### 2.2 基础实现

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use tracing::info;

#[derive(Debug)]
pub struct CustomExporter {
    name: String,
}

impl CustomExporter {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

#[async_trait]
impl SpanExporter for CustomExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        info!(
            exporter = %self.name,
            span_count = batch.len(),
            "Exporting spans"
        );
        
        for span in batch {
            // 处理每个 Span
            process_span(&span);
        }
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        info!(exporter = %self.name, "Shutting down exporter");
    }
}

fn process_span(span: &SpanData) {
    info!(
        trace_id = %span.span_context.trace_id(),
        span_id = %span.span_context.span_id(),
        name = %span.name,
        "Processing span"
    );
}
````

---

## 3. 完整示例

### 3.1 文件 Exporter

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use std::fs::OpenOptions;
use std::io::Write;
use serde_json;

#[derive(Debug)]
pub struct FileExporter {
    file_path: String,
}

impl FileExporter {
    pub fn new(file_path: String) -> Self {
        Self { file_path }
    }
}

#[async_trait]
impl SpanExporter for FileExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.file_path)
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        
        for span in batch {
            // 转换为 JSON
            let json = serde_json::json!({
                "trace_id": span.span_context.trace_id().to_string(),
                "span_id": span.span_context.span_id().to_string(),
                "name": span.name,
                "start_time": span.start_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
                "end_time": span.end_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
                "attributes": span.attributes.iter().map(|kv| {
                    (kv.key.to_string(), kv.value.to_string())
                }).collect::<std::collections::HashMap<_, _>>(),
            });
            
            // 写入文件
            writeln!(file, "{}", json)
                .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        }
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        tracing::info!(file = %self.file_path, "File exporter shutting down");
    }
}
````

**使用示例**:

````rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;

pub fn init_file_exporter() -> Result<(), Box<dyn std::error::Error>> {
    let exporter = FileExporter::new("traces.jsonl".to_string());
    
    let provider = TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    
    global::set_tracer_provider(provider);
    
    Ok(())
}
````

### 3.2 数据库 Exporter

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use sqlx::{PgPool, Postgres};

#[derive(Debug, Clone)]
pub struct DatabaseExporter {
    pool: PgPool,
}

impl DatabaseExporter {
    pub async fn new(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = PgPool::connect(database_url).await?;
        
        // 创建表
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS spans (
                id SERIAL PRIMARY KEY,
                trace_id VARCHAR(32) NOT NULL,
                span_id VARCHAR(16) NOT NULL,
                name TEXT NOT NULL,
                start_time BIGINT NOT NULL,
                end_time BIGINT NOT NULL,
                attributes JSONB,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            "#
        )
        .execute(&pool)
        .await?;
        
        Ok(Self { pool })
    }
}

#[async_trait]
impl SpanExporter for DatabaseExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        for span in batch {
            let trace_id = span.span_context.trace_id().to_string();
            let span_id = span.span_context.span_id().to_string();
            let start_time = span.start_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos() as i64;
            let end_time = span.end_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos() as i64;
            
            let attributes = serde_json::json!(
                span.attributes.iter().map(|kv| {
                    (kv.key.to_string(), kv.value.to_string())
                }).collect::<std::collections::HashMap<_, _>>()
            );
            
            sqlx::query(
                r#"
                INSERT INTO spans (trace_id, span_id, name, start_time, end_time, attributes)
                VALUES ($1, $2, $3, $4, $5, $6)
                "#
            )
            .bind(&trace_id)
            .bind(&span_id)
            .bind(&span.name)
            .bind(start_time)
            .bind(end_time)
            .bind(&attributes)
            .execute(&self.pool)
            .await
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        }
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        tracing::info!("Database exporter shutting down");
    }
}
````

### 3.3 Kafka Exporter

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;
use serde_json;

#[derive(Debug)]
pub struct KafkaExporter {
    producer: FutureProducer,
    topic: String,
}

impl KafkaExporter {
    pub fn new(brokers: &str, topic: String) -> Result<Self, rdkafka::error::KafkaError> {
        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .create()?;
        
        Ok(Self { producer, topic })
    }
}

#[async_trait]
impl SpanExporter for KafkaExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        for span in batch {
            // 序列化为 JSON
            let json = serde_json::json!({
                "trace_id": span.span_context.trace_id().to_string(),
                "span_id": span.span_context.span_id().to_string(),
                "name": span.name,
                "start_time": span.start_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
                "end_time": span.end_time.duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
            });
            
            let payload = serde_json::to_string(&json)
                .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
            
            // 发送到 Kafka
            let record = FutureRecord::to(&self.topic)
                .payload(&payload)
                .key(&span.span_context.trace_id().to_string());
            
            self.producer
                .send(record, std::time::Duration::from_secs(5))
                .await
                .map_err(|(e, _)| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        }
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        tracing::info!(topic = %self.topic, "Kafka exporter shutting down");
    }
}
````

---

## 4. 批处理优化

### 4.1 批量导出

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Debug)]
pub struct BatchExporter {
    inner: Arc<Mutex<Box<dyn SpanExporter>>>,
    max_batch_size: usize,
}

impl BatchExporter {
    pub fn new(exporter: Box<dyn SpanExporter>, max_batch_size: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(exporter)),
            max_batch_size,
        }
    }
}

#[async_trait]
impl SpanExporter for BatchExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 分批导出
        for chunk in batch.chunks(self.max_batch_size) {
            let mut exporter = self.inner.lock().await;
            exporter.export(chunk.to_vec()).await?;
        }
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        // Shutdown 会在 drop 时自动调用
    }
}
````

### 4.2 批处理配置

````rust
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

/// 批处理配置
pub fn create_batch_config() -> BatchConfig {
    BatchConfig::default()
        .with_max_queue_size(2048)           // 最大队列大小
        .with_max_export_batch_size(512)     // 最大批量大小
        .with_scheduled_delay(Duration::from_secs(5))  // 导出间隔
        .with_max_export_timeout(Duration::from_secs(30))  // 导出超时
}
````

---

## 5. 错误处理

### 5.1 重试机制

````rust
use opentelemetry::sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Debug)]
pub struct RetryExporter {
    inner: Arc<Mutex<Box<dyn SpanExporter>>>,
    max_retries: usize,
    retry_delay: std::time::Duration,
}

impl RetryExporter {
    pub fn new(exporter: Box<dyn SpanExporter>, max_retries: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(exporter)),
            max_retries,
            retry_delay: std::time::Duration::from_secs(1),
        }
    }
}

#[async_trait]
impl SpanExporter for RetryExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let mut attempts = 0;
        
        loop {
            let mut exporter = self.inner.lock().await;
            
            match exporter.export(batch.clone()).await {
                Ok(_) => return Ok(()),
                Err(e) if attempts < self.max_retries => {
                    attempts += 1;
                    tracing::warn!(
                        attempt = attempts,
                        error = %e,
                        "Export failed, retrying"
                    );
                    drop(exporter);  // 释放锁
                    tokio::time::sleep(self.retry_delay).await;
                }
                Err(e) => {
                    tracing::error!(error = %e, "Export failed after retries");
                    return Err(e);
                }
            }
        }
    }
}
````

### 5.2 降级策略

````rust
#[derive(Debug)]
pub struct FallbackExporter {
    primary: Arc<Mutex<Box<dyn SpanExporter>>>,
    fallback: Arc<Mutex<Box<dyn SpanExporter>>>,
}

impl FallbackExporter {
    pub fn new(
        primary: Box<dyn SpanExporter>,
        fallback: Box<dyn SpanExporter>,
    ) -> Self {
        Self {
            primary: Arc::new(Mutex::new(primary)),
            fallback: Arc::new(Mutex::new(fallback)),
        }
    }
}

#[async_trait]
impl SpanExporter for FallbackExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 尝试主 Exporter
        let mut primary = self.primary.lock().await;
        match primary.export(batch.clone()).await {
            Ok(_) => Ok(()),
            Err(e) => {
                tracing::warn!(error = %e, "Primary exporter failed, using fallback");
                drop(primary);
                
                // 使用备用 Exporter
                let mut fallback = self.fallback.lock().await;
                fallback.export(batch).await
            }
        }
    }
}
````

---

## 6. 性能优化

### 6.1 异步导出

````rust
use tokio::task::JoinHandle;

#[derive(Debug)]
pub struct AsyncExporter {
    sender: tokio::sync::mpsc::UnboundedSender<Vec<SpanData>>,
    _handle: JoinHandle<()>,
}

impl AsyncExporter {
    pub fn new(mut exporter: Box<dyn SpanExporter>) -> Self {
        let (sender, mut receiver) = tokio::sync::mpsc::unbounded_channel();
        
        let handle = tokio::spawn(async move {
            while let Some(batch) = receiver.recv().await {
                if let Err(e) = exporter.export(batch).await {
                    tracing::error!(error = %e, "Async export failed");
                }
            }
        });
        
        Self {
            sender,
            _handle: handle,
        }
    }
}

#[async_trait]
impl SpanExporter for AsyncExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        self.sender
            .send(batch)
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        Ok(())
    }
}
````

### 6.2 内存池

````rust
use std::sync::Arc;

#[derive(Clone)]
pub struct PooledExporter {
    pool: Arc<Vec<Arc<Mutex<Box<dyn SpanExporter>>>>>,
    counter: Arc<std::sync::atomic::AtomicUsize>,
}

impl PooledExporter {
    pub fn new(exporters: Vec<Box<dyn SpanExporter>>) -> Self {
        let pool = exporters
            .into_iter()
            .map(|e| Arc::new(Mutex::new(e)))
            .collect();
        
        Self {
            pool: Arc::new(pool),
            counter: Arc::new(std::sync::atomic::AtomicUsize::new(0)),
        }
    }
}

#[async_trait]
impl SpanExporter for PooledExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 轮询选择 Exporter
        let index = self.counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed) % self.pool.len();
        let mut exporter = self.pool[index].lock().await;
        exporter.export(batch).await
    }
}
````

---

## 7. 监控与调试

### 7.1 Exporter 指标

````rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct ExporterMetrics {
    pub export_count: Counter<u64>,
    pub export_errors: Counter<u64>,
    pub export_duration: Histogram<f64>,
}

impl ExporterMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("exporter");
        
        Self {
            export_count: meter
                .u64_counter("exporter.export.count")
                .with_description("Number of exports")
                .build(),
            export_errors: meter
                .u64_counter("exporter.export.errors")
                .with_description("Number of export errors")
                .build(),
            export_duration: meter
                .f64_histogram("exporter.export.duration")
                .with_description("Export duration in seconds")
                .build(),
        }
    }
}
````

### 7.2 日志输出

````rust
#[async_trait]
impl SpanExporter for MonitoredExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let start = std::time::Instant::now();
        let span_count = batch.len();
        
        tracing::info!(span_count, "Starting export");
        
        let result = self.inner.lock().await.export(batch).await;
        
        let duration = start.elapsed();
        
        match &result {
            Ok(_) => {
                self.metrics.export_count.add(span_count as u64, &[]);
                tracing::info!(
                    span_count,
                    duration_ms = duration.as_millis(),
                    "Export successful"
                );
            }
            Err(e) => {
                self.metrics.export_errors.add(1, &[]);
                tracing::error!(
                    span_count,
                    error = %e,
                    "Export failed"
                );
            }
        }
        
        self.metrics.export_duration.record(duration.as_secs_f64(), &[]);
        
        result
    }
}
````

---

## 8. 测试

### 8.1 单元测试

````rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry::sdk::export::trace::SpanData;
    use opentelemetry::trace::{SpanContext, SpanId, TraceId, TraceFlags};
    
    #[tokio::test]
    async fn test_file_exporter() {
        let temp_file = "/tmp/test_spans.jsonl";
        let mut exporter = FileExporter::new(temp_file.to_string());
        
        // 创建测试 Span
        let span = create_test_span();
        
        // 导出
        let result = exporter.export(vec![span]).await;
        assert!(result.is_ok());
        
        // 验证文件内容
        let content = std::fs::read_to_string(temp_file).unwrap();
        assert!(content.contains("test_span"));
        
        // 清理
        std::fs::remove_file(temp_file).ok();
    }
    
    fn create_test_span() -> SpanData {
        // 创建测试 SpanData
        // (简化版本，实际需要完整初始化)
        todo!()
    }
}
````

### 8.2 集成测试

````rust
#[tokio::test]
async fn test_exporter_integration() {
    // 初始化 TracerProvider with custom exporter
    let exporter = FileExporter::new("test_traces.jsonl".to_string());
    
    let provider = TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    
    opentelemetry::global::set_tracer_provider(provider);
    
    // 创建 Span
    let tracer = opentelemetry::global::tracer("test");
    let span = tracer.start("test_span");
    drop(span);
    
    // 等待导出
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    // 验证文件
    let content = std::fs::read_to_string("test_traces.jsonl").unwrap();
    assert!(content.contains("test_span"));
    
    // 清理
    std::fs::remove_file("test_traces.jsonl").ok();
}
````

---

## 9. 生产环境配置

### 9.1 超时配置

````rust
use std::time::Duration;

pub struct TimeoutExporter {
    inner: Arc<Mutex<Box<dyn SpanExporter>>>,
    timeout: Duration,
}

#[async_trait]
impl SpanExporter for TimeoutExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        tokio::time::timeout(self.timeout, async {
            let mut exporter = self.inner.lock().await;
            exporter.export(batch).await
        })
        .await
        .map_err(|_| opentelemetry::trace::TraceError::Other("Export timeout".into()))?
    }
}
````

### 9.2 资源限制

````rust
pub struct RateLimitedExporter {
    inner: Arc<Mutex<Box<dyn SpanExporter>>>,
    semaphore: Arc<tokio::sync::Semaphore>,
}

impl RateLimitedExporter {
    pub fn new(exporter: Box<dyn SpanExporter>, max_concurrent: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(exporter)),
            semaphore: Arc::new(tokio::sync::Semaphore::new(max_concurrent)),
        }
    }
}

#[async_trait]
impl SpanExporter for RateLimitedExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let _permit = self.semaphore.acquire().await
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        
        let mut exporter = self.inner.lock().await;
        exporter.export(batch).await
    }
}
````

---

## 10. 完整项目示例

### 10.1 Redis Exporter

````rust
use redis::AsyncCommands;

#[derive(Debug, Clone)]
pub struct RedisExporter {
    client: redis::Client,
    key_prefix: String,
}

impl RedisExporter {
    pub fn new(redis_url: &str, key_prefix: String) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        Ok(Self { client, key_prefix })
    }
}

#[async_trait]
impl SpanExporter for RedisExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let mut con = self.client.get_multiplexed_async_connection().await
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        
        for span in batch {
            let key = format!("{}:{}", self.key_prefix, span.span_context.trace_id());
            let value = serde_json::to_string(&span)
                .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
            
            con.set_ex(key, value, 3600).await
                .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        }
        
        Ok(())
    }
}
````

### 10.2 S3 Exporter

````rust
use aws_sdk_s3::Client as S3Client;

#[derive(Debug, Clone)]
pub struct S3Exporter {
    client: S3Client,
    bucket: String,
}

impl S3Exporter {
    pub async fn new(bucket: String) -> Self {
        let config = aws_config::load_from_env().await;
        let client = S3Client::new(&config);
        
        Self { client, bucket }
    }
}

#[async_trait]
impl SpanExporter for S3Exporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let key = format!("traces/{}.json", timestamp);
        let json = serde_json::to_string(&batch)
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        
        self.client
            .put_object()
            .bucket(&self.bucket)
            .key(&key)
            .body(json.into_bytes().into())
            .send()
            .await
            .map_err(|e| opentelemetry::trace::TraceError::Other(Box::new(e)))?;
        
        Ok(())
    }
}
````

---

## 总结

### 核心要点

1. **SpanExporter Trait**: 实现 `export` 和 `shutdown` 方法
2. **批处理**: 支持批量导出提高性能
3. **错误处理**: 重试机制、降级策略
4. **异步导出**: 提高吞吐量
5. **监控**: 指标和日志
6. **测试**: 单元测试和集成测试

### Exporter 对比

| Exporter | 优势 | 劣势 | 使用场景 |
|----------|------|------|----------|
| File | 简单、可靠 | 性能较低 | 调试、归档 |
| Database | 查询方便 | 写入开销大 | 分析、报表 |
| Kafka | 高吞吐 | 复杂度高 | 实时处理 |
| Redis | 快速 | 容量有限 | 缓存、临时存储 |
| S3 | 低成本、可靠 | 延迟较高 | 归档、备份 |

### 最佳实践清单

- ✅ 实现 `SpanExporter` trait
- ✅ 使用批处理优化性能
- ✅ 实现重试机制
- ✅ 添加超时控制
- ✅ 限制并发数量
- ✅ 记录指标和日志
- ✅ 编写单元测试
- ✅ 错误降级策略
- ✅ 异步导出提高吞吐
- ✅ 资源池复用连接
- ❌ 不要阻塞主线程
- ❌ 不要忽略错误

---

**相关文档**:

- [自定义 Sampler](./02_自定义_Sampler_Rust完整版.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [故障排查](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
