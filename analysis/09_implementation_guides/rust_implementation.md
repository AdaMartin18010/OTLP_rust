# Rust实现指南

## 概述

本文档提供OTLP项目的Rust实现指南，包括架构设计、核心组件实现、性能优化、测试策略等关键技术要点，为开发者提供详细的实现参考。

## 架构设计

### 1. 整体架构

```rust
// 核心架构组件
pub struct OTLPCore {
    pub collector: DataCollector,
    pub processor: DataProcessor,
    pub exporter: DataExporter,
    pub config_manager: ConfigManager,
    pub metrics_registry: MetricsRegistry,
}

pub struct DataCollector {
    pub trace_collector: TraceCollector,
    pub metric_collector: MetricCollector,
    pub log_collector: LogCollector,
    pub resource_detector: ResourceDetector,
}

pub struct DataProcessor {
    pub batch_processor: BatchProcessor,
    pub attribute_processor: AttributeProcessor,
    pub sampling_processor: SamplingProcessor,
    pub filter_processor: FilterProcessor,
}

pub struct DataExporter {
    pub otlp_exporter: OTLPExporter,
    pub jaeger_exporter: JaegerExporter,
    pub prometheus_exporter: PrometheusExporter,
    pub console_exporter: ConsoleExporter,
}
```

### 2. 模块化设计

```rust
// 模块化架构
pub mod core {
    pub mod collector;
    pub mod processor;
    pub mod exporter;
    pub mod resource;
}

pub mod protocols {
    pub mod otlp;
    pub mod jaeger;
    pub mod prometheus;
    pub mod zipkin;
}

pub mod utils {
    pub mod config;
    pub mod metrics;
    pub mod logging;
    pub mod error;
}

pub mod extensions {
    pub mod sampling;
    pub mod filtering;
    pub mod transformation;
    pub mod enrichment;
}
```

## 核心组件实现

### 1. 数据收集器

```rust
use tokio::sync::{mpsc, RwLock};
use std::sync::Arc;
use std::time::{Duration, Instant};

pub struct TraceCollector {
    pub spans: Arc<RwLock<Vec<Span>>>,
    pub sender: mpsc::UnboundedSender<Span>,
    pub receiver: Arc<RwLock<mpsc::UnboundedReceiver<Span>>>,
    pub config: CollectorConfig,
}

impl TraceCollector {
    pub fn new(config: CollectorConfig) -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        
        Self {
            spans: Arc::new(RwLock::new(Vec::new())),
            sender,
            receiver: Arc::new(RwLock::new(receiver)),
            config,
        }
    }
    
    pub async fn collect_span(&self, span: Span) -> Result<(), CollectionError> {
        // 验证span数据
        self.validate_span(&span)?;
        
        // 发送到处理队列
        self.sender.send(span).map_err(|e| {
            CollectionError::SendError(e.to_string())
        })?;
        
        Ok(())
    }
    
    pub async fn start_collection(&self) -> Result<(), CollectionError> {
        let receiver = self.receiver.clone();
        let spans = self.spans.clone();
        let config = self.config.clone();
        
        tokio::spawn(async move {
            let mut receiver = receiver.write().await;
            let mut batch = Vec::new();
            let mut last_flush = Instant::now();
            
            while let Some(span) = receiver.recv().await {
                batch.push(span);
                
                // 检查批量大小或时间间隔
                if batch.len() >= config.batch_size 
                   || last_flush.elapsed() >= config.flush_interval {
                    
                    // 批量处理spans
                    let mut spans_guard = spans.write().await;
                    spans_guard.extend(batch.drain(..));
                    drop(spans_guard);
                    
                    last_flush = Instant::now();
                }
            }
        });
        
        Ok(())
    }
    
    fn validate_span(&self, span: &Span) -> Result<(), ValidationError> {
        if span.trace_id.is_empty() {
            return Err(ValidationError::MissingTraceId);
        }
        
        if span.span_id.is_empty() {
            return Err(ValidationError::MissingSpanId);
        }
        
        if span.name.is_empty() {
            return Err(ValidationError::MissingSpanName);
        }
        
        Ok(())
    }
}
```

### 2. 数据处理器

```rust
use async_trait::async_trait;

#[async_trait]
pub trait Processor: Send + Sync {
    async fn process(&self, data: &mut TelemetryData) -> Result<(), ProcessingError>;
    async fn shutdown(&self) -> Result<(), ProcessingError>;
}

pub struct BatchProcessor {
    pub batch_size: usize,
    pub timeout: Duration,
    pub buffer: Arc<RwLock<Vec<TelemetryData>>>,
    pub sender: mpsc::UnboundedSender<Vec<TelemetryData>>,
}

#[async_trait]
impl Processor for BatchProcessor {
    async fn process(&self, data: &mut TelemetryData) -> Result<(), ProcessingError> {
        let mut buffer = self.buffer.write().await;
        buffer.push(data.clone());
        
        if buffer.len() >= self.batch_size {
            let batch = buffer.drain(..).collect();
            self.sender.send(batch).map_err(|e| {
                ProcessingError::SendError(e.to_string())
            })?;
        }
        
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ProcessingError> {
        let mut buffer = self.buffer.write().await;
        if !buffer.is_empty() {
            let batch = buffer.drain(..).collect();
            self.sender.send(batch).map_err(|e| {
                ProcessingError::SendError(e.to_string())
            })?;
        }
        
        Ok(())
    }
}

pub struct AttributeProcessor {
    pub actions: Vec<AttributeAction>,
}

#[async_trait]
impl Processor for AttributeProcessor {
    async fn process(&self, data: &mut TelemetryData) -> Result<(), ProcessingError> {
        for action in &self.actions {
            match action {
                AttributeAction::Insert { key, value } => {
                    data.attributes.insert(key.clone(), value.clone());
                },
                AttributeAction::Update { key, value } => {
                    if data.attributes.contains_key(key) {
                        data.attributes.insert(key.clone(), value.clone());
                    }
                },
                AttributeAction::Upsert { key, value } => {
                    data.attributes.insert(key.clone(), value.clone());
                },
                AttributeAction::Delete { key } => {
                    data.attributes.remove(key);
                },
                AttributeAction::Hash { key } => {
                    if let Some(value) = data.attributes.get(key) {
                        let hashed = self.hash_value(value);
                        data.attributes.insert(key.clone(), hashed);
                    }
                },
            }
        }
        
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ProcessingError> {
        Ok(())
    }
}

impl AttributeProcessor {
    fn hash_value(&self, value: &AttributeValue) -> AttributeValue {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        let hash = hasher.finish();
        
        AttributeValue::String(format!("hash_{}", hash))
    }
}
```

### 3. 数据导出器

```rust
use reqwest::Client;
use prost::Message;

pub struct OTLPExporter {
    pub client: Client,
    pub endpoint: String,
    pub headers: HashMap<String, String>,
    pub timeout: Duration,
    pub compression: CompressionType,
}

impl OTLPExporter {
    pub fn new(config: ExporterConfig) -> Self {
        let client = Client::builder()
            .timeout(config.timeout)
            .build()
            .expect("Failed to create HTTP client");
        
        Self {
            client,
            endpoint: config.endpoint,
            headers: config.headers,
            timeout: config.timeout,
            compression: config.compression,
        }
    }
    
    pub async fn export_traces(&self, spans: Vec<Span>) -> Result<(), ExportError> {
        // 转换为OTLP格式
        let otlp_spans = self.convert_to_otlp_spans(spans)?;
        
        // 序列化
        let mut buffer = Vec::new();
        otlp_spans.encode(&mut buffer).map_err(|e| {
            ExportError::SerializationError(e.to_string())
        })?;
        
        // 压缩
        let compressed_data = self.compress_data(&buffer)?;
        
        // 发送HTTP请求
        let mut request = self.client
            .post(&format!("{}/v1/traces", self.endpoint))
            .body(compressed_data);
        
        for (key, value) in &self.headers {
            request = request.header(key, value);
        }
        
        match self.compression {
            CompressionType::Gzip => {
                request = request.header("Content-Encoding", "gzip");
            },
            CompressionType::None => {},
        }
        
        let response = request.send().await.map_err(|e| {
            ExportError::NetworkError(e.to_string())
        })?;
        
        if !response.status().is_success() {
            return Err(ExportError::HttpError(response.status().as_u16()));
        }
        
        Ok(())
    }
    
    fn convert_to_otlp_spans(&self, spans: Vec<Span>) -> Result<otlp::TracesData, ConversionError> {
        let mut resource_spans = HashMap::new();
        
        for span in spans {
            let resource_key = self.get_resource_key(&span.resource);
            let resource_span_list = resource_spans
                .entry(resource_key)
                .or_insert_with(Vec::new);
            
            resource_span_list.push(self.convert_span_to_otlp(span)?);
        }
        
        let mut traces_data = otlp::TracesData::default();
        
        for (resource, spans) in resource_spans {
            let mut resource_spans = otlp::ResourceSpans::default();
            resource_spans.resource = Some(resource);
            
            let mut scope_spans = otlp::ScopeSpans::default();
            scope_spans.spans = spans;
            
            resource_spans.scope_spans = vec![scope_spans];
            traces_data.resource_spans.push(resource_spans);
        }
        
        Ok(traces_data)
    }
    
    fn compress_data(&self, data: &[u8]) -> Result<Vec<u8>, CompressionError> {
        match self.compression {
            CompressionType::Gzip => {
                use flate2::write::GzEncoder;
                use flate2::Compression;
                use std::io::Write;
                
                let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
                encoder.write_all(data).map_err(|e| {
                    CompressionError::CompressionFailed(e.to_string())
                })?;
                
                encoder.finish().map_err(|e| {
                    CompressionError::CompressionFailed(e.to_string())
                })
            },
            CompressionType::None => Ok(data.to_vec()),
        }
    }
}
```

## 性能优化

### 1. 内存优化

```rust
use std::sync::Arc;
use parking_lot::RwLock;
use crossbeam::queue::SegQueue;

pub struct MemoryOptimizedCollector {
    pub span_pool: Arc<SpanPool>,
    pub buffer_pool: Arc<BufferPool>,
    pub queue: Arc<SegQueue<Arc<Span>>>,
}

pub struct SpanPool {
    pub pool: SegQueue<Box<Span>>,
    pub max_size: usize,
    pub current_size: AtomicUsize,
}

impl SpanPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: SegQueue::new(),
            max_size,
            current_size: AtomicUsize::new(0),
        }
    }
    
    pub fn get_span(&self) -> Box<Span> {
        if let Some(span) = self.pool.pop() {
            // 重置span数据
            self.reset_span(&mut *span);
            span
        } else {
            Box::new(Span::default())
        }
    }
    
    pub fn return_span(&self, mut span: Box<Span>) {
        if self.current_size.load(Ordering::Relaxed) < self.max_size {
            // 清理span数据
            self.clear_span(&mut *span);
            self.pool.push(span);
        }
        // 如果池已满，让span自动释放
    }
    
    fn reset_span(&self, span: &mut Span) {
        span.trace_id.clear();
        span.span_id.clear();
        span.name.clear();
        span.attributes.clear();
        span.events.clear();
        span.links.clear();
    }
    
    fn clear_span(&self, span: &mut Span) {
        span.trace_id.clear();
        span.span_id.clear();
        span.name.clear();
        span.attributes.clear();
        span.events.clear();
        span.links.clear();
    }
}
```

### 2. 并发优化

```rust
use tokio::sync::Semaphore;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct ConcurrentProcessor {
    pub semaphore: Arc<Semaphore>,
    pub worker_count: usize,
    pub processed_count: AtomicU64,
    pub error_count: AtomicU64,
}

impl ConcurrentProcessor {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            worker_count: max_concurrent,
            processed_count: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
        }
    }
    
    pub async fn process_batch(&self, batch: Vec<TelemetryData>) -> Result<(), ProcessingError> {
        let chunk_size = (batch.len() + self.worker_count - 1) / self.worker_count;
        let chunks: Vec<_> = batch.chunks(chunk_size).collect();
        
        let mut tasks = Vec::new();
        
        for chunk in chunks {
            let chunk = chunk.to_vec();
            let semaphore = self.semaphore.clone();
            let processed_count = &self.processed_count;
            let error_count = &self.error_count;
            
            let task = tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                
                for data in chunk {
                    match Self::process_single_data(data).await {
                        Ok(_) => {
                            processed_count.fetch_add(1, Ordering::Relaxed);
                        },
                        Err(_) => {
                            error_count.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
            });
            
            tasks.push(task);
        }
        
        // 等待所有任务完成
        for task in tasks {
            task.await.map_err(|e| {
                ProcessingError::TaskError(e.to_string())
            })?;
        }
        
        Ok(())
    }
    
    async fn process_single_data(data: TelemetryData) -> Result<(), ProcessingError> {
        // 处理单个数据项
        tokio::time::sleep(Duration::from_millis(1)).await;
        Ok(())
    }
}
```

### 3. 网络优化

```rust
use tokio::net::TcpStream;
use tokio_util::codec::{Framed, LengthDelimitedCodec};
use futures::{SinkExt, StreamExt};

pub struct OptimizedNetworkExporter {
    pub connection_pool: ConnectionPool,
    pub retry_policy: RetryPolicy,
    pub circuit_breaker: CircuitBreaker,
}

pub struct ConnectionPool {
    pub connections: Arc<RwLock<Vec<Connection>>>,
    pub max_connections: usize,
    pub idle_timeout: Duration,
}

impl ConnectionPool {
    pub async fn get_connection(&self, endpoint: &str) -> Result<Connection, NetworkError> {
        // 尝试获取空闲连接
        {
            let mut connections = self.connections.write().await;
            for (i, conn) in connections.iter().enumerate() {
                if conn.endpoint == endpoint && conn.is_idle() {
                    return Ok(connections.remove(i));
                }
            }
        }
        
        // 创建新连接
        self.create_connection(endpoint).await
    }
    
    pub async fn return_connection(&self, connection: Connection) {
        let mut connections = self.connections.write().await;
        if connections.len() < self.max_connections {
            connections.push(connection);
        }
        // 如果池已满，连接会自动关闭
    }
    
    async fn create_connection(&self, endpoint: &str) -> Result<Connection, NetworkError> {
        let stream = TcpStream::connect(endpoint).await.map_err(|e| {
            NetworkError::ConnectionFailed(e.to_string())
        })?;
        
        let framed = Framed::new(stream, LengthDelimitedCodec::new());
        
        Ok(Connection {
            endpoint: endpoint.to_string(),
            framed: Arc::new(RwLock::new(framed)),
            last_used: Instant::now(),
        })
    }
}

pub struct Connection {
    pub endpoint: String,
    pub framed: Arc<RwLock<Framed<TcpStream, LengthDelimitedCodec>>>,
    pub last_used: Instant,
}

impl Connection {
    pub fn is_idle(&self) -> bool {
        self.last_used.elapsed() < Duration::from_secs(30)
    }
    
    pub async fn send_data(&mut self, data: &[u8]) -> Result<(), NetworkError> {
        let mut framed = self.framed.write().await;
        framed.send(data.into()).await.map_err(|e| {
            NetworkError::SendFailed(e.to_string())
        })?;
        
        self.last_used = Instant::now();
        Ok(())
    }
}
```

## 错误处理

### 1. 错误类型定义

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OTLPError {
    #[error("Collection error: {0}")]
    Collection(#[from] CollectionError),
    
    #[error("Processing error: {0}")]
    Processing(#[from] ProcessingError),
    
    #[error("Export error: {0}")]
    Export(#[from] ExportError),
    
    #[error("Configuration error: {0}")]
    Configuration(#[from] ConfigurationError),
    
    #[error("Network error: {0}")]
    Network(#[from] NetworkError),
}

#[derive(Error, Debug)]
pub enum CollectionError {
    #[error("Validation failed: {0}")]
    Validation(#[from] ValidationError),
    
    #[error("Send error: {0}")]
    SendError(String),
    
    #[error("Buffer overflow")]
    BufferOverflow,
    
    #[error("Resource detection failed: {0}")]
    ResourceDetection(String),
}

#[derive(Error, Debug)]
pub enum ProcessingError {
    #[error("Transformation failed: {0}")]
    Transformation(String),
    
    #[error("Filtering failed: {0}")]
    Filtering(String),
    
    #[error("Batching failed: {0}")]
    Batching(String),
    
    #[error("Task error: {0}")]
    TaskError(String),
}

#[derive(Error, Debug)]
pub enum ExportError {
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Compression error: {0}")]
    CompressionError(String),
    
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("HTTP error: {0}")]
    HttpError(u16),
    
    #[error("Authentication failed")]
    AuthenticationFailed,
}
```

### 2. 错误恢复机制

```rust
use std::sync::atomic::{AtomicU32, Ordering};

pub struct ErrorRecoveryManager {
    pub retry_policy: RetryPolicy,
    pub circuit_breaker: CircuitBreaker,
    pub fallback_exporter: Option<Box<dyn Exporter>>,
    pub error_metrics: ErrorMetrics,
}

pub struct RetryPolicy {
    pub max_attempts: u32,
    pub base_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
}

impl RetryPolicy {
    pub async fn execute_with_retry<F, T, E>(&self, mut operation: F) -> Result<T, E>
    where
        F: FnMut() -> Result<T, E>,
        E: std::fmt::Debug,
    {
        let mut attempt = 0;
        let mut delay = self.base_delay;
        
        loop {
            attempt += 1;
            
            match operation() {
                Ok(result) => return Ok(result),
                Err(error) => {
                    if attempt >= self.max_attempts {
                        return Err(error);
                    }
                    
                    // 等待重试
                    tokio::time::sleep(delay).await;
                    
                    // 计算下次重试延迟
                    delay = std::cmp::min(
                        Duration::from_millis(
                            (delay.as_millis() as f64 * self.backoff_multiplier) as u64
                        ),
                        self.max_delay
                    );
                }
            }
        }
    }
}

pub struct CircuitBreaker {
    pub failure_threshold: u32,
    pub recovery_timeout: Duration,
    pub failure_count: AtomicU32,
    pub last_failure_time: Arc<RwLock<Option<Instant>>>,
    pub state: Arc<RwLock<CircuitBreakerState>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // 检查熔断器状态
        let state = {
            let state_guard = self.state.read().await;
            state_guard.clone()
        };
        
        match state {
            CircuitBreakerState::Open => {
                // 检查是否可以尝试恢复
                let last_failure = self.last_failure_time.read().await;
                if let Some(last_failure_time) = *last_failure {
                    if last_failure_time.elapsed() >= self.recovery_timeout {
                        // 转换到半开状态
                        *self.state.write().await = CircuitBreakerState::HalfOpen;
                    } else {
                        return Err(CircuitBreakerError::CircuitOpen);
                    }
                }
            },
            CircuitBreakerState::HalfOpen => {
                // 半开状态，允许一次尝试
            },
            CircuitBreakerState::Closed => {
                // 正常状态
            },
        }
        
        // 执行操作
        match operation() {
            Ok(result) => {
                // 操作成功，重置失败计数
                self.failure_count.store(0, Ordering::Relaxed);
                *self.state.write().await = CircuitBreakerState::Closed;
                Ok(result)
            },
            Err(error) => {
                // 操作失败，增加失败计数
                let failures = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;
                *self.last_failure_time.write().await = Some(Instant::now());
                
                if failures >= self.failure_threshold {
                    *self.state.write().await = CircuitBreakerState::Open;
                }
                
                Err(CircuitBreakerError::OperationFailed(error))
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum CircuitBreakerError<E> {
    #[error("Circuit breaker is open")]
    CircuitOpen,
    
    #[error("Operation failed: {0:?}")]
    OperationFailed(E),
}
```

## 测试策略

### 1. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    
    #[tokio::test]
    async fn test_trace_collector_basic_functionality() {
        let config = CollectorConfig::default();
        let collector = TraceCollector::new(config);
        
        let span = Span {
            trace_id: "test_trace_id".to_string(),
            span_id: "test_span_id".to_string(),
            name: "test_span".to_string(),
            ..Default::default()
        };
        
        let result = collector.collect_span(span).await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_batch_processor_batching() {
        let processor = BatchProcessor {
            batch_size: 3,
            timeout: Duration::from_secs(1),
            buffer: Arc::new(RwLock::new(Vec::new())),
            sender: mpsc::unbounded_channel().0,
        };
        
        // 添加数据到批处理器
        for i in 0..5 {
            let mut data = TelemetryData::default();
            data.attributes.insert("index".to_string(), AttributeValue::Int(i));
            
            let result = processor.process(&mut data).await;
            assert!(result.is_ok());
        }
        
        // 验证批处理行为
        let buffer = processor.buffer.read().await;
        assert_eq!(buffer.len(), 2); // 3个已发送，2个在缓冲区
    }
    
    #[tokio::test]
    async fn test_otlp_exporter_serialization() {
        let config = ExporterConfig {
            endpoint: "http://localhost:4317".to_string(),
            timeout: Duration::from_secs(10),
            compression: CompressionType::None,
            headers: HashMap::new(),
        };
        
        let exporter = OTLPExporter::new(config);
        
        let spans = vec![
            Span {
                trace_id: "trace1".to_string(),
                span_id: "span1".to_string(),
                name: "test_span".to_string(),
                ..Default::default()
            }
        ];
        
        let otlp_spans = exporter.convert_to_otlp_spans(spans);
        assert!(otlp_spans.is_ok());
        
        let otlp_data = otlp_spans.unwrap();
        assert_eq!(otlp_data.resource_spans.len(), 1);
    }
}
```

### 2. 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use testcontainers::*;
    
    #[tokio::test]
    async fn test_end_to_end_trace_flow() {
        // 启动测试容器
        let docker = clients::Cli::default();
        let jaeger = docker.run(images::generic::GenericImage::new("jaegertracing/all-in-one", "latest"));
        
        let jaeger_port = jaeger.get_host_port_ipv4(14268);
        
        // 配置OTLP系统
        let config = OTLPConfig {
            collector: CollectorConfig::default(),
            processor: ProcessorConfig::default(),
            exporter: ExporterConfig {
                endpoint: format!("http://localhost:{}", jaeger_port),
                timeout: Duration::from_secs(10),
                compression: CompressionType::None,
                headers: HashMap::new(),
            },
        };
        
        let otlp_core = OTLPCore::new(config).await.unwrap();
        
        // 创建测试span
        let span = Span {
            trace_id: "integration_test_trace".to_string(),
            span_id: "integration_test_span".to_string(),
            name: "integration_test".to_string(),
            start_time: SystemTime::now(),
            end_time: SystemTime::now() + Duration::from_millis(100),
            ..Default::default()
        };
        
        // 发送span
        otlp_core.collector.collect_span(span).await.unwrap();
        
        // 等待处理完成
        tokio::time::sleep(Duration::from_secs(2)).await;
        
        // 验证数据已发送到Jaeger
        // 这里可以添加对Jaeger API的查询来验证数据
    }
    
    #[tokio::test]
    async fn test_high_throughput_performance() {
        let config = OTLPConfig::default();
        let otlp_core = OTLPCore::new(config).await.unwrap();
        
        let start_time = Instant::now();
        let span_count = 10000;
        
        // 并发发送大量span
        let mut tasks = Vec::new();
        for i in 0..span_count {
            let collector = otlp_core.collector.clone();
            let task = tokio::spawn(async move {
                let span = Span {
                    trace_id: format!("trace_{}", i),
                    span_id: format!("span_{}", i),
                    name: format!("test_span_{}", i),
                    ..Default::default()
                };
                
                collector.collect_span(span).await
            });
            tasks.push(task);
        }
        
        // 等待所有任务完成
        for task in tasks {
            task.await.unwrap().unwrap();
        }
        
        let elapsed = start_time.elapsed();
        let throughput = span_count as f64 / elapsed.as_secs_f64();
        
        println!("Processed {} spans in {:?}, throughput: {:.2} spans/sec", 
                 span_count, elapsed, throughput);
        
        // 验证性能指标
        assert!(throughput > 1000.0, "Throughput should be > 1000 spans/sec");
    }
}
```

### 3. 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_span_creation(c: &mut Criterion) {
    c.bench_function("span_creation", |b| {
        b.iter(|| {
            let span = Span {
                trace_id: black_box("test_trace_id".to_string()),
                span_id: black_box("test_span_id".to_string()),
                name: black_box("test_span".to_string()),
                ..Default::default()
            };
            black_box(span)
        })
    });
}

fn benchmark_attribute_processing(c: &mut Criterion) {
    let processor = AttributeProcessor {
        actions: vec![
            AttributeAction::Insert {
                key: "test_key".to_string(),
                value: AttributeValue::String("test_value".to_string()),
            },
            AttributeAction::Hash {
                key: "sensitive_data".to_string(),
            },
        ],
    };
    
    c.bench_function("attribute_processing", |b| {
        b.iter(|| {
            let mut data = TelemetryData {
                attributes: {
                    let mut attrs = HashMap::new();
                    attrs.insert("sensitive_data".to_string(), 
                               AttributeValue::String("secret_value".to_string()));
                    attrs
                },
                ..Default::default()
            };
            
            tokio_test::block_on(async {
                processor.process(black_box(&mut data)).await
            })
        })
    });
}

fn benchmark_batch_processing(c: &mut Criterion) {
    let (sender, _receiver) = mpsc::unbounded_channel();
    let processor = BatchProcessor {
        batch_size: 100,
        timeout: Duration::from_secs(1),
        buffer: Arc::new(RwLock::new(Vec::new())),
        sender,
    };
    
    c.bench_function("batch_processing", |b| {
        b.iter(|| {
            let mut data = TelemetryData::default();
            tokio_test::block_on(async {
                processor.process(black_box(&mut data)).await
            })
        })
    });
}

criterion_group!(benches, 
    benchmark_span_creation,
    benchmark_attribute_processing,
    benchmark_batch_processing
);
criterion_main!(benches);
```

## 配置管理

### 1. 配置结构

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OTLPConfig {
    pub collector: CollectorConfig,
    pub processor: ProcessorConfig,
    pub exporter: ExporterConfig,
    pub resource: ResourceConfig,
    pub logging: LoggingConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectorConfig {
    pub batch_size: usize,
    pub flush_interval: Duration,
    pub max_queue_size: usize,
    pub timeout: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessorConfig {
    pub processors: Vec<ProcessorType>,
    pub batch_processor: BatchProcessorConfig,
    pub attribute_processor: AttributeProcessorConfig,
    pub sampling_processor: SamplingProcessorConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExporterConfig {
    pub endpoint: String,
    pub timeout: Duration,
    pub compression: CompressionType,
    pub headers: HashMap<String, String>,
    pub retry_policy: RetryPolicyConfig,
}

impl Default for OTLPConfig {
    fn default() -> Self {
        Self {
            collector: CollectorConfig::default(),
            processor: ProcessorConfig::default(),
            exporter: ExporterConfig::default(),
            resource: ResourceConfig::default(),
            logging: LoggingConfig::default(),
        }
    }
}

impl OTLPConfig {
    pub fn from_file(path: &str) -> Result<Self, ConfigError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| ConfigError::FileReadError(e.to_string()))?;
        
        let config: OTLPConfig = toml::from_str(&content)
            .map_err(|e| ConfigError::ParseError(e.to_string()))?;
        
        config.validate()?;
        Ok(config)
    }
    
    pub fn from_env() -> Result<Self, ConfigError> {
        let mut config = Self::default();
        
        if let Ok(endpoint) = std::env::var("OTLP_EXPORTER_ENDPOINT") {
            config.exporter.endpoint = endpoint;
        }
        
        if let Ok(timeout) = std::env::var("OTLP_EXPORTER_TIMEOUT") {
            let timeout_secs: u64 = timeout.parse()
                .map_err(|e| ConfigError::ParseError(e.to_string()))?;
            config.exporter.timeout = Duration::from_secs(timeout_secs);
        }
        
        if let Ok(batch_size) = std::env::var("OTLP_BATCH_SIZE") {
            config.collector.batch_size = batch_size.parse()
                .map_err(|e| ConfigError::ParseError(e.to_string()))?;
        }
        
        config.validate()?;
        Ok(config)
    }
    
    fn validate(&self) -> Result<(), ConfigError> {
        if self.collector.batch_size == 0 {
            return Err(ConfigError::ValidationError(
                "Batch size must be greater than 0".to_string()
            ));
        }
        
        if self.exporter.endpoint.is_empty() {
            return Err(ConfigError::ValidationError(
                "Exporter endpoint cannot be empty".to_string()
            ));
        }
        
        if self.exporter.timeout.as_secs() == 0 {
            return Err(ConfigError::ValidationError(
                "Exporter timeout must be greater than 0".to_string()
            ));
        }
        
        Ok(())
    }
}
```

## 总结

本Rust实现指南提供了OTLP项目的完整实现框架，包括：

1. **架构设计**: 模块化、可扩展的系统架构
2. **核心组件**: 数据收集、处理、导出的完整实现
3. **性能优化**: 内存、并发、网络等多方面优化
4. **错误处理**: 完善的错误类型和恢复机制
5. **测试策略**: 单元测试、集成测试、基准测试
6. **配置管理**: 灵活的配置系统

这些实现为开发高性能、可靠的OTLP系统提供了坚实的基础，确保系统在生产环境中的稳定运行。
