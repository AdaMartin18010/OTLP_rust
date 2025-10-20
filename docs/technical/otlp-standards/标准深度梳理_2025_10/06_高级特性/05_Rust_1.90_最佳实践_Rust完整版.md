# Rust 1.90+ 最佳实践 - OTLP 完整版

## 目录

- [Rust 1.90+ 最佳实践 - OTLP 完整版](#rust-190-最佳实践---otlp-完整版)
  - [目录](#目录)
  - [1. Rust 1.90 新特性概览](#1-rust-190-新特性概览)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 标准库增强](#12-标准库增强)
  - [2. 异步编程最佳实践](#2-异步编程最佳实践)
    - [2.1 避免阻塞异步运行时](#21-避免阻塞异步运行时)
    - [2.2 优雅的错误传播](#22-优雅的错误传播)
    - [2.3 并发控制](#23-并发控制)
    - [2.4 超时与取消](#24-超时与取消)
  - [3. 错误处理最佳实践](#3-错误处理最佳实践)
    - [3.1 使用 thiserror 定义错误](#31-使用-thiserror-定义错误)
    - [3.2 Result 类型别名](#32-result-类型别名)
    - [3.3 错误恢复](#33-错误恢复)
  - [4. 性能优化技巧](#4-性能优化技巧)
    - [4.1 零拷贝与 Arc](#41-零拷贝与-arc)
    - [4.2 对象池](#42-对象池)
    - [4.3 批量处理与预分配](#43-批量处理与预分配)
    - [4.4 SIMD 优化（使用 Arrow）](#44-simd-优化使用-arrow)
  - [5. 类型系统高级用法](#5-类型系统高级用法)
    - [5.1 Builder Pattern](#51-builder-pattern)
    - [5.2 Newtype Pattern](#52-newtype-pattern)
    - [5.3 Phantom Types](#53-phantom-types)
  - [6. 并发与同步](#6-并发与同步)
    - [6.1 使用 parking\_lot](#61-使用-parking_lot)
    - [6.2 无锁数据结构](#62-无锁数据结构)
  - [7. 生产级代码组织](#7-生产级代码组织)
    - [7.1 模块结构](#71-模块结构)
    - [7.2 Feature Flags](#72-feature-flags)
  - [8. 完整示例](#8-完整示例)
    - [8.1 生产级 OTLP Collector](#81-生产级-otlp-collector)
  - [总结](#总结)

---

## 1. Rust 1.90 新特性概览

### 1.1 核心特性

```rust
// 1. Async fn in traits (稳定)
#[async_trait]
pub trait SpanExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), ExportError>;
}

// 2. 泛型关联类型 (GATs)
pub trait DataStream {
    type Item;
    type Error;
    
    async fn next(&mut self) -> Result<Option<Self::Item>, Self::Error>;
}

// 3. let-else 语法
pub fn process_span(data: Option<SpanData>) -> Result<(), Error> {
    let Some(span) = data else {
        return Err(Error::MissingSpan);
    };
    
    // 处理 span
    Ok(())
}

// 4. 更强大的 const 泛型
pub struct FixedSizeBuffer<T, const N: usize> {
    data: [T; N],
    len: usize,
}

impl<T: Default + Copy, const N: usize> FixedSizeBuffer<T, N> {
    pub const fn new() -> Self {
        Self {
            data: [T::default(); N],
            len: 0,
        }
    }
}
```

### 1.2 标准库增强

```rust
use std::sync::OnceLock;

// 全局单例（无需 lazy_static）
static TRACER_PROVIDER: OnceLock<TracerProvider> = OnceLock::new();

pub fn get_tracer_provider() -> &'static TracerProvider {
    TRACER_PROVIDER.get_or_init(|| {
        TracerProvider::builder()
            .with_resource(Resource::default())
            .build()
    })
}
```

---

## 2. 异步编程最佳实践

### 2.1 避免阻塞异步运行时

```rust
// ❌ 错误：在异步函数中使用同步 I/O
async fn bad_example() {
    let data = std::fs::read_to_string("file.txt").unwrap(); // 阻塞！
}

// ✅ 正确：使用异步 I/O
async fn good_example() -> Result<String, std::io::Error> {
    tokio::fs::read_to_string("file.txt").await
}

// ✅ 正确：CPU 密集型任务使用 spawn_blocking
async fn cpu_intensive_task(data: Vec<u8>) -> Result<Vec<u8>, Error> {
    tokio::task::spawn_blocking(move || {
        // CPU 密集型计算
        compress_data(data)
    })
    .await
    .map_err(|e| Error::TaskJoin(e))?
}

fn compress_data(data: Vec<u8>) -> Result<Vec<u8>, Error> {
    // 压缩逻辑
    Ok(data)
}
```

### 2.2 优雅的错误传播

```rust
use anyhow::{Context, Result};

async fn export_spans_with_context(spans: Vec<SpanData>) -> Result<()> {
    let exporter = create_exporter()
        .await
        .context("Failed to create exporter")?;
    
    exporter
        .export(spans)
        .await
        .context("Failed to export spans")?;
    
    Ok(())
}
```

### 2.3 并发控制

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

pub struct RateLimitedExporter {
    inner: Arc<dyn SpanExporter>,
    semaphore: Arc<Semaphore>,
}

impl RateLimitedExporter {
    pub fn new(inner: Arc<dyn SpanExporter>, max_concurrent: usize) -> Self {
        Self {
            inner,
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }
    
    pub async fn export(&self, spans: Vec<SpanData>) -> Result<(), ExportError> {
        // 获取许可证（限流）
        let _permit = self.semaphore.acquire().await.unwrap();
        
        self.inner.export(spans).await
    }
}
```

### 2.4 超时与取消

```rust
use tokio::time::{timeout, Duration};

async fn export_with_timeout(
    exporter: &dyn SpanExporter,
    spans: Vec<SpanData>,
    timeout_duration: Duration,
) -> Result<(), ExportError> {
    match timeout(timeout_duration, exporter.export(spans)).await {
        Ok(result) => result,
        Err(_) => Err(ExportError::Timeout),
    }
}

// 使用 tokio::select! 处理多个 Future
async fn export_with_cancellation(
    exporter: &dyn SpanExporter,
    spans: Vec<SpanData>,
    cancel_token: tokio_util::sync::CancellationToken,
) -> Result<(), ExportError> {
    tokio::select! {
        result = exporter.export(spans) => result,
        _ = cancel_token.cancelled() => Err(ExportError::Cancelled),
    }
}
```

---

## 3. 错误处理最佳实践

### 3.1 使用 thiserror 定义错误

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    #[error("Timeout after {0:?}")]
    Timeout(Duration),
    
    #[error("Invalid configuration: {0}")]
    InvalidConfig(String),
    
    #[error("Backend error: {status_code} - {message}")]
    Backend {
        status_code: u16,
        message: String,
    },
}
```

### 3.2 Result 类型别名

```rust
pub type Result<T> = std::result::Result<T, OtlpError>;

// 使用
pub async fn export_traces(spans: Vec<SpanData>) -> Result<()> {
    // ...
    Ok(())
}
```

### 3.3 错误恢复

```rust
use backoff::{ExponentialBackoff, future::retry};

pub async fn export_with_retry(
    exporter: &dyn SpanExporter,
    spans: Vec<SpanData>,
) -> Result<()> {
    let backoff = ExponentialBackoff {
        max_elapsed_time: Some(Duration::from_secs(60)),
        ..Default::default()
    };
    
    retry(backoff, || async {
        exporter.export(spans.clone())
            .await
            .map_err(|e| {
                if is_retryable(&e) {
                    backoff::Error::transient(e)
                } else {
                    backoff::Error::permanent(e)
                }
            })
    })
    .await
}

fn is_retryable(error: &ExportError) -> bool {
    match error {
        ExportError::Network(_) => true,
        ExportError::Timeout => true,
        ExportError::Backend { status_code, .. } => {
            *status_code == 429 || *status_code >= 500
        }
        _ => false,
    }
}
```

---

## 4. 性能优化技巧

### 4.1 零拷贝与 Arc

```rust
use std::sync::Arc;
use bytes::Bytes;

// ✅ 使用 Arc 避免克隆大对象
#[derive(Clone)]
pub struct SharedSpanData {
    inner: Arc<SpanDataInner>,
}

struct SpanDataInner {
    trace_id: TraceId,
    span_id: SpanId,
    attributes: Vec<KeyValue>,
    // 大量数据
}

// ✅ 使用 Bytes 零拷贝
pub struct ZeroCopyPayload {
    data: Bytes,
}

impl ZeroCopyPayload {
    pub fn slice(&self, range: std::ops::Range<usize>) -> Bytes {
        self.data.slice(range)  // 零拷贝切片
    }
}
```

### 4.2 对象池

```rust
use parking_lot::Mutex;
use std::sync::Arc;

pub struct SpanPool {
    pool: Arc<Mutex<Vec<Box<SpanData>>>>,
    capacity: usize,
}

impl SpanPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(capacity))),
            capacity,
        }
    }
    
    pub fn acquire(&self) -> PooledSpan {
        let mut pool = self.pool.lock();
        let span = pool.pop().unwrap_or_else(|| Box::new(SpanData::default()));
        
        PooledSpan {
            span: Some(span),
            pool: self.pool.clone(),
        }
    }
}

pub struct PooledSpan {
    span: Option<Box<SpanData>>,
    pool: Arc<Mutex<Vec<Box<SpanData>>>>,
}

impl Drop for PooledSpan {
    fn drop(&mut self) {
        if let Some(mut span) = self.span.take() {
            // 重置 Span
            span.attributes.clear();
            
            let mut pool = self.pool.lock();
            if pool.len() < pool.capacity() {
                pool.push(span);
            }
        }
    }
}

impl std::ops::Deref for PooledSpan {
    type Target = SpanData;
    
    fn deref(&self) -> &Self::Target {
        self.span.as_ref().unwrap()
    }
}

impl std::ops::DerefMut for PooledSpan {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.span.as_mut().unwrap()
    }
}
```

### 4.3 批量处理与预分配

```rust
pub struct BatchExporter {
    buffer: Vec<SpanData>,
    capacity: usize,
}

impl BatchExporter {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),  // 预分配
            capacity,
        }
    }
    
    pub fn add(&mut self, span: SpanData) -> Option<Vec<SpanData>> {
        self.buffer.push(span);
        
        if self.buffer.len() >= self.capacity {
            // 避免重新分配
            let mut batch = Vec::with_capacity(self.capacity);
            std::mem::swap(&mut batch, &mut self.buffer);
            Some(batch)
        } else {
            None
        }
    }
}
```

### 4.4 SIMD 优化（使用 Arrow）

```rust
use arrow::array::{Int64Array, StringArray};
use arrow::datatypes::{DataType, Field, Schema};
use arrow::record_batch::RecordBatch;
use std::sync::Arc;

pub fn convert_spans_to_arrow(spans: &[SpanData]) -> RecordBatch {
    let schema = Arc::new(Schema::new(vec![
        Field::new("trace_id", DataType::Utf8, false),
        Field::new("span_id", DataType::Utf8, false),
        Field::new("duration_ns", DataType::Int64, false),
    ]));
    
    let trace_ids: Vec<String> = spans.iter()
        .map(|s| format!("{:?}", s.span_context.trace_id()))
        .collect();
    
    let span_ids: Vec<String> = spans.iter()
        .map(|s| format!("{:?}", s.span_context.span_id()))
        .collect();
    
    let durations: Vec<i64> = spans.iter()
        .map(|s| (s.end_time - s.start_time).as_nanos() as i64)
        .collect();
    
    RecordBatch::try_new(
        schema,
        vec![
            Arc::new(StringArray::from(trace_ids)),
            Arc::new(StringArray::from(span_ids)),
            Arc::new(Int64Array::from(durations)),
        ],
    ).unwrap()
}
```

---

## 5. 类型系统高级用法

### 5.1 Builder Pattern

```rust
pub struct TracerProviderBuilder {
    resource: Option<Resource>,
    sampler: Option<Box<dyn Sampler>>,
    span_processors: Vec<Box<dyn SpanProcessor>>,
}

impl TracerProviderBuilder {
    pub fn new() -> Self {
        Self {
            resource: None,
            sampler: None,
            span_processors: Vec::new(),
        }
    }
    
    pub fn with_resource(mut self, resource: Resource) -> Self {
        self.resource = Some(resource);
        self
    }
    
    pub fn with_sampler(mut self, sampler: impl Sampler + 'static) -> Self {
        self.sampler = Some(Box::new(sampler));
        self
    }
    
    pub fn with_span_processor(mut self, processor: impl SpanProcessor + 'static) -> Self {
        self.span_processors.push(Box::new(processor));
        self
    }
    
    pub fn build(self) -> TracerProvider {
        TracerProvider {
            resource: self.resource.unwrap_or_default(),
            sampler: self.sampler.unwrap_or_else(|| Box::new(AlwaysOnSampler)),
            span_processors: self.span_processors,
        }
    }
}
```

### 5.2 Newtype Pattern

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TenantId(uuid::Uuid);

impl TenantId {
    pub fn new() -> Self {
        Self(uuid::Uuid::new_v4())
    }
    
    pub fn from_string(s: &str) -> Result<Self, uuid::Error> {
        Ok(Self(uuid::Uuid::parse_str(s)?))
    }
}

impl std::fmt::Display for TenantId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// 使用强类型避免混淆
fn process_tenant(tenant_id: TenantId) {
    // tenant_id 不会与普通 String 混淆
}
```

### 5.3 Phantom Types

```rust
use std::marker::PhantomData;

pub struct Initialized;
pub struct Uninitialized;

pub struct TracerProvider<State = Uninitialized> {
    resource: Resource,
    _state: PhantomData<State>,
}

impl TracerProvider<Uninitialized> {
    pub fn new() -> Self {
        Self {
            resource: Resource::default(),
            _state: PhantomData,
        }
    }
    
    pub fn with_resource(mut self, resource: Resource) -> Self {
        self.resource = resource;
        self
    }
    
    pub fn build(self) -> TracerProvider<Initialized> {
        TracerProvider {
            resource: self.resource,
            _state: PhantomData,
        }
    }
}

impl TracerProvider<Initialized> {
    pub fn tracer(&self, name: &str) -> Tracer {
        // 只有初始化后才能创建 Tracer
        Tracer::new(name, self.resource.clone())
    }
}
```

---

## 6. 并发与同步

### 6.1 使用 parking_lot

```rust
// ✅ parking_lot 性能更好
use parking_lot::{Mutex, RwLock};

pub struct ConcurrentRegistry {
    exporters: RwLock<HashMap<String, Arc<dyn SpanExporter>>>,
}

impl ConcurrentRegistry {
    pub fn new() -> Self {
        Self {
            exporters: RwLock::new(HashMap::new()),
        }
    }
    
    pub fn register(&self, name: String, exporter: Arc<dyn SpanExporter>) {
        let mut exporters = self.exporters.write();
        exporters.insert(name, exporter);
    }
    
    pub fn get(&self, name: &str) -> Option<Arc<dyn SpanExporter>> {
        let exporters = self.exporters.read();
        exporters.get(name).cloned()
    }
}
```

### 6.2 无锁数据结构

```rust
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};

pub struct Metrics {
    spans_received: AtomicU64,
    spans_exported: AtomicU64,
    is_healthy: AtomicBool,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            spans_received: AtomicU64::new(0),
            spans_exported: AtomicU64::new(0),
            is_healthy: AtomicBool::new(true),
        }
    }
    
    pub fn increment_received(&self) {
        self.spans_received.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn increment_exported(&self) {
        self.spans_exported.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn set_healthy(&self, healthy: bool) {
        self.is_healthy.store(healthy, Ordering::Release);
    }
    
    pub fn is_healthy(&self) -> bool {
        self.is_healthy.load(Ordering::Acquire)
    }
}
```

---

## 7. 生产级代码组织

### 7.1 模块结构

```text
otlp_collector/
├── src/
│   ├── main.rs
│   ├── lib.rs
│   ├── config/
│   │   ├── mod.rs
│   │   └── loader.rs
│   ├── receiver/
│   │   ├── mod.rs
│   │   ├── otlp.rs
│   │   └── jaeger.rs
│   ├── processor/
│   │   ├── mod.rs
│   │   ├── batch.rs
│   │   └── filter.rs
│   ├── exporter/
│   │   ├── mod.rs
│   │   ├── otlp.rs
│   │   └── jaeger.rs
│   └── pipeline/
│       ├── mod.rs
│       └── builder.rs
├── tests/
│   ├── integration_test.rs
│   └── e2e_test.rs
├── benches/
│   └── performance.rs
└── Cargo.toml
```

### 7.2 Feature Flags

```toml
[features]
default = ["otlp-grpc", "jaeger"]
otlp-grpc = ["tonic", "prost"]
otlp-http = ["reqwest", "serde_json"]
jaeger = ["thrift"]
prometheus = ["prometheus-client"]
```

```rust
// 条件编译
#[cfg(feature = "otlp-grpc")]
pub mod otlp_grpc;

#[cfg(feature = "jaeger")]
pub mod jaeger;
```

---

## 8. 完整示例

### 8.1 生产级 OTLP Collector

```rust
// main.rs
use anyhow::Result;
use tracing_subscriber::EnvFilter;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();
    
    // 2. 加载配置
    let config = config::load("config.yaml")?;
    
    // 3. 构建 Collector
    let collector = CollectorBuilder::new(config)
        .build()
        .await?;
    
    // 4. 启动服务
    collector.start().await?;
    
    // 5. 优雅关闭
    tokio::signal::ctrl_c().await?;
    tracing::info!("Shutting down...");
    
    collector.shutdown().await?;
    
    Ok(())
}
```

---

## 总结

Rust 1.90+ 在 OTLP 开发中的**最佳实践**：

1. **异步编程**：避免阻塞、使用 `spawn_blocking`、超时控制
2. **错误处理**：使用 `thiserror`、重试机制、错误分类
3. **性能优化**：零拷贝、对象池、SIMD、预分配
4. **类型系统**：Builder Pattern、Newtype、Phantom Types
5. **并发**：`parking_lot`、无锁数据结构、`tokio::select!`
6. **代码组织**：模块化、Feature Flags、测试分离

通过遵循这些最佳实践，可以构建高性能、可维护的 OTLP 系统。
