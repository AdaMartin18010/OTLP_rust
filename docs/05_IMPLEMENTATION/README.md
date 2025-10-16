# 🛠️ 实现指南

本文档提供了 OTLP Rust 项目的详细实现指南，包括 Rust 1.90 特性应用、异步编程模式、错误处理策略、测试方法和性能优化技巧。

## 📋 目录

- [🛠️ 实现指南](#️-实现指南)
  - [📋 目录](#-目录)
  - [🚀 Rust 1.90 特性应用](#-rust-190-特性应用)
    - [异步优先设计](#异步优先设计)
      - [现代异步编程](#现代异步编程)
      - [改进的 Trait Solver](#改进的-trait-solver)
    - [类型安全保证](#类型安全保证)
      - [强类型系统](#强类型系统)
      - [零成本抽象](#零成本抽象)
    - [零拷贝优化](#零拷贝优化)
      - [Pointer Provenance API](#pointer-provenance-api)
    - [并发安全](#并发安全)
      - [所有权系统](#所有权系统)
    - [MSRV 感知](#msrv-感知)
      - [版本兼容性](#版本兼容性)
  - [⚡ 异步编程模式](#-异步编程模式)
    - [Tokio 运行时](#tokio-运行时)
      - [运行时配置](#运行时配置)
    - [Future 组合](#future-组合)
      - [组合器模式](#组合器模式)
    - [异步流处理](#异步流处理)
      - [流式数据处理](#流式数据处理)
    - [并发控制](#并发控制)
      - [信号量控制](#信号量控制)
  - [❌ 错误处理模式](#-错误处理模式)
    - [错误类型设计](#错误类型设计)
      - [分层错误类型](#分层错误类型)
    - [错误传播](#错误传播)
      - [错误链](#错误链)
    - [错误恢复](#错误恢复)
      - [重试策略](#重试策略)
    - [错误监控](#错误监控)
      - [错误指标](#错误指标)
  - [🧪 测试策略](#-测试策略)
    - [单元测试](#单元测试)
      - [模块测试](#模块测试)
    - [集成测试](#集成测试)
      - [端到端测试](#端到端测试)
    - [性能测试](#性能测试)
      - [基准测试](#基准测试)
    - [模糊测试](#模糊测试)
      - [输入验证](#输入验证)
  - [⚡ 性能优化](#-性能优化)
    - [内存优化](#内存优化)
      - [内存池](#内存池)
    - [CPU 优化](#cpu-优化)
      - [SIMD 优化](#simd-优化)
    - [I/O 优化](#io-优化)
      - [异步 I/O](#异步-io)
    - [网络优化](#网络优化)
      - [连接复用](#连接复用)
  - [🔗 相关文档](#-相关文档)

## 🚀 Rust 1.90 特性应用

### 异步优先设计

#### 现代异步编程

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 使用 Rust 1.90 的改进 async/await
pub struct OtlpClient {
    inner: Arc<ClientInner>,
}

impl OtlpClient {
    /// 异步创建客户端
    pub async fn new(config: OtlpConfig) -> Result<Self, OtlpError> {
        let inner = ClientInner::new(config).await?;
        Ok(Self {
            inner: Arc::new(inner),
        })
    }
    
    /// 异步发送数据
    pub async fn send_trace(&self, operation: &str) -> Result<TraceBuilder, OtlpError> {
        let span = self.inner.create_span(operation).await?;
        Ok(TraceBuilder::new(span))
    }
}
```

#### 改进的 Trait Solver

```rust
use std::future::Future;

// 利用 Rust 1.90 改进的 Trait Solver
pub trait AsyncTransport: Send + Sync {
    type Error: std::error::Error + Send + Sync + 'static;
    
    async fn send(&self, data: &[u8]) -> Result<(), Self::Error>;
    async fn receive(&self) -> Result<Vec<u8>, Self::Error>;
}

// 自动推断复杂的 trait 约束
impl<T> OtlpClient<T> 
where
    T: AsyncTransport + Clone,
    T::Error: Into<OtlpError>,
{
    pub async fn send_data(&self, data: &[u8]) -> Result<(), OtlpError> {
        self.transport.send(data).await.map_err(Into::into)
    }
}
```

### 类型安全保证

#### 强类型系统

```rust
use std::marker::PhantomData;

// 使用类型系统保证安全性
pub struct TelemetryData<T> {
    inner: T,
    _marker: PhantomData<T>,
}

impl TelemetryData<TraceData> {
    pub fn trace(operation: String) -> Self {
        Self {
            inner: TraceData::new(operation),
            _marker: PhantomData,
        }
    }
}

impl TelemetryData<MetricData> {
    pub fn metric(name: String, value: f64) -> Self {
        Self {
            inner: MetricData::new(name, value),
            _marker: PhantomData,
        }
    }
}
```

#### 零成本抽象

```rust
// 零成本抽象设计
pub struct BatchProcessor<T> {
    items: Vec<T>,
    max_size: usize,
}

impl<T> BatchProcessor<T> {
    pub fn new(max_size: usize) -> Self {
        Self {
            items: Vec::with_capacity(max_size),
            max_size,
        }
    }
    
    pub fn add(&mut self, item: T) -> Option<Vec<T>> {
        self.items.push(item);
        if self.items.len() >= self.max_size {
            Some(std::mem::take(&mut self.items))
        } else {
            None
        }
    }
}
```

### 零拷贝优化

#### Pointer Provenance API

```rust
use std::ptr;

// 使用 Rust 1.90 的 Pointer Provenance API
pub struct ZeroCopyBuffer {
    data: *const u8,
    len: usize,
}

impl ZeroCopyBuffer {
    pub fn from_slice(slice: &[u8]) -> Self {
        Self {
            data: slice.as_ptr(),
            len: slice.len(),
        }
    }
    
    pub fn as_slice(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(self.data, self.len)
        }
    }
}

// 零拷贝序列化
impl Serialize for TelemetryData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // 直接序列化，避免中间拷贝
        match self {
            TelemetryData::Trace(trace) => trace.serialize(serializer),
            TelemetryData::Metric(metric) => metric.serialize(serializer),
            TelemetryData::Log(log) => log.serialize(serializer),
        }
    }
}
```

### 并发安全

#### 所有权系统

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

// 利用所有权系统实现并发安全
pub struct ConcurrentClient {
    inner: Arc<RwLock<ClientInner>>,
    config: Arc<OtlpConfig>,
}

impl ConcurrentClient {
    pub async fn send_concurrent(&self, data: Vec<TelemetryData>) -> Result<(), OtlpError> {
        let tasks: Vec<_> = data.into_iter().map(|item| {
            let client = Arc::clone(&self.inner);
            tokio::spawn(async move {
                let guard = client.read().await;
                guard.send_single(item).await
            })
        }).collect();
        
        // 等待所有任务完成
        for task in tasks {
            task.await??;
        }
        
        Ok(())
    }
}
```

### MSRV 感知

#### 版本兼容性

```rust
// 使用 Cargo 1.90 的 MSRV 感知解析器
#[cfg(feature = "rust_1_90")]
mod rust_1_90_features {
    use std::future::Future;
    
    // Rust 1.90 特有功能
    pub async fn advanced_async_processing() {
        // 使用最新的异步特性
    }
}

#[cfg(not(feature = "rust_1_90"))]
mod fallback {
    // 向后兼容的实现
    pub async fn basic_async_processing() {
        // 基础异步实现
    }
}
```

## ⚡ 异步编程模式

### Tokio 运行时

#### 运行时配置

```rust
use tokio::runtime::{Runtime, Builder};

// 优化的 Tokio 运行时配置
pub fn create_optimized_runtime() -> Result<Runtime, std::io::Error> {
    Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_name("otlp-worker")
        .thread_stack_size(3 * 1024 * 1024) // 3MB stack
        .enable_all()
        .build()
}

// 异步任务管理
pub struct AsyncTaskManager {
    runtime: Runtime,
    tasks: Vec<tokio::task::JoinHandle<()>>,
}

impl AsyncTaskManager {
    pub fn new() -> Result<Self, std::io::Error> {
        Ok(Self {
            runtime: create_optimized_runtime()?,
            tasks: Vec::new(),
        })
    }
    
    pub fn spawn_task<F>(&mut self, future: F)
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let handle = self.runtime.spawn(future);
        self.tasks.push(handle);
    }
}
```

### Future 组合

#### 组合器模式

```rust
use std::future::Future;
use std::pin::Pin;

// Future 组合器
pub struct RetryFuture<F> {
    future: F,
    max_retries: u32,
    current_retry: u32,
    delay: Duration,
}

impl<F, T, E> Future for RetryFuture<F>
where
    F: Future<Output = Result<T, E>> + Unpin,
    E: std::error::Error,
{
    type Output = Result<T, E>;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        loop {
            match Pin::new(&mut self.future).poll(cx) {
                Poll::Ready(Ok(result)) => return Poll::Ready(Ok(result)),
                Poll::Ready(Err(e)) => {
                    if self.current_retry >= self.max_retries {
                        return Poll::Ready(Err(e));
                    }
                    self.current_retry += 1;
                    // 实现指数退避
                    tokio::time::sleep(self.delay * self.current_retry).await;
                }
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}
```

### 异步流处理

#### 流式数据处理

```rust
use tokio_stream::{Stream, StreamExt};
use futures::stream;

// 异步流处理
pub struct AsyncDataProcessor {
    batch_size: usize,
    timeout: Duration,
}

impl AsyncDataProcessor {
    pub async fn process_stream<S, T>(
        &self,
        mut stream: S,
        processor: impl Fn(Vec<T>) -> Pin<Box<dyn Future<Output = Result<(), OtlpError>> + Send>>,
    ) -> Result<(), OtlpError>
    where
        S: Stream<Item = T> + Unpin,
        T: Send + 'static,
    {
        let mut batch = Vec::with_capacity(self.batch_size);
        let mut timeout_future = tokio::time::sleep(self.timeout);
        
        loop {
            tokio::select! {
                item = stream.next() => {
                    match item {
                        Some(data) => {
                            batch.push(data);
                            if batch.len() >= self.batch_size {
                                processor(batch).await?;
                                batch = Vec::with_capacity(self.batch_size);
                                timeout_future = tokio::time::sleep(self.timeout);
                            }
                        }
                        None => break,
                    }
                }
                _ = &mut timeout_future => {
                    if !batch.is_empty() {
                        processor(batch).await?;
                        batch = Vec::with_capacity(self.batch_size);
                    }
                    timeout_future = tokio::time::sleep(self.timeout);
                }
            }
        }
        
        // 处理剩余数据
        if !batch.is_empty() {
            processor(batch).await?;
        }
        
        Ok(())
    }
}
```

### 并发控制

#### 信号量控制

```rust
use tokio::sync::Semaphore;

// 并发控制
pub struct ConcurrencyController {
    semaphore: Semaphore,
    max_concurrent: usize,
}

impl ConcurrencyController {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Semaphore::new(max_concurrent),
            max_concurrent,
        }
    }
    
    pub async fn execute<F, T>(&self, future: F) -> Result<T, OtlpError>
    where
        F: Future<Output = Result<T, OtlpError>>,
    {
        let _permit = self.semaphore.acquire().await
            .map_err(|_| OtlpError::ConcurrencyLimit)?;
        
        future.await
    }
}
```

## ❌ 错误处理模式

### 错误类型设计

#### 分层错误类型

```rust
use thiserror::Error;

// 分层错误类型设计
#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    #[error("gRPC error: {0}")]
    Grpc(#[from] tonic::Status),
    
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    #[error("Configuration error: {0}")]
    Config(#[from] ConfigError),
    
    #[error("Authentication error: {0}")]
    Auth(String),
    
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    #[error("Batch processing error: {0}")]
    Batch(String),
    
    #[error("Concurrency limit exceeded")]
    ConcurrencyLimit,
    
    #[error("Custom error: {0}")]
    Custom(String),
}

// 错误上下文
impl OtlpError {
    pub fn with_context<C>(self, context: C) -> ContextualError<C>
    where
        C: std::fmt::Display + Send + Sync + 'static,
    {
        ContextualError {
            error: self,
            context: Some(Box::new(context)),
        }
    }
}
```

### 错误传播

#### 错误链

```rust
use std::error::Error;

// 错误链处理
pub struct ErrorChain {
    errors: Vec<Box<dyn Error + Send + Sync>>,
}

impl ErrorChain {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
        }
    }
    
    pub fn add_error<E>(&mut self, error: E)
    where
        E: Error + Send + Sync + 'static,
    {
        self.errors.push(Box::new(error));
    }
    
    pub fn root_cause(&self) -> Option<&dyn Error> {
        self.errors.first().map(|e| e.as_ref())
    }
    
    pub fn all_causes(&self) -> impl Iterator<Item = &dyn Error> {
        self.errors.iter().map(|e| e.as_ref())
    }
}
```

### 错误恢复

#### 重试策略

```rust
use std::time::Duration;

// 智能重试策略
pub struct RetryStrategy {
    max_retries: u32,
    base_delay: Duration,
    max_delay: Duration,
    backoff_multiplier: f64,
    jitter: bool,
}

impl RetryStrategy {
    pub fn new() -> Self {
        Self {
            max_retries: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
            jitter: true,
        }
    }
    
    pub async fn execute<F, T>(&self, mut operation: F) -> Result<T, OtlpError>
    where
        F: FnMut() -> Pin<Box<dyn Future<Output = Result<T, OtlpError>> + Send>>,
    {
        let mut last_error = None;
        
        for attempt in 0..=self.max_retries {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.max_retries {
                        let delay = self.calculate_delay(attempt);
                        tokio::time::sleep(delay).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap_or_else(|| OtlpError::Custom("Unknown error".to_string())))
    }
    
    fn calculate_delay(&self, attempt: u32) -> Duration {
        let delay = self.base_delay.as_millis() as f64 * 
                   self.backoff_multiplier.powi(attempt as i32);
        let delay = delay.min(self.max_delay.as_millis() as f64) as u64;
        
        if self.jitter {
            let jitter = fastrand::u64(0..delay / 4);
            Duration::from_millis(delay + jitter)
        } else {
            Duration::from_millis(delay)
        }
    }
}
```

### 错误监控

#### 错误指标

```rust
use std::sync::atomic::{AtomicU64, Ordering};

// 错误监控
pub struct ErrorMonitor {
    total_errors: AtomicU64,
    error_counts: std::sync::Mutex<std::collections::HashMap<String, u64>>,
}

impl ErrorMonitor {
    pub fn new() -> Self {
        Self {
            total_errors: AtomicU64::new(0),
            error_counts: std::sync::Mutex::new(std::collections::HashMap::new()),
        }
    }
    
    pub fn record_error(&self, error: &OtlpError) {
        self.total_errors.fetch_add(1, Ordering::Relaxed);
        
        let error_type = match error {
            OtlpError::Network(_) => "network",
            OtlpError::Grpc(_) => "grpc",
            OtlpError::Serialization(_) => "serialization",
            OtlpError::Config(_) => "config",
            OtlpError::Auth(_) => "auth",
            OtlpError::Timeout(_) => "timeout",
            OtlpError::Batch(_) => "batch",
            OtlpError::ConcurrencyLimit => "concurrency",
            OtlpError::Custom(_) => "custom",
        };
        
        let mut counts = self.error_counts.lock().unwrap();
        *counts.entry(error_type.to_string()).or_insert(0) += 1;
    }
    
    pub fn get_error_stats(&self) -> ErrorStats {
        let total = self.total_errors.load(Ordering::Relaxed);
        let counts = self.error_counts.lock().unwrap().clone();
        
        ErrorStats { total, counts }
    }
}
```

## 🧪 测试策略

### 单元测试

#### 模块测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    
    #[tokio::test]
    async fn test_client_creation() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317");
        
        let client = OtlpClient::new(config).await;
        assert!(client.is_ok());
    }
    
    #[tokio::test]
    async fn test_trace_sending() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317");
        
        let client = OtlpClient::new(config).await.unwrap();
        let result = client.send_trace("test-operation").await;
        assert!(result.is_ok());
    }
    
    #[test]
    fn test_config_validation() {
        let config = OtlpConfig::default()
            .with_endpoint("invalid-url");
        
        assert!(config.validate().is_err());
    }
}
```

### 集成测试

#### 端到端测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use tokio_test;
    
    #[tokio::test]
    async fn test_end_to_end_flow() {
        // 启动测试服务器
        let server = start_test_server().await;
        
        // 创建客户端
        let config = OtlpConfig::default()
            .with_endpoint(&server.url());
        
        let client = OtlpClient::new(config).await.unwrap();
        
        // 发送测试数据
        let trace_data = TelemetryData::trace("integration-test");
        let result = client.send_trace_data(trace_data).await;
        
        assert!(result.is_ok());
        
        // 验证服务器接收到数据
        assert!(server.received_data().await);
        
        // 清理
        server.shutdown().await;
    }
}
```

### 性能测试

#### 基准测试

```rust
#[cfg(test)]
mod bench_tests {
    use super::*;
    use criterion::{black_box, criterion_group, criterion_main, Criterion};
    
    fn bench_client_creation(c: &mut Criterion) {
        c.bench_function("client_creation", |b| {
            b.to_async(tokio::runtime::Runtime::new().unwrap())
                .iter(|| async {
                    let config = OtlpConfig::default();
                    OtlpClient::new(config).await
                });
        });
    }
    
    fn bench_data_serialization(c: &mut Criterion) {
        let data = TelemetryData::trace("benchmark-operation");
        
        c.bench_function("data_serialization", |b| {
            b.iter(|| {
                serde_json::to_string(black_box(&data))
            });
        });
    }
    
    criterion_group!(benches, bench_client_creation, bench_data_serialization);
    criterion_main!(benches);
}
```

### 模糊测试

#### 输入验证

```rust
#[cfg(test)]
mod fuzz_tests {
    use super::*;
    
    #[test]
    fn fuzz_config_parsing() {
        // 使用 quickcheck 进行属性测试
        use quickcheck::quickcheck;
        
        fn prop_config_roundtrip(config: OtlpConfig) -> bool {
            let serialized = serde_json::to_string(&config).unwrap();
            let deserialized: OtlpConfig = serde_json::from_str(&serialized).unwrap();
            config == deserialized
        }
        
        quickcheck(prop_config_roundtrip as fn(OtlpConfig) -> bool);
    }
}
```

## ⚡ 性能优化

### 内存优化

#### 内存池

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

// 内存池实现
pub struct MemoryPool {
    pools: Arc<Mutex<Vec<Vec<u8>>>>,
    pool_size: usize,
    buffer_size: usize,
}

impl MemoryPool {
    pub fn new(pool_size: usize, buffer_size: usize) -> Self {
        let mut pools = Vec::with_capacity(pool_size);
        for _ in 0..pool_size {
            pools.push(Vec::with_capacity(buffer_size));
        }
        
        Self {
            pools: Arc::new(Mutex::new(pools)),
            pool_size,
            buffer_size,
        }
    }
    
    pub async fn get_buffer(&self) -> Option<PooledBuffer> {
        let mut pools = self.pools.lock().await;
        pools.pop().map(|mut buffer| {
            buffer.clear();
            PooledBuffer {
                buffer,
                pool: Arc::clone(&self.pools),
            }
        })
    }
}

pub struct PooledBuffer {
    buffer: Vec<u8>,
    pool: Arc<Mutex<Vec<Vec<u8>>>>,
}

impl Drop for PooledBuffer {
    fn drop(&mut self) {
        let pool = Arc::clone(&self.pool);
        let buffer = std::mem::take(&mut self.buffer);
        tokio::spawn(async move {
            let mut pools = pool.lock().await;
            pools.push(buffer);
        });
    }
}
```

### CPU 优化

#### SIMD 优化

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

// SIMD 优化的数据处理
pub struct SimdProcessor;

impl SimdProcessor {
    #[cfg(target_arch = "x86_64")]
    pub unsafe fn process_batch_simd(data: &[f64]) -> Vec<f64> {
        let mut result = Vec::with_capacity(data.len());
        let chunks = data.chunks_exact(4);
        let remainder = chunks.remainder();
        
        for chunk in chunks {
            let a = _mm256_loadu_pd(chunk.as_ptr());
            let b = _mm256_set1_pd(2.0);
            let c = _mm256_mul_pd(a, b);
            
            let mut output = [0.0; 4];
            _mm256_storeu_pd(output.as_mut_ptr(), c);
            result.extend_from_slice(&output);
        }
        
        // 处理剩余元素
        for &value in remainder {
            result.push(value * 2.0);
        }
        
        result
    }
    
    #[cfg(not(target_arch = "x86_64"))]
    pub fn process_batch_simd(data: &[f64]) -> Vec<f64> {
        data.iter().map(|&x| x * 2.0).collect()
    }
}
```

### I/O 优化

#### 异步 I/O

```rust
use tokio::io::{AsyncRead, AsyncWrite};
use tokio::net::TcpStream;

// 异步 I/O 优化
pub struct AsyncIoProcessor {
    buffer_size: usize,
}

impl AsyncIoProcessor {
    pub fn new(buffer_size: usize) -> Self {
        Self { buffer_size }
    }
    
    pub async fn process_stream<R, W>(
        &self,
        mut reader: R,
        mut writer: W,
    ) -> Result<(), std::io::Error>
    where
        R: AsyncRead + Unpin,
        W: AsyncWrite + Unpin,
    {
        let mut buffer = vec![0u8; self.buffer_size];
        
        loop {
            let bytes_read = reader.read(&mut buffer).await?;
            if bytes_read == 0 {
                break;
            }
            
            writer.write_all(&buffer[..bytes_read]).await?;
        }
        
        writer.flush().await?;
        Ok(())
    }
}
```

### 网络优化

#### 连接复用

```rust
use std::collections::HashMap;
use tokio::sync::RwLock;

// 连接池优化
pub struct ConnectionPool<T> {
    connections: Arc<RwLock<HashMap<String, Vec<T>>>>,
    max_connections_per_host: usize,
}

impl<T> ConnectionPool<T> {
    pub fn new(max_connections_per_host: usize) -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
            max_connections_per_host,
        }
    }
    
    pub async fn get_connection(&self, host: &str) -> Option<PooledConnection<T>> {
        let mut connections = self.connections.write().await;
        let host_connections = connections.entry(host.to_string()).or_insert_with(Vec::new);
        
        host_connections.pop().map(|conn| PooledConnection {
            connection: conn,
            host: host.to_string(),
            pool: Arc::clone(&self.connections),
        })
    }
    
    pub async fn return_connection(&self, host: &str, connection: T) {
        let mut connections = self.connections.write().await;
        let host_connections = connections.entry(host.to_string()).or_insert_with(Vec::new);
        
        if host_connections.len() < self.max_connections_per_host {
            host_connections.push(connection);
        }
    }
}
```

## 🔗 相关文档

- [快速开始指南](../01_GETTING_STARTED/README.md)
- [API 参考文档](../03_API_REFERENCE/README.md)
- [架构设计文档](../04_ARCHITECTURE/README.md)
- [部署运维指南](../06_DEPLOYMENT/README.md)
- [集成指南](../07_INTEGRATION/README.md)

---

**实现指南版本**: 1.0.0  
**最后更新**: 2025年1月  
**维护者**: OTLP Rust 实现团队
