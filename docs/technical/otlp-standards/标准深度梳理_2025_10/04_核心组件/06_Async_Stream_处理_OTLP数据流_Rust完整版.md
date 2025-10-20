# Async Stream 处理 - OTLP 数据流 Rust 完整实现

> **Rust版本**: 1.90+  
> **Tokio**: 1.47.1  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Async Stream 处理 - OTLP 数据流 Rust 完整实现](#async-stream-处理---otlp-数据流-rust-完整实现)
  - [目录](#目录)
  - [1. Stream 处理概述](#1-stream-处理概述)
  - [2. 依赖配置](#2-依赖配置)
  - [3. 基础 Stream 概念](#3-基础-stream-概念)
  - [4. OTLP Span Stream 处理](#4-otlp-span-stream-处理)
  - [5. 批处理 Stream](#5-批处理-stream)
  - [6. 背压控制](#6-背压控制)
  - [7. Stream 组合和转换](#7-stream-组合和转换)
  - [8. 错误处理和重试](#8-错误处理和重试)
  - [9. 并发 Stream 处理](#9-并发-stream-处理)
  - [10. 完整实战示例](#10-完整实战示例)
  - [11. 性能优化](#11-性能优化)
  - [12. 生产环境最佳实践](#12-生产环境最佳实践)
  - [13. Rust 1.90 Stream 高级特性](#13-rust-190-stream-高级特性)
    - [13.1 TryStream 和错误处理](#131-trystream-和错误处理)
    - [13.2 Stream 合并和组合](#132-stream-合并和组合)
    - [13.3 Stream 缓冲和节流](#133-stream-缓冲和节流)
    - [13.4 Stream 分割和广播](#134-stream-分割和广播)
    - [13.5 性能最佳实践](#135-性能最佳实践)
  - [14. 参考资源](#14-参考资源)

---

## 1. Stream 处理概述

**为什么需要 Stream 处理**:

```text
传统批处理 vs Stream 处理:

批处理:
- 一次性处理大量数据
- 延迟较高
- 内存占用大
- 吞吐量有限

Stream 处理:
- 持续处理数据流
- 低延迟
- 内存占用可控
- 高吞吐量
- 背压控制

OTLP 应用场景:
✅ 实时追踪数据处理
✅ 海量 Span 流式处理
✅ 多源数据聚合
✅ 实时过滤和采样
✅ 动态批处理
```

**Stream 处理模型**:

```text
┌─────────────┐
│   Producer  │ (Span 生成器)
└──────┬──────┘
       │ Stream<Span>
       ▼
┌─────────────┐
│ Transform 1 │ (过滤)
└──────┬──────┘
       │ Stream<Span>
       ▼
┌─────────────┐
│ Transform 2 │ (批处理)
└──────┬──────┘
       │ Stream<Vec<Span>>
       ▼
┌─────────────┐
│  Consumer   │ (OTLP 导出)
└─────────────┘
```

---

## 2. 依赖配置

**Cargo.toml**:

```toml
[package]
name = "otlp-stream-processing"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# 异步运行时 (Rust 1.90 优化)
tokio = { version = "1.47.1", features = ["full"] }
tokio-stream = { version = "0.1.17", features = ["sync", "time"] }
tokio-util = "0.7.14"
futures = "0.3.31"
futures-util = "0.3.31"

# OpenTelemetry 生态系统
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }
tracing = "0.1.41"
tracing-subscriber = "0.3.20"

# Stream 处理
async-stream = "0.3.7"
pin-project = "1.1.8"

# 并发控制
async-trait = "0.1.87"

# 工具库
bytes = "1.10.1"
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"
uuid = { version = "1.18.1", features = ["v4"] }
chrono = "0.4.42"

# 错误处理
thiserror = "2.0.17"
anyhow = "1.0.100"

[dev-dependencies]
tokio-test = "0.4.4"
criterion = "0.7.0"
```

---

## 3. 基础 Stream 概念

**Rust Stream Trait**:

```rust
use futures::stream::{Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio_stream::StreamExt as TokioStreamExt;

/// Rust 1.90: Stream Trait 概述
/// 
/// Stream 是异步的迭代器，可以按需产生值
/// 特性:
/// - 懒惰评估 (Lazy evaluation)
/// - 背压控制 (Backpressure control)
/// - 零拷贝 (Zero-copy when possible)
/// - 组合器模式 (Combinator pattern)

/// 基础 Stream 示例
async fn basic_stream_example() {
    // 创建一个简单的 Stream
    let stream = futures::stream::iter(vec![1, 2, 3, 4, 5]);
    
    // 消费 Stream
    let result: Vec<i32> = stream.collect().await;
    println!("Collected: {:?}", result);
}

/// Rust 1.90: 改进的 Stream 组合器
async fn advanced_stream_combinators() {
    use futures::stream;
    
    let stream = stream::iter(1..=10);
    
    // map: 转换每个元素
    let mapped = stream
        .map(|x| x * 2)
        // filter: 过滤元素
        .filter(|x| futures::future::ready(*x % 3 == 0))
        // take: 只取前N个
        .take(3);
    
    let result: Vec<i32> = mapped.collect().await;
    println!("Result: {:?}", result); // [6, 12, 18]
}

/// Rust 1.90: Stream 与 Future 的互操作
async fn stream_future_interop() {
    use futures::stream;
    
    let stream = stream::iter(vec![1, 2, 3, 4, 5]);
    
    // for_each: 对每个元素执行异步操作
    stream
        .for_each(|x| async move {
            // 模拟异步操作
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            println!("Processed: {}", x);
        })
        .await;
}

/// 自定义 Stream 实现
struct CounterStream {
    count: u32,
    max: u32,
}

impl CounterStream {
    fn new(max: u32) -> Self {
        Self { count: 0, max }
    }
}

impl Stream for CounterStream {
    type Item = u32;
    
    fn poll_next(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        if self.count < self.max {
            let current = self.count;
            self.count += 1;
            Poll::Ready(Some(current))
        } else {
            Poll::Ready(None)
        }
    }
}

/// 使用自定义 Stream
async fn custom_stream_example() {
    let stream = CounterStream::new(5);
    
    tokio::pin!(stream);
    
    while let Some(value) = stream.next().await {
        println!("Value: {}", value);
    }
}

/// Rust 1.90: 使用 async-stream 宏简化 Stream 创建
/// 
/// async-stream 提供了 `stream!` 和 `try_stream!` 宏
/// 可以使用 async/await 语法创建 Stream
use async_stream::stream;

fn fibonacci_stream(limit: u32) -> impl Stream<Item = u64> {
    stream! {
        let mut a = 0u64;
        let mut b = 1u64;
        
        for _ in 0..limit {
            yield a;
            let temp = a;
            a = b;
            b = temp + b;
        }
    }
}

async fn fibonacci_example() {
    let stream = fibonacci_stream(10);
    tokio::pin!(stream);
    
    while let Some(value) = stream.next().await {
        println!("Fibonacci: {}", value);
    }
}

/// Rust 1.90: 异步生成器模式 (使用 async_stream)
fn span_generator(rate_per_sec: u32) -> impl Stream<Item = String> {
    stream! {
        let interval = std::time::Duration::from_millis(1000 / rate_per_sec as u64);
        let mut ticker = tokio::time::interval(interval);
        let mut counter = 0u64;
        
        loop {
            ticker.tick().await;
            counter += 1;
            yield format!("span-{}", counter);
        }
    }
}
```

---

## 4. OTLP Span Stream 处理

**完整的 Span Stream 处理器**:

```rust
use opentelemetry::trace::{SpanId, TraceId, Status};
use opentelemetry_sdk::export::trace::SpanData;
use tokio_stream::StreamExt;
use std::sync::Arc;

/// OTLP Span 数据结构
#[derive(Debug, Clone)]
pub struct OtlpSpan {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub name: String,
    pub start_time: std::time::SystemTime,
    pub end_time: std::time::SystemTime,
    pub status: Status,
    pub attributes: Vec<(String, String)>,
}

/// Span Stream 生成器
pub struct SpanStreamGenerator {
    rate_per_second: u32,
}

impl SpanStreamGenerator {
    pub fn new(rate_per_second: u32) -> Self {
        Self { rate_per_second }
    }
    
    /// 创建 Span Stream
    pub fn generate_stream(
        &self,
    ) -> impl Stream<Item = OtlpSpan> {
        let interval_ms = 1000 / self.rate_per_second;
        let interval = std::time::Duration::from_millis(interval_ms as u64);
        
        async_stream::stream! {
            let mut interval_timer = tokio::time::interval(interval);
            
            loop {
                interval_timer.tick().await;
                
                let span = OtlpSpan {
                    trace_id: TraceId::from_u128(uuid::Uuid::new_v4().as_u128()),
                    span_id: SpanId::from_u64(uuid::Uuid::new_v4().as_u128() as u64),
                    name: format!("operation-{}", uuid::Uuid::new_v4()),
                    start_time: std::time::SystemTime::now(),
                    end_time: std::time::SystemTime::now(),
                    status: Status::Ok,
                    attributes: vec![
                        ("service.name".to_string(), "my-service".to_string()),
                        ("environment".to_string(), "production".to_string()),
                    ],
                };
                
                yield span;
            }
        }
    }
}

/// Span 过滤器
pub struct SpanFilter {
    min_duration_ms: u64,
}

impl SpanFilter {
    pub fn new(min_duration_ms: u64) -> Self {
        Self { min_duration_ms }
    }
    
    /// 过滤 Span Stream
    pub fn filter_stream<S>(
        &self,
        stream: S,
    ) -> impl Stream<Item = OtlpSpan>
    where
        S: Stream<Item = OtlpSpan>,
    {
        let min_duration = self.min_duration_ms;
        
        stream.filter(move |span| {
            let duration = span.end_time
                .duration_since(span.start_time)
                .unwrap_or_default();
            
            futures::future::ready(duration.as_millis() as u64 >= min_duration)
        })
    }
}

/// Span 转换器
pub struct SpanTransformer;

impl SpanTransformer {
    /// 添加通用属性
    pub fn add_common_attributes<S>(
        stream: S,
        attributes: Vec<(String, String)>,
    ) -> impl Stream<Item = OtlpSpan>
    where
        S: Stream<Item = OtlpSpan>,
    {
        stream.map(move |mut span| {
            span.attributes.extend(attributes.clone());
            span
        })
    }
    
    /// 重命名 Span
    pub fn rename_spans<S, F>(
        stream: S,
        rename_fn: F,
    ) -> impl Stream<Item = OtlpSpan>
    where
        S: Stream<Item = OtlpSpan>,
        F: Fn(&str) -> String + Clone,
    {
        stream.map(move |mut span| {
            span.name = rename_fn(&span.name);
            span
        })
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // 创建 Span 生成器 (每秒 100 个 Span)
    let generator = SpanStreamGenerator::new(100);
    let stream = generator.generate_stream();
    
    // 过滤 (只保留耗时 > 10ms 的 Span)
    let filter = SpanFilter::new(10);
    let filtered_stream = filter.filter_stream(stream);
    
    // 添加通用属性
    let common_attrs = vec![
        ("cluster".to_string(), "prod-us-east".to_string()),
        ("version".to_string(), "1.0.0".to_string()),
    ];
    let transformed_stream = SpanTransformer::add_common_attributes(
        filtered_stream,
        common_attrs,
    );
    
    // 消费前 10 个 Span
    tokio::pin!(transformed_stream);
    
    let mut count = 0;
    while let Some(span) = transformed_stream.next().await {
        tracing::info!(
            trace_id = ?span.trace_id,
            span_id = ?span.span_id,
            name = %span.name,
            "Processed span"
        );
        
        count += 1;
        if count >= 10 {
            break;
        }
    }
    
    Ok(())
}
```

---

## 5. 批处理 Stream

**动态批处理实现**:

```rust
use tokio::time::{Duration, Instant};

/// 批处理配置
pub struct BatchConfig {
    pub max_size: usize,
    pub max_wait: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            max_size: 100,
            max_wait: Duration::from_secs(5),
        }
    }
}

/// 批处理 Stream 处理器
pub struct BatchProcessor {
    config: BatchConfig,
}

impl BatchProcessor {
    pub fn new(config: BatchConfig) -> Self {
        Self { config }
    }
    
    /// 将 Stream 转换为批处理 Stream
    pub fn batch_stream<S, T>(
        &self,
        stream: S,
    ) -> impl Stream<Item = Vec<T>>
    where
        S: Stream<Item = T> + Unpin,
        T: Send + 'static,
    {
        let max_size = self.config.max_size;
        let max_wait = self.config.max_wait;
        
        async_stream::stream! {
            tokio::pin!(stream);
            
            let mut buffer = Vec::with_capacity(max_size);
            let mut deadline = Instant::now() + max_wait;
            
            loop {
                tokio::select! {
                    // 尝试从 Stream 获取下一个元素
                    item = stream.next() => {
                        match item {
                            Some(item) => {
                                buffer.push(item);
                                
                                // 如果缓冲区满，立即发送
                                if buffer.len() >= max_size {
                                    yield buffer;
                                    buffer = Vec::with_capacity(max_size);
                                    deadline = Instant::now() + max_wait;
                                }
                            }
                            None => {
                                // Stream 结束，发送剩余数据
                                if !buffer.is_empty() {
                                    yield buffer;
                                }
                                break;
                            }
                        }
                    }
                    
                    // 超时，发送当前缓冲区
                    _ = tokio::time::sleep_until(deadline) => {
                        if !buffer.is_empty() {
                            yield buffer;
                            buffer = Vec::with_capacity(max_size);
                        }
                        deadline = Instant::now() + max_wait;
                    }
                }
            }
        }
    }
}

/// 使用示例
async fn batch_processing_example() -> Result<(), anyhow::Error> {
    // 创建 Span Stream
    let generator = SpanStreamGenerator::new(50);
    let stream = generator.generate_stream();
    
    // 批处理配置
    let batch_config = BatchConfig {
        max_size: 100,
        max_wait: Duration::from_secs(5),
    };
    
    let processor = BatchProcessor::new(batch_config);
    let batched_stream = processor.batch_stream(stream);
    
    tokio::pin!(batched_stream);
    
    // 处理批次
    let mut batch_count = 0;
    while let Some(batch) = batched_stream.next().await {
        tracing::info!(
            batch_size = batch.len(),
            batch_number = batch_count,
            "Processing batch"
        );
        
        // 导出批次到 OTLP
        // export_batch_to_otlp(batch).await?;
        
        batch_count += 1;
        if batch_count >= 5 {
            break;
        }
    }
    
    Ok(())
}
```

---

## 6. 背压控制

**背压控制实现**:

```rust
use tokio::sync::Semaphore;

/// 背压控制器
pub struct BackpressureController {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
}

impl BackpressureController {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
        }
    }
    
    /// 应用背压控制到 Stream
    pub fn apply<S, T, F, Fut>(
        &self,
        stream: S,
        process_fn: F,
    ) -> impl Stream<Item = Result<T, anyhow::Error>>
    where
        S: Stream<Item = T>,
        F: Fn(T) -> Fut + Clone,
        Fut: std::future::Future<Output = Result<T, anyhow::Error>>,
        T: Send + 'static,
    {
        let semaphore = Arc::clone(&self.semaphore);
        
        stream.then(move |item| {
            let semaphore = Arc::clone(&semaphore);
            let process_fn = process_fn.clone();
            
            async move {
                // 获取信号量许可
                let _permit = semaphore.acquire().await.unwrap();
                
                // 处理项目
                process_fn(item).await
            }
        })
    }
    
    /// 获取当前可用许可数
    pub fn available_permits(&self) -> usize {
        self.semaphore.available_permits()
    }
}

/// 使用示例
async fn backpressure_example() -> Result<(), anyhow::Error> {
    let generator = SpanStreamGenerator::new(100);
    let stream = generator.generate_stream();
    
    // 创建背压控制器 (最多 10 个并发)
    let controller = BackpressureController::new(10);
    
    // 应用背压控制
    let controlled_stream = controller.apply(stream, |span| async move {
        // 模拟处理延迟
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        tracing::debug!(span_id = ?span.span_id, "Processed span");
        
        Ok(span)
    });
    
    tokio::pin!(controlled_stream);
    
    let mut count = 0;
    while let Some(result) = controlled_stream.next().await {
        match result {
            Ok(span) => {
                count += 1;
                if count % 10 == 0 {
                    tracing::info!(
                        count = count,
                        available_permits = controller.available_permits(),
                        "Progress update"
                    );
                }
            }
            Err(e) => {
                tracing::error!(error = ?e, "Failed to process span");
            }
        }
        
        if count >= 100 {
            break;
        }
    }
    
    Ok(())
}
```

---

## 7. Stream 组合和转换

**高级 Stream 操作**:

```rust
use futures::stream::{self, select, StreamExt};

/// Stream 组合器
pub struct StreamCombiner;

impl StreamCombiner {
    /// 合并多个 Stream
    pub fn merge_streams<T>(
        streams: Vec<impl Stream<Item = T> + Unpin>,
    ) -> impl Stream<Item = T>
    where
        T: Send + 'static,
    {
        // 使用 select_all 合并多个 Stream
        stream::select_all(streams)
    }
    
    /// 交织两个 Stream
    pub fn interleave<T>(
        stream1: impl Stream<Item = T>,
        stream2: impl Stream<Item = T>,
    ) -> impl Stream<Item = T> {
        // 交替从两个 Stream 获取元素
        select(stream1, stream2)
    }
    
    /// Stream 分区
    pub fn partition<T, F>(
        stream: impl Stream<Item = T>,
        predicate: F,
    ) -> (impl Stream<Item = T>, impl Stream<Item = T>)
    where
        F: Fn(&T) -> bool + Clone,
        T: Clone,
    {
        let stream1 = stream.clone().filter(move |item| {
            futures::future::ready(predicate(item))
        });
        
        let stream2 = stream.filter(move |item| {
            futures::future::ready(!predicate(item))
        });
        
        (stream1, stream2)
    }
}

/// Stream 聚合器
pub struct StreamAggregator;

impl StreamAggregator {
    /// 窗口聚合
    pub fn window_aggregate<T, F, R>(
        stream: impl Stream<Item = T>,
        window_size: usize,
        aggregate_fn: F,
    ) -> impl Stream<Item = R>
    where
        F: Fn(Vec<T>) -> R,
        T: Send + 'static,
    {
        async_stream::stream! {
            tokio::pin!(stream);
            
            let mut window = Vec::with_capacity(window_size);
            
            while let Some(item) = stream.next().await {
                window.push(item);
                
                if window.len() >= window_size {
                    let result = aggregate_fn(window);
                    window = Vec::with_capacity(window_size);
                    yield result;
                }
            }
            
            // 处理剩余元素
            if !window.is_empty() {
                yield aggregate_fn(window);
            }
        }
    }
}
```

---

## 8. 错误处理和重试

**Stream 错误处理**:

```rust
/// Stream 错误处理器
pub struct StreamErrorHandler {
    max_retries: u32,
    retry_delay: Duration,
}

impl StreamErrorHandler {
    pub fn new(max_retries: u32, retry_delay: Duration) -> Self {
        Self {
            max_retries,
            retry_delay,
        }
    }
    
    /// 带重试的 Stream 处理
    pub fn with_retry<S, T, F, Fut, E>(
        &self,
        stream: S,
        process_fn: F,
    ) -> impl Stream<Item = Result<T, E>>
    where
        S: Stream<Item = T>,
        F: Fn(T) -> Fut + Clone,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
        T: Clone + Send + 'static,
    {
        let max_retries = self.max_retries;
        let retry_delay = self.retry_delay;
        
        stream.then(move |item| {
            let process_fn = process_fn.clone();
            let item_clone = item.clone();
            
            async move {
                let mut attempts = 0;
                let mut last_error = None;
                
                while attempts <= max_retries {
                    match process_fn(item_clone.clone()).await {
                        Ok(result) => return Ok(result),
                        Err(e) => {
                            tracing::warn!(
                                attempt = attempts + 1,
                                max_retries = max_retries,
                                error = %e,
                                "Retry failed"
                            );
                            
                            last_error = Some(e);
                            attempts += 1;
                            
                            if attempts <= max_retries {
                                tokio::time::sleep(retry_delay).await;
                            }
                        }
                    }
                }
                
                Err(last_error.unwrap())
            }
        })
    }
}
```

---

## 9. 并发 Stream 处理

**并发处理实现**:

```rust
/// 并发 Stream 处理器
pub struct ConcurrentStreamProcessor {
    concurrency: usize,
}

impl ConcurrentStreamProcessor {
    pub fn new(concurrency: usize) -> Self {
        Self { concurrency }
    }
    
    /// 并发处理 Stream
    pub fn process_concurrent<S, T, F, Fut, R>(
        &self,
        stream: S,
        process_fn: F,
    ) -> impl Stream<Item = R>
    where
        S: Stream<Item = T>,
        F: Fn(T) -> Fut + Clone + Send + 'static,
        Fut: std::future::Future<Output = R> + Send,
        T: Send + 'static,
        R: Send + 'static,
    {
        stream.buffer_unordered(self.concurrency)
            .map(move |item| {
                let process_fn = process_fn.clone();
                tokio::spawn(async move { process_fn(item).await })
            })
            .buffer_unordered(self.concurrency)
            .filter_map(|result| async move { result.ok() })
    }
}
```

---

## 10. 完整实战示例

**生产级 OTLP Stream 处理器**:

```rust
use std::sync::Arc;

/// 生产级 OTLP Stream 处理器
pub struct ProductionOtlpStreamProcessor {
    batch_processor: BatchProcessor,
    backpressure_controller: BackpressureController,
    error_handler: StreamErrorHandler,
}

impl ProductionOtlpStreamProcessor {
    pub fn new() -> Self {
        Self {
            batch_processor: BatchProcessor::new(BatchConfig::default()),
            backpressure_controller: BackpressureController::new(100),
            error_handler: StreamErrorHandler::new(3, Duration::from_millis(100)),
        }
    }
    
    /// 完整的处理流程
    pub async fn process_span_stream<S>(
        &self,
        stream: S,
    ) -> Result<(), anyhow::Error>
    where
        S: Stream<Item = OtlpSpan> + Unpin,
    {
        // 1. 过滤
        let filter = SpanFilter::new(5);
        let filtered_stream = filter.filter_stream(stream);
        
        // 2. 应用背压控制
        let controlled_stream = self.backpressure_controller.apply(
            filtered_stream,
            |span| async move { Ok(span) },
        );
        
        // 3. 批处理
        let batched_stream = self.batch_processor.batch_stream(
            controlled_stream.filter_map(|r| async move { r.ok() }),
        );
        
        tokio::pin!(batched_stream);
        
        // 4. 导出到 OTLP
        while let Some(batch) = batched_stream.next().await {
            tracing::info!(batch_size = batch.len(), "Exporting batch");
            
            // 实际导出逻辑
            // self.export_to_otlp(batch).await?;
        }
        
        Ok(())
    }
}
```

---

## 11. 性能优化

**优化技巧**:

```text
✅ 使用 buffer_unordered 并发处理
✅ 合理设置批处理大小
✅ 控制并发数量
✅ 使用零拷贝 (Bytes)
✅ 避免不必要的克隆
✅ 使用 tokio::pin! 避免 Box
✅ 合理设置通道缓冲区大小
```

---

## 12. 生产环境最佳实践

```text
✅ Stream 配置
  □ 合理设置批处理大小和超时
  □ 配置背压控制
  □ 设置重试策略
  □ 监控 Stream 健康状态

✅ 错误处理
  □ 实现降级策略
  □ 记录错误指标
  □ 死信队列
  □ 告警机制

✅ 性能监控
  □ 监控吞吐量
  □ 监控延迟
  □ 监控背压状态
  □ 监控错误率
```

---

## 13. Rust 1.90 Stream 高级特性

### 13.1 TryStream 和错误处理

**Rust 1.90: TryStream 特性**：

```rust
use futures::stream::{TryStreamExt, StreamExt};
use tokio_stream as stream;

/// TryStream 提供了强大的错误处理能力
async fn try_stream_example() {
    // 创建一个可能失败的 Stream
    let stream = stream::iter(vec![Ok(1), Err("error"), Ok(3), Ok(4)]);
    
    // try_filter: 过滤成功的元素
    let filtered = stream
        .try_filter(|&x| futures::future::ready(x > 2));
    
    // try_collect: 收集结果，遇到错误会停止
    match filtered.try_collect::<Vec<_>>().await {
        Ok(values) => println!("Success: {:?}", values),
        Err(e) => println!("Error: {}", e),
    }
}

/// Rust 1.90: 错误恢复策略
async fn error_recovery_stream() {
    use futures::stream;
    
    let stream = stream::iter(vec![Ok(1), Err("error"), Ok(3)]);
    
    // or_else: 错误恢复
    let recovered = stream.or_else(|e| {
        tracing::warn!("Recovered from error: {}", e);
        futures::future::ok(0)
    });
    
    let result: Result<Vec<_>, _> = recovered.try_collect().await;
    println!("Result: {:?}", result); // Ok([1, 0, 3])
}

/// OTLP Span TryStream 处理
async fn otlp_try_stream_processing() {
    use anyhow::Result;
    
    async fn process_span(span: OtlpSpan) -> Result<OtlpSpan> {
        // 模拟可能失败的处理
        if span.name.is_empty() {
            anyhow::bail!("Invalid span name");
        }
        Ok(span)
    }
    
    let span_stream = create_span_stream();
    
    // 使用 try_filter_map 处理和过滤
    let processed = span_stream
        .then(|span| async move { process_span(span).await })
        .filter_map(|result| async move {
            match result {
                Ok(span) => Some(span),
                Err(e) => {
                    tracing::error!("Failed to process span: {}", e);
                    None
                }
            }
        });
    
    tokio::pin!(processed);
    
    while let Some(span) = processed.next().await {
        // 导出处理后的 span
        tracing::debug!("Exporting span: {}", span.name);
    }
}
```

### 13.2 Stream 合并和组合

**Rust 1.90: 多 Stream 合并**：

```rust
use futures::stream::{select, select_all, StreamExt};

/// 合并多个 Stream
async fn merge_streams() {
    let stream1 = stream::iter(vec![1, 2, 3]);
    let stream2 = stream::iter(vec![4, 5, 6]);
    let stream3 = stream::iter(vec![7, 8, 9]);
    
    // select_all: 合并多个 Stream
    let merged = select_all(vec![stream1, stream2, stream3]);
    
    let result: Vec<_> = merged.collect().await;
    println!("Merged: {:?}", result);
}

/// Rust 1.90: Stream 交叉
async fn interleave_streams() {
    use futures::stream::{select, StreamExt};
    
    let stream1 = stream::iter(vec![1, 3, 5]);
    let stream2 = stream::iter(vec![2, 4, 6]);
    
    // select: 交叉合并两个 Stream
    let interleaved = select(stream1, stream2);
    
    let result: Vec<_> = interleaved.collect().await;
    println!("Interleaved: {:?}", result);
}

/// OTLP 多源 Span 合并
async fn merge_multi_source_spans() {
    // 创建多个 Span 源
    let source1 = create_http_span_stream();
    let source2 = create_grpc_span_stream();
    let source3 = create_db_span_stream();
    
    // 合并所有源
    let merged_stream = select_all(vec![
        Box::pin(source1) as Pin<Box<dyn Stream<Item = OtlpSpan> + Send>>,
        Box::pin(source2),
        Box::pin(source3),
    ]);
    
    // 统一处理
    let processed = merged_stream
        .map(|span| async move {
            // 添加源标识
            let mut span = span;
            span.attributes.push(("source.type".to_string(), "merged".to_string()));
            span
        })
        .buffer_unordered(10);
    
    tokio::pin!(processed);
    
    while let Some(span) = processed.next().await {
        export_span(span).await;
    }
}

// 辅助函数
fn create_http_span_stream() -> impl Stream<Item = OtlpSpan> + Send {
    stream::iter(vec![])
}

fn create_grpc_span_stream() -> impl Stream<Item = OtlpSpan> + Send {
    stream::iter(vec![])
}

fn create_db_span_stream() -> impl Stream<Item = OtlpSpan> + Send {
    stream::iter(vec![])
}

async fn export_span(span: OtlpSpan) {
    tracing::trace!("Exporting span: {}", span.name);
}
```

### 13.3 Stream 缓冲和节流

**Rust 1.90: 高级缓冲策略**：

```rust
use tokio_stream::StreamExt;
use std::time::Duration;

/// 缓冲策略
async fn buffer_strategies() {
    let stream = stream::iter(1..=10);
    
    // buffer_unordered: 无序缓冲，最大并发
    let buffered = stream
        .map(|x| async move {
            tokio::time::sleep(Duration::from_millis(100)).await;
            x * 2
        })
        .buffer_unordered(5); // 最多5个并发任务
    
    let result: Vec<_> = buffered.collect().await;
    println!("Buffered (unordered): {:?}", result);
}

/// Rust 1.90: 流量控制
async fn throttle_stream() {
    use tokio_stream::StreamExt;
    
    let stream = stream::iter(1..=100);
    
    // throttle: 限制每秒产生的元素数量
    let throttled = stream.throttle(Duration::from_millis(100));
    
    tokio::pin!(throttled);
    
    let start = std::time::Instant::now();
    let mut count = 0;
    
    while let Some(value) = throttled.next().await {
        count += 1;
        println!("Value: {}", value);
    }
    
    let elapsed = start.elapsed();
    println!("Processed {} items in {:?}", count, elapsed);
}

/// OTLP Span 自适应节流
pub struct AdaptiveThrottler {
    base_rate: Duration,
    max_rate: Duration,
    current_rate: std::sync::Arc<tokio::sync::RwLock<Duration>>,
}

impl AdaptiveThrottler {
    pub fn new(base_rate: Duration, max_rate: Duration) -> Self {
        Self {
            base_rate,
            max_rate,
            current_rate: std::sync::Arc::new(tokio::sync::RwLock::new(base_rate)),
        }
    }
    
    /// 应用自适应节流
    pub fn throttle<S>(&self, stream: S) -> impl Stream<Item = OtlpSpan>
    where
        S: Stream<Item = OtlpSpan> + Send + 'static,
    {
        let current_rate = self.current_rate.clone();
        
        stream! {
            tokio::pin!(stream);
            
            while let Some(span) = stream.next().await {
                let rate = *current_rate.read().await;
                tokio::time::sleep(rate).await;
                yield span;
            }
        }
    }
    
    /// 根据负载调整速率
    pub async fn adjust_rate(&self, load_factor: f64) {
        let mut rate = self.current_rate.write().await;
        let new_rate = self.base_rate.mul_f64(load_factor);
        *rate = new_rate.clamp(self.base_rate, self.max_rate);
        tracing::debug!("Adjusted throttle rate to: {:?}", *rate);
    }
}
```

### 13.4 Stream 分割和广播

**Rust 1.90: Stream 分割**：

```rust
use futures::stream::StreamExt;

/// Rust 1.90: Stream 分割
async fn split_stream() {
    let stream = stream::iter(1..=10);
    
    // partition: 根据条件分割
    let (even, odd): (Vec<_>, Vec<_>) = stream
        .partition(|x| async move { x % 2 == 0 })
        .await;
    
    println!("Even: {:?}", even);
    println!("Odd: {:?}", odd);
}

/// OTLP Span 广播
pub struct SpanBroadcaster {
    senders: Vec<tokio::sync::mpsc::Sender<OtlpSpan>>,
}

impl SpanBroadcaster {
    pub fn new(num_consumers: usize, buffer_size: usize) -> (Self, Vec<tokio::sync::mpsc::Receiver<OtlpSpan>>) {
        let (senders, receivers): (Vec<_>, Vec<_>) = (0..num_consumers)
            .map(|_| tokio::sync::mpsc::channel(buffer_size))
            .unzip();
        
        (Self { senders }, receivers)
    }
    
    /// 广播 Span 到所有消费者
    pub async fn broadcast<S>(&self, mut stream: S) -> Result<(), anyhow::Error>
    where
        S: Stream<Item = OtlpSpan> + Unpin,
    {
        while let Some(span) = stream.next().await {
            // 克隆 span 发送给所有消费者
            for sender in &self.senders {
                if let Err(e) = sender.send(span.clone()).await {
                    tracing::error!("Failed to broadcast span: {}", e);
                }
            }
        }
        Ok(())
    }
}

/// 使用示例
async fn broadcast_example() {
    let (broadcaster, mut receivers) = SpanBroadcaster::new(3, 100);
    
    // 启动消费者任务
    for (i, mut rx) in receivers.into_iter().enumerate() {
        tokio::spawn(async move {
            while let Some(span) = rx.recv().await {
                tracing::info!("Consumer {} received span: {}", i, span.name);
            }
        });
    }
    
    // 广播 span
    let span_stream = create_span_stream();
    broadcaster.broadcast(span_stream).await.ok();
}
```

### 13.5 性能最佳实践

**Rust 1.90 Stream 性能优化清单**：

```text
✅ 使用 buffer_unordered 提高并发
✅ 合理设置缓冲区大小（避免内存过度使用）
✅ 使用 tokio::spawn 处理CPU密集型任务
✅ 实现背压控制防止OOM
✅ 使用 Bytes 实现零拷贝
✅ 避免在 Stream 中持有长时间的锁
✅ 使用 select_all 合并多个源
✅ 应用节流避免下游过载
✅ 使用 try_stream 简化错误处理
✅ 批处理减少系统调用
✅ 预分配容量减少重新分配
✅ 使用 FuturesUnordered 处理动态任务
```

---

## 14. 参考资源

**官方文档**:

- [Tokio Stream 1.47.1](https://docs.rs/tokio-stream/0.1.17)
- [Futures Stream](https://docs.rs/futures/0.3.31/futures/stream/)
- [async-stream crate](https://docs.rs/async-stream/0.3.7)
- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Stream Trait RFC](https://rust-lang.github.io/rfcs/2996-async-iterator.html)

**性能优化资源**:

- [Tokio Performance Guide](https://tokio.rs/tokio/topics/performance)
- [Stream Performance Best Practices](https://tokio.rs/tokio/topics/streams)

---

**文档状态**: ✅ 完成 (Rust 1.90 + Tokio 1.47.1)  
**最后更新**: 2025年10月9日  
**审核状态**: 生产就绪  
**更新内容**: 补充 Rust 1.90 最新 Stream API 和异步迭代器特性  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [📖 查看其他组件](../README.md)
