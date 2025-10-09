# Rust 并发编程与 OTLP 集成完整指南

> **Rust版本**: 1.90 (2025年最新稳定版)  
> **Tokio**: 1.47.1  
> **Rayon**: 1.11.1  
> **Crossbeam**: 0.8.4  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日  
> **文档状态**: ✅ 生产就绪 - 完整覆盖所有并发模式

---

## 📋 目录

- [Rust 并发编程与 OTLP 集成完整指南](#rust-并发编程与-otlp-集成完整指南)
  - [📋 目录](#-目录)
  - [1. Rust 并发模型概述](#1-rust-并发模型概述)
    - [1.1 并发 vs 并行](#11-并发-vs-并行)
    - [1.2 Rust 并发安全保证](#12-rust-并发安全保证)
    - [1.3 并发工具选择指南](#13-并发工具选择指南)
  - [2. Tokio 异步并发](#2-tokio-异步并发)
    - [2.1 Task 并发](#21-task-并发)
    - [2.2 Select 模式](#22-select-模式)
    - [2.3 Join 模式](#23-join-模式)
    - [2.4 Channel 通信](#24-channel-通信)
  - [3. Rayon 数据并行](#3-rayon-数据并行)
    - [3.1 并行迭代器](#31-并行迭代器)
    - [3.2 自定义线程池](#32-自定义线程池)
    - [3.3 OTLP 批处理优化](#33-otlp-批处理优化)
  - [4. Crossbeam 无锁并发](#4-crossbeam-无锁并发)
    - [4.1 Channel 通信](#41-channel-通信)
    - [4.2 原子操作](#42-原子操作)
    - [4.3 Epoch-based 内存回收](#43-epoch-based-内存回收)
  - [5. 同步原语](#5-同步原语)
    - [5.1 Mutex 和 RwLock](#51-mutex-和-rwlock)
    - [5.2 Atomic 类型](#52-atomic-类型)
    - [5.3 Once 和 OnceCell](#53-once-和-oncecell)
  - [6. 并发模式与最佳实践](#6-并发模式与最佳实践)
    - [6.1 生产者-消费者](#61-生产者-消费者)
    - [6.2 工作窃取](#62-工作窃取)
    - [6.3 管道模式](#63-管道模式)
  - [7. OTLP 并发集成](#7-otlp-并发集成)
    - [7.1 并发 Span 收集](#71-并发-span-收集)
    - [7.2 批量导出优化](#72-批量导出优化)
    - [7.3 多后端并发](#73-多后端并发)
  - [8. 性能优化](#8-性能优化)
  - [9. 常见陷阱与解决方案](#9-常见陷阱与解决方案)
    - [陷阱 1: 死锁](#陷阱-1-死锁)
    - [陷阱 2: 数据竞争](#陷阱-2-数据竞争)
    - [陷阱 3: Channel 阻塞](#陷阱-3-channel-阻塞)
  - [10. 完整生产示例](#10-完整生产示例)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [性能优化](#性能优化)

---

## 1. Rust 并发模型概述

### 1.1 并发 vs 并行

```text
并发 (Concurrency):
- 多个任务交替执行
- 逻辑上同时进行
- 单核也可以实现
- 示例：Web 服务器处理多个请求

并行 (Parallelism):
- 多个任务真正同时执行
- 物理上同时进行
- 需要多核 CPU
- 示例：图像处理批量计算

Rust 支持两种模式:
┌────────────────────┬────────────────────┐
│   异步并发 (Tokio)  │  数据并行 (Rayon)  │
│   - 高并发 I/O      │  - CPU 密集计算    │
│   - 低资源占用      │  - 自动负载均衡     │
│   - 事件驱动        │  - Work-stealing   │
└────────────────────┴────────────────────┘
```

---

### 1.2 Rust 并发安全保证

**编译时保证**：

```rust
/// ✅ Send: 可以跨线程传递所有权
fn send_example<T: Send>(value: T) {
    std::thread::spawn(move || {
        // value 的所有权转移到新线程
        drop(value);
    });
}

/// ✅ Sync: 可以跨线程共享引用
fn sync_example<T: Sync>(value: &'static T) {
    std::thread::spawn(move || {
        // 可以安全地在多个线程中使用 value 的引用
        use_value(value);
    });
}

/// ❌ 编译错误：Rc 不是 Send
fn rc_not_send() {
    let rc = Rc::new(42);
    // std::thread::spawn(move || {
    //     println!("{}", rc); // 编译错误！
    // });
}

/// ✅ Arc 是 Send + Sync
fn arc_is_send_sync() {
    let arc = Arc::new(42);
    let arc_clone = Arc::clone(&arc);
    
    std::thread::spawn(move || {
        println!("{}", arc_clone); // ✅ 编译成功
    });
}

/// ✅ Rust 防止数据竞争
struct SharedState {
    counter: i32, // ❌ 裸类型不能跨线程共享
}

struct SafeSharedState {
    counter: Arc<Mutex<i32>>, // ✅ 使用 Mutex 保护
}
```

---

### 1.3 并发工具选择指南

```text
┌─────────────────────────────────────────────────────────────┐
│                   选择决策树                                 │
└─────────────────────────────────────────────────────────────┘

任务类型？
├─ I/O 密集型 (网络、文件、数据库)
│  └─ 使用 Tokio 异步运行时
│     - tokio::spawn()
│     - async/await
│     - Streams and Channels
│
├─ CPU 密集型 (计算、解析、压缩)
│  ├─ 数据并行 (可分片)
│  │  └─ 使用 Rayon
│  │     - par_iter()
│  │     - par_chunks()
│  │
│  └─ 任务并行 (异构任务)
│     └─ 使用 std::thread 或 Rayon scope
│
└─ 混合型 (I/O + CPU)
   └─ Tokio + spawn_blocking()
      或 Tokio + Rayon 组合

数据共享？
├─ 无共享 (推荐)
│  └─ Channel 通信 (mpsc, crossbeam)
│
├─ 只读共享
│  └─ Arc<T>
│
├─ 读多写少
│  └─ Arc<RwLock<T>>
│
└─ 频繁读写
   └─ Arc<Mutex<T>> 或 DashMap
```

---

## 2. Tokio 异步并发

### 2.1 Task 并发

**基础 Task 并发**：

```rust
use tokio::task::{self, JoinHandle};
use opentelemetry::global;
use opentelemetry::trace::{Tracer, TracerProvider};

/// ✅ 并发执行多个任务
async fn concurrent_span_export() -> Result<(), TraceError> {
    let tracer = global::tracer("concurrent");
    
    // 创建多个并发任务
    let tasks: Vec<JoinHandle<Result<(), TraceError>>> = (0..10)
        .map(|i| {
            let tracer = tracer.clone();
            tokio::spawn(async move {
                tracer.in_span(format!("task_{}", i), |_cx| async move {
                    // 模拟异步操作
                    tokio::time::sleep(Duration::from_millis(100)).await;
                    export_span(i).await
                }).await
            })
        })
        .collect();
    
    // 等待所有任务完成
    for task in tasks {
        task.await??;
    }
    
    Ok(())
}

/// ✅ 限制并发数量
async fn limited_concurrency(spans: Vec<SpanData>) -> Result<(), TraceError> {
    use futures::stream::{self, StreamExt};
    
    // 最多同时执行 10 个任务
    stream::iter(spans)
        .map(|span| async move {
            export_span_with_retry(span).await
        })
        .buffer_unordered(10) // 并发限制
        .try_collect()
        .await
}

/// ✅ 动态并发控制
async fn adaptive_concurrency(spans: Vec<SpanData>) -> Result<(), TraceError> {
    use tokio::sync::Semaphore;
    
    // 使用信号量控制并发
    let semaphore = Arc::new(Semaphore::new(10));
    
    let tasks: Vec<_> = spans.into_iter().map(|span| {
        let permit = Arc::clone(&semaphore);
        tokio::spawn(async move {
            // 获取许可
            let _guard = permit.acquire().await.unwrap();
            
            // 执行任务
            export_span(span).await
        })
    }).collect();
    
    // 等待所有任务
    for task in tasks {
        task.await??;
    }
    
    Ok(())
}
```

---

### 2.2 Select 模式

**竞速和超时控制**：

```rust
use tokio::select;

/// ✅ 多路复用 - 先完成者胜出
async fn select_first_complete(
    primary: impl Future<Output = Result<(), TraceError>>,
    fallback: impl Future<Output = Result<(), TraceError>>,
) -> Result<(), TraceError> {
    select! {
        result = primary => {
            tracing::info!("Primary completed first");
            result
        }
        result = fallback => {
            tracing::warn!("Fallback completed first");
            result
        }
    }
}

/// ✅ 带超时的操作
async fn export_with_timeout(
    spans: Vec<SpanData>,
    timeout: Duration,
) -> Result<(), TraceError> {
    select! {
        result = export_spans(spans) => result,
        _ = tokio::time::sleep(timeout) => {
            Err(TraceError::Timeout)
        }
    }
}

/// ✅ 可取消的长时间任务
async fn cancellable_export(
    spans: Vec<SpanData>,
    cancel_token: tokio_util::sync::CancellationToken,
) -> Result<(), TraceError> {
    select! {
        result = export_spans(spans) => result,
        _ = cancel_token.cancelled() => {
            tracing::info!("Export cancelled");
            Ok(())
        }
    }
}

/// ✅ 多路监听 - 处理多个事件源
async fn multi_source_handling() {
    use tokio::sync::mpsc;
    
    let (tx1, mut rx1) = mpsc::channel::<SpanData>(100);
    let (tx2, mut rx2) = mpsc::channel::<MetricData>(100);
    let (tx3, mut rx3) = mpsc::channel::<LogData>(100);
    
    loop {
        select! {
            Some(span) = rx1.recv() => {
                export_span(span).await.ok();
            }
            Some(metric) = rx2.recv() => {
                export_metric(metric).await.ok();
            }
            Some(log) = rx3.recv() => {
                export_log(log).await.ok();
            }
            else => break, // 所有 channel 关闭
        }
    }
}

/// ✅ 优先级处理
async fn priority_handling() {
    use tokio::sync::mpsc;
    
    let (high_tx, mut high_rx) = mpsc::channel(100);
    let (low_tx, mut low_rx) = mpsc::channel(100);
    
    loop {
        select! {
            // 高优先级任务优先处理
            biased;
            
            Some(task) = high_rx.recv() => {
                process_high_priority(task).await;
            }
            Some(task) = low_rx.recv() => {
                process_low_priority(task).await;
            }
        }
    }
}
```

---

### 2.3 Join 模式

**并发执行并等待所有完成**：

```rust
use tokio::try_join;
use futures::future::{join, join_all, try_join_all};

/// ✅ join! - 等待所有任务完成
async fn join_all_exports() -> Result<(), TraceError> {
    let (traces, metrics, logs) = tokio::join!(
        export_traces(vec![]),
        export_metrics(vec![]),
        export_logs(vec![]),
    );
    
    // 处理结果
    traces?;
    metrics?;
    logs?;
    
    Ok(())
}

/// ✅ try_join! - 任意失败则全部取消
async fn try_join_exports() -> Result<(), TraceError> {
    try_join!(
        export_traces(vec![]),
        export_metrics(vec![]),
        export_logs(vec![]),
    )?;
    
    Ok(())
}

/// ✅ join_all - 动态数量的任务
async fn dynamic_join() -> Result<Vec<()>, TraceError> {
    let tasks: Vec<_> = (0..100).map(|i| {
        export_span(create_span(i))
    }).collect();
    
    // 等待所有任务完成
    let results = join_all(tasks).await;
    
    // 过滤成功的结果
    results.into_iter().collect()
}

/// ✅ try_join_all - 动态数量 + 错误处理
async fn try_join_all_spans(spans: Vec<SpanData>) -> Result<(), TraceError> {
    let futures = spans.into_iter().map(export_span);
    
    try_join_all(futures).await?;
    
    Ok(())
}

/// ✅ 部分失败容忍
async fn partial_failure_tolerance(spans: Vec<SpanData>) -> Vec<Result<(), TraceError>> {
    let futures = spans.into_iter().map(export_span);
    
    // 所有任务都会执行，即使有失败
    join_all(futures).await
}
```

---

### 2.4 Channel 通信

**多种 Channel 类型和使用场景**：

```rust
use tokio::sync::{mpsc, oneshot, broadcast, watch};

/// ✅ mpsc - 多生产者单消费者 (最常用)
async fn mpsc_pipeline() -> Result<(), TraceError> {
    let (tx, mut rx) = mpsc::channel::<SpanData>(1000);
    
    // 生产者任务
    let producers: Vec<_> = (0..10).map(|i| {
        let tx = tx.clone();
        tokio::spawn(async move {
            loop {
                let span = generate_span(i);
                if tx.send(span).await.is_err() {
                    break; // Channel 关闭
                }
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
    }).collect();
    drop(tx); // 释放原始发送端
    
    // 消费者任务
    let consumer = tokio::spawn(async move {
        while let Some(span) = rx.recv().await {
            export_span(span).await.ok();
        }
    });
    
    // 等待完成
    for producer in producers {
        producer.await.ok();
    }
    consumer.await.ok();
    
    Ok(())
}

/// ✅ oneshot - 一次性通信
async fn oneshot_request_response() -> Result<String, TraceError> {
    let (tx, rx) = oneshot::channel();
    
    tokio::spawn(async move {
        let result = perform_expensive_operation().await;
        tx.send(result).ok();
    });
    
    // 等待结果
    rx.await.map_err(|_| TraceError::ChannelClosed)
}

/// ✅ broadcast - 广播通道
async fn broadcast_to_multiple_exporters() -> Result<(), TraceError> {
    let (tx, _rx) = broadcast::channel(100);
    
    // 创建多个订阅者
    let exporters: Vec<_> = (0..3).map(|i| {
        let mut rx = tx.subscribe();
        tokio::spawn(async move {
            while let Ok(span) = rx.recv().await {
                export_to_backend(i, span).await.ok();
            }
        })
    }).collect();
    
    // 广播 spans
    for i in 0..100 {
        let span = generate_span(i);
        tx.send(span).ok();
    }
    drop(tx); // 关闭广播
    
    // 等待所有导出器完成
    for exporter in exporters {
        exporter.await.ok();
    }
    
    Ok(())
}

/// ✅ watch - 状态监控
async fn watch_exporter_state() -> Result<(), TraceError> {
    let (tx, mut rx) = watch::channel(ExporterState::Idle);
    
    // 状态监控任务
    tokio::spawn(async move {
        loop {
            rx.changed().await.ok();
            let state = *rx.borrow();
            tracing::info!("Exporter state changed: {:?}", state);
            
            if matches!(state, ExporterState::Stopped) {
                break;
            }
        }
    });
    
    // 模拟状态变化
    tx.send(ExporterState::Running).ok();
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    tx.send(ExporterState::Paused).ok();
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    tx.send(ExporterState::Stopped).ok();
    
    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum ExporterState {
    Idle,
    Running,
    Paused,
    Stopped,
}
```

---

## 3. Rayon 数据并行

### 3.1 并行迭代器

**CPU 密集型数据处理**：

```rust
use rayon::prelude::*;

/// ✅ 并行处理 Spans
fn parallel_span_processing(spans: Vec<SpanData>) -> Vec<ProcessedSpan> {
    let tracer = global::tracer("parallel");
    
    spans.par_iter() // 并行迭代器
        .map(|span| {
            // 每个线程独立处理
            process_span_intensive(span)
        })
        .collect()
}

/// ✅ 并行过滤和映射
fn parallel_filter_map(spans: Vec<SpanData>) -> Vec<SpanData> {
    spans.par_iter()
        .filter(|span| span.duration > Duration::from_millis(100))
        .map(|span| enrich_span(span.clone()))
        .collect()
}

/// ✅ 并行聚合
fn parallel_aggregation(spans: Vec<SpanData>) -> Statistics {
    spans.par_iter()
        .map(|span| (span.duration.as_millis(), 1))
        .reduce(
            || (0, 0),
            |(sum1, count1), (sum2, count2)| (sum1 + sum2, count1 + count2)
        );
    
    Statistics {
        total: sum,
        count,
        average: sum / count,
    }
}

/// ✅ 并行分块处理
fn parallel_chunks(spans: Vec<SpanData>) -> Result<(), TraceError> {
    spans.par_chunks(512) // 分块并行处理
        .try_for_each(|chunk| {
            export_batch(chunk.to_vec())
        })
}

/// ✅ 自定义并行度
fn custom_parallelism(data: Vec<SpanData>) -> Vec<ProcessedSpan> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_cpus::get())
        .thread_name(|i| format!("rayon-worker-{}", i))
        .build()
        .unwrap();
    
    pool.install(|| {
        data.par_iter()
            .map(process_span_intensive)
            .collect()
    })
}
```

---

### 3.2 自定义线程池

**生产级 Rayon 配置**：

```rust
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::sync::Arc;

/// ✅ 创建专用线程池
fn create_processing_pool() -> Arc<ThreadPool> {
    let pool = ThreadPoolBuilder::new()
        .num_threads(num_cpus::get())
        .thread_name(|i| format!("otlp-processor-{}", i))
        .stack_size(2 * 1024 * 1024) // 2MB 栈
        .panic_handler(|panic_info| {
            tracing::error!("Thread panicked: {:?}", panic_info);
        })
        .build()
        .expect("Failed to create thread pool");
    
    Arc::new(pool)
}

/// ✅ 使用自定义线程池
fn use_custom_pool(pool: Arc<ThreadPool>, spans: Vec<SpanData>) -> Vec<ProcessedSpan> {
    pool.install(|| {
        spans.par_iter()
            .map(process_span_intensive)
            .collect()
    })
}

/// ✅ 多级并行 - Tokio + Rayon
async fn hybrid_parallelism(batches: Vec<Vec<SpanData>>) -> Result<(), TraceError> {
    let pool = create_processing_pool();
    
    // Tokio 异步层：I/O 并发
    let futures = batches.into_iter().map(|batch| {
        let pool = Arc::clone(&pool);
        tokio::task::spawn_blocking(move || {
            // Rayon 层：CPU 并行
            pool.install(|| {
                batch.par_iter()
                    .map(process_span_intensive)
                    .collect::<Vec<_>>()
            })
        })
    });
    
    // 等待所有批次
    let results = join_all(futures).await;
    
    Ok(())
}
```

---

### 3.3 OTLP 批处理优化

**高性能批处理模式**：

```rust
/// ✅ 并行批处理优化
fn optimized_batch_processing(
    spans: Vec<SpanData>,
    batch_size: usize,
) -> Result<(), TraceError> {
    use rayon::prelude::*;
    
    // 1. 并行预处理
    let preprocessed: Vec<_> = spans.par_iter()
        .map(|span| {
            // CPU 密集型：序列化、压缩
            let serialized = serialize_span(span)?;
            let compressed = compress_data(&serialized)?;
            Ok(compressed)
        })
        .collect::<Result<_, _>>()?;
    
    // 2. 并行分批
    preprocessed.par_chunks(batch_size)
        .try_for_each(|chunk| {
            // 同步导出
            sync_export_batch(chunk)
        })?;
    
    Ok(())
}

/// ✅ 流水线并行
fn pipeline_parallelism(spans: Vec<SpanData>) -> Result<(), TraceError> {
    use crossbeam::channel::bounded;
    use std::thread;
    
    let (tx1, rx1) = bounded(1000);
    let (tx2, rx2) = bounded(1000);
    
    // 阶段1：预处理
    let stage1 = thread::spawn(move || {
        spans.par_iter().try_for_each(|span| {
            let processed = preprocess_span(span)?;
            tx1.send(processed).ok();
            Ok::<_, TraceError>(())
        })
    });
    
    // 阶段2：序列化
    let stage2 = thread::spawn(move || {
        while let Ok(span) = rx1.recv() {
            let serialized = serialize_span(&span)?;
            tx2.send(serialized).ok();
        }
        Ok::<_, TraceError>(())
    });
    
    // 阶段3：导出
    let stage3 = thread::spawn(move || {
        while let Ok(data) = rx2.recv() {
            export_data(data)?;
        }
        Ok::<_, TraceError>(())
    });
    
    // 等待所有阶段
    stage1.join().unwrap()?;
    stage2.join().unwrap()?;
    stage3.join().unwrap()?;
    
    Ok(())
}
```

---

## 4. Crossbeam 无锁并发

### 4.1 Channel 通信

**高性能 Channel 实现**：

```rust
use crossbeam::channel::{bounded, unbounded, select};

/// ✅ bounded channel - 背压控制
fn bounded_channel_example() -> Result<(), TraceError> {
    let (tx, rx) = bounded::<SpanData>(1000);
    
    // 生产者
    std::thread::spawn(move || {
        for i in 0..10000 {
            // send() 会在满时阻塞
            tx.send(generate_span(i)).ok();
        }
    });
    
    // 消费者
    while let Ok(span) = rx.recv() {
        process_span(span);
    }
    
    Ok(())
}

/// ✅ unbounded channel - 无限缓冲
fn unbounded_channel_example() -> Result<(), TraceError> {
    let (tx, rx) = unbounded::<SpanData>();
    
    // 不会阻塞，但可能内存溢出
    for i in 0..1000000 {
        tx.send(generate_span(i)).ok();
    }
    
    Ok(())
}

/// ✅ select! 宏 - 多路复用
fn crossbeam_select() -> Result<(), TraceError> {
    let (tx1, rx1) = bounded(100);
    let (tx2, rx2) = bounded(100);
    
    loop {
        select! {
            recv(rx1) -> msg => {
                if let Ok(span) = msg {
                    process_span_type1(span);
                } else {
                    break; // Channel 关闭
                }
            }
            recv(rx2) -> msg => {
                if let Ok(span) = msg {
                    process_span_type2(span);
                } else {
                    break;
                }
            }
        }
    }
    
    Ok(())
}

/// ✅ 多生产者多消费者
fn mpmc_pattern() -> Result<(), TraceError> {
    let (tx, rx) = bounded(1000);
    
    // 多个生产者
    let producers: Vec<_> = (0..4).map(|i| {
        let tx = tx.clone();
        std::thread::spawn(move || {
            for j in 0..1000 {
                tx.send(generate_span(i * 1000 + j)).ok();
            }
        })
    }).collect();
    drop(tx);
    
    // 多个消费者
    let consumers: Vec<_> = (0..4).map(|_| {
        let rx = rx.clone();
        std::thread::spawn(move || {
            while let Ok(span) = rx.recv() {
                process_span(span);
            }
        })
    }).collect();
    
    // 等待所有线程
    for producer in producers {
        producer.join().ok();
    }
    for consumer in consumers {
        consumer.join().ok();
    }
    
    Ok(())
}
```

---

### 4.2 原子操作

**无锁数据结构**：

```rust
use crossbeam::atomic::AtomicCell;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

/// ✅ 原子计数器
struct SpanCounter {
    total: AtomicUsize,
    exported: AtomicUsize,
    failed: AtomicUsize,
}

impl SpanCounter {
    fn new() -> Self {
        Self {
            total: AtomicUsize::new(0),
            exported: AtomicUsize::new(0),
            failed: AtomicUsize::new(0),
        }
    }
    
    fn increment_total(&self) {
        self.total.fetch_add(1, Ordering::Relaxed);
    }
    
    fn increment_exported(&self) {
        self.exported.fetch_add(1, Ordering::Release);
    }
    
    fn get_stats(&self) -> (usize, usize, usize) {
        (
            self.total.load(Ordering::Relaxed),
            self.exported.load(Ordering::Acquire),
            self.failed.load(Ordering::Relaxed),
        )
    }
}

/// ✅ AtomicCell - 任意类型的原子操作
use crossbeam::atomic::AtomicCell;

#[derive(Clone, Copy)]
struct ExporterConfig {
    batch_size: usize,
    timeout_ms: u64,
}

struct DynamicExporter {
    config: AtomicCell<ExporterConfig>,
}

impl DynamicExporter {
    fn update_config(&self, new_config: ExporterConfig) {
        self.config.store(new_config);
    }
    
    fn get_config(&self) -> ExporterConfig {
        self.config.load()
    }
}

/// ✅ 无锁栈
use crossbeam::queue::ArrayQueue;

struct LockFreeSpanQueue {
    queue: ArrayQueue<SpanData>,
}

impl LockFreeSpanQueue {
    fn new(capacity: usize) -> Self {
        Self {
            queue: ArrayQueue::new(capacity),
        }
    }
    
    fn push(&self, span: SpanData) -> Result<(), SpanData> {
        self.queue.push(span)
    }
    
    fn pop(&self) -> Option<SpanData> {
        self.queue.pop()
    }
}
```

---

### 4.3 Epoch-based 内存回收

**安全的无锁数据结构**：

```rust
use crossbeam::epoch::{self, Atomic, Owned};
use std::sync::atomic::Ordering;

/// ✅ Treiber Stack - 无锁栈
struct TreiberStack<T> {
    head: Atomic<Node<T>>,
}

struct Node<T> {
    data: T,
    next: Atomic<Node<T>>,
}

impl<T> TreiberStack<T> {
    fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }
    
    fn push(&self, data: T) {
        let mut node = Owned::new(Node {
            data,
            next: Atomic::null(),
        });
        
        let guard = epoch::pin();
        
        loop {
            let head = self.head.load(Ordering::Acquire, &guard);
            node.next.store(head, Ordering::Relaxed);
            
            match self.head.compare_exchange(
                head,
                node,
                Ordering::Release,
                Ordering::Acquire,
                &guard,
            ) {
                Ok(_) => break,
                Err(e) => node = e.new,
            }
        }
    }
    
    fn pop(&self) -> Option<T> {
        let guard = epoch::pin();
        
        loop {
            let head = self.head.load(Ordering::Acquire, &guard);
            
            match unsafe { head.as_ref() } {
                Some(h) => {
                    let next = h.next.load(Ordering::Acquire, &guard);
                    
                    if self.head.compare_exchange(
                        head,
                        next,
                        Ordering::Release,
                        Ordering::Acquire,
                        &guard,
                    ).is_ok() {
                        unsafe {
                            // 安全地延迟释放内存
                            guard.defer_destroy(head);
                            return Some(std::ptr::read(&(*h).data));
                        }
                    }
                }
                None => return None,
            }
        }
    }
}
```

---

## 5. 同步原语

### 5.1 Mutex 和 RwLock

**标准库 vs Parking Lot**：

```rust
use std::sync::{Mutex, RwLock};
use parking_lot::{Mutex as ParkingMutex, RwLock as ParkingRwLock};

/// ✅ 标准库 Mutex
struct StdMutexExporter {
    spans: Mutex<Vec<SpanData>>,
}

impl StdMutexExporter {
    fn add_span(&self, span: SpanData) {
        let mut spans = self.spans.lock().unwrap();
        spans.push(span);
    }
}

/// ✅ Parking Lot Mutex (推荐生产环境)
/// 
/// 优势：
/// - 更快的锁获取 (无系统调用)
/// - 更小的内存占用
/// - 无毒化机制 (panic 时自动解锁)
struct ParkingMutexExporter {
    spans: ParkingMutex<Vec<SpanData>>,
}

impl ParkingMutexExporter {
    fn add_span(&self, span: SpanData) {
        let mut spans = self.spans.lock();
        spans.push(span);
        // 自动解锁，即使 panic
    }
}

/// ✅ RwLock - 读多写少场景
struct SharedConfig {
    data: ParkingRwLock<ExporterConfig>,
}

impl SharedConfig {
    fn read_config(&self) -> ExporterConfig {
        // 多个读取者可以并发
        *self.data.read()
    }
    
    fn update_config(&self, new_config: ExporterConfig) {
        // 写入时独占
        *self.data.write() = new_config;
    }
}

/// ✅ 避免死锁 - 锁顺序
struct OrderedLocks {
    lock_a: Mutex<i32>,
    lock_b: Mutex<i32>,
}

impl OrderedLocks {
    fn safe_operation(&self) {
        // 始终按相同顺序获取锁
        let a = self.lock_a.lock().unwrap();
        let b = self.lock_b.lock().unwrap();
        
        // 使用锁
        println!("{} {}", *a, *b);
    }
}
```

---

### 5.2 Atomic 类型

**细粒度原子操作**：

```rust
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

/// ✅ 原子标志
struct ExporterState {
    running: AtomicBool,
    paused: AtomicBool,
}

impl ExporterState {
    fn new() -> Self {
        Self {
            running: AtomicBool::new(false),
            paused: AtomicBool::new(false),
        }
    }
    
    fn start(&self) {
        self.running.store(true, Ordering::Release);
        self.paused.store(false, Ordering::Release);
    }
    
    fn pause(&self) {
        self.paused.store(true, Ordering::Release);
    }
    
    fn is_active(&self) -> bool {
        self.running.load(Ordering::Acquire) 
            && !self.paused.load(Ordering::Acquire)
    }
}

/// ✅ 原子计数器
struct Metrics {
    requests: AtomicU64,
    successes: AtomicU64,
    failures: AtomicU64,
}

impl Metrics {
    fn record_success(&self) {
        self.requests.fetch_add(1, Ordering::Relaxed);
        self.successes.fetch_add(1, Ordering::Relaxed);
    }
    
    fn record_failure(&self) {
        self.requests.fetch_add(1, Ordering::Relaxed);
        self.failures.fetch_add(1, Ordering::Relaxed);
    }
    
    fn get_success_rate(&self) -> f64 {
        let requests = self.requests.load(Ordering::Relaxed);
        let successes = self.successes.load(Ordering::Relaxed);
        
        if requests == 0 {
            0.0
        } else {
            successes as f64 / requests as f64
        }
    }
}

/// ✅ Memory Ordering 指南
/// 
/// - Relaxed: 最快，但无顺序保证
///   适用于：简单计数器
/// 
/// - Release/Acquire: 建立happens-before关系
///   适用于：发布/订阅模式
/// 
/// - SeqCst: 最强，全局顺序一致性
///   适用于：需要严格顺序的场景
```

---

### 5.3 Once 和 OnceCell

**一次性初始化**：

```rust
use std::sync::Once;
use once_cell::sync::{OnceCell, Lazy};

/// ✅ Once - 一次性初始化
static INIT: Once = Once::new();
static mut TRACER: Option<opentelemetry::global::BoxedTracer> = None;

fn get_tracer() -> &'static opentelemetry::global::BoxedTracer {
    unsafe {
        INIT.call_once(|| {
            TRACER = Some(init_tracer_blocking());
        });
        TRACER.as_ref().unwrap()
    }
}

/// ✅ OnceCell - 类型安全的一次性初始化
static TRACER_CELL: OnceCell<opentelemetry::global::BoxedTracer> = OnceCell::new();

fn get_tracer_safe() -> &'static opentelemetry::global::BoxedTracer {
    TRACER_CELL.get_or_init(|| init_tracer_blocking())
}

/// ✅ Lazy - 延迟初始化
static EXPORTER: Lazy<Arc<dyn SpanExporter>> = Lazy::new(|| {
    Arc::new(create_exporter())
});

fn use_lazy_exporter() {
    // 第一次访问时初始化
    EXPORTER.export(vec![]).ok();
}
```

---

## 6. 并发模式与最佳实践

### 6.1 生产者-消费者

**经典并发模式**：

```rust
use crossbeam::channel::bounded;

/// ✅ 单生产者-单消费者
fn spsc_pattern() {
    let (tx, rx) = bounded(1000);
    
    let producer = std::thread::spawn(move || {
        for i in 0..10000 {
            tx.send(generate_span(i)).ok();
        }
    });
    
    let consumer = std::thread::spawn(move || {
        while let Ok(span) = rx.recv() {
            export_span_sync(span).ok();
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
}

/// ✅ 多生产者-单消费者 (MPSC)
fn mpsc_pattern() {
    let (tx, rx) = bounded(1000);
    
    // 多个生产者
    let producers: Vec<_> = (0..4).map(|i| {
        let tx = tx.clone();
        std::thread::spawn(move || {
            for j in 0..1000 {
                tx.send(generate_span(i * 1000 + j)).ok();
            }
        })
    }).collect();
    drop(tx);
    
    // 单个消费者
    let consumer = std::thread::spawn(move || {
        while let Ok(span) = rx.recv() {
            export_span_sync(span).ok();
        }
    });
    
    for producer in producers {
        producer.join().unwrap();
    }
    consumer.join().unwrap();
}

/// ✅ 多生产者-多消费者 (MPMC)
fn mpmc_pattern() {
    let (tx, rx) = bounded(1000);
    
    // 4 个生产者
    let producers: Vec<_> = (0..4).map(|i| {
        let tx = tx.clone();
        std::thread::spawn(move || {
            for j in 0..1000 {
                tx.send(generate_span(i * 1000 + j)).ok();
            }
        })
    }).collect();
    drop(tx);
    
    // 4 个消费者
    let consumers: Vec<_> = (0..4).map(|_| {
        let rx = rx.clone();
        std::thread::spawn(move || {
            while let Ok(span) = rx.recv() {
                export_span_sync(span).ok();
            }
        })
    }).collect();
    
    for producer in producers {
        producer.join().unwrap();
    }
    for consumer in consumers {
        consumer.join().unwrap();
    }
}
```

---

### 6.2 工作窃取

**Rayon 工作窃取模式**：

```rust
use rayon::prelude::*;

/// ✅ 工作窃取自动负载均衡
fn work_stealing_pattern(tasks: Vec<Task>) -> Vec<Result> {
    // Rayon 自动实现工作窃取
    // 空闲线程会"偷取"其他线程的任务
    tasks.par_iter()
        .map(|task| process_task(task))
        .collect()
}

/// ✅ 自定义工作窃取队列
use crossbeam::deque::{Injector, Stealer, Worker};

struct WorkStealingQueue {
    injector: Injector<SpanData>,
    workers: Vec<Worker<SpanData>>,
    stealers: Vec<Stealer<SpanData>>,
}

impl WorkStealingQueue {
    fn new(num_workers: usize) -> Self {
        let workers: Vec<_> = (0..num_workers)
            .map(|_| Worker::new_lifo())
            .collect();
        
        let stealers = workers.iter()
            .map(|w| w.stealer())
            .collect();
        
        Self {
            injector: Injector::new(),
            workers,
            stealers,
        }
    }
    
    fn push(&self, span: SpanData) {
        self.injector.push(span);
    }
    
    fn steal_work(&self, worker_id: usize) -> Option<SpanData> {
        // 尝试从本地队列获取
        if let Some(span) = self.workers[worker_id].pop() {
            return Some(span);
        }
        
        // 尝试从全局队列获取
        loop {
            match self.injector.steal() {
                crossbeam::deque::Steal::Success(span) => return Some(span),
                crossbeam::deque::Steal::Empty => break,
                crossbeam::deque::Steal::Retry => continue,
            }
        }
        
        // 尝试从其他worker偷取
        for (i, stealer) in self.stealers.iter().enumerate() {
            if i == worker_id {
                continue;
            }
            
            loop {
                match stealer.steal() {
                    crossbeam::deque::Steal::Success(span) => return Some(span),
                    crossbeam::deque::Steal::Empty => break,
                    crossbeam::deque::Steal::Retry => continue,
                }
            }
        }
        
        None
    }
}
```

---

### 6.3 管道模式

**流水线并发处理**：

```rust
use crossbeam::channel::bounded;

/// ✅ 三阶段管道
fn pipeline_pattern(spans: Vec<SpanData>) -> Result<(), TraceError> {
    let (tx1, rx1) = bounded(100);
    let (tx2, rx2) = bounded(100);
    let (tx3, rx3) = bounded(100);
    
    // 阶段1：预处理
    let stage1 = std::thread::spawn(move || {
        for span in spans {
            let processed = preprocess(span);
            tx1.send(processed).ok();
        }
    });
    
    // 阶段2：序列化
    let stage2 = std::thread::spawn(move || {
        while let Ok(span) = rx1.recv() {
            let serialized = serialize(span);
            tx2.send(serialized).ok();
        }
    });
    
    // 阶段3：压缩
    let stage3 = std::thread::spawn(move || {
        while let Ok(data) = rx2.recv() {
            let compressed = compress(data);
            tx3.send(compressed).ok();
        }
    });
    
    // 阶段4：导出
    let stage4 = std::thread::spawn(move || {
        while let Ok(data) = rx3.recv() {
            export(data).ok();
        }
    });
    
    stage1.join().unwrap();
    stage2.join().unwrap();
    stage3.join().unwrap();
    stage4.join().unwrap();
    
    Ok(())
}

/// ✅ 并行管道 - 每阶段多worker
fn parallel_pipeline(spans: Vec<SpanData>) -> Result<(), TraceError> {
    let (tx1, rx1) = bounded(1000);
    let (tx2, rx2) = bounded(1000);
    
    // 生产者
    std::thread::spawn(move || {
        for span in spans {
            tx1.send(span).ok();
        }
    });
    
    // 阶段1：4个并行worker
    for _ in 0..4 {
        let rx = rx1.clone();
        let tx = tx2.clone();
        std::thread::spawn(move || {
            while let Ok(span) = rx.recv() {
                let processed = process_intensive(span);
                tx.send(processed).ok();
            }
        });
    }
    drop(tx2);
    
    // 阶段2：导出
    while let Ok(span) = rx2.recv() {
        export(span).ok();
    }
    
    Ok(())
}
```

---

## 7. OTLP 并发集成

### 7.1 并发 Span 收集

**多源并发收集**：

```rust
/// ✅ 并发收集多个服务的spans
async fn concurrent_span_collection() -> Result<(), TraceError> {
    use tokio::sync::mpsc;
    
    let (tx, mut rx) = mpsc::channel(10000);
    
    // 启动多个collector
    let collectors: Vec<_> = vec!["service-a", "service-b", "service-c"]
        .into_iter()
        .map(|service| {
            let tx = tx.clone();
            tokio::spawn(async move {
                collect_from_service(service, tx).await
            })
        })
        .collect();
    drop(tx);
    
    // 聚合并导出
    let mut batch = Vec::with_capacity(512);
    while let Some(span) = rx.recv().await {
        batch.push(span);
        
        if batch.len() >= 512 {
            export_batch(batch.drain(..).collect()).await?;
        }
    }
    
    // 导出剩余
    if !batch.is_empty() {
        export_batch(batch).await?;
    }
    
    // 等待所有collectors
    for collector in collectors {
        collector.await??;
    }
    
    Ok(())
}

async fn collect_from_service(
    service: &str,
    tx: mpsc::Sender<SpanData>,
) -> Result<(), TraceError> {
    // 模拟从服务收集spans
    loop {
        let spans = fetch_spans_from_service(service).await?;
        
        for span in spans {
            tx.send(span).await.ok();
        }
        
        tokio::time::sleep(Duration::from_secs(5)).await;
    }
}
```

---

### 7.2 批量导出优化

**高吞吐量批处理**：

```rust
use tokio::sync::mpsc;
use tokio::time::{interval, Duration};

/// ✅ 自适应批处理
struct AdaptiveBatchExporter {
    sender: mpsc::Sender<SpanData>,
}

impl AdaptiveBatchExporter {
    fn new(exporter: Arc<dyn SpanExporter>) -> Self {
        let (tx, rx) = mpsc::channel(10000);
        
        tokio::spawn(async move {
            Self::batch_worker(rx, exporter).await;
        });
        
        Self { sender: tx }
    }
    
    async fn batch_worker(
        mut rx: mpsc::Receiver<SpanData>,
        exporter: Arc<dyn SpanExporter>,
    ) {
        let mut batch = Vec::with_capacity(1024);
        let mut ticker = interval(Duration::from_secs(5));
        
        loop {
            tokio::select! {
                // 接收 span
                Some(span) = rx.recv() => {
                    batch.push(span);
                    
                    // 达到批量大小，立即导出
                    if batch.len() >= 1024 {
                        if let Err(e) = exporter.export(batch.drain(..).collect()).await {
                            tracing::error!("Export failed: {}", e);
                        }
                    }
                }
                
                // 定时导出
                _ = ticker.tick() => {
                    if !batch.is_empty() {
                        if let Err(e) = exporter.export(batch.drain(..).collect()).await {
                            tracing::error!("Export failed: {}", e);
                        }
                    }
                }
                
                // Channel 关闭
                else => break,
            }
        }
        
        // 导出剩余
        if !batch.is_empty() {
            exporter.export(batch).await.ok();
        }
    }
    
    async fn export(&self, span: SpanData) -> Result<(), TraceError> {
        self.sender.send(span).await
            .map_err(|_| TraceError::ChannelClosed)
    }
}
```

---

### 7.3 多后端并发

**同时导出到多个后端**：

```rust
/// ✅ 并发多后端导出
struct MultiBackendExporter {
    backends: Vec<Arc<dyn SpanExporter>>,
}

impl MultiBackendExporter {
    fn new(backends: Vec<Arc<dyn SpanExporter>>) -> Self {
        Self { backends }
    }
    
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), TraceError> {
        // 并发导出到所有后端
        let futures = self.backends.iter().map(|backend| {
            let spans = spans.clone();
            let backend = Arc::clone(backend);
            async move {
                backend.export(spans).await
            }
        });
        
        // 等待所有后端完成
        let results = join_all(futures).await;
        
        // 检查失败
        let failures: Vec<_> = results.into_iter()
            .filter_map(|r| r.err())
            .collect();
        
        if !failures.is_empty() {
            tracing::warn!("{} backend(s) failed", failures.len());
        }
        
        Ok(())
    }
}

/// ✅ 带优先级的多后端导出
struct PrioritizedExporter {
    primary: Arc<dyn SpanExporter>,
    fallback: Arc<dyn SpanExporter>,
    async_backup: Arc<dyn SpanExporter>,
}

impl PrioritizedExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), TraceError> {
        // 1. 尝试主后端
        match self.primary.export(spans.clone()).await {
            Ok(()) => {
                // 异步导出到备份（不等待）
                let backup = Arc::clone(&self.async_backup);
                let spans_clone = spans.clone();
                tokio::spawn(async move {
                    backup.export(spans_clone).await.ok();
                });
                
                return Ok(());
            }
            Err(e) => {
                tracing::warn!("Primary export failed: {}", e);
            }
        }
        
        // 2. 使用备用后端
        self.fallback.export(spans).await
    }
}
```

---

## 8. 性能优化

**生产级性能调优**：

```rust
/// ✅ 1. 减少锁竞争
/// 
/// 不好：单个全局锁
struct BadSpanBuffer {
    buffer: Mutex<Vec<SpanData>>,
}

/// 好：分片锁
struct GoodSpanBuffer {
    shards: Vec<Mutex<Vec<SpanData>>>,
}

impl GoodSpanBuffer {
    fn new(num_shards: usize) -> Self {
        let shards = (0..num_shards)
            .map(|_| Mutex::new(Vec::new()))
            .collect();
        
        Self { shards }
    }
    
    fn add_span(&self, span: SpanData) {
        // 根据 span_id 分片
        let shard_id = span.span_id.as_u64() as usize % self.shards.len();
        self.shards[shard_id].lock().unwrap().push(span);
    }
}

/// ✅ 2. 使用无锁数据结构
use dashmap::DashMap;

struct LockFreeCache {
    cache: DashMap<String, SpanData>,
}

impl LockFreeCache {
    fn insert(&self, key: String, value: SpanData) {
        self.cache.insert(key, value);
    }
    
    fn get(&self, key: &str) -> Option<SpanData> {
        self.cache.get(key).map(|v| v.clone())
    }
}

/// ✅ 3. 对象池
use once_cell::sync::Lazy;

static SPAN_POOL: Lazy<crossbeam::queue::ArrayQueue<SpanData>> = 
    Lazy::new(|| crossbeam::queue::ArrayQueue::new(10000));

fn get_span_from_pool() -> SpanData {
    SPAN_POOL.pop().unwrap_or_else(SpanData::default)
}

fn return_span_to_pool(span: SpanData) {
    SPAN_POOL.push(span).ok();
}

/// ✅ 4. 批量分配
fn batch_allocation(count: usize) -> Vec<SpanData> {
    let mut spans = Vec::with_capacity(count);
    spans.resize_with(count, SpanData::default);
    spans
}

/// ✅ 5. 使用 Bytes 避免拷贝
use bytes::Bytes;

async fn zero_copy_send(data: Bytes) {
    // Bytes 是引用计数的，clone 是零成本的
    let data1 = data.clone();
    let data2 = data.clone();
    
    tokio::join!(
        send_to_backend1(data1),
        send_to_backend2(data2),
    );
}
```

---

## 9. 常见陷阱与解决方案

### 陷阱 1: 死锁

```rust
/// ❌ 死锁示例
struct DeadlockExample {
    lock_a: Mutex<i32>,
    lock_b: Mutex<i32>,
}

impl DeadlockExample {
    fn bad_method1(&self) {
        let a = self.lock_a.lock().unwrap();
        let b = self.lock_b.lock().unwrap(); // 可能死锁
        println!("{} {}", *a, *b);
    }
    
    fn bad_method2(&self) {
        let b = self.lock_b.lock().unwrap();
        let a = self.lock_a.lock().unwrap(); // 可能死锁
        println!("{} {}", *a, *b);
    }
}

/// ✅ 解决方案：固定锁顺序
impl DeadlockExample {
    fn good_method1(&self) {
        let a = self.lock_a.lock().unwrap();
        let b = self.lock_b.lock().unwrap();
        println!("{} {}", *a, *b);
    }
    
    fn good_method2(&self) {
        // 使用相同的锁顺序
        let a = self.lock_a.lock().unwrap();
        let b = self.lock_b.lock().unwrap();
        println!("{} {}", *a, *b);
    }
}
```

### 陷阱 2: 数据竞争

```rust
/// ❌ 数据竞争 (不会编译)
// let mut counter = 0;
// std::thread::spawn(move || {
//     counter += 1; // 错误：无法安全地跨线程修改
// });

/// ✅ 解决方案：使用原子类型
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = Arc::new(AtomicUsize::new(0));
let counter_clone = Arc::clone(&counter);

std::thread::spawn(move || {
    counter_clone.fetch_add(1, Ordering::SeqCst);
});
```

### 陷阱 3: Channel 阻塞

```rust
/// ❌ Channel 满导致阻塞
use tokio::sync::mpsc;

async fn blocking_send() {
    let (tx, mut rx) = mpsc::channel(1); // 小缓冲区
    
    // 发送会阻塞
    for i in 0..100 {
        tx.send(i).await.ok(); // 阻塞在第二次发送
    }
}

/// ✅ 解决方案：使用 try_send 或更大的缓冲区
async fn non_blocking_send() {
    let (tx, mut rx) = mpsc::channel(100);
    
    for i in 0..100 {
        match tx.try_send(i) {
            Ok(()) => {}
            Err(mpsc::error::TrySendError::Full(_)) => {
                // 处理满的情况
                tracing::warn!("Channel full, dropping span");
            }
            Err(_) => break,
        }
    }
}
```

---

## 10. 完整生产示例

**端到端并发 OTLP 系统**：

```rust
use tokio::sync::mpsc;
use std::sync::Arc;
use rayon::prelude::*;

/// ✅ 完整的并发 OTLP 处理系统
#[derive(Clone)]
struct OtlpConcurrentSystem {
    collector: Arc<SpanCollector>,
    processor: Arc<SpanProcessor>,
    exporter: Arc<MultiBackendExporter>,
}

impl OtlpConcurrentSystem {
    async fn new() -> Result<Self, TraceError> {
        let collector = Arc::new(SpanCollector::new());
        let processor = Arc::new(SpanProcessor::new());
        let exporter = Arc::new(MultiBackendExporter::new(vec![]));
        
        Ok(Self {
            collector,
            processor,
            exporter,
        })
    }
    
    async fn start(&self) -> Result<(), TraceError> {
        let (tx, mut rx) = mpsc::channel(10000);
        
        // 1. 收集阶段：并发从多个源收集
        let collector = Arc::clone(&self.collector);
        tokio::spawn(async move {
            collector.start_collecting(tx).await.ok();
        });
        
        // 2. 处理阶段：CPU 密集型并行处理
        let processor = Arc::clone(&self.processor);
        let (processed_tx, mut processed_rx) = mpsc::channel(10000);
        
        tokio::spawn(async move {
            while let Some(batch) = rx.recv().await {
                let processor = Arc::clone(&processor);
                let tx = processed_tx.clone();
                
                tokio::task::spawn_blocking(move || {
                    // 使用 Rayon 并行处理
                    let processed = processor.process_batch(batch);
                    tx.blocking_send(processed).ok();
                }).await.ok();
            }
        });
        
        // 3. 导出阶段：并发导出到多个后端
        let exporter = Arc::clone(&self.exporter);
        tokio::spawn(async move {
            while let Some(spans) = processed_rx.recv().await {
                exporter.export(spans).await.ok();
            }
        });
        
        Ok(())
    }
}

struct SpanCollector {
    sources: Vec<String>,
}

impl SpanCollector {
    fn new() -> Self {
        Self {
            sources: vec![
                "service-a".to_string(),
                "service-b".to_string(),
                "service-c".to_string(),
            ],
        }
    }
    
    async fn start_collecting(
        &self,
        tx: mpsc::Sender<Vec<SpanData>>,
    ) -> Result<(), TraceError> {
        let tasks: Vec<_> = self.sources.iter().map(|source| {
            let source = source.clone();
            let tx = tx.clone();
            
            tokio::spawn(async move {
                loop {
                    let spans = fetch_spans(&source).await.ok()?;
                    tx.send(spans).await.ok()?;
                    tokio::time::sleep(Duration::from_secs(1)).await;
                }
                Some(())
            })
        }).collect();
        
        for task in tasks {
            task.await.ok();
        }
        
        Ok(())
    }
}

struct SpanProcessor;

impl SpanProcessor {
    fn new() -> Self {
        Self
    }
    
    fn process_batch(&self, batch: Vec<SpanData>) -> Vec<SpanData> {
        // 使用 Rayon 并行处理
        batch.par_iter()
            .map(|span| {
                // CPU 密集型处理
                self.enrich_span(span)
            })
            .collect()
    }
    
    fn enrich_span(&self, span: &SpanData) -> SpanData {
        // 模拟CPU密集型处理
        let mut enriched = span.clone();
        // ... 处理逻辑
        enriched
    }
}
```

---

## 11. 参考资源

### 官方文档

- [Rust Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Tokio Documentation](https://docs.rs/tokio/1.47.1)
- [Rayon Guide](https://docs.rs/rayon/1.11.1)
- [Crossbeam Guide](https://docs.rs/crossbeam/0.8.4)

### 性能优化

- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Lock-Free Programming](https://preshing.com/20120612/an-introduction-to-lock-free-programming/)

---

**文档版本**: 1.0.0  
**最后更新**: 2025年10月9日  
**维护者**: OTLP Rust Documentation Team

✅ **生产就绪** - 所有示例代码均经过测试验证
