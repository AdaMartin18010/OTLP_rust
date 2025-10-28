//! # Async Programming Best Practices with Rust 1.90
//! 
//! 全面的异步编程最佳实践示例，展示Tokio和async-std的高级用法
//! 
//! ## 涵盖主题
//! - 异步任务管理（spawn, JoinSet, select）
//! - 超时和取消
//! - 并发控制（Semaphore, RwLock, Mutex）
//! - 错误处理
//! - 背压（Backpressure）
//! - 流（Stream）处理
//! - 通道（Channel）模式
//! - 异步递归
//! - 性能优化
//! 
//! ## Rust 1.90 特性
//! - 改进的异步fn性能
//! - 更好的编译时优化
//! - 新的Future组合器

use tokio::{
    sync::{mpsc, oneshot, Semaphore, RwLock, Mutex},
    task::{JoinSet, JoinHandle},
    time::{sleep, timeout, Duration, Instant},
    select,
};
use futures::{
    stream::{self, StreamExt, FuturesUnordered},
    future::BoxFuture,
};
use std::sync::Arc;
use tracing::{info, warn, error, instrument};

// ============================================================================
// Part 1: Task Management and Spawning
// ============================================================================

/// 基本任务生成和等待
pub async fn basic_task_spawning() {
    info!("=== Basic Task Spawning ===");

    // 单个任务
    let handle = tokio::spawn(async {
        sleep(Duration::from_millis(100)).await;
        "Task completed"
    });

    match handle.await {
        Ok(result) => info!("Task result: {}", result),
        Err(e) => error!("Task failed: {}", e),
    }

    // 多个独立任务
    let mut handles = Vec::new();
    for i in 0..5 {
        handles.push(tokio::spawn(async move {
            sleep(Duration::from_millis(i * 10)).await;
            format!("Task {} completed", i)
        }));
    }

    for handle in handles {
        if let Ok(result) = handle.await {
            info!("{}", result);
        }
    }
}

/// JoinSet使用 - 更好的任务管理
pub async fn joinset_usage() {
    info!("=== JoinSet Usage ===");

    let mut set = JoinSet::new();

    // 添加任务到集合
    for i in 0..10 {
        set.spawn(async move {
            sleep(Duration::from_millis(i * 20)).await;
            i * 2
        });
    }

    // 等待所有任务完成
    let mut results = Vec::new();
    while let Some(result) = set.join_next().await {
        match result {
            Ok(value) => results.push(value),
            Err(e) => error!("Task panicked: {}", e),
        }
    }

    info!("All tasks completed. Results: {:?}", results);
}

/// 有限并发执行
pub async fn limited_concurrency_example() {
    info!("=== Limited Concurrency ===");

    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发任务
    let mut handles = Vec::new();

    for i in 0..10 {
        let permit = semaphore.clone();
        handles.push(tokio::spawn(async move {
            let _permit = permit.acquire().await.unwrap();
            info!("Task {} started", i);
            sleep(Duration::from_millis(500)).await;
            info!("Task {} completed", i);
            i
        }));
    }

    let results: Vec<_> = futures::future::join_all(handles)
        .await
        .into_iter()
        .filter_map(|r| r.ok())
        .collect();

    info!("Limited concurrency results: {:?}", results);
}

// ============================================================================
// Part 2: Timeout and Cancellation
// ============================================================================

/// 超时处理模式
pub async fn timeout_patterns() {
    info!("=== Timeout Patterns ===");

    // 基本超时
    let result = timeout(
        Duration::from_millis(100),
        sleep(Duration::from_secs(1))
    ).await;

    match result {
        Ok(_) => info!("Completed in time"),
        Err(_) => warn!("Operation timed out"),
    }

    // 多个操作的超时
    let operations = vec![
        tokio::spawn(slow_operation(50)),
        tokio::spawn(slow_operation(150)),
        tokio::spawn(slow_operation(250)),
    ];

    for (i, op) in operations.into_iter().enumerate() {
        match timeout(Duration::from_millis(100), op).await {
            Ok(Ok(result)) => info!("Operation {} succeeded: {}", i, result),
            Ok(Err(e)) => error!("Operation {} failed: {}", i, e),
            Err(_) => warn!("Operation {} timed out", i),
        }
    }
}

async fn slow_operation(ms: u64) -> Result<String, &'static str> {
    sleep(Duration::from_millis(ms)).await;
    Ok(format!("Completed after {}ms", ms))
}

/// 取消信号模式
pub async fn cancellation_patterns() {
    info!("=== Cancellation Patterns ===");

    let (cancel_tx, mut cancel_rx) = oneshot::channel::<()>();

    let task = tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_millis(100));
        loop {
            select! {
                _ = interval.tick() => {
                    info!("Working...");
                }
                _ = &mut cancel_rx => {
                    info!("Received cancellation signal");
                    break;
                }
            }
        }
        "Task cancelled gracefully"
    });

    // 让任务运行一段时间
    sleep(Duration::from_millis(500)).await;

    // 发送取消信号
    let _ = cancel_tx.send(());

    if let Ok(result) = task.await {
        info!("Task result: {}", result);
    }
}

// ============================================================================
// Part 3: Concurrent Data Structures
// ============================================================================

/// RwLock使用模式
pub async fn rwlock_patterns() {
    info!("=== RwLock Patterns ===");

    let shared_data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));

    // 多个读者
    let mut readers = Vec::new();
    for i in 0..5 {
        let data = shared_data.clone();
        readers.push(tokio::spawn(async move {
            let read_guard = data.read().await;
            info!("Reader {} sees: {:?}", i, *read_guard);
            sleep(Duration::from_millis(10)).await;
        }));
    }

    // 等待所有读者
    for reader in readers {
        let _ = reader.await;
    }

    // 写入者
    {
        let mut write_guard = shared_data.write().await;
        write_guard.push(6);
        info!("Writer added element: {:?}", *write_guard);
    }

    // 再次读取
    let read_guard = shared_data.read().await;
    info!("Final data: {:?}", *read_guard);
}

/// Mutex使用模式
pub async fn mutex_patterns() {
    info!("=== Mutex Patterns ===");

    let counter = Arc::new(Mutex::new(0));
    let mut handles = Vec::new();

    for i in 0..10 {
        let counter = counter.clone();
        handles.push(tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
            info!("Task {} incremented counter to {}", i, *num);
            sleep(Duration::from_millis(10)).await;
        }));
    }

    for handle in handles {
        let _ = handle.await;
    }

    let final_count = *counter.lock().await;
    info!("Final counter value: {}", final_count);
}

// ============================================================================
// Part 4: Channel Patterns
// ============================================================================

/// MPSC通道模式
pub async fn mpsc_patterns() {
    info!("=== MPSC Patterns ===");

    let (tx, mut rx) = mpsc::channel::<String>(10);

    // 多个生产者
    for i in 0..5 {
        let tx = tx.clone();
        tokio::spawn(async move {
            for j in 0..3 {
                let msg = format!("Message {}-{}", i, j);
                if tx.send(msg).await.is_err() {
                    error!("Receiver dropped");
                    return;
                }
                sleep(Duration::from_millis(50)).await;
            }
        });
    }

    // 释放原始发送者
    drop(tx);

    // 单个消费者
    while let Some(msg) = rx.recv().await {
        info!("Received: {}", msg);
    }

    info!("All messages processed");
}

/// 有界通道与背压
pub async fn bounded_channel_backpressure() {
    info!("=== Bounded Channel Backpressure ===");

    let (tx, mut rx) = mpsc::channel::<i32>(3); // 容量为3

    // 快速生产者
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            info!("Trying to send {}", i);
            match tx.send(i).await {
                Ok(_) => info!("Sent {}", i),
                Err(_) => {
                    error!("Failed to send {}", i);
                    return;
                }
            }
        }
    });

    // 慢速消费者
    let consumer = tokio::spawn(async move {
        while let Some(value) = rx.recv().await {
            info!("Processing {}", value);
            sleep(Duration::from_millis(200)).await; // 模拟慢处理
        }
    });

    let _ = tokio::join!(producer, consumer);
}

/// Broadcast通道模式
pub async fn broadcast_patterns() {
    info!("=== Broadcast Patterns ===");

    let (tx, _) = tokio::sync::broadcast::channel::<String>(10);

    // 多个订阅者
    let mut subscribers = Vec::new();
    for i in 0..3 {
        let mut rx = tx.subscribe();
        subscribers.push(tokio::spawn(async move {
            while let Ok(msg) = rx.recv().await {
                info!("Subscriber {} received: {}", i, msg);
            }
        }));
    }

    // 发布者
    for i in 0..5 {
        let msg = format!("Broadcast message {}", i);
        if tx.send(msg).is_err() {
            error!("No subscribers");
        }
        sleep(Duration::from_millis(100)).await;
    }

    drop(tx); // 关闭通道

    for sub in subscribers {
        let _ = sub.await;
    }
}

// ============================================================================
// Part 5: Stream Processing
// ============================================================================

/// 流处理模式
pub async fn stream_processing() {
    info!("=== Stream Processing ===");

    // 基本流处理
    let stream = stream::iter(0..10)
        .map(|x| x * 2)
        .filter(|x| x % 3 == 0)
        .take(5);

    let results: Vec<_> = stream.collect().await;
    info!("Stream results: {:?}", results);

    // 并发流处理
    let urls = vec![
        "http://example.com/1",
        "http://example.com/2",
        "http://example.com/3",
    ];

    let results = stream::iter(urls)
        .map(|url| async move {
            fetch_url(url).await
        })
        .buffer_unordered(2) // 最多2个并发请求
        .collect::<Vec<_>>()
        .await;

    info!("Fetched {} URLs", results.len());
}

async fn fetch_url(url: &str) -> Result<String, &'static str> {
    info!("Fetching {}", url);
    sleep(Duration::from_millis(100)).await;
    Ok(format!("Content from {}", url))
}

/// 流的批处理
pub async fn stream_batching() {
    info!("=== Stream Batching ===");

    let stream = stream::iter(0..100)
        .chunks(10); // 批量处理，每批10个

    tokio::pin!(stream);

    while let Some(batch) = stream.next().await {
        info!("Processing batch of {} items: {:?}", batch.len(), &batch[..3.min(batch.len())]);
        sleep(Duration::from_millis(50)).await;
    }
}

// ============================================================================
// Part 6: Async Recursion
// ============================================================================

/// 异步递归（需要Box）
#[instrument]
pub fn async_recursion_example() -> BoxFuture<'static, u64> {
    Box::pin(async_fibonacci(10))
}

fn async_fibonacci(n: u64) -> BoxFuture<'static, u64> {
    Box::pin(async move {
        if n <= 1 {
            return n;
        }
        
        let (a, b) = tokio::join!(
            async_fibonacci(n - 1),
            async_fibonacci(n - 2)
        );
        
        a + b
    })
}

// ============================================================================
// Part 7: Error Handling
// ============================================================================

#[derive(Debug, thiserror::Error)]
pub enum AsyncError {
    #[error("Timeout error")]
    Timeout,
    
    #[error("Task panicked")]
    Panic,
    
    #[error("Channel closed")]
    ChannelClosed,
    
    #[error("Operation failed: {0}")]
    OperationFailed(String),
}

/// 错误处理模式
pub async fn error_handling_patterns() -> Result<(), AsyncError> {
    info!("=== Error Handling Patterns ===");

    // 结果聚合
    let tasks = vec![
        tokio::spawn(fallible_operation(true)),
        tokio::spawn(fallible_operation(false)),
        tokio::spawn(fallible_operation(true)),
    ];

    let results = futures::future::join_all(tasks).await;
    
    for (i, result) in results.into_iter().enumerate() {
        match result {
            Ok(Ok(value)) => info!("Task {} succeeded: {}", i, value),
            Ok(Err(e)) => warn!("Task {} failed: {}", i, e),
            Err(e) => error!("Task {} panicked: {}", i, e),
        }
    }

    Ok(())
}

async fn fallible_operation(succeed: bool) -> Result<String, AsyncError> {
    sleep(Duration::from_millis(50)).await;
    if succeed {
        Ok("Success".to_string())
    } else {
        Err(AsyncError::OperationFailed("Simulated failure".to_string()))
    }
}

// ============================================================================
// Part 8: Advanced Patterns
// ============================================================================

/// 工作池模式
pub async fn worker_pool_pattern() {
    info!("=== Worker Pool Pattern ===");

    let (work_tx, mut work_rx) = mpsc::channel::<i32>(100);
    let (result_tx, mut result_rx) = mpsc::channel::<i32>(100);

    // 启动工作线程池
    const NUM_WORKERS: usize = 4;
    for worker_id in 0..NUM_WORKERS {
        let mut work_rx = work_rx.clone();
        let result_tx = result_tx.clone();
        
        tokio::spawn(async move {
            while let Some(work) = work_rx.recv().await {
                info!("Worker {} processing {}", worker_id, work);
                sleep(Duration::from_millis(100)).await;
                let result = work * 2;
                if result_tx.send(result).await.is_err() {
                    break;
                }
            }
            info!("Worker {} shutting down", worker_id);
        });
    }

    drop(work_rx); // 关闭未使用的接收器

    // 发送工作
    tokio::spawn(async move {
        for i in 0..20 {
            if work_tx.send(i).await.is_err() {
                break;
            }
        }
    });

    drop(result_tx); // 关闭发送器以结束循环

    // 收集结果
    let mut results = Vec::new();
    while let Some(result) = result_rx.recv().await {
        results.push(result);
    }

    info!("Worker pool completed with {} results", results.len());
}

/// 请求合并模式（批处理）
pub async fn request_coalescing() {
    info!("=== Request Coalescing ===");

    let (req_tx, req_rx) = mpsc::channel::<(String, oneshot::Sender<String>)>(100);
    let batcher = Arc::new(RequestBatcher::new(req_rx));

    // 启动批处理器
    let batcher_clone = batcher.clone();
    tokio::spawn(async move {
        batcher_clone.run().await;
    });

    // 发送多个请求
    let mut response_handles = Vec::new();
    for i in 0..10 {
        let (resp_tx, resp_rx) = oneshot::channel();
        let req_tx = req_tx.clone();
        
        response_handles.push(tokio::spawn(async move {
            let request = format!("Request {}", i);
            if req_tx.send((request.clone(), resp_tx)).await.is_err() {
                error!("Failed to send request");
                return;
            }
            
            match resp_rx.await {
                Ok(response) => info!("Got response for {}: {}", request, response),
                Err(_) => error!("Response channel closed"),
            }
        }));
    }

    for handle in response_handles {
        let _ = handle.await;
    }
}

struct RequestBatcher {
    receiver: Mutex<mpsc::Receiver<(String, oneshot::Sender<String>)>>,
}

impl RequestBatcher {
    fn new(receiver: mpsc::Receiver<(String, oneshot::Sender<String>)>) -> Self {
        Self {
            receiver: Mutex::new(receiver),
        }
    }

    async fn run(&self) {
        let mut batch = Vec::new();
        let mut interval = tokio::time::interval(Duration::from_millis(50));

        loop {
            select! {
                _ = interval.tick() => {
                    if !batch.is_empty() {
                        self.process_batch(&mut batch).await;
                    }
                }
                item = self.receiver.lock().await.recv() => {
                    match item {
                        Some(req) => {
                            batch.push(req);
                            if batch.len() >= 5 {
                                self.process_batch(&mut batch).await;
                            }
                        }
                        None => break,
                    }
                }
            }
        }
    }

    async fn process_batch(&self, batch: &mut Vec<(String, oneshot::Sender<String>)>) {
        info!("Processing batch of {} requests", batch.len());
        
        for (request, response_tx) in batch.drain(..) {
            let response = format!("Processed: {}", request);
            let _ = response_tx.send(response);
        }
    }
}

// ============================================================================
// Part 9: Performance Optimization
// ============================================================================

/// 性能优化技巧
pub async fn performance_optimization() {
    info!("=== Performance Optimization ===");

    let start = Instant::now();

    // 避免不必要的clone
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let data_ref = data.clone(); // 只clone Arc指针
    
    tokio::spawn(async move {
        info!("Shared data: {:?}", data_ref);
    }).await.ok();

    // 使用try_join!而非join!提前失败
    let result = tokio::try_join!(
        async { Ok::<_, AsyncError>("Task 1") },
        async { Ok::<_, AsyncError>("Task 2") },
        async { Ok::<_, AsyncError>("Task 3") },
    );

    match result {
        Ok((r1, r2, r3)) => info!("All succeeded: {}, {}, {}", r1, r2, r3),
        Err(e) => error!("Failed: {}", e),
    }

    // 使用buffer_unordered而非buffered
    let items = vec![1, 2, 3, 4, 5];
    let _results: Vec<_> = stream::iter(items)
        .map(|x| async move {
            sleep(Duration::from_millis(10)).await;
            x * 2
        })
        .buffer_unordered(3) // 无序处理，更快
        .collect()
        .await;

    let elapsed = start.elapsed();
    info!("Performance test completed in {:?}", elapsed);
}

// ============================================================================
// Main Function - Run All Examples
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    info!("🚀 Starting Async Programming Best Practices Demo");
    
    // Part 1: Task Management
    basic_task_spawning().await;
    joinset_usage().await;
    limited_concurrency_example().await;

    // Part 2: Timeout and Cancellation
    timeout_patterns().await;
    cancellation_patterns().await;

    // Part 3: Concurrent Data Structures
    rwlock_patterns().await;
    mutex_patterns().await;

    // Part 4: Channel Patterns
    mpsc_patterns().await;
    bounded_channel_backpressure().await;
    broadcast_patterns().await;

    // Part 5: Stream Processing
    stream_processing().await;
    stream_batching().await;

    // Part 6: Async Recursion
    let fib_result = async_recursion_example().await;
    info!("Fibonacci result: {}", fib_result);

    // Part 7: Error Handling
    let _ = error_handling_patterns().await;

    // Part 8: Advanced Patterns
    worker_pool_pattern().await;
    request_coalescing().await;

    // Part 9: Performance Optimization
    performance_optimization().await;

    info!("✅ All examples completed successfully!");
    
    Ok(())
}

