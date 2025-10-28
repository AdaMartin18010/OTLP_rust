//! # Complete CSP (Communicating Sequential Processes) Model Implementation
//! 
//! 完整的CSP模型实现，基于Go语言风格的channel通信
//! 
//! ## CSP核心概念
//! - **Channel**: 进程间通信的管道
//! - **Select**: 多路复用，从多个channel中选择
//! - **Process**: 独立的计算单元
//! - **Synchronous Communication**: 同步通信模式
//! 
//! ## 实现特性
//! - Unbounded/Bounded channels
//! - Select多路复用
//! - Fan-in/Fan-out模式
//! - Pipeline模式
//! - Worker pool模式
//! - Timeout支持
//! - Priority channels
//! 
//! ## 使用场景
//! - 并发数据处理
//! - 流水线处理
//! - 生产者-消费者模式
//! - 任务调度

use tokio::sync::{mpsc, oneshot};
use tokio::time::{sleep, timeout, Duration, Instant};
use tokio::{select, join};
use futures::stream::{self, StreamExt};
use std::sync::Arc;
use tracing::{info, warn, error, instrument};

// ============================================================================
// Part 1: Channel Types and Utilities
// ============================================================================

/// 消息类型
#[derive(Debug, Clone)]
pub struct Message<T> {
    pub data: T,
    pub timestamp: Instant,
    pub id: u64,
}

impl<T> Message<T> {
    pub fn new(data: T, id: u64) -> Self {
        Self {
            data,
            timestamp: Instant::now(),
            id,
        }
    }
}

/// 工作任务
#[derive(Debug, Clone)]
pub struct Task {
    pub id: u64,
    pub name: String,
    pub payload: String,
}

/// 工作结果
#[derive(Debug, Clone)]
pub struct TaskResult {
    pub task_id: u64,
    pub result: String,
    pub duration_ms: u128,
}

// ============================================================================
// Part 2: Basic Channel Communication
// ============================================================================

/// Demo: 基本的channel通信
#[instrument]
pub async fn demo_basic_channels() {
    info!("=== Demo: Basic Channel Communication ===");

    // Unbounded channel
    let (tx, mut rx) = mpsc::unbounded_channel::<String>();

    // Sender task
    tokio::spawn(async move {
        for i in 0..5 {
            let msg = format!("Message {}", i);
            info!("Sending: {}", msg);
            tx.send(msg).unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    // Receiver task
    while let Some(msg) = rx.recv().await {
        info!("Received: {}", msg);
    }

    info!("Basic channel demo completed");
}

/// Demo: Bounded channel with backpressure
#[instrument]
pub async fn demo_bounded_channels() {
    info!("=== Demo: Bounded Channel with Backpressure ===");

    let (tx, mut rx) = mpsc::channel::<i32>(3); // capacity = 3

    // Fast sender
    let sender = tokio::spawn(async move {
        for i in 0..10 {
            info!("Trying to send {}", i);
            tx.send(i).await.unwrap();
            info!("Sent {}", i);
        }
    });

    // Slow receiver
    let receiver = tokio::spawn(async move {
        while let Some(value) = rx.recv().await {
            info!("Received: {}", value);
            sleep(Duration::from_millis(200)).await; // Slow processing
        }
    });

    let _ = join!(sender, receiver);
    info!("Bounded channel demo completed");
}

// ============================================================================
// Part 3: Select - Multiplexing
// ============================================================================

/// Demo: Select多路复用
#[instrument]
pub async fn demo_select_multiplexing() {
    info!("=== Demo: Select Multiplexing ===");

    let (tx1, mut rx1) = mpsc::channel::<String>(10);
    let (tx2, mut rx2) = mpsc::channel::<String>(10);
    let (tx3, mut rx3) = mpsc::channel::<String>(10);

    // Sender 1
    tokio::spawn(async move {
        for i in 0..3 {
            tx1.send(format!("Channel 1: Message {}", i)).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    // Sender 2
    tokio::spawn(async move {
        for i in 0..3 {
            tx2.send(format!("Channel 2: Message {}", i)).await.unwrap();
            sleep(Duration::from_millis(150)).await;
        }
    });

    // Sender 3
    tokio::spawn(async move {
        for i in 0..3 {
            tx3.send(format!("Channel 3: Message {}", i)).await.unwrap();
            sleep(Duration::from_millis(200)).await;
        }
    });

    // Select from multiple channels
    let mut count = 0;
    while count < 9 {
        select! {
            Some(msg) = rx1.recv() => {
                info!("Received from rx1: {}", msg);
                count += 1;
            }
            Some(msg) = rx2.recv() => {
                info!("Received from rx2: {}", msg);
                count += 1;
            }
            Some(msg) = rx3.recv() => {
                info!("Received from rx3: {}", msg);
                count += 1;
            }
        }
    }

    info!("Select demo completed");
}

/// Demo: Select with timeout
#[instrument]
pub async fn demo_select_with_timeout() {
    info!("=== Demo: Select with Timeout ===");

    let (tx, mut rx) = mpsc::channel::<String>(10);

    // Sender with delay
    tokio::spawn(async move {
        sleep(Duration::from_millis(500)).await;
        tx.send("Delayed message".to_string()).await.unwrap();
    });

    // Receiver with timeout
    let timeout_duration = Duration::from_millis(200);
    
    select! {
        Some(msg) = rx.recv() => {
            info!("Received message: {}", msg);
        }
        _ = sleep(timeout_duration) => {
            warn!("Timeout! No message received within {:?}", timeout_duration);
        }
    }

    info!("Select with timeout demo completed");
}

// ============================================================================
// Part 4: Pipeline Pattern
// ============================================================================

/// Demo: Pipeline处理模式
#[instrument]
pub async fn demo_pipeline() {
    info!("=== Demo: Pipeline Pattern ===");

    // Stage 1: Generator
    let (gen_tx, gen_rx) = mpsc::channel::<i32>(10);
    tokio::spawn(async move {
        for i in 1..=10 {
            info!("Generator: producing {}", i);
            gen_tx.send(i).await.unwrap();
        }
    });

    // Stage 2: Doubler
    let (double_tx, double_rx) = mpsc::channel::<i32>(10);
    tokio::spawn(async move {
        let mut rx = gen_rx;
        while let Some(value) = rx.recv().await {
            let doubled = value * 2;
            info!("Doubler: {} -> {}", value, doubled);
            double_tx.send(doubled).await.unwrap();
        }
    });

    // Stage 3: Squarer
    let (square_tx, square_rx) = mpsc::channel::<i32>(10);
    tokio::spawn(async move {
        let mut rx = double_rx;
        while let Some(value) = rx.recv().await {
            let squared = value * value;
            info!("Squarer: {} -> {}", value, squared);
            square_tx.send(squared).await.unwrap();
        }
    });

    // Final consumer
    let consumer = tokio::spawn(async move {
        let mut rx = square_rx;
        let mut results = Vec::new();
        while let Some(value) = rx.recv().await {
            info!("Consumer: received {}", value);
            results.push(value);
        }
        results
    });

    let results = consumer.await.unwrap();
    info!("Pipeline results: {:?}", results);
}

// ============================================================================
// Part 5: Fan-Out / Fan-In Pattern
// ============================================================================

/// Demo: Fan-Out模式 (一个生产者，多个消费者)
#[instrument]
pub async fn demo_fan_out() {
    info!("=== Demo: Fan-Out Pattern ===");

    let (tx, _) = tokio::sync::broadcast::channel::<i32>(10);

    // Single producer
    let producer = tx.clone();
    tokio::spawn(async move {
        for i in 0..10 {
            info!("Producer: broadcasting {}", i);
            producer.send(i).unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    // Multiple consumers
    let mut handles = Vec::new();
    for worker_id in 0..3 {
        let mut rx = tx.subscribe();
        let handle = tokio::spawn(async move {
            while let Ok(value) = rx.recv().await {
                info!("Worker {}: received {}", worker_id, value);
                sleep(Duration::from_millis(50)).await;
            }
        });
        handles.push(handle);
    }

    sleep(Duration::from_secs(2)).await;
    drop(tx); // Close channel

    for handle in handles {
        let _ = handle.await;
    }

    info!("Fan-out demo completed");
}

/// Demo: Fan-In模式 (多个生产者，一个消费者)
#[instrument]
pub async fn demo_fan_in() {
    info!("=== Demo: Fan-In Pattern ===");

    let (tx, mut rx) = mpsc::channel::<String>(100);

    // Multiple producers
    let num_producers = 3;
    for producer_id in 0..num_producers {
        let tx = tx.clone();
        tokio::spawn(async move {
            for i in 0..5 {
                let msg = format!("Producer {} - Message {}", producer_id, i);
                info!("{}", msg);
                tx.send(msg).await.unwrap();
                sleep(Duration::from_millis(100 + producer_id * 50)).await;
            }
        });
    }

    drop(tx); // Close the original sender

    // Single consumer
    let mut count = 0;
    while let Some(msg) = rx.recv().await {
        info!("Consumer: received '{}'", msg);
        count += 1;
    }

    info!("Fan-in demo completed, received {} messages", count);
}

// ============================================================================
// Part 6: Worker Pool Pattern
// ============================================================================

/// Demo: Worker Pool模式
#[instrument]
pub async fn demo_worker_pool() {
    info!("=== Demo: Worker Pool Pattern ===");

    let (work_tx, work_rx) = mpsc::channel::<Task>(100);
    let (result_tx, mut result_rx) = mpsc::channel::<TaskResult>(100);

    // Shared work queue
    let work_rx = Arc::new(tokio::sync::Mutex::new(work_rx));

    // Spawn worker pool
    const NUM_WORKERS: usize = 4;
    let mut worker_handles = Vec::new();

    for worker_id in 0..NUM_WORKERS {
        let work_rx = work_rx.clone();
        let result_tx = result_tx.clone();

        let handle = tokio::spawn(async move {
            loop {
                let task = {
                    let mut rx = work_rx.lock().await;
                    rx.recv().await
                };

                match task {
                    Some(task) => {
                        info!("Worker {} processing task {}: {}", 
                              worker_id, task.id, task.name);
                        
                        let start = Instant::now();
                        
                        // Simulate work
                        sleep(Duration::from_millis(100)).await;
                        
                        let result = TaskResult {
                            task_id: task.id,
                            result: format!("Processed by worker {}", worker_id),
                            duration_ms: start.elapsed().as_millis(),
                        };
                        
                        result_tx.send(result).await.unwrap();
                    }
                    None => {
                        info!("Worker {} shutting down", worker_id);
                        break;
                    }
                }
            }
        });

        worker_handles.push(handle);
    }

    // Dispatcher: send tasks
    tokio::spawn(async move {
        for i in 0..20 {
            let task = Task {
                id: i,
                name: format!("Task-{}", i),
                payload: format!("Data for task {}", i),
            };
            work_tx.send(task).await.unwrap();
        }
    });

    // Result collector
    let collector = tokio::spawn(async move {
        let mut results = Vec::new();
        for _ in 0..20 {
            if let Some(result) = result_rx.recv().await {
                info!("Result for task {}: {} ({}ms)", 
                      result.task_id, result.result, result.duration_ms);
                results.push(result);
            }
        }
        results
    });

    let results = collector.await.unwrap();
    info!("Worker pool processed {} tasks", results.len());

    // Wait for workers to finish
    for handle in worker_handles {
        let _ = handle.await;
    }
}

// ============================================================================
// Part 7: Barrier and Synchronization
// ============================================================================

/// Demo: 使用channel实现barrier同步
#[instrument]
pub async fn demo_barrier_sync() {
    info!("=== Demo: Barrier Synchronization ===");

    let num_workers = 5;
    let (barrier_tx, mut barrier_rx) = mpsc::channel::<()>(num_workers);

    // Spawn workers
    let mut handles = Vec::new();
    for worker_id in 0..num_workers {
        let tx = barrier_tx.clone();
        
        let handle = tokio::spawn(async move {
            // Phase 1: Initialization
            info!("Worker {} initializing...", worker_id);
            sleep(Duration::from_millis(100 + worker_id as u64 * 50)).await;
            info!("Worker {} initialized", worker_id);
            
            // Signal completion
            tx.send(()).await.unwrap();
        });
        
        handles.push(handle);
    }

    drop(barrier_tx);

    // Wait for all workers to reach barrier
    let mut count = 0;
    while let Some(_) = barrier_rx.recv().await {
        count += 1;
        info!("Worker {}/{} reached barrier", count, num_workers);
    }

    info!("All workers synchronized!");

    // Now all workers can proceed to phase 2
    for handle in handles {
        let _ = handle.await;
    }
}

// ============================================================================
// Part 8: Priority Channels
// ============================================================================

/// 优先级消息
#[derive(Debug, Clone)]
pub struct PriorityMessage {
    pub priority: u8, // 0 = highest
    pub data: String,
}

/// Demo: 优先级channel
#[instrument]
pub async fn demo_priority_channels() {
    info!("=== Demo: Priority Channels ===");

    let (high_tx, mut high_rx) = mpsc::channel::<PriorityMessage>(10);
    let (medium_tx, mut medium_rx) = mpsc::channel::<PriorityMessage>(10);
    let (low_tx, mut low_rx) = mpsc::channel::<PriorityMessage>(10);

    // Send messages with different priorities
    tokio::spawn(async move {
        for i in 0..3 {
            high_tx.send(PriorityMessage {
                priority: 0,
                data: format!("HIGH priority {}", i),
            }).await.unwrap();
            
            medium_tx.send(PriorityMessage {
                priority: 1,
                data: format!("MEDIUM priority {}", i),
            }).await.unwrap();
            
            low_tx.send(PriorityMessage {
                priority: 2,
                data: format!("LOW priority {}", i),
            }).await.unwrap();
            
            sleep(Duration::from_millis(50)).await;
        }
    });

    // Process with priority
    let mut count = 0;
    while count < 9 {
        select! {
            // Try high priority first (biased select)
            biased;
            
            Some(msg) = high_rx.recv() => {
                info!("Processing: {:?}", msg);
                count += 1;
            }
            Some(msg) = medium_rx.recv() => {
                info!("Processing: {:?}", msg);
                count += 1;
            }
            Some(msg) = low_rx.recv() => {
                info!("Processing: {:?}", msg);
                count += 1;
            }
        }
    }

    info!("Priority channels demo completed");
}

// ============================================================================
// Part 9: Request-Reply Pattern
// ============================================================================

/// 请求消息
#[derive(Debug)]
pub struct Request {
    pub id: u64,
    pub query: String,
    pub reply_to: oneshot::Sender<Response>,
}

/// 响应消息
#[derive(Debug)]
pub struct Response {
    pub request_id: u64,
    pub result: String,
}

/// Demo: Request-Reply模式
#[instrument]
pub async fn demo_request_reply() {
    info!("=== Demo: Request-Reply Pattern ===");

    let (req_tx, mut req_rx) = mpsc::channel::<Request>(10);

    // Server
    tokio::spawn(async move {
        while let Some(request) = req_rx.recv().await {
            info!("Server processing request {}: {}", request.id, request.query);
            
            // Process request
            sleep(Duration::from_millis(100)).await;
            
            let response = Response {
                request_id: request.id,
                result: format!("Result for: {}", request.query),
            };
            
            // Send reply
            let _ = request.reply_to.send(response);
        }
    });

    // Clients
    let mut client_handles = Vec::new();
    for i in 0..5 {
        let tx = req_tx.clone();
        
        let handle = tokio::spawn(async move {
            let (reply_tx, reply_rx) = oneshot::channel();
            
            let request = Request {
                id: i,
                query: format!("Query {}", i),
                reply_to: reply_tx,
            };
            
            info!("Client {} sending request", i);
            tx.send(request).await.unwrap();
            
            // Wait for reply
            match reply_rx.await {
                Ok(response) => {
                    info!("Client {} received: {:?}", i, response);
                }
                Err(_) => {
                    error!("Client {} failed to receive reply", i);
                }
            }
        });
        
        client_handles.push(handle);
    }

    for handle in client_handles {
        let _ = handle.await;
    }

    info!("Request-reply demo completed");
}

// ============================================================================
// Part 10: Generator Pattern
// ============================================================================

/// Demo: Generator模式
#[instrument]
pub async fn demo_generator() {
    info!("=== Demo: Generator Pattern ===");

    // Generator function
    async fn generate_numbers(tx: mpsc::Sender<i32>, start: i32, end: i32) {
        for i in start..=end {
            info!("Generator: yielding {}", i);
            if tx.send(i).await.is_err() {
                break;
            }
            sleep(Duration::from_millis(100)).await;
        }
    }

    let (tx, mut rx) = mpsc::channel::<i32>(10);

    // Start generator
    tokio::spawn(generate_numbers(tx, 1, 10));

    // Consume generated values
    while let Some(value) = rx.recv().await {
        info!("Consumer: received {}", value);
        
        // Process value
        let result = value * value;
        info!("Consumer: processed {} -> {}", value, result);
    }

    info!("Generator demo completed");
}

// ============================================================================
// Main Function - Run All Demos
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    info!("🚀 Starting CSP Model Demos");

    // Demo 1: Basic channels
    demo_basic_channels().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 2: Bounded channels
    demo_bounded_channels().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 3: Select multiplexing
    demo_select_multiplexing().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 4: Select with timeout
    demo_select_with_timeout().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 5: Pipeline
    demo_pipeline().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 6: Fan-out
    demo_fan_out().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 7: Fan-in
    demo_fan_in().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 8: Worker pool
    demo_worker_pool().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 9: Barrier sync
    demo_barrier_sync().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 10: Priority channels
    demo_priority_channels().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 11: Request-reply
    demo_request_reply().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 12: Generator
    demo_generator().await;

    info!("✅ All CSP demos completed!");

    Ok(())
}

