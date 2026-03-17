//! # Tokio 1.50+ 新特性集成
//!
//! 本模块展示 Tokio 1.50+ 版本的新特性和最佳实践，
//! 用于构建高性能异步遥测处理系统。
//!
//! ## Tokio 1.50+ 新特性
//!
//! - **任务指标**: `tokio::runtime::RuntimeMetrics` 提供运行时统计
//! - **任务转储**: 调试和诊断功能增强
//! - ** Cooperative Scheduling**: 改进的任务调度公平性
//! - **io_uring 支持**: Linux 高性能异步 I/O (tokio-uring)
//! - **tracing 集成**: 与 tracing 生态的深度集成
//!
//! ## 性能优化
//!
//! - 使用 `tokio::task::yield_now()` 避免长任务阻塞
//! - 使用 `tokio::task::consume_budget()` 控制 CPU 预算
//! - 使用 `tokio::runtime::Handle` 进行跨运行时通信
//! - 使用 `tokio::sync::watch` 进行广播配置更新

use std::{
    future::Future,
    sync::Arc,
    time::Duration,
};

use tokio::{
    sync::{mpsc, watch, Semaphore},
    task::JoinHandle,
};

/// Tokio 运行时指标收集器
///
/// 利用 Tokio 1.50+ 的运行时指标 API 收集性能数据
#[derive(Debug, Clone)]
pub struct TokioMetricsCollector {
    runtime_handle: tokio::runtime::Handle,
}

impl TokioMetricsCollector {
    /// 创建新的指标收集器
    pub fn new() -> Self {
        Self {
            runtime_handle: tokio::runtime::Handle::current(),
        }
    }

    /// 收集当前运行时指标
    ///
    /// 返回包含各种运行时统计的结构体
    pub fn collect_metrics(&self) -> TokioRuntimeMetrics {
        let metrics = self.runtime_handle.metrics();
        
        TokioRuntimeMetrics {
            // 工作线程统计
            num_workers: metrics.num_workers(),
            
            // 任务统计 (使用全局队列深度作为近似)
            active_tasks_count: metrics.global_queue_depth(),
            blocking_tasks_count: 0, // Tokio 1.50 不直接暴露此指标
            
            // 注入队列统计
            injection_queue_depth: metrics.global_queue_depth(),
            
            // 工作线程队列统计（简化）
            worker_local_queue_depth: vec![metrics.global_queue_depth() / metrics.num_workers().max(1)],
            
            // 偷取统计（简化）
            total_steal_count: 0,
            total_steal_operations: 0,
            
            // 阻塞操作统计
            blocking_queue_depth: 0,
            
            // IO 驱动统计（如果启用）
            num_alive_tasks: metrics.global_queue_depth(),
            
            // 时间统计
            elapsed: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        }
    }

    /// 检查运行时健康状况
    pub fn health_check(&self) -> RuntimeHealth {
        let metrics = self.collect_metrics();
        
        // 简单的健康检查逻辑
        let is_healthy = metrics.injection_queue_depth < 1000 
            && metrics.active_tasks_count < 10000;
        
        let is_overloaded = metrics.active_tasks_count > 50000
            || metrics.injection_queue_depth > 10000;
        
        RuntimeHealth {
            is_healthy,
            is_overloaded,
            metrics,
        }
    }
}

impl Default for TokioMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Tokio 运行时指标快照
#[derive(Debug, Clone)]
pub struct TokioRuntimeMetrics {
    pub num_workers: usize,
    pub active_tasks_count: usize,
    pub blocking_tasks_count: usize,
    pub injection_queue_depth: usize,
    pub worker_local_queue_depth: Vec<usize>,
    pub total_steal_count: u64,
    pub total_steal_operations: u64,
    pub blocking_queue_depth: usize,
    pub num_alive_tasks: usize,
    pub elapsed: u64,
}

/// 运行时健康状态
#[derive(Debug, Clone)]
pub struct RuntimeHealth {
    pub is_healthy: bool,
    pub is_overloaded: bool,
    pub metrics: TokioRuntimeMetrics,
}

/// 协作式任务调度器
///
/// 使用 `tokio::task::consume_budget()` 实现协作式调度，
/// 防止单个任务长时间占用 CPU
pub struct CooperativeProcessor<T> {
    items: Vec<T>,
    processed: usize,
}

impl<T> CooperativeProcessor<T> {
    pub fn new(items: Vec<T>) -> Self {
        Self {
            items,
            processed: 0,
        }
    }

    /// 处理下一个批次，同时检查协作预算
    ///
    /// 定期 yield 以允许其他任务运行
    pub async fn process_next_batch<F, Fut>(&mut self, batch_size: usize, processor: F) -> usize
    where
        F: Fn(T) -> Fut,
        Fut: Future<Output = ()>,
    {
        let mut count = 0;
        
        while count < batch_size && self.processed < self.items.len() {
            // 每处理 100 项检查一次预算
            if count > 0 && count % 100 == 0 {
                tokio::task::consume_budget().await;
            }
            
            let item = std::mem::replace(
                &mut self.items[self.processed],
                unsafe { std::mem::zeroed() },
            );
            processor(item).await;
            
            self.processed += 1;
            count += 1;
        }
        
        count
    }

    /// 是否还有更多项目需要处理
    pub fn has_more(&self) -> bool {
        self.processed < self.items.len()
    }

    /// 获取处理进度
    pub fn progress(&self) -> (usize, usize) {
        (self.processed, self.items.len())
    }
}

/// 使用 watch 通道的配置管理器
///
/// Tokio 的 watch 通道适合用于广播配置更新
#[derive(Debug, Clone)]
pub struct WatchedConfig<T: Clone + Send + Sync + 'static> {
    tx: watch::Sender<T>,
}

impl<T: Clone + Send + Sync + 'static> WatchedConfig<T> {
    /// 创建新的 watched 配置
    pub fn new(initial: T) -> Self {
        let (tx, _) = watch::channel(initial);
        Self { tx }
    }

    /// 更新配置
    pub fn update(&self, new_value: T) -> Result<(), watch::error::SendError<T>> {
        self.tx.send(new_value)
    }

    /// 订阅配置更新
    pub fn subscribe(&self) -> watch::Receiver<T> {
        self.tx.subscribe()
    }

    /// 获取当前值
    pub fn current(&self) -> T {
        self.tx.borrow().clone()
    }
}

/// 动态批次处理器
///
/// 根据运行时负载动态调整批量大小
pub struct AdaptiveBatchProcessor<T> {
    items: Vec<T>,
    base_batch_size: usize,
    metrics_collector: TokioMetricsCollector,
}

impl<T> AdaptiveBatchProcessor<T> {
    pub fn new(base_batch_size: usize) -> Self {
        Self {
            items: Vec::new(),
            base_batch_size,
            metrics_collector: TokioMetricsCollector::new(),
        }
    }

    /// 添加项目
    pub fn push(&mut self, item: T) {
        self.items.push(item);
    }

    /// 根据运行时负载计算动态批量大小
    pub fn dynamic_batch_size(&self) -> usize {
        let metrics = self.metrics_collector.collect_metrics();
        
        // 如果运行时负载高，减小批量大小
        if metrics.injection_queue_depth > 100 {
            self.base_batch_size / 2
        } else if metrics.active_tasks_count < 100 {
            // 如果运行时空闲，增大批量大小
            self.base_batch_size * 2
        } else {
            self.base_batch_size
        }
    }

    /// 处理当前批次
    pub fn process_batch<F>(&mut self, mut processor: F) -> Vec<T>
    where
        F: FnMut(&T),
    {
        let batch_size = self.dynamic_batch_size().min(self.items.len());
        let batch: Vec<T> = self.items.drain(..batch_size).collect();
        
        // 处理每个项目但不获取所有权
        for item in &batch {
            processor(item);
        }
        batch
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

/// 基于信号量的并发限制器
///
/// 使用 Tokio 的信号量控制并发任务数量
#[derive(Debug, Clone)]
pub struct ConcurrencyLimiter {
    semaphore: Arc<Semaphore>,
}

impl ConcurrencyLimiter {
    /// 创建新的并发限制器
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    /// 获取一个并发槽位
    pub async fn acquire(&self) -> Result<tokio::sync::SemaphorePermit<'_>, tokio::sync::AcquireError> {
        self.semaphore.acquire().await
    }

    /// 尝试立即获取槽位
    pub fn try_acquire(&self) -> Result<tokio::sync::SemaphorePermit<'_>, tokio::sync::TryAcquireError> {
        self.semaphore.try_acquire()
    }

    /// 在限制内执行异步任务
    pub async fn run<F, Fut, R>(&self, f: F) -> R
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = R>,
    {
        let _permit = self.acquire().await.expect("Semaphore closed");
        f().await
    }
}

/// 任务取消处理器
///
/// 使用 Tokio 的取消令牌实现优雅的任务取消
#[derive(Debug)]
pub struct CancellableTask<T> {
    handle: JoinHandle<T>,
    cancel_tx: watch::Sender<bool>,
}

impl<T> CancellableTask<T> {
    /// 创建新的可取消任务
    pub fn new<F, Fut>(f: F) -> Self
    where
        F: FnOnce(watch::Receiver<bool>) -> Fut + Send + 'static,
        Fut: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let (cancel_tx, cancel_rx) = watch::channel(false);
        
        let handle = tokio::spawn(async move {
            f(cancel_rx).await
        });
        
        Self {
            handle,
            cancel_tx,
        }
    }

    /// 请求取消任务
    pub fn cancel(&self) -> Result<(), watch::error::SendError<bool>> {
        self.cancel_tx.send(true)
    }

    /// 等待任务完成
    pub async fn await_completion(self) -> Result<T, tokio::task::JoinError> {
        self.handle.await
    }

    /// 中止任务
    pub fn abort(&self) {
        self.handle.abort();
    }
}

/// 高性能异步批处理通道
///
/// 使用 mpsc 通道实现生产者-消费者模式
pub struct BatchChannel<T> {
    tx: mpsc::Sender<T>,
    rx: mpsc::Receiver<T>,
}

impl<T> BatchChannel<T> {
    /// 创建新的批处理通道
    pub fn new(capacity: usize) -> Self {
        let (tx, rx) = mpsc::channel(capacity);
        Self { tx, rx }
    }

    /// 获取发送端
    pub fn sender(&self) -> mpsc::Sender<T> {
        self.tx.clone()
    }

    /// 获取接收端
    pub fn receiver(&mut self) -> &mut mpsc::Receiver<T> {
        &mut self.rx
    }

    /// 批量接收项目
    pub async fn recv_batch(&mut self, batch_size: usize, timeout: Duration) -> Vec<T> {
        let mut batch = Vec::with_capacity(batch_size);
        let deadline = tokio::time::Instant::now() + timeout;
        
        while batch.len() < batch_size {
            let remaining = deadline.duration_since(tokio::time::Instant::now());
            
            match tokio::time::timeout(remaining, self.rx.recv()).await {
                Ok(Some(item)) => batch.push(item),
                Ok(None) => break, // 通道关闭
                Err(_) => break,   // 超时
            }
        }
        
        batch
    }
}

/// 使用 tokio::select! 的多路复用处理器
///
/// 同时处理多个异步源
pub struct MultiplexedProcessor<T> {
    channel: BatchChannel<T>,
    config: WatchedConfig<ProcessorConfig>,
}

#[derive(Debug, Clone)]
pub struct ProcessorConfig {
    pub batch_size: usize,
    pub timeout_ms: u64,
}

impl Default for ProcessorConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            timeout_ms: 1000,
        }
    }
}

impl<T: Send + 'static> MultiplexedProcessor<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            channel: BatchChannel::new(capacity),
            config: WatchedConfig::new(ProcessorConfig::default()),
        }
    }

    /// 运行多路复用处理器
    pub async fn run<F, Fut>(mut self, mut processor: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(Vec<T>) -> Fut + Send + 'static,
        Fut: Future<Output = Result<(), Box<dyn std::error::Error>>> + Send + 'static,
    {
        let mut config_rx = self.config.subscribe();
        let mut current_config = ProcessorConfig::default();
        
        loop {
            tokio::select! {
                // 批量接收项目
                batch = self.channel.recv_batch(
                    current_config.batch_size,
                    Duration::from_millis(current_config.timeout_ms)
                ) => {
                    if batch.is_empty() {
                        continue;
                    }
                    
                    if let Err(e) = processor(batch).await {
                        tracing::error!(error = ?e, "Batch processing failed");
                    }
                }
                
                // 配置更新
                Ok(()) = config_rx.changed() => {
                    current_config = config_rx.borrow().clone();
                    tracing::info!(config = ?current_config, "Configuration updated");
                }
                
                // 优雅关闭信号
                _ = tokio::signal::ctrl_c() => {
                    tracing::info!("Shutdown signal received");
                    break;
                }
            }
        }
        
        Ok(())
    }

    pub fn sender(&self) -> mpsc::Sender<T> {
        self.channel.sender()
    }

    pub fn config(&self) -> &WatchedConfig<ProcessorConfig> {
        &self.config
    }
}

/// 创建优化后的 Tokio 运行时
///
/// 配置适合遥测处理的工作线程和阻塞线程池
pub fn create_telemetry_runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_stack_size(2 * 1024 * 1024) // 2MB 栈大小
        .enable_all()
        .build()
        .expect("Failed to create Tokio runtime")
}

/// 启动运行时指标监控任务
pub fn spawn_metrics_monitor(collector: TokioMetricsCollector, interval_secs: u64) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(interval_secs));
        
        loop {
            interval.tick().await;
            
            let metrics = collector.collect_metrics();
            let health = collector.health_check();
            
            tracing::info!(
                active_tasks = metrics.active_tasks_count,
                injection_queue = metrics.injection_queue_depth,
                healthy = health.is_healthy,
                "Runtime metrics"
            );
            
            if health.is_overloaded {
                tracing::warn!("Runtime is overloaded!");
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metrics_collector() {
        let collector = TokioMetricsCollector::new();
        let metrics = collector.collect_metrics();
        
        assert!(metrics.num_workers > 0);
        assert!(metrics.active_tasks_count >= 1); // 当前测试任务
    }

    #[tokio::test]
    async fn test_watched_config() {
        let config = WatchedConfig::new(42i32);
        let mut rx = config.subscribe();
        
        assert_eq!(config.current(), 42);
        
        config.update(100).unwrap();
        
        rx.changed().await.unwrap();
        assert_eq!(*rx.borrow(), 100);
    }

    #[tokio::test]
    async fn test_concurrency_limiter() {
        let limiter = ConcurrencyLimiter::new(2);
        let counter = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        
        let mut handles = vec![];
        
        for _ in 0..5 {
            let limiter = limiter.clone();
            let counter = counter.clone();
            
            handles.push(tokio::spawn(async move {
                limiter.run(|| async {
                    counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    tokio::time::sleep(Duration::from_millis(10)).await;
                    counter.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                }).await;
            }));
        }
        
        for h in handles {
            h.await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_batch_channel() {
        let mut channel: BatchChannel<i32> = BatchChannel::new(100);
        let tx = channel.sender();
        
        for i in 0..10 {
            tx.send(i).await.unwrap();
        }
        
        let batch = channel.recv_batch(5, Duration::from_millis(100)).await;
        assert_eq!(batch.len(), 5);
        assert_eq!(batch, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_create_telemetry_runtime() {
        let rt = create_telemetry_runtime();
        
        rt.block_on(async {
            let collector = TokioMetricsCollector::new();
            let metrics = collector.collect_metrics();
            
            assert!(metrics.num_workers > 0);
        });
    }
}
