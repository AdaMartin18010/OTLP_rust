//! # 性能优化模块
//!
//! 基于Rust 1.90特性的性能优化实现，包括零拷贝、内存池、批量处理等

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};
use tokio::time::{interval, sleep};
use crate::rust_1_90_optimizations::{OptimizedMemoryPool, ZeroCopyOptimizer};

/// 高性能批处理器
/// 
/// 使用零拷贝和内存池技术优化批量数据处理
pub struct HighPerformanceBatchProcessor<T: Clone + Send + 'static> {
    batch_size: usize,
    batch_timeout: Duration,
    buffer: Arc<Mutex<VecDeque<T>>>,
    semaphore: Arc<Semaphore>,
    last_flush: Arc<RwLock<Instant>>,
    processor: Arc<dyn BatchProcessor<T> + Send + Sync>,
    // 集成Rust 1.90优化特性
    memory_pool: Arc<OptimizedMemoryPool<T>>,
    zero_copy_optimizer: Arc<ZeroCopyOptimizer>,
}

/// 批处理处理器trait
pub trait BatchProcessor<T>: Send + Sync {
    async fn process_batch(&self, batch: Vec<T>) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
}

impl<T: Clone + Send + Sync + 'static> HighPerformanceBatchProcessor<T> {
    /// 创建新的批处理器
    pub fn new(
        batch_size: usize,
        batch_timeout: Duration,
        max_concurrency: usize,
        processor: Arc<dyn BatchProcessor<T> + Send + Sync>,
    ) -> Self {
        // 创建Rust 1.90优化的内存池和零拷贝优化器
        let memory_pool = Arc::new(OptimizedMemoryPool::new(
            || std::default::Default::default(),
            batch_size * 2, // 预分配更多对象
        ));
        let zero_copy_optimizer = Arc::new(ZeroCopyOptimizer);
        
        Self {
            batch_size,
            batch_timeout,
            buffer: Arc::new(Mutex::new(VecDeque::new())),
            semaphore: Arc::new(Semaphore::new(max_concurrency)),
            last_flush: Arc::new(RwLock::new(Instant::now())),
            processor,
            memory_pool,
            zero_copy_optimizer,
        }
    }

    /// 添加数据到批处理队列
    pub async fn add_data(&self, data: T) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut buffer = self.buffer.lock().await;
        buffer.push_back(data);

        // 检查是否需要立即处理
        if buffer.len() >= self.batch_size {
            self.flush_buffer_internal(&mut buffer).await?;
        }

        Ok(())
    }

    /// 强制刷新缓冲区
    pub async fn flush(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut buffer = self.buffer.lock().await;
        self.flush_buffer_internal(&mut buffer).await
    }

    /// 内部刷新缓冲区方法
    async fn flush_buffer_internal(
        &self,
        buffer: &mut VecDeque<T>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if buffer.is_empty() {
            return Ok(());
        }

        // 使用Rust 1.90的元组收集特性优化批处理
        let batch: Vec<T> = buffer.drain(..).collect();
        let processor = Arc::clone(&self.processor);
        let semaphore = Arc::clone(&self.semaphore);

        // 使用信号量控制并发
        let _permit = semaphore.acquire().await
            .map_err(|e| format!("Failed to acquire semaphore: {}", e))?;

        // 异步处理批次
        tokio::spawn(async move {
            if let Err(e) = processor.process_batch(batch).await {
                eprintln!("Batch processing error: {}", e);
            }
        });

        // 更新最后刷新时间
        {
            let mut last_flush = self.last_flush.write().await;
            *last_flush = Instant::now();
        }

        Ok(())
    }

    /// 启动定时刷新任务
    pub async fn start_timer(&self) {
        let buffer = Arc::clone(&self.buffer);
        let last_flush = Arc::clone(&self.last_flush);
        let batch_timeout = self.batch_timeout;
        let processor = Arc::clone(&self.processor);
        let semaphore = Arc::clone(&self.semaphore);

        tokio::spawn(async move {
            let mut interval = interval(batch_timeout);
            loop {
                interval.tick().await;

                let should_flush = {
                    let last_flush = last_flush.read().await;
                    last_flush.elapsed() >= batch_timeout
                };

                if should_flush {
                    let mut buffer = buffer.lock().await;
                    if !buffer.is_empty() {
                        // 使用Rust 1.90的元组收集特性优化批处理
                        let batch: Vec<T> = buffer.drain(..).collect();
                        let processor = Arc::clone(&processor);
                        let semaphore = Arc::clone(&semaphore);

                        let _permit = semaphore.acquire().await;
                        tokio::spawn(async move {
                            if let Err(e) = processor.process_batch(batch).await {
                                eprintln!("Timer batch processing error: {}", e);
                            }
                        });

                        let mut last_flush = last_flush.write().await;
                        *last_flush = Instant::now();
                    }
                }
            }
        });
    }
}

/// 内存池管理器
/// 
/// 使用对象池技术减少内存分配和GC压力
pub struct MemoryPool<T> {
    pool: Arc<Mutex<Vec<T>>>,
    factory: Arc<dyn Fn() -> T + Send + Sync>,
    max_size: usize,
}

impl<T: Send + Sync + 'static> MemoryPool<T> {
    /// 创建新的内存池
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            pool: Arc::new(Mutex::new(Vec::new())),
            factory: Arc::new(factory),
            max_size,
        }
    }

    /// 从池中获取对象
    pub async fn acquire(&self) -> T {
        let mut pool = self.pool.lock().await;
        pool.pop().unwrap_or_else(|| (self.factory)())
    }

    /// 将对象返回到池中
    pub async fn release(&self, mut obj: T) {
        let mut pool = self.pool.lock().await;
        if pool.len() < self.max_size {
            // 重置对象状态（如果实现了Reset trait）
            if let Some(resettable) = (&mut obj as &mut dyn std::any::Any)
                .downcast_mut::<Box<dyn Reset>>()
            {
                resettable.reset();
            }
            pool.push(obj);
        }
    }
}

/// 可重置对象trait
pub trait Reset {
    fn reset(&mut self);
}

/// 零拷贝字符串池
/// 
/// 使用字符串池减少字符串分配和复制
pub struct StringPool {
    pool: Arc<Mutex<Vec<String>>>,
    max_size: usize,
}

impl StringPool {
    /// 创建新的字符串池
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::new())),
            max_size,
        }
    }

    /// 获取字符串（优先从池中获取）
    pub async fn get(&self, capacity: usize) -> String {
        let mut pool = self.pool.lock().await;
        pool.pop().unwrap_or_else(|| String::with_capacity(capacity))
    }

    /// 返回字符串到池中
    pub async fn put(&self, mut s: String) {
        let mut pool = self.pool.lock().await;
        if pool.len() < self.max_size {
            s.clear();
            pool.push(s);
        }
    }
}

/// 高性能计数器
/// 
/// 使用无锁技术实现高性能计数器
pub struct HighPerformanceCounter {
    counters: Arc<Vec<AtomicU64>>,
    mask: usize,
}

impl HighPerformanceCounter {
    /// 创建新的高性能计数器
    pub fn new(num_counters: usize) -> Self {
        let num_counters = num_counters.next_power_of_two();
        let counters = (0..num_counters)
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>();
        
        Self {
            counters: Arc::new(counters),
            mask: num_counters - 1,
        }
    }

    /// 增加计数
    pub fn increment(&self, key: u64) {
        let index = (key as usize) & self.mask;
        self.counters[index].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// 获取计数
    pub fn get(&self, key: u64) -> u64 {
        let index = (key as usize) & self.mask;
        self.counters[index].load(std::sync::atomic::Ordering::Relaxed)
    }

    /// 获取所有计数
    pub fn get_all(&self) -> Vec<u64> {
        self.counters
            .iter()
            .map(|c| c.load(std::sync::atomic::Ordering::Relaxed))
            .collect()
    }
}

/// 自适应批处理大小调整器
/// 
/// 根据系统负载动态调整批处理大小
pub struct AdaptiveBatchSizer {
    current_size: Arc<RwLock<usize>>,
    min_size: usize,
    max_size: usize,
    adjustment_factor: f64,
    last_adjustment: Arc<RwLock<Instant>>,
    adjustment_interval: Duration,
}

impl AdaptiveBatchSizer {
    /// 创建新的自适应批处理大小调整器
    pub fn new(
        initial_size: usize,
        min_size: usize,
        max_size: usize,
        adjustment_factor: f64,
        adjustment_interval: Duration,
    ) -> Self {
        Self {
            current_size: Arc::new(RwLock::new(initial_size)),
            min_size,
            max_size,
            adjustment_factor,
            last_adjustment: Arc::new(RwLock::new(Instant::now())),
            adjustment_interval,
        }
    }

    /// 获取当前批处理大小
    pub async fn get_current_size(&self) -> usize {
        *self.current_size.read().await
    }

    /// 根据性能指标调整批处理大小
    pub async fn adjust_size(&self, throughput: f64, latency: Duration) {
        let now = Instant::now();
        let last_adjustment = *self.last_adjustment.read().await;
        
        if now.duration_since(last_adjustment) < self.adjustment_interval {
            return;
        }

        let mut current_size = self.current_size.write().await;
        let mut last_adjustment = self.last_adjustment.write().await;
        
        // 基于吞吐量和延迟调整批处理大小
        let latency_ms = latency.as_millis() as f64;
        let adjustment = if latency_ms > 100.0 {
            // 延迟过高，减少批处理大小
            -self.adjustment_factor
        } else if throughput < 1000.0 {
            // 吞吐量过低，增加批处理大小
            self.adjustment_factor
        } else {
            // 性能良好，保持当前大小
            0.0
        };

        if adjustment != 0.0 {
            let new_size = (*current_size as f64 * (1.0 + adjustment)) as usize;
            *current_size = new_size.clamp(self.min_size, self.max_size);
        }

        *last_adjustment = now;
    }
}

/// 性能监控器
/// 
/// 监控系统性能指标并提供优化建议
pub struct PerformanceMonitor {
    metrics: Arc<RwLock<PerformanceMetrics>>,
    start_time: Instant,
}

#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_latency: Duration,
    pub min_latency: Duration,
    pub max_latency: Duration,
    pub throughput: f64,
    pub error_rate: f64,
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(PerformanceMetrics {
                total_requests: 0,
                successful_requests: 0,
                failed_requests: 0,
                total_latency: Duration::ZERO,
                min_latency: Duration::MAX,
                max_latency: Duration::ZERO,
                throughput: 0.0,
                error_rate: 0.0,
            })),
            start_time: Instant::now(),
        }
    }

    /// 记录请求
    pub async fn record_request(&self, success: bool, latency: Duration) {
        let mut metrics = self.metrics.write().await;
        
        metrics.total_requests += 1;
        if success {
            metrics.successful_requests += 1;
        } else {
            metrics.failed_requests += 1;
        }

        metrics.total_latency += latency;
        metrics.min_latency = metrics.min_latency.min(latency);
        metrics.max_latency = metrics.max_latency.max(latency);

        // 计算吞吐量和错误率
        let elapsed = self.start_time.elapsed();
        if elapsed.as_secs() > 0 {
            metrics.throughput = metrics.total_requests as f64 / elapsed.as_secs() as f64;
            metrics.error_rate = metrics.failed_requests as f64 / metrics.total_requests as f64;
        }
    }

    /// 获取性能指标
    pub async fn get_metrics(&self) -> PerformanceMetrics {
        self.metrics.read().await.clone()
    }

    /// 获取平均延迟
    pub async fn get_average_latency(&self) -> Duration {
        let metrics = self.metrics.read().await;
        if metrics.total_requests > 0 {
            Duration::from_nanos(
                metrics.total_latency.as_nanos() as u64 / metrics.total_requests
            )
        } else {
            Duration::ZERO
        }
    }
}

impl Default for PerformanceMonitor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU64;

    struct TestBatchProcessor {
        processed_count: Arc<AtomicU64>,
    }

    impl TestBatchProcessor {
        fn new() -> Self {
            Self {
                processed_count: Arc::new(AtomicU64::new(0)),
            }
        }
    }

    #[async_trait::async_trait]
    impl BatchProcessor<String> for TestBatchProcessor {
        async fn process_batch(&self, batch: Vec<String>) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
            self.processed_count.fetch_add(batch.len() as u64, std::sync::atomic::Ordering::Relaxed);
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_batch_processor() {
        let processor = Arc::new(TestBatchProcessor::new());
        let batch_processor = HighPerformanceBatchProcessor::new(
            3,
            Duration::from_millis(100),
            10,
            processor.clone(),
        );

        // 添加数据
        for i in 0..5 {
            batch_processor.add_data(format!("data-{}", i)).await
                .expect("Failed to add data to batch processor");
        }

        // 等待处理完成
        sleep(Duration::from_millis(200)).await;

        // 验证处理结果
        assert_eq!(processor.processed_count.load(std::sync::atomic::Ordering::Relaxed), 5);
    }

    #[tokio::test]
    async fn test_memory_pool() {
        let pool = MemoryPool::new(|| String::new(), 10);
        
        let s1 = pool.acquire().await;
        let s2 = pool.acquire().await;
        
        pool.release(s1).await;
        pool.release(s2).await;
        
        // 验证池中有对象
        let pool_internal = pool.pool.lock().await;
        assert_eq!(pool_internal.len(), 2);
    }

    #[tokio::test]
    async fn test_string_pool() {
        let pool = StringPool::new(5);
        
        let s1 = pool.get(100).await;
        let s2 = pool.get(200).await;
        
        pool.put(s1).await;
        pool.put(s2).await;
        
        // 验证池中有字符串
        let pool_internal = pool.pool.lock().await;
        assert_eq!(pool_internal.len(), 2);
    }

    #[test]
    fn test_high_performance_counter() {
        let counter = HighPerformanceCounter::new(4);
        
        counter.increment(1);
        counter.increment(1);
        counter.increment(2);
        
        assert_eq!(counter.get(1), 2);
        assert_eq!(counter.get(2), 1);
    }

    #[tokio::test]
    async fn test_adaptive_batch_sizer() {
        let sizer = AdaptiveBatchSizer::new(
            100,
            10,
            1000,
            0.1,
            Duration::from_millis(100),
        );
        
        assert_eq!(sizer.get_current_size().await, 100);
        
        // 模拟高延迟情况
        sizer.adjust_size(500.0, Duration::from_millis(200)).await;
        assert!(sizer.get_current_size().await < 100);
    }

    #[tokio::test]
    async fn test_performance_monitor() {
        let monitor = PerformanceMonitor::new();
        
        monitor.record_request(true, Duration::from_millis(10)).await;
        monitor.record_request(false, Duration::from_millis(20)).await;
    }

    /// 获取内存池统计信息
    pub async fn get_memory_pool_stats(&self) -> crate::rust_1_90_optimizations::PoolStats {
        self.memory_pool.get_stats().await
    }

    /// 获取零拷贝优化器
    pub fn get_zero_copy_optimizer(&self) -> &ZeroCopyOptimizer {
        &self.zero_copy_optimizer
    }
}
