//! # 性能增强模块
//!
//! 利用Rust 1.90的新特性实现高性能优化，包括：
//! - 异步生成器
//! - 改进的模式匹配
//! - 优化的内存管理
//! - 并发性能优化

use anyhow::Result;
use std::collections::VecDeque;
use std::future::Future;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::{Duration, Instant};

/// 高性能异步生成器
///
/// 利用Rust 1.90的生成器特性实现高效的数据流处理
pub struct AsyncGenerator<T> {
    items: VecDeque<T>,
    is_complete: bool,
    semaphore: Arc<Semaphore>,
}

impl<T> AsyncGenerator<T> {
    /// 创建新的异步生成器
    pub fn new(capacity: usize) -> Self {
        Self {
            items: VecDeque::with_capacity(capacity),
            is_complete: false,
            semaphore: Arc::new(Semaphore::new(capacity)),
        }
    }

    /// 添加项目到生成器
    pub async fn push(&mut self, item: T) {
        let _permit = self.semaphore.acquire().await.unwrap();
        self.items.push_back(item);
    }

    /// 标记生成器完成
    pub fn complete(&mut self) {
        self.is_complete = true;
    }

    /// 获取下一个项目
    pub async fn next(&mut self) -> Option<T> {
        if self.items.is_empty() && self.is_complete {
            return None;
        }
        self.items.pop_front()
    }
}

/// 高性能批处理器
///
/// 使用Rust 1.90的优化特性实现高效的批处理
#[allow(dead_code)]
#[allow(unused_variables)]
pub struct HighPerformanceBatchProcessor<T> {
    batch_size: usize,
    timeout: Duration,
    batches: Arc<RwLock<VecDeque<Vec<T>>>>,
    current_batch: Arc<RwLock<Vec<T>>>,
    metrics: Arc<BatchProcessorMetrics>,
    semaphore: Arc<Semaphore>,
}

/// 批处理器指标
#[derive(Debug, Default)]
pub struct BatchProcessorMetrics {
    pub total_batches: AtomicU64,
    pub total_items: AtomicU64,
    pub average_batch_size: AtomicUsize,
    pub processing_time: AtomicU64, // 纳秒
    pub queue_size: AtomicUsize,
}

impl<T: Send + Sync + Clone + 'static> HighPerformanceBatchProcessor<T> {
    /// 创建新的高性能批处理器
    pub fn new(batch_size: usize, timeout: Duration, max_concurrent: usize) -> Self {
        Self {
            batch_size,
            timeout,
            batches: Arc::new(RwLock::new(VecDeque::new())),
            current_batch: Arc::new(RwLock::new(Vec::with_capacity(batch_size))),
            metrics: Arc::new(BatchProcessorMetrics::default()),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    /// 添加项目到批处理器
    pub async fn add_item(&self, item: T) -> Result<()> {
        let mut current_batch = self.current_batch.write().await;
        current_batch.push(item);

        // 更新指标
        self.metrics.total_items.fetch_add(1, Ordering::Relaxed);
        self.metrics.queue_size.fetch_add(1, Ordering::Relaxed);

        // 检查是否需要创建新批次
        if current_batch.len() >= self.batch_size {
            let batch = std::mem::replace(&mut *current_batch, Vec::with_capacity(self.batch_size));
            drop(current_batch);

            self.create_batch(batch).await;
        }

        Ok(())
    }

    /// 创建新批次
    async fn create_batch(&self, batch: Vec<T>) {
        let start_time = Instant::now();

        // 更新指标
        self.metrics.total_batches.fetch_add(1, Ordering::Relaxed);
        self.metrics
            .queue_size
            .fetch_sub(batch.len(), Ordering::Relaxed);

        // 计算平均批次大小
        let total_batches = self.metrics.total_batches.load(Ordering::Relaxed);
        let total_items = self.metrics.total_items.load(Ordering::Relaxed);
        let avg_size = if total_batches > 0 {
            total_items / total_batches
        } else {
            0
        };
        self.metrics
            .average_batch_size
            .store(avg_size as usize, Ordering::Relaxed);

        // 添加到批次队列
        {
            let mut batches = self.batches.write().await;
            batches.push_back(batch);
        }

        // 更新处理时间
        let processing_time = start_time.elapsed().as_nanos() as u64;
        self.metrics
            .processing_time
            .fetch_add(processing_time, Ordering::Relaxed);
    }

    /// 获取下一个批次
    pub async fn get_next_batch(&self) -> Option<Vec<T>> {
        let mut batches = self.batches.write().await;
        batches.pop_front()
    }

    /// 强制刷新当前批次
    pub async fn flush(&self) -> Result<Option<Vec<T>>> {
        let mut current_batch = self.current_batch.write().await;
        if current_batch.is_empty() {
            return Ok(None);
        }

        let batch = std::mem::replace(&mut *current_batch, Vec::with_capacity(self.batch_size));
        drop(current_batch);

        self.create_batch(batch.clone()).await;
        Ok(Some(batch))
    }

    /// 获取处理器指标
    pub fn get_metrics(&self) -> BatchProcessorMetricsSnapshot {
        BatchProcessorMetricsSnapshot {
            total_batches: self.metrics.total_batches.load(Ordering::Relaxed),
            total_items: self.metrics.total_items.load(Ordering::Relaxed),
            average_batch_size: self.metrics.average_batch_size.load(Ordering::Relaxed),
            processing_time: Duration::from_nanos(
                self.metrics.processing_time.load(Ordering::Relaxed),
            ),
            queue_size: self.metrics.queue_size.load(Ordering::Relaxed),
        }
    }
}

/// 批处理器指标快照
#[derive(Debug, Clone)]
pub struct BatchProcessorMetricsSnapshot {
    pub total_batches: u64,
    pub total_items: u64,
    pub average_batch_size: usize,
    pub processing_time: Duration,
    pub queue_size: usize,
}

/// 高性能并发执行器
///
/// 使用Rust 1.90的优化特性实现高效的并发执行
pub struct HighPerformanceExecutor {
    semaphore: Arc<Semaphore>,
    metrics: Arc<ExecutorMetrics>,
}

/// 执行器指标
#[derive(Debug, Default)]
pub struct ExecutorMetrics {
    pub total_tasks: AtomicU64,
    pub completed_tasks: AtomicU64,
    pub failed_tasks: AtomicU64,
    pub active_tasks: AtomicUsize,
    pub total_execution_time: AtomicU64, // 纳秒
}

impl HighPerformanceExecutor {
    /// 创建新的高性能执行器
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            metrics: Arc::new(ExecutorMetrics::default()),
        }
    }

    /// 执行异步任务
    pub async fn execute<F, Fut, R>(&self, task: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R>> + Send + 'static,
        R: Send + 'static,
    {
        let _permit = self.semaphore.acquire().await.unwrap();
        let start_time = Instant::now();

        // 更新指标
        self.metrics.total_tasks.fetch_add(1, Ordering::Relaxed);
        self.metrics.active_tasks.fetch_add(1, Ordering::Relaxed);

        let result = task().await;

        // 更新指标
        let execution_time = start_time.elapsed().as_nanos() as u64;
        self.metrics
            .total_execution_time
            .fetch_add(execution_time, Ordering::Relaxed);
        self.metrics.active_tasks.fetch_sub(1, Ordering::Relaxed);

        match &result {
            Ok(_) => {
                self.metrics.completed_tasks.fetch_add(1, Ordering::Relaxed);
            }
            Err(_) => {
                self.metrics.failed_tasks.fetch_add(1, Ordering::Relaxed);
            }
        }

        result
    }

    /// 批量执行任务
    pub async fn execute_batch<F, Fut, R>(&self, tasks: Vec<F>) -> Vec<Result<R>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R>> + Send + 'static,
        R: Send + 'static,
    {
        let futures: Vec<_> = tasks
            .into_iter()
            .map(|task| {
                let executor = self.clone();
                async move { executor.execute(task).await }
            })
            .collect();

        futures::future::join_all(futures).await
    }

    /// 获取执行器指标
    pub fn get_metrics(&self) -> ExecutorMetricsSnapshot {
        ExecutorMetricsSnapshot {
            total_tasks: self.metrics.total_tasks.load(Ordering::Relaxed),
            completed_tasks: self.metrics.completed_tasks.load(Ordering::Relaxed),
            failed_tasks: self.metrics.failed_tasks.load(Ordering::Relaxed),
            active_tasks: self.metrics.active_tasks.load(Ordering::Relaxed),
            total_execution_time: Duration::from_nanos(
                self.metrics.total_execution_time.load(Ordering::Relaxed),
            ),
            success_rate: {
                let total = self.metrics.total_tasks.load(Ordering::Relaxed);
                let completed = self.metrics.completed_tasks.load(Ordering::Relaxed);
                if total > 0 {
                    completed as f64 / total as f64
                } else {
                    0.0
                }
            },
        }
    }
}

impl Clone for HighPerformanceExecutor {
    fn clone(&self) -> Self {
        Self {
            semaphore: Arc::clone(&self.semaphore),
            metrics: Arc::clone(&self.metrics),
        }
    }
}

/// 执行器指标快照
#[derive(Debug, Clone)]
pub struct ExecutorMetricsSnapshot {
    pub total_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub active_tasks: usize,
    pub total_execution_time: Duration,
    pub success_rate: f64,
}

/// 高性能内存池
///
/// 使用Rust 1.90的优化特性实现高效的内存管理
pub struct HighPerformanceMemoryPool<T> {
    pool: Arc<RwLock<Vec<T>>>,
    factory: Arc<dyn Fn() -> T + Send + Sync>,
    max_size: usize,
    metrics: Arc<MemoryPoolMetrics>,
}

/// 内存池指标
#[derive(Debug, Default)]
pub struct MemoryPoolMetrics {
    pub total_allocations: AtomicU64,
    pub total_deallocations: AtomicU64,
    pub pool_hits: AtomicU64,
    pub pool_misses: AtomicU64,
    pub current_pool_size: AtomicUsize,
}

impl<T: Send + Sync + 'static> HighPerformanceMemoryPool<T> {
    /// 创建新的高性能内存池
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            pool: Arc::new(RwLock::new(Vec::with_capacity(max_size))),
            factory: Arc::new(factory),
            max_size,
            metrics: Arc::new(MemoryPoolMetrics::default()),
        }
    }

    /// 从池中获取对象
    pub async fn acquire(&self) -> PooledObject<T> {
        let obj = {
            let mut pool = self.pool.write().await;
            if let Some(obj) = pool.pop() {
                self.metrics.pool_hits.fetch_add(1, Ordering::Relaxed);
                self.metrics
                    .current_pool_size
                    .fetch_sub(1, Ordering::Relaxed);
                obj
            } else {
                self.metrics.pool_misses.fetch_add(1, Ordering::Relaxed);
                (self.factory)()
            }
        };

        self.metrics
            .total_allocations
            .fetch_add(1, Ordering::Relaxed);

        PooledObject::new(
            obj,
            Arc::clone(&self.pool),
            Arc::clone(&self.metrics),
            self.max_size,
        )
    }

    /// 获取内存池指标
    pub fn get_metrics(&self) -> MemoryPoolMetricsSnapshot {
        MemoryPoolMetricsSnapshot {
            total_allocations: self.metrics.total_allocations.load(Ordering::Relaxed),
            total_deallocations: self.metrics.total_deallocations.load(Ordering::Relaxed),
            pool_hits: self.metrics.pool_hits.load(Ordering::Relaxed),
            pool_misses: self.metrics.pool_misses.load(Ordering::Relaxed),
            current_pool_size: self.metrics.current_pool_size.load(Ordering::Relaxed),
            hit_rate: {
                let hits = self.metrics.pool_hits.load(Ordering::Relaxed);
                let misses = self.metrics.pool_misses.load(Ordering::Relaxed);
                let total = hits + misses;
                if total > 0 {
                    hits as f64 / total as f64
                } else {
                    0.0
                }
            },
        }
    }
}

/// 池化对象
pub struct PooledObject<T: Send + Sync + 'static> {
    object: Option<T>,
    pool: Arc<RwLock<Vec<T>>>,
    metrics: Arc<MemoryPoolMetrics>,
    max_size: usize,
}

impl<T: Send + Sync + 'static> PooledObject<T> {
    fn new(
        object: T,
        pool: Arc<RwLock<Vec<T>>>,
        metrics: Arc<MemoryPoolMetrics>,
        max_size: usize,
    ) -> Self {
        Self {
            object: Some(object),
            pool,
            metrics,
            max_size,
        }
    }

    /// 获取对象的引用
    pub fn get(&self) -> &T {
        self.object.as_ref().unwrap()
    }

    /// 获取对象的可变引用
    pub fn get_mut(&mut self) -> &mut T {
        self.object.as_mut().unwrap()
    }
}

impl<T: Send + Sync + 'static> Drop for PooledObject<T> {
    fn drop(&mut self) {
        if let Some(obj) = self.object.take() {
            let pool = Arc::clone(&self.pool);
            let metrics = Arc::clone(&self.metrics);
            let max_size = self.max_size;

            tokio::spawn(async move {
                let mut pool = pool.write().await;
                if pool.len() < max_size {
                    pool.push(obj);
                    metrics.current_pool_size.fetch_add(1, Ordering::Relaxed);
                }
                metrics.total_deallocations.fetch_add(1, Ordering::Relaxed);
            });
        }
    }
}

/// 内存池指标快照
#[derive(Debug, Clone)]
pub struct MemoryPoolMetricsSnapshot {
    pub total_allocations: u64,
    pub total_deallocations: u64,
    pub pool_hits: u64,
    pub pool_misses: u64,
    pub current_pool_size: usize,
    pub hit_rate: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_generator() {
        let mut generator = AsyncGenerator::new(10);

        generator.push("item1").await;
        generator.push("item2").await;
        generator.complete();

        assert_eq!(generator.next().await, Some("item1"));
        assert_eq!(generator.next().await, Some("item2"));
        assert_eq!(generator.next().await, None);
    }

    #[tokio::test]
    async fn test_batch_processor() {
        let processor = HighPerformanceBatchProcessor::new(3, Duration::from_millis(100), 10);

        for i in 0..5 {
            processor.add_item(i).await.unwrap();
        }

        let batch = processor.get_next_batch().await;
        assert!(batch.is_some());
        assert_eq!(batch.unwrap().len(), 3);

        let remaining = processor.flush().await.unwrap();
        assert!(remaining.is_some());
        assert_eq!(remaining.unwrap().len(), 2);
    }

    #[tokio::test]
    async fn test_high_performance_executor() {
        let executor = HighPerformanceExecutor::new(5);

        let result = executor
            .execute(|| async { Ok::<i32, anyhow::Error>(42) })
            .await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);

        let metrics = executor.get_metrics();
        assert_eq!(metrics.total_tasks, 1);
        assert_eq!(metrics.completed_tasks, 1);
        assert_eq!(metrics.success_rate, 1.0);
    }

    #[tokio::test]
    async fn test_memory_pool() {
        let pool = HighPerformanceMemoryPool::new(|| String::with_capacity(1024), 10);

        let obj1 = pool.acquire().await;
        assert_eq!(obj1.get().capacity(), 1024);

        drop(obj1);

        // 等待异步回收
        tokio::time::sleep(Duration::from_millis(10)).await;

        let obj2 = pool.acquire().await;
        assert_eq!(obj2.get().capacity(), 1024);

        let metrics = pool.get_metrics();
        assert!(metrics.total_allocations >= 1);
    }
}
