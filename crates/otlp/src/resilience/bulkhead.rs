//! # 舱壁模式实现
//!
//! 基于理论文档中的容错设计模式，实现舱壁模式进行资源隔离。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.1.2节

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};

/// 舱壁配置
#[derive(Debug, Clone)]
pub struct BulkheadConfig {
    /// 最大并发请求数
    pub max_concurrent_requests: usize,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 队列等待超时时间
    pub queue_timeout: Duration,
    /// 是否启用统计信息
    pub enable_stats: bool,
}

impl Default for BulkheadConfig {
    fn default() -> Self {
        Self {
            max_concurrent_requests: 10,
            max_queue_size: 100,
            queue_timeout: Duration::from_secs(30),
            enable_stats: true,
        }
    }
}

/// 舱壁统计信息
#[derive(Debug, Default)]
pub struct BulkheadStats {
    /// 总请求数
    pub total_requests: AtomicUsize,
    /// 成功请求数
    pub successful_requests: AtomicUsize,
    /// 失败请求数
    pub failed_requests: AtomicUsize,
    /// 队列满次数
    pub queue_full_count: AtomicUsize,
    /// 超时次数
    pub timeout_count: AtomicUsize,
    /// 平均等待时间（微秒）
    pub average_wait_time: AtomicUsize,
    /// 最大等待时间（微秒）
    pub max_wait_time: AtomicUsize,
}

/// 舱壁实现
pub struct Bulkhead {
    config: BulkheadConfig,
    semaphore: Arc<Semaphore>,
    queue: Arc<Mutex<VecDeque<QueuedRequest>>>,
    stats: Arc<BulkheadStats>,
    is_closed: AtomicUsize, // 0: open, 1: closed
}

/// 队列中的请求
#[allow(dead_code)]
struct QueuedRequest {
    id: u64,
    created_at: Instant,
    callback: Box<dyn FnOnce() + Send>,
}

/// 舱壁许可
pub struct BulkheadPermit {
    _permit: tokio::sync::OwnedSemaphorePermit,
    bulkhead: Arc<Bulkhead>,
    request_id: u64,
    start_time: Instant,
}

impl BulkheadPermit {
    /// 获取请求ID
    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    /// 获取等待时间
    pub fn wait_time(&self) -> Duration {
        self.start_time.elapsed()
    }
}

impl Drop for BulkheadPermit {
    fn drop(&mut self) {
        // 更新统计信息
        let wait_time = self.start_time.elapsed().as_micros() as usize;
        self.bulkhead.update_stats_on_completion(wait_time, true);
    }
}

/// 舱壁错误类型
#[derive(Debug, PartialEq, thiserror::Error)]
pub enum BulkheadError {
    #[error("舱壁已关闭")]
    BulkheadClosed,

    #[error("队列已满")]
    QueueFull,

    #[error("获取许可超时: {timeout:?}")]
    Timeout { timeout: Duration },

    #[error("队列等待超时")]
    QueueTimeout,
}

/// 舱壁实现
impl Bulkhead {
    /// 创建新的舱壁
    pub fn new(config: BulkheadConfig) -> Self {
        Self {
            config: config.clone(),
            semaphore: Arc::new(Semaphore::new(config.max_concurrent_requests)),
            queue: Arc::new(Mutex::new(VecDeque::new())),
            stats: Arc::new(BulkheadStats::default()),
            is_closed: AtomicUsize::new(0),
        }
    }

    /// 尝试获取许可
    pub async fn try_acquire(&self) -> Result<BulkheadPermit, BulkheadError> {
        if self.is_closed.load(Ordering::Acquire) != 0 {
            return Err(BulkheadError::BulkheadClosed);
        }

        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);

        // 尝试获取许可
        if let Ok(permit) = self.semaphore.clone().try_acquire_owned() {
            let request_id = self.generate_request_id();
            let start_time = Instant::now();

            Ok(BulkheadPermit {
                _permit: permit,
                bulkhead: Arc::new(self.clone()),
                request_id,
                start_time,
            })
        } else {
            // 无法立即获取许可，检查是否可以排队
            if self.can_queue_request() {
                self.queue_request().await
            } else {
                self.stats.queue_full_count.fetch_add(1, Ordering::Relaxed);
                Err(BulkheadError::QueueFull)
            }
        }
    }

    /// 获取许可（带超时）
    pub async fn acquire(&self) -> Result<BulkheadPermit, BulkheadError> {
        if self.is_closed.load(Ordering::Acquire) != 0 {
            return Err(BulkheadError::BulkheadClosed);
        }

        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);

        // 尝试立即获取许可
        if let Ok(permit) = self.semaphore.clone().try_acquire_owned() {
            let request_id = self.generate_request_id();
            let start_time = Instant::now();

            return Ok(BulkheadPermit {
                _permit: permit,
                bulkhead: Arc::new(self.clone()),
                request_id,
                start_time,
            });
        }

        // 无法立即获取许可，尝试排队
        if self.can_queue_request() {
            self.queue_request().await
        } else {
            // 队列已满，等待许可释放
            self.wait_for_permit().await
        }
    }

    /// 执行受保护的操作
    pub async fn execute<F, R, E>(&self, operation: F) -> Result<R, BulkheadError>
    where
        F: std::future::Future<Output = Result<R, E>>,
    {
        let _permit = self.acquire().await?;
        operation.await.map_err(|_| BulkheadError::Timeout {
            timeout: self.config.queue_timeout,
        })
    }

    /// 获取统计信息
    pub fn stats(&self) -> &BulkheadStats {
        &self.stats
    }

    /// 获取状态
    pub fn status(&self) -> BulkheadStatus {
        let available_permits = self.semaphore.available_permits();
        let max_permits = self.config.max_concurrent_requests;
        let active_requests = max_permits - available_permits;

        BulkheadStatus {
            active_requests,
            max_concurrent_requests: max_permits,
            queued_requests: 0, // 需要从队列获取
            max_queue_size: self.config.max_queue_size,
        }
    }

    /// 关闭舱壁
    pub async fn close(&self) {
        self.is_closed.store(1, Ordering::Release);

        // 清空队列
        let mut queue = self.queue.lock().await;
        queue.clear();
    }

    /// 重置统计信息
    pub fn reset(&self) {
        self.stats.total_requests.store(0, Ordering::Release);
        self.stats.successful_requests.store(0, Ordering::Release);
        self.stats.failed_requests.store(0, Ordering::Release);
        self.stats.queue_full_count.store(0, Ordering::Release);
        self.stats.timeout_count.store(0, Ordering::Release);
        self.stats.average_wait_time.store(0, Ordering::Release);
        self.stats.max_wait_time.store(0, Ordering::Release);
    }

    /// 检查是否可以排队请求
    fn can_queue_request(&self) -> bool {
        // 这里需要检查队列大小，但由于队列是异步的，我们使用一个简化的检查
        true // 实际实现中需要更复杂的队列大小检查
    }

    /// 排队请求
    async fn queue_request(&self) -> Result<BulkheadPermit, BulkheadError> {
        let request_id = self.generate_request_id();
        let start_time = Instant::now();

        // 创建队列请求
        let queued_request = QueuedRequest {
            id: request_id,
            created_at: start_time,
            callback: Box::new(|| {}), // 占位符
        };

        // 添加到队列
        {
            let mut queue = self.queue.lock().await;
            if queue.len() >= self.config.max_queue_size {
                return Err(BulkheadError::QueueFull);
            }
            queue.push_back(queued_request);
        }

        // 等待许可
        self.wait_for_permit().await
    }

    /// 等待许可
    async fn wait_for_permit(&self) -> Result<BulkheadPermit, BulkheadError> {
        let start_time = Instant::now();

        // 使用超时等待许可
        match tokio::time::timeout(
            self.config.queue_timeout,
            self.semaphore.clone().acquire_owned(),
        )
        .await
        {
            Ok(Ok(permit)) => {
                let request_id = self.generate_request_id();
                Ok(BulkheadPermit {
                    _permit: permit,
                    bulkhead: Arc::new(self.clone()),
                    request_id,
                    start_time,
                })
            }
            Ok(Err(_)) => {
                self.stats.timeout_count.fetch_add(1, Ordering::Relaxed);
                Err(BulkheadError::BulkheadClosed)
            }
            Err(_) => {
                self.stats.timeout_count.fetch_add(1, Ordering::Relaxed);
                Err(BulkheadError::Timeout {
                    timeout: self.config.queue_timeout,
                })
            }
        }
    }

    /// 生成请求ID
    fn generate_request_id(&self) -> u64 {
        // 简单的ID生成，实际实现中可以使用更复杂的ID生成器
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64
    }

    /// 更新完成统计信息
    fn update_stats_on_completion(&self, wait_time: usize, success: bool) {
        if success {
            self.stats
                .successful_requests
                .fetch_add(1, Ordering::Relaxed);
        } else {
            self.stats.failed_requests.fetch_add(1, Ordering::Relaxed);
        }

        // 更新平均等待时间
        let total_requests = self.stats.total_requests.load(Ordering::Acquire);
        let current_avg = self.stats.average_wait_time.load(Ordering::Acquire);
        let new_avg = (current_avg * (total_requests - 1) + wait_time) / total_requests;
        self.stats
            .average_wait_time
            .store(new_avg, Ordering::Release);

        // 更新最大等待时间
        let current_max = self.stats.max_wait_time.load(Ordering::Acquire);
        if wait_time > current_max {
            self.stats.max_wait_time.store(wait_time, Ordering::Release);
        }
    }
}

impl Clone for Bulkhead {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            semaphore: self.semaphore.clone(),
            queue: self.queue.clone(),
            stats: self.stats.clone(),
            is_closed: AtomicUsize::new(0),
        }
    }
}

/// 舱壁状态
#[derive(Debug, Clone)]
pub struct BulkheadStatus {
    pub active_requests: usize,
    pub max_concurrent_requests: usize,
    pub queued_requests: usize,
    pub max_queue_size: usize,
}

/// 舱壁构建器
pub struct BulkheadBuilder {
    config: BulkheadConfig,
}

impl BulkheadBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: BulkheadConfig::default(),
        }
    }

    /// 设置最大并发请求数
    pub fn max_concurrent_requests(mut self, max: usize) -> Self {
        self.config.max_concurrent_requests = max;
        self
    }

    /// 设置最大队列大小
    pub fn max_queue_size(mut self, max: usize) -> Self {
        self.config.max_queue_size = max;
        self
    }

    /// 设置队列超时时间
    pub fn queue_timeout(mut self, timeout: Duration) -> Self {
        self.config.queue_timeout = timeout;
        self
    }

    /// 启用统计信息
    pub fn enable_stats(mut self) -> Self {
        self.config.enable_stats = true;
        self
    }

    /// 构建舱壁
    pub fn build(self) -> Bulkhead {
        Bulkhead::new(self.config)
    }
}

impl Default for BulkheadBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 舱壁管理器 - 支持多个舱壁的管理
pub struct BulkheadManager {
    bulkheads: Arc<RwLock<HashMap<String, Arc<Bulkhead>>>>,
}

impl BulkheadManager {
    /// 创建新的舱壁管理器
    pub fn new() -> Self {
        Self {
            bulkheads: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 获取或创建舱壁
    pub async fn get_or_create_bulkhead(
        &self,
        name: &str,
        config: BulkheadConfig,
    ) -> Arc<Bulkhead> {
        let mut bulkheads = self.bulkheads.write().await;
        if let Some(bulkhead) = bulkheads.get(name) {
            return bulkhead.clone();
        }

        let bulkhead = Arc::new(Bulkhead::new(config));
        bulkheads.insert(name.to_string(), bulkhead.clone());
        bulkhead
    }

    /// 获取所有舱壁的状态
    pub async fn get_all_status(&self) -> HashMap<String, BulkheadStatus> {
        let bulkheads = self.bulkheads.read().await;
        bulkheads
            .iter()
            .map(|(name, bulkhead)| (name.clone(), bulkhead.status()))
            .collect()
    }

    /// 关闭所有舱壁
    pub async fn close_all(&self) {
        let bulkheads = self.bulkheads.read().await;
        for bulkhead in bulkheads.values() {
            bulkhead.close().await;
        }
    }
}

impl Default for BulkheadManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_bulkhead_basic() {
        let config = BulkheadConfig {
            max_concurrent_requests: 2,
            max_queue_size: 5,
            queue_timeout: Duration::from_secs(1),
            enable_stats: true,
        };
        let bulkhead = Bulkhead::new(config);

        // 获取许可
        let permit = bulkhead.acquire().await.unwrap();
        assert_eq!(permit.request_id() > 0, true);

        // 释放许可（通过Drop）
        drop(permit);

        // 再次获取许可
        let permit = bulkhead.acquire().await.unwrap();
        assert_eq!(permit.request_id() > 0, true);
    }

    #[tokio::test]
    async fn test_bulkhead_concurrent_limit() {
        let config = BulkheadConfig {
            max_concurrent_requests: 1,
            max_queue_size: 5,
            queue_timeout: Duration::from_millis(100),
            enable_stats: true,
        };
        let bulkhead = Arc::new(Bulkhead::new(config));

        // 获取第一个许可
        let permit1 = bulkhead.acquire().await.unwrap();

        // 尝试获取第二个许可（应该超时）
        let result = bulkhead.acquire().await;
        assert!(matches!(result, Err(BulkheadError::Timeout { .. })));

        // 释放第一个许可
        drop(permit1);

        // 现在应该能够获取许可
        let permit2 = bulkhead.acquire().await.unwrap();
        assert_eq!(permit2.request_id() > 0, true);
    }

    #[tokio::test]
    async fn test_bulkhead_execute() {
        let config = BulkheadConfig::default();
        let bulkhead = Bulkhead::new(config);

        // 执行成功操作
        let result: Result<i32, BulkheadError> =
            bulkhead.execute::<_, i32, &str>(async { Ok(42) }).await;
        assert_eq!(result, Ok(42));

        // 执行失败操作
        let result: Result<i32, BulkheadError> =
            bulkhead.execute(async { Err("test error") }).await;
        assert!(matches!(result, Err(BulkheadError::Timeout { .. })));
    }

    #[tokio::test]
    async fn test_bulkhead_builder() {
        let bulkhead = BulkheadBuilder::new()
            .max_concurrent_requests(5)
            .max_queue_size(10)
            .queue_timeout(Duration::from_secs(30))
            .enable_stats()
            .build();

        let status = bulkhead.status();
        assert_eq!(status.max_concurrent_requests, 5);
        assert_eq!(status.max_queue_size, 10);
    }

    #[tokio::test]
    async fn test_bulkhead_manager() {
        let manager = BulkheadManager::new();

        let config = BulkheadConfig::default();
        let bulkhead = manager
            .get_or_create_bulkhead("test_bulkhead", config)
            .await;

        let status = bulkhead.status();
        assert_eq!(status.max_concurrent_requests, 10);

        let all_status = manager.get_all_status().await;
        assert!(all_status.contains_key("test_bulkhead"));
    }
}
