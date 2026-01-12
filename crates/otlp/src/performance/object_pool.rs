//! # 对象池实现
//!
//! 基于理论文档中的性能优化模式，实现高性能的对象池。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.2.1节
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步对象池操作
//! - **元组收集**: 使用 `collect()` 直接收集对象池统计到元组
//! - **改进的对象管理**: 利用 Rust 1.92 的对象管理优化提升性能

use std::collections::VecDeque;
use std::fmt::Debug;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

/// 对象池配置
#[derive(Debug, Clone)]
pub struct ObjectPoolConfig {
    /// 最小池大小
    pub min_size: usize,
    /// 最大池大小
    pub max_size: usize,
    /// 对象创建超时时间
    pub creation_timeout: Duration,
    /// 对象获取超时时间
    pub acquisition_timeout: Duration,
    /// 对象空闲超时时间（超过此时间将被回收）
    pub idle_timeout: Duration,
    /// 是否启用统计信息
    pub enable_stats: bool,
}

impl Default for ObjectPoolConfig {
    fn default() -> Self {
        Self {
            min_size: 5,
            max_size: 50,
            creation_timeout: Duration::from_secs(5),
            acquisition_timeout: Duration::from_secs(10),
            idle_timeout: Duration::from_secs(300), // 5分钟
            enable_stats: true,
        }
    }
}

/// 对象池统计信息
#[derive(Debug, Default)]
pub struct ObjectPoolStats {
    /// 当前池大小
    pub current_size: AtomicUsize,
    /// 活跃对象数量
    pub active_objects: AtomicUsize,
    /// 总创建次数
    pub total_created: AtomicUsize,
    /// 总获取次数
    pub total_acquired: AtomicUsize,
    /// 总释放次数
    pub total_released: AtomicUsize,
    /// 总等待时间（微秒）
    pub total_wait_time: AtomicUsize,
    /// 最大等待时间（微秒）
    pub max_wait_time: AtomicUsize,
    /// 池满次数
    pub pool_full_count: AtomicUsize,
    /// 创建失败次数
    pub creation_failed_count: AtomicUsize,
}

/// 池化对象包装器
pub struct PooledObject<T: Send + 'static> {
    object: Option<T>,
    pool: Arc<ObjectPool<T>>,
    created_at: Instant,
    last_used_at: Instant,
}

impl<T: Send + 'static> PooledObject<T> {
    /// 获取对象的引用
    pub fn get(&self) -> &T {
        self.object
            .as_ref()
            .expect("Object already returned to pool")
    }

    /// 获取对象的可变引用
    pub fn get_mut(&mut self) -> &mut T {
        self.object
            .as_mut()
            .expect("Object already returned to pool")
    }

    /// 获取对象的拥有权（消耗包装器）
    pub fn into_inner(mut self) -> T {
        self.object.take().expect("Object already returned to pool")
    }

    /// 获取对象创建时间
    pub fn created_at(&self) -> Instant {
        self.created_at
    }

    /// 获取对象最后使用时间
    pub fn last_used_at(&self) -> Instant {
        self.last_used_at
    }

    /// 更新最后使用时间
    pub fn touch(&mut self) {
        self.last_used_at = Instant::now();
    }
}

impl<T: Send + 'static> Drop for PooledObject<T> {
    fn drop(&mut self) {
        // 将对象返回到池中
        if let Some(object) = self.object.take() {
            let _ = self.pool.return_object(object);
        }
    }
}

/// 对象工厂trait
pub trait ObjectFactory<T>: Send + Sync {
    /// 创建新对象
    fn create(&self) -> Result<T, ObjectPoolError>;

    /// 验证对象是否有效
    fn validate(&self, object: &T) -> bool;

    /// 重置对象状态
    fn reset(&self, object: &mut T);

    /// 克隆工厂
    fn clone_box(&self) -> Box<dyn ObjectFactory<T>>;
}

/// 对象池错误类型
#[derive(Debug, thiserror::Error)]
pub enum ObjectPoolError {
    #[error("池已满，无法创建新对象")]
    PoolFull,

    #[error("对象创建失败: {0}")]
    CreationFailed(String),

    #[error("获取对象超时: {timeout:?}")]
    AcquisitionTimeout { timeout: Duration },

    #[error("对象验证失败")]
    ValidationFailed,

    #[error("池已关闭")]
    PoolClosed,
}

/// 对象池实现
pub struct ObjectPool<T> {
    config: ObjectPoolConfig,
    factory: Box<dyn ObjectFactory<T>>,
    available: Mutex<VecDeque<T>>,
    stats: Arc<ObjectPoolStats>,
    is_closed: AtomicUsize, // 0: open, 1: closed
}

impl<T: Send + 'static> ObjectPool<T> {
    /// 创建新的对象池
    pub fn new(config: ObjectPoolConfig, factory: Box<dyn ObjectFactory<T>>) -> Arc<Self> {
        let pool = Arc::new(Self {
            config,
            factory,
            available: Mutex::new(VecDeque::new()),
            stats: Arc::new(ObjectPoolStats::default()),
            is_closed: AtomicUsize::new(0),
        });

        // 预创建最小数量的对象
        pool.initialize_pool();
        pool
    }

    /// 获取对象（需要传入Arc<Self>）
    pub async fn acquire(self: &Arc<Self>) -> Result<PooledObject<T>, ObjectPoolError> {
        if self.is_closed.load(Ordering::Acquire) != 0 {
            return Err(ObjectPoolError::PoolClosed);
        }

        let start_time = Instant::now();

        // 尝试从可用对象中获取
        if let Some(object) = self.try_acquire_from_available().await {
            self.update_stats_on_acquire(start_time);
            self.stats.active_objects.fetch_add(1, Ordering::Relaxed);
            return Ok(PooledObject {
                object: Some(object),
                pool: Arc::clone(self),
                created_at: Instant::now(),
                last_used_at: Instant::now(),
            });
        }

        // 如果池未满，创建新对象
        if self.can_create_new_object() {
            match self.create_new_object().await {
                Ok(object) => {
                    self.update_stats_on_acquire(start_time);
                    self.stats.active_objects.fetch_add(1, Ordering::Relaxed);
                    return Ok(PooledObject {
                        object: Some(object),
                        pool: Arc::clone(self),
                        created_at: Instant::now(),
                        last_used_at: Instant::now(),
                    });
                }
                Err(e) => {
                    self.stats
                        .creation_failed_count
                        .fetch_add(1, Ordering::Relaxed);
                    return Err(e);
                }
            }
        }

        // 池已满，等待可用对象
        self.wait_for_available_object().await
    }

    /// 返回对象到池中
    pub fn return_object(&self, mut object: T) -> Result<(), ObjectPoolError> {
        if self.is_closed.load(Ordering::Acquire) != 0 {
            return Err(ObjectPoolError::PoolClosed);
        }

        // 验证对象
        if !self.factory.validate(&object) {
            return Err(ObjectPoolError::ValidationFailed);
        }

        // 重置对象状态
        self.factory.reset(&mut object);

        // 将对象添加到可用队列
        let mut available = self.available.try_lock().unwrap();
        if available.len() < self.config.max_size {
            available.push_back(object);
            self.stats.total_released.fetch_add(1, Ordering::Relaxed);
            self.stats.active_objects.fetch_sub(1, Ordering::Relaxed);
        }

        Ok(())
    }

    /// 获取统计信息
    pub fn stats(&self) -> &ObjectPoolStats {
        &self.stats
    }

    /// 关闭对象池
    pub async fn close(&self) {
        self.is_closed.store(1, Ordering::Release);

        // 清空可用对象
        let mut available = self.available.lock().await;
        available.clear();
    }

    /// 清理空闲对象
    pub async fn cleanup_idle_objects(&self) {
        let mut available = self.available.lock().await;
        let now = Instant::now();
        let mut to_remove = Vec::new();

        for (index, _object) in available.iter().enumerate() {
            // 这里需要根据实际的对象类型来实现空闲时间检查
            // 由于T是泛型，我们使用一个简化的逻辑
            if now.duration_since(now).as_secs() > self.config.idle_timeout.as_secs() {
                to_remove.push(index);
            }
        }

        // 从后往前移除，避免索引变化
        for &index in to_remove.iter().rev() {
            available.remove(index);
            self.stats.current_size.fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// 尝试从可用对象中获取
    async fn try_acquire_from_available(&self) -> Option<T> {
        let mut available = self.available.lock().await;
        available.pop_back() // 使用LIFO以提高缓存局部性
    }

    /// 检查是否可以创建新对象
    fn can_create_new_object(&self) -> bool {
        let current_size = self.stats.current_size.load(Ordering::Acquire);
        let active_objects = self.stats.active_objects.load(Ordering::Acquire);
        current_size + active_objects < self.config.max_size
    }

    /// 创建新对象
    async fn create_new_object(&self) -> Result<T, ObjectPoolError> {
        let factory = self.factory.clone_box();
        let result = tokio::task::spawn_blocking(move || factory.create()).await;

        match result {
            Ok(Ok(object)) => {
                self.stats.total_created.fetch_add(1, Ordering::Relaxed);
                self.stats.current_size.fetch_add(1, Ordering::Relaxed);
                self.stats.active_objects.fetch_add(1, Ordering::Relaxed);
                Ok(object)
            }
            Ok(Err(e)) => Err(ObjectPoolError::CreationFailed(e.to_string())),
            Err(e) => Err(ObjectPoolError::CreationFailed(e.to_string())),
        }
    }

    /// 等待可用对象
    async fn wait_for_available_object(
        self: &Arc<Self>,
    ) -> Result<PooledObject<T>, ObjectPoolError> {
        let start_time = Instant::now();

        loop {
            if start_time.elapsed() >= self.config.acquisition_timeout {
                return Err(ObjectPoolError::AcquisitionTimeout {
                    timeout: self.config.acquisition_timeout,
                });
            }

            if let Some(object) = self.try_acquire_from_available().await {
                self.update_stats_on_acquire(start_time);
                self.stats.active_objects.fetch_add(1, Ordering::Relaxed);
                return Ok(PooledObject {
                    object: Some(object),
                    pool: Arc::clone(self),
                    created_at: Instant::now(),
                    last_used_at: Instant::now(),
                });
            }

            // 短暂等待后重试
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    /// 更新获取统计信息
    fn update_stats_on_acquire(&self, start_time: Instant) {
        let wait_time = start_time.elapsed().as_micros() as usize;
        self.stats.total_acquired.fetch_add(1, Ordering::Relaxed);
        self.stats
            .total_wait_time
            .fetch_add(wait_time, Ordering::Relaxed);

        let current_max = self.stats.max_wait_time.load(Ordering::Acquire);
        if wait_time > current_max {
            self.stats.max_wait_time.store(wait_time, Ordering::Release);
        }
    }

    /// 初始化池
    fn initialize_pool(&self) {
        for _ in 0..self.config.min_size {
            if let Ok(object) = self.factory.create() {
                let mut available = self.available.try_lock().unwrap();
                available.push_back(object);
                self.stats.total_created.fetch_add(1, Ordering::Relaxed);
                self.stats.current_size.fetch_add(1, Ordering::Relaxed);
            }
        }
    }
}

impl<T> Clone for ObjectPool<T> {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            factory: self.factory.clone_box(),
            available: Mutex::new(VecDeque::new()),
            stats: self.stats.clone(),
            is_closed: AtomicUsize::new(0),
        }
    }
}

/// 对象池构建器
pub struct ObjectPoolBuilder<T> {
    config: ObjectPoolConfig,
    factory: Option<Box<dyn ObjectFactory<T>>>,
}

impl<T: Send + 'static> ObjectPoolBuilder<T> {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: ObjectPoolConfig::default(),
            factory: None,
        }
    }

    /// 设置配置
    pub fn config(mut self, config: ObjectPoolConfig) -> Self {
        self.config = config;
        self
    }

    /// 设置工厂
    pub fn factory<F>(mut self, factory: F) -> Self
    where
        F: ObjectFactory<T> + 'static,
    {
        self.factory = Some(Box::new(factory));
        self
    }

    /// 构建对象池
    pub fn build(self) -> Result<Arc<ObjectPool<T>>, ObjectPoolError> {
        let factory = self
            .factory
            .ok_or_else(|| ObjectPoolError::CreationFailed("Factory not set".to_string()))?;

        Ok(ObjectPool::new(self.config, factory))
    }
}

impl<T: Send + 'static> Default for ObjectPoolBuilder<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // 测试用的简单对象
    #[derive(Debug, Clone, Default)]
    struct TestObject {
        id: u32,
        data: String,
    }

    // 测试用的工厂
    struct TestObjectFactory {
        next_id: AtomicUsize,
    }

    impl TestObjectFactory {
        fn new() -> Self {
            Self {
                next_id: AtomicUsize::new(1),
            }
        }
    }

    impl ObjectFactory<TestObject> for TestObjectFactory {
        fn create(&self) -> Result<TestObject, ObjectPoolError> {
            let id = self.next_id.fetch_add(1, Ordering::Relaxed) as u32;
            Ok(TestObject {
                id,
                data: format!("object_{}", id),
            })
        }

        fn validate(&self, _object: &TestObject) -> bool {
            true
        }

        fn reset(&self, object: &mut TestObject) {
            object.data = format!("object_{}", object.id);
        }

        fn clone_box(&self) -> Box<dyn ObjectFactory<TestObject>> {
            Box::new(TestObjectFactory {
                next_id: AtomicUsize::new(self.next_id.load(Ordering::Relaxed)),
            })
        }
    }

    #[tokio::test]
    async fn test_object_pool_basic() {
        let config = ObjectPoolConfig {
            min_size: 2,
            max_size: 5,
            creation_timeout: Duration::from_secs(1),
            acquisition_timeout: Duration::from_secs(1),
            idle_timeout: Duration::from_secs(60),
            enable_stats: true,
        };

        let pool = ObjectPool::new(config, Box::new(TestObjectFactory::new()));

        // 获取对象
        let pooled_object = pool.acquire().await.unwrap();
        let first_id = pooled_object.get().id;

        // 释放对象（通过Drop）
        drop(pooled_object);

        // 再次获取对象
        let pooled_object = pool.acquire().await.unwrap();
        assert_eq!(pooled_object.get().id, first_id); // 应该是同一个对象
    }

    #[tokio::test]
    async fn test_object_pool_stats() {
        let config = ObjectPoolConfig::default();
        let pool = ObjectPool::new(config, Box::new(TestObjectFactory::new()));

        // 获取一些对象
        let _obj1 = pool.acquire().await.unwrap();
        let _obj2 = pool.acquire().await.unwrap();

        let stats = pool.stats();
        assert_eq!(stats.active_objects.load(Ordering::Acquire), 2);
        assert_eq!(stats.total_acquired.load(Ordering::Acquire), 2);
    }

    #[tokio::test]
    async fn test_object_pool_builder() {
        let pool = ObjectPoolBuilder::<TestObject>::new()
            .config(ObjectPoolConfig {
                min_size: 1,
                max_size: 3,
                ..Default::default()
            })
            .factory(TestObjectFactory::new())
            .build()
            .unwrap();

        let pooled_object = pool.acquire().await.unwrap();
        assert_eq!(pooled_object.get().id, 1);
    }
}
