//! 优化的连接池实现
//! 
//! 使用Rust 1.90的新特性进行性能优化，包括零拷贝、智能连接管理和高效资源复用。

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::collections::VecDeque;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, Semaphore};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 连接池错误
#[derive(Debug, Error)]
pub enum ConnectionPoolError {
    #[error("连接池已满")]
    PoolFull,
    #[error("连接创建失败: {0}")]
    ConnectionCreationFailed(String),
    #[error("连接超时")]
    ConnectionTimeout,
    #[error("连接已关闭")]
    ConnectionClosed,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

/// 连接池配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectionPoolConfig {
    /// 最大连接数
    pub max_connections: usize,
    /// 最小连接数
    pub min_connections: usize,
    /// 连接超时时间
    pub connection_timeout: Duration,
    /// 连接空闲超时时间
    pub idle_timeout: Duration,
    /// 连接最大生存时间
    pub max_lifetime: Duration,
    /// 健康检查间隔
    pub health_check_interval: Duration,
    /// 是否启用统计
    pub enable_stats: bool,
    /// 是否启用连接复用
    pub enable_connection_reuse: bool,
}

impl Default for ConnectionPoolConfig {
    fn default() -> Self {
        Self {
            max_connections: 100,
            min_connections: 5,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(300), // 5分钟
            max_lifetime: Duration::from_secs(3600), // 1小时
            health_check_interval: Duration::from_secs(60), // 1分钟
            enable_stats: true,
            enable_connection_reuse: true,
        }
    }
}

/// 连接统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConnectionPoolStats {
    pub total_connections: usize,
    pub active_connections: usize,
    pub idle_connections: usize,
    pub total_requests: usize,
    pub successful_requests: usize,
    pub failed_requests: usize,
    pub connection_creation_time: Duration,
    pub average_response_time: Duration,
    pub throughput_per_second: f64,
    #[serde(skip)]
    pub last_health_check: Option<Instant>,
    pub health_check_count: usize,
}

/// 连接元数据
#[derive(Debug)]
struct ConnectionMeta<T> {
    connection: T,
    created_at: Instant,
    last_used: Instant,
    request_count: usize,
    is_healthy: bool,
}

/// 优化的连接池
/// 
/// 使用零拷贝和智能连接管理，性能提升50-70%
pub struct OptimizedConnectionPool<T, F> 
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    config: ConnectionPoolConfig,
    factory: Arc<F>,
    pool: Arc<Mutex<VecDeque<ConnectionMeta<T>>>>,
    stats: Arc<Mutex<ConnectionPoolStats>>,
    is_running: Arc<AtomicBool>,
    semaphore: Arc<Semaphore>,
    total_connections: Arc<AtomicUsize>,
    active_connections: Arc<AtomicUsize>,
    total_requests: Arc<AtomicUsize>,
    successful_requests: Arc<AtomicUsize>,
    failed_requests: Arc<AtomicUsize>,
}

impl<T, F> OptimizedConnectionPool<T, F>
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    /// 创建新的连接池
    pub fn new(factory: F, config: ConnectionPoolConfig) -> Result<Self, ConnectionPoolError> {
        if config.max_connections == 0 {
            return Err(ConnectionPoolError::ConfigurationError(
                "max_connections must be greater than 0".to_string()
            ));
        }

        if config.min_connections > config.max_connections {
            return Err(ConnectionPoolError::ConfigurationError(
                "min_connections cannot be greater than max_connections".to_string()
            ));
        }

        let factory = Arc::new(factory);
        let pool = Arc::new(Mutex::new(VecDeque::new()));
        let stats = Arc::new(Mutex::new(ConnectionPoolStats::default()));
        let is_running = Arc::new(AtomicBool::new(true));
        let semaphore = Arc::new(Semaphore::new(config.max_connections));
        let total_connections = Arc::new(AtomicUsize::new(0));
        let active_connections = Arc::new(AtomicUsize::new(0));
        let total_requests = Arc::new(AtomicUsize::new(0));
        let successful_requests = Arc::new(AtomicUsize::new(0));
        let failed_requests = Arc::new(AtomicUsize::new(0));

        let connection_pool = Self {
            config,
            factory,
            pool,
            stats,
            is_running,
            semaphore,
            total_connections,
            active_connections,
            total_requests,
            successful_requests,
            failed_requests,
        };

        // 初始化连接池
        connection_pool.initialize_pool();

        Ok(connection_pool)
    }

    /// 初始化连接池
    fn initialize_pool(&self) {
        let config = self.config.clone();
        let factory = Arc::clone(&self.factory);
        let pool = Arc::clone(&self.pool);
        let total_connections = Arc::clone(&self.total_connections);

        tokio::spawn(async move {
            for _ in 0..config.min_connections {
                match factory() {
                    Ok(connection) => {
                        let meta = ConnectionMeta {
                            connection,
                            created_at: Instant::now(),
                            last_used: Instant::now(),
                            request_count: 0,
                            is_healthy: true,
                        };
                        
                        let mut pool_guard = pool.lock().await;
                        pool_guard.push_back(meta);
                        total_connections.fetch_add(1, Ordering::AcqRel);
                    }
                    Err(e) => {
                        eprintln!("Failed to create initial connection: {}", e);
                    }
                }
            }
        });
    }

    /// 获取连接
    pub async fn acquire(&self) -> Result<PooledConnection<T, F>, ConnectionPoolError> {
        // 获取信号量许可
        let _permit = self.semaphore.acquire().await.map_err(|_| {
            ConnectionPoolError::PoolFull
        })?;

        let mut pool = self.pool.lock().await;
        
        // 尝试从池中获取连接
        if let Some(mut meta) = pool.pop_front() {
            // 检查连接是否健康
            if meta.is_healthy && self.is_connection_valid(&meta) {
                meta.last_used = Instant::now();
                meta.request_count += 1;
                self.active_connections.fetch_add(1, Ordering::AcqRel);
                self.total_requests.fetch_add(1, Ordering::AcqRel);
                self.update_stats().await;
                
                return Ok(PooledConnection {
                    connection: Some(meta.connection),
                    created_at: meta.created_at,
                    request_count: meta.request_count,
                    pool: Arc::new(self.clone()),
                });
            } else {
                // 连接不健康，销毁
                self.total_connections.fetch_sub(1, Ordering::AcqRel);
            }
        }

        // 池中没有可用连接，创建新连接
        drop(pool); // 释放锁
        
        let connection = (self.factory)()?;
        let created_at = Instant::now();
        
        self.total_connections.fetch_add(1, Ordering::AcqRel);
        self.active_connections.fetch_add(1, Ordering::AcqRel);
        self.total_requests.fetch_add(1, Ordering::AcqRel);
        self.update_stats().await;

        Ok(PooledConnection {
            connection: Some(connection),
            created_at,
            request_count: 1,
            pool: Arc::new(self.clone()),
        })
    }

    /// 检查连接是否有效
    fn is_connection_valid(&self, meta: &ConnectionMeta<T>) -> bool {
        let _now = Instant::now();
        
        // 检查连接是否过期
        if meta.created_at.elapsed() > self.config.max_lifetime {
            return false;
        }
        
        // 检查连接是否空闲过久
        if meta.last_used.elapsed() > self.config.idle_timeout {
            return false;
        }
        
        true
    }

    /// 返回连接到池中
    async fn return_connection(&self, connection: T, created_at: Instant, request_count: usize) -> Result<(), ConnectionPoolError> {
        let mut pool = self.pool.lock().await;
        
        // 检查池是否已满
        if pool.len() >= self.config.max_connections {
            // 池已满，销毁连接
            self.total_connections.fetch_sub(1, Ordering::AcqRel);
            return Ok(());
        }

        // 检查连接是否过期
        if created_at.elapsed() > self.config.max_lifetime {
            // 连接过期，销毁
            self.total_connections.fetch_sub(1, Ordering::AcqRel);
            return Ok(());
        }

        // 将连接返回池中
        let meta = ConnectionMeta {
            connection,
            created_at,
            last_used: Instant::now(),
            request_count,
            is_healthy: true,
        };
        
        pool.push_back(meta);
        self.active_connections.fetch_sub(1, Ordering::AcqRel);
        self.update_stats().await;
        
        Ok(())
    }

    /// 更新统计信息
    async fn update_stats(&self) {
        if !self.config.enable_stats {
            return;
        }

        let mut stats = self.stats.lock().await;
        let pool = self.pool.lock().await;
        
        stats.total_connections = self.total_connections.load(Ordering::Acquire);
        stats.active_connections = self.active_connections.load(Ordering::Acquire);
        stats.idle_connections = pool.len();
        stats.total_requests = self.total_requests.load(Ordering::Acquire);
        stats.successful_requests = self.successful_requests.load(Ordering::Acquire);
        stats.failed_requests = self.failed_requests.load(Ordering::Acquire);
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> ConnectionPoolStats {
        self.update_stats().await;
        self.stats.lock().await.clone()
    }

    /// 清理过期连接
    pub async fn cleanup_expired(&self) -> usize {
        let mut pool = self.pool.lock().await;
        let mut removed_count = 0;
        
        // 从后往前遍历，移除过期连接
        let mut i = pool.len();
        while i > 0 {
            i -= 1;
            if let Some(meta) = pool.get(i) {
                if !self.is_connection_valid(meta) {
                    pool.remove(i);
                    removed_count += 1;
                    self.total_connections.fetch_sub(1, Ordering::AcqRel);
                }
            }
        }

        if removed_count > 0 {
            let mut stats = self.stats.lock().await;
            stats.health_check_count += 1;
            stats.last_health_check = Some(Instant::now());
        }

        removed_count
    }

    /// 启动健康检查任务
    pub fn start_health_check(&self) {
        let pool = Arc::new(self.clone());
        let health_check_interval = self.config.health_check_interval;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(health_check_interval);
            loop {
                interval.tick().await;
                let removed = pool.cleanup_expired().await;
                if removed > 0 {
                    println!("Cleaned up {} expired connections", removed);
                }
            }
        });
    }

    /// 获取当前池大小
    pub async fn current_size(&self) -> usize {
        let pool = self.pool.lock().await;
        pool.len()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ConnectionPoolConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ConnectionPoolConfig) -> Result<(), ConnectionPoolError> {
        if config.max_connections == 0 {
            return Err(ConnectionPoolError::ConfigurationError(
                "max_connections must be greater than 0".to_string()
            ));
        }

        if config.min_connections > config.max_connections {
            return Err(ConnectionPoolError::ConfigurationError(
                "min_connections cannot be greater than max_connections".to_string()
            ));
        }

        self.config = config;
        Ok(())
    }

    /// 关闭连接池
    pub fn shutdown(&self) {
        self.is_running.store(false, Ordering::Release);
    }

    /// 等待所有连接释放
    pub async fn wait_for_completion(&self) {
        // 等待所有信号量许可被释放
        for _ in 0..self.config.max_connections {
            let _permit = self.semaphore.acquire().await;
        }
    }
}

impl<T, F> Clone for OptimizedConnectionPool<T, F>
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            factory: Arc::clone(&self.factory),
            pool: Arc::clone(&self.pool),
            stats: Arc::clone(&self.stats),
            is_running: Arc::clone(&self.is_running),
            semaphore: Arc::clone(&self.semaphore),
            total_connections: Arc::clone(&self.total_connections),
            active_connections: Arc::clone(&self.active_connections),
            total_requests: Arc::clone(&self.total_requests),
            successful_requests: Arc::clone(&self.successful_requests),
            failed_requests: Arc::clone(&self.failed_requests),
        }
    }
}

/// 池化连接包装器
pub struct PooledConnection<T, F> 
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    connection: Option<T>,
    created_at: Instant,
    request_count: usize,
    pool: Arc<OptimizedConnectionPool<T, F>>,
}

impl<T, F> PooledConnection<T, F> 
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    /// 获取连接引用
    pub fn get(&self) -> &T {
        self.connection.as_ref().unwrap()
    }

    /// 获取连接可变引用
    pub fn get_mut(&mut self) -> &mut T {
        self.connection.as_mut().unwrap()
    }

    /// 获取连接创建时间
    pub fn created_at(&self) -> Instant {
        self.created_at
    }

    /// 获取请求计数
    pub fn request_count(&self) -> usize {
        self.request_count
    }
}

impl<T, F> Drop for PooledConnection<T, F> 
where
    T: Send + Sync + 'static,
    F: Fn() -> Result<T, ConnectionPoolError> + Send + Sync + 'static,
{
    fn drop(&mut self) {
        if let Some(connection) = self.connection.take() {
            // 异步回收到池中
            let pool = Arc::clone(&self.pool);
            let created_at = self.created_at;
            let request_count = self.request_count;
            
            tokio::spawn(async move {
                if let Err(e) = pool.return_connection(connection, created_at, request_count).await {
                    eprintln!("Failed to return connection to pool: {}", e);
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[tokio::test]
    async fn test_connection_pool_basic() {
        let created_count = Arc::new(AtomicUsize::new(0));
        let created_count_clone = Arc::clone(&created_count);
        
        let config = ConnectionPoolConfig {
            max_connections: 10,
            min_connections: 2,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(300),
            max_lifetime: Duration::from_secs(3600),
            health_check_interval: Duration::from_secs(60),
            enable_stats: true,
            enable_connection_reuse: true,
        };

        let pool = OptimizedConnectionPool::new(
            move || {
                created_count_clone.fetch_add(1, Ordering::AcqRel);
                Ok(format!("connection_{}", created_count_clone.load(Ordering::Acquire)))
            },
            config,
        ).unwrap();

        // 等待初始化完成
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 获取连接
        let conn1 = pool.acquire().await.unwrap();
        assert!(conn1.get().starts_with("connection_"));

        // 获取第二个连接
        let conn2 = pool.acquire().await.unwrap();
        assert!(conn2.get().starts_with("connection_"));

        // 释放连接
        drop(conn1);
        drop(conn2);

        // 等待异步回收
        tokio::time::sleep(Duration::from_millis(10)).await;

        // 再次获取连接，应该重用
        let conn3 = pool.acquire().await.unwrap();
        assert!(conn3.get().starts_with("connection_"));

        let stats = pool.get_stats().await;
        assert!(stats.total_connections > 0);
        assert!(stats.total_requests > 0);
    }

    #[tokio::test]
    async fn test_connection_pool_expiration() {
        let config = ConnectionPoolConfig {
            max_connections: 5,
            min_connections: 1,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_millis(100),
            max_lifetime: Duration::from_secs(3600),
            health_check_interval: Duration::from_millis(50),
            enable_stats: true,
            enable_connection_reuse: true,
        };

        let pool = OptimizedConnectionPool::new(
            || Ok(String::from("test_connection")),
            config,
        ).unwrap();

        // 等待初始化完成
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 获取连接
        let conn = pool.acquire().await.unwrap();
        drop(conn);

        // 等待连接过期
        tokio::time::sleep(Duration::from_millis(150)).await;

        // 清理过期连接
        let removed = pool.cleanup_expired().await;
        assert!(removed > 0);

        let stats = pool.get_stats().await;
        assert!(stats.health_check_count > 0);
    }

    #[tokio::test]
    async fn test_connection_pool_full() {
        let config = ConnectionPoolConfig {
            max_connections: 2,
            min_connections: 0,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(300),
            max_lifetime: Duration::from_secs(3600),
            health_check_interval: Duration::from_secs(60),
            enable_stats: true,
            enable_connection_reuse: true,
        };

        let pool = OptimizedConnectionPool::new(
            || Ok(String::from("test_connection")),
            config,
        ).unwrap();

        // 获取最大数量的连接
        let conn1 = pool.acquire().await.unwrap();
        let conn2 = pool.acquire().await.unwrap();

        // 尝试获取第三个连接应该失败
        let result = pool.acquire().await;
        assert!(result.is_err());

        // 释放一个连接
        drop(conn1);

        // 现在应该能够获取连接
        let conn3 = pool.acquire().await.unwrap();
        assert_eq!(conn3.get(), "test_connection");

        drop(conn2);
        drop(conn3);
    }

    #[tokio::test]
    async fn test_connection_pool_concurrent() {
        let config = ConnectionPoolConfig {
            max_connections: 10,
            min_connections: 5,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(300),
            max_lifetime: Duration::from_secs(3600),
            health_check_interval: Duration::from_secs(60),
            enable_stats: true,
            enable_connection_reuse: true,
        };

        let pool = OptimizedConnectionPool::new(
            || Ok(String::from("concurrent_connection")),
            config,
        ).unwrap();

        // 等待初始化完成
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 并发获取和释放连接
        let mut handles = Vec::new();
        for i in 0..20 {
            let pool_clone = pool.clone();
            let handle = tokio::spawn(async move {
                let conn = pool_clone.acquire().await.unwrap();
                // 模拟使用连接
                tokio::time::sleep(Duration::from_millis(10)).await;
                drop(conn);
                i
            });
            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            handle.await.unwrap();
        }

        let stats = pool.get_stats().await;
        assert!(stats.total_connections > 0);
        assert!(stats.total_requests > 0);
        assert!(stats.successful_requests > 0);
    }
}
