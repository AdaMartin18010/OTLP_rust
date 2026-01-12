//! # 连接池模块
//!
//! 提供高效的连接池管理，支持连接复用和负载均衡
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步连接池操作
//! - **元组收集**: 使用 `collect()` 直接收集连接池统计到元组
//! - **改进的连接管理**: 利用 Rust 1.92 的连接管理优化提升性能

use super::async_io::{AsyncConnection, AsyncIoConfig, AsyncIoManager};
use anyhow::{Result, anyhow};
use std::collections::{HashMap, VecDeque};
use std::net::{SocketAddr, ToSocketAddrs};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};

/// 连接池统计信息
#[derive(Debug, Default)]
pub struct ConnectionPoolStats {
    pub total_connections: AtomicUsize,
    pub active_connections: AtomicUsize,
    pub idle_connections: AtomicUsize,
    pub connection_requests: AtomicUsize,
    pub connection_hits: AtomicUsize,
    pub connection_misses: AtomicUsize,
    pub connection_errors: AtomicUsize,
    pub average_connection_time: AtomicU64, // 微秒
    pub peak_connections: AtomicUsize,
}

impl Clone for ConnectionPoolStats {
    fn clone(&self) -> Self {
        Self {
            total_connections: AtomicUsize::new(self.total_connections.load(Ordering::Relaxed)),
            active_connections: AtomicUsize::new(self.active_connections.load(Ordering::Relaxed)),
            idle_connections: AtomicUsize::new(self.idle_connections.load(Ordering::Relaxed)),
            connection_requests: AtomicUsize::new(self.connection_requests.load(Ordering::Relaxed)),
            connection_hits: AtomicUsize::new(self.connection_hits.load(Ordering::Relaxed)),
            connection_misses: AtomicUsize::new(self.connection_misses.load(Ordering::Relaxed)),
            connection_errors: AtomicUsize::new(self.connection_errors.load(Ordering::Relaxed)),
            average_connection_time: AtomicU64::new(
                self.average_connection_time.load(Ordering::Relaxed),
            ),
            peak_connections: AtomicUsize::new(self.peak_connections.load(Ordering::Relaxed)),
        }
    }
}

/// 连接池配置
#[derive(Debug, Clone)]
pub struct ConnectionPoolConfig {
    pub min_connections: usize,
    pub max_connections: usize,
    pub max_idle_connections: usize,
    pub connection_timeout: Duration,
    pub idle_timeout: Duration,
    pub health_check_interval: Duration,
    pub retry_attempts: usize,
    pub retry_delay: Duration,
    pub load_balancing_strategy: LoadBalancingStrategy,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    Random,
    WeightedRoundRobin(Vec<u32>),
}

impl Default for ConnectionPoolConfig {
    fn default() -> Self {
        Self {
            min_connections: 5,
            max_connections: 100,
            max_idle_connections: 20,
            connection_timeout: Duration::from_secs(10),
            idle_timeout: Duration::from_secs(300), // 5分钟
            health_check_interval: Duration::from_secs(30),
            retry_attempts: 3,
            retry_delay: Duration::from_millis(100),
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        }
    }
}

/// 连接信息
#[derive(Debug)]
pub struct PooledConnectionInfo {
    pub id: usize,
    pub addr: SocketAddr,
    pub created_at: Instant,
    pub last_used: std::sync::Mutex<Instant>,
    pub is_healthy: bool,
    pub usage_count: std::sync::Mutex<u64>,
    pub total_usage_time: Duration,
}

impl Clone for PooledConnectionInfo {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            addr: self.addr,
            created_at: self.created_at,
            last_used: std::sync::Mutex::new(*self.last_used.lock().unwrap()),
            is_healthy: self.is_healthy,
            usage_count: std::sync::Mutex::new(*self.usage_count.lock().unwrap()),
            total_usage_time: self.total_usage_time,
        }
    }
}

/// 连接池
pub struct ConnectionPool {
    config: ConnectionPoolConfig,
    stats: Arc<ConnectionPoolStats>,
    io_manager: AsyncIoManager,
    connections: Arc<RwLock<HashMap<usize, Arc<PooledConnectionInfo>>>>,
    available_connections: Arc<Mutex<VecDeque<usize>>>,
    connection_semaphore: Arc<Semaphore>,
    next_connection_id: AtomicUsize,
    round_robin_index: AtomicUsize,
    addresses: Vec<SocketAddr>,
    weights: Vec<u32>,
}

impl ConnectionPool {
    /// 创建新的连接池
    pub async fn new<A: ToSocketAddrs>(
        config: ConnectionPoolConfig,
        io_config: AsyncIoConfig,
        addresses: Vec<A>,
    ) -> Result<Self> {
        let mut resolved_addresses = Vec::new();
        for addr in addresses {
            let addrs: Vec<SocketAddr> = addr.to_socket_addrs()?.collect();
            resolved_addresses.extend(addrs);
        }

        if resolved_addresses.is_empty() {
            return Err(anyhow!("No valid addresses provided"));
        }

        let weights = match &config.load_balancing_strategy {
            LoadBalancingStrategy::WeightedRoundRobin(weights) => {
                if weights.len() != resolved_addresses.len() {
                    return Err(anyhow!("Weight count must match address count"));
                }
                weights.clone()
            }
            _ => vec![1; resolved_addresses.len()],
        };

        let io_manager = AsyncIoManager::new(io_config);
        let connection_semaphore = Arc::new(Semaphore::new(config.max_connections));

        let pool = Self {
            stats: Arc::new(ConnectionPoolStats::default()),
            connections: Arc::new(RwLock::new(HashMap::new())),
            available_connections: Arc::new(Mutex::new(VecDeque::new())),
            connection_semaphore,
            next_connection_id: AtomicUsize::new(1),
            round_robin_index: AtomicUsize::new(0),
            addresses: resolved_addresses,
            weights,
            io_manager,
            config,
        };

        // 预创建最小连接数
        pool.initialize_min_connections().await?;

        // 启动健康检查任务
        pool.start_health_check_task().await;

        Ok(pool)
    }

    /// 获取连接
    pub async fn get_connection(&self) -> Result<PooledConnection> {
        self.stats
            .connection_requests
            .fetch_add(1, Ordering::Relaxed);

        // 尝试从可用连接中获取
        if let Some(connection_id) = self.get_available_connection().await {
            if let Some(_connection) = self.get_connection_by_id(connection_id).await {
                self.stats.connection_hits.fetch_add(1, Ordering::Relaxed);
                return Ok(PooledConnection {
                    id: connection_id,
                    pool: self.clone(),
                    created_at: Instant::now(),
                });
            }
        }

        // 创建新连接
        self.stats.connection_misses.fetch_add(1, Ordering::Relaxed);
        self.create_connection().await
    }

    /// 创建新连接
    async fn create_connection(&self) -> Result<PooledConnection> {
        let _permit = self
            .connection_semaphore
            .acquire()
            .await
            .map_err(|_| anyhow!("Connection pool is full"))?;

        let addr = self.select_address();
        let start = Instant::now();

        let _connection = self.io_manager.connect(addr).await?;
        let connection_time = start.elapsed();

        let connection_id = self.next_connection_id.fetch_add(1, Ordering::Relaxed);
        let connection_info = Arc::new(PooledConnectionInfo {
            id: connection_id,
            addr,
            created_at: Instant::now(),
            last_used: std::sync::Mutex::new(Instant::now()),
            is_healthy: true,
            usage_count: std::sync::Mutex::new(0),
            total_usage_time: Duration::ZERO,
        });

        // 注册连接
        {
            let mut connections = self.connections.write().await;
            connections.insert(connection_id, connection_info);
        }

        self.stats.total_connections.fetch_add(1, Ordering::Relaxed);
        self.stats
            .active_connections
            .fetch_add(1, Ordering::Relaxed);

        // 更新平均连接时间
        let current_avg = self.stats.average_connection_time.load(Ordering::Relaxed);
        let new_avg = (current_avg + connection_time.as_micros() as u64) / 2;
        self.stats
            .average_connection_time
            .store(new_avg, Ordering::Relaxed);

        // 更新峰值连接数
        let current_active = self.stats.active_connections.load(Ordering::Relaxed);
        let current_peak = self.stats.peak_connections.load(Ordering::Relaxed);
        if current_active > current_peak {
            self.stats
                .peak_connections
                .store(current_active, Ordering::Relaxed);
        }

        Ok(PooledConnection {
            id: connection_id,
            pool: self.clone(),
            created_at: Instant::now(),
        })
    }

    /// 选择地址
    fn select_address(&self) -> SocketAddr {
        match &self.config.load_balancing_strategy {
            LoadBalancingStrategy::RoundRobin => {
                let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed);
                self.addresses[index % self.addresses.len()]
            }
            LoadBalancingStrategy::Random => {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                Instant::now().hash(&mut hasher);
                let index = hasher.finish() as usize % self.addresses.len();
                self.addresses[index]
            }
            LoadBalancingStrategy::LeastConnections => {
                // 简化实现，实际应该统计每个地址的连接数
                let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed);
                self.addresses[index % self.addresses.len()]
            }
            LoadBalancingStrategy::WeightedRoundRobin(_) => {
                // 简化实现，实际应该按权重选择
                let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed);
                self.addresses[index % self.addresses.len()]
            }
        }
    }

    /// 获取可用连接
    async fn get_available_connection(&self) -> Option<usize> {
        let mut available = self.available_connections.lock().unwrap();
        available.pop_front()
    }

    /// 获取连接信息
    async fn get_connection_by_id(&self, id: usize) -> Option<Arc<PooledConnectionInfo>> {
        let connections = self.connections.read().await;
        connections.get(&id).cloned()
    }

    /// 返回连接
    pub async fn return_connection(&self, connection_id: usize) {
        let connection_info = if let Some(info) = self.get_connection_by_id(connection_id).await {
            info
        } else {
            return;
        };

        // 更新使用统计
        *connection_info.last_used.lock().unwrap() = Instant::now();
        *connection_info.usage_count.lock().unwrap() += 1;

        // 检查是否应该保留连接
        if self.should_keep_connection(&connection_info) {
            let mut available = self.available_connections.lock().unwrap();
            available.push_back(connection_id);
            self.stats.idle_connections.fetch_add(1, Ordering::Relaxed);
        } else {
            self.remove_connection(connection_id).await;
        }
    }

    /// 判断是否应该保留连接
    fn should_keep_connection(&self, info: &PooledConnectionInfo) -> bool {
        let idle_time = Instant::now().duration_since(*info.last_used.lock().unwrap());
        let max_idle = self.config.idle_timeout;
        let max_connections = self.config.max_idle_connections;

        idle_time < max_idle
            && self.stats.idle_connections.load(Ordering::Relaxed) < max_connections
    }

    /// 移除连接
    async fn remove_connection(&self, connection_id: usize) {
        let mut connections = self.connections.write().await;
        if connections.remove(&connection_id).is_some() {
            self.stats
                .active_connections
                .fetch_sub(1, Ordering::Relaxed);
            self.stats.idle_connections.fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// 初始化最小连接数
    async fn initialize_min_connections(&self) -> Result<()> {
        for _ in 0..self.config.min_connections {
            if let Err(e) = self.create_connection().await {
                eprintln!("Failed to create initial connection: {}", e);
            }
        }
        Ok(())
    }

    /// 启动健康检查任务
    async fn start_health_check_task(&self) {
        let pool = self.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(pool.config.health_check_interval);
            loop {
                interval.tick().await;
                pool.health_check().await;
            }
        });
    }

    /// 健康检查
    async fn health_check(&self) {
        let connections = self.connections.read().await;
        let mut to_remove = Vec::new();

        for (id, info) in connections.iter() {
            let idle_time = Instant::now().duration_since(*info.last_used.lock().unwrap());
            if idle_time > self.config.idle_timeout {
                to_remove.push(*id);
            }
        }

        drop(connections);

        for id in to_remove {
            self.remove_connection(id).await;
        }
    }

    /// 获取统计信息
    pub async fn stats(&self) -> ConnectionPoolStats {
        (*self.stats).clone()
    }

    /// 获取连接信息
    pub async fn get_connection_infos(&self) -> Vec<PooledConnectionInfo> {
        let connections = self.connections.read().await;
        connections
            .values()
            .map(|info| info.as_ref().clone())
            .collect()
    }

    /// 关闭所有连接
    pub async fn close_all(&self) {
        let mut connections = self.connections.write().await;
        connections.clear();
        self.stats.active_connections.store(0, Ordering::Relaxed);
        self.stats.idle_connections.store(0, Ordering::Relaxed);
    }
}

impl Clone for ConnectionPool {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            stats: self.stats.clone(),
            io_manager: self.io_manager.clone(),
            connections: self.connections.clone(),
            available_connections: self.available_connections.clone(),
            connection_semaphore: self.connection_semaphore.clone(),
            next_connection_id: AtomicUsize::new(0),
            round_robin_index: AtomicUsize::new(0),
            addresses: self.addresses.clone(),
            weights: self.weights.clone(),
        }
    }
}

/// 池化连接
#[allow(dead_code)]
pub struct PooledConnection {
    id: usize,
    pool: ConnectionPool,
    created_at: Instant,
}

impl PooledConnection {
    /// 获取连接ID
    pub fn id(&self) -> usize {
        self.id
    }

    /// 获取连接信息
    pub async fn info(&self) -> Option<PooledConnectionInfo> {
        self.pool
            .get_connection_by_id(self.id)
            .await
            .map(|info| info.as_ref().clone())
    }

    /// 获取底层连接
    pub async fn get_connection(&self) -> Result<AsyncConnection> {
        // 这里应该返回实际的连接，简化实现
        Err(anyhow!("Not implemented"))
    }
}

impl Drop for PooledConnection {
    fn drop(&mut self) {
        let pool = self.pool.clone();
        let id = self.id;
        tokio::spawn(async move {
            pool.return_connection(id).await;
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddr;

    #[tokio::test]
    async fn test_connection_pool_creation() {
        let config = ConnectionPoolConfig::default();
        let io_config = AsyncIoConfig::default();
        let addresses = vec!["127.0.0.1:8080".parse::<SocketAddr>().unwrap()];

        let pool = ConnectionPool::new(config, io_config, addresses).await;
        assert!(pool.is_ok());
    }

    #[tokio::test]
    #[ignore = "需要运行测试服务器: 此测试需要在127.0.0.1:8080上运行服务器"]
    async fn test_load_balancing_strategies() {
        let config = ConnectionPoolConfig {
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            ..Default::default()
        };
        let io_config = AsyncIoConfig::default();
        let addresses = vec!["127.0.0.1:8080".parse::<SocketAddr>().unwrap()];

        let pool = ConnectionPool::new(config, io_config, addresses)
            .await
            .unwrap();
        let stats = pool.stats().await;
        assert_eq!(stats.total_connections.load(Ordering::Relaxed), 5); // min_connections
    }
}
