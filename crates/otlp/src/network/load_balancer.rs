//! 负载均衡模块
//!
//! 提供多种负载均衡算法和健康检查机制

use super::async_io::AsyncIoConfig;
use super::connection_pool::{ConnectionPool, ConnectionPoolConfig, LoadBalancingStrategy};
use anyhow::{Result, anyhow};
use std::collections::HashMap;
use std::net::{SocketAddr, ToSocketAddrs};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::time::interval;

/// 负载均衡统计信息
#[derive(Debug, Default)]
pub struct LoadBalancerStats {
    pub total_requests: AtomicUsize,
    pub successful_requests: AtomicUsize,
    pub failed_requests: AtomicUsize,
    pub average_response_time: AtomicU64, // 微秒
    pub peak_response_time: AtomicU64,    // 微秒
    pub active_backends: AtomicUsize,
    pub unhealthy_backends: AtomicUsize,
}

impl Clone for LoadBalancerStats {
    fn clone(&self) -> Self {
        Self {
            total_requests: AtomicUsize::new(self.total_requests.load(Ordering::Relaxed)),
            successful_requests: AtomicUsize::new(self.successful_requests.load(Ordering::Relaxed)),
            failed_requests: AtomicUsize::new(self.failed_requests.load(Ordering::Relaxed)),
            average_response_time: AtomicU64::new(
                self.average_response_time.load(Ordering::Relaxed),
            ),
            peak_response_time: AtomicU64::new(self.peak_response_time.load(Ordering::Relaxed)),
            active_backends: AtomicUsize::new(self.active_backends.load(Ordering::Relaxed)),
            unhealthy_backends: AtomicUsize::new(self.unhealthy_backends.load(Ordering::Relaxed)),
        }
    }
}

/// 后端服务器信息
#[derive(Debug, Clone)]
pub struct BackendServer {
    pub id: String,
    pub addr: SocketAddr,
    pub weight: u32,
    pub is_healthy: bool,
    pub last_health_check: Instant,
    pub response_time: Duration,
    pub success_count: u64,
    pub failure_count: u64,
    pub active_connections: usize,
}

/// 负载均衡器配置
#[derive(Debug, Clone)]
pub struct LoadBalancerConfig {
    pub health_check_interval: Duration,
    pub health_check_timeout: Duration,
    pub health_check_path: String,
    pub max_retries: usize,
    pub retry_delay: Duration,
    pub circuit_breaker_threshold: usize,
    pub circuit_breaker_timeout: Duration,
    pub sticky_sessions: bool,
    pub session_timeout: Duration,
}

impl Default for LoadBalancerConfig {
    fn default() -> Self {
        Self {
            health_check_interval: Duration::from_secs(30),
            health_check_timeout: Duration::from_secs(5),
            health_check_path: "/health".to_string(),
            max_retries: 3,
            retry_delay: Duration::from_millis(100),
            circuit_breaker_threshold: 5,
            circuit_breaker_timeout: Duration::from_secs(60),
            sticky_sessions: false,
            session_timeout: Duration::from_secs(300),
        }
    }
}

/// 负载均衡器
pub struct LoadBalancer {
    config: LoadBalancerConfig,
    stats: Arc<LoadBalancerStats>,
    backends: Arc<Mutex<HashMap<String, BackendServer>>>,
    connection_pools: Arc<Mutex<HashMap<String, Arc<ConnectionPool>>>>,
    round_robin_index: AtomicUsize,
    next_backend_id: AtomicUsize,
}

impl LoadBalancer {
    /// 创建新的负载均衡器
    pub fn new(config: LoadBalancerConfig) -> Self {
        Self {
            stats: Arc::new(LoadBalancerStats::default()),
            backends: Arc::new(Mutex::new(HashMap::new())),
            connection_pools: Arc::new(Mutex::new(HashMap::new())),
            round_robin_index: AtomicUsize::new(0),
            next_backend_id: AtomicUsize::new(1),
            config,
        }
    }

    /// 添加后端服务器
    pub async fn add_backend<A: ToSocketAddrs>(&self, addr: A, weight: u32) -> Result<String> {
        let addrs: Vec<SocketAddr> = addr.to_socket_addrs()?.collect();
        if addrs.is_empty() {
            return Err(anyhow!("No valid addresses provided"));
        }

        let backend_id = format!(
            "backend_{}",
            self.next_backend_id.fetch_add(1, Ordering::Relaxed)
        );
        let backend = BackendServer {
            id: backend_id.clone(),
            addr: addrs[0],
            weight,
            is_healthy: true,
            last_health_check: Instant::now(),
            response_time: Duration::ZERO,
            success_count: 0,
            failure_count: 0,
            active_connections: 0,
        };

        // 创建连接池
        let pool_config = ConnectionPoolConfig {
            min_connections: 5,
            max_connections: 50,
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            ..Default::default()
        };
        let io_config = AsyncIoConfig::default();
        let pool = ConnectionPool::new(pool_config, io_config, vec![backend.addr]).await?;

        // 注册后端和连接池
        {
            let mut backends = self.backends.lock().unwrap();
            backends.insert(backend_id.clone(), backend);
        }
        {
            let mut pools = self.connection_pools.lock().unwrap();
            pools.insert(backend_id.clone(), Arc::new(pool));
        }

        self.stats.active_backends.fetch_add(1, Ordering::Relaxed);

        // 启动健康检查
        self.start_health_check_for_backend(backend_id.clone())
            .await;

        Ok(backend_id)
    }

    /// 移除后端服务器
    pub async fn remove_backend(&self, backend_id: &str) -> Result<()> {
        let mut backends = self.backends.lock().unwrap();
        if backends.remove(backend_id).is_some() {
            self.stats.active_backends.fetch_sub(1, Ordering::Relaxed);
        }

        let mut pools = self.connection_pools.lock().unwrap();
        if let Some(pool) = pools.remove(backend_id) {
            pool.close_all().await;
        }

        Ok(())
    }

    /// 选择后端服务器
    pub async fn select_backend(&self, strategy: &LoadBalancingStrategy) -> Result<String> {
        let backends = self.backends.lock().unwrap();
        let healthy_backends: Vec<_> = backends
            .values()
            .filter(|backend| backend.is_healthy)
            .collect();

        if healthy_backends.is_empty() {
            return Err(anyhow!("No healthy backends available"));
        }

        let selected = match strategy {
            LoadBalancingStrategy::RoundRobin => {
                let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed);
                &healthy_backends[index % healthy_backends.len()]
            }
            LoadBalancingStrategy::LeastConnections => healthy_backends
                .iter()
                .min_by_key(|backend| backend.active_connections)
                .unwrap(),
            LoadBalancingStrategy::Random => {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                Instant::now().hash(&mut hasher);
                let index = hasher.finish() as usize % healthy_backends.len();
                &healthy_backends[index]
            }
            LoadBalancingStrategy::WeightedRoundRobin(_weights) => {
                // 简化实现，实际应该按权重选择
                let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed);
                &healthy_backends[index % healthy_backends.len()]
            }
        };

        Ok(selected.id.clone())
    }

    /// 获取连接
    pub async fn get_connection(&self, backend_id: &str) -> Result<()> {
        let pools = self.connection_pools.lock().unwrap();
        if let Some(pool) = pools.get(backend_id) {
            let _connection = pool.get_connection().await?;
            // 更新活跃连接数
            self.update_backend_connections(backend_id, 1).await;
            Ok(())
        } else {
            Err(anyhow!("Backend not found: {}", backend_id))
        }
    }

    /// 更新后端连接数
    async fn update_backend_connections(&self, backend_id: &str, delta: i32) {
        let mut backends = self.backends.lock().unwrap();
        if let Some(backend) = backends.get_mut(backend_id) {
            if delta > 0 {
                backend.active_connections += delta as usize;
            } else {
                backend.active_connections =
                    backend.active_connections.saturating_sub((-delta) as usize);
            }
        }
    }

    /// 记录请求结果
    pub async fn record_request_result(
        &self,
        backend_id: &str,
        success: bool,
        response_time: Duration,
    ) {
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);

        if success {
            self.stats
                .successful_requests
                .fetch_add(1, Ordering::Relaxed);
        } else {
            self.stats.failed_requests.fetch_add(1, Ordering::Relaxed);
        }

        // 更新平均响应时间
        let current_avg = self.stats.average_response_time.load(Ordering::Relaxed);
        let new_avg = (current_avg + response_time.as_micros() as u64) / 2;
        self.stats
            .average_response_time
            .store(new_avg, Ordering::Relaxed);

        // 更新峰值响应时间
        let current_peak = self.stats.peak_response_time.load(Ordering::Relaxed);
        if response_time.as_micros() as u64 > current_peak {
            self.stats
                .peak_response_time
                .store(response_time.as_micros() as u64, Ordering::Relaxed);
        }

        // 更新后端统计
        let mut backends = self.backends.lock().unwrap();
        if let Some(backend) = backends.get_mut(backend_id) {
            backend.response_time = response_time;
            if success {
                backend.success_count += 1;
            } else {
                backend.failure_count += 1;
            }
        }
    }

    /// 启动健康检查
    async fn start_health_check_for_backend(&self, backend_id: String) {
        let config = self.config.clone();
        let backends = self.backends.clone();
        let stats = self.stats.clone();

        tokio::spawn(async move {
            let mut interval = interval(config.health_check_interval);
            loop {
                interval.tick().await;

                let is_healthy = Self::check_backend_health(&backend_id, &config).await;

                {
                    let mut backends = backends.lock().unwrap();
                    if let Some(backend) = backends.get_mut(&backend_id) {
                        backend.is_healthy = is_healthy;
                        backend.last_health_check = Instant::now();
                    }
                }

                if is_healthy {
                    stats.unhealthy_backends.fetch_sub(1, Ordering::Relaxed);
                } else {
                    stats.unhealthy_backends.fetch_add(1, Ordering::Relaxed);
                }
            }
        });
    }

    /// 检查后端健康状态
    async fn check_backend_health(_backend_id: &str, _config: &LoadBalancerConfig) -> bool {
        // 简化实现，实际应该发送HTTP请求
        // 这里只是模拟健康检查
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }

    /// 获取统计信息
    pub async fn stats(&self) -> LoadBalancerStats {
        (*self.stats).clone()
    }

    /// 获取后端信息
    pub async fn get_backends(&self) -> Vec<BackendServer> {
        let backends = self.backends.lock().unwrap();
        backends.values().cloned().collect()
    }

    /// 获取健康的后端
    pub async fn get_healthy_backends(&self) -> Vec<BackendServer> {
        let backends = self.backends.lock().unwrap();
        backends
            .values()
            .filter(|backend| backend.is_healthy)
            .cloned()
            .collect()
    }

    /// 获取不健康的后端
    pub async fn get_unhealthy_backends(&self) -> Vec<BackendServer> {
        let backends = self.backends.lock().unwrap();
        backends
            .values()
            .filter(|backend| !backend.is_healthy)
            .cloned()
            .collect()
    }
}

/// 健康检查器
pub struct HealthChecker {
    config: LoadBalancerConfig,
    backends: Arc<Mutex<HashMap<String, BackendServer>>>,
}

impl HealthChecker {
    /// 创建新的健康检查器
    pub fn new(config: LoadBalancerConfig) -> Self {
        Self {
            backends: Arc::new(Mutex::new(HashMap::new())),
            config,
        }
    }

    /// 添加后端进行健康检查
    pub fn add_backend(&self, backend: BackendServer) {
        let mut backends = self.backends.lock().unwrap();
        backends.insert(backend.id.clone(), backend);
    }

    /// 执行健康检查
    pub async fn check_all(&self) -> HashMap<String, bool> {
        let mut results = HashMap::new();
        let backends = self.backends.lock().unwrap();

        for (id, _backend) in backends.iter() {
            let is_healthy = Self::check_single_backend(id, &self.config).await;
            results.insert(id.clone(), is_healthy);
        }

        results
    }

    /// 检查单个后端
    async fn check_single_backend(_backend_id: &str, _config: &LoadBalancerConfig) -> bool {
        // 简化实现，实际应该发送HTTP请求
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddr;

    #[tokio::test]
    async fn test_load_balancer_creation() {
        let config = LoadBalancerConfig::default();
        let lb = LoadBalancer::new(config);
        let stats = lb.stats().await;
        assert_eq!(stats.total_requests.load(Ordering::Relaxed), 0);
    }

    #[tokio::test]
    async fn test_add_backend() {
        let config = LoadBalancerConfig::default();
        let lb = LoadBalancer::new(config);
        let addr = "127.0.0.1:8080".parse::<SocketAddr>().unwrap();

        let result = lb.add_backend(addr, 1).await;
        assert!(result.is_ok());

        let backends = lb.get_backends().await;
        assert_eq!(backends.len(), 1);
    }

    #[tokio::test]
    async fn test_select_backend() {
        let config = LoadBalancerConfig::default();
        let lb = LoadBalancer::new(config);
        let addr = "127.0.0.1:8080".parse::<SocketAddr>().unwrap();

        lb.add_backend(addr, 1).await.unwrap();

        let backend_id = lb.select_backend(&LoadBalancingStrategy::RoundRobin).await;
        assert!(backend_id.is_ok());
    }

    #[tokio::test]
    async fn test_health_checker() {
        let config = LoadBalancerConfig::default();
        let checker = HealthChecker::new(config);

        let backend = BackendServer {
            id: "test".to_string(),
            addr: "127.0.0.1:8080".parse().unwrap(),
            weight: 1,
            is_healthy: true,
            last_health_check: Instant::now(),
            response_time: Duration::ZERO,
            success_count: 0,
            failure_count: 0,
            active_connections: 0,
        };

        checker.add_backend(backend);
        let results = checker.check_all().await;
        assert_eq!(results.len(), 1);
    }
}
