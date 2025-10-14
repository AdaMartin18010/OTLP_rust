//! 网络I/O优化模块
//! 
//! 提供高性能的网络I/O操作、连接池和负载均衡

use std::net::ToSocketAddrs;
use std::sync::Arc;
use std::sync::{Mutex};
use std::time::Duration;

pub mod async_io;
pub mod connection_pool;
pub mod load_balancer;

// 重新导出主要类型
pub use async_io::{
    AsyncConnection, AsyncIoConfig, AsyncIoManager, AsyncIoStats, BatchIo, ConnectionInfo,
};
pub use connection_pool::{
    ConnectionPool, ConnectionPoolConfig, ConnectionPoolStats, LoadBalancingStrategy,
    PooledConnection, PooledConnectionInfo,
};
pub use load_balancer::{
    BackendServer, HealthChecker, LoadBalancer, LoadBalancerConfig, LoadBalancerStats,
};

/// 网络I/O配置
#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// 异步I/O配置
    pub async_io: AsyncIoConfig,
    /// 连接池配置
    pub connection_pool: ConnectionPoolConfig,
    /// 负载均衡配置
    pub load_balancer: LoadBalancerConfig,
    /// 启用连接池
    pub enable_connection_pool: bool,
    /// 启用负载均衡
    pub enable_load_balancer: bool,
    /// 启用健康检查
    pub enable_health_check: bool,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        Self {
            async_io: AsyncIoConfig::default(),
            connection_pool: ConnectionPoolConfig::default(),
            load_balancer: LoadBalancerConfig::default(),
            enable_connection_pool: true,
            enable_load_balancer: true,
            enable_health_check: true,
        }
    }
}

/// 网络I/O管理器
pub struct NetworkManager {
    config: NetworkConfig,
    async_io_manager: AsyncIoManager,
    connection_pool: Option<ConnectionPool>,
    load_balancer: Option<LoadBalancer>,
    health_checker: Option<HealthChecker>,
}

impl NetworkManager {
    /// 创建新的网络管理器
    pub async fn new(config: NetworkConfig) -> Result<Self, anyhow::Error> {
        let async_io_manager = AsyncIoManager::new(config.async_io.clone());
        
        let mut manager = Self {
            config,
            async_io_manager,
            connection_pool: None,
            load_balancer: None,
            health_checker: None,
        };

        // 初始化组件
        if manager.config.enable_connection_pool {
            manager.init_connection_pool().await?;
        }

        if manager.config.enable_load_balancer {
            manager.init_load_balancer().await?;
        }

        if manager.config.enable_health_check {
            manager.init_health_checker().await?;
        }

        Ok(manager)
    }

    /// 初始化连接池
    async fn init_connection_pool(&mut self) -> Result<(), anyhow::Error> {
        let addresses = vec!["127.0.0.1:8080"]; // 默认地址
        let pool = ConnectionPool::new(
            self.config.connection_pool.clone(),
            self.config.async_io.clone(),
            addresses,
        ).await?;
        self.connection_pool = Some(pool);
        Ok(())
    }

    /// 初始化负载均衡器
    async fn init_load_balancer(&mut self) -> Result<(), anyhow::Error> {
        let lb = LoadBalancer::new(self.config.load_balancer.clone());
        self.load_balancer = Some(lb);
        Ok(())
    }

    /// 初始化健康检查器
    async fn init_health_checker(&mut self) -> Result<(), anyhow::Error> {
        let checker = HealthChecker::new(self.config.load_balancer.clone());
        self.health_checker = Some(checker);
        Ok(())
    }

    /// 获取连接
    pub async fn get_connection(&self) -> Result<AsyncConnection, anyhow::Error> {
        if let Some(ref pool) = self.connection_pool {
            let _pooled_connection = pool.get_connection().await?;
            // 这里应该返回实际的连接，简化实现
            Err(anyhow::anyhow!("Not implemented"))
        } else {
            // 直接使用异步I/O管理器
            self.async_io_manager.connect("127.0.0.1:8080").await
        }
    }

    /// 添加后端服务器
    pub async fn add_backend<A: ToSocketAddrs>(
        &self,
        addr: A,
        weight: u32,
    ) -> Result<String, anyhow::Error> {
        if let Some(ref lb) = self.load_balancer {
            lb.add_backend(addr, weight).await
        } else {
            Err(anyhow::anyhow!("Load balancer not enabled"))
        }
    }

    /// 选择后端服务器
    pub async fn select_backend(&self, strategy: &LoadBalancingStrategy) -> Result<String, anyhow::Error> {
        if let Some(ref lb) = self.load_balancer {
            lb.select_backend(strategy).await
        } else {
            Err(anyhow::anyhow!("Load balancer not enabled"))
        }
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> NetworkStats {
        let async_io_stats = self.async_io_manager.stats().await;
        let connection_pool_stats = if let Some(ref pool) = self.connection_pool {
            Some(pool.stats().await)
        } else {
            None
        };
        let load_balancer_stats = if let Some(ref lb) = self.load_balancer {
            Some(lb.stats().await)
        } else {
            None
        };

        NetworkStats {
            async_io: async_io_stats,
            connection_pool: connection_pool_stats,
            load_balancer: load_balancer_stats,
        }
    }

    /// 获取配置
    pub fn config(&self) -> &NetworkConfig {
        &self.config
    }

    /// 更新配置
    pub async fn update_config(&mut self, config: NetworkConfig) -> Result<(), anyhow::Error> {
        self.config = config;
        
        // 重新初始化组件
        if self.config.enable_connection_pool {
            self.init_connection_pool().await?;
        }

        if self.config.enable_load_balancer {
            self.init_load_balancer().await?;
        }

        if self.config.enable_health_check {
            self.init_health_checker().await?;
        }

        Ok(())
    }

    /// 关闭所有连接
    pub async fn shutdown(&self) {
        if let Some(ref pool) = self.connection_pool {
            pool.close_all().await;
        }
    }
}

/// 网络统计信息
#[derive(Debug, Clone)]
pub struct NetworkStats {
    pub async_io: AsyncIoStats,
    pub connection_pool: Option<ConnectionPoolStats>,
    pub load_balancer: Option<LoadBalancerStats>,
}

/// 网络性能监控器
pub struct NetworkMonitor {
    stats: Arc<Mutex<NetworkStats>>,
    update_interval: Duration,
}

impl NetworkMonitor {
    /// 创建新的网络监控器
    pub fn new(update_interval: Duration) -> Self {
        Self {
            stats: Arc::new(Mutex::new(NetworkStats {
                async_io: AsyncIoStats::default(),
                connection_pool: None,
                load_balancer: None,
            })),
            update_interval,
        }
    }

    /// 启动监控
    pub async fn start_monitoring(&self, manager: Arc<NetworkManager>) {
        let stats = self.stats.clone();
        let interval = self.update_interval;

        tokio::spawn(async move {
            let mut timer = tokio::time::interval(interval);
            loop {
                timer.tick().await;
                let new_stats = manager.get_stats().await;
                {
                    let mut current_stats = stats.lock()
                        .unwrap_or_else(|e| {
                            eprintln!("Failed to acquire network stats lock: {}", e);
                            std::process::exit(1);
                        });
                    *current_stats = new_stats;
                }
            }
        });
    }

    /// 获取当前统计信息
    pub fn get_stats(&self) -> NetworkStats {
        self.stats.lock()
            .unwrap_or_else(|e| {
                eprintln!("Failed to acquire network stats lock: {}", e);
                std::process::exit(1);
            })
            .clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[tokio::test]
    async fn test_network_manager_creation() {
        let config = NetworkConfig::default();
        let manager = NetworkManager::new(config).await;
        assert!(manager.is_ok());
    }

    #[tokio::test]
    async fn test_network_config_default() {
        let config = NetworkConfig::default();
        assert!(config.enable_connection_pool);
        assert!(config.enable_load_balancer);
        assert!(config.enable_health_check);
    }

    #[tokio::test]
    async fn test_network_monitor() {
        let monitor = NetworkMonitor::new(Duration::from_secs(1));
        let stats = monitor.get_stats();
        assert_eq!(stats.async_io.total_connections.load(Ordering::Relaxed), 0);
    }
}
