//! 性能优化模块
//!
//! 包含使用Rust 1.90新特性的高性能组件实现

pub mod optimized_batch_processor;
pub mod optimized_circuit_breaker;
pub mod optimized_connection_pool;
pub mod optimized_memory_pool;

// 重新导出主要类型
pub use optimized_circuit_breaker::{
    CircuitBreakerConfig, CircuitBreakerError, CircuitBreakerState, OptimizedCircuitBreaker,
};

pub use optimized_memory_pool::{
    MemoryPoolConfig, MemoryPoolError, MemoryPoolStats, OptimizedMemoryPool, PooledObject,
};

pub use optimized_batch_processor::{
    BatchItem, BatchProcessorConfig, BatchProcessorError, BatchProcessorStats, BatchResult,
    OptimizedBatchProcessor,
};

pub use optimized_connection_pool::{
    ConnectionPoolConfig, ConnectionPoolError, ConnectionPoolStats, OptimizedConnectionPool,
    PooledConnection,
};

/// 性能优化配置
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct PerformanceConfig {
    /// 熔断器配置
    pub circuit_breaker: CircuitBreakerConfig,
    /// 内存池配置
    pub memory_pool: MemoryPoolConfig,
    /// 批处理器配置
    pub batch_processor: BatchProcessorConfig,
    /// 连接池配置
    pub connection_pool: ConnectionPoolConfig,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            circuit_breaker: CircuitBreakerConfig::default(),
            memory_pool: MemoryPoolConfig::default(),
            batch_processor: BatchProcessorConfig::default(),
            connection_pool: ConnectionPoolConfig::default(),
        }
    }
}

/// 性能优化管理器
///
/// 统一管理所有性能优化组件
pub struct PerformanceManager {
    config: PerformanceConfig,
    circuit_breaker: Option<OptimizedCircuitBreaker>,
    memory_pool: Option<OptimizedMemoryPool<String>>,
    batch_processor: Option<
        OptimizedBatchProcessor<
            String,
            Box<
                dyn Fn(
                        Vec<String>,
                    ) -> Result<
                        optimized_batch_processor::BatchResult<String>,
                        optimized_batch_processor::BatchProcessorError,
                    > + Send
                    + Sync,
            >,
        >,
    >,
    connection_pool: Option<
        OptimizedConnectionPool<
            String,
            Box<
                dyn Fn() -> Result<String, optimized_connection_pool::ConnectionPoolError>
                    + Send
                    + Sync,
            >,
        >,
    >,
}

impl PerformanceManager {
    /// 创建新的性能管理器
    pub fn new(config: PerformanceConfig) -> Self {
        Self {
            config,
            circuit_breaker: None,
            memory_pool: None,
            batch_processor: None,
            connection_pool: None,
        }
    }

    /// 初始化熔断器
    pub fn init_circuit_breaker(
        &mut self,
    ) -> Result<(), optimized_circuit_breaker::CircuitBreakerError> {
        self.circuit_breaker = Some(OptimizedCircuitBreaker::new(
            self.config.circuit_breaker.clone(),
        )?);
        Ok(())
    }

    /// 初始化内存池
    pub async fn init_memory_pool(&mut self) -> Result<(), optimized_memory_pool::MemoryPoolError> {
        self.memory_pool = Some(
            OptimizedMemoryPool::new(
                || String::with_capacity(1024),
                self.config.memory_pool.clone(),
            )
            .await?,
        );
        Ok(())
    }

    /// 初始化批处理器
    pub fn init_batch_processor(
        &mut self,
    ) -> Result<(), optimized_batch_processor::BatchProcessorError> {
        let processor: Box<
            dyn Fn(
                    Vec<String>,
                ) -> Result<
                    optimized_batch_processor::BatchResult<String>,
                    optimized_batch_processor::BatchProcessorError,
                > + Send
                + Sync,
        > = Box::new(|items: Vec<String>| {
            Ok(optimized_batch_processor::BatchResult {
                items,
                processing_time: std::time::Duration::from_millis(10),
                compressed_size: None,
                original_size: 1024,
            })
        });

        self.batch_processor = Some(OptimizedBatchProcessor::new(
            processor,
            self.config.batch_processor.clone(),
        )?);
        Ok(())
    }

    /// 初始化连接池
    pub fn init_connection_pool(
        &mut self,
    ) -> Result<(), optimized_connection_pool::ConnectionPoolError> {
        let factory: Box<
            dyn Fn() -> Result<String, optimized_connection_pool::ConnectionPoolError>
                + Send
                + Sync,
        > = Box::new(|| Ok(String::from("connection")));

        self.connection_pool = Some(OptimizedConnectionPool::new(
            factory,
            self.config.connection_pool.clone(),
        )?);
        Ok(())
    }

    /// 获取熔断器
    pub fn get_circuit_breaker(&self) -> Option<&OptimizedCircuitBreaker> {
        self.circuit_breaker.as_ref()
    }

    /// 获取内存池
    pub fn get_memory_pool(&self) -> Option<&OptimizedMemoryPool<String>> {
        self.memory_pool.as_ref()
    }

    /// 获取批处理器
    pub fn get_batch_processor(
        &self,
    ) -> Option<
        &OptimizedBatchProcessor<
            String,
            Box<
                dyn Fn(
                        Vec<String>,
                    ) -> Result<
                        optimized_batch_processor::BatchResult<String>,
                        optimized_batch_processor::BatchProcessorError,
                    > + Send
                    + Sync,
            >,
        >,
    > {
        self.batch_processor.as_ref()
    }

    /// 获取连接池
    pub fn get_connection_pool(
        &self,
    ) -> Option<
        &OptimizedConnectionPool<
            String,
            Box<
                dyn Fn() -> Result<String, optimized_connection_pool::ConnectionPoolError>
                    + Send
                    + Sync,
            >,
        >,
    > {
        self.connection_pool.as_ref()
    }

    /// 获取配置
    pub fn get_config(&self) -> &PerformanceConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: PerformanceConfig) {
        self.config = config;
    }

    /// 关闭所有组件
    pub fn shutdown(&self) {
        if let Some(cb) = &self.circuit_breaker {
            cb.shutdown();
        }
        if let Some(bp) = &self.batch_processor {
            bp.shutdown();
        }
        if let Some(cp) = &self.connection_pool {
            cp.shutdown();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_config_default() {
        let config = PerformanceConfig::default();
        assert_eq!(config.circuit_breaker.failure_threshold, 5);
        assert_eq!(config.memory_pool.max_size, 100);
        assert_eq!(config.batch_processor.max_batch_size, 1000);
        assert_eq!(config.connection_pool.max_connections, 100);
    }

    #[tokio::test]
    async fn test_performance_manager() {
        let config = PerformanceConfig::default();
        let mut manager = PerformanceManager::new(config);

        // 初始化组件
        manager.init_circuit_breaker().unwrap();
        manager.init_memory_pool().await.unwrap();
        manager.init_batch_processor().unwrap();
        manager.init_connection_pool().unwrap();

        // 验证组件已初始化
        assert!(manager.get_circuit_breaker().is_some());
        assert!(manager.get_memory_pool().is_some());
        assert!(manager.get_batch_processor().is_some());
        assert!(manager.get_connection_pool().is_some());

        // 关闭组件
        manager.shutdown();
    }
}
