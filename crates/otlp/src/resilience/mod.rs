//! # 容错与弹性模块
//!
//! 基于理论文档中的容错设计模式，提供完整的容错和弹性机制。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.1节
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步容错操作
//! - **元组收集**: 使用 `collect()` 直接收集容错统计到元组
//! - **改进的错误处理**: 利用 Rust 1.92 的错误处理优化提升性能

pub mod bulkhead;
pub mod circuit_breaker;
pub mod retry;
pub mod timeout;

// 重新导出主要类型
pub use bulkhead::{Bulkhead, BulkheadConfig, BulkheadError, BulkheadManager};
pub use circuit_breaker::{
    CircuitBreaker, CircuitBreakerConfig, CircuitBreakerManager, CircuitState,
    Error as CircuitBreakerError,
};
pub use retry::{
    Retrier, RetrierBuilder, RetrierManager, RetryConfig, RetryError, RetryStats, RetryStrategy,
};
pub use timeout::{Timeout, TimeoutConfig, TimeoutError};

/// 弹性模块统一错误类型
#[derive(Debug, thiserror::Error)]
pub enum ResilienceError {
    #[error("Circuit breaker error: {0}")]
    CircuitBreaker(#[from] CircuitBreakerError),
    #[error("Retry error: {0}")]
    Retry(#[from] RetryError<anyhow::Error>),
    #[error("Bulkhead error: {0}")]
    Bulkhead(#[from] BulkheadError),
    #[error("Timeout error: {0}")]
    Timeout(#[from] TimeoutError),
    #[error("Configuration error: {0}")]
    Config(String),
    #[error("Operation failed: {0}")]
    Operation(String),
}

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 弹性管理器 - 统一管理所有容错组件
pub struct ResilienceManager {
    circuit_breakers: Arc<RwLock<HashMap<String, Arc<CircuitBreaker>>>>,
    retriers: Arc<RwLock<HashMap<String, Arc<Retrier>>>>,
    bulkheads: Arc<RwLock<HashMap<String, Arc<Bulkhead>>>>,
    timeouts: Arc<RwLock<HashMap<String, Arc<Timeout>>>>,
}

impl ResilienceManager {
    /// 创建新的弹性管理器
    pub fn new() -> Self {
        Self {
            circuit_breakers: Arc::new(RwLock::new(HashMap::new())),
            retriers: Arc::new(RwLock::new(HashMap::new())),
            bulkheads: Arc::new(RwLock::new(HashMap::new())),
            timeouts: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 获取或创建断路器
    pub async fn get_or_create_circuit_breaker(
        &self,
        name: &str,
        config: CircuitBreakerConfig,
    ) -> Arc<CircuitBreaker> {
        let mut breakers = self.circuit_breakers.write().await;
        if let Some(breaker) = breakers.get(name) {
            return breaker.clone();
        }

        let breaker = Arc::new(CircuitBreaker::new(config));
        breakers.insert(name.to_string(), breaker.clone());
        breaker
    }

    /// 获取或创建重试器
    pub async fn get_or_create_retrier(&self, name: &str, config: RetryConfig) -> Arc<Retrier> {
        let mut retriers = self.retriers.write().await;
        if let Some(retrier) = retriers.get(name) {
            return retrier.clone();
        }

        let retrier = Arc::new(Retrier::new(config));
        retriers.insert(name.to_string(), retrier.clone());
        retrier
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

    /// 获取或创建超时器
    pub async fn get_or_create_timeout(&self, name: &str, config: TimeoutConfig) -> Arc<Timeout> {
        let mut timeouts = self.timeouts.write().await;
        if let Some(timeout) = timeouts.get(name) {
            return timeout.clone();
        }

        let timeout = Arc::new(Timeout::new(config));
        timeouts.insert(name.to_string(), timeout.clone());
        timeout
    }

    /// 获取所有组件的状态
    pub async fn get_all_status(&self) -> ResilienceStatus {
        let circuit_breakers = self.circuit_breakers.read().await;
        let retriers = self.retriers.read().await;
        let bulkheads = self.bulkheads.read().await;
        let timeouts = self.timeouts.read().await;

        let mut retrier_stats = HashMap::new();
        for (name, retrier) in retriers.iter() {
            retrier_stats.insert(name.clone(), retrier.stats().await);
        }

        ResilienceStatus {
            circuit_breakers: circuit_breakers
                .iter()
                .map(|(name, breaker)| (name.clone(), breaker.state()))
                .collect(),
            retriers: retrier_stats,
            bulkheads: {
                let mut bulkhead_status = HashMap::new();
                for (name, bulkhead) in bulkheads.iter() {
                    let status = bulkhead.status();
                    bulkhead_status.insert(
                        name.clone(),
                        BulkheadStatus {
                            active_requests: status.active_requests,
                            max_concurrent_requests: status.max_concurrent_requests,
                            queued_requests: status.queued_requests,
                            max_queue_size: status.max_queue_size,
                        },
                    );
                }
                bulkhead_status
            },
            timeouts: {
                let mut timeout_status = HashMap::new();
                for (name, timeout) in timeouts.iter() {
                    let status = timeout.status().await;
                    timeout_status.insert(
                        name.clone(),
                        TimeoutStatus {
                            active_timeouts: status.active_timeouts,
                            total_timeouts: status.total_timeouts,
                            timeout_rate: status.timeout_rate,
                        },
                    );
                }
                timeout_status
            },
        }
    }

    /// 重置所有组件
    pub async fn reset_all(&self) {
        let circuit_breakers = self.circuit_breakers.read().await;
        for breaker in circuit_breakers.values() {
            breaker.reset();
        }

        let retriers = self.retriers.read().await;
        for retrier in retriers.values() {
            retrier.reset_stats().await;
        }

        let bulkheads = self.bulkheads.read().await;
        for bulkhead in bulkheads.values() {
            bulkhead.reset();
        }

        let timeouts = self.timeouts.read().await;
        for timeout in timeouts.values() {
            timeout.reset().await;
        }
    }
}

impl Default for ResilienceManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 弹性状态信息
#[derive(Debug)]
pub struct ResilienceStatus {
    pub circuit_breakers: HashMap<String, CircuitState>,
    pub retriers: HashMap<String, RetryStats>,
    pub bulkheads: HashMap<String, BulkheadStatus>,
    pub timeouts: HashMap<String, TimeoutStatus>,
}

/// 舱壁状态
#[derive(Debug, Clone)]
pub struct BulkheadStatus {
    pub active_requests: usize,
    pub max_concurrent_requests: usize,
    pub queued_requests: usize,
    pub max_queue_size: usize,
}

/// 超时状态
#[derive(Debug, Clone)]
pub struct TimeoutStatus {
    pub active_timeouts: usize,
    pub total_timeouts: u64,
    pub timeout_rate: f64,
}

/// 弹性配置
#[derive(Debug, Clone, Default)]
pub struct ResilienceConfig {
    pub circuit_breaker: CircuitBreakerConfig,
    pub retry: RetryConfig,
    pub bulkhead: BulkheadConfig,
    pub timeout: TimeoutConfig,
}

/// 弹性构建器
pub struct ResilienceBuilder {
    config: ResilienceConfig,
}

impl ResilienceBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: ResilienceConfig::default(),
        }
    }

    /// 设置断路器配置
    pub fn circuit_breaker(mut self, config: CircuitBreakerConfig) -> Self {
        self.config.circuit_breaker = config;
        self
    }

    /// 设置重试配置
    pub fn retry(mut self, config: RetryConfig) -> Self {
        self.config.retry = config;
        self
    }

    /// 设置舱壁配置
    pub fn bulkhead(mut self, config: BulkheadConfig) -> Self {
        self.config.bulkhead = config;
        self
    }

    /// 设置超时配置
    pub fn timeout(mut self, config: TimeoutConfig) -> Self {
        self.config.timeout = config;
        self
    }

    /// 构建弹性管理器
    pub fn build(self) -> ResilienceManager {
        ResilienceManager::new()
    }
}

impl Default for ResilienceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_resilience_manager() {
        let manager = ResilienceManager::new();

        // 创建断路器
        let breaker_config = CircuitBreakerConfig {
            failure_threshold: 3,
            recovery_timeout: Duration::from_millis(100),
            half_open_max_requests: 2,
            success_threshold: 2,
        };
        let breaker = manager
            .get_or_create_circuit_breaker("test_breaker", breaker_config)
            .await;

        assert_eq!(breaker.state(), CircuitState::Closed);

        // 创建重试器
        let retry_config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Fixed {
                interval: Duration::from_millis(10),
            },
            total_timeout: None,
            health_check: false,
        };
        let retrier = manager
            .get_or_create_retrier("test_retrier", retry_config)
            .await;

        let stats = retrier.stats().await;
        assert_eq!(stats.total_retries, 0);

        // 获取状态
        let status = manager.get_all_status().await;
        assert!(status.circuit_breakers.contains_key("test_breaker"));
        assert!(status.retriers.contains_key("test_retrier"));
    }

    #[tokio::test]
    async fn test_resilience_builder() {
        let config = ResilienceConfig {
            circuit_breaker: CircuitBreakerConfig {
                failure_threshold: 5,
                recovery_timeout: Duration::from_secs(30),
                half_open_max_requests: 3,
                success_threshold: 2,
            },
            retry: RetryConfig {
                max_attempts: 5,
                strategy: RetryStrategy::Exponential {
                    initial_interval: Duration::from_millis(100),
                    max_interval: Duration::from_secs(30),
                    multiplier: 2.0,
                },
                total_timeout: Some(Duration::from_secs(60)),
                health_check: true,
            },
            bulkhead: BulkheadConfig::default(),
            timeout: TimeoutConfig::default(),
        };

        let manager = ResilienceBuilder::new()
            .circuit_breaker(config.circuit_breaker.clone())
            .retry(config.retry.clone())
            .build();

        let breaker = manager
            .get_or_create_circuit_breaker("test", config.circuit_breaker)
            .await;
        assert_eq!(breaker.state(), CircuitState::Closed);
    }
}
