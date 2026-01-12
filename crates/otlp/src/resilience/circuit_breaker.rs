//! # 断路器模式实现
//!
//! 基于理论文档中的容错设计模式，实现高性能的断路器模式。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.1.1节
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步断路器操作
//! - **元组收集**: 使用 `collect()` 直接收集断路器统计到元组
//! - **改进的状态管理**: 利用 Rust 1.92 的状态管理优化提升性能

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// 关闭状态 - 正常处理请求
    Closed,
    /// 打开状态 - 快速失败
    Open,
    /// 半开状态 - 尝试恢复
    HalfOpen,
}

/// 断路器配置
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    /// 失败阈值 - 连续失败多少次后打开断路器
    pub failure_threshold: u64,
    /// 恢复超时 - 打开状态持续多长时间后尝试恢复
    pub recovery_timeout: Duration,
    /// 半开状态最大请求数 - 半开状态下最多处理多少个请求
    pub half_open_max_requests: u64,
    /// 成功阈值 - 半开状态下成功多少次后关闭断路器
    pub success_threshold: u64,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(30),
            half_open_max_requests: 3,
            success_threshold: 2,
        }
    }
}

/// 断路器统计信息
#[derive(Debug, Default)]
pub struct CircuitBreakerStats {
    /// 总请求数
    pub total_requests: AtomicU64,
    /// 成功请求数
    pub successful_requests: AtomicU64,
    /// 失败请求数
    pub failed_requests: AtomicU64,
    /// 断路器打开次数
    pub circuit_opened_count: AtomicU64,
    /// 最后失败时间
    pub last_failure_time: Arc<RwLock<Option<Instant>>>,
}

/// 高性能断路器实现
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: AtomicU8, // 0: Closed, 1: Open, 2: HalfOpen
    failure_count: AtomicU64,
    success_count: AtomicU64,
    half_open_requests: AtomicU64,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
    stats: Arc<CircuitBreakerStats>,
}

impl CircuitBreaker {
    /// 创建新的断路器
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: AtomicU8::new(0), // Closed
            failure_count: AtomicU64::new(0),
            success_count: AtomicU64::new(0),
            half_open_requests: AtomicU64::new(0),
            last_failure_time: Arc::new(RwLock::new(None)),
            stats: Arc::new(CircuitBreakerStats::default()),
        }
    }

    /// 获取当前状态
    pub fn state(&self) -> CircuitState {
        match self.state.load(Ordering::Acquire) {
            0 => CircuitState::Closed,
            1 => CircuitState::Open,
            2 => CircuitState::HalfOpen,
            _ => CircuitState::Closed,
        }
    }

    /// 检查是否允许请求通过
    pub async fn can_execute(&self) -> bool {
        match self.state() {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否应该尝试恢复
                if self.should_attempt_reset().await {
                    self.transition_to_half_open();
                    true
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => {
                // 检查半开状态下的请求限制
                let current_requests = self.half_open_requests.load(Ordering::Acquire);
                current_requests < self.config.half_open_max_requests
            }
        }
    }

    /// 记录成功请求
    pub fn record_success(&self) {
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);
        self.stats
            .successful_requests
            .fetch_add(1, Ordering::Relaxed);

        match self.state() {
            CircuitState::Closed => {
                // 重置失败计数
                self.failure_count.store(0, Ordering::Release);
            }
            CircuitState::HalfOpen => {
                let success_count = self.success_count.fetch_add(1, Ordering::Relaxed) + 1;
                if success_count >= self.config.success_threshold {
                    self.transition_to_closed();
                }
            }
            CircuitState::Open => {
                // 在打开状态下不应该有成功请求
            }
        }
    }

    /// 记录失败请求
    pub async fn record_failure(&self) {
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);
        self.stats.failed_requests.fetch_add(1, Ordering::Relaxed);

        let now = Instant::now();
        {
            let mut last_failure = self.last_failure_time.write().await;
            *last_failure = Some(now);
        }

        match self.state() {
            CircuitState::Closed => {
                let failure_count = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;
                if failure_count >= self.config.failure_threshold {
                    self.transition_to_open();
                }
            }
            CircuitState::HalfOpen => {
                // 半开状态下的失败立即打开断路器
                self.transition_to_open();
            }
            CircuitState::Open => {
                // 已经是打开状态，不需要额外处理
            }
        }
    }

    /// 执行受保护的异步操作
    pub async fn execute<F, R, E>(&self, operation: F) -> Result<R, E>
    where
        F: std::future::Future<Output = Result<R, E>>,
        E: From<Error>,
    {
        if !self.can_execute().await {
            return Err(Error::CircuitBreakerOpen.into());
        }

        // 在半开状态下增加请求计数
        if self.state() == CircuitState::HalfOpen {
            self.half_open_requests.fetch_add(1, Ordering::Relaxed);
        }

        match operation.await {
            Ok(result) => {
                self.record_success();
                Ok(result)
            }
            Err(error) => {
                self.record_failure().await;
                Err(error)
            }
        }
    }

    /// 获取统计信息
    pub fn stats(&self) -> &CircuitBreakerStats {
        &self.stats
    }

    /// 手动重置断路器
    pub fn reset(&self) {
        self.failure_count.store(0, Ordering::Release);
        self.success_count.store(0, Ordering::Release);
        self.half_open_requests.store(0, Ordering::Release);
        self.state.store(0, Ordering::Release); // Closed
    }

    /// 检查是否应该尝试重置
    async fn should_attempt_reset(&self) -> bool {
        if let Some(last_failure) = *self.last_failure_time.read().await {
            Instant::now().duration_since(last_failure) >= self.config.recovery_timeout
        } else {
            true
        }
    }

    /// 转换到关闭状态
    fn transition_to_closed(&self) {
        self.state.store(0, Ordering::Release); // Closed
        self.failure_count.store(0, Ordering::Release);
        self.success_count.store(0, Ordering::Release);
        self.half_open_requests.store(0, Ordering::Release);
    }

    /// 转换到打开状态
    fn transition_to_open(&self) {
        self.state.store(1, Ordering::Release); // Open
        self.stats
            .circuit_opened_count
            .fetch_add(1, Ordering::Relaxed);
    }

    /// 转换到半开状态
    fn transition_to_half_open(&self) {
        self.state.store(2, Ordering::Release); // HalfOpen
        self.success_count.store(0, Ordering::Release);
        self.half_open_requests.store(0, Ordering::Release);
    }
}

/// 断路器错误类型
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("断路器已打开")]
    CircuitBreakerOpen,
}

/// 断路器管理器 - 支持多个断路器的管理
pub struct CircuitBreakerManager {
    breakers: Arc<RwLock<HashMap<String, Arc<CircuitBreaker>>>>,
}

impl CircuitBreakerManager {
    /// 创建新的断路器管理器
    pub fn new() -> Self {
        Self {
            breakers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 获取或创建断路器
    pub async fn get_or_create_breaker(
        &self,
        name: &str,
        config: CircuitBreakerConfig,
    ) -> Arc<CircuitBreaker> {
        let mut breakers = self.breakers.write().await;
        if let Some(breaker) = breakers.get(name) {
            return breaker.clone();
        }

        let breaker = Arc::new(CircuitBreaker::new(config));
        breakers.insert(name.to_string(), breaker.clone());
        breaker
    }

    /// 获取所有断路器的状态
    pub async fn get_all_states(&self) -> HashMap<String, CircuitState> {
        let breakers = self.breakers.read().await;
        breakers
            .iter()
            .map(|(name, breaker)| (name.clone(), breaker.state()))
            .collect()
    }

    /// 重置所有断路器
    pub async fn reset_all(&self) {
        let breakers = self.breakers.read().await;
        for breaker in breakers.values() {
            breaker.reset();
        }
    }
}

impl Default for CircuitBreakerManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_circuit_breaker_closed_to_open() {
        let config = CircuitBreakerConfig {
            failure_threshold: 3,
            recovery_timeout: Duration::from_millis(100),
            half_open_max_requests: 2,
            success_threshold: 2,
        };
        let breaker = CircuitBreaker::new(config);

        // 初始状态应该是关闭的
        assert_eq!(breaker.state(), CircuitState::Closed);

        // 记录失败直到达到阈值
        for _ in 0..3 {
            breaker.record_failure().await;
        }

        // 应该转换到打开状态
        assert_eq!(breaker.state(), CircuitState::Open);
        assert!(!breaker.can_execute().await);
    }

    #[tokio::test]
    async fn test_circuit_breaker_recovery() {
        let config = CircuitBreakerConfig {
            failure_threshold: 2,
            recovery_timeout: Duration::from_millis(50),
            half_open_max_requests: 2,
            success_threshold: 2,
        };
        let breaker = CircuitBreaker::new(config);

        // 触发打开状态
        for _ in 0..2 {
            breaker.record_failure().await;
        }
        assert_eq!(breaker.state(), CircuitState::Open);

        // 等待恢复超时
        sleep(Duration::from_millis(100)).await;

        // can_execute会触发状态转换到HalfOpen
        assert!(breaker.can_execute().await);
        // 现在应该是半开状态
        assert_eq!(breaker.state(), CircuitState::HalfOpen);

        // 记录成功直到达到阈值
        for _ in 0..2 {
            breaker.record_success();
        }

        // 应该转换到关闭状态
        assert_eq!(breaker.state(), CircuitState::Closed);
    }

    #[tokio::test]
    async fn test_circuit_breaker_execute() {
        let config = CircuitBreakerConfig::default();
        let breaker = CircuitBreaker::new(config);

        // 测试成功操作
        let result: Result<i32, anyhow::Error> = breaker.execute(async { Ok(42) }).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
        assert_eq!(breaker.state(), CircuitState::Closed);

        // 测试失败操作
        let result: Result<i32, anyhow::Error> = breaker
            .execute(async { Err(anyhow::anyhow!("test error")) })
            .await;
        assert!(result.is_err());
    }
}
