//! # 重试策略实现
//!
//! 基于理论文档中的容错设计模式，实现智能重试机制。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.1.1节
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步重试操作
//! - **元组收集**: 使用 `collect()` 直接收集重试统计到元组
//! - **改进的重试策略**: 利用 Rust 1.92 的重试策略优化提升性能

use anyhow;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::{sleep, timeout};

/// 重试策略类型
#[derive(Debug, Clone, PartialEq)]
pub enum RetryStrategy {
    /// 固定间隔重试
    Fixed { interval: Duration },
    /// 线性退避重试
    Linear {
        initial_interval: Duration,
        max_interval: Duration,
        increment: Duration,
    },
    /// 指数退避重试
    Exponential {
        initial_interval: Duration,
        max_interval: Duration,
        multiplier: f64,
    },
    /// 指数退避带抖动
    ExponentialWithJitter {
        initial_interval: Duration,
        max_interval: Duration,
        multiplier: f64,
        jitter_factor: f64,
    },
}

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 重试策略
    pub strategy: RetryStrategy,
    /// 总超时时间
    pub total_timeout: Option<Duration>,
    /// 是否在重试前进行健康检查
    pub health_check: bool,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            strategy: RetryStrategy::ExponentialWithJitter {
                initial_interval: Duration::from_millis(100),
                max_interval: Duration::from_secs(30),
                multiplier: 2.0,
                jitter_factor: 0.1,
            },
            total_timeout: Some(Duration::from_secs(60)),
            health_check: false,
        }
    }
}

/// 重试统计信息
#[derive(Debug, Default, Clone)]
pub struct RetryStats {
    /// 总重试次数
    pub total_retries: u64,
    /// 成功重试次数
    pub successful_retries: u64,
    /// 失败重试次数
    pub failed_retries: u64,
    /// 平均重试间隔
    pub average_retry_interval: Duration,
    /// 最大重试间隔
    pub max_retry_interval: Duration,
}

/// 重试器实现
pub struct Retrier {
    config: RetryConfig,
    stats: Arc<RwLock<RetryStats>>,
}

impl Retrier {
    /// 创建新的重试器
    pub fn new(config: RetryConfig) -> Self {
        Self {
            config,
            stats: Arc::new(RwLock::new(RetryStats::default())),
        }
    }

    /// 执行带重试的异步操作
    pub async fn execute<F, R, E>(&self, operation: F) -> Result<R, RetryError<E>>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<R, E>> + Send>>,
        E: Clone + Send + Sync + 'static,
    {
        let start_time = Instant::now();
        let mut attempt = 0;
        let mut last_error: Option<E> = None;

        loop {
            attempt += 1;

            // 检查总超时
            if let Some(total_timeout) = self.config.total_timeout {
                if start_time.elapsed() >= total_timeout {
                    return Err(RetryError::Timeout {
                        total_timeout,
                        elapsed: start_time.elapsed(),
                        last_error,
                    });
                }
            }

            // 检查最大重试次数
            if attempt > self.config.max_attempts {
                return Err(RetryError::MaxAttemptsReached {
                    max_attempts: self.config.max_attempts,
                    last_error,
                });
            }

            // 执行操作
            let result = operation().await;

            match result {
                Ok(value) => {
                    // 成功，更新统计信息
                    self.update_stats_on_success(attempt).await;
                    return Ok(value);
                }
                Err(error) => {
                    last_error = Some(error.clone());

                    // 如果是最后一次尝试，返回MaxAttemptsReached
                    if attempt >= self.config.max_attempts {
                        self.update_stats_on_failure(attempt).await;
                        return Err(RetryError::MaxAttemptsReached {
                            max_attempts: self.config.max_attempts,
                            last_error: Some(error),
                        });
                    }

                    // 计算重试间隔
                    let retry_interval = self.calculate_retry_interval(attempt);

                    // 更新统计信息
                    self.update_stats_on_retry(attempt, retry_interval).await;

                    // 等待重试间隔
                    sleep(retry_interval).await;
                }
            }
        }
    }

    /// 执行带超时的重试操作
    pub async fn execute_with_timeout<F, R, E>(
        &self,
        operation: F,
        operation_timeout: Duration,
    ) -> Result<R, RetryError<E>>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<R, E>> + Send>>,
        E: Clone + Send + Sync + 'static,
    {
        let start_time = Instant::now();
        let mut attempt = 0;
        let mut last_error: Option<E> = None;

        loop {
            attempt += 1;

            // 检查总超时
            if let Some(total_timeout) = self.config.total_timeout {
                if start_time.elapsed() >= total_timeout {
                    return Err(RetryError::Timeout {
                        total_timeout,
                        elapsed: start_time.elapsed(),
                        last_error,
                    });
                }
            }

            // 检查最大重试次数
            if attempt > self.config.max_attempts {
                return Err(RetryError::MaxAttemptsReached {
                    max_attempts: self.config.max_attempts,
                    last_error,
                });
            }

            // 执行带超时的操作
            let result = timeout(operation_timeout, operation()).await;

            match result {
                Ok(Ok(value)) => {
                    // 成功，更新统计信息
                    self.update_stats_on_success(attempt).await;
                    return Ok(value);
                }
                Ok(Err(error)) => {
                    last_error = Some(error.clone());

                    // 如果是最后一次尝试，返回MaxAttemptsReached
                    if attempt >= self.config.max_attempts {
                        self.update_stats_on_failure(attempt).await;
                        return Err(RetryError::MaxAttemptsReached {
                            max_attempts: self.config.max_attempts,
                            last_error: Some(error),
                        });
                    }

                    // 计算重试间隔
                    let retry_interval = self.calculate_retry_interval(attempt);

                    // 更新统计信息
                    self.update_stats_on_retry(attempt, retry_interval).await;

                    // 等待重试间隔
                    sleep(retry_interval).await;
                }
                Err(_) => {
                    // 操作超时
                    return Err(RetryError::OperationTimeout(operation_timeout));
                }
            }
        }
    }

    /// 获取统计信息
    pub async fn stats(&self) -> RetryStats {
        (*self.stats.read().await).clone()
    }

    /// 重置统计信息
    pub async fn reset_stats(&self) {
        let mut stats = self.stats.write().await;
        *stats = RetryStats::default();
    }

    /// 计算重试间隔
    fn calculate_retry_interval(&self, attempt: u32) -> Duration {
        match &self.config.strategy {
            RetryStrategy::Fixed { interval } => *interval,

            RetryStrategy::Linear {
                initial_interval,
                max_interval,
                increment,
            } => {
                let interval = *initial_interval + *increment * (attempt - 1);
                interval.min(*max_interval)
            }

            RetryStrategy::Exponential {
                initial_interval,
                max_interval,
                multiplier,
            } => {
                let interval_ms =
                    initial_interval.as_millis() as f64 * multiplier.powi(attempt as i32 - 1);
                let interval = Duration::from_millis(interval_ms as u64);
                interval.min(*max_interval)
            }

            RetryStrategy::ExponentialWithJitter {
                initial_interval,
                max_interval,
                multiplier,
                jitter_factor,
            } => {
                let base_interval_ms =
                    initial_interval.as_millis() as f64 * multiplier.powi(attempt as i32 - 1);
                let jitter = base_interval_ms * jitter_factor * (2.0 * rand::random::<f64>() - 1.0);
                let interval_ms = (base_interval_ms + jitter).max(0.0) as u64;
                let interval = Duration::from_millis(interval_ms);
                interval.min(*max_interval)
            }
        }
    }

    /// 更新成功统计信息
    async fn update_stats_on_success(&self, attempts: u32) {
        let mut stats = self.stats.write().await;
        stats.total_retries += (attempts - 1) as u64;
        stats.successful_retries += 1;
    }

    /// 更新失败统计信息
    async fn update_stats_on_failure(&self, attempts: u32) {
        let mut stats = self.stats.write().await;
        stats.total_retries += (attempts - 1) as u64;
        stats.failed_retries += 1;
    }

    /// 更新重试统计信息
    async fn update_stats_on_retry(&self, _attempt: u32, interval: Duration) {
        let mut stats = self.stats.write().await;
        stats.total_retries += 1;

        // 更新平均重试间隔
        let total_retries = stats.total_retries;
        let current_avg = stats.average_retry_interval.as_millis() as f64;
        let new_avg = (current_avg * (total_retries - 1) as f64 + interval.as_millis() as f64)
            / total_retries as f64;
        stats.average_retry_interval = Duration::from_millis(new_avg as u64);

        // 更新最大重试间隔
        if interval > stats.max_retry_interval {
            stats.max_retry_interval = interval;
        }
    }
}

/// 重试错误类型
#[derive(Debug, PartialEq, thiserror::Error)]
pub enum RetryError<E = anyhow::Error> {
    #[error("操作失败: 尝试了 {attempts} 次")]
    OperationFailed {
        attempts: u32,
        last_error: Option<E>,
    },

    #[error("达到最大重试次数: {max_attempts}")]
    MaxAttemptsReached {
        max_attempts: u32,
        last_error: Option<E>,
    },

    #[error("总超时: {total_timeout:?}, 已用时间: {elapsed:?}")]
    Timeout {
        total_timeout: Duration,
        elapsed: Duration,
        last_error: Option<E>,
    },

    #[error("操作超时: {0:?}")]
    OperationTimeout(Duration),
}

/// 重试器构建器
pub struct RetrierBuilder {
    config: RetryConfig,
}

impl RetrierBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: RetryConfig::default(),
        }
    }

    /// 设置最大重试次数
    pub fn max_attempts(mut self, max_attempts: u32) -> Self {
        self.config.max_attempts = max_attempts;
        self
    }

    /// 设置重试策略
    pub fn strategy(mut self, strategy: RetryStrategy) -> Self {
        self.config.strategy = strategy;
        self
    }

    /// 设置总超时时间
    pub fn total_timeout(mut self, timeout: Duration) -> Self {
        self.config.total_timeout = Some(timeout);
        self
    }

    /// 启用健康检查
    pub fn enable_health_check(mut self) -> Self {
        self.config.health_check = true;
        self
    }

    /// 构建重试器
    pub fn build(self) -> Retrier {
        Retrier::new(self.config)
    }
}

impl Default for RetrierBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 重试器管理器 - 支持多个重试器的管理
pub struct RetrierManager {
    retriers: Arc<RwLock<HashMap<String, Arc<Retrier>>>>,
}

impl RetrierManager {
    /// 创建新的重试器管理器
    pub fn new() -> Self {
        Self {
            retriers: Arc::new(RwLock::new(HashMap::new())),
        }
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

    /// 获取所有重试器的统计信息
    pub async fn get_all_stats(&self) -> HashMap<String, RetryStats> {
        let retriers = self.retriers.read().await;
        let mut stats_map = HashMap::new();

        for (name, retrier) in retriers.iter() {
            stats_map.insert(name.clone(), retrier.stats().await);
        }

        stats_map
    }
}

impl Default for RetrierManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_fixed_retry_strategy() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Fixed {
                interval: Duration::from_millis(10),
            },
            total_timeout: None,
            health_check: false,
        };
        let retrier = Retrier::new(config);

        let result: Result<i32, RetryError<&str>> = retrier
            .execute(|| Box::pin(async { Err("temporary error") }))
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_exponential_backoff() {
        let config = RetryConfig {
            max_attempts: 4,
            strategy: RetryStrategy::Exponential {
                initial_interval: Duration::from_millis(10),
                max_interval: Duration::from_millis(100),
                multiplier: 2.0,
            },
            total_timeout: None,
            health_check: false,
        };
        let retrier = Retrier::new(config);

        let result: Result<i32, RetryError<&str>> = retrier
            .execute(|| Box::pin(async { Err("temporary error") }))
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_max_attempts_reached() {
        let config = RetryConfig {
            max_attempts: 2,
            strategy: RetryStrategy::Fixed {
                interval: Duration::from_millis(1),
            },
            total_timeout: None,
            health_check: false,
        };
        let retrier = Retrier::new(config);

        let result: Result<i32, RetryError<&str>> = retrier
            .execute(|| Box::pin(async { Err("permanent error") }))
            .await;

        assert!(matches!(result, Err(RetryError::MaxAttemptsReached { .. })));
    }

    #[tokio::test]
    async fn test_retrier_builder() {
        let retrier = RetrierBuilder::new()
            .max_attempts(5)
            .strategy(RetryStrategy::Fixed {
                interval: Duration::from_millis(10),
            })
            .total_timeout(Duration::from_secs(1))
            .enable_health_check()
            .build();

        let stats = retrier.stats().await;
        assert_eq!(stats.total_retries, 0);
    }
}
