//! # 超时模式实现
//!
//! 基于理论文档中的容错设计模式，实现超时控制机制。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.1.3节

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::timeout;

/// 超时配置
#[derive(Debug, Clone)]
pub struct TimeoutConfig {
    /// 默认超时时间
    pub default_timeout: Duration,
    /// 最大超时时间
    pub max_timeout: Duration,
    /// 最小超时时间
    pub min_timeout: Duration,
    /// 是否启用统计信息
    pub enable_stats: bool,
    /// 是否启用自适应超时
    pub enable_adaptive: bool,
    /// 自适应超时因子
    pub adaptive_factor: f64,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            default_timeout: Duration::from_secs(30),
            max_timeout: Duration::from_secs(300), // 5分钟
            min_timeout: Duration::from_millis(100),
            enable_stats: true,
            enable_adaptive: true,
            adaptive_factor: 1.5,
        }
    }
}

/// 超时统计信息
#[derive(Debug, Default)]
pub struct TimeoutStats {
    /// 总超时次数
    pub total_timeouts: AtomicU64,
    /// 成功完成次数
    pub successful_completions: AtomicU64,
    /// 平均执行时间（微秒）
    pub average_execution_time: AtomicUsize,
    /// 最大执行时间（微秒）
    pub max_execution_time: AtomicUsize,
    /// 最小执行时间（微秒）
    pub min_execution_time: AtomicUsize,
    /// 当前自适应超时时间（微秒）
    pub current_adaptive_timeout: AtomicUsize,
}

/// 超时状态
#[derive(Debug, Clone)]
pub struct TimeoutStatus {
    pub active_timeouts: usize,
    pub total_timeouts: u64,
    pub timeout_rate: f64,
    pub average_execution_time: Duration,
    pub current_adaptive_timeout: Duration,
}

/// 超时错误类型
#[derive(Debug, PartialEq, thiserror::Error)]
pub enum TimeoutError {
    #[error("操作超时: {timeout:?}")]
    Timeout { timeout: Duration },

    #[error("超时配置无效: {timeout:?}")]
    InvalidTimeout { timeout: Duration },

    #[error("自适应超时计算失败")]
    AdaptiveCalculationFailed,
}

/// 超时器实现
pub struct Timeout {
    config: TimeoutConfig,
    stats: Arc<TimeoutStats>,
    adaptive_timeout: Arc<RwLock<Duration>>,
}

impl Timeout {
    /// 创建新的超时器
    pub fn new(config: TimeoutConfig) -> Self {
        let adaptive_timeout = Arc::new(RwLock::new(config.default_timeout));

        Self {
            config,
            stats: Arc::new(TimeoutStats::default()),
            adaptive_timeout,
        }
    }

    /// 执行带超时的异步操作
    pub async fn execute<F, R, E>(&self, operation: F) -> Result<R, TimeoutError>
    where
        F: std::future::Future<Output = Result<R, E>>,
    {
        self.execute_with_timeout(operation, self.get_timeout())
            .await
    }

    /// 执行带指定超时的异步操作
    pub async fn execute_with_timeout<F, R, E>(
        &self,
        operation: F,
        timeout_duration: Duration,
    ) -> Result<R, TimeoutError>
    where
        F: std::future::Future<Output = Result<R, E>>,
    {
        // 验证超时时间
        if !self.is_valid_timeout(timeout_duration) {
            return Err(TimeoutError::InvalidTimeout {
                timeout: timeout_duration,
            });
        }

        let start_time = Instant::now();

        match timeout(timeout_duration, operation).await {
            Ok(Ok(result)) => {
                let execution_time = start_time.elapsed();
                self.update_stats_on_success(execution_time).await;
                Ok(result)
            }
            Ok(Err(_)) => {
                // 操作失败但不是超时
                let execution_time = start_time.elapsed();
                self.update_stats_on_success(execution_time).await;
                Err(TimeoutError::Timeout {
                    timeout: timeout_duration,
                })
            }
            Err(_) => {
                // 超时
                self.update_stats_on_timeout().await;
                Err(TimeoutError::Timeout {
                    timeout: timeout_duration,
                })
            }
        }
    }

    /// 执行带自适应超时的异步操作
    pub async fn execute_adaptive<F, R, E>(&self, operation: F) -> Result<R, TimeoutError>
    where
        F: std::future::Future<Output = Result<R, E>>,
    {
        if !self.config.enable_adaptive {
            return self.execute(operation).await;
        }

        let adaptive_timeout = self.get_adaptive_timeout().await;
        self.execute_with_timeout(operation, adaptive_timeout).await
    }

    /// 获取当前超时时间
    pub fn get_timeout(&self) -> Duration {
        self.config.default_timeout
    }

    /// 获取自适应超时时间
    pub async fn get_adaptive_timeout(&self) -> Duration {
        let adaptive = self.adaptive_timeout.read().await;
        *adaptive
    }

    /// 设置超时时间
    pub fn set_timeout(&mut self, timeout: Duration) -> Result<(), TimeoutError> {
        if !self.is_valid_timeout(timeout) {
            return Err(TimeoutError::InvalidTimeout { timeout });
        }

        self.config.default_timeout = timeout;
        Ok(())
    }

    /// 获取统计信息
    pub fn stats(&self) -> &TimeoutStats {
        &self.stats
    }

    /// 获取状态
    pub async fn status(&self) -> TimeoutStatus {
        let total_timeouts = self.stats.total_timeouts.load(Ordering::Acquire);
        let successful_completions = self.stats.successful_completions.load(Ordering::Acquire);
        let timeout_rate = if total_timeouts + successful_completions > 0 {
            total_timeouts as f64 / (total_timeouts + successful_completions) as f64
        } else {
            0.0
        };

        let average_execution_time =
            Duration::from_micros(self.stats.average_execution_time.load(Ordering::Acquire) as u64);

        let current_adaptive_timeout = self.get_adaptive_timeout().await;

        TimeoutStatus {
            active_timeouts: 0, // 需要额外的跟踪机制
            total_timeouts,
            timeout_rate,
            average_execution_time,
            current_adaptive_timeout,
        }
    }

    /// 重置统计信息
    pub async fn reset(&self) {
        self.stats.total_timeouts.store(0, Ordering::Release);
        self.stats
            .successful_completions
            .store(0, Ordering::Release);
        self.stats
            .average_execution_time
            .store(0, Ordering::Release);
        self.stats.max_execution_time.store(0, Ordering::Release);
        self.stats.min_execution_time.store(0, Ordering::Release);

        // 重置自适应超时
        let mut adaptive = self.adaptive_timeout.write().await;
        *adaptive = self.config.default_timeout;
    }

    /// 验证超时时间是否有效
    fn is_valid_timeout(&self, timeout: Duration) -> bool {
        timeout >= self.config.min_timeout && timeout <= self.config.max_timeout
    }

    /// 更新成功统计信息
    async fn update_stats_on_success(&self, execution_time: Duration) {
        let execution_time_micros = execution_time.as_micros() as usize;

        self.stats
            .successful_completions
            .fetch_add(1, Ordering::Relaxed);

        // 更新平均执行时间
        let total_completions = self.stats.successful_completions.load(Ordering::Acquire) as usize;
        let current_avg = self.stats.average_execution_time.load(Ordering::Acquire);
        let new_avg =
            (current_avg * (total_completions - 1) + execution_time_micros) / total_completions;
        self.stats
            .average_execution_time
            .store(new_avg, Ordering::Release);

        // 更新最大执行时间
        let current_max = self.stats.max_execution_time.load(Ordering::Acquire);
        if execution_time_micros > current_max {
            self.stats
                .max_execution_time
                .store(execution_time_micros, Ordering::Release);
        }

        // 更新最小执行时间
        let current_min = self.stats.min_execution_time.load(Ordering::Acquire);
        if current_min == 0 || execution_time_micros < current_min {
            self.stats
                .min_execution_time
                .store(execution_time_micros, Ordering::Release);
        }

        // 更新自适应超时
        if self.config.enable_adaptive {
            self.update_adaptive_timeout(execution_time).await;
        }
    }

    /// 更新超时统计信息
    async fn update_stats_on_timeout(&self) {
        self.stats.total_timeouts.fetch_add(1, Ordering::Relaxed);

        // 超时时增加自适应超时时间
        if self.config.enable_adaptive {
            self.increase_adaptive_timeout().await;
        }
    }

    /// 更新自适应超时时间
    async fn update_adaptive_timeout(&self, execution_time: Duration) {
        let mut adaptive = self.adaptive_timeout.write().await;
        let current_timeout = *adaptive;

        // 基于执行时间调整超时时间
        let new_timeout = if execution_time > current_timeout {
            // 执行时间接近超时时间，增加超时时间
            current_timeout.mul_f64(self.config.adaptive_factor)
        } else if execution_time < current_timeout / 2 {
            // 执行时间远小于超时时间，减少超时时间
            current_timeout.div_f64(self.config.adaptive_factor)
        } else {
            // 执行时间适中，保持当前超时时间
            current_timeout
        };

        // 确保新超时时间在有效范围内
        let new_timeout = new_timeout
            .max(self.config.min_timeout)
            .min(self.config.max_timeout);

        *adaptive = new_timeout;
        self.stats
            .current_adaptive_timeout
            .store(new_timeout.as_micros() as usize, Ordering::Release);
    }

    /// 增加自适应超时时间
    async fn increase_adaptive_timeout(&self) {
        let mut adaptive = self.adaptive_timeout.write().await;
        let new_timeout = adaptive
            .mul_f64(self.config.adaptive_factor)
            .min(self.config.max_timeout);

        *adaptive = new_timeout;
        self.stats
            .current_adaptive_timeout
            .store(new_timeout.as_micros() as usize, Ordering::Release);
    }
}

/// 超时构建器
pub struct TimeoutBuilder {
    config: TimeoutConfig,
}

impl TimeoutBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: TimeoutConfig::default(),
        }
    }

    /// 设置默认超时时间
    pub fn default_timeout(mut self, timeout: Duration) -> Self {
        self.config.default_timeout = timeout;
        self
    }

    /// 设置最大超时时间
    pub fn max_timeout(mut self, timeout: Duration) -> Self {
        self.config.max_timeout = timeout;
        self
    }

    /// 设置最小超时时间
    pub fn min_timeout(mut self, timeout: Duration) -> Self {
        self.config.min_timeout = timeout;
        self
    }

    /// 启用统计信息
    pub fn enable_stats(mut self) -> Self {
        self.config.enable_stats = true;
        self
    }

    /// 启用自适应超时
    pub fn enable_adaptive(mut self) -> Self {
        self.config.enable_adaptive = true;
        self
    }

    /// 设置自适应因子
    pub fn adaptive_factor(mut self, factor: f64) -> Self {
        self.config.adaptive_factor = factor;
        self
    }

    /// 构建超时器
    pub fn build(self) -> Timeout {
        Timeout::new(self.config)
    }
}

impl Default for TimeoutBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 超时管理器 - 支持多个超时器的管理
pub struct TimeoutManager {
    timeouts: Arc<RwLock<HashMap<String, Arc<Timeout>>>>,
}

impl TimeoutManager {
    /// 创建新的超时管理器
    pub fn new() -> Self {
        Self {
            timeouts: Arc::new(RwLock::new(HashMap::new())),
        }
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

    /// 获取所有超时器的状态
    pub async fn get_all_status(&self) -> HashMap<String, TimeoutStatus> {
        let timeouts = self.timeouts.read().await;
        let mut status_map = HashMap::new();

        for (name, timeout) in timeouts.iter() {
            status_map.insert(name.clone(), timeout.status().await);
        }

        status_map
    }

    /// 重置所有超时器
    pub async fn reset_all(&self) {
        let timeouts = self.timeouts.read().await;
        for timeout in timeouts.values() {
            timeout.reset().await;
        }
    }
}

impl Default for TimeoutManager {
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
    async fn test_timeout_success() {
        let config = TimeoutConfig::default();
        let timeout = Timeout::new(config);

        let result: Result<i32, TimeoutError> =
            timeout.execute::<_, i32, &str>(async { Ok(42) }).await;

        assert_eq!(result, Ok(42));
    }

    #[tokio::test]
    async fn test_timeout_timeout() {
        let config = TimeoutConfig {
            default_timeout: Duration::from_millis(100),
            ..Default::default()
        };
        let timeout = Timeout::new(config);

        let result: Result<i32, TimeoutError> = timeout
            .execute::<_, i32, &str>(async {
                sleep(Duration::from_millis(200)).await;
                Ok(42)
            })
            .await;

        assert!(matches!(result, Err(TimeoutError::Timeout { .. })));
    }

    #[tokio::test]
    async fn test_timeout_adaptive() {
        let config = TimeoutConfig {
            enable_adaptive: true,
            adaptive_factor: 1.5,
            ..Default::default()
        };
        let timeout = Timeout::new(config);

        // 执行快速操作
        let result: Result<i32, TimeoutError> = timeout
            .execute_adaptive::<_, i32, &str>(async { Ok(42) })
            .await;

        assert_eq!(result, Ok(42));

        // 检查自适应超时是否调整
        let adaptive_timeout = timeout.get_adaptive_timeout().await;
        assert!(adaptive_timeout > Duration::from_millis(0));
    }

    #[tokio::test]
    async fn test_timeout_builder() {
        let timeout = TimeoutBuilder::new()
            .default_timeout(Duration::from_secs(10))
            .max_timeout(Duration::from_secs(60))
            .min_timeout(Duration::from_millis(100))
            .enable_stats()
            .enable_adaptive()
            .adaptive_factor(2.0)
            .build();

        let status = timeout.status().await;
        assert_eq!(status.timeout_rate, 0.0);
    }

    #[tokio::test]
    async fn test_timeout_manager() {
        let manager = TimeoutManager::new();

        let config = TimeoutConfig::default();
        let timeout = manager.get_or_create_timeout("test_timeout", config).await;

        let result: Result<i32, TimeoutError> =
            timeout.execute::<_, i32, &str>(async { Ok(42) }).await;

        assert_eq!(result, Ok(42));

        let all_status = manager.get_all_status().await;
        assert!(all_status.contains_key("test_timeout"));
    }

    #[tokio::test]
    async fn test_timeout_stats() {
        let config = TimeoutConfig::default();
        let timeout = Timeout::new(config);

        // 执行一些操作
        let _: Result<i32, TimeoutError> = timeout.execute::<_, i32, &str>(async { Ok(42) }).await;

        let stats = timeout.stats();
        assert!(stats.successful_completions.load(Ordering::Acquire) > 0);
    }
}
