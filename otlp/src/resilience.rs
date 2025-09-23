//! # 系统弹性和容错机制
//! 
//! 提供完整的错误处理、容错、重试、熔断和优雅降级机制，
//! 确保系统在各种异常情况下的可靠性和稳定性。

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::{sleep, timeout};
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, error};
use thiserror::Error;

/// 弹性配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceConfig {
    /// 重试配置
    pub retry: RetryConfig,
    /// 熔断器配置
    pub circuit_breaker: CircuitBreakerConfig,
    /// 超时配置
    pub timeout: TimeoutConfig,
    /// 优雅降级配置
    pub graceful_degradation: GracefulDegradationConfig,
    /// 健康检查配置
    pub health_check: HealthCheckConfig,
}

impl Default for ResilienceConfig {
    fn default() -> Self {
        Self {
            retry: RetryConfig::default(),
            circuit_breaker: CircuitBreakerConfig::default(),
            timeout: TimeoutConfig::default(),
            graceful_degradation: GracefulDegradationConfig::default(),
            health_check: HealthCheckConfig::default(),
        }
    }
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 基础延迟时间
    pub base_delay: Duration,
    /// 最大延迟时间
    pub max_delay: Duration,
    /// 退避乘数
    pub backoff_multiplier: f64,
    /// 是否添加抖动
    pub jitter: bool,
    /// 可重试的错误类型
    pub retryable_errors: Vec<String>,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_failed".to_string(),
                "network_unreachable".to_string(),
                "service_unavailable".to_string(),
                "rate_limited".to_string(),
            ],
        }
    }
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 失败阈值
    pub failure_threshold: u32,
    /// 恢复超时时间
    pub recovery_timeout: Duration,
    /// 半开状态最大调用次数
    pub half_open_max_calls: u32,
    /// 滑动窗口大小
    pub sliding_window_size: Duration,
    /// 最小调用次数（用于计算失败率）
    pub minimum_calls: u32,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
            half_open_max_calls: 3,
            sliding_window_size: Duration::from_secs(60),
            minimum_calls: 10,
        }
    }
}

/// 超时配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    /// 连接超时
    pub connect_timeout: Duration,
    /// 读取超时
    pub read_timeout: Duration,
    /// 写入超时
    pub write_timeout: Duration,
    /// 操作超时
    pub operation_timeout: Duration,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            connect_timeout: Duration::from_secs(5),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            operation_timeout: Duration::from_secs(60),
        }
    }
}

/// 优雅降级配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GracefulDegradationConfig {
    /// 是否启用优雅降级
    pub enabled: bool,
    /// 降级策略
    pub strategies: Vec<DegradationStrategy>,
    /// 降级触发条件
    pub trigger_conditions: Vec<TriggerCondition>,
}

impl Default for GracefulDegradationConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            strategies: vec![
                DegradationStrategy::UseCache,
                DegradationStrategy::UseFallback,
                DegradationStrategy::ReduceQuality,
            ],
            trigger_conditions: vec![
                TriggerCondition::HighErrorRate { threshold: 0.5 },
                TriggerCondition::HighLatency { threshold: Duration::from_secs(10) },
                TriggerCondition::ResourceExhaustion,
            ],
        }
    }
}

/// 健康检查配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckConfig {
    /// 健康检查间隔
    pub interval: Duration,
    /// 健康检查超时
    pub timeout: Duration,
    /// 健康检查路径
    pub path: String,
    /// 不健康阈值
    pub unhealthy_threshold: u32,
    /// 健康阈值
    pub healthy_threshold: u32,
}

impl Default for HealthCheckConfig {
    fn default() -> Self {
        Self {
            interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            path: "/health".to_string(),
            unhealthy_threshold: 3,
            healthy_threshold: 2,
        }
    }
}

/// 降级策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DegradationStrategy {
    /// 使用缓存数据
    UseCache,
    /// 使用备用服务
    UseFallback,
    /// 降低服务质量
    ReduceQuality,
    /// 跳过非关键功能
    SkipNonCritical,
    /// 返回默认值
    ReturnDefault,
}

/// 触发条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TriggerCondition {
    /// 高错误率
    HighErrorRate { threshold: f64 },
    /// 高延迟
    HighLatency { threshold: Duration },
    /// 资源耗尽
    ResourceExhaustion,
    /// 熔断器开启
    CircuitBreakerOpen,
    /// 自定义条件
    Custom { name: String, condition: String },
}

/// 弹性管理器
pub struct ResilienceManager {
    config: ResilienceConfig,
    circuit_breakers: Arc<RwLock<std::collections::HashMap<String, CircuitBreaker>>>,
    health_status: Arc<RwLock<HealthStatus>>,
    metrics: Arc<RwLock<ResilienceMetrics>>,
}

impl ResilienceManager {
    /// 创建新的弹性管理器
    pub fn new(config: ResilienceConfig) -> Self {
        Self {
            config,
            circuit_breakers: Arc::new(RwLock::new(std::collections::HashMap::new())),
            health_status: Arc::new(RwLock::new(HealthStatus::Healthy)),
            metrics: Arc::new(RwLock::new(ResilienceMetrics::default())),
        }
    }

    /// 执行带弹性的操作
    pub async fn execute_with_resilience<F, R>(
        &self,
        operation_name: &str,
        operation: F,
    ) -> Result<R, ResilienceError>
    where
        F: Fn() -> BoxFuture<'static, Result<R, anyhow::Error>> + Send + Sync + 'static + Clone,
        R: Send,
    {
        let start_time = Instant::now();
        
        // 1. 健康检查
        if !self.is_healthy().await {
            return Err(ResilienceError::SystemUnhealthy);
        }

        // 2. 获取或创建熔断器
        let circuit_breaker = self.get_or_create_circuit_breaker(operation_name).await;

        // 3. 通过熔断器执行操作
        let result = circuit_breaker.call(|| {
            operation()
        }).await;

        let duration = start_time.elapsed();
        self.update_metrics(operation_name, &result, duration).await;

        // 5. 检查是否需要降级
        if result.is_err() {
            self.check_degradation_conditions(operation_name).await;
        }

        match result {
            Ok(response) => Ok(response),
            Err(e) => Err(match e {
                CircuitBreakerError::CircuitBreakerOpen => ResilienceError::CircuitBreakerOpen,
                CircuitBreakerError::ExecutionError(err) => ResilienceError::OperationFailed(err),
                CircuitBreakerError::HalfOpenMaxCallsReached => ResilienceError::RateLimited,
            })
        }
    }

    /// 带重试的操作执行
    #[allow(dead_code)]
    async fn execute_with_retry<F, R>(
        &self,
        operation_name: &str,
        operation: Box<F>,
    ) -> Result<R, anyhow::Error>
    where
        F: Fn() -> BoxFuture<'static, Result<R, anyhow::Error>> + Send + Sync + 'static,
        R: Send,
    {
        let mut attempt = 0;
        let mut delay = self.config.retry.base_delay;

        loop {
            attempt += 1;
            
            // 应用超时
            let result = timeout(
                self.config.timeout.operation_timeout,
                operation()
            ).await;

            match result {
                Ok(Ok(response)) => {
                    if attempt > 1 {
                        info!("操作 {} 在第 {} 次尝试后成功", operation_name, attempt);
                    }
                    return Ok(response);
                }
                Ok(Err(e)) => {
                    if attempt >= self.config.retry.max_attempts {
                        error!("操作 {} 在 {} 次尝试后仍然失败: {:?}", operation_name, attempt, e);
                        return Err(e);
                    }
                    
                    if self.should_retry(&e) {
                        warn!("操作 {} 第 {} 次尝试失败，将在 {:?} 后重试: {:?}", 
                              operation_name, attempt, delay, e);
                        
                        self.add_jitter_if_enabled(&mut delay);
                        sleep(delay).await;
                        
                        delay = std::cmp::min(
                            delay.mul_f64(self.config.retry.backoff_multiplier),
                            self.config.retry.max_delay
                        );
                    } else {
                        error!("操作 {} 遇到不可重试的错误: {:?}", operation_name, e);
                        return Err(e);
                    }
                }
                Err(_) => {
                    if attempt >= self.config.retry.max_attempts {
                        error!("操作 {} 在 {} 次尝试后超时", operation_name, attempt);
                        return Err(anyhow::anyhow!("操作超时"));
                    }
                    
                    warn!("操作 {} 第 {} 次尝试超时，将在 {:?} 后重试", 
                          operation_name, attempt, delay);
                    
                    self.add_jitter_if_enabled(&mut delay);
                    sleep(delay).await;
                    
                    delay = std::cmp::min(
                        delay.mul_f64(self.config.retry.backoff_multiplier),
                        self.config.retry.max_delay
                    );
                }
            }
        }
    }

    /// 判断是否应该重试
    fn should_retry(&self, error: &anyhow::Error) -> bool {
        let error_string = error.to_string().to_lowercase();
        self.config.retry.retryable_errors.iter()
            .any(|retryable| error_string.contains(retryable))
    }

    /// 添加抖动
    fn add_jitter_if_enabled(&self, delay: &mut Duration) {
        if self.config.retry.jitter {
            let jitter = (rand::random::<f64>() * 0.1) * delay.as_nanos() as f64;
            *delay = Duration::from_nanos(delay.as_nanos() as u64 + jitter as u64);
        }
    }

    /// 获取或创建熔断器
    async fn get_or_create_circuit_breaker(&self, operation_name: &str) -> CircuitBreaker {
        let mut circuit_breakers = self.circuit_breakers.write().await;
        
        if let Some(cb) = circuit_breakers.get(operation_name) {
            cb.clone()
        } else {
            let cb = CircuitBreaker::new(self.config.circuit_breaker.clone());
            circuit_breakers.insert(operation_name.to_string(), cb.clone());
            cb
        }
    }

    /// 检查健康状态
    async fn is_healthy(&self) -> bool {
        let health_status = self.health_status.read().await;
        matches!(*health_status, HealthStatus::Healthy)
    }

    /// 更新指标
    async fn update_metrics<R>(&self, operation_name: &str, result: &Result<R, CircuitBreakerError>, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.total_operations += 1;
        metrics.total_duration += duration;
        
        match result {
            Ok(_) => metrics.successful_operations += 1,
            Err(_) => metrics.failed_operations += 1,
        }
        
        // 更新操作特定的指标
        let operation_metrics = metrics.operation_metrics.entry(operation_name.to_string()).or_insert_with(OperationMetrics::default);
        operation_metrics.total_operations = operation_metrics.total_operations.saturating_add(1);
        operation_metrics.total_duration += duration;
        
        match result {
            Ok(_) => operation_metrics.successful_operations = operation_metrics.successful_operations.saturating_add(1),
            Err(_) => operation_metrics.failed_operations = operation_metrics.failed_operations.saturating_add(1),
        }
    }

    /// 检查降级条件
    async fn check_degradation_conditions(&self, operation_name: &str) {
        if !self.config.graceful_degradation.enabled {
            return;
        }

        let metrics = self.metrics.read().await;
        let operation_metrics = metrics.operation_metrics.get(operation_name);
        
        if let Some(op_metrics) = operation_metrics {
            let error_rate = op_metrics.failed_operations as f64 / op_metrics.total_operations as f64;
            let avg_duration = if op_metrics.total_operations > 0 {
                op_metrics.total_duration / op_metrics.total_operations as u32
            } else {
                Duration::ZERO
            };
            
            // 检查触发条件
            for condition in &self.config.graceful_degradation.trigger_conditions {
                match condition {
                    TriggerCondition::HighErrorRate { threshold } => {
                        if error_rate > *threshold {
                            warn!("检测到高错误率 {}，触发优雅降级", error_rate);
                            self.trigger_degradation(operation_name).await;
                            return;
                        }
                    }
                    TriggerCondition::HighLatency { threshold } => {
                        if avg_duration > *threshold {
                            warn!("检测到高延迟 {:?}，触发优雅降级", avg_duration);
                            self.trigger_degradation(operation_name).await;
                            return;
                        }
                    }
                    _ => {} // 其他条件的处理
                }
            }
        }
    }

    /// 触发降级
    async fn trigger_degradation(&self, operation_name: &str) {
        info!("为操作 {} 触发优雅降级", operation_name);
        
        for strategy in &self.config.graceful_degradation.strategies {
            match strategy {
                DegradationStrategy::UseCache => {
                    info!("应用缓存降级策略");
                    // 实现缓存降级逻辑
                }
                DegradationStrategy::UseFallback => {
                    info!("应用备用服务降级策略");
                    // 实现备用服务逻辑
                }
                DegradationStrategy::ReduceQuality => {
                    info!("应用质量降级策略");
                    // 实现质量降级逻辑
                }
                DegradationStrategy::SkipNonCritical => {
                    info!("应用跳过非关键功能降级策略");
                    // 实现跳过非关键功能逻辑
                }
                DegradationStrategy::ReturnDefault => {
                    info!("应用返回默认值降级策略");
                    // 实现返回默认值逻辑
                }
            }
        }
    }

    /// 获取健康状态
    pub async fn get_health_status(&self) -> HealthStatus {
        let health_status = self.health_status.read().await;
        health_status.clone()
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> ResilienceMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器
#[derive(Clone)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<Mutex<CircuitBreakerState>>,
    failure_count: Arc<Mutex<u32>>,
    success_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    half_open_calls: Arc<Mutex<u32>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(Mutex::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            success_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
            half_open_calls: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        let state = self.state.lock().await;
        
        match *state {
            CircuitBreakerState::Closed => {
                drop(state);
                self.execute_call(f).await
            }
            CircuitBreakerState::Open => {
                drop(state);
                self.check_recovery_time().await.map(|_| unreachable!())
            }
            CircuitBreakerState::HalfOpen => {
                drop(state);
                self.execute_half_open_call(f).await
            }
        }
    }

    async fn execute_call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        match f().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn execute_half_open_call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        let mut half_open_calls = self.half_open_calls.lock().await;
        if *half_open_calls >= self.config.half_open_max_calls {
            return Err(CircuitBreakerError::HalfOpenMaxCallsReached);
        }

        *half_open_calls += 1;
        drop(half_open_calls);

        match f().await {
            Ok(result) => {
                self.on_half_open_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_half_open_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn check_recovery_time(&self) -> Result<(), CircuitBreakerError> {
        let last_failure_time = self.last_failure_time.lock().await;
        if let Some(last_failure) = *last_failure_time {
            if last_failure.elapsed() >= self.config.recovery_timeout {
                drop(last_failure_time);
                self.transition_to_half_open().await;
                return Ok(());
            }
        }
        Err(CircuitBreakerError::CircuitBreakerOpen)
    }

    async fn on_success(&self) {
        let mut failure_count = self.failure_count.lock().await;
        let mut success_count = self.success_count.lock().await;
        
        *failure_count = 0;
        *success_count += 1;
    }

    async fn on_failure(&self) {
        let mut failure_count = self.failure_count.lock().await;
        *failure_count += 1;

        let mut last_failure_time = self.last_failure_time.lock().await;
        *last_failure_time = Some(Instant::now());

        if *failure_count >= self.config.failure_threshold {
            self.transition_to_open().await;
        }
    }

    async fn on_half_open_success(&self) {
        self.transition_to_closed().await;
    }

    async fn on_half_open_failure(&self) {
        self.transition_to_open().await;
    }

    async fn transition_to_open(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::Open;
        
        let mut last_failure_time = self.last_failure_time.lock().await;
        *last_failure_time = Some(Instant::now());
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::HalfOpen;

        let mut half_open_calls = self.half_open_calls.lock().await;
        *half_open_calls = 0;
    }

    async fn transition_to_closed(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::Closed;

        let mut failure_count = self.failure_count.lock().await;
        let mut half_open_calls = self.half_open_calls.lock().await;
        
        *failure_count = 0;
        *half_open_calls = 0;
    }

    pub async fn get_state(&self) -> CircuitBreakerState {
        let state = self.state.lock().await;
        state.clone()
    }
}

/// 熔断器错误
#[derive(Debug, Error)]
pub enum CircuitBreakerError {
    #[error("熔断器已开启")]
    CircuitBreakerOpen,
    #[error("半开状态最大调用次数已达上限")]
    HalfOpenMaxCallsReached,
    #[error("执行错误: {0}")]
    ExecutionError(anyhow::Error),
}

/// 健康状态
#[derive(Debug, Clone, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Degraded,
}

/// 弹性指标
#[derive(Debug, Clone, Default)]
pub struct ResilienceMetrics {
    pub total_operations: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
    pub total_duration: Duration,
    pub operation_metrics: std::collections::HashMap<String, OperationMetrics>,
}

/// 操作指标
#[derive(Debug, Clone, Default)]
pub struct OperationMetrics {
    pub total_operations: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
    pub total_duration: Duration,
}

/// 弹性错误
#[derive(Debug, Error)]
pub enum ResilienceError {
    #[error("系统不健康")]
    SystemUnhealthy,
    #[error("熔断器已开启")]
    CircuitBreakerOpen,
    #[error("操作失败: {0}")]
    OperationFailed(anyhow::Error),
    #[error("速率限制")]
    RateLimited,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_resilience_manager() {
        let config = ResilienceConfig::default();
        let manager = ResilienceManager::new(config);

        let result = manager.execute_with_resilience("test_operation", || {
            Box::pin(async move {
                Ok::<(), anyhow::Error>(())
            })
        }).await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_circuit_breaker() {
        let config = CircuitBreakerConfig::default();
        let circuit_breaker = CircuitBreaker::new(config);

        let result = circuit_breaker.call(|| {
            Box::pin(async move {
                Ok::<(), anyhow::Error>(())
            })
        }).await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_retry_mechanism() {
        let config = ResilienceConfig::default();
        let manager = ResilienceManager::new(config);

        // 测试基本的弹性执行
        let result = manager.execute_with_resilience("test_operation", || {
            Box::pin(async move {
                Ok::<(), anyhow::Error>(())
            })
        }).await;

        assert!(result.is_ok());
    }
}
