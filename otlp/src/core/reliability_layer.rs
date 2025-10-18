//! 可靠性增强层
//! 
//! 提供重试、熔断、超时等可靠性机制

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

/// 可靠性管理器
/// 
/// 提供各种可靠性增强策略：
/// - 重试机制 (Retry)
/// - 熔断器 (Circuit Breaker)
/// - 超时控制 (Timeout)
/// - 降级策略 (Fallback)
pub struct ReliabilityManager {
    /// 重试配置
    retry_config: RetryConfig,
    
    /// 熔断器
    circuit_breaker: Arc<Mutex<CircuitBreaker>>,
    
    /// 超时配置
    timeout_config: TimeoutConfig,
    
    /// 统计信息
    stats: Arc<Mutex<ReliabilityStats>>,
}

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_retries: usize,
    
    /// 初始重试延迟
    pub initial_delay: Duration,
    
    /// 最大重试延迟
    pub max_delay: Duration,
    
    /// 延迟倍增因子
    pub multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_delay: Duration::from_millis(1000),
            max_delay: Duration::from_secs(30),
            multiplier: 2.0,
        }
    }
}

/// 超时配置
#[derive(Debug, Clone)]
pub struct TimeoutConfig {
    /// 默认超时时间
    pub default_timeout: Duration,
    
    /// 是否启用超时
    pub enabled: bool,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            default_timeout: Duration::from_secs(30),
            enabled: true,
        }
    }
}

/// 熔断器
/// 
/// 实现熔断机制，当失败率超过阈值时自动打开熔断器
#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    /// 熔断器状态
    state: CircuitBreakerState,
    
    /// 失败计数
    failure_count: u32,
    
    /// 成功计数
    success_count: u32,
    
    /// 失败率阈值 (0.0 - 1.0)
    failure_threshold: f64,
    
    /// 最小请求数（只有达到此数量才会触发熔断）
    min_requests: u32,
    
    /// 开放状态持续时间
    open_duration: Duration,
    
    /// 上次状态改变时间
    last_state_change: Option<Instant>,
}

/// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitBreakerState {
    /// 关闭（正常）
    Closed,
    /// 开启（熔断）
    Open,
    /// 半开（尝试恢复）
    HalfOpen,
}

impl Default for CircuitBreaker {
    fn default() -> Self {
        Self {
            state: CircuitBreakerState::Closed,
            failure_count: 0,
            success_count: 0,
            failure_threshold: 0.5, // 50%
            min_requests: 10,
            open_duration: Duration::from_secs(60),
            last_state_change: None,
        }
    }
}

impl CircuitBreaker {
    /// 记录成功
    pub fn record_success(&mut self) {
        self.success_count += 1;
        
        match self.state {
            CircuitBreakerState::HalfOpen => {
                // 半开状态成功，尝试关闭
                if self.success_count >= 3 {
                    self.close();
                }
            }
            _ => {
                // 检查是否应该关闭
                self.check_and_update_state();
            }
        }
    }
    
    /// 记录失败
    pub fn record_failure(&mut self) {
        self.failure_count += 1;
        
        match self.state {
            CircuitBreakerState::HalfOpen => {
                // 半开状态失败，重新打开
                self.open();
            }
            CircuitBreakerState::Closed => {
                // 检查是否应该打开
                self.check_and_update_state();
            }
            _ => {}
        }
    }
    
    /// 检查是否可以执行请求
    pub fn can_execute(&mut self) -> bool {
        match self.state {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => {
                // 检查是否可以转换到半开状态
                if let Some(last_change) = self.last_state_change {
                    if last_change.elapsed() >= self.open_duration {
                        self.half_open();
                        return true;
                    }
                }
                false
            }
            CircuitBreakerState::HalfOpen => true,
        }
    }
    
    /// 打开熔断器
    fn open(&mut self) {
        self.state = CircuitBreakerState::Open;
        self.last_state_change = Some(Instant::now());
    }
    
    /// 关闭熔断器
    fn close(&mut self) {
        self.state = CircuitBreakerState::Closed;
        self.failure_count = 0;
        self.success_count = 0;
        self.last_state_change = Some(Instant::now());
    }
    
    /// 设置为半开状态
    fn half_open(&mut self) {
        self.state = CircuitBreakerState::HalfOpen;
        self.failure_count = 0;
        self.success_count = 0;
        self.last_state_change = Some(Instant::now());
    }
    
    /// 检查并更新状态
    fn check_and_update_state(&mut self) {
        let total = self.failure_count + self.success_count;
        
        if total >= self.min_requests {
            let failure_rate = self.failure_count as f64 / total as f64;
            
            if failure_rate >= self.failure_threshold {
                self.open();
            }
        }
    }
    
    /// 获取当前状态
    pub fn state(&self) -> CircuitBreakerState {
        self.state
    }
}

/// 可靠性统计信息
#[derive(Debug, Clone, Default)]
pub struct ReliabilityStats {
    /// 总重试次数
    pub total_retries: u64,
    
    /// 成功重试次数
    pub successful_retries: u64,
    
    /// 熔断次数
    pub circuit_breaks: u64,
    
    /// 超时次数
    pub timeouts: u64,
    
    /// 降级次数
    pub fallbacks: u64,
}

impl ReliabilityStats {
    /// 计算重试成功率
    pub fn retry_success_rate(&self) -> f64 {
        if self.total_retries == 0 {
            0.0
        } else {
            self.successful_retries as f64 / self.total_retries as f64
        }
    }
}

impl ReliabilityManager {
    /// 创建新的可靠性管理器
    pub fn new() -> Self {
        Self {
            retry_config: RetryConfig::default(),
            circuit_breaker: Arc::new(Mutex::new(CircuitBreaker::default())),
            timeout_config: TimeoutConfig::default(),
            stats: Arc::new(Mutex::new(ReliabilityStats::default())),
        }
    }
    
    /// 使用自定义配置创建
    pub fn with_configs(
        retry_config: RetryConfig,
        timeout_config: TimeoutConfig,
    ) -> Self {
        Self {
            retry_config,
            circuit_breaker: Arc::new(Mutex::new(CircuitBreaker::default())),
            timeout_config,
            stats: Arc::new(Mutex::new(ReliabilityStats::default())),
        }
    }
    
    /// 使用自定义重试配置创建
    pub fn with_retry_config(retry_config: RetryConfig) -> Self {
        Self {
            retry_config,
            circuit_breaker: Arc::new(Mutex::new(CircuitBreaker::default())),
            timeout_config: TimeoutConfig::default(),
            stats: Arc::new(Mutex::new(ReliabilityStats::default())),
        }
    }
    
    /// 获取重试配置
    pub fn retry_config(&self) -> &RetryConfig {
        &self.retry_config
    }
    
    /// 获取超时配置
    pub fn timeout_config(&self) -> &TimeoutConfig {
        &self.timeout_config
    }
    
    /// 获取统计信息
    pub async fn stats(&self) -> ReliabilityStats {
        self.stats.lock().await.clone()
    }
    
    /// 获取熔断器状态
    pub async fn circuit_breaker_state(&self) -> CircuitBreakerState {
        self.circuit_breaker.lock().await.state()
    }
    
    /// 执行带重试的操作
    /// 
    /// # 示例
    /// 
    /// ```rust,no_run
    /// # use otlp::core::ReliabilityManager;
    /// # async fn example() {
    /// let manager = ReliabilityManager::new();
    /// 
    /// let result = manager.retry(|| async {
    ///     // 可能失败的操作
    ///     Ok::<_, Box<dyn std::error::Error>>(())
    /// }).await;
    /// # }
    /// ```
    pub async fn retry<F, Fut, T, E>(&self, mut operation: F) -> Result<T, E>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        let mut attempts = 0;
        let mut delay = self.retry_config.initial_delay;
        
        // 更新统计
        {
            let mut stats = self.stats.lock().await;
            stats.total_retries += 1;
        }
        
        loop {
            match operation().await {
                Ok(result) => {
                    // 记录成功
                    self.circuit_breaker.lock().await.record_success();
                    
                    if attempts > 0 {
                        let mut stats = self.stats.lock().await;
                        stats.successful_retries += 1;
                    }
                    
                    return Ok(result);
                }
                Err(e) => {
                    // 记录失败
                    self.circuit_breaker.lock().await.record_failure();
                    
                    attempts += 1;
                    
                    if attempts >= self.retry_config.max_retries {
                        return Err(e);
                    }
                    
                    // 等待后重试
                    tokio::time::sleep(delay).await;
                    
                    // 指数退避
                    delay = std::cmp::min(
                        Duration::from_millis((delay.as_millis() as f64 * self.retry_config.multiplier) as u64),
                        self.retry_config.max_delay
                    );
                }
            }
        }
    }
    
    /// 执行带超时和重试的操作
    pub async fn retry_with_timeout<F, Fut, T, E>(
        &self,
        mut operation: F,
        timeout: Duration,
    ) -> Result<T, String>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 检查熔断器
        {
            let mut breaker = self.circuit_breaker.lock().await;
            if !breaker.can_execute() {
                let mut stats = self.stats.lock().await;
                stats.circuit_breaks += 1;
                return Err("Circuit breaker is open".to_string());
            }
        }
        
        let mut attempts = 0;
        let mut delay = self.retry_config.initial_delay;
        
        loop {
            // 带超时执行
            match tokio::time::timeout(timeout, operation()).await {
                Ok(Ok(result)) => {
                    // 成功
                    self.circuit_breaker.lock().await.record_success();
                    return Ok(result);
                }
                Ok(Err(e)) => {
                    // 操作失败
                    self.circuit_breaker.lock().await.record_failure();
                    
                    attempts += 1;
                    
                    if attempts >= self.retry_config.max_retries {
                        return Err(format!("Operation failed after {} attempts: {}", attempts, e));
                    }
                    
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(
                        Duration::from_millis((delay.as_millis() as f64 * self.retry_config.multiplier) as u64),
                        self.retry_config.max_delay
                    );
                }
                Err(_) => {
                    // 超时
                    let mut stats = self.stats.lock().await;
                    stats.timeouts += 1;
                    
                    attempts += 1;
                    
                    if attempts >= self.retry_config.max_retries {
                        return Err(format!("Operation timed out after {} attempts", attempts));
                    }
                    
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(
                        Duration::from_millis((delay.as_millis() as f64 * self.retry_config.multiplier) as u64),
                        self.retry_config.max_delay
                    );
                }
            }
        }
    }
    
    /// 执行带降级的操作
    /// 
    /// 如果主操作失败，自动执行降级操作
    pub async fn with_fallback<F, Fut, FB, FutB, T>(
        &self,
        operation: F,
        fallback: FB,
    ) -> T
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Option<T>>,
        FB: FnOnce() -> FutB,
        FutB: std::future::Future<Output = T>,
    {
        match operation().await {
            Some(result) => result,
            None => {
                // 记录降级
                let mut stats = self.stats.lock().await;
                stats.fallbacks += 1;
                
                fallback().await
            }
        }
    }
}

impl Default for ReliabilityManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reliability_manager_creation() {
        let manager = ReliabilityManager::new();
        assert_eq!(manager.retry_config().max_retries, 3);
        assert_eq!(manager.timeout_config().default_timeout, Duration::from_secs(30));
    }

    #[test]
    fn test_custom_retry_config() {
        let config = RetryConfig {
            max_retries: 5,
            initial_delay: Duration::from_millis(500),
            max_delay: Duration::from_secs(60),
            multiplier: 1.5,
        };
        let manager = ReliabilityManager::with_retry_config(config);
        assert_eq!(manager.retry_config().max_retries, 5);
    }

    #[tokio::test]
    async fn test_retry_success() {
        let manager = ReliabilityManager::new();
        
        let attempts = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(0));
        let attempts_clone = attempts.clone();
        
        let result = manager.retry(|| {
            let att = attempts_clone.clone();
            async move {
                let count = att.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if count < 1 {
                    Err("Error")
                } else {
                    Ok("Success")
                }
            }
        }).await;
        
        assert_eq!(result, Ok("Success"));
        assert_eq!(attempts.load(std::sync::atomic::Ordering::SeqCst), 2);
    }

    #[test]
    fn test_circuit_breaker_states() {
        let mut breaker = CircuitBreaker::default();
        
        // 初始状态是关闭
        assert_eq!(breaker.state(), CircuitBreakerState::Closed);
        assert!(breaker.can_execute());
        
        // 记录多次失败
        for _ in 0..15 {
            breaker.record_failure();
        }
        
        // 应该打开熔断器
        assert_eq!(breaker.state(), CircuitBreakerState::Open);
    }

    #[test]
    fn test_circuit_breaker_recovery() {
        let mut breaker = CircuitBreaker::default();
        breaker.failure_threshold = 0.5;
        breaker.min_requests = 10;
        breaker.open_duration = Duration::from_millis(100);
        
        // 触发熔断
        for _ in 0..15 {
            breaker.record_failure();
        }
        assert_eq!(breaker.state(), CircuitBreakerState::Open);
        
        // 等待后转为半开
        std::thread::sleep(Duration::from_millis(150));
        breaker.can_execute();
        
        // 记录成功，应该关闭
        for _ in 0..3 {
            breaker.record_success();
        }
        assert_eq!(breaker.state(), CircuitBreakerState::Closed);
    }

    #[tokio::test]
    async fn test_retry_with_timeout() {
        let manager = ReliabilityManager::new();
        
        // 快速成功的操作
        let result = manager.retry_with_timeout(
            || async { Ok::<_, String>("Success") },
            Duration::from_secs(1),
        ).await;
        
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_with_fallback() {
        let manager = ReliabilityManager::new();
        
        // 主操作失败，使用降级
        let result = manager.with_fallback(
            || async { None },
            || async { "Fallback result" },
        ).await;
        
        assert_eq!(result, "Fallback result");
        
        // 检查统计
        let stats = manager.stats().await;
        assert_eq!(stats.fallbacks, 1);
    }

    #[tokio::test]
    async fn test_reliability_stats() {
        let manager = ReliabilityManager::new();
        
        // 执行一些操作
        let _ = manager.retry(|| async {
            Ok::<_, String>("Success")
        }).await;
        
        let stats = manager.stats().await;
        assert!(stats.total_retries > 0);
    }

    #[test]
    fn test_reliability_stats_calculations() {
        let mut stats = ReliabilityStats::default();
        
        stats.total_retries = 10;
        stats.successful_retries = 8;
        
        assert_eq!(stats.retry_success_rate(), 0.8);
    }

    #[tokio::test]
    async fn test_circuit_breaker_state_query() {
        let manager = ReliabilityManager::new();
        
        let state = manager.circuit_breaker_state().await;
        assert_eq!(state, CircuitBreakerState::Closed);
    }
}

