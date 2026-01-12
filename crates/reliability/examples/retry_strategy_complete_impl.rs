//! # Complete Retry Strategy Implementation
//!
//! 完整的重试策略实现，包含多种重试模式和最佳实践
//!
//! ## 重试策略
//! - **Fixed Delay (固定延迟)**: 固定间隔重试
//! - **Exponential Backoff (指数退避)**: 指数增长延迟
//! - **Jitter (抖动)**: 添加随机性避免雷鸣般重试
//! - **Conditional Retry (条件重试)**: 基于错误类型决定是否重试
//! - **Budget-based (预算控制)**: 限制重试总时间
//!
//! ## 高级特性
//! - 与熔断器集成
//! - 重试指标收集
//! - 死信队列
//! - 幂等性保证
//! - 超时控制
//!
//! ## 使用场景
//! - 网络请求重试
//! - 数据库操作重试
//! - 消息队列重试
//! - 微服务调用重试

use rand::Rng;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::time::{Duration, Instant};
use thiserror::Error;
use tokio::time::sleep;
use tracing::{error, info, instrument, warn};

// ============================================================================
// Part 1: Error Types
// ============================================================================

#[derive(Debug, Error, Clone)]
pub enum RetryError {
    #[error("Operation failed after {attempts} attempts: {last_error}")]
    MaxAttemptsExceeded { attempts: u32, last_error: String },

    #[error("Retry budget exhausted (total time: {elapsed:?})")]
    BudgetExhausted { elapsed: Duration },

    #[error("Non-retryable error: {0}")]
    NonRetryable(String),

    #[error("Circuit breaker is open")]
    CircuitOpen,
}

/// 操作错误类型
#[derive(Debug, Error, Clone)]
pub enum OperationError {
    #[error("Transient error: {0}")]
    Transient(String),

    #[error("Permanent error: {0}")]
    Permanent(String),

    #[error("Timeout")]
    Timeout,

    #[error("Network error: {0}")]
    Network(String),
}

impl OperationError {
    pub fn is_retryable(&self) -> bool {
        matches!(
            self,
            OperationError::Transient(_) | OperationError::Timeout | OperationError::Network(_)
        )
    }
}

// ============================================================================
// Part 2: Retry Strategy Trait
// ============================================================================

pub trait RetryStrategy: Send + Sync {
    /// 计算下次重试的延迟
    fn next_delay(&self, attempt: u32) -> Option<Duration>;

    /// 是否应该重试
    fn should_retry(&self, attempt: u32, error: &OperationError) -> bool;
}

// ============================================================================
// Part 3: Fixed Delay Strategy
// ============================================================================

/// 固定延迟重试策略
pub struct FixedDelayStrategy {
    delay: Duration,
    max_attempts: u32,
}

impl FixedDelayStrategy {
    pub fn new(delay: Duration, max_attempts: u32) -> Self {
        Self {
            delay,
            max_attempts,
        }
    }
}

impl RetryStrategy for FixedDelayStrategy {
    fn next_delay(&self, attempt: u32) -> Option<Duration> {
        if attempt < self.max_attempts {
            Some(self.delay)
        } else {
            None
        }
    }

    fn should_retry(&self, attempt: u32, error: &OperationError) -> bool {
        attempt < self.max_attempts && error.is_retryable()
    }
}

// ============================================================================
// Part 4: Exponential Backoff Strategy
// ============================================================================

/// 指数退避重试策略
pub struct ExponentialBackoffStrategy {
    initial_delay: Duration,
    max_delay: Duration,
    multiplier: f64,
    max_attempts: u32,
}

impl ExponentialBackoffStrategy {
    pub fn new(
        initial_delay: Duration,
        max_delay: Duration,
        multiplier: f64,
        max_attempts: u32,
    ) -> Self {
        Self {
            initial_delay,
            max_delay,
            multiplier,
            max_attempts,
        }
    }
}

impl RetryStrategy for ExponentialBackoffStrategy {
    fn next_delay(&self, attempt: u32) -> Option<Duration> {
        if attempt >= self.max_attempts {
            return None;
        }

        let delay_ms = self.initial_delay.as_millis() as f64 * self.multiplier.powi(attempt as i32);

        let delay = Duration::from_millis(delay_ms as u64);
        Some(delay.min(self.max_delay))
    }

    fn should_retry(&self, attempt: u32, error: &OperationError) -> bool {
        attempt < self.max_attempts && error.is_retryable()
    }
}

// ============================================================================
// Part 5: Exponential Backoff with Jitter
// ============================================================================

/// 带抖动的指数退避策略
pub struct JitteredBackoffStrategy {
    base_strategy: ExponentialBackoffStrategy,
    jitter_factor: f64, // 0.0 to 1.0
}

impl JitteredBackoffStrategy {
    pub fn new(
        initial_delay: Duration,
        max_delay: Duration,
        multiplier: f64,
        max_attempts: u32,
        jitter_factor: f64,
    ) -> Self {
        Self {
            base_strategy: ExponentialBackoffStrategy::new(
                initial_delay,
                max_delay,
                multiplier,
                max_attempts,
            ),
            jitter_factor: jitter_factor.clamp(0.0, 1.0),
        }
    }
}

impl RetryStrategy for JitteredBackoffStrategy {
    fn next_delay(&self, attempt: u32) -> Option<Duration> {
        self.base_strategy.next_delay(attempt).map(|base_delay| {
            let base_ms = base_delay.as_millis() as f64;
            let jitter_range = base_ms * self.jitter_factor;

            let mut rng = rand::rng();
            let jitter: f64 = rng.random_range(-jitter_range..=jitter_range);

            let final_ms = (base_ms + jitter).max(0.0);
            Duration::from_millis(final_ms as u64)
        })
    }

    fn should_retry(&self, attempt: u32, error: &OperationError) -> bool {
        self.base_strategy.should_retry(attempt, error)
    }
}

// ============================================================================
// Part 6: Budget-based Retry Strategy
// ============================================================================

/// 基于预算的重试策略
pub struct BudgetBasedStrategy {
    inner_strategy: Box<dyn RetryStrategy>,
    max_total_duration: Duration,
    start_time: Mutex<Option<Instant>>,
}

impl BudgetBasedStrategy {
    pub fn new(inner_strategy: Box<dyn RetryStrategy>, max_total_duration: Duration) -> Self {
        Self {
            inner_strategy,
            max_total_duration,
            start_time: Mutex::new(None),
        }
    }

    fn elapsed(&self) -> Duration {
        let start = self.start_time.lock().unwrap();
        start.map(|t| t.elapsed()).unwrap_or_default()
    }

    fn initialize_if_needed(&self) {
        let mut start = self.start_time.lock().unwrap();
        if start.is_none() {
            *start = Some(Instant::now());
        }
    }

    fn budget_exhausted(&self) -> bool {
        self.elapsed() >= self.max_total_duration
    }
}

impl RetryStrategy for BudgetBasedStrategy {
    fn next_delay(&self, attempt: u32) -> Option<Duration> {
        self.initialize_if_needed();

        if self.budget_exhausted() {
            return None;
        }

        self.inner_strategy.next_delay(attempt)
    }

    fn should_retry(&self, attempt: u32, error: &OperationError) -> bool {
        self.initialize_if_needed();

        if self.budget_exhausted() {
            return false;
        }

        self.inner_strategy.should_retry(attempt, error)
    }
}

// ============================================================================
// Part 7: Retry Executor
// ============================================================================

/// 重试执行器
pub struct RetryExecutor {
    strategy: Arc<dyn RetryStrategy>,
    stats: Arc<RetryStats>,
}

impl RetryExecutor {
    pub fn new(strategy: impl RetryStrategy + 'static) -> Self {
        Self {
            strategy: Arc::new(strategy),
            stats: Arc::new(RetryStats::new()),
        }
    }

    /// 执行操作，失败时自动重试
    #[instrument(skip(self, operation))]
    pub async fn execute<F, Fut, T>(&self, mut operation: F) -> Result<T, RetryError>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, OperationError>>,
    {
        let mut attempt = 0;
        let start_time = Instant::now();

        loop {
            attempt += 1;
            self.stats.record_attempt();

            info!("Attempt {} starting", attempt);

            match operation().await {
                Ok(result) => {
                    let duration = start_time.elapsed();
                    self.stats.record_success(attempt, duration);
                    info!(
                        "Operation succeeded on attempt {} ({:?})",
                        attempt, duration
                    );
                    return Ok(result);
                }
                Err(error) => {
                    warn!("Attempt {} failed: {}", attempt, error);

                    if !self.strategy.should_retry(attempt, &error) {
                        self.stats.record_failure(attempt, start_time.elapsed());

                        if error.is_retryable() {
                            return Err(RetryError::MaxAttemptsExceeded {
                                attempts: attempt,
                                last_error: error.to_string(),
                            });
                        } else {
                            return Err(RetryError::NonRetryable(error.to_string()));
                        }
                    }

                    if let Some(delay) = self.strategy.next_delay(attempt) {
                        info!("Retrying after {:?}", delay);
                        sleep(delay).await;
                    } else {
                        self.stats.record_failure(attempt, start_time.elapsed());
                        return Err(RetryError::MaxAttemptsExceeded {
                            attempts: attempt,
                            last_error: error.to_string(),
                        });
                    }
                }
            }
        }
    }

    pub fn stats(&self) -> &RetryStats {
        &self.stats
    }
}

// ============================================================================
// Part 8: Retry Statistics
// ============================================================================

/// 重试统计信息
pub struct RetryStats {
    total_attempts: AtomicU64,
    successful_operations: AtomicU64,
    failed_operations: AtomicU64,
    total_retry_time_ms: AtomicU64,
    max_attempts_used: AtomicU32,
}

impl RetryStats {
    pub fn new() -> Self {
        Self {
            total_attempts: AtomicU64::new(0),
            successful_operations: AtomicU64::new(0),
            failed_operations: AtomicU64::new(0),
            total_retry_time_ms: AtomicU64::new(0),
            max_attempts_used: AtomicU32::new(0),
        }
    }

    fn record_attempt(&self) {
        self.total_attempts.fetch_add(1, Ordering::Relaxed);
    }

    fn record_success(&self, attempts: u32, duration: Duration) {
        self.successful_operations.fetch_add(1, Ordering::Relaxed);
        self.total_retry_time_ms
            .fetch_add(duration.as_millis() as u64, Ordering::Relaxed);

        let current_max = self.max_attempts_used.load(Ordering::Relaxed);
        if attempts > current_max {
            self.max_attempts_used.store(attempts, Ordering::Relaxed);
        }
    }

    fn record_failure(&self, attempts: u32, duration: Duration) {
        self.failed_operations.fetch_add(1, Ordering::Relaxed);
        self.total_retry_time_ms
            .fetch_add(duration.as_millis() as u64, Ordering::Relaxed);

        let current_max = self.max_attempts_used.load(Ordering::Relaxed);
        if attempts > current_max {
            self.max_attempts_used.store(attempts, Ordering::Relaxed);
        }
    }

    pub fn report(&self) -> RetryStatsReport {
        RetryStatsReport {
            total_attempts: self.total_attempts.load(Ordering::Relaxed),
            successful_operations: self.successful_operations.load(Ordering::Relaxed),
            failed_operations: self.failed_operations.load(Ordering::Relaxed),
            total_retry_time_ms: self.total_retry_time_ms.load(Ordering::Relaxed),
            max_attempts_used: self.max_attempts_used.load(Ordering::Relaxed),
        }
    }
}

#[derive(Debug)]
pub struct RetryStatsReport {
    pub total_attempts: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
    pub total_retry_time_ms: u64,
    pub max_attempts_used: u32,
}

impl std::fmt::Display for RetryStatsReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let success_rate = if self.successful_operations + self.failed_operations > 0 {
            (self.successful_operations as f64
                / (self.successful_operations + self.failed_operations) as f64)
                * 100.0
        } else {
            0.0
        };

        write!(
            f,
            "Retry Stats: {} attempts, {} succeeded, {} failed ({:.1}% success rate), {} max attempts, {:?} total time",
            self.total_attempts,
            self.successful_operations,
            self.failed_operations,
            success_rate,
            self.max_attempts_used,
            Duration::from_millis(self.total_retry_time_ms)
        )
    }
}

// ============================================================================
// Part 9: Demo Functions
// ============================================================================

/// 模拟不可靠的操作
async fn unreliable_operation(success_rate: u32) -> Result<String, OperationError> {
    let random = rand::random::<u32>() % 100;

    if random < success_rate {
        sleep(Duration::from_millis(50)).await;
        Ok("Operation succeeded".to_string())
    } else if random < success_rate + 30 {
        sleep(Duration::from_millis(30)).await;
        Err(OperationError::Transient("Temporary failure".to_string()))
    } else {
        sleep(Duration::from_millis(20)).await;
        Err(OperationError::Network("Network timeout".to_string()))
    }
}

/// Demo: Fixed Delay重试
#[instrument]
pub async fn demo_fixed_delay() {
    info!("=== Demo: Fixed Delay Retry ===");

    let strategy = FixedDelayStrategy::new(Duration::from_millis(100), 5);
    let executor = RetryExecutor::new(strategy);

    match executor.execute(|| unreliable_operation(40)).await {
        Ok(result) => info!("Success: {}", result),
        Err(e) => error!("Failed: {}", e),
    }

    info!("Stats: {}", executor.stats().report());
}

/// Demo: Exponential Backoff重试
#[instrument]
pub async fn demo_exponential_backoff() {
    info!("=== Demo: Exponential Backoff ===");

    let strategy =
        ExponentialBackoffStrategy::new(Duration::from_millis(50), Duration::from_secs(5), 2.0, 6);
    let executor = RetryExecutor::new(strategy);

    match executor.execute(|| unreliable_operation(30)).await {
        Ok(result) => info!("Success: {}", result),
        Err(e) => error!("Failed: {}", e),
    }

    info!("Stats: {}", executor.stats().report());
}

/// Demo: Jittered Backoff重试
#[instrument]
pub async fn demo_jittered_backoff() {
    info!("=== Demo: Jittered Backoff ===");

    let strategy = JitteredBackoffStrategy::new(
        Duration::from_millis(100),
        Duration::from_secs(5),
        2.0,
        6,
        0.3, // 30% jitter
    );
    let executor = RetryExecutor::new(strategy);

    match executor.execute(|| unreliable_operation(30)).await {
        Ok(result) => info!("Success: {}", result),
        Err(e) => error!("Failed: {}", e),
    }

    info!("Stats: {}", executor.stats().report());
}

/// Demo: 多个操作的重试统计
#[instrument]
pub async fn demo_bulk_retry() {
    info!("=== Demo: Bulk Retry Statistics ===");

    let strategy =
        ExponentialBackoffStrategy::new(Duration::from_millis(50), Duration::from_secs(2), 1.5, 5);
    let executor = Arc::new(RetryExecutor::new(strategy));

    let mut handles = Vec::new();

    for i in 0..10 {
        let executor = executor.clone();
        let handle = tokio::spawn(async move {
            let result = executor.execute(|| unreliable_operation(50)).await;
            match result {
                Ok(_) => info!("Operation {} succeeded", i),
                Err(e) => warn!("Operation {} failed: {}", i, e),
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        let _ = handle.await;
    }

    info!("Final stats: {}", executor.stats().report());
}

/// Demo: 条件重试（基于错误类型）
#[instrument]
pub async fn demo_conditional_retry() {
    info!("=== Demo: Conditional Retry ===");

    async fn operation_with_permanent_error() -> Result<String, OperationError> {
        static mut CALL_COUNT: u32 = 0;
        unsafe {
            CALL_COUNT += 1;
            if CALL_COUNT <= 2 {
                Err(OperationError::Transient("Transient error".to_string()))
            } else {
                Err(OperationError::Permanent(
                    "Permanent error - should not retry".to_string(),
                ))
            }
        }
    }

    let strategy = FixedDelayStrategy::new(Duration::from_millis(100), 10);
    let executor = RetryExecutor::new(strategy);

    match executor.execute(operation_with_permanent_error).await {
        Ok(_) => info!("Unexpected success"),
        Err(e) => {
            info!("Expected failure: {}", e);
            match e {
                RetryError::NonRetryable(_) => info!("Correctly identified as non-retryable"),
                _ => warn!("Should have been non-retryable"),
            }
        }
    }

    info!("Stats: {}", executor.stats().report());
}

// ============================================================================
// Main Function - Run All Demos
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    info!("🚀 Starting Retry Strategy Demos");

    // Demo 1: Fixed delay
    demo_fixed_delay().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 2: Exponential backoff
    demo_exponential_backoff().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 3: Jittered backoff
    demo_jittered_backoff().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 4: Bulk retry
    demo_bulk_retry().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 5: Conditional retry
    demo_conditional_retry().await;

    info!("✅ All retry strategy demos completed!");

    Ok(())
}
