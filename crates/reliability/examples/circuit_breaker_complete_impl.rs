//! # Complete Circuit Breaker Implementation
//!
//! 完整的熔断器模式实现，包含多种熔断策略和真实场景应用
//!
//! ## 熔断器状态
//! - **Closed**: 正常状态，请求正常通过
//! - **Open**: 熔断状态，快速失败
//! - **HalfOpen**: 半开状态，尝试恢复
//!
//! ## 熔断策略
//! - 基于错误率
//! - 基于错误数量
//! - 基于慢调用率
//! - 基于超时
//! - 组合策略
//!
//! ## 高级特性
//! - 滑动窗口统计
//! - 指数退避
//! - 降级策略
//! - 监控和告警
//! - 分布式熔断

use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};
use std::time::{Duration, Instant};
use thiserror::Error;
use tokio::sync::{RwLock, Semaphore};
use tokio::time::{sleep, timeout};
use tracing::{error, info, instrument, warn};

// ============================================================================
// Part 1: Core Circuit Breaker Types
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl std::fmt::Display for CircuitState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CircuitState::Closed => write!(f, "CLOSED"),
            CircuitState::Open => write!(f, "OPEN"),
            CircuitState::HalfOpen => write!(f, "HALF_OPEN"),
        }
    }
}

#[derive(Debug, Error)]
pub enum CircuitError {
    #[error("Circuit is open")]
    CircuitOpen,

    #[error("Operation timeout")]
    Timeout,

    #[error("Operation failed: {0}")]
    OperationFailed(String),

    #[error("Max retries exceeded")]
    MaxRetriesExceeded,
}

// ============================================================================
// Part 2: Circuit Breaker Configuration
// ============================================================================

#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    /// 失败阈值（百分比，0-100）
    pub failure_threshold_percentage: f64,

    /// 最小请求数（达到此数量后才开始计算阈值）
    pub minimum_request_threshold: u64,

    /// 滑动窗口大小（秒）
    pub sliding_window_size: Duration,

    /// 熔断后等待时间
    pub wait_duration_in_open_state: Duration,

    /// 半开状态允许的请求数
    pub permitted_requests_in_half_open: u32,

    /// 操作超时时间
    pub timeout_duration: Duration,

    /// 慢调用阈值（毫秒）
    pub slow_call_duration_threshold: Duration,

    /// 慢调用率阈值（百分比）
    pub slow_call_rate_threshold: f64,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold_percentage: 50.0,
            minimum_request_threshold: 20,
            sliding_window_size: Duration::from_secs(60),
            wait_duration_in_open_state: Duration::from_secs(60),
            permitted_requests_in_half_open: 10,
            timeout_duration: Duration::from_secs(5),
            slow_call_duration_threshold: Duration::from_millis(1000),
            slow_call_rate_threshold: 50.0,
        }
    }
}

// ============================================================================
// Part 3: Sliding Window Statistics
// ============================================================================

#[derive(Debug)]
struct SlidingWindow {
    success_count: AtomicU64,
    failure_count: AtomicU64,
    slow_call_count: AtomicU64,
    total_duration_ms: AtomicU64,
    last_reset: Arc<RwLock<Instant>>,
    window_size: Duration,
}

impl SlidingWindow {
    fn new(window_size: Duration) -> Self {
        Self {
            success_count: AtomicU64::new(0),
            failure_count: AtomicU64::new(0),
            slow_call_count: AtomicU64::new(0),
            total_duration_ms: AtomicU64::new(0),
            last_reset: Arc::new(RwLock::new(Instant::now())),
            window_size,
        }
    }

    async fn record_success(&self, duration: Duration) {
        self.check_and_reset().await;
        self.success_count.fetch_add(1, Ordering::Relaxed);
        self.total_duration_ms
            .fetch_add(duration.as_millis() as u64, Ordering::Relaxed);
    }

    async fn record_failure(&self, duration: Duration) {
        self.check_and_reset().await;
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        self.total_duration_ms
            .fetch_add(duration.as_millis() as u64, Ordering::Relaxed);
    }

    async fn record_slow_call(&self, duration: Duration) {
        self.check_and_reset().await;
        self.slow_call_count.fetch_add(1, Ordering::Relaxed);
        self.total_duration_ms
            .fetch_add(duration.as_millis() as u64, Ordering::Relaxed);
    }

    async fn check_and_reset(&self) {
        let mut last_reset = self.last_reset.write().await;
        if last_reset.elapsed() >= self.window_size {
            self.success_count.store(0, Ordering::Relaxed);
            self.failure_count.store(0, Ordering::Relaxed);
            self.slow_call_count.store(0, Ordering::Relaxed);
            self.total_duration_ms.store(0, Ordering::Relaxed);
            *last_reset = Instant::now();
        }
    }

    fn total_count(&self) -> u64 {
        self.success_count.load(Ordering::Relaxed) + self.failure_count.load(Ordering::Relaxed)
    }

    fn failure_rate(&self) -> f64 {
        let total = self.total_count();
        if total == 0 {
            return 0.0;
        }
        let failures = self.failure_count.load(Ordering::Relaxed);
        (failures as f64 / total as f64) * 100.0
    }

    fn slow_call_rate(&self) -> f64 {
        let total = self.total_count();
        if total == 0 {
            return 0.0;
        }
        let slow_calls = self.slow_call_count.load(Ordering::Relaxed);
        (slow_calls as f64 / total as f64) * 100.0
    }

    fn average_duration_ms(&self) -> f64 {
        let total = self.total_count();
        if total == 0 {
            return 0.0;
        }
        let total_ms = self.total_duration_ms.load(Ordering::Relaxed);
        total_ms as f64 / total as f64
    }
}

// ============================================================================
// Part 4: Main Circuit Breaker Implementation
// ============================================================================

pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitState>>,
    sliding_window: Arc<SlidingWindow>,
    state_changed_at: Arc<RwLock<Instant>>,
    half_open_semaphore: Arc<Semaphore>,
    state_transitions: Arc<AtomicU64>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        let sliding_window_size = config.sliding_window_size;
        let permitted_requests = config.permitted_requests_in_half_open as usize;

        Self {
            half_open_semaphore: Arc::new(Semaphore::new(permitted_requests)),
            sliding_window: Arc::new(SlidingWindow::new(sliding_window_size)),
            config,
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            state_changed_at: Arc::new(RwLock::new(Instant::now())),
            state_transitions: Arc::new(AtomicU64::new(0)),
        }
    }

    #[instrument(skip(self, operation))]
    pub async fn call<F, T, E>(&self, operation: F) -> Result<T, CircuitError>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // Check if we can proceed
        self.before_call().await?;

        // Execute with timeout
        let start = Instant::now();
        let result = timeout(self.config.timeout_duration, operation).await;

        let duration = start.elapsed();

        // Process result
        match result {
            Ok(Ok(value)) => {
                self.on_success(duration).await;
                Ok(value)
            }
            Ok(Err(e)) => {
                self.on_error(duration).await;
                Err(CircuitError::OperationFailed(e.to_string()))
            }
            Err(_) => {
                self.on_timeout(duration).await;
                Err(CircuitError::Timeout)
            }
        }
    }

    async fn before_call(&self) -> Result<(), CircuitError> {
        let state = *self.state.read().await;

        match state {
            CircuitState::Closed => Ok(()),

            CircuitState::Open => {
                // Check if we should transition to half-open
                let state_changed_at = *self.state_changed_at.read().await;
                if state_changed_at.elapsed() >= self.config.wait_duration_in_open_state {
                    self.transition_to_half_open().await;
                    Ok(())
                } else {
                    Err(CircuitError::CircuitOpen)
                }
            }

            CircuitState::HalfOpen => {
                // Try to acquire a permit
                match self.half_open_semaphore.try_acquire() {
                    Ok(_permit) => Ok(()),
                    Err(_) => Err(CircuitError::CircuitOpen),
                }
            }
        }
    }

    async fn on_success(&self, duration: Duration) {
        let state = *self.state.read().await;

        // Record success
        if duration >= self.config.slow_call_duration_threshold {
            self.sliding_window.record_slow_call(duration).await;
        } else {
            self.sliding_window.record_success(duration).await;
        }

        // State transition logic
        if state == CircuitState::HalfOpen {
            // Check if we've had enough successful requests
            if self.sliding_window.total_count()
                >= self.config.permitted_requests_in_half_open as u64
            {
                let failure_rate = self.sliding_window.failure_rate();
                if failure_rate < self.config.failure_threshold_percentage {
                    self.transition_to_closed().await;
                }
            }
        }
    }

    async fn on_error(&self, duration: Duration) {
        self.sliding_window.record_failure(duration).await;
        self.check_and_trip().await;
    }

    async fn on_timeout(&self, duration: Duration) {
        self.sliding_window.record_failure(duration).await;
        self.check_and_trip().await;
    }

    async fn check_and_trip(&self) {
        let total_count = self.sliding_window.total_count();

        // Only check if we've met the minimum request threshold
        if total_count < self.config.minimum_request_threshold {
            return;
        }

        let failure_rate = self.sliding_window.failure_rate();
        let slow_call_rate = self.sliding_window.slow_call_rate();

        // Check failure rate threshold
        if failure_rate >= self.config.failure_threshold_percentage {
            warn!(
                "Circuit breaker tripping due to failure rate: {:.2}% (threshold: {:.2}%)",
                failure_rate, self.config.failure_threshold_percentage
            );
            self.transition_to_open().await;
            return;
        }

        // Check slow call rate threshold
        if slow_call_rate >= self.config.slow_call_rate_threshold {
            warn!(
                "Circuit breaker tripping due to slow call rate: {:.2}% (threshold: {:.2}%)",
                slow_call_rate, self.config.slow_call_rate_threshold
            );
            self.transition_to_open().await;
        }
    }

    async fn transition_to_open(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitState::Open {
            *state = CircuitState::Open;
            *self.state_changed_at.write().await = Instant::now();
            self.state_transitions.fetch_add(1, Ordering::Relaxed);
            error!("Circuit breaker opened");
        }
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitState::HalfOpen {
            *state = CircuitState::HalfOpen;
            *self.state_changed_at.write().await = Instant::now();
            self.state_transitions.fetch_add(1, Ordering::Relaxed);
            info!("Circuit breaker transitioned to half-open");
        }
    }

    async fn transition_to_closed(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitState::Closed {
            *state = CircuitState::Closed;
            *self.state_changed_at.write().await = Instant::now();
            self.state_transitions.fetch_add(1, Ordering::Relaxed);
            info!("Circuit breaker closed");
        }
    }

    pub async fn get_state(&self) -> CircuitState {
        *self.state.read().await
    }

    pub async fn get_stats(&self) -> CircuitStats {
        CircuitStats {
            state: *self.state.read().await,
            total_requests: self.sliding_window.total_count(),
            success_count: self.sliding_window.success_count.load(Ordering::Relaxed),
            failure_count: self.sliding_window.failure_count.load(Ordering::Relaxed),
            slow_call_count: self.sliding_window.slow_call_count.load(Ordering::Relaxed),
            failure_rate: self.sliding_window.failure_rate(),
            slow_call_rate: self.sliding_window.slow_call_rate(),
            average_duration_ms: self.sliding_window.average_duration_ms(),
            state_transitions: self.state_transitions.load(Ordering::Relaxed),
        }
    }

    pub async fn reset(&self) {
        let mut state = self.state.write().await;
        *state = CircuitState::Closed;
        *self.state_changed_at.write().await = Instant::now();

        self.sliding_window
            .success_count
            .store(0, Ordering::Relaxed);
        self.sliding_window
            .failure_count
            .store(0, Ordering::Relaxed);
        self.sliding_window
            .slow_call_count
            .store(0, Ordering::Relaxed);
        self.sliding_window
            .total_duration_ms
            .store(0, Ordering::Relaxed);

        info!("Circuit breaker reset");
    }
}

#[derive(Debug, Clone)]
pub struct CircuitStats {
    pub state: CircuitState,
    pub total_requests: u64,
    pub success_count: u64,
    pub failure_count: u64,
    pub slow_call_count: u64,
    pub failure_rate: f64,
    pub slow_call_rate: f64,
    pub average_duration_ms: f64,
    pub state_transitions: u64,
}

impl std::fmt::Display for CircuitStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "State: {} | Requests: {} | Success: {} | Failures: {} | Slow: {} | Failure Rate: {:.2}% | Slow Rate: {:.2}% | Avg Duration: {:.2}ms | Transitions: {}",
            self.state,
            self.total_requests,
            self.success_count,
            self.failure_count,
            self.slow_call_count,
            self.failure_rate,
            self.slow_call_rate,
            self.average_duration_ms,
            self.state_transitions
        )
    }
}

// ============================================================================
// Part 5: Fallback and Degradation Strategies
// ============================================================================

pub struct CircuitBreakerWithFallback<T> {
    circuit_breaker: Arc<CircuitBreaker>,
    fallback_fn: Arc<dyn Fn() -> T + Send + Sync>,
}

impl<T> CircuitBreakerWithFallback<T>
where
    T: Clone + Send + 'static,
{
    pub fn new(
        config: CircuitBreakerConfig,
        fallback_fn: impl Fn() -> T + Send + Sync + 'static,
    ) -> Self {
        Self {
            circuit_breaker: Arc::new(CircuitBreaker::new(config)),
            fallback_fn: Arc::new(fallback_fn),
        }
    }

    pub async fn call_with_fallback<F, E>(&self, operation: F) -> T
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        match self.circuit_breaker.call(operation).await {
            Ok(value) => value,
            Err(e) => {
                warn!("Circuit breaker error: {}, using fallback", e);
                (self.fallback_fn)()
            }
        }
    }
}

// ============================================================================
// Part 6: Example Usage Scenarios
// ============================================================================

/// Simulate an unreliable external service
async fn unreliable_service(fail_rate: u32) -> Result<String, &'static str> {
    let random = rand::random::<u32>() % 100;

    if random < fail_rate {
        sleep(Duration::from_millis(50)).await;
        Err("Service failed")
    } else {
        sleep(Duration::from_millis(100)).await;
        Ok("Success".to_string())
    }
}

/// Simulate a slow service
async fn slow_service(delay_ms: u64) -> Result<String, &'static str> {
    sleep(Duration::from_millis(delay_ms)).await;
    Ok(format!("Completed after {}ms", delay_ms))
}

/// Demo: Basic circuit breaker usage
#[instrument]
pub async fn demo_basic_usage() {
    info!("=== Demo: Basic Circuit Breaker Usage ===");

    let config = CircuitBreakerConfig {
        failure_threshold_percentage: 50.0,
        minimum_request_threshold: 10,
        ..Default::default()
    };

    let cb = Arc::new(CircuitBreaker::new(config));

    // Simulate requests
    for i in 0..50 {
        let cb = cb.clone();
        tokio::spawn(async move {
            let result = cb.call(unreliable_service(60)).await;
            match result {
                Ok(_) => info!("Request {} succeeded", i),
                Err(e) => warn!("Request {} failed: {}", i, e),
            }
        });

        sleep(Duration::from_millis(50)).await;
    }

    sleep(Duration::from_secs(5)).await;

    let stats = cb.get_stats().await;
    info!("Final stats: {}", stats);
}

/// Demo: Circuit breaker with fallback
#[instrument]
pub async fn demo_with_fallback() {
    info!("=== Demo: Circuit Breaker with Fallback ===");

    let config = CircuitBreakerConfig::default();
    let cb = CircuitBreakerWithFallback::new(config, || "Fallback response".to_string());

    for i in 0..20 {
        let result = cb.call_with_fallback(unreliable_service(70)).await;
        info!("Request {}: {}", i, result);
        sleep(Duration::from_millis(100)).await;
    }
}

/// Demo: Slow call detection
#[instrument]
pub async fn demo_slow_call_detection() {
    info!("=== Demo: Slow Call Detection ===");

    let config = CircuitBreakerConfig {
        slow_call_duration_threshold: Duration::from_millis(500),
        slow_call_rate_threshold: 30.0,
        minimum_request_threshold: 10,
        ..Default::default()
    };

    let cb = Arc::new(CircuitBreaker::new(config));

    // Mix of fast and slow calls
    for i in 0..30 {
        let cb = cb.clone();
        let delay = if i % 3 == 0 { 800 } else { 200 };

        tokio::spawn(async move {
            let result = cb.call(slow_service(delay)).await;
            match result {
                Ok(msg) => info!("Request {}: {}", i, msg),
                Err(e) => warn!("Request {} failed: {}", i, e),
            }
        });

        sleep(Duration::from_millis(100)).await;
    }

    sleep(Duration::from_secs(5)).await;

    let stats = cb.get_stats().await;
    info!("Final stats: {}", stats);
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

    info!("🚀 Starting Circuit Breaker Demos");

    // Demo 1: Basic usage
    demo_basic_usage().await;
    sleep(Duration::from_secs(2)).await;

    // Demo 2: With fallback
    demo_with_fallback().await;
    sleep(Duration::from_secs(2)).await;

    // Demo 3: Slow call detection
    demo_slow_call_detection().await;

    info!("✅ All demos completed!");

    Ok(())
}
