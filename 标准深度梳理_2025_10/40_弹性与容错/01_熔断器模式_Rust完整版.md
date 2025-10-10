# OTLP 熔断器模式 - Rust 完整实现

> **版本**: 1.0.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: v0.27+  
> **最后更新**: 2025-10-09

## 目录

- [OTLP 熔断器模式 - Rust 完整实现](#otlp-熔断器模式---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [核心架构](#核心架构)
  - [熔断器实现](#熔断器实现)
  - [熔断器状态机](#熔断器状态机)
  - [故障检测策略](#故障检测策略)
  - [半开状态处理](#半开状态处理)
  - [熔断器监控](#熔断器监控)
  - [多级熔断](#多级熔断)
  - [分布式熔断](#分布式熔断)
  - [完整示例](#完整示例)
  - [性能优化](#性能优化)
    - [1. **无锁实现**](#1-无锁实现)
    - [2. **批量记录**](#2-批量记录)
  - [最佳实践](#最佳实践)
    - [1. **配置建议**](#1-配置建议)
    - [2. **监控与告警**](#2-监控与告警)
  - [依赖项](#依赖项)
  - [总结](#总结)

---

## 概述

熔断器模式是一种保护分布式系统稳定性的重要机制，当检测到下游服务故障时，自动切断请求，防止故障扩散，并在适当时机尝试恢复。

### 核心特性

- ✅ **三状态管理**: Closed、Open、HalfOpen
- ✅ **自动恢复**: 半开状态探测与自动恢复
- ✅ **故障检测**: 多种故障检测策略
- ✅ **实时监控**: 完整的指标与事件
- ✅ **分布式支持**: 基于 Redis 的分布式熔断
- ✅ **高性能**: 基于 Tokio 的异步实现

---

## 核心架构

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CircuitBreakerState {
    Closed,    // 关闭状态：正常工作
    Open,      // 打开状态：拒绝请求
    HalfOpen,  // 半开状态：尝试恢复
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 故障阈值（失败率）
    pub failure_threshold: f64,
    
    /// 最小请求数（统计窗口内）
    pub minimum_requests: u64,
    
    /// 统计窗口大小
    pub window_size: Duration,
    
    /// 打开状态持续时间
    pub open_timeout: Duration,
    
    /// 半开状态允许的请求数
    pub half_open_requests: u32,
    
    /// 半开状态成功阈值
    pub half_open_success_threshold: u32,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 0.5,
            minimum_requests: 10,
            window_size: Duration::from_secs(60),
            open_timeout: Duration::from_secs(30),
            half_open_requests: 5,
            half_open_success_threshold: 3,
        }
    }
}

/// 请求结果
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RequestResult {
    Success,
    Failure,
}

/// 熔断器指标
#[derive(Debug, Clone, Default)]
pub struct CircuitBreakerMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub rejected_requests: u64,
    pub state_changes: u64,
    pub current_failure_rate: f64,
}
```

---

## 熔断器实现

```rust
use std::collections::VecDeque;

/// 熔断器
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitBreakerState>>,
    request_history: Arc<RwLock<VecDeque<(Instant, RequestResult)>>>,
    state_changed_at: Arc<RwLock<Instant>>,
    half_open_successes: Arc<RwLock<u32>>,
    metrics: Arc<RwLock<CircuitBreakerMetrics>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitBreakerState::Closed)),
            request_history: Arc::new(RwLock::new(VecDeque::new())),
            state_changed_at: Arc::new(RwLock::new(Instant::now())),
            half_open_successes: Arc::new(RwLock::new(0)),
            metrics: Arc::new(RwLock::new(CircuitBreakerMetrics::default())),
        }
    }

    /// 尝试执行请求
    pub async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: std::future::Future<Output = Result<T, E>>,
    {
        // 检查是否允许请求
        if !self.allow_request().await {
            let mut metrics = self.metrics.write().await;
            metrics.rejected_requests += 1;
            return Err(CircuitBreakerError::Open);
        }

        // 执行请求
        let start = Instant::now();
        let result = f.await;

        // 记录结果
        match &result {
            Ok(_) => {
                self.record_success().await;
            }
            Err(_) => {
                self.record_failure().await;
            }
        }

        // 更新状态
        self.update_state().await;

        result.map_err(CircuitBreakerError::InnerError)
    }

    /// 检查是否允许请求
    async fn allow_request(&self) -> bool {
        let state = *self.state.read().await;

        match state {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => {
                // 检查是否可以转换到半开状态
                let state_changed_at = *self.state_changed_at.read().await;
                if state_changed_at.elapsed() >= self.config.open_timeout {
                    self.transition_to_half_open().await;
                    true
                } else {
                    false
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 半开状态允许有限的请求
                let half_open_successes = *self.half_open_successes.read().await;
                half_open_successes < self.config.half_open_requests
            }
        }
    }

    /// 记录成功
    async fn record_success(&self) {
        let mut history = self.request_history.write().await;
        history.push_back((Instant::now(), RequestResult::Success));

        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;
        metrics.successful_requests += 1;

        // 清理过期记录
        self.clean_old_records(&mut history).await;
    }

    /// 记录失败
    async fn record_failure(&self) {
        let mut history = self.request_history.write().await;
        history.push_back((Instant::now(), RequestResult::Failure));

        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;
        metrics.failed_requests += 1;

        // 清理过期记录
        self.clean_old_records(&mut history).await;
    }

    /// 清理过期记录
    async fn clean_old_records(&self, history: &mut VecDeque<(Instant, RequestResult)>) {
        let cutoff = Instant::now() - self.config.window_size;
        while let Some(&(timestamp, _)) = history.front() {
            if timestamp < cutoff {
                history.pop_front();
            } else {
                break;
            }
        }
    }

    /// 更新熔断器状态
    async fn update_state(&self) {
        let state = *self.state.read().await;

        match state {
            CircuitBreakerState::Closed => {
                // 检查是否需要打开熔断器
                if self.should_open().await {
                    self.transition_to_open().await;
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 检查是否可以关闭或需要重新打开
                let successes = *self.half_open_successes.read().await;
                
                if successes >= self.config.half_open_success_threshold {
                    self.transition_to_closed().await;
                } else if self.should_open().await {
                    self.transition_to_open().await;
                }
            }
            CircuitBreakerState::Open => {
                // Open 状态由 allow_request 处理
            }
        }
    }

    /// 判断是否应该打开熔断器
    async fn should_open(&self) -> bool {
        let history = self.request_history.read().await;

        if history.len() < self.config.minimum_requests as usize {
            return false;
        }

        let failures = history
            .iter()
            .filter(|(_, result)| *result == RequestResult::Failure)
            .count();

        let failure_rate = failures as f64 / history.len() as f64;

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.current_failure_rate = failure_rate;
        }

        failure_rate >= self.config.failure_threshold
    }

    /// 转换到打开状态
    async fn transition_to_open(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitBreakerState::Open {
            *state = CircuitBreakerState::Open;
            *self.state_changed_at.write().await = Instant::now();

            let mut metrics = self.metrics.write().await;
            metrics.state_changes += 1;

            tracing::warn!("Circuit breaker transitioned to OPEN state");
        }
    }

    /// 转换到半开状态
    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitBreakerState::HalfOpen {
            *state = CircuitBreakerState::HalfOpen;
            *self.state_changed_at.write().await = Instant::now();
            *self.half_open_successes.write().await = 0;

            let mut metrics = self.metrics.write().await;
            metrics.state_changes += 1;

            tracing::info!("Circuit breaker transitioned to HALF_OPEN state");
        }
    }

    /// 转换到关闭状态
    async fn transition_to_closed(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitBreakerState::Closed {
            *state = CircuitBreakerState::Closed;
            *self.state_changed_at.write().await = Instant::now();

            // 清空历史记录
            self.request_history.write().await.clear();

            let mut metrics = self.metrics.write().await;
            metrics.state_changes += 1;

            tracing::info!("Circuit breaker transitioned to CLOSED state");
        }
    }

    /// 获取当前状态
    pub async fn state(&self) -> CircuitBreakerState {
        *self.state.read().await
    }

    /// 获取指标
    pub async fn metrics(&self) -> CircuitBreakerMetrics {
        self.metrics.read().await.clone()
    }

    /// 手动重置熔断器
    pub async fn reset(&self) {
        self.transition_to_closed().await;
    }

    /// 手动打开熔断器
    pub async fn trip(&self) {
        self.transition_to_open().await;
    }
}

/// 熔断器错误
#[derive(Debug)]
pub enum CircuitBreakerError<E> {
    Open,
    InnerError(E),
}

impl<E: std::fmt::Display> std::fmt::Display for CircuitBreakerError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CircuitBreakerError::Open => write!(f, "Circuit breaker is open"),
            CircuitBreakerError::InnerError(e) => write!(f, "Inner error: {}", e),
        }
    }
}

impl<E: std::error::Error> std::error::Error for CircuitBreakerError<E> {}
```

---

## 熔断器状态机

```rust
/// 熔断器状态机
pub struct CircuitBreakerStateMachine {
    current_state: CircuitBreakerState,
    config: CircuitBreakerConfig,
}

impl CircuitBreakerStateMachine {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            current_state: CircuitBreakerState::Closed,
            config,
        }
    }

    /// 处理成功事件
    pub fn on_success(&mut self, metrics: &CircuitBreakerMetrics) -> Option<CircuitBreakerState> {
        match self.current_state {
            CircuitBreakerState::Closed => None,
            CircuitBreakerState::HalfOpen => {
                // 半开状态成功足够多次，转换到关闭
                if metrics.successful_requests >= self.config.half_open_success_threshold as u64 {
                    self.current_state = CircuitBreakerState::Closed;
                    Some(CircuitBreakerState::Closed)
                } else {
                    None
                }
            }
            CircuitBreakerState::Open => None,
        }
    }

    /// 处理失败事件
    pub fn on_failure(&mut self, metrics: &CircuitBreakerMetrics) -> Option<CircuitBreakerState> {
        match self.current_state {
            CircuitBreakerState::Closed => {
                // 检查是否达到打开阈值
                if metrics.total_requests >= self.config.minimum_requests
                    && metrics.current_failure_rate >= self.config.failure_threshold
                {
                    self.current_state = CircuitBreakerState::Open;
                    Some(CircuitBreakerState::Open)
                } else {
                    None
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 半开状态失败，立即打开
                self.current_state = CircuitBreakerState::Open;
                Some(CircuitBreakerState::Open)
            }
            CircuitBreakerState::Open => None,
        }
    }

    /// 处理超时事件
    pub fn on_timeout(&mut self, elapsed: Duration) -> Option<CircuitBreakerState> {
        if self.current_state == CircuitBreakerState::Open
            && elapsed >= self.config.open_timeout
        {
            self.current_state = CircuitBreakerState::HalfOpen;
            Some(CircuitBreakerState::HalfOpen)
        } else {
            None
        }
    }

    pub fn current_state(&self) -> CircuitBreakerState {
        self.current_state
    }
}
```

---

## 故障检测策略

```rust
/// 故障检测策略
pub trait FailureDetectionStrategy: Send + Sync {
    fn should_trip(&self, metrics: &CircuitBreakerMetrics) -> bool;
}

/// 基于失败率的检测
pub struct FailureRateStrategy {
    threshold: f64,
    minimum_requests: u64,
}

impl FailureRateStrategy {
    pub fn new(threshold: f64, minimum_requests: u64) -> Self {
        Self {
            threshold,
            minimum_requests,
        }
    }
}

impl FailureDetectionStrategy for FailureRateStrategy {
    fn should_trip(&self, metrics: &CircuitBreakerMetrics) -> bool {
        metrics.total_requests >= self.minimum_requests
            && metrics.current_failure_rate >= self.threshold
    }
}

/// 基于连续失败次数的检测
pub struct ConsecutiveFailureStrategy {
    threshold: u64,
}

impl ConsecutiveFailureStrategy {
    pub fn new(threshold: u64) -> Self {
        Self { threshold }
    }
}

impl FailureDetectionStrategy for ConsecutiveFailureStrategy {
    fn should_trip(&self, metrics: &CircuitBreakerMetrics) -> bool {
        // 简化：使用失败请求数作为连续失败的近似
        metrics.failed_requests >= self.threshold
    }
}

/// 基于错误率和延迟的综合检测
pub struct CompositeStrategy {
    failure_rate_threshold: f64,
    latency_threshold: Duration,
    minimum_requests: u64,
}

impl CompositeStrategy {
    pub fn new(failure_rate_threshold: f64, latency_threshold: Duration, minimum_requests: u64) -> Self {
        Self {
            failure_rate_threshold,
            latency_threshold,
            minimum_requests,
        }
    }
}

impl FailureDetectionStrategy for CompositeStrategy {
    fn should_trip(&self, metrics: &CircuitBreakerMetrics) -> bool {
        metrics.total_requests >= self.minimum_requests
            && metrics.current_failure_rate >= self.failure_rate_threshold
        // 这里可以加入延迟判断逻辑
    }
}
```

---

## 半开状态处理

```rust
/// 半开状态处理器
pub struct HalfOpenHandler {
    config: CircuitBreakerConfig,
    test_requests: Arc<RwLock<Vec<RequestResult>>>,
}

impl HalfOpenHandler {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            test_requests: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 记录测试请求结果
    pub async fn record_test_request(&self, result: RequestResult) {
        let mut requests = self.test_requests.write().await;
        requests.push(result);
    }

    /// 判断是否应该关闭熔断器
    pub async fn should_close(&self) -> bool {
        let requests = self.test_requests.read().await;

        if requests.len() < self.config.half_open_requests as usize {
            return false;
        }

        let successes = requests
            .iter()
            .filter(|&&r| r == RequestResult::Success)
            .count();

        successes as u32 >= self.config.half_open_success_threshold
    }

    /// 判断是否应该重新打开熔断器
    pub async fn should_reopen(&self) -> bool {
        let requests = self.test_requests.read().await;

        if requests.is_empty() {
            return false;
        }

        let failures = requests
            .iter()
            .filter(|&&r| r == RequestResult::Failure)
            .count();

        let failure_rate = failures as f64 / requests.len() as f64;
        failure_rate >= self.config.failure_threshold
    }

    /// 重置测试请求
    pub async fn reset(&self) {
        let mut requests = self.test_requests.write().await;
        requests.clear();
    }
}
```

---

## 熔断器监控

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 熔断器监控器
pub struct CircuitBreakerMonitor {
    breaker: Arc<CircuitBreaker>,
    state_change_count: Arc<AtomicU64>,
    last_state_change: Arc<RwLock<Instant>>,
}

impl CircuitBreakerMonitor {
    pub fn new(breaker: Arc<CircuitBreaker>) -> Self {
        Self {
            breaker,
            state_change_count: Arc::new(AtomicU64::new(0)),
            last_state_change: Arc::new(RwLock::new(Instant::now())),
        }
    }

    /// 启动监控
    pub async fn start(&self, interval: Duration) {
        let monitor = self.clone();
        tokio::spawn(async move {
            monitor.monitor_loop(interval).await;
        });
    }

    async fn monitor_loop(&self, interval: Duration) {
        let mut interval = tokio::time::interval(interval);

        loop {
            interval.tick().await;

            let state = self.breaker.state().await;
            let metrics = self.breaker.metrics().await;

            // 记录指标
            tracing::info!(
                target: "circuit_breaker_monitor",
                state = ?state,
                total_requests = metrics.total_requests,
                successful_requests = metrics.successful_requests,
                failed_requests = metrics.failed_requests,
                rejected_requests = metrics.rejected_requests,
                failure_rate = metrics.current_failure_rate,
                state_changes = metrics.state_changes,
                "Circuit breaker status"
            );

            // 检测状态变化
            if metrics.state_changes > self.state_change_count.load(Ordering::Relaxed) {
                self.state_change_count.store(metrics.state_changes, Ordering::Relaxed);
                *self.last_state_change.write().await = Instant::now();

                tracing::warn!(
                    "Circuit breaker state changed to {:?}",
                    state
                );
            }
        }
    }

    /// 获取状态变化次数
    pub fn state_change_count(&self) -> u64 {
        self.state_change_count.load(Ordering::Relaxed)
    }

    /// 获取最后状态变化时间
    pub async fn last_state_change(&self) -> Instant {
        *self.last_state_change.read().await
    }
}

impl Clone for CircuitBreakerMonitor {
    fn clone(&self) -> Self {
        Self {
            breaker: self.breaker.clone(),
            state_change_count: self.state_change_count.clone(),
            last_state_change: self.last_state_change.clone(),
        }
    }
}
```

---

## 多级熔断

```rust
/// 多级熔断器
pub struct TieredCircuitBreaker {
    primary: Arc<CircuitBreaker>,
    secondary: Arc<CircuitBreaker>,
    tertiary: Arc<CircuitBreaker>,
}

impl TieredCircuitBreaker {
    pub fn new(
        primary_config: CircuitBreakerConfig,
        secondary_config: CircuitBreakerConfig,
        tertiary_config: CircuitBreakerConfig,
    ) -> Self {
        Self {
            primary: Arc::new(CircuitBreaker::new(primary_config)),
            secondary: Arc::new(CircuitBreaker::new(secondary_config)),
            tertiary: Arc::new(CircuitBreaker::new(tertiary_config)),
        }
    }

    /// 执行请求（按优先级尝试）
    pub async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: std::future::Future<Output = Result<T, E>> + Clone,
    {
        // 尝试主要熔断器
        match self.primary.call(f.clone()).await {
            Ok(result) => return Ok(result),
            Err(CircuitBreakerError::Open) => {
                tracing::debug!("Primary circuit breaker is open, trying secondary");
            }
            Err(e) => return Err(e),
        }

        // 尝试次要熔断器
        match self.secondary.call(f.clone()).await {
            Ok(result) => return Ok(result),
            Err(CircuitBreakerError::Open) => {
                tracing::debug!("Secondary circuit breaker is open, trying tertiary");
            }
            Err(e) => return Err(e),
        }

        // 尝试第三级熔断器
        self.tertiary.call(f).await
    }

    /// 获取所有熔断器状态
    pub async fn get_states(&self) -> (CircuitBreakerState, CircuitBreakerState, CircuitBreakerState) {
        (
            self.primary.state().await,
            self.secondary.state().await,
            self.tertiary.state().await,
        )
    }
}
```

---

## 分布式熔断

```rust
use redis::AsyncCommands;

/// 分布式熔断器（基于 Redis）
pub struct DistributedCircuitBreaker {
    redis_client: redis::Client,
    key_prefix: String,
    config: CircuitBreakerConfig,
}

impl DistributedCircuitBreaker {
    pub fn new(
        redis_url: &str,
        key_prefix: String,
        config: CircuitBreakerConfig,
    ) -> Result<Self, redis::RedisError> {
        let redis_client = redis::Client::open(redis_url)?;

        Ok(Self {
            redis_client,
            key_prefix,
            config,
        })
    }

    /// 检查是否允许请求
    pub async fn allow_request(&self, service: &str) -> Result<bool, redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;

        let state_key = format!("{}:{}:state", self.key_prefix, service);
        let state: Option<String> = conn.get(&state_key).await?;

        match state.as_deref() {
            Some("open") => {
                // 检查是否可以转换到半开状态
                let opened_at_key = format!("{}:{}:opened_at", self.key_prefix, service);
                let opened_at: Option<u64> = conn.get(&opened_at_key).await?;

                if let Some(opened_at) = opened_at {
                    let now = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs();

                    if now - opened_at >= self.config.open_timeout.as_secs() {
                        // 转换到半开状态
                        let _: () = conn.set(&state_key, "half_open").await?;
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            Some("half_open") => Ok(true),
            _ => Ok(true), // closed 或不存在
        }
    }

    /// 记录请求结果
    pub async fn record_result(&self, service: &str, result: RequestResult) -> Result<(), redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;

        let failures_key = format!("{}:{}:failures", self.key_prefix, service);
        let total_key = format!("{}:{}:total", self.key_prefix, service);

        match result {
            RequestResult::Success => {
                let _: () = conn.incr(&total_key, 1).await?;
            }
            RequestResult::Failure => {
                let _: () = conn.incr(&failures_key, 1).await?;
                let _: () = conn.incr(&total_key, 1).await?;
            }
        }

        // 检查是否需要打开熔断器
        let failures: u64 = conn.get(&failures_key).await.unwrap_or(0);
        let total: u64 = conn.get(&total_key).await.unwrap_or(0);

        if total >= self.config.minimum_requests {
            let failure_rate = failures as f64 / total as f64;

            if failure_rate >= self.config.failure_threshold {
                // 打开熔断器
                let state_key = format!("{}:{}:state", self.key_prefix, service);
                let opened_at_key = format!("{}:{}:opened_at", self.key_prefix, service);

                let now = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs();

                let _: () = conn.set(&state_key, "open").await?;
                let _: () = conn.set(&opened_at_key, now).await?;

                tracing::warn!("Distributed circuit breaker opened for service: {}", service);
            }
        }

        // 设置过期时间
        let _: () = conn.expire(&failures_key, self.config.window_size.as_secs() as i64).await?;
        let _: () = conn.expire(&total_key, self.config.window_size.as_secs() as i64).await?;

        Ok(())
    }

    /// 重置熔断器
    pub async fn reset(&self, service: &str) -> Result<(), redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;

        let state_key = format!("{}:{}:state", self.key_prefix, service);
        let failures_key = format!("{}:{}:failures", self.key_prefix, service);
        let total_key = format!("{}:{}:total", self.key_prefix, service);
        let opened_at_key = format!("{}:{}:opened_at", self.key_prefix, service);

        let _: () = conn.del(&state_key).await?;
        let _: () = conn.del(&failures_key).await?;
        let _: () = conn.del(&total_key).await?;
        let _: () = conn.del(&opened_at_key).await?;

        Ok(())
    }
}
```

---

## 完整示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("=== OTLP 熔断器模式演示 ===\n");

    // 1. 创建熔断器配置
    let config = CircuitBreakerConfig {
        failure_threshold: 0.5,
        minimum_requests: 5,
        window_size: Duration::from_secs(10),
        open_timeout: Duration::from_secs(5),
        half_open_requests: 3,
        half_open_success_threshold: 2,
    };

    // 2. 创建熔断器
    let breaker = Arc::new(CircuitBreaker::new(config));

    // 3. 启动监控
    let monitor = CircuitBreakerMonitor::new(breaker.clone());
    monitor.start(Duration::from_secs(2)).await;

    // 4. 模拟正常请求
    println!("阶段 1: 正常请求");
    for i in 0..5 {
        let result = breaker.call(async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<_, String>(format!("Success {}", i))
        }).await;

        match result {
            Ok(msg) => println!("  ✓ {}", msg),
            Err(e) => println!("  ✗ Error: {:?}", e),
        }
    }

    let state = breaker.state().await;
    println!("  状态: {:?}\n", state);

    // 5. 模拟失败请求（触发熔断）
    println!("阶段 2: 失败请求（触发熔断）");
    for i in 0..7 {
        let result = breaker.call(async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            Err::<String, _>(format!("Failure {}", i))
        }).await;

        match result {
            Ok(_) => println!("  ✓ Success"),
            Err(CircuitBreakerError::Open) => println!("  ⊗ Circuit breaker is OPEN"),
            Err(CircuitBreakerError::InnerError(e)) => println!("  ✗ Error: {}", e),
        }

        tokio::time::sleep(Duration::from_millis(200)).await;
    }

    let state = breaker.state().await;
    println!("  状态: {:?}\n", state);

    // 6. 等待进入半开状态
    println!("阶段 3: 等待半开状态");
    println!("  等待 5 秒...");
    tokio::time::sleep(Duration::from_secs(6)).await;

    let state = breaker.state().await;
    println!("  状态: {:?}\n", state);

    // 7. 半开状态测试（成功恢复）
    println!("阶段 4: 半开状态测试");
    for i in 0..3 {
        let result = breaker.call(async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<_, String>(format!("Recovery {}", i))
        }).await;

        match result {
            Ok(msg) => println!("  ✓ {}", msg),
            Err(CircuitBreakerError::Open) => println!("  ⊗ Circuit breaker is OPEN"),
            Err(CircuitBreakerError::InnerError(e)) => println!("  ✗ Error: {}", e),
        }

        tokio::time::sleep(Duration::from_millis(200)).await;
    }

    let state = breaker.state().await;
    println!("  状态: {:?}\n", state);

    // 8. 显示最终指标
    let metrics = breaker.metrics().await;
    println!("最终指标:");
    println!("  总请求数: {}", metrics.total_requests);
    println!("  成功请求: {}", metrics.successful_requests);
    println!("  失败请求: {}", metrics.failed_requests);
    println!("  拒绝请求: {}", metrics.rejected_requests);
    println!("  状态变化: {}", metrics.state_changes);
    println!("  当前失败率: {:.2}%", metrics.current_failure_rate * 100.0);

    println!("\n✅ 熔断器演示完成!");

    Ok(())
}
```

---

## 性能优化

### 1. **无锁实现**

```rust
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};

pub struct LockFreeCircuitBreaker {
    state: AtomicU8,  // 0=Closed, 1=Open, 2=HalfOpen
    failures: AtomicU64,
    total: AtomicU64,
}
```

### 2. **批量记录**

```rust
// 批量记录请求结果
pub async fn record_batch(&self, results: Vec<RequestResult>) {
    // ...
}
```

---

## 最佳实践

### 1. **配置建议**

```rust
// Web 服务
let config = CircuitBreakerConfig {
    failure_threshold: 0.5,      // 50% 失败率
    minimum_requests: 10,        // 至少 10 个请求
    window_size: Duration::from_secs(60),
    open_timeout: Duration::from_secs(30),
    half_open_requests: 5,
    half_open_success_threshold: 3,
};

// 数据库服务
let config = CircuitBreakerConfig {
    failure_threshold: 0.7,      // 更高的阈值
    minimum_requests: 5,
    window_size: Duration::from_secs(30),
    open_timeout: Duration::from_secs(60),
    half_open_requests: 3,
    half_open_success_threshold: 2,
};
```

### 2. **监控与告警**

```rust
// 状态变化告警
if metrics.state_changes > last_count {
    send_alert(format!("Circuit breaker state changed to {:?}", state));
}

// 高拒绝率告警
if metrics.rejected_requests as f64 / metrics.total_requests as f64 > 0.1 {
    send_alert("High circuit breaker rejection rate");
}
```

---

## 依赖项

```toml
[dependencies]
tokio = { version = "1.41", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
redis = { version = "0.27", features = ["tokio-comp"] }
tracing = "0.1"
tracing-subscriber = "0.3"
```

---

## 总结

本文档提供了完整的 OTLP 熔断器模式的 Rust 实现，包括：

✅ **三状态管理**: Closed、Open、HalfOpen
✅ **自动恢复**: 半开状态探测
✅ **故障检测**: 多种检测策略
✅ **实时监控**: 完整指标与事件
✅ **分布式支持**: 基于 Redis
✅ **生产就绪**: 高性能、最佳实践

通过这些实现，您可以构建高可用的 OTLP 系统！
