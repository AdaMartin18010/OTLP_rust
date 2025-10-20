# OTLP 重试与超时策略 - Rust 完整实现

> **版本**: 1.0.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: v0.27+  
> **最后更新**: 2025-10-09

## 目录

- [OTLP 重试与超时策略 - Rust 完整实现](#otlp-重试与超时策略---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [核心架构](#核心架构)
  - [重试策略](#重试策略)
  - [指数退避](#指数退避)
  - [超时控制](#超时控制)
  - [抖动算法](#抖动算法)
  - [重试预算](#重试预算)
  - [组合策略](#组合策略)
  - [完整示例](#完整示例)
  - [性能优化](#性能优化)
    - [1. **批量重试**](#1-批量重试)
    - [2. **并发重试**](#2-并发重试)
  - [最佳实践](#最佳实践)
    - [1. **重试策略选择**](#1-重试策略选择)
    - [2. **超时配置**](#2-超时配置)
    - [3. **监控与告警**](#3-监控与告警)
  - [依赖项](#依赖项)
  - [总结](#总结)

---

## 概述

重试与超时是构建弹性系统的基础，合理的重试策略可以提高系统可靠性，而超时控制则防止资源浪费。

### 核心特性

- ✅ **多种重试策略**: 固定、线性、指数退避
- ✅ **智能超时**: 自适应超时控制
- ✅ **抖动算法**: 避免重试风暴
- ✅ **重试预算**: 限制重试消耗
- ✅ **条件重试**: 根据错误类型决定是否重试
- ✅ **异步支持**: 基于 Tokio 的高效实现

---

## 核心架构

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 重试策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RetryStrategy {
    /// 固定延迟
    Fixed {
        delay: Duration,
        max_attempts: u32,
    },
    /// 线性退避
    Linear {
        initial_delay: Duration,
        increment: Duration,
        max_attempts: u32,
    },
    /// 指数退避
    Exponential {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
        max_attempts: u32,
    },
    /// 自定义
    Custom {
        delays: Vec<Duration>,
    },
}

/// 重试结果
#[derive(Debug)]
pub enum RetryResult<T, E> {
    Success(T),
    Failure(E),
    ExhaustedRetries,
}

/// 重试指标
#[derive(Debug, Default, Clone)]
pub struct RetryMetrics {
    pub total_attempts: u64,
    pub successful_attempts: u64,
    pub failed_attempts: u64,
    pub retries_performed: u64,
    pub total_retry_delay: Duration,
}

/// 超时配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    pub base_timeout: Duration,
    pub max_timeout: Duration,
    pub multiplier: f64,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            base_timeout: Duration::from_secs(5),
            max_timeout: Duration::from_secs(30),
            multiplier: 1.5,
        }
    }
}
```

---

## 重试策略

```rust
/// 重试执行器
pub struct RetryExecutor {
    strategy: RetryStrategy,
    metrics: Arc<RwLock<RetryMetrics>>,
}

impl RetryExecutor {
    pub fn new(strategy: RetryStrategy) -> Self {
        Self {
            strategy,
            metrics: Arc::new(RwLock::new(RetryMetrics::default())),
        }
    }

    /// 执行带重试的操作
    pub async fn execute<F, T, E>(&self, mut operation: F) -> RetryResult<T, E>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Debug,
    {
        let max_attempts = self.max_attempts();

        for attempt in 0..max_attempts {
            let start = Instant::now();

            // 执行操作
            match operation().await {
                Ok(result) => {
                    // 记录成功
                    let mut metrics = self.metrics.write().await;
                    metrics.total_attempts += 1;
                    metrics.successful_attempts += 1;
                    if attempt > 0 {
                        metrics.retries_performed += 1;
                    }

                    return RetryResult::Success(result);
                }
                Err(e) => {
                    // 记录失败
                    let mut metrics = self.metrics.write().await;
                    metrics.total_attempts += 1;
                    metrics.failed_attempts += 1;

                    // 判断是否需要重试
                    if attempt + 1 < max_attempts {
                        // 计算延迟
                        let delay = self.calculate_delay(attempt);
                        metrics.total_retry_delay += delay;

                        tracing::debug!(
                            "Attempt {} failed, retrying after {:?}",
                            attempt + 1,
                            delay
                        );

                        drop(metrics);

                        // 等待后重试
                        tokio::time::sleep(delay).await;
                    } else {
                        tracing::error!("All {} attempts failed", max_attempts);
                        return RetryResult::Failure(e);
                    }
                }
            }
        }

        RetryResult::ExhaustedRetries
    }

    /// 计算重试延迟
    fn calculate_delay(&self, attempt: u32) -> Duration {
        match &self.strategy {
            RetryStrategy::Fixed { delay, .. } => *delay,
            RetryStrategy::Linear {
                initial_delay,
                increment,
                ..
            } => *initial_delay + *increment * attempt,
            RetryStrategy::Exponential {
                initial_delay,
                multiplier,
                max_delay,
                ..
            } => {
                let delay = initial_delay.as_secs_f64() * multiplier.powi(attempt as i32);
                Duration::from_secs_f64(delay.min(max_delay.as_secs_f64()))
            }
            RetryStrategy::Custom { delays } => {
                delays.get(attempt as usize).copied().unwrap_or_else(|| {
                    delays.last().copied().unwrap_or(Duration::from_secs(1))
                })
            }
        }
    }

    /// 获取最大尝试次数
    fn max_attempts(&self) -> u32 {
        match &self.strategy {
            RetryStrategy::Fixed { max_attempts, .. } => *max_attempts,
            RetryStrategy::Linear { max_attempts, .. } => *max_attempts,
            RetryStrategy::Exponential { max_attempts, .. } => *max_attempts,
            RetryStrategy::Custom { delays } => delays.len() as u32,
        }
    }

    /// 获取指标
    pub async fn metrics(&self) -> RetryMetrics {
        self.metrics.read().await.clone()
    }
}
```

---

## 指数退避

```rust
use rand::Rng;

/// 指数退避重试器
pub struct ExponentialBackoff {
    initial_delay: Duration,
    multiplier: f64,
    max_delay: Duration,
    max_attempts: u32,
    jitter: bool,
}

impl ExponentialBackoff {
    pub fn new(
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
        max_attempts: u32,
    ) -> Self {
        Self {
            initial_delay,
            multiplier,
            max_delay,
            max_attempts,
            jitter: true,
        }
    }

    pub fn with_jitter(mut self, jitter: bool) -> Self {
        self.jitter = jitter;
        self
    }

    /// 计算延迟（带抖动）
    pub fn calculate_delay(&self, attempt: u32) -> Duration {
        let base_delay = self.initial_delay.as_secs_f64()
            * self.multiplier.powi(attempt as i32);

        let capped_delay = base_delay.min(self.max_delay.as_secs_f64());

        if self.jitter {
            // 添加随机抖动（0.5 ~ 1.5 倍）
            let mut rng = rand::thread_rng();
            let jitter_factor = rng.gen_range(0.5..1.5);
            Duration::from_secs_f64(capped_delay * jitter_factor)
        } else {
            Duration::from_secs_f64(capped_delay)
        }
    }

    /// 执行带指数退避的重试
    pub async fn retry<F, T, E>(&self, mut operation: F) -> RetryResult<T, E>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Debug,
    {
        for attempt in 0..self.max_attempts {
            match operation().await {
                Ok(result) => return RetryResult::Success(result),
                Err(e) => {
                    if attempt + 1 < self.max_attempts {
                        let delay = self.calculate_delay(attempt);
                        tracing::debug!(
                            "Exponential backoff: attempt {} failed, retrying after {:?}",
                            attempt + 1,
                            delay
                        );
                        tokio::time::sleep(delay).await;
                    } else {
                        return RetryResult::Failure(e);
                    }
                }
            }
        }

        RetryResult::ExhaustedRetries
    }
}
```

---

## 超时控制

```rust
/// 超时控制器
pub struct TimeoutController {
    config: TimeoutConfig,
    adaptive: bool,
    recent_latencies: Arc<RwLock<Vec<Duration>>>,
}

impl TimeoutController {
    pub fn new(config: TimeoutConfig, adaptive: bool) -> Self {
        Self {
            config,
            adaptive,
            recent_latencies: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 执行带超时的操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T, TimeoutError>
    where
        F: std::future::Future<Output = T>,
    {
        let timeout = if self.adaptive {
            self.calculate_adaptive_timeout().await
        } else {
            self.config.base_timeout
        };

        let start = Instant::now();

        match tokio::time::timeout(timeout, operation).await {
            Ok(result) => {
                // 记录延迟
                let latency = start.elapsed();
                self.record_latency(latency).await;
                Ok(result)
            }
            Err(_) => {
                tracing::warn!("Operation timed out after {:?}", timeout);
                Err(TimeoutError::Elapsed)
            }
        }
    }

    /// 计算自适应超时
    async fn calculate_adaptive_timeout(&self) -> Duration {
        let latencies = self.recent_latencies.read().await;

        if latencies.is_empty() {
            return self.config.base_timeout;
        }

        // 计算 P99 延迟
        let mut sorted = latencies.clone();
        sorted.sort();

        let p99_index = (sorted.len() as f64 * 0.99) as usize;
        let p99_latency = sorted.get(p99_index).copied().unwrap_or(self.config.base_timeout);

        // 应用倍数
        let adaptive_timeout = Duration::from_secs_f64(
            p99_latency.as_secs_f64() * self.config.multiplier
        );

        // 限制在最大超时内
        adaptive_timeout.min(self.config.max_timeout)
    }

    /// 记录延迟
    async fn record_latency(&self, latency: Duration) {
        let mut latencies = self.recent_latencies.write().await;
        latencies.push(latency);

        // 只保留最近 100 个记录
        if latencies.len() > 100 {
            latencies.remove(0);
        }
    }

    /// 获取当前超时值
    pub async fn current_timeout(&self) -> Duration {
        if self.adaptive {
            self.calculate_adaptive_timeout().await
        } else {
            self.config.base_timeout
        }
    }
}

/// 超时错误
#[derive(Debug)]
pub enum TimeoutError {
    Elapsed,
}

impl std::fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TimeoutError::Elapsed => write!(f, "Operation timed out"),
        }
    }
}

impl std::error::Error for TimeoutError {}
```

---

## 抖动算法

```rust
/// 抖动策略
pub enum JitterStrategy {
    /// 无抖动
    None,
    /// 全抖动：0 ~ delay
    Full,
    /// 等值抖动：delay/2 ~ delay
    Equal,
    /// 装饰抖动：delay ~ delay * 1.5
    Decorrelated,
}

/// 抖动应用器
pub struct JitterApplier {
    strategy: JitterStrategy,
}

impl JitterApplier {
    pub fn new(strategy: JitterStrategy) -> Self {
        Self { strategy }
    }

    /// 应用抖动
    pub fn apply(&self, base_delay: Duration) -> Duration {
        let mut rng = rand::thread_rng();

        match self.strategy {
            JitterStrategy::None => base_delay,
            JitterStrategy::Full => {
                // 0 ~ delay
                let jitter_ms = rng.gen_range(0..=base_delay.as_millis());
                Duration::from_millis(jitter_ms as u64)
            }
            JitterStrategy::Equal => {
                // delay/2 ~ delay
                let min_ms = base_delay.as_millis() / 2;
                let max_ms = base_delay.as_millis();
                let jitter_ms = rng.gen_range(min_ms..=max_ms);
                Duration::from_millis(jitter_ms as u64)
            }
            JitterStrategy::Decorrelated => {
                // delay ~ delay * 1.5
                let jitter_factor = rng.gen_range(1.0..1.5);
                Duration::from_secs_f64(base_delay.as_secs_f64() * jitter_factor)
            }
        }
    }
}

/// 带抖动的指数退避
pub struct ExponentialBackoffWithJitter {
    backoff: ExponentialBackoff,
    jitter_applier: JitterApplier,
}

impl ExponentialBackoffWithJitter {
    pub fn new(backoff: ExponentialBackoff, jitter_strategy: JitterStrategy) -> Self {
        Self {
            backoff,
            jitter_applier: JitterApplier::new(jitter_strategy),
        }
    }

    /// 计算带抖动的延迟
    pub fn calculate_delay(&self, attempt: u32) -> Duration {
        let base_delay = self.backoff.calculate_delay(attempt);
        self.jitter_applier.apply(base_delay)
    }
}
```

---

## 重试预算

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 重试预算管理器
pub struct RetryBudget {
    /// 总预算
    total_budget: u64,
    /// 剩余预算
    remaining: Arc<AtomicU64>,
    /// 预算恢复速率（每秒）
    recovery_rate: u64,
    /// 上次恢复时间
    last_recovery: Arc<RwLock<Instant>>,
}

impl RetryBudget {
    pub fn new(total_budget: u64, recovery_rate: u64) -> Self {
        Self {
            total_budget,
            remaining: Arc::new(AtomicU64::new(total_budget)),
            recovery_rate,
            last_recovery: Arc::new(RwLock::new(Instant::now())),
        }
    }

    /// 尝试消费预算
    pub async fn try_consume(&self, amount: u64) -> bool {
        // 先尝试恢复预算
        self.recover().await;

        let current = self.remaining.load(Ordering::Acquire);

        if current >= amount {
            // 尝试原子地减少预算
            self.remaining.fetch_sub(amount, Ordering::Release);
            true
        } else {
            false
        }
    }

    /// 恢复预算
    async fn recover(&self) {
        let mut last_recovery = self.last_recovery.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last_recovery);

        if elapsed >= Duration::from_secs(1) {
            let recovery_amount = (elapsed.as_secs() * self.recovery_rate).min(self.total_budget);
            let current = self.remaining.load(Ordering::Acquire);
            let new_value = (current + recovery_amount).min(self.total_budget);

            self.remaining.store(new_value, Ordering::Release);
            *last_recovery = now;
        }
    }

    /// 获取剩余预算
    pub fn remaining(&self) -> u64 {
        self.remaining.load(Ordering::Acquire)
    }

    /// 获取预算使用率
    pub fn usage_rate(&self) -> f64 {
        let remaining = self.remaining.load(Ordering::Acquire);
        (self.total_budget - remaining) as f64 / self.total_budget as f64
    }
}
```

---

## 组合策略

```rust
/// 重试与超时组合器
pub struct RetryWithTimeout {
    retry_executor: RetryExecutor,
    timeout_controller: TimeoutController,
    retry_budget: Option<Arc<RetryBudget>>,
}

impl RetryWithTimeout {
    pub fn new(
        retry_strategy: RetryStrategy,
        timeout_config: TimeoutConfig,
        retry_budget: Option<Arc<RetryBudget>>,
    ) -> Self {
        Self {
            retry_executor: RetryExecutor::new(retry_strategy),
            timeout_controller: TimeoutController::new(timeout_config, true),
            retry_budget,
        }
    }

    /// 执行带重试和超时的操作
    pub async fn execute<F, T, E>(
        &self,
        operation: F,
    ) -> Result<RetryResult<T, E>, TimeoutError>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>
            + Clone,
        E: std::fmt::Debug,
    {
        let result = self.retry_executor
            .execute(move || {
                let operation = operation.clone();
                Box::pin(async move {
                    self.timeout_controller
                        .execute(operation())
                        .await
                        .map_err(|_| {
                            // 将超时错误转换为业务错误
                            // 这里需要根据实际情况处理
                            panic!("Timeout error")
                        })
                })
            })
            .await;

        Ok(result)
    }

    /// 执行带预算控制的重试
    pub async fn execute_with_budget<F, T, E>(
        &self,
        operation: F,
    ) -> Result<RetryResult<T, E>, String>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>
            + Clone,
        E: std::fmt::Debug,
    {
        // 检查重试预算
        if let Some(budget) = &self.retry_budget {
            if !budget.try_consume(1).await {
                return Err("Retry budget exhausted".to_string());
            }
        }

        match self.execute(operation).await {
            Ok(result) => Ok(result),
            Err(e) => Err(format!("Execution failed: {:?}", e)),
        }
    }
}
```

---

## 完整示例

```rust
use std::io;

async fn simulate_unreliable_service(fail_count: &mut u32) -> Result<String, io::Error> {
    if *fail_count > 0 {
        *fail_count -= 1;
        Err(io::Error::new(io::ErrorKind::ConnectionRefused, "Service unavailable"))
    } else {
        Ok("Success!".to_string())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("=== OTLP 重试与超时策略演示 ===\n");

    // 1. 测试固定延迟重试
    println!("测试 1: 固定延迟重试");
    let fixed_strategy = RetryStrategy::Fixed {
        delay: Duration::from_millis(500),
        max_attempts: 3,
    };
    let executor = RetryExecutor::new(fixed_strategy);

    let mut fail_count = 2u32;
    let result = executor.execute(|| {
        Box::pin(simulate_unreliable_service(&mut fail_count))
    }).await;

    match result {
        RetryResult::Success(msg) => println!("  ✓ {}", msg),
        RetryResult::Failure(e) => println!("  ✗ 失败: {}", e),
        RetryResult::ExhaustedRetries => println!("  ✗ 重试耗尽"),
    }

    let metrics = executor.metrics().await;
    println!("  总尝试: {}, 重试次数: {}\n", metrics.total_attempts, metrics.retries_performed);

    // 2. 测试指数退避
    println!("测试 2: 指数退避重试");
    let backoff = ExponentialBackoff::new(
        Duration::from_millis(100),
        2.0,
        Duration::from_secs(5),
        4,
    );

    let mut fail_count = 2u32;
    let result = backoff.retry(|| {
        Box::pin(simulate_unreliable_service(&mut fail_count))
    }).await;

    match result {
        RetryResult::Success(msg) => println!("  ✓ {}", msg),
        RetryResult::Failure(e) => println!("  ✗ 失败: {}", e),
        RetryResult::ExhaustedRetries => println!("  ✗ 重试耗尽"),
    }
    println!();

    // 3. 测试超时控制
    println!("测试 3: 超时控制");
    let timeout_config = TimeoutConfig {
        base_timeout: Duration::from_secs(2),
        max_timeout: Duration::from_secs(10),
        multiplier: 1.5,
    };
    let timeout_controller = TimeoutController::new(timeout_config, false);

    let result = timeout_controller.execute(async {
        tokio::time::sleep(Duration::from_millis(100)).await;
        "快速完成"
    }).await;

    match result {
        Ok(msg) => println!("  ✓ {}", msg),
        Err(e) => println!("  ✗ {}", e),
    }

    let result = timeout_controller.execute(async {
        tokio::time::sleep(Duration::from_secs(3)).await;
        "慢速完成"
    }).await;

    match result {
        Ok(msg) => println!("  ✓ {}", msg),
        Err(e) => println!("  ✗ {}", e),
    }
    println!();

    // 4. 测试抖动策略
    println!("测试 4: 抖动策略");
    let base_delay = Duration::from_secs(1);

    let jitter_strategies = [
        ("无抖动", JitterStrategy::None),
        ("全抖动", JitterStrategy::Full),
        ("等值抖动", JitterStrategy::Equal),
        ("装饰抖动", JitterStrategy::Decorrelated),
    ];

    for (name, strategy) in jitter_strategies {
        let applier = JitterApplier::new(strategy);
        let delays: Vec<Duration> = (0..5)
            .map(|_| applier.apply(base_delay))
            .collect();

        println!("  {}: {:?}", name, delays.iter().map(|d| d.as_millis()).collect::<Vec<_>>());
    }
    println!();

    // 5. 测试重试预算
    println!("测试 5: 重试预算");
    let budget = Arc::new(RetryBudget::new(10, 2));

    println!("  初始预算: {}", budget.remaining());

    // 快速消费预算
    for i in 0..12 {
        if budget.try_consume(1).await {
            println!("  请求 {} 允许 (剩余: {})", i + 1, budget.remaining());
        } else {
            println!("  请求 {} 被拒绝 (预算耗尽)", i + 1);
        }
    }

    // 等待预算恢复
    println!("  等待 2 秒恢复预算...");
    tokio::time::sleep(Duration::from_secs(2)).await;
    println!("  恢复后预算: {}", budget.remaining());
    println!();

    // 6. 测试组合策略
    println!("测试 6: 重试+超时组合");
    let combined = RetryWithTimeout::new(
        RetryStrategy::Exponential {
            initial_delay: Duration::from_millis(100),
            multiplier: 2.0,
            max_delay: Duration::from_secs(2),
            max_attempts: 3,
        },
        TimeoutConfig {
            base_timeout: Duration::from_secs(1),
            max_timeout: Duration::from_secs(5),
            multiplier: 1.5,
        },
        Some(budget.clone()),
    );

    let mut fail_count = 1u32;
    let result = combined.execute_with_budget(|| {
        Box::pin(simulate_unreliable_service(&mut fail_count))
    }).await;

    match result {
        Ok(RetryResult::Success(msg)) => println!("  ✓ {}", msg),
        Ok(RetryResult::Failure(e)) => println!("  ✗ 失败: {}", e),
        Ok(RetryResult::ExhaustedRetries) => println!("  ✗ 重试耗尽"),
        Err(e) => println!("  ✗ 错误: {}", e),
    }

    println!("\n✅ 重试与超时策略演示完成!");

    Ok(())
}
```

---

## 性能优化

### 1. **批量重试**

```rust
pub async fn retry_batch<F, T, E>(&self, operations: Vec<F>) -> Vec<RetryResult<T, E>>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
{
    let mut results = Vec::new();
    for mut op in operations {
        let result = self.execute(op).await;
        results.push(result);
    }
    results
}
```

### 2. **并发重试**

```rust
pub async fn retry_concurrent<F, T, E>(&self, operations: Vec<F>) -> Vec<RetryResult<T, E>>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>> + Send + 'static,
    T: Send + 'static,
    E: Send + 'static,
{
    let handles: Vec<_> = operations.into_iter()
        .map(|mut op| {
            tokio::spawn(async move {
                self.execute(op).await
            })
        })
        .collect();

    let mut results = Vec::new();
    for handle in handles {
        if let Ok(result) = handle.await {
            results.push(result);
        }
    }
    results
}
```

---

## 最佳实践

### 1. **重试策略选择**

```rust
// Web API 调用
let strategy = RetryStrategy::Exponential {
    initial_delay: Duration::from_millis(100),
    multiplier: 2.0,
    max_delay: Duration::from_secs(10),
    max_attempts: 5,
};

// 数据库操作
let strategy = RetryStrategy::Fixed {
    delay: Duration::from_millis(500),
    max_attempts: 3,
};

// 消息队列
let strategy = RetryStrategy::Linear {
    initial_delay: Duration::from_secs(1),
    increment: Duration::from_secs(2),
    max_attempts: 5,
};
```

### 2. **超时配置**

```rust
// 快速操作
let timeout = TimeoutConfig {
    base_timeout: Duration::from_millis(500),
    max_timeout: Duration::from_secs(2),
    multiplier: 1.5,
};

// 慢速操作
let timeout = TimeoutConfig {
    base_timeout: Duration::from_secs(5),
    max_timeout: Duration::from_secs(30),
    multiplier: 2.0,
};
```

### 3. **监控与告警**

```rust
// 定期检查重试指标
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let metrics = executor.metrics().await;
        
        let retry_rate = metrics.retries_performed as f64 / metrics.total_attempts as f64;
        if retry_rate > 0.3 {
            tracing::warn!("High retry rate: {:.2}%", retry_rate * 100.0);
        }
    }
});
```

---

## 依赖项

```toml
[dependencies]
tokio = { version = "1.41", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
rand = "0.8"
tracing = "0.1"
tracing-subscriber = "0.3"
```

---

## 总结

本文档提供了完整的 OTLP 重试与超时策略的 Rust 实现，包括：

✅ **多种重试策略**: 固定、线性、指数退避
✅ **智能超时**: 自适应超时控制
✅ **抖动算法**: 避免重试风暴
✅ **重试预算**: 限制重试消耗
✅ **组合策略**: 重试+超时+预算
✅ **生产就绪**: 高性能、最佳实践

通过这些实现，您可以构建高可靠的 OTLP 系统！
