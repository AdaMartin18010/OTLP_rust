# OTLP 流量控制与整形 - Rust 完整实现

> **版本**: 1.0.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: v0.27+  
> **最后更新**: 2025-10-09

## 目录

- [OTLP 流量控制与整形 - Rust 完整实现](#otlp-流量控制与整形---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [核心架构](#核心架构)
  - [令牌桶算法](#令牌桶算法)
  - [漏桶算法](#漏桶算法)
  - [滑动窗口限流](#滑动窗口限流)
  - [分布式限流](#分布式限流)
  - [流量整形器](#流量整形器)
  - [背压处理](#背压处理)
  - [自适应流控](#自适应流控)
  - [完整示例](#完整示例)
  - [性能优化](#性能优化)
    - [1. **无锁实现**](#1-无锁实现)
    - [2. **批量处理**](#2-批量处理)
    - [3. **分层限流**](#3-分层限流)
  - [最佳实践](#最佳实践)
    - [1. **选择合适的算法**](#1-选择合适的算法)
    - [2. **参数配置建议**](#2-参数配置建议)
    - [3. **监控与告警**](#3-监控与告警)
    - [4. **分布式场景**](#4-分布式场景)
  - [依赖项](#依赖项)
  - [总结](#总结)

---

## 概述

流量控制与整形是保护 OTLP 系统稳定性的关键机制，防止流量突发导致系统过载，确保服务质量和资源的合理分配。

### 核心特性

- ✅ **多种限流算法**: 令牌桶、漏桶、滑动窗口
- ✅ **分布式限流**: 基于 Redis 的全局流控
- ✅ **自适应调节**: 根据系统负载动态调整限流阈值
- ✅ **背压处理**: 优雅处理下游压力传导
- ✅ **流量整形**: 平滑流量峰值，保证稳定输出
- ✅ **异步高性能**: 基于 Tokio 的无锁实现

---

## 核心架构

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use serde::{Serialize, Deserialize};

/// 流控策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RateLimitStrategy {
    TokenBucket {
        capacity: u64,
        refill_rate: u64,
    },
    LeakyBucket {
        capacity: u64,
        leak_rate: u64,
    },
    SlidingWindow {
        window_size: Duration,
        max_requests: u64,
    },
    Adaptive {
        min_rate: u64,
        max_rate: u64,
        target_latency: Duration,
    },
}

/// 流控决策
#[derive(Debug, Clone, PartialEq)]
pub enum RateLimitDecision {
    Allowed,
    Denied,
    Throttled(Duration),
}

/// 流控指标
#[derive(Debug, Default, Clone)]
pub struct RateLimitMetrics {
    pub total_requests: u64,
    pub allowed_requests: u64,
    pub denied_requests: u64,
    pub throttled_requests: u64,
    pub current_rate: f64,
}
```

---

## 令牌桶算法

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 令牌桶限流器
pub struct TokenBucketLimiter {
    capacity: u64,
    tokens: Arc<AtomicU64>,
    refill_rate: u64,
    last_refill: Arc<RwLock<Instant>>,
    metrics: Arc<RwLock<RateLimitMetrics>>,
}

impl TokenBucketLimiter {
    pub fn new(capacity: u64, refill_rate: u64) -> Self {
        Self {
            capacity,
            tokens: Arc::new(AtomicU64::new(capacity)),
            refill_rate,
            last_refill: Arc::new(RwLock::new(Instant::now())),
            metrics: Arc::new(RwLock::new(RateLimitMetrics::default())),
        }
    }

    /// 尝试获取令牌
    pub async fn try_acquire(&self, tokens: u64) -> RateLimitDecision {
        // 先补充令牌
        self.refill_tokens().await;

        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;

        // 尝试消耗令牌
        let current = self.tokens.load(Ordering::Relaxed);
        if current >= tokens {
            self.tokens.fetch_sub(tokens, Ordering::Relaxed);
            metrics.allowed_requests += 1;
            RateLimitDecision::Allowed
        } else {
            metrics.denied_requests += 1;
            // 计算需要等待的时间
            let wait_time = Duration::from_secs_f64(
                (tokens - current) as f64 / self.refill_rate as f64
            );
            RateLimitDecision::Throttled(wait_time)
        }
    }

    /// 异步等待并获取令牌
    pub async fn acquire(&self, tokens: u64) -> Result<(), String> {
        loop {
            match self.try_acquire(tokens).await {
                RateLimitDecision::Allowed => return Ok(()),
                RateLimitDecision::Throttled(wait_time) => {
                    tokio::time::sleep(wait_time).await;
                }
                RateLimitDecision::Denied => {
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
            }
        }
    }

    /// 补充令牌
    async fn refill_tokens(&self) {
        let mut last_refill = self.last_refill.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill);

        if elapsed >= Duration::from_secs(1) {
            let new_tokens = (elapsed.as_secs_f64() * self.refill_rate as f64) as u64;
            let current = self.tokens.load(Ordering::Relaxed);
            let new_total = (current + new_tokens).min(self.capacity);
            self.tokens.store(new_total, Ordering::Relaxed);
            *last_refill = now;
        }
    }

    /// 批量获取令牌
    pub async fn acquire_batch(&self, count: u64, tokens_per_item: u64) -> Result<(), String> {
        self.acquire(count * tokens_per_item).await
    }

    /// 获取当前令牌数
    pub fn available_tokens(&self) -> u64 {
        self.tokens.load(Ordering::Relaxed)
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> RateLimitMetrics {
        self.metrics.read().await.clone()
    }
}
```

---

## 漏桶算法

```rust
use tokio::sync::mpsc;

/// 漏桶限流器
pub struct LeakyBucketLimiter {
    capacity: u64,
    leak_rate: u64,
    queue: Arc<RwLock<Vec<Instant>>>,
    metrics: Arc<RwLock<RateLimitMetrics>>,
}

impl LeakyBucketLimiter {
    pub fn new(capacity: u64, leak_rate: u64) -> Self {
        let limiter = Self {
            capacity,
            leak_rate,
            queue: Arc::new(RwLock::new(Vec::new())),
            metrics: Arc::new(RwLock::new(RateLimitMetrics::default())),
        };

        // 启动漏桶泄露任务
        let limiter_clone = limiter.clone();
        tokio::spawn(async move {
            limiter_clone.leak_loop().await;
        });

        limiter
    }

    /// 尝试添加到漏桶
    pub async fn try_acquire(&self) -> RateLimitDecision {
        let mut queue = self.queue.write().await;
        let mut metrics = self.metrics.write().await;

        metrics.total_requests += 1;

        if queue.len() < self.capacity as usize {
            queue.push(Instant::now());
            metrics.allowed_requests += 1;
            RateLimitDecision::Allowed
        } else {
            metrics.denied_requests += 1;
            RateLimitDecision::Denied
        }
    }

    /// 异步等待添加到漏桶
    pub async fn acquire(&self) -> Result<(), String> {
        loop {
            match self.try_acquire().await {
                RateLimitDecision::Allowed => return Ok(()),
                RateLimitDecision::Denied => {
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
                _ => unreachable!(),
            }
        }
    }

    /// 漏桶泄露循环
    async fn leak_loop(&self) {
        let leak_interval = Duration::from_secs(1) / self.leak_rate as u32;
        let mut interval = tokio::time::interval(leak_interval);

        loop {
            interval.tick().await;
            let mut queue = self.queue.write().await;
            if !queue.is_empty() {
                queue.remove(0);
            }
        }
    }

    /// 获取当前队列长度
    pub async fn queue_length(&self) -> usize {
        self.queue.read().await.len()
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> RateLimitMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for LeakyBucketLimiter {
    fn clone(&self) -> Self {
        Self {
            capacity: self.capacity,
            leak_rate: self.leak_rate,
            queue: self.queue.clone(),
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 滑动窗口限流

```rust
use std::collections::VecDeque;

/// 滑动窗口限流器
pub struct SlidingWindowLimiter {
    window_size: Duration,
    max_requests: u64,
    timestamps: Arc<RwLock<VecDeque<Instant>>>,
    metrics: Arc<RwLock<RateLimitMetrics>>,
}

impl SlidingWindowLimiter {
    pub fn new(window_size: Duration, max_requests: u64) -> Self {
        Self {
            window_size,
            max_requests,
            timestamps: Arc::new(RwLock::new(VecDeque::new())),
            metrics: Arc::new(RwLock::new(RateLimitMetrics::default())),
        }
    }

    /// 尝试记录请求
    pub async fn try_acquire(&self) -> RateLimitDecision {
        let now = Instant::now();
        let mut timestamps = self.timestamps.write().await;
        let mut metrics = self.metrics.write().await;

        // 移除窗口外的时间戳
        let window_start = now - self.window_size;
        while let Some(&front) = timestamps.front() {
            if front < window_start {
                timestamps.pop_front();
            } else {
                break;
            }
        }

        metrics.total_requests += 1;

        // 检查是否超过限制
        if timestamps.len() < self.max_requests as usize {
            timestamps.push_back(now);
            metrics.allowed_requests += 1;
            metrics.current_rate = timestamps.len() as f64 / self.window_size.as_secs_f64();
            RateLimitDecision::Allowed
        } else {
            metrics.denied_requests += 1;
            // 计算需要等待的时间
            if let Some(&oldest) = timestamps.front() {
                let wait_time = (oldest + self.window_size)
                    .duration_since(now);
                RateLimitDecision::Throttled(wait_time)
            } else {
                RateLimitDecision::Denied
            }
        }
    }

    /// 异步等待并记录请求
    pub async fn acquire(&self) -> Result<(), String> {
        loop {
            match self.try_acquire().await {
                RateLimitDecision::Allowed => return Ok(()),
                RateLimitDecision::Throttled(wait_time) => {
                    tokio::time::sleep(wait_time).await;
                }
                RateLimitDecision::Denied => {
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
            }
        }
    }

    /// 获取当前窗口内的请求数
    pub async fn current_requests(&self) -> usize {
        let now = Instant::now();
        let timestamps = self.timestamps.read().await;
        let window_start = now - self.window_size;

        timestamps.iter().filter(|&&t| t >= window_start).count()
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> RateLimitMetrics {
        self.metrics.read().await.clone()
    }
}
```

---

## 分布式限流

```rust
use redis::AsyncCommands;

/// 分布式限流器（基于 Redis）
pub struct DistributedRateLimiter {
    redis_client: redis::Client,
    key_prefix: String,
    window_size: Duration,
    max_requests: u64,
}

impl DistributedRateLimiter {
    pub fn new(
        redis_url: &str,
        key_prefix: String,
        window_size: Duration,
        max_requests: u64,
    ) -> Result<Self, redis::RedisError> {
        let redis_client = redis::Client::open(redis_url)?;

        Ok(Self {
            redis_client,
            key_prefix,
            window_size,
            max_requests,
        })
    }

    /// 尝试获取许可（使用 Redis Lua 脚本保证原子性）
    pub async fn try_acquire(&self, key: &str) -> Result<RateLimitDecision, redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;

        let full_key = format!("{}:{}", self.key_prefix, key);
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let window_start = now - self.window_size.as_secs();

        // Lua 脚本：滑动窗口限流
        let script = r#"
            local key = KEYS[1]
            local now = tonumber(ARGV[1])
            local window_start = tonumber(ARGV[2])
            local max_requests = tonumber(ARGV[3])
            local ttl = tonumber(ARGV[4])

            -- 删除窗口外的记录
            redis.call('ZREMRANGEBYSCORE', key, 0, window_start)

            -- 获取当前窗口内的请求数
            local current = redis.call('ZCARD', key)

            if current < max_requests then
                -- 添加新的时间戳
                redis.call('ZADD', key, now, now)
                redis.call('EXPIRE', key, ttl)
                return 1
            else
                return 0
            end
        "#;

        let result: i32 = redis::Script::new(script)
            .key(&full_key)
            .arg(now)
            .arg(window_start)
            .arg(self.max_requests)
            .arg(self.window_size.as_secs())
            .invoke_async(&mut conn)
            .await?;

        if result == 1 {
            Ok(RateLimitDecision::Allowed)
        } else {
            Ok(RateLimitDecision::Denied)
        }
    }

    /// 获取当前请求数
    pub async fn current_count(&self, key: &str) -> Result<u64, redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;

        let full_key = format!("{}:{}", self.key_prefix, key);
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let window_start = now - self.window_size.as_secs();

        // 删除过期记录
        let _: () = conn.zrembyscore(&full_key, 0, window_start as isize).await?;

        // 获取当前数量
        let count: u64 = conn.zcard(&full_key).await?;

        Ok(count)
    }

    /// 重置限流计数
    pub async fn reset(&self, key: &str) -> Result<(), redis::RedisError> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;
        let full_key = format!("{}:{}", self.key_prefix, key);
        let _: () = conn.del(&full_key).await?;
        Ok(())
    }
}
```

---

## 流量整形器

```rust
use tokio::sync::mpsc;

/// 流量整形器
pub struct TrafficShaper {
    input_rx: mpsc::Receiver<Vec<u8>>,
    output_tx: mpsc::Sender<Vec<u8>>,
    target_rate: u64,
    buffer_size: usize,
}

impl TrafficShaper {
    pub fn new(
        input_rx: mpsc::Receiver<Vec<u8>>,
        output_tx: mpsc::Sender<Vec<u8>>,
        target_rate: u64,
        buffer_size: usize,
    ) -> Self {
        Self {
            input_rx,
            output_tx,
            target_rate,
            buffer_size,
        }
    }

    /// 启动整形
    pub async fn start(mut self) {
        let interval_duration = Duration::from_secs(1) / self.target_rate as u32;
        let mut interval = tokio::time::interval(interval_duration);
        let mut buffer = Vec::new();

        loop {
            tokio::select! {
                // 接收输入
                Some(data) = self.input_rx.recv() => {
                    if buffer.len() < self.buffer_size {
                        buffer.push(data);
                    } else {
                        // 缓冲区满，丢弃或记录
                        tracing::warn!("Traffic shaper buffer full, dropping packet");
                    }
                }

                // 定时发送
                _ = interval.tick() => {
                    if let Some(data) = buffer.pop() {
                        if self.output_tx.send(data).await.is_err() {
                            tracing::error!("Failed to send shaped traffic");
                            break;
                        }
                    }
                }
            }
        }
    }
}

/// 批量流量整形器
pub struct BatchTrafficShaper {
    limiter: Arc<TokenBucketLimiter>,
    batch_size: usize,
    batch_timeout: Duration,
}

impl BatchTrafficShaper {
    pub fn new(
        limiter: Arc<TokenBucketLimiter>,
        batch_size: usize,
        batch_timeout: Duration,
    ) -> Self {
        Self {
            limiter,
            batch_size,
            batch_timeout,
        }
    }

    /// 整形并发送批量数据
    pub async fn shape_batch(&self, items: Vec<Vec<u8>>) -> Result<(), String> {
        let mut batch = Vec::new();
        let start = Instant::now();

        for item in items {
            batch.push(item);

            // 达到批量大小或超时
            if batch.len() >= self.batch_size || start.elapsed() >= self.batch_timeout {
                // 获取令牌
                self.limiter.acquire(batch.len() as u64).await?;

                // 发送批量
                self.send_batch(&batch).await?;
                batch.clear();
            }
        }

        // 发送剩余数据
        if !batch.is_empty() {
            self.limiter.acquire(batch.len() as u64).await?;
            self.send_batch(&batch).await?;
        }

        Ok(())
    }

    async fn send_batch(&self, _batch: &[Vec<u8>]) -> Result<(), String> {
        // 实际发送逻辑
        tokio::time::sleep(Duration::from_millis(10)).await;
        Ok(())
    }
}
```

---

## 背压处理

```rust
/// 背压处理器
pub struct BackpressureHandler {
    buffer: Arc<RwLock<VecDeque<Vec<u8>>>>,
    max_buffer_size: usize,
    semaphore: Arc<Semaphore>,
    metrics: Arc<RwLock<BackpressureMetrics>>,
}

#[derive(Debug, Default, Clone)]
pub struct BackpressureMetrics {
    pub total_items: u64,
    pub buffered_items: u64,
    pub dropped_items: u64,
    pub buffer_full_count: u64,
}

impl BackpressureHandler {
    pub fn new(max_buffer_size: usize, max_concurrent: usize) -> Self {
        Self {
            buffer: Arc::new(RwLock::new(VecDeque::new())),
            max_buffer_size,
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            metrics: Arc::new(RwLock::new(BackpressureMetrics::default())),
        }
    }

    /// 添加数据（带背压）
    pub async fn push(&self, data: Vec<u8>) -> Result<(), String> {
        let mut buffer = self.buffer.write().await;
        let mut metrics = self.metrics.write().await;

        metrics.total_items += 1;

        if buffer.len() < self.max_buffer_size {
            buffer.push_back(data);
            metrics.buffered_items += 1;
            Ok(())
        } else {
            metrics.dropped_items += 1;
            metrics.buffer_full_count += 1;
            Err("Buffer full, backpressure applied".to_string())
        }
    }

    /// 弹出数据（带并发控制）
    pub async fn pop(&self) -> Option<Vec<u8>> {
        // 获取信号量许可
        let _permit = self.semaphore.acquire().await.ok()?;

        let mut buffer = self.buffer.write().await;
        buffer.pop_front()
    }

    /// 批量弹出
    pub async fn pop_batch(&self, count: usize) -> Vec<Vec<u8>> {
        let mut buffer = self.buffer.write().await;
        let mut result = Vec::new();

        for _ in 0..count {
            if let Some(item) = buffer.pop_front() {
                result.push(item);
            } else {
                break;
            }
        }

        result
    }

    /// 获取缓冲区大小
    pub async fn buffer_size(&self) -> usize {
        self.buffer.read().await.len()
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> BackpressureMetrics {
        self.metrics.read().await.clone()
    }
}
```

---

## 自适应流控

```rust
use sysinfo::{System, SystemExt};

/// 自适应流控器
pub struct AdaptiveRateLimiter {
    min_rate: u64,
    max_rate: u64,
    current_rate: Arc<RwLock<u64>>,
    target_latency: Duration,
    adjustment_interval: Duration,
    system: Arc<RwLock<System>>,
}

impl AdaptiveRateLimiter {
    pub fn new(
        min_rate: u64,
        max_rate: u64,
        target_latency: Duration,
        adjustment_interval: Duration,
    ) -> Self {
        let limiter = Self {
            min_rate,
            max_rate,
            current_rate: Arc::new(RwLock::new(max_rate)),
            target_latency,
            adjustment_interval,
            system: Arc::new(RwLock::new(System::new_all())),
        };

        // 启动自适应调节任务
        let limiter_clone = limiter.clone();
        tokio::spawn(async move {
            limiter_clone.adjustment_loop().await;
        });

        limiter
    }

    /// 自适应调节循环
    async fn adjustment_loop(&self) {
        let mut interval = tokio::time::interval(self.adjustment_interval);

        loop {
            interval.tick().await;

            // 获取系统指标
            let (cpu_usage, memory_usage) = self.get_system_metrics().await;

            // 调整速率
            let mut current_rate = self.current_rate.write().await;

            if cpu_usage > 80.0 || memory_usage > 80.0 {
                // 系统负载高，降低速率
                *current_rate = (*current_rate * 9 / 10).max(self.min_rate);
                tracing::info!("Reducing rate to {} due to high load", *current_rate);
            } else if cpu_usage < 50.0 && memory_usage < 50.0 {
                // 系统负载低，提高速率
                *current_rate = (*current_rate * 11 / 10).min(self.max_rate);
                tracing::info!("Increasing rate to {} due to low load", *current_rate);
            }
        }
    }

    /// 获取系统指标
    async fn get_system_metrics(&self) -> (f32, f32) {
        let mut system = self.system.write().await;
        system.refresh_all();

        let cpu_usage = system.global_cpu_info().cpu_usage();
        let memory_usage = (system.used_memory() as f32 / system.total_memory() as f32) * 100.0;

        (cpu_usage, memory_usage)
    }

    /// 获取当前速率
    pub async fn current_rate(&self) -> u64 {
        *self.current_rate.read().await
    }

    /// 尝试获取许可
    pub async fn try_acquire(&self) -> RateLimitDecision {
        let rate = self.current_rate().await;

        // 使用动态速率创建临时令牌桶
        let limiter = TokenBucketLimiter::new(rate, rate);
        limiter.try_acquire(1).await
    }
}

impl Clone for AdaptiveRateLimiter {
    fn clone(&self) -> Self {
        Self {
            min_rate: self.min_rate,
            max_rate: self.max_rate,
            current_rate: self.current_rate.clone(),
            target_latency: self.target_latency,
            adjustment_interval: self.adjustment_interval,
            system: self.system.clone(),
        }
    }
}
```

---

## 完整示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("=== OTLP 流量控制与整形系统 ===\n");

    // 1. 令牌桶限流测试
    println!("测试令牌桶限流器:");
    let token_bucket = TokenBucketLimiter::new(100, 10);

    for i in 0..15 {
        match token_bucket.try_acquire(1).await {
            RateLimitDecision::Allowed => {
                println!("  请求 {} 被允许", i + 1);
            }
            RateLimitDecision::Denied => {
                println!("  请求 {} 被拒绝", i + 1);
            }
            RateLimitDecision::Throttled(wait) => {
                println!("  请求 {} 被限流，需等待 {:?}", i + 1, wait);
            }
        }
    }

    let metrics = token_bucket.get_metrics().await;
    println!("  总请求: {}, 允许: {}, 拒绝: {}", 
        metrics.total_requests, metrics.allowed_requests, metrics.denied_requests);

    // 2. 漏桶限流测试
    println!("\n测试漏桶限流器:");
    let leaky_bucket = LeakyBucketLimiter::new(10, 5);

    for i in 0..12 {
        match leaky_bucket.try_acquire().await {
            RateLimitDecision::Allowed => {
                println!("  请求 {} 进入漏桶", i + 1);
            }
            RateLimitDecision::Denied => {
                println!("  请求 {} 被拒绝（漏桶已满）", i + 1);
            }
            _ => {}
        }
    }

    println!("  当前队列长度: {}", leaky_bucket.queue_length().await);

    // 3. 滑动窗口限流测试
    println!("\n测试滑动窗口限流器:");
    let sliding_window = SlidingWindowLimiter::new(Duration::from_secs(10), 20);

    for i in 0..25 {
        match sliding_window.try_acquire().await {
            RateLimitDecision::Allowed => {
                println!("  请求 {} 通过", i + 1);
            }
            RateLimitDecision::Denied => {
                println!("  请求 {} 被拒绝", i + 1);
            }
            RateLimitDecision::Throttled(wait) => {
                println!("  请求 {} 被限流，需等待 {:?}", i + 1, wait);
            }
        }
    }

    println!("  当前窗口内请求数: {}", sliding_window.current_requests().await);

    // 4. 背压处理测试
    println!("\n测试背压处理器:");
    let backpressure = BackpressureHandler::new(100, 10);

    // 快速推送数据
    for i in 0..120 {
        let data = format!("data-{}", i).into_bytes();
        match backpressure.push(data).await {
            Ok(_) => {
                if i < 5 || i >= 115 {
                    println!("  数据 {} 已缓冲", i);
                }
            }
            Err(e) => {
                if i == 100 {
                    println!("  数据 {} 被丢弃: {}", i, e);
                }
            }
        }
    }

    println!("  缓冲区大小: {}", backpressure.buffer_size().await);
    let bp_metrics = backpressure.get_metrics().await;
    println!("  总项目: {}, 已缓冲: {}, 已丢弃: {}", 
        bp_metrics.total_items, bp_metrics.buffered_items, bp_metrics.dropped_items);

    // 5. 自适应流控测试
    println!("\n测试自适应流控器:");
    let adaptive = AdaptiveRateLimiter::new(
        10,
        1000,
        Duration::from_millis(100),
        Duration::from_secs(1),
    );

    println!("  初始速率: {}/s", adaptive.current_rate().await);

    // 等待一段时间让自适应调节生效
    tokio::time::sleep(Duration::from_secs(3)).await;

    println!("  调节后速率: {}/s", adaptive.current_rate().await);

    // 6. 流量整形测试
    println!("\n测试流量整形器:");
    let (input_tx, input_rx) = mpsc::channel(100);
    let (output_tx, mut output_rx) = mpsc::channel(100);

    let shaper = TrafficShaper::new(input_rx, output_tx, 10, 50);

    // 启动整形器
    tokio::spawn(async move {
        shaper.start().await;
    });

    // 发送数据
    for i in 0..20 {
        let data = format!("packet-{}", i).into_bytes();
        input_tx.send(data).await?;
    }

    // 接收整形后的数据
    let mut count = 0;
    let start = Instant::now();
    while count < 20 {
        if let Some(_data) = output_rx.recv().await {
            count += 1;
            if count <= 5 || count >= 16 {
                println!("  接收整形数据包 {}", count);
            }
        }
        if start.elapsed() > Duration::from_secs(5) {
            break;
        }
    }

    println!("  共接收 {} 个整形后的数据包", count);

    println!("\n✅ 流量控制与整形系统测试完成!");

    Ok(())
}
```

---

## 性能优化

### 1. **无锁实现**

```rust
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};

pub struct LockFreeTokenBucket {
    tokens: AtomicU64,
    last_refill_ns: AtomicU64,
    capacity: u64,
    refill_rate: u64,
}

impl LockFreeTokenBucket {
    pub fn try_acquire(&self, tokens: u64) -> bool {
        loop {
            let current_tokens = self.tokens.load(Ordering::Acquire);
            
            if current_tokens < tokens {
                return false;
            }

            if self.tokens.compare_exchange(
                current_tokens,
                current_tokens - tokens,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                return true;
            }
        }
    }
}
```

### 2. **批量处理**

对于高吞吐场景，使用批量获取令牌可以减少锁竞争。

### 3. **分层限流**

```rust
pub struct HierarchicalRateLimiter {
    global_limiter: Arc<TokenBucketLimiter>,
    tenant_limiters: Arc<RwLock<HashMap<String, Arc<TokenBucketLimiter>>>>,
}
```

---

## 最佳实践

### 1. **选择合适的算法**

- **令牌桶**: 允许突发流量，适合大多数场景
- **漏桶**: 严格限速，适合需要平滑输出的场景
- **滑动窗口**: 精确限流，适合需要严格控制的场景

### 2. **参数配置建议**

```rust
// 令牌桶配置
let token_bucket = TokenBucketLimiter::new(
    1000,  // 容量：允许突发
    100,   // 补充速率：平均速率
);

// 漏桶配置
let leaky_bucket = LeakyBucketLimiter::new(
    500,   // 容量：缓冲大小
    50,    // 泄露速率：输出速率
);
```

### 3. **监控与告警**

```rust
// 定期检查限流指标
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let metrics = limiter.get_metrics().await;
        
        let denial_rate = metrics.denied_requests as f64 / metrics.total_requests as f64;
        if denial_rate > 0.1 {
            tracing::warn!("High denial rate: {:.2}%", denial_rate * 100.0);
        }
    }
});
```

### 4. **分布式场景**

- 使用 Redis 实现全局限流
- 考虑网络延迟和时钟偏差
- 实现降级策略

---

## 依赖项

```toml
[dependencies]
tokio = { version = "1.41", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
redis = { version = "0.27", features = ["tokio-comp", "script"] }
tracing = "0.1"
tracing-subscriber = "0.3"
sysinfo = "0.32"
futures = "0.3"
```

---

## 总结

本文档提供了完整的 OTLP 流量控制与整形的 Rust 实现，包括：

✅ **多种限流算法**: 令牌桶、漏桶、滑动窗口
✅ **分布式限流**: 基于 Redis 的全局流控
✅ **流量整形**: 平滑流量峰值
✅ **背压处理**: 优雅处理下游压力
✅ **自适应流控**: 根据系统负载动态调节
✅ **生产就绪**: 监控、指标、最佳实践

通过这些实现，您可以构建高性能、高可用的 OTLP 流量控制系统。
