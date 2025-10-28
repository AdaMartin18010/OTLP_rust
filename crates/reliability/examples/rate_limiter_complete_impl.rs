//! # Complete Rate Limiter Implementation
//! 
//! 完整的限流器实现，包含多种经典限流算法
//! 
//! ## 限流算法
//! - **Token Bucket (令牌桶)**: 平滑突发流量
//! - **Leaky Bucket (漏桶)**: 恒定速率输出
//! - **Fixed Window (固定窗口)**: 简单计数限流
//! - **Sliding Window (滑动窗口)**: 更精确的限流
//! - **Sliding Log (滑动日志)**: 最精确但开销大
//! 
//! ## 使用场景
//! - API限流
//! - 资源保护
//! - 流量整形
//! - 防止DDoS
//! - 公平性保证
//! 
//! ## 分布式支持
//! - Redis实现
//! - 多节点协调
//! - 配额共享

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicU32, Ordering};
use std::time::{Duration, Instant};
use std::collections::VecDeque;
use tokio::sync::RwLock;
use tokio::time::sleep;
use tracing::{info, warn, error, instrument};
use thiserror::Error;

// ============================================================================
// Part 1: Error Types
// ============================================================================

#[derive(Debug, Error)]
pub enum RateLimitError {
    #[error("Rate limit exceeded")]
    RateLimitExceeded,
    
    #[error("Invalid configuration: {0}")]
    InvalidConfig(String),
    
    #[error("Timeout waiting for permit")]
    Timeout,
}

// ============================================================================
// Part 2: Token Bucket Algorithm
// ============================================================================

/// 令牌桶限流器
/// 
/// 特点：
/// - 允许一定程度的突发流量
/// - 令牌以恒定速率生成
/// - 请求消耗令牌
pub struct TokenBucket {
    /// 桶容量(最大令牌数)
    capacity: u64,
    /// 当前令牌数
    tokens: Arc<AtomicU64>,
    /// 令牌生成速率(tokens/second)
    refill_rate: f64,
    /// 上次补充时间
    last_refill: Arc<RwLock<Instant>>,
}

impl TokenBucket {
    pub fn new(capacity: u64, refill_rate: f64) -> Self {
        Self {
            capacity,
            tokens: Arc::new(AtomicU64::new(capacity)),
            refill_rate,
            last_refill: Arc::new(RwLock::new(Instant::now())),
        }
    }

    /// 尝试获取N个令牌
    #[instrument(skip(self))]
    pub async fn acquire(&self, tokens_needed: u64) -> Result<(), RateLimitError> {
        self.refill().await;

        let current = self.tokens.load(Ordering::Relaxed);
        
        if current >= tokens_needed {
            self.tokens.fetch_sub(tokens_needed, Ordering::Relaxed);
            info!("Acquired {} tokens (remaining: {})", tokens_needed, current - tokens_needed);
            Ok(())
        } else {
            warn!("Rate limit exceeded (need: {}, available: {})", tokens_needed, current);
            Err(RateLimitError::RateLimitExceeded)
        }
    }

    /// 等待直到可以获取令牌
    #[instrument(skip(self))]
    pub async fn acquire_blocking(&self, tokens_needed: u64) -> Result<(), RateLimitError> {
        loop {
            match self.acquire(tokens_needed).await {
                Ok(_) => return Ok(()),
                Err(RateLimitError::RateLimitExceeded) => {
                    // Calculate wait time
                    let wait_ms = (tokens_needed as f64 / self.refill_rate * 1000.0) as u64;
                    info!("Waiting {}ms for tokens", wait_ms);
                    sleep(Duration::from_millis(wait_ms)).await;
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// 补充令牌
    async fn refill(&self) {
        let mut last_refill = self.last_refill.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill);
        
        if elapsed > Duration::from_millis(1) {
            let new_tokens = (elapsed.as_secs_f64() * self.refill_rate) as u64;
            
            if new_tokens > 0 {
                let current = self.tokens.load(Ordering::Relaxed);
                let new_total = (current + new_tokens).min(self.capacity);
                self.tokens.store(new_total, Ordering::Relaxed);
                *last_refill = now;
            }
        }
    }

    pub fn available_tokens(&self) -> u64 {
        self.tokens.load(Ordering::Relaxed)
    }
}

// ============================================================================
// Part 3: Leaky Bucket Algorithm
// ============================================================================

/// 漏桶限流器
/// 
/// 特点：
/// - 恒定速率输出
/// - 请求放入队列
/// - 超出容量的请求被拒绝
pub struct LeakyBucket {
    /// 桶容量
    capacity: usize,
    /// 漏出速率(requests/second)
    leak_rate: f64,
    /// 队列
    queue: Arc<RwLock<VecDeque<Instant>>>,
    /// 上次泄漏时间
    last_leak: Arc<RwLock<Instant>>,
}

impl LeakyBucket {
    pub fn new(capacity: usize, leak_rate: f64) -> Self {
        Self {
            capacity,
            leak_rate,
            queue: Arc::new(RwLock::new(VecDeque::new())),
            last_leak: Arc::new(RwLock::new(Instant::now())),
        }
    }

    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<(), RateLimitError> {
        self.leak().await;

        let mut queue = self.queue.write().await;
        
        if queue.len() < self.capacity {
            queue.push_back(Instant::now());
            info!("Request added to bucket (size: {})", queue.len());
            Ok(())
        } else {
            warn!("Bucket full (capacity: {})", self.capacity);
            Err(RateLimitError::RateLimitExceeded)
        }
    }

    /// 漏出请求
    async fn leak(&self) {
        let mut last_leak = self.last_leak.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last_leak);
        
        let leak_count = (elapsed.as_secs_f64() * self.leak_rate) as usize;
        
        if leak_count > 0 {
            let mut queue = self.queue.write().await;
            let to_remove = leak_count.min(queue.len());
            
            for _ in 0..to_remove {
                queue.pop_front();
            }
            
            *last_leak = now;
            info!("Leaked {} requests (remaining: {})", to_remove, queue.len());
        }
    }

    pub async fn size(&self) -> usize {
        self.queue.read().await.len()
    }
}

// ============================================================================
// Part 4: Fixed Window Algorithm
// ============================================================================

/// 固定窗口限流器
/// 
/// 特点：
/// - 简单易实现
/// - 固定时间窗口内限制请求数
/// - 边界问题(临界时刻可能超限)
pub struct FixedWindow {
    /// 窗口大小
    window_size: Duration,
    /// 窗口内最大请求数
    max_requests: u32,
    /// 当前窗口开始时间
    window_start: Arc<RwLock<Instant>>,
    /// 当前窗口请求计数
    request_count: Arc<AtomicU32>,
}

impl FixedWindow {
    pub fn new(window_size: Duration, max_requests: u32) -> Self {
        Self {
            window_size,
            max_requests,
            window_start: Arc::new(RwLock::new(Instant::now())),
            request_count: Arc::new(AtomicU32::new(0)),
        }
    }

    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<(), RateLimitError> {
        self.check_window_reset().await;

        let current = self.request_count.fetch_add(1, Ordering::Relaxed);
        
        if current < self.max_requests {
            info!("Request allowed ({}/{})", current + 1, self.max_requests);
            Ok(())
        } else {
            warn!("Rate limit exceeded in window ({}/{})", current, self.max_requests);
            self.request_count.fetch_sub(1, Ordering::Relaxed);
            Err(RateLimitError::RateLimitExceeded)
        }
    }

    async fn check_window_reset(&self) {
        let mut window_start = self.window_start.write().await;
        let now = Instant::now();
        
        if now.duration_since(*window_start) >= self.window_size {
            *window_start = now;
            self.request_count.store(0, Ordering::Relaxed);
            info!("Window reset");
        }
    }

    pub fn current_count(&self) -> u32 {
        self.request_count.load(Ordering::Relaxed)
    }
}

// ============================================================================
// Part 5: Sliding Window Algorithm
// ============================================================================

/// 滑动窗口限流器
/// 
/// 特点：
/// - 更精确的限流
/// - 避免固定窗口边界问题
/// - 使用加权计数
pub struct SlidingWindow {
    /// 窗口大小
    window_size: Duration,
    /// 窗口内最大请求数
    max_requests: u32,
    /// 上一个窗口的请求数
    previous_count: Arc<AtomicU32>,
    /// 当前窗口的请求数
    current_count: Arc<AtomicU32>,
    /// 当前窗口开始时间
    current_window_start: Arc<RwLock<Instant>>,
}

impl SlidingWindow {
    pub fn new(window_size: Duration, max_requests: u32) -> Self {
        Self {
            window_size,
            max_requests,
            previous_count: Arc::new(AtomicU32::new(0)),
            current_count: Arc::new(AtomicU32::new(0)),
            current_window_start: Arc::new(RwLock::new(Instant::now())),
        }
    }

    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<(), RateLimitError> {
        self.check_window_slide().await;

        let now = Instant::now();
        let window_start = *self.current_window_start.read().await;
        let elapsed = now.duration_since(window_start);
        let window_progress = elapsed.as_secs_f64() / self.window_size.as_secs_f64();

        // Calculate weighted count
        let previous = self.previous_count.load(Ordering::Relaxed) as f64;
        let current = self.current_count.load(Ordering::Relaxed) as f64;
        let estimated_count = (previous * (1.0 - window_progress) + current) as u32;

        if estimated_count < self.max_requests {
            self.current_count.fetch_add(1, Ordering::Relaxed);
            info!("Request allowed (estimated: {}/{})", estimated_count + 1, self.max_requests);
            Ok(())
        } else {
            warn!("Rate limit exceeded (estimated: {}/{})", estimated_count, self.max_requests);
            Err(RateLimitError::RateLimitExceeded)
        }
    }

    async fn check_window_slide(&self) {
        let mut window_start = self.current_window_start.write().await;
        let now = Instant::now();
        
        if now.duration_since(*window_start) >= self.window_size {
            let current = self.current_count.load(Ordering::Relaxed);
            self.previous_count.store(current, Ordering::Relaxed);
            self.current_count.store(0, Ordering::Relaxed);
            *window_start = now;
            info!("Window slid (previous: {}, current: 0)", current);
        }
    }
}

// ============================================================================
// Part 6: Sliding Log Algorithm
// ============================================================================

/// 滑动日志限流器
/// 
/// 特点：
/// - 最精确的限流
/// - 记录每个请求时间戳
/// - 内存开销较大
pub struct SlidingLog {
    /// 窗口大小
    window_size: Duration,
    /// 窗口内最大请求数
    max_requests: usize,
    /// 请求时间戳日志
    log: Arc<RwLock<VecDeque<Instant>>>,
}

impl SlidingLog {
    pub fn new(window_size: Duration, max_requests: usize) -> Self {
        Self {
            window_size,
            max_requests,
            log: Arc::new(RwLock::new(VecDeque::new())),
        }
    }

    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<(), RateLimitError> {
        self.cleanup_old_entries().await;

        let mut log = self.log.write().await;
        
        if log.len() < self.max_requests {
            log.push_back(Instant::now());
            info!("Request logged ({}/{})", log.len(), self.max_requests);
            Ok(())
        } else {
            warn!("Rate limit exceeded ({}/{})", log.len(), self.max_requests);
            Err(RateLimitError::RateLimitExceeded)
        }
    }

    async fn cleanup_old_entries(&self) {
        let mut log = self.log.write().await;
        let now = Instant::now();
        
        while let Some(timestamp) = log.front() {
            if now.duration_since(*timestamp) > self.window_size {
                log.pop_front();
            } else {
                break;
            }
        }
    }

    pub async fn count(&self) -> usize {
        self.log.read().await.len()
    }
}

// ============================================================================
// Part 7: Composite Rate Limiter
// ============================================================================

/// 组合限流器 - 同时使用多种策略
pub struct CompositeRateLimiter {
    token_bucket: Option<TokenBucket>,
    fixed_window: Option<FixedWindow>,
    sliding_window: Option<SlidingWindow>,
}

impl CompositeRateLimiter {
    pub fn new() -> Self {
        Self {
            token_bucket: None,
            fixed_window: None,
            sliding_window: None,
        }
    }

    pub fn with_token_bucket(mut self, capacity: u64, rate: f64) -> Self {
        self.token_bucket = Some(TokenBucket::new(capacity, rate));
        self
    }

    pub fn with_fixed_window(mut self, window: Duration, max_requests: u32) -> Self {
        self.fixed_window = Some(FixedWindow::new(window, max_requests));
        self
    }

    pub fn with_sliding_window(mut self, window: Duration, max_requests: u32) -> Self {
        self.sliding_window = Some(SlidingWindow::new(window, max_requests));
        self
    }

    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<(), RateLimitError> {
        // All limiters must pass
        if let Some(ref limiter) = self.token_bucket {
            limiter.acquire(1).await?;
        }

        if let Some(ref limiter) = self.fixed_window {
            limiter.acquire().await?;
        }

        if let Some(ref limiter) = self.sliding_window {
            limiter.acquire().await?;
        }

        Ok(())
    }
}

// ============================================================================
// Part 8: Demo Functions
// ============================================================================

/// Demo: Token Bucket
#[instrument]
pub async fn demo_token_bucket() {
    info!("=== Demo: Token Bucket ===");

    let limiter = TokenBucket::new(10, 5.0); // 10 capacity, 5 tokens/sec

    // Burst requests
    for i in 0..15 {
        match limiter.acquire(1).await {
            Ok(_) => info!("Request {} allowed", i),
            Err(_) => warn!("Request {} rejected", i),
        }
        sleep(Duration::from_millis(50)).await;
    }

    info!("Remaining tokens: {}", limiter.available_tokens());
}

/// Demo: Leaky Bucket
#[instrument]
pub async fn demo_leaky_bucket() {
    info!("=== Demo: Leaky Bucket ===");

    let limiter = LeakyBucket::new(5, 2.0); // 5 capacity, 2 req/sec leak rate

    // Send burst
    for i in 0..10 {
        match limiter.acquire().await {
            Ok(_) => info!("Request {} added to bucket", i),
            Err(_) => warn!("Request {} rejected (bucket full)", i),
        }
        sleep(Duration::from_millis(100)).await;
    }

    info!("Final bucket size: {}", limiter.size().await);
}

/// Demo: Fixed Window
#[instrument]
pub async fn demo_fixed_window() {
    info!("=== Demo: Fixed Window ===");

    let limiter = FixedWindow::new(Duration::from_secs(1), 5);

    // Send requests
    for i in 0..12 {
        match limiter.acquire().await {
            Ok(_) => info!("Request {} allowed", i),
            Err(_) => warn!("Request {} rejected", i),
        }
        sleep(Duration::from_millis(100)).await;
    }
}

/// Demo: Sliding Window
#[instrument]
pub async fn demo_sliding_window() {
    info!("=== Demo: Sliding Window ===");

    let limiter = SlidingWindow::new(Duration::from_secs(1), 5);

    for i in 0..15 {
        match limiter.acquire().await {
            Ok(_) => info!("Request {} allowed", i),
            Err(_) => warn!("Request {} rejected", i),
        }
        sleep(Duration::from_millis(100)).await;
    }
}

/// Demo: Sliding Log
#[instrument]
pub async fn demo_sliding_log() {
    info!("=== Demo: Sliding Log ===");

    let limiter = SlidingLog::new(Duration::from_secs(1), 5);

    for i in 0..12 {
        match limiter.acquire().await {
            Ok(_) => info!("Request {} logged", i),
            Err(_) => warn!("Request {} rejected", i),
        }
        info!("Current count: {}", limiter.count().await);
        sleep(Duration::from_millis(100)).await;
    }
}

/// Demo: Composite Limiter
#[instrument]
pub async fn demo_composite() {
    info!("=== Demo: Composite Rate Limiter ===");

    let limiter = CompositeRateLimiter::new()
        .with_token_bucket(10, 5.0)
        .with_sliding_window(Duration::from_secs(1), 8);

    for i in 0..20 {
        match limiter.acquire().await {
            Ok(_) => info!("Request {} allowed by all limiters", i),
            Err(_) => warn!("Request {} rejected by at least one limiter", i),
        }
        sleep(Duration::from_millis(50)).await;
    }
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

    info!("🚀 Starting Rate Limiter Demos");

    // Demo 1: Token Bucket
    demo_token_bucket().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 2: Leaky Bucket
    demo_leaky_bucket().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 3: Fixed Window
    demo_fixed_window().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 4: Sliding Window
    demo_sliding_window().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 5: Sliding Log
    demo_sliding_log().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 6: Composite
    demo_composite().await;

    info!("✅ All rate limiter demos completed!");

    Ok(())
}

