# 重试模式 (Retry Pattern) - Rust 1.90 + OTLP 完整实现指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **对标标准**: AWS Well-Architected Framework, Google Cloud Retry Best Practices, Microsoft Azure Retry Guidance

---

## 📑 目录

- [重试模式 (Retry Pattern) - Rust 1.90 + OTLP 完整实现指南](#重试模式-retry-pattern---rust-190--otlp-完整实现指南)
  - [📑 目录](#-目录)
  - [1. 重试模式概述](#1-重试模式概述)
    - [1.1 什么是重试模式?](#11-什么是重试模式)
    - [1.2 暂时性故障 vs 永久性故障](#12-暂时性故障-vs-永久性故障)
    - [1.3 何时使用重试模式?](#13-何时使用重试模式)
  - [2. 核心退避策略](#2-核心退避策略)
    - [2.1 常见退避策略](#21-常见退避策略)
    - [2.2 退避策略对比](#22-退避策略对比)
    - [2.3 "惊群效应" (Thundering Herd) 问题](#23-惊群效应-thundering-herd-问题)
  - [3. Rust 1.90 完整实现](#3-rust-190-完整实现)
    - [3.1 项目结构](#31-项目结构)
    - [3.2 依赖配置 (`Cargo.toml`)](#32-依赖配置-cargotoml)
    - [3.3 退避算法实现](#33-退避算法实现)
    - [3.4 重试策略实现](#34-重试策略实现)
    - [3.5 错误分类](#35-错误分类)
    - [3.6 重试执行器](#36-重试执行器)
  - [4. 幂等性设计](#4-幂等性设计)
    - [4.1 什么是幂等性?](#41-什么是幂等性)
    - [4.2 实现幂等性](#42-实现幂等性)
      - [4.2.1 幂等键 (Idempotency Key)](#421-幂等键-idempotency-key)
      - [4.2.2 条件更新 (Conditional Update)](#422-条件更新-conditional-update)
  - [5. OTLP 追踪与监控](#5-otlp-追踪与监控)
    - [5.1 追踪重试过程](#51-追踪重试过程)
    - [5.2 Jaeger 追踪示例](#52-jaeger-追踪示例)
  - [6. 重试策略配置](#6-重试策略配置)
    - [6.1 不同场景的配置](#61-不同场景的配置)
  - [7. 与微服务集成](#7-与微服务集成)
    - [7.1 HTTP 客户端集成](#71-http-客户端集成)
  - [8. 部署与监控](#8-部署与监控)
    - [8.1 Prometheus Metrics](#81-prometheus-metrics)
  - [9. 最佳实践与陷阱](#9-最佳实践与陷阱)
    - [9.1 最佳实践](#91-最佳实践)
    - [9.2 常见陷阱](#92-常见陷阱)
  - [10. 与其他模式组合](#10-与其他模式组合)
    - [10.1 重试 + 熔断器](#101-重试--熔断器)
    - [10.2 重试 + 超时](#102-重试--超时)
  - [📚 参考资料](#-参考资料)
    - [国际标准与最佳实践](#国际标准与最佳实践)
  - [✅ 总结](#-总结)
    - [重试模式核心价值](#重试模式核心价值)
    - [关键设计原则](#关键设计原则)

---

## 1. 重试模式概述

### 1.1 什么是重试模式?

**Retry Pattern** (重试模式) 是一种弹性架构模式,当操作失败时自动重试,以应对暂时性故障(Transient Faults)。

**核心思想**: 许多故障是暂时的(网络抖动、服务临时过载),短暂等待后重试往往能成功。

```text
┌──────────────────────────────────────────────────────────────┐
│              无重试: 一次失败即放弃                            │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Client ──► Request ──► Network Glitch 💥 ──► Error         │
│                                                              │
│  ❌ 问题:                                                    │
│     • 暂时性故障(如网络抖动)导致操作失败                        │
│     • 用户体验差,需要手动重试                                  │
│     • 系统可用性降低                                          │
│                                                              │
└──────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────┐
│              有重试: 自动重试直到成功                          │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Client ──► Request 1 ──► Network Glitch 💥 ──► Retry       │
│                    ↓                                         │
│              Wait 100ms                                      │
│                    ↓                                         │
│             Request 2 ──► Server Overload 💥 ──► Retry       │
│                    ↓                                         │
│              Wait 200ms (指数退避)                            │
│                    ↓                                         │
│             Request 3 ──► Success ✅                         │
│                                                              │
│  ✅ 优势:                                                    │
│     • 自动处理暂时性故障                                      │
│     • 提高系统可用性和用户体验                                 │
│     • 无需人工干预                                            │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 1.2 暂时性故障 vs 永久性故障

| 故障类型 | 特征 | 是否应该重试 | 示例 |
|---------|------|-------------|------|
| **暂时性故障** (Transient Fault) | 短暂发生,可自行恢复 | ✅ **应该重试** | 网络抖动、服务临时过载、数据库连接池满 |
| **永久性故障** (Permanent Fault) | 持续存在,不会自行恢复 | ❌ **不应重试** | 404 Not Found、401 Unauthorized、参数错误 |
| **限流故障** (Throttling) | 超过速率限制 | ⚠️ **谨慎重试** | 429 Too Many Requests (需指数退避) |

### 1.3 何时使用重试模式?

| 场景 | 是否适用 | 原因 |
|------|---------|------|
| 调用外部 API (第三方服务) | ✅ **强烈推荐** | 网络不稳定,服务可能临时不可用 |
| 分布式系统中的微服务调用 | ✅ 推荐 | 网络延迟、服务临时过载常见 |
| 数据库操作 (SELECT) | ✅ 推荐 | 连接池满、主从切换等暂时性问题 |
| 数据库写操作 (INSERT/UPDATE) | ⚠️ 谨慎使用 | 需要确保幂等性,避免重复写入 |
| 本地文件操作 | ❌ 不必要 | 本地操作失败通常是永久性的 |
| 用户输入验证 | ❌ 不必要 | 验证错误是逻辑错误,不是暂时性故障 |

---

## 2. 核心退避策略

### 2.1 常见退避策略

```rust
/// 退避策略 (Backoff Strategy)
#[derive(Debug, Clone)]
pub enum BackoffStrategy {
    /// 固定延迟 (Fixed Delay)
    /// 每次重试间隔固定
    /// 例如: 100ms, 100ms, 100ms
    Fixed { delay: Duration },

    /// 线性退避 (Linear Backoff)
    /// 线性增长
    /// 例如: 100ms, 200ms, 300ms
    Linear {
        initial_delay: Duration,
        increment: Duration,
    },

    /// 指数退避 (Exponential Backoff)
    /// 指数增长 (最常用)
    /// 例如: 100ms, 200ms, 400ms, 800ms
    Exponential {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
    },

    /// 指数退避 + 抖动 (Exponential Backoff with Jitter)
    /// 加入随机性,避免"惊群效应" (Thundering Herd)
    /// 例如: 100ms±20ms, 200ms±40ms, 400ms±80ms
    ExponentialWithJitter {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
        jitter_factor: f64, // 0.0 - 1.0
    },

    /// 装饰性退避 (Decorrelated Jitter)
    /// AWS 推荐的算法,更好的分散重试时间
    /// delay = random(base_delay, prev_delay * 3)
    DecorrelatedJitter {
        base_delay: Duration,
        max_delay: Duration,
    },
}
```

### 2.2 退避策略对比

```text
┌─────────────────────────────────────────────────────────────┐
│              退避策略可视化                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  时间 (ms)                                                   │
│  1000 │                                                     │
│       │                                  ● 指数退避         │
│   800 │                              ●                      │
│       │                                                     │
│   600 │                          ●                          │
│       │              ▲ 线性退避  ●                          │
│   400 │          ▲           ●                              │
│       │      ▲           ●                                  │
│   200 │  ▲   ■───────────────────  固定延迟                 │
│       │  ■   ■   ■   ■   ■                                  │
│     0 └──┴───┴───┴───┴───┴───► 重试次数                     │
│         1   2   3   4   5                                   │
│                                                             │
│  📊 对比:                                                    │
│     • 固定延迟: 简单,但高负载时可能加剧拥塞                  │
│     • 线性退避: 温和增长,适合中等负载                       │
│     • 指数退避: 快速拉大间隔,适合高负载(推荐)               │
│     • 加抖动: 避免多个客户端同时重试(最佳)                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.3 "惊群效应" (Thundering Herd) 问题

```text
┌─────────────────────────────────────────────────────────────┐
│          无抖动: 惊群效应 (Thundering Herd)                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  服务故障 💥                                                 │
│       ↓                                                      │
│  1000 个客户端同时失败                                       │
│       ↓                                                      │
│  使用固定延迟 100ms                                          │
│       ↓                                                      │
│  100ms 后,1000 个客户端 "同时" 重试 💥💥💥                    │
│       ↓                                                      │
│  服务再次被打垮!                                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│          有抖动: 分散重试时间 (Jitter)                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  服务故障 💥                                                 │
│       ↓                                                      │
│  1000 个客户端同时失败                                       │
│       ↓                                                      │
│  使用指数退避 + 抖动                                         │
│       ↓                                                      │
│  客户端在 80ms-120ms 之间 "随机" 重试                        │
│  ├── 客户端 1: 85ms                                         │
│  ├── 客户端 2: 112ms                                        │
│  ├── 客户端 3: 93ms                                         │
│  └── ... (时间分散)                                          │
│       ↓                                                      │
│  服务逐步恢复,避免被打垮 ✅                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. Rust 1.90 完整实现

### 3.1 项目结构

```text
retry-rs/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   │
│   ├── retry/
│   │   ├── mod.rs
│   │   ├── strategy.rs           # 重试策略
│   │   ├── backoff.rs            # 退避算法
│   │   ├── policy.rs             # 重试策略
│   │   └── error.rs              # 错误分类
│   │
│   ├── middleware/               # Axum 中间件
│   │   └── retry_middleware.rs
│   │
│   ├── telemetry/                # OTLP 集成
│   │   └── mod.rs
│   │
│   └── examples/
│       ├── basic_retry.rs
│       └── http_client_retry.rs
│
└── tests/
    ├── backoff_tests.rs
    └── integration_tests.rs
```

### 3.2 依赖配置 (`Cargo.toml`)

```toml
[package]
name = "retry-rs"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# 时间处理
chrono = "0.4"

# 随机数 (用于抖动)
rand = "0.8"

# OpenTelemetry
opentelemetry = "0.31"
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# HTTP 客户端 (示例)
reqwest = { version = "0.12", optional = true }

# Web 框架 (可选)
axum = { version = "0.7", optional = true }
```

### 3.3 退避算法实现

```rust
// src/retry/backoff.rs
use std::time::Duration;
use rand::Rng;

/// 退避策略
#[derive(Debug, Clone)]
pub enum BackoffStrategy {
    Fixed {
        delay: Duration,
    },
    Linear {
        initial_delay: Duration,
        increment: Duration,
    },
    Exponential {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
    },
    ExponentialWithJitter {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
        jitter_factor: f64,
    },
    DecorrelatedJitter {
        base_delay: Duration,
        max_delay: Duration,
    },
}

impl BackoffStrategy {
    /// 计算下次重试延迟
    pub fn next_delay(&self, attempt: usize, prev_delay: Option<Duration>) -> Duration {
        match self {
            Self::Fixed { delay } => *delay,

            Self::Linear { initial_delay, increment } => {
                *initial_delay + *increment * attempt as u32
            }

            Self::Exponential { initial_delay, multiplier, max_delay } => {
                let delay = initial_delay.as_millis() as f64 * multiplier.powi(attempt as i32);
                Duration::from_millis(delay.min(max_delay.as_millis() as f64) as u64)
            }

            Self::ExponentialWithJitter {
                initial_delay,
                multiplier,
                max_delay,
                jitter_factor,
            } => {
                // 计算基础延迟
                let base_delay = initial_delay.as_millis() as f64 * multiplier.powi(attempt as i32);
                let base_delay = base_delay.min(max_delay.as_millis() as f64);

                // 加入抖动
                let jitter_range = base_delay * jitter_factor;
                let mut rng = rand::thread_rng();
                let jitter = rng.gen_range(-jitter_range..=jitter_range);
                let final_delay = (base_delay + jitter).max(0.0);

                Duration::from_millis(final_delay as u64)
            }

            Self::DecorrelatedJitter { base_delay, max_delay } => {
                // AWS 推荐的装饰性抖动算法
                // delay = random(base_delay, prev_delay * 3)
                let prev = prev_delay.unwrap_or(*base_delay);
                let upper_bound = (prev.as_millis() * 3).min(max_delay.as_millis());
                
                let mut rng = rand::thread_rng();
                let delay_ms = rng.gen_range(base_delay.as_millis()..=upper_bound);
                
                Duration::from_millis(delay_ms as u64)
            }
        }
    }
}

impl Default for BackoffStrategy {
    fn default() -> Self {
        // 默认: 指数退避 + 抖动
        Self::ExponentialWithJitter {
            initial_delay: Duration::from_millis(100),
            multiplier: 2.0,
            max_delay: Duration::from_secs(30),
            jitter_factor: 0.2, // ±20% 抖动
        }
    }
}
```

### 3.4 重试策略实现

```rust
// src/retry/policy.rs
use std::time::Duration;
use crate::retry::backoff::BackoffStrategy;
use crate::retry::error::ErrorClassification;

/// 重试策略
#[derive(Debug, Clone)]
pub struct RetryPolicy {
    /// 最大重试次数
    pub max_attempts: usize,

    /// 退避策略
    pub backoff: BackoffStrategy,

    /// 整体超时时间 (所有重试加起来的时间)
    pub total_timeout: Option<Duration>,

    /// 错误分类器 (决定哪些错误应该重试)
    pub error_classifier: ErrorClassifier,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            backoff: BackoffStrategy::default(),
            total_timeout: Some(Duration::from_secs(60)),
            error_classifier: ErrorClassifier::default(),
        }
    }
}

/// 错误分类器
#[derive(Debug, Clone)]
pub struct ErrorClassifier {
    /// 可重试的 HTTP 状态码
    pub retryable_status_codes: Vec<u16>,
}

impl Default for ErrorClassifier {
    fn default() -> Self {
        Self {
            retryable_status_codes: vec![
                408, // Request Timeout
                429, // Too Many Requests
                500, // Internal Server Error
                502, // Bad Gateway
                503, // Service Unavailable
                504, // Gateway Timeout
            ],
        }
    }
}

impl ErrorClassifier {
    /// 判断错误是否可重试
    pub fn is_retryable(&self, classification: &ErrorClassification) -> bool {
        match classification {
            ErrorClassification::Transient => true,
            ErrorClassification::Permanent => false,
            ErrorClassification::HttpStatus(code) => {
                self.retryable_status_codes.contains(code)
            }
            ErrorClassification::NetworkError => true,
            ErrorClassification::Timeout => true,
        }
    }
}
```

### 3.5 错误分类

```rust
// src/retry/error.rs
use thiserror::Error;

/// 错误分类
#[derive(Debug, Clone)]
pub enum ErrorClassification {
    /// 暂时性故障 (可重试)
    Transient,

    /// 永久性故障 (不应重试)
    Permanent,

    /// HTTP 状态码错误
    HttpStatus(u16),

    /// 网络错误 (可重试)
    NetworkError,

    /// 超时错误 (可重试)
    Timeout,
}

#[derive(Debug, Error)]
pub enum RetryError {
    #[error("Max retry attempts exceeded")]
    MaxAttemptsExceeded,

    #[error("Total timeout exceeded")]
    TotalTimeoutExceeded,

    #[error("Permanent error (not retryable): {0}")]
    PermanentError(String),

    #[error("Operation failed: {0}")]
    OperationFailed(String),
}
```

### 3.6 重试执行器

```rust
// src/retry/mod.rs
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::{info, warn, instrument};

pub mod backoff;
pub mod policy;
pub mod error;

use backoff::BackoffStrategy;
use policy::RetryPolicy;
use error::{ErrorClassification, RetryError};

/// 重试执行器
pub struct RetryExecutor {
    policy: RetryPolicy,
}

impl RetryExecutor {
    pub fn new(policy: RetryPolicy) -> Self {
        Self { policy }
    }

    /// 执行带重试的操作
    #[instrument(skip(self, operation), fields(
        retry.max_attempts = %self.policy.max_attempts,
        retry.backoff = ?self.policy.backoff
    ))]
    pub async fn execute<F, T, E>(&self, mut operation: F) -> Result<T, RetryError>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Display + Classify,
    {
        let start_time = Instant::now();
        let mut prev_delay: Option<Duration> = None;

        for attempt in 0..self.policy.max_attempts {
            // 检查总超时
            if let Some(total_timeout) = self.policy.total_timeout {
                if start_time.elapsed() > total_timeout {
                    warn!("⏱️ Total timeout exceeded");
                    return Err(RetryError::TotalTimeoutExceeded);
                }
            }

            // 执行操作
            info!("🔄 Attempt {} of {}", attempt + 1, self.policy.max_attempts);
            let result = operation().await;

            match result {
                Ok(value) => {
                    info!("✅ Operation succeeded on attempt {}", attempt + 1);
                    return Ok(value);
                }
                Err(e) => {
                    let classification = e.classify();
                    warn!("❌ Attempt {} failed: {}", attempt + 1, e);

                    // 检查是否应该重试
                    if !self.policy.error_classifier.is_retryable(&classification) {
                        warn!("🚫 Error is not retryable (permanent failure)");
                        return Err(RetryError::PermanentError(e.to_string()));
                    }

                    // 如果是最后一次尝试,直接返回错误
                    if attempt == self.policy.max_attempts - 1 {
                        warn!("🚫 Max retry attempts exceeded");
                        return Err(RetryError::MaxAttemptsExceeded);
                    }

                    // 计算退避延迟
                    let delay = self.policy.backoff.next_delay(attempt, prev_delay);
                    prev_delay = Some(delay);

                    info!("⏳ Waiting {:?} before next retry", delay);
                    sleep(delay).await;
                }
            }
        }

        unreachable!()
    }
}

/// 错误分类 Trait
pub trait Classify {
    fn classify(&self) -> ErrorClassification;
}

// 为常见错误类型实现 Classify
impl Classify for reqwest::Error {
    fn classify(&self) -> ErrorClassification {
        if self.is_timeout() {
            ErrorClassification::Timeout
        } else if self.is_connect() {
            ErrorClassification::NetworkError
        } else if let Some(status) = self.status() {
            ErrorClassification::HttpStatus(status.as_u16())
        } else {
            ErrorClassification::Transient
        }
    }
}

impl Classify for std::io::Error {
    fn classify(&self) -> ErrorClassification {
        use std::io::ErrorKind;
        match self.kind() {
            ErrorKind::ConnectionRefused | ErrorKind::ConnectionReset | ErrorKind::TimedOut => {
                ErrorClassification::Transient
            }
            ErrorKind::NotFound | ErrorKind::PermissionDenied => {
                ErrorClassification::Permanent
            }
            _ => ErrorClassification::Transient,
        }
    }
}
```

---

## 4. 幂等性设计

### 4.1 什么是幂等性?

**幂等性 (Idempotency)**: 多次执行相同操作,结果与执行一次相同。

```text
┌─────────────────────────────────────────────────────────────┐
│              幂等 vs 非幂等操作                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ✅ 幂等操作 (安全重试):                                     │
│     • GET /api/users/123              (读取,无副作用)       │
│     • PUT /api/users/123 {name: "A"}  (覆盖写入)            │
│     • DELETE /api/users/123           (删除,删除已删除的无影响)│
│                                                             │
│  ❌ 非幂等操作 (重试有风险):                                 │
│     • POST /api/orders                (创建,重试会重复创建) │
│     • POST /api/payments              (扣款,重试会重复扣款) │
│     • PATCH /api/users/123/points +10 (增量更新,重复加分)   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 实现幂等性

#### 4.2.1 幂等键 (Idempotency Key)

```rust
// 使用幂等键确保操作只执行一次
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct IdempotentRequest<T> {
    /// 幂等键 (客户端生成,确保唯一)
    pub idempotency_key: String,

    /// 请求体
    pub body: T,
}

impl<T> IdempotentRequest<T> {
    pub fn new(body: T) -> Self {
        Self {
            idempotency_key: Uuid::new_v4().to_string(),
            body,
        }
    }
}

// 服务端实现
pub struct OrderService {
    processed_keys: Arc<RwLock<HashSet<String>>>,
}

impl OrderService {
    pub async fn create_order(&self, request: IdempotentRequest<OrderData>) -> Result<Order> {
        // 1. 检查幂等键是否已处理
        {
            let keys = self.processed_keys.read().await;
            if keys.contains(&request.idempotency_key) {
                tracing::info!("🔁 Duplicate request detected, returning cached result");
                return self.get_cached_result(&request.idempotency_key).await;
            }
        }

        // 2. 处理请求
        let order = self.create_order_internal(request.body).await?;

        // 3. 记录幂等键
        {
            let mut keys = self.processed_keys.write().await;
            keys.insert(request.idempotency_key.clone());
        }

        Ok(order)
    }
}
```

#### 4.2.2 条件更新 (Conditional Update)

```rust
// 使用版本号或时间戳实现幂等性
#[derive(Debug, Clone)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub version: i64, // 版本号 (乐观锁)
}

impl UserService {
    /// 幂等的更新操作 (使用版本号)
    pub async fn update_user(&self, user: User) -> Result<User, UpdateError> {
        let updated = sqlx::query_as!(
            User,
            r#"
            UPDATE users
            SET name = $1, version = version + 1
            WHERE id = $2 AND version = $3
            RETURNING id, name, version
            "#,
            user.name,
            user.id,
            user.version
        )
        .fetch_optional(&self.db)
        .await?;

        match updated {
            Some(user) => Ok(user),
            None => Err(UpdateError::VersionMismatch), // 版本不匹配,已被其他请求更新
        }
    }
}
```

---

## 5. OTLP 追踪与监控

### 5.1 追踪重试过程

```rust
// src/retry/mod.rs (追踪增强)
use tracing::{info, warn, instrument, Span};
use opentelemetry::trace::{Span as OtelSpan, Tracer};

impl RetryExecutor {
    #[instrument(skip(self, operation), fields(
        retry.max_attempts = %self.policy.max_attempts,
        retry.current_attempt = 0,
        retry.total_delay_ms = 0,
        otel.kind = "client"
    ))]
    pub async fn execute<F, T, E>(&self, mut operation: F) -> Result<T, RetryError>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Display + Classify,
    {
        let span = Span::current();
        let start_time = Instant::now();
        let mut total_delay = Duration::ZERO;
        let mut prev_delay: Option<Duration> = None;

        for attempt in 0..self.policy.max_attempts {
            // 更新 Span 属性
            span.record("retry.current_attempt", attempt + 1);

            // 执行操作
            let result = operation().await;

            match result {
                Ok(value) => {
                    span.record("retry.success", true);
                    span.record("retry.final_attempt", attempt + 1);
                    return Ok(value);
                }
                Err(e) => {
                    let classification = e.classify();
                    
                    // 记录失败信息
                    span.record("retry.last_error", e.to_string().as_str());
                    span.record("retry.error_classification", format!("{:?}", classification).as_str());

                    if !self.policy.error_classifier.is_retryable(&classification) {
                        span.record("retry.success", false);
                        span.record("retry.failure_reason", "permanent_error");
                        return Err(RetryError::PermanentError(e.to_string()));
                    }

                    if attempt == self.policy.max_attempts - 1 {
                        span.record("retry.success", false);
                        span.record("retry.failure_reason", "max_attempts_exceeded");
                        return Err(RetryError::MaxAttemptsExceeded);
                    }

                    // 计算退避延迟
                    let delay = self.policy.backoff.next_delay(attempt, prev_delay);
                    total_delay += delay;
                    prev_delay = Some(delay);

                    span.record("retry.total_delay_ms", total_delay.as_millis() as i64);

                    sleep(delay).await;
                }
            }
        }

        unreachable!()
    }
}
```

### 5.2 Jaeger 追踪示例

```text
🔍 Jaeger Trace 示例 (Retry):

Trace ID: abc123def456
Span 1: http_client.request (duration: 1250ms)
  ├── Attribute: http.method = "POST"
  ├── Attribute: http.url = "/api/orders"
  ├── Attribute: retry.max_attempts = "3"
  │
  ├── Span 2: retry.execute (duration: 1245ms)
  │   ├── Attribute: retry.max_attempts = "3"
  │   ├── Attribute: retry.current_attempt = "3"
  │   ├── Attribute: retry.total_delay_ms = "300"
  │   ├── Attribute: retry.success = "true"
  │   ├── Attribute: retry.final_attempt = "3"
  │   │
  │   ├── Span 3: attempt_1 (duration: 150ms)
  │   │   ├── Attribute: http.status_code = "503"
  │   │   └── Event: "Service Unavailable, retrying..."
  │   │
  │   ├── Event: "Waiting 100ms before retry"
  │   │
  │   ├── Span 4: attempt_2 (duration: 180ms)
  │   │   ├── Attribute: http.status_code = "504"
  │   │   └── Event: "Gateway Timeout, retrying..."
  │   │
  │   ├── Event: "Waiting 200ms before retry"
  │   │
  │   └── Span 5: attempt_3 (duration: 815ms)
  │       ├── Attribute: http.status_code = "200"
  │       └── Event: "Success ✅"
  │
  └── Attribute: http.status_code = "200"

✅ 通过追踪可以看到:
   • 总共尝试了 3 次
   • 总退避延迟 300ms
   • 最终第 3 次成功
   • 可以精确看到每次失败的原因
```

---

## 6. 重试策略配置

### 6.1 不同场景的配置

```rust
/// 为不同场景配置不同的重试策略
pub struct RetryPolicyRegistry;

impl RetryPolicyRegistry {
    /// 外部 API 调用 (激进重试)
    pub fn for_external_api() -> RetryPolicy {
        RetryPolicy {
            max_attempts: 5,
            backoff: BackoffStrategy::ExponentialWithJitter {
                initial_delay: Duration::from_millis(100),
                multiplier: 2.0,
                max_delay: Duration::from_secs(10),
                jitter_factor: 0.3, // ±30% 抖动
            },
            total_timeout: Some(Duration::from_secs(30)),
            error_classifier: ErrorClassifier::default(),
        }
    }

    /// 内部微服务调用 (温和重试)
    pub fn for_internal_service() -> RetryPolicy {
        RetryPolicy {
            max_attempts: 3,
            backoff: BackoffStrategy::Exponential {
                initial_delay: Duration::from_millis(50),
                multiplier: 2.0,
                max_delay: Duration::from_secs(5),
            },
            total_timeout: Some(Duration::from_secs(15)),
            error_classifier: ErrorClassifier::default(),
        }
    }

    /// 数据库查询 (保守重试)
    pub fn for_database() -> RetryPolicy {
        RetryPolicy {
            max_attempts: 2,
            backoff: BackoffStrategy::Fixed {
                delay: Duration::from_millis(100),
            },
            total_timeout: Some(Duration::from_secs(5)),
            error_classifier: ErrorClassifier {
                retryable_status_codes: vec![], // 数据库错误不使用 HTTP 状态码
            },
        }
    }

    /// 非关键功能 (快速失败)
    pub fn for_non_critical() -> RetryPolicy {
        RetryPolicy {
            max_attempts: 2,
            backoff: BackoffStrategy::Fixed {
                delay: Duration::from_millis(50),
            },
            total_timeout: Some(Duration::from_secs(2)),
            error_classifier: ErrorClassifier::default(),
        }
    }
}
```

---

## 7. 与微服务集成

### 7.1 HTTP 客户端集成

```rust
// examples/http_client_retry.rs
use reqwest::Client;
use retry_rs::*;

pub struct ResilientHttpClient {
    client: Client,
    retry_executor: RetryExecutor,
}

impl ResilientHttpClient {
    pub fn new(policy: RetryPolicy) -> Self {
        Self {
            client: Client::new(),
            retry_executor: RetryExecutor::new(policy),
        }
    }

    /// 调用下游服务 (自动重试)
    pub async fn post_json<T: serde::Serialize>(
        &self,
        url: &str,
        body: &T,
    ) -> Result<String, RetryError> {
        let url = url.to_string();
        let body_json = serde_json::to_string(body).unwrap();

        self.retry_executor
            .execute(|| {
                let url = url.clone();
                let body = body_json.clone();
                let client = self.client.clone();

                Box::pin(async move {
                    client
                        .post(&url)
                        .header("Content-Type", "application/json")
                        .body(body)
                        .send()
                        .await?
                        .text()
                        .await
                })
            })
            .await
    }
}

#[tokio::main]
async fn main() {
    let policy = RetryPolicyRegistry::for_external_api();
    let client = ResilientHttpClient::new(policy);

    match client.post_json("http://api.example.com/orders", &order_data).await {
        Ok(response) => println!("✅ Order created: {}", response),
        Err(e) => println!("❌ Failed after retries: {:?}", e),
    }
}
```

---

## 8. 部署与监控

### 8.1 Prometheus Metrics

```rust
// src/telemetry/metrics.rs
use metrics::{counter, histogram};

/// 记录重试次数
pub fn record_retry_attempt(service: &str, attempt: usize) {
    counter!("retry_attempts_total", "service" => service.to_string(), "attempt" => attempt.to_string()).increment(1);
}

/// 记录重试成功
pub fn record_retry_success(service: &str, final_attempt: usize) {
    counter!("retry_success_total", "service" => service.to_string()).increment(1);
    histogram!("retry_final_attempt", "service" => service.to_string()).record(final_attempt as f64);
}

/// 记录重试失败
pub fn record_retry_failure(service: &str, reason: &str) {
    counter!("retry_failure_total", "service" => service.to_string(), "reason" => reason.to_string()).increment(1);
}

/// 记录退避延迟
pub fn record_backoff_delay(service: &str, delay_ms: u64) {
    histogram!("retry_backoff_delay_ms", "service" => service.to_string()).record(delay_ms as f64);
}
```

---

## 9. 最佳实践与陷阱

### 9.1 最佳实践

```rust
/// ✅ DO: 重试模式最佳实践

// 1. 使用指数退避 + 抖动 (避免惊群效应)
// ✅ 正确
pub fn create_backoff() -> BackoffStrategy {
    BackoffStrategy::ExponentialWithJitter {
        initial_delay: Duration::from_millis(100),
        multiplier: 2.0,
        max_delay: Duration::from_secs(30),
        jitter_factor: 0.2, // 加入抖动
    }
}

// ❌ 错误: 固定延迟
pub fn bad_backoff() -> BackoffStrategy {
    BackoffStrategy::Fixed {
        delay: Duration::from_millis(100), // 所有客户端同时重试!
    }
}


// 2. 只重试暂时性故障,不重试永久性故障
// ✅ 正确: 分类错误
impl Classify for MyError {
    fn classify(&self) -> ErrorClassification {
        match self {
            MyError::NetworkTimeout => ErrorClassification::Transient,
            MyError::NotFound => ErrorClassification::Permanent,
            MyError::Unauthorized => ErrorClassification::Permanent,
            MyError::ServiceUnavailable => ErrorClassification::Transient,
        }
    }
}


// 3. 设置合理的最大重试次数和总超时
// ✅ 正确
pub fn reasonable_policy() -> RetryPolicy {
    RetryPolicy {
        max_attempts: 3,                          // 不要过多
        total_timeout: Some(Duration::from_secs(10)), // 避免无限等待
        ..Default::default()
    }
}

// ❌ 错误: 过多重试
pub fn aggressive_policy() -> RetryPolicy {
    RetryPolicy {
        max_attempts: 100,       // 太多!
        total_timeout: None,     // 无限等待!
        ..Default::default()
    }
}


// 4. 确保操作幂等性
// ✅ 正确: 使用幂等键
pub async fn create_order(&self, order: OrderData) -> Result<Order> {
    let request = IdempotentRequest::new(order);
    // 带幂等键的请求可以安全重试
}


// 5. 记录重试指标
// ✅ 正确: 监控重试行为
pub async fn execute_with_metrics<F, T>(&self, operation: F) -> Result<T>
where
    F: FnMut() -> std::future::Future<Output = Result<T>>,
{
    for attempt in 0..self.max_attempts {
        metrics::record_retry_attempt("my_service", attempt);
        
        match operation().await {
            Ok(value) => {
                metrics::record_retry_success("my_service", attempt + 1);
                return Ok(value);
            }
            Err(e) => { /* 重试... */ }
        }
    }
    
    metrics::record_retry_failure("my_service", "max_attempts_exceeded");
    Err(Error::MaxRetriesExceeded)
}
```

### 9.2 常见陷阱

```rust
/// ❌ ANTI-PATTERNS: 常见错误

// ❌ 陷阱 1: 重试非幂等操作
// 问题: 可能导致重复扣款、重复创建订单等
// ❌ 错误: 直接重试 POST 请求
pub async fn create_payment_bad(&self, amount: f64) -> Result<PaymentId> {
    retry_executor.execute(|| async {
        self.payment_service.charge(amount).await // 可能重复扣款!
    }).await
}

// ✅ 正确: 使用幂等键
pub async fn create_payment(&self, amount: f64) -> Result<PaymentId> {
    let idempotency_key = Uuid::new_v4().to_string();
    
    retry_executor.execute(|| async {
        self.payment_service
            .charge_idempotent(amount, &idempotency_key)
            .await
    }).await
}


// ❌ 陷阱 2: 重试导致雪崩效应
// 问题: 服务已过载,大量重试加剧过载
// ❌ 错误: 无条件重试
pub async fn call_overloaded_service(&self) -> Result<String> {
    retry_executor.execute(|| async {
        self.client.call().await // 服务过载,重试只会更糟!
    }).await
}

// ✅ 正确: 配合熔断器使用
pub async fn call_with_circuit_breaker(&self) -> Result<String> {
    // 先检查熔断器
    if self.circuit_breaker.is_open() {
        return Err(Error::ServiceUnavailable);
    }

    // 熔断器未打开,才重试
    retry_executor.execute(|| async {
        self.client.call().await
    }).await
}


// ❌ 陷阱 3: 忘记设置总超时
// 问题: 重试可能导致请求挂起很长时间
// ❌ 错误: 无总超时限制
pub fn no_timeout_policy() -> RetryPolicy {
    RetryPolicy {
        max_attempts: 10,
        total_timeout: None, // 可能等待几分钟!
        ..Default::default()
    }
}

// ✅ 正确: 设置合理的总超时
pub fn with_timeout_policy() -> RetryPolicy {
    RetryPolicy {
        max_attempts: 10,
        total_timeout: Some(Duration::from_secs(30)), // 最多等待30秒
        ..Default::default()
    }
}


// ❌ 陷阱 4: 重试逻辑中有状态
// 问题: 闭包捕获可变状态,重试后状态不一致
// ❌ 错误: 闭包中修改外部状态
pub async fn bad_retry(&self) -> Result<String> {
    let mut counter = 0; // 外部状态

    retry_executor.execute(|| async {
        counter += 1; // 每次重试都会增加!
        self.fetch_data(counter).await
    }).await
}

// ✅ 正确: 无状态的操作
pub async fn good_retry(&self) -> Result<String> {
    retry_executor.execute(|| async {
        self.fetch_data().await // 纯函数,无副作用
    }).await
}


// ❌ 陷阱 5: 对下游所有错误都重试
// 问题: 404、401 等永久性错误不应重试
// ❌ 错误: 不分类错误
pub async fn retry_all_errors(&self) -> Result<User> {
    retry_executor.execute(|| async {
        self.user_service.get_user(user_id).await
        // 404 Not Found 也会重试 3 次!
    }).await
}

// ✅ 正确: 分类错误,只重试暂时性故障
impl Classify for UserServiceError {
    fn classify(&self) -> ErrorClassification {
        match self.status_code {
            404 | 401 | 403 => ErrorClassification::Permanent,
            500 | 502 | 503 | 504 => ErrorClassification::Transient,
            _ => ErrorClassification::Transient,
        }
    }
}
```

---

## 10. 与其他模式组合

### 10.1 重试 + 熔断器

```rust
// 组合使用: 先检查熔断器,再重试
pub struct ResilientClient {
    circuit_breaker: SharedCircuitBreaker,
    retry_executor: RetryExecutor,
}

impl ResilientClient {
    pub async fn call(&self, url: &str) -> Result<String, AppError> {
        // 先检查熔断器
        {
            let cb = self.circuit_breaker.read().await;
            if cb.state() == CircuitBreakerState::Open {
                return Err(AppError::CircuitBreakerOpen);
            }
        }

        // 熔断器未打开,执行重试逻辑
        self.retry_executor
            .execute(|| Box::pin(self.http_get(url)))
            .await
            .map_err(Into::into)
    }
}
```

### 10.2 重试 + 超时

```rust
// 组合使用: 单次请求超时 + 总体重试超时
pub async fn call_with_timeout_and_retry(&self) -> Result<String> {
    let retry_policy = RetryPolicy {
        max_attempts: 3,
        total_timeout: Some(Duration::from_secs(10)), // 总超时
        backoff: BackoffStrategy::default(),
        error_classifier: ErrorClassifier::default(),
    };

    let executor = RetryExecutor::new(retry_policy);

    executor
        .execute(|| {
            Box::pin(async {
                // 单次请求超时 3 秒
                tokio::time::timeout(Duration::from_secs(3), self.client.call()).await?
            })
        })
        .await
}
```

---

## 📚 参考资料

### 国际标准与最佳实践

1. **AWS - Exponential Backoff And Jitter**
   - <https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/>
   - AWS 推荐的退避算法

2. **Google Cloud - Retry Strategy**
   - <https://cloud.google.com/architecture/best-practices-for-cloud-interconnect-latency>
   - Google Cloud 重试最佳实践

3. **Microsoft Azure - Retry guidance**
   - <https://learn.microsoft.com/en-us/azure/architecture/best-practices/retry-service-specific>
   - Azure 重试指南

---

## ✅ 总结

### 重试模式核心价值

1. **提高可用性**: 自动处理暂时性故障
2. **改善用户体验**: 无需用户手动重试
3. **弹性架构**: 增强系统容错能力

### 关键设计原则

1. **指数退避 + 抖动**: 避免惊群效应
2. **错误分类**: 只重试暂时性故障
3. **幂等性**: 确保操作可安全重试
4. **合理限制**: 最大重试次数 + 总超时

---

**文档状态**: ✅ 生产就绪  
**最后更新**: 2025-10-11  
**维护者**: OTLP Rust Team
