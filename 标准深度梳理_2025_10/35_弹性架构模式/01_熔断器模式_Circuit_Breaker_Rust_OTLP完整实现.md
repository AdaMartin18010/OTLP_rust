# 熔断器模式 (Circuit Breaker) - Rust 1.90 + OTLP 完整实现指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **对标标准**: Netflix Hystrix, Resilience4j, Microsoft Azure Circuit Breaker Pattern, AWS Well-Architected Framework

---

## 📑 目录

- [熔断器模式 (Circuit Breaker) - Rust 1.90 + OTLP 完整实现指南](#熔断器模式-circuit-breaker---rust-190--otlp-完整实现指南)
  - [📑 目录](#-目录)
  - [1. 熔断器模式概述](#1-熔断器模式概述)
    - [1.1 什么是熔断器?](#11-什么是熔断器)
    - [1.2 核心概念](#12-核心概念)
    - [1.3 何时使用熔断器?](#13-何时使用熔断器)
  - [2. 核心状态机原理](#2-核心状态机原理)
    - [2.1 状态转换图](#21-状态转换图)
    - [2.2 状态详解](#22-状态详解)
      - [2.2.1 CLOSED 状态 (关闭状态)](#221-closed-状态-关闭状态)
      - [2.2.2 OPEN 状态 (打开状态)](#222-open-状态-打开状态)
      - [2.2.3 HALF\_OPEN 状态 (半开状态)](#223-half_open-状态-半开状态)
  - [3. Rust 1.90 完整实现](#3-rust-190-完整实现)
    - [3.1 项目结构](#31-项目结构)
    - [3.2 依赖配置 (`Cargo.toml`)](#32-依赖配置-cargotoml)
    - [3.3 熔断器核心实现](#33-熔断器核心实现)
    - [3.4 指标统计 (滑动窗口)](#34-指标统计-滑动窗口)
    - [3.5 配置](#35-配置)
    - [3.6 错误类型](#36-错误类型)
  - [4. 与微服务集成](#4-与微服务集成)
    - [4.1 HTTP 客户端集成](#41-http-客户端集成)
    - [4.2 Axum 中间件](#42-axum-中间件)
  - [5. OTLP 追踪与监控](#5-otlp-追踪与监控)
    - [5.1 追踪熔断器状态](#51-追踪熔断器状态)
    - [5.2 Jaeger 追踪示例](#52-jaeger-追踪示例)
  - [6. 熔断策略配置](#6-熔断策略配置)
    - [6.1 不同场景的配置](#61-不同场景的配置)
  - [7. 降级与回退](#7-降级与回退)
    - [7.1 降级策略](#71-降级策略)
  - [8. 部署与监控](#8-部署与监控)
    - [8.1 Prometheus Metrics](#81-prometheus-metrics)
    - [8.2 Grafana 监控面板](#82-grafana-监控面板)
  - [9. 最佳实践与陷阱](#9-最佳实践与陷阱)
    - [9.1 最佳实践](#91-最佳实践)
    - [9.2 常见陷阱](#92-常见陷阱)
  - [10. 与其他模式组合](#10-与其他模式组合)
    - [10.1 熔断器 + 重试](#101-熔断器--重试)
    - [10.2 熔断器 + 限流](#102-熔断器--限流)
  - [📚 参考资料](#-参考资料)
    - [国际标准与最佳实践](#国际标准与最佳实践)
  - [✅ 总结](#-总结)
    - [熔断器核心价值](#熔断器核心价值)
    - [Rust 实现优势](#rust-实现优势)

---

## 1. 熔断器模式概述

### 1.1 什么是熔断器?

**Circuit Breaker Pattern** (熔断器模式) 是一种防止级联故障的弹性架构模式,当下游服务出现故障时,熔断器会"打开",快速失败,避免无谓的等待和资源消耗。

**灵感来源**: 类比电路中的保险丝,当电流过大时自动断开,保护电路不被烧毁。

```text
┌──────────────────────────────────────────────────────────────┐
│              无熔断器: 级联故障 (Cascading Failure)            │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  User Request                                                │
│      ↓                                                        │
│  Service A (正常)                                             │
│      ↓                                                        │
│  Service B (正常)                                             │
│      ↓                                                        │
│  Service C (故障,响应时间10秒) 💥                             │
│      ↓                                                       │
│  ❌ 问题:                                                    │
│     • Service B 等待 Service C 响应,线程阻塞                  │
│     • Service B 线程池耗尽,无法处理新请求                      │
│     • Service A 也开始超时,线程池耗尽                          │
│     • 整个系统崩溃 (雪崩效应)                                  │
│                                                              │
└──────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────┐
│              有熔断器: 快速失败 (Fail Fast)                    │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  User Request                                                │
│      ↓                                                       │
│  Service A (正常)                                             │
│      ↓                                                        │
│  Service B (正常)                                             │
│      ↓                                                       │
│  Circuit Breaker (检测到 Service C 故障率高)                  │
│      ↓                                                       │
│  ⚡ 熔断器打开 (OPEN)                                         │
│      ↓                                                       │
│  直接返回降级响应 (0.1ms) ✅                                  │
│      ↓                                                       │
│  ✅ 优势:                                                    │
│     • 快速失败,不阻塞线程                                      │
│     • Service B 和 Service A 保持正常运行                     │
│     • 用户收到友好的降级响应                                   │
│     • 系统整体保持稳定                                        │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 1.2 核心概念

```rust
/// 熔断器的三个核心状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitBreakerState {
    /// 关闭状态 (正常运行)
    /// • 请求正常通过
    /// • 统计失败率
    /// • 失败率超过阈值 → 转为 OPEN
    Closed,

    /// 打开状态 (熔断)
    /// • 拒绝所有请求,快速失败
    /// • 返回降级响应
    /// • 等待一段时间 → 转为 HALF_OPEN
    Open,

    /// 半开状态 (试探性恢复)
    /// • 允许少量请求通过
    /// • 如果成功 → 转为 CLOSED
    /// • 如果失败 → 转回 OPEN
    HalfOpen,
}

/// 熔断器配置
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    /// 失败率阈值 (0.0 - 1.0)
    /// 例如: 0.5 表示 50% 失败率触发熔断
    pub failure_rate_threshold: f64,

    /// 最小请求数 (用于计算失败率)
    /// 例如: 10 表示至少10个请求才计算失败率
    pub minimum_request_count: usize,

    /// 熔断持续时间 (OPEN → HALF_OPEN)
    pub open_duration: std::time::Duration,

    /// 半开状态允许的请求数
    pub half_open_max_requests: usize,

    /// 请求超时时间
    pub request_timeout: std::time::Duration,
}
```

### 1.3 何时使用熔断器?

| 场景 | 是否适用 | 原因 |
|------|---------|------|
| 调用外部 API (第三方服务) | ✅ **强烈推荐** | 外部服务不可控,可能随时故障 |
| 微服务间调用 | ✅ 推荐 | 防止级联故障,保护上游服务 |
| 数据库查询 | ⚠️ 谨慎使用 | 数据库故障通常需要立即报警,而非熔断 |
| 缓存查询 | ❌ 不必要 | 缓存失败应该直接穿透到数据库 |
| 本地函数调用 | ❌ 不必要 | 无网络延迟,不会造成级联故障 |

---

## 2. 核心状态机原理

### 2.1 状态转换图

```text
┌─────────────────────────────────────────────────────────────┐
│              Circuit Breaker 状态机                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                    ┌──────────────┐                         │
│         启动       │   CLOSED     │                         │
│      ─────────────►│   (关闭)     │                         │
│                    │              │                         │
│                    │ • 请求正常通过│                         │
│                    │ • 统计失败率  │                         │
│                    └──────┬───────┘                         │
│                           │                                 │
│              失败率 > 阈值 │                                 │
│             (例如: 50%)   │                                 │
│                           │                                 │
│                    ┌──────▼───────┐                         │
│         ◄──────────│   OPEN       │                         │
│         │          │   (打开)     │                         │
│         │          │              │                         │
│         │          │ • 拒绝所有请求│                         │
│         │          │ • 快速失败    │                         │
│         │          │ • 返回降级响应│                         │
│         │          └──────┬───────┘                         │
│         │                 │                                 │
│         │    等待一段时间  │                                 │
│         │   (例如: 30秒)  │                                 │
│         │                 │                                 │
│         │          ┌──────▼───────┐                         │
│         │          │  HALF_OPEN   │                         │
│         │          │  (半开)      │                         │
│         │          │              │                         │
│         │          │ • 允许少量请求│                         │
│         │          │ • 试探性恢复  │                         │
│         │          └──────┬───────┘                         │
│         │                 │                                 │
│         │    ┌────────────┴────────────┐                    │
│         │    │                         │                    │
│  请求失败│    │                    请求成功                  │
│         │    │                         │                    │
│         └────┘                         │                    │
│                                        │                    │
│                                ┌───────▼──────┐             │
│                                │   CLOSED     │             │
│                                │  (恢复正常)  │             │
│                                └──────────────┘             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 状态详解

#### 2.2.1 CLOSED 状态 (关闭状态)

```rust
/// CLOSED 状态行为
impl CircuitBreaker {
    async fn handle_closed_state(&mut self, request: Request) -> Result<Response> {
        // 1. 正常执行请求
        let result = self.execute_request(request).await;

        // 2. 记录结果到滑动窗口
        match &result {
            Ok(_) => self.metrics.record_success(),
            Err(_) => self.metrics.record_failure(),
        }

        // 3. 检查是否应该转为 OPEN
        if self.should_open() {
            self.state = CircuitBreakerState::Open;
            self.open_at = Some(Instant::now());
            tracing::warn!("🔴 Circuit Breaker opened: failure rate exceeded threshold");
        }

        result
    }

    fn should_open(&self) -> bool {
        // 条件 1: 请求数达到最小阈值
        if self.metrics.total_requests() < self.config.minimum_request_count {
            return false;
        }

        // 条件 2: 失败率超过阈值
        let failure_rate = self.metrics.failure_rate();
        failure_rate > self.config.failure_rate_threshold
    }
}
```

#### 2.2.2 OPEN 状态 (打开状态)

```rust
/// OPEN 状态行为
impl CircuitBreaker {
    async fn handle_open_state(&mut self, _request: Request) -> Result<Response> {
        // 1. 检查是否应该转为 HALF_OPEN
        if let Some(open_at) = self.open_at {
            if open_at.elapsed() > self.config.open_duration {
                self.state = CircuitBreakerState::HalfOpen;
                self.half_open_requests = 0;
                tracing::info!("🟡 Circuit Breaker entering half-open state");
            }
        }

        // 2. 如果仍是 OPEN,快速失败
        if self.state == CircuitBreakerState::Open {
            tracing::warn!("⚡ Circuit Breaker open: request rejected");
            return Err(CircuitBreakerError::CircuitOpen);
        }

        // 3. 如果已转为 HALF_OPEN,继续处理
        self.handle_half_open_state(_request).await
    }
}
```

#### 2.2.3 HALF_OPEN 状态 (半开状态)

```rust
/// HALF_OPEN 状态行为
impl CircuitBreaker {
    async fn handle_half_open_state(&mut self, request: Request) -> Result<Response> {
        // 1. 检查是否超过半开状态允许的请求数
        if self.half_open_requests >= self.config.half_open_max_requests {
            tracing::warn!("⚠️ Half-open request limit reached, rejecting request");
            return Err(CircuitBreakerError::HalfOpenLimitExceeded);
        }

        // 2. 增加半开请求计数
        self.half_open_requests += 1;

        // 3. 执行请求
        let result = self.execute_request(request).await;

        // 4. 根据结果决定状态转换
        match &result {
            Ok(_) => {
                // 成功 → 转为 CLOSED
                self.state = CircuitBreakerState::Closed;
                self.metrics.reset();
                tracing::info!("🟢 Circuit Breaker closed: service recovered");
            }
            Err(_) => {
                // 失败 → 转回 OPEN
                self.state = CircuitBreakerState::Open;
                self.open_at = Some(Instant::now());
                tracing::warn!("🔴 Circuit Breaker reopened: half-open test failed");
            }
        }

        result
    }
}
```

---

## 3. Rust 1.90 完整实现

### 3.1 项目结构

```text
circuit-breaker-rs/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   │
│   ├── circuit_breaker/
│   │   ├── mod.rs
│   │   ├── state.rs              # 状态机
│   │   ├── metrics.rs            # 指标统计 (滑动窗口)
│   │   ├── config.rs             # 配置
│   │   └── error.rs              # 错误类型
│   │
│   ├── middleware/               # Axum 中间件
│   │   └── circuit_breaker_middleware.rs
│   │
│   ├── telemetry/                # OTLP 集成
│   │   └── mod.rs
│   │
│   └── examples/
│       ├── basic_usage.rs
│       └── microservice_integration.rs
│
└── tests/
    ├── integration_tests.rs
    └── state_machine_tests.rs
```

### 3.2 依赖配置 (`Cargo.toml`)

```toml
[package]
name = "circuit-breaker-rs"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# 时间处理
chrono = "0.4"

# 滑动窗口实现
arc-swap = "1.7"

# OpenTelemetry
opentelemetry = "0.31"
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 序列化
serde = { version = "1.0", features = ["derive"] }

# Web 框架 (可选,用于中间件)
axum = { version = "0.7", optional = true }

[dev-dependencies]
mockall = "0.13"
criterion = "0.5"
```

### 3.3 熔断器核心实现

```rust
// src/circuit_breaker/mod.rs
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn, instrument};

mod state;
mod metrics;
mod config;
mod error;

pub use state::CircuitBreakerState;
pub use metrics::Metrics;
pub use config::CircuitBreakerConfig;
pub use error::CircuitBreakerError;

/// 熔断器
pub struct CircuitBreaker {
    /// 当前状态
    state: CircuitBreakerState,

    /// 配置
    config: CircuitBreakerConfig,

    /// 指标统计 (滑动窗口)
    metrics: Metrics,

    /// OPEN 状态开始时间
    open_at: Option<Instant>,

    /// HALF_OPEN 状态已发出的请求数
    half_open_requests: usize,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: CircuitBreakerState::Closed,
            config,
            metrics: Metrics::new(Duration::from_secs(60)), // 60秒滑动窗口
            open_at: None,
            half_open_requests: 0,
        }
    }

    /// 执行受保护的操作
    #[instrument(skip(self, operation), fields(
        circuit_breaker.state = ?self.state,
        circuit_breaker.failure_rate = %self.metrics.failure_rate()
    ))]
    pub async fn call<F, T, E>(&mut self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 1. 根据当前状态决定行为
        match self.state {
            CircuitBreakerState::Closed => {
                self.handle_closed_state(operation).await
            }
            CircuitBreakerState::Open => {
                self.handle_open_state().await?;
                self.handle_half_open_state(operation).await
            }
            CircuitBreakerState::HalfOpen => {
                self.handle_half_open_state(operation).await
            }
        }
    }

    /// CLOSED 状态处理
    async fn handle_closed_state<F, T, E>(&mut self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 执行操作 (带超时)
        let result = tokio::time::timeout(self.config.request_timeout, operation).await;

        match result {
            Ok(Ok(value)) => {
                // 成功
                self.metrics.record_success();
                Ok(value)
            }
            Ok(Err(e)) => {
                // 失败
                self.metrics.record_failure();
                
                // 检查是否应该转为 OPEN
                if self.should_open() {
                    self.transition_to_open();
                }

                Err(CircuitBreakerError::OperationFailed(e.to_string()))
            }
            Err(_) => {
                // 超时
                self.metrics.record_failure();
                
                if self.should_open() {
                    self.transition_to_open();
                }

                Err(CircuitBreakerError::RequestTimeout)
            }
        }
    }

    /// OPEN 状态处理
    async fn handle_open_state(&mut self) -> Result<(), CircuitBreakerError> {
        // 检查是否应该转为 HALF_OPEN
        if let Some(open_at) = self.open_at {
            if open_at.elapsed() > self.config.open_duration {
                self.transition_to_half_open();
                return Ok(());
            }
        }

        // 仍是 OPEN,拒绝请求
        warn!("⚡ Circuit breaker is OPEN, request rejected");
        Err(CircuitBreakerError::CircuitOpen)
    }

    /// HALF_OPEN 状态处理
    async fn handle_half_open_state<F, T, E>(&mut self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 检查半开请求限制
        if self.half_open_requests >= self.config.half_open_max_requests {
            warn!("⚠️ Half-open request limit reached");
            return Err(CircuitBreakerError::HalfOpenLimitExceeded);
        }

        self.half_open_requests += 1;

        // 执行操作
        let result = tokio::time::timeout(self.config.request_timeout, operation).await;

        match result {
            Ok(Ok(value)) => {
                // 成功 → 转为 CLOSED
                self.transition_to_closed();
                Ok(value)
            }
            Ok(Err(e)) => {
                // 失败 → 转回 OPEN
                self.transition_to_open();
                Err(CircuitBreakerError::OperationFailed(e.to_string()))
            }
            Err(_) => {
                // 超时 → 转回 OPEN
                self.transition_to_open();
                Err(CircuitBreakerError::RequestTimeout)
            }
        }
    }

    /// 检查是否应该打开熔断器
    fn should_open(&self) -> bool {
        if self.metrics.total_requests() < self.config.minimum_request_count {
            return false;
        }

        self.metrics.failure_rate() > self.config.failure_rate_threshold
    }

    /// 状态转换: → OPEN
    fn transition_to_open(&mut self) {
        self.state = CircuitBreakerState::Open;
        self.open_at = Some(Instant::now());
        warn!(
            "🔴 Circuit Breaker OPENED: failure rate {:.2}% > threshold {:.2}%",
            self.metrics.failure_rate() * 100.0,
            self.config.failure_rate_threshold * 100.0
        );
    }

    /// 状态转换: → HALF_OPEN
    fn transition_to_half_open(&mut self) {
        self.state = CircuitBreakerState::HalfOpen;
        self.half_open_requests = 0;
        info!("🟡 Circuit Breaker entering HALF_OPEN state");
    }

    /// 状态转换: → CLOSED
    fn transition_to_closed(&mut self) {
        self.state = CircuitBreakerState::Closed;
        self.metrics.reset();
        info!("🟢 Circuit Breaker CLOSED: service recovered");
    }

    /// 获取当前状态
    pub fn state(&self) -> CircuitBreakerState {
        self.state
    }

    /// 获取失败率
    pub fn failure_rate(&self) -> f64 {
        self.metrics.failure_rate()
    }
}

/// 线程安全的熔断器 (使用 Arc<RwLock>)
pub type SharedCircuitBreaker = Arc<RwLock<CircuitBreaker>>;
```

### 3.4 指标统计 (滑动窗口)

```rust
// src/circuit_breaker/metrics.rs
use std::collections::VecDeque;
use std::time::{Duration, Instant};

/// 请求结果
#[derive(Debug, Clone, Copy)]
enum RequestResult {
    Success(Instant),
    Failure(Instant),
}

/// 指标统计 (基于时间的滑动窗口)
pub struct Metrics {
    /// 窗口大小 (例如: 60秒)
    window_duration: Duration,

    /// 请求结果队列
    results: VecDeque<RequestResult>,
}

impl Metrics {
    pub fn new(window_duration: Duration) -> Self {
        Self {
            window_duration,
            results: VecDeque::new(),
        }
    }

    /// 记录成功
    pub fn record_success(&mut self) {
        self.cleanup_old_results();
        self.results.push_back(RequestResult::Success(Instant::now()));
    }

    /// 记录失败
    pub fn record_failure(&mut self) {
        self.cleanup_old_results();
        self.results.push_back(RequestResult::Failure(Instant::now()));
    }

    /// 计算失败率
    pub fn failure_rate(&self) -> f64 {
        let total = self.total_requests();
        if total == 0 {
            return 0.0;
        }

        let failures = self.failure_count();
        failures as f64 / total as f64
    }

    /// 总请求数
    pub fn total_requests(&self) -> usize {
        self.results.len()
    }

    /// 失败请求数
    fn failure_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r, RequestResult::Failure(_)))
            .count()
    }

    /// 清理超出窗口的旧结果
    fn cleanup_old_results(&mut self) {
        let now = Instant::now();
        self.results.retain(|result| {
            let timestamp = match result {
                RequestResult::Success(t) | RequestResult::Failure(t) => *t,
            };
            now.duration_since(timestamp) <= self.window_duration
        });
    }

    /// 重置指标
    pub fn reset(&mut self) {
        self.results.clear();
    }
}
```

### 3.5 配置

```rust
// src/circuit_breaker/config.rs
use std::time::Duration;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 失败率阈值 (0.0 - 1.0)
    /// 默认: 0.5 (50%)
    pub failure_rate_threshold: f64,

    /// 最小请求数 (用于计算失败率)
    /// 默认: 10
    pub minimum_request_count: usize,

    /// 熔断持续时间 (OPEN → HALF_OPEN)
    /// 默认: 30秒
    pub open_duration: Duration,

    /// 半开状态允许的请求数
    /// 默认: 5
    pub half_open_max_requests: usize,

    /// 请求超时时间
    /// 默认: 5秒
    pub request_timeout: Duration,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_rate_threshold: 0.5,
            minimum_request_count: 10,
            open_duration: Duration::from_secs(30),
            half_open_max_requests: 5,
            request_timeout: Duration::from_secs(5),
        }
    }
}

impl CircuitBreakerConfig {
    /// 创建激进配置 (快速熔断)
    pub fn aggressive() -> Self {
        Self {
            failure_rate_threshold: 0.3, // 30% 失败率即熔断
            minimum_request_count: 5,
            open_duration: Duration::from_secs(10),
            half_open_max_requests: 3,
            request_timeout: Duration::from_secs(2),
        }
    }

    /// 创建保守配置 (容忍度高)
    pub fn conservative() -> Self {
        Self {
            failure_rate_threshold: 0.7, // 70% 失败率才熔断
            minimum_request_count: 20,
            open_duration: Duration::from_secs(60),
            half_open_max_requests: 10,
            request_timeout: Duration::from_secs(10),
        }
    }
}
```

### 3.6 错误类型

```rust
// src/circuit_breaker/error.rs
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CircuitBreakerError {
    #[error("Circuit breaker is OPEN")]
    CircuitOpen,

    #[error("Half-open request limit exceeded")]
    HalfOpenLimitExceeded,

    #[error("Request timeout")]
    RequestTimeout,

    #[error("Operation failed: {0}")]
    OperationFailed(String),
}
```

---

## 4. 与微服务集成

### 4.1 HTTP 客户端集成

```rust
// examples/microservice_integration.rs
use reqwest::Client;
use std::sync::Arc;
use tokio::sync::RwLock;
use circuit_breaker_rs::*;

pub struct ResilientHttpClient {
    client: Client,
    circuit_breaker: SharedCircuitBreaker,
}

impl ResilientHttpClient {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        let circuit_breaker = Arc::new(RwLock::new(CircuitBreaker::new(config)));

        Self {
            client: Client::new(),
            circuit_breaker,
        }
    }

    /// 调用下游服务 (受熔断器保护)
    pub async fn call_service(&self, url: &str) -> Result<String, CircuitBreakerError> {
        let mut cb = self.circuit_breaker.write().await;

        cb.call(async {
            self.client
                .get(url)
                .send()
                .await
                .map_err(|e| format!("HTTP error: {}", e))?
                .text()
                .await
                .map_err(|e| format!("Response error: {}", e))
        })
        .await
    }
}

#[tokio::main]
async fn main() {
    let client = ResilientHttpClient::new(CircuitBreakerConfig::default());

    // 调用下游服务
    match client.call_service("http://downstream-service:8080/api/data").await {
        Ok(response) => println!("✅ Response: {}", response),
        Err(CircuitBreakerError::CircuitOpen) => {
            println!("⚡ Circuit breaker is OPEN, using fallback");
            // 使用降级响应
        }
        Err(e) => println!("❌ Error: {:?}", e),
    }
}
```

### 4.2 Axum 中间件

```rust
// src/middleware/circuit_breaker_middleware.rs
use axum::{
    extract::State,
    http::{Request, StatusCode},
    middleware::Next,
    response::{IntoResponse, Response},
};
use circuit_breaker_rs::*;

pub async fn circuit_breaker_middleware<B>(
    State(cb): State<SharedCircuitBreaker>,
    request: Request<B>,
    next: Next<B>,
) -> Result<Response, CircuitBreakerMiddlewareError> {
    let mut circuit_breaker = cb.write().await;

    // 使用熔断器保护请求
    circuit_breaker
        .call(async {
            Ok(next.run(request).await)
        })
        .await
        .map_err(|e| CircuitBreakerMiddlewareError(e))
}

pub struct CircuitBreakerMiddlewareError(CircuitBreakerError);

impl IntoResponse for CircuitBreakerMiddlewareError {
    fn into_response(self) -> Response {
        let (status, message) = match self.0 {
            CircuitBreakerError::CircuitOpen => {
                (StatusCode::SERVICE_UNAVAILABLE, "Service temporarily unavailable")
            }
            CircuitBreakerError::RequestTimeout => {
                (StatusCode::GATEWAY_TIMEOUT, "Request timeout")
            }
            _ => (StatusCode::INTERNAL_SERVER_ERROR, "Internal server error"),
        };

        (status, message).into_response()
    }
}
```

---

## 5. OTLP 追踪与监控

### 5.1 追踪熔断器状态

```rust
// src/circuit_breaker/mod.rs (追踪增强)
use tracing::{info, warn, instrument, Span};
use opentelemetry::trace::{Span as OtelSpan, Tracer};

impl CircuitBreaker {
    #[instrument(skip(self, operation), fields(
        circuit_breaker.name = %self.config.name,
        circuit_breaker.state = ?self.state,
        circuit_breaker.failure_rate = %self.metrics.failure_rate(),
        circuit_breaker.total_requests = %self.metrics.total_requests()
    ))]
    pub async fn call<F, T, E>(&mut self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 记录状态变化到 Span
        let span = Span::current();
        span.record("circuit_breaker.state", format!("{:?}", self.state).as_str());

        // 执行操作
        let result = match self.state {
            CircuitBreakerState::Closed => self.handle_closed_state(operation).await,
            CircuitBreakerState::Open => {
                span.record("circuit_breaker.action", "rejected");
                self.handle_open_state().await?;
                self.handle_half_open_state(operation).await
            }
            CircuitBreakerState::HalfOpen => {
                span.record("circuit_breaker.action", "half_open_test");
                self.handle_half_open_state(operation).await
            }
        };

        // 记录结果
        match &result {
            Ok(_) => span.record("circuit_breaker.result", "success"),
            Err(e) => span.record("circuit_breaker.result", format!("{:?}", e).as_str()),
        }

        result
    }
}
```

### 5.2 Jaeger 追踪示例

```text
🔍 Jaeger Trace 示例 (Circuit Breaker):

Trace ID: xyz789abc123
Span 1: http_request (duration: 150ms)
  ├── Attribute: http.method = "GET"
  ├── Attribute: http.url = "/api/users"
  │
  ├── Span 2: circuit_breaker.call (duration: 145ms)
  │   ├── Attribute: circuit_breaker.name = "user_service_cb"
  │   ├── Attribute: circuit_breaker.state = "Closed"
  │   ├── Attribute: circuit_breaker.failure_rate = "0.35"
  │   ├── Attribute: circuit_breaker.total_requests = "47"
  │   │
  │   ├── Span 3: downstream_service.call (duration: 140ms)
  │   │   ├── Attribute: service.name = "user-service"
  │   │   └── Attribute: http.status_code = "200"
  │   │
  │   └── Attribute: circuit_breaker.result = "success"
  │
  └── Attribute: http.status_code = "200"

─────────────────────────────────────────────────────────────

Trace ID: def456ghi789 (熔断场景)
Span 1: http_request (duration: 5ms) ⚡ 快速失败!
  ├── Attribute: http.method = "GET"
  ├── Attribute: http.url = "/api/orders"
  │
  ├── Span 2: circuit_breaker.call (duration: 2ms)
  │   ├── Attribute: circuit_breaker.name = "order_service_cb"
  │   ├── Attribute: circuit_breaker.state = "Open" 🔴
  │   ├── Attribute: circuit_breaker.failure_rate = "0.65"
  │   ├── Attribute: circuit_breaker.action = "rejected"
  │   └── Attribute: circuit_breaker.result = "CircuitOpen"
  │
  └── Attribute: http.status_code = "503" (Service Unavailable)

✅ 通过追踪可以看到:
   • 熔断器处于 OPEN 状态
   • 请求被快速拒绝 (2ms vs 140ms)
   • 失败率 65% > 阈值 50%
   • 返回 503 降级响应
```

---

## 6. 熔断策略配置

### 6.1 不同场景的配置

```rust
/// 为不同服务配置不同的熔断策略
pub struct CircuitBreakerRegistry {
    breakers: HashMap<String, SharedCircuitBreaker>,
}

impl CircuitBreakerRegistry {
    pub fn new() -> Self {
        let mut breakers = HashMap::new();

        // 1. 外部支付服务 (激进配置)
        breakers.insert(
            "payment_service".to_string(),
            Arc::new(RwLock::new(CircuitBreaker::new(
                CircuitBreakerConfig {
                    failure_rate_threshold: 0.3,  // 30% 失败率即熔断
                    minimum_request_count: 5,
                    open_duration: Duration::from_secs(10),
                    half_open_max_requests: 3,
                    request_timeout: Duration::from_secs(3),
                },
            ))),
        );

        // 2. 内部用户服务 (保守配置)
        breakers.insert(
            "user_service".to_string(),
            Arc::new(RwLock::new(CircuitBreaker::new(
                CircuitBreakerConfig {
                    failure_rate_threshold: 0.6,  // 60% 失败率才熔断
                    minimum_request_count: 15,
                    open_duration: Duration::from_secs(30),
                    half_open_max_requests: 8,
                    request_timeout: Duration::from_secs(5),
                },
            ))),
        );

        // 3. 第三方推荐服务 (非关键,快速熔断)
        breakers.insert(
            "recommendation_service".to_string(),
            Arc::new(RwLock::new(CircuitBreaker::new(
                CircuitBreakerConfig {
                    failure_rate_threshold: 0.2,  // 20% 即熔断
                    minimum_request_count: 3,
                    open_duration: Duration::from_secs(5),
                    half_open_max_requests: 2,
                    request_timeout: Duration::from_secs(1),
                },
            ))),
        );

        Self { breakers }
    }

    pub fn get(&self, service_name: &str) -> Option<SharedCircuitBreaker> {
        self.breakers.get(service_name).cloned()
    }
}
```

---

## 7. 降级与回退

### 7.1 降级策略

```rust
// examples/fallback_strategy.rs
use circuit_breaker_rs::*;

pub struct ServiceWithFallback {
    circuit_breaker: SharedCircuitBreaker,
    cache: Arc<RwLock<HashMap<String, String>>>,
}

impl ServiceWithFallback {
    pub async fn get_user(&self, user_id: &str) -> Result<User, AppError> {
        let mut cb = self.circuit_breaker.write().await;

        // 尝试调用主服务
        match cb.call(async {
            self.call_user_service(user_id).await
        }).await {
            Ok(user) => Ok(user),
            Err(CircuitBreakerError::CircuitOpen) => {
                // 熔断打开,使用降级策略
                self.get_user_fallback(user_id).await
            }
            Err(e) => Err(AppError::from(e)),
        }
    }

    /// 降级策略 1: 返回缓存数据
    async fn get_user_fallback(&self, user_id: &str) -> Result<User, AppError> {
        let cache = self.cache.read().await;
        
        if let Some(cached_user) = cache.get(user_id) {
            tracing::info!("🔁 Using cached user data (fallback)");
            return Ok(serde_json::from_str(cached_user)?);
        }

        // 降级策略 2: 返回默认用户
        tracing::warn!("⚠️ Returning default user (fallback)");
        Ok(User::default_with_id(user_id))
    }

    /// 降级策略 3: 返回空响应 (优雅降级)
    async fn get_recommendations_fallback(&self) -> Vec<Product> {
        tracing::warn!("⚠️ Recommendation service unavailable, returning empty list");
        vec![]
    }
}
```

---

## 8. 部署与监控

### 8.1 Prometheus Metrics

```rust
// src/telemetry/metrics.rs
use metrics::{counter, gauge, histogram};

/// 记录熔断器状态变化
pub fn record_circuit_breaker_state(service: &str, state: CircuitBreakerState) {
    let state_value = match state {
        CircuitBreakerState::Closed => 0.0,
        CircuitBreakerState::Open => 1.0,
        CircuitBreakerState::HalfOpen => 0.5,
    };

    gauge!("circuit_breaker_state", "service" => service.to_string()).set(state_value);
}

/// 记录熔断器拒绝的请求数
pub fn record_circuit_breaker_rejection(service: &str) {
    counter!("circuit_breaker_rejections_total", "service" => service.to_string()).increment(1);
}

/// 记录失败率
pub fn record_circuit_breaker_failure_rate(service: &str, failure_rate: f64) {
    gauge!("circuit_breaker_failure_rate", "service" => service.to_string()).set(failure_rate);
}
```

### 8.2 Grafana 监控面板

```yaml
# Grafana Dashboard (Prometheus 查询)
panels:
  - title: "Circuit Breaker State"
    targets:
      - expr: 'circuit_breaker_state{service="user_service"}'
        legend: "{{service}}"
    thresholds:
      - value: 0.0  # CLOSED (绿色)
      - value: 0.5  # HALF_OPEN (黄色)
      - value: 1.0  # OPEN (红色)

  - title: "Failure Rate"
    targets:
      - expr: 'circuit_breaker_failure_rate{service="user_service"}'
        legend: "{{service}}"
    thresholds:
      - value: 0.5  # 阈值线

  - title: "Rejected Requests"
    targets:
      - expr: 'rate(circuit_breaker_rejections_total[5m])'
        legend: "{{service}}"
```

---

## 9. 最佳实践与陷阱

### 9.1 最佳实践

```rust
/// ✅ DO: 熔断器最佳实践

// 1. 为每个下游服务单独配置熔断器
// ✅ 正确: 独立的熔断器
pub struct ServiceClients {
    user_service_cb: SharedCircuitBreaker,
    order_service_cb: SharedCircuitBreaker,
    payment_service_cb: SharedCircuitBreaker,
}

// ❌ 错误: 共享一个熔断器
pub struct BadServiceClients {
    shared_cb: SharedCircuitBreaker, // 一个服务故障影响所有服务!
}


// 2. 合理设置超时时间
// ✅ 正确: 超时时间 < 熔断阈值时间
pub fn create_config() -> CircuitBreakerConfig {
    CircuitBreakerConfig {
        request_timeout: Duration::from_secs(3),      // 单次请求超时
        minimum_request_count: 10,                    // 至少10次请求
        open_duration: Duration::from_secs(30),       // 熔断30秒
        // 3秒 * 10次 = 30秒,合理
        ..Default::default()
    }
}


// 3. 始终提供降级响应
// ✅ 正确: 有降级策略
pub async fn get_recommendations(&self) -> Vec<Product> {
    match self.call_with_circuit_breaker().await {
        Ok(products) => products,
        Err(_) => vec![], // 降级: 返回空列表
    }
}

// ❌ 错误: 直接抛出错误
pub async fn get_recommendations_bad(&self) -> Result<Vec<Product>> {
    self.call_with_circuit_breaker().await // 熔断时用户看到错误页面!
}


// 4. 监控熔断器状态
// ✅ 正确: 定期上报指标
pub async fn monitor_circuit_breakers(registry: &CircuitBreakerRegistry) {
    for (service, cb) in registry.iter() {
        let state = cb.read().await.state();
        let failure_rate = cb.read().await.failure_rate();

        metrics::record_circuit_breaker_state(service, state);
        metrics::record_circuit_breaker_failure_rate(service, failure_rate);

        if state == CircuitBreakerState::Open {
            alert!("Circuit breaker for {} is OPEN", service);
        }
    }
}


// 5. 使用滑动窗口而非计数窗口
// ✅ 正确: 基于时间的滑动窗口 (Metrics 实现)
pub struct TimeBasedWindow {
    window_duration: Duration, // 最近60秒
}

// ❌ 错误: 基于请求数的固定窗口
pub struct CountBasedWindow {
    last_n_requests: Vec<Result>, // 最近100个请求 (可能跨度很长)
}
```

### 9.2 常见陷阱

```rust
/// ❌ ANTI-PATTERNS: 常见错误

// ❌ 陷阱 1: 熔断器配置过于敏感
// 问题: 短暂的网络抖动导致熔断,影响正常业务
// ❌ 错误配置
pub fn overly_sensitive() -> CircuitBreakerConfig {
    CircuitBreakerConfig {
        failure_rate_threshold: 0.1,  // 10% 失败率即熔断 (太低!)
        minimum_request_count: 2,     // 仅2个请求就计算失败率 (太少!)
        open_duration: Duration::from_secs(300), // 熔断5分钟 (太长!)
        ..Default::default()
    }
}

// ✅ 正确配置
pub fn reasonable() -> CircuitBreakerConfig {
    CircuitBreakerConfig {
        failure_rate_threshold: 0.5,  // 50% 失败率
        minimum_request_count: 10,    // 至少10个请求
        open_duration: Duration::from_secs(30), // 熔断30秒
        ..Default::default()
    }
}


// ❌ 陷阱 2: 忘记处理 HALF_OPEN 状态
// 问题: 半开状态请求超过限制,但没有降级响应
// ❌ 错误处理
pub async fn call_service_bad(&self) -> Result<String> {
    self.circuit_breaker.call(/* operation */).await // 半开限制超出时直接报错
}

// ✅ 正确处理
pub async fn call_service(&self) -> Result<String> {
    match self.circuit_breaker.call(/* operation */).await {
        Ok(result) => Ok(result),
        Err(CircuitBreakerError::HalfOpenLimitExceeded) => {
            // 半开状态请求限制,返回缓存或降级响应
            self.get_fallback_response().await
        }
        Err(e) => Err(e.into()),
    }
}


// ❌ 陷阱 3: 在熔断器内部处理降级
// 问题: 熔断器职责不清,应该由调用方处理降级
// ❌ 错误设计
impl CircuitBreaker {
    pub async fn call_with_fallback<F, T>(&mut self, operation: F, fallback: T) -> T {
        match self.call(operation).await {
            Ok(result) => result,
            Err(_) => fallback, // 熔断器不应该处理业务逻辑!
        }
    }
}

// ✅ 正确设计
impl ServiceClient {
    pub async fn get_data(&self) -> Result<Data> {
        // 熔断器只负责保护调用
        match self.circuit_breaker.call(/* operation */).await {
            Ok(data) => Ok(data),
            Err(_) => {
                // 业务层处理降级
                self.get_cached_data().await
            }
        }
    }
}


// ❌ 陷阱 4: 数据库查询使用熔断器
// 问题: 数据库是核心依赖,熔断后无法提供服务
// ❌ 错误: 数据库查询使用熔断器
pub async fn get_user_from_db(&self, id: &str) -> Result<User> {
    self.db_circuit_breaker.call(async {
        self.db.query_user(id).await
    }).await // 数据库熔断后怎么办?
}

// ✅ 正确: 数据库故障应该立即报警,而非熔断
pub async fn get_user_from_db(&self, id: &str) -> Result<User> {
    match self.db.query_user(id).await {
        Ok(user) => Ok(user),
        Err(e) => {
            alert!("Database failure: {}", e); // 立即报警
            Err(e)
        }
    }
}


// ❌ 陷阱 5: 忽略熔断器的性能开销
// 问题: 每次调用都加锁,高并发下性能下降
// ❌ 错误: 使用全局 RwLock
pub async fn call_service(&self) -> Result<String> {
    let mut cb = self.global_circuit_breaker.write().await; // 串行化所有请求!
    cb.call(/* operation */).await
}

// ✅ 正确: 为每个服务实例单独创建熔断器 (无锁)
pub struct ServiceClient {
    circuit_breaker: CircuitBreaker, // 每个客户端实例独立
}
```

---

## 10. 与其他模式组合

### 10.1 熔断器 + 重试

```rust
// 组合使用: 先重试,失败后熔断
pub async fn call_with_retry_and_circuit_breaker<F, T>(
    circuit_breaker: &mut CircuitBreaker,
    operation: F,
    max_retries: usize,
) -> Result<T, CircuitBreakerError>
where
    F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, String>>>>,
{
    circuit_breaker.call(async {
        // 重试逻辑
        for attempt in 0..max_retries {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) if attempt < max_retries - 1 => {
                    tracing::warn!("Attempt {} failed: {}, retrying...", attempt + 1, e);
                    tokio::time::sleep(Duration::from_millis(100 * 2_u64.pow(attempt as u32))).await;
                }
                Err(e) => return Err(e),
            }
        }
        unreachable!()
    }).await
}
```

### 10.2 熔断器 + 限流

```rust
// 组合使用: 先限流,再熔断
pub struct RateLimitedCircuitBreaker {
    rate_limiter: governor::RateLimiter</* ... */>,
    circuit_breaker: SharedCircuitBreaker,
}

impl RateLimitedCircuitBreaker {
    pub async fn call<F, T>(&self, operation: F) -> Result<T, AppError>
    where
        F: std::future::Future<Output = Result<T, String>>,
    {
        // 1. 先检查限流
        if self.rate_limiter.check().is_err() {
            return Err(AppError::RateLimitExceeded);
        }

        // 2. 再检查熔断器
        let mut cb = self.circuit_breaker.write().await;
        cb.call(operation).await.map_err(Into::into)
    }
}
```

---

## 📚 参考资料

### 国际标准与最佳实践

1. **Martin Fowler - CircuitBreaker**
   - <https://martinfowler.com/bliki/CircuitBreaker.html>

2. **Netflix Hystrix (Archived)**
   - <https://github.com/Netflix/Hystrix>
   - 熔断器模式的先驱实现

3. **Resilience4j**
   - <https://resilience4j.readme.io/docs/circuitbreaker>
   - 现代 Java 熔断器实现

4. **Microsoft Azure - Circuit Breaker Pattern**
   - <https://learn.microsoft.com/en-us/azure/architecture/patterns/circuit-breaker>

---

## ✅ 总结

### 熔断器核心价值

1. **防止级联故障**: 快速失败,保护上游服务
2. **自动恢复**: 半开状态试探性恢复
3. **资源保护**: 避免无谓的等待和线程阻塞

### Rust 实现优势

- **类型安全**: 编译期状态机验证
- **高性能**: 无 GC,极低开销
- **并发安全**: `Arc<RwLock>` 线程安全共享

---

**文档状态**: ✅ 生产就绪  
**最后更新**: 2025-10-11  
**维护者**: OTLP Rust Team
