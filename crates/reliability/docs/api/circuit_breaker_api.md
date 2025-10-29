# 熔断器完整实现 - API参考文档

**示例文件**: `crates/reliability/examples/circuit_breaker_complete_impl.rs`  
**版本**: 1.0.0  
**Rust版本**: 1.90.0+  
**最后更新**: 2025年10月28日

---

## 📋 目录
- [核心概念](#核心概念)
- [核心类型](#核心类型)
  - [CircuitState](#circuitstate)
  - [CircuitError](#circuiterror)
  - [CircuitBreakerConfig](#circuitbreakerconfig)
- [熔断器](#熔断器)
  - [CircuitBreaker](#circuitbreaker)
  - [CircuitBreakerWithFallback](#circuitbreakerwithfallback)
- [统计系统](#统计系统)
  - [CircuitStats](#circuitstats)
  - [SlidingWindow](#slidingwindow)
- [使用示例](#使用示例)
- [最佳实践](#最佳实践)

---

## 核心概念

### 熔断器模式

熔断器是一种容错模式，用于防止系统cascade failure（级联失败）。

**状态机**:
```
    ┌─────────┐
    │ Closed  │ ──(失败率>阈值)──> ┌─────────┐
    └─────────┘                   │  Open   │
        ▲                         └─────────┘
        │                               │
        │                         (等待超时)
        │                               │
        │                               ▼
        │                         ┌──────────┐
        └──(成功率>阈值)───────────│HalfOpen  │
                                  └──────────┘
```

**状态说明**:
- **Closed**: 正常状态，请求正常通过
- **Open**: 熔断状态，快速失败，不执行操作
- **HalfOpen**: 半开状态，尝试少量请求测试恢复

---

## 核心类型

### `CircuitState`

**定义**:
```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}
```

**功能**: 熔断器的三种状态。

**状态转换条件**:
- `Closed → Open`: 失败率或慢调用率超过阈值
- `Open → HalfOpen`: 等待时间到达后自动转换
- `HalfOpen → Closed`: 测试请求成功率足够高
- `HalfOpen → Open`: 测试请求失败

**特征实现**: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `Display`

---

### `CircuitError`

**定义**:
```rust
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
```

**功能**: 熔断器相关的错误类型。

**错误说明**:
- `CircuitOpen`: 熔断器处于Open状态，请求被拒绝
- `Timeout`: 操作超时
- `OperationFailed`: 操作执行失败
- `MaxRetriesExceeded`: 超过最大重试次数

**特征实现**: `Debug`, `Error`

---

### `CircuitBreakerConfig`

**定义**:
```rust
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    pub failure_threshold_percentage: f64,
    pub minimum_request_threshold: u64,
    pub sliding_window_size: Duration,
    pub wait_duration_in_open_state: Duration,
    pub permitted_requests_in_half_open: u32,
    pub timeout_duration: Duration,
    pub slow_call_duration_threshold: Duration,
    pub slow_call_rate_threshold: f64,
}
```

**功能**: 熔断器配置参数。

**字段说明**:

#### `failure_threshold_percentage`
- **类型**: `f64`
- **范围**: 0.0 - 100.0
- **默认**: 50.0
- **说明**: 失败率阈值百分比，超过此值触发熔断

#### `minimum_request_threshold`
- **类型**: `u64`
- **默认**: 20
- **说明**: 最小请求数，达到此数量后才开始计算失败率

#### `sliding_window_size`
- **类型**: `Duration`
- **默认**: 60秒
- **说明**: 滑动窗口大小，统计此时间段内的请求

#### `wait_duration_in_open_state`
- **类型**: `Duration`
- **默认**: 60秒
- **说明**: 熔断后等待时间，之后转为HalfOpen状态

#### `permitted_requests_in_half_open`
- **类型**: `u32`
- **默认**: 10
- **说明**: HalfOpen状态下允许的测试请求数量

#### `timeout_duration`
- **类型**: `Duration`
- **默认**: 5秒
- **说明**: 操作超时时间

#### `slow_call_duration_threshold`
- **类型**: `Duration`
- **默认**: 1秒
- **说明**: 慢调用判定阈值

#### `slow_call_rate_threshold`
- **类型**: `f64`
- **范围**: 0.0 - 100.0
- **默认**: 50.0
- **说明**: 慢调用率阈值，超过此值触发熔断

**使用示例**:
```rust
let config = CircuitBreakerConfig {
    failure_threshold_percentage: 50.0,
    minimum_request_threshold: 20,
    sliding_window_size: Duration::from_secs(60),
    wait_duration_in_open_state: Duration::from_secs(60),
    permitted_requests_in_half_open: 10,
    timeout_duration: Duration::from_secs(5),
    slow_call_duration_threshold: Duration::from_millis(1000),
    slow_call_rate_threshold: 50.0,
};
```

**配置建议**:

| 场景 | failure_threshold | min_requests | window_size | wait_duration |
|------|-------------------|--------------|-------------|---------------|
| 数据库 | 50-70% | 20-50 | 60-120s | 30-60s |
| HTTP API | 30-50% | 10-30 | 30-60s | 10-30s |
| 微服务 | 40-60% | 15-40 | 60-120s | 30-60s |
| 缓存 | 70-90% | 30-100 | 30-60s | 10-20s |

---

## 熔断器

### `CircuitBreaker`

**定义**:
```rust
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitState>>,
    sliding_window: Arc<SlidingWindow>,
    state_changed_at: Arc<RwLock<Instant>>,
    half_open_semaphore: Arc<Semaphore>,
    state_transitions: Arc<AtomicU64>,
}
```

**功能**: 完整的熔断器实现。

---

#### `CircuitBreaker::new()`

**签名**:
```rust
pub fn new(config: CircuitBreakerConfig) -> Self
```

**功能**: 创建新的熔断器实例。

**参数**:
- `config`: 熔断器配置

**返回值**: CircuitBreaker实例

**使用示例**:
```rust
let config = CircuitBreakerConfig::default();
let circuit_breaker = CircuitBreaker::new(config);
```

---

#### `CircuitBreaker::call()`

**签名**:
```rust
pub async fn call<F, T, E>(&self, operation: F) -> Result<T, CircuitError>
where
    F: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
```

**功能**: 通过熔断器执行操作。

**参数**:
- `operation`: 要执行的异步操作

**返回值**:
- `Ok(T)`: 操作成功，返回结果
- `Err(CircuitError)`: 操作失败或熔断器打开

**执行流程**:
1. 检查熔断器状态
   - Closed: 允许执行
   - Open: 检查是否可以转为HalfOpen
   - HalfOpen: 尝试获取permit
2. 执行操作（带超时）
3. 记录结果并更新统计
4. 根据统计决定状态转换

**使用示例**:
```rust
use std::time::Duration;
use tokio::time::sleep;

let cb = Arc::new(CircuitBreaker::new(config));

// 执行可能失败的操作
let result = cb.call(|| async {
    // 模拟外部调用
    sleep(Duration::from_millis(100)).await;
    
    if random() < 0.3 {
        Err("Service unavailable")
    } else {
        Ok("Success")
    }
}).await;

match result {
    Ok(value) => println!("Operation succeeded: {}", value),
    Err(CircuitError::CircuitOpen) => {
        println!("Circuit is open, using fallback");
        // 使用降级逻辑
    }
    Err(e) => println!("Operation failed: {}", e),
}
```

**错误处理**:
```rust
match cb.call(operation).await {
    Ok(result) => handle_success(result),
    Err(CircuitError::CircuitOpen) => {
        // 熔断器打开，使用fallback
        use_fallback()
    }
    Err(CircuitError::Timeout) => {
        // 操作超时
        log_timeout();
        Err("Timeout")
    }
    Err(CircuitError::OperationFailed(msg)) => {
        // 操作失败
        log_failure(&msg);
        Err(msg)
    }
    Err(e) => Err(e.to_string()),
}
```

**性能特点**:
- 开销: Closed状态 ~0.1ms, Open状态 ~0.01ms
- 吞吐量: Closed > 100K req/s, Open > 1M req/s
- 内存: ~1KB per instance

---

#### `CircuitBreaker::get_state()`

**签名**:
```rust
pub async fn get_state(&self) -> CircuitState
```

**功能**: 获取当前熔断器状态。

**返回值**: 当前状态（Closed/Open/HalfOpen）

**使用示例**:
```rust
let state = cb.get_state().await;
match state {
    CircuitState::Closed => println!("Circuit is healthy"),
    CircuitState::Open => println!("Circuit is open!"),
    CircuitState::HalfOpen => println!("Circuit is testing"),
}
```

---

#### `CircuitBreaker::get_stats()`

**签名**:
```rust
pub async fn get_stats(&self) -> CircuitStats
```

**功能**: 获取熔断器统计信息。

**返回值**: 包含详细统计的`CircuitStats`结构

**使用示例**:
```rust
let stats = cb.get_stats().await;
println!("Circuit Stats:");
println!("  State: {}", stats.state);
println!("  Total Requests: {}", stats.total_requests);
println!("  Failure Rate: {:.2}%", stats.failure_rate);
println!("  Avg Duration: {:.2}ms", stats.average_duration_ms);
```

---

#### `CircuitBreaker::reset()`

**签名**:
```rust
pub async fn reset(&self)
```

**功能**: 重置熔断器到初始状态。

**效果**:
- 状态重置为Closed
- 清空统计数据
- 重置状态转换计数器

**使用场景**:
- 手动恢复服务
- 测试场景
- 配置更新后

**使用示例**:
```rust
// 手动重置熔断器
cb.reset().await;
info!("Circuit breaker has been reset");
```

⚠️ **警告**: 在生产环境谨慎使用，应该让熔断器自动恢复。

---

### `CircuitBreakerWithFallback`

**定义**:
```rust
pub struct CircuitBreakerWithFallback<T> {
    circuit_breaker: Arc<CircuitBreaker>,
    fallback_fn: Arc<dyn Fn() -> T + Send + Sync>,
}
```

**功能**: 带降级策略的熔断器。

---

#### `CircuitBreakerWithFallback::new()`

**签名**:
```rust
pub fn new(
    config: CircuitBreakerConfig,
    fallback_fn: impl Fn() -> T + Send + Sync + 'static,
) -> Self
```

**功能**: 创建带fallback的熔断器。

**参数**:
- `config`: 熔断器配置
- `fallback_fn`: 降级函数，当操作失败时调用

**使用示例**:
```rust
let cb = CircuitBreakerWithFallback::new(
    config,
    || "Default response from cache".to_string(),
);
```

---

#### `CircuitBreakerWithFallback::call_with_fallback()`

**签名**:
```rust
pub async fn call_with_fallback<F, E>(&self, operation: F) -> T
where
    F: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
```

**功能**: 执行操作，失败时自动使用fallback。

**返回值**: 总是返回`T`，不会失败

**使用示例**:
```rust
let cb = CircuitBreakerWithFallback::new(
    config,
    || vec![], // fallback返回空列表
);

// 总是有返回值
let users = cb.call_with_fallback(|| async {
    fetch_users_from_db().await
}).await;

// 不需要错误处理
println!("Got {} users", users.len());
```

**降级策略示例**:
```rust
// 1. 返回缓存数据
let cb = CircuitBreakerWithFallback::new(config, || {
    CACHE.get("users").unwrap_or_default()
});

// 2. 返回默认值
let cb = CircuitBreakerWithFallback::new(config, || {
    User::default()
});

// 3. 返回静态数据
let cb = CircuitBreakerWithFallback::new(config, || {
    vec![User { id: 0, name: "Guest".to_string() }]
});
```

---

## 统计系统

### `CircuitStats`

**定义**:
```rust
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
```

**功能**: 熔断器统计数据。

**字段说明**:
- `state`: 当前状态
- `total_requests`: 总请求数
- `success_count`: 成功次数
- `failure_count`: 失败次数
- `slow_call_count`: 慢调用次数
- `failure_rate`: 失败率（百分比）
- `slow_call_rate`: 慢调用率（百分比）
- `average_duration_ms`: 平均响应时间（毫秒）
- `state_transitions`: 状态转换次数

**Display实现**:
```rust
impl Display for CircuitStats {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
```

---

### `SlidingWindow`

**定义**:
```rust
struct SlidingWindow {
    success_count: AtomicU64,
    failure_count: AtomicU64,
    slow_call_count: AtomicU64,
    total_duration_ms: AtomicU64,
    last_reset: Arc<RwLock<Instant>>,
    window_size: Duration,
}
```

**功能**: 滑动窗口统计实现（内部使用）。

**特点**:
- 线程安全（使用Atomic操作）
- 自动清理过期数据
- 高性能（无锁读取）

---

## 使用示例

### 基本使用

```rust
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // 创建熔断器
    let config = CircuitBreakerConfig::default();
    let cb = Arc::new(CircuitBreaker::new(config));

    // 模拟多个请求
    for i in 0..100 {
        let cb = cb.clone();
        tokio::spawn(async move {
            let result = cb.call(|| unreliable_service()).await;
            match result {
                Ok(_) => println!("Request {} succeeded", i),
                Err(CircuitError::CircuitOpen) => {
                    println!("Request {} rejected (circuit open)", i);
                }
                Err(e) => println!("Request {} failed: {}", i, e),
            }
        });
    }

    // 等待并查看统计
    tokio::time::sleep(Duration::from_secs(5)).await;
    let stats = cb.get_stats().await;
    println!("\nFinal stats: {}", stats);
}

async fn unreliable_service() -> Result<String, &'static str> {
    if rand::random::<f64>() < 0.3 {
        Err("Service failed")
    } else {
        Ok("Success".to_string())
    }
}
```

### 与Web服务集成

```rust
use axum::{extract::State, Json};

struct AppState {
    circuit_breaker: Arc<CircuitBreaker>,
    // ... other state
}

async fn get_user(
    State(state): State<Arc<AppState>>,
    id: i64,
) -> Result<Json<User>, AppError> {
    let user = state.circuit_breaker
        .call(|| fetch_user_from_db(id))
        .await
        .map_err(|e| match e {
            CircuitError::CircuitOpen => {
                AppError::ServiceUnavailable("Database circuit is open")
            }
            _ => AppError::InternalError,
        })?;
    
    Ok(Json(user))
}
```

### 与缓存集成

```rust
let cb_with_cache = CircuitBreakerWithFallback::new(
    config,
    || {
        // fallback: 从缓存读取
        CACHE.get("user_list").unwrap_or_default()
    },
);

// 总是有返回值
let users = cb_with_cache.call_with_fallback(|| async {
    // 主要逻辑：从数据库读取
    fetch_users_from_db().await
}).await;
```

---

## 最佳实践

### 配置选择

```rust
// ✅ 推荐：根据场景调整配置
let db_config = CircuitBreakerConfig {
    failure_threshold_percentage: 60.0, // 数据库容忍度高一些
    minimum_request_threshold: 30,
    timeout_duration: Duration::from_secs(10), // 数据库查询超时长一些
    ..Default::default()
};

// ❌ 不推荐：所有场景用同一配置
let config = CircuitBreakerConfig::default();
```

### 监控和告警

```rust
// ✅ 推荐：定期检查熔断器状态
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(10));
    loop {
        interval.tick().await;
        let stats = cb.get_stats().await;
        
        // 记录指标
        metrics::gauge!("circuit_breaker.failure_rate", stats.failure_rate);
        metrics::gauge!("circuit_breaker.avg_duration", stats.average_duration_ms);
        
        // 告警
        if stats.state == CircuitState::Open {
            alert!("Circuit breaker is OPEN!");
        }
    }
});
```

### 降级策略

```rust
// ✅ 推荐：提供有意义的fallback
let cb = CircuitBreakerWithFallback::new(config, || {
    // 返回缓存数据或默认值
    get_cached_data().unwrap_or_else(|| default_data())
});

// ❌ 不推荐：空fallback
let cb = CircuitBreakerWithFallback::new(config, || {
    vec![] // 用户体验差
});
```

### 超时设置

```rust
// ✅ 推荐：设置合理的超时
let config = CircuitBreakerConfig {
    timeout_duration: Duration::from_secs(5), // 根据实际情况调整
    ..Default::default()
};

// ⚠️ 警告：超时太短可能导致误判
let config = CircuitBreakerConfig {
    timeout_duration: Duration::from_millis(100), // 可能太短
    ..Default::default()
};
```

---

## 性能指标

| 操作 | Closed状态 | Open状态 | HalfOpen状态 |
|------|-----------|----------|--------------|
| call() 开销 | ~0.1ms | ~0.01ms | ~0.1ms |
| 吞吐量 | >100K req/s | >1M req/s | >50K req/s |
| 内存占用 | ~1KB | ~1KB | ~1KB |
| CPU使用 | 低 | 极低 | 低 |

---

## 相关文档

- [限流器API](./rate_limiter_api.md)
- [重试策略API](./retry_strategy_api.md)
- [容错模式指南](../guides/fault_tolerance.md)
- [示例代码](../../examples/circuit_breaker_complete_impl.rs)

---

**版本**: 1.0.0  
**维护者**: OTLP Rust Team  
**最后更新**: 2025年10月28日

