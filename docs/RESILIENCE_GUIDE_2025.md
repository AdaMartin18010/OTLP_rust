# 容错与弹性指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

容错与弹性模块 (`crates/otlp/src/resilience/`) 提供了完整的容错和弹性机制，包括熔断器、重试、超时和舱壁隔离等功能。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::resilience::{ResilienceManager, CircuitBreakerConfig, RetryConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = ResilienceManager::new();

    // 创建断路器
    let breaker_config = CircuitBreakerConfig {
        failure_threshold: 5,
        recovery_timeout: Duration::from_secs(30),
        half_open_max_requests: 3,
        success_threshold: 2,
    };

    let breaker = manager
        .get_or_create_circuit_breaker("api", breaker_config)
        .await;

    // 使用断路器保护操作
    match breaker.call(|| async {
        // 可能失败的操作
        Ok(())
    }).await {
        Ok(result) => println!("成功: {:?}", result),
        Err(e) => eprintln!("失败: {}", e),
    }

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### ResilienceManager

弹性管理器，统一管理所有容错组件。

**方法**:

- `new() -> Self` - 创建管理器
- `get_or_create_circuit_breaker(name: &str, config: CircuitBreakerConfig) -> Arc<CircuitBreaker>` - 获取或创建断路器
- `get_or_create_retrier(name: &str, config: RetryConfig) -> Arc<Retrier>` - 获取或创建重试器
- `get_or_create_bulkhead(name: &str, config: BulkheadConfig) -> Arc<Bulkhead>` - 获取或创建舱壁
- `get_or_create_timeout(name: &str, config: TimeoutConfig) -> Arc<Timeout>` - 获取或创建超时器

#### CircuitBreaker

熔断器，用于防止级联故障。

**状态**:

- `Closed` - 关闭（正常）
- `Open` - 打开（故障）
- `HalfOpen` - 半开（恢复中）

**方法**:

- `call<F, T>(f: F) -> Result<T>` - 执行操作
- `state() -> CircuitState` - 获取状态
- `reset()` - 重置状态

#### Retrier

重试器，用于自动重试失败的操作。

**策略**:

- `Fixed { interval: Duration }` - 固定间隔
- `Exponential { initial_interval, max_interval, multiplier }` - 指数退避

**方法**:

- `retry<F, T>(f: F) -> Result<T>` - 重试操作
- `stats() -> RetryStats` - 获取统计信息

#### Bulkhead

舱壁隔离，用于限制并发请求。

**方法**:

- `execute<F, T>(f: F) -> Result<T>` - 执行操作
- `status() -> BulkheadStatus` - 获取状态

#### Timeout

超时控制，用于防止操作超时。

**方法**:

- `timeout<F, T>(f: F) -> Result<T>` - 执行带超时的操作
- `status() -> TimeoutStatus` - 获取状态

---

## 💡 示例代码

### 示例 1: 熔断器

```rust
use otlp::resilience::{ResilienceManager, CircuitBreakerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = ResilienceManager::new();

    let breaker_config = CircuitBreakerConfig {
        failure_threshold: 5,
        recovery_timeout: Duration::from_secs(30),
        half_open_max_requests: 3,
        success_threshold: 2,
    };

    let breaker = manager
        .get_or_create_circuit_breaker("api", breaker_config)
        .await;

    // 使用断路器
    let result = breaker.call(|| async {
        // API 调用
        Ok("success")
    }).await?;

    Ok(())
}
```

### 示例 2: 重试器

```rust
use otlp::resilience::{ResilienceManager, RetryConfig, RetryStrategy};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = ResilienceManager::new();

    let retry_config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::Exponential {
            initial_interval: Duration::from_millis(100),
            max_interval: Duration::from_secs(30),
            multiplier: 2.0,
        },
        total_timeout: Some(Duration::from_secs(60)),
        health_check: false,
    };

    let retrier = manager
        .get_or_create_retrier("api", retry_config)
        .await;

    // 使用重试器
    let result = retrier.retry(|| async {
        // 可能失败的操作
        Ok("success")
    }).await?;

    Ok(())
}
```

### 示例 3: 舱壁隔离

```rust
use otlp::resilience::{ResilienceManager, BulkheadConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = ResilienceManager::new();

    let bulkhead_config = BulkheadConfig {
        max_concurrent_requests: 10,
        max_queue_size: 100,
    };

    let bulkhead = manager
        .get_or_create_bulkhead("api", bulkhead_config)
        .await;

    // 使用舱壁
    let result = bulkhead.execute(|| async {
        // 受保护的操作
        Ok("success")
    }).await?;

    Ok(())
}
```

### 示例 4: 超时控制

```rust
use otlp::resilience::{ResilienceManager, TimeoutConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = ResilienceManager::new();

    let timeout_config = TimeoutConfig {
        timeout: Duration::from_secs(5),
    };

    let timeout = manager
        .get_or_create_timeout("api", timeout_config)
        .await;

    // 使用超时器
    let result = timeout.timeout(|| async {
        // 可能超时的操作
        Ok("success")
    }).await?;

    Ok(())
}
```

### 示例 5: 组合使用

```rust
use otlp::resilience::{ResilienceManager, CircuitBreakerConfig, RetryConfig, RetryStrategy};
use std::time::Duration;

async fn resilient_operation(manager: &ResilienceManager) -> Result<String, Box<dyn std::error::Error>> {
    // 创建断路器
    let breaker = manager
        .get_or_create_circuit_breaker("api", CircuitBreakerConfig::default())
        .await;

    // 创建重试器
    let retrier = manager
        .get_or_create_retrier("api", RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Exponential {
                initial_interval: Duration::from_millis(100),
                max_interval: Duration::from_secs(5),
                multiplier: 2.0,
            },
            total_timeout: None,
            health_check: false,
        })
        .await;

    // 组合使用：先重试，再通过断路器
    let result = retrier.retry(|| {
        breaker.call(|| async {
            // 实际操作
            Ok("success".to_string())
        })
    }).await?;

    Ok(result)
}
```

---

## 🎯 最佳实践

### 1. 配置选择

根据场景选择合适的配置：

```rust
// 生产环境：严格的熔断器
let breaker_config = CircuitBreakerConfig {
    failure_threshold: 5,
    recovery_timeout: Duration::from_secs(60),
    half_open_max_requests: 2,
    success_threshold: 3,
};

// 开发环境：宽松的熔断器
let breaker_config = CircuitBreakerConfig {
    failure_threshold: 10,
    recovery_timeout: Duration::from_secs(10),
    half_open_max_requests: 5,
    success_threshold: 2,
};
```

### 2. 重试策略

选择合适的重试策略：

```rust
// 网络请求：指数退避
let retry_config = RetryConfig {
    max_attempts: 5,
    strategy: RetryStrategy::Exponential {
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(30),
        multiplier: 2.0,
    },
    total_timeout: Some(Duration::from_secs(60)),
    health_check: false,
};

// 快速操作：固定间隔
let retry_config = RetryConfig {
    max_attempts: 3,
    strategy: RetryStrategy::Fixed {
        interval: Duration::from_millis(100),
    },
    total_timeout: None,
    health_check: false,
};
```

### 3. 监控状态

定期监控容错组件状态：

```rust
let status = manager.get_all_status().await;

// 检查断路器状态
for (name, state) in &status.circuit_breakers {
    match state {
        CircuitState::Open => {
            eprintln!("断路器 {} 已打开", name);
        }
        CircuitState::HalfOpen => {
            println!("断路器 {} 半开", name);
        }
        CircuitState::Closed => {
            // 正常
        }
    }
}

// 检查重试统计
for (name, stats) in &status.retriers {
    println!("重试器 {}: 总重试 {} 次", name, stats.total_retries);
}
```

---

## ⚠️ 注意事项

### 1. 状态管理

熔断器状态是共享的，多个操作会共享同一个熔断器：

```rust
// 所有 "api" 操作共享同一个熔断器
let breaker1 = manager.get_or_create_circuit_breaker("api", config).await;
let breaker2 = manager.get_or_create_circuit_breaker("api", config).await;
// breaker1 和 breaker2 是同一个实例
```

### 2. 超时设置

合理设置超时时间：

```rust
// ❌ 错误：超时时间过短
let timeout_config = TimeoutConfig {
    timeout: Duration::from_millis(10),  // 太短
};

// ✅ 正确：根据操作类型设置
let timeout_config = TimeoutConfig {
    timeout: Duration::from_secs(5),  // 合理
};
```

### 3. 资源限制

舱壁隔离会限制并发，确保有足够的容量：

```rust
// 根据实际负载设置
let bulkhead_config = BulkheadConfig {
    max_concurrent_requests: 100,  // 根据服务器容量
    max_queue_size: 1000,  // 根据内存容量
};
```

---

## 📚 参考资源

### 相关文档

- [容错模式](https://en.wikipedia.org/wiki/Circuit_breaker_design_pattern)
- [重试模式](https://docs.microsoft.com/en-us/azure/architecture/patterns/retry)

### API 参考

- `ResilienceManager` - 弹性管理器
- `CircuitBreaker` - 熔断器
- `Retrier` - 重试器
- `Bulkhead` - 舱壁隔离
- `Timeout` - 超时控制

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
