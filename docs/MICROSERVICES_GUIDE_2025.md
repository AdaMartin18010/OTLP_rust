# 微服务支持指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

微服务支持模块 (`crates/otlp/src/microservices/`) 提供了微服务架构设计模式实现，包括服务发现、负载均衡、熔断器和重试机制。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::microservices::{MicroserviceClient, ServiceEndpoint, CircuitBreakerConfig, RetryConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let service_discovery = Arc::new(MockConsulClient::new());
    let load_balancer = Arc::new(RoundRobinLoadBalancer::new());

    let client = MicroserviceClient::new(
        service_discovery,
        load_balancer,
        CircuitBreakerConfig::default(),
        RetryConfig::default(),
    );

    // 调用服务
    let result = client.call_service("api", |endpoint| async {
        // 服务调用逻辑
        Ok("success")
    }).await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### MicroserviceClient

微服务客户端，整合服务发现、负载均衡和容错机制。

**方法**:

- `new(service_discovery, load_balancer, circuit_breaker_config, retry_config) -> Self` - 创建客户端
- `call_service<F, Fut, R>(service_name: &str, f: F) -> Result<R>` - 调用服务

#### LoadBalancer

负载均衡器 trait。

**实现**:

- `RoundRobinLoadBalancer` - 轮询负载均衡
- `WeightedRoundRobinLoadBalancer` - 加权轮询负载均衡

#### CircuitBreaker

熔断器，防止级联故障。

**状态**:

- `Closed` - 关闭（正常）
- `Open` - 打开（故障）
- `HalfOpen` - 半开（恢复中）

---

## 💡 示例代码

### 示例 1: 基本服务调用

```rust
use otlp::microservices::{MicroserviceClient, MockConsulClient, RoundRobinLoadBalancer};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let service_discovery = Arc::new(MockConsulClient::new());
    let load_balancer = Arc::new(RoundRobinLoadBalancer::new());

    let client = MicroserviceClient::new(
        service_discovery,
        load_balancer,
        CircuitBreakerConfig::default(),
        RetryConfig::default(),
    );

    let result = client.call_service("api", |endpoint| async {
        // 调用 API
        Ok("success".to_string())
    }).await?;

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 负载均衡策略

根据场景选择策略：

```rust
// 均匀负载：轮询
let balancer = Arc::new(RoundRobinLoadBalancer::new());

// 性能优化：加权轮询
let balancer = Arc::new(WeightedRoundRobinLoadBalancer::new());
```

---

## 📚 参考资源

### API 参考

- `MicroserviceClient` - 微服务客户端
- `LoadBalancer` - 负载均衡器
- `CircuitBreaker` - 熔断器
- `Retryer` - 重试器

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
