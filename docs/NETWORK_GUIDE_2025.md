# 网络管理指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

网络管理模块 (`crates/otlp/src/network/`) 提供了网络和连接管理功能，包括连接池、负载均衡、健康检查和网络监控。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::network::{ConnectionPool, ConnectionPoolConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = ConnectionPoolConfig::default();
    let pool = ConnectionPool::new(config);

    // 获取连接
    let connection = pool.get_connection().await?;

    // 使用连接...

    // 归还连接
    pool.return_connection(connection).await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### ConnectionPool

连接池，用于管理连接复用。

**方法**:

- `new(config: ConnectionPoolConfig) -> Self` - 创建连接池
- `get_connection() -> Result<PooledConnection>` - 获取连接
- `return_connection(connection: PooledConnection) -> Result<()>` - 归还连接
- `get_stats() -> ConnectionPoolStats` - 获取统计信息

#### LoadBalancer

负载均衡器，用于分发请求。

**策略**:

- `RoundRobin` - 轮询
- `LeastConnections` - 最少连接
- `Random` - 随机
- `WeightedRoundRobin` - 加权轮询

**方法**:

- `new(config: LoadBalancerConfig) -> Self` - 创建负载均衡器
- `select_backend() -> Option<BackendServer>` - 选择后端
- `get_stats() -> LoadBalancerStats` - 获取统计信息

#### NetworkManager

网络管理器，统一管理网络功能。

**方法**:

- `new(config: NetworkConfig) -> Self` - 创建管理器
- `get_connection_pool(name: &str) -> Option<Arc<ConnectionPool>>` - 获取连接池
- `get_load_balancer(name: &str) -> Option<Arc<LoadBalancer>>` - 获取负载均衡器

---

## 💡 示例代码

### 示例 1: 连接池

```rust
use otlp::network::{ConnectionPool, ConnectionPoolConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = ConnectionPoolConfig {
        max_connections: 100,
        min_connections: 10,
        idle_timeout: Duration::from_secs(300),
        ..Default::default()
    };

    let pool = ConnectionPool::new(config);

    // 获取连接
    let connection = pool.get_connection().await?;

    // 使用连接执行操作
    // ...

    // 归还连接
    pool.return_connection(connection).await?;

    Ok(())
}
```

### 示例 2: 负载均衡

```rust
use otlp::network::{LoadBalancer, LoadBalancerConfig, LoadBalancingStrategy};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = LoadBalancerConfig {
        strategy: LoadBalancingStrategy::RoundRobin,
        backends: vec![
            BackendServer::new("http://server1:8080"),
            BackendServer::new("http://server2:8080"),
            BackendServer::new("http://server3:8080"),
        ],
    };

    let balancer = LoadBalancer::new(config);

    // 选择后端
    if let Some(backend) = balancer.select_backend() {
        // 使用后端...
    }

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 连接池配置

根据负载调整连接池配置：

```rust
let config = ConnectionPoolConfig {
    max_connections: 100,  // 根据服务器容量
    min_connections: 10,   // 保持最小连接数
    idle_timeout: Duration::from_secs(300),  // 空闲超时
    ..Default::default()
};
```

### 2. 负载均衡策略

根据场景选择策略：

```rust
// 均匀负载：轮询
let strategy = LoadBalancingStrategy::RoundRobin;

// 性能优化：最少连接
let strategy = LoadBalancingStrategy::LeastConnections;

// 加权分发：加权轮询
let strategy = LoadBalancingStrategy::WeightedRoundRobin;
```

---

## 📚 参考资源

### API 参考

- `ConnectionPool` - 连接池
- `LoadBalancer` - 负载均衡器
- `NetworkManager` - 网络管理器
- `HealthChecker` - 健康检查器

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
