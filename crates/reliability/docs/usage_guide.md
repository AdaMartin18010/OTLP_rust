# c13_reliability 使用指南

**版本**: 0.3.0  
**最后更新**: 2025年10月27日  
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)  
**状态**: 🟢 活跃维护

> **简介**: c13_reliability的完整使用指南，涵盖依赖配置、功能特性、代码示例、性能优化等所有内容。

---

## 📋 目录

- [1. 快速开始](#1-快速开始)
- [2. 功能特性说明](#2-功能特性说明)
- [3. 使用示例](#3-使用示例)
- [4. 代码示例](#4-代码示例)
- [5. 完整项目示例](#5-完整项目示例)
- [6. 运行和测试](#6-运行和测试)
- [7. 性能优化建议](#7-性能优化建议)
- [8. 安全性考虑](#8-安全性考虑)
- [9. 进一步学习](#9-进一步学习)
- [10. 贡献和支持](#10-贡献和支持)

---

## 1. 快速开始

### 1.1 添加依赖

在您的项目 `Cargo.toml` 中添加：

```toml
[dependencies]
c13_reliability = { version = "0.2.0", path = "../c13_reliability" }

# 或者从 crates.io（发布后）
# c13_reliability = "0.2.0"

# 或者从 GitHub
# c13_reliability = { git = "https://github.com/rust-lang/c13_reliability" }

# Rust 1.90 推荐配置（受益于 LLD 链接器）
[profile.release]
lto = true           # 链接时优化
codegen-units = 1    # 单个代码生成单元（更好的优化）
strip = true         # 移除调试信息（减小二进制大小）
opt-level = 3        # 最高优化级别

# Rust 1.90 新特性说明:
# - Linux x86_64 平台自动启用 LLD 链接器，编译速度提升 30-50%
# - 支持更多 const API，可在编译期进行更多计算
# - 完全兼容最新的 Tokio 异步运行时
```

### 1.2 选择功能特性

根据您的需求启用相应的 features：

```toml
[dependencies]
c13_reliability = { 
    version = "0.2.0",
    path = "../c13_reliability",
    features = ["async", "monitoring", "fault-tolerance", "otlp"]
}
```

---

## 2. 功能特性说明

### 2.1 默认特性 (default)

```toml
default = [
    "std", 
    "async", 
    "monitoring", 
    "fault-tolerance", 
    "otlp", 
    "logging", 
    "os-environment"
]
```

这些特性在不指定时会自动启用。

### 2.2 核心特性

| Feature | 说明 | 依赖项 |
|---------|------|--------|
| `std` | 标准库支持 | 无 |
| `async` | 异步运行时支持 | tokio, futures, async-trait |
| `monitoring` | 监控和指标收集 | metrics, prometheus, sysinfo |
| `fault-tolerance` | 容错机制 | parking_lot, dashmap, crossbeam |
| `logging` | 日志记录 | env_logger |

### 2.3 可观测性特性

| Feature | 说明 | 用途 |
|---------|------|------|
| `otlp` | OpenTelemetry OTLP 支持 | 分布式追踪 |
| `otlp-stdout` | OTLP 标准输出导出 | 调试和开发 |
| `otlp-proto` | OTLP 协议支持 | 协议解析 |

### 2.4 高级特性

| Feature | 说明 | 适用场景 |
|---------|------|----------|
| `chaos-engineering` | 混沌工程测试 | 压力测试 |
| `jemalloc` | jemalloc 内存分配器 | 性能优化 |
| `verification` | 形式化验证基础 | 代码验证 |
| `prusti` | Prusti 验证工具 | 静态分析 |
| `creusot` | Creusot 验证工具 | 演绎验证 |

### 2.5 环境支持

| Feature | 说明 | 目标环境 |
|---------|------|----------|
| `os-environment` | 操作系统环境 | 标准服务器 |
| `embedded-environment` | 嵌入式环境 | IoT 设备 |
| `container-environment` | 容器环境 | Docker/K8s |

### 2.6 云原生特性 (可选)

| Feature | 说明 | 何时启用 |
|---------|------|----------|
| `containers` | 容器支持 | 容器化部署 |
| `virtualization` | 虚拟化支持 | VM 环境 |
| `kubernetes` | Kubernetes 集成 | K8s 部署 |
| `docker-runtime` | Docker 运行时适配 | 本地 Docker |
| `oci` | OCI 规范支持 | OCI 容器 |

---

## 3. 使用示例

### 3.1 最小配置

仅使用核心功能，不需要异步和监控：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    default-features = false,
    features = ["std"]
}
```

### 3.2 异步应用

构建异步 Web 服务：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["async", "monitoring", "otlp"]
}
tokio = { version = "1.48", features = ["full"] }
```

### 3.3 可观测性完整方案

启用完整的可观测性支持：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "otlp-proto",
        "logging"
    ]
}
```

### 3.4 云原生部署

Kubernetes 环境部署：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "containers",
        "kubernetes"
    ]
}
```

### 3.5 高性能配置

使用 jemalloc 和容错机制：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "fault-tolerance",
        "jemalloc",
        "monitoring"
    ]
}
```

### 3.6 形式化验证

开发时进行代码验证：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["verification", "prusti"]
}

# 开发依赖
[dev-dependencies]
prusti-contracts = "0.2"
```

### 3.7 嵌入式系统

资源受限的嵌入式环境：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    default-features = false,
    features = ["embedded-environment"]
}
```

---

## 4. 代码示例

### 4.1 基础使用

```rust
use c13_reliability::prelude::*;

fn main() {
    // 初始化可靠性框架
    let config = ReliabilityConfig::default();
    let reliability = Reliability::new(config);
    
    // 使用错误处理
    match reliability.execute(|| {
        // 您的业务逻辑
        Ok(())
    }) {
        Ok(_) => println!("执行成功"),
        Err(e) => eprintln!("执行失败: {}", e),
    }
}
```

### 4.2 异步使用

```rust
use c13_reliability::prelude::*;
use tokio;

#[tokio::main]
async fn main() {
    let config = ReliabilityConfig::default();
    let reliability = Reliability::new(config);
    
    // 异步执行
    if let Err(e) = reliability.execute_async(async {
        // 异步业务逻辑
        Ok(())
    }).await {
        eprintln!("异步执行失败: {}", e);
    }
}
```

### 4.3 监控和指标

```rust
use c13_reliability::monitoring::*;

fn main() {
    // 启用监控
    let monitor = Monitor::new();
    monitor.start();
    
    // 记录指标
    monitor.record_metric("request_count", 1.0);
    monitor.record_latency("api_latency", 125);
    
    // 导出 Prometheus 指标
    let metrics = monitor.export_prometheus();
    println!("{}", metrics);
}
```

### 4.4 容错机制

```rust
use c13_reliability::fault_tolerance::*;
use std::time::Duration;

fn main() {
    // 创建重试策略
    let retry = RetryPolicy::exponential_backoff(
        3,                              // 最大重试次数
        Duration::from_secs(1),         // 初始延迟
        Duration::from_secs(60)         // 最大延迟
    );
    
    // 执行带重试的操作
    let result = retry.execute(|| {
        // 可能失败的操作
        external_api_call()
    });
}

fn external_api_call() -> Result<String, Error> {
    // 外部 API 调用
    Ok("Success".to_string())
}
```

### 4.5 OpenTelemetry 追踪

```rust
use c13_reliability::telemetry::*;
use tracing::{info, span, Level};

#[tokio::main]
async fn main() {
    // 初始化 OpenTelemetry
    let _guard = init_telemetry("my-service");
    
    // 创建 span
    let span = span!(Level::INFO, "process_request");
    let _enter = span.enter();
    
    info!("处理请求");
    process_request().await;
    info!("请求完成");
}

async fn process_request() {
    // 业务逻辑
}
```

---

## 5. 完整项目示例

### 5.1 Web 服务项目的 Cargo.toml

```toml
[package]
name = "my-web-service"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# 可靠性框架
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "logging",
        "os-environment"
    ]
}

# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# Web 框架
axum = "0.8"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

[dev-dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["chaos-engineering"]
}
```

### 5.2 微服务项目的 Cargo.toml

```toml
[package]
name = "my-microservice"
version = "0.1.0"
edition = "2024"

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "containers",
        "kubernetes",
        "jemalloc"
    ]
}

# 服务发现
consul = "0.4"

# 配置管理
config = "0.15"

# 数据库
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio"] }

# 消息队列
rdkafka = "0.36"
```

---

## 6. 运行和测试

### 6.1 构建项目

```bash
# 使用默认特性
cargo build

# 指定特性
cargo build --features "async,monitoring,otlp"

# 发布构建
cargo build --release --features "async,monitoring,fault-tolerance,jemalloc"
```

### 6.2 运行示例

```bash
# 运行基础示例
cargo run --example basic_usage

# 运行形式化验证示例
cargo run --example creusot_basic
cargo run --example prusti_basic
cargo run --example kani_basic
```

### 6.3 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定特性的测试
cargo test --features "async,monitoring"

# 运行示例测试
cargo test --examples
```

---

## 7. 性能优化建议

### 7.1 生产环境配置

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async",
        "fault-tolerance",
        "jemalloc",
        "monitoring"
    ]
}
```

### 7.2 开发环境配置

```toml
[profile.dev]
opt-level = 0

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async",
        "logging",
        "chaos-engineering"
    ]
}
```

---

## 8. 安全性考虑

### 8.1 审计依赖

```bash
# 安装 cargo-audit
cargo install cargo-audit

# 检查安全漏洞
cargo audit
```

### 8.2 最小权限原则

仅启用必需的特性：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    default-features = false,
    features = ["std", "async"]  # 仅启用必需特性
}
```

---

## 9. 进一步学习

### 9.1 核心文档

- [00_MASTER_INDEX.md](./00_MASTER_INDEX.md) - 完整文档导航
- [错误处理最佳实践](./ERROR_HANDLING_GUIDE.md)
- [容错机制详解](./FAULT_TOLERANCE_ENHANCEMENT_REPORT.md)
- [形式化验证工具](./FORMAL_VERIFICATION_TOOLS_GUIDE.md)

### 9.2 示例代码

- [examples/](../examples/) - 示例代码
- [tests/](../tests/) - 测试用例
- [benches/](../benches/) - 性能基准

---

## 10. 贡献和支持

### 10.1 社区资源

- **GitHub**: <https://github.com/rust-lang/c13_reliability>
- **文档**: <https://docs.rs/c13_reliability>
- **问题反馈**: <https://github.com/rust-lang/c13_reliability/issues>

### 10.2 许可证

MIT OR Apache-2.0 双许可证

---

**版本**: 0.3.0  
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)  
**最后更新**: 2025年10月27日  
**维护者**: C13 Reliability Team  
**反馈**: [提交 Issue](https://github.com/rust-lang/c13_reliability/issues)

---

> **提示**: 根据您的项目需求选择合适的功能特性，从最小配置开始逐步添加！🦀✨
