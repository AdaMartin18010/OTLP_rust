# 🚀 快速开始指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 快速开始指南 - 从零到一，5分钟上手 OpenTelemetry Protocol 实现。

---

## 📋 目录

- [🚀 快速开始指南](#-快速开始指南)
  - [📋 目录](#-目录)
  - [🔧 系统要求](#-系统要求)
    - [必需环境](#必需环境)
    - [推荐环境](#推荐环境)
  - [📦 安装](#-安装)
    - [1. 检查 Rust 版本](#1-检查-rust-版本)
    - [2. 添加依赖](#2-添加依赖)
    - [3. 安装依赖](#3-安装依赖)
  - [🎯 基本使用](#-基本使用)
    - [最简单的示例](#最简单的示例)
  - [⚙️ 配置选项](#️-配置选项)
    - [基本配置](#基本配置)
    - [高级配置](#高级配置)
  - [📝 示例代码](#-示例代码)
    - [发送指标数据](#发送指标数据)
    - [发送日志数据](#发送日志数据)
    - [批量发送](#批量发送)
  - [🔍 验证安装](#-验证安装)
    - [运行测试](#运行测试)
    - [检查配置](#检查配置)
  - [🚨 常见问题](#-常见问题)
    - [连接问题](#连接问题)
    - [性能问题](#性能问题)
    - [编译问题](#编译问题)
  - [📚 下一步](#-下一步)
    - [深入学习](#深入学习)
    - [实践项目](#实践项目)
    - [社区参与](#社区参与)

## 🔧 系统要求

### 必需环境

- **Rust**: 1.90.0 或更高版本
- **操作系统**: Windows 10+, macOS 10.15+, Ubuntu 18.04+
- **内存**: 建议 4GB 以上
- **网络**: 支持 HTTP/HTTPS 和 gRPC 协议

### 推荐环境

- **CPU**: 多核心处理器
- **存储**: SSD 硬盘
- **网络**: 稳定的互联网连接

## 📦 安装

### 1. 检查 Rust 版本

```bash
rustc --version
# 应该显示 1.90.0 或更高版本
```

### 2. 添加依赖

在您的 `Cargo.toml` 中添加：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.47", features = ["full"] }
```

### 3. 安装依赖

```bash
cargo build
```

## 🎯 基本使用

### 最简单的示例

```rust
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use otlp::config::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("my-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));

    // 创建客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;

    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("duration", 150.0)
        .finish()
        .await?;

    println!("追踪数据发送结果: 成功 {} 条", result.success_count);

    // 关闭客户端
    client.shutdown().await?;

    Ok(())
}
```

## ⚙️ 配置选项

### 基本配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("https://api.example.com/otlp")
    .with_protocol(TransportProtocol::Grpc)
    .with_api_key("your-api-key")
    .with_tls(true);
```

### 高级配置

```rust
use otlp::config::{Compression, BatchConfig, RetryConfig};

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_millis(5000),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(5000),
};

let retry_config = RetryConfig {
    max_retries: 5,
    initial_retry_delay: Duration::from_millis(1000),
    max_retry_delay: Duration::from_secs(30),
    retry_delay_multiplier: 2.0,
    randomize_retry_delay: true,
};

let config = OtlpConfig::default()
    .with_endpoint("https://api.example.com/otlp")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_batch_config(batch_config)
    .with_retry_config(retry_config);
```

## 📝 示例代码

### 发送指标数据

```rust
// 发送指标数据
let metric_data = TelemetryData::metric("request_count")
    .with_value(42.0)
    .with_attribute("method", "GET")
    .with_attribute("status", "200");

let result = client.send_metric(metric_data).await?;
```

### 发送日志数据

```rust
// 发送日志数据
let log_data = TelemetryData::log("User login")
    .with_severity(LogSeverity::Info)
    .with_attribute("user_id", "12345")
    .with_attribute("ip_address", "192.168.1.1");

let result = client.send_log(log_data).await?;
```

### 批量发送

```rust
// 批量发送数据
let mut batch_data = Vec::new();

for i in 0..100 {
    let trace_data = TelemetryData::trace(format!("operation-{}", i))
        .with_attribute("batch_id", "batch-001")
        .with_attribute("operation_index", i.to_string());

    batch_data.push(trace_data);
}

let result = client.send_batch(batch_data).await?;
println!("批量发送结果: 成功 {} 条", result.success_count);
```

## 🔍 验证安装

### 运行测试

```bash
# 运行单元测试
cargo test

# 运行集成测试
cargo test --test integration

# 运行基准测试
cargo bench
```

### 检查配置

```rust
// 验证配置
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317");

println!("配置验证: {:?}", config.validate());
```

## 🚨 常见问题

### 连接问题

- 确保 OTLP 收集器正在运行
- 检查网络连接和防火墙设置
- 验证端点 URL 是否正确

### 性能问题

- 调整批处理配置
- 启用压缩
- 优化重试策略

### 编译问题

- 确保 Rust 版本 >= 1.90.0
- 检查依赖版本兼容性
- 清理并重新构建项目

## 📚 下一步

### 深入学习

1. 阅读 [API 参考文档](../03_API_REFERENCE/README.md)
2. 了解 [架构设计](../04_ARCHITECTURE/README.md)
3. 探索 [理论框架](../02_THEORETICAL_FRAMEWORK/README.md)

### 实践项目

1. 集成到现有微服务
2. 设置监控和告警
3. 优化性能和可靠性

### 社区参与

1. 查看 [贡献指南](../../CONTRIBUTING.md)
2. 报告问题和建议
3. 参与社区讨论

---

**需要帮助？** 查看 [故障排除指南](../06_DEPLOYMENT/troubleshooting.md) 或 [联系我们](../../README.md#支持)。
