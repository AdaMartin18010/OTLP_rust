# 🚀 OTLP Rust - OpenTelemetry Protocol 完整实现

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/otlp.svg)](https://crates.io/crates/otlp)
[![Documentation](https://docs.rs/otlp/badge.svg)](https://docs.rs/otlp)

一个基于 **Rust 1.90** 语言特性的 **OpenTelemetry Protocol (OTLP)** 完整实现，支持同步和异步结合的遥测数据收集、处理和传输。

## ✨ 核心特性

- 🎯 **异步优先设计** - 利用 Rust 1.90 的 async/await 特性实现高性能异步处理
- 🔄 **同步兼容** - 提供同步 API 接口，支持传统同步代码集成
- 🌐 **多传输协议** - 支持 gRPC 和 HTTP/JSON 两种 OTLP 传输方式
- 🛡️ **类型安全** - 利用 Rust 类型系统确保编译时安全性
- ⚡ **零拷贝优化** - 使用 Rust 1.90 的内存管理特性优化性能
- 🔒 **并发安全** - 基于 Rust 的所有权系统实现无锁并发
- 📊 **完整错误处理** - 提供详细的错误类型和重试机制
- 📈 **性能监控** - 内置指标收集和性能分析功能
- 🗜️ **数据压缩** - 支持 Gzip、Brotli、Zstd 多种压缩算法
- 🔧 **灵活配置** - 支持批处理、重试、采样等高级配置

## 🏗️ 架构设计

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   数据收集层     │    │   数据处理层     │    │   数据传输层     │
│  (Collection)   │───▶│  (Processing)   │───▶│  (Transport)    │
│                 │    │                 │    │                 │
│ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
│ • Metrics       │    │ • 批处理        │    │ • HTTP/JSON     │
│ • Logs          │    │ • 压缩          │    │ • 重试机制      │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

## 🚀 快速开始

### 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
```

### 基本使用

```rust
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use otlp::data::{LogSeverity, StatusCode};
use otlp::config::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP 配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("my-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 创建并初始化客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("duration", 150.0)
        .with_status(StatusCode::Ok, Some("操作成功".to_string()))
        .finish()
        .await?;
    
    println!("追踪数据发送结果: 成功 {} 条", result.success_count);
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

## 📚 使用示例

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

### 异步并发发送

```rust
// 异步并发发送
let mut futures = Vec::new();

for i in 0..10 {
    let client_clone = client.clone();
    let future = tokio::spawn(async move {
        client_clone.send_trace(format!("async-operation-{}", i)).await?
            .with_attribute("async", "true")
            .finish()
            .await
    });
    futures.push(future);
}

// 等待所有异步操作完成
for future in futures {
    let result = future.await??;
    println!("异步操作结果: 成功 {} 条", result.success_count);
}
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
    .with_api_key("your-api-key")
    .with_tls(true)
    .with_sampling_ratio(0.1)
    .with_batch_config(batch_config)
    .with_retry_config(retry_config)
    .with_resource_attribute("environment", "production")
    .with_resource_attribute("region", "us-west-2");
```

## 🔧 配置选项

### 传输协议

- **gRPC** - 高性能二进制协议，支持流式传输
- **HTTP/JSON** - 基于 HTTP 的 JSON 格式传输
- **HTTP/Protobuf** - 基于 HTTP 的 Protobuf 格式传输

### 压缩算法

- **Gzip** - 标准 gzip 压缩
- **Brotli** - Google 开发的压缩算法
- **Zstd** - Facebook 开发的高性能压缩算法

### 批处理配置

- 批处理大小控制
- 超时时间设置
- 队列大小限制
- 调度间隔配置

### 重试机制

- 指数退避算法
- 最大重试次数
- 随机化延迟
- 可重试错误识别

## 📊 性能特性

### 异步处理

- 基于 Tokio 异步运行时
- 支持高并发数据处理
- 非阻塞 I/O 操作
- 异步批处理机制

### 内存优化

- 零拷贝数据传输
- 高效的内存管理
- 自动垃圾回收
- 内存池技术

### 网络优化

- 连接池管理
- 自动重连机制
- 压缩传输
- 负载均衡

## 🧪 测试和基准测试

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_client_creation

# 运行集成测试
cargo test --test integration
```

### 运行基准测试

```bash
# 运行性能基准测试
cargo bench

# 运行特定基准测试
cargo bench batch_trace_send
```

### 集成测试

```bash
# 启动测试服务器
docker run -p 4317:4317 -p 4318:4318 otel/opentelemetry-collector

# 运行集成测试
cargo test --test integration
```

## 📖 文档

### 完整文档

- [API 文档](https://docs.rs/otlp)
- [使用指南](docs/README.md)
- [架构设计](docs/architecture/README.md)
- [性能优化](docs/performance_optimization/README.md)

### 2025年最新分析文档

- [OTLP国际标准分析](otlp/docs/standards/OTLP_INTERNATIONAL_STANDARDS_2025.md)
- [同步异步控制流分析](otlp/docs/sync_async/OTLP_SYNC_ASYNC_CONTROL_FLOW_2025.md)
- [算法和设计模式](otlp/docs/algorithms/OTLP_ALGORITHMS_DESIGN_PATTERNS_2025.md)
- [采样控制和动态调整](otlp/docs/sampling/OTLP_SAMPLING_CONTROL_2025.md)
- [递归和调度组合](otlp/docs/advanced/OTLP_RECURSIVE_MIXED_SCHEDULING_2025.md)

## 🤝 贡献指南

1. Fork 项目
2. 创建特性分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 打开 Pull Request

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双重许可证。详情请参阅 [LICENSE](LICENSE) 文件。

## 🙏 致谢

- [OpenTelemetry](https://opentelemetry.io/) - 提供 OTLP 协议标准
- [Rust社区](https://www.rust-lang.org/community) - 提供优秀的语言和工具
- [Tokio](https://tokio.rs/) - 提供异步运行时
- [Tonic](https://github.com/hyperium/tonic) - 提供 gRPC 实现

## 📞 支持

如果您遇到问题或有任何建议，请：

1. 查看 [Issues](https://github.com/your-repo/otlp-rust/issues)
2. 创建新的 Issue
3. 联系维护者

---

**注意**: 这是一个演示项目，展示了如何使用 Rust 1.90 的语言特性实现 OTLP 协议。在生产环境中使用前，请进行充分的测试和性能评估。
