# 项目文档索引

## 📚 文档导航

### 🚀 快速开始

- [项目概览](../README.md) - 项目整体介绍和快速开始
- [安装指南](installation.md) - 安装和配置指南
- [快速示例](quick-start.md) - 5分钟快速上手

### 📖 用户指南

- [OTLP 客户端使用](otlp-client.md) - OTLP 客户端详细使用指南
- [可靠性框架](reliability-framework.md) - 错误处理和容错机制
- [性能优化](performance-optimization.md) - 性能调优最佳实践
- [监控和可观测性](monitoring.md) - 监控配置和使用

### 🏗️ 架构设计

- [系统架构](../architecture/system-architecture.md) - 整体系统架构设计
- [模块设计](../architecture/module-design.md) - 各模块详细设计
- [API 设计原则](../design/api-design.md) - API 设计理念和原则
- [性能设计](../design/performance-design.md) - 性能优化设计思路

### 🔧 API 参考

- [OTLP API](../api/otlp.md) - OTLP 客户端完整 API 文档
- [Reliability API](../api/reliability.md) - 可靠性框架 API 文档
- [类型定义](../api/types.md) - 核心类型和数据结构

### 📝 示例和教程

- [基础示例](basic-examples.md) - 基础使用示例
- [高级示例](advanced-examples.md) - 高级功能和模式
- [微服务集成](microservices.md) - 微服务架构集成示例
- [性能基准](benchmarks.md) - 性能测试和基准

### 🔍 深入分析

- [语义模型分析](../../analysis/semantic-models.md) - 语义模型深度分析
- [分布式架构](../../analysis/distributed-architecture.md) - 分布式系统设计
- [Rust 1.90 特性](../../analysis/rust-190-features.md) - Rust 1.90 新特性应用

## 🏛️ 项目结构

```text
OTLP_rust/
├── crates/                    # Rust crates 目录
│   ├── otlp/                  # OTLP 核心实现
│   └── reliability/           # 可靠性框架
├── docs/                      # 项目文档
│   ├── api/                   # API 参考文档
│   ├── guides/                # 用户指南
│   ├── examples/              # 示例和教程
│   ├── architecture/          # 架构设计文档
│   └── design/                # 设计理念文档
├── analysis/                  # 深度分析文档
├── benchmarks/                # 性能基准测试
└── scripts/                   # 构建脚本
```

## 🎯 核心特性

### OTLP 核心实现

- ✅ **异步优先设计** - 基于 Tokio 的高性能异步处理
- ✅ **多传输协议** - 支持 gRPC 和 HTTP/JSON 传输
- ✅ **类型安全** - 利用 Rust 类型系统确保编译时安全
- ✅ **零拷贝优化** - 最小化内存拷贝操作
- ✅ **并发安全** - 无锁并发数据结构

### 可靠性框架

- ✅ **统一错误处理** - 类型安全、上下文丰富的错误处理
- ✅ **容错机制** - 断路器、重试、超时、降级
- ✅ **运行时监控** - 健康检查、性能监控、异常检测
- ✅ **自动恢复** - 内存泄漏检测、连接池重建
- ✅ **混沌工程** - 故障注入、弹性测试

## 🚀 快速开始1

### 安装依赖

```bash
# 确保使用 Rust 1.90+
rustup update
rustup default 1.90

# 克隆项目
git clone <repository-url>
cd OTLP_rust

# 构建项目
cargo build
```

### 基础使用

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .build()
        .await?;

    let tracer = client.tracer("my-component");
    let span = tracer.start("my-operation");
    // ... 业务逻辑
    drop(span);
    
    Ok(())
}
```

## 📊 性能特性

- **高吞吐量** - 支持每秒百万级事件处理
- **低延迟** - 微秒级响应时间
- **内存高效** - 智能内存管理和对象池
- **CPU 优化** - SIMD 指令集优化
- **网络优化** - HTTP/2 多路复用和压缩

## 🤝 贡献指南

我们欢迎社区贡献！请查看：

- [贡献指南](CONTRIBUTING.md)
- [代码规范](CODE_STYLE.md)
- [测试指南](TESTING.md)

## 📄 许可证

本项目采用 MIT OR Apache-2.0 双许可证。

## 🔗 相关链接

- [OpenTelemetry 官网](https://opentelemetry.io/)
- [Rust 官网](https://www.rust-lang.org/)
- [Tokio 异步运行时](https://tokio.rs/)
- [项目 GitHub](https://github.com/your-org/OTLP_rust)

---

*最后更新: 2025年10月20日*-
