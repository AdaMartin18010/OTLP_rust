# OTLP Rust 项目文档

欢迎来到 OTLP Rust 项目的文档中心。本项目提供了基于 Rust 1.90+ 的 OpenTelemetry Protocol (OTLP) 完整实现，以及统一的可靠性框架。

## 📚 文档导航

> 💡 **新手推荐**: 先阅读 [📖 文档导航指南](DOCUMENTATION_GUIDE.md)，快速找到适合您的学习路径！

### 🚀 快速开始

- [项目概览](README.md) - 项目整体介绍和快速开始
- [📖 文档导航指南](DOCUMENTATION_GUIDE.md) ⭐ - 根据角色和需求快速定位文档
- [🎯 快速开始指南](01_GETTING_STARTED/README.md) ⭐ - 完整的入门教程（268 行）
- [安装指南](guides/installation.md) ✅ - 环境配置快速参考
- [快速入门](guides/quick-start.md) ✅ - 5分钟快速上手

### 📖 用户指南

- [OTLP 客户端使用](guides/otlp-client.md) ✅ - OTLP 客户端详细使用指南
- [可靠性框架](guides/reliability-framework.md) ✅ - 错误处理和容错机制
- [性能优化](guides/performance-optimization.md) ✅ - 性能调优最佳实践
- [监控配置](guides/monitoring.md) ✅ - 监控和告警配置
- [部署指南](guides/deployment.md) ✅ - 生产环境部署指南
- [故障排除](guides/troubleshooting.md) ✅ - 常见问题和解决方案
- [更多用户指南](guides/README.md) - 完整用户指南索引

### 🏗️ 架构设计

- [🏛️ 完整架构文档](04_ARCHITECTURE/README.md) ⭐ - 微服务架构、性能优化、安全架构（653 行）
- [系统架构](architecture/system-architecture.md) ✅ - 整体架构快速参考
- [模块设计](architecture/module-design.md) ✅ - 模块设计快速参考
- [架构索引](architecture/README.md) - 更多架构文档

### 🔧 API 参考

- [📚 完整 API 文档](03_API_REFERENCE/README.md) ⭐ - OtlpClient、配置选项、数据类型（578 行）
- [OTLP API](api/otlp.md) ✅ - OTLP API 快速参考
- [Reliability API](api/reliability.md) ✅ - 可靠性 API 快速参考
- [API 索引](api/README.md) - 更多 API 文档

### 📝 示例和教程

- [📦 示例代码索引](EXAMPLES_INDEX.md) ⭐ - 38+ 个可运行示例快速查找
- [基础示例文档](examples/basic-examples.md) ✅ - Hello World 到完整应用的 7 个示例
- [高级示例文档](examples/advanced-examples.md) ✅ - 微服务、分布式追踪等高级示例
- [OTLP 示例代码](../crates/otlp/examples/) - 25 个 OTLP 实际代码示例
- [可靠性示例代码](../crates/reliability/examples/) - 13 个可靠性框架代码示例

### 🔬 理论框架

- [理论框架总览](02_THEORETICAL_FRAMEWORK/README.md) - 完整的理论基础和形式化模型
- [语义模型与流分析](02_THEORETICAL_FRAMEWORK/SEMANTIC_MODELS_AND_FLOW_ANALYSIS.md) - 2600+行核心理论
- [自我修复架构](02_THEORETICAL_FRAMEWORK/SELF_HEALING_AUTO_ADJUSTMENT_ARCHITECTURE.md) - MAPE-K 循环实现
- [快速参考指南](02_THEORETICAL_FRAMEWORK/QUICK_REFERENCE.md) - 核心概念速查
- [分布式系统理论](02_THEORETICAL_FRAMEWORK/DISTRIBUTED_SYSTEMS_THEORY.md) - 分布式理论基础

### 🛠️ 实现指南

> 🆕 **OTLP 2024-2025 新特性实现**

- [实现指南总览](05_IMPLEMENTATION/README.md) - 完整的实现指南索引
- [🔥 Profile 信号实现指南](05_IMPLEMENTATION/profile_signal_implementation_guide.md) - 885 行性能分析实现详解 ⭐ NEW
  - Profile 数据采集与导出 | CPU/内存/锁分析 | 持续性能分析
- [⚡ Event 信号实现指南](05_IMPLEMENTATION/event_signal_implementation_guide.md) - 1011 行事件系统实现详解 ⭐ NEW
  - Event vs Logs 对比 | 结构化事件处理 | 业务事件跟踪
- [🚀 OTLP/Arrow 配置指南](05_IMPLEMENTATION/otlp_arrow_configuration_guide.md) - 430 行高性能传输配置 ⭐ NEW
  - Apache Arrow 集成 | 列式内存格式 | 零拷贝优化

### 📚 参考资料

- [参考资料总览](08_REFERENCE/README.md) - 完整的参考资料索引
- [🌟 OTLP 标准对齐](08_REFERENCE/otlp_standards_alignment.md) - 1300+ 行 OTLP 标准完整参考 ⭐ NEW
- [🚀 OTLP 2024-2025 特性](08_REFERENCE/otlp_2024_2025_features.md) - 800+ 行最新特性详解 ⭐ NEW
- [最佳实践指南](08_REFERENCE/best_practices.md) - 开发、性能、安全最佳实践
- [术语表](08_REFERENCE/glossary.md) - OTLP 和 OpenTelemetry 术语
- [故障排除指南](08_REFERENCE/troubleshooting_guide.md) - 常见问题解决方案

### 🔍 深入分析

- 高级分析文档位于 `../analysis/` 目录
- 包含语义模型、分布式架构、形式化验证等主题
- 详见项目根目录的 analysis 文件夹

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
└── scripts/                   # 构建和部署脚本
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

## 🚀 快速开始

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

- [贡献指南](guides/CONTRIBUTING.md) - 完整的贡献流程和规范

## 📄 许可证

本项目采用 MIT OR Apache-2.0 双许可证。

## 🔗 相关链接

- [OpenTelemetry 官网](https://opentelemetry.io/)
- [Rust 官网](https://www.rust-lang.org/)
- [Tokio 异步运行时](https://tokio.rs/)
- [项目 GitHub](https://github.com/your-org/OTLP_rust)

---

## 🎉 最近更新

### 2025年10月24日

- ✅ **OTLP 2024-2025 实现指南** (2462+ 行) - Profile/Event 信号、OTLP/Arrow 完整实现指南
  - Profile 信号性能分析实现 (885 行)
  - Event 信号事件系统实现 (1011 行)
  - OTLP/Arrow 高性能传输配置 (430 行)
- ✅ **OTLP 标准对齐文档** (1300+ 行) - 完整的 OTLP 协议版本、数据模型、Semantic Conventions 参考
- ✅ **OTLP 2024-2025 特性文档** (800+ 行) - Profile/Event 信号、增强日志模型、OTLP/Arrow 等最新特性
- ✅ **参考资料索引升级** - 新增 2000+ 行高质量参考文档

---

*最后更新: 2025年10月24日*
