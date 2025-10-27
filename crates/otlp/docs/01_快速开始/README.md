# 快速开始指南

**版本**: 1.1.0  
**最后更新**: 2025年10月27日  
**Rust 版本**: 1.90.0  
**状态**: 🟢 活跃维护

> **简介**: 欢迎使用 OTLP Rust 项目！本目录提供新用户快速上手的完整指南，5 分钟即可开始使用 OTLP。

---

## 📋 目录

- [快速开始指南](#快速开始指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 目录说明](#11-目录说明)
    - [1.2 前提条件](#12-前提条件)
  - [2. 快速导航](#2-快速导航)
    - [2.1 文档列表](#21-文档列表)
    - [2.2 推荐阅读顺序](#22-推荐阅读顺序)
  - [3. 5分钟快速上手](#3-5分钟快速上手)
    - [3.1 安装依赖](#31-安装依赖)
    - [3.2 基础使用](#32-基础使用)
    - [3.3 运行示例](#33-运行示例)
  - [4. 下一步](#4-下一步)
    - [4.1 深入学习](#41-深入学习)
    - [4.2 学习路径建议](#42-学习路径建议)
  - [5. 常见问题](#5-常见问题)
  - [6. 获取帮助](#6-获取帮助)

---

## 1. 概述

### 1.1 目录说明

本目录包含 OTLP Rust 项目的快速开始指南，帮助您：

- ✅ 快速安装和配置环境
- ✅ 5分钟运行第一个示例
- ✅ 了解基本使用方法
- ✅ 解决常见问题

### 1.2 前提条件

开始之前，请确保您已安装：

```bash
# Rust 1.90+ (必须)
rustc --version  # 应显示 1.90.0 或更高版本

# Cargo (包管理器，随 Rust 一起安装)
cargo --version

# 可选：OTLP Collector（用于接收数据）
# 参考：https://opentelemetry.io/docs/collector/
```

---

## 2. 快速导航

### 2.1 文档列表

| 文档 | 说明 | 预计时间 |
|------|------|---------|
| [安装指南](安装指南.md) | 详细的环境安装和配置步骤 | 15 分钟 |
| [基础示例](基础示例.md) | 简单的使用示例和代码讲解 | 10 分钟 |
| [常见问题](常见问题.md) | 新手常见问题解答 | 按需查阅 |

### 2.2 推荐阅读顺序

```text
快速上手流程
  ↓
1. 阅读本文档 (5 分钟)
  ↓
2. 完成 5 分钟快速上手 (↓)
  ↓
3. [可选] 详细的安装指南
  ↓
4. [可选] 查看更多基础示例
  ↓
进入核心概念学习
```

---

## 3. 5分钟快速上手

### 3.1 安装依赖

在您的 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
# OTLP 客户端
otlp = "0.1.0"

# 异步运行时 (Rust 1.90 完全兼容)
tokio = { version = "1.0", features = ["full"] }

# 可选：日志和追踪
tracing = "0.1"
tracing-subscriber = "0.3"
```

**Rust 1.90 优化配置** (可选):

```toml
[profile.release]
lto = true           # 链接时优化
codegen-units = 1    # 受益于 LLD 链接器
opt-level = 3        # 最高优化级别
```

### 3.2 基础使用

创建 `src/main.rs` 文件：

```rust
use otlp::{OtlpClient, OtlpConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")  // OTLP Collector 地址
        .with_service("my-service", "1.0.0");     // 服务名称和版本
    
    // 2. 创建客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 3. 发送追踪数据
    let result = client
        .send_trace("my_operation")
        .await?
        .with_attribute("user_id", "12345")
        .with_attribute("action", "login")
        .finish()
        .await?;
    
    println!("✅ 发送成功: {} 条追踪数据", result.success_count);
    
    // 4. 发送指标数据
    client
        .send_metric("http_requests_total", 1.0)
        .with_label("method", "GET")
        .with_label("status", "200")
        .await?;
    
    println!("✅ 指标数据已发送");
    
    Ok(())
}
```

### 3.3 运行示例

#### 3.3.1 启动 OTLP Collector (可选)

如果没有 OTLP Collector，可以使用 Docker 快速启动：

```bash
# 使用 Docker 启动 OTLP Collector
docker run -d \
  --name otlp-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  otel/opentelemetry-collector:latest
```

#### 3.3.2 运行您的应用

```bash
# 编译并运行（受益于 Rust 1.90 LLD 链接器加速）
cargo run

# 或者运行示例
cargo run --example simple_demo
```

#### 3.3.3 预期输出

```text
✅ 发送成功: 1 条追踪数据
✅ 指标数据已发送
```

---

## 4. 下一步

### 4.1 深入学习

完成快速开始后，建议继续学习：

| 主题 | 文档 | 预计时间 |
|------|------|---------|
| **核心概念** | [核心概念](../02_核心概念/README.md) | 2-3 小时 |
| **标准规范** | [标准规范](../03_标准规范/README.md) | 1-2 小时 |
| **开发指南** | [开发指南](../05_开发指南/README.md) | 3-4 小时 |
| **示例教程** | [示例和教程](../08_示例和教程/README.md) | 按需查阅 |
| **API 参考** | [API Reference](../API_REFERENCE.md) | 按需查阅 |

### 4.2 学习路径建议

#### 路径 1: 快速实践 (1 周)

```text
Day 1: 快速开始 + 基础示例
  ↓
Day 2-3: 核心概念学习
  ↓
Day 4-5: 运行更多示例
  ↓
Day 6-7: 实际项目集成
```

#### 路径 2: 系统学习 (2-3 周)

```text
Week 1: 快速开始 → 核心概念 → 标准规范
  ↓
Week 2: 架构设计 → 开发指南 → 示例教程
  ↓
Week 3: 高级特性 → 性能优化 → 生产部署
```

#### 路径 3: 闭环学习 (推荐)

```text
1. 完成本页 5 分钟上手
   ↓
2. 阅读并理解【核心概念】
   ↓
3. 返回本页运行更多【示例教程】
   ↓
4. 结合【用户指南】进行进阶配置与实践
   ↓
5. 查阅【API 参考】深入了解细节
```

---

## 5. 常见问题

### Q1: 为什么连接不上 OTLP Collector？

**A**: 请检查：
1. Collector 是否正在运行：`docker ps | grep otlp`
2. 端口是否正确：默认 gRPC 端口 `4317`，HTTP 端口 `4318`
3. 网络是否可达：`telnet localhost 4317`

### Q2: 如何查看发送的数据？

**A**: 可以：
1. 查看 Collector 的日志输出
2. 配置 Collector 导出到 Jaeger 或 Prometheus
3. 使用 OTLP 的调试模式

### Q3: Rust 1.90 有什么特殊配置吗？

**A**: Rust 1.90 主要改进：
- ✅ LLD 链接器自动启用（Linux x86_64），编译速度提升 30-50%
- ✅ 更多 const API 稳定
- ✅ Workspace 一键发布：`cargo publish --workspace`

无需特殊配置，自动受益！

### Q4: 如何在生产环境使用？

**A**: 请参考：
1. [部署指南](../07_部署运维/README.md)
2. [生产检查清单](../PRODUCTION_CHECKLIST.md)
3. [安全配置指南](../07_部署运维/OTLP_RUST_安全配置和最佳实践指南.md)

更多问题请查看 [完整常见问题文档](常见问题.md)。

---

## 6. 获取帮助

### 6.1 文档资源

- 📖 [用户指南](../USER_GUIDE.md) - 完整的使用手册
- 📋 [API 参考](../API_REFERENCE.md) - API 详细文档
- 🔧 [开发指南](../05_开发指南/README.md) - 开发者文档

### 6.2 社区支持

- 🐛 [GitHub Issues](https://github.com/your-org/otlp-rust/issues) - 报告问题
- 💬 [GitHub Discussions](https://github.com/your-org/otlp-rust/discussions) - 讨论交流
- 📧 Email: support@example.com

### 6.3 相关链接

- [OpenTelemetry 官网](https://opentelemetry.io/)
- [Rust 官网](https://www.rust-lang.org/)
- [Tokio 文档](https://tokio.rs/)

---

**文档版本**: 1.1.0  
**维护者**: OTLP 文档团队  
**最后更新**: 2025年10月27日  
**Rust 版本**: 1.90.0

---

**🎉 恭喜您完成快速开始！现在可以开始探索更多功能了！** 🚀

**下一步推荐**: [核心概念](../02_核心概念/README.md) - 深入理解 OTLP 协议
