# 📚 OTLP Rust 文档中心

**项目版本**: v0.1.0  
**Rust版本**: 1.90+  
**文档更新**: 2025年1月

---

## 🎯 快速导航

### 📖 核心文档

1. **[项目概述](README.md)** - 项目介绍和快速开始
2. **[架构设计](architecture.md)** - 系统架构和设计理念
3. **[API参考](api.md)** - 完整的API文档
4. **[性能报告](performance.md)** - 性能基准和优化指南

### 🔧 开发文档

1. **[开发指南](development.md)** - 开发环境设置和贡献指南
2. **[测试指南](testing.md)** - 测试策略和最佳实践
3. **[部署指南](deployment.md)** - 生产环境部署指南
4. **[故障排除](troubleshooting.md)** - 常见问题和解决方案

### 📊 理论文档

1. **[理论框架](theory.md)** - 形式化语义和可计算性理论
2. **[设计模式](patterns.md)** - 架构模式和最佳实践
3. **[性能优化](optimization.md)** - 性能优化策略和技巧
4. **[安全指南](security.md)** - 安全最佳实践

---

## 🚀 快速开始

### 安装

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.47", features = ["full"] }
```

### 基本使用

```rust
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use otlp::config::TransportProtocol;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    // 创建客户端
    let client = OtlpClient::new(config).await?;
    
    // 发送数据
    let trace_data = TelemetryData::trace("example-operation");
    client.send_trace(trace_data).await?;
    
    Ok(())
}
```

---

## 📈 项目状态

### 当前版本特性

- ✅ **核心功能**: 完整的OTLP协议实现
- ✅ **性能优化**: 纳秒级客户端创建，皮秒级数据处理
- ✅ **类型安全**: Rust类型系统保证内存安全
- ✅ **异步支持**: 基于Tokio的高性能异步处理
- ✅ **多传输**: 支持gRPC和HTTP传输协议

### 性能指标

| 指标 | 性能 | 状态 |
|------|------|------|
| 客户端创建 | 188 ns | ✅ 优秀 |
| 序列化性能 | 3,972 条/秒 | ✅ 良好 |
| 数据处理 | 29.7M 条/秒 | ✅ 优秀 |

---

## 🎓 学习路径

### 初学者

1. 阅读[项目概述](README.md)
2. 运行[快速开始](quickstart.md)示例
3. 学习[基本概念](concepts.md)

### 开发者

1. 查看[API参考](api.md)
2. 阅读[架构设计](architecture.md)
3. 参与[开发指南](development.md)

### 研究者

1. 深入研究[理论框架](theory.md)
2. 分析[设计模式](patterns.md)
3. 探索[性能优化](optimization.md)

---

## 🤝 贡献指南

### 如何贡献

1. **Fork项目**
2. **创建特性分支**
3. **提交更改**
4. **创建Pull Request**

### 贡献类型

- 🐛 **Bug修复**: 修复已知问题
- ✨ **新功能**: 添加新特性
- 📚 **文档**: 改进文档质量
- 🧪 **测试**: 增加测试覆盖
- ⚡ **性能**: 性能优化

---

## 📞 支持

### 获取帮助

1. **GitHub Issues**: 报告问题和功能请求
2. **文档**: 查看完整文档
3. **社区**: 参与社区讨论
4. **邮件**: 联系维护者

### 联系方式

- **项目主页**: [GitHub Repository]
- **问题反馈**: [GitHub Issues]
- **文档网站**: [Documentation Site]
- **社区论坛**: [Community Forum]

---

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双重许可证。

---

**文档最后更新**: 2025年1月  
**维护者**: OTLP Rust Team  
**项目状态**: ✅ 活跃开发中

🎉 **欢迎使用 OTLP Rust！** 🎉
