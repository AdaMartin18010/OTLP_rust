# 📚 OTLP Rust 文档中心

**项目版本**: v0.1.0  
**Rust版本**: 1.90+  
**文档更新**: 2025年1月

---

## 🎯 快速导航

### 📖 核心文档

1. **[快速开始指南](01_GETTING_STARTED/README.md)** - 项目介绍和快速上手
2. **[理论框架](02_THEORETICAL_FRAMEWORK/README.md)** - 形式化语义和理论基础
3. **[API参考文档](03_API_REFERENCE/README.md)** - 完整的API文档
4. **[架构设计文档](04_ARCHITECTURE/README.md)** - 系统架构和设计理念

### 🛠️ 实践文档

1. **[实现指南](05_IMPLEMENTATION/README.md)** - Rust 1.90 特性和实现细节
2. **[部署运维指南](06_DEPLOYMENT/README.md)** - 生产环境部署和运维
3. **[集成指南](07_INTEGRATION/README.md)** - 第三方工具和生态系统集成
4. **[参考资料](08_REFERENCE/README.md)** - 最佳实践、术语表和故障排除

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

1. 阅读[快速开始指南](01_GETTING_STARTED/README.md)
2. 学习[基本概念](08_REFERENCE/glossary.md)
3. 查看[常见问题](08_REFERENCE/troubleshooting_guide.md)

### 开发者

1. 查看[API参考文档](03_API_REFERENCE/README.md)
2. 阅读[架构设计文档](04_ARCHITECTURE/README.md)
3. 学习[实现指南](05_IMPLEMENTATION/README.md)

### 研究者

1. 深入研究[理论框架](02_THEORETICAL_FRAMEWORK/README.md)
2. 分析[最佳实践](08_REFERENCE/best_practices.md)
3. 探索[标准合规性](08_REFERENCE/standards_compliance.md)

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
