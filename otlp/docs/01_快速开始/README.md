# 快速开始指南

## 📋 概述

欢迎使用OTLP Rust项目！本目录提供新用户快速上手的完整指南。

## 🚀 快速导航

- [📖 安装指南](安装指南.md) - 环境安装和配置
- [💡 基础示例](基础示例.md) - 简单使用示例
- [❓ 常见问题](常见问题.md) - 新手常见问题解答

## 🎯 5分钟快速上手

### 1. 安装依赖

在`Cargo.toml`中添加依赖：

```toml
[dependencies]
c21_otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
```

### 2. 基础使用

```rust
use c21_otlp::{OtlpClient, OtlpConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_service("my-service", "1.0.0");
    
    // 创建客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送数据
    let result = client.send_trace("operation").await?
        .with_attribute("key", "value")
        .finish()
        .await?;
    
    println!("发送成功: {} 条", result.success_count);
    Ok(())
}
```

### 3. 运行示例

```bash
cargo run --example simple_demo
```

## 📚 下一步

完成快速开始后，建议继续学习：

- [核心概念](../02_核心概念/README.md) - 了解OTLP协议基础
- [开发指南](../05_开发指南/README.md) - 深入学习开发技巧
- [示例教程](../08_示例和教程/README.md) - 查看更多示例

---

**目录版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP文档团队
