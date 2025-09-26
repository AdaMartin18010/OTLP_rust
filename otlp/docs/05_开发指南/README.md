# 开发指南

## 📋 概述

本目录包含OTLP Rust项目的开发相关文档，涵盖API参考、配置指南、最佳实践、错误处理等内容。

## 🚀 快速导航

- [📚 API参考](API参考.md) - 完整API文档
- [⚙️ 配置指南](配置指南.md) - 配置管理详解
- [✨ 最佳实践](最佳实践.md) - 开发最佳实践
- [🐛 错误处理](错误处理.md) - 错误处理指南
- [🔍 调试技巧](调试技巧.md) - 调试和测试

## 🎯 开发概览

### 1. API设计

- **统一接口**: 提供统一的API接口
- **类型安全**: 编译时类型检查
- **链式调用**: 支持流畅的链式调用
- **异步优先**: 所有操作都是异步的

### 2. 配置管理

- **灵活配置**: 支持多种配置方式
- **环境适配**: 自动适配不同环境
- **动态更新**: 支持配置动态更新
- **验证机制**: 配置验证和错误提示

### 3. 错误处理

- **类型化错误**: 使用Result类型处理错误
- **错误链**: 完整的错误信息链
- **恢复机制**: 自动错误恢复
- **日志记录**: 详细的错误日志

### 4. 性能优化

- **零拷贝**: 高效的内存管理
- **批处理**: 智能批处理优化
- **连接池**: 连接池管理
- **压缩**: 多种压缩算法

## 🏗️ 开发架构

### 核心组件

```text
OtlpClient (客户端)
├── OtlpProcessor (处理器)
│   ├── DataProcessor (数据处理器)
│   ├── BatchProcessor (批处理器)
│   └── SamplingProcessor (采样处理器)
├── Transport (传输层)
│   ├── GrpcTransport (gRPC传输)
│   ├── HttpTransport (HTTP传输)
│   └── WebSocketTransport (WebSocket传输)
├── Config (配置管理)
│   ├── OtlpConfig (主配置)
│   ├── BatchConfig (批处理配置)
│   └── TransportConfig (传输配置)
└── TelemetryData (数据模型)
    ├── TraceData (追踪数据)
    ├── MetricData (指标数据)
    └── LogData (日志数据)
```

## 🚀 快速开始

### 1. 基础使用1

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
    
    // 发送追踪数据
    let result = client.send_trace("operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("operation.type", "database")
        .finish()
        .await?;
    
    println!("发送成功: {} 条", result.success_count);
    
    client.shutdown().await?;
    Ok(())
}
```

### 2. 高级配置1

```rust
// 高吞吐量配置
let config = OtlpConfig::for_production()
    .with_endpoint("https://api.honeycomb.io:443")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(CompressionAlgorithm::Zstd)
    .with_sampling_ratio(0.1)
    .with_batch_config(BatchConfig {
        max_export_batch_size: 1000,
        export_timeout: Duration::from_millis(5000),
        max_queue_size: 10000,
        scheduled_delay: Duration::from_millis(1000),
    })
    .with_auth(AuthConfig::with_api_key("your-api-key"))
    .with_tls(TlsConfig::enabled());
```

### 3. 错误处理1

```rust
use c21_otlp::error::OtlpError;

async fn handle_errors() -> Result<(), OtlpError> {
    let client = OtlpClient::new(config).await?;
    
    match client.initialize().await {
        Ok(_) => println!("客户端初始化成功"),
        Err(OtlpError::ConnectionError(e)) => {
            eprintln!("连接错误: {}", e);
            // 处理连接错误
        }
        Err(OtlpError::ConfigError(e)) => {
            eprintln!("配置错误: {}", e);
            // 处理配置错误
        }
        Err(e) => {
            eprintln!("其他错误: {}", e);
            // 处理其他错误
        }
    }
    
    Ok(())
}
```

## 📚 学习路径

### 初学者路径

1. 从[API参考](API参考.md)开始了解基础API
2. 学习[配置指南](配置指南.md)掌握配置管理
3. 实践[最佳实践](最佳实践.md)中的示例
4. 掌握[错误处理](错误处理.md)技巧

### 进阶学习

1. 深入理解API设计原理
2. 学习高级配置技巧
3. 掌握性能优化方法
4. 实践复杂场景应用

## 🔗 相关文档

- [快速开始](../01_快速开始/README.md) - 入门指南
- [核心概念](../02_核心概念/README.md) - 基础概念
- [架构设计](../04_架构设计/README.md) - 架构设计
- [高级特性](../06_高级特性/README.md) - 高级功能

---

**目录版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP开发团队
