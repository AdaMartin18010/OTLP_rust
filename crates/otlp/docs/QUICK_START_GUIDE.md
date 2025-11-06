# OTLP Rust 快速开始指南

**版本**: 1.1
**最后更新**: 2025年10月27日
**Rust 版本**: 1.90.0 (LLD链接器、const API)
**状态**: 🟢 活跃维护

> **简介**: 5分钟快速入门指南，帮助您快速开始使用 OTLP Rust 库进行分布式追踪、指标收集和日志记录。

---

## 📋 目录

- [OTLP Rust 快速开始指南](#otlp-rust-快速开始指南)
  - [📋 目录](#-目录)
  - [🎯 快速开始](#-快速开始)
  - [📝 前置要求](#-前置要求)
  - [💡 安装](#-安装)
    - [3.1 添加依赖](#31-添加依赖)
    - [3.2 创建项目](#32-创建项目)
  - [🔧 基础使用](#-基础使用)
    - [4.1 最简单的示例](#41-最简单的示例)
    - [4.2 运行示例](#42-运行示例)
  - [📊 发送不同类型的数据](#-发送不同类型的数据)
    - [5.1 发送追踪数据](#51-发送追踪数据)
    - [5.2 发送指标数据](#52-发送指标数据)
    - [5.3 发送日志数据](#53-发送日志数据)
  - [🚀 配置选项](#-配置选项)
    - [6.1 基本配置](#61-基本配置)
    - [6.2 高级配置](#62-高级配置)
    - [6.3 TLS 配置](#63-tls-配置)
  - [🔍 常见场景](#-常见场景)
    - [7.1 Web 服务集成](#71-web-服务集成)
    - [7.2 数据库操作追踪](#72-数据库操作追踪)
    - [7.3 微服务通信追踪](#73-微服务通信追踪)
  - [💻 故障排查](#-故障排查)
  - [📚 下一步](#-下一步)

---

## 🎯 快速开始

本指南将帮助您在几分钟内开始使用OTLP Rust库。

---

## 📝 前置要求

- Rust 1.90 或更高版本
- 基本的Rust编程知识
- 运行中的OTLP收集器（如Jaeger、OpenTelemetry Collector等）

---

## 💡 安装

### 3.1 添加依赖

在您的 `Cargo.toml` 文件中添加OTLP依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.47", features = ["full"] }
anyhow = "1.0"
```

### 3.2 创建项目

```bash
cargo new my-otlp-app
cd my-otlp-app
```

---

## 🔧 基础使用

### 4.1 最简单的示例

创建一个 `src/main.rs` 文件：

```rust
use anyhow::Result;
use otlp::{OtlpClient, OtlpClientBuilder, OtlpConfig, StatusCode, AttributeValue};

#[tokio::main]
async fn main() -> Result<()> {
    // 创建OTLP客户端
    let client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_config(OtlpConfig::default())
        .build()
        .await?;

    // 发送追踪数据
    client.trace_builder()
        .with_trace_id("1234567890abcdef")
        .with_span_id("abcdef1234567890")
        .with_operation_name("hello_world")
        .with_status_code(StatusCode::Ok)
        .with_attribute("message", AttributeValue::String("Hello, OTLP!".to_string()))
        .send()
        .await?;

    println!("✅ 追踪数据发送成功！");
    Ok(())
}
```

### 4.2 运行示例

```bash
cargo run
```

---

## 📊 发送不同类型的数据

### 5.1 发送追踪数据

```rust
use otlp::{TraceBuilder, StatusCode, AttributeValue};

async fn send_trace_data(client: &OtlpClient) -> Result<()> {
    client.trace_builder()
        .with_trace_id("trace_123")
        .with_span_id("span_456")
        .with_operation_name("user_login")
        .with_status_code(StatusCode::Ok)
        .with_attribute("user.id", AttributeValue::String("user123".to_string()))
        .with_attribute("request.duration", AttributeValue::Int64(150))
        .send()
        .await?;

    Ok(())
}
```

### 5.2 发送指标数据

```rust
use otlp::{MetricBuilder, AttributeValue};

async fn send_metric_data(client: &OtlpClient) -> Result<()> {
    client.metric_builder()
        .with_name("request_count")
        .with_description("Total number of requests")
        .with_value(AttributeValue::Int64(1000))
        .with_attribute("service", AttributeValue::String("my_service".to_string()))
        .send()
        .await?;

    Ok(())
}
```

### 5.3 发送日志数据

```rust
use otlp::{LogBuilder, AttributeValue};

async fn send_log_data(client: &OtlpClient) -> Result<()> {
    client.log_builder()
        .with_message("User login successful")
        .with_level("INFO")
        .with_attribute("user.id", AttributeValue::String("user123".to_string()))
        .with_attribute("ip_address", AttributeValue::String("192.168.1.100".to_string()))
        .send()
        .await?;

    Ok(())
}
```

---

## 🚀 配置选项

### 6.1 基本配置

```rust
use otlp::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression};

let config = OtlpConfigBuilder::new()
    .with_endpoint("http://localhost:4317")
    .with_transport_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .build();
```

### 6.2 高级配置

```rust
use otlp::{BatchConfig, Duration};

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_secs(30),
    max_queue_size: 2048,
};

let config = OtlpConfigBuilder::new()
    .with_batch_config(batch_config)
    .build();
```

### 6.3 TLS 配置

```rust
use otlp::{TlsConfig, OtlpConfigBuilder};

let tls_config = TlsConfig {
    enabled: true,
    ca_cert_path: Some("ca.pem".to_string()),
    client_cert_path: Some("client.pem".to_string()),
    client_key_path: Some("client-key.pem".to_string()),
};

let config = OtlpConfigBuilder::new()
    .with_endpoint("https://secure-collector:4317")
    .with_tls_config(tls_config)
    .build();
```

---

## 🔍 常见场景

### 7.1 Web 服务集成

```rust
use otlp::{ComprehensivePerformanceOptimizer, TelemetryData};

async fn use_performance_optimizer() -> Result<()> {
    let optimizer = ComprehensivePerformanceOptimizer::new();

    // 创建测试数据
    let test_data = vec![TelemetryData::default(); 1000];

    // 优化处理
    let optimized_data = optimizer.optimize_processing(test_data).await?;

    println!("优化处理了 {} 条数据", optimized_data.len());
    Ok(())
}
```

### 7.2 数据库操作追踪

```rust
use otlp::{OtlpClient, AttributeValue};

async fn trace_database_operation(client: &OtlpClient) -> Result<()> {
    // 开始数据库操作追踪
    client.trace_builder()
        .with_trace_id("db_trace_001")
        .with_span_id("db_span_001")
        .with_operation_name("database_query")
        .with_attribute("db.system", AttributeValue::String("postgresql".to_string()))
        .with_attribute("db.statement", AttributeValue::String("SELECT * FROM users".to_string()))
        .send()
        .await?;

    Ok(())
}
```

### 7.3 微服务通信追踪

```rust
use otlp::{OtlpClient, AttributeValue};

async fn trace_microservice_call(client: &OtlpClient) -> Result<()> {
    // 追踪微服务间通信
    client.trace_builder()
        .with_trace_id("ms_trace_001")
        .with_span_id("ms_span_001")
        .with_operation_name("call_user_service")
        .with_attribute("service.name", AttributeValue::String("api-gateway".to_string()))
        .with_attribute("target.service", AttributeValue::String("user-service".to_string()))
        .send()
        .await?;

    Ok(())
}
```

---

## 💻 故障排查

**常见问题及解决方案**:

1. **连接失败**
   - 检查OTLP收集器是否运行
   - 验证endpoint配置是否正确
   - 确认网络连接正常

2. **数据未显示**
   - 检查数据格式是否正确
   - 验证trace_id和span_id是否有效
   - 查看收集器日志

3. **性能问题**
   - 启用批量发送
   - 调整批量大小和超时时间
   - 使用异步发送

---

## 📚 下一步

现在您已经掌握了OTLP Rust库的基础用法，可以：

1. **阅读完整API文档**: 查看 [API_REFERENCE.md](API_REFERENCE.md) 了解所有可用功能
2. **运行综合示例**: 查看 `examples/` 目录了解高级用法
3. **探索核心概念**: 阅读 [02_核心概念/](02_核心概念/) 深入理解OTLP
4. **性能优化**: 查看 [06_高级特性/性能优化.md](06_高级特性/性能优化.md)
5. **生产部署**: 参考 [DEPLOYMENT_GUIDE.md](DEPLOYMENT_GUIDE.md)

**推荐学习路径**:

```
快速开始 → 核心概念 → API参考 → 高级特性 → 生产部署
```

---

**文档版本**: 1.1
**Rust 版本**: 1.90.0 (LLD链接器、const API)
**最后更新**: 2025年10月27日
**反馈**: [提交 Issue](https://github.com/your-org/otlp-rust/issues)

---

> **提示**: 本文档是快速入门指南。如需更深入的内容，请参考完整文档索引 [00_MASTER_INDEX.md](00_MASTER_INDEX.md)。

**🎉 祝您使用愉快！** 🚀
