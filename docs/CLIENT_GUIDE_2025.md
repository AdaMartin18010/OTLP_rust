# OTLP 客户端指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

OTLP 客户端模块 (`crates/otlp/src/client.rs`) 提供了高级的 OTLP 客户端接口，整合了处理器、导出器和传输层，支持完整的遥测数据收集和导出功能。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::{OtlpClient, OtlpClientBuilder};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = OtlpClientBuilder::new()
        .endpoint("https://api.example.com:4317")
        .timeout(Duration::from_secs(10))
        .build()
        .await?;

    // 初始化
    client.initialize().await?;

    // 发送数据
    // ...

    // 关闭
    client.shutdown().await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### OtlpClient

主要的客户端结构体，提供完整的 OTLP 功能。

**主要方法**:

- `new(config: OtlpConfig) -> Result<Self>` - 创建客户端
- `initialize() -> Result<()>` - 初始化客户端
- `send(data: TelemetryData) -> Result<ExportResult>` - 发送单个数据
- `send_batch(data: Vec<TelemetryData>) -> Result<ExportResult>` - 批量发送
- `shutdown() -> Result<()>` - 关闭客户端
- `get_metrics() -> ClientMetrics` - 获取指标

#### OtlpClientBuilder

客户端构建器，提供链式 API。

**方法**:

- `new() -> Self` - 创建构建器
- `endpoint(url: impl Into<String>) -> Self` - 设置端点
- `protocol(protocol: TransportProtocol) -> Self` - 设置协议
- `service(name: impl Into<String>, version: impl Into<String>) -> Self` - 设置服务信息
- `auth(api_key: impl Into<String>) -> Self` - 设置认证
- `timeout(timeout: Duration) -> Self` - 设置超时
- `build() -> Result<OtlpClient>` - 构建客户端

#### TraceBuilder, MetricBuilder, LogBuilder

用于构建和发送不同类型的遥测数据的构建器。

---

## 💡 示例代码

### 示例 1: 基本客户端使用

```rust
use otlp::{OtlpClient, OtlpClientBuilder};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = OtlpClientBuilder::new()
        .endpoint("https://api.example.com:4317")
        .build()
        .await?;

    client.initialize().await?;

    // 使用客户端...

    client.shutdown().await?;
    Ok(())
}
```

### 示例 2: 发送追踪数据

```rust
use otlp::OtlpClient;

async fn send_trace(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let trace = client.send_trace("my-operation").await?
        .with_attribute("key", "value")
        .with_numeric_attribute("duration", 123.45)
        .finish()
        .await?;

    println!("追踪发送成功: {:?}", trace);
    Ok(())
}
```

### 示例 3: 发送指标数据

```rust
use otlp::OtlpClient;

async fn send_metric(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let metric = client.send_metric("requests_per_second", 100.0).await?
        .with_label("service", "api")
        .with_description("Requests per second")
        .with_unit("1/s")
        .send()
        .await?;

    println!("指标发送成功: {:?}", metric);
    Ok(())
}
```

### 示例 4: 批量发送

```rust
use otlp::{OtlpClient, TelemetryData};

async fn send_batch(client: &OtlpClient, data: Vec<TelemetryData>) -> Result<(), Box<dyn std::error::Error>> {
    let result = client.send_batch(data).await?;
    println!("批量发送: 成功 {} 个, 失败 {} 个",
        result.success_count, result.failure_count);
    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 使用构建器模式

推荐使用 `OtlpClientBuilder` 来创建客户端：

```rust
let client = OtlpClientBuilder::new()
    .endpoint("https://api.example.com:4317")
    .timeout(Duration::from_secs(10))
    .build()
    .await?;
```

### 2. 初始化客户端

在使用客户端之前，必须调用 `initialize()`：

```rust
client.initialize().await?;
```

### 3. 优雅关闭

在程序退出前，调用 `shutdown()` 来优雅关闭：

```rust
client.shutdown().await?;
```

### 4. 监控指标

定期检查客户端指标：

```rust
let metrics = client.get_metrics().await;
println!("总发送数据量: {}", metrics.total_data_sent);
```

---

## ⚠️ 注意事项

### 1. 初始化顺序

必须先初始化客户端才能使用：

```rust
// ❌ 错误：未初始化
let result = client.send(data).await?;  // 会返回错误

// ✅ 正确：先初始化
client.initialize().await?;
let result = client.send(data).await?;
```

### 2. 并发安全

客户端是并发安全的，可以在多个任务中使用：

```rust
let client = Arc::new(client);
let client1 = client.clone();
let client2 = client.clone();

tokio::spawn(async move {
    client1.send(data1).await?;
});

tokio::spawn(async move {
    client2.send(data2).await?;
});
```

---

## 📚 参考资源

### 相关文档

- [配置指南](./CONFIG_GUIDE_2025.md) - 客户端配置
- [错误处理指南](./ERROR_HANDLING_GUIDE_2025.md) - 错误处理
- [导出器指南](./EXPORTER_GUIDE_2025.md) - 导出器使用

### API 参考

- `OtlpClient` - 客户端结构体
- `OtlpClientBuilder` - 客户端构建器
- `TraceBuilder` - 追踪构建器
- `MetricBuilder` - 指标构建器
- `LogBuilder` - 日志构建器
- `ClientMetrics` - 客户端指标

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
