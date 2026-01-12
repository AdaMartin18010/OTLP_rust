# OTLP 传输层使用指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

OTLP 传输层模块 (`transport.rs`) 提供了 OpenTelemetry Protocol (OTLP) 的数据传输实现，支持多种传输协议，包括 gRPC 和 HTTP。该模块利用 Rust 1.90+ 的异步特性，实现了高性能、可扩展的数据传输层。

### 核心功能

- **多协议支持**: 支持 gRPC、HTTP 和 HTTP/Protobuf 协议
- **异步传输**: 基于 `tokio` 的异步 I/O，提供高性能数据传输
- **连接管理**: 自动管理连接池和连接状态
- **错误处理**: 完善的错误处理和重试机制
- **超时控制**: 可配置的请求超时时间

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::config::{OtlpConfig, TransportProtocol};
use otlp::transport::{Transport, TransportFactory};
use otlp::data::TelemetryData;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    // 创建传输实例
    let transport = TransportFactory::create(config).await?;

    // 发送遥测数据
    let data = vec![/* TelemetryData */];
    transport.send(data).await?;

    Ok(())
}
```

---

## 📖 详细说明

### Transport Trait

`Transport` trait 定义了传输层的核心接口：

```rust
#[async_trait]
pub trait Transport: Send + Sync {
    /// 发送遥测数据批次
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()>;

    /// 发送单个遥测数据
    async fn send_single(&self, data: TelemetryData) -> Result<()>;

    /// 检查连接状态
    async fn is_connected(&self) -> bool;

    /// 关闭连接
    async fn close(&self) -> Result<()>;

    /// 获取传输协议
    fn protocol(&self) -> TransportProtocol;
}
```

### GrpcTransport

gRPC 传输实现，用于高性能的二进制数据传输。

#### 创建实例

```rust
use otlp::transport::GrpcTransport;
use otlp::config::{OtlpConfig, TransportProtocol};

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc);

let transport = GrpcTransport::new(config).await?;
```

#### 发送数据

```rust
// 发送批次数据
let data = vec![telemetry_data1, telemetry_data2];
transport.send(data).await?;

// 发送单个数据
transport.send_single(telemetry_data).await?;
```

### HttpTransport

HTTP 传输实现，用于基于 JSON 的数据传输。

#### 创建实例

```rust
use otlp::transport::HttpTransport;
use otlp::config::{OtlpConfig, TransportProtocol};

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4318")
    .with_protocol(TransportProtocol::Http);

let transport = HttpTransport::new(config).await?;
```

### TransportFactory

传输工厂用于根据配置自动创建合适的传输实例。

```rust
use otlp::transport::TransportFactory;
use otlp::config::{OtlpConfig, TransportProtocol};

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc);

let transport = TransportFactory::create(config).await?;
```

### TransportPool

传输池用于管理多个传输实例，实现负载均衡。

```rust
use otlp::transport::{TransportPool, GrpcTransport};
use otlp::config::{OtlpConfig, TransportProtocol};

let mut pool = TransportPool::new();

// 添加传输实例
let config1 = OtlpConfig::default()
    .with_endpoint("http://endpoint1:4317")
    .with_protocol(TransportProtocol::Grpc);
let transport1 = GrpcTransport::new(config1).await?;
pool.add_transport(Box::new(transport1));

// 获取下一个传输实例（轮询）
if let Some(transport) = pool.get_next() {
    transport.send(data).await?;
}
```

---

## 💡 示例代码

### 示例 1: 使用 gRPC 传输

```rust
use otlp::config::{OtlpConfig, TransportProtocol};
use otlp::transport::{Transport, GrpcTransport};
use otlp::data::TelemetryData;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置 gRPC 传输
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_timeout(Duration::from_secs(30));

    // 创建传输实例
    let transport = GrpcTransport::new(config).await?;

    // 检查连接状态
    if transport.is_connected().await {
        println!("连接已建立");
    }

    // 发送数据
    let telemetry_data = TelemetryData::new(/* ... */);
    transport.send_single(telemetry_data).await?;

    // 关闭连接
    transport.close().await?;

    Ok(())
}
```

### 示例 2: 使用 HTTP 传输

```rust
use otlp::config::{OtlpConfig, TransportProtocol};
use otlp::transport::{Transport, HttpTransport};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置 HTTP 传输
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4318")
        .with_protocol(TransportProtocol::Http);

    // 创建传输实例
    let transport = HttpTransport::new(config).await?;

    // 发送批次数据
    let data = vec![
        TelemetryData::new(/* ... */),
        TelemetryData::new(/* ... */),
    ];
    transport.send(data).await?;

    Ok(())
}
```

### 示例 3: 使用传输工厂

```rust
use otlp::config::{OtlpConfig, TransportProtocol};
use otlp::transport::{Transport, TransportFactory};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 根据配置自动选择传输协议
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    // 工厂自动创建合适的传输实例
    let transport = TransportFactory::create(config).await?;

    // 使用传输实例
    println!("协议: {:?}", transport.protocol());
    transport.send(data).await?;

    Ok(())
}
```

### 示例 4: 使用传输池实现负载均衡

```rust
use otlp::transport::{TransportPool, GrpcTransport};
use otlp::config::{OtlpConfig, TransportProtocol};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut pool = TransportPool::new();

    // 添加多个传输实例
    for i in 1..=3 {
        let config = OtlpConfig::default()
            .with_endpoint(format!("http://endpoint{}:4317", i))
            .with_protocol(TransportProtocol::Grpc);
        let transport = GrpcTransport::new(config).await?;
        pool.add_transport(Box::new(transport));
    }

    // 轮询使用传输实例
    for _ in 0..10 {
        if let Some(transport) = pool.get_next() {
            transport.send(data.clone()).await?;
        }
    }

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 选择合适的传输协议

- **gRPC**: 适用于高性能、低延迟的场景，支持流式传输
- **HTTP**: 适用于简单部署、防火墙友好的场景

### 2. 配置超时时间

```rust
let config = OtlpConfig::default()
    .with_timeout(Duration::from_secs(30)); // 设置 30 秒超时
```

### 3. 使用连接池

对于高并发场景，使用 `TransportPool` 管理多个连接：

```rust
let mut pool = TransportPool::new();
// 添加多个传输实例
// 轮询使用以实现负载均衡
```

### 4. 错误处理

```rust
match transport.send(data).await {
    Ok(()) => println!("发送成功"),
    Err(e) => {
        eprintln!("发送失败: {}", e);
        // 实现重试逻辑
    }
}
```

### 5. 连接状态检查

在发送数据前检查连接状态：

```rust
if transport.is_connected().await {
    transport.send(data).await?;
} else {
    // 重新建立连接
}
```

---

## ⚠️ 注意事项

### 1. 协议选择

- gRPC 需要服务器支持 gRPC 协议
- HTTP 使用 JSON 格式，数据量较大
- HTTP/Protobuf 结合了 HTTP 的简单性和 Protobuf 的紧凑性

### 2. 超时设置

- 超时时间过短可能导致请求失败
- 超时时间过长可能导致资源占用
- 建议根据网络环境调整超时时间

### 3. 连接管理

- 传输实例会自动管理连接生命周期
- 不需要手动关闭连接（除非明确需要）
- 连接池中的连接会自动复用

### 4. 错误处理

- 网络错误会自动转换为 `TransportError`
- 服务器错误会包含状态码和错误信息
- 序列化错误会包含详细的错误原因

---

## 🔧 故障排查

### 问题 1: 连接失败

**症状**: `TransportError::Connection`

**解决方案**:

- 检查端点 URL 是否正确
- 检查网络连接
- 检查防火墙设置
- 验证服务器是否运行

### 问题 2: 超时错误

**症状**: `TransportError::Timeout`

**解决方案**:

- 增加超时时间
- 检查网络延迟
- 优化数据大小
- 使用批处理减少请求次数

### 问题 3: 序列化错误

**症状**: `TransportError::Serialization`

**解决方案**:

- 检查数据格式
- 验证 `TelemetryData` 结构
- 检查数据大小限制

---

## 📚 参考资源

### 相关文档

- [配置管理指南](CONFIG_GUIDE_2025.md) - 了解如何配置传输层
- [错误处理指南](ERROR_HANDLING_GUIDE_2025.md) - 了解错误处理机制
- [客户端指南](CLIENT_GUIDE_2025.md) - 了解如何使用客户端

### OpenTelemetry 规范

- [OTLP 规范](https://opentelemetry.io/docs/specs/otlp/)
- [gRPC 传输](https://opentelemetry.io/docs/specs/otlp/#otlpgrpc)
- [HTTP 传输](https://opentelemetry.io/docs/specs/otlp/#otlphttp)

### Rust 异步编程

- [Tokio 文档](https://tokio.rs/)
- [async-trait 文档](https://docs.rs/async-trait/)

---

## 📊 API 参考

### Transport Trait

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `send()` | 发送遥测数据批次 | `Result<()>` |
| `send_single()` | 发送单个遥测数据 | `Result<()>` |
| `is_connected()` | 检查连接状态 | `bool` |
| `close()` | 关闭连接 | `Result<()>` |
| `protocol()` | 获取传输协议 | `TransportProtocol` |

### GrpcTransport

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `new()` | 创建 gRPC 传输实例 | `Result<Self>` |

### HttpTransport

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `new()` | 创建 HTTP 传输实例 | `Result<Self>` |

### TransportFactory

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `create()` | 根据配置创建传输实例 | `Result<Box<dyn Transport>>` |

### TransportPool

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `new()` | 创建传输池 | `Self` |
| `add_transport()` | 添加传输实例 | `()` |
| `get_next()` | 获取下一个传输实例（轮询） | `Option<&mut dyn Transport>` |

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
