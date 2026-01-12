# 配置管理指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

配置管理模块 (`crates/otlp/src/config.rs`) 提供了 OTLP 客户端的完整配置功能，支持编译时优化、运行时配置和多种传输协议。

---

## 🚀 快速开始

### 基本配置

```rust
use otlp::config::{OtlpConfig, OtlpConfigBuilder};

// 使用默认配置
let config = OtlpConfig::default();

// 使用构建器模式
let config = OtlpConfigBuilder::new()
    .endpoint("https://api.example.com:4317")
    .timeout(Duration::from_secs(10))
    .batch_size(1000)
    .build()?;
```

---

## 📖 详细说明

### 核心类型

#### OtlpConfig

主要的配置结构体，包含所有 OTLP 客户端配置选项。

**字段**:

- `endpoint`: 端点 URL
- `timeout`: 超时时间
- `batch_config`: 批处理配置
- `retry_config`: 重试配置
- `tls_config`: TLS 配置
- `auth_config`: 认证配置
- `transport_protocol`: 传输协议 (gRPC/HTTP/HTTP-Protobuf)
- `compression`: 压缩算法 (None/Gzip/Brotli/Zstd)

#### OtlpConfigBuilder

配置构建器，提供链式 API 来构建配置。

**方法**:

- `new() -> Self` - 创建新构建器
- `endpoint(url: impl Into<String>) -> Self` - 设置端点
- `timeout(duration: Duration) -> Self` - 设置超时
- `batch_size(size: usize) -> Self` - 设置批处理大小
- `build() -> Result<OtlpConfig>` - 构建配置

---

### 配置选项

#### 传输协议

```rust
use otlp::config::TransportProtocol;

let config = OtlpConfigBuilder::new()
    .transport_protocol(TransportProtocol::Grpc)  // gRPC
    // .transport_protocol(TransportProtocol::Http)  // HTTP/JSON
    // .transport_protocol(TransportProtocol::HttpProtobuf)  // HTTP/Protobuf
    .build()?;
```

#### 压缩算法

```rust
use otlp::config::Compression;

let config = OtlpConfigBuilder::new()
    .compression(Compression::Gzip)  // Gzip 压缩
    // .compression(Compression::Brotli)  // Brotli 压缩
    // .compression(Compression::Zstd)  // Zstd 压缩
    // .compression(Compression::None)  // 无压缩
    .build()?;
```

#### 批处理配置

```rust
use otlp::config::BatchConfig;
use std::time::Duration;

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_secs(5),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(200),
};

let config = OtlpConfigBuilder::new()
    .batch_config(batch_config)
    .build()?;
```

#### 重试配置

```rust
use otlp::config::RetryConfig;
use std::time::Duration;

let retry_config = RetryConfig {
    max_attempts: 3,
    initial_interval: Duration::from_millis(100),
    max_interval: Duration::from_secs(5),
    multiplier: 2.0,
};

let config = OtlpConfigBuilder::new()
    .retry_config(retry_config)
    .build()?;
```

#### TLS 配置

```rust
use otlp::config::TlsConfig;

let tls_config = TlsConfig {
    enabled: true,
    ca_cert_path: Some("/path/to/ca.crt".to_string()),
    client_cert_path: Some("/path/to/client.crt".to_string()),
    client_key_path: Some("/path/to/client.key".to_string()),
    insecure_skip_verify: false,
};

let config = OtlpConfigBuilder::new()
    .tls_config(tls_config)
    .build()?;
```

#### 认证配置

```rust
use otlp::config::AuthConfig;

let auth_config = AuthConfig {
    api_key: Some("your-api-key".to_string()),
    bearer_token: Some("your-bearer-token".to_string()),
    // 其他认证选项...
};

let config = OtlpConfigBuilder::new()
    .auth_config(auth_config)
    .build()?;
```

---

### 编译时常量

模块提供了多个编译时常量，用于编译时优化：

```rust
use otlp::config::{
    DEFAULT_BATCH_SIZE,
    DEFAULT_TIMEOUT,
    MAX_BATCH_SIZE,
    MIN_BATCH_SIZE,
    validate_batch_size,
    validate_timeout,
};

// 使用常量
let batch_size = DEFAULT_BATCH_SIZE;  // 1000

// 编译时验证
if validate_batch_size(batch_size) {
    // 批处理大小有效
}

// 运行时验证
if validate_timeout(Duration::from_secs(5)) {
    // 超时值有效
}
```

---

## 💡 示例代码

### 示例 1: 基本配置

```rust
use otlp::config::{OtlpConfig, OtlpConfigBuilder};
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfigBuilder::new()
        .endpoint("https://api.example.com:4317")
        .timeout(Duration::from_secs(10))
        .batch_size(1000)
        .build()?;

    println!("配置创建成功: {:?}", config);
    Ok(())
}
```

### 示例 2: 完整配置

```rust
use otlp::config::{OtlpConfigBuilder, TransportProtocol, Compression};
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfigBuilder::new()
        .endpoint("https://api.example.com:4317")
        .timeout(Duration::from_secs(10))
        .transport_protocol(TransportProtocol::Grpc)
        .compression(Compression::Gzip)
        .batch_size(512)
        .max_queue_size(2048)
        .build()?;

    println!("完整配置创建成功");
    Ok(())
}
```

### 示例 3: 环境变量配置

```rust
use otlp::config::OtlpConfigBuilder;
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let endpoint = env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "https://api.example.com:4317".to_string());

    let config = OtlpConfigBuilder::new()
        .endpoint(endpoint)
        .build()?;

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 使用构建器模式

推荐使用 `OtlpConfigBuilder` 来构建配置，它提供了类型安全和链式 API：

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("https://api.example.com:4317")
    .timeout(Duration::from_secs(10))
    .build()?;
```

### 2. 验证配置

在构建配置后，验证配置的有效性：

```rust
let config = OtlpConfigBuilder::new()
    .batch_size(5000)  // 可能超出限制
    .build()?;

// 配置构建器会自动验证
```

### 3. 使用编译时常量

对于固定值，使用编译时常量：

```rust
use otlp::config::DEFAULT_BATCH_SIZE;

let config = OtlpConfigBuilder::new()
    .batch_size(DEFAULT_BATCH_SIZE)
    .build()?;
```

### 4. 环境特定配置

根据环境（开发/测试/生产）使用不同的配置：

```rust
let config = match env::var("ENV").as_deref() {
    Ok("production") => OtlpConfigBuilder::new()
        .endpoint("https://prod-api.example.com:4317")
        .batch_size(1000)
        .build()?,
    Ok("staging") => OtlpConfigBuilder::new()
        .endpoint("https://staging-api.example.com:4317")
        .batch_size(500)
        .build()?,
    _ => OtlpConfigBuilder::new()
        .endpoint("http://localhost:4317")
        .batch_size(100)
        .build()?,
};
```

---

## ⚠️ 注意事项

### 1. 批处理大小限制

批处理大小必须在 `MIN_BATCH_SIZE` (10) 和 `MAX_BATCH_SIZE` (10000) 之间：

```rust
// ❌ 错误：超出限制
let config = OtlpConfigBuilder::new()
    .batch_size(20000)  // 超出 MAX_BATCH_SIZE
    .build()?;  // 会返回错误

// ✅ 正确：在限制范围内
let config = OtlpConfigBuilder::new()
    .batch_size(1000)  // 在限制范围内
    .build()?;
```

### 2. 超时时间限制

超时时间必须在 `MIN_TIMEOUT` (100ms) 和 `MAX_TIMEOUT` (60s) 之间：

```rust
// ❌ 错误：超出限制
let config = OtlpConfigBuilder::new()
    .timeout(Duration::from_secs(120))  // 超出 MAX_TIMEOUT
    .build()?;  // 会返回错误

// ✅ 正确：在限制范围内
let config = OtlpConfigBuilder::new()
    .timeout(Duration::from_secs(10))  // 在限制范围内
    .build()?;
```

### 3. 端点 URL 格式

端点 URL 必须包含协议和端口：

```rust
// ❌ 错误：缺少协议
let config = OtlpConfigBuilder::new()
    .endpoint("api.example.com:4317")  // 缺少协议
    .build()?;

// ✅ 正确：包含协议
let config = OtlpConfigBuilder::new()
    .endpoint("https://api.example.com:4317")  // 包含协议
    .build()?;
```

---

## 📚 参考资源

### 相关文档

- [错误处理指南](./ERROR_HANDLING_GUIDE_2025.md) - 配置错误处理
- [客户端指南](./CLIENT_GUIDE_2025.md) - 使用配置创建客户端
- [导出器指南](./EXPORTER_GUIDE_2025.md) - 导出器配置

### API 参考

- `OtlpConfig` - 配置结构体
- `OtlpConfigBuilder` - 配置构建器
- `TransportProtocol` - 传输协议枚举
- `Compression` - 压缩算法枚举
- `BatchConfig` - 批处理配置
- `RetryConfig` - 重试配置
- `TlsConfig` - TLS 配置
- `AuthConfig` - 认证配置

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
