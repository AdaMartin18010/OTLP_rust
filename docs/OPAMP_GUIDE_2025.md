# OPAMP 协议指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

OPAMP (Open Agent Management Protocol) 模块 (`crates/otlp/src/opamp/`) 提供了完整的 OPAMP 实现，包括协议消息、配置管理、证书管理和二进制管理等功能。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::opamp::{OpampClient, OpampConfig, OpampCapabilities};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OpampConfig::new(
        "https://opamp.example.com:4320".to_string(),
        "agent-123".to_string(),
    )
    .with_capabilities(OpampCapabilities::all());

    let mut client = OpampClient::new(config)?;
    client.start().await?;

    // 使用客户端...

    client.stop().await?;
    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### OpampClient

OPAMP 客户端，用于与 OPAMP 服务器通信。

**方法**:

- `new(config: OpampConfig) -> Result<Self>` - 创建客户端
- `start() -> Result<()>` - 启动客户端
- `stop() -> Result<()>` - 停止客户端
- `is_connected() -> bool` - 检查连接状态

#### OpampConfig

OPAMP 客户端配置。

**字段**:

- `server_endpoint: String` - 服务器端点
- `agent_id: String` - Agent ID
- `capabilities: OpampCapabilities` - Agent 能力
- `tls_config: Option<TlsConfig>` - TLS 配置

**方法**:

- `new(server_endpoint: String, agent_id: String) -> Self` - 创建配置
- `with_capabilities(capabilities: OpampCapabilities) -> Self` - 设置能力
- `with_tls(tls_config: TlsConfig) -> Self` - 设置 TLS

#### OpampCapabilities

Agent 能力标识。

**方法**:

- `all() -> Self` - 所有能力
- `basic() -> Self` - 基础能力

#### GraduationStrategy

灰度策略，用于企业级灰度发布。

**方法**:

- `new(selector: LabelSelector) -> Self` - 创建策略
- `with_weight(weight: f64) -> Self` - 设置权重
- `with_rollback_window(window: Duration) -> Self` - 设置回滚窗口

---

## 💡 示例代码

### 示例 1: 基本客户端

```rust
use otlp::opamp::{OpampClient, OpampConfig, OpampCapabilities};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OpampConfig::new(
        "https://opamp.example.com:4320".to_string(),
        "agent-123".to_string(),
    )
    .with_capabilities(OpampCapabilities::basic());

    let mut client = OpampClient::new(config)?;
    client.start().await?;

    println!("客户端已连接: {}", client.is_connected());

    client.stop().await?;
    Ok(())
}
```

### 示例 2: 灰度策略

```rust
use otlp::opamp::{GraduationStrategy, LabelSelector};
use std::time::Duration;

fn create_graduation_strategy() -> GraduationStrategy {
    let selector = LabelSelector::new()
        .with_label("env".to_string(), "prod".to_string());

    GraduationStrategy::new(selector)
        .with_weight(0.1)  // 10% 灰度
        .with_rollback_window(Duration::from_secs(300))
}
```

### 示例 3: 证书管理

```rust
use otlp::opamp::CertificateManager;

async fn manage_certificates() -> Result<(), Box<dyn std::error::Error>> {
    let manager = CertificateManager::new(
        "/path/to/cert.pem".to_string(),
        "/path/to/key.pem".to_string(),
    )
    .with_ca_cert("/path/to/ca.pem".to_string());

    let cert = manager.load_certificates().await?;
    let key = manager.load_private_key().await?;

    // 验证证书
    let is_valid = manager.validate_certificate().await?;

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 使用能力标识

根据实际需求选择能力：

```rust
// 生产环境：使用所有能力
let capabilities = OpampCapabilities::all();

// 开发环境：使用基础能力
let capabilities = OpampCapabilities::basic();
```

### 2. TLS 配置

在生产环境中使用 TLS：

```rust
let tls_config = TlsConfig {
    ca_cert_path: Some("/path/to/ca.pem".to_string()),
    client_cert_path: Some("/path/to/client.pem".to_string()),
    client_key_path: Some("/path/to/client.key".to_string()),
    server_name: Some("opamp.example.com".to_string()),
    insecure_skip_verify: false,
};

let config = OpampConfig::new(endpoint, agent_id)
    .with_tls(tls_config);
```

### 3. 错误处理

始终处理连接错误：

```rust
match client.start().await {
    Ok(()) => println!("连接成功"),
    Err(e) => eprintln!("连接失败: {}", e),
}
```

---

## ⚠️ 注意事项

### 1. 连接状态

在使用客户端之前，检查连接状态：

```rust
if !client.is_connected() {
    client.start().await?;
}
```

### 2. 证书路径

确保证书文件路径正确：

```rust
// ❌ 错误：路径不存在
let manager = CertificateManager::new(
    "/nonexistent/cert.pem".to_string(),
    "/nonexistent/key.pem".to_string(),
);

// ✅ 正确：路径存在
let manager = CertificateManager::new(
    "/valid/path/cert.pem".to_string(),
    "/valid/path/key.pem".to_string(),
);
```

---

## 📚 参考资源

### 相关文档

- [OPAMP 规范](https://opentelemetry.io/docs/specs/opamp/)

### API 参考

- `OpampClient` - OPAMP 客户端
- `OpampConfig` - OPAMP 配置
- `OpampCapabilities` - Agent 能力
- `GraduationStrategy` - 灰度策略
- `CertificateManager` - 证书管理器
- `PackageManager` - 包管理器

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
