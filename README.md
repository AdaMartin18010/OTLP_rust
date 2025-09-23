# 🚀 OTLP Rust - 基于Rust 1.90的微服务可观测性平台

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/otlp.svg)](https://crates.io/crates/otlp)
[![Documentation](https://docs.rs/otlp/badge.svg)](https://docs.rs/otlp)
[![Microservices](https://img.shields.io/badge/microservices-ready-green.svg)](https://microservices.io/)
[![Service Mesh](https://img.shields.io/badge/service--mesh-istio%20%7C%20linkerd-blue.svg)](https://servicemesh.es/)

一个基于 **Rust 1.90** 最新语言特性的 **OpenTelemetry Protocol (OTLP)** 完整实现，专为现代微服务架构设计，支持云原生部署、服务网格集成和全面的可观测性解决方案。

## ✨ 核心特性

### 🚀 Rust 1.90 语言特性

- 🎯 **异步优先设计** - 利用 Rust 1.90 的 async/await 特性和改进的Trait Solver
- 🛡️ **类型安全** - 利用 Rust 1.90 的类型系统确保编译时安全性
- ⚡ **零拷贝优化** - 使用 Rust 1.90 的Pointer Provenance API优化性能
- 🔒 **并发安全** - 基于 Rust 1.90 的所有权系统实现无锁并发
- 🔧 **MSRV感知** - 支持 Cargo 1.90 的MSRV感知解析器
- ✅ **完全兼容** - 修复了所有编译错误，支持 gRPC 和 HTTP 传输协议

### 🌐 微服务架构支持

- 🏗️ **服务发现** - 集成 Consul、etcd、Kubernetes 等主流服务发现组件
- 🔄 **负载均衡** - 支持轮询、加权轮询、一致性哈希、最少连接等负载均衡策略
- 🌍 **服务网格** - 原生支持 Istio、Linkerd2、Envoy 等服务网格
- ☁️ **云原生** - 完整的 Kubernetes、Docker、Helm 集成支持
- 🔧 **配置管理** - 动态配置更新、配置中心集成、热重载
- 🛡️ **安全认证** - mTLS、OAuth2、JWT、Vault 等安全认证方案

### 📊 可观测性能力

- 🔍 **分布式追踪** - 基于 OTLP 的完整分布式追踪解决方案
- 📈 **指标监控** - 支持 Prometheus、Grafana 等主流监控系统
- 📝 **日志聚合** - 集成 ELK Stack、Fluentd 等日志系统
- 🚨 **智能告警** - 基于机器学习的异常检测和告警

### 🔧 高级功能

- 🗜️ **数据压缩** - 支持 Gzip、Brotli、Zstd、LZ4、Snappy 多种压缩算法
- 🔄 **智能重试** - 指数退避、熔断器、故障转移、限流器等高级重试策略
- 🔒 **安全认证** - 支持 OAuth2、JWT、Vault、mTLS 等安全认证方案
- ⚡ **性能优化** - 零拷贝传输、批量处理、连接池、缓存等性能优化机制
- 🧠 **AI/ML集成** - 智能服务调度、异常检测、预测性维护
- 🌐 **边缘计算** - 分布式边缘服务部署和管理

## 🏗️ 微服务架构设计

```text
┌───────────────────────────────────────────────────────────────────┐
│                    微服务应用层 (Application Layer)                │
├─────────────────┬─────────────────┬─────────────────┬─────────────┤
│   用户服务       │  订单服务       │   支付服务       │   通知服务   │
│  (User)         │  (Order)        │  (Payment)     │(Notification)│
└─────────────────┴─────────────────┴─────────────────┴─────────────┘
                                │
                    ┌─────────────────┐
                    │   服务网格层     │
                    │ (Service Mesh)  │
                    │                 │
                    │ • Istio         │
                    │ • Linkerd2      │
                    │ • Envoy Proxy   │
                    └─────────────────┘
                                │
┌───────────────────────────────────────────────────────────────────┐
│                    可观测性层 (Observability Layer)                │
├─────────────────┬─────────────────┬─────────────────┬─────────────┤
│   数据收集层     │   数据处理层     │   数据传输层     │   存储分析层 │
│  (Collection)   │  (Processing)   │  (Transport)    │ (Storage)   │
│                 │                 │                 │             │
│ • Traces        │ • 过滤/聚合      │ • gRPC/HTTP     │ • Jaeger    │
│ • Metrics       │ • 批处理        │ • 压缩传输      │ • Prometheus│
│ • Logs          │ • 采样控制      │ • 重试机制      │ • ELK Stack │
└─────────────────┴─────────────────┴─────────────────┴─────────────┘
                                │
┌───────────────────────────────────────────────────────────────────┐
│                    基础设施层 (Infrastructure Layer)               │
├─────────────────┬─────────────────┬─────────────────┬─────────────┤
│  容器编排        │   服务发现      │   配置管理       │   安全认证   │
│ (Orchestration) │ (Discovery)     │ (Configuration) │ (Security)  │
│                 │                 │                 │             │
│ • Kubernetes    │ • Consul        │ • etcd          │ • Vault     │
│ • Docker        │ • Eureka        │ • ConfigMap     │ • OAuth2    │
│ • Helm          │ • DNS           │ • Secret        │ • JWT       │
└─────────────────┴─────────────────┴─────────────────┴─────────────┘
```

## 🚀 快速开始

### 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
```

### 基本使用

```rust
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use otlp::data::{LogSeverity, StatusCode};
use otlp::config::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP 配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("my-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 创建并初始化客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("duration", 150.0)
        .with_status(StatusCode::Ok, Some("操作成功".to_string()))
        .finish()
        .await?;
    
    println!("追踪数据发送结果: 成功 {} 条", result.success_count);
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

## 📚 使用示例

### 批量发送

```rust
// 批量发送数据
let mut batch_data = Vec::new();

for i in 0..100 {
    let trace_data = TelemetryData::trace(format!("operation-{}", i))
        .with_attribute("batch_id", "batch-001")
        .with_attribute("operation_index", i.to_string());
    
    batch_data.push(trace_data);
}

let result = client.send_batch(batch_data).await?;
println!("批量发送结果: 成功 {} 条", result.success_count);
```

### 异步并发发送

```rust
// 异步并发发送
let mut futures = Vec::new();

for i in 0..10 {
    let client_clone = client.clone();
    let future = tokio::spawn(async move {
        client_clone.send_trace(format!("async-operation-{}", i)).await?
            .with_attribute("async", "true")
            .finish()
            .await
    });
    futures.push(future);
}

// 等待所有异步操作完成
for future in futures {
    let result = future.await??;
    println!("异步操作结果: 成功 {} 条", result.success_count);
}
```

### 高级配置

```rust
use otlp::config::{Compression, BatchConfig, RetryConfig};

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_millis(5000),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(5000),
};

let retry_config = RetryConfig {
    max_retries: 5,
    initial_retry_delay: Duration::from_millis(1000),
    max_retry_delay: Duration::from_secs(30),
    retry_delay_multiplier: 2.0,
    randomize_retry_delay: true,
};

let config = OtlpConfig::default()
    .with_endpoint("https://api.example.com/otlp")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_api_key("your-api-key")
    .with_tls(true)
    .with_sampling_ratio(0.1)
    .with_batch_config(batch_config)
    .with_retry_config(retry_config)
    .with_resource_attribute("environment", "production")
    .with_resource_attribute("region", "us-west-2");
    // 采样与多租户限流
    let config = config
        .with_sampling_ratio(0.2)
        .with_error_sampling_floor(0.8) // 错误优先，错误Span至少80%采样
        .with_tenant_id_key("tenant.id") // 从资源属性读取租户ID
        .with_per_tenant_token_bucket(100, 50) // 每租户令牌桶：容量100，每秒补充50
        .with_audit_enabled(true);
```

## 🔧 配置选项

### 传输协议

- **gRPC** - 高性能二进制协议，支持流式传输
- **HTTP/JSON** - 基于 HTTP 的 JSON 格式传输
- **HTTP/Protobuf** - 基于 HTTP 的 Protobuf 格式传输

### 压缩算法

- **Gzip** - 标准 gzip 压缩
- **Brotli** - Google 开发的压缩算法
- **Zstd** - Facebook 开发的高性能压缩算法

### 批处理配置

- 批处理大小控制
- 超时时间设置
- 队列大小限制
- 调度间隔配置

### 重试机制

- 指数退避算法
- 最大重试次数
- 随机化延迟
- 可重试错误识别

## 📊 性能特性

### 异步处理

- 基于 Tokio 异步运行时
- 支持高并发数据处理
- 非阻塞 I/O 操作
- 异步批处理机制

### 内存优化

- 零拷贝数据传输
- 高效的内存管理
- 自动垃圾回收
- 内存池技术

### 网络优化

- 连接池管理
- 自动重连机制
- 压缩传输
- 负载均衡

## 🧪 测试和基准测试

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_client_creation

# 运行集成测试
cargo test --test integration
```

### 运行基准测试

```bash
# 运行性能基准测试
cargo bench

# 运行特定基准测试
cargo bench batch_trace_send
```

### 集成测试

```bash
# 启动测试服务器
docker run -p 4318:4318 otel/opentelemetry-collector

# 启用端到端(E2E)集成测试（HTTP 4318）
# Windows PowerShell
$env:OTLP_E2E=1; cargo test --test integration_tests | cat
# Linux/macOS bash/zsh
OTLP_E2E=1 cargo test --test integration_tests | cat
```

#### CI 中的 E2E

- 已提供 GitHub Actions 工作流 `.github/workflows/e2e.yml`：自动拉起 OpenTelemetry Collector（HTTP 4318），运行 `integration_tests`。

### gRPC/HTTP 切换

- 通过环境变量 `OTLP_PROTOCOL=grpc` 切换到 gRPC（Collector 默认端口 4317），不设置则使用 HTTP（端口 4318）。

### 审计钩子用法

```rust
use std::sync::Arc;
use otlp::OtlpClient;
// 客制化File/HTTP审计钩子在 otlp::client 模块中
use otlp::client::{FileAuditHook, HttpAuditHook};

let client: OtlpClient = /* ... */;
client.set_audit_hook(Arc::new(FileAuditHook::new("audit.log"))).await;
// 或
client.set_audit_hook(Arc::new(HttpAuditHook::new("https://audit.example.com/ingest"))).await;
```

## 📖 文档

### 📚 完整文档体系

#### 🏗️ 微服务架构设计1

- [Rust 1.90 微服务架构设计指南](docs/07_Rust_1.90_微服务架构设计/README.md)
- [服务发现与注册中心](docs/07_Rust_1.90_微服务架构设计/01_核心组件设计/服务发现与注册中心.md)
- [OTLP分布式追踪](docs/07_Rust_1.90_微服务架构设计/05_监控与可观测性/OTLP分布式追踪.md)
- [Rust 1.90语言特性应用](docs/07_Rust_1.90_微服务架构设计/00_架构总览/Rust_1.90语言特性应用.md)

#### 📊 可观测性解决方案

- [分布式追踪实现](docs/02_形式论证与证明体系/分布式追踪视角OTLP完整分析报告.md)
- [指标监控与告警](docs/05_实践应用/部署运维/监控告警.md)
- [日志聚合与分析](docs/08_部署运维指南/README.md)

#### 🔧 技术实现指南

- [API 文档](https://docs.rs/otlp)
- [基础使用指南](docs/05_实践应用/使用示例/基础使用.md)
- [高级配置](docs/05_实践应用/使用示例/高级配置.md)
- [企业级集成](docs/05_实践应用/企业集成/企业级集成迁移指南.md)

#### 🌐 2025年最新技术文档

- [OTLP国际标准深度对标](docs/01_标准规范与对标/OTLP_2025年9月最新规范全面对标分析.md)
- [Rust 1.90语言特性应用](docs/07_Rust_1.90_微服务架构设计/00_架构总览/Rust_1.90语言特性应用.md)
- [服务发现与注册中心](docs/07_Rust_1.90_微服务架构设计/01_核心组件设计/服务发现与注册中心.md)
- [OTLP分布式追踪](docs/07_Rust_1.90_微服务架构设计/05_监控与可观测性/OTLP分布式追踪.md)
- [同步异步控制流分析](otlp/docs/sync_async/OTLP_SYNC_ASYNC_CONTROL_FLOW_2025.md)
- [算法和设计模式](otlp/docs/algorithms/OTLP_ALGORITHMS_DESIGN_PATTERNS_2025.md)
- [采样控制和动态调整](otlp/docs/sampling/OTLP_SAMPLING_CONTROL_2025.md)
- [递归和调度组合](otlp/docs/advanced/OTLP_RECURSIVE_MIXED_SCHEDULING_2025.md)

## 🤝 贡献指南

1. Fork 项目
2. 创建特性分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 打开 Pull Request

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双重许可证。详情请参阅 [LICENSE](LICENSE) 文件。

## 🙏 致谢

- [OpenTelemetry](https://opentelemetry.io/) - 提供 OTLP 协议标准
- [Rust社区](https://www.rust-lang.org/community) - 提供优秀的语言和工具
- [Tokio](https://tokio.rs/) - 提供异步运行时
- [Tonic](https://github.com/hyperium/tonic) - 提供 gRPC 实现

## 📞 支持

如果您遇到问题或有任何建议，请：

1. 查看 [Issues](https://github.com/your-repo/otlp-rust/issues)
2. 创建新的 Issue
3. 联系维护者

---

**注意**: 这是一个演示项目，展示了如何使用 Rust 1.90 的语言特性实现 OTLP 协议。在生产环境中使用前，请进行充分的测试和性能评估。
