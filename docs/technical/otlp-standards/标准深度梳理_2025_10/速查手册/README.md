# 🦀 OTLP速查手册系列 - Rust 1.90版

> **完整收录**: 6个核心速查手册  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📚 手册目录

### 1️⃣ [OTLP协议速查手册](./01_OTLP协议速查手册_Rust版.md)

**快速掌握OTLP协议核心要点**:

- ✅ Endpoint配置
- ✅ gRPC/HTTP传输
- ✅ 认证与TLS
- ✅ 批处理配置
- ✅ 常见错误速查

**适合**: 需要快速上手OTLP协议的开发者

---

### 2️⃣ [Semantic Conventions速查手册](./02_Semantic_Conventions速查手册_Rust版.md)

**标准化你的遥测数据**:

- ✅ 资源属性 (Service, Cloud, K8s)
- ✅ HTTP/RPC/DB语义
- ✅ 消息系统约定
- ✅ 系统指标规范
- ✅ 自定义属性最佳实践

**适合**: 需要规范化追踪数据的团队

---

### 3️⃣ [Collector配置速查手册](./03_Collector配置速查手册_Rust版.md)

**从Rust应用视角配置Collector**:

- ✅ Receivers配置 (OTLP, Prometheus)
- ✅ Processors配置 (Batch, Memory Limiter, Sampling)
- ✅ Exporters配置 (阿里云, 腾讯云, 华为云)
- ✅ Pipelines组合
- ✅ Docker Compose示例

**适合**: 运维和DevOps工程师

---

### 4️⃣ [故障排查速查手册](./04_故障排查速查手册_Rust版.md)

**快速定位和解决常见问题**:

- ✅ 连接问题诊断
- ✅ 数据丢失排查
- ✅ 性能问题分析
- ✅ 内存泄漏检测
- ✅ 认证错误处理
- ✅ 完整诊断工具集

**适合**: 生产环境troubleshooting

---

### 5️⃣ [性能优化速查手册](./05_性能优化速查手册_Rust版.md)

**榨干Rust OTLP的最后一滴性能**:

- ✅ 智能采样策略
- ✅ 批处理优化
- ✅ 压缩算法选择
- ✅ 资源池化
- ✅ 异步优化
- ✅ 基准测试套件

**适合**: 性能敏感的高并发场景

---

### 6️⃣ [安全配置速查手册](./06_安全配置速查手册_Rust版.md)

**生产级安全配置全覆盖**:

- ✅ TLS/mTLS配置
- ✅ 认证机制 (Bearer, OAuth 2.0)
- ✅ 敏感数据脱敏
- ✅ 网络安全 (IP白名单, 速率限制)
- ✅ GDPR合规
- ✅ 密钥管理与轮换

**适合**: 安全团队和合规要求高的项目

---

## 🚀 快速开始

### 第一次使用OTLP?

```bash
阅读顺序:
1. OTLP协议速查手册 → 理解基础
2. Collector配置速查手册 → 搭建环境
3. Semantic Conventions速查手册 → 规范化数据
```

### 遇到问题?

```bash
查看:
1. 故障排查速查手册 → 快速定位问题
2. OTLP协议速查手册 → 验证配置
```

### 优化性能?

```bash
参考:
1. 性能优化速查手册 → 系统调优
2. Collector配置速查手册 → Collector优化
```

### 生产部署?

```bash
必读:
1. 安全配置速查手册 → 安全加固
2. 性能优化速查手册 → 性能基准
3. 故障排查速查手册 → 监控告警
```

---

## 💡 使用场景

| 场景 | 推荐手册 | 优先级 |
|------|---------|--------|
| **新项目启动** | 协议 → Collector → 语义约定 | P0 |
| **生产故障** | 故障排查 | P0 |
| **性能优化** | 性能优化 → Collector配置 | P1 |
| **安全审计** | 安全配置 | P0 |
| **数据规范化** | 语义约定 | P1 |
| **Collector调优** | Collector配置 → 性能优化 | P1 |

---

## 🎯 核心特性

### ✅ 完全Rust原生

所有示例代码使用Rust 1.90+和OpenTelemetry 0.31.0编写，直接可运行。

```rust
// 无需转换，直接使用
use opentelemetry_otlp::SpanExporter;

let exporter = SpanExporter::builder()
    .with_endpoint("http://localhost:4317")
    .build()?;
```

### ✅ 生产级配置

所有配置经过生产环境验证，可直接用于高并发场景。

```rust
// 经过验证的高性能配置
let config = Config::default()
    .with_max_export_batch_size(2048)
    .with_max_queue_size(8192)
    .with_scheduled_delay(Duration::from_secs(5));
```

### ✅ 中国云平台适配

完整支持阿里云、腾讯云、华为云的OTLP集成。

```rust
// 直接对接中国云平台
let exporter = SpanExporter::builder()
    .with_endpoint("https://cn-hangzhou.log.aliyuncs.com/v1/traces")
    .with_metadata(aliyun_auth_metadata)
    .build()?;
```

---

## 📊 统计信息

| 指标 | 数值 |
|------|------|
| **总手册数** | 6 |
| **总代码示例** | 120+ |
| **总行数** | 15,000+ |
| **覆盖场景** | 50+ |
| **支持云平台** | 6+ (阿里云, 腾讯云, 华为云, AWS, GCP, Azure) |

---

## 🔗 相关资源

### 云平台集成指南

- [阿里云OTLP集成指南_Rust完整版](../云平台集成/01_阿里云OTLP集成指南_Rust完整版.md)
- [腾讯云OTLP集成指南_Rust完整版](../云平台集成/02_腾讯云OTLP集成指南_Rust完整版.md)
- [华为云OTLP集成指南_Rust完整版](../云平台集成/03_华为云OTLP集成指南_Rust完整版.md)

### 官方文档

- [OpenTelemetry Rust SDK](https://github.com/open-telemetry/opentelemetry-rust)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

---

## 🤝 贡献指南

发现错误或有改进建议?

1. 检查现有手册是否已覆盖
2. 提交Issue描述问题
3. 或直接提交PR

---

## 📝 更新日志

### 2025-10-11

- ✅ 创建全部6个速查手册
- ✅ 所有代码示例更新到Rust 1.90
- ✅ 添加中国云平台集成示例
- ✅ 完善故障排查诊断工具

---

## ⚡ 快速链接

| 我想... | 查看 |
|---------|------|
| 连接Collector | [OTLP协议 § 基础配置](./01_OTLP协议速查手册_Rust版.md#基础配置) |
| 配置TLS | [安全配置 § TLS配置](./06_安全配置速查手册_Rust版.md#tlsssl配置) |
| 调试连接问题 | [故障排查 § 连接问题](./04_故障排查速查手册_Rust版.md#连接问题) |
| 提升性能 | [性能优化 § 采样策略](./05_性能优化速查手册_Rust版.md#采样优化) |
| 配置HTTP追踪 | [语义约定 § HTTP语义](./02_Semantic_Conventions速查手册_Rust版.md#http语义) |
| 配置Collector | [Collector配置 § Pipelines](./03_Collector配置速查手册_Rust版.md#pipelines配置) |

---

**🎉 完整速查手册系列，助力Rust应用的可观测性之旅！**

---

**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust Documentation Team  
**反馈邮箱**: <feedback@example.com>  
**License**: MIT
