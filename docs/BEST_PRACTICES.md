# OpenTelemetry Rust 最佳实践指南

**版本**: 1.0
**更新日期**: 2026-03-15
**适用版本**: Rust 1.94+, OTLP 1.10

---

## 📋 目录

- [OpenTelemetry Rust 最佳实践指南](#opentelemetry-rust-最佳实践指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心原则](#核心原则)
  - [命名规范](#命名规范)
    - [属性命名](#属性命名)
    - [命名空间约定](#命名空间约定)
    - [组织级命名](#组织级命名)
  - [资源属性](#资源属性)
    - [必需属性](#必需属性)
    - [推荐属性](#推荐属性)
  - [采样策略](#采样策略)
    - [采样器类型](#采样器类型)
    - [采样策略选择指南](#采样策略选择指南)
  - [性能优化](#性能优化)
    - [批处理配置](#批处理配置)
    - [属性大小限制](#属性大小限制)
    - [异步导出](#异步导出)
    - [内存管理](#内存管理)
  - [错误处理](#错误处理)
    - [错误记录](#错误记录)
    - [超时和重试](#超时和重试)
  - [安全最佳实践](#安全最佳实践)
    - [敏感数据处理](#敏感数据处理)
    - [PII 处理](#pii-处理)
    - [传输安全](#传输安全)
  - [生产环境检查清单](#生产环境检查清单)
    - [部署前检查](#部署前检查)
    - [运行时检查](#运行时检查)
    - [监控指标](#监控指标)
  - [参考资源](#参考资源)

---

## 概述

本指南提供 OpenTelemetry Rust 的最佳实践，帮助您构建可靠、高性能、可观测的应用程序。

### 核心原则

1. **一致性**: 遵循统一的命名和标注规范
2. **标准化**: 使用 OpenTelemetry 语义约定
3. **性能优先**: 避免在高频路径上产生开销
4. **安全**: 不在遥测数据中包含敏感信息

---

## 命名规范

### 属性命名

使用点号分隔的层级命名空间：

```rust
// ✅ 推荐
span.set_attribute("http.request.method", "GET");
span.set_attribute("http.response.status_code", 200);
span.set_attribute("db.system", "postgresql");
span.set_attribute("db.operation.name", "SELECT");

// ❌ 避免
span.set_attribute("http_method", "GET");
span.set_attribute("dbSystem", "postgresql");
```

### 命名空间约定

| 前缀 | 用途 | 示例 |
|------|------|------|
| `http.*` | HTTP 相关属性 | `http.request.method` |
| `db.*` | 数据库操作 | `db.system`, `db.operation.name` |
| `messaging.*` | 消息系统 | `messaging.system`, `messaging.operation.type` |
| `service.*` | 服务信息 | `service.name`, `service.version` |
| `deployment.*` | 部署环境 | `deployment.environment` |

### 组织级命名

建议为您的组织使用统一前缀：

```rust
// 组织级属性
span.set_attribute("mycompany.region", "us-east-1");
span.set_attribute("mycompany.team", "platform");

// 应用级属性
span.set_attribute("app.module", "payment");
span.set_attribute("app.feature", "checkout");
```

---

## 资源属性

### 必需属性

在生产环境中必须设置的资源属性：

```rust
use otlp::config::OtlpConfig;

let config = OtlpConfig::new()
    .with_resource_attribute("service.name", "checkout-service")
    .with_resource_attribute("service.version", "1.2.3")
    .with_resource_attribute("deployment.environment", "production")
    .with_resource_attribute("service.namespace", "ecommerce");
```

### 推荐属性

| 属性 | 说明 | 示例 |
|------|------|------|
| `service.name` | 服务唯一标识 | `checkout-api` |
| `service.version` | 部署版本 | `1.2.3` |
| `deployment.environment` | 环境名称 | `production`, `staging` |
| `service.namespace` | 逻辑分组 | `ecommerce` |
| `host.name` | 主机名 | `web-server-01` |
| `host.id` | 主机唯一ID | `i-1234567890abcdef0` |

---

## 采样策略

### 采样器类型

根据场景选择合适的采样策略：

```rust
use otlp::config::{OtlpConfig, SamplerType};

// 1. Always On - 开发/低流量服务
let config = OtlpConfig::new()
    .with_sampler(SamplerType::AlwaysOn);

// 2. Probabilistic - 生产环境适中流量
let config = OtlpConfig::new()
    .with_sampler(SamplerType::Probabilistic)
    .with_sampling_ratio(0.1); // 10% 采样

// 3. Rate Limiting - 高流量服务
let config = OtlpConfig::new()
    .with_sampler(SamplerType::RateLimiting)
    .with_rate_limit(100); // 每秒100条

// 4. Parent Based - 分布式系统
let config = OtlpConfig::new()
    .with_sampler(SamplerType::ParentBased)
    .with_sampling_ratio(0.1);
```

### 采样策略选择指南

| 场景 | 推荐策略 | 说明 |
|------|----------|------|
| 开发环境 | Always On | 捕获所有追踪 |
| 生产低流量 | Always On | < 100 RPS |
| 生产中等流量 | Probabilistic | 100-10000 RPS |
| 生产高流量 | Rate Limiting | > 10000 RPS |
| 分布式系统 | Parent Based | 尊重上游决策 |

---

## 性能优化

### 批处理配置

优化批处理参数以减少网络开销：

```rust
use otlp::config::{OtlpConfig, BatchConfig};

let batch_config = BatchConfig::new()
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(Duration::from_millis(5000));

let config = OtlpConfig::new()
    .with_batch_config(batch_config);
```

### 属性大小限制

避免在遥测数据中使用大属性值：

```rust
// ✅ 推荐 - 保持简洁
span.set_attribute("error.message", "Connection timeout");

// ❌ 避免 - 大属性值
span.set_attribute("error.stack_trace", full_stack_trace); // 可能超过1KB

// ✅ 推荐 - 截断或哈希
span.set_attribute("error.stack_trace_hash", hash(stack_trace));
```

### 异步导出

确保遥测导出不阻塞应用关键路径：

```rust
use otlp::exporter::OtlpExporter;

// 默认异步导出
let exporter = OtlpExporter::new(config);

// 配置异步通道
let config = OtlpConfig::new()
    .with_async_export(true)
    .with_export_queue_size(1024);
```

### 内存管理

避免在高频路径上分配内存：

```rust
use otlp::data::AttributeValue;

// ✅ 推荐 - 预分配属性
let attributes = [
    ("http.method", AttributeValue::String("GET".to_string())),
    ("http.route", AttributeValue::String("/api/users".to_string())),
];

// ❌ 避免 - 动态分配
let mut attrs = HashMap::new();
attrs.insert("http.method", AttributeValue::String("GET".to_string()));
```

---

## 错误处理

### 错误记录

确保异常被正确捕获并附加到跨度：

```rust
use otlp::client::TraceBuilder;
use std::panic;

async fn process_request() {
    let result = TraceBuilder::new("process_request", config.clone())
        .with_attribute("request.id", request_id)
        .finish()
        .await;

    match result {
        Ok(_) => tracing::info!("Request processed successfully"),
        Err(e) => {
            tracing::error!(error = %e, "Failed to process request");
            // 错误已自动附加到跨度
        }
    }
}
```

### 超时和重试

配置合理的超时和重试策略：

```rust
use otlp::config::OtlpConfig;
use std::time::Duration;

let config = OtlpConfig::new()
    .with_timeout(Duration::from_secs(10))
    .with_retry_policy(RetryPolicy::ExponentialBackoff {
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        max_retries: 3,
    });
```

---

## 安全最佳实践

### 敏感数据处理

**永远不要**在遥测数据中包含敏感信息：

```rust
// ❌ 永远不要这样做
span.set_attribute("user.password", password);
span.set_attribute("api.key", api_key);
span.set_attribute("token", jwt_token);

// ✅ 推荐做法
span.set_attribute("user.id", user_id); // 使用ID而非敏感信息
span.set_attribute("api.key_hash", hash(api_key)); // 使用哈希
span.set_attribute("token.valid", true); // 仅记录状态
```

### PII 处理

对个人身份信息(PII)进行脱敏：

```rust
// ✅ 推荐 - 脱敏处理
span.set_attribute("user.email_hash", hash_email(email));
span.set_attribute("user.phone_last4", phone.chars().rev().take(4).collect());

// ❌ 避免
span.set_attribute("user.email", "user@example.com");
span.set_attribute("user.phone", "+1234567890");
```

### 传输安全

使用 TLS 加密传输：

```rust
use otlp::config::{OtlpConfig, TransportProtocol, TlsConfig};

let config = OtlpConfig::new()
    .with_protocol(TransportProtocol::Grpc)
    .with_tls_config(TlsConfig::new()
        .with_cert_path("/path/to/cert.pem")
        .with_key_path("/path/to/key.pem"));
```

---

## 生产环境检查清单

### 部署前检查

- [ ] `service.name` 已设置且有意义的名称
- [ ] `deployment.environment` 区分 prod/staging/dev
- [ ] 采样策略适合流量规模
- [ ] 批处理参数已优化
- [ ] 不包含敏感数据（密码、令牌、PII）
- [ ] 错误处理完善
- [ ] 超时和重试已配置
- [ ] TLS 加密已启用
- [ ] 遥测导出正常工作（已验证）

### 运行时检查

- [ ] 内存使用稳定，无泄漏
- [ ] CPU 开销 < 5%
- [ ] 网络带宽使用合理
- [ ] 无错误日志堆积
- [ ] 采样率符合预期
- [ ] 追踪数据在收集器中可见

### 监控指标

```rust
// 监控 OpenTelemetry SDK 本身的指标
use otlp::monitoring::{MetricsCollector, MetricType};

let collector = MetricsCollector::new("otel_sdk");

// 记录导出延迟
collector.record_histogram(
    "otel.export_latency",
    export_duration.as_millis() as f64,
    &[],
);

// 记录导出错误
collector.record_counter(
    "otel.export_errors",
    1.0,
    &[("error.type", error_type)],
);

// 记录队列大小
collector.record_gauge(
    "otel.queue_size",
    queue_size as f64,
    &[],
);
```

---

## 参考资源

- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/concepts/semantic-conventions/)
- [OpenTelemetry Best Practices](https://opentelemetry.io/docs/concepts/best-practices/)
- [OpenTelemetry Rust API](https://docs.rs/opentelemetry/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)

---

**文档维护**: OTLP Rust Team
**最后更新**: 2026-03-15
