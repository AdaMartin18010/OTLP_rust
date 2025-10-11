# ✅ Rust OTLP 最佳实践 Checklist

> **适用场景**: 生产环境部署前检查  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0+  
> **最后更新**: 2025年10月10日

---

## 📋 使用说明

本 Checklist 分为以下几个级别：

- 🔴 **P0 - 必须**: 生产环境必须满足
- 🟡 **P1 - 推荐**: 强烈推荐，影响稳定性和性能
- 🟢 **P2 - 可选**: 锦上添花，进一步优化

在每个检查项前打勾 ✅ 表示已完成。

---

## 📑 目录

- [✅ Rust OTLP 最佳实践 Checklist](#-rust-otlp-最佳实践-checklist)
  - [📋 使用说明](#-使用说明)
  - [📑 目录](#-目录)
  - [1. 🏗️ 架构设计](#1-️-架构设计)
    - [🔴 P0 - 必须](#-p0---必须)
    - [🟡 P1 - 推荐](#-p1---推荐)
    - [🟢 P2 - 可选](#-p2---可选)
  - [2. ⚙️ 配置管理](#2-️-配置管理)
    - [2.1 🔴 P0 - 必须](#21--p0---必须)
    - [2.2 🟡 P1 - 推荐](#22--p1---推荐)
    - [2.3 🟢 P2 - 可选](#23--p2---可选)
  - [3. 🔧 SDK 集成](#3--sdk-集成)
    - [3.1 🔴 P0 - 必须](#31--p0---必须)
    - [3.2 🟡 P1 - 推荐](#32--p1---推荐)
    - [3.3 🟢 P2 - 可选](#33--p2---可选)
  - [4. 📊 追踪 (Traces)](#4--追踪-traces)
    - [4.1 🔴 P0 - 必须](#41--p0---必须)
    - [4.2 🟡 P1 - 推荐](#42--p1---推荐)
    - [4.3 🟢 P2 - 可选](#43--p2---可选)
  - [5. 📈 指标 (Metrics)](#5--指标-metrics)
    - [5.1 🔴 P0 - 必须](#51--p0---必须)
    - [5.2 🟡 P1 - 推荐](#52--p1---推荐)
    - [5.3 🟢 P2 - 可选](#53--p2---可选)
  - [6. 📝 日志 (Logs)](#6--日志-logs)
    - [6.1 🔴 P0 - 必须](#61--p0---必须)
    - [6.2 🟡 P1 - 推荐](#62--p1---推荐)
    - [6.3 🟢 P2 - 可选](#63--p2---可选)
  - [7. 🎯 采样策略](#7--采样策略)
    - [7.1 🔴 P0 - 必须](#71--p0---必须)
    - [7.2 🟡 P1 - 推荐](#72--p1---推荐)
    - [7.3 🟢 P2 - 可选](#73--p2---可选)
  - [8. ⚡ 性能优化](#8--性能优化)
    - [8.1 🔴 P0 - 必须](#81--p0---必须)
    - [8.2 🟡 P1 - 推荐](#82--p1---推荐)
    - [8.3 🟢 P2 - 可选](#83--p2---可选)
  - [9. 🔒 安全加固](#9--安全加固)
    - [9.1 🔴 P0 - 必须](#91--p0---必须)
    - [9.2 🟡 P1 - 推荐](#92--p1---推荐)
    - [9.3 🟢 P2 - 可选](#93--p2---可选)
  - [10. 🧪 测试](#10--测试)
    - [10.1 🔴 P0 - 必须](#101--p0---必须)
    - [10.2 🟡 P1 - 推荐](#102--p1---推荐)
    - [10.3 🟢 P2 - 可选](#103--p2---可选)
  - [11. 📦 部署](#11--部署)
    - [11.1 🔴 P0 - 必须](#111--p0---必须)
    - [11.2 🟡 P1 - 推荐](#112--p1---推荐)
    - [11.3 🟢 P2 - 可选](#113--p2---可选)
  - [12. 🔍 监控和告警](#12--监控和告警)
    - [12.1 🔴 P0 - 必须](#121--p0---必须)
    - [12.2 🟡 P1 - 推荐](#122--p1---推荐)
    - [12.3 🟢 P2 - 可选](#123--p2---可选)
  - [📊 检查总结](#-检查总结)
    - [完成度统计](#完成度统计)
    - [风险评估](#风险评估)
    - [建议](#建议)
  - [🔗 参考资源](#-参考资源)

---

## 1. 🏗️ 架构设计

### 🔴 P0 - 必须

- [ ] **服务标识**
  - [ ] 每个服务都有唯一的 `service.name`
  - [ ] 设置 `service.version` 用于版本追踪
  - [ ] 配置 `service.namespace` 区分环境（dev/staging/prod）
  
  ```rust
  Resource::new(vec![
      KeyValue::new("service.name", "my-service"),
      KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
      KeyValue::new("service.namespace", "production"),
      KeyValue::new("deployment.environment", "prod"),
  ])
  ```

- [ ] **Collector 部署**
  - [ ] 使用 OpenTelemetry Collector 作为中间层（不要直接发送到后端）
  - [ ] Collector 配置高可用（至少 2 个实例）
  - [ ] 配置 Collector 的健康检查

- [ ] **容错机制**
  - [ ] 实现 Exporter 失败时的降级策略
  - [ ] 配置重试机制（指数退避）
  - [ ] 设置合理的超时时间

### 🟡 P1 - 推荐

- [ ] **资源属性标准化**
  - [ ] 使用 Semantic Conventions 标准属性
  - [ ] 添加 `host.name`, `host.id` 等基础设施信息
  - [ ] 设置 `cloud.provider`, `cloud.region` 等云环境信息

- [ ] **多环境支持**
  - [ ] 不同环境使用不同的 Collector 端点
  - [ ] 环境配置通过环境变量管理
  - [ ] 测试环境可以使用更高的采样率

### 🟢 P2 - 可选

- [ ] **服务网格集成**
  - [ ] 如使用 Istio/Linkerd，配置自动追踪注入
  - [ ] 验证 Envoy Proxy 的追踪配置

---

## 2. ⚙️ 配置管理

### 2.1 🔴 P0 - 必须

- [ ] **配置外部化**
  - [ ] OTLP 端点通过环境变量配置
  - [ ] 采样率可动态调整
  - [ ] 敏感信息（API Key）使用密钥管理系统
  
  ```rust
  let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
      .unwrap_or_else(|_| "http://localhost:4317".to_string());
  ```

- [ ] **配置验证**
  - [ ] 启动时验证 OTLP 配置正确性
  - [ ] 检查 Collector 连接可用性
  - [ ] 配置加载失败时提供明确错误信息

### 2.2 🟡 P1 - 推荐

- [ ] **配置热重载**
  - [ ] 支持动态调整采样率而无需重启
  - [ ] 使用配置管理系统（如 etcd, Consul）

- [ ] **配置模板**
  - [ ] 为不同服务类型提供配置模板
  - [ ] 文档化所有配置选项

### 2.3 🟢 P2 - 可选

- [ ] **配置即代码**
  - [ ] 使用 Terraform/Pulumi 管理 Collector 配置
  - [ ] 版本控制所有配置文件

---

## 3. 🔧 SDK 集成

### 3.1 🔴 P0 - 必须

- [ ] **依赖版本锁定**
  - [ ] 在 `Cargo.toml` 中使用精确版本或锁定主版本
  - [ ] 定期更新到最新稳定版
  
  ```toml
  opentelemetry = "0.31.0"  # 锁定版本
  opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
  ```

- [ ] **正确初始化顺序**
  - [ ] 在应用启动早期初始化 OpenTelemetry
  - [ ] 在应用关闭前调用 `shutdown()` 或 `force_flush()`

```rust
  // 初始化
  let provider = init_tracer()?;
  
  // 运行应用...
  
  // 清理
  provider.shutdown()?;
  ```

- [ ] **错误处理**
  - [ ] 处理 Tracer 初始化失败
  - [ ] Span 创建失败不应导致业务逻辑中断
  - [ ] 使用 `Result` 类型处理可能的错误

### 3.2 🟡 P1 - 推荐

- [ ] **使用批量导出器**
  - [ ] 避免同步导出（性能差）
  - [ ] 配置合理的批次大小和刷新间隔

```rust
  .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
  ```

- [ ] **Context 传播**
  - [ ] HTTP 客户端自动注入 Trace Context
  - [ ] HTTP 服务器自动提取 Trace Context
  - [ ] 使用 W3C Trace Context 格式

### 3.3 🟢 P2 - 可选

- [ ] **自定义传播器**
  - [ ] 支持多种 Context 传播格式（Baggage, B3 等）
  - [ ] 实现自定义传播逻辑

---

## 4. 📊 追踪 (Traces)

### 4.1 🔴 P0 - 必须

- [ ] **关键路径追踪**
  - [ ] 所有 HTTP 请求都有 Span
  - [ ] 所有 RPC 调用都有 Span
  - [ ] 所有数据库操作都有 Span
  - [ ] 所有消息队列操作都有 Span

- [ ] **Span 属性标准化**
  - [ ] 使用 Semantic Conventions 标准属性名
  - [ ] HTTP: `http.method`, `http.status_code`, `http.route`
  - [ ] DB: `db.system`, `db.operation`, `db.statement`
  - [ ] RPC: `rpc.system`, `rpc.service`, `rpc.method`

- [ ] **错误追踪**
  - [ ] 捕获所有异常并记录到 Span
  - [ ] 设置 Span 状态为 `Status::Error`
  - [ ] 添加 `exception.type`, `exception.message` 属性
  
  ```rust
  span.record_exception(&error);
  span.set_status(Status::error(error.to_string()));
  ```

- [ ] **SpanKind 正确设置**
  - [ ] HTTP 服务器: `SpanKind::Server`
  - [ ] HTTP 客户端: `SpanKind::Client`
  - [ ] 消息生产者: `SpanKind::Producer`
  - [ ] 消息消费者: `SpanKind::Consumer`
  - [ ] 内部操作: `SpanKind::Internal`

### 4.2 🟡 P1 - 推荐

- [ ] **Span 生命周期管理**
  - [ ] 使用 RAII 模式自动结束 Span
  - [ ] 避免忘记结束 Span
  
  ```rust
  // 推荐: Span 在作用域结束时自动结束
  {
      let _span = tracer.start("operation");
      // ... 业务逻辑
  } // Span 自动结束
  ```

- [ ] **Span 嵌套**
  - [ ] 正确建立父子 Span 关系
  - [ ] 使用 `with_parent_context()` 或 `Context::current()`

- [ ] **避免过度追踪**
  - [ ] 不要为每个小函数创建 Span
  - [ ] 关注业务关键路径
  - [ ] 避免追踪循环内部（批量操作）

### 4.3 🟢 P2 - 可选

- [ ] **Span 事件 (Events)**
  - [ ] 记录关键业务事件
  - [ ] 添加结构化事件属性

- [ ] **Span 链接 (Links)**
  - [ ] 跨 Trace 关联（批处理场景）
  - [ ] 异步任务关联

---

## 5. 📈 指标 (Metrics)

### 5.1 🔴 P0 - 必须

- [ ] **系统指标**
  - [ ] CPU 使用率
  - [ ] 内存使用率
  - [ ] 进程句柄数

- [ ] **业务指标**
  - [ ] 请求总数 (Counter)
  - [ ] 请求延迟分布 (Histogram)
  - [ ] 并发连接数 (Gauge)

- [ ] **指标命名规范**
  - [ ] 使用小写字母和下划线
  - [ ] 添加单位后缀（`_bytes`, `_seconds`, `_total`）
  - [ ] 使用 Semantic Conventions 标准名称

```rust
  let request_counter = meter
      .u64_counter("http_server_requests_total")
      .with_description("Total HTTP requests")
      .init();
  ```

### 5.2 🟡 P1 - 推荐

- [ ] **RED 指标**
  - [ ] Rate (请求速率)
  - [ ] Errors (错误率)
  - [ ] Duration (延迟分布)

- [ ] **USE 指标** (资源)
  - [ ] Utilization (利用率)
  - [ ] Saturation (饱和度)
  - [ ] Errors (错误)

- [ ] **标签管理**
  - [ ] 限制标签基数（避免高基数标签）
  - [ ] 使用有意义的标签名
  - [ ] 避免动态标签值（如 user_id）

### 5.3 🟢 P2 - 可选

- [ ] **自定义指标**
  - [ ] 业务KPI指标
  - [ ] SLO/SLA 相关指标

---

## 6. 📝 日志 (Logs)

### 6.1 🔴 P0 - 必须

- [ ] **结构化日志**
  - [ ] 使用 JSON 格式输出日志
  - [ ] 包含 `trace_id`, `span_id` 字段
  - [ ] 日志级别正确设置

```rust
  use tracing::{info, span};
  
  info!(
      trace_id = %span.context().trace_id(),
      span_id = %span.context().span_id(),
      "User logged in"
  );
  ```

- [ ] **关键操作日志**
  - [ ] 记录所有API请求/响应
  - [ ] 记录所有错误和异常
  - [ ] 记录认证/授权事件

- [ ] **敏感信息脱敏**
  - [ ] 不记录密码、Token
  - [ ] 脱敏用户身份信息
  - [ ] 脱敏支付信息

### 6.2 🟡 P1 - 推荐

- [ ] **日志关联**
  - [ ] 日志自动关联 Trace ID
  - [ ] 使用 `tracing-opentelemetry` 集成

- [ ] **日志采样**
  - [ ] 高频日志进行采样
  - [ ] 错误日志始终记录

### 6.3 🟢 P2 - 可选

- [ ] **日志聚合**
  - [ ] 集成 ELK/Loki
  - [ ] 配置日志保留策略

---

## 7. 🎯 采样策略

### 7.1 🔴 P0 - 必须

- [ ] **配置采样率**
  - [ ] 生产环境使用 1-10% 采样率
  - [ ] 测试环境可使用 100% 采样

```rust
  use opentelemetry_sdk::trace::Sampler;
  
  .with_config(
      trace::Config::default()
          .with_sampler(Sampler::TraceIdRatioBased(0.01)) // 1%
  )
  ```

- [ ] **错误始终采样**
  - [ ] 所有错误 Trace 都被采样
  - [ ] 配置 `ParentBased` 采样器

### 7.2 🟡 P1 - 推荐

- [ ] **智能采样**
  - [ ] 慢请求（P95+ 延迟）始终采样
  - [ ] 关键业务路径提高采样率

- [ ] **动态采样**
  - [ ] 根据负载动态调整采样率
  - [ ] 使用 Collector 的尾部采样功能

### 7.3 🟢 P2 - 可选

- [ ] **自定义采样器**
  - [ ] 基于用户ID采样（测试特定用户）
  - [ ] 基于HTTP header采样（调试模式）

---

## 8. ⚡ 性能优化

### 8.1 🔴 P0 - 必须

- [ ] **使用异步导出**
  - [ ] 避免同步阻塞
  - [ ] 使用 `rt-tokio` feature
  
  ```toml
  opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
  ```

- [ ] **批量导出配置**
  - [ ] `max_queue_size`: 2048-8192
  - [ ] `max_export_batch_size`: 512-2048
  - [ ] `scheduled_delay`: 1-5秒

- [ ] **资源限制**
  - [ ] 设置导出超时（5-10秒）
  - [ ] 限制内存使用
  - [ ] 配置最大队列长度

### 8.2 🟡 P1 - 推荐

- [ ] **零分配优化**
  - [ ] 使用 `Arc` 共享数据
  - [ ] 复用 buffer
  - [ ] 避免不必要的克隆

- [ ] **CPU 优化**
  - [ ] 使用 SIMD 加速（Arrow）
  - [ ] 启用 LTO 编译优化
  
  ```toml
  [profile.release]
  lto = true
  codegen-units = 1
  ```

### 8.3 🟢 P2 - 可选

- [ ] **Arrow 列式存储**
  - [ ] 使用 Arrow Flight 传输
  - [ ] 启用列式压缩

- [ ] **内存池**
  - [ ] 实现自定义内存分配器
  - [ ] 监控内存使用

---

## 9. 🔒 安全加固

### 9.1 🔴 P0 - 必须

- [ ] **TLS 加密**
  - [ ] 生产环境必须使用 TLS
  - [ ] 验证证书有效性

```rust
use tonic::transport::ClientTlsConfig;

  let tls = ClientTlsConfig::new()
      .ca_certificate(Certificate::from_pem(ca_cert))
      .domain_name("collector.example.com");
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
      .with_tls_config(tls)
        .build_span_exporter()?;
  ```

- [ ] **认证配置**
  - [ ] API Key 通过 Header 传递
  - [ ] 使用密钥管理系统存储凭据
  - [ ] 定期轮换密钥

- [ ] **数据脱敏**
  - [ ] SQL 语句脱敏（隐藏参数值）
  - [ ] HTTP Header 脱敏（Authorization, Cookie）
  - [ ] 敏感属性值脱敏

### 9.2 🟡 P1 - 推荐

- [ ] **最小权限原则**
  - [ ] 服务账户只有发送遥测数据权限
  - [ ] 使用 RBAC 控制访问

- [ ] **数据保留策略**
  - [ ] 定义数据保留期限
  - [ ] 自动清理过期数据

### 9.3 🟢 P2 - 可选

- [ ] **合规性**
  - [ ] GDPR 合规
  - [ ] 数据本地化需求

---

## 10. 🧪 测试

### 10.1 🔴 P0 - 必须

- [ ] **单元测试**
  - [ ] 测试 Tracer 初始化
  - [ ] 测试 Span 创建和属性设置
  - [ ] 使用 `opentelemetry::testing` 模块

```rust
#[cfg(test)]
mod tests {
      use opentelemetry::testing::trace::NoopTracer;
      
      #[test]
      fn test_span_creation() {
          let tracer = NoopTracer::new();
          let span = tracer.start("test");
          assert_eq!(span.span_context().is_valid(), false);
    }
}
```

- [ ] **集成测试**
  - [ ] 测试与 Collector 的连接
  - [ ] 验证 Span 数据正确导出
  - [ ] 测试错误场景

### 10.2 🟡 P1 - 推荐

- [ ] **性能测试**
  - [ ] 基准测试（Criterion）
  - [ ] 负载测试
  - [ ] 内存泄漏测试

- [ ] **E2E 测试**
  - [ ] 端到端追踪验证
  - [ ] 跨服务链路测试

### 10.3 🟢 P2 - 可选

- [ ] **混沌测试**
  - [ ] Collector 不可用场景
  - [ ] 网络分区场景

---

## 11. 📦 部署

### 11.1 🔴 P0 - 必须

- [ ] **容器化**
  - [ ] 使用多阶段构建减小镜像大小
  - [ ] 配置健康检查
  
  ```dockerfile
  FROM rust:1.90 as builder
  # ... 构建 ...
  
  FROM debian:bookworm-slim
  # ... 运行时 ...
  
  HEALTHCHECK --interval=30s --timeout=3s \
    CMD curl -f http://localhost:8080/health || exit 1
  ```

- [ ] **Kubernetes 配置**
  - [ ] 设置资源限制（CPU/Memory）
  - [ ] 配置 liveness 和 readiness 探针
  - [ ] 使用 ConfigMap 管理配置

- [ ] **环境变量**
  - [ ] `OTEL_EXPORTER_OTLP_ENDPOINT`
  - [ ] `OTEL_SERVICE_NAME`
  - [ ] `OTEL_TRACES_SAMPLER`

### 11.2 🟡 P1 - 推荐

- [ ] **服务网格**
  - [ ] 配置 Istio/Linkerd 自动追踪
  - [ ] 验证 sidecar 注入

- [ ] **自动扩缩容**
  - [ ] 配置 HPA（基于 CPU/内存）
  - [ ] 使用 KEDA（基于队列长度）

### 11.3 🟢 P2 - 可选

- [ ] **Helm Chart**
  - [ ] 打包为 Helm Chart
  - [ ] 参数化配置

---

## 12. 🔍 监控和告警

### 12.1 🔴 P0 - 必须

- [ ] **Exporter 健康监控**
  - [ ] 监控 Exporter 成功率
  - [ ] 监控导出延迟
  - [ ] 监控队列长度

- [ ] **关键告警**
  - [ ] Collector 不可用告警
  - [ ] Trace 丢失率过高告警
  - [ ] 内存使用过高告警

### 12.2 🟡 P1 - 推荐

- [ ] **仪表盘**
  - [ ] 服务拓扑图
  - [ ] 延迟分布图
  - [ ] 错误率趋势

- [ ] **SLO/SLA 监控**
  - [ ] P95/P99 延迟
  - [ ] 可用性百分比
  - [ ] 错误预算

### 12.3 🟢 P2 - 可选

- [ ] **成本监控**
  - [ ] 遥测数据量
  - [ ] Collector 资源消耗

---

## 📊 检查总结

### 完成度统计

- **P0 必须项**: _____ / 50
- **P1 推荐项**: _____ / 35
- **P2 可选项**: _____ / 20
- **总完成度**: _____ / 105

### 风险评估

- 🔴 **高风险**: P0 完成度 < 80%
- 🟡 **中风险**: P0 完成度 80-95%
- 🟢 **低风险**: P0 完成度 > 95%

### 建议

根据你的完成度，建议采取以下行动：

- **< 50%**: ⛔ 不建议生产部署，需要大量补充工作
- **50-80%**: ⚠️ 可以部署到测试环境，但需谨慎
- **> 80%**: ✅ 可以考虑生产部署，继续完善剩余项

---

## 🔗 参考资源

- [OpenTelemetry 官方最佳实践](https://opentelemetry.io/docs/concepts/best-practices/)
- [Rust OpenTelemetry 文档](https://docs.rs/opentelemetry/)
- [完整文档导航](../README.md)

---

**Checklist 版本**: v1.0  
**创建日期**: 2025年10月10日  
**适用范围**: 生产环境 Rust OTLP 部署

---

[🏠 返回主目录](../README.md) | [📚 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md) | [📖 学习路径](../20_学习路径导航/)
