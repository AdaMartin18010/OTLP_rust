# OTLP Rust - Crate 快速参考

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: Crate 快速参考 - 一页纸速查手册，快速了解各 Crate 的职责和使用场景。

---

## 📦 核心 Crates (L1 - 基础层)

### `otlp-core`

**用途**: OTLP 核心数据模型和类型
**依赖**: 最小化 (serde, chrono, uuid)
**场景**: 需要 OTLP 类型定义但不需要网络传输时

```rust
use otlp_core::types::{TraceData, MetricData, LogData};

let trace = TraceData::new()
    .with_trace_id("abc123")
    .with_span_name("operation");
```

---

### `otlp-proto`

**用途**: Protocol Buffers 编解码
**依赖**: otlp-core, prost, opentelemetry-proto
**场景**: 自定义序列化/反序列化 OTLP 数据

```rust
use otlp_proto::codec::TraceCodec;

let codec = TraceCodec::new();
let bytes = codec.encode(&trace_data)?;
let decoded = codec.decode(&bytes)?;
```

---

### `otlp-transport`

**用途**: 网络传输层 (gRPC/HTTP)
**依赖**: otlp-core, otlp-proto, tokio, tonic/hyper
**场景**: 自定义 OTLP 客户端/服务器传输

```rust
use otlp_transport::grpc::GrpcClient;

let client = GrpcClient::builder()
    .endpoint("http://localhost:4317")
    .with_tls()
    .build()
    .await?;

client.send_traces(traces).await?;
```

---

## 🎯 功能 Crates (L2 - 功能层)

### `otlp` ⭐ (主 Crate)

**用途**: 完整的 OTLP 客户端实现
**依赖**: otlp-core, otlp-proto, otlp-transport, opentelemetry
**场景**: 最常用，功能完整的 OTLP 集成

```rust
use otlp::prelude::*;

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .with_performance_optimizations()
    .build()
    .await?;

let tracer = client.tracer("my-component");
let span = tracer.start("operation");
// 业务逻辑
drop(span);
```

**特性标志**:

```toml
[dependencies]
otlp = { version = "0.2", features = ["full"] }
# 或按需选择
otlp = { version = "0.2", features = ["client", "monitoring", "performance"] }
```

---

### `reliability`

**用途**: 统一可靠性框架
**依赖**: otlp-core (轻量), 可选 otlp (完整集成)
**场景**: 错误处理、容错机制、自动恢复

```rust
use reliability::prelude::*;

// 基础容错
let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));

circuit_breaker
    .with_retry(retry_policy)
    .execute(|| async {
        // 可能失败的操作
        Ok(())
    })
    .await?;

// 运行时监控
let health_checker = HealthChecker::new();
health_checker.check_system_health().await?;
```

**特性标志**:

```toml
[dependencies]
reliability = { version = "0.2", features = ["full"] }
# 或轻量级（无 OTLP 集成）
reliability = { version = "0.2", features = ["async", "fault-tolerance"] }
```

---

### `otlp-microservices`

**用途**: 微服务架构支持
**依赖**: otlp, reliability
**场景**: 服务发现、负载均衡、熔断

```rust
use otlp_microservices::prelude::*;

// 服务发现
let discovery = ConsulDiscovery::new("http://consul:8500");
let services = discovery.discover("my-service").await?;

// 负载均衡
let lb = WeightedRoundRobinLoadBalancer::new(services);
let endpoint = lb.select().await?;

// 带熔断的请求
let circuit_breaker = CircuitBreaker::default();
circuit_breaker.call(endpoint, request).await?;
```

---

## 🔗 整合 Crates (L3 - 整合层)

### `otlp-reliability-bridge`

**用途**: OTLP + Reliability 深度整合
**依赖**: otlp, reliability
**场景**: 统一可观测性和可靠性

```rust
use otlp_reliability_bridge::UnifiedObservability;

let unified = UnifiedObservability::builder()
    .with_otlp_endpoint("http://localhost:4317")
    .with_auto_recovery()
    .with_error_trace_correlation()
    .build()
    .await?;

// 自动记录追踪、错误和恢复
unified.execute_with_full_observability(|| async {
    // 业务逻辑
    // - 错误会自动转换为 spans
    // - 重试/熔断决策会记录到追踪
    // - 自动恢复会生成事件
    Ok(())
}).await?;
```

---

### `otlp-integrations`

**用途**: 外部系统集成
**依赖**: otlp + 各种客户端库
**场景**: Kubernetes、Prometheus、Grafana、Jaeger

```rust
use otlp_integrations::kubernetes::K8sExporter;
use otlp_integrations::prometheus::PrometheusExporter;

// Kubernetes 集成
let k8s_exporter = K8sExporter::new()
    .with_namespace("monitoring")
    .build()?;
k8s_exporter.export_as_configmap(config).await?;

// Prometheus 集成
let prom_exporter = PrometheusExporter::new()
    .with_port(9090)
    .start()?;
```

---

## 🛠️ 工具 Crates (L4 - 应用层)

### `otlp-cli`

**用途**: 命令行工具
**使用**:

```bash
# 发送测试追踪
otlp send trace --endpoint http://localhost:4317 --service my-service

# 验证配置
otlp validate config.toml

# 性能测试
otlp bench --duration 60s --rate 1000

# 查看监控数据
otlp monitor --endpoint http://localhost:4317
```

---

## 🎨 使用场景决策树

```text
需要什么？
│
├─ 只需要 OTLP 类型定义
│  └─> otlp-core
│
├─ 自定义序列化/传输
│  ├─> otlp-core + otlp-proto
│  └─> otlp-core + otlp-transport
│
├─ 完整的 OTLP 客户端
│  └─> otlp
│
├─ 只需要容错和错误处理（不依赖 OTLP）
│  └─> reliability (features = ["async", "fault-tolerance"])
│
├─ OTLP + 容错一起使用
│  ├─> otlp + reliability
│  └─> otlp-reliability-bridge (推荐，深度整合)
│
├─ 微服务架构
│  └─> otlp + reliability + otlp-microservices
│
├─ 与外部系统集成
│  └─> otlp + otlp-integrations
│
└─ 命令行工具
   └─> otlp-cli
```

---

## 📊 依赖大小对比

| Crate | 依赖项数量 | 编译时间 (估算) | 二进制大小 (估算) |
|-------|-----------|----------------|------------------|
| `otlp-core` | ~5 | < 10s | ~50KB |
| `otlp-proto` | ~10 | ~20s | ~500KB |
| `otlp-transport` | ~20 | ~30s | ~2MB |
| `otlp` | ~50 | ~60s | ~5MB |
| `reliability` | ~15 | ~30s | ~1MB |
| `otlp-microservices` | ~30 | ~40s | ~3MB |
| `otlp-reliability-bridge` | ~60 | ~70s | ~6MB |
| `otlp-integrations` | 按需 | 按需 | 按需 |

---

## 🚀 推荐组合

### 1️⃣ 最小化（库作者）

```toml
[dependencies]
otlp-core = "0.1"
```

适用于：库开发者，只需要类型定义

---

### 2️⃣ 基础应用

```toml
[dependencies]
otlp = { version = "0.2", features = ["client", "async"] }
```

适用于：简单应用，基础 OTLP 集成

---

### 3️⃣ 生产应用

```toml
[dependencies]
otlp = { version = "0.2", features = ["full"] }
reliability = { version = "0.2", features = ["full"] }
otlp-reliability-bridge = "0.1"
```

适用于：生产环境，需要完整的可观测性和可靠性

---

### 4️⃣ 微服务平台

```toml
[dependencies]
otlp = { version = "0.2", features = ["full"] }
reliability = { version = "0.2", features = ["full"] }
otlp-microservices = { version = "0.1", features = ["service-discovery", "load-balancing"] }
otlp-integrations = { version = "0.1", features = ["kubernetes", "prometheus"] }
```

适用于：完整的微服务架构

---

## 💡 性能提示

### 使用 SIMD 优化

```toml
[dependencies]
otlp = { version = "0.2", features = ["performance", "simd"] }
```

### 使用零拷贝

```toml
[dependencies]
otlp = { version = "0.2", features = ["performance", "zero-copy"] }
```

### 禁用不需要的特性

```toml
[dependencies]
otlp = { version = "0.2", default-features = false, features = ["client"] }
```

---

## 📚 更多资源

- **完整架构**: [CRATE_ARCHITECTURE_PLAN.md](CRATE_ARCHITECTURE_PLAN.md)
- **API 文档**: 运行 `cargo doc --open`
- **示例代码**: `otlp/examples/`, `reliability/examples/`
- **基准测试**: `cargo bench`

---

**版本**: 1.0
**更新**: 2025-10-20
