# OTLP 1.9.0 规范对齐指南

> 本文档对齐 OpenTelemetry Protocol (OTLP) 1.9.0 规范（2025年11月发布）  
> 参考: https://github.com/open-telemetry/opentelemetry-proto/releases/tag/v1.9.0

## 1. OTLP 1.9.0 新特性概览

### 1.1 协议版本演进

| 版本 | 发布日期 | 关键变更 |
|------|---------|---------|
| 1.9.0 | 2025-11 | Profiles 信号稳定化，性能优化 |
| 1.8.0 | 2025-09 | 指标聚合改进，资源属性扩展 |
| 1.7.0 | 2025-05 | 日志信号 GA，上下文传播增强 |
| 1.5.0 | 2025-01 | 协议优化，压缩算法更新 |

### 1.2 核心变更

#### Profiles 信号支持
OTLP 1.9.0 将 Profiles（性能分析）信号提升为稳定状态：

```protobuf
// opentelemetry/proto/profiles/v1development/profiles.proto
message ProfilesData {
  // 资源信息
  opentelemetry.proto.resource.v1.Resource resource = 1;
  // 作用域 profiles
  repeated ScopeProfiles scope_profiles = 2;
}
```

#### 增强的资源属性
- 支持更长的属性键（512 bytes，之前 128 bytes）
- 支持更大的属性值（64 KiB，之前 256 bytes）
- 单个 span 支持最多 1024 个属性（之前 32 个）

## 2. OpenTelemetry Rust 0.31.0 对齐

### 2.1 API 变更总结

| 特性 | 0.28 及之前 | 0.29+ | 0.31.0 (当前) |
|------|------------|-------|--------------|
| Runtime | 显式传递 | 内部线程 | 内部线程 |
| Baggage | 任意类型 | ASCII 字符串 | ASCII 字符串 |
| Prometheus | 内置导出器 | OTLP+Collector | OTLP+Collector |
| 导出器接口 | `&mut self` | `&self` | `&self` |
| 资源构建 | 替换模式 | 累加模式 | 累加模式 |

### 2.2 推荐架构

```rust
// 现代 OpenTelemetry Rust 架构 (0.31.0)
use opentelemetry_sdk::trace::SdkTracerProvider;
use opentelemetry_otlp::SpanExporter;

// 1. 创建导出器
let exporter = SpanExporter::builder()
    .with_tonic()  // gRPC
    .with_endpoint("http://localhost:4317")
    .build()?;

// 2. 创建 Provider（无需显式 Runtime）
let provider = SdkTracerProvider::builder()
    .with_batch_exporter(exporter)  // 内部线程管理
    .with_resource(
        Resource::builder()
            .with_service_name("my-service")
            .build()
    )
    .build();

// 3. 设置全局 Provider
global::set_tracer_provider(provider.clone());

// 4. 获取 tracer
let tracer = global::tracer("my-component");

// 5. 关闭时刷新
provider.shutdown()?;
```

## 3. 最佳实践

### 3.1 Tracing 集成

推荐使用 `tracing` + `tracing-opentelemetry` 桥接模式：

```rust
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

// 初始化 tracing 订阅者
tracing_subscriber::registry()
    .with(tracing_subscriber::EnvFilter::from_default_env())
    .with(tracing_subscriber::fmt::layer())  // 控制台输出
    .with(tracing_opentelemetry::layer().with_tracer(tracer))  // OTLP 导出
    .init();

// 使用 tracing 宏
#[tracing::instrument]
async fn process_request(req: Request) -> Result<Response> {
    tracing::info!(request_id = %req.id, "Processing request");
    // ...
}
```

### 3.2 上下文传播

实现 W3C Trace Context 标准：

```rust
use opentelemetry::propagation::TextMapPropagator;
use opentelemetry_sdk::propagation::TraceContextPropagator;

// 设置全局传播器
global::set_text_map_propagator(TraceContextPropagator::new());

// 注入上下文到 HTTP 头
let mut headers = HeaderMap::new();
global::get_text_map_propagator(|propagator| {
    propagator.inject_context(&Context::current(), &mut HeaderInjector(&mut headers));
});

// 从 HTTP 头提取上下文
let parent_context = global::get_text_map_propagator(|propagator| {
    propagator.extract(&HeaderExtractor(&headers))
});
```

### 3.3 Baggage 使用

Baggage 值必须是 ASCII 字符串：

```rust
use opentelemetry::baggage::{Baggage, KeyValue};

// ✅ 正确：ASCII 字符串
let baggage = Baggage::new(vec![
    KeyValue::new("user_id", "12345"),
    KeyValue::new("tenant", "production"),
]);

// ❌ 错误：非 ASCII 字符
// KeyValue::new("用户", "张三");  // 会被忽略

// 复杂数据序列化为 JSON
let metadata = serde_json::json!({
    "permissions": ["read", "write"],
    "region": "us-east-1"
}).to_string();
let baggage = Baggage::new(vec![
    KeyValue::new("metadata", metadata),
]);
```

### 3.4 资源属性累加

```rust
// 基础资源
let base_resource = Resource::builder()
    .with_service_name("payment-service")
    .with_service_version("2.3.1")
    .build();

// 环境特定资源
let env_resource = Resource::builder()
    .with_attribute(KeyValue::new("deployment.environment", "production"))
    .with_attribute(KeyValue::new("host.name", hostname::get()?.to_string_lossy().to_string()))
    .build();

// K8s 资源
let k8s_resource = Resource::builder()
    .with_attribute(KeyValue::new("k8s.namespace.name", std::env::var("KUBERNETES_NAMESPACE").unwrap_or_default()))
    .with_attribute(KeyValue::new("k8s.pod.name", std::env::var("POD_NAME").unwrap_or_default()))
    .build();

// 合并（累加模式）
let tracer_provider = SdkTracerProvider::builder()
    .with_resource(base_resource)
    .with_resource(env_resource)
    .with_resource(k8s_resource)
    .build();
```

## 4. 导出器配置

### 4.1 gRPC (Tonic)

```rust
use opentelemetry_otlp::SpanExporter;

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(10))
    .build()?;
```

### 4.2 HTTP (Reqwest)

```rust
let exporter = SpanExporter::builder()
    .with_http()
    .with_endpoint("http://localhost:4318/v1/traces")
    .with_headers(HashMap::from([
        ("Authorization".to_string(), format!("Bearer {}", token)),
    ]))
    .build()?;
```

## 5. 迁移检查清单

- [x] OpenTelemetry 升级到 0.31.0
- [ ] 移除 async-std 依赖
- [ ] 更新导出器接口（`&mut self` → `&self`）
- [ ] 资源构建器改为累加模式
- [ ] Baggage 值转换为 ASCII 字符串
- [ ] 实现 tracing-opentelemetry 桥接
- [ ] 配置 W3C Trace Context 传播
- [ ] 添加 Profiles 信号支持
- [ ] 更新批处理处理器配置
- [ ] 验证 OTLP 1.9.0 兼容性

## 6. 参考资源

- [OpenTelemetry Rust Docs](https://opentelemetry.io/docs/languages/rust/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [opentelemetry-rust GitHub](https://github.com/open-telemetry/opentelemetry-rust)
- [opentelemetry-proto](https://github.com/open-telemetry/opentelemetry-proto)
