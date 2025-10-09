# MeterProvider - Rust 完整实现指南

## 📋 目录

- [MeterProvider - Rust 完整实现指南](#meterprovider---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [MeterProvider 的职责](#meterprovider-的职责)
    - [1. **全局配置**](#1-全局配置)
    - [2. **Meter 管理**](#2-meter-管理)
    - [3. **生命周期钩子**](#3-生命周期钩子)
  - [Rust 实现](#rust-实现)
    - [基础配置](#基础配置)
    - [生产级配置](#生产级配置)
      - [**多 Reader 支持**](#多-reader-支持)
      - [**自定义 View：直方图边界**](#自定义-view直方图边界)
    - [Resource 自动检测](#resource-自动检测)
    - [多租户支持](#多租户支持)
  - [生命周期管理](#生命周期管理)
    - [**优雅关闭**](#优雅关闭)
    - [**ForceFlush：确保导出**](#forceflush确保导出)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**可选增强**](#可选增强)
  - [总结](#总结)

---

## 核心概念

**MeterProvider** 是 OpenTelemetry Metrics SDK 的入口点，负责：

1. **全局配置管理**：Resource、MetricReader、View
2. **Meter 工厂**：创建和管理 Meter 实例
3. **生命周期管理**：初始化、运行时配置、优雅关闭

```text
┌─────────────────────────────────────────────────┐
│            MeterProvider                        │
│  ┌───────────────────────────────────────────┐  │
│  │ Resource: service.name, host.name, ...    │  │
│  ├───────────────────────────────────────────┤  │
│  │ MetricReader: OTLP/Prometheus/...         │  │
│  ├───────────────────────────────────────────┤  │
│  │ View: 自定义聚合、过滤                     │  │
│  └───────────────────────────────────────────┘  │
│                     ↓                           │
│     ┌─────────────────────────────────┐         │
│     │ Meter("my-service", "1.0.0")    │         │
│     └─────────────────────────────────┘         │
└─────────────────────────────────────────────────┘
```

---

## MeterProvider 的职责

### 1. **全局配置**

- **Resource**：描述服务的元数据（服务名、版本、主机名等）
- **MetricReader**：定义指标导出策略（推送 vs 拉取）
- **View**：自定义聚合规则、直方图边界、属性过滤

### 2. **Meter 管理**

- 根据 `instrumentation_scope`（库名 + 版本）创建 Meter
- 缓存 Meter 实例以避免重复创建
- 支持动态配置更新

### 3. **生命周期钩子**

- **初始化**：加载配置、启动 MetricReader
- **Shutdown**：刷新所有未导出的指标、清理资源
- **ForceFlush**：强制导出所有待处理的指标

---

## Rust 实现

### 基础配置

```rust
use opentelemetry::{
    global,
    metrics::{MeterProvider as _, Result},
    KeyValue,
};
use opentelemetry_sdk::{
    metrics::{MeterProvider, PeriodicReader, SdkMeterProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 创建 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    // 2. 创建 PeriodicReader（每 60 秒导出一次）
    let reader = PeriodicReader::builder(exporter)
        .with_interval(Duration::from_secs(60))
        .build();

    // 3. 定义 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);

    // 4. 创建 MeterProvider
    let meter_provider = SdkMeterProvider::builder()
        .with_resource(resource)
        .with_reader(reader)
        .build();

    // 5. 设置为全局 MeterProvider
    global::set_meter_provider(meter_provider.clone());

    // 6. 使用 Meter 创建指标
    let meter = global::meter("my-library");
    let counter = meter.u64_counter("requests_total").init();
    counter.add(1, &[KeyValue::new("http.method", "GET")]);

    // 7. 优雅关闭
    meter_provider.shutdown()?;
    Ok(())
}
```

**依赖 (Cargo.toml)**：

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"
tokio = { version = "1", features = ["full"] }
```

---

### 生产级配置

#### **多 Reader 支持**

```rust
use opentelemetry_sdk::metrics::{
    PeriodicReader, ManualReader, SdkMeterProvider,
};

async fn init_provider() -> Result<SdkMeterProvider> {
    // Reader 1: OTLP 推送（每 30 秒）
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .build_metrics_exporter(/* ... */)?;
    let otlp_reader = PeriodicReader::builder(otlp_exporter)
        .with_interval(Duration::from_secs(30))
        .build();

    // Reader 2: Prometheus 拉取（ManualReader）
    let prometheus_exporter = opentelemetry_prometheus::exporter()
        .with_registry(/* custom registry */)
        .build()?;
    let prometheus_reader = ManualReader::builder().build();

    // 同时使用两个 Reader
    let provider = SdkMeterProvider::builder()
        .with_resource(detect_resource())
        .with_reader(otlp_reader)
        .with_reader(prometheus_reader)
        .build();

    Ok(provider)
}
```

---

#### **自定义 View：直方图边界**

```rust
use opentelemetry_sdk::metrics::{
    Aggregation, Instrument, InstrumentKind, Stream, View,
};

fn create_custom_views() -> Vec<View> {
    vec![
        // 1. 为 http.server.duration 设置自定义直方图边界
        View::new(
            Instrument::new()
                .name("http.server.duration")
                .kind(InstrumentKind::Histogram),
            Stream::new()
                .name("http.server.duration")
                .aggregation(Aggregation::ExplicitBucketHistogram {
                    boundaries: vec![
                        0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0,
                    ],
                    record_min_max: true,
                }),
        ),
        
        // 2. 过滤高基数属性（只保留 http.method）
        View::new(
            Instrument::new()
                .name("http.server.request.count"),
            Stream::new()
                .attribute_keys(vec!["http.method".to_string()]),
        ),
    ]
}

let provider = SdkMeterProvider::builder()
    .with_view(create_custom_views())
    .with_reader(reader)
    .build();
```

---

### Resource 自动检测

```rust
use opentelemetry_sdk::Resource;
use opentelemetry_semantic_conventions as semconv;

fn detect_resource() -> Resource {
    // 1. 基础资源
    let mut resource = Resource::default();

    // 2. 从环境变量读取
    if let Ok(service_name) = std::env::var("OTEL_SERVICE_NAME") {
        resource = resource.merge(&Resource::new(vec![
            KeyValue::new(semconv::resource::SERVICE_NAME, service_name),
        ]));
    }

    // 3. 自动检测主机信息
    resource = resource.merge(&Resource::new(vec![
        KeyValue::new(
            semconv::resource::HOST_NAME,
            hostname::get()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        ),
        KeyValue::new(
            semconv::resource::OS_TYPE,
            std::env::consts::OS,
        ),
    ]));

    // 4. 检测容器环境（K8s/Docker）
    if let Ok(pod_name) = std::env::var("HOSTNAME") {
        resource = resource.merge(&Resource::new(vec![
            KeyValue::new("k8s.pod.name", pod_name),
        ]));
    }

    resource
}
```

**依赖**：

```toml
[dependencies]
opentelemetry-semantic-conventions = "0.16"
hostname = "0.4"
```

---

### 多租户支持

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

struct MultiTenantMeterProvider {
    providers: Arc<RwLock<HashMap<String, SdkMeterProvider>>>,
}

impl MultiTenantMeterProvider {
    fn new() -> Self {
        Self {
            providers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    async fn get_provider(&self, tenant_id: &str) -> Result<SdkMeterProvider> {
        // 1. 尝试从缓存获取
        {
            let providers = self.providers.read().unwrap();
            if let Some(provider) = providers.get(tenant_id) {
                return Ok(provider.clone());
            }
        }

        // 2. 创建新 Provider
        let resource = Resource::new(vec![
            KeyValue::new("tenant.id", tenant_id.to_string()),
        ]);

        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(format!("http://collector-{}.local:4317", tenant_id))
            .build_metrics_exporter(/* ... */)?;

        let reader = PeriodicReader::builder(exporter).build();

        let provider = SdkMeterProvider::builder()
            .with_resource(resource)
            .with_reader(reader)
            .build();

        // 3. 缓存 Provider
        {
            let mut providers = self.providers.write().unwrap();
            providers.insert(tenant_id.to_string(), provider.clone());
        }

        Ok(provider)
    }
}

// 使用示例
async fn handle_request(tenant_id: &str, multi_provider: &MultiTenantMeterProvider) -> Result<()> {
    let provider = multi_provider.get_provider(tenant_id).await?;
    let meter = provider.meter("tenant-service");
    let counter = meter.u64_counter("requests").init();
    counter.add(1, &[]);
    Ok(())
}
```

---

## 生命周期管理

### **优雅关闭**

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> Result<()> {
    let provider = init_meter_provider().await?;
    global::set_meter_provider(provider.clone());

    // 应用逻辑
    tokio::spawn(async {
        // 模拟业务逻辑
    });

    // 等待 SIGTERM/SIGINT
    signal::ctrl_c().await.expect("Failed to listen for Ctrl+C");
    println!("Shutting down gracefully...");

    // 强制刷新 + 关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    Ok(())
}
```

### **ForceFlush：确保导出**

```rust
use std::time::Duration;

async fn critical_operation(provider: &SdkMeterProvider) -> Result<()> {
    let meter = provider.meter("critical-ops");
    let counter = meter.u64_counter("critical_events").init();
    
    counter.add(1, &[KeyValue::new("type", "payment")]);
    
    // 立即导出（不等待周期性触发）
    provider.force_flush()?;
    
    Ok(())
}
```

---

## 最佳实践

### ✅ **推荐**

1. **全局单例**：使用 `global::set_meter_provider` 设置一次
2. **Resource 检测**：自动检测环境信息（K8s、云平台）
3. **View 优化**：
   - 为高频直方图设置合理边界
   - 过滤高基数属性（如 user_id）
4. **多 Reader**：同时支持推送（OTLP）和拉取（Prometheus）
5. **优雅关闭**：监听系统信号，调用 `shutdown()` 前先 `force_flush()`

### ❌ **避免**

1. **频繁创建 Provider**：应缓存和复用
2. **忘记调用 shutdown()**：可能导致数据丢失
3. **过度使用 ForceFlush**：会增加延迟，仅在关键路径使用
4. **忽略错误处理**：Exporter 失败时记录日志但不阻塞业务

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"          # OTLP 导出
opentelemetry-prometheus = "0.17"    # Prometheus 导出
tokio = { version = "1", features = ["full"] }
```

### **可选增强**

```toml
opentelemetry-semantic-conventions = "0.16"  # 语义约定
hostname = "0.4"                             # 主机名检测
```

---

## 总结

| 功能 | 实现方式 |
|------|---------|
| 全局配置 | `SdkMeterProvider::builder()` |
| OTLP 导出 | `PeriodicReader` + `opentelemetry_otlp` |
| Prometheus 导出 | `ManualReader` + `opentelemetry_prometheus` |
| 自定义聚合 | `View::new()` 配置 |
| Resource 检测 | `Resource::default()` + 环境变量 |
| 优雅关闭 | `force_flush()` + `shutdown()` |
| 多租户 | 为每个租户创建独立 Provider |

**下一步**：[02_Meter_Rust完整版.md](./02_Meter_Rust完整版.md) - 学习如何使用 Meter 创建指标
