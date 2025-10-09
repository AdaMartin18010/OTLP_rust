# MetricReader - Rust 完整实现指南

## 📋 目录

- [MetricReader - Rust 完整实现指南](#metricreader---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Reader 类型](#reader-类型)
    - [**推送 vs 拉取**](#推送-vs-拉取)
  - [Rust 实现](#rust-实现)
    - [PeriodicReader 详解](#periodicreader-详解)
      - [**基础配置**](#基础配置)
      - [**高级配置：多 Exporter**](#高级配置多-exporter)
      - [**自适应间隔**](#自适应间隔)
    - [ManualReader 详解](#manualreader-详解)
      - [**Prometheus 集成**](#prometheus-集成)
      - [**自定义拉取端点**](#自定义拉取端点)
    - [多 Reader 配置](#多-reader-配置)
      - [**同时支持推送和拉取**](#同时支持推送和拉取)
  - [时间性语义](#时间性语义)
    - [**Cumulative（累计）**](#cumulative累计)
    - [**Delta（增量）**](#delta增量)
    - [**选择建议**](#选择建议)
  - [高级配置](#高级配置)
    - [**导出超时控制**](#导出超时控制)
    - [**导出失败重试**](#导出失败重试)
    - [**条件导出：按需触发**](#条件导出按需触发)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**HTTP 框架（拉取模式）**](#http-框架拉取模式)
  - [总结](#总结)

---

## 核心概念

**MetricReader** 负责从 SDK 读取指标数据并触发导出，定义了**推送 (Push)** 和**拉取 (Pull)** 两种模式：

```text
┌─────────────────────────────────────────────────┐
│            MeterProvider                        │
│  ┌───────────────────────────────────────────┐  │
│  │ Instrument 1: http.requests               │  │
│  │ Instrument 2: http.duration               │  │
│  │ Instrument 3: cpu.usage                   │  │
│  └───────────────────────────────────────────┘  │
│                     ↓                           │
│     ┌─────────────────────────────────┐         │
│     │ MetricReader (PeriodicReader)   │         │
│     │  - 每 60 秒自动收集              │         │
│     │  - 调用 MetricExporter 导出      │         │
│     └─────────────────────────────────┘         │
│                     ↓                           │
│     ┌─────────────────────────────────┐         │
│     │ MetricExporter (OTLP/Prometheus)│         │
│     └─────────────────────────────────┘         │
└─────────────────────────────────────────────────┘
```

**职责**：

1. **数据聚合**：收集所有 Instrument 的数据点
2. **触发导出**：周期性或按需调用 MetricExporter
3. **时间性管理**：定义 Cumulative（累计）或 Delta（增量）语义

---

## Reader 类型

| 类型 | 模式 | 使用场景 | 示例后端 |
|------|------|---------|---------|
| **PeriodicReader** | 推送 | 主动推送到远程后端 | OTLP、Jaeger、InfluxDB |
| **ManualReader** | 拉取 | 后端主动拉取 | Prometheus、自定义监控 |

### **推送 vs 拉取**

| 维度 | 推送（PeriodicReader） | 拉取（ManualReader） |
|------|----------------------|-------------------|
| **控制权** | SDK 控制导出时机 | 后端控制读取时机 |
| **网络流量** | 周期性主动发送 | 按需被动响应 |
| **高可用** | 需要后端持续可用 | 后端临时不可用不影响应用 |
| **延迟** | 固定延迟（如 60 秒） | 实时查询 |
| **典型后端** | OTLP Collector、云服务 | Prometheus、Grafana |

---

## Rust 实现

### PeriodicReader 详解

#### **基础配置**

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    // 2. 创建 PeriodicReader（每 30 秒导出一次）
    let reader = PeriodicReader::builder(exporter)
        .with_interval(Duration::from_secs(30))   // 导出间隔
        .with_timeout(Duration::from_secs(10))    // 单次导出超时
        .build();

    // 3. 创建 MeterProvider
    let provider = SdkMeterProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
        ]))
        .with_reader(reader)
        .build();

    global::set_meter_provider(provider.clone());

    // 4. 使用指标
    let meter = global::meter("app");
    let counter = meter.u64_counter("requests").init();
    
    for i in 0..100 {
        counter.add(1, &[KeyValue::new("iteration", i.to_string())]);
        tokio::time::sleep(Duration::from_millis(500)).await;
    }

    // 5. 优雅关闭（会触发最后一次导出）
    provider.shutdown()?;
    Ok(())
}
```

---

#### **高级配置：多 Exporter**

```rust
use opentelemetry_sdk::metrics::PeriodicReader;

async fn init_dual_export() -> Result<SdkMeterProvider, Box<dyn std::error::Error>> {
    // Exporter 1: OTLP (gRPC)
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://otlp-collector:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    let otlp_reader = PeriodicReader::builder(otlp_exporter)
        .with_interval(Duration::from_secs(60))
        .build();

    // Exporter 2: InfluxDB (假设有自定义实现)
    // let influx_exporter = InfluxExporter::new("http://influxdb:8086");
    // let influx_reader = PeriodicReader::builder(influx_exporter)
    //     .with_interval(Duration::from_secs(30))
    //     .build();

    let provider = SdkMeterProvider::builder()
        .with_resource(Resource::default())
        .with_reader(otlp_reader)
        // .with_reader(influx_reader)
        .build();

    Ok(provider)
}
```

---

#### **自适应间隔**

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

struct AdaptiveReader {
    base_reader: PeriodicReader,
    request_rate: Arc<AtomicU64>,
}

impl AdaptiveReader {
    fn new(exporter: impl opentelemetry_sdk::metrics::exporter::MetricExporter) -> Self {
        let reader = PeriodicReader::builder(exporter)
            .with_interval(Duration::from_secs(60))
            .build();

        Self {
            base_reader: reader,
            request_rate: Arc::new(AtomicU64::new(0)),
        }
    }

    async fn adjust_interval(&self) {
        loop {
            let rate = self.request_rate.load(Ordering::Relaxed);
            
            // 高流量时缩短间隔，低流量时延长间隔
            let new_interval = if rate > 1000 {
                Duration::from_secs(15)
            } else if rate > 100 {
                Duration::from_secs(30)
            } else {
                Duration::from_secs(60)
            };

            // 注意：当前 SDK 不支持动态调整，这里仅示意概念
            println!("建议导出间隔: {:?} (当前 QPS: {})", new_interval, rate);
            tokio::time::sleep(Duration::from_secs(60)).await;
        }
    }
}
```

---

### ManualReader 详解

#### **Prometheus 集成**

```rust
use opentelemetry_prometheus::exporter;
use prometheus::{Encoder, TextEncoder};
use warp::Filter;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 Prometheus Exporter
    let exporter = exporter().build()?;

    // 2. 创建 MeterProvider（Prometheus 使用 ManualReader）
    let provider = SdkMeterProvider::builder()
        .with_reader(exporter)
        .build();

    global::set_meter_provider(provider.clone());

    // 3. 创建指标
    let meter = global::meter("prometheus-demo");
    let counter = meter.u64_counter("http_requests_total").init();

    // 4. 模拟业务逻辑
    tokio::spawn(async move {
        loop {
            counter.add(1, &[KeyValue::new("status", "200")]);
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
    });

    // 5. 启动 HTTP 服务器暴露 /metrics 端点
    let metrics_route = warp::path("metrics").map(move || {
        let encoder = TextEncoder::new();
        let metric_families = prometheus::gather();
        let mut buffer = Vec::new();
        encoder.encode(&metric_families, &mut buffer).unwrap();
        warp::reply::with_header(buffer, "Content-Type", encoder.format_type())
    });

    println!("Prometheus metrics: http://localhost:9090/metrics");
    warp::serve(metrics_route).run(([0, 0, 0, 0], 9090)).await;

    Ok(())
}
```

**依赖**：

```toml
[dependencies]
opentelemetry-prometheus = "0.17"
prometheus = "0.13"
warp = "0.3"
```

---

#### **自定义拉取端点**

```rust
use axum::{routing::get, Router};
use opentelemetry_sdk::metrics::ManualReader;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 ManualReader
    let reader = ManualReader::builder().build();

    let provider = SdkMeterProvider::builder()
        .with_reader(reader.clone())
        .build();

    global::set_meter_provider(provider.clone());

    // 2. HTTP 端点
    let app = Router::new().route("/metrics", get({
        let reader = reader.clone();
        move || async move {
            // 触发手动收集
            match reader.collect() {
                Ok(metrics) => {
                    // 序列化为 JSON（示例）
                    let json = serde_json::to_string(&metrics).unwrap();
                    (axum::http::StatusCode::OK, json)
                }
                Err(e) => (
                    axum::http::StatusCode::INTERNAL_SERVER_ERROR,
                    format!("Error: {}", e),
                ),
            }
        }
    }));

    println!("Custom metrics endpoint: http://localhost:3000/metrics");
    axum::Server::bind(&"0.0.0.0:3000".parse()?)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}
```

**依赖**：

```toml
[dependencies]
axum = "0.7"
serde_json = "1.0"
```

---

### 多 Reader 配置

#### **同时支持推送和拉取**

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Reader 1: OTLP 推送（每 60 秒）
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    let otlp_reader = PeriodicReader::builder(otlp_exporter)
        .with_interval(Duration::from_secs(60))
        .build();

    // Reader 2: Prometheus 拉取
    let prometheus_exporter = opentelemetry_prometheus::exporter().build()?;

    // 组合两个 Reader
    let provider = SdkMeterProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "hybrid-service"),
        ]))
        .with_reader(otlp_reader)
        .with_reader(prometheus_exporter)
        .build();

    global::set_meter_provider(provider.clone());

    // 业务逻辑...
    let meter = global::meter("app");
    let counter = meter.u64_counter("requests").init();
    counter.add(1, &[]);

    tokio::signal::ctrl_c().await?;
    provider.shutdown()?;
    Ok(())
}
```

---

## 时间性语义

### **Cumulative（累计）**

- **语义**：每个数据点是从程序启动以来的累计值
- **适用**：Counter、UpDownCounter
- **示例**：总请求数从 0 → 100 → 250 → 1000

```rust
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .build_metrics_exporter(
        Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
        Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
    )?;
```

**导出数据示例**：

```text
时间戳    | 值
--------|------
T1      | 100
T2      | 250
T3      | 1000
```

---

### **Delta（增量）**

- **语义**：每个数据点是自上次导出以来的增量
- **适用**：高频率指标（减少网络传输）
- **示例**：T1→T2 增加 150，T2→T3 增加 750

```rust
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .build_metrics_exporter(
        Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
        Box::new(opentelemetry_sdk::metrics::data::Temporality::Delta),
    )?;
```

**导出数据示例**：

```text
时间戳    | 增量
--------|------
T1      | 100
T2      | 150
T3      | 750
```

---

### **选择建议**

| 后端 | 推荐时间性 | 原因 |
|------|-----------|------|
| Prometheus | Cumulative | Prometheus 原生支持累计值 + rate() 函数 |
| InfluxDB | Delta | 减少存储空间，InfluxDB 适合增量数据 |
| OTLP Collector | Cumulative | 通用性更好，后端可按需转换 |
| 自定义后端 | 根据存储特性选择 | - |

---

## 高级配置

### **导出超时控制**

```rust
let reader = PeriodicReader::builder(exporter)
    .with_interval(Duration::from_secs(60))
    .with_timeout(Duration::from_secs(5))  // 单次导出最多 5 秒
    .build();
```

---

### **导出失败重试**

```rust
use opentelemetry_sdk::metrics::exporter::MetricExporter;

struct RetryableExporter {
    inner: Box<dyn MetricExporter>,
    max_retries: usize,
}

impl MetricExporter for RetryableExporter {
    fn export(&self, metrics: &mut dyn Iterator<Item = &opentelemetry_sdk::metrics::data::ResourceMetrics>) -> opentelemetry::metrics::Result<()> {
        let mut attempts = 0;
        loop {
            match self.inner.export(metrics) {
                Ok(_) => return Ok(()),
                Err(e) if attempts < self.max_retries => {
                    attempts += 1;
                    eprintln!("导出失败，重试 {}/{}: {:?}", attempts, self.max_retries, e);
                    std::thread::sleep(Duration::from_secs(2u64.pow(attempts as u32)));
                }
                Err(e) => return Err(e),
            }
        }
    }

    // 实现其他必需方法...
}
```

---

### **条件导出：按需触发**

```rust
use std::sync::Arc;
use tokio::sync::Notify;

struct ConditionalReader {
    reader: PeriodicReader,
    force_export: Arc<Notify>,
}

impl ConditionalReader {
    async fn wait_for_signal(&self) {
        self.force_export.notified().await;
        // 触发立即导出
        println!("收到信号，立即导出指标");
    }
}

// 在关键事件发生时触发
async fn on_critical_event(reader: &ConditionalReader) {
    reader.force_export.notify_one();
}
```

---

## 最佳实践

### ✅ **推荐**

1. **选择合适的 Reader 类型**：
   - 云服务/OTLP → PeriodicReader
   - Prometheus → ManualReader
2. **导出间隔**：
   - 低流量服务：60 秒
   - 中等流量：30 秒
   - 高流量/关键服务：15 秒
3. **超时配置**：导出超时应小于导出间隔的 50%
4. **多 Reader 隔离**：不同后端使用不同 Reader，避免相互影响
5. **优雅关闭**：调用 `shutdown()` 确保最后一批数据导出

### ❌ **避免**

1. **过高频率**：导出间隔 < 10 秒会增加 CPU/网络开销
2. **忽略超时**：导出阻塞会影响应用性能
3. **忘记关闭**：程序退出前未调用 `shutdown()` 可能丢失数据
4. **混用时间性**：同一 MeterProvider 中多个 Reader 应使用相同时间性

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"          # OTLP Exporter
opentelemetry-prometheus = "0.17"    # Prometheus Exporter
tokio = { version = "1", features = ["full"] }
```

### **HTTP 框架（拉取模式）**

```toml
axum = "0.7"           # 或
warp = "0.3"           # 或
actix-web = "4"
```

---

## 总结

| Reader 类型 | 模式 | 适用场景 | 配置关键点 |
|------------|------|---------|-----------|
| **PeriodicReader** | 推送 | OTLP、云服务 | `with_interval()` 设置周期 |
| **ManualReader** | 拉取 | Prometheus | 暴露 HTTP 端点 + `collect()` |
| **混合模式** | 推送+拉取 | 同时支持多后端 | 多个 `with_reader()` |

**关键配置**：

- **导出间隔**：平衡实时性与性能
- **超时控制**：避免阻塞业务线程
- **时间性**：Cumulative（通用）vs Delta（高频）

**下一步**：[05_MetricExporter_Rust完整版.md](./05_MetricExporter_Rust完整版.md) - 学习如何实现自定义导出器
