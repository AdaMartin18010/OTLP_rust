# OpenTelemetry Rust API 完整参考

**版本**: 0.6.0
**Rust 版本**: 1.94+
**OTLP 版本**: 1.10

---

## 📚 目录

- [OpenTelemetry Rust API 完整参考](#opentelemetry-rust-api-完整参考)
  - [📚 目录](#-目录)
  - [核心模块](#核心模块)
    - [crate 结构](#crate-结构)
    - [重新导出的类型](#重新导出的类型)
  - [数据模型](#数据模型)
    - [TelemetryData](#telemetrydata)
    - [构造方法](#构造方法)
    - [链式 API](#链式-api)
  - [客户端 API](#客户端-api)
    - [OtlpClientBuilder](#otlpclientbuilder)
    - [TraceBuilder](#tracebuilder)
    - [MetricBuilder](#metricbuilder)
    - [LogBuilder](#logbuilder)
  - [导出器 API](#导出器-api)
    - [OtlpExporter](#otlpexporter)
    - [导出结果](#导出结果)
    - [PartialSuccess (OTLP 1.10+)](#partialsuccess-otlp-110)
  - [配置 API](#配置-api)
    - [OtlpConfig](#otlpconfig)
    - [配置构建器](#配置构建器)
    - [批处理配置](#批处理配置)
  - [SIMD API](#simd-api)
    - [特性检测](#特性检测)
    - [聚合操作](#聚合操作)
    - [真实 SIMD 实现](#真实-simd-实现)
  - [性能分析 API](#性能分析-api)
    - [CPU 分析器](#cpu-分析器)
    - [内存分析器](#内存分析器)
    - [分析数据导出](#分析数据导出)
  - [Rust 1.94 特性 API](#rust-194-特性-api)
    - [array\_windows](#array_windows)
    - [element\_offset](#element_offset)
    - [数学常量](#数学常量)
  - [最佳实践](#最佳实践)
    - [错误处理](#错误处理)
    - [资源属性](#资源属性)
    - [采样配置](#采样配置)
  - [版本兼容性](#版本兼容性)
  - [参考资源](#参考资源)

---

## 核心模块

### crate 结构

```rust
// 主要模块
pub mod client;      // 客户端构建器
pub mod config;      // 配置管理
pub mod data;        // 数据模型
pub mod error;       // 错误处理
pub mod exporter;    // 导出器
pub mod simd;        // SIMD优化
pub mod profiling;   // 性能分析
```

### 重新导出的类型

```rust
// 数据类型
pub use data::{
    TelemetryData, TelemetryDataType, TelemetryContent,
    TraceData, MetricData, LogData, ProfileData,
    SpanKind, SpanStatus, StatusCode,
    MetricType, DataPoint, DataPointValue,
    LogSeverity, AttributeValue,
    // OTLP 1.10+ 新增
    ExponentialHistogramData, ExponentialHistogramBuckets,
    SampleType, Sample, Label, Mapping, Location, Function,
};

// 导出器
pub use exporter::{
    OtlpExporter, ExportResult, ExporterMetrics, PartialSuccess,
};

// 客户端
pub use client::{
    OtlpClient, OtlpClientBuilder, TraceBuilder, MetricBuilder, LogBuilder,
};
```

---

## 数据模型

### TelemetryData

OTLP 数据的核心结构。

```rust
pub struct TelemetryData {
    /// 数据类型
    pub data_type: TelemetryDataType,
    /// 时间戳（纳秒）
    pub timestamp: u64,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
    /// 作用域属性
    pub scope_attributes: HashMap<String, String>,
    /// 数据内容
    pub content: TelemetryContent,
}
```

### 构造方法

```rust
impl TelemetryData {
    /// 创建新的遥测数据
    pub fn new(data_type: TelemetryDataType, content: TelemetryContent) -> Self;

    /// 创建追踪数据
    pub fn trace(name: impl Into<String>) -> Self;

    /// 创建指标数据
    pub fn metric(name: impl Into<String>, metric_type: MetricType) -> Self;

    /// 创建日志数据
    pub fn log(message: impl Into<String>, severity: LogSeverity) -> Self;

    /// 创建性能分析数据 (OTLP 1.10+)
    pub fn profile(sample_type: SampleType) -> Self;
}
```

### 链式 API

```rust
let data = TelemetryData::trace("http_request")
    .with_resource_attribute("service.name", "my-service")
    .with_scope_attribute("scope.version", "1.0.0")
    .with_attribute("http.method", "GET")
    .with_numeric_attribute("http.status_code", 200.0)
    .with_status(StatusCode::Ok, None)
    .finish();
```

---

## 客户端 API

### OtlpClientBuilder

构建 OTLP 客户端的主要方式。

```rust
use otlp::client::OtlpClientBuilder;
use otlp::config::TransportProtocol;

let client = OtlpClientBuilder::new()
    .endpoint("http://localhost:4317")
    .protocol(TransportProtocol::Grpc)
    .timeout(Duration::from_secs(5))
    .batch_size(100)
    .service("my-service", "1.0.0")
    .with_attribute("env", "production")
    .build()
    .await?;
```

### TraceBuilder

用于构建和发送追踪数据。

```rust
use otlp::client::TraceBuilder;

TraceBuilder::new("process_order", config)
    .with_attribute("order.id", order_id)
    .with_numeric_attribute("order.amount", amount)
    .with_duration(100) // 毫秒
    .finish()
    .await?;
```

### MetricBuilder

用于构建和发送指标数据。

```rust
use otlp::client::MetricBuilder;
use otlp::data::MetricType;

MetricBuilder::new("request_count", 1.0, config)
    .with_label("method", "GET")
    .with_label("status", "200")
    .with_description("HTTP request count")
    .with_unit("count")
    .send()
    .await?;
```

### LogBuilder

用于构建和发送日志数据。

```rust
use otlp::client::LogBuilder;
use otlp::data::LogSeverity;

LogBuilder::new("Processing started", config)
    .with_severity(LogSeverity::Info)
    .with_attribute("request.id", request_id)
    .send()
    .await?;
```

---

## 导出器 API

### OtlpExporter

核心导出器实现。

```rust
use otlp::exporter::OtlpExporter;

let exporter = OtlpExporter::new(config);
exporter.initialize().await?;

// 导出数据
let result = exporter.export(vec![data]).await?;
println!("导出成功: {} 条", result.success_count);
```

### 导出结果

```rust
pub struct ExportResult {
    /// 成功导出的数据数量
    pub success_count: usize,
    /// 失败的数据数量
    pub failure_count: usize,
    /// 导出耗时
    pub duration: Duration,
    /// 错误信息
    pub errors: Vec<String>,
    /// 部分成功信息 (OTLP 1.10+)
    pub partial_success: Option<PartialSuccess>,
}

impl ExportResult {
    /// 是否完全成功
    pub fn is_success(&self) -> bool;

    /// 是否部分成功
    pub fn is_partial_success(&self) -> bool;

    /// 成功率
    pub fn success_rate(&self) -> f64;
}
```

### PartialSuccess (OTLP 1.10+)

```rust
pub struct PartialSuccess {
    /// 被拒绝的追踪跨度数量
    pub rejected_spans: u64,
    /// 被拒绝的指标数据点数量
    pub rejected_data_points: u64,
    /// 被拒绝的日志记录数量
    pub rejected_log_records: u64,
    /// 被拒绝的性能分析样本数量
    pub rejected_profiles: u64,
    /// 错误信息
    pub error_message: String,
}
```

---

## 配置 API

### OtlpConfig

主要配置结构。

```rust
pub struct OtlpConfig {
    /// 端点地址
    pub endpoint: String,
    /// 传输协议
    pub protocol: TransportProtocol,
    /// 超时时间
    pub timeout: Duration,
    /// 批处理配置
    pub batch_config: BatchConfig,
    /// 服务配置
    pub service_config: ServiceConfig,
    /// 重试策略
    pub retry_policy: RetryPolicy,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
}
```

### 配置构建器

```rust
use otlp::config::OtlpConfig;

let config = OtlpConfig::new()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc)
    .with_timeout(Duration::from_secs(10))
    .with_batch_config(BatchConfig::default())
    .with_resource_attribute("service.name", "my-service")
    .with_resource_attribute("deployment.environment", "production");
```

### 批处理配置

```rust
pub struct BatchConfig {
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 最大导出批次大小
    pub max_export_batch_size: usize,
    /// 调度延迟
    pub scheduled_delay: Duration,
    /// 导出超时
    pub export_timeout: Duration,
}

impl BatchConfig {
    pub fn new() -> Self;
    pub fn with_max_queue_size(mut self, size: usize) -> Self;
    pub fn with_max_export_batch_size(mut self, size: usize) -> Self;
    pub fn with_scheduled_delay(mut self, delay: Duration) -> Self;
}
```

---

## SIMD API

### 特性检测

```rust
use otlp::simd::CpuFeatures;

let features = CpuFeatures::detect();
if features.has_avx512fp16() {
    println!("AVX-512 FP16 可用");
}
if features.has_neon() {
    println!("NEON 可用");
}
```

### 聚合操作

```rust
use otlp::simd::Aggregator;

// 求和
let sum = Aggregator::sum_i64(&values);
let sum_f = Aggregator::sum_f64(&values);

// 最值
let min = Aggregator::min_i64(&values);
let max = Aggregator::max_i64(&values);

// 统计
let stats = Aggregator::compute_stats(&values);
```

### 真实 SIMD 实现

```rust
use otlp::simd::{
    real_simd_sum_i64,
    real_simd_sum_f64,
    simd_aggregate_metrics,
};

// AVX2 加速求和
let sum = real_simd_sum_i64(&values);

// 指标聚合
let aggregated = simd_aggregate_metrics(&metrics);
```

---

## 性能分析 API

### CPU 分析器

```rust
use otlp::profiling::{CpuProfiler, ProfileConfig};

let config = ProfileConfig::new()
    .with_sample_rate(100) // 每秒100个样本
    .with_duration(Duration::from_secs(30));

let profiler = CpuProfiler::new(config);
profiler.start().await?;

// ... 运行代码 ...

let profile = profiler.stop().await?;
```

### 内存分析器

```rust
use otlp::profiling::{MemoryProfiler, MemoryProfileConfig};

let config = MemoryProfileConfig::new()
    .with_allocation_tracking(true)
    .with_leak_detection(true);

let profiler = MemoryProfiler::new(config);
profiler.start().await?;

// ... 运行代码 ...

let report = profiler.generate_report().await?;
```

### 分析数据导出

```rust
// 导出为 OTLP Profile 格式
let profile_data = ProfileData::new()
    .with_sample_types(vec![SampleType {
        type: "cpu".to_string(),
        unit: "nanoseconds".to_string(),
    }])
    .with_samples(samples);

exporter.export(vec![TelemetryData::profile(profile_data)]).await?;
```

---

## Rust 1.94 特性 API

### array_windows

```rust
use otlp::rust_1_94_alignment::Rust194Features;

// 检测重复模式
let patterns = Rust194Features::detect_repeated_pattern(&data, 4);

// 在遥测数据处理中的应用
fn detect_anomaly(data: &[u8]) -> bool {
    data.array_windows()
        .any(|[a, b, c, d]| a == d && b == c && a != b)
}
```

### element_offset

```rust
// 计算元素偏移
let positions = Rust194Features::calculate_element_positions(&slice);

// 用于零拷贝序列化
fn serialize_zero_copy<T>(data: &[T]) -> Vec<u8> {
    let offsets = Rust194Features::calculate_element_positions(data);
    // ... 序列化逻辑
}
```

### 数学常量

```rust
use otlp::rust_1_94_alignment::Rust194Features;

// 自适应采样率
let rate = Rust194Features::calculate_adaptive_sample_rate(iteration);

// 编译时融合乘加
const RESULT: f64 = Rust194Features::const_fma(2.0, 3.0, 4.0); // 10.0
```

---

## 最佳实践

### 错误处理

```rust
use otlp::error::{OtlpError, Result};

match exporter.export(data).await {
    Ok(result) => {
        if result.is_partial_success() {
            tracing::warn!("Partial success: {:?}", result.partial_success);
        }
    }
    Err(OtlpError::Export(e)) => {
        tracing::error!("Export failed: {}", e);
    }
    Err(e) => {
        tracing::error!("Unexpected error: {}", e);
    }
}
```

### 资源属性

```rust
// 必须设置的属性
let config = OtlpConfig::new()
    .with_resource_attribute("service.name", env!("CARGO_PKG_NAME"))
    .with_resource_attribute("service.version", env!("CARGO_PKG_VERSION"))
    .with_resource_attribute("deployment.environment", "production");
```

### 采样配置

```rust
// 生产环境推荐
let config = OtlpConfig::new()
    .with_sampler(SamplerType::ParentBased)
    .with_sampling_ratio(0.1);

// 高流量服务
let config = OtlpConfig::new()
    .with_sampler(SamplerType::RateLimiting)
    .with_rate_limit(1000);
```

---

## 版本兼容性

| 版本 | Rust | OTLP | 状态 |
|------|------|------|------|
| 0.6.0 | 1.94+ | 1.10 | ✅ 当前 |
| 0.5.0 | 1.92+ | 1.3 | ⚠️ 已弃用 |
| 0.4.0 | 1.90+ | 1.2 | ❌ 不支持 |

---

## 参考资源

- [OpenTelemetry Rust API Docs](https://docs.rs/opentelemetry/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Rust 1.94 Release Notes](https://blog.rust-lang.org/releases/)
- [Crate 文档](https://docs.rs/otlp/)

---

**文档维护**: OTLP Rust Team
**最后更新**: 2026-03-15
