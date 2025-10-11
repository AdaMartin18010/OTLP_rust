# 🦀 OTLP协议速查手册 - Rust 1.90版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **OTLP协议**: 1.3.2  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 OTLP协议速查手册 - Rust 1.90版](#-otlp协议速查手册---rust-190版)
  - [📋 快速索引](#-快速索引)
  - [🎯 协议基础](#-协议基础)
    - [OTLP Endpoint格式](#otlp-endpoint格式)
    - [基础配置](#基础配置)
  - [🔍 Traces导出](#-traces导出)
    - [快速初始化](#快速初始化)
    - [Span属性速查](#span属性速查)
    - [Span状态](#span状态)
  - [📊 Metrics导出](#-metrics导出)
    - [快速初始化1](#快速初始化1)
    - [指标类型速查](#指标类型速查)
  - [📝 Logs导出](#-logs导出)
    - [快速初始化2](#快速初始化2)
    - [日志级别](#日志级别)
  - [🌐 传输协议](#-传输协议)
    - [gRPC配置](#grpc配置)
    - [HTTP配置](#http配置)
    - [压缩选项](#压缩选项)
  - [🔐 认证与安全](#-认证与安全)
    - [API Key认证](#api-key认证)
    - [Bearer Token认证](#bearer-token认证)
    - [TLS配置](#tls配置)
  - [⚙️ 批处理配置](#️-批处理配置)
    - [默认配置](#默认配置)
    - [高吞吐配置](#高吞吐配置)
    - [低延迟配置](#低延迟配置)
  - [🎯 采样策略](#-采样策略)
    - [始终采样](#始终采样)
    - [比例采样](#比例采样)
    - [父级采样](#父级采样)
  - [❌ 常见错误速查](#-常见错误速查)
    - [1. 连接错误](#1-连接错误)
    - [2. 认证错误](#2-认证错误)
    - [3. 超时错误](#3-超时错误)
    - [4. 数据丢失](#4-数据丢失)
  - [🛠️ 诊断工具](#️-诊断工具)
    - [连接诊断](#连接诊断)
  - [📊 性能优化速查](#-性能优化速查)
  - [🌍 环境变量速查](#-环境变量速查)
  - [📚 资源链接](#-资源链接)

---

## 🎯 协议基础

### OTLP Endpoint格式

```rust
// gRPC Endpoints
const OTLP_GRPC_TRACES: &str = "http://localhost:4317/v1/traces";
const OTLP_GRPC_METRICS: &str = "http://localhost:4317/v1/metrics";
const OTLP_GRPC_LOGS: &str = "http://localhost:4317/v1/logs";

// HTTP/Protobuf Endpoints
const OTLP_HTTP_TRACES: &str = "http://localhost:4318/v1/traces";
const OTLP_HTTP_METRICS: &str = "http://localhost:4318/v1/metrics";
const OTLP_HTTP_LOGS: &str = "http://localhost:4318/v1/logs";
```

### 基础配置

```rust
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

// 超时配置
.with_timeout(Duration::from_secs(30))

// 压缩配置
.with_compression(tonic::codec::CompressionEncoding::Gzip)

// TLS配置
.with_tls_config(/* tls_config */)

// 认证配置
.with_metadata(metadata_map)
```

---

## 🔍 Traces导出

### 快速初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::SpanExporter;
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    resource::Resource,
    runtime,
};

pub fn init_tracer() -> anyhow::Result<TracerProvider> {
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)
        .with_config(Config::default().with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
        ])))
        .build();

    global::set_tracer_provider(provider.clone());
    Ok(provider)
}
```

### Span属性速查

```rust
use opentelemetry::trace::{Span, Tracer};

let mut span = tracer.start("operation");

// HTTP属性
span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.url", "https://example.com"));
span.set_attribute(KeyValue::new("http.status_code", 200));

// DB属性
span.set_attribute(KeyValue::new("db.system", "postgresql"));
span.set_attribute(KeyValue::new("db.name", "mydb"));
span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users"));

// RPC属性
span.set_attribute(KeyValue::new("rpc.system", "grpc"));
span.set_attribute(KeyValue::new("rpc.service", "MyService"));
span.set_attribute(KeyValue::new("rpc.method", "GetUser"));

span.end();
```

### Span状态

```rust
use opentelemetry::trace::Status;

// 成功
span.set_status(Status::Ok);

// 错误
span.set_status(Status::error("Database connection failed"));

// 未设置
span.set_status(Status::Unset);
```

---

## 📊 Metrics导出

### 快速初始化1

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::MetricsExporter;
use opentelemetry_sdk::{
    metrics::{MeterProvider, PeriodicReader},
    resource::Resource,
    runtime,
};

pub fn init_meter() -> anyhow::Result<MeterProvider> {
    let exporter = MetricsExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let reader = PeriodicReader::builder(exporter, runtime::Tokio)
        .with_interval(Duration::from_secs(60))
        .build();

    let provider = MeterProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
        ]))
        .with_reader(reader)
        .build();

    global::set_meter_provider(provider.clone());
    Ok(provider)
}
```

### 指标类型速查

```rust
use opentelemetry::metrics::Meter;

let meter = global::meter("my-app");

// 1. Counter (累加)
let counter = meter
    .u64_counter("requests_total")
    .with_description("Total requests")
    .init();
counter.add(1, &[KeyValue::new("method", "GET")]);

// 2. UpDownCounter (可增可减)
let active_connections = meter
    .i64_up_down_counter("active_connections")
    .init();
active_connections.add(1, &[]); // 连接建立
active_connections.add(-1, &[]); // 连接关闭

// 3. Histogram (分布)
let latency = meter
    .f64_histogram("request_duration_seconds")
    .with_unit("s")
    .init();
latency.record(0.125, &[KeyValue::new("endpoint", "/api/users")]);

// 4. Gauge (观察值)
let cpu_usage = meter
    .f64_observable_gauge("cpu_usage_percent")
    .with_description("CPU usage percentage")
    .init();
```

---

## 📝 Logs导出

### 快速初始化2

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::LogExporter;
use opentelemetry_sdk::{
    logs::LoggerProvider,
    resource::Resource,
    runtime,
};

pub fn init_logger() -> anyhow::Result<LoggerProvider> {
    let exporter = LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let provider = LoggerProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
        ]))
        .with_batch_exporter(exporter, runtime::Tokio)
        .build();

    global::set_logger_provider(provider.clone());
    Ok(provider)
}
```

### 日志级别

```rust
use opentelemetry::logs::{LogRecord, Severity};

let mut record = LogRecord::default();

// 设置级别
record.set_severity(Severity::Info);    // INFO
record.set_severity(Severity::Warn);    // WARN
record.set_severity(Severity::Error);   // ERROR
record.set_severity(Severity::Debug);   // DEBUG
record.set_severity(Severity::Trace);   // TRACE
```

---

## 🌐 传输协议

### gRPC配置

```rust
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use tonic::metadata::MetadataMap;

let mut metadata = MetadataMap::new();
metadata.insert("authorization", "Bearer token123".parse()?);

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("grpc://localhost:4317")
    .with_timeout(Duration::from_secs(30))
    .with_compression(tonic::codec::CompressionEncoding::Gzip)
    .with_metadata(metadata)
    .build()?;
```

### HTTP配置

```rust
use opentelemetry_otlp::{SpanExporter, WithExportConfig, WithHttpConfig};

let exporter = SpanExporter::builder()
    .with_http()
    .with_endpoint("http://localhost:4318/v1/traces")
    .with_timeout(Duration::from_secs(30))
    .with_http_client(reqwest::Client::new())
    .build()?;
```

### 压缩选项

```rust
// gRPC压缩
use tonic::codec::CompressionEncoding;

.with_compression(CompressionEncoding::Gzip)    // 推荐
.with_compression(CompressionEncoding::Zstd)    // 高压缩率
.with_compression(CompressionEncoding::Snappy)  // 快速

// HTTP压缩 (自动处理)
```

---

## 🔐 认证与安全

### API Key认证

```rust
let mut metadata = MetadataMap::new();
metadata.insert("x-api-key", "your-api-key".parse()?);

.with_metadata(metadata)
```

### Bearer Token认证

```rust
let mut metadata = MetadataMap::new();
metadata.insert(
    "authorization",
    format!("Bearer {}", token).parse()?
);

.with_metadata(metadata)
```

### TLS配置

```rust
use tonic::transport::ClientTlsConfig;

let tls_config = ClientTlsConfig::new()
    .domain_name("example.com")
    .ca_certificate(/* cert */);

.with_tls_config(tls_config)
```

---

## ⚙️ 批处理配置

### 默认配置

```rust
use opentelemetry_sdk::trace::Config;

let config = Config::default()
    .with_max_export_batch_size(512)     // 最大批次
    .with_max_queue_size(2048)           // 队列大小
    .with_scheduled_delay(Duration::from_secs(5)); // 延迟
```

### 高吞吐配置

```rust
let config = Config::default()
    .with_max_export_batch_size(1024)
    .with_max_queue_size(8192)
    .with_scheduled_delay(Duration::from_millis(500));
```

### 低延迟配置

```rust
let config = Config::default()
    .with_max_export_batch_size(128)
    .with_max_queue_size(512)
    .with_scheduled_delay(Duration::from_millis(100));
```

---

## 🎯 采样策略

### 始终采样

```rust
use opentelemetry_sdk::trace::Sampler;

let sampler = Sampler::AlwaysOn;
```

### 比例采样

```rust
// 10%采样
let sampler = Sampler::TraceIdRatioBased(0.1);
```

### 父级采样

```rust
let sampler = Sampler::ParentBased(Box::new(
    Sampler::TraceIdRatioBased(0.1)
));
```

---

## ❌ 常见错误速查

### 1. 连接错误

```text
Error: transport error
原因: Collector未启动或地址错误
解决: 检查endpoint和Collector状态
```

```rust
// 诊断代码
let client = reqwest::Client::new();
match client.get("http://localhost:4318/v1/traces").send().await {
    Ok(_) => println!("✅ Collector可达"),
    Err(e) => println!("❌ 连接失败: {}", e),
}
```

### 2. 认证错误

```text
Error: Unauthenticated
原因: Token无效或缺失
解决: 检查metadata中的认证信息
```

```rust
// 检查认证
let mut metadata = MetadataMap::new();
if let Ok(token) = std::env::var("OTLP_TOKEN") {
    metadata.insert("authorization", format!("Bearer {}", token).parse()?);
}
```

### 3. 超时错误

```text
Error: timeout
原因: 网络延迟或Collector过载
解决: 增加timeout或优化批处理
```

```rust
// 增加超时
.with_timeout(Duration::from_secs(60))
```

### 4. 数据丢失

```text
原因: 队列溢出
解决: 增大队列或减少导出延迟
```

```rust
let config = Config::default()
    .with_max_queue_size(8192)  // 增大队列
    .with_scheduled_delay(Duration::from_secs(1)); // 减少延迟
```

---

## 🛠️ 诊断工具

### 连接诊断

```rust
pub async fn diagnose_otlp_connection(endpoint: &str) -> anyhow::Result<()> {
    println!("🔍 Diagnosing OTLP connection to {}\n", endpoint);

    // 1. 网络测试
    println!("1️⃣ Testing network...");
    let client = reqwest::Client::new();
    match client.get(format!("{}/health", endpoint)).send().await {
        Ok(_) => println!("   ✅ Network OK"),
        Err(e) => println!("   ❌ Network failed: {}", e),
    }

    // 2. TLS测试
    println!("\n2️⃣ Testing TLS...");
    if endpoint.starts_with("https") {
        println!("   ✅ TLS enabled");
    } else {
        println!("   ⚠️ TLS not used");
    }

    // 3. 导出测试
    println!("\n3️⃣ Testing export...");
    // 实际导出测试

    Ok(())
}
```

---

## 📊 性能优化速查

| 场景 | 配置建议 |
|------|---------|
| **高吞吐** | batch_size=1024, queue=8192, delay=500ms |
| **低延迟** | batch_size=128, queue=512, delay=100ms |
| **低成本** | 采样率=0.01-0.1, 压缩=Gzip |
| **生产环境** | batch_size=512, queue=2048, delay=5s, 采样=0.1 |

---

## 🌍 环境变量速查

```bash
# Endpoint配置
export OTEL_EXPORTER_OTLP_ENDPOINT="http://localhost:4317"
export OTEL_EXPORTER_OTLP_TRACES_ENDPOINT="http://localhost:4317/v1/traces"
export OTEL_EXPORTER_OTLP_METRICS_ENDPOINT="http://localhost:4317/v1/metrics"
export OTEL_EXPORTER_OTLP_LOGS_ENDPOINT="http://localhost:4317/v1/logs"

# 协议选择
export OTEL_EXPORTER_OTLP_PROTOCOL="grpc"  # 或 "http/protobuf"

# 认证
export OTEL_EXPORTER_OTLP_HEADERS="authorization=Bearer token123"

# 超时
export OTEL_EXPORTER_OTLP_TIMEOUT="30000"  # 毫秒

# 压缩
export OTEL_EXPORTER_OTLP_COMPRESSION="gzip"
```

---

## 📚 资源链接

| 资源 | 链接 |
|------|------|
| **OTLP规范** | <https://opentelemetry.io/docs/specs/otlp/> |
| **Rust SDK** | <https://github.com/open-telemetry/opentelemetry-rust> |
| **Protocol Buffers** | <https://github.com/open-telemetry/opentelemetry-proto> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**下一篇**: [Semantic_Conventions速查手册_Rust版](./02_Semantic_Conventions速查手册_Rust版.md)
