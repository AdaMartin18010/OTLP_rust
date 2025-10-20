# MetricExporter - Rust 完整实现指南

## 📋 目录

- [MetricExporter - Rust 完整实现指南](#metricexporter---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Exporter 类型](#exporter-类型)
  - [Rust 实现](#rust-实现)
    - [OTLP Exporter](#otlp-exporter)
      - [**gRPC 传输**](#grpc-传输)
      - [**HTTP/JSON 传输**](#httpjson-传输)
      - [**TLS 认证**](#tls-认证)
      - [**Header 认证**](#header-认证)
    - [Prometheus Exporter](#prometheus-exporter)
      - [**基础集成**](#基础集成)
    - [Stdout Exporter](#stdout-exporter)
    - [自定义 Exporter](#自定义-exporter)
      - [**实现 InfluxDB Exporter**](#实现-influxdb-exporter)
  - [错误处理](#错误处理)
    - [**重试机制**](#重试机制)
    - [**降级策略**](#降级策略)
  - [性能优化](#性能优化)
    - [**批量压缩**](#批量压缩)
    - [**连接池复用**](#连接池复用)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**自定义 Exporter 依赖**](#自定义-exporter-依赖)
  - [总结](#总结)

---

## 核心概念

**MetricExporter** 负责将指标数据发送到监控后端，是 OpenTelemetry 管道的最后一环：

```text
┌──────────────────────────────────────────────┐
│         MeterProvider                        │
│  ┌────────────────────────────────────────┐  │
│  │ Instruments (Counter, Histogram, ...)  │  │
│  └────────────────────────────────────────┘  │
│                  ↓                           │
│  ┌────────────────────────────────────────┐  │
│  │ MetricReader (Periodic/Manual)         │  │
│  │  - 聚合数据                             │  │
│  │  - 触发导出                             │  │
│  └────────────────────────────────────────┘  │
│                  ↓                           │
│  ┌────────────────────────────────────────┐  │
│  │ MetricExporter                         │  │
│  │  - 序列化数据                           │  │
│  │  - 发送到后端                           │  │
│  └────────────────────────────────────────┘  │
│                  ↓                           │
│     Backend (OTLP/Prometheus/InfluxDB)       │
└──────────────────────────────────────────────┘
```

---

## Exporter 类型

| Exporter | 协议 | 模式 | 适用场景 |
|----------|------|------|---------|
| **OTLP** | gRPC/HTTP | 推送 | 标准后端、Collector |
| **Prometheus** | HTTP | 拉取 | Prometheus 监控 |
| **Stdout** | 标准输出 | 推送 | 本地调试 |
| **自定义** | 任意 | 任意 | InfluxDB、Datadog 等 |

---

## Rust 实现

### OTLP Exporter

#### **gRPC 传输**

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
    // 创建 OTLP gRPC Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    let reader = PeriodicReader::builder(exporter)
        .with_interval(Duration::from_secs(30))
        .build();

    let provider = SdkMeterProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-demo"),
        ]))
        .with_reader(reader)
        .build();

    global::set_meter_provider(provider.clone());

    // 使用指标
    let meter = global::meter("app");
    let counter = meter.u64_counter("requests").init();
    counter.add(1, &[KeyValue::new("status", "200")]);

    provider.shutdown()?;
    Ok(())
}
```

---

#### **HTTP/JSON 传输**

```rust
let exporter = opentelemetry_otlp::new_exporter()
    .http()
    .with_endpoint("http://localhost:4318/v1/metrics")
    .with_timeout(Duration::from_secs(10))
    .build_metrics_exporter(
        Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector),
        Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
    )?;
```

---

#### **TLS 认证**

```rust
use opentelemetry_otlp::WithExportConfig;

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(
        tonic::transport::ClientTlsConfig::new()
            .ca_certificate(tonic::transport::Certificate::from_pem(
                std::fs::read_to_string("ca.pem")?
            ))
            .domain_name("collector.example.com"),
    )
    .build_metrics_exporter(/* ... */)?;
```

---

#### **Header 认证**

```rust
use opentelemetry_otlp::{WithExportConfig, WithHttpConfig};

let mut headers = std::collections::HashMap::new();
headers.insert("Authorization".to_string(), "Bearer YOUR_TOKEN".to_string());

let exporter = opentelemetry_otlp::new_exporter()
    .http()
    .with_endpoint("http://localhost:4318/v1/metrics")
    .with_headers(headers)
    .build_metrics_exporter(/* ... */)?;
```

---

### Prometheus Exporter

#### **基础集成**

```rust
use opentelemetry_prometheus::exporter;
use prometheus::{Encoder, TextEncoder};
use warp::Filter;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 Prometheus Exporter
    let exporter = exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()?;

    let provider = SdkMeterProvider::builder()
        .with_reader(exporter)
        .build();

    global::set_meter_provider(provider.clone());

    // 创建指标
    let meter = global::meter("app");
    let counter = meter.u64_counter("requests_total").init();

    // 模拟业务逻辑
    tokio::spawn(async move {
        loop {
            counter.add(1, &[KeyValue::new("method", "GET")]);
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
    });

    // 暴露 /metrics 端点
    let metrics = warp::path("metrics").map(|| {
        let encoder = TextEncoder::new();
        let families = prometheus::gather();
        let mut buffer = Vec::new();
        encoder.encode(&families, &mut buffer).unwrap();
        warp::reply::with_header(buffer, "Content-Type", encoder.format_type())
    });

    println!("Metrics: http://localhost:9090/metrics");
    warp::serve(metrics).run(([0, 0, 0, 0], 9090)).await;
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

### Stdout Exporter

```rust
use opentelemetry_sdk::metrics::data::Temporality;

let exporter = opentelemetry_stdout::MetricsExporter::default();

let reader = PeriodicReader::builder(exporter)
    .with_interval(Duration::from_secs(5))
    .build();

let provider = SdkMeterProvider::builder()
    .with_reader(reader)
    .build();

global::set_meter_provider(provider.clone());

// 每 5 秒输出到控制台
```

**依赖**：

```toml
[dependencies]
opentelemetry-stdout = { version = "0.24", features = ["metrics"] }
```

---

### 自定义 Exporter

#### **实现 InfluxDB Exporter**

```rust
use opentelemetry_sdk::metrics::{
    data::ResourceMetrics,
    exporter::MetricExporter,
};
use async_trait::async_trait;

struct InfluxDBExporter {
    client: reqwest::Client,
    url: String,
    token: String,
}

impl InfluxDBExporter {
    fn new(url: String, token: String) -> Self {
        Self {
            client: reqwest::Client::new(),
            url,
            token,
        }
    }

    fn convert_to_line_protocol(&self, metrics: &ResourceMetrics) -> Vec<String> {
        let mut lines = Vec::new();
        
        for scope_metrics in &metrics.scope_metrics {
            for metric in &scope_metrics.metrics {
                let line = format!(
                    "{},service={} value={} {}",
                    metric.name,
                    metrics.resource.get("service.name").unwrap_or("unknown"),
                    // 简化示例，实际需处理不同 Aggregation 类型
                    "1.0",
                    chrono::Utc::now().timestamp_nanos()
                );
                lines.push(line);
            }
        }
        
        lines
    }
}

#[async_trait]
impl MetricExporter for InfluxDBExporter {
    async fn export(&self, metrics: &ResourceMetrics) -> opentelemetry::metrics::Result<()> {
        let lines = self.convert_to_line_protocol(metrics);
        let body = lines.join("\n");

        self.client
            .post(&format!("{}/api/v2/write", self.url))
            .header("Authorization", format!("Token {}", self.token))
            .body(body)
            .send()
            .await
            .map_err(|e| opentelemetry::metrics::MetricsError::Other(e.to_string()))?;

        Ok(())
    }

    fn force_flush(&self) -> opentelemetry::metrics::Result<()> {
        Ok(())
    }

    fn shutdown(&self) -> opentelemetry::metrics::Result<()> {
        Ok(())
    }
}

// 使用
let exporter = InfluxDBExporter::new(
    "http://localhost:8086".to_string(),
    "your-token".to_string(),
);

let reader = PeriodicReader::builder(exporter).build();
```

**依赖**：

```toml
[dependencies]
reqwest = { version = "0.12", features = ["json"] }
async-trait = "0.1"
chrono = "0.4"
```

---

## 错误处理

### **重试机制**

```rust
use std::time::Duration;

struct RetryableExporter {
    inner: Box<dyn MetricExporter>,
    max_retries: usize,
}

#[async_trait]
impl MetricExporter for RetryableExporter {
    async fn export(&self, metrics: &ResourceMetrics) -> opentelemetry::metrics::Result<()> {
        let mut attempts = 0;
        
        loop {
            match self.inner.export(metrics).await {
                Ok(_) => return Ok(()),
                Err(e) if attempts < self.max_retries => {
                    attempts += 1;
                    eprintln!("导出失败，重试 {}/{}: {:?}", attempts, self.max_retries, e);
                    tokio::time::sleep(Duration::from_secs(2u64.pow(attempts as u32))).await;
                }
                Err(e) => return Err(e),
            }
        }
    }

    async fn force_flush(&self) -> opentelemetry::metrics::Result<()> {
        self.inner.force_flush().await
    }

    fn shutdown(&self) -> opentelemetry::metrics::Result<()> {
        self.inner.shutdown()
    }
}
```

---

### **降级策略**

```rust
struct FallbackExporter {
    primary: Box<dyn MetricExporter>,
    fallback: Box<dyn MetricExporter>,
}

#[async_trait]
impl MetricExporter for FallbackExporter {
    async fn export(&self, metrics: &ResourceMetrics) -> opentelemetry::metrics::Result<()> {
        match self.primary.export(metrics).await {
            Ok(_) => Ok(()),
            Err(e) => {
                eprintln!("主导出器失败，使用备用: {:?}", e);
                self.fallback.export(metrics).await
            }
        }
    }

    // 其他方法实现...
}
```

---

## 性能优化

### **批量压缩**

```rust
use flate2::write::GzEncoder;
use flate2::Compression;

fn compress_payload(data: &[u8]) -> Vec<u8> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data).unwrap();
    encoder.finish().unwrap()
}

// 在自定义 Exporter 中使用
let compressed = compress_payload(body.as_bytes());
client
    .post(&url)
    .header("Content-Encoding", "gzip")
    .body(compressed)
    .send()
    .await?;
```

---

### **连接池复用**

```rust
use reqwest::Client;
use std::sync::Arc;

struct PooledExporter {
    client: Arc<Client>,  // 复用 HTTP 客户端
}

impl PooledExporter {
    fn new() -> Self {
        let client = Client::builder()
            .pool_max_idle_per_host(10)
            .timeout(Duration::from_secs(10))
            .build()
            .unwrap();
        
        Self {
            client: Arc::new(client),
        }
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **选择合适的传输协议**：
   - gRPC：低延迟、双向流
   - HTTP/JSON：防火墙友好、易调试
2. **配置超时**：导出超时应小于周期间隔的 50%
3. **实现重试**：网络抖动时自动重试
4. **压缩数据**：大规模指标导出应启用 gzip
5. **连接池**：复用 HTTP 连接减少握手开销
6. **监控导出状态**：记录导出成功率和延迟

### ❌ **避免**

1. **阻塞导出**：Exporter 不应执行同步阻塞操作
2. **忽略错误**：导出失败应记录日志
3. **无限重试**：应设置最大重试次数
4. **未关闭资源**：`shutdown()` 应清理连接和缓冲区

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"          # OTLP
opentelemetry-prometheus = "0.17"    # Prometheus
opentelemetry-stdout = "0.24"        # Stdout
tokio = { version = "1", features = ["full"] }
```

### **自定义 Exporter 依赖**

```toml
reqwest = { version = "0.12", features = ["json", "gzip"] }
async-trait = "0.1"
serde_json = "1.0"
flate2 = "1.0"             # gzip 压缩
```

---

## 总结

| Exporter | 协议 | 适用场景 | 配置要点 |
|----------|------|---------|---------|
| **OTLP gRPC** | gRPC | 标准后端 | `with_endpoint()` + `with_timeout()` |
| **OTLP HTTP** | HTTP/JSON | 防火墙环境 | `http()` + `with_headers()` |
| **Prometheus** | HTTP Pull | Prometheus | 暴露 `/metrics` 端点 |
| **Stdout** | 标准输出 | 本地调试 | 直接输出到控制台 |
| **自定义** | 任意 | InfluxDB/Datadog | 实现 `MetricExporter` trait |

**下一步**：完成 Metrics SDK 模块，进入 Logs SDK 文档编写
