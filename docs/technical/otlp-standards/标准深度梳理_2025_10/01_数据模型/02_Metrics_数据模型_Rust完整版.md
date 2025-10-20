# Metrics 数据模型 - Rust 完整版

## 目录

- [Metrics 数据模型 - Rust 完整版](#metrics-数据模型---rust-完整版)
  - [目录](#目录)
  - [1. Metrics 数据模型概述](#1-metrics-数据模型概述)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 数据流](#12-数据流)
  - [2. 指标类型](#2-指标类型)
    - [2.1 Counter (计数器)](#21-counter-计数器)
    - [2.2 UpDownCounter (双向计数器)](#22-updowncounter-双向计数器)
    - [2.3 Histogram (直方图)](#23-histogram-直方图)
    - [2.4 Gauge (仪表盘)](#24-gauge-仪表盘)
    - [2.5 ObservableCounter (可观测计数器)](#25-observablecounter-可观测计数器)
    - [2.6 ObservableGauge (可观测仪表盘)](#26-observablegauge-可观测仪表盘)
  - [3. Metric 数据结构](#3-metric-数据结构)
    - [3.1 Metric](#31-metric)
    - [3.2 DataPoint](#32-datapoint)
    - [3.3 Exemplar](#33-exemplar)
  - [4. Aggregation Temporality](#4-aggregation-temporality)
    - [4.1 Cumulative (累积)](#41-cumulative-累积)
    - [4.2 Delta (增量)](#42-delta-增量)
    - [4.3 对比](#43-对比)
  - [5. Rust 实现](#5-rust-实现)
    - [5.1 Counter 实现](#51-counter-实现)
    - [5.2 Histogram 实现](#52-histogram-实现)
    - [5.3 Gauge 实现](#53-gauge-实现)
    - [5.4 UpDownCounter 实现](#54-updowncounter-实现)
  - [6. 标签与维度](#6-标签与维度)
    - [6.1 标签设计](#61-标签设计)
    - [6.2 高基数问题](#62-高基数问题)
  - [7. OTLP 导出格式](#7-otlp-导出格式)
    - [7.1 Protobuf 定义](#71-protobuf-定义)
    - [7.2 Rust 导出](#72-rust-导出)
  - [8. Prometheus 集成](#8-prometheus-集成)
    - [8.1 Prometheus Exporter](#81-prometheus-exporter)
    - [8.2 数据模型映射](#82-数据模型映射)
  - [9. 完整示例](#9-完整示例)
    - [9.1 HTTP 服务器指标](#91-http-服务器指标)
    - [9.2 业务指标](#92-业务指标)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 命名规范](#101-命名规范)
    - [10.2 标签选择](#102-标签选择)
    - [10.3 性能优化](#103-性能优化)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [指标类型选择](#指标类型选择)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Metrics 数据模型概述

### 1.1 核心概念

````text
Metric (指标):
├─ Name: 指标名称 (http.server.duration)
├─ Description: 描述信息
├─ Unit: 单位 (ms, bytes, 1)
├─ Type: 指标类型 (Counter/Histogram/Gauge)
├─ DataPoints: 数据点集合
│  ├─ Attributes: 标签 (method=GET, status=200)
│  ├─ Value: 数值
│  ├─ StartTime: 开始时间
│  ├─ Time: 记录时间
│  └─ Exemplars: 示例 (关联 Trace)
└─ Aggregation Temporality: 聚合方式 (Cumulative/Delta)
````

### 1.2 数据流

````text
Application
    ↓
Meter.create_counter("http.requests")
    ↓
Counter.add(1, &[("method", "GET")])
    ↓
MetricReader (PeriodicExportingMetricReader)
    ↓
Aggregation (Sum/Histogram/LastValue)
    ↓
MetricExporter (OTLP/Prometheus)
    ↓
Backend (Prometheus/Grafana/Victoria Metrics)
````

---

## 2. 指标类型

### 2.1 Counter (计数器)

**特点**:

- 单调递增
- 只能增加，不能减少
- 累积值

**适用场景**:

- HTTP 请求总数
- 错误总数
- 发送字节总数

**Rust 实现**:

````rust
use opentelemetry::metrics::{Counter, Meter};

pub struct RequestMetrics {
    requests_total: Counter<u64>,
    errors_total: Counter<u64>,
}

impl RequestMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("http.server.requests")
                .with_description("Total number of HTTP requests")
                .with_unit("1")
                .build(),
            errors_total: meter
                .u64_counter("http.server.errors")
                .with_description("Total number of HTTP errors")
                .with_unit("1")
                .build(),
        }
    }

    pub fn record_request(&self, method: &str, status: u16) {
        self.requests_total.add(1, &[
            ("http.method", method.to_string()).into(),
            ("http.status_code", status.to_string()).into(),
        ]);

        if status >= 500 {
            self.errors_total.add(1, &[
                ("http.method", method.to_string()).into(),
            ]);
        }
    }
}
````

**Protobuf 结构**:

````protobuf
message Sum {
  repeated NumberDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;  // CUMULATIVE
  bool is_monotonic = 3;  // true for Counter
}
````

### 2.2 UpDownCounter (双向计数器)

**特点**:

- 可增可减
- 非单调

**适用场景**:

- 活跃连接数
- 队列长度
- 内存使用量

**Rust 实现**:

````rust
use opentelemetry::metrics::{UpDownCounter, Meter};

pub struct ConnectionMetrics {
    active_connections: UpDownCounter<i64>,
}

impl ConnectionMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            active_connections: meter
                .i64_up_down_counter("http.server.active_connections")
                .with_description("Number of active HTTP connections")
                .with_unit("1")
                .build(),
        }
    }

    pub fn on_connection_opened(&self) {
        self.active_connections.add(1, &[]);
    }

    pub fn on_connection_closed(&self) {
        self.active_connections.add(-1, &[]);
    }
}
````

### 2.3 Histogram (直方图)

**特点**:

- 记录值的分布
- 自动计算桶 (buckets)
- 可计算百分位数

**适用场景**:

- 请求延迟
- 响应大小
- 查询耗时

**Rust 实现**:

````rust
use opentelemetry::metrics::{Histogram, Meter};

pub struct LatencyMetrics {
    request_duration: Histogram<f64>,
}

impl LatencyMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP request duration")
                .with_unit("ms")
                .build(),
        }
    }

    pub fn record_duration(&self, duration_ms: f64, method: &str, status: u16) {
        self.request_duration.record(duration_ms, &[
            ("http.method", method.to_string()).into(),
            ("http.status_code", status.to_string()).into(),
        ]);
    }
}
````

**Protobuf 结构**:

````protobuf
message Histogram {
  repeated HistogramDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
}

message HistogramDataPoint {
  repeated KeyValue attributes = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  uint64 count = 4;  // 总数
  double sum = 5;    // 总和
  repeated uint64 bucket_counts = 6;  // 每个桶的计数
  repeated double explicit_bounds = 7;  // 桶边界
  repeated Exemplar exemplars = 8;
}
````

**默认桶边界** (Prometheus):

````text
[0, 5, 10, 25, 50, 75, 100, 250, 500, 750, 1000, 2500, 5000, 7500, 10000, +Inf]
````

### 2.4 Gauge (仪表盘)

**特点**:

- 可任意变化
- 记录当前值
- 非累积

**适用场景**:

- CPU 使用率
- 内存使用量
- 队列深度

**Rust 实现**:

````rust
use opentelemetry::metrics::{Gauge, Meter};

pub struct SystemMetrics {
    cpu_usage: Gauge<f64>,
    memory_usage: Gauge<u64>,
}

impl SystemMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            cpu_usage: meter
                .f64_gauge("system.cpu.usage")
                .with_description("CPU usage percentage")
                .with_unit("%")
                .build(),
            memory_usage: meter
                .u64_gauge("system.memory.usage")
                .with_description("Memory usage in bytes")
                .with_unit("bytes")
                .build(),
        }
    }

    pub fn update_cpu_usage(&self, usage: f64) {
        self.cpu_usage.record(usage, &[]);
    }

    pub fn update_memory_usage(&self, bytes: u64) {
        self.memory_usage.record(bytes, &[]);
    }
}
````

### 2.5 ObservableCounter (可观测计数器)

**特点**:

- 异步回调
- SDK 定期调用回调函数
- 适合外部数据源

**Rust 实现**:

````rust
use opentelemetry::metrics::Meter;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct AppState {
    pub processed_jobs: Arc<RwLock<u64>>,
}

pub fn register_observable_counter(meter: &Meter, state: AppState) {
    meter
        .u64_observable_counter("jobs.processed")
        .with_description("Total number of processed jobs")
        .with_callback(move |observer| {
            let state = state.clone();
            let count = tokio::runtime::Handle::current().block_on(async {
                *state.processed_jobs.read().await
            });
            observer.observe(count, &[]);
        })
        .build();
}
````

### 2.6 ObservableGauge (可观测仪表盘)

**Rust 实现**:

````rust
use opentelemetry::metrics::Meter;
use sysinfo::{System, SystemExt};

pub fn register_system_metrics(meter: &Meter) {
    // CPU 使用率
    meter
        .f64_observable_gauge("system.cpu.usage")
        .with_description("CPU usage percentage")
        .with_callback(|observer| {
            let mut sys = System::new_all();
            sys.refresh_cpu();
            let usage = sys.global_cpu_info().cpu_usage();
            observer.observe(usage as f64, &[]);
        })
        .build();

    // 内存使用量
    meter
        .u64_observable_gauge("system.memory.usage")
        .with_description("Memory usage in bytes")
        .with_callback(|observer| {
            let mut sys = System::new_all();
            sys.refresh_memory();
            let used = sys.used_memory();
            observer.observe(used, &[]);
        })
        .build();
}
````

---

## 3. Metric 数据结构

### 3.1 Metric

````rust
pub struct Metric {
    pub name: String,
    pub description: String,
    pub unit: String,
    pub data: MetricData,
}

pub enum MetricData {
    Sum(Sum),
    Gauge(Gauge),
    Histogram(Histogram),
    ExponentialHistogram(ExponentialHistogram),
    Summary(Summary),
}
````

### 3.2 DataPoint

````rust
pub struct NumberDataPoint {
    pub attributes: Vec<KeyValue>,
    pub start_time_unix_nano: u64,
    pub time_unix_nano: u64,
    pub value: NumberValue,
    pub exemplars: Vec<Exemplar>,
}

pub enum NumberValue {
    AsInt(i64),
    AsDouble(f64),
}
````

### 3.3 Exemplar

````text
Exemplar: 将 Metric 关联到 Trace
├─ Value: 指标值
├─ Timestamp: 时间戳
├─ TraceId: 关联的 Trace ID
├─ SpanId: 关联的 Span ID
└─ Attributes: 额外属性
````

**Rust 实现**:

````rust
use opentelemetry::trace::TraceContextExt;

pub fn record_with_exemplar(histogram: &Histogram<f64>, duration_ms: f64) {
    // 当前 Span 的 TraceId 和 SpanId 会自动作为 Exemplar
    let context = tracing::Span::current().context();
    let span_context = context.span().span_context();

    histogram.record(duration_ms, &[
        ("trace_id", span_context.trace_id().to_string()).into(),
        ("span_id", span_context.span_id().to_string()).into(),
    ]);
}
````

---

## 4. Aggregation Temporality

### 4.1 Cumulative (累积)

**特点**:

- 从程序启动开始累积
- 每次上报完整的累积值
- Prometheus 默认方式

**示例**:

````text
Time  | Counter Value | Reported Value
------|---------------|---------------
T0    | 0             | 0
T1    | 100           | 100 (累积)
T2    | 250           | 250 (累积)
T3    | 400           | 400 (累积)
````

### 4.2 Delta (增量)

**特点**:

- 只上报增量
- 两次采集之间的差值
- Statsd 默认方式

**示例**:

````text
Time  | Counter Value | Reported Value
------|---------------|---------------
T0    | 0             | 0
T1    | 100           | 100 (增量)
T2    | 250           | 150 (增量)
T3    | 400           | 150 (增量)
````

### 4.3 对比

| 方式 | 优势 | 劣势 | 适用场景 |
|------|------|------|---------|
| Cumulative | 数据完整、易于查询 | 存储开销大 | Prometheus |
| Delta | 存储开销小 | 数据可能丢失 | Statsd, Datadog |

**Rust 配置**:

````rust
use opentelemetry_sdk::metrics::{
    Aggregation, InstrumentKind, PeriodicReader,
    Temporality,
};

pub fn create_reader_with_temporality() -> PeriodicReader {
    PeriodicReader::builder(
        opentelemetry_otlp::MetricExporter::builder()
            .with_tonic()
            .build()
            .unwrap(),
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_temporality(|kind, _| {
        match kind {
            InstrumentKind::Counter | InstrumentKind::Histogram => {
                Temporality::Delta  // 增量
            }
            _ => Temporality::Cumulative  // 累积
        }
    })
    .build()
}
````

---

## 5. Rust 实现

### 5.1 Counter 实现

````rust
use opentelemetry::metrics::{Counter, Meter};

pub struct AppMetrics {
    requests_total: Counter<u64>,
    bytes_sent: Counter<u64>,
}

impl AppMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("app.requests.total")
                .with_description("Total requests")
                .build(),
            bytes_sent: meter
                .u64_counter("app.bytes.sent")
                .with_description("Total bytes sent")
                .with_unit("bytes")
                .build(),
        }
    }

    pub fn record_request(&self, method: &str, bytes: u64) {
        self.requests_total.add(1, &[
            ("method", method.to_string()).into(),
        ]);
        self.bytes_sent.add(bytes, &[]);
    }
}
````

### 5.2 Histogram 实现

````rust
use opentelemetry::metrics::{Histogram, Meter};

pub struct LatencyMetrics {
    request_duration: Histogram<f64>,
    response_size: Histogram<u64>,
}

impl LatencyMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("Request duration in milliseconds")
                .with_unit("ms")
                .build(),
            response_size: meter
                .u64_histogram("http.server.response.size")
                .with_description("Response size in bytes")
                .with_unit("bytes")
                .build(),
        }
    }

    pub fn record(&self, duration_ms: f64, size_bytes: u64, method: &str) {
        let attrs = &[("method", method.to_string()).into()];
        
        self.request_duration.record(duration_ms, attrs);
        self.response_size.record(size_bytes, attrs);
    }
}
````

### 5.3 Gauge 实现

````rust
use opentelemetry::metrics::{Gauge, Meter};

pub struct QueueMetrics {
    queue_depth: Gauge<i64>,
}

impl QueueMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            queue_depth: meter
                .i64_gauge("queue.depth")
                .with_description("Current queue depth")
                .with_unit("1")
                .build(),
        }
    }

    pub fn update_depth(&self, depth: i64, queue_name: &str) {
        self.queue_depth.record(depth, &[
            ("queue.name", queue_name.to_string()).into(),
        ]);
    }
}
````

### 5.4 UpDownCounter 实现

````rust
use opentelemetry::metrics::{UpDownCounter, Meter};

pub struct ResourceMetrics {
    active_tasks: UpDownCounter<i64>,
}

impl ResourceMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            active_tasks: meter
                .i64_up_down_counter("app.tasks.active")
                .with_description("Number of active tasks")
                .with_unit("1")
                .build(),
        }
    }

    pub fn task_started(&self, task_type: &str) {
        self.active_tasks.add(1, &[
            ("task.type", task_type.to_string()).into(),
        ]);
    }

    pub fn task_completed(&self, task_type: &str) {
        self.active_tasks.add(-1, &[
            ("task.type", task_type.to_string()).into(),
        ]);
    }
}
````

---

## 6. 标签与维度

### 6.1 标签设计

**推荐标签**:

````rust
// ✅ 低基数标签 (推荐)
&[
    ("http.method", "GET").into(),           // ~10 个值
    ("http.status_code", "200").into(),      // ~50 个值
    ("service.name", "api-gateway").into(),  // ~5 个值
]

// ❌ 高基数标签 (避免)
&[
    ("user.id", "12345").into(),             // 数百万个值
    ("request.id", "uuid-xxx").into(),       // 无限个值
    ("timestamp", "2025-10-09T12:34:56").into(),
]
````

### 6.2 高基数问题

**问题**: 每个唯一标签组合会生成一个时间序列。

````text
指标: http.server.requests
标签: method (10个值) × status (50个值) × service (5个值)
时间序列数: 10 × 50 × 5 = 2,500

如果添加 user_id (1,000,000个用户):
时间序列数: 10 × 50 × 5 × 1,000,000 = 2,500,000,000 (25亿！)
````

**解决方案**:

````rust
// 方案 1: 移除高基数标签
self.requests_total.add(1, &[
    ("method", "GET").into(),
    ("status", "200").into(),
    // 不包含 user_id
]);

// 方案 2: 使用 Exemplar 关联 Trace (保留详细信息)
self.request_duration.record(duration_ms, &[
    ("method", "GET").into(),
    // user_id 作为 Exemplar 关联到 Trace
]);
````

---

## 7. OTLP 导出格式

### 7.1 Protobuf 定义

````protobuf
message MetricsData {
  repeated ResourceMetrics resource_metrics = 1;
}

message ResourceMetrics {
  Resource resource = 1;
  repeated ScopeMetrics scope_metrics = 2;
}

message ScopeMetrics {
  InstrumentationScope scope = 1;
  repeated Metric metrics = 2;
}

message Metric {
  string name = 1;
  string description = 2;
  string unit = 3;
  oneof data {
    Gauge gauge = 4;
    Sum sum = 5;
    Histogram histogram = 6;
    ExponentialHistogram exponential_histogram = 7;
    Summary summary = 8;
  }
}
````

### 7.2 Rust 导出

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::metrics::{PeriodicReader, SdkMeterProvider};
use opentelemetry_otlp::MetricExporter;

pub fn init_metrics() -> anyhow::Result<()> {
    let exporter = MetricExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(10))
        .build()?;

    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(std::time::Duration::from_secs(60))
        .build();

    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(opentelemetry_sdk::Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
            KeyValue::new("service.version", "1.0.0"),
        ]))
        .build();

    global::set_meter_provider(provider);
    Ok(())
}
````

---

## 8. Prometheus 集成

### 8.1 Prometheus Exporter

````toml
[dependencies]
opentelemetry-prometheus = "0.17"
prometheus = "0.13"
````

````rust
use opentelemetry::metrics::Meter;
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::{Encoder, TextEncoder};

pub fn init_prometheus() -> PrometheusExporter {
    opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()
        .unwrap()
}

pub async fn metrics_handler(exporter: PrometheusExporter) -> String {
    let encoder = TextEncoder::new();
    let metric_families = exporter.registry().gather();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}
````

### 8.2 数据模型映射

| OpenTelemetry | Prometheus |
|---------------|------------|
| Counter | Counter |
| UpDownCounter | Gauge |
| Histogram | Histogram |
| Gauge | Gauge |
| ObservableCounter | Counter |
| ObservableGauge | Gauge |

---

## 9. 完整示例

### 9.1 HTTP 服务器指标

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram, UpDownCounter, Meter};
use axum::{
    extract::State,
    middleware::{self, Next},
    response::Response,
    Router,
    routing::get,
};
use std::time::Instant;

#[derive(Clone)]
pub struct HttpMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    active_requests: UpDownCounter<i64>,
}

impl HttpMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("http.server.requests")
                .with_description("Total HTTP requests")
                .build(),
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP request duration")
                .with_unit("ms")
                .build(),
            active_requests: meter
                .i64_up_down_counter("http.server.active_requests")
                .with_description("Active HTTP requests")
                .build(),
        }
    }
}

pub async fn metrics_middleware(
    State(metrics): State<HttpMetrics>,
    request: axum::http::Request<axum::body::Body>,
    next: Next,
) -> Response {
    let method = request.method().to_string();
    let path = request.uri().path().to_string();

    // 活跃请求 +1
    metrics.active_requests.add(1, &[]);

    let start = Instant::now();
    let response = next.run(request).await;
    let duration = start.elapsed().as_secs_f64() * 1000.0;

    // 活跃请求 -1
    metrics.active_requests.add(-1, &[]);

    // 记录指标
    let status = response.status().as_u16();
    let attrs = &[
        ("http.method", method).into(),
        ("http.route", path).into(),
        ("http.status_code", status.to_string()).into(),
    ];

    metrics.requests_total.add(1, attrs);
    metrics.request_duration.record(duration, attrs);

    response
}

pub fn app() -> Router {
    let meter = global::meter("http-server");
    let metrics = HttpMetrics::new(&meter);

    Router::new()
        .route("/", get(|| async { "Hello, World!" }))
        .layer(middleware::from_fn_with_state(
            metrics,
            metrics_middleware,
        ))
}
````

### 9.2 业务指标

````rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct OrderMetrics {
    orders_created: Counter<u64>,
    order_value: Histogram<f64>,
    payment_errors: Counter<u64>,
}

impl OrderMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            orders_created: meter
                .u64_counter("orders.created")
                .with_description("Total orders created")
                .build(),
            order_value: meter
                .f64_histogram("orders.value")
                .with_description("Order value distribution")
                .with_unit("USD")
                .build(),
            payment_errors: meter
                .u64_counter("orders.payment.errors")
                .with_description("Payment errors")
                .build(),
        }
    }

    pub fn record_order(&self, amount: f64, payment_method: &str) {
        self.orders_created.add(1, &[
            ("payment.method", payment_method.to_string()).into(),
        ]);
        self.order_value.record(amount, &[]);
    }

    pub fn record_payment_error(&self, error_type: &str) {
        self.payment_errors.add(1, &[
            ("error.type", error_type.to_string()).into(),
        ]);
    }
}
````

---

## 10. 最佳实践

### 10.1 命名规范

````text
格式: <namespace>.<component>.<metric_name>

推荐:
✅ http.server.requests
✅ http.server.duration
✅ db.connection.pool.size
✅ queue.depth

避免:
❌ HTTPServerRequests (大小写混用)
❌ http_server_requests (使用下划线)
❌ requests (缺少命名空间)
````

### 10.2 标签选择

````rust
// ✅ 推荐: 低基数标签
&[
    ("http.method", "GET").into(),
    ("http.status_code", "200").into(),
    ("service.name", "api").into(),
]

// ❌ 避免: 高基数标签
&[
    ("user.id", "12345").into(),
    ("request.id", "uuid").into(),
]
````

### 10.3 性能优化

````rust
// ✅ 推荐: 复用标签数组
static LABELS: &[(&str, &str)] = &[
    ("method", "GET"),
    ("status", "200"),
];

counter.add(1, LABELS);

// ❌ 避免: 每次创建新的标签
counter.add(1, &[
    ("method", "GET").into(),
    ("status", "200").into(),
]);
````

---

## 总结

### 核心要点

1. **指标类型**: Counter (单调递增)、UpDownCounter (可增可减)、Histogram (分布)、Gauge (当前值)
2. **Aggregation Temporality**: Cumulative (累积) vs Delta (增量)
3. **标签设计**: 避免高基数标签，推荐低基数标签
4. **Exemplar**: 将 Metric 关联到 Trace，保留详细上下文
5. **命名规范**: `<namespace>.<component>.<metric_name>`
6. **性能优化**: 复用标签数组，避免每次创建

### 指标类型选择

| 场景 | 推荐类型 | 原因 |
|------|---------|------|
| HTTP 请求总数 | Counter | 单调递增 |
| 活跃连接数 | UpDownCounter | 可增可减 |
| 请求延迟 | Histogram | 需要百分位数 |
| CPU 使用率 | Gauge | 当前值 |
| 队列长度 | Gauge / UpDownCounter | 当前值 |
| 错误总数 | Counter | 单调递增 |

### 最佳实践清单

- ✅ 使用语义化命名 (`http.server.duration`)
- ✅ 避免高基数标签 (不要包含 user_id)
- ✅ Counter 命名加 `.total` 后缀
- ✅ Histogram 单位明确 (ms, bytes)
- ✅ 使用 Exemplar 关联 Trace
- ✅ 定期导出指标 (60秒间隔)
- ✅ 使用 Prometheus 格式兼容
- ✅ 监控指标基数 (时间序列数量)
- ✅ 复用标签数组提升性能
- ✅ 为业务指标添加描述和单位

---

**相关文档**:

- [Metrics 最佳实践](../03_指标与度量/01_Metrics_最佳实践_Rust完整版.md)
- [Traces 数据模型](./01_Traces_数据模型_Rust完整版.md)
- [Logs 数据模型](./03_Logs_数据模型_Rust完整版.md)
- [性能优化指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
