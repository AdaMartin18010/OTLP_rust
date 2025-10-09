# Metrics 最佳实践 Rust 完整版

## 目录

- [Metrics 最佳实践 Rust 完整版](#metrics-最佳实践-rust-完整版)
  - [目录](#目录)
  - [一、Metrics 架构与概述](#一metrics-架构与概述)
    - [1.1 OpenTelemetry Metrics 架构](#11-opentelemetry-metrics-架构)
    - [1.2 Metrics 类型](#12-metrics-类型)
  - [二、依赖配置](#二依赖配置)
    - [2.1 Cargo.toml](#21-cargotoml)
  - [三、Metrics 类型详解](#三metrics-类型详解)
    - [3.1 初始化 MeterProvider](#31-初始化-meterprovider)
  - [四、Counter 计数器](#四counter-计数器)
    - [4.1 基础 Counter](#41-基础-counter)
    - [4.2 Axum 中间件集成](#42-axum-中间件集成)
  - [五、Histogram 直方图](#五histogram-直方图)
    - [5.1 延迟追踪](#51-延迟追踪)
    - [5.2 自定义桶边界](#52-自定义桶边界)
  - [六、Gauge 仪表](#六gauge-仪表)
    - [6.1 系统资源监控](#61-系统资源监控)
    - [6.2 应用状态监控](#62-应用状态监控)
  - [七、UpDownCounter 上下计数器](#七updowncounter-上下计数器)
    - [7.1 队列长度监控](#71-队列长度监控)
  - [八、标签与维度](#八标签与维度)
    - [8.1 标签最佳实践](#81-标签最佳实践)
    - [8.2 标签过滤](#82-标签过滤)
  - [九、聚合与导出](#九聚合与导出)
    - [9.1 Prometheus 导出器](#91-prometheus-导出器)
    - [9.2 OTLP 导出器](#92-otlp-导出器)
  - [十、业务指标](#十业务指标)
    - [10.1 电商业务指标](#101-电商业务指标)
  - [十一、性能监控](#十一性能监控)
    - [11.1 零分配 Metrics](#111-零分配-metrics)
  - [十二、生产环境完整示例](#十二生产环境完整示例)
    - [12.1 完整应用](#121-完整应用)
    - [12.2 Docker Compose 配置](#122-docker-compose-配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
    - [性能考虑](#性能考虑)

---

## 一、Metrics 架构与概述

### 1.1 OpenTelemetry Metrics 架构

````text
┌─────────────────────────────────────────┐
│      Application Instrumentation       │
│  (Counter, Histogram, Gauge, etc.)     │
└──────────────┬──────────────────────────┘
               ↓
     ┌─────────────────────┐
     │  MeterProvider      │
     │  - Aggregation      │
     │  - Exemplars        │
     └──────────┬──────────┘
                ↓
     ┌──────────────────────┐
     │  MetricReader        │
     │  - PeriodicReader    │
     │  - ManualReader      │
     └──────────┬──────────┘
                ↓
     ┌──────────────────────┐
     │  MetricExporter      │
     │  - OTLP              │
     │  - Prometheus        │
     └──────────────────────┘
````

### 1.2 Metrics 类型

| 类型 | 用途 | 示例 |
|------|------|------|
| **Counter** | 单调递增计数 | 请求总数、错误次数 |
| **Histogram** | 值分布统计 | 请求延迟、响应大小 |
| **Gauge** | 瞬时值测量 | CPU 使用率、内存占用 |
| **UpDownCounter** | 可增可减计数 | 活动连接数、队列长度 |

---

## 二、依赖配置

### 2.1 Cargo.toml

````toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "metrics"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic", "metrics"] }

# Prometheus 导出器
opentelemetry-prometheus = "0.17.0"
prometheus = "0.13"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# Web 框架
axum = { version = "0.8.7", features = ["macros"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
````

---

## 三、Metrics 类型详解

### 3.1 初始化 MeterProvider

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::metrics::{MeterProvider, PeriodicReader, SdkMeterProvider};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

pub fn init_metrics() -> anyhow::Result<SdkMeterProvider> {
    // 创建 OTLP 导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector::new()),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;
    
    // 创建周期性读取器
    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(30))
        .build();
    
    // 创建 MeterProvider
    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(
            opentelemetry_sdk::Resource::new(vec![
                KeyValue::new("service.name", "rust-metrics-app"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ])
        )
        .build();
    
    // 设置全局 MeterProvider
    global::set_meter_provider(provider.clone());
    
    Ok(provider)
}
````

---

## 四、Counter 计数器

### 4.1 基础 Counter

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;

pub struct HttpMetrics {
    request_count: Counter<u64>,
    error_count: Counter<u64>,
}

impl HttpMetrics {
    pub fn new() -> Self {
        let meter = global::meter("http-server");
        
        Self {
            request_count: meter
                .u64_counter("http.server.request.count")
                .with_description("HTTP 请求总数")
                .build(),
            error_count: meter
                .u64_counter("http.server.error.count")
                .with_description("HTTP 错误总数")
                .build(),
        }
    }
    
    pub fn record_request(&self, method: &str, path: &str, status: u16) {
        self.request_count.add(
            1,
            &[
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.route", path.to_string()),
                KeyValue::new("http.status_code", status as i64),
            ],
        );
    }
    
    pub fn record_error(&self, method: &str, path: &str, error_type: &str) {
        self.error_count.add(
            1,
            &[
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.route", path.to_string()),
                KeyValue::new("error.type", error_type.to_string()),
            ],
        );
    }
}
````

### 4.2 Axum 中间件集成

````rust
use axum::{
    body::Body,
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use std::sync::Arc;

pub async fn metrics_middleware(
    request: Request,
    next: Next,
) -> Response {
    let method = request.method().to_string();
    let path = request.uri().path().to_string();
    
    let response = next.run(request).await;
    let status = response.status().as_u16();
    
    // 记录请求
    let metrics = Arc::new(HttpMetrics::new());
    metrics.record_request(&method, &path, status);
    
    if status >= 400 {
        metrics.record_error(&method, &path, "http_error");
    }
    
    response
}
````

---

## 五、Histogram 直方图

### 5.1 延迟追踪

````rust
use opentelemetry::metrics::Histogram;
use std::time::Instant;

pub struct LatencyMetrics {
    request_duration: Histogram<f64>,
    database_duration: Histogram<f64>,
}

impl LatencyMetrics {
    pub fn new() -> Self {
        let meter = global::meter("latency");
        
        Self {
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP 请求耗时（毫秒）")
                .with_unit("ms")
                .build(),
            database_duration: meter
                .f64_histogram("db.query.duration")
                .with_description("数据库查询耗时（毫秒）")
                .with_unit("ms")
                .build(),
        }
    }
    
    pub fn record_request_duration(&self, method: &str, path: &str, duration_ms: f64) {
        self.request_duration.record(
            duration_ms,
            &[
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.route", path.to_string()),
            ],
        );
    }
    
    pub fn record_database_duration(&self, operation: &str, table: &str, duration_ms: f64) {
        self.database_duration.record(
            duration_ms,
            &[
                KeyValue::new("db.operation", operation.to_string()),
                KeyValue::new("db.table", table.to_string()),
            ],
        );
    }
}

// 使用示例
pub async fn handle_request(metrics: Arc<LatencyMetrics>) -> Result<(), anyhow::Error> {
    let start = Instant::now();
    
    // 处理请求
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    let duration = start.elapsed().as_millis() as f64;
    metrics.record_request_duration("GET", "/api/users", duration);
    
    Ok(())
}
````

### 5.2 自定义桶边界

````rust
use opentelemetry_sdk::metrics::data::Histogram as HistogramData;
use opentelemetry_sdk::metrics::aggregation::ExplicitBucketHistogramAggregation;

pub fn create_custom_histogram() -> Histogram<f64> {
    let meter = global::meter("custom");
    
    // 自定义桶边界（适合延迟监控）
    let boundaries = vec![
        5.0,    // 5ms
        10.0,   // 10ms
        25.0,   // 25ms
        50.0,   // 50ms
        100.0,  // 100ms
        250.0,  // 250ms
        500.0,  // 500ms
        1000.0, // 1s
        2500.0, // 2.5s
        5000.0, // 5s
    ];
    
    meter
        .f64_histogram("custom.duration")
        .with_description("自定义延迟分布")
        .with_unit("ms")
        .build()
}
````

---

## 六、Gauge 仪表

### 6.1 系统资源监控

````rust
use opentelemetry::metrics::{Gauge, ObservableGauge};
use sysinfo::{System, SystemExt, CpuExt};
use std::sync::{Arc, Mutex};

pub struct SystemMetrics {
    system: Arc<Mutex<System>>,
}

impl SystemMetrics {
    pub fn new() -> Self {
        let system = Arc::new(Mutex::new(System::new_all()));
        
        let meter = global::meter("system");
        
        // CPU 使用率
        let system_clone = system.clone();
        meter
            .f64_observable_gauge("system.cpu.usage")
            .with_description("CPU 使用率（百分比）")
            .with_unit("%")
            .with_callback(move |observer| {
                let mut sys = system_clone.lock().unwrap();
                sys.refresh_cpu();
                let usage = sys.global_cpu_info().cpu_usage();
                observer.observe(usage as f64, &[]);
            })
            .build();
        
        // 内存使用
        let system_clone = system.clone();
        meter
            .f64_observable_gauge("system.memory.usage")
            .with_description("内存使用量（字节）")
            .with_unit("By")
            .with_callback(move |observer| {
                let mut sys = system_clone.lock().unwrap();
                sys.refresh_memory();
                let used = sys.used_memory();
                observer.observe(used as f64, &[]);
            })
            .build();
        
        Self { system }
    }
}
````

### 6.2 应用状态监控

````rust
use std::sync::atomic::{AtomicU64, Ordering};

pub struct AppStateMetrics {
    active_connections: Arc<AtomicU64>,
}

impl AppStateMetrics {
    pub fn new() -> Self {
        let active_connections = Arc::new(AtomicU64::new(0));
        
        let meter = global::meter("app-state");
        
        let conn_clone = active_connections.clone();
        meter
            .u64_observable_gauge("app.active_connections")
            .with_description("活动连接数")
            .with_callback(move |observer| {
                let count = conn_clone.load(Ordering::Relaxed);
                observer.observe(count, &[]);
            })
            .build();
        
        Self { active_connections }
    }
    
    pub fn increment_connections(&self) {
        self.active_connections.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn decrement_connections(&self) {
        self.active_connections.fetch_sub(1, Ordering::Relaxed);
    }
}
````

---

## 七、UpDownCounter 上下计数器

### 7.1 队列长度监控

````rust
use opentelemetry::metrics::UpDownCounter;

pub struct QueueMetrics {
    queue_length: UpDownCounter<i64>,
    processing_items: UpDownCounter<i64>,
}

impl QueueMetrics {
    pub fn new() -> Self {
        let meter = global::meter("queue");
        
        Self {
            queue_length: meter
                .i64_up_down_counter("queue.length")
                .with_description("队列长度")
                .build(),
            processing_items: meter
                .i64_up_down_counter("queue.processing")
                .with_description("正在处理的项目数")
                .build(),
        }
    }
    
    pub fn enqueue(&self, queue_name: &str) {
        self.queue_length.add(1, &[KeyValue::new("queue.name", queue_name.to_string())]);
    }
    
    pub fn dequeue(&self, queue_name: &str) {
        self.queue_length.add(-1, &[KeyValue::new("queue.name", queue_name.to_string())]);
    }
    
    pub fn start_processing(&self, queue_name: &str) {
        self.processing_items.add(1, &[KeyValue::new("queue.name", queue_name.to_string())]);
    }
    
    pub fn finish_processing(&self, queue_name: &str) {
        self.processing_items.add(-1, &[KeyValue::new("queue.name", queue_name.to_string())]);
    }
}
````

---

## 八、标签与维度

### 8.1 标签最佳实践

````rust
pub struct LabeledMetrics {
    request_count: Counter<u64>,
}

impl LabeledMetrics {
    pub fn new() -> Self {
        let meter = global::meter("labeled");
        
        Self {
            request_count: meter
                .u64_counter("requests.total")
                .with_description("请求总数（带标签）")
                .build(),
        }
    }
    
    /// ✅ 好的标签设计：低基数
    pub fn record_good_labels(&self, method: &str, status: u16) {
        self.request_count.add(
            1,
            &[
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.status_code", status as i64),
                // 基数：5 methods × 10 status codes = 50 时间序列
            ],
        );
    }
    
    /// ❌ 不好的标签设计：高基数
    pub fn record_bad_labels(&self, user_id: &str, request_id: &str) {
        self.request_count.add(
            1,
            &[
                KeyValue::new("user.id", user_id.to_string()), // 高基数！
                KeyValue::new("request.id", request_id.to_string()), // 高基数！
                // 基数：百万用户 × 百万请求 = 万亿时间序列（爆炸！）
            ],
        );
    }
}
````

### 8.2 标签过滤

````rust
use opentelemetry_sdk::metrics::view::{View, Stream};

pub fn configure_label_filtering() -> SdkMeterProvider {
    let view = View::new()
        .with_attribute_keys(vec![
            "http.method".into(),
            "http.status_code".into(),
            // 只保留这些标签
        ]);
    
    SdkMeterProvider::builder()
        .with_view(view)
        .build()
}
````

---

## 九、聚合与导出

### 9.1 Prometheus 导出器

````rust
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::{Encoder, TextEncoder};

pub fn init_prometheus() -> anyhow::Result<PrometheusExporter> {
    let exporter = opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()?;
    
    global::set_meter_provider(exporter.provider()?);
    
    Ok(exporter)
}

// Axum 端点
pub async fn metrics_handler() -> String {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder.encode(&metric_families, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}
````

### 9.2 OTLP 导出器

````rust
pub fn init_otlp_metrics() -> anyhow::Result<SdkMeterProvider> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector::new()),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;
    
    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(10))
        .build();
    
    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .build();
    
    global::set_meter_provider(provider.clone());
    
    Ok(provider)
}
````

---

## 十、业务指标

### 10.1 电商业务指标

````rust
pub struct EcommerceMetrics {
    orders_created: Counter<u64>,
    order_value: Histogram<f64>,
    cart_size: Histogram<f64>,
    checkout_duration: Histogram<f64>,
}

impl EcommerceMetrics {
    pub fn new() -> Self {
        let meter = global::meter("ecommerce");
        
        Self {
            orders_created: meter
                .u64_counter("ecommerce.orders.created")
                .with_description("创建的订单数")
                .build(),
            order_value: meter
                .f64_histogram("ecommerce.order.value")
                .with_description("订单金额（美元）")
                .with_unit("USD")
                .build(),
            cart_size: meter
                .f64_histogram("ecommerce.cart.size")
                .with_description("购物车商品数量")
                .build(),
            checkout_duration: meter
                .f64_histogram("ecommerce.checkout.duration")
                .with_description("结账流程耗时（秒）")
                .with_unit("s")
                .build(),
        }
    }
    
    pub fn record_order(&self, value: f64, item_count: usize, duration_secs: f64) {
        self.orders_created.add(1, &[]);
        self.order_value.record(value, &[]);
        self.cart_size.record(item_count as f64, &[]);
        self.checkout_duration.record(duration_secs, &[]);
    }
}
````

---

## 十一、性能监控

### 11.1 零分配 Metrics

````rust
use std::sync::Arc;

pub struct ZeroAllocMetrics {
    request_count: Counter<u64>,
    // 预分配标签
    labels: Vec<KeyValue>,
}

impl ZeroAllocMetrics {
    pub fn new() -> Self {
        let meter = global::meter("zero-alloc");
        
        Self {
            request_count: meter
                .u64_counter("requests.fast")
                .build(),
            labels: vec![
                KeyValue::new("method", "GET"),
                KeyValue::new("status", 200),
            ],
        }
    }
    
    pub fn record_fast(&self) {
        self.request_count.add(1, &self.labels);
    }
}
````

---

## 十二、生产环境完整示例

### 12.1 完整应用

````rust
use axum::{
    extract::Extension,
    routing::{get, post},
    Router,
};
use opentelemetry::global;
use std::sync::Arc;
use std::time::Instant;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化 Metrics
    let _provider = init_metrics()?;
    
    // 创建指标
    let http_metrics = Arc::new(HttpMetrics::new());
    let latency_metrics = Arc::new(LatencyMetrics::new());
    let system_metrics = Arc::new(SystemMetrics::new());
    
    // 创建 Axum 应用
    let app = Router::new()
        .route("/api/users", get(handle_users))
        .route("/metrics", get(metrics_handler))
        .layer(Extension(http_metrics))
        .layer(Extension(latency_metrics));
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8000").await?;
    tracing::info!("Server started on <http://localhost:8000>");
    
    axum::serve(listener, app).await?;
    
    // 优雅关闭
    global::shutdown_meter_provider();
    
    Ok(())
}

async fn handle_users(
    Extension(metrics): Extension<Arc<HttpMetrics>>,
    Extension(latency): Extension<Arc<LatencyMetrics>>,
) -> &'static str {
    let start = Instant::now();
    
    // 模拟处理
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    let duration = start.elapsed().as_millis() as f64;
    latency.record_request_duration("GET", "/api/users", duration);
    metrics.record_request("GET", "/api/users", 200);
    
    "OK"
}
````

### 12.2 Docker Compose 配置

````yaml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8000:8000"
    environment:
      OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
  
  otel-collector:
    image: otel/opentelemetry-collector:0.116.1
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
  
  prometheus:
    image: prom/prometheus:v3.3.0
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
  
  grafana:
    image: grafana/grafana:11.5.0
    ports:
      - "3000:3000"
    environment:
      GF_SECURITY_ADMIN_PASSWORD: admin
````

---

## 总结

### 核心要点

1. **类型选择**：Counter、Histogram、Gauge、UpDownCounter
2. **标签设计**：低基数、有意义、可聚合
3. **聚合策略**：Delta vs Cumulative
4. **导出器**：OTLP、Prometheus
5. **性能优化**：预分配、零分配、批量导出

### 最佳实践

- Counter 用于单调递增（请求数、错误数）
- Histogram 用于分布统计（延迟、大小）
- Gauge 用于瞬时值（CPU、内存）
- UpDownCounter 用于可变计数（连接数、队列长度）
- 标签基数控制在 < 100

### 性能考虑

- 避免高基数标签（user_id、request_id）
- 使用预分配标签减少内存分配
- 批量导出减少网络开销
- 合理设置导出间隔（10-60秒）
- 监控指标数据本身的开销

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**OpenTelemetry 版本**: 0.31.0+
