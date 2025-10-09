# Metrics 数据模型 - Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月9日

---

## 目录

- [Metrics 数据模型 - Rust 完整版](#metrics-数据模型---rust-完整版)
  - [目录](#目录)
  - [1. Rust 中的 Metrics 概述](#1-rust-中的-metrics-概述)
    - [1.1 什么是 Metrics](#11-什么是-metrics)
    - [1.2 OpenTelemetry Rust SDK 架构](#12-opentelemetry-rust-sdk-架构)
  - [2. Metrics 类型与 Rust 实现](#2-metrics-类型与-rust-实现)
    - [2.1 Counter](#21-counter)
    - [2.2 UpDownCounter](#22-updowncounter)
    - [2.3 Histogram](#23-histogram)
    - [2.4 Gauge (Observable)](#24-gauge-observable)
  - [3. Rust 类型安全设计](#3-rust-类型安全设计)
    - [3.1 类型安全的 Metric 包装器](#31-类型安全的-metric-包装器)
    - [3.2 泛型 Metric Builder](#32-泛型-metric-builder)
  - [4. 异步 Metrics 集成](#4-异步-metrics-集成)
    - [4.1 Tokio 任务中的 Metrics](#41-tokio-任务中的-metrics)
    - [4.2 异步回调 Gauge](#42-异步回调-gauge)
  - [5. Metrics 中间件与框架集成](#5-metrics-中间件与框架集成)
    - [5.1 Axum HTTP 服务器](#51-axum-http-服务器)
    - [5.2 Tonic gRPC 服务](#52-tonic-grpc-服务)
  - [6. 数据库 Metrics](#6-数据库-metrics)
    - [6.1 SQLx 连接池 Metrics](#61-sqlx-连接池-metrics)
  - [7. 自定义 Metrics](#7-自定义-metrics)
    - [7.1 业务指标](#71-业务指标)
  - [8. 基数控制与性能优化](#8-基数控制与性能优化)
    - [8.1 基数控制](#81-基数控制)
    - [8.2 属性缓存](#82-属性缓存)
  - [9. Metrics 导出与后端集成](#9-metrics-导出与后端集成)
    - [9.1 OTLP Exporter 配置](#91-otlp-exporter-配置)
    - [9.2 Prometheus Exporter](#92-prometheus-exporter)
  - [10. 测试与验证](#10-测试与验证)
    - [10.1 单元测试](#101-单元测试)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 DO's](#111-dos)
    - [11.2 DON'Ts](#112-donts)

---

## 1. Rust 中的 Metrics 概述

### 1.1 什么是 Metrics

**定义**：

```text
Metrics (指标): 在特定时间点采集的数值测量

Rust 实现特点:
1. 类型安全
   - Counter: u64/i64/f64
   - 编译时保证类型正确

2. 零成本抽象
   - 无运行时开销
   - 泛型特化优化

3. 并发安全
   - Arc<Mutex<_>> 或 Arc<RwLock<_>>
   - 原子操作 (AtomicU64, AtomicF64)

4. 生命周期管理
   - RAII 自动清理
   - Drop trait 资源回收

5. 异步友好
   - async/await 集成
   - Tokio 兼容
```

### 1.2 OpenTelemetry Rust SDK 架构

**依赖配置**：

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "metrics"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic", "metrics"] }
opentelemetry-semantic-conventions = "0.31"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# HTTP 框架
axum = "0.7"

# gRPC 框架
tonic = "0.12"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"
```

**初始化 Metrics**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    metrics::{MeterProvider, PeriodicReader, SdkMeterProvider},
    Resource,
};
use opentelemetry_otlp::MetricExporter;
use opentelemetry_semantic_conventions::resource::{SERVICE_NAME, SERVICE_VERSION};
use anyhow::Result;
use std::time::Duration;

/// 初始化 OpenTelemetry Metrics
///
/// # 功能
/// - 创建 OTLP Exporter (gRPC)
/// - 配置 PeriodicReader (60秒导出)
/// - 注册全局 MeterProvider
/// - 设置 Resource 属性
pub async fn init_metrics() -> Result<SdkMeterProvider> {
    // 1. 创建 OTLP Exporter
    let exporter = MetricExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 2. 创建 PeriodicReader
    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(60)) // 60秒导出一次
        .with_timeout(Duration::from_secs(10))  // 10秒超时
        .build();

    // 3. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, "rust-metrics-service"),
        KeyValue::new(SERVICE_VERSION, "1.0.0"),
    ]);

    // 4. 创建 MeterProvider
    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(resource)
        .build();

    // 5. 注册全局 MeterProvider
    global::set_meter_provider(provider.clone());

    Ok(provider)
}

/// 优雅关闭 Metrics
pub async fn shutdown_metrics(provider: SdkMeterProvider) -> Result<()> {
    provider.shutdown()?;
    Ok(())
}
```

**完整示例**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Meter;
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 初始化 Metrics
    let provider = init_metrics().await?;

    // 2. 获取 Meter
    let meter = global::meter("my-app");

    // 3. 创建 Counter
    let counter = meter
        .u64_counter("http.server.requests")
        .with_description("HTTP 请求总数")
        .with_unit("{request}")
        .init();

    // 4. 使用 Counter
    counter.add(1, &[
        KeyValue::new("http.method", "GET"),
        KeyValue::new("http.status_code", 200),
    ]);

    // 5. 等待导出
    tokio::time::sleep(tokio::time::Duration::from_secs(65)).await;

    // 6. 优雅关闭
    shutdown_metrics(provider).await?;

    Ok(())
}
```

---

## 2. Metrics 类型与 Rust 实现

### 2.1 Counter

**定义与特性**：

```text
Counter: 单调递增的累计值

特点:
- 只增不减
- 值 ≥ 0
- 类型: u64, f64

Rust 类型:
- Counter<u64>: 整数计数
- Counter<f64>: 浮点数计数 (如: 字节数)

线程安全:
- 内部使用原子操作
- 可以在多线程中共享 (Arc<Counter>)
```

**基础 Counter 实现**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;
use std::sync::Arc;

/// Counter 包装器
///
/// 提供类型安全的 Counter 操作
pub struct RequestCounter {
    counter: Counter<u64>,
}

impl RequestCounter {
    pub fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let counter = meter
            .u64_counter("http.server.requests")
            .with_description("HTTP 请求总数")
            .with_unit("{request}")
            .init();

        Self { counter }
    }

    /// 增加计数
    pub fn increment(&self, method: &str, status_code: u16) {
        self.counter.add(1, &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status_code as i64),
        ]);
    }

    /// 增加指定数量
    pub fn add(&self, count: u64, method: &str, status_code: u16) {
        self.counter.add(count, &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status_code as i64),
        ]);
    }
}

/// 使用示例
#[tokio::main]
async fn main() {
    let meter = global::meter("my-app");
    let counter = Arc::new(RequestCounter::new(&meter));

    // 在多线程中使用
    let handles: Vec<_> = (0..10)
        .map(|_| {
            let counter = Arc::clone(&counter);
            tokio::spawn(async move {
                counter.increment("GET", 200);
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
}
```

**浮点数 Counter (字节计数)**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;

/// 字节计数器
pub struct BytesCounter {
    counter: Counter<f64>,
}

impl BytesCounter {
    pub fn new(meter: &opentelemetry::metrics::Meter, direction: &str) -> Self {
        let counter = meter
            .f64_counter(format!("network.io.{}", direction))
            .with_description(format!("网络 {} 字节数", direction))
            .with_unit("By")  // 字节单位
            .init();

        Self { counter }
    }

    /// 记录字节数
    pub fn record(&self, bytes: usize, protocol: &str) {
        self.counter.add(bytes as f64, &[
            KeyValue::new("network.protocol.name", protocol.to_string()),
        ]);
    }
}

/// 使用示例
fn example_bytes_counter() {
    let meter = global::meter("my-app");
    let sent_bytes = BytesCounter::new(&meter, "sent");
    let recv_bytes = BytesCounter::new(&meter, "received");

    sent_bytes.record(1024, "tcp");
    recv_bytes.record(2048, "tcp");
}
```

### 2.2 UpDownCounter

**定义与特性**：

```text
UpDownCounter: 可增可减的累计值

特点:
- 可增可减
- 值可以是负数
- 类型: i64, f64

用途:
- 活跃连接数
- 队列长度
- 内存使用量
```

**UpDownCounter 实现**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::UpDownCounter;

/// 活跃连接计数器
pub struct ActiveConnectionCounter {
    counter: UpDownCounter<i64>,
}

impl ActiveConnectionCounter {
    pub fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let counter = meter
            .i64_up_down_counter("http.server.active_connections")
            .with_description("活跃 HTTP 连接数")
            .with_unit("{connection}")
            .init();

        Self { counter }
    }

    /// 连接建立，+1
    pub fn connection_opened(&self, protocol: &str) {
        self.counter.add(1, &[
            KeyValue::new("network.protocol.name", protocol.to_string()),
        ]);
    }

    /// 连接关闭，-1
    pub fn connection_closed(&self, protocol: &str) {
        self.counter.add(-1, &[
            KeyValue::new("network.protocol.name", protocol.to_string()),
        ]);
    }
}

/// RAII 连接守卫
///
/// 自动管理连接计数，利用 Drop trait
pub struct ConnectionGuard {
    counter: ActiveConnectionCounter,
    protocol: String,
}

impl ConnectionGuard {
    pub fn new(counter: ActiveConnectionCounter, protocol: String) -> Self {
        counter.connection_opened(&protocol);
        Self { counter, protocol }
    }
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        self.counter.connection_closed(&self.protocol);
    }
}

/// 使用示例
async fn handle_connection(counter: &ActiveConnectionCounter) {
    // 连接开始，自动 +1
    let _guard = ConnectionGuard::new(counter.clone(), "http".to_string());

    // 处理连接...
    tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;

    // _guard Drop，自动 -1
}
```

### 2.3 Histogram

**定义与特性**：

```text
Histogram: 值的分布统计

特点:
- 记录值的分布
- 支持百分位数
- 类型: u64, i64, f64

输出:
- count: 总观测数
- sum: 总和
- buckets: 各 bucket 的 count
- min/max: 最小/最大值
```

**Histogram 实现**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Histogram;
use std::time::Instant;

/// 请求延迟直方图
pub struct RequestDurationHistogram {
    histogram: Histogram<f64>,
}

impl RequestDurationHistogram {
    pub fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let histogram = meter
            .f64_histogram("http.server.duration")
            .with_description("HTTP 请求处理时间")
            .with_unit("s")
            .init();

        Self { histogram }
    }

    /// 记录请求延迟
    pub fn record(&self, duration_sec: f64, method: &str, route: &str, status_code: u16) {
        self.histogram.record(duration_sec, &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", route.to_string()),
            KeyValue::new("http.status_code", status_code as i64),
        ]);
    }
}

/// RAII 计时器
///
/// 自动测量操作时间并记录到 Histogram
pub struct DurationTimer {
    histogram: RequestDurationHistogram,
    start: Instant,
    method: String,
    route: String,
    status_code: u16,
}

impl DurationTimer {
    pub fn new(
        histogram: RequestDurationHistogram,
        method: String,
        route: String,
    ) -> Self {
        Self {
            histogram,
            start: Instant::now(),
            method,
            route,
            status_code: 200,
        }
    }

    /// 设置状态码
    pub fn set_status_code(&mut self, status_code: u16) {
        self.status_code = status_code;
    }
}

impl Drop for DurationTimer {
    fn drop(&mut self) {
        let duration = self.start.elapsed().as_secs_f64();
        self.histogram.record(
            duration,
            &self.method,
            &self.route,
            self.status_code,
        );
    }
}

/// 使用示例
async fn handle_request(histogram: &RequestDurationHistogram) -> Result<(), anyhow::Error> {
    let mut timer = DurationTimer::new(
        histogram.clone(),
        "GET".to_string(),
        "/api/users".to_string(),
    );

    // 处理请求...
    let result = process_request().await;

    if result.is_err() {
        timer.set_status_code(500);
    }

    result
}

async fn process_request() -> Result<(), anyhow::Error> {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}
```

**自定义 Bucket 边界**：

```rust
use opentelemetry_sdk::metrics::data::Histogram as HistogramData;
use opentelemetry_sdk::metrics::reader::TemporalitySelector;

/// 创建带自定义 bucket 的 Histogram
fn create_custom_histogram() {
    // 注意: OpenTelemetry Rust SDK 的 bucket 配置是在 View 级别设置的
    // 这里展示概念，具体实现需要通过 View 配置
    
    // 自定义 bucket 边界 (毫秒)
    let boundaries = vec![
        0.0, 5.0, 10.0, 25.0, 50.0, 75.0, 100.0, 250.0, 500.0, 750.0, 1000.0,
        2500.0, 5000.0, 7500.0, 10000.0,
    ];

    // 使用 View 配置 Histogram
    use opentelemetry_sdk::metrics::View;
    use opentelemetry_sdk::metrics::Instrument;

    let view = View::new(
        "http.server.duration",
        "Custom HTTP duration histogram",
    )
    .with_aggregation(opentelemetry_sdk::metrics::Aggregation::ExplicitBucketHistogram {
        boundaries: boundaries.clone(),
        record_min_max: true,
    });

    // 在 MeterProvider 创建时应用 View
    // 详细配置见下文
}
```

### 2.4 Gauge (Observable)

**定义与特性**：

```text
Gauge: 瞬时值观测

特点:
- 表示当前状态
- 通过回调函数采集
- 类型: u64, i64, f64

用途:
- CPU 使用率
- 内存使用量
- 队列长度
- 温度
```

**Observable Gauge 实现**：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Meter, ObservableGauge};
use std::sync::Arc;
use tokio::sync::RwLock;

/// 系统资源监控器
pub struct SystemMonitor {
    cpu_usage: Arc<RwLock<f64>>,
    memory_usage: Arc<RwLock<u64>>,
}

impl SystemMonitor {
    pub fn new(meter: &Meter) -> Self {
        let cpu_usage = Arc::new(RwLock::new(0.0));
        let memory_usage = Arc::new(RwLock::new(0));

        // 创建 CPU 使用率 Gauge
        let cpu_usage_clone = Arc::clone(&cpu_usage);
        let _cpu_gauge = meter
            .f64_observable_gauge("system.cpu.utilization")
            .with_description("CPU 使用率")
            .with_unit("1")
            .with_callback(move |observer| {
                let usage = tokio::runtime::Handle::current()
                    .block_on(cpu_usage_clone.read());
                observer.observe(*usage, &[]);
            })
            .init();

        // 创建内存使用量 Gauge
        let memory_usage_clone = Arc::clone(&memory_usage);
        let _memory_gauge = meter
            .u64_observable_gauge("process.runtime.memory.heap.used")
            .with_description("堆内存使用量")
            .with_unit("By")
            .with_callback(move |observer| {
                let usage = tokio::runtime::Handle::current()
                    .block_on(memory_usage_clone.read());
                observer.observe(*usage, &[]);
            })
            .init();

        Self {
            cpu_usage,
            memory_usage,
        }
    }

    /// 更新 CPU 使用率
    pub async fn update_cpu_usage(&self, usage: f64) {
        *self.cpu_usage.write().await = usage;
    }

    /// 更新内存使用量
    pub async fn update_memory_usage(&self, usage: u64) {
        *self.memory_usage.write().await = usage;
    }
}

/// 使用示例
#[tokio::main]
async fn main() {
    let meter = global::meter("my-app");
    let monitor = SystemMonitor::new(&meter);

    // 后台任务：定期更新系统指标
    tokio::spawn(async move {
        loop {
            // 获取 CPU 使用率
            let cpu_usage = get_cpu_usage().await;
            monitor.update_cpu_usage(cpu_usage).await;

            // 获取内存使用量
            let memory_usage = get_memory_usage().await;
            monitor.update_memory_usage(memory_usage).await;

            tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
        }
    });
}

async fn get_cpu_usage() -> f64 {
    // 实际实现：读取 /proc/stat 或使用 sysinfo crate
    0.65
}

async fn get_memory_usage() -> u64 {
    // 实际实现：读取 /proc/meminfo 或使用 sysinfo crate
    524288000 // ~500MB
}
```

**多维度 Gauge**：

```rust
use opentelemetry::{global, KeyValue};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 队列监控器
pub struct QueueMonitor {
    queues: Arc<RwLock<HashMap<String, u64>>>,
}

impl QueueMonitor {
    pub fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let queues = Arc::new(RwLock::new(HashMap::new()));

        let queues_clone = Arc::clone(&queues);
        let _gauge = meter
            .u64_observable_gauge("queue.length")
            .with_description("队列长度")
            .with_unit("{item}")
            .with_callback(move |observer| {
                let queues = tokio::runtime::Handle::current()
                    .block_on(queues_clone.read());
                
                for (queue_name, length) in queues.iter() {
                    observer.observe(*length, &[
                        KeyValue::new("queue.name", queue_name.clone()),
                    ]);
                }
            })
            .init();

        Self { queues }
    }

    /// 更新队列长度
    pub async fn update_queue_length(&self, queue_name: String, length: u64) {
        self.queues.write().await.insert(queue_name, length);
    }
}

/// 使用示例
async fn monitor_queues() {
    let meter = global::meter("my-app");
    let monitor = QueueMonitor::new(&meter);

    monitor.update_queue_length("orders".to_string(), 100).await;
    monitor.update_queue_length("payments".to_string(), 50).await;
    monitor.update_queue_length("notifications".to_string(), 200).await;
}
```

---

## 3. Rust 类型安全设计

### 3.1 类型安全的 Metric 包装器

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram, UpDownCounter, Meter};
use std::marker::PhantomData;

/// HTTP Metrics 包装器
///
/// 提供类型安全的 HTTP 指标记录
pub struct HttpMetrics {
    request_counter: Counter<u64>,
    duration_histogram: Histogram<f64>,
    active_requests: UpDownCounter<i64>,
}

impl HttpMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            request_counter: meter
                .u64_counter("http.server.requests")
                .with_description("HTTP 请求总数")
                .with_unit("{request}")
                .init(),

            duration_histogram: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP 请求处理时间")
                .with_unit("s")
                .init(),

            active_requests: meter
                .i64_up_down_counter("http.server.active_requests")
                .with_description("活跃 HTTP 请求数")
                .with_unit("{request}")
                .init(),
        }
    }

    /// 记录请求开始
    pub fn request_started(&self, method: &str, route: &str) {
        self.active_requests.add(1, &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", route.to_string()),
        ]);
    }

    /// 记录请求完成
    pub fn request_completed(
        &self,
        method: &str,
        route: &str,
        status_code: u16,
        duration: f64,
    ) {
        let attrs = [
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", route.to_string()),
            KeyValue::new("http.status_code", status_code as i64),
        ];

        self.request_counter.add(1, &attrs);
        self.duration_histogram.record(duration, &attrs);
        self.active_requests.add(-1, &attrs[..2]); // 只用 method 和 route
    }
}

/// HTTP 请求追踪器
///
/// 利用 RAII 自动记录请求指标
pub struct HttpRequestTracker {
    metrics: HttpMetrics,
    method: String,
    route: String,
    start: std::time::Instant,
    status_code: u16,
}

impl HttpRequestTracker {
    pub fn new(metrics: HttpMetrics, method: String, route: String) -> Self {
        metrics.request_started(&method, &route);
        Self {
            metrics,
            method,
            route,
            start: std::time::Instant::now(),
            status_code: 200,
        }
    }

    pub fn set_status_code(&mut self, status_code: u16) {
        self.status_code = status_code;
    }
}

impl Drop for HttpRequestTracker {
    fn drop(&mut self) {
        let duration = self.start.elapsed().as_secs_f64();
        self.metrics.request_completed(
            &self.method,
            &self.route,
            self.status_code,
            duration,
        );
    }
}
```

### 3.2 泛型 Metric Builder

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use std::marker::PhantomData;

/// 泛型 Counter Builder
pub struct CounterBuilder<T> {
    name: String,
    description: Option<String>,
    unit: Option<String>,
    _phantom: PhantomData<T>,
}

impl<T> CounterBuilder<T> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: None,
            unit: None,
            _phantom: PhantomData,
        }
    }

    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = Some(description.into());
        self
    }

    pub fn with_unit(mut self, unit: impl Into<String>) -> Self {
        self.unit = Some(unit.into());
        self
    }
}

impl CounterBuilder<u64> {
    pub fn build(self, meter: &Meter) -> Counter<u64> {
        let mut builder = meter.u64_counter(self.name);
        
        if let Some(desc) = self.description {
            builder = builder.with_description(desc);
        }
        if let Some(unit) = self.unit {
            builder = builder.with_unit(unit);
        }

        builder.init()
    }
}

impl CounterBuilder<f64> {
    pub fn build(self, meter: &Meter) -> Counter<f64> {
        let mut builder = meter.f64_counter(self.name);
        
        if let Some(desc) = self.description {
            builder = builder.with_description(desc);
        }
        if let Some(unit) = self.unit {
            builder = builder.with_unit(unit);
        }

        builder.init()
    }
}

/// 使用示例
fn example_generic_builder() {
    let meter = global::meter("my-app");

    let u64_counter = CounterBuilder::<u64>::new("requests.count")
        .with_description("请求计数")
        .with_unit("{request}")
        .build(&meter);

    let f64_counter = CounterBuilder::<f64>::new("data.bytes")
        .with_description("数据字节数")
        .with_unit("By")
        .build(&meter);
}
```

---

## 4. 异步 Metrics 集成

### 4.1 Tokio 任务中的 Metrics

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;
use std::sync::Arc;
use tokio::time::{sleep, Duration};

/// 任务 Metrics 监控
pub struct TaskMetrics {
    task_counter: Counter<u64>,
    task_duration: opentelemetry::metrics::Histogram<f64>,
}

impl TaskMetrics {
    pub fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        Self {
            task_counter: meter
                .u64_counter("tasks.completed")
                .with_description("完成的任务数")
                .with_unit("{task}")
                .init(),

            task_duration: meter
                .f64_histogram("tasks.duration")
                .with_description("任务执行时间")
                .with_unit("s")
                .init(),
        }
    }

    pub fn record_completion(&self, task_type: &str, duration: f64, success: bool) {
        self.task_counter.add(1, &[
            KeyValue::new("task.type", task_type.to_string()),
            KeyValue::new("task.success", success),
        ]);

        self.task_duration.record(duration, &[
            KeyValue::new("task.type", task_type.to_string()),
        ]);
    }
}

/// 使用示例：并发任务监控
#[tokio::main]
async fn main() {
    let meter = global::meter("my-app");
    let metrics = Arc::new(TaskMetrics::new(&meter));

    let mut handles = vec![];

    for i in 0..10 {
        let metrics = Arc::clone(&metrics);
        let handle = tokio::spawn(async move {
            let start = std::time::Instant::now();
            
            // 执行任务
            sleep(Duration::from_millis(100)).await;
            let success = i % 2 == 0; // 模拟成功/失败

            let duration = start.elapsed().as_secs_f64();
            metrics.record_completion("data_processing", duration, success);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

### 4.2 异步回调 Gauge

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Meter;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 异步系统监控器
pub struct AsyncSystemMonitor {
    connection_count: Arc<RwLock<u64>>,
}

impl AsyncSystemMonitor {
    pub fn new(meter: &Meter) -> Self {
        let connection_count = Arc::new(RwLock::new(0u64));

        let count_clone = Arc::clone(&connection_count);
        let _gauge = meter
            .u64_observable_gauge("system.connections.active")
            .with_description("活跃连接数")
            .with_unit("{connection}")
            .with_callback(move |observer| {
                // 在回调中异步读取
                let count = tokio::runtime::Handle::current()
                    .block_on(count_clone.read());
                observer.observe(*count, &[]);
            })
            .init();

        Self { connection_count }
    }

    pub async fn increment_connections(&self) {
        *self.connection_count.write().await += 1;
    }

    pub async fn decrement_connections(&self) {
        *self.connection_count.write().await -= 1;
    }
}
```

---

## 5. Metrics 中间件与框架集成

### 5.1 Axum HTTP 服务器

```rust
use axum::{
    Router,
    routing::get,
    extract::State,
    middleware::{self, Next},
    response::Response,
    http::{Request, StatusCode},
};
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram, UpDownCounter};
use std::sync::Arc;
use std::time::Instant;

/// Axum Metrics 中间件
#[derive(Clone)]
pub struct AxumMetrics {
    request_counter: Counter<u64>,
    duration_histogram: Histogram<f64>,
    active_requests: UpDownCounter<i64>,
}

impl AxumMetrics {
    pub fn new() -> Self {
        let meter = global::meter("axum");
        
        Self {
            request_counter: meter
                .u64_counter("http.server.requests")
                .with_description("HTTP 请求总数")
                .with_unit("{request}")
                .init(),

            duration_histogram: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP 请求处理时间")
                .with_unit("s")
                .init(),

            active_requests: meter
                .i64_up_down_counter("http.server.active_requests")
                .with_description("活跃 HTTP 请求数")
                .with_unit("{request}")
                .init(),
        }
    }
}

/// Metrics 中间件
pub async fn metrics_middleware<B>(
    State(metrics): State<Arc<AxumMetrics>>,
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let start = Instant::now();
    let method = req.method().to_string();
    let path = req.uri().path().to_string();

    // 请求开始
    metrics.active_requests.add(1, &[
        KeyValue::new("http.method", method.clone()),
        KeyValue::new("http.route", path.clone()),
    ]);

    // 处理请求
    let response = next.run(req).await;
    let status_code = response.status().as_u16();

    // 请求结束
    let duration = start.elapsed().as_secs_f64();
    let attrs = [
        KeyValue::new("http.method", method.clone()),
        KeyValue::new("http.route", path.clone()),
        KeyValue::new("http.status_code", status_code as i64),
    ];

    metrics.request_counter.add(1, &attrs);
    metrics.duration_histogram.record(duration, &attrs);
    metrics.active_requests.add(-1, &attrs[..2]);

    response
}

/// Axum 应用
async fn hello_handler() -> &'static str {
    "Hello, World!"
}

#[tokio::main]
async fn main() {
    let metrics = Arc::new(AxumMetrics::new());

    let app = Router::new()
        .route("/", get(hello_handler))
        .route("/api/users", get(hello_handler))
        .layer(middleware::from_fn_with_state(
            Arc::clone(&metrics),
            metrics_middleware,
        ))
        .with_state(metrics);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}
```

### 5.2 Tonic gRPC 服务

```rust
use tonic::{Request, Response, Status};
use tonic::service::Interceptor;
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram};
use std::sync::Arc;
use std::time::Instant;

/// gRPC Metrics
#[derive(Clone)]
pub struct GrpcMetrics {
    request_counter: Counter<u64>,
    duration_histogram: Histogram<f64>,
}

impl GrpcMetrics {
    pub fn new() -> Self {
        let meter = global::meter("grpc");
        
        Self {
            request_counter: meter
                .u64_counter("rpc.server.requests")
                .with_description("gRPC 请求总数")
                .with_unit("{request}")
                .init(),

            duration_histogram: meter
                .f64_histogram("rpc.server.duration")
                .with_description("gRPC 请求处理时间")
                .with_unit("s")
                .init(),
        }
    }

    pub fn record_request(&self, service: &str, method: &str, status: &str, duration: f64) {
        let attrs = [
            KeyValue::new("rpc.service", service.to_string()),
            KeyValue::new("rpc.method", method.to_string()),
            KeyValue::new("rpc.grpc.status_code", status.to_string()),
        ];

        self.request_counter.add(1, &attrs);
        self.duration_histogram.record(duration, &attrs);
    }
}

/// gRPC 拦截器
pub struct MetricsInterceptor {
    metrics: Arc<GrpcMetrics>,
    start: Instant,
    service: String,
    method: String,
}

impl Interceptor for MetricsInterceptor {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        self.start = Instant::now();
        
        // 提取 service 和 method
        let path = request.uri().path();
        let parts: Vec<&str> = path.split('/').collect();
        if parts.len() >= 3 {
            self.service = parts[1].to_string();
            self.method = parts[2].to_string();
        }

        Ok(request)
    }
}

// 注意: 完整的 gRPC 拦截器实现需要结合 tonic 的中间件机制
// 这里展示核心概念，实际实现可能需要自定义 Layer
```

---

## 6. 数据库 Metrics

### 6.1 SQLx 连接池 Metrics

```rust
use sqlx::postgres::{PgPoolOptions, PgPool};
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Meter, UpDownCounter, Histogram};
use std::sync::Arc;
use std::time::Instant;

/// 数据库 Metrics
pub struct DatabaseMetrics {
    pool_connections: opentelemetry::metrics::ObservableGauge<u64>,
    query_duration: Histogram<f64>,
    query_counter: opentelemetry::metrics::Counter<u64>,
}

impl DatabaseMetrics {
    pub fn new(meter: &Meter, pool: Arc<PgPool>) -> Self {
        // 连接池指标
        let pool_clone = Arc::clone(&pool);
        let pool_connections = meter
            .u64_observable_gauge("db.client.connections.usage")
            .with_description("数据库连接池使用情况")
            .with_unit("{connection}")
            .with_callback(move |observer| {
                let size = pool_clone.size();
                let idle = pool_clone.num_idle();
                
                observer.observe(size as u64, &[
                    KeyValue::new("state", "used"),
                    KeyValue::new("pool.name", "postgres"),
                ]);
                observer.observe(idle as u64, &[
                    KeyValue::new("state", "idle"),
                    KeyValue::new("pool.name", "postgres"),
                ]);
            })
            .init();

        // 查询时长
        let query_duration = meter
            .f64_histogram("db.client.operation.duration")
            .with_description("数据库查询时长")
            .with_unit("s")
            .init();

        // 查询计数
        let query_counter = meter
            .u64_counter("db.client.operations")
            .with_description("数据库操作计数")
            .with_unit("{operation}")
            .init();

        Self {
            pool_connections,
            query_duration,
            query_counter,
        }
    }

    pub fn record_query(&self, operation: &str, duration: f64, success: bool) {
        let attrs = [
            KeyValue::new("db.operation", operation.to_string()),
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("success", success),
        ];

        self.query_counter.add(1, &attrs);
        self.query_duration.record(duration, &attrs);
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = Arc::new(
        PgPoolOptions::new()
            .max_connections(10)
            .connect("postgres://user:pass@localhost/db")
            .await?
    );

    let meter = global::meter("database");
    let metrics = Arc::new(DatabaseMetrics::new(&meter, Arc::clone(&pool)));

    // 执行查询
    let start = Instant::now();
    let result = sqlx::query("SELECT * FROM users")
        .fetch_all(&*pool)
        .await;
    
    let duration = start.elapsed().as_secs_f64();
    metrics.record_query("SELECT", duration, result.is_ok());

    Ok(())
}
```

---

## 7. 自定义 Metrics

### 7.1 业务指标

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::{Counter, Histogram, Meter};

/// 订单业务指标
pub struct OrderMetrics {
    order_created: Counter<u64>,
    order_value: Histogram<f64>,
    order_items: Histogram<u64>,
}

impl OrderMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            order_created: meter
                .u64_counter("orders.created")
                .with_description("创建的订单数")
                .with_unit("{order}")
                .init(),

            order_value: meter
                .f64_histogram("orders.value")
                .with_description("订单金额")
                .with_unit("USD")
                .init(),

            order_items: meter
                .u64_histogram("orders.items")
                .with_description("订单商品数")
                .with_unit("{item}")
                .init(),
        }
    }

    pub fn record_order_created(
        &self,
        user_tier: &str,
        payment_method: &str,
        value: f64,
        items: u64,
    ) {
        let attrs = [
            KeyValue::new("user.tier", user_tier.to_string()),
            KeyValue::new("payment.method", payment_method.to_string()),
        ];

        self.order_created.add(1, &attrs);
        self.order_value.record(value, &attrs);
        self.order_items.record(items, &attrs);
    }
}

/// 使用示例
fn create_order_with_metrics(metrics: &OrderMetrics) {
    metrics.record_order_created(
        "premium",
        "credit_card",
        99.99,
        5,
    );
}
```

---

## 8. 基数控制与性能优化

### 8.1 基数控制

```rust
use opentelemetry::KeyValue;
use std::collections::HashSet;

/// 基数控制器
///
/// 限制属性值的唯一数量，防止基数爆炸
pub struct CardinalityLimiter {
    max_cardinality: usize,
    seen_values: HashSet<String>,
}

impl CardinalityLimiter {
    pub fn new(max_cardinality: usize) -> Self {
        Self {
            max_cardinality,
            seen_values: HashSet::new(),
        }
    }

    /// 获取受限的属性值
    ///
    /// 如果超过基数限制，返回 "OTHER"
    pub fn limit(&mut self, value: &str) -> String {
        if self.seen_values.contains(value) {
            value.to_string()
        } else if self.seen_values.len() < self.max_cardinality {
            self.seen_values.insert(value.to_string());
            value.to_string()
        } else {
            "OTHER".to_string()
        }
    }
}

/// 使用示例
fn example_cardinality_control() {
    let mut limiter = CardinalityLimiter::new(100);

    let user_id = "user-123456"; // 高基数维度
    let user_tier = limiter.limit(user_id); // 限制为 "OTHER"

    let attrs = [KeyValue::new("user.tier", user_tier)];
}
```

### 8.2 属性缓存

```rust
use opentelemetry::KeyValue;
use std::sync::Arc;
use once_cell::sync::Lazy;

/// 静态属性缓存
///
/// 预分配常用属性，避免重复创建
pub static COMMON_ATTRS: Lazy<CommonAttributes> = Lazy::new(|| CommonAttributes::new());

pub struct CommonAttributes {
    pub http_method_get: KeyValue,
    pub http_method_post: KeyValue,
    pub http_status_200: KeyValue,
    pub http_status_404: KeyValue,
    pub http_status_500: KeyValue,
}

impl CommonAttributes {
    fn new() -> Self {
        Self {
            http_method_get: KeyValue::new("http.method", "GET"),
            http_method_post: KeyValue::new("http.method", "POST"),
            http_status_200: KeyValue::new("http.status_code", 200),
            http_status_404: KeyValue::new("http.status_code", 404),
            http_status_500: KeyValue::new("http.status_code", 500),
        }
    }
}

/// 使用示例
fn example_cached_attributes() {
    let counter = global::meter("app").u64_counter("requests").init();

    // 复用预分配的属性
    counter.add(1, &[
        COMMON_ATTRS.http_method_get.clone(),
        COMMON_ATTRS.http_status_200.clone(),
    ]);
}
```

---

## 9. Metrics 导出与后端集成

### 9.1 OTLP Exporter 配置

```rust
use opentelemetry_sdk::metrics::{MeterProvider, PeriodicReader, SdkMeterProvider};
use opentelemetry_otlp::MetricExporter;
use std::time::Duration;

/// 完整的 Metrics 导出配置
pub async fn init_metrics_with_config() -> Result<SdkMeterProvider, anyhow::Error> {
    // OTLP Exporter
    let exporter = MetricExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build()?;

    // PeriodicReader 配置
    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(60))
        .with_timeout(Duration::from_secs(10))
        .build();

    // Resource
    let resource = opentelemetry_sdk::Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);

    // MeterProvider
    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(resource)
        .build();

    opentelemetry::global::set_meter_provider(provider.clone());

    Ok(provider)
}
```

### 9.2 Prometheus Exporter

```rust
use opentelemetry_sdk::metrics::{MeterProvider, SdkMeterProvider};
use opentelemetry_prometheus::PrometheusExporter;

/// Prometheus Exporter 配置
pub fn init_prometheus_metrics() -> Result<SdkMeterProvider, anyhow::Error> {
    let exporter = opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()?;

    let provider = SdkMeterProvider::builder()
        .with_reader(exporter)
        .build();

    opentelemetry::global::set_meter_provider(provider.clone());

    Ok(provider)
}

/// Prometheus HTTP 端点
use axum::{Router, routing::get};

async fn metrics_handler() -> String {
    use prometheus::Encoder;
    let encoder = prometheus::TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}

pub fn metrics_router() -> Router {
    Router::new().route("/metrics", get(metrics_handler))
}
```

---

## 10. 测试与验证

### 10.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::testing::metrics::InMemoryMetricsExporter;

    #[tokio::test]
    async fn test_counter_increment() {
        let exporter = InMemoryMetricsExporter::default();
        let reader = opentelemetry_sdk::metrics::PeriodicReader::builder(
            exporter.clone(),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();

        let provider = SdkMeterProvider::builder()
            .with_reader(reader)
            .build();

        let meter = provider.meter("test");
        let counter = meter.u64_counter("test.counter").init();

        counter.add(1, &[]);
        counter.add(2, &[]);

        provider.force_flush().unwrap();

        let metrics = exporter.get_finished_metrics().unwrap();
        assert_eq!(metrics.len(), 1);
        // 验证 sum = 3
    }
}
```

---

## 11. 最佳实践

### 11.1 DO's

```text
✅ 使用类型安全的 Metric 包装器
✅ 利用 RAII (Drop) 自动记录 metrics
✅ 预分配常用属性，减少分配开销
✅ 控制基数，避免高基数维度 (如 user_id, request_id)
✅ 使用 Arc 共享 Metrics 实例
✅ 异步导出，不阻塞主流程
✅ 批量导出，减少网络请求
✅ 为 Histogram 选择合适的 bucket 边界
✅ 使用语义约定命名 (http.server.*, db.client.*)
✅ 定期监控 metrics 基数和导出延迟
```

### 11.2 DON'Ts

```text
❌ 不要在热路径中动态创建 Metrics
❌ 不要使用高基数维度 (user_id, ip_address)
❌ 不要忽略错误处理
❌ 不要在同步代码中阻塞等待导出
❌ 不要过度细化维度 (导致基数爆炸)
❌ 不要忘记调用 shutdown()
❌ 不要在每次请求时分配新的 KeyValue
❌ 不要混用不同的 MeterProvider
```

---

**文档状态**: ✅ 完成  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**相关文档**: [SpanContext](../01_Traces数据模型/02_SpanContext_Rust完整版.md), [Logs概述](../03_Logs数据模型/01_Logs概述_Rust完整版.md)
