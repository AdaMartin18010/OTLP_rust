# 📊 Instrument 类型 Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [📊 Instrument 类型 Rust 完整版](#-instrument-类型-rust-完整版)
  - [📋 目录](#-目录)
  - [1. Instrument 概述](#1-instrument-概述)
    - [1.1 什么是 Instrument？](#11-什么是-instrument)
    - [1.2 Instrument 分类](#12-instrument-分类)
    - [1.3 同步 vs 异步](#13-同步-vs-异步)
  - [2. Counter（计数器）](#2-counter计数器)
    - [2.1 Counter 定义](#21-counter-定义)
    - [2.2 基本使用](#22-基本使用)
    - [2.3 Counter 类型](#23-counter-类型)
    - [2.4 HTTP 请求计数](#24-http-请求计数)
    - [2.5 错误计数](#25-错误计数)
  - [3. UpDownCounter（双向计数器）](#3-updowncounter双向计数器)
    - [3.1 UpDownCounter 定义](#31-updowncounter-定义)
    - [3.2 基本使用](#32-基本使用)
    - [3.3 连接池监控](#33-连接池监控)
    - [3.4 队列长度监控](#34-队列长度监控)
  - [4. Histogram（直方图）](#4-histogram直方图)
    - [4.1 Histogram 定义](#41-histogram-定义)
    - [4.2 基本使用](#42-基本使用)
    - [4.3 请求延迟监控](#43-请求延迟监控)
    - [4.4 响应大小监控](#44-响应大小监控)
    - [4.5 数据库查询延迟](#45-数据库查询延迟)
  - [5. Gauge（仪表盘）](#5-gauge仪表盘)
    - [5.1 Gauge 定义](#51-gauge-定义)
    - [5.2 Observable Gauge](#52-observable-gauge)
    - [5.3 进程指标](#53-进程指标)
  - [6. Asynchronous Instruments](#6-asynchronous-instruments)
    - [6.1 异步 Counter](#61-异步-counter)
    - [6.2 异步 UpDownCounter](#62-异步-updowncounter)
  - [7. 类型选择指南](#7-类型选择指南)
    - [7.1 决策树](#71-决策树)
    - [7.2 场景示例表](#72-场景示例表)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 Instrument 命名](#81-instrument-命名)
    - [8.2 单位标准化](#82-单位标准化)
    - [8.3 属性控制](#83-属性控制)
    - [8.4 使用静态 Instruments](#84-使用静态-instruments)
  - [9. 性能优化](#9-性能优化)
    - [9.1 属性缓存](#91-属性缓存)
    - [9.2 批量记录](#92-批量记录)
  - [10. 实战案例](#10-实战案例)
    - [10.1 Web 服务完整监控](#101-web-服务完整监控)
    - [10.2 数据库连接池监控](#102-数据库连接池监控)
  - [🔗 参考资源](#-参考资源)

---

## 1. Instrument 概述

### 1.1 什么是 Instrument？

**Instrument** 是 OpenTelemetry Metrics 的核心抽象，用于记录应用程序的度量数据。

### 1.2 Instrument 分类

OpenTelemetry 定义了 6 种 Instrument 类型：

| Instrument | 同步/异步 | 单调性 | 用途 |
|-----------|-----------|--------|------|
| **Counter** | 同步 | 单调递增 | 请求数、错误数 |
| **UpDownCounter** | 同步 | 可增可减 | 活跃连接数、队列长度 |
| **Histogram** | 同步 | N/A | 请求延迟、响应大小 |
| **Asynchronous Counter** | 异步 | 单调递增 | CPU时间、进程启动时间 |
| **Asynchronous UpDownCounter** | 异步 | 可增可减 | 队列深度、内存使用 |
| **Asynchronous Gauge** | 异步 | N/A | CPU使用率、温度 |

### 1.3 同步 vs 异步

**同步 Instruments**:

- 在业务逻辑中主动记录
- 每次事件发生时调用
- 示例: `counter.add(1, &attrs)`

**异步 Instruments**:

- 通过回调定期采样
- SDK 定时调用回调函数
- 示例: `Observable Gauge` 监控内存使用

---

## 2. Counter（计数器）

### 2.1 Counter 定义

**Counter** 是单调递增的累积度量，用于记录只增不减的值。

**特性**:

- ✅ 只能增加，不能减少
- ✅ 初始值为 0
- ✅ 支持整数和浮点数
- ✅ 线程安全

### 2.2 基本使用

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;

fn basic_counter_example() {
    let meter = global::meter("my-service");
    
    // 创建 Counter
    let counter = meter
        .u64_counter("http_requests_total")
        .with_description("Total HTTP requests")
        .with_unit("requests")
        .init();
    
    // 记录值
    counter.add(1, &[
        KeyValue::new("method", "GET"),
        KeyValue::new("status", "200"),
    ]);
}
```

### 2.3 Counter 类型

**u64 Counter** (推荐):

```rust
let counter: Counter<u64> = meter
    .u64_counter("requests_total")
    .init();

counter.add(1, &[]);
counter.add(5, &[KeyValue::new("method", "POST")]);
```

**f64 Counter** (用于小数):

```rust
let counter: Counter<f64> = meter
    .f64_counter("data_processed_bytes")
    .init();

counter.add(1024.5, &[KeyValue::new("type", "upload")]);
```

### 2.4 HTTP 请求计数

```rust
use axum::{
    Router,
    routing::get,
    middleware::{self, Next},
    response::Response,
    http::Request,
};
use std::sync::OnceLock;

static HTTP_REQUESTS: OnceLock<Counter<u64>> = OnceLock::new();

fn init_metrics() {
    let meter = global::meter("http-server");
    HTTP_REQUESTS.set(
        meter
            .u64_counter("http_requests_total")
            .with_description("Total HTTP requests")
            .init()
    ).ok();
}

async fn metrics_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let method = request.method().clone();
    let path = request.uri().path().to_string();
    
    let response = next.run(request).await;
    
    let status = response.status();
    
    if let Some(counter) = HTTP_REQUESTS.get() {
        counter.add(1, &[
            KeyValue::new("method", method.to_string()),
            KeyValue::new("path", path),
            KeyValue::new("status", status.as_u16() as i64),
        ]);
    }
    
    response
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_metrics();
    
    let app = Router::new()
        .route("/", get(|| async { "Hello" }))
        .layer(middleware::from_fn(metrics_middleware));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

### 2.5 错误计数

```rust
use std::sync::OnceLock;

static ERROR_COUNTER: OnceLock<Counter<u64>> = OnceLock::new();

fn init_error_metrics() {
    let meter = global::meter("error-tracking");
    ERROR_COUNTER.set(
        meter
            .u64_counter("errors_total")
            .with_description("Total errors")
            .init()
    ).ok();
}

fn record_error(error_type: &str, severity: &str) {
    if let Some(counter) = ERROR_COUNTER.get() {
        counter.add(1, &[
            KeyValue::new("error.type", error_type.to_string()),
            KeyValue::new("error.severity", severity.to_string()),
        ]);
    }
}

// 使用
async fn process_request() -> Result<(), Error> {
    match risky_operation().await {
        Ok(result) => Ok(result),
        Err(e) => {
            record_error("database_error", "high");
            Err(e)
        }
    }
}
```

---

## 3. UpDownCounter（双向计数器）

### 3.1 UpDownCounter 定义

**UpDownCounter** 是可增可减的度量，用于记录当前值的变化。

**特性**:

- ✅ 可以增加和减少
- ✅ 可以为负数
- ✅ 适合跟踪当前状态

### 3.2 基本使用

```rust
use opentelemetry::metrics::UpDownCounter;

fn basic_updowncounter_example() {
    let meter = global::meter("my-service");
    
    let counter = meter
        .i64_up_down_counter("active_connections")
        .with_description("Number of active connections")
        .with_unit("connections")
        .init();
    
    // 连接建立
    counter.add(1, &[KeyValue::new("protocol", "http")]);
    
    // 连接关闭
    counter.add(-1, &[KeyValue::new("protocol", "http")]);
}
```

### 3.3 连接池监控

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct ConnectionPool {
    active: Arc<RwLock<usize>>,
    counter: UpDownCounter<i64>,
}

impl ConnectionPool {
    pub fn new() -> Self {
        let meter = global::meter("connection-pool");
        let counter = meter
            .i64_up_down_counter("pool.connections.active")
            .with_description("Active connections in the pool")
            .init();
        
        Self {
            active: Arc::new(RwLock::new(0)),
            counter,
        }
    }
    
    pub async fn acquire(&self) -> Connection {
        let mut active = self.active.write().await;
        *active += 1;
        
        self.counter.add(1, &[KeyValue::new("pool", "database")]);
        
        Connection::new(self.clone())
    }
    
    pub async fn release(&self) {
        let mut active = self.active.write().await;
        *active -= 1;
        
        self.counter.add(-1, &[KeyValue::new("pool", "database")]);
    }
}

pub struct Connection {
    pool: ConnectionPool,
}

impl Connection {
    fn new(pool: ConnectionPool) -> Self {
        Self { pool }
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        tokio::spawn({
            let pool = self.pool.clone();
            async move {
                pool.release().await;
            }
        });
    }
}
```

### 3.4 队列长度监控

```rust
use tokio::sync::mpsc;

pub struct MonitoredQueue<T> {
    sender: mpsc::Sender<T>,
    receiver: mpsc::Receiver<T>,
    counter: UpDownCounter<i64>,
}

impl<T> MonitoredQueue<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, receiver) = mpsc::channel(capacity);
        
        let meter = global::meter("queue");
        let counter = meter
            .i64_up_down_counter("queue.length")
            .with_description("Current queue length")
            .init();
        
        Self {
            sender,
            receiver,
            counter,
        }
    }
    
    pub async fn send(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.sender.send(item).await?;
        self.counter.add(1, &[KeyValue::new("queue", "tasks")]);
        Ok(())
    }
    
    pub async fn recv(&mut self) -> Option<T> {
        let item = self.receiver.recv().await;
        if item.is_some() {
            self.counter.add(-1, &[KeyValue::new("queue", "tasks")]);
        }
        item
    }
}
```

---

## 4. Histogram（直方图）

### 4.1 Histogram 定义

**Histogram** 记录值的分布，用于分析数据的统计特性。

**特性**:

- ✅ 记录值的分布（最小值、最大值、平均值、百分位数）
- ✅ 自动计算桶（buckets）
- ✅ 适合延迟、大小等度量

### 4.2 基本使用

```rust
use opentelemetry::metrics::Histogram;

fn basic_histogram_example() {
    let meter = global::meter("my-service");
    
    let histogram = meter
        .f64_histogram("http_request_duration_seconds")
        .with_description("HTTP request duration in seconds")
        .with_unit("s")
        .init();
    
    // 记录延迟
    histogram.record(0.125, &[
        KeyValue::new("method", "GET"),
        KeyValue::new("path", "/api/users"),
    ]);
}
```

### 4.3 请求延迟监控

```rust
use std::time::Instant;

async fn measure_request_duration<F, T>(
    operation_name: &str,
    histogram: &Histogram<f64>,
    f: F,
) -> T
where
    F: Future<Output = T>,
{
    let start = Instant::now();
    
    let result = f.await;
    
    let duration = start.elapsed().as_secs_f64();
    histogram.record(duration, &[
        KeyValue::new("operation", operation_name.to_string()),
    ]);
    
    result
}

// 使用
async fn handle_request() -> Result<Response, Error> {
    let meter = global::meter("http-server");
    let histogram = meter
        .f64_histogram("request_duration_seconds")
        .init();
    
    measure_request_duration(
        "handle_request",
        &histogram,
        async {
            process_request().await
        }
    ).await
}
```

### 4.4 响应大小监控

```rust
use axum::{
    body::Body,
    response::Response,
};

static RESPONSE_SIZE: OnceLock<Histogram<u64>> = OnceLock::new();

fn init_size_metrics() {
    let meter = global::meter("http-server");
    RESPONSE_SIZE.set(
        meter
            .u64_histogram("http_response_size_bytes")
            .with_description("HTTP response size in bytes")
            .with_unit("bytes")
            .init()
    ).ok();
}

async fn response_size_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let response = next.run(request).await;
    
    // 估算响应大小
    if let Some(content_length) = response.headers().get("content-length") {
        if let Ok(size_str) = content_length.to_str() {
            if let Ok(size) = size_str.parse::<u64>() {
                if let Some(histogram) = RESPONSE_SIZE.get() {
                    histogram.record(size, &[
                        KeyValue::new("status", response.status().as_u16() as i64),
                    ]);
                }
            }
        }
    }
    
    response
}
```

### 4.5 数据库查询延迟

```rust
use sqlx::{PgPool, Row};

pub struct MonitoredDatabase {
    pool: PgPool,
    histogram: Histogram<f64>,
}

impl MonitoredDatabase {
    pub fn new(pool: PgPool) -> Self {
        let meter = global::meter("database");
        let histogram = meter
            .f64_histogram("db_query_duration_seconds")
            .with_description("Database query duration")
            .with_unit("s")
            .init();
        
        Self { pool, histogram }
    }
    
    pub async fn query<T>(&self, sql: &str) -> Result<Vec<T>, sqlx::Error>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Unpin + Send,
    {
        let start = Instant::now();
        
        let result = sqlx::query_as(sql)
            .fetch_all(&self.pool)
            .await;
        
        let duration = start.elapsed().as_secs_f64();
        
        self.histogram.record(duration, &[
            KeyValue::new("query.success", result.is_ok()),
        ]);
        
        result
    }
}
```

---

## 5. Gauge（仪表盘）

### 5.1 Gauge 定义

**Gauge** 记录当前值的快照，通常用于异步观察。

**特性**:

- ✅ 记录瞬时值
- ✅ 通过回调定期采样
- ✅ 适合 CPU、内存等系统指标

### 5.2 Observable Gauge

```rust
use opentelemetry::metrics::ObservableGauge;
use sysinfo::{System, SystemExt, ProcessExt};

fn init_system_metrics() {
    let meter = global::meter("system");
    
    // CPU 使用率
    let _cpu_gauge = meter
        .f64_observable_gauge("system.cpu.utilization")
        .with_description("CPU utilization")
        .with_unit("percent")
        .with_callback(|observer| {
            let mut system = System::new_all();
            system.refresh_all();
            
            let cpu_usage = system.global_cpu_info().cpu_usage() as f64;
            observer.observe(cpu_usage, &[]);
        })
        .init();
    
    // 内存使用
    let _memory_gauge = meter
        .u64_observable_gauge("system.memory.usage")
        .with_description("Memory usage in bytes")
        .with_unit("bytes")
        .with_callback(|observer| {
            let mut system = System::new_all();
            system.refresh_all();
            
            let used_memory = system.used_memory();
            observer.observe(used_memory, &[]);
        })
        .init();
}
```

### 5.3 进程指标

```rust
fn init_process_metrics() {
    let meter = global::meter("process");
    
    // 线程数
    let _thread_gauge = meter
        .i64_observable_gauge("process.threads")
        .with_description("Number of threads")
        .with_callback(|observer| {
            let thread_count = std::thread::available_parallelism()
                .map(|n| n.get() as i64)
                .unwrap_or(0);
            observer.observe(thread_count, &[]);
        })
        .init();
    
    // 文件描述符
    let _fd_gauge = meter
        .i64_observable_gauge("process.open_file_descriptors")
        .with_description("Open file descriptors")
        .with_callback(|observer| {
            // 实际实现依赖平台
            #[cfg(target_os = "linux")]
            {
                use std::fs;
                if let Ok(entries) = fs::read_dir("/proc/self/fd") {
                    let count = entries.count() as i64;
                    observer.observe(count, &[]);
                }
            }
        })
        .init();
}
```

---

## 6. Asynchronous Instruments

### 6.1 异步 Counter

```rust
fn init_async_counter() {
    let meter = global::meter("async-metrics");
    
    let _async_counter = meter
        .u64_observable_counter("process.cpu.time")
        .with_description("CPU time consumed by process")
        .with_unit("s")
        .with_callback(|observer| {
            let cpu_time = get_process_cpu_time();
            observer.observe(cpu_time, &[
                KeyValue::new("state", "user"),
            ]);
        })
        .init();
}

fn get_process_cpu_time() -> u64 {
    // 平台特定实现
    0
}
```

### 6.2 异步 UpDownCounter

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

static QUEUE_DEPTH: Arc<RwLock<i64>> = Arc::new(RwLock::new(0));

fn init_async_updown_counter() {
    let meter = global::meter("queue");
    
    let _async_counter = meter
        .i64_observable_up_down_counter("queue.depth")
        .with_description("Current queue depth")
        .with_callback(move |observer| {
            let depth = *QUEUE_DEPTH.blocking_read();
            observer.observe(depth, &[
                KeyValue::new("queue", "tasks"),
            ]);
        })
        .init();
}
```

---

## 7. 类型选择指南

### 7.1 决策树

```text
需要记录度量？
    │
    ├─ 是否需要立即记录？
    │   │
    │   ├─ 是（同步）
    │   │   │
    │   │   ├─ 只增不减？
    │   │   │   └─ Counter
    │   │   │
    │   │   ├─ 可增可减？
    │   │   │   └─ UpDownCounter
    │   │   │
    │   │   └─ 需要分布信息？
    │   │       └─ Histogram
    │   │
    │   └─ 否（异步/定期采样）
    │       │
    │       ├─ 只增不减？
    │       │   └─ Asynchronous Counter
    │       │
    │       ├─ 可增可减？
    │       │   └─ Asynchronous UpDownCounter
    │       │
    │       └─ 当前值快照？
    │           └─ Gauge
```

### 7.2 场景示例表

| 场景 | 推荐类型 | 理由 |
|------|---------|------|
| HTTP 请求数 | Counter | 单调递增 |
| 活跃连接数 | UpDownCounter | 可增可减 |
| 请求延迟 | Histogram | 需要分布 |
| CPU 使用率 | Gauge | 瞬时值 |
| 累积 CPU 时间 | Async Counter | 单调递增 + 采样 |
| 内存使用 | Gauge | 瞬时值 |
| 队列长度 | UpDownCounter | 可增可减 |
| 响应大小 | Histogram | 需要分布 |
| 错误数 | Counter | 单调递增 |
| 缓存命中率 | Gauge | 计算值 |

---

## 8. 最佳实践

### 8.1 Instrument 命名

遵循 OpenTelemetry 语义约定：

```rust
// ✅ 好的命名
meter.u64_counter("http.server.requests")
meter.f64_histogram("http.server.duration")
meter.i64_up_down_counter("http.server.active_requests")

// ❌ 不好的命名
meter.u64_counter("requests")  // 太泛化
meter.f64_histogram("latency")  // 缺少上下文
meter.i64_up_down_counter("connections")  // 不明确
```

### 8.2 单位标准化

```rust
// ✅ 使用标准单位
meter
    .f64_histogram("http.server.duration")
    .with_unit("s")  // 秒
    .init();

meter
    .u64_histogram("http.server.response.size")
    .with_unit("bytes")  // 字节
    .init();

meter
    .f64_gauge("system.cpu.utilization")
    .with_unit("1")  // 比率（0-1）
    .init();
```

### 8.3 属性控制

```rust
// ✅ 限制属性基数
const MAX_PATH_SEGMENTS: usize = 3;

fn normalize_path(path: &str) -> String {
    let segments: Vec<&str> = path.split('/').collect();
    if segments.len() > MAX_PATH_SEGMENTS {
        format!("{}/*", segments[..MAX_PATH_SEGMENTS].join("/"))
    } else {
        path.to_string()
    }
}

counter.add(1, &[
    KeyValue::new("path", normalize_path("/api/users/123/orders/456")),
]);
// 结果: "/api/users/123/*"
```

### 8.4 使用静态 Instruments

```rust
use std::sync::OnceLock;

// ✅ 静态初始化（推荐）
static HTTP_REQUESTS: OnceLock<Counter<u64>> = OnceLock::new();

fn init_metrics() {
    let meter = global::meter("http");
    HTTP_REQUESTS.set(
        meter.u64_counter("requests_total").init()
    ).ok();
}

fn record_request() {
    if let Some(counter) = HTTP_REQUESTS.get() {
        counter.add(1, &[]);
    }
}

// ❌ 每次创建（性能差）
fn bad_record_request() {
    let meter = global::meter("http");
    let counter = meter.u64_counter("requests_total").init();
    counter.add(1, &[]);
}
```

---

## 9. 性能优化

### 9.1 属性缓存

```rust
use std::sync::OnceLock;

static COMMON_ATTRS: OnceLock<Vec<KeyValue>> = OnceLock::new();

fn init_common_attrs() {
    COMMON_ATTRS.set(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]).ok();
}

fn record_with_cached_attrs(counter: &Counter<u64>) {
    let mut attrs = COMMON_ATTRS.get().cloned().unwrap_or_default();
    attrs.push(KeyValue::new("dynamic", "value"));
    
    counter.add(1, &attrs);
}
```

### 9.2 批量记录

```rust
async fn batch_metrics_recording(events: Vec<Event>) {
    let counter = HTTP_REQUESTS.get().unwrap();
    
    // 聚合相同属性的事件
    let mut aggregated = std::collections::HashMap::new();
    
    for event in events {
        let key = (event.method.clone(), event.status);
        *aggregated.entry(key).or_insert(0) += 1;
    }
    
    // 批量记录
    for ((method, status), count) in aggregated {
        counter.add(count, &[
            KeyValue::new("method", method),
            KeyValue::new("status", status as i64),
        ]);
    }
}
```

---

## 10. 实战案例

### 10.1 Web 服务完整监控

```rust
use axum::{Router, routing::get};
use std::sync::OnceLock;

struct Metrics {
    requests: Counter<u64>,
    duration: Histogram<f64>,
    active: UpDownCounter<i64>,
}

static METRICS: OnceLock<Metrics> = OnceLock::new();

fn init_web_metrics() {
    let meter = global::meter("web-server");
    
    METRICS.set(Metrics {
        requests: meter.u64_counter("http_requests_total").init(),
        duration: meter.f64_histogram("http_request_duration_seconds").init(),
        active: meter.i64_up_down_counter("http_requests_active").init(),
    }).ok();
}

async fn metrics_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let metrics = METRICS.get().unwrap();
    let start = Instant::now();
    
    metrics.active.add(1, &[]);
    
    let method = request.method().clone();
    let response = next.run(request).await;
    let status = response.status();
    
    metrics.active.add(-1, &[]);
    
    let duration = start.elapsed().as_secs_f64();
    let attrs = vec![
        KeyValue::new("method", method.to_string()),
        KeyValue::new("status", status.as_u16() as i64),
    ];
    
    metrics.requests.add(1, &attrs);
    metrics.duration.record(duration, &attrs);
    
    response
}
```

### 10.2 数据库连接池监控

```rust
pub struct InstrumentedPool {
    pool: PgPool,
    metrics: PoolMetrics,
}

struct PoolMetrics {
    connections_active: UpDownCounter<i64>,
    connections_idle: Gauge<i64>,
    wait_duration: Histogram<f64>,
    acquire_count: Counter<u64>,
}

impl InstrumentedPool {
    pub fn new(pool: PgPool) -> Self {
        let meter = global::meter("database.pool");
        
        let metrics = PoolMetrics {
            connections_active: meter
                .i64_up_down_counter("db.pool.connections.active")
                .init(),
            connections_idle: meter
                .i64_gauge("db.pool.connections.idle")
                .with_callback(|observer| {
                    // 获取空闲连接数
                    let idle = get_idle_connections();
                    observer.observe(idle, &[]);
                })
                .init(),
            wait_duration: meter
                .f64_histogram("db.pool.acquire_duration_seconds")
                .init(),
            acquire_count: meter
                .u64_counter("db.pool.acquires_total")
                .init(),
        };
        
        Self { pool, metrics }
    }
    
    pub async fn acquire(&self) -> Result<PoolConnection, Error> {
        let start = Instant::now();
        
        let conn = self.pool.acquire().await?;
        
        let duration = start.elapsed().as_secs_f64();
        
        self.metrics.connections_active.add(1, &[]);
        self.metrics.wait_duration.record(duration, &[]);
        self.metrics.acquire_count.add(1, &[]);
        
        Ok(InstrumentedConnection {
            conn,
            metrics: self.metrics.clone(),
        })
    }
}

struct InstrumentedConnection {
    conn: PoolConnection,
    metrics: PoolMetrics,
}

impl Drop for InstrumentedConnection {
    fn drop(&mut self) {
        self.metrics.connections_active.add(-1, &[]);
    }
}
```

---

## 🔗 参考资源

- [OpenTelemetry Metrics Specification](https://opentelemetry.io/docs/specs/otel/metrics/api/)
- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry/)
- [Metrics 概述](./01_Metrics概述_Rust完整版.md)
- [Rust OTLP 最佳实践](../../17_最佳实践清单/Rust_OTLP_最佳实践Checklist.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../../README.md) | [📊 Metrics 概述](./01_Metrics概述_Rust完整版.md) | [📚 数据模型](../README.md)
