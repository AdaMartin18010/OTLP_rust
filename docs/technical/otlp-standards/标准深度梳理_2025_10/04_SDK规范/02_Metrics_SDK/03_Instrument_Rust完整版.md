# Instrument - Rust 完整实现指南

## 📋 目录

- [Instrument - Rust 完整实现指南](#instrument---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Instrument 类型](#instrument-类型)
    - [**同步 vs 异步**](#同步-vs-异步)
    - [**累加 vs 瞬时值**](#累加-vs-瞬时值)
  - [Rust 实现](#rust-实现)
    - [Counter 详解](#counter-详解)
      - [**基础用法**](#基础用法)
      - [**线程安全的并发记录**](#线程安全的并发记录)
      - [**浮点数 Counter（f64）**](#浮点数-counterf64)
    - [UpDownCounter 详解](#updowncounter-详解)
      - [**连接池监控**](#连接池监控)
      - [**库存管理**](#库存管理)
    - [Histogram 详解](#histogram-详解)
      - [**HTTP 延迟监控**](#http-延迟监控)
      - [**自定义直方图边界**](#自定义直方图边界)
      - [**消息大小分布**](#消息大小分布)
    - [Observable 详解](#observable-详解)
      - [**ObservableGauge：系统资源监控**](#observablegauge系统资源监控)
      - [**ObservableCounter：累计进程 CPU 时间**](#observablecounter累计进程-cpu-时间)
      - [**ObservableUpDownCounter：实时队列长度**](#observableupdowncounter实时队列长度)
  - [属性管理](#属性管理)
    - [**低基数 vs 高基数**](#低基数-vs-高基数)
    - [**属性复用**](#属性复用)
    - [**语义约定**](#语义约定)
  - [聚合策略](#聚合策略)
  - [高级用法](#高级用法)
    - [**条件记录：采样控制**](#条件记录采样控制)
    - [**单位转换**](#单位转换)
    - [**多 Instrument 组合**](#多-instrument-组合)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**系统监控**](#系统监控)
    - [**工具库**](#工具库)
  - [总结](#总结)

---

## 核心概念

**Instrument** 是指标的数据记录接口，由 Meter 创建。OpenTelemetry 定义了 6 种标准 Instrument：

| 类型 | 行为 | 典型用途 |
|------|------|---------|
| **Counter** | 同步单调递增 | HTTP 请求数、错误数 |
| **UpDownCounter** | 同步可增可减 | 活跃连接数、队列长度 |
| **Histogram** | 同步分布记录 | 请求延迟、响应大小 |
| **ObservableCounter** | 异步单调递增 | 累计 CPU 时间 |
| **ObservableUpDownCounter** | 异步可增可减 | 当前内存使用 |
| **ObservableGauge** | 异步瞬时值 | CPU 温度、磁盘使用率 |

**关键特性**：

- **同步 Instrument**：业务代码主动调用 `add()`/`record()`
- **异步 Instrument**：SDK 定期回调 `with_callback()`
- **属性关联**：每个数据点可携带多维度标签

```text
┌────────────────────────────────────────────────┐
│                  Meter                         │
│  ┌──────────────────────────────────────────┐  │
│  │ Counter("http.requests")                 │  │
│  │   └─ add(1, [method=GET, status=200])    │  │
│  ├──────────────────────────────────────────┤  │
│  │ Histogram("http.duration")               │  │
│  │   └─ record(0.123, [route=/api/users])   │  │
│  ├──────────────────────────────────────────┤  │
│  │ ObservableGauge("cpu.usage")             │  │
│  │   └─ callback() → 45%                    │  │
│  └──────────────────────────────────────────┘  │
└────────────────────────────────────────────────┘
```

---

## Instrument 类型

### **同步 vs 异步**

| 维度 | 同步 Instrument | 异步 Instrument |
|------|----------------|----------------|
| **调用方式** | 业务代码主动调用 | SDK 定期回调 |
| **性能开销** | 每次调用都有开销 | 仅在导出时执行 |
| **适用场景** | 事件驱动（请求、错误） | 状态监控（CPU、内存） |
| **并发安全** | 需线程安全实现 | 回调内部需保证安全 |

### **累加 vs 瞬时值**

| 类型 | 语义 | 示例 |
|------|------|------|
| **Counter** | 永远递增 | 累计请求数 |
| **UpDownCounter** | 可增可减 | 当前队列长度 |
| **Gauge** | 最新值 | 当前 CPU 温度 |

---

## Rust 实现

### Counter 详解

#### **基础用法**

```rust
use opentelemetry::{global, KeyValue};

#[tokio::main]
async fn main() {
    let meter = global::meter("payment-service");
    
    // 创建 u64 Counter
    let payment_counter = meter
        .u64_counter("payments.processed")
        .with_description("Total successful payments")
        .with_unit("{payment}")
        .init();

    // 记录单笔支付
    payment_counter.add(1, &[
        KeyValue::new("payment.method", "credit_card"),
        KeyValue::new("currency", "USD"),
    ]);

    // 批量记录（如批处理场景）
    payment_counter.add(50, &[
        KeyValue::new("payment.method", "bank_transfer"),
        KeyValue::new("currency", "EUR"),
    ]);
}
```

---

#### **线程安全的并发记录**

```rust
use std::sync::Arc;
use tokio::task;

#[tokio::main]
async fn main() {
    let meter = global::meter("concurrent-service");
    let counter = Arc::new(
        meter
            .u64_counter("concurrent.operations")
            .init()
    );

    let mut handles = vec![];
    for i in 0..10 {
        let counter_clone = counter.clone();
        let handle = task::spawn(async move {
            for _ in 0..100 {
                counter_clone.add(1, &[KeyValue::new("worker_id", i.to_string())]);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("所有任务完成，共记录 1000 次操作");
}
```

---

#### **浮点数 Counter（f64）**

```rust
// 累计处理的数据量（GB）
let data_processed = meter
    .f64_counter("data.processed.bytes")
    .with_unit("By")
    .init();

data_processed.add(1024.5 * 1024.0 * 1024.0, &[
    KeyValue::new("source", "s3"),
]);
```

---

### UpDownCounter 详解

#### **连接池监控**

```rust
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

struct ConnectionPool {
    active_connections: Arc<AtomicI64>,
    counter: opentelemetry::metrics::UpDownCounter<i64>,
}

impl ConnectionPool {
    fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let counter = meter
            .i64_up_down_counter("db.pool.active")
            .with_description("Active database connections")
            .init();
        
        Self {
            active_connections: Arc::new(AtomicI64::new(0)),
            counter,
        }
    }

    fn acquire(&self) {
        let new_count = self.active_connections.fetch_add(1, Ordering::Relaxed) + 1;
        self.counter.add(1, &[KeyValue::new("pool", "postgres")]);
        println!("连接获取，当前活跃: {}", new_count);
    }

    fn release(&self) {
        let new_count = self.active_connections.fetch_sub(1, Ordering::Relaxed) - 1;
        self.counter.add(-1, &[KeyValue::new("pool", "postgres")]);
        println!("连接释放，当前活跃: {}", new_count);
    }
}

#[tokio::main]
async fn main() {
    let meter = global::meter("db-pool");
    let pool = Arc::new(ConnectionPool::new(&meter));

    // 模拟连接获取和释放
    for _ in 0..5 {
        let pool_clone = pool.clone();
        tokio::spawn(async move {
            pool_clone.acquire();
            tokio::time::sleep(Duration::from_secs(2)).await;
            pool_clone.release();
        });
    }

    tokio::time::sleep(Duration::from_secs(5)).await;
}
```

---

#### **库存管理**

```rust
let inventory = meter
    .i64_up_down_counter("inventory.stock")
    .with_unit("{item}")
    .init();

// 入库
inventory.add(100, &[
    KeyValue::new("product_id", "SKU-12345"),
    KeyValue::new("warehouse", "WH-01"),
]);

// 出库
inventory.add(-5, &[
    KeyValue::new("product_id", "SKU-12345"),
    KeyValue::new("warehouse", "WH-01"),
]);
```

---

### Histogram 详解

#### **HTTP 延迟监控**

```rust
use std::time::Instant;

#[tokio::main]
async fn main() {
    let meter = global::meter("http-server");
    let duration_histogram = meter
        .f64_histogram("http.server.duration")
        .with_description("HTTP request duration in seconds")
        .with_unit("s")
        .init();

    // 模拟请求处理
    let start = Instant::now();
    handle_request("/api/users", "GET").await;
    let duration = start.elapsed().as_secs_f64();

    duration_histogram.record(duration, &[
        KeyValue::new("http.method", "GET"),
        KeyValue::new("http.route", "/api/users"),
        KeyValue::new("http.status_code", 200),
    ]);
}

async fn handle_request(route: &str, method: &str) {
    tokio::time::sleep(Duration::from_millis(150)).await;
    println!("处理请求: {} {}", method, route);
}
```

---

#### **自定义直方图边界**

在 MeterProvider 中配置 View：

```rust
use opentelemetry_sdk::metrics::{
    Aggregation, Instrument, InstrumentKind, Stream, View,
};

fn create_latency_view() -> View {
    View::new(
        Instrument::new()
            .name("http.server.duration")
            .kind(InstrumentKind::Histogram),
        Stream::new()
            .aggregation(Aggregation::ExplicitBucketHistogram {
                boundaries: vec![
                    0.005, 0.01, 0.025, 0.05, 0.075, 0.1, 0.25, 0.5,
                    0.75, 1.0, 2.5, 5.0, 7.5, 10.0,
                ],
                record_min_max: true,
            }),
    )
}

// 在 MeterProvider 初始化时应用
let provider = SdkMeterProvider::builder()
    .with_view(create_latency_view())
    .with_reader(reader)
    .build();
```

---

#### **消息大小分布**

```rust
let message_size = meter
    .u64_histogram("kafka.message.size")
    .with_description("Kafka message size distribution")
    .with_unit("By")
    .init();

async fn send_message(data: &[u8]) {
    let size = data.len() as u64;
    message_size.record(size, &[
        KeyValue::new("topic", "user-events"),
        KeyValue::new("partition", "0"),
    ]);
    // 实际发送逻辑...
}
```

---

### Observable 详解

#### **ObservableGauge：系统资源监控**

```rust
use sysinfo::{System, SystemExt, ProcessorExt};
use std::sync::{Arc, Mutex};

#[tokio::main]
async fn main() {
    let meter = global::meter("system-monitor");
    let system = Arc::new(Mutex::new(System::new_all()));
    
    // CPU 使用率
    {
        let system_clone = system.clone();
        meter
            .f64_observable_gauge("system.cpu.utilization")
            .with_description("CPU utilization percentage")
            .with_unit("1")
            .with_callback(move |observer| {
                let sys = system_clone.lock().unwrap();
                for (i, processor) in sys.processors().iter().enumerate() {
                    observer.observe(
                        processor.cpu_usage() as f64 / 100.0,
                        &[KeyValue::new("cpu.id", i.to_string())],
                    );
                }
            })
            .init();
    }

    // 内存使用
    {
        let system_clone = system.clone();
        meter
            .u64_observable_gauge("system.memory.usage")
            .with_unit("By")
            .with_callback(move |observer| {
                let sys = system_clone.lock().unwrap();
                observer.observe(
                    sys.used_memory(),
                    &[KeyValue::new("state", "used")],
                );
                observer.observe(
                    sys.available_memory(),
                    &[KeyValue::new("state", "available")],
                );
            })
            .init();
    }

    // 后台刷新系统信息
    tokio::spawn(async move {
        loop {
            {
                let mut sys = system.lock().unwrap();
                sys.refresh_all();
            }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });

    tokio::signal::ctrl_c().await.unwrap();
}
```

**依赖**：

```toml
[dependencies]
sysinfo = "0.30"
```

---

#### **ObservableCounter：累计进程 CPU 时间**

```rust
use std::fs;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let meter = global::meter("process-monitor");

    meter
        .u64_observable_counter("process.cpu.time")
        .with_description("Cumulative CPU time consumed by the process")
        .with_unit("s")
        .with_callback(|observer| {
            if let Ok(cpu_time) = get_process_cpu_time() {
                observer.observe(cpu_time, &[
                    KeyValue::new("state", "user"),
                ]);
            }
        })
        .init();

    tokio::signal::ctrl_c().await.unwrap();
}

fn get_process_cpu_time() -> Result<u64, std::io::Error> {
    // Linux: 读取 /proc/self/stat
    #[cfg(target_os = "linux")]
    {
        let stat = fs::read_to_string("/proc/self/stat")?;
        let fields: Vec<&str> = stat.split_whitespace().collect();
        if fields.len() > 14 {
            let utime: u64 = fields[13].parse().unwrap_or(0);
            let stime: u64 = fields[14].parse().unwrap_or(0);
            // 转换为秒（假设时钟频率为 100 Hz）
            return Ok((utime + stime) / 100);
        }
    }
    Ok(0)
}
```

---

#### **ObservableUpDownCounter：实时队列长度**

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::VecDeque;

struct MessageQueue {
    queue: Arc<Mutex<VecDeque<String>>>,
}

impl MessageQueue {
    fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let queue = Arc::new(Mutex::new(VecDeque::new()));
        let queue_clone = queue.clone();

        meter
            .i64_observable_up_down_counter("queue.length")
            .with_description("Current queue length")
            .with_callback(move |observer| {
                let len = queue_clone.blocking_lock().len() as i64;
                observer.observe(len, &[KeyValue::new("queue", "main")]);
            })
            .init();

        Self { queue }
    }

    async fn push(&self, msg: String) {
        self.queue.lock().await.push_back(msg);
    }

    async fn pop(&self) -> Option<String> {
        self.queue.lock().await.pop_front()
    }
}

#[tokio::main]
async fn main() {
    let meter = global::meter("queue-monitor");
    let queue = MessageQueue::new(&meter);

    // 生产者
    tokio::spawn(async move {
        for i in 0..100 {
            queue.push(format!("message-{}", i)).await;
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });

    tokio::time::sleep(Duration::from_secs(30)).await;
}
```

---

## 属性管理

### **低基数 vs 高基数**

```rust
// ✅ 低基数属性（推荐）
histogram.record(duration, &[
    KeyValue::new("http.method", "GET"),        // ~10 个值
    KeyValue::new("http.status_code", 200),     // ~60 个值
    KeyValue::new("region", "us-east-1"),       // ~20 个值
]);

// ❌ 高基数属性（避免！）
histogram.record(duration, &[
    KeyValue::new("user_id", "123456"),         // 数百万个值
    KeyValue::new("request_id", uuid),          // 无限唯一值
    KeyValue::new("url.full", "/api/users?page=1&filter=..."), // 无限组合
]);
```

**高基数属性的危害**：

- **内存爆炸**：每个唯一属性组合都需要独立存储
- **导出缓慢**：数据点过多导致序列化开销巨大
- **后端压力**：时序数据库难以处理海量 series

---

### **属性复用**

```rust
// ❌ 每次创建新数组（性能差）
for i in 0..10000 {
    counter.add(1, &[KeyValue::new("region", "us-west-2")]);
}

// ✅ 复用属性数组
let attrs = [KeyValue::new("region", "us-west-2")];
for i in 0..10000 {
    counter.add(1, &attrs);
}
```

---

### **语义约定**

```rust
use opentelemetry_semantic_conventions as semconv;

duration_histogram.record(0.123, &[
    KeyValue::new(semconv::trace::HTTP_REQUEST_METHOD, "POST"),
    KeyValue::new(semconv::trace::HTTP_RESPONSE_STATUS_CODE, 201),
    KeyValue::new(semconv::trace::URL_PATH, "/api/orders"),
    KeyValue::new(semconv::trace::SERVER_ADDRESS, "api.example.com"),
]);
```

---

## 聚合策略

不同 Instrument 类型对应不同的默认聚合方式：

| Instrument 类型 | 默认聚合 | 输出数据 |
|----------------|---------|---------|
| Counter | Sum | 累计值 |
| UpDownCounter | Sum | 当前值 |
| Histogram | ExplicitBucketHistogram | 分布（桶计数 + min/max/sum） |
| ObservableGauge | LastValue | 最新值 |
| ObservableCounter | Sum | 累计值 |
| ObservableUpDownCounter | Sum | 当前值 |

**自定义聚合**（通过 View）：

```rust
// 将 Histogram 改为仅记录 Sum 和 Count（不保留分布）
View::new(
    Instrument::new()
        .name("http.server.duration")
        .kind(InstrumentKind::Histogram),
    Stream::new()
        .aggregation(Aggregation::Sum),
)
```

---

## 高级用法

### **条件记录：采样控制**

```rust
use rand::Rng;

let histogram = meter.f64_histogram("expensive.operation").init();

fn record_with_sampling(duration: f64) {
    // 仅采样 10% 的请求
    if rand::thread_rng().gen_bool(0.1) {
        histogram.record(duration, &[]);
    }
}
```

---

### **单位转换**

```rust
// 记录纳秒级延迟，但导出为秒
let start = Instant::now();
handle_request().await;
let nanos = start.elapsed().as_nanos() as f64;

duration_histogram.record(
    nanos / 1_000_000_000.0,  // 转换为秒
    &[KeyValue::new("unit", "s")],
);
```

---

### **多 Instrument 组合**

```rust
struct RequestMetrics {
    counter: opentelemetry::metrics::Counter<u64>,
    duration: opentelemetry::metrics::Histogram<f64>,
    active: opentelemetry::metrics::UpDownCounter<i64>,
}

impl RequestMetrics {
    fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        Self {
            counter: meter.u64_counter("http.requests").init(),
            duration: meter.f64_histogram("http.duration").with_unit("s").init(),
            active: meter.i64_up_down_counter("http.active").init(),
        }
    }

    async fn track_request<F, T>(&self, f: F, attrs: &[KeyValue]) -> T
    where
        F: Future<Output = T>,
    {
        self.active.add(1, attrs);
        let start = Instant::now();

        let result = f.await;

        let duration = start.elapsed().as_secs_f64();
        self.duration.record(duration, attrs);
        self.counter.add(1, attrs);
        self.active.add(-1, attrs);

        result
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **命名规范**：`{namespace}.{name}` 格式，使用小写 + 下划线
2. **单位明确**：遵循 [UCUM 规范](https://ucum.org/)（`s`、`By`、`{request}`）
3. **属性稳定**：不要用动态生成的高基数值
4. **描述完整**：`with_description()` 说明用途和单位
5. **异步回调轻量**：ObservableGauge 的回调应避免阻塞操作
6. **复用 Instrument**：静态初始化，避免重复创建

### ❌ **避免**

1. **高基数属性**：user_id、request_id、完整 URL
2. **过度细分**：不要为每个函数创建独立 Instrument
3. **忽略单位**：导致无法正确聚合
4. **阻塞回调**：Observable 回调不应有网络 I/O
5. **负值 Counter**：Counter 只能递增，负值会被忽略

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-semantic-conventions = "0.16"
tokio = { version = "1", features = ["full"] }
```

### **系统监控**

```toml
sysinfo = "0.30"           # 跨平台系统信息
procfs = "0.16"            # Linux 进程信息（更高性能）
```

### **工具库**

```toml
once_cell = "1.19"         # 懒加载静态变量
parking_lot = "0.12"       # 高性能锁
```

---

## 总结

| Instrument 类型 | 典型场景 | 关键方法 |
|----------------|---------|---------|
| Counter | 请求计数、错误数 | `add(value, attrs)` |
| UpDownCounter | 连接数、队列长度 | `add(delta, attrs)` |
| Histogram | 延迟、大小分布 | `record(value, attrs)` |
| ObservableGauge | CPU、内存使用率 | `with_callback(fn)` |
| ObservableCounter | 累计 CPU 时间 | `with_callback(fn)` |
| ObservableUpDownCounter | 实时队列长度 | `with_callback(fn)` |

**下一步**：[04_MetricReader_Rust完整版.md](./04_MetricReader_Rust完整版.md) - 学习指标的读取和导出策略
