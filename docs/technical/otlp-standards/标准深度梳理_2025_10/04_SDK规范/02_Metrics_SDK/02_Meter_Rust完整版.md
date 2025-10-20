# Meter - Rust 完整实现指南

## 📋 目录

- [Meter - Rust 完整实现指南](#meter---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Meter 的职责](#meter-的职责)
    - [1. **Instrument 创建**](#1-instrument-创建)
    - [2. **作用域管理**](#2-作用域管理)
  - [Rust 实现](#rust-实现)
    - [基础用法](#基础用法)
      - [**创建 Meter**](#创建-meter)
    - [Instrument 类型](#instrument-类型)
      - [**1. Counter：单调递增**](#1-counter单调递增)
      - [**2. UpDownCounter：可增可减**](#2-updowncounter可增可减)
      - [**3. Histogram：分布统计**](#3-histogram分布统计)
      - [**4. ObservableGauge：异步瞬时值**](#4-observablegauge异步瞬时值)
      - [**5. ObservableCounter：异步递增**](#5-observablecounter异步递增)
    - [属性最佳实践](#属性最佳实践)
      - [**语义约定**](#语义约定)
      - [**属性基数控制**](#属性基数控制)
    - [异步指标](#异步指标)
      - [**模式 1：定时轮询**](#模式-1定时轮询)
      - [**模式 2：事件驱动**](#模式-2事件驱动)
    - [高级模式](#高级模式)
      - [**条件记录：避免无效指标**](#条件记录避免无效指标)
      - [**批量记录：减少开销**](#批量记录减少开销)
  - [性能优化](#性能优化)
    - [**1. 属性复用**](#1-属性复用)
    - [**2. 懒加载 Instrument**](#2-懒加载-instrument)
    - [**3. 避免过度采样**](#3-避免过度采样)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**系统指标**](#系统指标)
    - [**工具库**](#工具库)
  - [总结](#总结)

---

## 核心概念

**Meter** 是创建指标仪器（Instrument）的工厂，由 MeterProvider 管理。每个 Meter 由 **instrumentation_scope** 唯一标识：

```rust
let meter = global::meter_with_version(
    "my-library",      // 库名
    "1.0.0",          // 版本
    "https://schema", // Schema URL（可选）
    None              // 属性（可选）
);
```

**关键特性**：

- **Instrument 工厂**：创建 Counter、Histogram、Gauge 等
- **作用域隔离**：不同库的指标互不干扰
- **懒初始化**：首次使用时才分配资源

```text
┌───────────────────────────────────────────────┐
│            MeterProvider                      │
│  ┌────────────────────────────────────────┐   │
│  │ Meter("http-server", "2.0.0")          │   │
│  │   ├─ Counter("http.requests")          │   │
│  │   ├─ Histogram("http.duration")        │   │
│  │   └─ UpDownCounter("active_requests")  │   │
│  ├────────────────────────────────────────┤   │
│  │ Meter("database", "1.5.0")             │   │
│  │   ├─ Counter("db.queries")             │   │
│  │   └─ Histogram("db.latency")           │   │
│  └────────────────────────────────────────┘   │
└───────────────────────────────────────────────┘
```

---

## Meter 的职责

### 1. **Instrument 创建**

| 类型 | 用途 | 示例 |
|------|------|------|
| **Counter** | 单调递增 | 请求数、错误数 |
| **UpDownCounter** | 可增可减 | 活跃连接数、队列长度 |
| **Histogram** | 分布统计 | 请求延迟、响应大小 |
| **ObservableCounter** | 异步递增 | 累计 CPU 时间 |
| **ObservableUpDownCounter** | 异步增减 | 当前内存使用 |
| **ObservableGauge** | 异步瞬时值 | CPU 温度、磁盘使用率 |

### 2. **作用域管理**

- 每个 Meter 关联一个 **instrumentation_scope**
- 后端可按 Meter 过滤/聚合指标
- 支持库版本升级时的平滑迁移

---

## Rust 实现

### 基础用法

#### **创建 Meter**

```rust
use opentelemetry::{global, KeyValue};

fn main() {
    // 方式 1: 简单名称
    let meter = global::meter("my-service");

    // 方式 2: 带版本号
    let meter = global::meter_with_version("my-service", "1.2.3", None, None);

    // 方式 3: 完整配置
    let meter = global::meter_with_scope(
        opentelemetry::InstrumentationScope::builder("my-service")
            .with_version("1.2.3")
            .with_schema_url("https://opentelemetry.io/schemas/1.20.0")
            .with_attributes([KeyValue::new("deployment", "production")])
            .build()
    );
}
```

---

### Instrument 类型

#### **1. Counter：单调递增**

```rust
use opentelemetry::{global, KeyValue};

#[tokio::main]
async fn main() {
    let meter = global::meter("http-server");
    
    // 创建 Counter
    let request_counter = meter
        .u64_counter("http.server.requests")
        .with_description("Total HTTP requests")
        .with_unit("{request}")
        .init();

    // 记录数据
    request_counter.add(
        1,
        &[
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.status_code", 200),
        ],
    );
}
```

**适用场景**：

- HTTP 请求数
- 处理的消息数
- 数据库查询次数

---

#### **2. UpDownCounter：可增可减**

```rust
let active_connections = meter
    .i64_up_down_counter("db.pool.active_connections")
    .with_description("Active database connections")
    .init();

// 新连接建立
active_connections.add(1, &[KeyValue::new("db.name", "postgres")]);

// 连接关闭
active_connections.add(-1, &[KeyValue::new("db.name", "postgres")]);
```

**适用场景**：

- 活跃连接数
- 队列中的消息数
- 内存中的缓存项数

---

#### **3. Histogram：分布统计**

```rust
let request_duration = meter
    .f64_histogram("http.server.duration")
    .with_description("HTTP request duration")
    .with_unit("s")
    .init();

// 记录延迟
let start = std::time::Instant::now();
handle_request().await;
let duration = start.elapsed().as_secs_f64();

request_duration.record(
    duration,
    &[
        KeyValue::new("http.method", "POST"),
        KeyValue::new("http.route", "/api/users"),
    ],
);
```

**适用场景**：

- 请求延迟
- 响应大小
- 批处理耗时

**自定义边界**（在 MeterProvider 中配置 View）：

```rust
// 见 01_MeterProvider_Rust完整版.md 的 View 配置
```

---

#### **4. ObservableGauge：异步瞬时值**

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let meter = global::meter("system-monitor");
    
    // 共享状态
    let cpu_usage = Arc::new(AtomicU64::new(0));
    let cpu_usage_clone = cpu_usage.clone();

    // 注册异步 Gauge
    let _gauge = meter
        .u64_observable_gauge("system.cpu.usage")
        .with_description("Current CPU usage percentage")
        .with_unit("%")
        .with_callback(move |observer| {
            let value = cpu_usage_clone.load(Ordering::Relaxed);
            observer.observe(value, &[KeyValue::new("cpu.id", "0")]);
        })
        .init();

    // 后台任务更新 CPU 使用率
    tokio::spawn(async move {
        loop {
            let usage = get_cpu_usage(); // 模拟获取 CPU 使用率
            cpu_usage.store(usage, Ordering::Relaxed);
            tokio::time::sleep(std::time::Duration::from_secs(5)).await;
        }
    });

    // Gauge 会在 MetricReader 周期性读取时自动调用回调
    tokio::signal::ctrl_c().await.unwrap();
}

fn get_cpu_usage() -> u64 {
    // 实际实现：读取 /proc/stat 或使用 sysinfo crate
    rand::random::<u64>() % 100
}
```

**适用场景**：

- CPU/内存使用率
- 磁盘容量
- 线程池大小

---

#### **5. ObservableCounter：异步递增**

```rust
use std::time::{SystemTime, UNIX_EPOCH};

let _counter = meter
    .u64_observable_counter("process.cpu.time")
    .with_description("Cumulative CPU time")
    .with_unit("s")
    .with_callback(|observer| {
        // 读取进程 CPU 时间（示例）
        let cpu_time = get_process_cpu_time();
        observer.observe(cpu_time, &[]);
    })
    .init();

fn get_process_cpu_time() -> u64 {
    // 实际实现：使用 procfs 或 sysinfo crate
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
```

---

### 属性最佳实践

#### **语义约定**

使用 OpenTelemetry 标准属性名：

```rust
use opentelemetry_semantic_conventions as semconv;

request_counter.add(
    1,
    &[
        KeyValue::new(semconv::trace::HTTP_REQUEST_METHOD, "GET"),
        KeyValue::new(semconv::trace::HTTP_RESPONSE_STATUS_CODE, 200),
        KeyValue::new(semconv::trace::URL_PATH, "/api/users"),
    ],
);
```

**依赖**：

```toml
[dependencies]
opentelemetry-semantic-conventions = "0.16"
```

---

#### **属性基数控制**

```rust
// ❌ 高基数属性（会导致指标爆炸）
counter.add(1, &[KeyValue::new("user_id", "12345678")]);

// ✅ 低基数属性
counter.add(
    1,
    &[
        KeyValue::new("http.method", "GET"),      // 枚举值
        KeyValue::new("http.status_code", 200),   // 有限值
        KeyValue::new("region", "us-west-2"),     // 受控制
    ],
);

// ✅ 使用 Resource 存储高基数信息
// 在 MeterProvider 初始化时设置 Resource:
// Resource::new(vec![KeyValue::new("service.instance.id", uuid)])
```

---

### 异步指标

#### **模式 1：定时轮询**

```rust
use sysinfo::{System, SystemExt};

#[tokio::main]
async fn main() {
    let meter = global::meter("system-metrics");
    let system = Arc::new(Mutex::new(System::new_all()));
    let system_clone = system.clone();

    // 内存使用 Gauge
    let _memory_gauge = meter
        .u64_observable_gauge("system.memory.used")
        .with_unit("By")
        .with_callback(move |observer| {
            let sys = system_clone.lock().unwrap();
            observer.observe(
                sys.used_memory(),
                &[KeyValue::new("state", "used")],
            );
        })
        .init();

    // 后台刷新系统信息
    tokio::spawn(async move {
        loop {
            system.lock().unwrap().refresh_memory();
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

#### **模式 2：事件驱动**

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

struct MessageQueue {
    size: Arc<AtomicUsize>,
}

impl MessageQueue {
    fn new(meter: &opentelemetry::metrics::Meter) -> Self {
        let size = Arc::new(AtomicUsize::new(0));
        let size_clone = size.clone();

        // 注册 Gauge 监控队列长度
        meter
            .u64_observable_gauge("queue.size")
            .with_callback(move |observer| {
                let value = size_clone.load(Ordering::Relaxed) as u64;
                observer.observe(value, &[]);
            })
            .init();

        Self { size }
    }

    fn push(&self, _msg: String) {
        self.size.fetch_add(1, Ordering::Relaxed);
    }

    fn pop(&self) -> Option<String> {
        if self.size.load(Ordering::Relaxed) > 0 {
            self.size.fetch_sub(1, Ordering::Relaxed);
            Some("message".to_string())
        } else {
            None
        }
    }
}
```

---

### 高级模式

#### **条件记录：避免无效指标**

```rust
let error_counter = meter.u64_counter("errors").init();

async fn process_request(result: Result<(), String>) {
    if let Err(e) = result {
        // 仅在错误时记录
        error_counter.add(
            1,
            &[
                KeyValue::new("error.type", e),
                KeyValue::new("severity", "error"),
            ],
        );
    }
}
```

---

#### **批量记录：减少开销**

```rust
use std::sync::Mutex;

struct BatchMetrics {
    request_counter: opentelemetry::metrics::Counter<u64>,
    buffer: Mutex<Vec<(u64, Vec<KeyValue>)>>,
}

impl BatchMetrics {
    fn record(&self, value: u64, attrs: Vec<KeyValue>) {
        let mut buffer = self.buffer.lock().unwrap();
        buffer.push((value, attrs));

        // 达到阈值时批量提交
        if buffer.len() >= 100 {
            for (val, attrs) in buffer.drain(..) {
                self.request_counter.add(val, &attrs);
            }
        }
    }

    fn flush(&self) {
        let mut buffer = self.buffer.lock().unwrap();
        for (val, attrs) in buffer.drain(..) {
            self.request_counter.add(val, &attrs);
        }
    }
}
```

---

## 性能优化

### **1. 属性复用**

```rust
// ❌ 每次都创建新属性
for _ in 0..1000 {
    counter.add(1, &[KeyValue::new("region", "us-east-1")]);
}

// ✅ 复用属性数组
let attrs = [KeyValue::new("region", "us-east-1")];
for _ in 0..1000 {
    counter.add(1, &attrs);
}
```

---

### **2. 懒加载 Instrument**

```rust
use once_cell::sync::Lazy;

static REQUEST_COUNTER: Lazy<opentelemetry::metrics::Counter<u64>> = Lazy::new(|| {
    global::meter("http-server")
        .u64_counter("requests")
        .init()
});

fn handle_request() {
    REQUEST_COUNTER.add(1, &[]);
}
```

**依赖**：

```toml
[dependencies]
once_cell = "1.19"
```

---

### **3. 避免过度采样**

```rust
use std::time::Duration;
use tokio::time::Instant;

struct RateLimitedHistogram {
    histogram: opentelemetry::metrics::Histogram<f64>,
    last_record: Mutex<Instant>,
    min_interval: Duration,
}

impl RateLimitedHistogram {
    fn record(&self, value: f64, attrs: &[KeyValue]) {
        let mut last = self.last_record.lock().unwrap();
        let now = Instant::now();
        
        if now.duration_since(*last) >= self.min_interval {
            self.histogram.record(value, attrs);
            *last = now;
        }
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **命名规范**：使用点号分隔（`http.server.duration`）
2. **单位明确**：在 `with_unit()` 中指定（`s`、`By`、`{request}`）
3. **描述完整**：`with_description()` 说明用途
4. **属性低基数**：避免用户 ID、URL 参数等
5. **异步指标缓存**：ObservableGauge 的回调应读取缓存，而非实时计算
6. **语义约定**：优先使用 `opentelemetry-semantic-conventions`

### ❌ **避免**

1. **重复创建 Meter**：同一作用域应复用 Meter 实例
2. **高基数属性**：如 `user_id`、`request_id`
3. **阻塞回调**：ObservableGauge 的回调不应有 I/O 操作
4. **忽略单位**：导致后端无法正确聚合
5. **过度细分 Meter**：不应为每个函数创建独立 Meter

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-semantic-conventions = "0.16"
tokio = { version = "1", features = ["full"] }
```

### **系统指标**

```toml
sysinfo = "0.30"           # 系统资源监控
procfs = "0.16"            # Linux 进程信息
```

### **工具库**

```toml
once_cell = "1.19"         # 懒加载静态变量
arc-swap = "1.7"           # 原子化 Arc 更新
```

---

## 总结

| 功能 | Instrument 类型 | 示例 |
|------|----------------|------|
| 计数累加 | Counter | 请求数、错误数 |
| 可增可减 | UpDownCounter | 活跃连接、队列长度 |
| 分布统计 | Histogram | 延迟、大小 |
| 异步瞬时值 | ObservableGauge | CPU、内存使用率 |
| 异步累加 | ObservableCounter | 累计 CPU 时间 |
| 异步增减 | ObservableUpDownCounter | 当前线程数 |

**下一步**：[03_Instrument_Rust完整版.md](./03_Instrument_Rust完整版.md) - 深入 Instrument 的高级配置
