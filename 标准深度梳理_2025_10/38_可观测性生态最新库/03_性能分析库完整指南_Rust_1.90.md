# 性能分析库完整指南 - Rust 1.90 + OTLP

## 📋 目录

- [概述](#概述)
- [核心概念](#核心概念)
- [CPU Profiling](#cpu-profiling)
- [内存 Profiling](#内存-profiling)
- [火焰图生成](#火焰图生成)
- [基准测试](#基准测试)
- [OTLP 集成](#otlp-集成)
- [生产环境分析](#生产环境分析)
- [最佳实践](#最佳实践)
- [完整示例](#完整示例)

---

## 概述

### Rust 性能分析工具生态

| 工具 | 类型 | 特点 | 适用场景 |
|-----|------|------|---------|
| **pprof** | CPU/内存/堆 | Google 标准格式 | 生产环境持续分析 |
| **samply** | 采样分析 | 原生火焰图支持 | 开发调试 |
| **criterion** | 基准测试 | 统计分析 | 性能回归检测 |
| **dhat** | 堆分析 | Valgrind DHAT | 内存优化 |
| **heaptrack** | 内存泄漏 | 详细调用栈 | 内存泄漏排查 |
| **perf** | 系统级 | Linux 内核集成 | 底层性能分析 |
| **cargo-flamegraph** | 火焰图 | 一键生成 | 快速可视化 |

### 为什么需要性能分析?

```
问题: 应用 CPU 占用 80%,不知道哪个函数耗时高
  ↓
使用 pprof 采样分析
  ↓
发现: JSON 序列化占用 45%,某个循环占用 25%
  ↓
优化: 切换到 simd-json,重写循环为迭代器
  ↓
结果: CPU 占用降至 35%
```

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **采样数据** | 自定义 Metrics |
| **性能瓶颈** | Span Attributes |
| **资源使用** | Metrics(CPU/Memory) |
| **热点函数** | Tracing Events |

---

## 核心概念

### 1. 性能分析类型

```rust
// CPU Profiling: 哪个函数占用 CPU 时间最多
fn cpu_intensive() {
    for i in 0..1_000_000 {
        let _ = i * i;
    }
}

// Memory Profiling: 哪个函数分配内存最多
fn memory_intensive() {
    let mut v = Vec::new();
    for i in 0..1_000_000 {
        v.push(i);
    }
}

// Latency Profiling: 哪个操作延迟最高
async fn latency_test() {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

### 2. 采样 vs 插桩

| 方式 | 开销 | 精度 | 适用场景 |
|-----|------|------|---------|
| **采样(Sampling)** | 低(<5%) | 统计近似 | 生产环境 |
| **插桩(Instrumentation)** | 高(10-50%) | 精确 | 开发/测试 |

---

## CPU Profiling

### 1. pprof-rs

```toml
# Cargo.toml
[dependencies]
pprof = { version = "0.14", features = ["flamegraph", "protobuf-codec"] }
tokio = { version = "1.40", features = ["full"] }
```

```rust
use pprof::ProfilerGuard;
use std::fs::File;
use std::io::Write;

fn main() {
    // 启动 CPU Profiler
    let guard = ProfilerGuard::new(100).unwrap(); // 100 Hz 采样频率

    // 运行需要分析的代码
    cpu_intensive_work();

    // 生成报告
    if let Ok(report) = guard.report().build() {
        // 1. 生成 pprof 格式(可用 pprof 工具查看)
        let mut file = File::create("profile.pb").unwrap();
        let profile = report.pprof().unwrap();
        let mut content = Vec::new();
        profile.write_to_vec(&mut content).unwrap();
        file.write_all(&content).unwrap();

        println!("pprof 报告已保存到 profile.pb");

        // 2. 生成火焰图
        let file = File::create("flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();

        println!("火焰图已保存到 flamegraph.svg");
    }
}

fn cpu_intensive_work() {
    for _ in 0..1000 {
        calculate_fibonacci(30);
    }
}

fn calculate_fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => calculate_fibonacci(n - 1) + calculate_fibonacci(n - 2),
    }
}
```

### 2. 异步代码分析

```rust
use pprof::ProfilerGuardBuilder;

#[tokio::main]
async fn main() {
    let guard = ProfilerGuardBuilder::default()
        .frequency(100)
        .blocklist(&["libc", "libpthread"])
        .build()
        .unwrap();

    // 运行异步任务
    let handles: Vec<_> = (0..10)
        .map(|i| {
            tokio::spawn(async move {
                async_intensive_work(i).await;
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }

    // 生成报告
    if let Ok(report) = guard.report().build() {
        let file = File::create("async_flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();
        
        println!("异步火焰图已保存");
    }
}

async fn async_intensive_work(id: usize) {
    for _ in 0..100 {
        tokio::time::sleep(tokio::time::Duration::from_micros(100)).await;
        let _ = calculate_prime(1000 + id);
    }
}

fn calculate_prime(n: usize) -> Vec<usize> {
    let mut primes = Vec::new();
    for i in 2..n {
        if is_prime(i) {
            primes.push(i);
        }
    }
    primes
}

fn is_prime(n: usize) -> bool {
    if n < 2 {
        return false;
    }
    for i in 2..=(n as f64).sqrt() as usize {
        if n % i == 0 {
            return false;
        }
    }
    true
}
```

### 3. HTTP 服务分析

```rust
use axum::{
    extract::Query,
    routing::get,
    Router,
};
use pprof::ProfilerGuardBuilder;
use std::sync::{Arc, Mutex};

#[derive(Clone)]
struct AppState {
    profiler: Arc<Mutex<Option<ProfilerGuard<'static>>>>,
}

async fn start_profiling(
    axum::extract::State(state): axum::extract::State<AppState>,
) -> &'static str {
    let mut profiler = state.profiler.lock().unwrap();
    
    if profiler.is_some() {
        return "Profiling already running";
    }

    *profiler = Some(ProfilerGuardBuilder::default()
        .frequency(100)
        .build()
        .unwrap());

    "Profiling started"
}

async fn stop_profiling(
    axum::extract::State(state): axum::extract::State<AppState>,
) -> Vec<u8> {
    let mut profiler = state.profiler.lock().unwrap();
    
    if let Some(guard) = profiler.take() {
        if let Ok(report) = guard.report().build() {
            let mut flamegraph = Vec::new();
            report.flamegraph(&mut flamegraph).unwrap();
            return flamegraph;
        }
    }

    b"No active profiling session".to_vec()
}

#[tokio::main]
async fn main() {
    let state = AppState {
        profiler: Arc::new(Mutex::new(None)),
    };

    let app = Router::new()
        .route("/profile/start", get(start_profiling))
        .route("/profile/stop", get(stop_profiling))
        .route("/api/data", get(api_handler))
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    println!("服务运行在 http://localhost:3000");
    println!("访问 /profile/start 开始分析");
    println!("访问 /profile/stop 停止并获取火焰图");

    axum::serve(listener, app).await.unwrap();
}

async fn api_handler() -> String {
    // 模拟一些工作
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    let result = calculate_fibonacci(25);
    format!("Result: {}", result)
}
```

---

## 内存 Profiling

### 1. dhat-rs

```toml
[dependencies]
dhat = "0.3"
```

```rust
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    let _profiler = dhat::Profiler::new_heap();

    // 运行需要分析的代码
    memory_intensive_work();

    // Profiler 在 drop 时自动生成 dhat-heap.json
}

fn memory_intensive_work() {
    let mut data = Vec::new();
    
    // 大量小对象分配
    for i in 0..100_000 {
        data.push(Box::new(i));
    }

    // 大对象分配
    let big_buffer = vec![0u8; 10 * 1024 * 1024]; // 10MB

    // 短生命周期分配
    for _ in 0..1000 {
        let temp = vec![0; 1024];
        let _ = temp.len();
    }
}
```

**查看报告**:

```bash
# 生成的 dhat-heap.json 可以上传到:
# https://nnethercote.github.io/dh_view/dh_view.html
```

### 2. heaptrack

```bash
# 安装 heaptrack
sudo apt install heaptrack

# 运行分析
heaptrack ./target/release/myapp

# 查看报告
heaptrack_gui heaptrack.myapp.*.gz
```

```rust
// 示例: 检测内存泄漏
use std::sync::Arc;

fn main() {
    let mut leaks = Vec::new();

    for i in 0..1000 {
        // 模拟内存泄漏
        let data = Arc::new(vec![0u8; 1024 * 1024]); // 1MB
        leaks.push(data);

        if i % 100 == 0 {
            println!("Allocated {} MB", (i + 1));
        }
    }

    println!("Press Enter to exit...");
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();
}
```

---

## 火焰图生成

### 1. cargo-flamegraph

```bash
# 安装
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin myapp

# 指定参数
cargo flamegraph --bin myapp -- --arg1 value1
```

### 2. samply

```bash
# 安装
cargo install samply

# 运行分析
samply record ./target/release/myapp

# 自动打开浏览器查看交互式火焰图
```

### 3. 自定义火焰图

```rust
use pprof::flamegraph;
use std::fs::File;

fn generate_custom_flamegraph() {
    let guard = ProfilerGuard::new(100).unwrap();

    // 运行代码
    for _ in 0..100 {
        function_a();
        function_b();
        function_c();
    }

    if let Ok(report) = guard.report().build() {
        // 生成折叠的调用栈
        let mut folded = Vec::new();
        report.flamegraph(&mut folded).unwrap();

        // 自定义颜色方案
        let file = File::create("custom_flamegraph.svg").unwrap();
        let mut options = flamegraph::Options::default();
        options.title = "My Application Profile".to_string();
        options.colors = flamegraph::color::Palette::Hot;
        
        flamegraph::from_lines(
            &mut options,
            folded.as_slice(),
            file,
        ).unwrap();
    }
}

fn function_a() {
    std::thread::sleep(std::time::Duration::from_micros(100));
}

fn function_b() {
    std::thread::sleep(std::time::Duration::from_micros(200));
}

fn function_c() {
    std::thread::sleep(std::time::Duration::from_micros(50));
}
```

---

## 基准测试

### 1. Criterion

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn fibonacci_recursive(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci_recursive(n - 1) + fibonacci_recursive(n - 2),
    }
}

fn fibonacci_iterative(n: u64) -> u64 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..n {
        let temp = a;
        a = b;
        b = temp + b;
    }
    a
}

fn criterion_benchmark(c: &mut Criterion) {
    // 单个基准测试
    c.bench_function("fib 20", |b| {
        b.iter(|| fibonacci_recursive(black_box(20)))
    });

    // 对比测试
    let mut group = c.benchmark_group("fibonacci");
    
    for i in [10u64, 15, 20, 25].iter() {
        group.bench_with_input(BenchmarkId::new("recursive", i), i, |b, i| {
            b.iter(|| fibonacci_recursive(*i))
        });
        
        group.bench_with_input(BenchmarkId::new("iterative", i), i, |b, i| {
            b.iter(|| fibonacci_iterative(*i))
        });
    }
    
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

**运行基准测试**:

```bash
cargo bench

# 查看报告
open target/criterion/report/index.html
```

### 2. 异步基准测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use tokio::runtime::Runtime;

fn async_benchmark(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    c.bench_function("async_operation", |b| {
        b.to_async(&rt).iter(|| async {
            tokio::time::sleep(tokio::time::Duration::from_micros(100)).await;
        })
    });
}

criterion_group!(benches, async_benchmark);
criterion_main!(benches);
```

---

## OTLP 集成

### 1. 性能指标导出

```rust
use opentelemetry::metrics::{Histogram, Meter};
use pprof::ProfilerGuard;

pub struct PerformanceAnalyzer {
    cpu_usage: Histogram<f64>,
    memory_usage: Histogram<u64>,
    function_duration: Histogram<f64>,
}

impl PerformanceAnalyzer {
    pub fn new(meter: &Meter) -> Self {
        Self {
            cpu_usage: meter
                .f64_histogram("app.cpu_usage")
                .with_description("CPU 使用率(%)")
                .with_unit("%")
                .init(),
            memory_usage: meter
                .u64_histogram("app.memory_usage")
                .with_description("内存使用(字节)")
                .with_unit("bytes")
                .init(),
            function_duration: meter
                .f64_histogram("app.function_duration")
                .with_description("函数执行时间(ms)")
                .with_unit("ms")
                .init(),
        }
    }

    pub fn record_cpu_sample(&self, usage_percent: f64) {
        self.cpu_usage.record(usage_percent, &[]);
    }

    pub fn record_memory_sample(&self, bytes: u64) {
        self.memory_usage.record(bytes, &[]);
    }

    pub fn record_function_duration(&self, name: &str, duration_ms: f64) {
        use opentelemetry::KeyValue;
        self.function_duration.record(
            duration_ms,
            &[KeyValue::new("function", name.to_string())],
        );
    }
}
```

### 2. 自动采样

```rust
use std::sync::Arc;
use std::time::Duration;
use sysinfo::{System, SystemExt, ProcessExt};

pub async fn start_performance_monitoring(
    analyzer: Arc<PerformanceAnalyzer>,
) -> tokio::task::JoinHandle<()> {
    tokio::spawn(async move {
        let mut sys = System::new_all();
        
        loop {
            sys.refresh_all();

            // CPU 使用率
            if let Some(process) = sys.process(sysinfo::get_current_pid().unwrap()) {
                let cpu_usage = process.cpu_usage();
                analyzer.record_cpu_sample(cpu_usage as f64);

                // 内存使用
                let memory_usage = process.memory();
                analyzer.record_memory_sample(memory_usage);

                tracing::info!(
                    cpu_usage = cpu_usage,
                    memory_mb = memory_usage / 1024 / 1024,
                    "性能采样"
                );
            }

            tokio::time::sleep(Duration::from_secs(10)).await;
        }
    })
}
```

---

## 生产环境分析

### 1. 动态开启/关闭

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub struct ProductionProfiler {
    enabled: Arc<AtomicBool>,
    guard: Arc<Mutex<Option<ProfilerGuard<'static>>>>,
}

impl ProductionProfiler {
    pub fn new() -> Self {
        Self {
            enabled: Arc::new(AtomicBool::new(false)),
            guard: Arc::new(Mutex::new(None)),
        }
    }

    pub fn start(&self) -> Result<(), String> {
        if self.enabled.load(Ordering::Relaxed) {
            return Err("Profiler already running".to_string());
        }

        let guard = ProfilerGuardBuilder::default()
            .frequency(99) // 降低采样频率减少开销
            .blocklist(&["libc", "libpthread", "ld"])
            .build()
            .map_err(|e| e.to_string())?;

        *self.guard.lock().unwrap() = Some(guard);
        self.enabled.store(true, Ordering::Relaxed);

        tracing::info!("生产环境 Profiler 已启动");
        Ok(())
    }

    pub fn stop(&self) -> Result<Vec<u8>, String> {
        if !self.enabled.load(Ordering::Relaxed) {
            return Err("Profiler not running".to_string());
        }

        let guard = self.guard.lock().unwrap().take();

        if let Some(g) = guard {
            let report = g.report().build().map_err(|e| e.to_string())?;
            
            let mut flamegraph = Vec::new();
            report.flamegraph(&mut flamegraph).map_err(|e| e.to_string())?;

            self.enabled.store(false, Ordering::Relaxed);

            tracing::info!(
                flamegraph_size_kb = flamegraph.len() / 1024,
                "生产环境 Profiler 已停止"
            );

            return Ok(flamegraph);
        }

        Err("Failed to generate report".to_string())
    }

    pub fn is_running(&self) -> bool {
        self.enabled.load(Ordering::Relaxed)
    }
}
```

### 2. HTTP API 集成

```rust
use axum::{
    extract::State,
    http::{header, StatusCode},
    response::IntoResponse,
    routing::get,
    Router,
};

#[derive(Clone)]
struct AppState {
    profiler: Arc<ProductionProfiler>,
}

async fn profiler_start(
    State(state): State<AppState>,
) -> Result<String, StatusCode> {
    state
        .profiler
        .start()
        .map_err(|_| StatusCode::CONFLICT)?;
    
    Ok("Profiling started for 30 seconds".to_string())
}

async fn profiler_stop(
    State(state): State<AppState>,
) -> impl IntoResponse {
    match state.profiler.stop() {
        Ok(svg) => {
            (
                StatusCode::OK,
                [(header::CONTENT_TYPE, "image/svg+xml")],
                svg,
            ).into_response()
        }
        Err(err) => {
            (StatusCode::BAD_REQUEST, err).into_response()
        }
    }
}

async fn profiler_status(
    State(state): State<AppState>,
) -> String {
    if state.profiler.is_running() {
        "Profiling active".to_string()
    } else {
        "Profiling inactive".to_string()
    }
}

#[tokio::main]
async fn main() {
    let profiler = Arc::new(ProductionProfiler::new());

    let app_state = AppState {
        profiler: profiler.clone(),
    };

    // 自动停止(30秒后)
    let profiler_clone = profiler.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(1)).await;
            if profiler_clone.is_running() {
                tokio::time::sleep(Duration::from_secs(30)).await;
                let _ = profiler_clone.stop();
                break;
            }
        }
    });

    let app = Router::new()
        .route("/debug/pprof/start", get(profiler_start))
        .route("/debug/pprof/stop", get(profiler_stop))
        .route("/debug/pprof/status", get(profiler_status))
        .with_state(app_state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

---

## 最佳实践

### 1. 分层分析策略

```
1. 快速定位(1-5分钟)
   └─> cargo flamegraph 或 samply
   └─> 识别热点函数

2. 详细分析(10-30分钟)
   └─> pprof 采样
   └─> 分析调用栈

3. 精确测量(1小时+)
   └─> criterion 基准测试
   └─> 对比优化前后

4. 内存排查(按需)
   └─> dhat 堆分析
   └─> heaptrack 泄漏检测
```

### 2. 性能优化检查清单

```rust
// ✅ 1. 使用迭代器而非循环
let sum: i32 = vec.iter().filter(|&x| x % 2 == 0).sum();

// ✅ 2. 避免不必要的克隆
fn process(data: &Data) { /* ... */ }

// ✅ 3. 使用 Cow 减少复制
use std::borrow::Cow;
fn maybe_owned(input: &str) -> Cow<str> {
    if input.contains("special") {
        Cow::Owned(input.to_uppercase())
    } else {
        Cow::Borrowed(input)
    }
}

// ✅ 4. 预分配容量
let mut vec = Vec::with_capacity(1000);

// ✅ 5. 使用 SmallVec 优化小数组
use smallvec::SmallVec;
let mut vec: SmallVec<[i32; 4]> = SmallVec::new();
```

### 3. 常见性能陷阱

```rust
// ❌ 1. 字符串连接
let mut s = String::new();
for i in 0..1000 {
    s = s + &i.to_string(); // 每次分配新字符串
}

// ✅ 改进
let mut s = String::with_capacity(4000);
for i in 0..1000 {
    s.push_str(&i.to_string());
}

// ❌ 2. 不必要的 Vec 转换
fn process(data: Vec<i32>) {
    for x in &data { /* ... */ }
}

// ✅ 改进
fn process(data: &[i32]) {
    for x in data { /* ... */ }
}

// ❌ 3. 过度使用 Arc/Mutex
let shared = Arc::new(Mutex::new(data));

// ✅ 改进: 使用 RwLock 或消息传递
let shared = Arc::new(RwLock::new(data));
```

---

## 完整示例

### 1. 综合性能分析

```rust
use pprof::ProfilerGuard;
use criterion::{black_box, Criterion};
use std::fs::File;

fn main() {
    // 1. CPU Profiling
    let guard = ProfilerGuard::new(100).unwrap();
    
    let data = generate_test_data(100_000);
    
    // 测试不同算法
    let result1 = algorithm_naive(&data);
    let result2 = algorithm_optimized(&data);
    
    assert_eq!(result1, result2);
    
    if let Ok(report) = guard.report().build() {
        let file = File::create("comparison_flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();
    }

    // 2. 基准测试
    let mut criterion = Criterion::default();
    
    criterion.bench_function("naive", |b| {
        b.iter(|| algorithm_naive(black_box(&data)))
    });
    
    criterion.bench_function("optimized", |b| {
        b.iter(|| algorithm_optimized(black_box(&data)))
    });
}

fn generate_test_data(size: usize) -> Vec<i32> {
    (0..size as i32).collect()
}

fn algorithm_naive(data: &[i32]) -> i64 {
    let mut sum = 0i64;
    for i in data {
        if i % 2 == 0 {
            sum += *i as i64 * *i as i64;
        }
    }
    sum
}

fn algorithm_optimized(data: &[i32]) -> i64 {
    data.iter()
        .filter(|&x| x % 2 == 0)
        .map(|&x| x as i64 * x as i64)
        .sum()
}
```

---

## 总结

### 核心工具对比

| 工具 | 开销 | 精度 | 学习曲线 | 推荐场景 |
|-----|------|------|---------|---------|
| **pprof** | 低 | 中 | 低 | 生产环境 |
| **samply** | 低 | 高 | 低 | 开发调试 |
| **criterion** | N/A | 高 | 中 | 基准测试 |
| **dhat** | 中 | 高 | 中 | 内存优化 |
| **flamegraph** | 低 | 中 | 低 | 快速定位 |

### 性能优化流程

```
1. 测量(Measure): 使用 profiler 找到瓶颈
2. 分析(Analyze): 理解为什么慢
3. 优化(Optimize): 改进代码
4. 验证(Verify): 基准测试确认提升
5. 监控(Monitor): OTLP 持续跟踪
```

### 下一步

- **持续分析**: 集成 CI/CD 的性能回归检测
- **分布式追踪**: 跨服务的性能瓶颈定位
- **自动优化**: 基于 PGO(Profile-Guided Optimization)
- **可观测性**: 性能指标接入 Grafana

---

## 参考资料

- [pprof-rs 文档](https://docs.rs/pprof)
- [Criterion 文档](https://docs.rs/criterion)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [The Rust Performance Book](https://github.com/nnethercote/perf-book)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**pprof 版本**: 0.14+  
**criterion 版本**: 0.5+

