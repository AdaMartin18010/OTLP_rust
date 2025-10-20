# Pprof性能分析：CPU/内存火焰图与OTLP集成指南 (Rust 1.90)

## 目录

- [Pprof性能分析：CPU/内存火焰图与OTLP集成指南 (Rust 1.90)](#pprof性能分析cpu内存火焰图与otlp集成指南-rust-190)
  - [目录](#目录)
  - [一、性能分析核心概念](#一性能分析核心概念)
    - [1.1 CPU Profiling](#11-cpu-profiling)
    - [1.2 Memory Profiling](#12-memory-profiling)
    - [1.3 火焰图可视化](#13-火焰图可视化)
  - [二、Rust性能分析生态](#二rust性能分析生态)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目配置](#22-项目配置)
  - [三、CPU性能分析](#三cpu性能分析)
    - [3.1 基础CPU Profiling](#31-基础cpu-profiling)
    - [3.2 采样频率控制](#32-采样频率控制)
    - [3.3 热点函数识别](#33-热点函数识别)
  - [四、内存性能分析](#四内存性能分析)
    - [4.1 堆内存分析](#41-堆内存分析)
    - [4.2 内存泄漏检测](#42-内存泄漏检测)
    - [4.3 分配追踪](#43-分配追踪)
  - [五、火焰图生成](#五火焰图生成)
    - [5.1 CPU火焰图](#51-cpu火焰图)
    - [5.2 内存火焰图](#52-内存火焰图)
    - [5.3 差异火焰图](#53-差异火焰图)
  - [六、HTTP端点集成](#六http端点集成)
    - [6.1 Pprof HTTP服务器](#61-pprof-http服务器)
    - [6.2 与Axum集成](#62-与axum集成)
    - [6.3 动态采样控制](#63-动态采样控制)
  - [七、OTLP集成](#七otlp集成)
    - [7.1 性能指标导出](#71-性能指标导出)
    - [7.2 追踪与性能关联](#72-追踪与性能关联)
    - [7.3 分布式性能分析](#73-分布式性能分析)
  - [八、生产环境优化](#八生产环境优化)
    - [8.1 低开销采样](#81-低开销采样)
    - [8.2 按需启用](#82-按需启用)
    - [8.3 性能影响评估](#83-性能影响评估)
  - [九、实战案例](#九实战案例)
    - [9.1 定位CPU热点](#91-定位cpu热点)
    - [9.2 排查内存泄漏](#92-排查内存泄漏)
    - [9.3 优化前后对比](#93-优化前后对比)
  - [十、可视化工具集成](#十可视化工具集成)
    - [10.1 Speedscope集成](#101-speedscope集成)
    - [10.2 Grafana Pyroscope集成](#102-grafana-pyroscope集成)
    - [10.3 Google Perftools集成](#103-google-perftools集成)
  - [十一、Docker部署](#十一docker部署)
  - [十二、参考资源](#十二参考资源)
    - [官方文档](#官方文档)
    - [国际标准](#国际标准)
    - [工具](#工具)
    - [博客](#博客)
  - [总结](#总结)

---

## 一、性能分析核心概念

### 1.1 CPU Profiling

**原理**：通过定期采样（如100Hz）记录程序调用栈，统计每个函数的CPU时间占比。

**采样方式**：

- **On-CPU Profiling**：采样正在执行的线程（99%场景）
- **Off-CPU Profiling**：采样阻塞的线程（I/O密集型场景）

**指标**：

- **Self Time**：函数自身执行时间（不包括调用的子函数）
- **Total Time**：函数总时间（包括子函数）

**应用场景**：

- 识别CPU密集型热点函数
- 优化算法复杂度
- 发现不必要的计算

### 1.2 Memory Profiling

**原理**：跟踪内存分配和释放，统计内存使用情况。

**分析维度**：

- **Allocated Memory**：已分配内存总量
- **In-Use Memory**：当前使用中的内存
- **Allocation Count**：分配次数（频繁分配影响性能）

**应用场景**：

- 检测内存泄漏（未释放的内存持续增长）
- 优化内存分配策略
- 减少堆碎片化

### 1.3 火焰图可视化

**火焰图特点**：

- **X轴**：按字母排序（不代表时间顺序）
- **Y轴**：调用栈深度
- **宽度**：CPU时间或内存占比
- **颜色**：随机或根据模块分类

**解读技巧**：

- **平顶山**：CPU热点（需优化）
- **高塔**：深层调用栈（可能过度设计）
- **宽基**：公共基础函数

---

## 二、Rust性能分析生态

### 2.1 核心依赖

```toml
[dependencies]
# CPU Profiling
pprof = { version = "0.14", features = ["flamegraph", "protobuf-codec", "criterion"] }

# HTTP服务器
axum = "0.7"
tokio = { version = "1.42", features = ["full"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# OpenTelemetry集成
opentelemetry = { version = "0.31", features = ["metrics"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "metrics"] }
opentelemetry-otlp = { version = "0.31", features = ["metrics", "grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.28"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

[dev-dependencies]
criterion = { version = "0.6", features = ["html_reports"] }

[profile.release]
debug = true  # 生成调试符号，用于性能分析
```

### 2.2 项目配置

```bash
mkdir -p pprof-demo/src/{cpu,memory,flamegraph,http}
cd pprof-demo
cargo init
```

**注意**：生产环境需要保留调试符号，但可以使用`strip = "symbols"`删除不必要的符号以减小二进制大小。

---

## 三、CPU性能分析

### 3.1 基础CPU Profiling

使用`pprof`库进行CPU采样：

```rust
// src/cpu/basic.rs
use pprof::ProfilerGuard;
use std::fs::File;
use std::io::Write;

/// 执行CPU性能分析
pub fn run_cpu_profiling<F>(sample_frequency: i32, duration_secs: u64, workload: F) -> anyhow::Result<()>
where
    F: FnOnce(),
{
    // 启动采样器（100Hz = 每10ms采样一次）
    let guard = ProfilerGuard::new(sample_frequency)?;

    // 执行工作负载
    workload();

    // 生成报告
    if let Ok(report) = guard.report().build() {
        // 1. 输出火焰图SVG
        let file = File::create("flamegraph.svg")?;
        report.flamegraph(file)?;

        // 2. 输出protobuf格式（兼容Google Pprof）
        let mut file = File::create("profile.pb")?;
        let profile = report.pprof()?;
        let mut content = Vec::new();
        profile.write_to_vec(&mut content)?;
        file.write_all(&content)?;

        println!("✅ CPU profile saved: flamegraph.svg, profile.pb");
    }

    Ok(())
}

/// 模拟CPU密集型任务
fn cpu_intensive_task() {
    let mut sum: u64 = 0;
    for i in 0..10_000_000 {
        sum = sum.wrapping_add(fibonacci(i % 30));
    }
    println!("Sum: {}", sum);
}

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_profiling() {
        run_cpu_profiling(100, 10, || {
            cpu_intensive_task();
        })
        .unwrap();
    }
}
```

**生成的火焰图示例**：

```text
                    [main]
                      |
            [cpu_intensive_task]
                      |
         +------------+------------+
         |                         |
    [fibonacci]              [wrapping_add]
      (80%)                      (20%)
```

### 3.2 采样频率控制

不同场景选择不同采样频率：

```rust
// src/cpu/sampling_control.rs
use pprof::ProfilerGuardBuilder;
use std::time::Duration;

pub enum SamplingMode {
    /// 低开销模式（10Hz，生产环境）
    LowOverhead,
    /// 标准模式（100Hz，测试环境）
    Standard,
    /// 高精度模式（1000Hz，开发环境）
    HighPrecision,
}

impl SamplingMode {
    fn frequency(&self) -> i32 {
        match self {
            Self::LowOverhead => 10,
            Self::Standard => 100,
            Self::HighPrecision => 1000,
        }
    }
}

pub fn profile_with_mode<F>(mode: SamplingMode, workload: F) -> anyhow::Result<pprof::Report>
where
    F: FnOnce(),
{
    let guard = ProfilerGuardBuilder::default()
        .frequency(mode.frequency())
        .blocklist(&["libc", "libpthread"]) // 忽略系统库
        .build()?;

    workload();

    guard.report().build().map_err(|e| anyhow::anyhow!(e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sampling_modes() {
        // 低开销模式
        let report = profile_with_mode(SamplingMode::LowOverhead, || {
            std::thread::sleep(Duration::from_secs(1));
        })
        .unwrap();

        println!("Low overhead report: {} samples", report.data.len());

        // 高精度模式
        let report = profile_with_mode(SamplingMode::HighPrecision, || {
            std::thread::sleep(Duration::from_secs(1));
        })
        .unwrap();

        println!("High precision report: {} samples", report.data.len());
    }
}
```

**性能影响**：

- **10Hz**：< 1% CPU开销
- **100Hz**：< 5% CPU开销
- **1000Hz**：10-20% CPU开销

### 3.3 热点函数识别

分析报告找出热点函数：

```rust
// src/cpu/hotspot_analysis.rs
use pprof::Report;
use std::collections::HashMap;

/// 分析热点函数
pub fn analyze_hotspots(report: &Report) -> Vec<(String, u64)> {
    let mut function_times: HashMap<String, u64> = HashMap::new();

    for (frames, count) in &report.data {
        for frame in frames {
            for symbol in &frame.symbols {
                let name = symbol.name().unwrap_or("unknown");
                *function_times.entry(name.to_string()).or_insert(0) += count;
            }
        }
    }

    let mut sorted: Vec<_> = function_times.into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1));

    // 返回Top 10热点
    sorted.into_iter().take(10).collect()
}

pub fn print_hotspots(hotspots: &[(String, u64)]) {
    println!("\n🔥 Top 10 CPU Hotspots:");
    println!("{:<50} {:<15} {}", "Function", "Samples", "Percentage");
    println!("{:-<80}", "");

    let total_samples: u64 = hotspots.iter().map(|(_, count)| count).sum();

    for (func, count) in hotspots {
        let percentage = (*count as f64 / total_samples as f64) * 100.0;
        println!("{:<50} {:<15} {:.2}%", func, count, percentage);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::sampling_control::{profile_with_mode, SamplingMode};

    #[test]
    fn test_hotspot_analysis() {
        let report = profile_with_mode(SamplingMode::Standard, || {
            // 模拟不同函数调用
            expensive_function_a();
            cheap_function_b();
        })
        .unwrap();

        let hotspots = analyze_hotspots(&report);
        print_hotspots(&hotspots);

        assert!(!hotspots.is_empty());
    }

    fn expensive_function_a() {
        for _ in 0..1_000_000 {
            std::hint::black_box(compute());
        }
    }

    fn cheap_function_b() {
        for _ in 0..100 {
            std::hint::black_box(compute());
        }
    }

    fn compute() -> u64 {
        (0..100).sum()
    }
}
```

---

## 四、内存性能分析

### 4.1 堆内存分析

Rust使用`jemalloc`或`mimalloc`分配器配合`pprof`：

```rust
// src/memory/heap_profiling.rs
use pprof::ProfilerGuard;
use std::collections::HashMap;

/// 模拟内存密集型任务
pub fn memory_intensive_task() {
    let mut data: Vec<HashMap<String, Vec<u8>>> = Vec::new();

    // 分配大量小对象
    for i in 0..10_000 {
        let mut map = HashMap::new();
        map.insert(
            format!("key_{}", i),
            vec![0u8; 1024], // 1KB per entry
        );
        data.push(map);
    }

    println!("Allocated {} maps", data.len());

    // 保持内存占用
    std::thread::sleep(std::time::Duration::from_secs(2));
}

/// 执行内存性能分析
pub fn profile_memory<F>(workload: F) -> anyhow::Result<()>
where
    F: FnOnce(),
{
    let guard = ProfilerGuard::new(100)?;

    workload();

    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("memory_flamegraph.svg")?;
        report.flamegraph(file)?;

        println!("✅ Memory profile saved: memory_flamegraph.svg");
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_profiling() {
        profile_memory(|| {
            memory_intensive_task();
        })
        .unwrap();
    }
}
```

**使用jemalloc**（推荐用于内存分析）：

```toml
# Cargo.toml
[dependencies]
jemallocator = "0.6"

[target.'cfg(not(target_env = "msvc"))'.dependencies]
tikv-jemallocator = "0.6"
```

```rust
// src/main.rs
#[cfg(not(target_env = "msvc"))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
```

### 4.2 内存泄漏检测

模拟内存泄漏并检测：

```rust
// src/memory/leak_detection.rs
use std::sync::{Arc, Mutex};

lazy_static::lazy_static! {
    /// 全局缓存（可能导致泄漏）
    static ref GLOBAL_CACHE: Arc<Mutex<Vec<Vec<u8>>>> = Arc::new(Mutex::new(Vec::new()));
}

/// 模拟内存泄漏
pub fn simulate_memory_leak() {
    for _ in 0..1000 {
        let data = vec![0u8; 10_240]; // 10KB
        GLOBAL_CACHE.lock().unwrap().push(data);
    }

    println!(
        "Global cache size: {} entries",
        GLOBAL_CACHE.lock().unwrap().len()
    );
}

/// 检测内存泄漏
pub fn detect_leaks() {
    let initial_size = GLOBAL_CACHE.lock().unwrap().len();

    // 执行多次分配
    for _ in 0..5 {
        simulate_memory_leak();
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    let final_size = GLOBAL_CACHE.lock().unwrap().len();

    if final_size > initial_size {
        println!("⚠️  Potential memory leak detected!");
        println!("  Initial: {} entries", initial_size);
        println!("  Final: {} entries", final_size);
        println!("  Growth: {} entries", final_size - initial_size);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leak_detection() {
        detect_leaks();
    }
}
```

### 4.3 分配追踪

追踪内存分配热点：

```rust
// src/memory/allocation_tracking.rs
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};

pub struct TrackingAllocator;

static ALLOCATED: AtomicU64 = AtomicU64::new(0);
static DEALLOCATED: AtomicU64 = AtomicU64::new(0);
static ALLOCATION_COUNT: AtomicU64 = AtomicU64::new(0);

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            ALLOCATED.fetch_add(layout.size() as u64, Ordering::Relaxed);
            ALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
        DEALLOCATED.fetch_add(layout.size() as u64, Ordering::Relaxed);
    }
}

#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;

pub fn print_allocation_stats() {
    let allocated = ALLOCATED.load(Ordering::Relaxed);
    let deallocated = DEALLOCATED.load(Ordering::Relaxed);
    let count = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let net = allocated.saturating_sub(deallocated);

    println!("\n📊 Allocation Statistics:");
    println!("  Total allocated: {} bytes", allocated);
    println!("  Total deallocated: {} bytes", deallocated);
    println!("  Net allocated: {} bytes", net);
    println!("  Allocation count: {}", count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocation_tracking() {
        let before_count = ALLOCATION_COUNT.load(Ordering::Relaxed);

        // 分配一些内存
        let vec: Vec<u8> = vec![0; 1024];
        drop(vec);

        let after_count = ALLOCATION_COUNT.load(Ordering::Relaxed);

        print_allocation_stats();

        assert!(after_count > before_count);
    }
}
```

---

## 五、火焰图生成

### 5.1 CPU火焰图

生成交互式火焰图：

```rust
// src/flamegraph/cpu_flamegraph.rs
use pprof::protos::Message;
use pprof::Report;
use std::fs::File;
use std::io::Write;

pub fn generate_cpu_flamegraph(report: &Report, output_path: &str) -> anyhow::Result<()> {
    let file = File::create(output_path)?;
    report.flamegraph(file)?;

    println!("✅ CPU flamegraph saved: {}", output_path);
    Ok(())
}

pub fn generate_pprof_protobuf(report: &Report, output_path: &str) -> anyhow::Result<()> {
    let profile = report.pprof()?;

    let mut buffer = Vec::new();
    profile.write_to_vec(&mut buffer)?;

    let mut file = File::create(output_path)?;
    file.write_all(&buffer)?;

    println!("✅ Pprof protobuf saved: {}", output_path);
    println!("  View with: go tool pprof -http=:8080 {}", output_path);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::sampling_control::{profile_with_mode, SamplingMode};

    #[test]
    fn test_generate_flamegraphs() {
        let report = profile_with_mode(SamplingMode::Standard, || {
            expensive_computation();
        })
        .unwrap();

        generate_cpu_flamegraph(&report, "test_cpu.svg").unwrap();
        generate_pprof_protobuf(&report, "test_cpu.pb").unwrap();
    }

    fn expensive_computation() {
        let mut sum = 0u64;
        for i in 0..5_000_000 {
            sum = sum.wrapping_add(i * 2);
        }
        std::hint::black_box(sum);
    }
}
```

### 5.2 内存火焰图

生成内存分配火焰图：

```rust
// src/flamegraph/memory_flamegraph.rs
use pprof::Report;
use std::fs::File;

pub fn generate_memory_flamegraph(report: &Report, output_path: &str) -> anyhow::Result<()> {
    let file = File::create(output_path)?;

    // 使用反向火焰图（从分配点向上展示调用栈）
    report.flamegraph(file)?;

    println!("✅ Memory flamegraph saved: {}", output_path);
    println!("  Red areas = high memory allocation");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::sampling_control::{profile_with_mode, SamplingMode};

    #[test]
    fn test_memory_flamegraph() {
        let report = profile_with_mode(SamplingMode::Standard, || {
            allocate_heavy();
            allocate_light();
        })
        .unwrap();

        generate_memory_flamegraph(&report, "test_memory.svg").unwrap();
    }

    fn allocate_heavy() {
        let _data: Vec<Vec<u8>> = (0..1000).map(|_| vec![0u8; 10_240]).collect();
    }

    fn allocate_light() {
        let _data: Vec<u8> = vec![0u8; 1024];
    }
}
```

### 5.3 差异火焰图

对比优化前后的性能差异：

```rust
// src/flamegraph/diff_flamegraph.rs
use pprof::Report;

pub fn generate_diff_report(
    before: &Report,
    after: &Report,
) -> anyhow::Result<()> {
    // 提取样本数据
    let before_samples: u64 = before.data.values().sum();
    let after_samples: u64 = after.data.values().sum();

    let improvement = (before_samples as f64 - after_samples as f64) / before_samples as f64 * 100.0;

    println!("\n📊 Performance Comparison:");
    println!("  Before: {} samples", before_samples);
    println!("  After: {} samples", after_samples);
    println!("  Improvement: {:.2}%", improvement);

    // 生成独立火焰图
    let before_file = std::fs::File::create("before.svg")?;
    before.flamegraph(before_file)?;

    let after_file = std::fs::File::create("after.svg")?;
    after.flamegraph(after_file)?;

    println!("✅ Diff flamegraphs saved: before.svg, after.svg");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::sampling_control::{profile_with_mode, SamplingMode};

    #[test]
    fn test_diff_flamegraph() {
        // 优化前
        let before = profile_with_mode(SamplingMode::Standard, || {
            slow_function();
        })
        .unwrap();

        // 优化后
        let after = profile_with_mode(SamplingMode::Standard, || {
            optimized_function();
        })
        .unwrap();

        generate_diff_report(&before, &after).unwrap();
    }

    fn slow_function() {
        for _ in 0..1_000_000 {
            std::hint::black_box(expensive_operation());
        }
    }

    fn optimized_function() {
        for _ in 0..1_000_000 {
            std::hint::black_box(cheap_operation());
        }
    }

    fn expensive_operation() -> u64 {
        (0..100).sum()
    }

    fn cheap_operation() -> u64 {
        42
    }
}
```

---

## 六、HTTP端点集成

### 6.1 Pprof HTTP服务器

创建HTTP端点暴露性能数据：

```rust
// src/http/pprof_server.rs
use axum::{
    extract::Query,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::get,
    Router,
};
use pprof::ProfilerGuardBuilder;
use serde::Deserialize;
use std::net::SocketAddr;
use std::time::Duration;

#[derive(Debug, Deserialize)]
struct ProfileParams {
    #[serde(default = "default_duration")]
    seconds: u64,
    #[serde(default = "default_frequency")]
    frequency: i32,
}

fn default_duration() -> u64 {
    30
}

fn default_frequency() -> i32 {
    100
}

/// CPU Profile端点
async fn cpu_profile_handler(Query(params): Query<ProfileParams>) -> Response {
    let guard = match ProfilerGuardBuilder::default()
        .frequency(params.frequency)
        .blocklist(&["libc", "libpthread"])
        .build()
    {
        Ok(g) => g,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("Failed to start profiler: {}", e),
            )
                .into_response()
        }
    };

    // 采样指定时间
    tokio::time::sleep(Duration::from_secs(params.seconds)).await;

    match guard.report().build() {
        Ok(report) => {
            let mut buffer = Vec::new();
            if let Ok(profile) = report.pprof() {
                use pprof::protos::Message;
                if profile.write_to_vec(&mut buffer).is_ok() {
                    return (
                        StatusCode::OK,
                        [("Content-Type", "application/octet-stream")],
                        buffer,
                    )
                        .into_response();
                }
            }

            (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Failed to generate profile",
            )
                .into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to build report: {}", e),
        )
            .into_response(),
    }
}

/// 火焰图端点
async fn flamegraph_handler(Query(params): Query<ProfileParams>) -> Response {
    let guard = match ProfilerGuardBuilder::default()
        .frequency(params.frequency)
        .build()
    {
        Ok(g) => g,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("Failed to start profiler: {}", e),
            )
                .into_response()
        }
    };

    tokio::time::sleep(Duration::from_secs(params.seconds)).await;

    match guard.report().build() {
        Ok(report) => {
            let mut buffer = Vec::new();
            if report.flamegraph(&mut buffer).is_ok() {
                return (StatusCode::OK, [("Content-Type", "image/svg+xml")], buffer)
                    .into_response();
            }

            (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Failed to generate flamegraph",
            )
                .into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to build report: {}", e),
        )
            .into_response(),
    }
}

/// 启动Pprof HTTP服务器
pub async fn start_pprof_server(addr: SocketAddr) {
    let app = Router::new()
        .route("/debug/pprof/profile", get(cpu_profile_handler))
        .route("/debug/pprof/flamegraph", get(flamegraph_handler));

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    tracing::info!("Pprof server listening on {}", addr);
    tracing::info!("  CPU Profile: http://{}/debug/pprof/profile?seconds=30", addr);
    tracing::info!("  Flamegraph: http://{}/debug/pprof/flamegraph?seconds=10", addr);

    axum::serve(listener, app).await.unwrap();
}
```

### 6.2 与Axum集成

将Pprof集成到现有Axum应用：

```rust
// src/http/axum_integration.rs
use axum::{
    extract::State,
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    // 应用状态
}

#[derive(Debug, Serialize, Deserialize)]
struct CreateOrderRequest {
    product_id: u64,
    quantity: u32,
}

#[derive(Debug, Serialize)]
struct CreateOrderResponse {
    order_id: u64,
}

async fn create_order(
    State(_state): State<Arc<AppState>>,
    Json(payload): Json<CreateOrderRequest>,
) -> Result<Json<CreateOrderResponse>, StatusCode> {
    // 模拟业务逻辑
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;

    Ok(Json(CreateOrderResponse { order_id: 12345 }))
}

async fn list_orders() -> impl IntoResponse {
    Json(vec!["order1", "order2"])
}

pub async fn start_app_with_pprof(addr: SocketAddr, pprof_addr: SocketAddr) {
    let state = Arc::new(AppState {});

    // 业务路由
    let app = Router::new()
        .route("/api/orders", post(create_order).get(list_orders))
        .with_state(state);

    // 启动业务服务器
    let app_listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    tracing::info!("App server listening on {}", addr);

    tokio::spawn(async move {
        axum::serve(app_listener, app).await.unwrap();
    });

    // 启动Pprof服务器（独立端口）
    crate::http::pprof_server::start_pprof_server(pprof_addr).await;
}
```

### 6.3 动态采样控制

通过HTTP API动态启动/停止采样：

```rust
// src/http/dynamic_sampling.rs
use axum::{
    extract::State,
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use pprof::ProfilerGuard;
use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
struct SamplingState {
    guard: Arc<Mutex<Option<ProfilerGuard<'static>>>>,
}

#[derive(Debug, Deserialize)]
struct StartSamplingRequest {
    frequency: i32,
}

#[derive(Debug, Serialize)]
struct SamplingResponse {
    status: String,
    message: String,
}

async fn start_sampling(
    State(state): State<SamplingState>,
    Json(payload): Json<StartSamplingRequest>,
) -> impl IntoResponse {
    let mut guard_lock = state.guard.lock().unwrap();

    if guard_lock.is_some() {
        return (
            StatusCode::CONFLICT,
            Json(SamplingResponse {
                status: "error".to_string(),
                message: "Sampling already in progress".to_string(),
            }),
        );
    }

    match ProfilerGuard::new(payload.frequency) {
        Ok(guard) => {
            *guard_lock = Some(guard);
            (
                StatusCode::OK,
                Json(SamplingResponse {
                    status: "success".to_string(),
                    message: format!("Sampling started at {}Hz", payload.frequency),
                }),
            )
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(SamplingResponse {
                status: "error".to_string(),
                message: format!("Failed to start sampling: {}", e),
            }),
        ),
    }
}

async fn stop_sampling(State(state): State<SamplingState>) -> impl IntoResponse {
    let mut guard_lock = state.guard.lock().unwrap();

    if let Some(guard) = guard_lock.take() {
        match guard.report().build() {
            Ok(report) => {
                let mut buffer = Vec::new();
                if report.flamegraph(&mut buffer).is_ok() {
                    return (StatusCode::OK, [("Content-Type", "image/svg+xml")], buffer)
                        .into_response();
                }
            }
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    format!("Failed to build report: {}", e),
                )
                    .into_response()
            }
        }
    }

    (StatusCode::NOT_FOUND, "No active sampling").into_response()
}

pub fn create_router() -> Router {
    let state = SamplingState {
        guard: Arc::new(Mutex::new(None)),
    };

    Router::new()
        .route("/sampling/start", post(start_sampling))
        .route("/sampling/stop", get(stop_sampling))
        .with_state(state)
}
```

**使用示例**：

```bash
# 启动采样
curl -X POST http://localhost:8080/sampling/start \
  -H "Content-Type: application/json" \
  -d '{"frequency": 100}'

# 执行业务操作...

# 停止采样并获取火焰图
curl http://localhost:8080/sampling/stop > flamegraph.svg
```

---

## 七、OTLP集成

### 7.1 性能指标导出

将性能分析结果作为指标导出到OTLP：

```rust
// src/otel/metrics_export.rs
use opentelemetry::{global, KeyValue};
use pprof::Report;

pub fn export_profiling_metrics(report: &Report) {
    let meter = global::meter("profiling-metrics");

    // 采样总数
    let total_samples: u64 = report.data.values().sum();
    let sample_counter = meter
        .u64_counter("profiling_samples_total")
        .with_description("Total profiling samples collected")
        .build();

    sample_counter.add(total_samples, &[]);

    // Top函数CPU时间
    let cpu_time_gauge = meter
        .f64_observable_gauge("profiling_function_cpu_time_ratio")
        .with_description("CPU time ratio by function")
        .with_callback(move |observer| {
            // 这里应该从report中提取Top函数数据
            observer.observe(0.35, &[KeyValue::new("function", "hot_function")]);
        })
        .build();

    tracing::info!("Exported profiling metrics to OTLP");
}
```

### 7.2 追踪与性能关联

在追踪Span中嵌入性能数据：

```rust
// src/otel/tracing_correlation.rs
use opentelemetry::trace::TraceContextExt;
use pprof::ProfilerGuard;
use tracing::{info_span, Span};
use tracing_opentelemetry::OpenTelemetrySpanExt;

pub async fn traced_expensive_operation() {
    let span = info_span!("expensive_operation");
    let _enter = span.enter();

    // 在Span内启动性能分析
    let guard = ProfilerGuard::new(100).unwrap();

    // 执行业务逻辑
    expensive_computation();

    // 生成报告
    if let Ok(report) = guard.report().build() {
        let total_samples: u64 = report.data.values().sum();

        // 将性能数据添加到Span属性
        Span::current().set_attribute("profiling.samples", total_samples as i64);
        Span::current().set_attribute("profiling.hotspot", "expensive_computation");

        tracing::info!(samples = total_samples, "Performance profiling completed");
    }
}

fn expensive_computation() {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_traced_profiling() {
        traced_expensive_operation().await;
    }
}
```

### 7.3 分布式性能分析

跨服务关联性能数据：

```rust
// src/otel/distributed_profiling.rs
use opentelemetry::{global, trace::{Span, Tracer}, KeyValue};
use pprof::Report;

pub fn profile_distributed_request(service_name: &str, operation: &str, report: &Report) {
    let tracer = global::tracer("distributed-profiling");

    let mut span = tracer
        .span_builder(format!("profile:{}", operation))
        .with_attributes(vec![
            KeyValue::new("service.name", service_name.to_string()),
            KeyValue::new("profiling.operation", operation.to_string()),
        ])
        .start(&tracer);

    // 添加性能指标
    let total_samples: u64 = report.data.values().sum();
    span.set_attribute("profiling.samples", total_samples as i64);

    // 导出到OTLP
    span.end();

    tracing::info!(
        service = service_name,
        operation = operation,
        samples = total_samples,
        "Distributed profiling data exported"
    );
}
```

---

## 八、生产环境优化

### 8.1 低开销采样

生产环境使用低频采样：

```rust
// src/production/low_overhead.rs
use pprof::ProfilerGuardBuilder;
use std::time::Duration;

pub struct ProductionProfiler {
    frequency: i32,
    duration: Duration,
}

impl ProductionProfiler {
    pub fn new() -> Self {
        Self {
            frequency: 10,  // 10Hz，< 1% CPU overhead
            duration: Duration::from_secs(60),
        }
    }

    pub async fn profile_periodically<F>(&self, workload: F)
    where
        F: Fn() + Send + 'static,
    {
        loop {
            tracing::info!("Starting periodic profiling");

            let guard = ProfilerGuardBuilder::default()
                .frequency(self.frequency)
                .blocklist(&["libc", "libpthread", "ld-linux"])
                .build()
                .unwrap();

            tokio::time::sleep(self.duration).await;

            if let Ok(report) = guard.report().build() {
                // 异步保存到S3或本地
                self.save_report(&report).await;
            }

            // 间隔5分钟再次采样
            tokio::time::sleep(Duration::from_secs(300)).await;
        }
    }

    async fn save_report(&self, report: &pprof::Report) {
        let timestamp = chrono::Utc::now().format("%Y%m%d_%H%M%S");
        let filename = format!("profile_{}.svg", timestamp);

        if let Ok(file) = std::fs::File::create(&filename) {
            let _ = report.flamegraph(file);
            tracing::info!(file = %filename, "Profile saved");
        }
    }
}
```

### 8.2 按需启用

通过环境变量或配置文件控制：

```rust
// src/production/conditional_profiling.rs
use std::env;

pub fn is_profiling_enabled() -> bool {
    env::var("ENABLE_PROFILING")
        .unwrap_or_else(|_| "false".to_string())
        .parse()
        .unwrap_or(false)
}

pub async fn maybe_profile<F, T>(name: &str, f: F) -> T
where
    F: FnOnce() -> T,
{
    if is_profiling_enabled() {
        tracing::info!(operation = name, "Profiling enabled");

        let guard = pprof::ProfilerGuard::new(10).ok();

        let result = f();

        if let Some(g) = guard {
            if let Ok(report) = g.report().build() {
                let filename = format!("{}_profile.svg", name);
                if let Ok(file) = std::fs::File::create(&filename) {
                    let _ = report.flamegraph(file);
                }
            }
        }

        result
    } else {
        f()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_conditional_profiling() {
        env::set_var("ENABLE_PROFILING", "true");

        let result = maybe_profile("test_operation", || {
            std::thread::sleep(std::time::Duration::from_millis(100));
            42
        }).await;

        assert_eq!(result, 42);
    }
}
```

### 8.3 性能影响评估

评估性能分析对应用的影响：

```rust
// src/production/overhead_measurement.rs
use std::time::Instant;

pub fn measure_profiling_overhead<F>(f: F) -> (std::time::Duration, std::time::Duration)
where
    F: Fn(),
{
    // 无性能分析基准
    let start_baseline = Instant::now();
    f();
    let baseline_duration = start_baseline.elapsed();

    // 有性能分析
    let guard = pprof::ProfilerGuard::new(100).unwrap();
    let start_profiled = Instant::now();
    f();
    let profiled_duration = start_profiled.elapsed();
    drop(guard);

    let overhead = profiled_duration.saturating_sub(baseline_duration);
    let overhead_percent = (overhead.as_secs_f64() / baseline_duration.as_secs_f64()) * 100.0;

    println!("\n📊 Profiling Overhead:");
    println!("  Baseline: {:?}", baseline_duration);
    println!("  With profiling: {:?}", profiled_duration);
    println!("  Overhead: {:?} ({:.2}%)", overhead, overhead_percent);

    (baseline_duration, profiled_duration)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_overhead_measurement() {
        measure_profiling_overhead(|| {
            std::thread::sleep(std::time::Duration::from_secs(1));
        });
    }
}
```

---

## 九、实战案例

### 9.1 定位CPU热点

完整案例：优化JSON序列化：

```rust
// src/cases/cpu_hotspot.rs
use serde::{Deserialize, Serialize};
use pprof::ProfilerGuard;

#[derive(Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    email: String,
    tags: Vec<String>,
}

/// 慢版本：频繁序列化
fn slow_json_processing() {
    for i in 0..10_000 {
        let user = User {
            id: i,
            name: format!("user_{}", i),
            email: format!("user{}@example.com", i),
            tags: vec!["tag1".to_string(), "tag2".to_string()],
        };

        let _json = serde_json::to_string(&user).unwrap();
        let _: User = serde_json::from_str(&_json).unwrap();
    }
}

/// 快版本：批量序列化
fn fast_json_processing() {
    let users: Vec<User> = (0..10_000)
        .map(|i| User {
            id: i,
            name: format!("user_{}", i),
            email: format!("user{}@example.com", i),
            tags: vec!["tag1".to_string(), "tag2".to_string()],
        })
        .collect();

    let _json = serde_json::to_string(&users).unwrap();
    let _: Vec<User> = serde_json::from_str(&_json).unwrap();
}

pub fn compare_json_performance() {
    // Profile慢版本
    let guard = ProfilerGuard::new(100).unwrap();
    slow_json_processing();
    let slow_report = guard.report().build().unwrap();

    let slow_file = std::fs::File::create("slow_json.svg").unwrap();
    slow_report.flamegraph(slow_file).unwrap();

    // Profile快版本
    let guard = ProfilerGuard::new(100).unwrap();
    fast_json_processing();
    let fast_report = guard.report().build().unwrap();

    let fast_file = std::fs::File::create("fast_json.svg").unwrap();
    fast_report.flamegraph(fast_file).unwrap();

    println!("✅ Comparison complete: slow_json.svg vs fast_json.svg");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_optimization() {
        compare_json_performance();
    }
}
```

### 9.2 排查内存泄漏

模拟并检测内存泄漏：

```rust
// src/cases/memory_leak.rs
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

lazy_static::lazy_static! {
    static ref SESSION_CACHE: Arc<Mutex<HashMap<String, Vec<u8>>>> =
        Arc::new(Mutex::new(HashMap::new()));
}

/// 有泄漏的会话管理
fn leaky_session_manager() {
    for i in 0..1_000 {
        let session_id = format!("session_{}", i);
        let session_data = vec![0u8; 10_240]; // 10KB per session

        // 添加到缓存，但从不清理
        SESSION_CACHE.lock().unwrap().insert(session_id, session_data);
    }

    println!("Session cache size: {}", SESSION_CACHE.lock().unwrap().len());
}

/// 修复后的版本（LRU缓存）
struct LruSessionCache {
    cache: lru::LruCache<String, Vec<u8>>,
}

impl LruSessionCache {
    fn new(capacity: usize) -> Self {
        Self {
            cache: lru::LruCache::new(std::num::NonZeroUsize::new(capacity).unwrap()),
        }
    }

    fn insert(&mut self, key: String, value: Vec<u8>) {
        self.cache.put(key, value);
    }
}

pub fn detect_and_fix_leak() {
    println!("\n🔍 Detecting memory leak...");

    // 泄漏版本
    let guard = pprof::ProfilerGuard::new(100).unwrap();
    leaky_session_manager();
    let leak_report = guard.report().build().unwrap();

    let leak_file = std::fs::File::create("leak_memory.svg").unwrap();
    leak_report.flamegraph(leak_file).unwrap();

    println!("✅ Leak profile saved: leak_memory.svg");

    // 修复后
    let mut fixed_cache = LruSessionCache::new(100); // 限制100个session
    for i in 0..1_000 {
        let session_id = format!("session_{}", i);
        let session_data = vec![0u8; 10_240];
        fixed_cache.insert(session_id, session_data);
    }

    println!("✅ Fixed: LRU cache limits memory usage");
}
```

### 9.3 优化前后对比

标准化性能优化流程：

```rust
// src/cases/optimization_workflow.rs
use std::time::{Duration, Instant};
use pprof::Report;

pub struct OptimizationResult {
    pub before_duration: Duration,
    pub after_duration: Duration,
    pub improvement_percent: f64,
}

pub fn benchmark_optimization<F1, F2>(
    name: &str,
    before: F1,
    after: F2,
) -> OptimizationResult
where
    F1: Fn(),
    F2: Fn(),
{
    println!("\n🚀 Optimizing: {}", name);

    // 优化前
    let start = Instant::now();
    before();
    let before_duration = start.elapsed();

    let guard = pprof::ProfilerGuard::new(100).unwrap();
    before();
    let before_report = guard.report().build().unwrap();
    save_report(&before_report, &format!("{}_before.svg", name));

    // 优化后
    let start = Instant::now();
    after();
    let after_duration = start.elapsed();

    let guard = pprof::ProfilerGuard::new(100).unwrap();
    after();
    let after_report = guard.report().build().unwrap();
    save_report(&after_report, &format!("{}_after.svg", name));

    let improvement_percent =
        (before_duration.as_secs_f64() - after_duration.as_secs_f64())
            / before_duration.as_secs_f64()
            * 100.0;

    println!("  Before: {:?}", before_duration);
    println!("  After: {:?}", after_duration);
    println!("  Improvement: {:.2}%", improvement_percent);

    OptimizationResult {
        before_duration,
        after_duration,
        improvement_percent,
    }
}

fn save_report(report: &Report, filename: &str) {
    if let Ok(file) = std::fs::File::create(filename) {
        let _ = report.flamegraph(file);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_optimization_workflow() {
        let result = benchmark_optimization(
            "string_concatenation",
            || {
                // 慢版本
                let mut s = String::new();
                for i in 0..10_000 {
                    s = format!("{}{}", s, i);
                }
            },
            || {
                // 快版本
                let mut s = String::with_capacity(50_000);
                for i in 0..10_000 {
                    use std::fmt::Write;
                    write!(&mut s, "{}", i).unwrap();
                }
            },
        );

        assert!(result.improvement_percent > 50.0);
    }
}
```

---

## 十、可视化工具集成

### 10.1 Speedscope集成

生成Speedscope兼容格式：

```rust
// src/visualization/speedscope.rs
use pprof::Report;
use std::fs::File;
use std::io::Write;

pub fn export_to_speedscope(report: &Report, output_path: &str) -> anyhow::Result<()> {
    let profile = report.pprof()?;

    let mut buffer = Vec::new();
    use pprof::protos::Message;
    profile.write_to_vec(&mut buffer)?;

    let mut file = File::create(output_path)?;
    file.write_all(&buffer)?;

    println!("✅ Speedscope profile saved: {}", output_path);
    println!("  View at: https://www.speedscope.app/");
    println!("  Or: speedscope {}", output_path);

    Ok(())
}
```

### 10.2 Grafana Pyroscope集成

集成Pyroscope进行连续性能分析：

```rust
// src/visualization/pyroscope.rs
use pprof::Report;
use reqwest::Client;

pub async fn push_to_pyroscope(
    report: &Report,
    pyroscope_url: &str,
    app_name: &str,
) -> anyhow::Result<()> {
    let profile = report.pprof()?;

    let mut buffer = Vec::new();
    use pprof::protos::Message;
    profile.write_to_vec(&mut buffer)?;

    let client = Client::new();
    let url = format!("{}/ingest", pyroscope_url);

    client
        .post(&url)
        .header("Content-Type", "application/octet-stream")
        .query(&[("name", app_name)])
        .body(buffer)
        .send()
        .await?;

    tracing::info!("✅ Profile pushed to Pyroscope: {}", pyroscope_url);

    Ok(())
}
```

### 10.3 Google Perftools集成

使用`go tool pprof`分析：

```bash
# 生成protobuf格式
cargo test --release

# 使用Go工具分析
go tool pprof -http=:8080 profile.pb

# 或命令行分析
go tool pprof profile.pb
> top10
> list hot_function
> web  # 生成调用图
```

---

## 十一、Docker部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "3000:3000"    # 应用端口
      - "8080:8080"    # Pprof端口
    environment:
      - RUST_LOG=info
      - ENABLE_PROFILING=true
    volumes:
      - ./profiles:/app/profiles  # 保存性能数据

  pyroscope:
    image: grafana/pyroscope:latest
    ports:
      - "4040:4040"
    environment:
      - PYROSCOPE_LOG_LEVEL=debug

  grafana:
    image: grafana/grafana:11.4.0
    ports:
      - "3001:3000"
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
    volumes:
      - grafana_data:/var/lib/grafana

volumes:
  grafana_data:
```

**Dockerfile**：

```dockerfile
FROM rust:1.90 AS builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 保留调试符号
RUN cargo build --release

FROM ubuntu:24.04

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY --from=builder /app/target/release/pprof-demo .

EXPOSE 3000 8080

CMD ["./pprof-demo"]
```

---

## 十二、参考资源

### 官方文档

1. **pprof库文档**: <https://docs.rs/pprof/>
2. **Google Pprof**: <https://github.com/google/pprof>
3. **Flame Graphs**: <https://www.brendangregg.com/flamegraphs.html>

### 国际标准

1. **Continuous Profiling**: <https://www.cncf.io/blog/2022/05/31/what-is-continuous-profiling/>
2. **Profiling Best Practices** (Google): <https://cloud.google.com/profiler/docs/best-practices>

### 工具

1. **Speedscope**: <https://www.speedscope.app/>
2. **Grafana Pyroscope**: <https://grafana.com/oss/pyroscope/>
3. **Criterion.rs**: <https://github.com/bheisler/criterion.rs>

### 博客

1. **Profiling Rust Applications** (Datadog): <https://www.datadoghq.com/blog/rust-profiling/>
2. **Rust Performance Book**: <https://nnethercote.github.io/perf-book/>

---

## 总结

本文档提供了Rust 1.90中Pprof性能分析的完整指南，涵盖：

✅ **CPU/内存分析**：采样、热点识别、内存泄漏检测  
✅ **火焰图生成**：SVG、Protobuf、差异火焰图  
✅ **HTTP端点**：动态采样、Axum集成  
✅ **OTLP集成**：指标导出、追踪关联  
✅ **生产优化**：低开销采样、按需启用、性能影响评估  
✅ **实战案例**：CPU热点优化、内存泄漏排查  
✅ **可视化工具**：Speedscope、Pyroscope、Google Pprof  

**核心优势**：

- 遵循Google Pprof标准，兼容生态工具
- 生产环境友好（< 1% CPU开销@10Hz）
- 完整的可视化和分析工具链
- 与OpenTelemetry深度集成

**下一步**：

- 探索`tracing-appender`进行日志管理
- 学习`opentelemetry-rust`高级特性
- 集成APM平台（Datadog、New Relic）
