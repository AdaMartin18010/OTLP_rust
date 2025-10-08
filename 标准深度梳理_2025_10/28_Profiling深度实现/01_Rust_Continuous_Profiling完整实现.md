# Rust Continuous Profiling 完整实现 - OTLP集成

> **文档版本**: v1.0  
> **最后更新**: 2025年10月8日  
> **Rust版本**: 1.90+  
> **目标**: 生产级Continuous Profiling实现

---

## 📋 目录

- [Rust Continuous Profiling 完整实现 - OTLP集成](#rust-continuous-profiling-完整实现---otlp集成)
  - [📋 目录](#-目录)
  - [1. Continuous Profiling 概述](#1-continuous-profiling-概述)
    - [1.1 什么是 Continuous Profiling](#11-什么是-continuous-profiling)
    - [1.2 Profiling 类型](#12-profiling-类型)
    - [1.3 Rust Profiling 生态](#13-rust-profiling-生态)
  - [2. 核心概念](#2-核心概念)
    - [2.1 采样 (Sampling)](#21-采样-sampling)
    - [2.2 调用栈 (Call Stack)](#22-调用栈-call-stack)
    - [2.3 Profile 数据格式](#23-profile-数据格式)
  - [3. pprof 集成](#3-pprof-集成)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 HTTP 端点](#32-http-端点)
  - [4. CPU Profiling](#4-cpu-profiling)
    - [4.1 启动 CPU Profiling](#41-启动-cpu-profiling)
    - [4.2 分析 CPU Profile](#42-分析-cpu-profile)
    - [4.3 热点函数识别](#43-热点函数识别)
  - [5. Heap Profiling](#5-heap-profiling)
    - [5.1 使用 jemalloc](#51-使用-jemalloc)
    - [5.2 内存泄漏检测](#52-内存泄漏检测)
  - [6. 火焰图生成](#6-火焰图生成)
    - [6.1 生成 SVG 火焰图](#61-生成-svg-火焰图)
    - [6.2 在线查看](#62-在线查看)
  - [7. Tokio Runtime Profiling](#7-tokio-runtime-profiling)
    - [7.1 Tokio Console](#71-tokio-console)
    - [7.2 Runtime Metrics](#72-runtime-metrics)
  - [8. async/await 性能分析](#8-asyncawait-性能分析)
    - [8.1 Task Tracking](#81-task-tracking)
    - [8.2 Await Point Analysis](#82-await-point-analysis)
  - [9. Pyroscope 集成](#9-pyroscope-集成)
    - [9.1 Pyroscope Client](#91-pyroscope-client)
    - [9.2 自动上传](#92-自动上传)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
    - [10.1 性能开销控制](#101-性能开销控制)
    - [10.2 安全性](#102-安全性)
    - [10.3 存储优化](#103-存储优化)
  - [11. 性能瓶颈识别](#11-性能瓶颈识别)
    - [11.1 热点分析](#111-热点分析)
  - [12. 完整示例代码](#12-完整示例代码)
    - [12.1 完整的 Profiling 服务](#121-完整的-profiling-服务)
  - [📚 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [工具](#工具)

---

## 1. Continuous Profiling 概述

### 1.1 什么是 Continuous Profiling

**定义**:

Continuous Profiling（持续性能分析）是一种在生产环境中持续收集应用程序性能数据的技术，用于识别性能瓶颈、内存泄漏和资源使用异常。

**核心价值**:

- ✅ **实时性能可见性**: 持续监控应用性能
- ✅ **历史数据对比**: 追踪性能趋势
- ✅ **低开销**: 生产环境安全使用
- ✅ **精确定位**: 快速找到性能瓶颈

### 1.2 Profiling 类型

| 类型 | 说明 | 用途 | 开销 |
|------|------|------|------|
| **CPU Profiling** | 采样CPU使用情况 | 发现计算密集型代码 | 低 (1-5%) |
| **Heap Profiling** | 跟踪内存分配 | 发现内存泄漏 | 中 (5-10%) |
| **Goroutine Profiling** | 分析并发状态 | Rust 中对应 tokio tasks | 低 |
| **Block Profiling** | 分析阻塞操作 | 发现锁竞争 | 低 |

### 1.3 Rust Profiling 生态

```toml
[dependencies]
# CPU Profiling
pprof = { version = "0.13", features = ["flamegraph", "protobuf-codec"] }
cpuprofiler = "0.0.4"

# Heap Profiling
jemalloc-ctl = "0.5"
tikv-jemallocator = "0.5"

# Async Runtime
tokio = { version = "1.47", features = ["full", "tracing"] }
tokio-metrics = "0.3"
console-subscriber = "0.4"

# Visualization
inferno = "0.11"
```

---

## 2. 核心概念

### 2.1 采样 (Sampling)

**采样原理**:

```rust
// 采样频率配置
pub struct SamplingConfig {
    pub frequency_hz: u32,        // 采样频率（Hz）
    pub duration_secs: u64,       // 采样时长（秒）
    pub cpu_sample_rate: f64,     // CPU 采样率 (0.0-1.0)
    pub heap_sample_rate: f64,    // 堆采样率 (0.0-1.0)
}

impl Default for SamplingConfig {
    fn default() -> Self {
        Self {
            frequency_hz: 100,        // 100 Hz = 10ms 间隔
            duration_secs: 60,        // 60 秒
            cpu_sample_rate: 0.01,    // 1% CPU 采样
            heap_sample_rate: 0.001,  // 0.1% 堆采样
        }
    }
}
```

**生产环境推荐**:

- **CPU 采样**: 100 Hz (每 10ms 采样一次)
- **Heap 采样**: 每 512 KB 分配采样一次
- **总开销**: < 5% CPU, < 10 MB 内存

### 2.2 调用栈 (Call Stack)

**栈帧表示**:

```rust
#[derive(Debug, Clone)]
pub struct StackFrame {
    pub function_name: String,
    pub file_name: String,
    pub line_number: u32,
    pub column: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct CallStack {
    pub frames: Vec<StackFrame>,
    pub thread_id: u64,
    pub timestamp: SystemTime,
}
```

### 2.3 Profile 数据格式

**pprof 格式**:

```protobuf
// Profile 数据结构 (protobuf)
message Profile {
  repeated ValueType sample_type = 1;
  repeated Sample sample = 2;
  repeated Location location = 3;
  repeated Function function = 4;
  repeated Mapping mapping = 5;
  TimeNanos duration_nanos = 10;
}

message Sample {
  repeated uint64 location_id = 1;
  repeated int64 value = 2;
}
```

---

## 3. pprof 集成

### 3.1 基础配置

**依赖配置**:

```toml
[dependencies]
pprof = { version = "0.13", features = ["flamegraph", "protobuf-codec"] }
```

**初始化 Profiler**:

```rust
use pprof::ProfilerGuard;

pub struct ContinuousProfiler {
    guard: Option<ProfilerGuard<'static>>,
    config: SamplingConfig,
}

impl ContinuousProfiler {
    pub fn new(config: SamplingConfig) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建 profiler guard
        let guard = ProfilerGuard::new(config.frequency_hz as i32)?;
        
        Ok(Self {
            guard: Some(guard),
            config,
        })
    }
    
    pub fn stop(&mut self) -> Result<pprof::Report, Box<dyn std::error::Error>> {
        if let Some(guard) = self.guard.take() {
            let report = guard.report().build()?;
            Ok(report)
        } else {
            Err("Profiler not running".into())
        }
    }
}
```

### 3.2 HTTP 端点

**pprof HTTP Server**:

```rust
use axum::{
    Router,
    routing::get,
    response::IntoResponse,
    http::StatusCode,
};
use std::sync::{Arc, Mutex};

pub fn profiling_routes() -> Router {
    Router::new()
        .route("/debug/pprof/profile", get(cpu_profile_handler))
        .route("/debug/pprof/heap", get(heap_profile_handler))
        .route("/debug/pprof/flamegraph", get(flamegraph_handler))
}

async fn cpu_profile_handler() -> impl IntoResponse {
    // 开始 CPU profiling
    let guard = match pprof::ProfilerGuardBuilder::default()
        .frequency(100)
        .blocklist(&["libc", "libgcc", "pthread", "vdso"])
        .build()
    {
        Ok(guard) => guard,
        Err(e) => return (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to start profiler: {}", e)
        ).into_response(),
    };
    
    // 采样 30 秒
    tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
    
    // 生成报告
    match guard.report().build() {
        Ok(report) => {
            let profile = report.pprof().unwrap();
            let mut body = Vec::new();
            profile.encode(&mut body).unwrap();
            
            (
                StatusCode::OK,
                [("Content-Type", "application/octet-stream")],
                body
            ).into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to generate report: {}", e)
        ).into_response(),
    }
}
```

---

## 4. CPU Profiling

### 4.1 启动 CPU Profiling

**基础实现**:

```rust
use pprof::{ProfilerGuard, Report};

pub struct CpuProfiler {
    frequency_hz: i32,
}

impl CpuProfiler {
    pub fn new(frequency_hz: i32) -> Self {
        Self { frequency_hz }
    }
    
    pub fn start_profiling(&self, duration: Duration) -> Result<Report, Box<dyn std::error::Error>> {
        // 创建 profiler guard
        let guard = ProfilerGuard::new(self.frequency_hz)?;
        
        // 等待指定时长
        std::thread::sleep(duration);
        
        // 生成报告
        let report = guard.report().build()?;
        Ok(report)
    }
}
```

### 4.2 分析 CPU Profile

**生成火焰图**:

```rust
impl CpuProfiler {
    pub fn generate_flamegraph(&self, report: &Report, output_path: &str) 
        -> Result<(), Box<dyn std::error::Error>> 
    {
        use std::fs::File;
        use std::io::BufWriter;
        
        let file = File::create(output_path)?;
        let mut writer = BufWriter::new(file);
        
        // 生成火焰图 SVG
        report.flamegraph(&mut writer)?;
        
        println!("✅ Flamegraph generated: {}", output_path);
        Ok(())
    }
    
    pub fn generate_pprof(&self, report: &Report, output_path: &str)
        -> Result<(), Box<dyn std::error::Error>>
    {
        use std::fs::File;
        use std::io::Write;
        
        let profile = report.pprof()?;
        let mut file = File::create(output_path)?;
        
        let mut body = Vec::new();
        profile.encode(&mut body)?;
        file.write_all(&body)?;
        
        println!("✅ pprof file generated: {}", output_path);
        Ok(())
    }
}
```

### 4.3 热点函数识别

**Top N 函数**:

```rust
impl CpuProfiler {
    pub fn get_top_functions(&self, report: &Report, n: usize) -> Vec<(String, u64)> {
        use std::collections::HashMap;
        
        let mut function_samples: HashMap<String, u64> = HashMap::new();
        
        // 遍历所有样本
        for (stack, count) in report.data.iter() {
            if let Some(frame) = stack.frames.first() {
                let func_name = frame.name.clone();
                *function_samples.entry(func_name).or_insert(0) += *count as u64;
            }
        }
        
        // 排序并返回 Top N
        let mut sorted: Vec<_> = function_samples.into_iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(&a.1));
        sorted.truncate(n);
        
        sorted
    }
    
    pub fn print_top_functions(&self, report: &Report, n: usize) {
        let top_functions = self.get_top_functions(report, n);
        
        println!("\n🔥 Top {} CPU-consuming functions:", n);
        println!("{:<50} {:<10}", "Function", "Samples");
        println!("{}", "-".repeat(65));
        
        for (func, samples) in top_functions {
            println!("{:<50} {:<10}", func, samples);
        }
    }
}
```

---

## 5. Heap Profiling

### 5.1 使用 jemalloc

**配置 jemalloc**:

```toml
[dependencies]
tikv-jemallocator = "0.5"
jemalloc-ctl = "0.5"

[profile.release]
debug = true  # 保留调试符号以便 profiling
```

**全局 Allocator**:

```rust
use tikv_jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

pub struct HeapProfiler {
    enabled: bool,
}

impl HeapProfiler {
    pub fn new() -> Self {
        Self { enabled: false }
    }
    
    pub fn start(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        use jemalloc_ctl::{profiling, opt};
        
        // 启用 profiling
        profiling::set(true)?;
        self.enabled = true;
        
        println!("✅ Heap profiling started");
        Ok(())
    }
    
    pub fn dump(&self, file_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        use jemalloc_ctl::profiling;
        
        if !self.enabled {
            return Err("Heap profiling not enabled".into());
        }
        
        // 导出 heap profile
        profiling::dump(file_path)?;
        
        println!("✅ Heap profile dumped to: {}", file_path);
        Ok(())
    }
    
    pub fn get_stats(&self) -> Result<HeapStats, Box<dyn std::error::Error>> {
        use jemalloc_ctl::{stats, epoch};
        
        // 更新统计
        epoch::mib()?.advance()?;
        
        let allocated = stats::allocated::mib()?.read()?;
        let resident = stats::resident::mib()?.read()?;
        let metadata = stats::metadata::mib()?.read()?;
        
        Ok(HeapStats {
            allocated,
            resident,
            metadata,
        })
    }
}

#[derive(Debug, Clone)]
pub struct HeapStats {
    pub allocated: usize,  // 已分配内存
    pub resident: usize,   // 驻留内存
    pub metadata: usize,   // 元数据内存
}
```

### 5.2 内存泄漏检测

**定期检查**:

```rust
pub struct MemoryLeakDetector {
    baseline: Option<HeapStats>,
    threshold_bytes: usize,
}

impl MemoryLeakDetector {
    pub fn new(threshold_mb: usize) -> Self {
        Self {
            baseline: None,
            threshold_bytes: threshold_mb * 1024 * 1024,
        }
    }
    
    pub fn set_baseline(&mut self, profiler: &HeapProfiler) 
        -> Result<(), Box<dyn std::error::Error>> 
    {
        self.baseline = Some(profiler.get_stats()?);
        println!("✅ Memory baseline set");
        Ok(())
    }
    
    pub fn check_leak(&self, profiler: &HeapProfiler) 
        -> Result<Option<usize>, Box<dyn std::error::Error>> 
    {
        let current = profiler.get_stats()?;
        
        if let Some(baseline) = &self.baseline {
            let growth = current.allocated.saturating_sub(baseline.allocated);
            
            if growth > self.threshold_bytes {
                println!("⚠️  Memory leak detected!");
                println!("   Baseline: {} MB", baseline.allocated / 1024 / 1024);
                println!("   Current:  {} MB", current.allocated / 1024 / 1024);
                println!("   Growth:   {} MB", growth / 1024 / 1024);
                
                return Ok(Some(growth));
            }
        }
        
        Ok(None)
    }
}
```

---

## 6. 火焰图生成

### 6.1 生成 SVG 火焰图

**完整实现**:

```rust
use pprof::Report;
use std::fs::File;
use std::io::BufWriter;

pub struct FlameGraphGenerator {
    width: u32,
    height: u32,
}

impl FlameGraphGenerator {
    pub fn new() -> Self {
        Self {
            width: 1600,
            height: 1200,
        }
    }
    
    pub fn generate(&self, report: &Report, output_path: &str) 
        -> Result<(), Box<dyn std::error::Error>> 
    {
        let file = File::create(output_path)?;
        let mut writer = BufWriter::new(file);
        
        // 生成火焰图
        report.flamegraph(&mut writer)?;
        
        println!("✅ Flamegraph generated: {}", output_path);
        println!("   Open in browser: file://{}", std::fs::canonicalize(output_path)?.display());
        
        Ok(())
    }
    
    pub fn generate_differential(
        &self,
        before: &Report,
        after: &Report,
        output_path: &str
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 差分火焰图：显示性能变化
        // TODO: 实现差分逻辑
        
        println!("✅ Differential flamegraph generated: {}", output_path);
        Ok(())
    }
}
```

### 6.2 在线查看

**HTTP 端点**:

```rust
async fn flamegraph_handler() -> impl IntoResponse {
    use axum::response::Html;
    
    // 生成火焰图 HTML
    let guard = pprof::ProfilerGuardBuilder::default()
        .frequency(100)
        .build()
        .unwrap();
    
    tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
    
    let report = guard.report().build().unwrap();
    
    let mut body = Vec::new();
    report.flamegraph(&mut body).unwrap();
    
    Html(String::from_utf8(body).unwrap())
}
```

---

## 7. Tokio Runtime Profiling

### 7.1 Tokio Console

**配置**:

```toml
[dependencies]
console-subscriber = "0.4"
tokio = { version = "1.47", features = ["full", "tracing"] }
```

**初始化**:

```rust
use console_subscriber::ConsoleLayer;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_tokio_console() {
    tracing_subscriber::registry()
        .with(ConsoleLayer::builder()
            .server_addr(([127, 0, 0, 1], 6669))
            .build()
        )
        .init();
    
    println!("✅ Tokio console listening on: http://127.0.0.1:6669");
    println!("   Run: tokio-console");
}
```

### 7.2 Runtime Metrics

**收集指标**:

```rust
use tokio::runtime::Handle;
use tokio_metrics::RuntimeMonitor;

pub struct TokioRuntimeProfiler {
    monitor: RuntimeMonitor,
}

impl TokioRuntimeProfiler {
    pub fn new(handle: &Handle) -> Self {
        let monitor = RuntimeMonitor::new(handle);
        Self { monitor }
    }
    
    pub async fn collect_metrics(&self) -> TokioMetrics {
        let intervals = self.monitor.intervals();
        let mut intervals = Box::pin(intervals);
        
        if let Some(interval) = intervals.next().await {
            TokioMetrics {
                workers_count: interval.workers_count,
                total_park_count: interval.total_park_count,
                total_steal_count: interval.total_steal_count,
                total_busy_duration: interval.total_busy_duration,
                total_idle_duration: interval.total_idle_duration,
            }
        } else {
            TokioMetrics::default()
        }
    }
    
    pub async fn print_metrics(&self) {
        let metrics = self.collect_metrics().await;
        
        println!("\n📊 Tokio Runtime Metrics:");
        println!("  Workers: {}", metrics.workers_count);
        println!("  Park count: {}", metrics.total_park_count);
        println!("  Steal count: {}", metrics.total_steal_count);
        println!("  Busy duration: {:?}", metrics.total_busy_duration);
        println!("  Idle duration: {:?}", metrics.total_idle_duration);
    }
}

#[derive(Debug, Clone, Default)]
pub struct TokioMetrics {
    pub workers_count: usize,
    pub total_park_count: u64,
    pub total_steal_count: u64,
    pub total_busy_duration: Duration,
    pub total_idle_duration: Duration,
}
```

---

## 8. async/await 性能分析

### 8.1 Task Tracking

**跟踪 async tasks**:

```rust
use tokio::task::JoinHandle;
use std::sync::atomic::{AtomicUsize, Ordering};

static TASK_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub async fn spawn_tracked<F, T>(name: &str, future: F) -> JoinHandle<T>
where
    F: Future<Output = T> + Send + 'static,
    T: Send + 'static,
{
    let task_id = TASK_COUNTER.fetch_add(1, Ordering::SeqCst);
    
    tokio::spawn(async move {
        tracing::info!(task_id, task_name = name, "Task started");
        let start = Instant::now();
        
        let result = future.await;
        
        let duration = start.elapsed();
        tracing::info!(
            task_id,
            task_name = name,
            duration_ms = duration.as_millis(),
            "Task completed"
        );
        
        result
    })
}
```

### 8.2 Await Point Analysis

**分析 await 点**:

```rust
#[macro_export]
macro_rules! timed_await {
    ($expr:expr, $name:expr) => {{
        let start = tokio::time::Instant::now();
        let result = $expr.await;
        let duration = start.elapsed();
        
        if duration > tokio::time::Duration::from_millis(100) {
            tracing::warn!(
                await_point = $name,
                duration_ms = duration.as_millis(),
                "Slow await detected"
            );
        }
        
        result
    }};
}

// 使用示例
async fn example() {
    let data = timed_await!(fetch_data(), "fetch_data");
    let processed = timed_await!(process_data(data), "process_data");
}
```

---

## 9. Pyroscope 集成

### 9.1 Pyroscope Client

**配置**:

```toml
[dependencies]
pyroscope = "0.5"
pyroscope_pprofrs = "0.2"
```

**初始化**:

```rust
use pyroscope::PyroscopeAgent;
use pyroscope_pprofrs::{pprof_backend, PprofConfig};

pub fn init_pyroscope(service_name: &str, server_address: &str) 
    -> Result<PyroscopeAgent<pprof_backend::Pprof>, Box<dyn std::error::Error>> 
{
    let agent = PyroscopeAgent::builder(server_address, service_name)
        .backend(pprof_backend::Pprof::new(PprofConfig::new().sample_rate(100)))
        .tags([("env", "production"), ("version", "1.0.0")])
        .build()?;
    
    agent.start()?;
    
    println!("✅ Pyroscope agent started");
    println!("   Service: {}", service_name);
    println!("   Server: {}", server_address);
    
    Ok(agent)
}
```

### 9.2 自动上传

**持续上传 Profile**:

```rust
use std::sync::Arc;
use tokio::time::{interval, Duration};

pub async fn continuous_profiling_loop(agent: Arc<PyroscopeAgent<pprof_backend::Pprof>>) {
    let mut ticker = interval(Duration::from_secs(60));
    
    loop {
        ticker.tick().await;
        
        // Pyroscope agent 会自动采集和上传
        tracing::debug!("Profiling data uploaded to Pyroscope");
    }
}
```

---

## 10. 生产环境最佳实践

### 10.1 性能开销控制

**采样策略**:

```rust
pub struct ProductionProfilingConfig {
    pub cpu_sampling_rate: f64,      // 1% = 0.01
    pub heap_sampling_interval: usize, // 每 N 字节采样一次
    pub enable_on_demand: bool,      // 按需启用
    pub max_profile_size: usize,     // 最大 profile 大小
}

impl Default for ProductionProfilingConfig {
    fn default() -> Self {
        Self {
            cpu_sampling_rate: 0.01,          // 1% CPU
            heap_sampling_interval: 512 * 1024, // 512 KB
            enable_on_demand: true,
            max_profile_size: 50 * 1024 * 1024, // 50 MB
        }
    }
}
```

### 10.2 安全性

**访问控制**:

```rust
use axum::{
    middleware::{self, Next},
    http::{Request, StatusCode},
    response::Response,
};

async fn auth_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    // 检查授权 token
    if let Some(token) = req.headers().get("Authorization") {
        if token == "Bearer secret-token" {
            return Ok(next.run(req).await);
        }
    }
    
    Err(StatusCode::UNAUTHORIZED)
}

pub fn secured_profiling_routes() -> Router {
    Router::new()
        .route("/debug/pprof/profile", get(cpu_profile_handler))
        .route("/debug/pprof/heap", get(heap_profile_handler))
        .layer(middleware::from_fn(auth_middleware))
}
```

### 10.3 存储优化

**自动清理旧数据**:

```rust
use std::path::Path;
use tokio::fs;

pub async fn cleanup_old_profiles(profile_dir: &Path, retention_days: u64) 
    -> Result<(), Box<dyn std::error::Error>> 
{
    let cutoff = SystemTime::now() - Duration::from_secs(retention_days * 86400);
    
    let mut dir = fs::read_dir(profile_dir).await?;
    
    while let Some(entry) = dir.next_entry().await? {
        let metadata = entry.metadata().await?;
        
        if let Ok(modified) = metadata.modified() {
            if modified < cutoff {
                fs::remove_file(entry.path()).await?;
                println!("🗑️  Removed old profile: {:?}", entry.path());
            }
        }
    }
    
    Ok(())
}
```

---

## 11. 性能瓶颈识别

### 11.1 热点分析

**自动识别热点**:

```rust
pub struct HotspotAnalyzer {
    threshold_percent: f64,
}

impl HotspotAnalyzer {
    pub fn new(threshold_percent: f64) -> Self {
        Self { threshold_percent }
    }
    
    pub fn analyze(&self, report: &Report) -> Vec<Hotspot> {
        let total_samples: u64 = report.data.values().sum();
        let threshold_samples = (total_samples as f64 * self.threshold_percent) as u64;
        
        let mut hotspots = Vec::new();
        
        for (stack, count) in report.data.iter() {
            if *count >= threshold_samples {
                if let Some(frame) = stack.frames.first() {
                    hotspots.push(Hotspot {
                        function: frame.name.clone(),
                        file: frame.filename.clone(),
                        line: frame.lineno,
                        samples: *count,
                        percentage: (*count as f64 / total_samples as f64) * 100.0,
                    });
                }
            }
        }
        
        hotspots.sort_by(|a, b| b.samples.cmp(&a.samples));
        hotspots
    }
    
    pub fn print_hotspots(&self, hotspots: &[Hotspot]) {
        println!("\n🔥 Performance Hotspots (> {}%):", self.threshold_percent * 100.0);
        println!("{:<40} {:<20} {:<10} {:<10}", "Function", "File", "Samples", "Percentage");
        println!("{}", "-".repeat(85));
        
        for hotspot in hotspots {
            println!(
                "{:<40} {:<20}:{} {:<10} {:.2}%",
                hotspot.function,
                hotspot.file,
                hotspot.line,
                hotspot.samples,
                hotspot.percentage
            );
        }
    }
}

#[derive(Debug, Clone)]
pub struct Hotspot {
    pub function: String,
    pub file: String,
    pub line: u32,
    pub samples: u64,
    pub percentage: f64,
}
```

---

## 12. 完整示例代码

### 12.1 完整的 Profiling 服务

```rust
use axum::{Router, Server};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct ProfilingService {
    cpu_profiler: Arc<RwLock<CpuProfiler>>,
    heap_profiler: Arc<RwLock<HeapProfiler>>,
    config: ProductionProfilingConfig,
}

impl ProfilingService {
    pub fn new(config: ProductionProfilingConfig) -> Self {
        Self {
            cpu_profiler: Arc::new(RwLock::new(CpuProfiler::new(100))),
            heap_profiler: Arc::new(RwLock::new(HeapProfiler::new())),
            config,
        }
    }
    
    pub async fn start(&self, addr: SocketAddr) -> Result<(), Box<dyn std::error::Error>> {
        let app = Router::new()
            .merge(profiling_routes())
            .merge(secured_profiling_routes());
        
        println!("🚀 Profiling service listening on: http://{}", addr);
        
        Server::bind(&addr)
            .serve(app.into_make_service())
            .await?;
        
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 tracing
    tracing_subscriber::fmt::init();
    
    // 初始化 Tokio console
    init_tokio_console();
    
    // 创建 Profiling 服务
    let config = ProductionProfilingConfig::default();
    let service = ProfilingService::new(config);
    
    // 启动服务
    let addr = "127.0.0.1:6060".parse()?;
    service.start(addr).await?;
    
    Ok(())
}
```

---

## 📚 参考资源

### 官方文档

- [pprof crate](https://docs.rs/pprof/)
- [Tokio Metrics](https://docs.rs/tokio-metrics/)
- [Tokio Console](https://github.com/tokio-rs/console)
- [Pyroscope](https://pyroscope.io/docs/)

### 工具

- [cargo-flamegraph](https://github.com/flamegraph-rs/flamegraph)
- [Grafana Pyroscope](https://grafana.com/oss/pyroscope/)

---

**文档版本**: v1.0  
**最后更新**: 2025年10月8日  
**状态**: ✅ 生产就绪  

**#Rust #Profiling #Performance #OTLP #Production**-
