# Tokio Console 运行时诊断 - Rust 完整实现指南

> **Rust版本**: 1.90+  
> **Tokio**: 1.47.1  
> **tokio-console**: 0.1.12  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Tokio Console 运行时诊断 - Rust 完整实现指南](#tokio-console-运行时诊断---rust-完整实现指南)
  - [目录](#目录)
  - [1. Tokio Console 概述](#1-tokio-console-概述)
  - [2. 依赖配置](#2-依赖配置)
  - [3. 基础集成](#3-基础集成)
  - [4. 与 OTLP 集成](#4-与-otlp-集成)
  - [5. 任务追踪](#5-任务追踪)
  - [6. 资源监控](#6-资源监控)
  - [7. 性能分析](#7-性能分析)
  - [8. 死锁检测](#8-死锁检测)
  - [9. 完整监控系统](#9-完整监控系统)
  - [10. 生产环境使用](#10-生产环境使用)
  - [11. 故障排查](#11-故障排查)
  - [12. 最佳实践](#12-最佳实践)
  - [13. 参考资源](#13-参考资源)

---

## 1. Tokio Console 概述

**什么是 Tokio Console**:

```text
Tokio Console = 异步运行时调试器
类似于 Chrome DevTools 之于浏览器

功能:
✅ 实时查看异步任务状态
✅ 监控资源使用情况
✅ 检测性能瓶颈
✅ 发现死锁和泄漏
✅ 分析任务调度
✅ 追踪 Poll 时间

适用场景:
- 开发环境调试
- 性能分析
- 故障排查
- 生产环境监控 (谨慎使用)
```

**架构**:

```text
┌─────────────────────────────────┐
│      Rust Application           │
│  ┌──────────────────────────┐   │
│  │  tokio-console-subscriber│   │
│  │  (收集运行时数据)         │   │
│  └────────────┬─────────────┘   │
│               │ gRPC            │
└───────────────┼─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│    tokio-console (CLI)          │
│    (显示和分析)                  │
└─────────────────────────────────┘
```

---

## 2. 依赖配置

**Cargo.toml**:

```toml
[package]
name = "otlp-tokio-console"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Tokio (启用 tracing 和 console 支持)
tokio = { version = "1.47.1", features = [
    "full",
    "tracing",          # 必需: 启用 tracing 支持
] }
tokio-util = "0.7.14"

# Tokio Console Subscriber
console-subscriber = "0.4.1"

# OpenTelemetry 生态系统
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }

# Tracing
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.20", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 其他工具
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"
anyhow = "1.0.100"

[profile.dev]
# 重要: 启用调试信息
debug = true

[profile.release]
# 如果需要在 release 模式使用 console
debug = 1  # 启用基本调试信息

# 或者创建专门的 profile
[profile.release-with-console]
inherits = "release"
debug = true
```

**安装 Tokio Console CLI**:

```bash
# 安装 tokio-console
cargo install --locked tokio-console

# 验证安装
tokio-console --version
```

---

## 3. 基础集成

**简单集成**:

```rust
use tracing_subscriber::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 console subscriber
    console_subscriber::init();
    
    // 你的应用代码
    run_application().await?;
    
    Ok(())
}

async fn run_application() -> Result<(), Box<dyn std::error::Error>> {
    // 创建一些异步任务
    let handle1 = tokio::spawn(async {
        tracing::info!("Task 1 started");
        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
        tracing::info!("Task 1 completed");
    });
    
    let handle2 = tokio::spawn(async {
        tracing::info!("Task 2 started");
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        tracing::info!("Task 2 completed");
    });
    
    // 等待任务完成
    let _ = tokio::try_join!(handle1, handle2)?;
    
    Ok(())
}
```

**运行和查看**:

```bash
# 终端 1: 运行应用
RUSTFLAGS="--cfg tokio_unstable" cargo run

# 终端 2: 启动 console
tokio-console
```

---

## 4. 与 OTLP 集成

**同时启用 Console 和 OTLP**:

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use opentelemetry::global;
use opentelemetry_sdk::trace::{self as sdktrace, Sampler};

/// 初始化 Console + OTLP 追踪
pub async fn init_telemetry_with_console() -> Result<(), anyhow::Error> {
    // 1. 创建 OTLP Tracer
    let otlp_tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            sdktrace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "otlp-console-demo"),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 2. 创建 OpenTelemetry Layer
    let otlp_layer = tracing_opentelemetry::layer()
        .with_tracer(otlp_tracer);
    
    // 3. 创建 Console Layer
    let console_layer = console_subscriber::ConsoleLayer::builder()
        .server_addr(([127, 0, 0, 1], 6669))  // 自定义端口
        .spawn();
    
    // 4. 创建标准输出 Layer
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true);
    
    // 5. 组合所有 Layer
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env()
            .add_directive(tracing::Level::INFO.into()))
        .with(console_layer)
        .with(otlp_layer)
        .with(fmt_layer)
        .init();
    
    tracing::info!("Telemetry initialized with Console and OTLP");
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // 初始化遥测
    init_telemetry_with_console().await?;
    
    // 运行应用
    run_monitored_application().await?;
    
    // 关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn run_monitored_application() -> Result<(), anyhow::Error> {
    // 创建多个任务进行监控
    let tasks: Vec<_> = (0..10).map(|i| {
        tokio::spawn(async move {
            let span = tracing::info_span!("worker_task", task_id = i);
            let _enter = span.enter();
            
            tracing::info!(task_id = i, "Task started");
            
            // 模拟工作负载
            tokio::time::sleep(tokio::time::Duration::from_millis(100 * (i + 1))).await;
            
            tracing::info!(task_id = i, "Task completed");
        })
    }).collect();
    
    // 等待所有任务完成
    for task in tasks {
        task.await?;
    }
    
    Ok(())
}
```

---

## 5. 任务追踪

**详细的任务监控**:

```rust
use tokio::task::JoinHandle;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// 任务监控器
pub struct TaskMonitor {
    total_tasks: Arc<AtomicU64>,
    active_tasks: Arc<AtomicU64>,
}

impl TaskMonitor {
    pub fn new() -> Self {
        Self {
            total_tasks: Arc::new(AtomicU64::new(0)),
            active_tasks: Arc::new(AtomicU64::new(0)),
        }
    }
    
    /// 启动被监控的任务
    pub fn spawn_monitored<F, T>(&self, name: &str, future: F) -> JoinHandle<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let total = Arc::clone(&self.total_tasks);
        let active = Arc::clone(&self.active_tasks);
        let name = name.to_string();
        
        tokio::spawn(async move {
            // 增加计数
            let task_id = total.fetch_add(1, Ordering::SeqCst);
            active.fetch_add(1, Ordering::SeqCst);
            
            // 创建任务 Span
            let span = tracing::info_span!(
                "monitored_task",
                task.id = task_id,
                task.name = %name,
            );
            
            let _enter = span.enter();
            
            tracing::info!(
                task_id = task_id,
                task_name = %name,
                "Task started"
            );
            
            // 执行任务
            let start = std::time::Instant::now();
            let result = future.await;
            let duration = start.elapsed();
            
            // 记录完成
            tracing::info!(
                task_id = task_id,
                task_name = %name,
                duration_ms = duration.as_millis(),
                "Task completed"
            );
            
            // 减少活跃任务计数
            active.fetch_sub(1, Ordering::SeqCst);
            
            result
        })
    }
    
    /// 获取统计信息
    pub fn stats(&self) -> TaskStats {
        TaskStats {
            total_spawned: self.total_tasks.load(Ordering::SeqCst),
            currently_active: self.active_tasks.load(Ordering::SeqCst),
        }
    }
}

#[derive(Debug)]
pub struct TaskStats {
    pub total_spawned: u64,
    pub currently_active: u64,
}

/// 使用示例
async fn task_monitoring_example() -> Result<(), anyhow::Error> {
    let monitor = Arc::new(TaskMonitor::new());
    
    // 启动多个被监控的任务
    let mut handles = vec![];
    
    for i in 0..20 {
        let monitor = Arc::clone(&monitor);
        let handle = monitor.spawn_monitored(
            &format!("worker-{}", i),
            async move {
                // 模拟不同的工作负载
                tokio::time::sleep(
                    tokio::time::Duration::from_millis(100 * (i % 5 + 1))
                ).await;
                i * 2
            },
        );
        handles.push(handle);
    }
    
    // 定期报告统计信息
    let monitor_stats = Arc::clone(&monitor);
    let stats_task = tokio::spawn(async move {
        for _ in 0..10 {
            tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
            let stats = monitor_stats.stats();
            tracing::info!(
                total = stats.total_spawned,
                active = stats.currently_active,
                "Task statistics"
            );
        }
    });
    
    // 等待所有任务完成
    for handle in handles {
        let _ = handle.await?;
    }
    
    stats_task.await?;
    
    Ok(())
}
```

---

## 6. 资源监控

**监控异步资源**:

```rust
use tokio::sync::{Semaphore, RwLock, Mutex};
use std::sync::Arc;

/// 资源监控器
pub struct ResourceMonitor {
    semaphore_usage: Arc<AtomicU64>,
    lock_contentions: Arc<AtomicU64>,
}

impl ResourceMonitor {
    pub fn new() -> Self {
        Self {
            semaphore_usage: Arc::new(AtomicU64::new(0)),
            lock_contentions: Arc::new(AtomicU64::new(0)),
        }
    }
    
    /// 监控 Semaphore 使用
    pub async fn acquire_monitored(
        &self,
        semaphore: &Semaphore,
        operation: &str,
    ) -> Result<tokio::sync::SemaphorePermit<'_>, anyhow::Error> {
        let span = tracing::debug_span!(
            "semaphore_acquire",
            operation = %operation,
            available = semaphore.available_permits(),
        );
        let _enter = span.enter();
        
        let start = std::time::Instant::now();
        
        // 尝试获取许可
        let permit = semaphore.acquire().await?;
        
        let wait_time = start.elapsed();
        
        self.semaphore_usage.fetch_add(1, Ordering::SeqCst);
        
        tracing::debug!(
            operation = %operation,
            wait_ms = wait_time.as_millis(),
            "Semaphore acquired"
        );
        
        Ok(permit)
    }
    
    /// 监控 Mutex 锁
    pub async fn lock_monitored<T>(
        &self,
        mutex: &Mutex<T>,
        operation: &str,
    ) -> tokio::sync::MutexGuard<'_, T> {
        let span = tracing::debug_span!(
            "mutex_lock",
            operation = %operation,
        );
        let _enter = span.enter();
        
        let start = std::time::Instant::now();
        
        let guard = mutex.lock().await;
        
        let wait_time = start.elapsed();
        
        if wait_time.as_millis() > 10 {
            self.lock_contentions.fetch_add(1, Ordering::SeqCst);
            tracing::warn!(
                operation = %operation,
                wait_ms = wait_time.as_millis(),
                "Lock contention detected"
            );
        }
        
        guard
    }
}

/// 资源监控示例
async fn resource_monitoring_example() -> Result<(), anyhow::Error> {
    let monitor = Arc::new(ResourceMonitor::new());
    let semaphore = Arc::new(Semaphore::new(5));
    let shared_data = Arc::new(Mutex::new(0u64));
    
    // 创建多个竞争资源的任务
    let mut handles = vec![];
    
    for i in 0..20 {
        let monitor = Arc::clone(&monitor);
        let semaphore = Arc::clone(&semaphore);
        let shared_data = Arc::clone(&shared_data);
        
        let handle = tokio::spawn(async move {
            // 获取 semaphore
            let _permit = monitor
                .acquire_monitored(&semaphore, &format!("task-{}", i))
                .await
                .unwrap();
            
            // 获取 mutex
            let mut data = monitor
                .lock_monitored(&shared_data, &format!("task-{}", i))
                .await;
            
            *data += 1;
            
            // 模拟工作
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        });
        
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await?;
    }
    
    tracing::info!(
        semaphore_uses = monitor.semaphore_usage.load(Ordering::SeqCst),
        lock_contentions = monitor.lock_contentions.load(Ordering::SeqCst),
        "Resource usage statistics"
    );
    
    Ok(())
}
```

---

## 7. 性能分析

**性能指标收集**:

```rust
use std::time::{Duration, Instant};

/// 性能分析器
pub struct PerformanceProfiler {
    metrics: Arc<RwLock<PerformanceMetrics>>,
}

#[derive(Debug, Default)]
pub struct PerformanceMetrics {
    pub task_durations: Vec<Duration>,
    pub poll_counts: Vec<u64>,
    pub slow_tasks: Vec<(String, Duration)>,
}

impl PerformanceProfiler {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(PerformanceMetrics::default())),
        }
    }
    
    /// 分析异步操作
    pub async fn profile_async<F, T>(
        &self,
        name: &str,
        future: F,
    ) -> T
    where
        F: std::future::Future<Output = T>,
    {
        let span = tracing::debug_span!(
            "profiled_operation",
            operation = %name,
        );
        let _enter = span.enter();
        
        let start = Instant::now();
        let result = future.await;
        let duration = start.elapsed();
        
        // 记录指标
        let mut metrics = self.metrics.write().await;
        metrics.task_durations.push(duration);
        
        // 检测慢操作
        if duration.as_millis() > 100 {
            metrics.slow_tasks.push((name.to_string(), duration));
            tracing::warn!(
                operation = %name,
                duration_ms = duration.as_millis(),
                "Slow operation detected"
            );
        }
        
        result
    }
    
    /// 生成性能报告
    pub async fn generate_report(&self) -> String {
        let metrics = self.metrics.read().await;
        
        if metrics.task_durations.is_empty() {
            return "No metrics collected".to_string();
        }
        
        let total_tasks = metrics.task_durations.len();
        let avg_duration = metrics.task_durations.iter()
            .map(|d| d.as_millis())
            .sum::<u128>() / total_tasks as u128;
        
        let mut sorted = metrics.task_durations.clone();
        sorted.sort();
        let p50 = sorted[total_tasks / 2].as_millis();
        let p95 = sorted[total_tasks * 95 / 100].as_millis();
        let p99 = sorted[total_tasks * 99 / 100].as_millis();
        
        format!(
            r#"Performance Report:
================
Total Tasks: {}
Average Duration: {}ms
P50: {}ms
P95: {}ms
P99: {}ms
Slow Tasks: {}

Slow Tasks Details:
{}"#,
            total_tasks,
            avg_duration,
            p50,
            p95,
            p99,
            metrics.slow_tasks.len(),
            metrics.slow_tasks.iter()
                .map(|(name, dur)| format!("  - {}: {}ms", name, dur.as_millis()))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
```

---

## 8. 死锁检测

**死锁检测实现**:

```rust
/// 死锁检测器
pub struct DeadlockDetector {
    timeout: Duration,
}

impl DeadlockDetector {
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }
    
    /// 带超时的操作
    pub async fn with_timeout<F, T>(
        &self,
        name: &str,
        future: F,
    ) -> Result<T, anyhow::Error>
    where
        F: std::future::Future<Output = T>,
    {
        let span = tracing::warn_span!(
            "deadlock_protected",
            operation = %name,
        );
        let _enter = span.enter();
        
        match tokio::time::timeout(self.timeout, future).await {
            Ok(result) => Ok(result),
            Err(_) => {
                tracing::error!(
                    operation = %name,
                    timeout_ms = self.timeout.as_millis(),
                    "Potential deadlock detected"
                );
                Err(anyhow::anyhow!("Operation timed out: {}", name))
            }
        }
    }
}

/// 死锁检测示例
async fn deadlock_detection_example() -> Result<(), anyhow::Error> {
    let detector = DeadlockDetector::new(Duration::from_secs(5));
    
    // 正常操作
    let result = detector.with_timeout("normal_operation", async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        "Success"
    }).await?;
    
    tracing::info!(result = %result, "Operation completed");
    
    // 可能死锁的操作
    let result = detector.with_timeout("potential_deadlock", async {
        tokio::time::sleep(Duration::from_secs(10)).await;
        "Should timeout"
    }).await;
    
    match result {
        Ok(_) => unreachable!(),
        Err(e) => tracing::error!(error = %e, "Deadlock detected"),
    }
    
    Ok(())
}
```

---

## 9. 完整监控系统

**生产级监控系统**:

```rust
/// 完整的 Tokio 运行时监控系统
pub struct TokioRuntimeMonitor {
    task_monitor: Arc<TaskMonitor>,
    resource_monitor: Arc<ResourceMonitor>,
    performance_profiler: Arc<PerformanceProfiler>,
    deadlock_detector: DeadlockDetector,
}

impl TokioRuntimeMonitor {
    pub fn new() -> Self {
        Self {
            task_monitor: Arc::new(TaskMonitor::new()),
            resource_monitor: Arc::new(ResourceMonitor::new()),
            performance_profiler: Arc::new(PerformanceProfiler::new()),
            deadlock_detector: DeadlockDetector::new(Duration::from_secs(30)),
        }
    }
    
    /// 启动监控服务
    pub async fn start_monitoring(&self) {
        let task_monitor = Arc::clone(&self.task_monitor);
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(10));
            
            loop {
                interval.tick().await;
                
                let stats = task_monitor.stats();
                tracing::info!(
                    total_tasks = stats.total_spawned,
                    active_tasks = stats.currently_active,
                    "Runtime monitoring report"
                );
            }
        });
    }
    
    /// 生成完整报告
    pub async fn generate_full_report(&self) -> String {
        let task_stats = self.task_monitor.stats();
        let perf_report = self.performance_profiler.generate_report().await;
        
        format!(
            r#"Tokio Runtime Monitoring Report
================================

Task Statistics:
- Total Spawned: {}
- Currently Active: {}

{}
"#,
            task_stats.total_spawned,
            task_stats.currently_active,
            perf_report
        )
    }
}
```

---

## 10. 生产环境使用

**生产环境配置**:

```rust
/// 生产环境 Console 配置
pub fn init_production_console() -> Result<(), anyhow::Error> {
    // 只在开启特定环境变量时启用
    if std::env::var("ENABLE_TOKIO_CONSOLE").is_ok() {
        console_subscriber::ConsoleLayer::builder()
            .server_addr(([0, 0, 0, 0], 6669))  // 监听所有接口
            .retention(Duration::from_secs(60))  // 只保留最近 60 秒数据
            .spawn();
        
        tracing::warn!("Tokio Console enabled in production");
    }
    
    Ok(())
}
```

---

## 11. 故障排查

**常见问题和解决方案**:

```text
问题 1: Console 无法连接
解决:
- 确保 RUSTFLAGS="--cfg tokio_unstable" 已设置
- 检查端口是否被占用
- 确认应用正在运行

问题 2: 看不到任务
解决:
- 确保使用 tokio::spawn 创建任务
- 检查 tracing span 是否正确创建
- 确认 debug 符号已启用

问题 3: 性能影响
解决:
- 只在开发/测试环境使用
- 生产环境使用采样
- 限制数据保留时间

问题 4: 内存使用过高
解决:
- 减少 retention 时间
- 限制监控的任务数量
- 定期清理旧数据
```

---

## 12. 最佳实践

```text
✅ 开发环境
  □ 始终启用 Console
  □ 使用详细的 span 命名
  □ 添加丰富的上下文信息
  □ 定期查看任务状态

✅ 测试环境
  □ 性能测试时启用
  □ 记录基准指标
  □ 识别瓶颈
  □ 验证优化效果

✅ 生产环境
  □ 默认禁用
  □ 按需启用（环境变量控制）
  □ 限制数据保留时间
  □ 监控性能影响
  □ 使用 OTLP 作为主要监控

✅ 代码实践
  □ 为重要任务添加 span
  □ 使用描述性名称
  □ 添加关键属性
  □ 避免过度监控
```

---

## 13. 参考资源

**官方文档**:

- [Tokio Console](https://github.com/tokio-rs/console)
- [console-subscriber](https://docs.rs/console-subscriber/)
- [Tokio Tracing](https://tokio.rs/tokio/topics/tracing)

**教程**:

- [Tokio Console Tutorial](https://tokio.rs/tokio/topics/tracing)
- [Async Rust Debugging](https://docs.rs/tokio/latest/tokio/task/index.html)

---

**文档状态**: ✅ 完成 (Rust 1.90 + Tokio 1.47.1)  
**最后更新**: 2025年10月8日  
**审核状态**: 生产就绪  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [📖 查看其他组件](../README.md)
