# Rust OTLP 故障排查完整指南

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08
> - 适用场景: 生产环境故障诊断

## 目录

- [Rust OTLP 故障排查完整指南](#rust-otlp-故障排查完整指南)
  - [目录](#目录)
  - [概述](#概述)
    - [故障排查流程](#故障排查流程)
  - [1. 常见问题诊断](#1-常见问题诊断)
    - [1.1 数据未上报](#11-数据未上报)
    - [1.2 Span 丢失](#12-span-丢失)
    - [1.3 TraceID 不连续](#13-traceid-不连续)
    - [1.4 Exporter 失败](#14-exporter-失败)
  - [2. 性能瓶颈分析](#2-性能瓶颈分析)
    - [2.1 高延迟诊断](#21-高延迟诊断)
    - [2.2 高CPU占用](#22-高cpu占用)
    - [2.3 内存占用过高](#23-内存占用过高)
    - [2.4 批处理优化](#24-批处理优化)
  - [3. 内存泄漏排查](#3-内存泄漏排查)
    - [3.1 检测内存泄漏](#31-检测内存泄漏)
    - [3.2 常见泄漏场景](#32-常见泄漏场景)
    - [3.3 使用 valgrind 排查](#33-使用-valgrind-排查)
    - [3.4 使用 heaptrack 分析](#34-使用-heaptrack-分析)
  - [4. 异步死锁检测](#4-异步死锁检测)
    - [4.1 检测死锁](#41-检测死锁)
    - [4.2 常见死锁场景](#42-常见死锁场景)
    - [4.3 使用 tokio-console 诊断](#43-使用-tokio-console-诊断)
    - [4.4 避免死锁最佳实践](#44-避免死锁最佳实践)
  - [5. 日志和追踪调试](#5-日志和追踪调试)
    - [5.1 启用详细日志](#51-启用详细日志)
    - [5.2 追踪特定 Span](#52-追踪特定-span)
    - [5.3 导出到本地文件](#53-导出到本地文件)
  - [6. 网络问题排查](#6-网络问题排查)
    - [6.1 连接失败](#61-连接失败)
    - [6.2 超时问题](#62-超时问题)
    - [6.3 TLS/SSL 问题](#63-tlsssl-问题)
  - [7. 配置问题诊断](#7-配置问题诊断)
    - [7.1 采样率配置](#71-采样率配置)
    - [7.2 资源属性配置](#72-资源属性配置)
    - [7.3 导出器配置](#73-导出器配置)
  - [8. 生产环境最佳实践](#8-生产环境最佳实践)
    - [8.1 监控告警](#81-监控告警)
    - [8.2 故障恢复](#82-故障恢复)
    - [8.3 容量规划](#83-容量规划)
  - [9. 工具和技巧](#9-工具和技巧)
    - [9.1 命令行工具](#91-命令行工具)
    - [9.2 可视化工具](#92-可视化工具)
    - [9.3 Rust 特定工具](#93-rust-特定工具)
  - [10. 完整诊断案例](#10-完整诊断案例)
    - [案例 1: 生产环境 Span 丢失](#案例-1-生产环境-span-丢失)
    - [案例 2: 内存泄漏导致 OOM](#案例-2-内存泄漏导致-oom)
    - [案例 3: 异步死锁导致服务挂起](#案例-3-异步死锁导致服务挂起)
  - [总结](#总结)

---

## 概述

本指南提供 Rust OTLP 应用的完整故障排查方法论，包括：

- ✅ 常见问题快速诊断
- ✅ 性能瓶颈分析
- ✅ 内存泄漏排查
- ✅ 异步死锁检测
- ✅ 完整的诊断工具链
- ✅ 生产环境最佳实践

### 故障排查流程

```text
问题报告
   │
   ├─> 1. 收集信息（日志、指标、追踪）
   │
   ├─> 2. 初步诊断（分类问题）
   │      ├─ 数据问题
   │      ├─ 性能问题
   │      ├─ 内存问题
   │      └─ 网络问题
   │
   ├─> 3. 详细分析（使用工具）
   │      ├─ 日志分析
   │      ├─ 性能剖析
   │      ├─ 内存分析
   │      └─ 网络诊断
   │
   ├─> 4. 定位根因
   │
   └─> 5. 实施修复和验证
```

---

## 1. 常见问题诊断

### 1.1 数据未上报

**症状**: 没有数据发送到后端

**诊断步骤**:

```rust
use tracing::{info, error};
use opentelemetry::global;

// ✅ 步骤 1: 检查 TracerProvider 初始化
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启用详细日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    info!("Initializing tracer provider");
    
    // 检查初始化是否成功
    let tracer_provider = init_tracer()?;
    info!("Tracer provider initialized successfully");
    
    // 设置全局 provider
    global::set_tracer_provider(tracer_provider.clone());
    
    // ✅ 步骤 2: 验证 Span 创建
    let tracer = global::tracer("test");
    let span = tracer.start("test-span");
    info!("Test span created: {:?}", span.span_context());
    
    // ✅ 步骤 3: 强制刷新
    if let Err(e) = tracer_provider.force_flush() {
        error!("Failed to flush: {:?}", e);
    }
    
    // ✅ 步骤 4: 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

fn init_tracer() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(5));
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer)
}
```

**常见原因**:

1. ❌ **未初始化 TracerProvider**
2. ❌ **未设置全局 provider**
3. ❌ **忘记调用 `shutdown`**
4. ❌ **Exporter 配置错误**

**解决方案**:

```rust
// ✅ 推荐：使用初始化检查器
pub struct TelemetryGuard {
    provider: opentelemetry_sdk::trace::TracerProvider,
}

impl TelemetryGuard {
    pub fn init() -> Result<Self, Box<dyn std::error::Error>> {
        let provider = init_tracer()?;
        opentelemetry::global::set_tracer_provider(provider.clone());
        
        // 创建测试 span 验证
        let tracer = opentelemetry::global::tracer("init-check");
        let _span = tracer.start("init-verification");
        
        tracing::info!("Telemetry initialized and verified");
        
        Ok(Self { provider })
    }
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        tracing::info!("Shutting down telemetry");
        if let Err(e) = self.provider.force_flush() {
            tracing::error!("Failed to flush: {:?}", e);
        }
        opentelemetry::global::shutdown_tracer_provider();
    }
}

// 使用方式
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let _guard = TelemetryGuard::init()?;
    
    // 应用逻辑
    run_application().await?;
    
    // _guard 自动清理
    Ok(())
}
```

---

### 1.2 Span 丢失

**症状**: 部分 Span 没有被记录

**诊断代码**:

```rust
use tracing::{instrument, info, warn};
use opentelemetry::trace::{Tracer, TracerProvider};

// ❌ 问题代码：Span 未正确关联
pub async fn process_order_bad(order_id: &str) {
    // Span 1: 创建订单
    let tracer = opentelemetry::global::tracer("app");
    let span1 = tracer.start("create_order");
    create_order_impl(order_id).await;
    // span1 在这里结束
    
    // ❌ Span 2 不是 Span 1 的子 span
    let span2 = tracer.start("validate_order");
    validate_order_impl(order_id).await;
}

// ✅ 修复代码：正确的父子关系
#[instrument(name = "process_order", skip_all, fields(order_id = %order_id))]
pub async fn process_order_good(order_id: &str) {
    // Span 会自动创建为当前上下文的子 span
    create_order(order_id).await;
    validate_order(order_id).await;
}

#[instrument(name = "create_order")]
async fn create_order(order_id: &str) {
    info!("Creating order");
    // 实现
}

#[instrument(name = "validate_order")]
async fn validate_order(order_id: &str) {
    info!("Validating order");
    // 实现
}
```

**常见原因**:

1. ❌ **未使用 `#[instrument]` 宏**
2. ❌ **手动创建 Span 未关联上下文**
3. ❌ **异步任务中丢失上下文**
4. ❌ **跨线程传递上下文错误**

**解决方案**:

```rust
use tracing::Instrument;

// ✅ 推荐：异步任务中保持上下文
pub async fn spawn_task_with_context() {
    let span = tracing::info_span!("background_task");
    
    tokio::spawn(
        async move {
            tracing::info!("Running in background");
            // 任务逻辑
        }
        .instrument(span) // 关键：传递 span
    );
}

// ✅ 推荐：跨线程传递上下文
use opentelemetry::Context;

pub fn run_in_thread_pool(ctx: Context) {
    std::thread::spawn(move || {
        let _guard = ctx.attach();
        
        // 在这个作用域内，追踪上下文已激活
        tracing::info!("Running in thread pool");
    });
}
```

---

### 1.3 TraceID 不连续

**症状**: 分布式追踪链路断裂

**诊断代码**:

```rust
use opentelemetry::{
    global,
    propagation::TextMapPropagator,
    trace::{TraceContextExt, Tracer},
};
use opentelemetry_sdk::propagation::TraceContextPropagator;

// ❌ 问题代码：未传播上下文
pub async fn call_service_bad(client: &reqwest::Client, url: &str) -> Result<String, reqwest::Error> {
    let response = client
        .get(url)
        .send() // ❌ 未注入追踪头部
        .await?;
    
    Ok(response.text().await?)
}

// ✅ 修复代码：正确传播上下文
pub async fn call_service_good(client: &reqwest::Client, url: &str) -> Result<String, reqwest::Error> {
    use opentelemetry::Context;
    use std::collections::HashMap;
    
    // 1. 获取当前上下文
    let cx = Context::current();
    let span = cx.span();
    let span_context = span.span_context();
    
    tracing::debug!(
        "Current trace_id: {:?}, span_id: {:?}",
        span_context.trace_id(),
        span_context.span_id()
    );
    
    // 2. 创建传播器
    let propagator = TraceContextPropagator::new();
    
    // 3. 注入上下文到 HTTP 头部
    let mut headers = HashMap::new();
    propagator.inject_context(&cx, &mut headers);
    
    // 4. 构建请求
    let mut request = client.get(url);
    for (key, value) in headers {
        request = request.header(key, value);
    }
    
    // 5. 发送请求
    let response = request.send().await?;
    
    Ok(response.text().await?)
}

// ✅ 推荐：使用 reqwest 中间件自动注入
use tower_http::trace::TraceLayer;

pub fn create_instrumented_client() -> reqwest::Client {
    use reqwest::header::HeaderMap;
    use opentelemetry_http::HeaderInjector;
    
    let client = reqwest::Client::builder()
        .default_headers({
            let mut headers = HeaderMap::new();
            
            // 自动注入追踪头部
            let cx = opentelemetry::Context::current();
            let propagator = TraceContextPropagator::new();
            let mut injector = HeaderInjector(&mut headers);
            propagator.inject_context(&cx, &mut injector);
            
            headers
        })
        .build()
        .unwrap();
    
    client
}
```

**服务端接收上下文**:

```rust
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use opentelemetry::{
    global,
    propagation::TextMapPropagator,
};
use opentelemetry_sdk::propagation::TraceContextPropagator;

// ✅ Axum 中间件：提取追踪上下文
pub async fn trace_context_middleware(
    request: Request,
    next: Next,
) -> Response {
    use opentelemetry_http::HeaderExtractor;
    
    // 1. 创建传播器
    let propagator = TraceContextPropagator::new();
    
    // 2. 从头部提取上下文
    let extractor = HeaderExtractor(request.headers());
    let parent_cx = propagator.extract(&extractor);
    
    // 3. 创建新的 span
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder("http.request")
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    // 4. 附加到当前上下文
    let cx = opentelemetry::Context::current_with_span(span);
    let _guard = cx.attach();
    
    tracing::info!(
        trace_id = ?cx.span().span_context().trace_id(),
        "Request received"
    );
    
    // 5. 处理请求
    next.run(request).await
}
```

---

### 1.4 Exporter 失败

**症状**: 导出器报错

**诊断代码**:

```rust
use tracing::{error, info};

// ✅ 添加重试逻辑
use opentelemetry_otlp::{ExportConfig, Protocol, WithExportConfig};

pub fn init_resilient_exporter() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use std::time::Duration;
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(5))
        .with_protocol(Protocol::Grpc);
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_batch_config(
            opentelemetry_sdk::trace::BatchConfig::default()
                .with_max_queue_size(2048)
                .with_max_export_batch_size(512)
                .with_scheduled_delay(Duration::from_secs(5))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    info!("Exporter initialized with retry logic");
    
    Ok(tracer)
}

// ✅ 监控导出失败
use opentelemetry::metrics::{Counter, Meter};

pub struct ExporterMetrics {
    export_success: Counter<u64>,
    export_failure: Counter<u64>,
}

impl ExporterMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            export_success: meter
                .u64_counter("otlp.exporter.success")
                .with_description("Successful exports")
                .init(),
            export_failure: meter
                .u64_counter("otlp.exporter.failure")
                .with_description("Failed exports")
                .init(),
        }
    }
    
    pub fn record_success(&self) {
        self.export_success.add(1, &[]);
    }
    
    pub fn record_failure(&self, reason: &str) {
        use opentelemetry::KeyValue;
        self.export_failure.add(1, &[KeyValue::new("reason", reason.to_string())]);
    }
}
```

**常见错误处理**:

```rust
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExporterError {
    #[error("Connection failed: {0}")]
    ConnectionFailed(String),
    
    #[error("Timeout after {0:?}")]
    Timeout(std::time::Duration),
    
    #[error("Authentication failed")]
    AuthenticationFailed,
    
    #[error("Quota exceeded")]
    QuotaExceeded,
}

// ✅ 错误分类和处理
pub async fn handle_export_error(error: ExporterError) {
    match error {
        ExporterError::ConnectionFailed(msg) => {
            error!("Connection failed: {}", msg);
            // 启动重连逻辑
        }
        ExporterError::Timeout(duration) => {
            error!("Timeout after {:?}", duration);
            // 增加超时时间
        }
        ExporterError::AuthenticationFailed => {
            error!("Authentication failed");
            // 刷新认证令牌
        }
        ExporterError::QuotaExceeded => {
            error!("Quota exceeded");
            // 降低采样率
        }
    }
}
```

---

## 2. 性能瓶颈分析

### 2.1 高延迟诊断

**使用 tracing 分析延迟**:

```rust
use tracing::{instrument, info};
use std::time::Instant;

#[instrument]
pub async fn analyze_latency() {
    let start = Instant::now();
    
    // 操作 1
    let op1_start = Instant::now();
    operation1().await;
    info!("Operation 1 took: {:?}", op1_start.elapsed());
    
    // 操作 2
    let op2_start = Instant::now();
    operation2().await;
    info!("Operation 2 took: {:?}", op2_start.elapsed());
    
    info!("Total time: {:?}", start.elapsed());
}

#[instrument]
async fn operation1() {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}

#[instrument]
async fn operation2() {
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
}
```

**使用 criterion 进行基准测试**:

```rust
// benches/otlp_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_span_creation(c: &mut Criterion) {
    let tracer = opentelemetry::global::tracer("bench");
    
    c.bench_function("span_creation", |b| {
        b.iter(|| {
            let _span = tracer.start(black_box("test-span"));
        })
    });
}

fn benchmark_span_with_attributes(c: &mut Criterion) {
    let tracer = opentelemetry::global::tracer("bench");
    
    c.bench_function("span_with_attributes", |b| {
        b.iter(|| {
            let span = tracer.start(black_box("test-span"));
            span.set_attribute(opentelemetry::KeyValue::new("key1", "value1"));
            span.set_attribute(opentelemetry::KeyValue::new("key2", "value2"));
        })
    });
}

criterion_group!(benches, benchmark_span_creation, benchmark_span_with_attributes);
criterion_main!(benches);
```

---

### 2.2 高CPU占用

**诊断 CPU 热点**:

```bash
# 使用 perf 分析
cargo build --release
perf record --call-graph dwarf ./target/release/my_app
perf report

# 使用 flamegraph
cargo install flamegraph
cargo flamegraph --bin my_app
```

**常见优化**:

```rust
// ❌ 问题：频繁创建 Span
pub async fn process_items_bad(items: &[Item]) {
    for item in items {
        let _span = tracing::info_span!("process_item", item_id = %item.id);
        process_item(item).await;
    }
}

// ✅ 优化：批量处理
#[instrument(skip(items))]
pub async fn process_items_good(items: &[Item]) {
    tracing::info!("Processing {} items", items.len());
    
    for chunk in items.chunks(100) {
        process_chunk(chunk).await;
    }
}

#[instrument(skip(chunk))]
async fn process_chunk(chunk: &[Item]) {
    for item in chunk {
        process_item(item).await;
    }
}
```

---

### 2.3 内存占用过高

**监控内存使用**:

```rust
use tracing::info;

pub fn log_memory_usage() {
    #[cfg(target_os = "linux")]
    {
        use std::fs;
        
        if let Ok(status) = fs::read_to_string("/proc/self/status") {
            for line in status.lines() {
                if line.starts_with("VmRSS:") || line.starts_with("VmSize:") {
                    info!("{}", line);
                }
            }
        }
    }
    
    #[cfg(not(target_os = "linux"))]
    {
        info!("Memory monitoring not available on this platform");
    }
}
```

---

### 2.4 批处理优化

```rust
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

// ✅ 推荐配置
pub fn create_optimized_batch_config() -> BatchConfig {
    BatchConfig::default()
        // 队列大小：2048 spans
        .with_max_queue_size(2048)
        
        // 批次大小：512 spans
        .with_max_export_batch_size(512)
        
        // 调度延迟：5 秒
        .with_scheduled_delay(Duration::from_secs(5))
        
        // 最大导出超时：30 秒
        .with_max_export_timeout(Duration::from_secs(30))
}
```

---

## 3. 内存泄漏排查

### 3.1 检测内存泄漏

**使用 valgrind**:

```bash
# 安装 valgrind
sudo apt-get install valgrind

# 运行内存检查
cargo build --release
valgrind --leak-check=full \
         --show-leak-kinds=all \
         --track-origins=yes \
         --verbose \
         ./target/release/my_app
```

---

### 3.2 常见泄漏场景

```rust
// ❌ 场景 1: 循环引用
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    next: Option<Rc<RefCell<Node>>>,
}

pub fn create_cycle() {
    let node1 = Rc::new(RefCell::new(Node { next: None }));
    let node2 = Rc::new(RefCell::new(Node { next: Some(node1.clone()) }));
    node1.borrow_mut().next = Some(node2.clone());
    // ❌ 内存泄漏：循环引用
}

// ✅ 修复：使用 Weak
use std::rc::Weak;

struct SafeNode {
    next: Option<Weak<RefCell<SafeNode>>>,
}

// ❌ 场景 2: 忘记关闭 Span
pub async fn leak_spans() {
    let tracer = opentelemetry::global::tracer("app");
    loop {
        let _span = tracer.start("leaked-span");
        // ❌ Span 没有正确结束
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}

// ✅ 修复：使用 RAII 保证清理
#[tracing::instrument]
pub async fn no_leak_spans() {
    loop {
        // Span 会在作用域结束时自动结束
        process_request().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}
```

---

### 3.3 使用 valgrind 排查

```bash
valgrind --tool=memcheck \
         --leak-check=full \
         --track-origins=yes \
         ./target/debug/my_app
```

---

### 3.4 使用 heaptrack 分析

```bash
# 安装 heaptrack
sudo apt-get install heaptrack

# 运行分析
heaptrack ./target/release/my_app

# 查看结果
heaptrack_gui heaptrack.my_app.*.gz
```

---

## 4. 异步死锁检测

### 4.1 检测死锁

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

// ❌ 死锁场景：相互等待
pub async fn deadlock_example() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    let lock1_clone = lock1.clone();
    let lock2_clone = lock2.clone();
    
    // 任务 1
    let task1 = tokio::spawn(async move {
        let _g1 = lock1_clone.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        let _g2 = lock2_clone.lock().await; // 等待 lock2
    });
    
    // 任务 2
    let task2 = tokio::spawn(async move {
        let _g2 = lock2.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        let _g1 = lock1.lock().await; // 等待 lock1
    });
    
    // ❌ 死锁发生
    let _ = tokio::join!(task1, task2);
}
```

---

### 4.2 常见死锁场景

```rust
// ❌ 场景 1: 嵌套锁
pub async fn nested_locks_bad() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    let _g1 = lock1.lock().await;
    // ❌ 持有 lock1 时获取 lock2
    let _g2 = lock2.lock().await;
}

// ✅ 修复：统一锁顺序
pub async fn nested_locks_good() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    // ✅ 总是按相同顺序获取锁
    let _g1 = lock1.lock().await;
    let _g2 = lock2.lock().await;
}
```

---

### 4.3 使用 tokio-console 诊断

```toml
# Cargo.toml
[dependencies]
console-subscriber = "0.4"
```

```rust
// main.rs
#[tokio::main]
async fn main() {
    console_subscriber::init();
    
    // 应用逻辑
}
```

```bash
# 运行应用
RUSTFLAGS="--cfg tokio_unstable" cargo run

# 在另一个终端运行 tokio-console
tokio-console
```

---

### 4.4 避免死锁最佳实践

```rust
// ✅ 实践 1: 使用 try_lock
use tokio::sync::Mutex;
use std::sync::Arc;

pub async fn try_lock_pattern() {
    let lock = Arc::new(Mutex::new(0));
    
    match lock.try_lock() {
        Ok(guard) => {
            // 获取到锁
            println!("Value: {}", *guard);
        }
        Err(_) => {
            // 锁被占用，执行其他逻辑
            println!("Lock is busy");
        }
    }
}

// ✅ 实践 2: 使用超时
use tokio::time::{timeout, Duration};

pub async fn lock_with_timeout() -> Result<(), Box<dyn std::error::Error>> {
    let lock = Arc::new(Mutex::new(0));
    
    match timeout(Duration::from_secs(1), lock.lock()).await {
        Ok(guard) => {
            println!("Value: {}", *guard);
            Ok(())
        }
        Err(_) => {
            Err("Lock timeout".into())
        }
    }
}
```

---

## 5. 日志和追踪调试

### 5.1 启用详细日志

```rust
use tracing_subscriber::{EnvFilter, fmt, prelude::*};

pub fn init_detailed_logging() {
    tracing_subscriber::registry()
        .with(fmt::layer().with_target(true).with_line_number(true))
        .with(
            EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| {
                    // 详细日志级别
                    "debug,\
                     opentelemetry=trace,\
                     opentelemetry_sdk=trace,\
                     opentelemetry_otlp=trace".into()
                })
        )
        .init();
}
```

---

### 5.2 追踪特定 Span

```rust
#[tracing::instrument(
    name = "debug_span",
    fields(
        debug_info = tracing::field::Empty,
        result = tracing::field::Empty,
    )
)]
pub async fn debug_specific_operation() -> Result<String, Box<dyn std::error::Error>> {
    let span = tracing::Span::current();
    
    // 记录调试信息
    span.record("debug_info", "Starting operation");
    
    let result = perform_operation().await?;
    
    // 记录结果
    span.record("result", &result.as_str());
    
    Ok(result)
}

async fn perform_operation() -> Result<String, Box<dyn std::error::Error>> {
    Ok("Success".to_string())
}
```

---

### 5.3 导出到本地文件

```rust
use opentelemetry_sdk::export::trace::stdout;

pub fn init_file_exporter() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use std::fs::File;
    
    let file = File::create("traces.json")?;
    let exporter = stdout::new_pipeline()
        .with_writer(file)
        .install_simple();
    
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    
    Ok(provider)
}
```

---

## 6. 网络问题排查

### 6.1 连接失败

```rust
use tracing::{error, info};

pub async fn diagnose_connection() {
    use tokio::net::TcpStream;
    
    let endpoint = "localhost:4317";
    
    info!("Attempting to connect to {}", endpoint);
    
    match TcpStream::connect(endpoint).await {
        Ok(_stream) => {
            info!("✅ Connection successful");
        }
        Err(e) => {
            error!("❌ Connection failed: {}", e);
            
            // 详细诊断
            if e.kind() == std::io::ErrorKind::ConnectionRefused {
                error!("Connection refused - is the collector running?");
            } else if e.kind() == std::io::ErrorKind::TimedOut {
                error!("Connection timed out - check network/firewall");
            }
        }
    }
}
```

---

### 6.2 超时问题

```rust
use std::time::Duration;

pub fn configure_timeouts() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10)) // 连接超时
        .with_protocol(opentelemetry_otlp::Protocol::Grpc);
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_batch_config(
            opentelemetry_sdk::trace::BatchConfig::default()
                .with_max_export_timeout(Duration::from_secs(30)) // 导出超时
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer)
}
```

---

### 6.3 TLS/SSL 问题

```rust
pub fn configure_tls() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    use tonic::transport::ClientTlsConfig;
    
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(tonic::transport::Certificate::from_pem(
            std::fs::read("ca.pem")?
        ))
        .domain_name("localhost");
    
    let channel = tonic::transport::Channel::from_static("https://localhost:4317")
        .tls_config(tls_config)?
        .connect_lazy();
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_channel(channel);
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer)
}
```

---

## 7. 配置问题诊断

### 7.1 采样率配置

```rust
use opentelemetry_sdk::trace::{Sampler, SamplerDecision};

// ✅ 验证采样配置
pub fn verify_sampling() {
    let sampler = Sampler::TraceIdRatioBased(0.1); // 10% 采样
    
    // 测试采样决策
    use opentelemetry::trace::{TraceId, SpanKind};
    use opentelemetry_sdk::trace::SamplingResult;
    
    let trace_id = TraceId::from_u128(12345);
    let result = sampler.should_sample(
        None,
        trace_id,
        "test-span",
        &SpanKind::Internal,
        &[],
        &[],
    );
    
    match result.decision {
        SamplerDecision::RecordAndSample => {
            println!("✅ Span will be sampled");
        }
        SamplerDecision::Drop => {
            println!("❌ Span will be dropped");
        }
        SamplerDecision::RecordOnly => {
            println!("⚠️ Span will be recorded but not sampled");
        }
    }
}
```

---

### 7.2 资源属性配置

```rust
use opentelemetry::KeyValue;
use opentelemetry_sdk::Resource;

// ✅ 验证资源属性
pub fn verify_resource_attributes() {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);
    
    println!("Resource attributes:");
    for kv in resource.iter() {
        println!("  {} = {:?}", kv.key, kv.value);
    }
}
```

---

### 7.3 导出器配置

```rust
// ✅ 完整配置检查
pub fn verify_exporter_config() -> Result<(), Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    use std::time::Duration;
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .with_protocol(opentelemetry_otlp::Protocol::Grpc);
    
    println!("✅ Exporter configuration:");
    println!("  Endpoint: http://localhost:4317");
    println!("  Timeout: 10s");
    println!("  Protocol: gRPC");
    
    Ok(())
}
```

---

## 8. 生产环境最佳实践

### 8.1 监控告警

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct TelemetryMetrics {
    spans_created: Counter<u64>,
    spans_exported: Counter<u64>,
    export_duration: Histogram<f64>,
    export_errors: Counter<u64>,
}

impl TelemetryMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            spans_created: meter
                .u64_counter("otlp.spans.created")
                .with_description("Total spans created")
                .init(),
            
            spans_exported: meter
                .u64_counter("otlp.spans.exported")
                .with_description("Total spans exported")
                .init(),
            
            export_duration: meter
                .f64_histogram("otlp.export.duration")
                .with_description("Export duration in seconds")
                .init(),
            
            export_errors: meter
                .u64_counter("otlp.export.errors")
                .with_description("Export errors")
                .init(),
        }
    }
}
```

---

### 8.2 故障恢复

```rust
use tokio::time::{sleep, Duration};

// ✅ 自动重连
pub async fn auto_reconnect_exporter() {
    let mut retry_count = 0;
    let max_retries = 5;
    
    loop {
        match init_tracer().await {
            Ok(provider) => {
                tracing::info!("Exporter connected successfully");
                break;
            }
            Err(e) => {
                retry_count += 1;
                if retry_count >= max_retries {
                    tracing::error!("Failed to connect after {} retries", max_retries);
                    break;
                }
                
                let backoff = Duration::from_secs(2_u64.pow(retry_count));
                tracing::warn!(
                    "Connection failed: {}, retrying in {:?}...",
                    e,
                    backoff
                );
                sleep(backoff).await;
            }
        }
    }
}

async fn init_tracer() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    // 初始化逻辑
    Ok(opentelemetry_sdk::trace::TracerProvider::default())
}
```

---

### 8.3 容量规划

```rust
// ✅ 基于负载的配置
pub fn calculate_batch_config(
    expected_spans_per_second: usize,
) -> opentelemetry_sdk::trace::BatchConfig {
    use std::time::Duration;
    
    // 队列大小：可容纳 10 秒的数据
    let queue_size = expected_spans_per_second * 10;
    
    // 批次大小：每秒导出一次
    let batch_size = expected_spans_per_second;
    
    opentelemetry_sdk::trace::BatchConfig::default()
        .with_max_queue_size(queue_size)
        .with_max_export_batch_size(batch_size)
        .with_scheduled_delay(Duration::from_secs(1))
}
```

---

## 9. 工具和技巧

### 9.1 命令行工具

```bash
# 1. 检查端口是否开放
nc -zv localhost 4317

# 2. 抓包分析
tcpdump -i any -s 0 -w otlp.pcap port 4317

# 3. 查看进程网络连接
lsof -i :4317

# 4. 监控进程资源
top -p $(pgrep my_app)
```

---

### 9.2 可视化工具

- **Jaeger UI**: 查看分布式追踪
- **Grafana**: 可视化指标
- **tokio-console**: 异步任务监控
- **heaptrack**: 内存分析
- **flamegraph**: CPU 火焰图

---

### 9.3 Rust 特定工具

```bash
# cargo-flamegraph: 性能剖析
cargo install flamegraph
cargo flamegraph --bin my_app

# cargo-expand: 查看宏展开
cargo install cargo-expand
cargo expand

# cargo-udeps: 检查未使用的依赖
cargo install cargo-udeps
cargo +nightly udeps
```

---

## 10. 完整诊断案例

### 案例 1: 生产环境 Span 丢失

**问题描述**: 生产环境中 50% 的 Span 丢失

**诊断步骤**:

```rust
// 1. 添加详细日志
use tracing::{info, warn};

#[tracing::instrument]
pub async fn investigate_span_loss() {
    info!("Starting investigation");
    
    // 2. 检查采样率
    let sampler = opentelemetry::global::tracer_provider()
        .tracer("investigation");
    
    // 3. 监控队列大小
    monitor_queue_size().await;
    
    // 4. 检查导出成功率
    check_export_success_rate().await;
}

async fn monitor_queue_size() {
    // 实现队列监控
}

async fn check_export_success_rate() {
    // 实现成功率检查
}
```

**根因**: 批处理队列大小不足，导致 Span 被丢弃

**解决方案**:

```rust
// 增加队列大小
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

pub fn fix_queue_size() -> BatchConfig {
    BatchConfig::default()
        .with_max_queue_size(4096) // 从 2048 增加到 4096
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
}
```

---

### 案例 2: 内存泄漏导致 OOM

**问题描述**: 服务运行几小时后内存持续增长最终 OOM

**诊断步骤**:

```bash
# 1. 使用 heaptrack 分析
heaptrack ./target/release/my_app

# 2. 分析报告
heaptrack_gui heaptrack.my_app.*.gz
```

**根因**: Span 未正确结束，导致内存泄漏

**解决方案**:

```rust
// ❌ 错误代码
pub async fn leak_example() {
    let tracer = opentelemetry::global::tracer("app");
    let _span = tracer.start("long-lived-span");
    
    // Span 永远不会结束
    loop {
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }
}

// ✅ 修复代码
#[tracing::instrument]
pub async fn fixed_example() {
    // Span 会在函数结束时自动结束
    loop {
        process_request().await;
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }
}

#[tracing::instrument]
async fn process_request() {
    // 每次请求创建新的 Span
}
```

---

### 案例 3: 异步死锁导致服务挂起

**问题描述**: 服务偶尔完全无响应

**诊断步骤**:

```bash
# 使用 tokio-console
RUSTFLAGS="--cfg tokio_unstable" cargo run
tokio-console
```

**根因**: 嵌套锁导致死锁

**解决方案**:

```rust
// ❌ 死锁代码
pub async fn deadlock_code() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    let _g1 = lock1.lock().await;
    // 持有 lock1 时尝试获取 lock2
    let _g2 = lock2.lock().await; // 可能死锁
}

// ✅ 修复代码
pub async fn fixed_code() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    // 使用超时
    use tokio::time::{timeout, Duration};
    
    let _g1 = lock1.lock().await;
    
    match timeout(Duration::from_secs(1), lock2.lock()).await {
        Ok(guard) => {
            // 成功获取锁
        }
        Err(_) => {
            // 超时，记录错误
            tracing::error!("Lock timeout");
        }
    }
}
```

---

## 总结

本指南提供了完整的 Rust OTLP 故障排查方法论：

1. ✅ **常见问题快速诊断**
   - 数据未上报
   - Span 丢失
   - TraceID 断裂
   - Exporter 失败

2. ✅ **性能分析**
   - 延迟诊断
   - CPU 热点
   - 内存占用
   - 批处理优化

3. ✅ **内存泄漏**
   - 检测方法
   - 常见场景
   - 工具使用

4. ✅ **异步死锁**
   - 检测技术
   - 典型案例
   - 预防策略

5. ✅ **生产最佳实践**
   - 监控告警
   - 故障恢复
   - 容量规划

通过本指南，您可以快速定位和解决 Rust OTLP 应用的各类问题。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
