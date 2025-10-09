# Rust 同步异步编程模式下的 OTLP 集成详解

> **Rust版本**: 1.90+  
> **OpenTelemetry Rust SDK**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月8日  
> **文档状态**: ✅ Rust 1.90 最新优化版 (仅包含Rust相关内容)

---

## 目录

- [Rust 同步异步编程模式下的 OTLP 集成详解](#rust-同步异步编程模式下的-otlp-集成详解)
  - [目录](#目录)
  - [1. Rust 异步编程基础](#1-rust-异步编程基础)
    - [1.1 异步运行时选择](#11-异步运行时选择)
    - [1.2 Tokio 运行时配置](#12-tokio-运行时配置)
    - [1.3 Rust 1.90 异步特性增强](#13-rust-190-异步特性增强)
    - [1.4 异步编程模式](#14-异步编程模式)
  - [2. OpenTelemetry Rust SDK 集成](#2-opentelemetry-rust-sdk-集成)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 异步初始化](#22-异步初始化)
    - [2.3 同步初始化](#23-同步初始化)
  - [3. 异步追踪模式](#3-异步追踪模式)
    - [3.1 异步函数追踪](#31-异步函数追踪)
    - [3.2 Future追踪](#32-future追踪)
    - [3.3 Stream追踪](#33-stream追踪)
  - [4. 同步追踪模式](#4-同步追踪模式)
    - [4.1 同步函数追踪](#41-同步函数追踪)
    - [4.2 阻塞操作追踪](#42-阻塞操作追踪)
  - [5. 混合编程模式](#5-混合编程模式)
    - [5.1 异步中调用同步](#51-异步中调用同步)
    - [5.2 同步中调用异步](#52-同步中调用异步)
    - [5.3 上下文传播](#53-上下文传播)
  - [6. 高级特性](#6-高级特性)
    - [6.1 零拷贝传输](#61-零拷贝传输)
    - [6.2 批处理优化](#62-批处理优化)
    - [6.3 背压控制](#63-背压控制)
  - [7. 性能优化](#7-性能优化)
    - [7.1 内存优化](#71-内存优化)
    - [7.2 CPU优化](#72-cpu优化)
    - [7.3 网络优化](#73-网络优化)
  - [8. Rust 1.90 OTLP 高级模式](#8-rust-190-otlp-高级模式)
    - [8.1 零成本抽象的遥测收集](#81-零成本抽象的遥测收集)
    - [8.2 异步上下文传播优化](#82-异步上下文传播优化)
    - [8.3 内存池优化](#83-内存池优化)
    - [8.4 异步批处理优化](#84-异步批处理优化)
    - [8.5 流式处理优化](#85-流式处理优化)
  - [9. 错误处理](#9-错误处理)
    - [9.1 异步错误处理](#91-异步错误处理)
    - [9.2 同步错误处理](#92-同步错误处理)
    - [9.3 错误追踪](#93-错误追踪)
  - [10. 测试和基准测试](#10-测试和基准测试)
    - [10.1 异步测试](#101-异步测试)
    - [10.2 性能基准测试](#102-性能基准测试)
  - [11. 生产环境最佳实践](#11-生产环境最佳实践)
  - [12. 完整示例](#12-完整示例)
    - [12.1 Web服务器示例 (Axum + OTLP)](#121-web服务器示例-axum--otlp)
    - [12.2 微服务示例 (gRPC + OTLP)](#122-微服务示例-grpc--otlp)
  - [13. Rust 1.90 特定优化总结](#13-rust-190-特定优化总结)
    - [13.1 编译器优化](#131-编译器优化)
    - [13.2 运行时性能调优](#132-运行时性能调优)
    - [13.3 内存优化技巧](#133-内存优化技巧)
    - [13.4 异步性能最佳实践](#134-异步性能最佳实践)
  - [14. 参考资源](#14-参考资源)
    - [官方文档 (2025年10月最新)](#官方文档-2025年10月最新)
    - [OpenTelemetry规范](#opentelemetry规范)
    - [示例代码和教程](#示例代码和教程)
    - [Rust 1.90 特性文档](#rust-190-特性文档)
    - [性能优化资源](#性能优化资源)
    - [依赖库文档 (2025年10月最新版本)](#依赖库文档-2025年10月最新版本)
    - [社区和支持](#社区和支持)
  - [15. Rust 1.90 Async/Await 特性清单](#15-rust-190-asyncawait-特性清单)
    - [15.1 核心语言特性](#151-核心语言特性)
    - [15.2 性能优化特性](#152-性能优化特性)
    - [15.3 最佳实践总结](#153-最佳实践总结)
    - [15.4 迁移指南](#154-迁移指南)
  - [✨ 文档特性亮点](#-文档特性亮点)
    - [Rust 1.90 核心特性](#rust-190-核心特性)
    - [OpenTelemetry 0.31.0 完整支持](#opentelemetry-0310-完整支持)
    - [性能优化](#性能优化)
    - [生产级特性](#生产级特性)
  - [📚 相关文档导航](#-相关文档导航)
    - [核心组件文档](#核心组件文档)
    - [协议文档](#协议文档)
    - [性能优化1](#性能优化1)
    - [实战案例](#实战案例)
  - [🚀 快速开始](#-快速开始)

---

## 1. Rust 异步编程基础

### 1.1 异步运行时选择

**Rust 异步运行时对比 (2025年10月)**：

```text
┌──────────────┬──────────────┬──────────────┬──────────────┬──────────────────┐
│ 运行时        │ 成熟度       │ 生态系统      │ 性能         │ OTLP支持          │
├──────────────┼──────────────┼──────────────┼──────────────┼──────────────────┤
│ Tokio        │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐⭐ │ ✅ 官方支持      │
│ smol         │ ⭐⭐⭐⭐   │ ⭐⭐⭐      │ ⭐⭐⭐⭐⭐ │ ⚠️ 社区支持     │
│ glommio      │ ⭐⭐⭐     │ ⭐⭐         │ ⭐⭐⭐⭐⭐ │ ⚠️ 实验性       │
│ async-std    │ ⭐⭐⭐     │ ⭐⭐         │ ⭐⭐⭐⭐   │ ⚠️ 社区维护      │
└──────────────┴──────────────┴──────────────┴──────────────┴──────────────────┘

强烈推荐: Tokio 1.47.1+
✅ 最成熟和广泛使用的Rust异步运行时
✅ OpenTelemetry官方直接支持 (rt-tokio特性)
✅ 丰富的生态系统 (tower, hyper, tonic等)
✅ 优秀的性能和稳定性
✅ 活跃的社区维护和更新
✅ 支持Rust 1.90所有新特性

注意: async-std已逐渐被废弃，推荐迁移到Tokio
```

### 1.2 Tokio 运行时配置

**基础配置**：

```rust
use tokio::runtime::{Builder, Runtime};
use std::time::Duration;

/// 创建多线程运行时 (推荐用于生产环境)
fn create_multi_thread_runtime() -> Runtime {
    Builder::new_multi_thread()
        .worker_threads(num_cpus::get()) // 根据CPU核心数设置工作线程
        .thread_name("otlp-worker")
        .thread_stack_size(3 * 1024 * 1024) // 3MB栈大小
        .enable_all() // 启用所有功能 (IO, 时间等)
        .build()
        .expect("Failed to create Tokio runtime")
}

/// 创建单线程运行时 (适用于轻量级应用)
fn create_current_thread_runtime() -> Runtime {
    Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("Failed to create Tokio runtime")
}

/// 自定义配置的运行时
fn create_custom_runtime() -> Runtime {
    Builder::new_multi_thread()
        .worker_threads(8) // 固定8个工作线程
        .max_blocking_threads(512) // 最多512个阻塞线程
        .thread_keep_alive(Duration::from_secs(60)) // 线程保活时间
        .global_queue_interval(31) // 全局队列检查间隔
        .event_interval(61) // 事件检查间隔
        .enable_all()
        .build()
        .expect("Failed to create custom runtime")
}

/// 使用宏快速创建运行时
#[tokio::main]
async fn main() {
    // Tokio会自动创建多线程运行时
    println!("Running in Tokio runtime");
}

/// 自定义运行时宏
#[tokio::main(flavor = "current_thread")]
async fn main_single_thread() {
    // 单线程运行时
    println!("Running in single-thread runtime");
}

/// 完全自定义
#[tokio::main(worker_threads = 4)]
async fn main_custom() {
    // 4个工作线程
    println!("Running with 4 worker threads");
}
```

### 1.3 Rust 1.90 异步特性增强

**Rust 1.90 异步编程关键特性**：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::time::{sleep, Duration};
use opentelemetry::trace::{TraceError, Span};
use serde::Serialize;

/// 1. 原生 Async Fn in Trait (AFIT) - Rust 1.75+ 稳定，1.90 优化
/// 无需 #[async_trait] 宏，零成本抽象
/// 
/// Rust 1.90 改进:
/// - 更智能的生命周期推导
/// - 更好的编译器优化和内联
/// - 减少了 Future 大小
/// - 改进的错误消息
trait TelemetryExporter: Send + Sync {
    /// 直接在 trait 中定义异步方法
    async fn export_spans(&self, spans: Vec<SpanData>) -> Result<(), TraceError>;
    
    /// 支持生命周期参数 - Rust 1.90 改进的生命周期推导
    async fn export_with_context<'a>(&'a self, context: &'a Context) -> Result<(), TraceError>;
    
    /// 支持泛型 - Rust 1.90 改进的类型推导
    async fn export_batch<T>(&self, batch: Vec<T>) -> Result<(), TraceError>
    where
        T: Serialize + Send + Sync + 'static;
    
    /// Rust 1.90: 异步默认实现
    async fn export_with_retry(&self, spans: Vec<SpanData>, max_retries: u32) -> Result<(), TraceError> {
        for attempt in 0..max_retries {
            match self.export_spans(spans.clone()).await {
                Ok(_) => return Ok(()),
                Err(e) if attempt < max_retries - 1 => {
                    tracing::warn!("Export failed, retrying... (attempt {}/{})", attempt + 1, max_retries);
                    tokio::time::sleep(Duration::from_millis(100 * (attempt + 1) as u64)).await;
                }
                Err(e) => return Err(e),
            }
        }
        Err(TraceError::Other(Box::new(std::io::Error::new(
            std::io::ErrorKind::Other,
            "Max retries exceeded"
        ))))
    }
}

/// 实现异步 trait (不需要额外宏) - 零成本抽象
#[derive(Clone)]
struct OtlpExporter {
    endpoint: String,
    client: reqwest::Client,
}

impl TelemetryExporter for OtlpExporter {
    async fn export_spans(&self, spans: Vec<SpanData>) -> Result<(), TraceError> {
        // 直接实现异步方法，编译器生成高效代码
        self.send_to_backend(spans).await
    }
    
    async fn export_with_context<'a>(&'a self, context: &'a Context) -> Result<(), TraceError> {
        // 生命周期自动推导，无运行时开销
        Ok(())
    }
    
    async fn export_batch<T>(&self, batch: Vec<T>) -> Result<(), TraceError>
    where
        T: Serialize + Send + Sync + 'static,
    {
        // 泛型异步方法，单态化后无虚函数开销
        Ok(())
    }
}

// 辅助类型
#[derive(Debug, Serialize)]
struct SpanData {
    trace_id: String,
    span_id: String,
    name: String,
}

impl OtlpExporter {
    async fn send_to_backend(&self, spans: Vec<SpanData>) -> Result<(), TraceError> {
        // 实际发送实现
        Ok(())
    }
}

/// 2. impl Trait in Associated Types (RPITIT) - Rust 1.75+，1.90 优化
/// 零成本抽象，无需 Box<dyn Future>
trait AsyncProcessor: Send + Sync {
    /// 返回实现了 Future 的类型 - 编译时确定类型
    fn process(&self) -> impl Future<Output = Result<(), ProcessError>> + Send;
    
    /// 简化异步迭代器 - 零拷贝流式处理
    fn stream_data(&self) -> impl tokio_stream::Stream<Item = TelemetryData> + Send;
}

struct SpanProcessor {
    batch_size: usize,
}

impl AsyncProcessor for SpanProcessor {
    // Rust 1.90 优化：返回类型在编译时确定，无虚函数调用开销
    fn process(&self) -> impl Future<Output = Result<(), ProcessError>> + Send {
        async move {
            // 异步处理逻辑
            tracing::info!("Processing batch of size {}", self.batch_size);
            Ok(())
        }
    }
    
    // Rust 1.90 优化：编译器内联优化
    fn stream_data(&self) -> impl tokio_stream::Stream<Item = TelemetryData> + Send {
        tokio_stream::iter(vec![TelemetryData::default()])
    }
}

// 辅助类型
#[derive(Debug, Clone)]
struct ProcessError(String);

#[derive(Debug, Default, Clone)]
struct TelemetryData {
    timestamp: u64,
    payload: Vec<u8>,
}

/// 3. Rust 1.90 改进的 Future 组合器
/// 高性能并发执行，零开销抽象
async fn advanced_future_combinators() {
    use tokio::try_join;
    use futures::future::{try_join_all, select, Either};
    use tokio::time::timeout;
    
    // 并发执行多个异步操作 - Rust 1.90 优化的 try_join!
    // 编译器会生成最优化的并发代码
    let (traces, metrics, logs) = try_join!(
        export_traces(),
        export_metrics(),
        export_logs(),
    ).expect("Failed to export telemetry");
    
    // 动态数量的 Future - 使用 FuturesUnordered 优化
    let futures = vec![
        export_span(1),
        export_span(2),
        export_span(3),
    ];
    
    // Rust 1.90: 编译器优化的批量 await
    try_join_all(futures)
        .await
        .expect("Failed to export spans");
    
    // Rust 1.90: 改进的 select 模式
    // 竞争执行两个 Future，返回第一个完成的
    let result = select(
        export_traces(),
        timeout(Duration::from_secs(5), export_metrics())
    ).await;
    
    match result {
        Either::Left((traces, _)) => {
            tracing::info!("Traces exported first");
        }
        Either::Right((metrics, _)) => {
            tracing::info!("Metrics exported first");
        }
    }
    
    // Rust 1.90: 超时处理优化
    match timeout(Duration::from_secs(10), export_logs()).await {
        Ok(Ok(_)) => tracing::info!("Logs exported successfully"),
        Ok(Err(e)) => tracing::error!("Export failed: {}", e),
        Err(_) => tracing::error!("Export timed out"),
    }
}

/// 4. Rust 1.90: 异步闭包和迭代器优化
async fn async_iterators_example() {
    use futures::stream::{StreamExt, FuturesUnordered};
    
    let span_ids = vec![1, 2, 3, 4, 5];
    
    // 使用传统方式
    let futures: Vec<_> = span_ids.iter()
        .map(|&id| async move {
            export_span(id).await
        })
        .collect();
    
    try_join_all(futures).await.ok();
    
    // Rust 1.90: 优化的异步迭代器模式
    let mut tasks = span_ids.into_iter()
        .map(|id| tokio::spawn(async move {
            export_span(id).await
        }))
        .collect::<FuturesUnordered<_>>();
    
    while let Some(result) = tasks.next().await {
        match result {
            Ok(Ok(_)) => tracing::trace!("Span exported"),
            Ok(Err(e)) => tracing::error!("Export error: {}", e),
            Err(e) => tracing::error!("Task panic: {}", e),
        }
    }
}

// 辅助函数
async fn export_traces() -> Result<(), Box<dyn std::error::Error>> {
    tracing::debug!("Exporting traces");
    Ok(())
}

async fn export_metrics() -> Result<(), Box<dyn std::error::Error>> {
    tracing::debug!("Exporting metrics");
    Ok(())
}

async fn export_logs() -> Result<(), Box<dyn std::error::Error>> {
    tracing::debug!("Exporting logs");
    Ok(())
}

async fn export_span(id: u64) -> Result<(), Box<dyn std::error::Error>> {
    tracing::trace!("Exporting span {}", id);
    Ok(())
}
```

### 1.4 异步编程模式

**基础异步模式**：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::time::{sleep, Duration};

/// 1. async/await 模式 (推荐)
async fn fetch_data() -> Result<String, Box<dyn std::error::Error>> {
    // 模拟异步IO操作
    sleep(Duration::from_millis(100)).await;
    Ok("data".to_string())
}

/// 2. Future trait 手动实现
struct CustomFuture {
    completed: bool,
}

impl Future for CustomFuture {
    type Output = String;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.completed {
            Poll::Ready("completed".to_string())
        } else {
            self.completed = true;
            // 通知再次轮询
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// 3. 并发执行
async fn concurrent_operations() {
    use tokio::join;
    
    let (result1, result2, result3) = join!(
        fetch_data(),
        fetch_data(),
        fetch_data(),
    );
    
    println!("Results: {:?}, {:?}, {:?}", result1, result2, result3);
}

/// 4. 选择性执行
async fn select_operation() {
    use tokio::select;
    
    select! {
        result = fetch_data() => {
            println!("fetch_data completed: {:?}", result);
        }
        _ = sleep(Duration::from_secs(1)) => {
            println!("Timeout!");
        }
    }
}

/// 5. Stream 处理
async fn stream_processing() {
    use tokio_stream::{self as stream, StreamExt};
    
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);
    
    while let Some(item) = stream.next().await {
        println!("Item: {}", item);
    }
}

/// 6. Channel 通信
async fn channel_communication() {
    use tokio::sync::mpsc;
    
    let (tx, mut rx) = mpsc::channel(32);
    
    // 发送任务
    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
        }
    });
    
    // 接收任务
    while let Some(value) = rx.recv().await {
        println!("Received: {}", value);
    }
}
```

---

## 2. OpenTelemetry Rust SDK 集成

### 2.1 依赖配置

**Cargo.toml 配置**：

```toml
[package]
name = "otlp-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# ========== OpenTelemetry 核心 (2025年10月最新版本 - Rust 1.90优化) ==========
# OpenTelemetry 0.31.0 完全支持 Rust 1.90 的 async fn in traits
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = [
    "rt-tokio",                    # Tokio运行时支持 (推荐)
    "rt-tokio-current-thread",     # 单线程运行时支持
    "trace",                        # 追踪功能
    "metrics",                      # 指标功能
    "logs",                         # 日志功能
] }
opentelemetry-otlp = { version = "0.31.0", features = [
    "grpc-tonic",                  # gRPC传输 (高性能，推荐)
    "http-json",                   # HTTP/JSON传输
    "http-proto",                  # HTTP/Protobuf传输
    "trace",                       # 追踪数据导出
    "metrics",                     # 指标数据导出
    "logs",                        # 日志数据导出
] }
opentelemetry-stdout = "0.31.0"  # 标准输出导出器（调试用）
opentelemetry-proto = { version = "0.31.0", features = [
    "gen-tonic",                   # Tonic代码生成
    "trace",                       # 追踪协议
    "metrics",                     # 指标协议
    "logs",                        # 日志协议
] }

# ========== 追踪和结构化日志集成 (Rust 1.90兼容) ==========
tracing = "0.1.41"               # 结构化追踪和日志框架
tracing-subscriber = { version = "0.3.20", features = [
    "env-filter",                  # 环境变量过滤
    "json",                        # JSON格式输出
    "ansi",                        # ANSI颜色终端
    "registry",                    # 订阅者注册表
    "tracing-log",                 # log crate集成
] }
tracing-opentelemetry = "0.31"   # OpenTelemetry集成层
tracing-appender = "0.2"         # 异步日志文件写入
log = "0.4.28"                   # 标准日志接口

# ========== 异步运行时 - Tokio生态系统 (Rust 1.90全面优化) ==========
tokio = { version = "1.47.1", features = ["full"] }  # 完整Tokio异步运行时
tokio-util = { version = "0.7.16", features = [
    "codec",                       # 编解码支持
    "compat",                      # 兼容性支持
    "time",                        # 时间工具
] }
tokio-stream = "0.1.17"          # 异步流处理
futures = "0.3.31"               # Future trait和组合器
futures-util = "0.3.31"          # Future工具集
# 注意: Rust 1.90 原生支持 async fn in traits，无需 async-trait (可选)
# async-trait = "0.1.89"  # 仅在需要向后兼容时使用

# ========== gRPC 支持 (Rust 1.90性能优化) ==========
tonic = { version = "0.14.2", features = [
    "transport",                   # 传输层
    "tls-ring",                    # Ring TLS支持
    "tls-webpki-roots",            # WebPKI根证书
    "channel",                     # 通道支持
    "prost",                       # Protobuf支持
    "codegen",                     # 代码生成
] }
tonic-build = "0.14.2"           # gRPC构建工具
prost = "0.14.1"                 # Protocol Buffers
prost-types = "0.14.1"           # Protobuf类型

# ========== HTTP 支持 (Rust 1.90优化) ==========
reqwest = { version = "0.12.23", features = [
    "json",                        # JSON支持
    "rustls-tls",                  # RustLS TLS后端 (推荐)
    "stream",                      # 流式传输
    "gzip",                        # Gzip压缩
    "brotli",                      # Brotli压缩
    "deflate",                     # Deflate压缩
] }
hyper = { version = "1.7.0", features = ["full", "http2"] }  # HTTP/2支持
hyper-util = { version = "0.1.18", features = ["tokio", "client", "server"] }
http = "1.3.2"                   # HTTP类型
http-body-util = "0.1.4"         # HTTP body工具

# ========== TLS 和安全 (Rust 1.90安全增强) ==========
rustls = { version = "0.23.33", features = ["ring"] }  # 纯Rust TLS实现
tokio-rustls = "0.26.5"          # Tokio RustLS集成
rustls-pemfile = "2.2.1"         # PEM文件解析
webpki-roots = "1.1.2"           # Web PKI根证书

# ========== 错误处理 (Rust 1.90兼容) ==========
anyhow = "1.0.100"               # 灵活的错误处理
thiserror = "2.0.17"             # 派生错误宏

# ========== 序列化 (Rust 1.90性能优化) ==========
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"           # JSON序列化
bincode = "2.0.1"                # 高性能二进制序列化

# ========== 高性能并发和同步 (Rust 1.90优化) ==========
parking_lot = "0.12.5"           # 高性能Mutex和RwLock
crossbeam = "0.8.4"              # 无锁数据结构
dashmap = "6.1.0"                # 并发HashMap
rayon = "1.11.1"                 # 数据并行处理

# ========== 性能优化库 (Rust 1.90零成本抽象) ==========
bytes = "1.10.1"                 # 零拷贝字节操作
once_cell = "1.21.3"             # 单次初始化
num_cpus = "1.17.0"              # CPU核心数检测

# ========== 时间处理 (Rust 1.90兼容) ==========
chrono = { version = "0.4.42", features = ["serde"] }  # 日期时间处理
uuid = { version = "1.18.1", features = ["v4", "serde"] }  # UUID生成

# ========== 配置管理 ==========
config = "0.15.18"               # 配置文件管理
dotenvy = "0.15.8"               # .env文件支持

# ========== 压缩算法 (可选，用于数据压缩) ==========
flate2 = "1.1.4"                 # Gzip/Deflate压缩
brotli = "8.0.2"                 # Brotli压缩

# ========== 开发和测试 ==========
[dev-dependencies]
tokio-test = "0.4.4"             # Tokio测试工具
criterion = "0.7.0"              # 基准测试框架
mockall = "0.13.1"               # 模拟对象生成
proptest = "1.8.0"               # 属性测试
tempfile = "3.23.0"              # 临时文件

# ========== 特性标志 ==========
[features]
default = ["grpc", "http", "compression"]
grpc = ["tonic", "prost"]        # gRPC传输支持
http = ["reqwest", "hyper"]      # HTTP传输支持
compression = ["flate2", "brotli"]  # 压缩支持
full = ["grpc", "http", "compression"]  # 完整功能
```

### 2.2 异步初始化

**完整异步初始化流程 (Rust 1.90 + OpenTelemetry 0.31.0)**：

```rust
use opentelemetry::{
    global,
    trace::{TraceError, TracerProvider as _, Tracer},
    KeyValue,
};
use opentelemetry_otlp::{WithExportConfig, Protocol};
use opentelemetry_sdk::{
    trace::{RandomIdGenerator, Sampler, BatchConfig},
    Resource,
    runtime::Tokio,
};
use std::time::Duration;
use tonic::metadata::{MetadataMap, MetadataValue};

/// 异步初始化 OTLP (gRPC) - Rust 1.90 最新优化版
/// 
/// 特性:
/// - 零成本抽象 (Rust 1.90)
/// - 类型安全的配置
/// - 完整的错误处理
/// - 生产级性能优化
pub async fn init_otlp_grpc() -> Result<opentelemetry_sdk::trace::TracerProvider, TraceError> {
    // 1. 配置 Resource (服务元数据) - OpenTelemetry 语义约定
    let resource = Resource::builder_empty()
        .with_service_name("rust-otlp-service")
        .with_attributes(vec![
            // 服务信息
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            KeyValue::new("service.namespace", "production"),
            KeyValue::new("deployment.environment", "production"),
            KeyValue::new("service.instance.id", uuid::Uuid::new_v4().to_string()),
            
            // 主机信息
            KeyValue::new("host.name", 
                std::env::var("HOSTNAME")
                    .unwrap_or_else(|_| "unknown".to_string())),
            KeyValue::new("host.arch", std::env::consts::ARCH),
            KeyValue::new("os.type", std::env::consts::OS),
            
            // SDK信息 (语义约定)
            KeyValue::new("telemetry.sdk.name", "opentelemetry"),
            KeyValue::new("telemetry.sdk.language", "rust"),
            KeyValue::new("telemetry.sdk.version", "0.31.0"),
        ])
        .build();

    // 2. 配置 gRPC 导出器 - TLS、认证、压缩 (Rust 1.90优化)
    let mut metadata = MetadataMap::new();
    
    // 添加认证头 (生产环境应从环境变量读取)
    if let Ok(api_key) = std::env::var("OTLP_API_KEY") {
        metadata.insert(
            "x-api-key", 
            MetadataValue::from_str(&api_key).expect("Invalid API key")
        );
    }
    
    if let Ok(token) = std::env::var("OTLP_AUTH_TOKEN") {
        let bearer = format!("Bearer {}", token);
        metadata.insert(
            "authorization",
            MetadataValue::from_str(&bearer).expect("Invalid token")
        );
    }

    // 从环境变量读取端点配置
    let endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "https://localhost:4317".to_string());

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(endpoint)                    // OTLP gRPC 端点
        .with_timeout(Duration::from_secs(10))      // 导出超时
        .with_metadata(metadata)                     // 自定义元数据
        // Rust 1.90: 类型安全的 Protocol 配置
        .with_protocol(Protocol::Grpc)              
        .build_span_exporter()?;

    // 3. 配置批处理器 - Rust 1.90 高性能优化
    let batch_config = BatchConfig::default()
        .with_max_queue_size(2048)                  // 内存队列大小
        .with_max_export_batch_size(512)            // 每批最多512个span
        .with_scheduled_delay(Duration::from_secs(5))  // 5秒定时导出
        .with_max_concurrent_exports(4);            // 最多4个并发导出

    // 4. 配置智能采样器 - 基于上下文的采样
    let sampler = Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1)            // 10% 采样率
    ));

    // 5. 配置 TracerProvider - 完整生产级配置
    let tracer_provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_batch_exporter(exporter, Tokio)       // Tokio运行时
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)             // 资源属性
                .with_sampler(sampler)               // 采样策略
                .with_id_generator(RandomIdGenerator::default())  // ID生成器
                // Span限制 (防止内存泄漏)
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
                .with_max_links_per_span(128)
                .with_max_attributes_per_event(128)
                .with_max_attributes_per_link(128)
        )
        .build();

    // 6. 设置全局 TracerProvider (Rust 1.90: 线程安全)
    global::set_tracer_provider(tracer_provider.clone());

    tracing::info!("OpenTelemetry TracerProvider initialized successfully");
    
    Ok(tracer_provider)
}

/// 异步初始化 OTLP (HTTP/JSON) - Rust 1.90 最新优化版
/// 
/// 特性:
/// - HTTP/2 支持
/// - 自动压缩 (gzip, brotli, deflate)
/// - RustLS TLS 后端 (纯Rust实现)
/// - 类型安全的配置
pub async fn init_otlp_http() -> Result<opentelemetry_sdk::trace::TracerProvider, TraceError> {
    // Resource配置 - 与gRPC版本保持一致
    let resource = Resource::builder_empty()
        .with_service_name("rust-otlp-http-service")
        .with_attributes(vec![
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            KeyValue::new("deployment.environment", "production"),
            KeyValue::new("telemetry.sdk.name", "opentelemetry"),
            KeyValue::new("telemetry.sdk.language", "rust"),
            KeyValue::new("telemetry.sdk.version", "0.31.0"),
        ])
        .build();

    // HTTP 客户端配置 - Rust 1.90 优化
    let http_client = reqwest::Client::builder()
        .timeout(Duration::from_secs(10))
        .connect_timeout(Duration::from_secs(5))
        .pool_idle_timeout(Duration::from_secs(30))
        .pool_max_idle_per_host(10)            // 连接池优化
        // 压缩支持 (Rust 1.90: 零拷贝压缩)
        .gzip(true)                             // Gzip压缩
        .brotli(true)                           // Brotli压缩 (更高压缩比)
        .deflate(true)                          // Deflate压缩
        // TLS配置 (使用 RustLS - 纯Rust实现)
        .use_rustls_tls()                       
        .https_only(true)                       // 强制HTTPS
        .build()
        .expect("Failed to create HTTP client");

    // 从环境变量读取HTTP端点
    let endpoint = std::env::var("OTLP_HTTP_ENDPOINT")
        .unwrap_or_else(|_| "https://localhost:4318/v1/traces".to_string());

    let exporter = opentelemetry_otlp::new_exporter()
        .http()
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(10))
        .with_http_client(http_client)
        .with_protocol(Protocol::HttpBinary)    // Protobuf over HTTP (推荐)
        // 或使用 Protocol::HttpJson for JSON格式
        .build_span_exporter()?;

    // 批处理配置 - HTTP传输优化
    let batch_config = BatchConfig::default()
        .with_max_queue_size(4096)              // 更大的队列 (HTTP延迟更高)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .with_max_concurrent_exports(2);        // HTTP并发限制更低

    let tracer_provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_batch_exporter(exporter, Tokio)
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
                .with_sampler(Sampler::AlwaysOn)    // 始终采样 (测试环境)
                .with_id_generator(RandomIdGenerator::default())
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
                .with_max_links_per_span(128)
        )
        .build();

    global::set_tracer_provider(tracer_provider.clone());
    
    tracing::info!("OpenTelemetry HTTP TracerProvider initialized");

    Ok(tracer_provider)
}

/// Metrics 导出器初始化 - Rust 1.90 + OpenTelemetry 0.31.0
/// 
/// 支持:
/// - Counter (计数器)
/// - UpDownCounter (上下计数器)
/// - Histogram (直方图)
/// - Gauge (仪表)
/// - 自动聚合和导出
pub async fn init_otlp_metrics() -> Result<opentelemetry_sdk::metrics::SdkMeterProvider, Box<dyn std::error::Error>> {
    use opentelemetry_sdk::metrics::{
        SdkMeterProvider, 
        PeriodicReader,
        Temporality,
    };
    
    // 配置资源
    let resource = Resource::builder_empty()
        .with_service_name("rust-otlp-metrics")
        .with_attributes(vec![
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            KeyValue::new("deployment.environment", "production"),
        ])
        .build();

    // Metrics导出器 - gRPC
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(
            std::env::var("OTLP_ENDPOINT")
                .unwrap_or_else(|_| "https://localhost:4317".to_string())
        )
        .with_timeout(Duration::from_secs(10))
        .build_metrics_exporter(
            // Rust 1.90: 类型安全的Temporality配置
            Temporality::Cumulative,  // 累积模式 (推荐用于Prometheus)
            // 或使用 Temporality::Delta for 增量模式
        )?;

    // 定期读取器 - Rust 1.90 优化
    let reader = PeriodicReader::builder(exporter, Tokio)
        .with_interval(Duration::from_secs(60))     // 60秒导出间隔
        .with_timeout(Duration::from_secs(30))      // 导出超时
        .build();

    // MeterProvider配置 - 生产级设置
    let meter_provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(resource)
        .build();

    // 设置全局MeterProvider
    global::set_meter_provider(meter_provider.clone());
    
    tracing::info!("OpenTelemetry MeterProvider initialized");

    Ok(meter_provider)
}

/// Logs 导出器初始化 - Rust 1.90 + OpenTelemetry 0.31.0
/// 
/// 特性:
/// - 结构化日志导出
/// - 批处理优化
/// - 自动上下文关联
/// - 与tracing集成
pub async fn init_otlp_logs() -> Result<opentelemetry_sdk::logs::LoggerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_sdk::logs::{LoggerProvider, BatchLogProcessor, BatchConfig};
    
    // 配置资源
    let resource = Resource::builder_empty()
        .with_service_name("rust-otlp-logs")
        .with_attributes(vec![
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            KeyValue::new("deployment.environment", "production"),
        ])
        .build();

    // Logs导出器 - gRPC
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(
            std::env::var("OTLP_ENDPOINT")
                .unwrap_or_else(|_| "https://localhost:4317".to_string())
        )
        .with_timeout(Duration::from_secs(10))
        .build_log_exporter()?;

    // 批处理配置 - Rust 1.90 优化
    let batch_config = BatchConfig::default()
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .with_max_concurrent_exports(2);

    // 批处理器
    let processor = BatchLogProcessor::builder(exporter, Tokio)
        .with_batch_config(batch_config)
        .build();

    // LoggerProvider配置
    let logger_provider = LoggerProvider::builder()
        .with_log_processor(processor)
        .with_resource(resource)
        .build();

    // 设置全局LoggerProvider
    global::set_logger_provider(logger_provider.clone());
    
    tracing::info!("OpenTelemetry LoggerProvider initialized");

    Ok(logger_provider)
}

/// 集成 tracing 和 opentelemetry - Rust 1.90 优化版
/// 
/// 特性:
/// - 结构化日志 (tracing)
/// - OpenTelemetry集成
/// - JSON格式输出
/// - 环境变量过滤
/// - 异步日志文件写入
pub fn init_tracing_subscriber() {
    use tracing_subscriber::{
        layer::SubscriberExt, 
        util::SubscriberInitExt,
        fmt,
        EnvFilter,
    };

    // 创建 OpenTelemetry 追踪层
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(global::tracer("tracing-otel"));

    // 配置日志格式层 - Rust 1.90 优化
    let fmt_layer = fmt::layer()
        .with_target(true)              // 显示目标模块
        .with_thread_ids(true)          // 显示线程ID
        .with_thread_names(true)        // 显示线程名称
        .with_line_number(true)         // 显示行号
        .with_file(true)                // 显示文件名
        .with_ansi(true)                // 启用ANSI颜色
        .json();                         // JSON格式输出 (推荐生产环境)
        // 或使用 .pretty() for 开发环境

    // 环境变量过滤 - 支持 RUST_LOG
    let filter_layer = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| {
            // 默认过滤规则
            EnvFilter::new("info")
                // 可以添加更细粒度的过滤
                // .add_directive("hyper=warn".parse().unwrap())
                // .add_directive("tonic=warn".parse().unwrap())
        });

    // 组合所有层 - Rust 1.90 零成本抽象
    tracing_subscriber::registry()
        .with(filter_layer)              // 过滤层
        .with(fmt_layer)                 // 格式化层
        .with(telemetry_layer)           // OpenTelemetry层
        .init();
    
    tracing::info!("Tracing subscriber initialized with OpenTelemetry");
}

/// 完整遥测系统初始化 - Rust 1.90 生产级实现
/// 
/// 功能:
/// - Traces (追踪)
/// - Metrics (指标)
/// - Logs (日志)
/// - 优雅关闭
/// - 错误处理
pub async fn setup_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("Initializing telemetry system...");

    // 1. 初始化 Traces (追踪)
    let tracer_provider = init_otlp_grpc().await
        .map_err(|e| format!("Failed to initialize tracer: {}", e))?;

    // 2. 初始化 Metrics (指标)
    let meter_provider = init_otlp_metrics().await
        .map_err(|e| format!("Failed to initialize metrics: {}", e))?;

    // 3. 初始化 Logs (日志)
    let logger_provider = init_otlp_logs().await
        .map_err(|e| format!("Failed to initialize logs: {}", e))?;

    // 4. 初始化 tracing 订阅者
    init_tracing_subscriber();

    tracing::info!("Telemetry system initialized successfully");

    // 5. 设置优雅关闭 (Rust 1.90: async drop 模拟)
    tokio::spawn(async move {
        // 等待 Ctrl+C 信号
        match tokio::signal::ctrl_c().await {
            Ok(_) => {
                tracing::info!("Received shutdown signal, shutting down telemetry...");
            }
            Err(e) => {
                tracing::error!("Error waiting for shutdown signal: {}", e);
            }
        }
        
        // 刷新并关闭所有 providers
        // Rust 1.90: 并发关闭多个providers
        let shutdown_results = tokio::join!(
            tokio::task::spawn_blocking(move || tracer_provider.shutdown()),
            tokio::task::spawn_blocking(move || meter_provider.shutdown()),
            tokio::task::spawn_blocking(move || logger_provider.shutdown()),
        );
        
        // 检查关闭结果
        for (i, result) in shutdown_results.iter().enumerate() {
            match result {
                Ok(Ok(_)) => tracing::info!("Provider {} shut down successfully", i),
                Ok(Err(e)) => tracing::error!("Error shutting down provider {}: {:?}", i, e),
                Err(e) => tracing::error!("Task panic for provider {}: {:?}", i, e),
            }
        }
        
        tracing::info!("Telemetry system shut down complete");
    });

    Ok(())
}

/// 简化版初始化 - 仅初始化 Traces
pub async fn setup_telemetry_simple() -> Result<(), Box<dyn std::error::Error>> {
    // 仅初始化追踪
    init_otlp_grpc().await?;
    init_tracing_subscriber();
    
    tracing::info!("Simple telemetry initialized (traces only)");
    
    Ok(())
}
```

### 2.3 同步初始化

**同步环境下的初始化**：

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{self, TracerProvider};
use std::sync::Once;

static INIT: Once = Once::new();

/// 同步初始化 (使用 tokio::runtime::Handle)
pub fn init_otlp_sync() -> Result<(), Box<dyn std::error::Error>> {
    INIT.call_once(|| {
        // 创建运行时句柄
        let rt = tokio::runtime::Runtime::new().unwrap();
        
        // 在运行时中初始化
        rt.block_on(async {
            match init_otlp_grpc().await {
                Ok(_) => {
                    init_tracing_subscriber();
                    tracing::info!("Telemetry initialized successfully");
                }
                Err(e) => {
                    eprintln!("Failed to initialize telemetry: {}", e);
                }
            }
        });
    });

    Ok(())
}

/// 懒加载初始化
pub fn lazy_init_otlp() {
    use once_cell::sync::Lazy;
    
    static TELEMETRY: Lazy<Result<(), Box<dyn std::error::Error + Send + Sync>>> = 
        Lazy::new(|| {
            init_otlp_sync()
        });
    
    // 强制初始化
    let _ = &*TELEMETRY;
}
```

---

## 3. 异步追踪模式

### 3.1 异步函数追踪

**使用 tracing 宏追踪异步函数**：

```rust
use tracing::{instrument, info, warn, error, debug, trace};
use opentelemetry::trace::{Tracer, Span, SpanKind};
use std::time::Duration;
use tokio::time::sleep;

/// 1. 基础异步函数追踪
#[instrument]
async fn fetch_user(user_id: u64) -> Result<String, Box<dyn std::error::Error>> {
    info!("Fetching user with id: {}", user_id);
    
    // 模拟数据库查询
    sleep(Duration::from_millis(100)).await;
    
    if user_id == 0 {
        error!("Invalid user id");
        return Err("Invalid user id".into());
    }
    
    Ok(format!("User_{}", user_id))
}

/// 2. 带字段的追踪
#[instrument(fields(
    user.id = %user_id,
    user.type = "premium",
    db.system = "postgresql"
))]
async fn fetch_premium_user(user_id: u64) -> Result<String, Box<dyn std::error::Error>> {
    debug!("Querying premium user");
    
    // 添加动态字段
    tracing::Span::current().record("user.found", &true);
    
    sleep(Duration::from_millis(50)).await;
    Ok(format!("PremiumUser_{}", user_id))
}

/// 3. 跳过某些参数
#[instrument(skip(password))]
async fn authenticate(username: &str, password: &str) -> Result<bool, Box<dyn std::error::Error>> {
    info!("Authenticating user: {}", username);
    
    // password 不会被记录到追踪中
    sleep(Duration::from_millis(200)).await;
    
    Ok(true)
}

/// 4. 自定义 Span 名称
#[instrument(name = "database.query", level = "debug")]
async fn query_database(sql: &str) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    trace!("Executing SQL: {}", sql);
    
    sleep(Duration::from_millis(150)).await;
    
    Ok(vec!["result1".to_string(), "result2".to_string()])
}

/// 5. 手动创建 Span
async fn manual_span_creation() {
    use opentelemetry::global;
    
    let tracer = global::tracer("manual-tracer");
    
    let mut span = tracer
        .span_builder("complex_operation")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    
    // 在 span 上下文中执行操作
    {
        let _guard = span.make_current();
        
        // 添加属性
        span.set_attribute(opentelemetry::KeyValue::new("operation.type", "batch"));
        
        // 添加事件
        span.add_event("Processing started".to_string(), vec![]);
        
        // 执行业务逻辑
        sleep(Duration::from_millis(100)).await;
        
        span.add_event("Processing completed".to_string(), vec![]);
    }
    
    span.end();
}

/// 6. 嵌套 Span
#[instrument]
async fn parent_operation() {
    info!("Parent operation started");
    
    // 子操作会自动成为当前 span 的子 span
    child_operation().await;
    
    info!("Parent operation completed");
}

#[instrument]
async fn child_operation() {
    info!("Child operation executing");
    sleep(Duration::from_millis(50)).await;
}
```

### 3.2 Future追踪

**追踪 Future 执行**：

```rust
use std::future::Future;
use tracing::Instrument;

/// 1. 使用 Instrument trait
async fn traced_future<F, T>(future: F, span_name: &str) -> T
where
    F: Future<Output = T>,
{
    let span = tracing::info_span!(span_name);
    future.instrument(span).await
}

/// 2. 追踪任意 Future
async fn execute_with_tracing() {
    // 创建 future
    let future = async {
        sleep(Duration::from_millis(100)).await;
        "result"
    };
    
    // 附加追踪
    let result = traced_future(future, "custom_future").await;
    println!("Result: {}", result);
}

/// 3. 并发 Future 追踪
async fn concurrent_traced_operations() {
    use futures::future::join_all;
    
    let futures: Vec<_> = (0..5)
        .map(|i| {
            let span = tracing::info_span!("operation", id = i);
            async move {
                sleep(Duration::from_millis(100)).await;
                i * 2
            }
            .instrument(span)
        })
        .collect();
    
    let results = join_all(futures).await;
    println!("Results: {:?}", results);
}
```

### 3.3 Stream追踪

**追踪异步 Stream**：

```rust
use tokio_stream::{Stream, StreamExt};
use std::pin::Pin;

/// 1. 追踪 Stream 处理
#[instrument(skip(stream))]
async fn process_stream<S>(mut stream: S)
where
    S: Stream<Item = i32> + Unpin,
{
    info!("Starting stream processing");
    
    let mut count = 0;
    while let Some(item) = stream.next().await {
        let span = tracing::debug_span!("stream_item", item = item, count = count);
        let _enter = span.enter();
        
        debug!("Processing item: {}", item);
        count += 1;
    }
    
    info!("Stream processing completed, processed {} items", count);
}

/// 2. 创建被追踪的 Stream
fn create_traced_stream() -> impl Stream<Item = i32> {
    use tokio_stream::iter;
    
    iter(0..10).map(|i| {
        tracing::trace!("Generating item: {}", i);
        i
    })
}

/// 3. 带追踪的 Stream 转换
async fn transform_stream() {
    let stream = create_traced_stream()
        .map(|x| {
            tracing::debug!("Mapping value: {}", x);
            x * 2
        })
        .filter(|x| {
            tracing::debug!("Filtering value: {}", x);
            x % 4 == 0
        });
    
    process_stream(stream).await;
}
```

---

## 4. 同步追踪模式

### 4.1 同步函数追踪

**在同步代码中使用追踪**：

```rust
use tracing::{instrument, info, span, Level};

/// 1. 同步函数追踪
#[instrument]
fn calculate_sum(numbers: &[i32]) -> i32 {
    info!("Calculating sum of {} numbers", numbers.len());
    
    let sum: i32 = numbers.iter().sum();
    
    info!("Sum calculated: {}", sum);
    sum
}

/// 2. 手动 Span 管理
fn manual_sync_span() {
    let span = span!(Level::INFO, "sync_operation");
    let _enter = span.enter();
    
    info!("Executing synchronous operation");
    
    // 业务逻辑
    std::thread::sleep(std::time::Duration::from_millis(100));
    
    // span 在 _enter drop 时自动结束
}

/// 3. 多层嵌套追踪
#[instrument]
fn outer_sync_function() {
    info!("Outer function started");
    
    inner_sync_function();
    
    info!("Outer function completed");
}

#[instrument]
fn inner_sync_function() {
    info!("Inner function executing");
    std::thread::sleep(std::time::Duration::from_millis(50));
}
```

### 4.2 阻塞操作追踪

**追踪阻塞IO操作**：

```rust
use std::fs;
use std::io::Read;

/// 1. 文件IO追踪
#[instrument(skip(path))]
fn read_file_sync(path: &str) -> Result<String, std::io::Error> {
    info!("Reading file: {}", path);
    
    let mut file = fs::File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    
    info!("File read successfully, size: {} bytes", contents.len());
    Ok(contents)
}

/// 2. 网络请求追踪 (阻塞)
#[instrument]
fn http_request_sync(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    info!("Making HTTP request to: {}", url);
    
    // 使用阻塞的 HTTP 客户端
    let response = reqwest::blocking::get(url)?;
    let body = response.text()?;
    
    info!("Request completed, response size: {} bytes", body.len());
    Ok(body)
}
```

---

## 5. 混合编程模式

### 5.1 异步中调用同步

**在异步上下文中安全地调用同步代码**：

```rust
use tokio::task;

/// 1. 使用 spawn_blocking
async fn async_calls_sync() {
    let result = task::spawn_blocking(|| {
        // 同步操作在独立线程池中执行
        calculate_sum(&[1, 2, 3, 4, 5])
    })
    .await
    .expect("Blocking task panicked");
    
    info!("Sync result: {}", result);
}

/// 2. 带追踪的 spawn_blocking
#[instrument]
async fn async_with_blocking_traced() {
    let span = tracing::Span::current();
    
    let result = task::spawn_blocking(move || {
        let _enter = span.enter();
        
        info!("Executing blocking operation");
        
        // CPU 密集型计算
        (0..1000000).sum::<i32>()
    })
    .await
    .expect("Blocking task failed");
    
    info!("Computation result: {}", result);
}

/// 3. 批量阻塞操作
async fn batch_blocking_operations() {
    use futures::future::join_all;
    
    let operations: Vec<_> = (0..5)
        .map(|i| {
            task::spawn_blocking(move || {
                let span = tracing::info_span!("blocking_op", id = i);
                let _enter = span.enter();
                
                // 模拟CPU密集型工作
                std::thread::sleep(std::time::Duration::from_millis(100));
                i * i
            })
        })
        .collect();
    
    let results = join_all(operations).await;
    println!("Results: {:?}", results);
}
```

### 5.2 同步中调用异步

**在同步上下文中调用异步代码**：

```rust
/// 1. 使用 Runtime::block_on
fn sync_calls_async() {
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    let result = rt.block_on(async {
        fetch_user(123).await
    });
    
    println!("Async result: {:?}", result);
}

/// 2. 使用 Handle::block_on
fn sync_with_handle() {
    let handle = tokio::runtime::Handle::current();
    
    let result = handle.block_on(async {
        fetch_user(456).await
    });
    
    println!("Result: {:?}", result);
}

/// 3. 创建临时运行时
fn temporary_runtime() {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(async {
            concurrent_operations().await;
        });
}
```

### 5.3 上下文传播

**确保追踪上下文在同步和异步边界间正确传播**：

```rust
use tracing::Instrument;

/// 1. 跨边界传播 Span
async fn propagate_span_across_boundary() {
    let span = tracing::info_span!("parent_operation");
    
    // 异步操作
    let result = async {
        info!("In async operation");
        
        // 调用同步代码
        let sync_result = tokio::task::spawn_blocking(|| {
            // 同步代码中可以访问 span
            info!("In blocking operation");
            calculate_sum(&[1, 2, 3])
        })
        .await
        .unwrap();
        
        sync_result
    }
    .instrument(span)
    .await;
    
    info!("Final result: {}", result);
}

/// 2. 手动传播上下文
async fn manual_context_propagation() {
    let span = tracing::Span::current();
    
    let result = tokio::task::spawn_blocking(move || {
        // 在闭包中进入 span
        let _guard = span.enter();
        
        info!("Blocking operation with propagated context");
        42
    })
    .await
    .unwrap();
    
    info!("Result: {}", result);
}

/// 3. 使用 Context
async fn use_opentelemetry_context() {
    use opentelemetry::Context;
    
    // 获取当前上下文
    let cx = Context::current();
    
    let result = tokio::task::spawn_blocking(move || {
        // 在阻塞任务中设置上下文
        let _guard = cx.attach();
        
        // 现在可以创建子 span
        let span = tracing::info_span!("blocking_with_context");
        let _enter = span.enter();
        
        info!("Executing with OpenTelemetry context");
        100
    })
    .await
    .unwrap();
    
    info!("Result: {}", result);
}
```

---

## 6. 高级特性

### 6.1 零拷贝传输

**使用 Bytes 实现零拷贝**：

```rust
use bytes::{Bytes, BytesMut, Buf, BufMut};
use std::io::Cursor;

/// 1. 零拷贝 Span 数据
#[instrument(skip(data))]
async fn send_span_data(data: Bytes) {
    info!("Sending {} bytes", data.len());
    
    // data 是引用计数的，可以高效共享
    let clone1 = data.clone(); // 不会复制数据
    let clone2 = data.clone(); // 不会复制数据
    
    // 并发发送
    tokio::join!(
        send_to_backend(clone1),
        send_to_backup(clone2),
    );
}

async fn send_to_backend(data: Bytes) {
    // 模拟网络发送
    info!("Sent to backend: {} bytes", data.len());
}

async fn send_to_backup(data: Bytes) {
    // 模拟备份
    info!("Sent to backup: {} bytes", data.len());
}

/// 2. 高效构建 Payload
fn build_payload_zero_copy() -> Bytes {
    let mut buf = BytesMut::with_capacity(1024);
    
    // 写入数据
    buf.put_slice(b"trace_id:");
    buf.put_u64(123456789);
    buf.put_slice(b",span_id:");
    buf.put_u64(987654321);
    
    // 冻结为不可变 Bytes (零拷贝)
    buf.freeze()
}
```

### 6.2 批处理优化

**实现高效的批处理**：

```rust
use std::sync::Arc;
use tokio::sync::{mpsc, Mutex};
use std::time::Duration;

/// 批处理器
struct BatchProcessor {
    batch_size: usize,
    timeout: Duration,
    buffer: Arc<Mutex<Vec<String>>>,
    tx: mpsc::Sender<Vec<String>>,
}

impl BatchProcessor {
    fn new(batch_size: usize, timeout: Duration) -> (Self, mpsc::Receiver<Vec<String>>) {
        let (tx, rx) = mpsc::channel(100);
        let buffer = Arc::new(Mutex::new(Vec::with_capacity(batch_size)));
        
        let processor = Self {
            batch_size,
            timeout,
            buffer: buffer.clone(),
            tx,
        };
        
        // 启动后台刷新任务
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(timeout).await;
                let mut buf = buffer.lock().await;
                if !buf.is_empty() {
                    let batch = buf.drain(..).collect();
                    drop(buf); // 释放锁
                    
                    // 发送批次
                    if tx.send(batch).await.is_err() {
                        break;
                    }
                }
            }
        });
        
        (processor, rx)
    }
    
    #[instrument(skip(self, item))]
    async fn add(&self, item: String) -> Result<(), String> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(item);
        
        // 如果达到批次大小，立即发送
        if buffer.len() >= self.batch_size {
            let batch = buffer.drain(..).collect();
            drop(buffer); // 释放锁
            
            self.tx.send(batch).await
                .map_err(|_| "Failed to send batch".to_string())?;
        }
        
        Ok(())
    }
}

/// 使用批处理器
async fn use_batch_processor() {
    let (processor, mut rx) = BatchProcessor::new(100, Duration::from_secs(5));
    
    // 生产者任务
    tokio::spawn(async move {
        for i in 0..1000 {
            processor.add(format!("span_{}", i)).await.ok();
        }
    });
    
    // 消费者任务
    while let Some(batch) = rx.recv().await {
        info!("Received batch of {} items", batch.len());
        // 处理批次
        export_batch(batch).await;
    }
}

#[instrument(skip(batch))]
async fn export_batch(batch: Vec<String>) {
    info!("Exporting batch of {} spans", batch.len());
    sleep(Duration::from_millis(100)).await;
}
```

### 6.3 背压控制

**实现背压控制机制**：

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

/// 带背压控制的处理器
struct BackpressureProcessor {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
}

impl BackpressureProcessor {
    fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
        }
    }
    
    #[instrument(skip(self, data))]
    async fn process(&self, data: String) -> Result<(), Box<dyn std::error::Error>> {
        // 获取许可 (如果没有可用许可，会等待)
        let permit = self.semaphore.acquire().await?;
        
        info!("Processing data (available permits: {})", 
              self.max_concurrent - self.semaphore.available_permits());
        
        // 模拟处理
        sleep(Duration::from_millis(100)).await;
        
        // permit drop 时自动释放
        drop(permit);
        
        Ok(())
    }
}

/// 使用背压控制
async fn use_backpressure() {
    let processor = Arc::new(BackpressureProcessor::new(10));
    
    let mut tasks = vec![];
    
    for i in 0..100 {
        let processor = processor.clone();
        let task = tokio::spawn(async move {
            processor.process(format!("data_{}", i)).await
        });
        tasks.push(task);
    }
    
    // 等待所有任务完成
    for task in tasks {
        task.await.ok();
    }
}
```

---

## 7. 性能优化

### 7.1 内存优化

**减少内存分配和复制**：

```rust
use std::sync::Arc;
use parking_lot::RwLock;

/// 1. 使用对象池
use once_cell::sync::Lazy;
use crossbeam::queue::ArrayQueue;

static SPAN_POOL: Lazy<ArrayQueue<Vec<u8>>> = Lazy::new(|| {
    ArrayQueue::new(1000)
});

fn get_buffer() -> Vec<u8> {
    SPAN_POOL.pop().unwrap_or_else(|| Vec::with_capacity(1024))
}

fn return_buffer(mut buffer: Vec<u8>) {
    buffer.clear();
    SPAN_POOL.push(buffer).ok();
}

/// 2. 使用 Arc 共享数据
#[derive(Clone)]
struct SharedSpanData {
    data: Arc<RwLock<Vec<u8>>>,
}

impl SharedSpanData {
    fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    fn read(&self) -> Vec<u8> {
        self.data.read().clone()
    }
    
    fn write(&self, data: Vec<u8>) {
        *self.data.write() = data;
    }
}

/// 3. 预分配容量
fn preallocate_buffers() -> Vec<Vec<u8>> {
    let mut buffers = Vec::with_capacity(100);
    for _ in 0..100 {
        buffers.push(Vec::with_capacity(1024));
    }
    buffers
}
```

### 7.2 CPU优化

**减少CPU开销**：

```rust
use std::hint::black_box;

/// 1. 避免不必要的序列化
#[instrument(skip(data))]
async fn optimize_serialization(data: &[u8]) {
    // 只在需要时序列化
    if tracing::level_enabled!(tracing::Level::DEBUG) {
        let json = serde_json::to_string(data).unwrap();
        debug!("Data: {}", json);
    }
    
    // 业务逻辑
    process_data(data).await;
}

async fn process_data(data: &[u8]) {
    // 实际处理
    black_box(data);
}

/// 2. 使用并行处理
use rayon::prelude::*;

fn parallel_processing(items: Vec<i32>) -> Vec<i32> {
    items
        .par_iter()
        .map(|&x| {
            // CPU密集型计算
            x * x
        })
        .collect()
}

/// 3. 缓存计算结果
use std::collections::HashMap;

struct ComputationCache {
    cache: Arc<RwLock<HashMap<String, i32>>>,
}

impl ComputationCache {
    fn new() -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn get_or_compute(&self, key: String, compute: impl FnOnce() -> i32) -> i32 {
        // 先尝试读
        {
            let cache = self.cache.read();
            if let Some(&value) = cache.get(&key) {
                return value;
            }
        }
        
        // 计算新值
        let value = compute();
        
        // 写入缓存
        {
            let mut cache = self.cache.write();
            cache.insert(key, value);
        }
        
        value
    }
}
```

### 7.3 网络优化

**优化网络传输**：

```rust
use tokio::io::{AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;
use flate2::write::GzEncoder;
use flate2::Compression;

/// 1. 使用连接池
use deadpool::managed::{Manager, Pool, RecycleResult};
use async_trait::async_trait;

struct TcpConnectionManager {
    addr: String,
}

#[async_trait]
impl Manager for TcpConnectionManager {
    type Type = TcpStream;
    type Error = std::io::Error;

    async fn create(&self) -> Result<TcpStream, Self::Error> {
        TcpStream::connect(&self.addr).await
    }

    async fn recycle(&self, conn: &mut TcpStream) -> RecycleResult<Self::Error> {
        // 检查连接是否还有效
        Ok(())
    }
}

/// 2. 启用压缩
#[instrument(skip(data))]
async fn send_compressed(data: Vec<u8>) -> Result<(), Box<dyn std::error::Error>> {
    use std::io::Write;
    
    // 压缩数据
    let mut encoder = GzEncoder::new(Vec::new(), Compression::fast());
    encoder.write_all(&data)?;
    let compressed = encoder.finish()?;
    
    info!("Compressed {} bytes to {} bytes", data.len(), compressed.len());
    
    // 发送压缩数据
    // ...
    
    Ok(())
}

/// 3. 批量发送
struct BatchSender {
    stream: BufWriter<TcpStream>,
}

impl BatchSender {
    async fn new(addr: &str) -> Result<Self, std::io::Error> {
        let stream = TcpStream::connect(addr).await?;
        let buffered = BufWriter::new(stream);
        Ok(Self { stream: buffered })
    }
    
    async fn send_batch(&mut self, items: &[Vec<u8>]) -> Result<(), std::io::Error> {
        for item in items {
            self.stream.write_all(item).await?;
        }
        // 刷新缓冲区
        self.stream.flush().await?;
        Ok(())
    }
}
```

---

## 8. Rust 1.90 OTLP 高级模式

### 8.1 零成本抽象的遥测收集

**使用 Rust 1.90 特性实现高性能遥测收集**：

```rust
use std::sync::Arc;
use parking_lot::RwLock;
use dashmap::DashMap;
use opentelemetry::trace::{SpanId, TraceId};

// 辅助类型定义
#[derive(Debug, Clone)]
pub struct SpanData {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub name: String,
    pub start_time: std::time::SystemTime,
    pub end_time: std::time::SystemTime,
}

impl Default for SpanData {
    fn default() -> Self {
        Self {
            trace_id: TraceId::from_u128(0),
            span_id: SpanId::from_u64(0),
            name: String::new(),
            start_time: std::time::SystemTime::now(),
            end_time: std::time::SystemTime::now(),
        }
    }
}

/// 零成本抽象的 Span 收集器
/// 
/// Rust 1.90 优化:
/// - 使用 DashMap 实现无锁并发
/// - parking_lot 提供更快的锁实现
/// - 零拷贝的数据共享
pub struct SpanCollector {
    // 使用 DashMap 实现无锁并发访问
    active_spans: DashMap<SpanId, Arc<RwLock<SpanData>>>,
    // 使用 parking_lot 提供更快的锁实现
    completed_spans: Arc<RwLock<Vec<SpanData>>>,
    // Rust 1.90: 使用原子计数器进行统计
    total_spans: Arc<std::sync::atomic::AtomicU64>,
}

impl SpanCollector {
    pub fn new() -> Self {
        Self {
            active_spans: DashMap::new(),
            completed_spans: Arc::new(RwLock::new(Vec::with_capacity(1024))),
            total_spans: Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }
    
    /// 零拷贝添加 Span
    /// 
    /// Rust 1.90 优化:
    /// - DashMap 提供无锁并发插入
    /// - Arc<RwLock<_>> 允许多读者单写者模式
    pub fn add_span(&self, span_id: SpanId, span: SpanData) {
        self.active_spans.insert(span_id, Arc::new(RwLock::new(span)));
        self.total_spans.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    
    /// 高效完成 Span
    /// 
    /// Rust 1.90: 原子操作和无锁移除
    pub fn complete_span(&self, span_id: SpanId) {
        if let Some((_, span_arc)) = self.active_spans.remove(&span_id) {
            let span = span_arc.read().clone();
            self.completed_spans.write().push(span);
        }
    }
    
    /// 批量导出（零拷贝）
    /// 
    /// Rust 1.90: 使用 drain 实现零拷贝移动
    pub fn export_batch(&self, batch_size: usize) -> Vec<SpanData> {
        let mut completed = self.completed_spans.write();
        let export_count = completed.len().min(batch_size);
        completed.drain(..export_count).collect()
    }
    
    /// 获取统计信息
    pub fn stats(&self) -> CollectorStats {
        CollectorStats {
            active_spans: self.active_spans.len(),
            completed_spans: self.completed_spans.read().len(),
            total_spans: self.total_spans.load(std::sync::atomic::Ordering::Relaxed),
        }
    }
}

/// 收集器统计信息
#[derive(Debug, Clone)]
pub struct CollectorStats {
    pub active_spans: usize,
    pub completed_spans: usize,
    pub total_spans: u64,
}

/// 使用泛型实现类型安全的遥测数据处理
pub trait TelemetryData: Send + Sync + 'static {
    type Output;
    
    async fn process(&self) -> Result<Self::Output, ProcessError>;
}

/// 为不同的遥测类型实现 trait
impl TelemetryData for SpanData {
    type Output = ProcessedSpan;
    
    async fn process(&self) -> Result<Self::Output, ProcessError> {
        // Span 特定处理逻辑
        Ok(ProcessedSpan::from(self))
    }
}

impl TelemetryData for MetricData {
    type Output = ProcessedMetric;
    
    async fn process(&self) -> Result<Self::Output, ProcessError> {
        // Metric 特定处理逻辑
        Ok(ProcessedMetric::from(self))
    }
}

/// 泛型批处理器
pub struct BatchProcessor<T: TelemetryData> {
    buffer: Arc<RwLock<Vec<T>>>,
    batch_size: usize,
}

impl<T: TelemetryData> BatchProcessor<T> {
    pub fn new(batch_size: usize) -> Self {
        Self {
            buffer: Arc::new(RwLock::new(Vec::with_capacity(batch_size))),
            batch_size,
        }
    }
    
    /// 添加数据到批处理缓冲区
    pub async fn add(&self, data: T) -> Option<Vec<T>> {
        let mut buffer = self.buffer.write();
        buffer.push(data);
        
        if buffer.len() >= self.batch_size {
            Some(buffer.drain(..).collect())
        } else {
            None
        }
    }
    
    /// 异步批处理
    pub async fn process_batch(&self, batch: Vec<T>) -> Result<Vec<T::Output>, ProcessError> {
        let mut results = Vec::with_capacity(batch.len());
        
        for item in batch {
            results.push(item.process().await?);
        }
        
        Ok(results)
    }
}
```

### 8.2 异步上下文传播优化

**Rust 1.90 的上下文传播最佳实践**：

```rust
use opentelemetry::Context;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context as TaskContext, Poll};

/// 自定义 Future wrapper 实现自动上下文传播
pub struct WithContext<F> {
    future: F,
    context: Context,
}

impl<F> Future for WithContext<F>
where
    F: Future + Unpin,
{
    type Output = F::Output;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        // 在 poll 时设置上下文
        let _guard = self.context.clone().attach();
        Pin::new(&mut self.future).poll(cx)
    }
}

/// 辅助函数：为任何 Future 添加上下文
pub fn with_context<F>(future: F, context: Context) -> WithContext<F> {
    WithContext { future, context }
}

/// 异步函数的上下文传播
pub async fn operation_with_context() {
    let context = Context::current();
    
    // 自动传播上下文到子任务
    let handle = tokio::spawn(async move {
        let _guard = context.attach();
        
        // 在子任务中创建 span
        let tracer = global::tracer("child-task");
        let span = tracer.start("child-operation");
        let _span_guard = span.make_current();
        
        // 执行操作
        sleep(Duration::from_millis(100)).await;
    });
    
    handle.await.unwrap();
}

/// 使用 TaskLocal 实现线程安全的上下文传播
use tokio::task_local;

task_local! {
    static OTEL_CONTEXT: Context;
}

pub async fn with_task_local_context<F, R>(context: Context, future: F) -> R
where
    F: Future<Output = R>,
{
    OTEL_CONTEXT.scope(context, future).await
}
```

### 8.3 内存池优化

**使用对象池减少内存分配**：

```rust
use crossbeam::queue::ArrayQueue;
use std::sync::Arc;

/// Span 对象池
pub struct SpanPool {
    pool: Arc<ArrayQueue<Box<SpanData>>>,
    max_size: usize,
}

impl SpanPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: Arc::new(ArrayQueue::new(max_size)),
            max_size,
        }
    }
    
    /// 从池中获取或创建新的 Span
    pub fn acquire(&self) -> Box<SpanData> {
        self.pool
            .pop()
            .unwrap_or_else(|| Box::new(SpanData::default()))
    }
    
    /// 归还 Span 到池中
    pub fn release(&self, mut span: Box<SpanData>) {
        // 重置 span 数据
        *span = SpanData::default();
        
        // 尝试放回池中
        if self.pool.push(span).is_err() {
            // 池已满，丢弃对象
        }
    }
}

/// RAII 守卫自动归还对象
pub struct PooledSpan<'a> {
    span: Option<Box<SpanData>>,
    pool: &'a SpanPool,
}

impl<'a> PooledSpan<'a> {
    pub fn new(pool: &'a SpanPool) -> Self {
        Self {
            span: Some(pool.acquire()),
            pool,
        }
    }
    
    pub fn get_mut(&mut self) -> &mut SpanData {
        self.span.as_mut().unwrap()
    }
}

impl<'a> Drop for PooledSpan<'a> {
    fn drop(&mut self) {
        if let Some(span) = self.span.take() {
            self.pool.release(span);
        }
    }
}

/// 使用示例
async fn use_span_pool() {
    let pool = Arc::new(SpanPool::new(1000));
    
    // 使用池化的 span
    {
        let mut pooled_span = PooledSpan::new(&pool);
        let span = pooled_span.get_mut();
        
        span.name = "operation".to_string();
        span.trace_id = TraceId::new();
        
        // span 在作用域结束时自动归还到池
    }
}
```

### 8.4 异步批处理优化

**高性能异步批处理实现**：

```rust
use tokio::sync::mpsc;
use tokio::time::{interval, Duration};

/// 智能批处理器
pub struct SmartBatcher<T> {
    sender: mpsc::Sender<T>,
    config: BatchConfig,
}

pub struct BatchConfig {
    max_batch_size: usize,
    max_wait_time: Duration,
    max_concurrent_batches: usize,
}

impl<T: Send + 'static> SmartBatcher<T> {
    pub fn new(config: BatchConfig) -> (Self, BatchReceiver<T>) {
        let (tx, rx) = mpsc::channel(config.max_batch_size * 2);
        
        let batcher = Self {
            sender: tx,
            config: config.clone(),
        };
        
        let receiver = BatchReceiver::new(rx, config);
        
        (batcher, receiver)
    }
    
    /// 添加项目到批处理器
    pub async fn add(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.sender.send(item).await
    }
}

pub struct BatchReceiver<T> {
    receiver: mpsc::Receiver<T>,
    config: BatchConfig,
}

impl<T: Send + 'static> BatchReceiver<T> {
    fn new(receiver: mpsc::Receiver<T>, config: BatchConfig) -> Self {
        Self { receiver, config }
    }
    
    /// 启动批处理循环
    pub async fn run<F, Fut>(mut self, processor: F)
    where
        F: Fn(Vec<T>) -> Fut + Send + 'static,
        Fut: Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send,
    {
        let mut batch = Vec::with_capacity(self.config.max_batch_size);
        let mut ticker = interval(self.config.max_wait_time);
        
        loop {
            tokio::select! {
                // 接收新项目
                Some(item) = self.receiver.recv() => {
                    batch.push(item);
                    
                    // 批次已满，立即处理
                    if batch.len() >= self.config.max_batch_size {
                        let export_batch = std::mem::replace(
                            &mut batch,
                            Vec::with_capacity(self.config.max_batch_size)
                        );
                        
                        if let Err(e) = processor(export_batch).await {
                            tracing::error!("Failed to process batch: {}", e);
                        }
                    }
                }
                
                // 定时器触发，处理积累的项目
                _ = ticker.tick() => {
                    if !batch.is_empty() {
                        let export_batch = std::mem::replace(
                            &mut batch,
                            Vec::with_capacity(self.config.max_batch_size)
                        );
                        
                        if let Err(e) = processor(export_batch).await {
                            tracing::error!("Failed to process batch: {}", e);
                        }
                    }
                }
            }
        }
    }
}

/// 使用示例
async fn use_smart_batcher() {
    let config = BatchConfig {
        max_batch_size: 100,
        max_wait_time: Duration::from_secs(5),
        max_concurrent_batches: 4,
    };
    
    let (batcher, receiver) = SmartBatcher::new(config);
    
    // 启动批处理器
    tokio::spawn(async move {
        receiver.run(|batch| async move {
            // 处理批次
            export_spans_to_backend(batch).await?;
            Ok(())
        }).await;
    });
    
    // 添加 spans
    for i in 0..1000 {
        batcher.add(create_span(i)).await.unwrap();
    }
}
```

### 8.5 流式处理优化

**Rust 1.90 的 Stream 处理**：

```rust
use tokio_stream::{Stream, StreamExt};
use std::pin::Pin;

/// 流式 Span 处理器
pub struct StreamingSpanProcessor {
    batch_size: usize,
}

impl StreamingSpanProcessor {
    pub fn new(batch_size: usize) -> Self {
        Self { batch_size }
    }
    
    /// 处理 Span 流
    pub async fn process_stream<S>(&self, mut stream: S) -> Result<(), ProcessError>
    where
        S: Stream<Item = SpanData> + Unpin,
    {
        use tokio_stream::StreamExt;
        
        // 分批处理流
        let mut batch_stream = stream.chunks_timeout(
            self.batch_size,
            Duration::from_secs(5)
        );
        
        while let Some(batch) = batch_stream.next().await {
            // 并发处理批次
            self.export_batch(batch).await?;
        }
        
        Ok(())
    }
    
    /// 创建过滤和转换的流水线
    pub fn create_pipeline<S>(
        &self,
        input: S,
    ) -> impl Stream<Item = ProcessedSpan>
    where
        S: Stream<Item = SpanData> + Send + 'static,
    {
        input
            // 过滤：只处理采样的 span
            .filter(|span| {
                let should_sample = span.trace_flags.sampled();
                async move { should_sample }
            })
            // 转换：处理 span
            .filter_map(|span| async move {
                match process_span(span).await {
                    Ok(processed) => Some(processed),
                    Err(e) => {
                        tracing::error!("Failed to process span: {}", e);
                        None
                    }
                }
            })
            // 限流：防止过载
            .throttle(Duration::from_micros(100))
    }
}

/// 异步 Span 迭代器
pub struct SpanIterator {
    buffer: VecDeque<SpanData>,
    source: Box<dyn Stream<Item = SpanData> + Send + Unpin>,
}

impl SpanIterator {
    pub fn new<S>(stream: S) -> Self
    where
        S: Stream<Item = SpanData> + Send + Unpin + 'static,
    {
        Self {
            buffer: VecDeque::new(),
            source: Box::new(stream),
        }
    }
    
    /// 异步获取下一个 span
    pub async fn next(&mut self) -> Option<SpanData> {
        if let Some(span) = self.buffer.pop_front() {
            return Some(span);
        }
        
        self.source.next().await
    }
}
```

---

## 9. 错误处理

### 9.1 异步错误处理

**异步代码中的错误处理**：

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TelemetryError {
    #[error("Connection failed: {0}")]
    ConnectionError(String),
    
    #[error("Serialization failed: {0}")]
    SerializationError(#[from] serde_json::Error),
    
    #[error("Timeout occurred")]
    TimeoutError,
    
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

/// 1. 使用 Result
#[instrument]
async fn async_with_result() -> Result<String, TelemetryError> {
    // 可能失败的操作
    let data = fetch_data_fallible().await?;
    
    // 转换错误
    let json = serde_json::to_string(&data)?;
    
    Ok(json)
}

async fn fetch_data_fallible() -> Result<Vec<u8>, TelemetryError> {
    // 模拟可能失败的操作
    Ok(vec![1, 2, 3])
}

/// 2. 使用 anyhow
use anyhow::{Context, Result};

#[instrument]
async fn async_with_anyhow() -> Result<String> {
    let data = fetch_user(123)
        .await
        .context("Failed to fetch user")?;
    
    Ok(data)
}

/// 3. 错误恢复
#[instrument]
async fn with_fallback() -> String {
    match fetch_user(123).await {
        Ok(user) => user,
        Err(e) => {
            warn!("Failed to fetch user: {}, using default", e);
            "DefaultUser".to_string()
        }
    }
}

/// 4. 超时处理
#[instrument]
async fn with_timeout() -> Result<String> {
    use tokio::time::timeout;
    
    timeout(Duration::from_secs(5), fetch_user(123))
        .await
        .context("Operation timed out")?
        .context("Fetch failed")
}
```

### 9.2 同步错误处理

**同步代码中的错误处理**：

```rust
/// 1. Result 传播
#[instrument]
fn sync_with_result() -> Result<i32, TelemetryError> {
    let sum = calculate_sum(&[1, 2, 3]);
    
    if sum < 0 {
        return Err(TelemetryError::ConnectionError("Invalid sum".to_string()));
    }
    
    Ok(sum)
}

/// 2. 错误转换
#[instrument]
fn convert_errors() -> Result<String, TelemetryError> {
    let file_content = read_file_sync("data.txt")
        .map_err(|e| TelemetryError::IoError(e))?;
    
    Ok(file_content)
}
```

### 9.3 错误追踪

**记录和追踪错误**：

```rust
use tracing::error;

/// 1. 记录错误到 Span
#[instrument]
async fn operation_with_error() -> Result<(), TelemetryError> {
    match risky_operation().await {
        Ok(result) => {
            info!("Operation succeeded");
            Ok(())
        }
        Err(e) => {
            // 记录错误
            error!("Operation failed: {}", e);
            
            // 设置 span 状态
            let span = tracing::Span::current();
            span.record("error", &true);
            span.record("error.message", &&*e.to_string());
            
            Err(e)
        }
    }
}

async fn risky_operation() -> Result<String, TelemetryError> {
    // 可能失败的操作
    Err(TelemetryError::TimeoutError)
}

/// 2. 使用 OpenTelemetry 记录错误
async fn record_exception() {
    use opentelemetry::{global, trace::Status};
    
    let tracer = global::tracer("error-tracer");
    let mut span = tracer.span_builder("operation").start(&tracer);
    
    match risky_operation().await {
        Ok(_) => {}
        Err(e) => {
            // 记录异常
            span.record_error(&e);
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    span.end();
}
```

---

## 10. 测试和基准测试

### 10.1 异步测试

**测试异步代码**：

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    /// 1. 基础异步测试
    #[tokio::test]
    async fn test_fetch_user() {
        let result = fetch_user(123).await;
        assert!(result.is_ok());
    }
    
    /// 2. 带追踪的测试
    #[tokio::test]
    async fn test_with_tracing() {
        // 初始化测试追踪
        let subscriber = tracing_subscriber::fmt()
            .with_test_writer()
            .finish();
        
        tracing::subscriber::set_global_default(subscriber).ok();
        
        let result = fetch_premium_user(456).await;
        assert!(result.is_ok());
    }
    
    /// 3. 并发测试
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn test_concurrent() {
        let tasks: Vec<_> = (0..100)
            .map(|i| tokio::spawn(fetch_user(i)))
            .collect();
        
        for task in tasks {
            assert!(task.await.is_ok());
        }
    }
    
    /// 4. 超时测试
    #[tokio::test]
    async fn test_timeout() {
        use tokio::time::timeout;
        
        let result = timeout(Duration::from_secs(1), fetch_user(123)).await;
        assert!(result.is_ok());
    }
    
    /// 5. Mock 测试
    use mockall::mock;
    
    mock! {
        pub UserService {
            async fn fetch_user(&self, id: u64) -> Result<String, Box<dyn std::error::Error>>;
        }
    }
    
    #[tokio::test]
    async fn test_with_mock() {
        let mut mock = MockUserService::new();
        mock.expect_fetch_user()
            .returning(|_| Ok("MockUser".to_string()));
        
        let result = mock.fetch_user(123).await;
        assert_eq!(result.unwrap(), "MockUser");
    }
}
```

### 10.2 性能基准测试

**使用 Criterion 进行基准测试**：

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

/// 1. 简单基准测试
fn benchmark_calculate_sum(c: &mut Criterion) {
    let data = vec![1, 2, 3, 4, 5];
    
    c.bench_function("calculate_sum", |b| {
        b.iter(|| calculate_sum(black_box(&data)))
    });
}

/// 2. 参数化基准测试
fn benchmark_with_params(c: &mut Criterion) {
    let mut group = c.benchmark_group("fetch_user");
    
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                // 基准测试代码
                black_box(size);
            });
        });
    }
    
    group.finish();
}

/// 3. 异步基准测试
fn benchmark_async(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    c.bench_function("async_fetch", |b| {
        b.to_async(&rt).iter(|| async {
            fetch_user(black_box(123)).await
        });
    });
}

criterion_group!(benches, benchmark_calculate_sum, benchmark_with_params, benchmark_async);
criterion_main!(benches);
```

---

## 11. 生产环境最佳实践

```text
✅ 初始化
  □ 应用启动时初始化一次 TracerProvider
  □ 使用环境变量配置端点和采样率
  □ 设置合适的 Resource 属性
  □ 配置优雅关闭处理

✅ 采样
  □ 生产环境使用适当的采样率 (1-10%)
  □ 总是采样错误和慢请求
  □ 使用 ParentBased 采样保持一致性

✅ 性能
  □ 使用批处理导出器
  □ 启用压缩
  □ 使用对象池减少分配
  □ 避免在热路径中创建过多 span

✅ 错误处理
  □ 记录所有错误到 span
  □ 设置正确的 span 状态
  □ 使用结构化错误类型

✅ 异步
  □ 使用 Tokio 作为运行时
  □ 正确传播追踪上下文
  □ 在 spawn_blocking 中处理同步代码
  □ 实现背压控制

✅ 监控
  □ 监控 SDK 指标 (队列大小、导出失败等)
  □ 设置告警规则
  □ 定期检查追踪数据质量

✅ 安全
  □ 不要记录敏感信息 (密码、令牌等)
  □ 使用 TLS 连接
  □ 验证端点证书
```

---

## 12. 完整示例

### 12.1 Web服务器示例 (Axum + OTLP)

```rust
use axum::{
    extract::Path,
    response::Json,
    routing::get,
    Router,
};
use serde::{Deserialize, Serialize};
use tower_http::trace::TraceLayer;

#[derive(Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    setup_telemetry().await?;
    
    // 创建路由
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .layer(TraceLayer::new_for_http());
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await?;
    info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument(skip(_path))]
async fn get_user(Path(user_id): Path<u64>) -> Json<User> {
    info!("Fetching user with id: {}", user_id);
    
    // 模拟数据库查询
    let user = fetch_user_from_db(user_id).await;
    
    Json(user)
}

#[instrument]
async fn fetch_user_from_db(user_id: u64) -> User {
    // 模拟数据库延迟
    sleep(Duration::from_millis(50)).await;
    
    User {
        id: user_id,
        name: format!("User_{}", user_id),
    }
}
```

### 12.2 微服务示例 (gRPC + OTLP)

```rust
use tonic::{transport::Server, Request, Response, Status};

pub mod proto {
    tonic::include_proto!("users");
}

use proto::user_service_server::{UserService, UserServiceServer};
use proto::{GetUserRequest, GetUserResponse};

#[derive(Default)]
pub struct MyUserService;

#[tonic::async_trait]
impl UserService for MyUserService {
    #[instrument(skip(self, request))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<GetUserResponse>, Status> {
        let user_id = request.into_inner().user_id;
        
        info!("gRPC request for user_id: {}", user_id);
        
        // 业务逻辑
        let user = fetch_user_from_db(user_id as u64).await;
        
        let response = GetUserResponse {
            user_id,
            name: user.name,
        };
        
        Ok(Response::new(response))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    setup_telemetry().await?;
    
    let addr = "127.0.0.1:50051".parse()?;
    let service = MyUserService::default();
    
    info!("gRPC server listening on {}", addr);
    
    Server::builder()
        .add_service(UserServiceServer::new(service))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

---

## 13. Rust 1.90 特定优化总结

### 13.1 编译器优化

**Rust 1.90 编译优化配置**：

```toml
# Cargo.toml - 生产环境优化配置
[profile.release]
opt-level = 3                    # 最高优化级别
lto = "fat"                      # 完整链接时优化
codegen-units = 1                # 单一代码生成单元
strip = "symbols"                # 移除符号信息
panic = "abort"                  # Panic 时立即终止

# Rust 1.90 特定优化
[profile.release.package."*"]
opt-level = 3

# Rust 1.90: 更激进的内联优化
[profile.release.build-override]
opt-level = 3
codegen-units = 1

# 开发环境优化 - 更快的编译速度
[profile.dev]
opt-level = 0                    # 不优化（更快编译）
debug = true                      # 包含调试信息
debug-assertions = true           # 启用断言
overflow-checks = true            # 整数溢出检查
incremental = true                # 增量编译

# Rust 1.90: 开发环境依赖优化
[profile.dev.package."*"]
opt-level = 2                     # 优化依赖库
debug = false                     # 依赖库不含调试信息
```

**Rust 1.90 Async/Await 编译器改进**：

```text
✅ 改进的 Future 大小优化
   - 减少了 async fn 生成的 Future 大小
   - 更智能的栈布局优化
   - 更少的内存碎片

✅ 更好的内联优化
   - async fn in traits 可以被内联
   - 改进的跨 crate 内联
   - 更激进的 Future 组合器内联

✅ 改进的生命周期推导
   - 更少的生命周期标注需求
   - 更智能的借用检查
   - 更好的错误消息

✅ 零成本抽象验证
   - 编译器保证无额外开销
   - 与手写 Future 性能相同
   - 优化后的机器码质量提升
```

**Rust 1.90 编译器标志优化**：

```bash
# 最大性能优化编译
RUSTFLAGS="-C target-cpu=native -C opt-level=3 -C lto=fat -C embed-bitcode=yes" \
    cargo build --release

# 针对特定 CPU 架构优化
RUSTFLAGS="-C target-cpu=skylake -C target-feature=+avx2" \
    cargo build --release

# Rust 1.90: 启用所有安全优化
RUSTFLAGS="-C overflow-checks=yes -C panic=abort -Z share-generics=yes" \
    cargo +nightly build --release
```

### 13.2 运行时性能调优

**Tokio 运行时调优**：

```rust
use tokio::runtime::Builder;
use std::time::Duration;

/// 为 OTLP 优化的 Tokio 运行时配置
pub fn create_optimized_runtime() -> tokio::runtime::Runtime {
    Builder::new_multi_thread()
        // 工作线程数 = CPU 核心数
        .worker_threads(num_cpus::get())
        // 阻塞线程池大小
        .max_blocking_threads(512)
        // 线程名称前缀
        .thread_name("otlp-worker")
        // 线程栈大小 (3MB)
        .thread_stack_size(3 * 1024 * 1024)
        // 线程保活时间
        .thread_keep_alive(Duration::from_secs(60))
        // 全局队列检查间隔 (Rust 1.90 优化)
        .global_queue_interval(31)
        // 事件检查间隔
        .event_interval(61)
        // 启用所有功能
        .enable_all()
        // 启用 IO 驱动
        .enable_io()
        // 启用时间驱动
        .enable_time()
        .build()
        .expect("Failed to create Tokio runtime")
}

/// 自定义工作线程数
pub fn create_custom_runtime(worker_threads: usize) -> tokio::runtime::Runtime {
    Builder::new_multi_thread()
        .worker_threads(worker_threads)
        .enable_all()
        .build()
        .expect("Failed to create custom runtime")
}
```

### 13.3 内存优化技巧

**减少内存分配和提升性能**：

```rust
use std::sync::Arc;
use bytes::Bytes;

/// 使用 Bytes 实现零拷贝
pub struct ZeroCopySpan {
    /// 使用 Bytes 而不是 Vec<u8> 实现零拷贝共享
    data: Bytes,
    /// 使用 Arc 共享不可变数据
    metadata: Arc<SpanMetadata>,
}

impl Clone for ZeroCopySpan {
    fn clone(&self) -> Self {
        // 零拷贝克隆 - 只增加引用计数
        Self {
            data: self.data.clone(),      // 浅拷贝
            metadata: Arc::clone(&self.metadata),  // 引用计数增加
        }
    }
}

/// 预分配容量避免重新分配
pub struct OptimizedBuffer {
    buffer: Vec<u8>,
}

impl OptimizedBuffer {
    pub fn new() -> Self {
        // 预分配合理的初始容量
        Self {
            buffer: Vec::with_capacity(4096),
        }
    }
    
    pub fn add_data(&mut self, data: &[u8]) {
        // 检查容量，必要时扩展
        if self.buffer.len() + data.len() > self.buffer.capacity() {
            self.buffer.reserve(data.len());
        }
        self.buffer.extend_from_slice(data);
    }
}
```

### 13.4 异步性能最佳实践

**Rust 1.90 异步性能优化清单**：

```text
✅ 使用原生 async fn in traits (无需 async-trait 宏)
✅ 利用 impl Trait in associated types 简化代码
✅ 使用 tokio::spawn 而不是 std::thread::spawn
✅ 对 CPU 密集型任务使用 spawn_blocking
✅ 使用 select! 实现超时和取消
✅ 使用 join! 并发执行独立操作
✅ 避免在 async 函数中持有锁
✅ 使用 parking_lot 替代 std::sync::Mutex
✅ 使用 DashMap 实现无锁并发访问
✅ 使用对象池减少内存分配
✅ 批处理减少系统调用
✅ 使用 Bytes 实现零拷贝
✅ 合理设置缓冲区大小
✅ 启用压缩减少网络传输
✅ 使用连接池复用连接
```

---

## 14. 参考资源

### 官方文档 (2025年10月最新)

**OpenTelemetry Rust (v0.31.0)**:

- [OpenTelemetry Rust GitHub](https://github.com/open-telemetry/opentelemetry-rust)
- [opentelemetry crate](https://docs.rs/opentelemetry/0.31.0)
- [opentelemetry_sdk crate](https://docs.rs/opentelemetry_sdk/0.31.0)
- [opentelemetry-otlp crate](https://docs.rs/opentelemetry-otlp/0.31.0)

**Tokio生态系统 (v1.47+)**:

- [Tokio Documentation](https://tokio.rs/)
- [Tokio API Docs](https://docs.rs/tokio/1.47.1)
- [tokio-stream](https://docs.rs/tokio-stream/0.1.17)
- [tokio-util](https://docs.rs/tokio-util/0.7.16)

**Tracing生态系统**:

- [Tracing Documentation](https://docs.rs/tracing/)
- [tracing-subscriber](https://docs.rs/tracing-subscriber/0.3.20)
- [tracing-opentelemetry](https://docs.rs/tracing-opentelemetry/0.31)

### OpenTelemetry规范

- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Context Propagation](https://opentelemetry.io/docs/specs/otel/context/)

### 示例代码和教程

**官方示例**:

- [OpenTelemetry Rust Examples](https://github.com/open-telemetry/opentelemetry-rust/tree/main/examples)
- [Tokio Examples](https://github.com/tokio-rs/tokio/tree/master/examples)
- [Tracing Examples](https://github.com/tokio-rs/tracing/tree/master/examples)

**社区资源**:

- [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
- [Async Rust Book](https://rust-lang.github.io/async-book/)
- [OpenTelemetry Rust Guide](https://opentelemetry.io/docs/instrumentation/rust/)

### Rust 1.90 特性文档

**异步编程特性 (Rust 1.75+ 稳定，1.90 优化)**:

- [Async Fn in Traits](https://blog.rust-lang.org/2023/12/21/async-fn-rpit-in-traits.html)
- [impl Trait in Associated Types](https://rust-lang.github.io/rfcs/2515-type_alias_impl_trait.html)
- [Rust 1.81 Release](https://blog.rust-lang.org/2024/09/05/Rust-1.81.html)
- [Rust 1.90 安全增强](https://blog.rust-lang.org/)

**语言特性指南**:

- [Rust Reference - Async](https://doc.rust-lang.org/reference/expressions/await-expr.html)
- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Pin and Unpin](https://doc.rust-lang.org/std/pin/)

### 性能优化资源

**Rust性能优化**:

- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Tokio Performance Guide](https://tokio.rs/tokio/topics/performance)
- [Bytes Documentation](https://docs.rs/bytes/)
- [零拷贝技术](https://docs.rs/bytes/latest/bytes/#zero-copy)

**并发编程**:

- [Crossbeam Documentation](https://docs.rs/crossbeam/)
- [Rayon Documentation](https://docs.rs/rayon/)
- [DashMap Documentation](https://docs.rs/dashmap/)
- [parking_lot Documentation](https://docs.rs/parking_lot/)

### 依赖库文档 (2025年10月最新版本)

**gRPC和HTTP**:

- [Tonic 0.14.2](https://docs.rs/tonic/0.14.2)
- [Reqwest 0.12.23](https://docs.rs/reqwest/0.12.23)
- [Hyper 1.7.0](https://docs.rs/hyper/1.7.0)

**序列化**:

- [Serde 1.0.228](https://docs.rs/serde/)
- [Prost 0.14.1](https://docs.rs/prost/)

**错误处理**:

- [anyhow 1.0.100](https://docs.rs/anyhow/)
- [thiserror 2.0.17](https://docs.rs/thiserror/)

### 社区和支持

- [Rust官方论坛](https://users.rust-lang.org/)
- [Tokio Discord](https://discord.gg/tokio)
- [OpenTelemetry Slack](https://cloud-native.slack.com/)
- [GitHub Discussions](https://github.com/open-telemetry/opentelemetry-rust/discussions)

---

## 15. Rust 1.90 Async/Await 特性清单

### 15.1 核心语言特性

**稳定的 Async Fn in Traits (AFIT)**：

```rust
// Rust 1.75+ 稳定，1.90 优化
trait AsyncService {
    // 直接定义异步方法，无需宏
    async fn process(&self, data: Vec<u8>) -> Result<(), Error>;
    
    // 支持生命周期
    async fn process_ref<'a>(&'a self, data: &'a [u8]) -> Result<(), Error>;
    
    // 支持泛型
    async fn process_generic<T: Send + 'static>(&self, data: T) -> Result<T, Error>;
}

// Rust 1.90 改进:
// - 更小的 Future 大小
// - 更好的内联优化
// - 改进的生命周期推导
// - 更清晰的错误消息
```

**impl Trait in Return Position (RPITIT)**：

```rust
trait AsyncProcessor {
    // 返回类型为 impl Future，编译时确定
    fn process(&self) -> impl Future<Output = Result<(), Error>> + Send;
    
    // 返回 Stream
    fn stream(&self) -> impl Stream<Item = Data> + Send;
    
    // Rust 1.90: 零成本抽象，无虚函数开销
}
```

**Async Closures (实验性)**：

```rust
// Rust 1.90: 逐步稳定中
#![feature(async_closure)]

async fn process_items(items: Vec<Item>) {
    // 异步闭包可以直接在组合器中使用
    let results = items.into_iter()
        .map(async |item| {
            process_async(item).await
        })
        .collect::<Vec<_>>();
    
    futures::future::join_all(results).await;
}
```

### 15.2 性能优化特性

**Future 大小优化**：

```text
Rust 1.90 改进:
┌───────────────────────────────────┐
│ Feature               │ 改进     │
├───────────────────────────────────┤
│ Future 大小           │ -20~30%  │
│ 栈使用                │ -15~25%  │
│ 编译时间              │ -10~15%  │
│ 运行时性能            │ +5~10%   │
└───────────────────────────────────┘
```

**编译器优化**：

```text
✅ 跨 crate 内联
✅ 更激进的 Future 组合器优化
✅ 消除不必要的包装
✅ 更好的寄存器分配
✅ 减少动态分配
```

### 15.3 最佳实践总结

**Rust 1.90 Async 最佳实践**：

```text
DO ✅:
□ 使用原生 async fn in traits（不使用 async-trait 宏）
□ 使用 impl Trait 简化返回类型
□ 利用编译器优化（LTO, codegen-units=1）
□ 使用 Tokio 1.47.1+ 运行时
□ 使用 parking_lot 和 DashMap 优化并发
□ 启用 Bytes 实现零拷贝
□ 合理设置批处理大小
□ 实现优雅关闭机制

DON'T ❌:
□ 避免在 async 函数中持有 std::sync::Mutex
□ 不要过度使用 spawn（考虑使用 select! 或 join!）
□ 避免大型 Future（考虑拆分）
□ 不要忽略背压控制
□ 避免在热路径中频繁分配
□ 不要在生产环境使用 #[tokio::test(flavor = "current_thread")]
```

### 15.4 迁移指南

**从 async-trait 迁移到原生 AFIT**：

```rust
// 旧代码 (使用 async-trait 宏)
use async_trait::async_trait;

#[async_trait]
trait OldService {
    async fn process(&self) -> Result<(), Error>;
}

#[async_trait]
impl OldService for MyService {
    async fn process(&self) -> Result<(), Error> {
        Ok(())
    }
}

// 新代码 (Rust 1.90 原生支持)
trait NewService {
    async fn process(&self) -> Result<(), Error>;
}

impl NewService for MyService {
    async fn process(&self) -> Result<(), Error> {
        Ok(())
    }
}

// 优势:
// ✅ 零成本抽象（无宏开销）
// ✅ 更好的编译器优化
// ✅ 更小的 Future 大小
// ✅ 更清晰的错误消息
// ✅ 更快的编译速度
```

**性能对比**：

```text
Feature              │ async-trait │ 原生 AFIT │ 改进
─────────────────────┼─────────────┼───────────┼──────
Future 大小          │ 较大        │ 较小      │ -25%
编译时间             │ 基准        │ 更快      │ -15%
运行时性能           │ 基准        │ 更快      │ +10%
代码可读性           │ 良好        │ 更好      │ ✅
编译器优化           │ 受限        │ 完全      │ ✅
```

---

**文档状态**: ✅ 完成 (Rust 1.90 + OpenTelemetry 0.31.0 最新版)  
**审核状态**: 2025年10月9日更新  
**Rust 版本**: 1.90+  
**OpenTelemetry SDK**: 0.31.0  
**Tokio 版本**: 1.47.1  
**最后更新**: 2025年10月9日  
**文档类型**: 仅包含Rust相关内容  
**更新内容**: 补充 Rust 1.90 最新 async/await 特性和最佳实践

---

## ✨ 文档特性亮点

### Rust 1.90 核心特性

- ✅ **原生 Async Fn in Traits** - 无需 async-trait 宏
- ✅ **impl Trait in Associated Types** - 零成本抽象
- ✅ **改进的生命周期推导** - 更智能的编译器
- ✅ **优化的异步运行时** - Tokio 1.47.1 深度集成

### OpenTelemetry 0.31.0 完整支持

- ✅ **Traces导出** - gRPC + HTTP双协议
- ✅ **Metrics导出** - 完整指标支持
- ✅ **Logs导出** - 结构化日志
- ✅ **Tracing集成** - 无缝集成

### 性能优化

- ✅ **零拷贝传输** - Bytes crate优化
- ✅ **无锁并发** - crossbeam + dashmap
- ✅ **智能批处理** - 自适应批量处理
- ✅ **高性能同步原语** - parking_lot

### 生产级特性

- ✅ **完整错误处理** - thiserror + anyhow
- ✅ **优雅关闭机制** - 信号处理
- ✅ **环境变量配置** - 12-Factor App
- ✅ **TLS安全支持** - RustLS纯Rust实现

---

## 📚 相关文档导航

### 核心组件文档

- [SDK概述](01_SDK概述.md) - OpenTelemetry SDK架构
- [Collector架构](02_Collector架构.md) - Collector部署和配置
- [SDK最佳实践](03_SDK最佳实践.md) - 生产环境实践
- [Context Propagation详解](04_Context_Propagation详解.md) - 上下文传播

### 协议文档

- [OTLP协议概述](../01_OTLP核心协议/01_协议概述.md)
- [gRPC传输层](../01_OTLP核心协议/02_传输层_gRPC.md)
- [HTTP传输层](../01_OTLP核心协议/03_传输层_HTTP.md)

### 性能优化1

- [采样策略](../05_采样与性能/01_采样策略.md)
- [性能优化实践](../05_采样与性能/02_性能优化实践.md)

### 实战案例

- [微服务追踪实战](../06_实战案例/01_微服务追踪实战.md)

---

## 🚀 快速开始

```rust
use opentelemetry::global;
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化遥测系统
    setup_telemetry().await?;
    
    // 使用tracing记录日志
    info!("Application started");
    
    // 你的业务逻辑...
    
    Ok(())
}
```

---

**版权声明**: © 2025 OTLP Rust标准深度梳理项目  
**许可证**: MIT OR Apache-2.0  
**维护者**: Rust OTLP Team  
**问题反馈**: [GitHub Issues](https://github.com/your-repo/issues)
