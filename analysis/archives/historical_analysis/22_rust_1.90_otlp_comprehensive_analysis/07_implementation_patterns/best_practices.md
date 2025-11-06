# Rust OTLP 实现最佳实践

> **主题**: 实现模式 - 最佳实践
> **日期**: 2025年10月3日
> **难度**: ⭐⭐⭐ 中级

---

## 📋 目录

- [Rust OTLP 实现最佳实践](#rust-otlp-实现最佳实践)
  - [📋 目录](#-目录)
  - [项目结构](#项目结构)
    - [1. 推荐的模块组织](#1-推荐的模块组织)
    - [2. Cargo.toml 最佳配置](#2-cargotoml-最佳配置)
  - [类型设计](#类型设计)
    - [1. 使用 Newtype Pattern 保证类型安全](#1-使用-newtype-pattern-保证类型安全)
    - [2. Builder Pattern 构造复杂对象](#2-builder-pattern-构造复杂对象)
    - [3. Trait 抽象通用行为](#3-trait-抽象通用行为)
  - [异步编程](#异步编程)
    - [1. 使用 AFIT (Async Functions in Traits)](#1-使用-afit-async-functions-in-traits)
    - [2. 避免不必要的 `.await`](#2-避免不必要的-await)
    - [3. 使用 `tokio::select!` 处理超时](#3-使用-tokioselect-处理超时)
    - [4. 使用 `JoinSet` 管理多个任务](#4-使用-joinset-管理多个任务)
  - [错误处理](#错误处理)
    - [1. 使用 `thiserror` 定义错误类型](#1-使用-thiserror-定义错误类型)
    - [2. 区分可恢复和不可恢复错误](#2-区分可恢复和不可恢复错误)
    - [3. 使用 `anyhow` 简化应用程序错误处理](#3-使用-anyhow-简化应用程序错误处理)
  - [性能优化](#性能优化)
    - [1. 零拷贝序列化](#1-零拷贝序列化)
    - [2. 对象池复用内存](#2-对象池复用内存)
    - [3. 批处理减少网络开销](#3-批处理减少网络开销)
  - [测试策略](#测试策略)
    - [1. 单元测试](#1-单元测试)
    - [2. 属性测试 (Property Testing)](#2-属性测试-property-testing)
    - [3. 集成测试](#3-集成测试)
    - [4. 基准测试](#4-基准测试)
  - [文档与注释](#文档与注释)
    - [1. 模块级文档](#1-模块级文档)
    - [2. 函数文档](#2-函数文档)
    - [3. 安全性注释](#3-安全性注释)
  - [生产部署](#生产部署)
    - [1. 配置管理](#1-配置管理)
    - [2. 日志和监控](#2-日志和监控)
    - [3. 优雅关闭](#3-优雅关闭)
  - [总结](#总结)
    - [核心最佳实践](#核心最佳实践)
    - [学习路径](#学习路径)

---

## 项目结构

### 1. 推荐的模块组织

```text
otlp-rust/
├── Cargo.toml
├── src/
│   ├── lib.rs                  # 公共 API
│   ├── error.rs                # 错误类型
│   ├── model/                  # OTLP 数据模型
│   │   ├── mod.rs
│   │   ├── trace.rs            # Trace 模型
│   │   ├── metric.rs           # Metric 模型
│   │   ├── log.rs              # Log 模型
│   │   └── resource.rs         # Resource 模型
│   ├── exporter/               # 导出器
│   │   ├── mod.rs
│   │   ├── http.rs             # HTTP 导出器
│   │   ├── grpc.rs             # gRPC 导出器
│   │   └── batch.rs            # 批处理逻辑
│   ├── propagator/             # 上下文传播
│   │   ├── mod.rs
│   │   ├── w3c.rs              # W3C Trace Context
│   │   └── baggage.rs          # Baggage
│   └── runtime/                # 运行时配置
│       ├── mod.rs
│       └── tokio_config.rs
├── examples/                   # 示例代码
│   ├── basic_tracing.rs
│   ├── async_export.rs
│   └── custom_exporter.rs
├── benches/                    # 基准测试
│   └── span_creation.rs
└── tests/                      # 集成测试
    └── e2e_test.rs
```

### 2. Cargo.toml 最佳配置

```toml
[package]
name = "otlp-rust"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"  # MSRV
authors = ["Your Name <email@example.com>"]
license = "MIT OR Apache-2.0"
description = "OpenTelemetry Protocol (OTLP) implementation in Rust"
repository = "https://github.com/yourusername/otlp-rust"
keywords = ["otlp", "opentelemetry", "observability", "tracing"]
categories = ["development-tools::profiling", "asynchronous"]

[dependencies]
# 异步运行时
tokio = { version = "1.47", features = ["full"] }
# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
prost = "0.13"
# 网络
tonic = { version = "0.12", features = ["tls", "gzip"] }
reqwest = { version = "0.12", features = ["json", "gzip"] }
# 工具库
thiserror = "2.0"
tracing = "0.1"
bytes = "1.8"
# 时间
time = { version = "0.3", features = ["formatting", "parsing"] }

[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }
tokio-test = "0.4"
proptest = "1.0"

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
strip = true

[profile.bench]
inherits = "release"
debug = true  # 保留符号用于性能分析

[[bench]]
name = "span_creation"
harness = false
```

---

## 类型设计

### 1. 使用 Newtype Pattern 保证类型安全

```rust
/// ✅ 好的做法：强类型保证
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraceId([u8; 16]);

impl TraceId {
    /// 不允许创建全零 TraceId
    pub fn new(bytes: [u8; 16]) -> Option<Self> {
        if bytes == [0; 16] {
            None
        } else {
            Some(TraceId(bytes))
        }
    }

    /// 生成随机 TraceId
    pub fn random() -> Self {
        use rand::Rng;
        let mut bytes = [0u8; 16];
        rand::thread_rng().fill(&mut bytes);
        TraceId(bytes)
    }

    /// 从十六进制字符串解析
    pub fn from_hex(hex: &str) -> Result<Self, ParseError> {
        if hex.len() != 32 {
            return Err(ParseError::InvalidLength);
        }
        let mut bytes = [0u8; 16];
        hex::decode_to_slice(hex, &mut bytes)?;
        Self::new(bytes).ok_or(ParseError::AllZeros)
    }
}

// ❌ 不好的做法：使用原始类型
// type TraceId = [u8; 16];  // 无法添加方法和约束
```

### 2. Builder Pattern 构造复杂对象

```rust
/// ✅ 构建器模式
pub struct SpanBuilder {
    trace_id: TraceId,
    span_id: SpanId,
    parent_span_id: Option<SpanId>,
    name: String,
    kind: SpanKind,
    attributes: Vec<KeyValue>,
    events: Vec<Event>,
}

impl SpanBuilder {
    pub fn new(trace_id: TraceId, name: impl Into<String>) -> Self {
        Self {
            trace_id,
            span_id: SpanId::random(),
            parent_span_id: None,
            name: name.into(),
            kind: SpanKind::Internal,
            attributes: Vec::new(),
            events: Vec::new(),
        }
    }

    pub fn with_parent(mut self, parent_span_id: SpanId) -> Self {
        self.parent_span_id = Some(parent_span_id);
        self
    }

    pub fn with_kind(mut self, kind: SpanKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<AnyValue>) -> Self {
        self.attributes.push(KeyValue {
            key: key.into(),
            value: value.into(),
        });
        self
    }

    pub fn build(self) -> Span {
        Span {
            trace_id: self.trace_id,
            span_id: self.span_id,
            parent_span_id: self.parent_span_id,
            name: self.name,
            kind: self.kind,
            start_time: current_timestamp(),
            end_time: None,
            attributes: self.attributes,
            events: self.events,
            status: SpanStatus::Unset,
        }
    }
}

// 使用示例
let span = SpanBuilder::new(trace_id, "process_request")
    .with_kind(SpanKind::Server)
    .with_attribute("http.method", "GET")
    .with_attribute("http.status_code", 200)
    .build();
```

### 3. Trait 抽象通用行为

```rust
/// ✅ Trait 定义导出器接口
#[async_trait]
pub trait OtlpExporter: Send + Sync {
    type Error: std::error::Error + Send + Sync + 'static;

    async fn export_traces(&self, traces: Vec<Span>) -> Result<ExportResult, Self::Error>;
    async fn export_metrics(&self, metrics: Vec<Metric>) -> Result<ExportResult, Self::Error>;
    async fn export_logs(&self, logs: Vec<LogRecord>) -> Result<ExportResult, Self::Error>;

    /// 关闭导出器，释放资源
    async fn shutdown(&self) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// HTTP 导出器实现
pub struct HttpExporter {
    client: reqwest::Client,
    endpoint: String,
}

#[async_trait]
impl OtlpExporter for HttpExporter {
    type Error = HttpExportError;

    async fn export_traces(&self, traces: Vec<Span>) -> Result<ExportResult, Self::Error> {
        let request = ExportTraceServiceRequest { traces };
        let response = self.client
            .post(&format!("{}/v1/traces", self.endpoint))
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            Ok(ExportResult::Success)
        } else {
            Err(HttpExportError::ServerError(response.status()))
        }
    }

    // ... 其他方法
}
```

---

## 异步编程

### 1. 使用 AFIT (Async Functions in Traits)

Rust 1.75+ 原生支持异步 trait 方法：

```rust
/// ✅ Rust 1.75+ 原生支持
trait AsyncProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<(), Error>;
}

// ❌ 旧方法：需要 async-trait 宏
// #[async_trait]
// trait AsyncProcessor {
//     async fn process(&self, data: Vec<u8>) -> Result<(), Error>;
// }
```

### 2. 避免不必要的 `.await`

```rust
// ✅ 好的做法：并发执行
async fn export_all(exporter: &impl OtlpExporter, data: TelemetryData) {
    let (trace_result, metric_result, log_result) = tokio::join!(
        exporter.export_traces(data.traces),
        exporter.export_metrics(data.metrics),
        exporter.export_logs(data.logs),
    );
    // 处理结果...
}

// ❌ 不好的做法：串行执行
async fn export_all_slow(exporter: &impl OtlpExporter, data: TelemetryData) {
    exporter.export_traces(data.traces).await?;
    exporter.export_metrics(data.metrics).await?;  // 等待上一个完成
    exporter.export_logs(data.logs).await?;        // 等待上一个完成
}
```

### 3. 使用 `tokio::select!` 处理超时

```rust
use tokio::time::{timeout, Duration};

/// ✅ 带超时的导出
async fn export_with_timeout(
    exporter: &impl OtlpExporter,
    traces: Vec<Span>,
    timeout_duration: Duration,
) -> Result<ExportResult, ExportError> {
    match timeout(timeout_duration, exporter.export_traces(traces)).await {
        Ok(result) => result.map_err(Into::into),
        Err(_) => Err(ExportError::Timeout),
    }
}
```

### 4. 使用 `JoinSet` 管理多个任务

```rust
use tokio::task::JoinSet;

/// ✅ 动态任务管理
async fn batch_export(
    exporter: Arc<impl OtlpExporter + 'static>,
    batches: Vec<Vec<Span>>,
) -> Vec<Result<ExportResult, ExportError>> {
    let mut set = JoinSet::new();

    for batch in batches {
        let exporter = Arc::clone(&exporter);
        set.spawn(async move {
            exporter.export_traces(batch).await
        });
    }

    let mut results = Vec::new();
    while let Some(result) = set.join_next().await {
        results.push(result.unwrap());
    }
    results
}
```

---

## 错误处理

### 1. 使用 `thiserror` 定义错误类型

```rust
use thiserror::Error;

/// ✅ 结构化错误类型
#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("Invalid TraceId: {0}")]
    InvalidTraceId(String),

    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    #[error("Export timeout (limit: {limit:?})")]
    Timeout { limit: Duration },

    #[error("Server returned error: {status}")]
    ServerError { status: u16 },
}

// 使用示例
fn parse_trace_id(s: &str) -> Result<TraceId, OtlpError> {
    TraceId::from_hex(s)
        .map_err(|e| OtlpError::InvalidTraceId(e.to_string()))
}
```

### 2. 区分可恢复和不可恢复错误

```rust
/// ✅ 可恢复错误：返回 Result
pub async fn export_with_retry(
    exporter: &impl OtlpExporter,
    traces: Vec<Span>,
    max_retries: usize,
) -> Result<ExportResult, OtlpError> {
    let mut attempt = 0;
    loop {
        match exporter.export_traces(traces.clone()).await {
            Ok(result) => return Ok(result),
            Err(e) if attempt < max_retries => {
                attempt += 1;
                let backoff = Duration::from_millis(100 * 2_u64.pow(attempt as u32));
                tokio::time::sleep(backoff).await;
            }
            Err(e) => return Err(e.into()),
        }
    }
}

/// ❌ 不可恢复错误：使用 panic
pub fn validate_config(config: &OtlpConfig) {
    assert!(!config.endpoint.is_empty(), "Endpoint must not be empty");
    assert!(config.batch_size > 0, "Batch size must be positive");
}
```

### 3. 使用 `anyhow` 简化应用程序错误处理

```rust
use anyhow::{Context, Result};

/// ✅ 应用程序级别错误（非库代码）
async fn run_exporter() -> Result<()> {
    let config = load_config()
        .context("Failed to load configuration")?;

    let exporter = HttpExporter::new(config.endpoint)
        .context("Failed to create exporter")?;

    let traces = collect_traces()
        .await
        .context("Failed to collect traces")?;

    exporter.export_traces(traces)
        .await
        .context("Failed to export traces")?;

    Ok(())
}
```

---

## 性能优化

### 1. 零拷贝序列化

```rust
use bytes::{Bytes, BytesMut};

/// ✅ 零拷贝：使用 Bytes
pub struct ZeroCopySpan {
    trace_id: TraceId,
    span_id: SpanId,
    name: Bytes,  // ← 零拷贝字符串
    attributes: Vec<(Bytes, AnyValue)>,
}

impl ZeroCopySpan {
    pub fn serialize(&self) -> Bytes {
        let mut buf = BytesMut::with_capacity(1024);
        // 序列化到 buf
        // ...
        buf.freeze()  // ← 零拷贝转换为 Bytes
    }
}

// ❌ 不好的做法：每次都复制
// pub struct CopySpan {
//     name: String,  // ← 每次访问都可能复制
// }
```

### 2. 对象池复用内存

```rust
use std::sync::Arc;
use parking_lot::Mutex;

/// ✅ 对象池
pub struct SpanPool {
    pool: Arc<Mutex<Vec<Vec<Span>>>>,
    capacity: usize,
}

impl SpanPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(16))),
            capacity,
        }
    }

    /// 获取缓冲区（复用或新建）
    pub fn acquire(&self) -> Vec<Span> {
        self.pool
            .lock()
            .pop()
            .unwrap_or_else(|| Vec::with_capacity(self.capacity))
    }

    /// 归还缓冲区（清空但保留容量）
    pub fn release(&self, mut buffer: Vec<Span>) {
        if buffer.capacity() >= self.capacity {
            buffer.clear();
            let mut pool = self.pool.lock();
            if pool.len() < 16 {
                pool.push(buffer);
            }
        }
    }
}

// 使用示例
let pool = SpanPool::new(1000);
let mut buffer = pool.acquire();
buffer.push(span);
// ... 使用 buffer
pool.release(buffer);  // 归还复用
```

### 3. 批处理减少网络开销

```rust
/// ✅ 智能批处理
pub struct SmartBatcher {
    buffer: Arc<Mutex<Vec<Span>>>,
    batch_size: usize,
    flush_interval: Duration,
}

impl SmartBatcher {
    pub async fn collect(&self, span: Span) -> Option<Vec<Span>> {
        let mut buffer = self.buffer.lock();
        buffer.push(span);

        // 达到批大小，立即刷新
        if buffer.len() >= self.batch_size {
            Some(std::mem::take(&mut *buffer))
        } else {
            None
        }
    }

    /// 定时刷新任务
    pub async fn start_flush_task(self: Arc<Self>) {
        let mut interval = tokio::time::interval(self.flush_interval);
        loop {
            interval.tick().await;
            let batch = {
                let mut buffer = self.buffer.lock();
                if buffer.is_empty() {
                    continue;
                }
                std::mem::take(&mut *buffer)
            };
            tokio::spawn(async move {
                export_batch(batch).await;
            });
        }
    }
}
```

---

## 测试策略

### 1. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trace_id_creation() {
        // ✅ 测试正常情况
        let bytes = [1; 16];
        assert!(TraceId::new(bytes).is_some());

        // ✅ 测试边界条件
        let zeros = [0; 16];
        assert!(TraceId::new(zeros).is_none());
    }

    #[test]
    fn test_trace_id_from_hex() {
        let hex = "00112233445566778899aabbccddeeff";
        let trace_id = TraceId::from_hex(hex).unwrap();
        assert_eq!(trace_id.to_string(), hex);
    }

    #[test]
    #[should_panic(expected = "Invalid length")]
    fn test_trace_id_invalid_length() {
        TraceId::from_hex("short").unwrap();
    }
}
```

### 2. 属性测试 (Property Testing)

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_trace_id_roundtrip(bytes in prop::array::uniform16(any::<u8>())) {
        // 排除全零情况
        prop_assume!(bytes != [0; 16]);

        let trace_id = TraceId::new(bytes).unwrap();
        let hex = trace_id.to_string();
        let parsed = TraceId::from_hex(&hex).unwrap();

        prop_assert_eq!(trace_id, parsed);
    }

    #[test]
    fn test_span_builder_always_valid(
        name in "\\PC+",  // 非空字符串
        kind in prop_oneof![
            Just(SpanKind::Server),
            Just(SpanKind::Client),
            Just(SpanKind::Internal),
        ]
    ) {
        let trace_id = TraceId::random();
        let span = SpanBuilder::new(trace_id, name.clone())
            .with_kind(kind)
            .build();

        prop_assert_eq!(span.name, name);
        prop_assert_eq!(span.kind, kind);
    }
}
```

### 3. 集成测试

```rust
// tests/integration_test.rs
use otlp_rust::*;
use tokio::test;

#[tokio::test]
async fn test_end_to_end_export() {
    // 启动测试服务器
    let server = start_mock_server().await;

    // 创建导出器
    let exporter = HttpExporter::new(server.url());

    // 创建并导出 Span
    let trace_id = TraceId::random();
    let span = SpanBuilder::new(trace_id, "test_span")
        .with_attribute("test.key", "test_value")
        .build();

    let result = exporter.export_traces(vec![span]).await;
    assert!(result.is_ok());

    // 验证服务器收到数据
    let received = server.received_spans().await;
    assert_eq!(received.len(), 1);
    assert_eq!(received[0].name, "test_span");
}
```

### 4. 基准测试

```rust
// benches/span_creation.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use otlp_rust::*;

fn bench_span_creation(c: &mut Criterion) {
    let trace_id = TraceId::random();

    c.bench_function("span_creation", |b| {
        b.iter(|| {
            SpanBuilder::new(black_box(trace_id), black_box("test_span"))
                .with_attribute("key", "value")
                .build()
        });
    });
}

fn bench_batch_export(c: &mut Criterion) {
    let runtime = tokio::runtime::Runtime::new().unwrap();
    let exporter = HttpExporter::new("http://localhost:4318");

    let mut group = c.benchmark_group("batch_export");
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.to_async(&runtime).iter(|| async {
                let spans = create_test_spans(size);
                exporter.export_traces(black_box(spans)).await
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_span_creation, bench_batch_export);
criterion_main!(benches);
```

---

## 文档与注释

### 1. 模块级文档

```rust
//! # OTLP Rust - OpenTelemetry Protocol Implementation
//!
//! 这个库提供了 OpenTelemetry Protocol (OTLP) 的 Rust 实现，支持：
//!
//! - ✅ Trace、Metric、Log 数据模型
//! - ✅ HTTP 和 gRPC 导出器
//! - ✅ W3C Trace Context 传播
//! - ✅ 异步批处理和重试机制
//!
//! ## 快速开始
//!
//! ```rust
//! use otlp_rust::*;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let exporter = HttpExporter::new("http://localhost:4318");
//!
//!     let trace_id = TraceId::random();
//!     let span = SpanBuilder::new(trace_id, "example_span")
//!         .with_attribute("http.method", "GET")
//!         .build();
//!
//!     exporter.export_traces(vec![span]).await?;
//!     Ok(())
//! }
//! ```
//!
//! ## 性能特征
//!
//! - Span 创建: ~80 ns
//! - 批量导出 (1000 spans): ~5 ms
//! - 内存占用: ~100 MB (1000 spans 缓存)
```

### 2. 函数文档

```rust
/// 创建一个新的 TraceId
///
/// # 参数
///
/// * `bytes` - 16 字节的 TraceId 数据
///
/// # 返回
///
/// 如果 `bytes` 全为零，返回 `None`；否则返回 `Some(TraceId)`。
///
/// # 示例
///
/// ```
/// use otlp_rust::TraceId;
///
/// let bytes = [1; 16];
/// let trace_id = TraceId::new(bytes).unwrap();
/// assert_eq!(trace_id.as_bytes(), &bytes);
/// ```
///
/// # OTLP 规范
///
/// 根据 OTLP 规范，TraceId 必须是非全零的 16 字节值。
/// 参考：<https://opentelemetry.io/docs/specs/otel/trace/api/#traceid>
pub fn new(bytes: [u8; 16]) -> Option<Self> {
    if bytes == [0; 16] {
        None
    } else {
        Some(TraceId(bytes))
    }
}
```

### 3. 安全性注释

```rust
/// # Safety
///
/// 此函数跳过了 TraceId 的非零检查。调用者必须保证 `bytes` 不是全零。
///
/// 错误使用此函数可能导致违反 OTLP 规范，但不会导致内存不安全。
///
/// # 示例
///
/// ```
/// use otlp_rust::TraceId;
///
/// let bytes = [1; 16];
/// let trace_id = unsafe { TraceId::new_unchecked(bytes) };
/// ```
pub unsafe fn new_unchecked(bytes: [u8; 16]) -> Self {
    debug_assert!(bytes != [0; 16], "TraceId must not be all zeros");
    TraceId(bytes)
}
```

---

## 生产部署

### 1. 配置管理

```rust
use serde::{Deserialize, Serialize};

/// ✅ 完整的配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpConfig {
    /// OTLP 端点 URL
    #[serde(default = "default_endpoint")]
    pub endpoint: String,

    /// 批处理大小
    #[serde(default = "default_batch_size")]
    pub batch_size: usize,

    /// 刷新间隔（毫秒）
    #[serde(default = "default_flush_interval")]
    pub flush_interval_ms: u64,

    /// 最大重试次数
    #[serde(default = "default_max_retries")]
    pub max_retries: usize,

    /// 导出超时（秒）
    #[serde(default = "default_timeout")]
    pub timeout_secs: u64,

    /// 启用 gzip 压缩
    #[serde(default)]
    pub enable_compression: bool,
}

fn default_endpoint() -> String {
    "http://localhost:4318".to_string()
}

fn default_batch_size() -> usize {
    1000
}

fn default_flush_interval() -> u64 {
    5000  // 5 秒
}

fn default_max_retries() -> usize {
    3
}

fn default_timeout() -> u64 {
    30  // 30 秒
}

// 从环境变量和配置文件加载
impl OtlpConfig {
    pub fn from_env() -> Result<Self, ConfigError> {
        let mut config = Self::default();

        if let Ok(endpoint) = std::env::var("OTLP_ENDPOINT") {
            config.endpoint = endpoint;
        }
        if let Ok(batch_size) = std::env::var("OTLP_BATCH_SIZE") {
            config.batch_size = batch_size.parse()?;
        }

        Ok(config)
    }
}
```

### 2. 日志和监控

```rust
use tracing::{info, warn, error, instrument};

/// ✅ 结构化日志
#[instrument(skip(exporter, traces), fields(trace_count = traces.len()))]
pub async fn export_traces_instrumented(
    exporter: &impl OtlpExporter,
    traces: Vec<Span>,
) -> Result<ExportResult, OtlpError> {
    info!("Starting trace export");

    match exporter.export_traces(traces).await {
        Ok(result) => {
            info!("Trace export successful");
            Ok(result)
        }
        Err(e) => {
            error!("Trace export failed: {}", e);
            Err(e.into())
        }
    }
}

/// ✅ 指标收集
pub struct ExporterMetrics {
    pub export_count: Arc<AtomicU64>,
    pub export_errors: Arc<AtomicU64>,
    pub export_duration_ms: Arc<AtomicU64>,
}

impl ExporterMetrics {
    pub fn record_export(&self, duration: Duration, success: bool) {
        self.export_count.fetch_add(1, Ordering::Relaxed);
        self.export_duration_ms.fetch_add(
            duration.as_millis() as u64,
            Ordering::Relaxed
        );
        if !success {
            self.export_errors.fetch_add(1, Ordering::Relaxed);
        }
    }
}
```

### 3. 优雅关闭

```rust
use tokio::signal;

/// ✅ 优雅关闭
pub async fn run_with_graceful_shutdown(
    exporter: Arc<impl OtlpExporter>,
    collector: Arc<SpanCollector>,
) -> Result<(), Box<dyn std::error::Error>> {
    // 启动收集任务
    let collector_task = tokio::spawn(async move {
        collector.start_collection().await
    });

    // 等待关闭信号
    signal::ctrl_c().await?;
    info!("Received shutdown signal");

    // 停止接收新数据
    collector.stop_accepting();

    // 刷新剩余数据
    let remaining = collector.drain().await;
    if !remaining.is_empty() {
        info!("Flushing {} remaining spans", remaining.len());
        exporter.export_traces(remaining).await?;
    }

    // 关闭导出器
    exporter.shutdown().await?;

    // 等待任务完成
    collector_task.await??;

    info!("Shutdown complete");
    Ok(())
}
```

---

## 总结

### 核心最佳实践

1. **类型安全**: 使用 newtype、phantom types 编码不变量
2. **异步优先**: 使用 Tokio + AFIT 实现高性能
3. **错误处理**: 区分库错误 (thiserror) 和应用错误 (anyhow)
4. **性能优化**: 零拷贝、对象池、批处理
5. **测试覆盖**: 单元测试 + 属性测试 + 集成测试 + 基准测试
6. **文档完善**: 模块文档、函数文档、示例代码
7. **生产就绪**: 配置管理、日志监控、优雅关闭

### 学习路径

1. **初级**: 掌握基本类型设计和错误处理
2. **中级**: 理解异步编程和性能优化
3. **高级**: 实现复杂并发模式和形式化验证

---

**维护者**: OTLP Rust 2025 研究团队
**更新日期**: 2025年10月3日
**许可证**: MIT OR Apache-2.0
