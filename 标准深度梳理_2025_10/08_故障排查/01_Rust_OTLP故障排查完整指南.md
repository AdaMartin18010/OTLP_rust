# Rust OTLP 故障排查完整指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [Rust OTLP 故障排查完整指南](#rust-otlp-故障排查完整指南)
  - [目录](#目录)
  - [1. 常见问题速查](#1-常见问题速查)
    - [问题分类表](#问题分类表)
  - [2. 连接问题](#2-连接问题)
    - [问题1: 无法连接到 OTLP Collector](#问题1-无法连接到-otlp-collector)
    - [问题2: TLS/SSL 证书错误](#问题2-tlsssl-证书错误)
  - [3. 数据未显示](#3-数据未显示)
    - [问题3: Jaeger 中看不到追踪数据](#问题3-jaeger-中看不到追踪数据)
    - [问题4: Span 未正确关联](#问题4-span-未正确关联)
  - [4. 性能问题](#4-性能问题)
    - [问题5: 高延迟](#问题5-高延迟)
    - [问题6: 内存占用过高](#问题6-内存占用过高)
  - [5. 编译错误](#5-编译错误)
    - [问题7: 依赖版本冲突](#问题7-依赖版本冲突)
    - [问题8: 特性标志错误](#问题8-特性标志错误)
  - [6. 运行时错误](#6-运行时错误)
    - [问题9: Panic in tokio runtime](#问题9-panic-in-tokio-runtime)
  - [7. 调试技巧](#7-调试技巧)
    - [启用详细日志](#启用详细日志)
    - [自定义 Debug Exporter](#自定义-debug-exporter)
  - [8. 生产环境问题](#8-生产环境问题)
    - [问题10: 追踪数据丢失](#问题10-追踪数据丢失)

---

## 1. 常见问题速查

### 问题分类表

| 问题类型 | 症状 | 快速解决 |
|---------|------|---------|
| 连接失败 | `Connection refused` | 检查 Collector 是否运行 |
| 无追踪数据 | Jaeger 中无数据 | 检查 service.name 配置 |
| 编译错误 | 依赖冲突 | 运行 `cargo update` |
| 性能下降 | 高延迟 | 启用批处理 |
| 内存泄漏 | 内存持续增长 | 检查 Span 是否正确结束 |

---

## 2. 连接问题

### 问题1: 无法连接到 OTLP Collector

**症状**:

```text
Error: Failed to export spans: transport error
Connection refused (os error 111)
```

**诊断步骤**:

```rust
// 1. 测试连接
use tokio::net::TcpStream;

#[tokio::test]
async fn test_otlp_connection() {
    let result = TcpStream::connect("localhost:4317").await;
    assert!(result.is_ok(), "Cannot connect to OTLP endpoint");
}
```

**解决方案**:

```bash
# 检查 Collector 是否运行
docker ps | grep jaeger

# 启动 Jaeger
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 4317:4317 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest

# 测试端口
nc -zv localhost 4317
```

**代码修复**:

```rust
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

// 添加超时和重试
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(3))
    .build_span_exporter()?;
```

---

### 问题2: TLS/SSL 证书错误

**症状**:

```text
Error: InvalidCertificate
```

**解决方案**:

```rust
use tonic::transport::{Certificate, ClientTlsConfig};

// 禁用 TLS (仅开发环境)
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317") // 使用 http 而非 https
    .build_span_exporter()?;

// 或配置自定义证书 (生产环境)
let cert = std::fs::read_to_string("/path/to/ca.crt")?;
let cert = Certificate::from_pem(cert);

let tls_config = ClientTlsConfig::new()
    .ca_certificate(cert)
    .domain_name("collector.example.com");

let channel = tonic::transport::Channel::from_static("https://collector.example.com:4317")
    .tls_config(tls_config)?
    .connect()
    .await?;
```

---

## 3. 数据未显示

### 问题3: Jaeger 中看不到追踪数据

**诊断清单**:

```rust
// 检查点 1: service.name 是否设置
use opentelemetry::KeyValue;
use opentelemetry_sdk::Resource;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"), // ✅ 必须设置
]);

// 检查点 2: 是否正确关闭 provider
fn main() {
    // ... 初始化 ...
    
    // ❌ 错误: 没有调用 shutdown
    // 数据可能未导出就退出了
}

// ✅ 正确
fn main() {
    let provider = init_telemetry();
    
    // ... 应用逻辑 ...
    
    provider.shutdown().expect("Failed to shutdown provider"); // ✅
}
```

**调试代码**:

```rust
use tracing::{info, debug};

#[tokio::main]
async fn main() {
    // 启用详细日志
    std::env::set_var("RUST_LOG", "debug,opentelemetry=trace");
    
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    let provider = init_telemetry().await;
    
    // 测试追踪
    info!("Creating test span");
    
    let tracer = opentelemetry::global::tracer("test");
    let span = tracer.start("test-span");
    
    debug!("Span created: {:?}", span.span_context());
    
    drop(span); // 结束 span
    
    // 等待导出
    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
    
    provider.shutdown().unwrap();
    
    info!("Shutdown complete");
}
```

**验证导出**:

```rust
use opentelemetry_sdk::export::trace::SpanExporter;

// 自定义 exporter 用于调试
struct DebugExporter;

#[async_trait::async_trait]
impl SpanExporter for DebugExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()> {
        println!("✅ Exporting {} spans", batch.len());
        for span in &batch {
            println!("  - Span: {} ({})", span.name, span.span_context.trace_id());
        }
        Ok(())
    }
}

// 使用 debug exporter
let provider = TracerProvider::builder()
    .with_simple_exporter(DebugExporter)
    .build();
```

---

### 问题4: Span 未正确关联

**症状**: 追踪数据存在，但 Span 之间没有父子关系

**原因**: Context 未正确传播

```rust
// ❌ 错误: 新 span 没有父 span
#[tracing::instrument]
async fn parent_function() {
    child_function().await; // ❌ context 丢失
}

async fn child_function() {
    // 这个 span 不会关联到 parent
}

// ✅ 正确: 使用 instrument
#[tracing::instrument]
async fn parent_function() {
    child_function().await; // ✅ context 自动传播
}

#[tracing::instrument]
async fn child_function() {
    // 正确关联到 parent
}

// ✅ 或手动传递 context
use opentelemetry::Context;

async fn parent_function() {
    let cx = Context::current();
    child_function(cx).await;
}

async fn child_function(cx: Context) {
    let _guard = cx.attach();
    // 在这个作用域内创建的 span 会关联到 parent
}
```

---

## 4. 性能问题

### 问题5: 高延迟

**症状**: 启用追踪后，应用响应时间显著增加

**诊断**:

```rust
use std::time::Instant;

#[tokio::test]
async fn measure_tracing_overhead() {
    // 不启用追踪
    let start = Instant::now();
    for _ in 0..1000 {
        // 业务逻辑
    }
    let without_tracing = start.elapsed();
    
    // 启用追踪
    init_telemetry();
    let start = Instant::now();
    for _ in 0..1000 {
        traced_operation().await;
    }
    let with_tracing = start.elapsed();
    
    println!("Without: {:?}, With: {:?}, Overhead: {:?}",
        without_tracing, with_tracing,
        with_tracing - without_tracing);
}
```

**优化方案**:

```rust
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

// 1. 启用批处理
let batch_config = BatchConfig::builder()
    .with_max_export_batch_size(512)      // 增加批量大小
    .with_max_queue_size(2048)            // 增加队列大小
    .with_scheduled_delay(Duration::from_millis(500)) // 减少导出频率
    .build();

let processor = BatchSpanProcessor::builder(exporter, tokio::spawn, batch_config)
    .build();

// 2. 使用采样
use opentelemetry_sdk::trace::{Sampler, SamplerDecision};

let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1))); // 10% 采样

let provider = TracerProvider::builder()
    .with_span_processor(processor)
    .with_config(
        opentelemetry_sdk::trace::Config::default()
            .with_sampler(sampler)
    )
    .build();

// 3. 减少 Span 数量
// ❌ 过度追踪
for item in items {
    process_item(item).await; // 每个 item 一个 span
}

// ✅ 批量追踪
#[tracing::instrument(skip(items))]
async fn process_items(items: Vec<Item>) {
    for item in items {
        // 内部不创建 span
        process_item_internal(item).await;
    }
}
```

---

### 问题6: 内存占用过高

**症状**: 应用内存持续增长

**诊断**:

```rust
// 检查 Span 泄漏
use std::sync::atomic::{AtomicUsize, Ordering};

static ACTIVE_SPANS: AtomicUsize = AtomicUsize::new(0);

struct TrackedSpan {
    inner: Box<dyn opentelemetry::trace::Span>,
}

impl Drop for TrackedSpan {
    fn drop(&mut self) {
        ACTIVE_SPANS.fetch_sub(1, Ordering::Relaxed);
    }
}

// 定期检查
tokio::spawn(async {
    loop {
        let count = ACTIVE_SPANS.load(Ordering::Relaxed);
        println!("Active spans: {}", count);
        
        if count > 1000 {
            eprintln!("⚠️ Warning: {} active spans (possible leak)", count);
        }
        
        tokio::time::sleep(Duration::from_secs(10)).await;
    }
});
```

**解决方案**:

```rust
// 1. 确保 Span 正确结束
// ❌ 错误
let span = tracer.start("my-span");
// span 永远不会结束

// ✅ 正确
let span = tracer.start("my-span");
// ... 操作 ...
drop(span); // 显式结束

// 或使用 RAII
{
    let _span = tracer.start("my-span");
    // ... 操作 ...
} // 自动结束

// 2. 限制队列大小
let batch_config = BatchConfig::builder()
    .with_max_queue_size(1024) // 限制队列
    .build();
```

---

## 5. 编译错误

### 问题7: 依赖版本冲突

**症状**:

```text
error: failed to select a version for `opentelemetry`
```

**解决方案**:

```bash
# 1. 清理并更新
cargo clean
cargo update

# 2. 检查依赖树
cargo tree | grep opentelemetry

# 3. 统一版本
# Cargo.toml
[dependencies]
opentelemetry = "0.31.0"
opentelemetry_sdk = "0.31.0"
opentelemetry-otlp = "0.31.0"
tracing-opentelemetry = "0.31.0"
```

---

### 问题8: 特性标志错误

**症状**:

```text
error: cannot find function `build_span_exporter`
```

**解决方案**:

```toml
# 确保启用正确的 features
[dependencies]
opentelemetry-otlp = { version = "0.31.0", features = [
    "grpc-tonic",  # ✅ 必需
    "trace",       # ✅ 必需
] }
```

---

## 6. 运行时错误

### 问题9: Panic in tokio runtime

**症状**:

```text
thread 'tokio-runtime-worker' panicked at 'called `Result::unwrap()` on an `Err` value'
```

**解决方案**:

```rust
// ❌ 错误: 在异步上下文中 panic
#[tracing::instrument]
async fn my_function() {
    let result = risky_operation().await;
    result.unwrap(); // ❌ panic 会导致 tokio worker 崩溃
}

// ✅ 正确: 优雅处理错误
#[tracing::instrument(err)]
async fn my_function() -> Result<(), Box<dyn std::error::Error>> {
    let result = risky_operation().await?;
    Ok(())
}
```

---

## 7. 调试技巧

### 启用详细日志

```rust
// 环境变量
std::env::set_var("RUST_LOG", "trace");
std::env::set_var("OTEL_LOG_LEVEL", "debug");

// 或在启动时
// RUST_LOG=trace,opentelemetry=debug cargo run
```

### 自定义 Debug Exporter

```rust
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};

struct LoggingExporter;

#[async_trait::async_trait]
impl SpanExporter for LoggingExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::TraceResult<()> {
        for span in batch {
            println!("📊 Span Export:");
            println!("  Name: {}", span.name);
            println!("  Trace ID: {}", span.span_context.trace_id());
            println!("  Span ID: {}", span.span_context.span_id());
            println!("  Attributes: {:?}", span.attributes);
        }
        Ok(())
    }
}
```

---

## 8. 生产环境问题

### 问题10: 追踪数据丢失

**原因**:

- 应用退出过快
- 批处理未导出
- Collector 不可达

**解决方案**:

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let provider = init_telemetry().await?;
    
    // 应用逻辑
    let app = create_app();
    
    // 优雅关闭
    tokio::select! {
        _ = app.run() => {},
        _ = signal::ctrl_c() => {
            println!("Shutting down gracefully...");
        }
    }
    
    // 等待所有 span 导出
    println!("Flushing telemetry...");
    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
    
    provider.shutdown()?;
    
    println!("Shutdown complete");
    Ok(())
}
```

---

**相关文档**:

- [30分钟快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)
- [SDK最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
