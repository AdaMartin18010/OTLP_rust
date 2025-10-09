# SpanProcessor - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [SpanProcessor - Rust 完整实现指南](#spanprocessor---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 SpanProcessor](#11-什么是-spanprocessor)
    - [1.2 处理流程](#12-处理流程)
  - [2. SpanProcessor 接口](#2-spanprocessor-接口)
    - [2.1 Trait 定义](#21-trait-定义)
    - [2.2 生命周期回调](#22-生命周期回调)
  - [3. SimpleSpanProcessor](#3-simplespanprocessor)
    - [3.1 概述](#31-概述)
    - [3.2 基础用法](#32-基础用法)
    - [3.3 特点](#33-特点)
  - [4. BatchSpanProcessor](#4-batchspanprocessor)
    - [4.1 概述](#41-概述)
    - [4.2 基础配置](#42-基础配置)
    - [4.3 配置参数详解](#43-配置参数详解)
    - [4.4 触发导出的条件](#44-触发导出的条件)
    - [4.5 完整示例](#45-完整示例)
  - [5. 自定义 SpanProcessor](#5-自定义-spanprocessor)
    - [5.1 实现自定义 Processor](#51-实现自定义-processor)
    - [5.2 过滤 Span 的 Processor](#52-过滤-span-的-processor)
  - [6. 多 Processor 配置](#6-多-processor-配置)
    - [6.1 同时使用多个 Processor](#61-同时使用多个-processor)
    - [6.2 Processor 执行顺序](#62-processor-执行顺序)
  - [7. 完整示例](#7-完整示例)
    - [7.1 生产环境配置](#71-生产环境配置)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 Processor 选择](#81-processor-选择)
    - [8.2 配置建议](#82-配置建议)
    - [8.3 监控 Processor](#83-监控-processor)
    - [8.4 优雅关闭](#84-优雅关闭)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [推荐配置](#推荐配置)

---

## 1. 概述

### 1.1 什么是 SpanProcessor

`SpanProcessor` 是 Span 生命周期钩子，负责：

- **on_start**: Span 开始时的处理
- **on_end**: Span 结束时的处理（导出前）
- **force_flush**: 强制刷新待处理的 Span
- **shutdown**: 关闭并清理资源

### 1.2 处理流程

```text
Span.start()
   │
   ▼
┌──────────────────┐
│ on_start()       │ ← 可以修改 Span 属性
└────────┬─────────┘
         │
         │ (业务逻辑执行)
         │
         ▼
Span.end()
   │
   ▼
┌──────────────────┐
│ on_end()         │ ← 将 Span 发送给 Exporter
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│ SpanExporter     │ ← 导出到后端系统
└──────────────────┘
```

---

## 2. SpanProcessor 接口

### 2.1 Trait 定义

```rust
use opentelemetry::Context;
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry_sdk::trace::Span;

pub trait SpanProcessor: Send + Sync {
    /// Span 开始时调用
    fn on_start(&self, span: &mut Span, cx: &Context);
    
    /// Span 结束时调用
    fn on_end(&self, span: SpanData);
    
    /// 强制刷新所有待处理的 Span
    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()>;
    
    /// 关闭 Processor
    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()>;
}
```

### 2.2 生命周期回调

```rust
// 示例：SpanProcessor 生命周期
impl SpanProcessor for MyProcessor {
    fn on_start(&self, span: &mut Span, cx: &Context) {
        // Span 创建时：可以添加额外属性
        println!("Span started: {:?}", span.span_context().span_id());
    }
    
    fn on_end(&self, span: SpanData) {
        // Span 结束时：发送到 Exporter
        println!("Span ended: {:?}", span.span_context.span_id());
    }
    
    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        // 刷新所有待处理的 Span
        Ok(())
    }
    
    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        // 清理资源
        Ok(())
    }
}
```

---

## 3. SimpleSpanProcessor

### 3.1 概述

`SimpleSpanProcessor` **同步导出** Span，每个 Span 结束时立即导出。

**适用场景**：

- 测试环境
- 调试
- 低流量应用
- 需要实时导出的场景

**不适用于**：

- 生产环境高流量应用（性能开销大）

### 3.2 基础用法

```rust
use opentelemetry_sdk::trace::{SimpleSpanProcessor, TracerProvider};
use opentelemetry_sdk::export::trace::SpanExporter;

fn create_simple_processor(exporter: Box<dyn SpanExporter>) -> SimpleSpanProcessor {
    SimpleSpanProcessor::new(exporter)
}

fn setup_tracer_with_simple_processor() {
    let exporter = create_otlp_exporter();
    let processor = SimpleSpanProcessor::new(Box::new(exporter));
    
    let provider = TracerProvider::builder()
        .with_span_processor(processor)
        .build();
}
```

### 3.3 特点

```text
优点:
✅ 实时导出（Span 结束立即发送）
✅ 实现简单
✅ 适合调试
✅ 无需额外配置

缺点:
❌ 同步阻塞（影响应用性能）
❌ 每个 Span 一次网络调用（开销大）
❌ 不适合生产环境
```

---

## 4. BatchSpanProcessor

### 4.1 概述

`BatchSpanProcessor` **异步批量导出** Span，适合生产环境。

**工作原理**：

1. Span 结束时加入内存队列
2. 后台线程定期批量导出
3. 或队列满时触发导出

### 4.2 基础配置

```rust
use opentelemetry_sdk::trace::BatchSpanProcessor;
use opentelemetry_sdk::runtime::Tokio;
use std::time::Duration;

async fn create_batch_processor() -> anyhow::Result<BatchSpanProcessor> {
    let exporter = create_otlp_exporter().await?;
    
    let processor = BatchSpanProcessor::builder(exporter, Tokio)
        .with_max_queue_size(2048)                  // 队列最大容量
        .with_max_export_batch_size(512)            // 每批次最大 Span 数
        .with_scheduled_delay(Duration::from_millis(5000))  // 定时导出间隔
        .with_max_export_timeout(Duration::from_secs(30))   // 导出超时时间
        .build();
    
    Ok(processor)
}
```

### 4.3 配置参数详解

```rust
// 默认配置
BatchSpanProcessor::builder(exporter, runtime)
    .with_max_queue_size(2048)          // 队列大小（默认：2048）
    .with_max_export_batch_size(512)    // 批次大小（默认：512）
    .with_scheduled_delay(Duration::from_millis(5000))  // 延迟（默认：5秒）
    .with_max_export_timeout(Duration::from_secs(30))   // 超时（默认：30秒）
    .build();
```

| 参数 | 说明 | 默认值 | 推荐值 |
|------|------|--------|--------|
| `max_queue_size` | 内存队列容量 | 2048 | 2048-4096 |
| `max_export_batch_size` | 每批次 Span 数 | 512 | 256-1024 |
| `scheduled_delay` | 定时导出间隔 | 5s | 1s-10s |
| `max_export_timeout` | 导出超时 | 30s | 10s-60s |

### 4.4 触发导出的条件

```text
BatchSpanProcessor 在以下情况触发导出:

1. 定时触发: scheduled_delay 时间到达
2. 队列满: 队列中 Span 数达到 max_queue_size
3. 手动刷新: force_flush() 被调用
4. 关闭时: shutdown() 被调用
```

### 4.5 完整示例

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{TracerProvider, BatchSpanProcessor};
use opentelemetry_sdk::runtime::Tokio;
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1. 创建 OTLP 导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(3))
        .build_span_exporter()?;
    
    // 2. 创建 Batch Processor
    let processor = BatchSpanProcessor::builder(exporter, Tokio)
        .with_max_queue_size(4096)
        .with_max_export_batch_size(1024)
        .with_scheduled_delay(Duration::from_secs(2))
        .build();
    
    // 3. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_span_processor(processor)
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 4. 使用 Tracer
    let tracer = global::tracer("my-service");
    let span = tracer.start("my-operation");
    // ... 业务逻辑 ...
    drop(span);
    
    // 5. 优雅关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    Ok(())
}
```

---

## 5. 自定义 SpanProcessor

### 5.1 实现自定义 Processor

```rust
use opentelemetry::Context;
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry_sdk::trace::{Span, SpanProcessor};
use std::sync::atomic::{AtomicU64, Ordering};

pub struct MetricsSpanProcessor {
    span_count: AtomicU64,
    error_count: AtomicU64,
}

impl MetricsSpanProcessor {
    pub fn new() -> Self {
        Self {
            span_count: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
        }
    }
    
    pub fn get_span_count(&self) -> u64 {
        self.span_count.load(Ordering::Relaxed)
    }
    
    pub fn get_error_count(&self) -> u64 {
        self.error_count.load(Ordering::Relaxed)
    }
}

impl SpanProcessor for MetricsSpanProcessor {
    fn on_start(&self, _span: &mut Span, _cx: &Context) {
        // Span 开始时增加计数
        self.span_count.fetch_add(1, Ordering::Relaxed);
    }
    
    fn on_end(&self, span: SpanData) {
        // 检查是否有错误
        if !span.status.is_ok() {
            self.error_count.fetch_add(1, Ordering::Relaxed);
        }
    }
    
    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        // 无需刷新
        Ok(())
    }
    
    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        // 打印统计信息
        println!("Total spans: {}", self.get_span_count());
        println!("Total errors: {}", self.get_error_count());
        Ok(())
    }
}
```

### 5.2 过滤 Span 的 Processor

```rust
use opentelemetry::KeyValue;

pub struct FilteringSpanProcessor {
    inner: Box<dyn SpanProcessor>,
    filter_attribute: String,
}

impl FilteringSpanProcessor {
    pub fn new(inner: Box<dyn SpanProcessor>, filter_attr: String) -> Self {
        Self {
            inner,
            filter_attribute: filter_attr,
        }
    }
}

impl SpanProcessor for FilteringSpanProcessor {
    fn on_start(&self, span: &mut Span, cx: &Context) {
        self.inner.on_start(span, cx);
    }
    
    fn on_end(&self, span: SpanData) {
        // 只处理包含特定属性的 Span
        if span.attributes.iter().any(|(k, _)| k.as_str() == self.filter_attribute) {
            self.inner.on_end(span);
        }
        // 否则丢弃 Span
    }
    
    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.force_flush()
    }
    
    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.shutdown()
    }
}
```

---

## 6. 多 Processor 配置

### 6.1 同时使用多个 Processor

```rust
fn setup_multiple_processors() -> anyhow::Result<TracerProvider> {
    // Processor 1: OTLP 导出器（批量）
    let otlp_exporter = create_otlp_exporter()?;
    let otlp_processor = BatchSpanProcessor::builder(otlp_exporter, Tokio).build();
    
    // Processor 2: Jaeger 导出器（批量）
    let jaeger_exporter = create_jaeger_exporter()?;
    let jaeger_processor = BatchSpanProcessor::builder(jaeger_exporter, Tokio).build();
    
    // Processor 3: 日志导出器（简单）
    let stdout_exporter = create_stdout_exporter();
    let stdout_processor = SimpleSpanProcessor::new(Box::new(stdout_exporter));
    
    // Processor 4: 自定义指标 Processor
    let metrics_processor = MetricsSpanProcessor::new();
    
    // 组合所有 Processor
    let provider = TracerProvider::builder()
        .with_span_processor(otlp_processor)
        .with_span_processor(jaeger_processor)
        .with_span_processor(stdout_processor)
        .with_span_processor(metrics_processor)
        .build();
    
    Ok(provider)
}
```

### 6.2 Processor 执行顺序

```text
Span.start()
   │
   ├─> Processor 1: on_start()
   ├─> Processor 2: on_start()
   ├─> Processor 3: on_start()
   └─> Processor 4: on_start()
       │
       │ (业务逻辑)
       │
Span.end()
   │
   ├─> Processor 1: on_end()
   ├─> Processor 2: on_end()
   ├─> Processor 3: on_end()
   └─> Processor 4: on_end()

注意：on_end() 按添加顺序**依次执行**（阻塞）
```

---

## 7. 完整示例

### 7.1 生产环境配置

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{TracerProvider, BatchSpanProcessor, Config, Sampler};
use opentelemetry_sdk::Resource;
use opentelemetry::KeyValue;
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Resource 配置
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-production-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);
    
    // OTLP 导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://otel-collector:4317")
        .with_timeout(Duration::from_secs(3))
        .build_span_exporter()?;
    
    // Batch Processor（生产级配置）
    let batch_processor = BatchSpanProcessor::builder(
        otlp_exporter,
        opentelemetry_sdk::runtime::Tokio
    )
    .with_max_queue_size(4096)
    .with_max_export_batch_size(1024)
    .with_scheduled_delay(Duration::from_secs(2))
    .with_max_export_timeout(Duration::from_secs(30))
    .build();
    
    // TracerProvider
    let provider = TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1))))
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
        )
        .with_resource(resource)
        .with_span_processor(batch_processor)
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 运行应用
    run_application().await?;
    
    // 优雅关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    Ok(())
}

async fn run_application() -> anyhow::Result<()> {
    let tracer = global::tracer("my-service");
    
    for i in 0..1000 {
        let span = tracer.start(format!("operation-{}", i));
        tokio::time::sleep(Duration::from_millis(10)).await;
        drop(span);
    }
    
    Ok(())
}
```

---

## 8. 最佳实践

### 8.1 Processor 选择

```text
测试/调试环境:
✅ SimpleSpanProcessor
  - 实时导出，便于调试
  - StdoutExporter 配合使用

生产环境:
✅ BatchSpanProcessor
  - 高性能异步导出
  - 合理配置队列和批次大小
```

### 8.2 配置建议

```rust
// 低流量应用（< 100 QPS）
BatchSpanProcessor::builder(exporter, Tokio)
    .with_max_queue_size(1024)
    .with_max_export_batch_size(256)
    .with_scheduled_delay(Duration::from_secs(5))
    .build();

// 中流量应用（100-1000 QPS）
BatchSpanProcessor::builder(exporter, Tokio)
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(Duration::from_secs(2))
    .build();

// 高流量应用（> 1000 QPS）
BatchSpanProcessor::builder(exporter, Tokio)
    .with_max_queue_size(4096)
    .with_max_export_batch_size(1024)
    .with_scheduled_delay(Duration::from_secs(1))
    .build();
```

### 8.3 监控 Processor

```rust
// 添加监控 Processor 统计指标
pub struct MonitoredProcessor {
    inner: Box<dyn SpanProcessor>,
    queue_size: Arc<AtomicUsize>,
}

impl SpanProcessor for MonitoredProcessor {
    fn on_end(&self, span: SpanData) {
        self.queue_size.fetch_add(1, Ordering::Relaxed);
        self.inner.on_end(span);
        self.queue_size.fetch_sub(1, Ordering::Relaxed);
    }
    
    // ... 其他方法 ...
}
```

### 8.4 优雅关闭

```rust
async fn graceful_shutdown(provider: TracerProvider) -> anyhow::Result<()> {
    // 1. 停止接收新请求
    // ...
    
    // 2. 等待现有请求完成
    tokio::time::sleep(Duration::from_secs(5)).await;
    
    // 3. 刷新所有待处理的 Span
    provider.force_flush()?;
    
    // 4. 关闭 TracerProvider
    provider.shutdown()?;
    
    Ok(())
}
```

---

## 总结

### 核心要点

1. **SimpleSpanProcessor**: 同步导出，适合测试
2. **BatchSpanProcessor**: 异步批量导出，适合生产
3. **自定义 Processor**: 实现 SpanProcessor trait
4. **多 Processor**: 可同时使用多个 Processor
5. **优雅关闭**: 必须调用 `force_flush()` 和 `shutdown()`

### 推荐配置

```rust
// 生产环境推荐配置
BatchSpanProcessor::builder(exporter, Tokio)
    .with_max_queue_size(4096)
    .with_max_export_batch_size(1024)
    .with_scheduled_delay(Duration::from_secs(2))
    .with_max_export_timeout(Duration::from_secs(30))
    .build()
```

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
