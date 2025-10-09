# TracerProvider - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [TracerProvider - Rust 完整实现指南](#tracerprovider---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 TracerProvider](#11-什么是-tracerprovider)
    - [1.2 架构图](#12-架构图)
    - [1.3 Rust SDK 依赖](#13-rust-sdk-依赖)
  - [2. TracerProvider 核心概念](#2-tracerprovider-核心概念)
    - [2.1 核心接口](#21-核心接口)
    - [2.2 SDK 实现](#22-sdk-实现)
    - [2.3 生命周期状态](#23-生命周期状态)
  - [3. 构建 TracerProvider](#3-构建-tracerprovider)
    - [3.1 基础构建](#31-基础构建)
      - [方法 1: 使用构建器模式](#方法-1-使用构建器模式)
      - [方法 2: 使用默认配置](#方法-2-使用默认配置)
    - [3.2 完整构建示例](#32-完整构建示例)
  - [4. Tracer 创建与管理](#4-tracer-创建与管理)
    - [4.1 创建命名 Tracer](#41-创建命名-tracer)
    - [4.2 Tracer 命名规范](#42-tracer-命名规范)
    - [4.3 Tracer 缓存](#43-tracer-缓存)
  - [5. Resource 配置](#5-resource-配置)
    - [5.1 Resource 概念](#51-resource-概念)
    - [5.2 基础 Resource 配置](#52-基础-resource-配置)
    - [5.3 检测器自动填充](#53-检测器自动填充)
    - [5.4 Resource 合并规则](#54-resource-合并规则)
  - [6. Span Processor 配置](#6-span-processor-配置)
    - [6.1 Span Processor 类型](#61-span-processor-类型)
      - [Simple Span Processor](#simple-span-processor)
      - [Batch Span Processor](#batch-span-processor)
    - [6.2 多 Processor 配置](#62-多-processor-配置)
    - [6.3 自定义 Span Processor](#63-自定义-span-processor)
  - [7. Sampler 配置](#7-sampler-配置)
    - [7.1 内置 Sampler 类型](#71-内置-sampler-类型)
      - [AlwaysOn / AlwaysOff](#alwayson--alwaysoff)
      - [TraceIdRatioBased (概率采样)](#traceidratiobased-概率采样)
      - [ParentBased (父 Span 决定)](#parentbased-父-span-决定)
    - [7.2 自定义 Sampler](#72-自定义-sampler)
  - [8. 生命周期管理](#8-生命周期管理)
    - [8.1 初始化](#81-初始化)
    - [8.2 优雅关闭](#82-优雅关闭)
    - [8.3 超时控制](#83-超时控制)
  - [9. 全局 TracerProvider](#9-全局-tracerprovider)
    - [9.1 设置全局 Provider](#91-设置全局-provider)
    - [9.2 获取全局 Tracer](#92-获取全局-tracer)
    - [9.3 全局 Provider 的问题](#93-全局-provider-的问题)
  - [10. 完整示例](#10-完整示例)
    - [10.1 生产环境完整示例](#101-生产环境完整示例)
    - [10.2 测试环境示例](#102-测试环境示例)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 初始化](#111-初始化)
    - [11.2 Resource 配置](#112-resource-配置)
    - [11.3 Sampling 策略](#113-sampling-策略)
    - [11.4 关闭管理](#114-关闭管理)
  - [12. 故障排查](#12-故障排查)
    - [12.1 常见问题](#121-常见问题)
      - [问题 1: Span 没有被导出](#问题-1-span-没有被导出)
      - [问题 2: 全局 TracerProvider 无法 shutdown](#问题-2-全局-tracerprovider-无法-shutdown)
      - [问题 3: Resource 属性没有生效](#问题-3-resource-属性没有生效)
    - [12.2 调试技巧](#122-调试技巧)
      - [启用 OpenTelemetry 日志](#启用-opentelemetry-日志)
      - [使用 SimpleSpanProcessor 测试](#使用-simplespanprocessor-测试)
      - [检查 Span 是否被采样](#检查-span-是否被采样)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [推荐配置模板](#推荐配置模板)

---

## 1. 概述

### 1.1 什么是 TracerProvider

`TracerProvider` 是 OpenTelemetry SDK 的核心组件，负责：

- **创建 Tracer 实例**：为应用程序的不同组件提供 Tracer
- **管理全局配置**：Resource、Sampler、SpanProcessor
- **生命周期管理**：初始化、关闭、资源清理
- **上下文传播**：与 Context Propagator 集成

### 1.2 架构图

```text
┌─────────────────────────────────────────────────────────┐
│                    TracerProvider                        │
│ ┌─────────────────────────────────────────────────────┐ │
│ │  Resource (service.name, service.version, etc.)     │ │
│ └─────────────────────────────────────────────────────┘ │
│ ┌─────────────────────────────────────────────────────┐ │
│ │  Sampler (AlwaysOn, AlwaysOff, Probability, etc.)   │ │
│ └─────────────────────────────────────────────────────┘ │
│ ┌─────────────────────────────────────────────────────┐ │
│ │  SpanProcessor (Batch, Simple)                      │ │
│ │    └─> SpanExporter (OTLP, Jaeger, Zipkin)          │ │
│ └─────────────────────────────────────────────────────┘ │
│                                                          │
│  getTracer(name, version) ──> Tracer Instance           │
└─────────────────────────────────────────────────────────┘
```

### 1.3 Rust SDK 依赖

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = "0.31.0"

# OTLP 导出器
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }

# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# 日志与追踪
tracing = "0.1"
tracing-opentelemetry = "0.32"
```

---

## 2. TracerProvider 核心概念

### 2.1 核心接口

```rust
use opentelemetry::trace::{TracerProvider, Tracer};

pub trait TracerProvider {
    type Tracer: Tracer + Send + Sync;
    
    /// 创建或返回一个命名的 Tracer
    fn tracer(&self, name: impl Into<Cow<'static, str>>) -> Self::Tracer;
    
    /// 创建带版本和 schema_url 的 Tracer
    fn versioned_tracer(
        &self,
        name: impl Into<Cow<'static, str>>,
        version: Option<&'static str>,
        schema_url: Option<&'static str>,
        attributes: Option<Vec<KeyValue>>,
    ) -> Self::Tracer;
}
```

### 2.2 SDK 实现

```rust
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;

pub struct SdkTracerProvider {
    inner: Arc<TracerProviderInner>,
}

struct TracerProviderInner {
    resource: Resource,
    config: Config,
    span_processors: Vec<Box<dyn SpanProcessor>>,
    is_shutdown: AtomicBool,
}
```

### 2.3 生命周期状态

```rust
pub enum ProviderState {
    Active,      // 正常运行状态
    ShuttingDown, // 正在关闭
    Shutdown,    // 已关闭
}
```

---

## 3. 构建 TracerProvider

### 3.1 基础构建

#### 方法 1: 使用构建器模式

```rust
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_sdk::trace::{Config, Sampler};
use opentelemetry_sdk::Resource;

fn create_tracer_provider() -> SdkTracerProvider {
    SdkTracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
        )
        .with_resource(Resource::default())
        .build()
}
```

#### 方法 2: 使用默认配置

```rust
fn create_default_provider() -> SdkTracerProvider {
    SdkTracerProvider::builder()
        .build()
}
```

### 3.2 完整构建示例

```rust
use opentelemetry::KeyValue;
use opentelemetry_sdk::trace::{BatchSpanProcessor, Config, Sampler};
use opentelemetry_sdk::Resource;
use opentelemetry_otlp::{WithExportConfig, TonicExporterBuilder};
use std::time::Duration;

async fn create_production_provider() -> anyhow::Result<SdkTracerProvider> {
    // 1. 配置 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);
    
    // 2. 创建 OTLP 导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(3))
        .build_span_exporter()?;
    
    // 3. 配置 Batch Processor
    let batch_processor = BatchSpanProcessor::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_millis(500))
        .with_max_export_timeout(Duration::from_secs(30))
        .build();
    
    // 4. 构建 TracerProvider
    let provider = SdkTracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1))))
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
                .with_max_links_per_span(128)
        )
        .with_resource(resource)
        .with_span_processor(batch_processor)
        .build();
    
    Ok(provider)
}
```

---

## 4. Tracer 创建与管理

### 4.1 创建命名 Tracer

```rust
use opentelemetry::trace::TracerProvider;

fn create_tracers(provider: &SdkTracerProvider) {
    // 简单创建
    let tracer1 = provider.tracer("my-component");
    
    // 带版本创建
    let tracer2 = provider.versioned_tracer(
        "my-component",
        Some("1.0.0"),
        None,
        None,
    );
    
    // 带所有元数据
    let tracer3 = provider.versioned_tracer(
        "my-component",
        Some("1.0.0"),
        Some("https://opentelemetry.io/schemas/1.21.0"),
        Some(vec![
            KeyValue::new("component.type", "http-server"),
        ]),
    );
}
```

### 4.2 Tracer 命名规范

```rust
// ✅ 推荐：使用库名或模块名
let tracer = provider.tracer("opentelemetry-rust");

// ✅ 推荐：带版本
let tracer = provider.versioned_tracer(
    "opentelemetry-rust",
    Some(env!("CARGO_PKG_VERSION")),
    None,
    None,
);

// ❌ 不推荐：使用类名或函数名
let tracer = provider.tracer("MyClass");
```

### 4.3 Tracer 缓存

SDK 会自动缓存同名 Tracer：

```rust
// 这两个调用返回相同的 Tracer 实例
let tracer1 = provider.tracer("my-component");
let tracer2 = provider.tracer("my-component");

assert!(Arc::ptr_eq(
    &tracer1 as &Arc<_>,
    &tracer2 as &Arc<_>
));
```

---

## 5. Resource 配置

### 5.1 Resource 概念

Resource 描述了产生遥测数据的实体（服务、主机、容器等）。

### 5.2 基础 Resource 配置

```rust
use opentelemetry::KeyValue;
use opentelemetry_sdk::Resource;

fn create_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("service.namespace", "production"),
        KeyValue::new("deployment.environment", "production"),
    ])
}
```

### 5.3 检测器自动填充

```rust
use opentelemetry_sdk::resource::{
    EnvResourceDetector,
    OsResourceDetector,
    ProcessResourceDetector,
    ResourceDetector,
};

async fn create_auto_detected_resource() -> Resource {
    let mut resource = Resource::default();
    
    // 从环境变量检测
    resource = resource.merge(&EnvResourceDetector::new().detect(Duration::from_secs(0)));
    
    // 从操作系统检测
    resource = resource.merge(&OsResourceDetector.detect(Duration::from_secs(0)));
    
    // 从进程信息检测
    resource = resource.merge(&ProcessResourceDetector.detect(Duration::from_secs(0)));
    
    // 合并自定义属性
    resource = resource.merge(&Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
    ]));
    
    resource
}
```

### 5.4 Resource 合并规则

```rust
// 右侧的 Resource 覆盖左侧相同 key 的值
let r1 = Resource::new(vec![
    KeyValue::new("service.name", "service1"),
    KeyValue::new("host.name", "host1"),
]);

let r2 = Resource::new(vec![
    KeyValue::new("service.name", "service2"),  // 覆盖
]);

let merged = r1.merge(&r2);
// 结果：service.name=service2, host.name=host1
```

---

## 6. Span Processor 配置

### 6.1 Span Processor 类型

#### Simple Span Processor

同步导出，适合测试：

```rust
use opentelemetry_sdk::trace::{SimpleSpanProcessor};

let simple_processor = SimpleSpanProcessor::new(Box::new(exporter));
```

#### Batch Span Processor

异步批量导出，适合生产：

```rust
use opentelemetry_sdk::trace::BatchSpanProcessor;

let batch_processor = BatchSpanProcessor::builder(exporter, opentelemetry_sdk::runtime::Tokio)
    .with_max_queue_size(2048)              // 队列大小
    .with_max_export_batch_size(512)        // 批次大小
    .with_scheduled_delay(Duration::from_millis(5000))  // 延迟
    .with_max_export_timeout(Duration::from_secs(30))   // 超时
    .build();
```

### 6.2 多 Processor 配置

```rust
let provider = SdkTracerProvider::builder()
    .with_span_processor(batch_processor1)  // OTLP 导出器
    .with_span_processor(batch_processor2)  // Jaeger 导出器
    .with_span_processor(simple_processor)  // 日志导出器
    .build();
```

### 6.3 自定义 Span Processor

```rust
use opentelemetry::trace::SpanContext;
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry_sdk::trace::SpanProcessor;

struct CustomProcessor;

impl SpanProcessor for CustomProcessor {
    fn on_start(&self, span: &mut opentelemetry_sdk::trace::Span, cx: &opentelemetry::Context) {
        // Span 开始时的处理
        println!("Span started: {:?}", span.span_context().trace_id());
    }
    
    fn on_end(&self, span: SpanData) {
        // Span 结束时的处理
        println!("Span ended: {:?}", span.span_context.trace_id());
    }
    
    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        // 强制刷新
        Ok(())
    }
    
    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        // 关闭清理
        Ok(())
    }
}
```

---

## 7. Sampler 配置

### 7.1 内置 Sampler 类型

#### AlwaysOn / AlwaysOff

```rust
use opentelemetry_sdk::trace::Sampler;

// 总是采样
let sampler = Sampler::AlwaysOn;

// 从不采样
let sampler = Sampler::AlwaysOff;
```

#### TraceIdRatioBased (概率采样)

```rust
// 采样 10% 的 Trace
let sampler = Sampler::TraceIdRatioBased(0.1);
```

#### ParentBased (父 Span 决定)

```rust
// 如果父 Span 采样，则采样；否则使用 TraceIdRatioBased(0.1)
let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));
```

### 7.2 自定义 Sampler

```rust
use opentelemetry::trace::{SamplingDecision, SamplingResult, SpanKind, TraceContextExt};
use opentelemetry_sdk::trace::{Sampler, ShouldSample};

struct RateLimitingSampler {
    rate_limiter: Arc<Mutex<RateLimiter>>,
}

impl ShouldSample for RateLimitingSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        let mut limiter = self.rate_limiter.lock().unwrap();
        
        if limiter.allow() {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        }
    }
}
```

---

## 8. 生命周期管理

### 8.1 初始化

```rust
async fn initialize_tracing() -> anyhow::Result<SdkTracerProvider> {
    let provider = create_production_provider().await?;
    
    // 设置为全局 TracerProvider
    opentelemetry::global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}
```

### 8.2 优雅关闭

```rust
async fn shutdown_tracing(provider: SdkTracerProvider) -> anyhow::Result<()> {
    use opentelemetry::global;
    
    // 1. 刷新所有待处理的 Span
    provider.force_flush()?;
    
    // 2. 关闭 TracerProvider
    provider.shutdown()?;
    
    // 3. 重置全局 TracerProvider
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 8.3 超时控制

```rust
use tokio::time::timeout;

async fn shutdown_with_timeout(provider: SdkTracerProvider, timeout_duration: Duration) -> anyhow::Result<()> {
    timeout(timeout_duration, async {
        provider.force_flush()?;
        provider.shutdown()?;
        Ok::<(), anyhow::Error>(())
    })
    .await??;
    
    Ok(())
}
```

---

## 9. 全局 TracerProvider

### 9.1 设置全局 Provider

```rust
use opentelemetry::global;

async fn setup_global_provider() -> anyhow::Result<()> {
    let provider = create_production_provider().await?;
    
    // 设置全局 TracerProvider
    global::set_tracer_provider(provider);
    
    Ok(())
}
```

### 9.2 获取全局 Tracer

```rust
use opentelemetry::global;

fn get_tracer() -> impl opentelemetry::trace::Tracer {
    global::tracer("my-component")
}
```

### 9.3 全局 Provider 的问题

```rust
// ⚠️ 注意：全局 Provider 无法直接 shutdown
// 因为返回类型是 GenericTracerProvider，不是 SdkTracerProvider

// ✅ 解决方案：保留 SdkTracerProvider 的引用
let provider = create_production_provider().await?;
let provider_clone = provider.clone();

global::set_tracer_provider(provider);

// 关闭时使用保留的引用
provider_clone.shutdown()?;
```

---

## 10. 完整示例

### 10.1 生产环境完整示例

```rust
use opentelemetry::trace::{TracerProvider, Tracer};
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::{BatchSpanProcessor, Config, Sampler};
use opentelemetry_sdk::Resource;
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", std::env::var("ENV").unwrap_or_else(|_| "development".into())),
    ]);
    
    // 2. 创建 OTLP 导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(3))
        .build_span_exporter()?;
    
    // 3. 创建 Batch Processor
    let batch_processor = BatchSpanProcessor::builder(
        otlp_exporter,
        opentelemetry_sdk::runtime::Tokio
    )
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(Duration::from_millis(500))
    .build();
    
    // 4. 构建 TracerProvider
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1))))
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
        )
        .with_resource(resource)
        .with_span_processor(batch_processor)
        .build();
    
    // 5. 设置全局 TracerProvider
    global::set_tracer_provider(provider.clone());
    
    // 6. 集成 tracing-opentelemetry
    let tracer = global::tracer("my-rust-service");
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    // 7. 运行应用
    run_application().await?;
    
    // 8. 优雅关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    Ok(())
}

#[tracing::instrument]
async fn run_application() -> anyhow::Result<()> {
    tracing::info!("Application started");
    
    // 应用逻辑
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    tracing::info!("Application finished");
    Ok(())
}
```

### 10.2 测试环境示例

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::trace::SimpleSpanProcessor;
    use opentelemetry_sdk::testing::trace::InMemorySpanExporter;
    
    #[tokio::test]
    async fn test_with_in_memory_exporter() {
        // 使用内存导出器进行测试
        let exporter = InMemorySpanExporter::default();
        let exporter_clone = exporter.clone();
        
        let provider = opentelemetry_sdk::trace::TracerProvider::builder()
            .with_simple_span_processor(exporter)
            .build();
        
        let tracer = provider.tracer("test");
        
        // 创建 Span
        let span = tracer.start("test-span");
        drop(span);
        
        // 验证导出的 Span
        let exported_spans = exporter_clone.get_finished_spans().unwrap();
        assert_eq!(exported_spans.len(), 1);
        assert_eq!(exported_spans[0].name, "test-span");
    }
}
```

---

## 11. 最佳实践

### 11.1 初始化

✅ **应用启动时尽早初始化**

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 第一步：初始化追踪
    let provider = initialize_tracing().await?;
    
    // 第二步：运行应用
    run_app().await?;
    
    // 第三步：关闭
    shutdown_tracing(provider).await?;
    
    Ok(())
}
```

✅ **使用环境变量配置**

```rust
let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
    .unwrap_or_else(|_| "http://localhost:4317".to_string());
```

### 11.2 Resource 配置

✅ **始终设置 service.name**

```rust
let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"), // 必需
]);
```

✅ **使用语义约定**

```rust
use opentelemetry_semantic_conventions as semconv;

let resource = Resource::new(vec![
    KeyValue::new(semconv::resource::SERVICE_NAME, "my-service"),
    KeyValue::new(semconv::resource::SERVICE_VERSION, "1.0.0"),
]);
```

### 11.3 Sampling 策略

✅ **生产环境使用 ParentBased + Ratio**

```rust
let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));
```

✅ **开发环境使用 AlwaysOn**

```rust
let sampler = if cfg!(debug_assertions) {
    Sampler::AlwaysOn
} else {
    Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))
};
```

### 11.4 关闭管理

✅ **使用 RAII 模式**

```rust
struct TracingGuard {
    provider: SdkTracerProvider,
}

impl Drop for TracingGuard {
    fn drop(&mut self) {
        let _ = self.provider.force_flush();
        let _ = self.provider.shutdown();
    }
}
```

---

## 12. 故障排查

### 12.1 常见问题

#### 问题 1: Span 没有被导出

**原因**：忘记调用 `force_flush()` 或 `shutdown()`

**解决**：

```rust
provider.force_flush()?;
provider.shutdown()?;
```

#### 问题 2: 全局 TracerProvider 无法 shutdown

**原因**：`global::tracer_provider()` 返回的是 trait 对象

**解决**：

```rust
let provider = create_provider().await?;
let provider_clone = provider.clone();
global::set_tracer_provider(provider);

// 使用 clone 来 shutdown
provider_clone.shutdown()?;
```

#### 问题 3: Resource 属性没有生效

**原因**：Resource 设置在 SpanProcessor 之后

**解决**：

```rust
// ✅ 正确顺序
let provider = SdkTracerProvider::builder()
    .with_resource(resource)           // 先设置 Resource
    .with_span_processor(processor)    // 再设置 Processor
    .build();
```

### 12.2 调试技巧

#### 启用 OpenTelemetry 日志

```rust
std::env::set_var("OTEL_LOG_LEVEL", "debug");
```

#### 使用 SimpleSpanProcessor 测试

```rust
let provider = SdkTracerProvider::builder()
    .with_simple_span_processor(exporter)  // 同步导出，便于调试
    .build();
```

#### 检查 Span 是否被采样

```rust
let span = tracer.start("test");
if span.span_context().is_sampled() {
    println!("Span is sampled");
} else {
    println!("Span is NOT sampled");
}
```

---

## 总结

### 核心要点

1. **TracerProvider 是 SDK 的入口**：负责创建 Tracer、管理全局配置
2. **Resource 描述服务身份**：必须设置 `service.name`
3. **Sampler 控制采样率**：生产环境推荐 `ParentBased + TraceIdRatioBased`
4. **SpanProcessor 控制导出**：生产环境推荐 `BatchSpanProcessor`
5. **优雅关闭很重要**：必须调用 `force_flush()` 和 `shutdown()`

### 推荐配置模板

```rust
async fn create_recommended_provider() -> anyhow::Result<SdkTracerProvider> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let processor = BatchSpanProcessor::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_max_queue_size(2048)
        .with_scheduled_delay(Duration::from_millis(500))
        .build();
    
    let provider = SdkTracerProvider::builder()
        .with_config(Config::default()
            .with_sampler(Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))))
        .with_resource(resource)
        .with_span_processor(processor)
        .build();
    
    Ok(provider)
}
```

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
