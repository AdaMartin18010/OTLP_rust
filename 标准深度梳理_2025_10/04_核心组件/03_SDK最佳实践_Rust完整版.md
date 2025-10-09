# OpenTelemetry SDK 最佳实践 - Rust 1.90 完整指南

> **Rust版本**: 1.90+  
> **OpenTelemetry SDK**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月9日  
> **文档状态**: ✅ 生产就绪

---

## 目录

- [OpenTelemetry SDK 最佳实践 - Rust 1.90 完整指南](#opentelemetry-sdk-最佳实践---rust-190-完整指南)
  - [目录](#目录)
  - [1. SDK初始化最佳实践](#1-sdk初始化最佳实践)
    - [1.1 异步初始化模式](#11-异步初始化模式)
    - [1.2 同步初始化模式](#12-同步初始化模式)
    - [1.3 延迟初始化](#13-延迟初始化)
  - [2. Resource配置](#2-resource配置)
    - [2.1 自动Resource检测](#21-自动resource检测)
    - [2.2 自定义Resource](#22-自定义resource)
  - [3. TracerProvider配置](#3-tracerprovider配置)
    - [3.1 批处理配置](#31-批处理配置)
    - [3.2 采样配置](#32-采样配置)
    - [3.3 多Exporter配置](#33-多exporter配置)
  - [4. 异步追踪最佳实践](#4-异步追踪最佳实践)
    - [4.1 Async Fn追踪](#41-async-fn追踪)
    - [4.2 Stream追踪](#42-stream追踪)
    - [4.3 Future组合](#43-future组合)
  - [5. 错误处理](#5-错误处理)
    - [5.1 错误记录](#51-错误记录)
    - [5.2 Panic处理](#52-panic处理)
  - [6. 性能优化](#6-性能优化)
    - [6.1 零分配追踪](#61-零分配追踪)
    - [6.2 对象池](#62-对象池)
    - [6.3 批处理优化](#63-批处理优化)
  - [7. 内存管理](#7-内存管理)
    - [7.1 Arc vs Clone](#71-arc-vs-clone)
    - [7.2 生命周期管理](#72-生命周期管理)
  - [8. 生产环境配置](#8-生产环境配置)
    - [8.1 优雅关闭](#81-优雅关闭)
    - [8.2 监控集成](#82-监控集成)
  - [9. 测试最佳实践](#9-测试最佳实践)
  - [10. 故障排查](#10-故障排查)

---

## 1. SDK初始化最佳实践

### 1.1 异步初始化模式

**推荐的异步初始化**:

```rust
use opentelemetry::{global, trace::TracerProvider as _};
use opentelemetry_sdk::{
    trace::{self, TracerProvider, BatchConfig},
    Resource,
};
use opentelemetry_otlp::{WithExportConfig, Protocol};
use std::time::Duration;

/// 初始化OpenTelemetry (异步)
pub async fn init_telemetry() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. 配置Resource
    let resource = Resource::builder()
        .with_service_name("my-service")
        .with_service_version(env!("CARGO_PKG_VERSION"))
        .with_schema_url(opentelemetry_semantic_conventions::SCHEMA_URL)
        .build();
    
    // 2. 配置OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(30))
        .with_protocol(Protocol::Grpc)
        .build_span_exporter()?;
    
    // 3. 配置BatchProcessor
    let batch_config = BatchConfig::default()
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5));
    
    // 4. 构建TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_resource(resource)
        .with_config(trace::Config::default())
        .build();
    
    // 5. 设置全局Provider
    global::set_tracer_provider(provider.clone());
    
    tracing::info!("OpenTelemetry initialized successfully");
    
    Ok(provider)
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化tracing-subscriber
    tracing_subscriber::fmt::init();
    
    // 初始化OpenTelemetry
    let provider = init_telemetry().await?;
    
    // 应用逻辑
    run_application().await?;
    
    // 优雅关闭
    provider.shutdown()?;
    
    Ok(())
}
```

### 1.2 同步初始化模式

**阻塞式初始化 (适用于main函数)**:

```rust
use opentelemetry_sdk::runtime;

pub fn init_telemetry_sync() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    let resource = Resource::builder()
        .with_service_name("my-service")
        .build();
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let provider = TracerProvider::builder()
        .with_simple_exporter(exporter)  // 注意：使用simple而非batch
        .with_resource(resource)
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}
```

### 1.3 延迟初始化

**Lazy Static + OnceCell**:

```rust
use once_cell::sync::OnceCell;
use std::sync::Arc;

static TRACER_PROVIDER: OnceCell<Arc<TracerProvider>> = OnceCell::new();

pub fn get_tracer_provider() -> Arc<TracerProvider> {
    TRACER_PROVIDER
        .get_or_init(|| {
            let provider = init_telemetry_sync()
                .expect("Failed to initialize telemetry");
            Arc::new(provider)
        })
        .clone()
}

/// 使用
pub fn get_tracer(name: &str) -> opentelemetry::trace::Tracer {
    get_tracer_provider().tracer(name)
}
```

---

## 2. Resource配置

### 2.1 自动Resource检测

**使用ResourceDetector**:

```rust
use opentelemetry_sdk::resource::{
    EnvResourceDetector,
    OsResourceDetector,
    ProcessResourceDetector,
    ResourceDetector,
};

pub async fn detect_resource() -> Resource {
    // 1. 环境变量检测
    let env_resource = EnvResourceDetector::new()
        .detect(Duration::from_secs(5));
    
    // 2. 操作系统信息
    let os_resource = OsResourceDetector
        .detect(Duration::from_secs(5));
    
    // 3. 进程信息
    let process_resource = ProcessResourceDetector
        .detect(Duration::from_secs(5));
    
    // 4. 合并Resource
    let base_resource = Resource::builder()
        .with_service_name("my-service")
        .build();
    
    base_resource
        .merge(&env_resource)
        .merge(&os_resource)
        .merge(&process_resource)
}
```

### 2.2 自定义Resource

**添加自定义属性**:

```rust
use opentelemetry::KeyValue;

pub fn build_custom_resource() -> Resource {
    Resource::builder()
        // 服务信息
        .with_service_name("payment-service")
        .with_service_version("1.2.3")
        .with_service_namespace("production")
        .with_service_instance_id("instance-123")
        
        // 部署信息
        .with_attributes([
            KeyValue::new("deployment.environment", "production"),
            KeyValue::new("cloud.provider", "aws"),
            KeyValue::new("cloud.region", "us-east-1"),
            KeyValue::new("cloud.availability_zone", "us-east-1a"),
            KeyValue::new("k8s.cluster.name", "prod-cluster"),
            KeyValue::new("k8s.namespace.name", "payment"),
            KeyValue::new("k8s.pod.name", std::env::var("HOSTNAME").unwrap_or_default()),
        ])
        
        // 自定义标签
        .with_attributes([
            KeyValue::new("team", "platform"),
            KeyValue::new("cost.center", "engineering"),
        ])
        
        .build()
}
```

---

## 3. TracerProvider配置

### 3.1 批处理配置

**优化的批处理配置**:

```rust
use opentelemetry_sdk::trace::BatchConfig;

/// 生产环境配置
pub fn production_batch_config() -> BatchConfig {
    BatchConfig::default()
        // 最大队列大小 (建议 1k-10k)
        .with_max_queue_size(4096)
        
        // 批次大小 (建议 100-1k)
        .with_max_export_batch_size(512)
        
        // 调度延迟 (建议 5-30s)
        .with_scheduled_delay(Duration::from_secs(10))
        
        // 导出超时 (建议 30-120s)
        .with_max_export_timeout(Duration::from_secs(60))
}

/// 低延迟配置
pub fn low_latency_batch_config() -> BatchConfig {
    BatchConfig::default()
        .with_max_queue_size(1024)
        .with_max_export_batch_size(128)
        .with_scheduled_delay(Duration::from_secs(1))
        .with_max_export_timeout(Duration::from_secs(10))
}

/// 高吞吐配置
pub fn high_throughput_batch_config() -> BatchConfig {
    BatchConfig::default()
        .with_max_queue_size(10000)
        .with_max_export_batch_size(2048)
        .with_scheduled_delay(Duration::from_secs(30))
        .with_max_export_timeout(Duration::from_secs(120))
}
```

### 3.2 采样配置

**采样策略**:

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision};

/// 1. 始终采样 (开发环境)
let sampler = Sampler::AlwaysOn;

/// 2. 固定比例采样 (10%)
let sampler = Sampler::TraceIdRatioBased(0.1);

/// 3. 父级采样
let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));

/// 4. 自定义采样器
pub struct CustomSampler {
    high_priority_ratio: f64,
    default_ratio: f64,
}

impl opentelemetry_sdk::trace::ShouldSample for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        _span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[KeyValue],
        _links: &[opentelemetry::trace::Link],
    ) -> opentelemetry_sdk::trace::SamplingResult {
        // 检查是否高优先级
        let is_high_priority = attributes.iter().any(|kv| {
            kv.key.as_str() == "priority" && kv.value.as_str() == "high"
        });
        
        let ratio = if is_high_priority {
            self.high_priority_ratio
        } else {
            self.default_ratio
        };
        
        // 基于TraceID采样
        let threshold = (u64::MAX as f64 * ratio) as u64;
        let trace_id_value = u64::from_be_bytes(trace_id.to_bytes()[8..].try_into().unwrap());
        
        let decision = if trace_id_value < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        opentelemetry_sdk::trace::SamplingResult {
            decision,
            attributes: Vec::new(),
            trace_state: Default::default(),
        }
    }
}

/// 使用自定义采样器
let sampler = CustomSampler {
    high_priority_ratio: 1.0,  // 100% 采样高优先级
    default_ratio: 0.1,         // 10% 采样普通请求
};
```

### 3.3 多Exporter配置

**同时导出到多个后端**:

```rust
use opentelemetry_sdk::export::trace::SpanExporter;

pub async fn init_multi_exporter() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. OTLP Exporter (Jaeger)
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://jaeger:4317")
        .build_span_exporter()?;
    
    // 2. 控制台Exporter (调试)
    let console_exporter = opentelemetry_stdout::SpanExporter::default();
    
    // 3. 组合Exporter
    let resource = Resource::builder()
        .with_service_name("multi-export-service")
        .build();
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(otlp_exporter, tokio::spawn)
        .with_simple_exporter(console_exporter)  // 简单导出器用于调试
        .with_resource(resource)
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}
```

---

## 4. 异步追踪最佳实践

### 4.1 Async Fn追踪

**Rust 1.90 AFIT模式**:

```rust
use tracing::{instrument, info, error};

/// 1. 基础异步追踪
#[instrument]
async fn fetch_user(user_id: i64) -> Result<User, Error> {
    info!("Fetching user from database");
    
    let user = sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", user_id)
        .fetch_one(&pool)
        .await?;
    
    Ok(user)
}

/// 2. 跳过大参数
#[instrument(skip(data))]
async fn process_data(data: Vec<u8>) -> Result<(), Error> {
    info!("Processing {} bytes", data.len());
    // ...
    Ok(())
}

/// 3. 自定义span名称
#[instrument(name = "user.fetch")]
async fn get_user_by_id(id: i64) -> Result<User, Error> {
    // ...
}

/// 4. 记录返回值
#[instrument(ret)]
async fn calculate_sum(a: i32, b: i32) -> i32 {
    a + b
}

/// 5. 记录错误
#[instrument(err)]
async fn risky_operation() -> Result<(), Error> {
    // 如果返回Err，自动记录到span
    Ok(())
}

/// 6. 异步trait方法 (Rust 1.90+)
pub trait UserService {
    async fn create_user(&self, name: String) -> Result<User, Error>;
}

impl UserService for UserServiceImpl {
    #[instrument(skip(self))]
    async fn create_user(&self, name: String) -> Result<User, Error> {
        info!("Creating user: {}", name);
        // ...
    }
}
```

### 4.2 Stream追踪

**追踪异步Stream**:

```rust
use futures::stream::{Stream, StreamExt};

#[instrument(skip(stream))]
async fn process_event_stream<S>(mut stream: S) -> Result<(), Error>
where
    S: Stream<Item = Event> + Unpin,
{
    let span = tracing::Span::current();
    
    while let Some(event) = stream.next().await {
        let _enter = span.enter();
        
        info!("Processing event: {:?}", event);
        
        // 为每个事件创建子span
        let event_span = tracing::info_span!("process_event", event_id = %event.id);
        let _enter = event_span.enter();
        
        handle_event(event).await?;
    }
    
    Ok(())
}
```

### 4.3 Future组合

**追踪并发Future**:

```rust
use futures::future;

#[instrument]
async fn fetch_all_data() -> Result<(Users, Orders, Products), Error> {
    let span = tracing::Span::current();
    
    // 并发执行多个查询
    let (users, orders, products) = tokio::try_join!(
        async {
            let _enter = span.clone().entered();
            fetch_users().await
        },
        async {
            let _enter = span.clone().entered();
            fetch_orders().await
        },
        async {
            let _enter = span.clone().entered();
            fetch_products().await
        },
    )?;
    
    Ok((users, orders, products))
}
```

---

## 5. 错误处理

### 5.1 错误记录

**使用thiserror + tracing**:

```rust
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ServiceError {
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
    
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Invalid input: {0}")]
    InvalidInput(String),
}

#[instrument(err)]
async fn get_user(id: i64) -> Result<User, ServiceError> {
    let user = sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", id)
        .fetch_optional(&pool)
        .await?
        .ok_or_else(|| ServiceError::NotFound(format!("User {} not found", id)))?;
    
    Ok(user)
}

/// 手动记录错误
async fn handle_request() {
    match process_request().await {
        Ok(result) => {
            info!("Request successful");
        }
        Err(e) => {
            error!(error = %e, "Request failed");
            // 记录错误到span
            tracing::Span::current().record("error", &format!("{}", e));
        }
    }
}
```

### 5.2 Panic处理

**捕获Panic**:

```rust
use std::panic;

#[instrument]
async fn safe_task() {
    let result = panic::catch_unwind(|| {
        // 可能panic的代码
        risky_operation();
    });
    
    match result {
        Ok(_) => info!("Task completed successfully"),
        Err(e) => {
            error!("Task panicked: {:?}", e);
            tracing::Span::current().record("panic", &format!("{:?}", e));
        }
    }
}
```

---

## 6. 性能优化

### 6.1 零分配追踪

**避免不必要的克隆**:

```rust
/// ❌ 不好：每次调用都克隆
#[instrument]
async fn bad_example(data: String) {
    // data被移动到span中
}

/// ✅ 好：使用引用
#[instrument(skip(data))]
async fn good_example(data: &str) {
    // 只记录必要信息
    info!(data_len = data.len(), "Processing data");
}

/// ✅ 更好：使用Arc
#[instrument(skip(data))]
async fn best_example(data: Arc<String>) {
    // 只增加引用计数
    info!(data_len = data.len(), "Processing data");
}
```

### 6.2 对象池

**复用Span对象**:

```rust
use object_pool::Pool;

lazy_static::lazy_static! {
    static ref SPAN_POOL: Pool<Vec<SpanData>> = Pool::new(100, || Vec::with_capacity(1000));
}

pub fn get_span_buffer() -> object_pool::Reusable<Vec<SpanData>> {
    SPAN_POOL.pull()
}
```

### 6.3 批处理优化

**本地缓冲 + 批量发送**:

```rust
use tokio::sync::Mutex;

pub struct BufferedExporter {
    buffer: Arc<Mutex<Vec<SpanData>>>,
    batch_size: usize,
    exporter: Box<dyn SpanExporter>,
}

impl BufferedExporter {
    pub async fn export_span(&self, span: SpanData) -> Result<(), Error> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(span);
        
        if buffer.len() >= self.batch_size {
            let batch = std::mem::replace(&mut *buffer, Vec::with_capacity(self.batch_size));
            drop(buffer);
            
            self.exporter.export(batch).await?;
        }
        
        Ok(())
    }
}
```

---

## 7. 内存管理

### 7.1 Arc vs Clone

**选择合适的共享策略**:

```rust
use std::sync::Arc;

/// ✅ 使用Arc共享不可变数据
#[derive(Clone)]
pub struct AppState {
    config: Arc<Config>,
    tracer: Arc<opentelemetry::trace::Tracer>,
}

/// ✅ 使用Arc<Mutex>共享可变数据
pub struct MetricsCollector {
    counters: Arc<Mutex<HashMap<String, u64>>>,
}
```

### 7.2 生命周期管理

**正确管理Span生命周期**:

```rust
/// ✅ 使用RAII模式
pub async fn process_with_span() {
    let span = tracing::info_span!("process");
    let _enter = span.enter();
    
    // span在_enter drop时自动结束
    do_work().await;
}  // _enter在这里drop

/// ❌ 避免忘记结束span
pub async fn bad_example() {
    let span = tracing::info_span!("process");
    let _enter = span.enter();
    
    do_work().await;
    
    // 忘记drop _enter!
    std::mem::forget(_enter);  // 永远不要这样做！
}
```

---

## 8. 生产环境配置

### 8.1 优雅关闭

**正确关闭TracerProvider**:

```rust
use tokio::signal;

pub async fn run_with_graceful_shutdown(
    provider: TracerProvider,
) -> Result<(), Box<dyn std::error::Error>> {
    // 启动应用
    let server = tokio::spawn(async move {
        run_server().await
    });
    
    // 等待关闭信号
    signal::ctrl_c().await?;
    
    tracing::info!("Shutting down...");
    
    // 刷新所有pending spans
    provider.force_flush()?;
    
    // 关闭provider
    provider.shutdown()?;
    
    // 等待服务器关闭
    server.await??;
    
    tracing::info!("Shutdown complete");
    
    Ok(())
}
```

### 8.2 监控集成

**集成Prometheus**:

```rust
use prometheus::{Counter, Histogram, Registry};

pub struct TelemetryMetrics {
    pub spans_created: Counter,
    pub spans_exported: Counter,
    pub export_duration: Histogram,
}

impl TelemetryMetrics {
    pub fn new(registry: &Registry) -> Result<Self, Box<dyn std::error::Error>> {
        let spans_created = Counter::new(
            "otel_spans_created_total",
            "Total spans created",
        )?;
        
        let spans_exported = Counter::new(
            "otel_spans_exported_total",
            "Total spans exported",
        )?;
        
        let export_duration = Histogram::with_opts(
            prometheus::HistogramOpts::new(
                "otel_export_duration_seconds",
                "Export duration",
            ).buckets(vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0]),
        )?;
        
        registry.register(Box::new(spans_created.clone()))?;
        registry.register(Box::new(spans_exported.clone()))?;
        registry.register(Box::new(export_duration.clone()))?;
        
        Ok(Self {
            spans_created,
            spans_exported,
            export_duration,
        })
    }
}
```

---

## 9. 测试最佳实践

**测试追踪代码**:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry::trace::TraceContextExt;
    
    #[tokio::test]
    async fn test_with_tracing() {
        // 1. 初始化测试tracer
        let provider = TracerProvider::builder()
            .with_simple_exporter(opentelemetry_stdout::SpanExporter::default())
            .build();
        
        global::set_tracer_provider(provider.clone());
        
        // 2. 执行测试
        let result = fetch_user(123).await;
        
        // 3. 验证结果
        assert!(result.is_ok());
        
        // 4. 刷新spans
        provider.force_flush().unwrap();
        
        // 5. 清理
        provider.shutdown().unwrap();
    }
    
    #[tokio::test]
    async fn test_span_context() {
        let tracer = global::tracer("test");
        
        tracer.in_span("test_span", |cx| {
            // 验证span context
            let span = cx.span();
            assert!(span.span_context().is_valid());
        });
    }
}
```

---

## 10. 故障排查

**常见问题和解决方案**:

```rust
/// 问题1: Spans没有被导出
/// 解决: 确保调用force_flush()
provider.force_flush()?;

/// 问题2: 内存泄漏
/// 解决: 使用memory_limiter处理器
let memory_limiter = MemoryLimiterProcessor::new(1024 * 1024 * 1024); // 1GB

/// 问题3: 高延迟
/// 解决: 调整批处理配置
let config = BatchConfig::default()
    .with_scheduled_delay(Duration::from_secs(1))  // 降低延迟
    .with_max_export_batch_size(128);              // 减小批次

/// 问题4: 丢失上下文
/// 解决: 使用tracing-opentelemetry
use tracing_opentelemetry::OpenTelemetryLayer;

let telemetry = OpenTelemetryLayer::new(tracer);
tracing_subscriber::registry()
    .with(telemetry)
    .init();
```

---

**相关文档**:
- [Rust同步异步编程集成](05_Rust同步异步编程集成.md)
- [Collector架构](02_Collector架构_Rust完整版.md)
- [性能优化指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日

