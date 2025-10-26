# OTLP 三支柱信号集成设计

> **版本**: OTLP 1.3.0 & Rust 1.90  
> **日期**: 2025年10月2日  
> **主题**: Trace/Metric/Log 融合、自动关联、统一查询

---

## 📋 目录

- [OTLP 三支柱信号集成设计](#otlp-三支柱信号集成设计)
  - [📋 目录](#-目录)
  - [三支柱概述](#三支柱概述)
    - [1.1 为什么需要三支柱融合](#11-为什么需要三支柱融合)
    - [1.2 OTLP 统一数据模型](#12-otlp-统一数据模型)
  - [Trace (追踪)](#trace-追踪)
    - [2.1 数据模型](#21-数据模型)
    - [2.2 Rust 实现](#22-rust-实现)
  - [Metric (指标)](#metric-指标)
    - [3.1 指标类型](#31-指标类型)
    - [3.2 Rust 实现](#32-rust-实现)
  - [Log (日志)](#log-日志)
    - [4.1 结构化日志](#41-结构化日志)
    - [4.2 Rust 实现](#42-rust-实现)
  - [自动关联机制](#自动关联机制)
    - [5.1 Resource 关联](#51-resource-关联)
    - [5.2 TraceID 关联](#52-traceid-关联)
    - [5.3 时间戳关联](#53-时间戳关联)
  - [统一 SDK 设计](#统一-sdk-设计)
    - [6.1 统一配置](#61-统一配置)
    - [6.2 统一 Exporter](#62-统一-exporter)
  - [查询与分析](#查询与分析)
    - [7.1 跨信号查询](#71-跨信号查询)
    - [7.2 因果链重建](#72-因果链重建)
  - [性能优化](#性能优化)
    - [8.1 批处理优化](#81-批处理优化)
    - [8.2 采样策略](#82-采样策略)
  - [实战案例](#实战案例)
    - [9.1 微服务监控](#91-微服务监控)
    - [9.2 故障诊断流程](#92-故障诊断流程)
  - [📚 参考资源](#-参考资源)

---

## 三支柱概述

### 1.1 为什么需要三支柱融合

**单一信号的局限性**:

| 信号类型 | 优势 | 局限 |
|---------|------|-----|
| **Trace** | 调用链路完整 | 无法反映系统整体状态 |
| **Metric** | 系统趋势明显 | 缺乏请求级细节 |
| **Log** | 上下文详细 | 难以建立全局视图 |

**融合的价值**:

- ✅ **完整视图**: Trace 提供调用链 → Metric 反映趋势 → Log 补充细节
- ✅ **快速定位**: Metric 发现异常 → Trace 定位具体请求 → Log 查看错误详情
- ✅ **根因分析**: 从现象 (Metric) → 路径 (Trace) → 原因 (Log)

### 1.2 OTLP 统一数据模型

**核心抽象**:

```text
所有信号共享:
1. Resource: 描述信号来源 (service.name, host.name 等)
2. Scope: 描述生成库 (opentelemetry-rust@1.0.0)
3. Attributes: 键值对元数据
4. Timestamp: 时间戳 (纳秒精度)
```

**数据结构**:

```rust
/// 统一的遥测数据基础
struct TelemetryData {
    resource: Resource,
    scope: InstrumentationScope,
    timestamp: u64, // nanoseconds since epoch
    attributes: Vec<KeyValue>,
}

struct Resource {
    attributes: Vec<KeyValue>,
}

struct InstrumentationScope {
    name: String,
    version: String,
}

struct KeyValue {
    key: String,
    value: Value,
}

enum Value {
    String(String),
    Int(i64),
    Double(f64),
    Bool(bool),
}
```

---

## Trace (追踪)

### 2.1 数据模型

**Span 结构**:

```rust
struct Span {
    // 身份信息
    trace_id: [u8; 16],
    span_id: [u8; 8],
    parent_span_id: Option<[u8; 8]>,
    
    // 元数据
    name: String,
    kind: SpanKind,
    start_time: u64,
    end_time: u64,
    
    // 关联信息
    attributes: Vec<KeyValue>,
    events: Vec<Event>,
    links: Vec<Link>,
    
    // 状态
    status: Status,
}

#[derive(Debug, Clone, Copy)]
enum SpanKind {
    Internal,
    Server,
    Client,
    Producer,
    Consumer,
}

struct Event {
    name: String,
    timestamp: u64,
    attributes: Vec<KeyValue>,
}

struct Link {
    trace_id: [u8; 16],
    span_id: [u8; 8],
    attributes: Vec<KeyValue>,
}

struct Status {
    code: StatusCode,
    message: Option<String>,
}

#[derive(Debug, Clone, Copy)]
enum StatusCode {
    Unset,
    Ok,
    Error,
}
```

### 2.2 Rust 实现

```rust
use opentelemetry::{global, trace::{Tracer, TracerProvider}, KeyValue};

/// 创建 Span 并自动记录
async fn traced_operation() {
    let tracer = global::tracer("my-service");
    
    let span = tracer
        .span_builder("database_query")
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.name", "users"),
        ])
        .start(&tracer);
    
    // 操作执行
    let _guard = opentelemetry::trace::Context::current_with_span(span);
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    // Span 自动结束
}
```

---

## Metric (指标)

### 3.1 指标类型

**OTLP 标准指标**:

```text
1. Counter: 单调递增计数器 (请求总数)
2. UpDownCounter: 可增可减计数器 (活跃连接数)
3. Histogram: 直方图 (请求延迟分布)
4. Gauge: 瞬时值 (CPU 使用率)
```

### 3.2 Rust 实现

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter, Unit};

/// 指标收集器
struct MetricsCollector {
    request_counter: Counter<u64>,
    request_duration: Histogram<f64>,
    active_connections: opentelemetry::metrics::UpDownCounter<i64>,
}

impl MetricsCollector {
    fn new(meter: &Meter) -> Self {
        Self {
            request_counter: meter
                .u64_counter("http_requests_total")
                .with_description("Total HTTP requests")
                .init(),
            
            request_duration: meter
                .f64_histogram("http_request_duration_seconds")
                .with_unit(Unit::new("s"))
                .with_description("HTTP request duration")
                .init(),
            
            active_connections: meter
                .i64_up_down_counter("http_active_connections")
                .with_description("Active HTTP connections")
                .init(),
        }
    }
    
    /// 记录请求
    fn record_request(&self, duration_ms: f64, status_code: u16) {
        self.request_counter.add(1, &[
            KeyValue::new("status", status_code.to_string()),
        ]);
        
        self.request_duration.record(duration_ms / 1000.0, &[
            KeyValue::new("status", status_code.to_string()),
        ]);
    }
}
```

---

## Log (日志)

### 4.1 结构化日志

**LogRecord 结构**:

```rust
struct LogRecord {
    // 时间信息
    timestamp: u64,
    observed_timestamp: u64,
    
    // 内容
    severity: Severity,
    body: String,
    
    // 关联信息
    trace_id: Option<[u8; 16]>,
    span_id: Option<[u8; 8]>,
    
    // 元数据
    attributes: Vec<KeyValue>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Severity {
    Trace = 1,
    Debug = 5,
    Info = 9,
    Warn = 13,
    Error = 17,
    Fatal = 21,
}
```

### 4.2 Rust 实现

```rust
use tracing::{info, error, instrument};

/// 使用 tracing 库 (原生支持 OpenTelemetry)
#[instrument(
    name = "process_order",
    fields(
        order_id = %order_id,
        user_id = %user_id,
    )
)]
async fn process_order(order_id: u64, user_id: u64) -> Result<(), String> {
    info!("Processing order");
    
    // 业务逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    if order_id % 10 == 0 {
        error!(error_code = "PAYMENT_FAILED", "Payment processing failed");
        return Err("Payment failed".to_string());
    }
    
    info!("Order processed successfully");
    Ok(())
}
```

---

## 自动关联机制

### 5.1 Resource 关联

**共享 Resource 属性**:

```rust
use opentelemetry_sdk::Resource;

/// 创建统一 Resource
fn create_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "order-service"),
        KeyValue::new("service.version", "1.2.3"),
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("host.name", std::env::var("HOSTNAME").unwrap_or_default()),
    ])
}

/// 应用到所有信号
fn init_telemetry() {
    let resource = create_resource();
    
    // Trace Provider
    let tracer_provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_resource(resource.clone())
        .build();
    
    // Meter Provider
    let meter_provider = opentelemetry_sdk::metrics::SdkMeterProvider::builder()
        .with_resource(resource.clone())
        .build();
    
    // Logger Provider
    // (类似配置)
}
```

### 5.2 TraceID 关联

**日志自动注入 TraceID**:

```rust
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, Registry};

/// 配置 tracing 与 OpenTelemetry 集成
fn setup_tracing() {
    let tracer = opentelemetry::global::tracer("tracing-integration");
    
    let telemetry_layer = OpenTelemetryLayer::new(tracer);
    
    let subscriber = Registry::default()
        .with(telemetry_layer)
        .with(tracing_subscriber::fmt::layer());
    
    tracing::subscriber::set_global_default(subscriber)
        .expect("Failed to set subscriber");
}

/// 日志自动包含 trace_id 和 span_id
#[instrument]
async fn business_logic() {
    tracing::info!("This log automatically includes trace_id and span_id");
}
```

### 5.3 时间戳关联

**时间范围查询**:

```rust
/// 查询特定时间范围的所有信号
struct TimeRangeQuery {
    start: u64, // nanoseconds
    end: u64,
    resource_filter: Vec<KeyValue>,
}

impl TimeRangeQuery {
    /// 查询 Trace
    async fn query_traces(&self) -> Vec<Span> {
        // 实现查询逻辑
        vec![]
    }
    
    /// 查询 Metric
    async fn query_metrics(&self) -> Vec<MetricPoint> {
        vec![]
    }
    
    /// 查询 Log
    async fn query_logs(&self) -> Vec<LogRecord> {
        vec![]
    }
}

struct MetricPoint {
    timestamp: u64,
    value: f64,
}
```

---

## 统一 SDK 设计

### 6.1 统一配置

```rust
use opentelemetry_otlp::WithExportConfig;

/// 统一的 OTLP 配置
struct OtlpConfig {
    endpoint: String,
    headers: std::collections::HashMap<String, String>,
    timeout: std::time::Duration,
}

impl OtlpConfig {
    /// 初始化所有信号的 Exporter
    fn init_all_exporters(&self) -> Result<(), Box<dyn std::error::Error>> {
        // Trace Exporter
        let trace_exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(&self.endpoint)
            .with_timeout(self.timeout);
        
        // Metric Exporter
        let metric_exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(&self.endpoint)
            .with_timeout(self.timeout);
        
        // Log Exporter (类似配置)
        
        Ok(())
    }
}
```

### 6.2 统一 Exporter

```rust
/// 多信号批处理 Exporter
struct MultiSignalExporter {
    trace_exporter: Box<dyn TraceExporter>,
    metric_exporter: Box<dyn MetricExporter>,
    log_exporter: Box<dyn LogExporter>,
}

impl MultiSignalExporter {
    /// 批量发送所有信号
    async fn flush_all(&self) -> Result<(), ExportError> {
        tokio::try_join!(
            self.trace_exporter.flush(),
            self.metric_exporter.flush(),
            self.log_exporter.flush(),
        )?;
        Ok(())
    }
}

trait TraceExporter {
    async fn flush(&self) -> Result<(), ExportError>;
}

trait MetricExporter {
    async fn flush(&self) -> Result<(), ExportError>;
}

trait LogExporter {
    async fn flush(&self) -> Result<(), ExportError>;
}

#[derive(Debug)]
struct ExportError;
```

---

## 查询与分析

### 7.1 跨信号查询

**示例: 根据错误日志找到完整 Trace**:

```rust
/// 故障诊断工作流
async fn diagnose_error(error_log: LogRecord) -> DiagnosisResult {
    let trace_id = error_log.trace_id.expect("Log missing trace_id");
    
    // 1. 查询完整 Trace
    let trace = query_trace_by_id(trace_id).await;
    
    // 2. 查询同时间段的指标
    let metrics = query_metrics_by_time_range(
        error_log.timestamp - 60_000_000_000, // 前 60 秒
        error_log.timestamp + 60_000_000_000, // 后 60 秒
    ).await;
    
    // 3. 查询相关日志
    let related_logs = query_logs_by_trace_id(trace_id).await;
    
    DiagnosisResult {
        trace,
        metrics,
        logs: related_logs,
    }
}

struct DiagnosisResult {
    trace: Vec<Span>,
    metrics: Vec<MetricPoint>,
    logs: Vec<LogRecord>,
}

async fn query_trace_by_id(_trace_id: [u8; 16]) -> Vec<Span> {
    vec![]
}

async fn query_metrics_by_time_range(_start: u64, _end: u64) -> Vec<MetricPoint> {
    vec![]
}

async fn query_logs_by_trace_id(_trace_id: [u8; 16]) -> Vec<LogRecord> {
    vec![]
}
```

### 7.2 因果链重建

```rust
/// 重建完整调用链
fn rebuild_call_chain(spans: Vec<Span>) -> CallTree {
    let mut tree = CallTree::new();
    
    for span in spans {
        tree.add_span(span);
    }
    
    tree
}

struct CallTree {
    root: Option<Span>,
    children: std::collections::HashMap<[u8; 8], Vec<Span>>,
}

impl CallTree {
    fn new() -> Self {
        Self {
            root: None,
            children: std::collections::HashMap::new(),
        }
    }
    
    fn add_span(&mut self, span: Span) {
        if span.parent_span_id.is_none() {
            self.root = Some(span);
        } else {
            let parent_id = span.parent_span_id.unwrap();
            self.children.entry(parent_id).or_default().push(span);
        }
    }
}
```

---

## 性能优化

### 8.1 批处理优化

```rust
/// 多信号批处理器
struct BatchProcessor {
    trace_buffer: Vec<Span>,
    metric_buffer: Vec<MetricPoint>,
    log_buffer: Vec<LogRecord>,
    batch_size: usize,
}

impl BatchProcessor {
    async fn add_trace(&mut self, span: Span) {
        self.trace_buffer.push(span);
        if self.trace_buffer.len() >= self.batch_size {
            self.flush_traces().await;
        }
    }
    
    async fn flush_traces(&mut self) {
        println!("Flushing {} traces", self.trace_buffer.len());
        self.trace_buffer.clear();
    }
}
```

### 8.2 采样策略

```rust
/// 自适应采样器
struct AdaptiveSampler {
    base_rate: f64,
    error_boost: f64,
}

impl AdaptiveSampler {
    /// 根据 Span 特征决定是否采样
    fn should_sample(&self, span: &Span) -> bool {
        // 错误 Span 总是采样
        if span.status.code == StatusCode::Error {
            return true;
        }
        
        // 慢请求提高采样率
        let duration_ms = (span.end_time - span.start_time) / 1_000_000;
        if duration_ms > 1000 {
            return rand::random::<f64>() < self.base_rate * 10.0;
        }
        
        // 正常请求按基础采样率
        rand::random::<f64>() < self.base_rate
    }
}
```

---

## 实战案例

### 9.1 微服务监控

```rust
/// 完整的微服务可观测性设置
async fn setup_microservice_observability() {
    // 1. 配置 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "payment-service"),
        KeyValue::new("service.version", "2.1.0"),
    ]);
    
    // 2. 初始化 Trace
    let tracer = opentelemetry::global::tracer("payment-service");
    
    // 3. 初始化 Metric
    let meter = opentelemetry::global::meter("payment-service");
    let request_counter = meter.u64_counter("requests_total").init();
    
    // 4. 初始化 Log
    setup_tracing();
    
    // 5. 业务逻辑
    process_payment(&tracer, &request_counter).await;
}

async fn process_payment(tracer: &dyn opentelemetry::trace::Tracer, counter: &Counter<u64>) {
    let span = tracer.span_builder("process_payment").start(tracer);
    let _guard = opentelemetry::trace::Context::current_with_span(span);
    
    tracing::info!("Processing payment");
    
    // 业务逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    counter.add(1, &[KeyValue::new("status", "success")]);
}
```

### 9.2 故障诊断流程

```text
1. Metric 告警: "payment-service P99 延迟 > 5s"
2. 查询 Trace: 找到慢请求的 TraceID
3. 分析 Span: 发现 "database_query" Span 耗时 4.8s
4. 查看 Log: 找到 SQL 语句和错误信息
5. 根因: 数据库慢查询，缺少索引
```

---

## 📚 参考资源

1. **OTLP 规范**: <https://opentelemetry.io/docs/specs/otlp/>
2. **OpenTelemetry Rust**: <https://github.com/open-telemetry/opentelemetry-rust>
3. **tracing 文档**: <https://docs.rs/tracing/>
4. **三支柱可观测性**: <https://www.oreilly.com/library/view/distributed-systems-observability/9781492033431/>

---

**最后更新**: 2025年10月2日  
**作者**: OTLP Rust 项目组
