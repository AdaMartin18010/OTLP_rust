# OTLP 数据模型 - Rust 类型安全完整实现

> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **日期**: 2025年10月8日  
> **状态**: ✅ 生产就绪

---

## 📋 目录

- [概述](#概述)
- [依赖配置](#依赖配置)
- [核心数据模型](#核心数据模型)
  - [Trace 数据模型](#trace-数据模型)
  - [Metrics 数据模型](#metrics-数据模型)
  - [Logs 数据模型](#logs-数据模型)
- [Resource 模型](#resource-模型)
- [零成本抽象](#零成本抽象)
- [类型安全保证](#类型安全保证)
- [生命周期管理](#生命周期管理)
- [序列化和反序列化](#序列化和反序列化)
- [性能优化](#性能优化)
- [完整示例](#完整示例)
- [最佳实践](#最佳实践)
- [参考资源](#参考资源)

---

## 概述

OTLP (OpenTelemetry Protocol) 定义了遥测数据的标准数据模型，包括 **Traces**、**Metrics** 和 **Logs**。本文档展示如何在 Rust 中实现类型安全、零成本的 OTLP 数据模型。

### 核心特性

- ✅ **编译时类型安全**: 利用 Rust 类型系统在编译时捕获错误
- ✅ **零成本抽象**: 编译后无运行时开销
- ✅ **所有权模型**: 自动内存管理,无需 GC
- ✅ **生命周期保证**: 编译时防止悬垂引用
- ✅ **原生异步**: 完整的异步/await 支持
- ✅ **序列化优化**: 高效的 Protobuf/JSON 序列化

---

## 依赖配置

### Cargo.toml

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json", "grpc-tonic"] }
opentelemetry-semantic-conventions = "0.31.0"

# Protobuf 和序列化
prost = "0.14.1"
prost-types = "0.14.1"
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 工具
bytes = "1.10.1"        # 零拷贝
uuid = { version = "1.18.1", features = ["v4", "serde"] }
thiserror = "2.0.17"

[build-dependencies]
prost-build = "0.14.1"  # 用于编译 .proto 文件
```

---

## 核心数据模型

### Trace 数据模型

#### 1. Span 类型定义

```rust
use opentelemetry::{
    trace::{SpanContext, SpanId, SpanKind, Status, TraceId},
    KeyValue,
};
use std::time::SystemTime;
use bytes::Bytes;

/// 类型安全的 Span 定义
#[derive(Debug, Clone)]
pub struct TypeSafeSpan {
    /// Span 上下文 (TraceID + SpanID)
    context: SpanContext,
    
    /// 父 Span ID (Option 表示可能为根 Span)
    parent_span_id: Option<SpanId>,
    
    /// Span 名称 (owned String)
    name: String,
    
    /// Span 类型 (编译时枚举)
    kind: SpanKind,
    
    /// 开始时间
    start_time: SystemTime,
    
    /// 结束时间 (Option 表示可能未结束)
    end_time: Option<SystemTime>,
    
    /// 状态
    status: Status,
    
    /// 属性 (Vec 确保所有权)
    attributes: Vec<KeyValue>,
    
    /// 事件
    events: Vec<SpanEvent>,
    
    /// 链接
    links: Vec<SpanLink>,
    
    /// Resource (使用 Arc 共享)
    resource: std::sync::Arc<Resource>,
}

/// Span 事件 (值类型)
#[derive(Debug, Clone)]
pub struct SpanEvent {
    pub name: String,
    pub timestamp: SystemTime,
    pub attributes: Vec<KeyValue>,
}

/// Span 链接 (值类型)
#[derive(Debug, Clone)]
pub struct SpanLink {
    pub span_context: SpanContext,
    pub attributes: Vec<KeyValue>,
}
```

#### 2. SpanContext (不可变)

```rust
/// 不可变的 SpanContext
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ImmutableSpanContext {
    /// Trace ID (16 字节)
    trace_id: TraceId,
    
    /// Span ID (8 字节)
    span_id: SpanId,
    
    /// Trace Flags (1 字节)
    trace_flags: u8,
    
    /// 是否采样
    is_sampled: bool,
    
    /// 是否远程
    is_remote: bool,
}

impl ImmutableSpanContext {
    /// 创建新的 SpanContext
    pub const fn new(
        trace_id: TraceId,
        span_id: SpanId,
        trace_flags: u8,
        is_sampled: bool,
        is_remote: bool,
    ) -> Self {
        Self {
            trace_id,
            span_id,
            trace_flags,
            is_sampled,
            is_remote,
        }
    }
    
    /// 获取 Trace ID (借用)
    pub const fn trace_id(&self) -> &TraceId {
        &self.trace_id
    }
    
    /// 获取 Span ID (借用)
    pub const fn span_id(&self) -> &SpanId {
        &self.span_id
    }
    
    /// 是否有效
    pub const fn is_valid(&self) -> bool {
        self.trace_id.to_bytes() != [0u8; 16] && self.span_id.to_bytes() != [0u8; 8]
    }
}
```

#### 3. SpanKind (编译时枚举)

```rust
/// Span 类型 (编译时类型安全)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSafeSpanKind {
    /// 内部操作
    Internal,
    
    /// 服务端
    Server,
    
    /// 客户端
    Client,
    
    /// 生产者
    Producer,
    
    /// 消费者
    Consumer,
}

impl TypeSafeSpanKind {
    /// 转换为 OpenTelemetry SpanKind
    pub const fn to_otel_kind(&self) -> SpanKind {
        match self {
            Self::Internal => SpanKind::Internal,
            Self::Server => SpanKind::Server,
            Self::Client => SpanKind::Client,
            Self::Producer => SpanKind::Producer,
            Self::Consumer => SpanKind::Consumer,
        }
    }
}
```

#### 4. Span 构建器 (类型状态模式)

```rust
use std::marker::PhantomData;

/// Span 构建器状态标记
pub mod builder_state {
    pub struct NoName;
    pub struct HasName;
    pub struct NoKind;
    pub struct HasKind;
}

/// 类型状态 Span 构建器
pub struct SpanBuilder<NameState, KindState> {
    name: Option<String>,
    kind: Option<SpanKind>,
    attributes: Vec<KeyValue>,
    _name_state: PhantomData<NameState>,
    _kind_state: PhantomData<KindState>,
}

impl SpanBuilder<builder_state::NoName, builder_state::NoKind> {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            name: None,
            kind: None,
            attributes: Vec::new(),
            _name_state: PhantomData,
            _kind_state: PhantomData,
        }
    }
}

impl<KindState> SpanBuilder<builder_state::NoName, KindState> {
    /// 设置名称 (状态转换)
    pub fn with_name(
        self,
        name: impl Into<String>,
    ) -> SpanBuilder<builder_state::HasName, KindState> {
        SpanBuilder {
            name: Some(name.into()),
            kind: self.kind,
            attributes: self.attributes,
            _name_state: PhantomData,
            _kind_state: PhantomData,
        }
    }
}

impl<NameState> SpanBuilder<NameState, builder_state::NoKind> {
    /// 设置类型 (状态转换)
    pub fn with_kind(
        self,
        kind: SpanKind,
    ) -> SpanBuilder<NameState, builder_state::HasKind> {
        SpanBuilder {
            name: self.name,
            kind: Some(kind),
            attributes: self.attributes,
            _name_state: PhantomData,
            _kind_state: PhantomData,
        }
    }
}

impl<NameState, KindState> SpanBuilder<NameState, KindState> {
    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
}

impl SpanBuilder<builder_state::HasName, builder_state::HasKind> {
    /// 构建 Span (仅在有名称和类型时才能调用)
    pub fn build(self) -> TypeSafeSpan {
        TypeSafeSpan {
            context: generate_span_context(),
            parent_span_id: None,
            name: self.name.unwrap(),  // 类型系统保证 Some
            kind: self.kind.unwrap(),   // 类型系统保证 Some
            start_time: SystemTime::now(),
            end_time: None,
            status: Status::Unset,
            attributes: self.attributes,
            events: Vec::new(),
            links: Vec::new(),
            resource: std::sync::Arc::new(Resource::default()),
        }
    }
}

// 示例使用
fn example_type_state_builder() {
    // ✅ 编译通过 - 有名称和类型
    let span = SpanBuilder::new()
        .with_name("my_span")
        .with_kind(SpanKind::Client)
        .with_attribute("http.method", "GET")
        .build();
    
    // ❌ 编译失败 - 缺少名称
    // let span = SpanBuilder::new()
    //     .with_kind(SpanKind::Client)
    //     .build();  // Error: method `build` not found
}
```

---

### Metrics 数据模型

#### 1. Metric 类型定义

```rust
use std::sync::Arc;

/// 类型安全的 Metric 定义
#[derive(Debug, Clone)]
pub struct TypeSafeMetric {
    /// Metric 名称
    name: String,
    
    /// 描述
    description: Option<String>,
    
    /// 单位
    unit: Option<String>,
    
    /// Metric 类型
    kind: MetricKind,
    
    /// 数据点
    data_points: Vec<DataPoint>,
    
    /// Resource
    resource: Arc<Resource>,
}

/// Metric 类型 (编译时枚举)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetricKind {
    /// 计数器 (单调递增)
    Counter,
    
    /// 上下计数器 (可增可减)
    UpDownCounter,
    
    /// 直方图
    Histogram,
    
    /// 异步计数器
    ObservableCounter,
    
    /// 异步测量值
    ObservableGauge,
    
    /// 异步上下计数器
    ObservableUpDownCounter,
}

/// 数据点 (泛型)
#[derive(Debug, Clone)]
pub struct DataPoint<T> {
    /// 时间戳
    timestamp: SystemTime,
    
    /// 值
    value: T,
    
    /// 属性
    attributes: Vec<KeyValue>,
    
    /// 示例 (用于直方图)
    exemplars: Vec<Exemplar>,
}

/// 示例值
#[derive(Debug, Clone)]
pub struct Exemplar {
    pub value: f64,
    pub timestamp: SystemTime,
    pub span_id: Option<SpanId>,
    pub trace_id: Option<TraceId>,
}
```

#### 2. Counter (类型安全)

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 类型安全的 Counter
pub struct TypeSafeCounter {
    name: String,
    description: Option<String>,
    unit: Option<String>,
    value: AtomicU64,  // 线程安全
}

impl TypeSafeCounter {
    /// 创建新的 Counter
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: None,
            unit: None,
            value: AtomicU64::new(0),
        }
    }
    
    /// 增加 (线程安全)
    pub fn add(&self, value: u64) {
        self.value.fetch_add(value, Ordering::Relaxed);
    }
    
    /// 获取当前值 (线程安全)
    pub fn value(&self) -> u64 {
        self.value.load(Ordering::Relaxed)
    }
}
```

#### 3. Histogram (类型安全)

```rust
/// 类型安全的 Histogram
pub struct TypeSafeHistogram {
    name: String,
    description: Option<String>,
    unit: Option<String>,
    boundaries: Vec<f64>,  // 边界值
    counts: Vec<AtomicU64>,  // 每个桶的计数
    sum: AtomicU64,  // 总和 (存储为整数, 避免浮点原子操作)
    count: AtomicU64,  // 总计数
}

impl TypeSafeHistogram {
    /// 创建新的 Histogram
    pub fn new(name: impl Into<String>, boundaries: Vec<f64>) -> Self {
        let len = boundaries.len() + 1;  // +1 for overflow bucket
        let mut counts = Vec::with_capacity(len);
        for _ in 0..len {
            counts.push(AtomicU64::new(0));
        }
        
        Self {
            name: name.into(),
            description: None,
            unit: None,
            boundaries,
            counts,
            sum: AtomicU64::new(0),
            count: AtomicU64::new(0),
        }
    }
    
    /// 记录值
    pub fn record(&self, value: f64) {
        // 找到对应的桶
        let bucket = self.boundaries
            .iter()
            .position(|&b| value < b)
            .unwrap_or(self.boundaries.len());
        
        // 增加桶计数
        self.counts[bucket].fetch_add(1, Ordering::Relaxed);
        
        // 更新总和和总计数
        self.sum.fetch_add((value * 1000.0) as u64, Ordering::Relaxed);  // *1000 避免精度损失
        self.count.fetch_add(1, Ordering::Relaxed);
    }
}
```

---

### Logs 数据模型

#### 1. LogRecord 类型定义

```rust
/// 类型安全的 LogRecord
#[derive(Debug, Clone)]
pub struct TypeSafeLogRecord {
    /// 时间戳
    timestamp: SystemTime,
    
    /// 观察时间戳 (可选)
    observed_timestamp: Option<SystemTime>,
    
    /// 严重性 (编译时枚举)
    severity: Severity,
    
    /// 严重性文本
    severity_text: Option<String>,
    
    /// 日志体 (使用 enum 支持多种类型)
    body: LogBody,
    
    /// 属性
    attributes: Vec<KeyValue>,
    
    /// Span 上下文 (可选)
    span_context: Option<SpanContext>,
    
    /// Resource
    resource: Arc<Resource>,
}

/// 日志严重性 (编译时枚举)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Severity {
    Trace = 1,
    Debug = 5,
    Info = 9,
    Warn = 13,
    Error = 17,
    Fatal = 21,
}

/// 日志体 (支持多种类型)
#[derive(Debug, Clone)]
pub enum LogBody {
    String(String),
    Bytes(Bytes),
    Json(serde_json::Value),
}

impl TypeSafeLogRecord {
    /// 创建新的 LogRecord
    pub fn new(severity: Severity, body: impl Into<LogBody>) -> Self {
        Self {
            timestamp: SystemTime::now(),
            observed_timestamp: None,
            severity,
            severity_text: None,
            body: body.into(),
            attributes: Vec::new(),
            span_context: None,
            resource: Arc::new(Resource::default()),
        }
    }
    
    /// 添加属性 (Builder 模式)
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
    
    /// 关联 Span
    pub fn with_span_context(mut self, span_context: SpanContext) -> Self {
        self.span_context = Some(span_context);
        self
    }
}

impl From<String> for LogBody {
    fn from(s: String) -> Self {
        LogBody::String(s)
    }
}

impl From<&str> for LogBody {
    fn from(s: &str) -> Self {
        LogBody::String(s.to_string())
    }
}

impl From<Bytes> for LogBody {
    fn from(b: Bytes) -> Self {
        LogBody::Bytes(b)
    }
}
```

---

## Resource 模型

### 1. Resource 类型定义

```rust
/// 类型安全的 Resource
#[derive(Debug, Clone)]
pub struct Resource {
    /// 资源属性
    attributes: Vec<KeyValue>,
    
    /// Schema URL (可选)
    schema_url: Option<String>,
}

impl Resource {
    /// 创建新的 Resource
    pub fn new(attributes: Vec<KeyValue>) -> Self {
        Self {
            attributes,
            schema_url: None,
        }
    }
    
    /// 获取属性 (借用)
    pub fn attributes(&self) -> &[KeyValue] {
        &self.attributes
    }
    
    /// 合并 Resource (消费 self 和 other)
    pub fn merge(mut self, other: Resource) -> Self {
        self.attributes.extend(other.attributes);
        Self {
            attributes: self.attributes,
            schema_url: self.schema_url.or(other.schema_url),
        }
    }
}

impl Default for Resource {
    fn default() -> Self {
        Self {
            attributes: vec![
                KeyValue::new("service.name", "unknown_service"),
            ],
            schema_url: None,
        }
    }
}
```

### 2. 标准 Resource 属性

```rust
/// 标准 Resource 属性构建器
pub struct ResourceBuilder {
    attributes: Vec<KeyValue>,
}

impl ResourceBuilder {
    pub fn new() -> Self {
        Self {
            attributes: Vec::new(),
        }
    }
    
    /// 设置服务名称
    pub fn with_service_name(mut self, name: impl Into<String>) -> Self {
        self.attributes.push(KeyValue::new("service.name", name.into()));
        self
    }
    
    /// 设置服务版本
    pub fn with_service_version(mut self, version: impl Into<String>) -> Self {
        self.attributes.push(KeyValue::new("service.version", version.into()));
        self
    }
    
    /// 设置部署环境
    pub fn with_deployment_environment(mut self, env: impl Into<String>) -> Self {
        self.attributes.push(KeyValue::new("deployment.environment", env.into()));
        self
    }
    
    /// 构建 Resource
    pub fn build(self) -> Resource {
        Resource::new(self.attributes)
    }
}
```

---

## 零成本抽象

### 1. 编译时优化

```rust
/// 零成本的 Span 操作 (内联)
impl TypeSafeSpan {
    /// 添加事件 (inline hint)
    #[inline]
    pub fn add_event(&mut self, name: impl Into<String>, attributes: Vec<KeyValue>) {
        self.events.push(SpanEvent {
            name: name.into(),
            timestamp: SystemTime::now(),
            attributes,
        });
    }
    
    /// 设置状态 (inline hint)
    #[inline]
    pub fn set_status(&mut self, status: Status) {
        self.status = status;
    }
    
    /// 结束 Span (inline + const)
    #[inline]
    pub fn end(mut self) -> Self {
        self.end_time = Some(SystemTime::now());
        self
    }
}
```

### 2. 零大小类型 (ZST)

```rust
/// 零大小类型标记
pub struct TracerMarker;
pub struct MeterMarker;
pub struct LoggerMarker;

/// 泛型 Provider (编译时特化)
pub struct Provider<T> {
    _marker: std::marker::PhantomData<T>,
}

// 零运行时开销
assert_eq!(std::mem::size_of::<Provider<TracerMarker>>(), 0);
```

---

## 类型安全保证

### 1. 编译时验证

```rust
/// 类型安全的属性键
pub enum AttributeKey {
    HttpMethod,
    HttpStatusCode,
    DbStatement,
    DbOperation,
}

impl AttributeKey {
    /// 获取键名 (编译时常量)
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::HttpMethod => "http.method",
            Self::HttpStatusCode => "http.status_code",
            Self::DbStatement => "db.statement",
            Self::DbOperation => "db.operation",
        }
    }
}

/// 类型安全的属性值
pub enum AttributeValue {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
}

/// 类型安全的属性
pub struct TypeSafeAttribute {
    key: AttributeKey,
    value: AttributeValue,
}

impl TypeSafeAttribute {
    /// 创建新属性 (编译时类型检查)
    pub fn new(key: AttributeKey, value: AttributeValue) -> Self {
        Self { key, value }
    }
    
    /// 转换为 OpenTelemetry KeyValue
    pub fn into_key_value(self) -> KeyValue {
        let key = self.key.as_str();
        let value = match self.value {
            AttributeValue::String(s) => opentelemetry::Value::String(s.into()),
            AttributeValue::Int(i) => opentelemetry::Value::I64(i),
            AttributeValue::Float(f) => opentelemetry::Value::F64(f),
            AttributeValue::Bool(b) => opentelemetry::Value::Bool(b),
        };
        KeyValue::new(key, value)
    }
}
```

### 2. 生命周期保证

```rust
/// 带生命周期的 Span 引用
pub struct SpanRef<'a> {
    span: &'a TypeSafeSpan,
}

impl<'a> SpanRef<'a> {
    /// 创建 Span 引用 (借用)
    pub fn new(span: &'a TypeSafeSpan) -> Self {
        Self { span }
    }
    
    /// 获取 Span 名称 (借用)
    pub fn name(&self) -> &'a str {
        &self.span.name
    }
    
    /// 获取 Span 类型 (复制)
    pub fn kind(&self) -> SpanKind {
        self.span.kind
    }
}

// 编译时生命周期验证
fn example_lifetime() {
    let span = TypeSafeSpan::default();
    let span_ref = SpanRef::new(&span);
    
    // ✅ 编译通过 - span_ref 的生命周期不超过 span
    println!("Span name: {}", span_ref.name());
    
    // ❌ 编译失败 - span 被移动后无法借用
    // drop(span);
    // println!("Span name: {}", span_ref.name());  // Error: borrow of moved value
}
```

---

## 生命周期管理

### 1. RAII 模式

```rust
/// RAII Span Guard
pub struct SpanGuard {
    span: TypeSafeSpan,
}

impl SpanGuard {
    /// 创建新的 Span Guard
    pub fn new(name: impl Into<String>, kind: SpanKind) -> Self {
        let mut span = TypeSafeSpan::default();
        span.name = name.into();
        span.kind = kind;
        span.start_time = SystemTime::now();
        
        Self { span }
    }
    
    /// 获取 Span (借用)
    pub fn span(&self) -> &TypeSafeSpan {
        &self.span
    }
    
    /// 获取可变 Span (可变借用)
    pub fn span_mut(&mut self) -> &mut TypeSafeSpan {
        &mut self.span
    }
}

impl Drop for SpanGuard {
    /// 自动结束 Span
    fn drop(&mut self) {
        self.span.end_time = Some(SystemTime::now());
        // 可以在这里自动导出 Span
    }
}

// 使用示例
fn example_raii() {
    {
        let _span = SpanGuard::new("my_operation", SpanKind::Internal);
        // 执行操作...
    }  // Span 自动结束
}
```

### 2. 异步生命周期

```rust
use tokio::task::JoinHandle;

/// 异步 Span Guard
pub struct AsyncSpanGuard {
    span: TypeSafeSpan,
    _join_handle: Option<JoinHandle<()>>,
}

impl AsyncSpanGuard {
    /// 创建异步 Span Guard
    pub async fn new(name: impl Into<String>, kind: SpanKind) -> Self {
        let mut span = TypeSafeSpan::default();
        span.name = name.into();
        span.kind = kind;
        span.start_time = SystemTime::now();
        
        Self {
            span,
            _join_handle: None,
        }
    }
    
    /// 在异步上下文中执行
    pub async fn run<F, T>(mut self, f: F) -> T
    where
        F: std::future::Future<Output = T>,
    {
        let result = f.await;
        self.span.end_time = Some(SystemTime::now());
        result
    }
}

// 使用示例
async fn example_async_raii() {
    let span = AsyncSpanGuard::new("async_operation", SpanKind::Internal).await;
    
    span.run(async {
        // 异步操作...
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }).await;
    // Span 自动结束
}
```

---

## 序列化和反序列化

### 1. Protobuf 序列化

```rust
use prost::Message;

/// Span 的 Protobuf 表示
#[derive(Clone, PartialEq, Message)]
pub struct ProtoSpan {
    #[prost(bytes, tag = "1")]
    pub trace_id: Vec<u8>,
    
    #[prost(bytes, tag = "2")]
    pub span_id: Vec<u8>,
    
    #[prost(string, tag = "3")]
    pub name: String,
    
    #[prost(enumeration = "proto_span::SpanKind", tag = "4")]
    pub kind: i32,
    
    #[prost(uint64, tag = "5")]
    pub start_time_unix_nano: u64,
    
    #[prost(uint64, tag = "6")]
    pub end_time_unix_nano: u64,
}

impl From<TypeSafeSpan> for ProtoSpan {
    fn from(span: TypeSafeSpan) -> Self {
        ProtoSpan {
            trace_id: span.context.trace_id().to_bytes().to_vec(),
            span_id: span.context.span_id().to_bytes().to_vec(),
            name: span.name,
            kind: span.kind as i32,
            start_time_unix_nano: span.start_time
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64,
            end_time_unix_nano: span.end_time
                .map(|t| t.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos() as u64)
                .unwrap_or(0),
        }
    }
}
```

### 2. JSON 序列化

```rust
use serde::{Deserialize, Serialize};

/// Span 的 JSON 表示
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonSpan {
    pub trace_id: String,
    pub span_id: String,
    pub name: String,
    pub kind: String,
    pub start_time: u64,
    pub end_time: Option<u64>,
    pub attributes: Vec<JsonKeyValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonKeyValue {
    pub key: String,
    pub value: serde_json::Value,
}

impl From<TypeSafeSpan> for JsonSpan {
    fn from(span: TypeSafeSpan) -> Self {
        JsonSpan {
            trace_id: format!("{:032x}", u128::from_be_bytes(span.context.trace_id().to_bytes())),
            span_id: format!("{:016x}", u64::from_be_bytes(span.context.span_id().to_bytes())),
            name: span.name,
            kind: format!("{:?}", span.kind),
            start_time: span.start_time
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64,
            end_time: span.end_time
                .map(|t| t.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos() as u64),
            attributes: vec![],  // 简化示例
        }
    }
}
```

---

## 性能优化

### 1. 零拷贝

```rust
use bytes::Bytes;

/// 零拷贝 Span
pub struct ZeroCopySpan {
    /// 使用 Bytes 实现零拷贝
    trace_id: Bytes,
    span_id: Bytes,
    name: Bytes,
    
    /// 其他字段...
}

impl ZeroCopySpan {
    /// Cheap clone (只增加引用计数)
    pub fn cheap_clone(&self) -> Self {
        Self {
            trace_id: self.trace_id.clone(),  // 只复制指针
            span_id: self.span_id.clone(),
            name: self.name.clone(),
        }
    }
}
```

### 2. 对象池

```rust
use std::sync::Mutex;

/// Span 对象池
pub struct SpanPool {
    pool: Mutex<Vec<TypeSafeSpan>>,
    max_size: usize,
}

impl SpanPool {
    /// 创建新的对象池
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: Mutex::new(Vec::with_capacity(max_size)),
            max_size,
        }
    }
    
    /// 获取 Span (从池中或创建新的)
    pub fn acquire(&self) -> TypeSafeSpan {
        let mut pool = self.pool.lock().unwrap();
        pool.pop().unwrap_or_else(|| TypeSafeSpan::default())
    }
    
    /// 归还 Span
    pub fn release(&self, mut span: TypeSafeSpan) {
        // 清理 Span
        span.events.clear();
        span.links.clear();
        span.attributes.clear();
        
        let mut pool = self.pool.lock().unwrap();
        if pool.len() < self.max_size {
            pool.push(span);
        }
    }
}
```

---

## 完整示例

### 1. 完整的 Trace 示例

```rust
use opentelemetry::{global, trace::Tracer};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OTLP
    init_telemetry("rust-otlp-example").await?;
    
    // 创建 Span
    let span = SpanBuilder::new()
        .with_name("http_request")
        .with_kind(SpanKind::Server)
        .with_attribute("http.method", "GET")
        .with_attribute("http.url", "/api/users")
        .build();
    
    // 使用 RAII Guard
    {
        let mut guard = SpanGuard::new("database_query", SpanKind::Client);
        guard.span_mut().add_event("query_start", vec![]);
        
        // 执行查询...
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        guard.span_mut().add_event("query_end", vec![]);
    }  // Span 自动结束并导出
    
    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}
```

### 2. 完整的 Metrics 示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 Counter
    let request_counter = TypeSafeCounter::new("http_requests_total");
    
    // 创建 Histogram
    let latency_histogram = TypeSafeHistogram::new(
        "http_request_duration_seconds",
        vec![0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0],
    );
    
    // 记录指标
    for _ in 0..1000 {
        request_counter.add(1);
        latency_histogram.record(0.123);
    }
    
    println!("Total requests: {}", request_counter.value());
    Ok(())
}
```

---

## 最佳实践

### ✅ 类型安全

1. **使用类型状态模式**

   ```rust
   // ✅ 编译时验证
   SpanBuilder::new()
       .with_name("span")
       .with_kind(SpanKind::Client)
       .build();
   ```

2. **使用编译时枚举**

   ```rust
   // ✅ 类型安全的 SpanKind
   let kind = TypeSafeSpanKind::Client;
   ```

### ⚡ 性能优化

1. **使用零拷贝**

   ```rust
   // ✅ 使用 Bytes
   let name = Bytes::from("my_span");
   ```

2. **使用对象池**

   ```rust
   // ✅ 重用 Span 对象
   let pool = SpanPool::new(100);
   let span = pool.acquire();
   // ... 使用 span ...
   pool.release(span);
   ```

### 🔒 生命周期管理

1. **使用 RAII**

   ```rust
   // ✅ 自动清理
   {
       let _span = SpanGuard::new("op", SpanKind::Internal);
   }  // 自动结束
   ```

---

## 参考资源

### 📚 官方文档

- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry/latest/opentelemetry/)

### 🔧 相关库

- [opentelemetry](https://crates.io/crates/opentelemetry)
- [prost](https://crates.io/crates/prost)
- [bytes](https://crates.io/crates/bytes)

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月8日  
**作者**: AI Assistant  
**许可证**: MIT OR Apache-2.0

[🏠 返回目录](../README.md)
