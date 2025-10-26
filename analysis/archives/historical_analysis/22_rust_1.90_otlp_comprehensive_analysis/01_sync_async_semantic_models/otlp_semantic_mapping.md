# OTLP 语义模型到 Rust 类型系统的完整映射

> **版本**: Rust 1.90 + OTLP 1.3.0  
> **日期**: 2025年10月3日  
> **主题**: 语义模型、类型安全、零拷贝、形式化验证

---

## 📋 目录

- [OTLP 语义模型到 Rust 类型系统的完整映射](#otlp-语义模型到-rust-类型系统的完整映射)
  - [📋 目录](#-目录)
  - [OTLP 语义模型概览](#otlp-语义模型概览)
    - [1.1 核心设计哲学](#11-核心设计哲学)
    - [1.2 Rust 类型系统映射策略](#12-rust-类型系统映射策略)
  - [Resource Schema 映射](#resource-schema-映射)
    - [2.1 OTLP Resource 语义规范](#21-otlp-resource-语义规范)
    - [2.2 Rust 类型映射](#22-rust-类型映射)
    - [2.3 类型安全的属性访问](#23-类型安全的属性访问)
  - [Trace 语义映射](#trace-语义映射)
    - [3.1 OTLP Span 模型](#31-otlp-span-模型)
    - [3.2 Rust 类型映射](#32-rust-类型映射)
    - [3.3 构建器模式](#33-构建器模式)
  - [Metric 语义映射](#metric-语义映射)
    - [4.1 OTLP Metric 模型](#41-otlp-metric-模型)
    - [4.2 Rust 类型映射](#42-rust-类型映射)
    - [4.3 类型安全的 Metric 构建](#43-类型安全的-metric-构建)
  - [类型安全保证](#类型安全保证)
    - [5.1 编译时不变量检查](#51-编译时不变量检查)
    - [5.2 运行时验证](#52-运行时验证)
  - [性能优化](#性能优化)
    - [6.1 零拷贝序列化](#61-零拷贝序列化)
    - [6.2 内存池优化](#62-内存池优化)
  - [总结](#总结)
    - [核心映射关系](#核心映射关系)
    - [下一步](#下一步)

---

## OTLP 语义模型概览

### 1.1 核心设计哲学

**OTLP 的三个核心语义维度**:

```text
┌─────────────────────────────────────────┐
│  Resource (资源语义)                     │
│  ↓                                      │
│  "WHO" - 谁产生的数据                    │
│  - service.name                         │
│  - k8s.pod.name                         │
│  - host.name                            │
└─────────────────────────────────────────┘
           ↓
┌─────────────────────────────────────────┐
│  Signal (信号语义)                       │
│  ↓                                      │
│  "WHAT" - 什么类型的数据                 │
│  - Traces (因果链)                      │
│  - Metrics (定量数据)                   │
│  - Logs (事件流)                        │
└─────────────────────────────────────────┘
           ↓
┌─────────────────────────────────────────┐
│  Context (上下文语义)                    │
│  ↓                                      │
│  "HOW" - 数据如何关联                    │
│  - TraceId/SpanId                       │
│  - Baggage                              │
│  - TraceState                           │
└─────────────────────────────────────────┘
```

### 1.2 Rust 类型系统映射策略

**映射原则**:

1. **语义 → 类型**: 每个语义概念对应一个 Rust 类型
2. **不变量 → 类型约束**: 语义不变量通过类型系统强制
3. **零拷贝 → 借用**: 使用引用避免数据复制
4. **可扩展性 → 泛型**: 使用泛型支持自定义扩展

```rust
/// OTLP 核心三元组
pub enum TelemetryData {
    Traces(TraceData),
    Metrics(MetricData),
    Logs(LogData),
}

/// 资源语义封装
#[derive(Debug, Clone, PartialEq)]
pub struct Resource {
    /// 资源属性
    attributes: Vec<KeyValue>,
    /// 丢弃的属性数量
    dropped_attributes_count: u32,
}

/// 键值对语义
#[derive(Debug, Clone, PartialEq)]
pub struct KeyValue {
    pub key: String,
    pub value: AnyValue,
}

/// 类型安全的属性值
#[derive(Debug, Clone, PartialEq)]
pub enum AnyValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    ArrayValue(Vec<AnyValue>),
    KvlistValue(Vec<KeyValue>),
    Bytes(Vec<u8>),
}

#[derive(Debug, Clone)]
pub struct TraceData;

#[derive(Debug, Clone)]
pub struct MetricData;

#[derive(Debug, Clone)]
pub struct LogData;
```

---

## Resource Schema 映射

### 2.1 OTLP Resource 语义规范

**OpenTelemetry Semantic Conventions**:

```protobuf
// OTLP Protocol Buffer 定义
message Resource {
  repeated KeyValue attributes = 1;
  uint32 dropped_attributes_count = 2;
}

message KeyValue {
  string key = 1;
  AnyValue value = 2;
}
```

**标准属性分类**:

| 分类 | 前缀 | 示例 |
|------|------|------|
| 服务 | `service.*` | `service.name`, `service.version` |
| 部署 | `deployment.*` | `deployment.environment` |
| Kubernetes | `k8s.*` | `k8s.pod.name`, `k8s.namespace.name` |
| 云平台 | `cloud.*` | `cloud.provider`, `cloud.region` |
| 主机 | `host.*` | `host.name`, `host.arch` |
| 进程 | `process.*` | `process.pid`, `process.executable.name` |

### 2.2 Rust 类型映射

```rust
use std::collections::HashMap;
use std::borrow::Cow;

/// Resource 构建器模式
#[derive(Debug, Clone)]
pub struct ResourceBuilder {
    attributes: HashMap<Cow<'static, str>, AnyValue>,
}

impl ResourceBuilder {
    pub fn new() -> Self {
        Self {
            attributes: HashMap::new(),
        }
    }
    
    /// 设置服务信息
    pub fn with_service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.attributes.insert(
            Cow::Borrowed("service.name"),
            AnyValue::String(name.into()),
        );
        self.attributes.insert(
            Cow::Borrowed("service.version"),
            AnyValue::String(version.into()),
        );
        self
    }
    
    /// 设置 Kubernetes 信息
    pub fn with_k8s_pod(
        mut self,
        namespace: impl Into<String>,
        pod_name: impl Into<String>,
    ) -> Self {
        self.attributes.insert(
            Cow::Borrowed("k8s.namespace.name"),
            AnyValue::String(namespace.into()),
        );
        self.attributes.insert(
            Cow::Borrowed("k8s.pod.name"),
            AnyValue::String(pod_name.into()),
        );
        self
    }
    
    /// 设置主机信息
    pub fn with_host(mut self, name: impl Into<String>) -> Self {
        self.attributes.insert(
            Cow::Borrowed("host.name"),
            AnyValue::String(name.into()),
        );
        self
    }
    
    /// 构建 Resource
    pub fn build(self) -> Resource {
        Resource {
            attributes: self.attributes
                .into_iter()
                .map(|(k, v)| KeyValue {
                    key: k.into_owned(),
                    value: v,
                })
                .collect(),
            dropped_attributes_count: 0,
        }
    }
}

impl Default for ResourceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用示例
fn create_resource() -> Resource {
    ResourceBuilder::new()
        .with_service("user-service", "1.0.0")
        .with_k8s_pod("production", "user-service-abc123")
        .with_host("node-1")
        .build()
}
```

### 2.3 类型安全的属性访问

```rust
/// 类型安全的 Resource 扩展
pub trait ResourceExt {
    fn service_name(&self) -> Option<&str>;
    fn service_version(&self) -> Option<&str>;
    fn k8s_namespace(&self) -> Option<&str>;
    fn k8s_pod_name(&self) -> Option<&str>;
}

impl ResourceExt for Resource {
    fn service_name(&self) -> Option<&str> {
        self.attributes
            .iter()
            .find(|kv| kv.key == "service.name")
            .and_then(|kv| {
                if let AnyValue::String(s) = &kv.value {
                    Some(s.as_str())
                } else {
                    None
                }
            })
    }
    
    fn service_version(&self) -> Option<&str> {
        self.attributes
            .iter()
            .find(|kv| kv.key == "service.version")
            .and_then(|kv| {
                if let AnyValue::String(s) = &kv.value {
                    Some(s.as_str())
                } else {
                    None
                }
            })
    }
    
    fn k8s_namespace(&self) -> Option<&str> {
        self.attributes
            .iter()
            .find(|kv| kv.key == "k8s.namespace.name")
            .and_then(|kv| {
                if let AnyValue::String(s) = &kv.value {
                    Some(s.as_str())
                } else {
                    None
                }
            })
    }
    
    fn k8s_pod_name(&self) -> Option<&str> {
        self.attributes
            .iter()
            .find(|kv| kv.key == "k8s.pod.name")
            .and_then(|kv| {
                if let AnyValue::String(s) = &kv.value {
                    Some(s.as_str())
                } else {
                    None
                }
            })
    }
}

/// 编译时类型检查
fn use_resource(resource: &Resource) {
    // ✅ 类型安全访问
    if let Some(name) = resource.service_name() {
        println!("Service: {}", name);
    }
    
    // ❌ 编译错误：类型不匹配
    // let version: u32 = resource.service_version();
}
```

---

## Trace 语义映射

### 3.1 OTLP Span 模型

**Span 生命周期状态机**:

```text
                    ┌──────────┐
                    │  Created │
                    └────┬─────┘
                         │ start()
                    ┌────▼─────┐
              ┌────►│  Active  │◄────┐
              │     └────┬─────┘     │
   add_event()│          │           │ set_attribute()
              │     ┌────▼─────┐     │
              └─────┤  Events  ├─────┘
                    └────┬─────┘
                         │ end()
                    ┌────▼─────┐
                    │  Ended   │
                    └──────────┘
```

### 3.2 Rust 类型映射

```rust
use std::time::{SystemTime, UNIX_EPOCH};

/// Span 结构
#[derive(Debug, Clone)]
pub struct Span {
    /// Trace ID (16 字节)
    pub trace_id: TraceId,
    /// Span ID (8 字节)
    pub span_id: SpanId,
    /// Parent Span ID
    pub parent_span_id: Option<SpanId>,
    /// Span 名称
    pub name: String,
    /// Span 类型
    pub kind: SpanKind,
    /// 开始时间 (纳秒)
    pub start_time_unix_nano: u64,
    /// 结束时间 (纳秒)
    pub end_time_unix_nano: u64,
    /// 属性
    pub attributes: Vec<KeyValue>,
    /// 事件
    pub events: Vec<SpanEvent>,
    /// Links
    pub links: Vec<SpanLink>,
    /// 状态
    pub status: SpanStatus,
}

/// Trace ID (128-bit)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraceId([u8; 16]);

impl TraceId {
    pub fn random() -> Self {
        let mut bytes = [0u8; 16];
        for byte in &mut bytes {
            *byte = rand::random();
        }
        Self(bytes)
    }
    
    pub fn from_hex(hex: &str) -> Result<Self, ParseError> {
        if hex.len() != 32 {
            return Err(ParseError::InvalidLength);
        }
        
        let mut bytes = [0u8; 16];
        for i in 0..16 {
            bytes[i] = u8::from_str_radix(&hex[i*2..i*2+2], 16)?;
        }
        
        Ok(Self(bytes))
    }
    
    pub fn to_hex(&self) -> String {
        self.0.iter()
            .map(|b| format!("{:02x}", b))
            .collect()
    }
}

/// Span ID (64-bit)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanId([u8; 8]);

impl SpanId {
    pub fn random() -> Self {
        let mut bytes = [0u8; 8];
        for byte in &mut bytes {
            *byte = rand::random();
        }
        Self(bytes)
    }
    
    pub fn from_hex(hex: &str) -> Result<Self, ParseError> {
        if hex.len() != 16 {
            return Err(ParseError::InvalidLength);
        }
        
        let mut bytes = [0u8; 8];
        for i in 0..8 {
            bytes[i] = u8::from_str_radix(&hex[i*2..i*2+2], 16)?;
        }
        
        Ok(Self(bytes))
    }
    
    pub fn to_hex(&self) -> String {
        self.0.iter()
            .map(|b| format!("{:02x}", b))
            .collect()
    }
}

#[derive(Debug)]
pub enum ParseError {
    InvalidLength,
    ParseInt(std::num::ParseIntError),
}

impl From<std::num::ParseIntError> for ParseError {
    fn from(e: std::num::ParseIntError) -> Self {
        ParseError::ParseInt(e)
    }
}

/// Span 类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    /// 内部操作
    Internal,
    /// 服务端接收请求
    Server,
    /// 客户端发起请求
    Client,
    /// 消息生产者
    Producer,
    /// 消息消费者
    Consumer,
}

/// Span 事件
#[derive(Debug, Clone)]
pub struct SpanEvent {
    pub name: String,
    pub time_unix_nano: u64,
    pub attributes: Vec<KeyValue>,
}

/// Span Link
#[derive(Debug, Clone)]
pub struct SpanLink {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub attributes: Vec<KeyValue>,
}

/// Span 状态
#[derive(Debug, Clone)]
pub struct SpanStatus {
    pub code: StatusCode,
    pub message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatusCode {
    Unset = 0,
    Ok = 1,
    Error = 2,
}
```

### 3.3 构建器模式

```rust
/// Span 构建器
pub struct SpanBuilder {
    name: String,
    kind: SpanKind,
    parent: Option<SpanContext>,
    attributes: Vec<KeyValue>,
    links: Vec<SpanLink>,
}

#[derive(Clone)]
pub struct SpanContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
}

impl SpanBuilder {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: SpanKind::Internal,
            parent: None,
            attributes: Vec::new(),
            links: Vec::new(),
        }
    }
    
    pub fn with_kind(mut self, kind: SpanKind) -> Self {
        self.kind = kind;
        self
    }
    
    pub fn with_parent(mut self, parent: SpanContext) -> Self {
        self.parent = Some(parent);
        self
    }
    
    pub fn with_attribute(mut self, key: impl Into<String>, value: AnyValue) -> Self {
        self.attributes.push(KeyValue {
            key: key.into(),
            value,
        });
        self
    }
    
    pub fn with_link(mut self, link: SpanLink) -> Self {
        self.links.push(link);
        self
    }
    
    pub fn start(self) -> Span {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        let trace_id = self.parent
            .as_ref()
            .map(|p| p.trace_id)
            .unwrap_or_else(TraceId::random);
        
        let parent_span_id = self.parent.as_ref().map(|p| p.span_id);
        
        Span {
            trace_id,
            span_id: SpanId::random(),
            parent_span_id,
            name: self.name,
            kind: self.kind,
            start_time_unix_nano: now,
            end_time_unix_nano: 0,
            attributes: self.attributes,
            events: Vec::new(),
            links: self.links,
            status: SpanStatus {
                code: StatusCode::Unset,
                message: String::new(),
            },
        }
    }
}

/// 使用示例
fn create_span_with_parent() {
    let parent_ctx = SpanContext {
        trace_id: TraceId::random(),
        span_id: SpanId::random(),
    };
    
    let span = SpanBuilder::new("database_query")
        .with_kind(SpanKind::Client)
        .with_parent(parent_ctx)
        .with_attribute("db.system", AnyValue::String("postgresql".to_string()))
        .with_attribute("db.statement", AnyValue::String("SELECT * FROM users".to_string()))
        .start();
    
    println!("Span created: {:?}", span.name);
}
```

---

## Metric 语义映射

### 4.1 OTLP Metric 模型

**指标类型分类**:

```text
Metrics
├── Counter (单调递增)
│   └── Sum (累加值)
├── UpDownCounter (可增可减)
│   └── Sum (当前值)
├── Histogram (分布统计)
│   ├── Buckets (桶边界)
│   └── ExponentialHistogram (指数桶)
└── Gauge (瞬时值)
    └── 最新测量值
```

### 4.2 Rust 类型映射

```rust
/// Metric 数据点
#[derive(Debug, Clone)]
pub enum MetricData {
    Sum(SumDataPoint),
    Histogram(HistogramDataPoint),
    ExponentialHistogram(ExponentialHistogramDataPoint),
    Gauge(GaugeDataPoint),
}

/// Sum 数据点
#[derive(Debug, Clone)]
pub struct SumDataPoint {
    pub attributes: Vec<KeyValue>,
    pub start_time_unix_nano: u64,
    pub time_unix_nano: u64,
    pub value: SumValue,
    pub is_monotonic: bool,
}

#[derive(Debug, Clone)]
pub enum SumValue {
    Int(i64),
    Double(f64),
}

/// Histogram 数据点
#[derive(Debug, Clone)]
pub struct HistogramDataPoint {
    pub attributes: Vec<KeyValue>,
    pub start_time_unix_nano: u64,
    pub time_unix_nano: u64,
    pub count: u64,
    pub sum: Option<f64>,
    pub bucket_counts: Vec<u64>,
    pub explicit_bounds: Vec<f64>,
    pub min: Option<f64>,
    pub max: Option<f64>,
}

/// 指数直方图
#[derive(Debug, Clone)]
pub struct ExponentialHistogramDataPoint {
    pub attributes: Vec<KeyValue>,
    pub start_time_unix_nano: u64,
    pub time_unix_nano: u64,
    pub count: u64,
    pub sum: Option<f64>,
    pub scale: i32,
    pub zero_count: u64,
    pub positive: Buckets,
    pub negative: Buckets,
}

#[derive(Debug, Clone)]
pub struct Buckets {
    pub offset: i32,
    pub bucket_counts: Vec<u64>,
}

/// Gauge 数据点
#[derive(Debug, Clone)]
pub struct GaugeDataPoint {
    pub attributes: Vec<KeyValue>,
    pub time_unix_nano: u64,
    pub value: GaugeValue,
}

#[derive(Debug, Clone)]
pub enum GaugeValue {
    Int(i64),
    Double(f64),
}
```

### 4.3 类型安全的 Metric 构建

```rust
/// Counter 构建器
pub struct CounterBuilder {
    name: String,
    description: String,
    unit: String,
}

impl CounterBuilder {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: String::new(),
            unit: String::new(),
        }
    }
    
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = desc.into();
        self
    }
    
    pub fn with_unit(mut self, unit: impl Into<String>) -> Self {
        self.unit = unit.into();
        self
    }
    
    pub fn build(self) -> Counter {
        Counter {
            name: self.name,
            description: self.description,
            unit: self.unit,
        }
    }
}

pub struct Counter {
    name: String,
    description: String,
    unit: String,
}

impl Counter {
    pub fn add(&self, value: i64, attributes: Vec<KeyValue>) -> SumDataPoint {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        SumDataPoint {
            attributes,
            start_time_unix_nano: now,
            time_unix_nano: now,
            value: SumValue::Int(value),
            is_monotonic: true,
        }
    }
}

/// 使用示例
fn record_http_requests() {
    let counter = CounterBuilder::new("http.server.requests")
        .with_description("Total HTTP requests")
        .with_unit("1")
        .build();
    
    let data_point = counter.add(
        1,
        vec![
            KeyValue {
                key: "http.method".to_string(),
                value: AnyValue::String("GET".to_string()),
            },
            KeyValue {
                key: "http.status_code".to_string(),
                value: AnyValue::Int(200),
            },
        ],
    );
    
    println!("Recorded: {:?}", data_point);
}
```

---

## 类型安全保证

### 5.1 编译时不变量检查

```rust
/// 使用 newtype 模式保证 ID 类型安全
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceIdWrapper(TraceId);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpanIdWrapper(SpanId);

// ❌ 编译错误：类型不匹配
// let trace_id: TraceIdWrapper = SpanIdWrapper(SpanId::random());

/// 使用 PhantomData 标记状态
use std::marker::PhantomData;

pub struct Started;
pub struct Ended;

pub struct TypedSpan<State> {
    inner: Span,
    _state: PhantomData<State>,
}

impl TypedSpan<Started> {
    pub fn end(self) -> TypedSpan<Ended> {
        let mut inner = self.inner;
        inner.end_time_unix_nano = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        TypedSpan {
            inner,
            _state: PhantomData,
        }
    }
}

impl TypedSpan<Ended> {
    // ❌ 编译错误：Ended 状态不能再调用 end()
    // pub fn end(self) -> TypedSpan<Ended> { ... }
}
```

### 5.2 运行时验证

```rust
/// 验证 Resource 属性
impl Resource {
    pub fn validate(&self) -> Result<(), ValidationError> {
        // 必须包含 service.name
        let has_service_name = self.attributes
            .iter()
            .any(|kv| kv.key == "service.name");
        
        if !has_service_name {
            return Err(ValidationError::MissingServiceName);
        }
        
        // 属性键不能为空
        for kv in &self.attributes {
            if kv.key.is_empty() {
                return Err(ValidationError::EmptyAttributeKey);
            }
        }
        
        Ok(())
    }
}

#[derive(Debug)]
pub enum ValidationError {
    MissingServiceName,
    EmptyAttributeKey,
}

/// 使用示例
fn validate_resource() -> Result<(), ValidationError> {
    let resource = ResourceBuilder::new()
        .with_service("my-service", "1.0.0")
        .build();
    
    resource.validate()?;
    Ok(())
}
```

---

## 性能优化

### 6.1 零拷贝序列化

```rust
use bytes::BytesMut;

/// 零拷贝 Span 序列化
pub fn serialize_span_zero_copy(span: &Span) -> BytesMut {
    let capacity = estimate_span_size(span);
    let mut buf = BytesMut::with_capacity(capacity);
    
    // 直接写入缓冲区，避免中间分配
    write_span(&mut buf, span);
    
    buf
}

fn estimate_span_size(_span: &Span) -> usize {
    1024 // 简化估算
}

fn write_span(_buf: &mut BytesMut, _span: &Span) {
    // 实际序列化逻辑
}
```

### 6.2 内存池优化

```rust
use std::sync::Arc;
use parking_lot::Mutex;

/// Span 对象池
pub struct SpanPool {
    pool: Arc<Mutex<Vec<Span>>>,
}

impl SpanPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(capacity))),
        }
    }
    
    pub fn acquire(&self) -> Span {
        self.pool.lock().pop().unwrap_or_else(|| {
            // 池为空时创建新对象
            Span {
                trace_id: TraceId::random(),
                span_id: SpanId::random(),
                parent_span_id: None,
                name: String::new(),
                kind: SpanKind::Internal,
                start_time_unix_nano: 0,
                end_time_unix_nano: 0,
                attributes: Vec::new(),
                events: Vec::new(),
                links: Vec::new(),
                status: SpanStatus {
                    code: StatusCode::Unset,
                    message: String::new(),
                },
            }
        })
    }
    
    pub fn release(&self, mut span: Span) {
        // 重置 Span
        span.name.clear();
        span.attributes.clear();
        span.events.clear();
        span.links.clear();
        
        let mut pool = self.pool.lock();
        if pool.len() < pool.capacity() {
            pool.push(span);
        }
    }
}
```

---

## 总结

### 核心映射关系

| OTLP 概念 | Rust 类型 | 保证 |
|-----------|-----------|------|
| Resource | `struct Resource` | 编译时类型检查 |
| TraceId | `struct TraceId([u8; 16])` | newtype 模式 |
| SpanId | `struct SpanId([u8; 8])` | newtype 模式 |
| AnyValue | `enum AnyValue` | 类型安全的值 |
| SpanKind | `enum SpanKind` | 穷尽匹配 |
| Metric | `enum MetricData` | 类型驱动设计 |

### 下一步

- [同步异步互操作](./sync_async_interop.md)
- [性能特征分析](./performance_characteristics.md)
- [分布式追踪模型](../02_distributed_tracing_models/causal_relationship_model.md)

---

**参考资源**:

- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [OTLP Protocol Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Rust Type System](https://doc.rust-lang.org/book/ch10-00-generics.html)
