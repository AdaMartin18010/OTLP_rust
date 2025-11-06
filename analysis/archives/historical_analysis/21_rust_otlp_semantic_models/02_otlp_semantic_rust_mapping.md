# OTLP 语义模型与 Rust 类型系统映射

## 📋 目录

- [OTLP 语义模型与 Rust 类型系统映射](#otlp-语义模型与-rust-类型系统映射)
  - [📋 目录](#-目录)
  - [OTLP 语义模型概览](#otlp-语义模型概览)
    - [OTLP 核心设计哲学](#otlp-核心设计哲学)
    - [语义三要素](#语义三要素)
    - [Rust 类型系统的优势](#rust-类型系统的优势)
  - [三元组语义结构](#三元组语义结构)
    - [OTLP 核心三元组](#otlp-核心三元组)
    - [Rust 枚举类型映射](#rust-枚举类型映射)
    - [类型安全保证](#类型安全保证)
  - [Resource Schema 映射](#resource-schema-映射)
    - [OTLP Resource 语义](#otlp-resource-语义)
    - [Rust 结构体映射](#rust-结构体映射)
    - [使用示例](#使用示例)
  - [Trace 语义与类型映射](#trace-语义与类型映射)
    - [OTLP Span 语义模型](#otlp-span-语义模型)
    - [Rust 类型映射](#rust-类型映射)
    - [因果链构建](#因果链构建)
    - [类型安全的 Span 上下文传播](#类型安全的-span-上下文传播)
  - [Metric 语义与类型映射](#metric-语义与类型映射)
    - [OTLP Metric 模型](#otlp-metric-模型)
    - [Rust 类型映射1](#rust-类型映射1)
    - [类型安全的指标构建](#类型安全的指标构建)
  - [Log 语义与类型映射](#log-语义与类型映射)
    - [OTLP LogRecord 模型](#otlp-logrecord-模型)
    - [与 Trace 关联](#与-trace-关联)
  - [因果关系建模](#因果关系建模)
    - [因果链的 Rust 表示](#因果链的-rust-表示)
  - [属性系统类型安全设计](#属性系统类型安全设计)
    - [类型安全的属性值](#类型安全的属性值)
  - [总结](#总结)
    - [核心映射关系](#核心映射关系)
    - [下一步](#下一步)

---

## OTLP 语义模型概览

### OTLP 核心设计哲学

**OTLP 不仅是传输协议，更是自解释的语义模型**:

```text
数据携带语义 (Self-Describing Data)
    ↓
机器可理解 (Machine-Readable)
    ↓
自动分析决策 (Automated Analysis)
    ↓
自我运维系统 (Self-Operating System)
```

### 语义三要素

1. **结构化数据**: Trace, Metric, Log
2. **资源上下文**: Resource Schema
3. **因果关系**: TraceId, SpanId, ParentId

### Rust 类型系统的优势

| OTLP 需求 | Rust 特性 | 优势 |
|----------|----------|------|
| 类型安全 | 强类型系统 | 编译时错误检查 |
| 零拷贝 | 所有权系统 | 高性能序列化 |
| 并发安全 | Send/Sync | 无数据竞争 |
| 内存安全 | 借用检查器 | 无内存泄漏 |
| 可扩展性 | Trait 系统 | 灵活抽象 |

---

## 三元组语义结构

### OTLP 核心三元组

```text
┌─────────────────────────────────────────┐
│      OTLP 三元组 (Triple)               │
├─────────────────────────────────────────┤
│  Trace   │  因果链追踪 (Causality)     │
│  Metric  │  定量观测 (Quantitative)    │
│  Log     │  事件记录 (Event)           │
└─────────────────────────────────────────┘
             ↓
        Resource Schema
    (service.name, k8s.pod.name, ...)
```

### Rust 枚举类型映射

```rust
/// 遥测数据类型 (完全覆盖 OTLP 三元组)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TelemetryDataType {
    /// 追踪数据 - 因果关系
    Trace,
    /// 指标数据 - 定量观测
    Metric,
    /// 日志数据 - 事件记录
    Log,
}

/// 遥测数据容器 (统一接口)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryData {
    /// 数据类型标签
    pub data_type: TelemetryDataType,

    /// 时间戳 (纳秒精度)
    pub timestamp: u64,

    /// 资源属性 (Resource Schema)
    pub resource_attributes: HashMap<String, AttributeValue>,

    /// 作用域属性 (Instrumentation Scope)
    pub scope_attributes: HashMap<String, AttributeValue>,

    /// 具体数据内容 (使用 tagged union)
    pub content: TelemetryContent,
}

/// 数据内容 (Tagged Union - 类型安全)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TelemetryContent {
    Trace(TraceData),
    Metric(MetricData),
    Log(LogData),
}
```

### 类型安全保证

```rust
impl TelemetryData {
    /// 类型安全的构造器
    pub fn trace(trace_data: TraceData) -> Self {
        Self {
            data_type: TelemetryDataType::Trace,
            content: TelemetryContent::Trace(trace_data),
            ..Default::default()
        }
    }

    /// 类型安全的访问器 (编译时检查)
    pub fn as_trace(&self) -> Option<&TraceData> {
        match (&self.data_type, &self.content) {
            (TelemetryDataType::Trace, TelemetryContent::Trace(data)) => Some(data),
            _ => None,
        }
    }

    /// 模式匹配提取 (零成本抽象)
    pub fn into_trace(self) -> Result<TraceData, Self> {
        match self.content {
            TelemetryContent::Trace(data) => Ok(data),
            _ => Err(self),
        }
    }
}
```

---

## Resource Schema 映射

### OTLP Resource 语义

**Resource 定义**: 生成遥测数据的实体的不可变属性集合

```text
Resource {
    attributes: {
        "service.name": "payment-service",
        "service.namespace": "production",
        "service.version": "1.2.3",
        "host.name": "node-42",
        "k8s.pod.name": "payment-7d6c4f8b9-xr5tn",
        "k8s.namespace.name": "default",
        "cloud.provider": "aws",
        "cloud.region": "us-west-2",
    }
}
```

### Rust 结构体映射

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// Resource Schema 类型安全封装
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Resource {
    /// 属性键值对
    attributes: HashMap<String, AttributeValue>,

    /// Schema URL (可选)
    schema_url: Option<String>,
}

impl Resource {
    /// 构造器 - 使用 builder 模式
    pub fn builder() -> ResourceBuilder {
        ResourceBuilder::default()
    }

    /// 获取服务名称 (强类型访问)
    pub fn service_name(&self) -> Option<&str> {
        self.get_string("service.name")
    }

    /// 获取 Pod 名称
    pub fn k8s_pod_name(&self) -> Option<&str> {
        self.get_string("k8s.pod.name")
    }

    /// 泛型属性访问
    pub fn get_string(&self, key: &str) -> Option<&str> {
        self.attributes.get(key).and_then(|v| v.as_string())
    }
}

/// Builder 模式构造 Resource
#[derive(Default)]
pub struct ResourceBuilder {
    attributes: HashMap<String, AttributeValue>,
}

impl ResourceBuilder {
    /// 链式调用设置属性
    pub fn with_service(mut self, name: &str, version: &str) -> Self {
        self.attributes.insert(
            "service.name".to_string(),
            AttributeValue::String(name.to_string())
        );
        self.attributes.insert(
            "service.version".to_string(),
            AttributeValue::String(version.to_string())
        );
        self
    }

    pub fn with_k8s_pod(mut self, name: &str, namespace: &str) -> Self {
        self.attributes.insert(
            "k8s.pod.name".to_string(),
            AttributeValue::String(name.to_string())
        );
        self.attributes.insert(
            "k8s.namespace.name".to_string(),
            AttributeValue::String(namespace.to_string())
        );
        self
    }

    pub fn build(self) -> Resource {
        Resource {
            attributes: self.attributes,
            schema_url: Some("https://opentelemetry.io/schemas/1.24.0".to_string()),
        }
    }
}
```

### 使用示例

```rust
// 类型安全构造 Resource
let resource = Resource::builder()
    .with_service("payment-service", "1.2.3")
    .with_k8s_pod("payment-7d6c4f8b9-xr5tn", "default")
    .build();

// 类型安全访问
assert_eq!(resource.service_name(), Some("payment-service"));
```

---

## Trace 语义与类型映射

### OTLP Span 语义模型

```text
Span {
    trace_id: [u8; 16],           // 全局唯一追踪 ID
    span_id: [u8; 8],             // 当前跨度 ID
    parent_span_id: Option<[u8; 8]>, // 父跨度 ID (因果链)
    name: String,                  // 操作名称
    kind: SpanKind,                // 跨度类型
    start_time_unix_nano: u64,     // 开始时间
    end_time_unix_nano: u64,       // 结束时间
    status: Status,                // 状态
    attributes: Vec<KeyValue>,     // 属性
    events: Vec<Event>,            // 事件
    links: Vec<Link>,              // 链接
}
```

### Rust 类型映射

```rust
/// TraceId 类型别名 (强类型标识)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraceId([u8; 16]);

impl TraceId {
    /// 生成新的 TraceId
    pub fn new() -> Self {
        Self(rand::random())
    }

    /// 从十六进制字符串解析
    pub fn from_hex(s: &str) -> Result<Self, ParseError> {
        let bytes = hex::decode(s)?;
        if bytes.len() != 16 {
            return Err(ParseError::InvalidLength);
        }
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&bytes);
        Ok(Self(arr))
    }

    /// 转换为十六进制字符串
    pub fn to_hex(&self) -> String {
        hex::encode(self.0)
    }
}

/// SpanId 类型别名
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId([u8; 8]);

impl SpanId {
    pub fn new() -> Self {
        Self(rand::random())
    }
}

/// Span 数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Span {
    /// 追踪 ID (因果链根)
    pub trace_id: TraceId,

    /// 跨度 ID (当前节点)
    pub span_id: SpanId,

    /// 父跨度 ID (因果链指针)
    pub parent_span_id: Option<SpanId>,

    /// 操作名称
    pub name: String,

    /// 跨度类型
    pub kind: SpanKind,

    /// 开始时间 (纳秒)
    pub start_time: u64,

    /// 结束时间 (纳秒)
    pub end_time: u64,

    /// 状态
    pub status: SpanStatus,

    /// 属性
    pub attributes: HashMap<String, AttributeValue>,

    /// 事件列表
    pub events: Vec<SpanEvent>,

    /// 链接列表
    pub links: Vec<SpanLink>,
}

/// SpanKind 枚举 (OTLP 标准)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpanKind {
    /// 内部操作
    Internal,
    /// 服务器端接收请求
    Server,
    /// 客户端发送请求
    Client,
    /// 消息生产者
    Producer,
    /// 消息消费者
    Consumer,
}

/// Span 状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanStatus {
    /// 状态码
    pub code: StatusCode,
    /// 状态消息
    pub message: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StatusCode {
    /// 未设置
    Unset,
    /// 成功
    Ok,
    /// 错误
    Error,
}
```

### 因果链构建

```rust
/// 构建因果链
impl Span {
    /// 创建根 Span
    pub fn root(name: impl Into<String>) -> Self {
        Self {
            trace_id: TraceId::new(),
            span_id: SpanId::new(),
            parent_span_id: None,
            name: name.into(),
            kind: SpanKind::Internal,
            start_time: current_time_nanos(),
            end_time: 0,
            status: SpanStatus::ok(),
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        }
    }

    /// 创建子 Span (继承 trace_id)
    pub fn child(&self, name: impl Into<String>) -> Self {
        Self {
            trace_id: self.trace_id, // 继承追踪 ID
            span_id: SpanId::new(),
            parent_span_id: Some(self.span_id), // 设置父指针
            name: name.into(),
            kind: SpanKind::Internal,
            start_time: current_time_nanos(),
            end_time: 0,
            status: SpanStatus::ok(),
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        }
    }

    /// 结束 Span
    pub fn end(&mut self) {
        self.end_time = current_time_nanos();
    }

    /// 计算持续时间 (纳秒)
    pub fn duration(&self) -> u64 {
        self.end_time.saturating_sub(self.start_time)
    }
}
```

### 类型安全的 Span 上下文传播

```rust
/// SpanContext - 跨进程传播
#[derive(Debug, Clone, Copy)]
pub struct SpanContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub trace_flags: u8,
    pub trace_state: Option<TraceState>,
}

impl SpanContext {
    /// 从 HTTP 头部提取
    pub fn from_headers(headers: &HeaderMap) -> Option<Self> {
        let traceparent = headers.get("traceparent")?;
        Self::parse_traceparent(traceparent.to_str().ok()?)
    }

    /// 解析 W3C Trace Context
    pub fn parse_traceparent(s: &str) -> Option<Self> {
        // 格式: 00-{trace_id}-{span_id}-{flags}
        let parts: Vec<&str> = s.split('-').collect();
        if parts.len() != 4 || parts[0] != "00" {
            return None;
        }

        Some(Self {
            trace_id: TraceId::from_hex(parts[1]).ok()?,
            span_id: SpanId::from_hex(parts[2]).ok()?,
            trace_flags: u8::from_str_radix(parts[3], 16).ok()?,
            trace_state: None,
        })
    }

    /// 注入到 HTTP 头部
    pub fn inject_headers(&self, headers: &mut HeaderMap) {
        let traceparent = format!(
            "00-{}-{}-{:02x}",
            self.trace_id.to_hex(),
            self.span_id.to_hex(),
            self.trace_flags
        );
        headers.insert("traceparent", traceparent.parse().unwrap());
    }
}
```

---

## Metric 语义与类型映射

### OTLP Metric 模型

```text
Metric {
    name: String,
    description: String,
    unit: String,
    data: MetricData {
        Counter | Gauge | Histogram | Summary
    }
}
```

### Rust 类型映射1

```rust
/// 指标类型 (OTLP 标准)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MetricType {
    /// 单调递增计数器
    Counter,
    /// 可上下变动的仪表
    Gauge,
    /// 直方图 (分布)
    Histogram,
    /// 摘要 (分位数)
    Summary,
}

/// 指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metric {
    /// 指标名称
    pub name: String,

    /// 描述
    pub description: String,

    /// 单位 (如 "ms", "bytes", "1")
    pub unit: String,

    /// 指标类型
    pub metric_type: MetricType,

    /// 数据点
    pub data_points: Vec<DataPoint>,
}

/// 数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    /// 时间戳
    pub timestamp: u64,

    /// 属性 (维度)
    pub attributes: HashMap<String, AttributeValue>,

    /// 值
    pub value: DataPointValue,
}

/// 数据点值 (Tagged Union)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataPointValue {
    /// 数值型 (Counter, Gauge)
    Number(f64),

    /// 直方图
    Histogram(HistogramData),

    /// 摘要
    Summary(SummaryData),
}

/// 直方图数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramData {
    /// 总样本数
    pub count: u64,

    /// 样本总和
    pub sum: f64,

    /// 桶分布
    pub buckets: Vec<HistogramBucket>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    /// 上限
    pub upper_bound: f64,

    /// 落入该桶的样本数
    pub count: u64,
}
```

### 类型安全的指标构建

```rust
impl Metric {
    /// 创建 Counter
    pub fn counter(name: impl Into<String>) -> MetricBuilder<Counter> {
        MetricBuilder::new(name.into(), MetricType::Counter)
    }

    /// 创建 Gauge
    pub fn gauge(name: impl Into<String>) -> MetricBuilder<Gauge> {
        MetricBuilder::new(name.into(), MetricType::Gauge)
    }

    /// 创建 Histogram
    pub fn histogram(name: impl Into<String>) -> MetricBuilder<Histogram> {
        MetricBuilder::new(name.into(), MetricType::Histogram)
    }
}

/// 类型状态模式 (Type-State Pattern)
pub struct MetricBuilder<T> {
    name: String,
    metric_type: MetricType,
    description: String,
    unit: String,
    _phantom: PhantomData<T>,
}

/// 类型标记
pub struct Counter;
pub struct Gauge;
pub struct Histogram;

impl<T> MetricBuilder<T> {
    fn new(name: String, metric_type: MetricType) -> Self {
        Self {
            name,
            metric_type,
            description: String::new(),
            unit: String::from("1"),
            _phantom: PhantomData,
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
}

impl MetricBuilder<Counter> {
    /// Counter 只能递增
    pub fn record(self, value: u64) -> Metric {
        Metric {
            name: self.name,
            description: self.description,
            unit: self.unit,
            metric_type: MetricType::Counter,
            data_points: vec![DataPoint {
                timestamp: current_time_nanos(),
                attributes: HashMap::new(),
                value: DataPointValue::Number(value as f64),
            }],
        }
    }
}

impl MetricBuilder<Gauge> {
    /// Gauge 可以是任意值
    pub fn record(self, value: f64) -> Metric {
        Metric {
            name: self.name,
            description: self.description,
            unit: self.unit,
            metric_type: MetricType::Gauge,
            data_points: vec![DataPoint {
                timestamp: current_time_nanos(),
                attributes: HashMap::new(),
                value: DataPointValue::Number(value),
            }],
        }
    }
}
```

---

## Log 语义与类型映射

### OTLP LogRecord 模型

```rust
/// 日志记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogRecord {
    /// 时间戳
    pub timestamp: u64,

    /// 严重程度
    pub severity: LogSeverity,

    /// 日志体 (结构化)
    pub body: LogBody,

    /// 属性
    pub attributes: HashMap<String, AttributeValue>,

    /// 关联的 Trace Context (可选)
    pub trace_context: Option<SpanContext>,
}

/// 日志严重程度 (OTLP 标准)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[repr(u8)]
pub enum LogSeverity {
    Trace = 1,
    Debug = 5,
    Info = 9,
    Warn = 13,
    Error = 17,
    Fatal = 21,
}

/// 日志体 (可以是多种类型)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogBody {
    /// 字符串
    String(String),
    /// 结构化数据 (JSON)
    Structured(serde_json::Value),
    /// 二进制数据
    Binary(Vec<u8>),
}
```

### 与 Trace 关联

```rust
impl LogRecord {
    /// 创建关联到 Span 的日志
    pub fn with_span(span: &Span, body: impl Into<String>) -> Self {
        Self {
            timestamp: current_time_nanos(),
            severity: LogSeverity::Info,
            body: LogBody::String(body.into()),
            attributes: HashMap::new(),
            trace_context: Some(SpanContext {
                trace_id: span.trace_id,
                span_id: span.span_id,
                trace_flags: 0,
                trace_state: None,
            }),
        }
    }
}
```

---

## 因果关系建模

### 因果链的 Rust 表示

```rust
/// 因果链 (Causality Chain)
pub struct CausalityChain {
    /// 根 Span
    root: Span,

    /// 子 Span 树
    children: HashMap<SpanId, Vec<Span>>,
}

impl CausalityChain {
    /// 从 Span 列表重建因果链
    pub fn from_spans(spans: Vec<Span>) -> Self {
        let mut root = None;
        let mut children: HashMap<SpanId, Vec<Span>> = HashMap::new();

        for span in spans {
            if span.parent_span_id.is_none() {
                root = Some(span);
            } else {
                let parent_id = span.parent_span_id.unwrap();
                children.entry(parent_id).or_default().push(span);
            }
        }

        Self {
            root: root.expect("No root span found"),
            children,
        }
    }

    /// 遍历因果链 (DFS)
    pub fn traverse<F>(&self, mut visitor: F)
    where
        F: FnMut(&Span, usize), // (span, depth)
    {
        self.traverse_impl(&self.root, 0, &mut visitor);
    }

    fn traverse_impl<F>(&self, span: &Span, depth: usize, visitor: &mut F)
    where
        F: FnMut(&Span, usize),
    {
        visitor(span, depth);

        if let Some(children) = self.children.get(&span.span_id) {
            for child in children {
                self.traverse_impl(child, depth + 1, visitor);
            }
        }
    }
}
```

---

## 属性系统类型安全设计

### 类型安全的属性值

```rust
/// 属性值 (OTLP Any Value)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    Bytes(Vec<u8>),
    Array(Vec<AttributeValue>),
    Map(HashMap<String, AttributeValue>),
}

impl AttributeValue {
    /// 类型安全的访问器
    pub fn as_string(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(i) => Some(*i),
            _ => None,
        }
    }

    pub fn as_double(&self) -> Option<f64> {
        match self {
            Self::Double(d) => Some(*d),
            _ => None,
        }
    }
}

/// From trait 实现 (零成本转换)
impl From<String> for AttributeValue {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

impl From<&str> for AttributeValue {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<i64> for AttributeValue {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl From<f64> for AttributeValue {
    fn from(d: f64) -> Self {
        Self::Double(d)
    }
}
```

---

## 总结

### 核心映射关系

| OTLP 概念 | Rust 类型 | 保证 |
|----------|-----------|------|
| Resource | `struct Resource` | 不可变性 |
| Trace | `struct Span` | 因果一致性 |
| TraceId | `struct TraceId([u8; 16])` | 全局唯一 |
| Metric | `enum MetricType` | 类型安全 |
| Log | `struct LogRecord` | 结构化 |
| Attribute | `enum AttributeValue` | 类型安全 |

### 下一步

阅读 [03_distributed_system_design.md](./03_distributed_system_design.md) 了解如何基于这些语义模型构建分布式系统。

---

**参考资料**:

- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Rust Type System](https://doc.rust-lang.org/book/ch10-00-generics.html)
