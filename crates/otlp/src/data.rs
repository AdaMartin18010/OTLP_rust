//! # OTLP数据模型模块
//!
//! 定义OTLP协议的数据结构，支持Rust 1.92的类型系统特性。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
//use opentelemetry::trace::{SpanId, TraceId};
//use opentelemetry::KeyValue;

/// 遥测数据类型
/// 
/// 遵循 OTLP 1.10 规范
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum TelemetryDataType {
    /// 追踪数据 (Stable)
    #[default]
    Trace,
    /// 指标数据 (Stable)
    Metric,
    /// 日志数据 (Stable)
    Log,
    /// 性能分析数据 (Development)
    /// 
    /// 注意：Profiles 信号目前处于开发阶段，API 可能会变化
    Profile,
}

/// 遥测数据基类
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TelemetryData {
    /// 数据类型
    pub data_type: TelemetryDataType,
    /// 时间戳
    pub timestamp: u64,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
    /// 作用域属性
    pub scope_attributes: HashMap<String, String>,
    /// 数据内容
    pub content: TelemetryContent,
}

/// 遥测数据内容
/// 
/// 遵循 OTLP 1.10 规范，支持所有信号类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TelemetryContent {
    /// 追踪数据
    Trace(TraceData),
    /// 指标数据
    Metric(MetricData),
    /// 日志数据
    Log(LogData),
    /// 性能分析数据 (Development)
    Profile(ProfileData),
}

impl Default for TelemetryContent {
    fn default() -> Self {
        Self::Trace(TraceData::default())
    }
}

impl TelemetryContent {
    /// 获取内容类型
    pub fn content_type(&self) -> &'static str {
        match self {
            Self::Trace(_) => "trace",
            Self::Metric(_) => "metric",
            Self::Log(_) => "log",
            Self::Profile(_) => "profile",
        }
    }
    
    /// 获取数据点数量估算
    pub fn data_point_count(&self) -> usize {
        match self {
            Self::Trace(t) => 1 + t.events.len(),
            Self::Metric(m) => m.data_points.len(),
            Self::Log(_) => 1,
            Self::Profile(p) => p.samples.len(),
        }
    }
}

/// 追踪数据
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TraceData {
    /// 追踪ID
    pub trace_id: String,
    /// 跨度ID
    pub span_id: String,
    /// 父跨度ID
    pub parent_span_id: Option<String>,
    /// 操作名称
    pub name: String,
    /// 跨度类型
    pub span_kind: SpanKind,
    /// 开始时间
    pub start_time: u64,
    /// 结束时间
    pub end_time: u64,
    /// 状态
    pub status: SpanStatus,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 事件
    pub events: Vec<SpanEvent>,
    /// 链接
    pub links: Vec<SpanLink>,
}

/// 跨度类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub enum SpanKind {
    /// 内部跨度
    #[default]
    Internal,
    /// 服务器跨度
    Server,
    /// 客户端跨度
    Client,
    /// 生产者跨度
    Producer,
    /// 消费者跨度
    Consumer,
}


/// 跨度状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanStatus {
    /// 状态代码
    pub code: StatusCode,
    /// 状态消息
    pub message: Option<String>,
}

impl Default for SpanStatus {
    fn default() -> Self {
        Self {
            code: StatusCode::Ok,
            message: None,
        }
    }
}

/// 状态代码
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StatusCode {
    /// 未设置
    Unset,
    /// 成功
    Ok,
    /// 错误
    Error,
}

/// 属性值
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AttributeValue {
    /// 字符串值
    String(String),
    /// 布尔值
    Bool(bool),
    /// 整数
    Int(i64),
    /// 浮点数
    Double(f64),
    /// 字符串数组
    StringArray(Vec<String>),
    /// 布尔数组
    BoolArray(Vec<bool>),
    /// 整数数组
    IntArray(Vec<i64>),
    /// 浮点数数组
    DoubleArray(Vec<f64>),
}

/// 跨度事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanEvent {
    /// 时间戳
    pub timestamp: u64,
    /// 名称
    pub name: String,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
}

/// 跨度链接
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanLink {
    /// 追踪ID
    pub trace_id: String,
    /// 跨度ID
    pub span_id: String,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
}

/// 指标数据
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MetricData {
    /// 指标名称
    pub name: String,
    /// 指标描述
    pub description: String,
    /// 指标单位
    pub unit: String,
    /// 指标类型
    pub metric_type: MetricType,
    /// 数据点
    pub data_points: Vec<DataPoint>,
}

/// 指标类型
/// 
/// 遵循 OTLP 1.10 规范，包含所有标准指标类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum MetricType {
    /// 计数器 - 单调递增的累积值
    #[default]
    Counter,
    /// 仪表 - 可增可减的瞬时值
    Gauge,
    /// 直方图 - 值的分布统计
    Histogram,
    /// 指数直方图 - 使用指数桶的直方图 (OTLP 1.10+)
    ExponentialHistogram,
    /// 摘要 - 分位数摘要
    Summary,
}

/// 数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    /// 时间戳
    pub timestamp: u64,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 值
    pub value: DataPointValue,
}

/// 数据点值
/// 
/// 支持所有 OTLP 指标类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataPointValue {
    /// 数值
    Number(f64),
    /// 整数 (用于某些特定的计数器)
    Int(i64),
    /// 直方图
    Histogram(HistogramData),
    /// 指数直方图 (OTLP 1.10+)
    ExponentialHistogram(ExponentialHistogramData),
    /// 摘要
    Summary(SummaryData),
}

/// 直方图数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramData {
    /// 计数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 桶
    pub buckets: Vec<HistogramBucket>,
}

/// 直方图桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    /// 计数
    pub count: u64,
    /// 上限
    pub upper_bound: f64,
}

/// 摘要数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SummaryData {
    /// 计数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 分位数
    pub quantiles: Vec<Quantile>,
}

/// 指数直方图数据 (OTLP 1.10+)
/// 
/// 使用指数桶分布的直方图，更高效地表示大范围数值分布
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExponentialHistogramData {
    /// 计数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 最小值（可选）
    pub min: Option<f64>,
    /// 最大值（可选）
    pub max: Option<f64>,
    /// 桶的规模因子（决定桶的边界）
    pub scale: i32,
    /// 零计数（值恰好为零的计数）
    pub zero_count: u64,
    /// 正值桶
    pub positive_buckets: ExponentialHistogramBuckets,
    /// 负值桶
    pub negative_buckets: ExponentialHistogramBuckets,
}

/// 指数直方图桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExponentialHistogramBuckets {
    /// 偏移量
    pub offset: i32,
    /// 桶计数
    pub bucket_counts: Vec<u64>,
}

/// 分位数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Quantile {
    /// 分位数
    pub quantile: f64,
    /// 值
    pub value: f64,
}

/// Complete Log data structure per OTLP 1.10
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogData {
    /// Timestamp when the log was emitted (nanoseconds since Unix epoch)
    pub timestamp: u64,
    /// Timestamp when the log was observed (nanoseconds since Unix epoch)
    pub observed_timestamp: u64,
    /// Severity level
    pub severity: SeverityLevel,
    /// Severity text (optional custom text)
    pub severity_text: Option<String>,
    /// Body of the log (string or structured)
    pub body: LogBody,
    /// Attributes
    pub attributes: HashMap<String, AttributeValue>,
    /// Resource attributes (inherited from TelemetryData context)
    pub resource_attributes: HashMap<String, AttributeValue>,
    /// Trace context (for correlation)
    pub trace_context: Option<LogTraceContext>,
    /// Dropped attributes count
    pub dropped_attributes_count: u32,
    /// Flags
    pub flags: u32,
}

impl Default for LogData {
    fn default() -> Self {
        Self {
            timestamp: 0,
            observed_timestamp: 0,
            severity: SeverityLevel::Info,
            severity_text: None,
            body: LogBody::Empty,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        }
    }
}

impl LogData {
    /// Create a new log with the current timestamp
    pub fn new() -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;
        
        Self {
            timestamp: now,
            observed_timestamp: now,
            severity: SeverityLevel::Info,
            severity_text: None,
            body: LogBody::Empty,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        }
    }

    /// Create a log with a string body
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.body = LogBody::String(message.into());
        self
    }

    /// Set severity level
    pub fn with_severity(mut self, severity: SeverityLevel) -> Self {
        self.severity = severity;
        self.severity_text = Some(severity.as_str().to_string());
        self
    }

    /// Set severity with custom text
    pub fn with_severity_text(mut self, severity: SeverityLevel, text: impl Into<String>) -> Self {
        self.severity = severity;
        self.severity_text = Some(text.into());
        self
    }

    /// Set structured body
    pub fn with_structured_body(mut self, body: HashMap<String, AttributeValue>) -> Self {
        self.body = LogBody::Structured(body);
        self
    }

    /// Set array body
    pub fn with_array_body(mut self, body: Vec<AttributeValue>) -> Self {
        self.body = LogBody::Array(body);
        self
    }

    /// Add an attribute
    pub fn with_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.attributes.insert(key.into(), value);
        self
    }

    /// Add a string attribute
    pub fn with_string_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.insert(key.into(), AttributeValue::String(value.into()));
        self
    }

    /// Add resource attribute
    pub fn with_resource_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.resource_attributes.insert(key.into(), value);
        self
    }

    /// Set trace context for correlation
    pub fn with_trace_context(mut self, trace_id: impl Into<String>, span_id: impl Into<String>) -> Self {
        self.trace_context = Some(LogTraceContext {
            trace_id: trace_id.into(),
            span_id: span_id.into(),
            trace_flags: 0,
        });
        self
    }

    /// Set trace context with flags
    pub fn with_trace_context_full(
        mut self,
        trace_id: impl Into<String>,
        span_id: impl Into<String>,
        trace_flags: u8,
    ) -> Self {
        self.trace_context = Some(LogTraceContext {
            trace_id: trace_id.into(),
            span_id: span_id.into(),
            trace_flags,
        });
        self
    }

    /// Get the log message as a string (if body is a string)
    pub fn message(&self) -> Option<&str> {
        match &self.body {
            LogBody::String(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Check if severity is at least the given level
    pub fn is_at_least(&self, level: SeverityLevel) -> bool {
        self.severity as u8 >= level as u8
    }

    /// Get severity as numeric value
    pub fn severity_number(&self) -> u8 {
        self.severity as u8
    }
}

/// Severity levels following OpenTelemetry spec
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[derive(Default)]
pub enum SeverityLevel {
    /// TRACE level (1)
    Trace = 1,
    /// TRACE2 level (2)
    Trace2 = 2,
    /// TRACE3 level (3)
    Trace3 = 3,
    /// TRACE4 level (4)
    Trace4 = 4,
    /// DEBUG level (5)
    Debug = 5,
    /// DEBUG2 level (6)
    Debug2 = 6,
    /// DEBUG3 level (7)
    Debug3 = 7,
    /// DEBUG4 level (8)
    Debug4 = 8,
    /// INFO level (9)
    #[default]
    Info = 9,
    /// INFO2 level (10)
    Info2 = 10,
    /// INFO3 level (11)
    Info3 = 11,
    /// INFO4 level (12)
    Info4 = 12,
    /// WARN level (13)
    Warn = 13,
    /// WARN2 level (14)
    Warn2 = 14,
    /// WARN3 level (15)
    Warn3 = 15,
    /// WARN4 level (16)
    Warn4 = 16,
    /// ERROR level (17)
    Error = 17,
    /// ERROR2 level (18)
    Error2 = 18,
    /// ERROR3 level (19)
    Error3 = 19,
    /// ERROR4 level (20)
    Error4 = 20,
    /// FATAL level (21)
    Fatal = 21,
    /// FATAL2 level (22)
    Fatal2 = 22,
    /// FATAL3 level (23)
    Fatal3 = 23,
    /// FATAL4 level (24)
    Fatal4 = 24,
}

impl SeverityLevel {
    /// Get severity level as string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Trace => "TRACE",
            Self::Trace2 => "TRACE2",
            Self::Trace3 => "TRACE3",
            Self::Trace4 => "TRACE4",
            Self::Debug => "DEBUG",
            Self::Debug2 => "DEBUG2",
            Self::Debug3 => "DEBUG3",
            Self::Debug4 => "DEBUG4",
            Self::Info => "INFO",
            Self::Info2 => "INFO2",
            Self::Info3 => "INFO3",
            Self::Info4 => "INFO4",
            Self::Warn => "WARN",
            Self::Warn2 => "WARN2",
            Self::Warn3 => "WARN3",
            Self::Warn4 => "WARN4",
            Self::Error => "ERROR",
            Self::Error2 => "ERROR2",
            Self::Error3 => "ERROR3",
            Self::Error4 => "ERROR4",
            Self::Fatal => "FATAL",
            Self::Fatal2 => "FATAL2",
            Self::Fatal3 => "FATAL3",
            Self::Fatal4 => "FATAL4",
        }
    }

    /// Get short severity name (for compact logging)
    pub fn short_name(&self) -> &'static str {
        match self {
            Self::Trace | Self::Trace2 | Self::Trace3 | Self::Trace4 => "TRC",
            Self::Debug | Self::Debug2 | Self::Debug3 | Self::Debug4 => "DBG",
            Self::Info | Self::Info2 | Self::Info3 | Self::Info4 => "INF",
            Self::Warn | Self::Warn2 | Self::Warn3 | Self::Warn4 => "WRN",
            Self::Error | Self::Error2 | Self::Error3 | Self::Error4 => "ERR",
            Self::Fatal | Self::Fatal2 | Self::Fatal3 | Self::Fatal4 => "FTL",
        }
    }

    /// Parse severity from string (case-insensitive)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_uppercase().as_str() {
            "TRACE" | "TRC" => Some(Self::Trace),
            "TRACE2" => Some(Self::Trace2),
            "TRACE3" => Some(Self::Trace3),
            "TRACE4" => Some(Self::Trace4),
            "DEBUG" | "DBG" => Some(Self::Debug),
            "DEBUG2" => Some(Self::Debug2),
            "DEBUG3" => Some(Self::Debug3),
            "DEBUG4" => Some(Self::Debug4),
            "INFO" | "INF" => Some(Self::Info),
            "INFO2" => Some(Self::Info2),
            "INFO3" => Some(Self::Info3),
            "INFO4" => Some(Self::Info4),
            "WARN" | "WARNING" | "WRN" => Some(Self::Warn),
            "WARN2" => Some(Self::Warn2),
            "WARN3" => Some(Self::Warn3),
            "WARN4" => Some(Self::Warn4),
            "ERROR" | "ERR" => Some(Self::Error),
            "ERROR2" => Some(Self::Error2),
            "ERROR3" => Some(Self::Error3),
            "ERROR4" => Some(Self::Error4),
            "FATAL" | "FTL" => Some(Self::Fatal),
            "FATAL2" => Some(Self::Fatal2),
            "FATAL3" => Some(Self::Fatal3),
            "FATAL4" => Some(Self::Fatal4),
            _ => None,
        }
    }

    /// Check if this is an error level or higher
    pub fn is_error(&self) -> bool {
        *self as u8 >= Self::Error as u8
    }

    /// Check if this is a warning level or higher
    pub fn is_warn(&self) -> bool {
        *self as u8 >= Self::Warn as u8
    }
}

/// Log body types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogBody {
    /// Empty body
    Empty,
    /// String body (plain text message)
    String(String),
    /// Structured body (key-value pairs)
    Structured(HashMap<String, AttributeValue>),
    /// Array body (list of values)
    Array(Vec<AttributeValue>),
}

impl LogBody {
    /// Check if body is empty
    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    /// Get as string if it's a string body
    pub fn as_string(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Get as structured if it's a structured body
    pub fn as_structured(&self) -> Option<&HashMap<String, AttributeValue>> {
        match self {
            Self::Structured(map) => Some(map),
            _ => None,
        }
    }

    /// Get as array if it's an array body
    pub fn as_array(&self) -> Option<&Vec<AttributeValue>> {
        match self {
            Self::Array(arr) => Some(arr),
            _ => None,
        }
    }

    /// Convert to a display string
    pub fn to_display_string(&self) -> String {
        match self {
            Self::Empty => String::new(),
            Self::String(s) => s.clone(),
            Self::Structured(map) => {
                serde_json::to_string(map).unwrap_or_default()
            }
            Self::Array(arr) => {
                serde_json::to_string(arr).unwrap_or_default()
            }
        }
    }

    /// Get the size of the body in bytes (estimate)
    pub fn size(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::String(s) => s.len(),
            Self::Structured(map) => map.len() * 32, // rough estimate
            Self::Array(arr) => arr.len() * 16, // rough estimate
        }
    }
}

impl Default for LogBody {
    fn default() -> Self {
        Self::Empty
    }
}

impl From<String> for LogBody {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

impl From<&str> for LogBody {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<HashMap<String, AttributeValue>> for LogBody {
    fn from(map: HashMap<String, AttributeValue>) -> Self {
        Self::Structured(map)
    }
}

/// Trace context for log correlation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogTraceContext {
    /// Trace ID (16 bytes hex encoded)
    pub trace_id: String,
    /// Span ID (8 bytes hex encoded)
    pub span_id: String,
    /// Trace flags (e.g., sampled flag)
    pub trace_flags: u8,
}

impl LogTraceContext {
    /// Check if this trace is sampled
    pub fn is_sampled(&self) -> bool {
        (self.trace_flags & 0x01) != 0
    }

    /// Create a new trace context
    pub fn new(trace_id: impl Into<String>, span_id: impl Into<String>) -> Self {
        Self {
            trace_id: trace_id.into(),
            span_id: span_id.into(),
            trace_flags: 0,
        }
    }

    /// Create a new trace context with sampling flag
    pub fn with_sampling(trace_id: impl Into<String>, span_id: impl Into<String>, sampled: bool) -> Self {
        Self {
            trace_id: trace_id.into(),
            span_id: span_id.into(),
            trace_flags: if sampled { 0x01 } else { 0x00 },
        }
    }
}

/// Legacy LogSeverity alias for backward compatibility
pub type LogSeverity = SeverityLevel;

/// 性能分析数据 (OTLP Profiles Signal - Development)
/// 
/// 注意：Profiles 信号目前处于开发阶段，API 可能会变化
/// 参考：https://opentelemetry.io/docs/specs/otlp/
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ProfileData {
    /// 采样类型（如 CPU、内存、锁等）
    pub sample_types: Vec<SampleType>,
    /// 采样数据
    pub samples: Vec<Sample>,
    /// 映射信息（库、可执行文件等）
    pub mappings: Vec<Mapping>,
    /// 位置信息（函数调用位置）
    pub locations: Vec<Location>,
    /// 函数信息
    pub functions: Vec<Function>,
    /// 时间戳
    pub timestamp: u64,
    /// 采样持续时间（纳秒）
    pub duration_nanos: u64,
    /// 周期类型（如 CPU 周期、内存字节等）
    pub period_type: Option<SampleType>,
    /// 周期值
    pub period: i64,
}

/// 采样类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SampleType {
    /// 类型名称（如 "cpu", "memory", "lock"）
    pub r#type: String,
    /// 单位（如 "nanoseconds", "bytes", "count"）
    pub unit: String,
}

/// 采样数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Sample {
    /// 位置 ID 列表（指向位置表）
    pub location_ids: Vec<u64>,
    /// 采样值（与 sample_types 对应）
    pub values: Vec<i64>,
    /// 标签属性
    pub labels: Vec<Label>,
}

/// 标签
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Label {
    /// 键
    pub key: String,
    /// 字符串值
    pub str_value: Option<String>,
    /// 数值
    pub num_value: Option<i64>,
}

/// 映射信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mapping {
    /// 映射 ID
    pub id: u64,
    /// 内存起始地址
    pub memory_start: u64,
    /// 内存限制
    pub memory_limit: u64,
    /// 文件偏移
    pub file_offset: u64,
    /// 文件名
    pub filename: String,
    /// 构建 ID
    pub build_id: String,
}

/// 位置信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// 位置 ID
    pub id: u64,
    /// 映射 ID
    pub mapping_id: u64,
    /// 地址
    pub address: u64,
    /// 行号信息
    pub lines: Vec<Line>,
}

/// 行信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Line {
    /// 函数 ID
    pub function_id: u64,
    /// 行号
    pub line: i64,
    /// 列号
    pub column: i64,
}

/// 函数信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Function {
    /// 函数 ID
    pub id: u64,
    /// 函数名
    pub name: String,
    /// 系统名称（如 C++ 修饰名）
    pub system_name: String,
    /// 文件名
    pub filename: String,
    /// 起始行号
    pub start_line: i64,
}

impl TelemetryData {
    /// 创建新的遥测数据
    pub fn new(data_type: TelemetryDataType, content: TelemetryContent) -> Self {
        Self {
            data_type,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content,
        }
    }

    /// 创建追踪数据
    pub fn trace(name: impl Into<String>) -> Self {
        let trace_id = format!("{:032x}", rand::random::<u128>());
        let span_id = format!("{:016x}", rand::random::<u64>());

        let trace_data = TraceData {
            trace_id: trace_id.clone(),
            span_id: span_id.clone(),
            parent_span_id: None,
            name: name.into(),
            span_kind: SpanKind::Internal,
            start_time: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            end_time: 0,
            status: SpanStatus::default(),
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        };

        Self::new(
            TelemetryDataType::Trace,
            TelemetryContent::Trace(trace_data),
        )
    }

    /// 创建指标数据
    pub fn metric(name: impl Into<String>, metric_type: MetricType) -> Self {
        let metric_data = MetricData {
            name: name.into(),
            description: String::new(),
            unit: String::new(),
            metric_type,
            data_points: Vec::new(),
        };

        Self::new(
            TelemetryDataType::Metric,
            TelemetryContent::Metric(metric_data),
        )
    }

    /// 创建日志数据
    pub fn log(message: impl Into<String>, severity: LogSeverity) -> Self {
        let log_data = LogData {
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            observed_timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            severity,
            severity_text: Some(format!("{:?}", severity)),
            body: LogBody::String(message.into()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        };

        Self::new(TelemetryDataType::Log, TelemetryContent::Log(log_data))
    }

    /// 创建性能分析数据 (Development)
    /// 
    /// 注意：Profiles 信号目前处于开发阶段
    pub fn profile(sample_type: SampleType) -> Self {
        let profile_data = ProfileData {
            sample_types: vec![sample_type],
            samples: Vec::new(),
            mappings: Vec::new(),
            locations: Vec::new(),
            functions: Vec::new(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            duration_nanos: 0,
            period_type: None,
            period: 0,
        };

        Self::new(TelemetryDataType::Profile, TelemetryContent::Profile(profile_data))
    }

    /// 添加资源属性
    pub fn with_resource_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.resource_attributes.insert(key.into(), value.into());
        self
    }

    /// 添加作用域属性
    pub fn with_scope_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.scope_attributes.insert(key.into(), value.into());
        self
    }

    /// 添加属性（针对追踪数据）
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data
                .attributes
                .insert(key.into(), AttributeValue::String(value.into()));
        }
        self
    }

    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: impl Into<String>, value: f64) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data
                .attributes
                .insert(key.into(), AttributeValue::Double(value));
        }
        self
    }

    /// 添加布尔属性
    pub fn with_bool_attribute(mut self, key: impl Into<String>, value: bool) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data
                .attributes
                .insert(key.into(), AttributeValue::Bool(value));
        }
        self
    }

    /// 设置跨度状态
    pub fn with_status(mut self, code: StatusCode, message: Option<String>) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.status = SpanStatus { code, message };
        }
        self
    }

    /// 添加事件
    pub fn with_event(
        mut self,
        name: impl Into<String>,
        attributes: HashMap<String, AttributeValue>,
    ) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            let event = SpanEvent {
                timestamp: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_nanos() as u64,
                name: name.into(),
                attributes,
            };
            trace_data.events.push(event);
        }
        self
    }

    /// 完成追踪（设置结束时间）
    pub fn finish(mut self) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.end_time = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64;
        }
        self
    }

    /// 获取数据大小（字节）
    pub fn size(&self) -> usize {
        // 简化的大小计算，实际实现中可能需要更精确的计算
        let mut size = 0;

        // 基础字段
        size += 8; // timestamp
        size += self.resource_attributes.len() * 32; // 估算
        size += self.scope_attributes.len() * 32; // 估算

        // 内容大小
        match &self.content {
            TelemetryContent::Trace(trace) => {
                size += trace.trace_id.len();
                size += trace.span_id.len();
                size += trace.name.len();
                size += trace.attributes.len() * 32;
                size += trace.events.len() * 64;
                size += trace.links.len() * 64;
            }
            TelemetryContent::Metric(metric) => {
                size += metric.name.len();
                size += metric.description.len();
                size += metric.unit.len();
                size += metric.data_points.len() * 64;
            }
            TelemetryContent::Log(log) => {
                size += log.body.size();
                size += log.severity_text.as_ref().map(|s| s.len()).unwrap_or(0);
                size += log.attributes.len() * 32;
                size += 8; // dropped_attributes_count + flags
            }
            TelemetryContent::Profile(profile) => {
                size += profile.sample_types.len() * 32;
                size += profile.samples.len() * 128;
                size += profile.functions.len() * 64;
                size += profile.locations.len() * 48;
            }
        }

        size
    }

    /// 检查数据是否有效
    pub fn is_valid(&self) -> bool {
        match &self.content {
            TelemetryContent::Trace(trace) => {
                !trace.trace_id.is_empty() && !trace.span_id.is_empty() && !trace.name.is_empty()
            }
            TelemetryContent::Metric(metric) => {
                !metric.name.is_empty() && !metric.data_points.is_empty()
            }
            TelemetryContent::Log(log) => !log.body.is_empty(),
            TelemetryContent::Profile(profile) => {
                !profile.sample_types.is_empty() && !profile.samples.is_empty()
            }
        }
    }
}

impl std::fmt::Display for AttributeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AttributeValue::String(s) => write!(f, "{}", s),
            AttributeValue::Bool(b) => write!(f, "{}", b),
            AttributeValue::Int(i) => write!(f, "{}", i),
            AttributeValue::Double(d) => write!(f, "{}", d),
            AttributeValue::StringArray(arr) => write!(f, "{:?}", arr),
            AttributeValue::BoolArray(arr) => write!(f, "{:?}", arr),
            AttributeValue::IntArray(arr) => write!(f, "{:?}", arr),
            AttributeValue::DoubleArray(arr) => write!(f, "{:?}", arr),
        }
    }
}

impl AttributeValue {
    /// 转换为格式化字符串（避免与 Display::to_string 冲突）
    pub fn to_formatted_string(&self) -> String {
        match self {
            AttributeValue::Double(v) => format!("{:.2}", v),
            _ => format!("{}", self),
        }
    }

    /// 获取类型名称
    pub fn type_name(&self) -> &'static str {
        match self {
            AttributeValue::String(_) => "string",
            AttributeValue::Bool(_) => "bool",
            AttributeValue::Int(_) => "int",
            AttributeValue::Double(_) => "double",
            AttributeValue::StringArray(_) => "string_array",
            AttributeValue::BoolArray(_) => "bool_array",
            AttributeValue::IntArray(_) => "int_array",
            AttributeValue::DoubleArray(_) => "double_array",
        }
    }
}

// From implementations for convenient conversion
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

impl From<bool> for AttributeValue {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<i64> for AttributeValue {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl From<i32> for AttributeValue {
    fn from(i: i32) -> Self {
        Self::Int(i as i64)
    }
}

impl From<f64> for AttributeValue {
    fn from(f: f64) -> Self {
        Self::Double(f)
    }
}

impl From<f32> for AttributeValue {
    fn from(f: f32) -> Self {
        Self::Double(f as f64)
    }
}

impl From<Vec<String>> for AttributeValue {
    fn from(v: Vec<String>) -> Self {
        Self::StringArray(v)
    }
}

impl From<Vec<bool>> for AttributeValue {
    fn from(v: Vec<bool>) -> Self {
        Self::BoolArray(v)
    }
}

impl From<Vec<i64>> for AttributeValue {
    fn from(v: Vec<i64>) -> Self {
        Self::IntArray(v)
    }
}

impl From<Vec<f64>> for AttributeValue {
    fn from(v: Vec<f64>) -> Self {
        Self::DoubleArray(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_telemetry_data_creation() {
        let trace_data = TelemetryData::trace("test-operation");
        assert_eq!(trace_data.data_type, TelemetryDataType::Trace);
        assert!(trace_data.is_valid());

        let metric_data = TelemetryData::metric("test-metric", MetricType::Counter);
        assert_eq!(metric_data.data_type, TelemetryDataType::Metric);

        let log_data = TelemetryData::log("test message", LogSeverity::Info);
        assert_eq!(log_data.data_type, TelemetryDataType::Log);
    }

    #[test]
    fn test_trace_data_attributes() {
        let trace_data = TelemetryData::trace("test-operation")
            .with_attribute("service.name", "test-service")
            .with_numeric_attribute("duration", 100.0)
            .with_bool_attribute("success", true)
            .with_status(StatusCode::Ok, Some("success".to_string()));

        if let TelemetryContent::Trace(trace) = &trace_data.content {
            assert_eq!(trace.name, "test-operation");
            assert!(trace.attributes.contains_key("service.name"));
            assert!(trace.attributes.contains_key("duration"));
            assert!(trace.attributes.contains_key("success"));
            assert_eq!(trace.status.code, StatusCode::Ok);
        }
    }

    #[test]
    fn test_attribute_value_conversion() {
        let string_attr = AttributeValue::String("test".to_string());
        assert_eq!(string_attr.to_formatted_string(), "test");
        assert_eq!(string_attr.type_name(), "string");

        let bool_attr = AttributeValue::Bool(true);
        assert_eq!(bool_attr.to_formatted_string(), "true");
        assert_eq!(bool_attr.type_name(), "bool");

        let int_attr = AttributeValue::Int(42);
        assert_eq!(int_attr.to_formatted_string(), "42");
        assert_eq!(int_attr.type_name(), "int");

        let double_attr = AttributeValue::Double(std::f64::consts::PI);
        assert_eq!(double_attr.to_formatted_string(), "3.14");
        assert_eq!(double_attr.type_name(), "double");
    }

    #[test]
    fn test_data_size_calculation() {
        let trace_data = TelemetryData::trace("test-operation").with_attribute("key", "value");

        let size = trace_data.size();
        assert!(size > 0);
    }
}
