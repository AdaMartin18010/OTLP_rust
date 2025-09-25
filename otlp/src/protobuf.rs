//! # OTLP Protobuf 集成模块
//!
//! 提供与OpenTelemetry protobuf定义的集成，支持完整的OTLP协议实现。

use crate::data::{LogData, MetricData, TelemetryContent, TelemetryData, TraceData};
use crate::error::{Result, DataError};
use prost::Message;

/// OTLP资源定义
#[derive(Clone, PartialEq, Message)]
pub struct Resource {
    #[prost(map = "string, message", tag = "1")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "2")]
    pub dropped_attributes_count: u32,
}

/// 属性值定义
#[derive(Clone, PartialEq, Message)]
pub struct AttributeValue {
    #[prost(oneof = "attribute_value::Value", tags = "1, 2, 3, 4, 5")]
    pub value: Option<attribute_value::Value>,
}

pub mod attribute_value {
    use prost::Oneof;

    #[derive(Clone, PartialEq, Oneof)]
    pub enum Value {
        #[prost(string, tag = "1")]
        StringValue(String),
        #[prost(bool, tag = "2")]
        BoolValue(bool),
        #[prost(int64, tag = "3")]
        IntValue(i64),
        #[prost(double, tag = "4")]
        DoubleValue(f64),
        #[prost(message, tag = "5")]
        ArrayValue(super::ArrayValue),
    }
}

/// 数组值定义
#[derive(Clone, PartialEq, Message)]
pub struct ArrayValue {
    #[prost(message, repeated, tag = "1")]
    pub values: Vec<AttributeValue>,
}

/// 作用域定义
#[derive(Clone, PartialEq, Message)]
pub struct Scope {
    #[prost(string, tag = "1")]
    pub name: String,
    #[prost(string, tag = "2")]
    pub version: String,
    #[prost(map = "string, message", tag = "3")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "4")]
    pub dropped_attributes_count: u32,
}

/// 追踪数据导出请求
#[derive(Clone, PartialEq, Message)]
pub struct ExportTraceServiceRequest {
    #[prost(message, repeated, tag = "1")]
    pub resource_spans: Vec<ResourceSpans>,
}

/// 追踪数据导出响应
#[derive(Clone, PartialEq, Message)]
pub struct ExportTraceServiceResponse {
    #[prost(message, optional, tag = "1")]
    pub partial_success: Option<ExportTracePartialSuccess>,
}

/// 指标数据导出请求
#[derive(Clone, PartialEq, Message)]
pub struct ExportMetricsServiceRequest {
    #[prost(message, repeated, tag = "1")]
    pub resource_metrics: Vec<ResourceMetrics>,
}

/// 指标数据导出响应
#[derive(Clone, PartialEq, Message)]
pub struct ExportMetricsServiceResponse {
    #[prost(message, optional, tag = "1")]
    pub partial_success: Option<ExportMetricsPartialSuccess>,
}

/// 日志数据导出请求
#[derive(Clone, PartialEq, Message)]
pub struct ExportLogsServiceRequest {
    #[prost(message, repeated, tag = "1")]
    pub resource_logs: Vec<ResourceLogs>,
}

/// 日志数据导出响应
#[derive(Clone, PartialEq, Message)]
pub struct ExportLogsServiceResponse {
    #[prost(message, optional, tag = "1")]
    pub partial_success: Option<ExportLogsPartialSuccess>,
}

/// 资源追踪数据
#[derive(Clone, PartialEq, Message)]
pub struct ResourceSpans {
    #[prost(message, optional, tag = "1")]
    pub resource: Option<Resource>,
    #[prost(message, repeated, tag = "2")]
    pub scope_spans: Vec<ScopeSpans>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 作用域追踪数据
#[derive(Clone, PartialEq, Message)]
pub struct ScopeSpans {
    #[prost(message, optional, tag = "1")]
    pub scope: Option<Scope>,
    #[prost(message, repeated, tag = "2")]
    pub spans: Vec<Span>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 跨度定义
#[derive(Clone, PartialEq, Message)]
pub struct Span {
    #[prost(bytes = "vec", tag = "1")]
    pub trace_id: Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub span_id: Vec<u8>,
    #[prost(string, tag = "3")]
    pub trace_state: String,
    #[prost(bytes = "vec", tag = "4")]
    pub parent_span_id: Vec<u8>,
    #[prost(string, tag = "5")]
    pub name: String,
    #[prost(enumeration = "SpanKind", tag = "6")]
    pub kind: i32,
    #[prost(fixed64, tag = "7")]
    pub start_time_unix_nano: u64,
    #[prost(fixed64, tag = "8")]
    pub end_time_unix_nano: u64,
    #[prost(map = "string, message", tag = "9")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "10")]
    pub dropped_attributes_count: u32,
    #[prost(message, repeated, tag = "11")]
    pub events: Vec<SpanEvent>,
    #[prost(uint32, tag = "12")]
    pub dropped_events_count: u32,
    #[prost(message, repeated, tag = "13")]
    pub links: Vec<SpanLink>,
    #[prost(uint32, tag = "14")]
    pub dropped_links_count: u32,
    #[prost(message, optional, tag = "15")]
    pub status: Option<Status>,
}

/// 跨度类型枚举
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum SpanKind {
    Unspecified = 0,
    Internal = 1,
    Server = 2,
    Client = 3,
    Producer = 4,
    Consumer = 5,
}

/// 跨度状态
#[derive(Clone, PartialEq, Message)]
pub struct Status {
    #[prost(enumeration = "StatusCode", tag = "1")]
    pub code: i32,
    #[prost(string, tag = "2")]
    pub message: String,
}

/// 状态代码枚举
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum StatusCode {
    Unset = 0,
    Ok = 1,
    Error = 2,
}

/// 跨度事件
#[derive(Clone, PartialEq, Message)]
pub struct SpanEvent {
    #[prost(fixed64, tag = "1")]
    pub time_unix_nano: u64,
    #[prost(string, tag = "2")]
    pub name: String,
    #[prost(map = "string, message", tag = "3")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "4")]
    pub dropped_attributes_count: u32,
}

/// 跨度链接
#[derive(Clone, PartialEq, Message)]
pub struct SpanLink {
    #[prost(bytes = "vec", tag = "1")]
    pub trace_id: Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub span_id: Vec<u8>,
    #[prost(string, tag = "3")]
    pub trace_state: String,
    #[prost(map = "string, message", tag = "4")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "5")]
    pub dropped_attributes_count: u32,
}

/// 资源指标数据
#[derive(Clone, PartialEq, Message)]
pub struct ResourceMetrics {
    #[prost(message, optional, tag = "1")]
    pub resource: Option<Resource>,
    #[prost(message, repeated, tag = "2")]
    pub scope_metrics: Vec<ScopeMetrics>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 作用域指标数据
#[derive(Clone, PartialEq, Message)]
pub struct ScopeMetrics {
    #[prost(message, optional, tag = "1")]
    pub scope: Option<Scope>,
    #[prost(message, repeated, tag = "2")]
    pub metrics: Vec<Metric>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 指标定义
#[derive(Clone, PartialEq, Message)]
pub struct Metric {
    #[prost(string, tag = "1")]
    pub name: String,
    #[prost(string, tag = "2")]
    pub description: String,
    #[prost(string, tag = "3")]
    pub unit: String,
    #[prost(oneof = "metric::Data", tags = "5, 7, 9, 10")]
    pub data: Option<metric::Data>,
}

pub mod metric {
    use prost::Oneof;

    #[derive(Clone, PartialEq, Oneof)]
    pub enum Data {
        #[prost(message, tag = "5")]
        Gauge(super::Gauge),
        #[prost(message, tag = "7")]
        Sum(super::Sum),
        #[prost(message, tag = "9")]
        Histogram(super::Histogram),
        #[prost(message, tag = "10")]
        Summary(super::Summary),
    }
}

/// 仪表指标
#[derive(Clone, PartialEq, Message)]
pub struct Gauge {
    #[prost(message, repeated, tag = "1")]
    pub data_points: Vec<NumberDataPoint>,
}

/// 求和指标
#[derive(Clone, PartialEq, Message)]
pub struct Sum {
    #[prost(message, repeated, tag = "1")]
    pub data_points: Vec<NumberDataPoint>,
    #[prost(enumeration = "AggregationTemporality", tag = "2")]
    pub aggregation_temporality: i32,
    #[prost(bool, tag = "3")]
    pub is_monotonic: bool,
}

/// 直方图指标
#[derive(Clone, PartialEq, Message)]
pub struct Histogram {
    #[prost(message, repeated, tag = "1")]
    pub data_points: Vec<HistogramDataPoint>,
    #[prost(enumeration = "AggregationTemporality", tag = "2")]
    pub aggregation_temporality: i32,
}

/// 摘要指标
#[derive(Clone, PartialEq, Message)]
pub struct Summary {
    #[prost(message, repeated, tag = "1")]
    pub data_points: Vec<SummaryDataPoint>,
}

/// 聚合时间性枚举
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum AggregationTemporality {
    Unspecified = 0,
    Delta = 1,
    Cumulative = 2,
}

/// 数值数据点
#[derive(Clone, PartialEq, Message)]
pub struct NumberDataPoint {
    #[prost(map = "string, message", tag = "7")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(fixed64, tag = "2")]
    pub start_time_unix_nano: u64,
    #[prost(fixed64, tag = "3")]
    pub time_unix_nano: u64,
    #[prost(oneof = "number_data_point::Value", tags = "4, 6")]
    pub value: Option<number_data_point::Value>,
    #[prost(message, repeated, tag = "5")]
    pub exemplars: Vec<Exemplar>,
    #[prost(uint32, tag = "8")]
    pub flags: u32,
}

pub mod number_data_point {
    use prost::Oneof;

    #[derive(Clone, PartialEq, Oneof)]
    pub enum Value {
        #[prost(double, tag = "4")]
        AsDouble(f64),
        #[prost(sfixed64, tag = "6")]
        AsInt(i64),
    }
}

/// 直方图数据点
#[derive(Clone, PartialEq, Message)]
pub struct HistogramDataPoint {
    #[prost(map = "string, message", tag = "9")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(fixed64, tag = "2")]
    pub start_time_unix_nano: u64,
    #[prost(fixed64, tag = "3")]
    pub time_unix_nano: u64,
    #[prost(fixed64, tag = "4")]
    pub count: u64,
    #[prost(double, tag = "5")]
    pub sum: f64,
    #[prost(double, repeated, tag = "6")]
    pub bucket_counts: Vec<f64>,
    #[prost(double, repeated, tag = "7")]
    pub explicit_bounds: Vec<f64>,
    #[prost(message, repeated, tag = "8")]
    pub exemplars: Vec<Exemplar>,
    #[prost(uint32, tag = "10")]
    pub flags: u32,
    #[prost(double, tag = "11")]
    pub min: f64,
    #[prost(double, tag = "12")]
    pub max: f64,
}

/// 摘要数据点
#[derive(Clone, PartialEq, Message)]
pub struct SummaryDataPoint {
    #[prost(map = "string, message", tag = "7")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(fixed64, tag = "2")]
    pub start_time_unix_nano: u64,
    #[prost(fixed64, tag = "3")]
    pub time_unix_nano: u64,
    #[prost(uint64, tag = "4")]
    pub count: u64,
    #[prost(double, tag = "5")]
    pub sum: f64,
    #[prost(message, repeated, tag = "6")]
    pub quantile_values: Vec<ValueAtQuantile>,
    #[prost(uint32, tag = "8")]
    pub flags: u32,
}

/// 分位数值
#[derive(Clone, PartialEq, Message)]
pub struct ValueAtQuantile {
    #[prost(double, tag = "1")]
    pub quantile: f64,
    #[prost(double, tag = "2")]
    pub value: f64,
}

/// 示例
#[derive(Clone, PartialEq, Message)]
pub struct Exemplar {
    #[prost(map = "string, message", tag = "7")]
    pub filtered_attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(fixed64, tag = "2")]
    pub time_unix_nano: u64,
    #[prost(oneof = "exemplar::Value", tags = "3, 6")]
    pub value: Option<exemplar::Value>,
    #[prost(bytes = "vec", tag = "4")]
    pub span_id: Vec<u8>,
    #[prost(bytes = "vec", tag = "5")]
    pub trace_id: Vec<u8>,
}

pub mod exemplar {
    use prost::Oneof;

    #[derive(Clone, PartialEq, Oneof)]
    pub enum Value {
        #[prost(double, tag = "3")]
        AsDouble(f64),
        #[prost(sfixed64, tag = "6")]
        AsInt(i64),
    }
}

/// 资源日志数据
#[derive(Clone, PartialEq, Message)]
pub struct ResourceLogs {
    #[prost(message, optional, tag = "1")]
    pub resource: Option<Resource>,
    #[prost(message, repeated, tag = "2")]
    pub scope_logs: Vec<ScopeLogs>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 作用域日志数据
#[derive(Clone, PartialEq, Message)]
pub struct ScopeLogs {
    #[prost(message, optional, tag = "1")]
    pub scope: Option<Scope>,
    #[prost(message, repeated, tag = "2")]
    pub log_records: Vec<LogRecord>,
    #[prost(string, tag = "3")]
    pub schema_url: String,
}

/// 日志记录
#[derive(Clone, PartialEq, Message)]
pub struct LogRecord {
    #[prost(fixed64, tag = "1")]
    pub time_unix_nano: u64,
    #[prost(message, optional, tag = "2")]
    pub observed_time_unix_nano: Option<u64>,
    #[prost(enumeration = "SeverityNumber", tag = "3")]
    pub severity_number: i32,
    #[prost(string, tag = "4")]
    pub severity_text: String,
    #[prost(message, optional, tag = "5")]
    pub body: Option<AttributeValue>,
    #[prost(map = "string, message", tag = "6")]
    pub attributes: ::std::collections::HashMap<String, AttributeValue>,
    #[prost(uint32, tag = "7")]
    pub dropped_attributes_count: u32,
    #[prost(uint32, tag = "8")]
    pub flags: u32,
    #[prost(bytes = "vec", tag = "9")]
    pub trace_id: Vec<u8>,
    #[prost(bytes = "vec", tag = "10")]
    pub span_id: Vec<u8>,
}

/// 严重程度枚举
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum SeverityNumber {
    Unspecified = 0,
    Trace = 1,
    Trace2 = 2,
    Trace3 = 3,
    Trace4 = 4,
    Debug = 5,
    Debug2 = 6,
    Debug3 = 7,
    Debug4 = 8,
    Info = 9,
    Info2 = 10,
    Info3 = 11,
    Info4 = 12,
    Warn = 13,
    Warn2 = 14,
    Warn3 = 15,
    Warn4 = 16,
    Error = 17,
    Error2 = 18,
    Error3 = 19,
    Error4 = 20,
    Fatal = 21,
    Fatal2 = 22,
    Fatal3 = 23,
    Fatal4 = 24,
}

/// 部分成功响应
#[derive(Clone, PartialEq, Message)]
pub struct ExportTracePartialSuccess {
    #[prost(int64, tag = "1")]
    pub rejected_spans: i64,
    #[prost(string, tag = "2")]
    pub error_message: String,
}

#[derive(Clone, PartialEq, Message)]
pub struct ExportMetricsPartialSuccess {
    #[prost(int64, tag = "1")]
    pub rejected_data_points: i64,
    #[prost(string, tag = "2")]
    pub error_message: String,
}

#[derive(Clone, PartialEq, Message)]
pub struct ExportLogsPartialSuccess {
    #[prost(int64, tag = "1")]
    pub rejected_log_records: i64,
    #[prost(string, tag = "2")]
    pub error_message: String,
}

/// Protobuf序列化器
pub struct ProtobufSerializer;

impl ProtobufSerializer {
    /// 序列化追踪数据
    pub fn serialize_traces(&self, data: Vec<TelemetryData>) -> Result<Vec<u8>> {
        let mut resource_spans = Vec::new();

        for telemetry_data in data {
            if let TelemetryContent::Trace(trace_data) = telemetry_data.content {
                let span = self.convert_trace_to_span(trace_data)?;
                let scope_spans = ScopeSpans {
                    scope: None,
                    spans: vec![span],
                    schema_url: String::new(),
                };
                let resource_span = ResourceSpans {
                    resource: None,
                    scope_spans: vec![scope_spans],
                    schema_url: String::new(),
                };
                resource_spans.push(resource_span);
            }
        }

        let request = ExportTraceServiceRequest { resource_spans };
        let mut buf = Vec::new();
        request
            .encode(&mut buf)
            .map_err(|e| DataError::Format { reason: e.to_string() })?;

        Ok(buf)
    }

    /// 序列化指标数据
    pub fn serialize_metrics(&self, data: Vec<TelemetryData>) -> Result<Vec<u8>> {
        let mut resource_metrics = Vec::new();

        for telemetry_data in data {
            if let TelemetryContent::Metric(metric_data) = telemetry_data.content {
                let metric = self.convert_metric_to_protobuf(metric_data)?;
                let scope_metrics = ScopeMetrics {
                    scope: None,
                    metrics: vec![metric],
                    schema_url: String::new(),
                };
                let resource_metric = ResourceMetrics {
                    resource: None,
                    scope_metrics: vec![scope_metrics],
                    schema_url: String::new(),
                };
                resource_metrics.push(resource_metric);
            }
        }

        let request = ExportMetricsServiceRequest { resource_metrics };
        let mut buf = Vec::new();
        request
            .encode(&mut buf)
            .map_err(|e| DataError::Format { reason: e.to_string() })?;

        Ok(buf)
    }

    /// 序列化日志数据
    pub fn serialize_logs(&self, data: Vec<TelemetryData>) -> Result<Vec<u8>> {
        let mut resource_logs = Vec::new();

        for telemetry_data in data {
            if let TelemetryContent::Log(log_data) = telemetry_data.content {
                let log_record = self.convert_log_to_protobuf(log_data)?;
                let scope_logs = ScopeLogs {
                    scope: None,
                    log_records: vec![log_record],
                    schema_url: String::new(),
                };
                let resource_log = ResourceLogs {
                    resource: None,
                    scope_logs: vec![scope_logs],
                    schema_url: String::new(),
                };
                resource_logs.push(resource_log);
            }
        }

        let request = ExportLogsServiceRequest { resource_logs };
        let mut buf = Vec::new();
        request
            .encode(&mut buf)
            .map_err(|e| DataError::Format { reason: e.to_string() })?;

        Ok(buf)
    }

    /// 转换追踪数据为protobuf格式
    fn convert_trace_to_span(&self, trace_data: TraceData) -> Result<Span> {
        let trace_id =
            hex::decode(&trace_data.trace_id).map_err(|e| DataError::Format { reason: format!("Invalid trace_id: {}", e) })?;

        let span_id = hex::decode(&trace_data.span_id).map_err(|e| DataError::Format { reason: format!("Invalid span_id: {}", e) })?;

        let parent_span_id = trace_data
            .parent_span_id
            .map(|id| hex::decode(id))
            .transpose()
            .map_err(|e| DataError::Format { reason: format!("Invalid parent_span_id: {}", e) })?
            .unwrap_or_default();

        let mut attributes = std::collections::HashMap::new();
        for (key, value) in trace_data.attributes {
            attributes.insert(key, self.convert_attribute_value(value));
        }

        let status = Some(Status {
            code: match trace_data.status.code {
                crate::data::StatusCode::Unset => StatusCode::Unset as i32,
                crate::data::StatusCode::Ok => StatusCode::Ok as i32,
                crate::data::StatusCode::Error => StatusCode::Error as i32,
            },
            message: trace_data.status.message.unwrap_or_default(),
        });

        Ok(Span {
            trace_id,
            span_id,
            trace_state: String::new(),
            parent_span_id,
            name: trace_data.name,
            kind: SpanKind::Internal as i32,
            start_time_unix_nano: trace_data.start_time,
            end_time_unix_nano: trace_data.end_time,
            attributes,
            dropped_attributes_count: 0,
            events: Vec::new(),
            dropped_events_count: 0,
            links: Vec::new(),
            dropped_links_count: 0,
            status,
        })
    }

    /// 转换指标数据为protobuf格式
    fn convert_metric_to_protobuf(&self, metric_data: MetricData) -> Result<Metric> {
        let mut data_points = Vec::new();

        for data_point in metric_data.data_points {
            let attributes = std::collections::HashMap::new();
            let value = match data_point.value {
                crate::data::DataPointValue::Number(value) => {
                    Some(number_data_point::Value::AsDouble(value))
                }
                _ => None,
            };

            let number_data_point = NumberDataPoint {
                attributes,
                start_time_unix_nano: 0,
                time_unix_nano: data_point.timestamp,
                value,
                exemplars: Vec::new(),
                flags: 0,
            };

            data_points.push(number_data_point);
        }

        let data = match metric_data.metric_type {
            crate::data::MetricType::Counter => Some(metric::Data::Sum(Sum {
                data_points,
                aggregation_temporality: AggregationTemporality::Cumulative as i32,
                is_monotonic: true,
            })),
            crate::data::MetricType::Gauge => Some(metric::Data::Gauge(Gauge { data_points })),
            _ => None,
        };

        Ok(Metric {
            name: metric_data.name,
            description: metric_data.description,
            unit: metric_data.unit,
            data,
        })
    }

    /// 转换日志数据为protobuf格式
    fn convert_log_to_protobuf(&self, log_data: LogData) -> Result<LogRecord> {
        let mut attributes = std::collections::HashMap::new();
        for (key, value) in log_data.attributes {
            attributes.insert(key, self.convert_attribute_value(value));
        }

        let trace_id = log_data
            .trace_id
            .map(|id| hex::decode(id))
            .transpose()
            .map_err(|e| DataError::Format { reason: format!("Invalid trace_id: {}", e) })?
            .unwrap_or_default();

        let span_id = log_data
            .span_id
            .map(|id| hex::decode(id))
            .transpose()
            .map_err(|e| DataError::Format { reason: format!("Invalid span_id: {}", e) })?
            .unwrap_or_default();

        let body = Some(AttributeValue {
            value: Some(attribute_value::Value::StringValue(log_data.message)),
        });

        Ok(LogRecord {
            time_unix_nano: log_data.timestamp,
            observed_time_unix_nano: None,
            severity_number: log_data.severity as i32,
            severity_text: log_data.severity_text,
            body,
            attributes,
            dropped_attributes_count: 0,
            flags: 0,
            trace_id,
            span_id,
        })
    }

    /// 转换属性值
    fn convert_attribute_value(&self, value: crate::data::AttributeValue) -> AttributeValue {
        match value {
            crate::data::AttributeValue::String(s) => AttributeValue {
                value: Some(attribute_value::Value::StringValue(s)),
            },
            crate::data::AttributeValue::Bool(b) => AttributeValue {
                value: Some(attribute_value::Value::BoolValue(b)),
            },
            crate::data::AttributeValue::Int(i) => AttributeValue {
                value: Some(attribute_value::Value::IntValue(i)),
            },
            crate::data::AttributeValue::Double(d) => AttributeValue {
                value: Some(attribute_value::Value::DoubleValue(d)),
            },
            _ => AttributeValue {
                value: Some(attribute_value::Value::StringValue(value.to_string())),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::TelemetryData;

    #[test]
    fn test_protobuf_serialization() {
        let serializer = ProtobufSerializer;
        let trace_data = TelemetryData::trace("test-operation");
        let result = serializer.serialize_traces(vec![trace_data]);
        assert!(result.is_ok());
    }
}
