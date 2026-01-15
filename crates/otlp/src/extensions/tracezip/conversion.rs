//! # SpanData到TraceData转换
//!
//! 提供SpanData到TraceData格式的转换功能，用于Tracezip压缩。

use opentelemetry_sdk::export::trace::SpanData;
use crate::data::{TraceData, SpanKind, SpanStatus, AttributeValue};

/// 将SpanData转换为TraceData格式
///
/// # 参数
///
/// * `span_data` - OpenTelemetry SDK的SpanData
///
/// # 返回
///
/// 转换后的TraceData
pub fn span_data_to_trace_data(span_data: &SpanData) -> TraceData {
    // 提取trace_id和span_id
    let trace_id = format!("{:032x}", span_data.span_context.trace_id());
    let span_id = format!("{:016x}", span_data.span_context.span_id());

    // 提取parent_span_id
    let parent_span_id = span_data.parent_span_id
        .map(|id| format!("{:016x}", id));

    // 提取name
    let name = span_data.name.clone().into_owned();

    // 转换span_kind
    let span_kind = match span_data.span_kind {
        opentelemetry::trace::SpanKind::Internal => SpanKind::Internal,
        opentelemetry::trace::SpanKind::Server => SpanKind::Server,
        opentelemetry::trace::SpanKind::Client => SpanKind::Client,
        opentelemetry::trace::SpanKind::Producer => SpanKind::Producer,
        opentelemetry::trace::SpanKind::Consumer => SpanKind::Consumer,
    };

    // 提取时间戳
    // 注意: SpanData的时间字段类型可能需要调整
    // 这里使用duration_since_epoch的方式获取纳秒时间戳
    let start_time = span_data.start_time
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    let end_time = span_data.end_time
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);

    // 转换status
    // 注意: opentelemetry的StatusCode在不同版本可能不同
    // 这里使用字符串匹配的方式，更兼容
    let status = match format!("{:?}", span_data.status.code).as_str() {
        s if s.contains("Unset") => SpanStatus::Unset,
        s if s.contains("Ok") => SpanStatus::Ok,
        s if s.contains("Error") => SpanStatus::Error,
        _ => SpanStatus::Unset,
    };

    // 转换attributes
    let mut attributes = std::collections::HashMap::new();
    for (key, value) in span_data.attributes.iter() {
        let attr_value = match value {
            opentelemetry::Value::String(s) => AttributeValue::String(s.clone().into_owned()),
            opentelemetry::Value::Bool(b) => AttributeValue::Bool(*b),
            opentelemetry::Value::Int(i) => AttributeValue::Int(*i),
            opentelemetry::Value::Double(d) => AttributeValue::Double(*d),
            opentelemetry::Value::Array(_) => {
                // 数组类型可能需要特殊处理
                AttributeValue::String(format!("{:?}", value))
            },
        };
        attributes.insert(key.clone().into_owned(), attr_value);
    }

    // 转换events（简化处理）
    let events = span_data.events.iter().map(|event| {
        let timestamp = event.timestamp
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        crate::data::SpanEvent {
            name: event.name.clone().into_owned(),
            timestamp,
            attributes: std::collections::HashMap::new(), // 简化处理
        }
    }).collect();

    // 转换links（简化处理）
    let links = span_data.links.iter().map(|_link| {
        crate::data::SpanLink {
            trace_id: String::new(),
            span_id: String::new(),
            attributes: std::collections::HashMap::new(),
        }
    }).collect();

    TraceData {
        trace_id,
        span_id,
        parent_span_id,
        name,
        span_kind,
        start_time,
        end_time,
        status,
        attributes,
        events,
        links,
    }
}

/// 批量转换SpanData到TraceData格式
pub fn batch_span_data_to_trace_data(batch: &[SpanData]) -> Vec<TraceData> {
    batch.iter()
        .map(span_data_to_trace_data)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry::trace::{SpanContext, TraceFlags, TraceState};
    use opentelemetry::trace::SpanKind as OtelSpanKind;
    use opentelemetry_sdk::trace::SpanData;
    use opentelemetry::KeyValue;

    fn create_test_span_data() -> SpanData {
        let trace_id = opentelemetry::trace::TraceId::from_bytes([1u8; 16]);
        let span_id = opentelemetry::trace::SpanId::from_bytes([2u8; 8]);
        let span_context = SpanContext::new(trace_id, span_id, TraceFlags::default(), false, TraceState::default());

        // 创建InstrumentationScope
        // 注意: opentelemetry_sdk的API在不同版本可能不同
        use opentelemetry::InstrumentationScope;
        let instrumentation_scope = InstrumentationScope::new("test", None, None);

        SpanData {
            span_context,
            parent_span_id: None,
            span_kind: OtelSpanKind::Internal,
            name: "test-span".into(),
            start_time: std::time::SystemTime::now(),
            end_time: std::time::SystemTime::now(),
            attributes: vec![
                KeyValue::new("key1", "value1"),
                KeyValue::new("key2", 42i64),
            ].into_iter().collect(),
            events: vec![],
            links: vec![],
            status: opentelemetry::trace::Status::ok(),
            resource: opentelemetry_sdk::Resource::empty(),
            instrumentation_lib: instrumentation_scope,
        }
    }

    #[test]
    fn test_span_data_to_trace_data() {
        let span_data = create_test_span_data();
        let trace_data = span_data_to_trace_data(&span_data);

        assert_eq!(trace_data.name, "test-span");
        assert_eq!(trace_data.span_kind, SpanKind::Internal);
        assert_eq!(trace_data.attributes.len(), 2);
    }

    #[test]
    fn test_batch_conversion() {
        let span_data1 = create_test_span_data();
        let span_data2 = create_test_span_data();
        let batch = vec![span_data1, span_data2];

        let trace_data_batch = batch_span_data_to_trace_data(&batch);
        assert_eq!(trace_data_batch.len(), 2);
    }
}
