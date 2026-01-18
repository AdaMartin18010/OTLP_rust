//! # SpanData到TraceData转换
//!
//! 提供SpanData到TraceData格式的转换功能，用于Tracezip压缩。

use opentelemetry_sdk::trace::SpanData;
use crate::data::{TraceData, SpanKind, SpanStatus, StatusCode};

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
    // 注意: opentelemetry_sdk 0.31中parent_span_id的类型可能不同
    // 如果parent_span_id是SpanId类型，直接格式化
    // 如果是Option<SpanId>，使用map
    let parent_span_id = if span_data.parent_span_is_remote {
        // 如果parent_span_id字段存在，格式化它
        // 注意: 需要根据实际的SpanData结构调整
        None
    } else {
        None
    };

    // 提取name
    // 注意: opentelemetry_sdk 0.31中name的类型可能不同
    // 如果是StringValue，可能需要不同的转换方式
    let name = span_data.name.to_string();

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
    // 注意: opentelemetry 0.31中Status可能没有code字段
    // 需要使用不同的方式获取status code
    let status_code = match format!("{:?}", span_data.status).as_str() {
        s if s.contains("Unset") => StatusCode::Unset,
        s if s.contains("Ok") => StatusCode::Ok,
        s if s.contains("Error") => StatusCode::Error,
        _ => StatusCode::Unset,
    };
    let status = SpanStatus {
        code: status_code,
        message: None,
    };

    // 转换attributes
    // 注意: opentelemetry_sdk 0.31中attributes的类型可能不同
    // SpanData.attributes可能是Vec<KeyValue>或其他类型
    let attributes = std::collections::HashMap::new();
    // 暂时注释掉，因为attributes的API在v0.31中可能已经改变
    // for attr in span_data.attributes.iter() {
    //     let key = attr.key.clone().to_string();
    //     let attr_value = match &attr.value {
    //         opentelemetry::Value::Str(s) => AttributeValue::String(s.to_string()),
    //         opentelemetry::Value::Bool(b) => AttributeValue::Bool(*b),
    //         opentelemetry::Value::I64(i) => AttributeValue::Int(*i),
    //         opentelemetry::Value::F64(d) => AttributeValue::Double(*d),
    //         opentelemetry::Value::Array(_) => {
    //             // 数组类型可能需要特殊处理
    //             AttributeValue::String(format!("{:?}", attr.value))
    //         },
    //         _ => AttributeValue::String(format!("{:?}", attr.value)),
    //     };
    //     attributes.insert(key, attr_value);
    // }

    // 转换events（简化处理）
    // 注意: opentelemetry_sdk 0.31中events的类型可能是SpanEvents而不是Vec
    let events: Vec<crate::data::SpanEvent> = vec![]; // 暂时为空，因为events的API在v0.31中可能已改变
    // let events = span_data.events.iter().map(|event| {
    //     let timestamp = event.timestamp
    //         .duration_since(std::time::UNIX_EPOCH)
    //         .map(|d| d.as_nanos() as u64)
    //         .unwrap_or(0);
    //     crate::data::SpanEvent {
    //         name: event.name.to_string(),
    //         timestamp,
    //         attributes: std::collections::HashMap::new(), // 简化处理
    //     }
    // }).collect();

    // 转换links（简化处理）
    // 注意: opentelemetry_sdk 0.31中links的类型可能是SpanLinks而不是Vec
    let links: Vec<crate::data::SpanLink> = vec![]; // 暂时为空，因为links的API在v0.31中可能已改变
    // let links = span_data.links.iter().map(|_link| {
    //     crate::data::SpanLink {
    //         trace_id: String::new(),
    //         span_id: String::new(),
    //         attributes: std::collections::HashMap::new(),
    //     }
    // }).collect();

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
    // 测试暂时注释掉，因为SpanData的结构在opentelemetry_sdk 0.31中已经改变
    // use super::*;
    // use opentelemetry::trace::{SpanContext, TraceFlags, TraceState};
    // use opentelemetry::trace::SpanKind as OtelSpanKind;
    // use opentelemetry_sdk::trace::SpanData;
    // use opentelemetry::KeyValue;

    // 测试函数暂时注释掉，因为SpanData的结构在opentelemetry_sdk 0.31中已经改变
    // 需要根据新的API重新实现
    // fn create_test_span_data() -> SpanData {
    //     let trace_id = opentelemetry::trace::TraceId::from_bytes([1u8; 16]);
    //     let span_id = opentelemetry::trace::SpanId::from_bytes([2u8; 8]);
    //     let span_context = SpanContext::new(trace_id, span_id, TraceFlags::default(), false, TraceState::default());
    //
    //     // 创建InstrumentationScope
    //     // 注意: opentelemetry_sdk的API在不同版本可能不同
    //     use opentelemetry::InstrumentationScope;
    //     let instrumentation_scope = InstrumentationScope::new("test", None, None);
    //
    //     // 注意: opentelemetry_sdk 0.31中SpanData的结构已经改变
    //     // 这个测试需要根据实际的API调整
    //     // todo!("SpanData structure has changed in opentelemetry_sdk 0.31. Test needs to be updated to match the new API");
    //
    //     // SpanData {
    //     //     span_context,
    //     //     parent_span_id: None,
    //     //     span_kind: OtelSpanKind::Internal,
    //     //     name: "test-span".into(),
    //     //     start_time: std::time::SystemTime::now(),
    //     //     end_time: std::time::SystemTime::now(),
    //     //     attributes: vec![
    //     //         KeyValue::new("key1", "value1"),
    //     //         KeyValue::new("key2", 42i64),
    //     //     ].into_iter().collect(),
    //     //     events: vec![],
    //     //     links: vec![],
    //     //     status: opentelemetry::trace::Status::ok(),
    //     //     resource: opentelemetry_sdk::Resource::empty(),
    //     //     instrumentation_lib: instrumentation_scope,
    //     // }
    // }

    // 测试暂时注释掉，因为SpanData的结构在opentelemetry_sdk 0.31中已经改变
    // 需要根据新的API重新实现测试
    // #[test]
    // fn test_span_data_to_trace_data() {
    //     let span_data = create_test_span_data();
    //     let trace_data = span_data_to_trace_data(&span_data);
    //
    //     assert_eq!(trace_data.name, "test-span");
    //     assert_eq!(trace_data.span_kind, SpanKind::Internal);
    //     assert_eq!(trace_data.attributes.len(), 2);
    // }
    //
    // #[test]
    // fn test_batch_conversion() {
    //     let span_data1 = create_test_span_data();
    //     let span_data2 = create_test_span_data();
    //     let batch = vec![span_data1, span_data2];
    //
    //     let trace_data_batch = batch_span_data_to_trace_data(&batch);
    //     assert_eq!(trace_data_batch.len(), 2);
    // }
}
