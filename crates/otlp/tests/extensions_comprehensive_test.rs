//! # 扩展模块综合测试
//!
//! 测试扩展模块的综合使用场景。

#[cfg(test)]
mod tests {
    use opentelemetry_sdk::export::trace::NoopSpanExporter;
    use opentelemetry::trace::{SpanContext, TraceFlags, TraceState};
    use opentelemetry::trace::SpanKind as OtelSpanKind;
    use opentelemetry_sdk::export::trace::SpanData;
    use opentelemetry::KeyValue;
    use std::time::SystemTime;

    fn create_test_span_data() -> SpanData {
        let trace_id = opentelemetry::trace::TraceId::from_bytes([1u8; 16]);
        let span_id = opentelemetry::trace::SpanId::from_bytes([2u8; 8]);
        let span_context = SpanContext::new(trace_id, span_id, TraceFlags::default(), false, TraceState::default());

        SpanData {
            span_context,
            parent_span_id: None,
            span_kind: OtelSpanKind::Internal,
            name: "test-span".into(),
            start_time: SystemTime::now(),
            end_time: SystemTime::now(),
            attributes: vec![
                KeyValue::new("key1", "value1"),
                KeyValue::new("key2", 42i64),
            ].into_iter().collect(),
            events: vec![],
            links: vec![],
            status: opentelemetry::trace::Status::ok(),
            resource: opentelemetry_sdk::Resource::empty(),
            instrumentation_lib: opentelemetry_sdk::trace::InstrumentationScope::new("test", None, None),
        }
    }

    #[tokio::test]
    async fn test_all_extensions_chain() {
        use crate::extensions::*;

        let noop = Box::new(NoopSpanExporter::new());

        // 测试所有扩展的链式组合
        let exporter = ComplianceExporter::wrap(noop)
            .with_compliance(true);
        let exporter = MultiTenantExporter::wrap(Box::new(exporter))
            .with_tenant_id("test-tenant".to_string());
        let exporter = SimdSpanExporter::wrap(Box::new(exporter))
            .with_simd_optimization(true);
        let exporter = TracezipSpanExporter::wrap(Box::new(exporter))
            .with_compression(true);
        let mut exporter = BatchOptimizedExporter::wrap(Box::new(exporter))
            .with_batch_size(10);

        let span_data = create_test_span_data();
        let result = exporter.export(vec![span_data]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_tracezip_conversion() {
        use crate::extensions::tracezip::conversion::span_data_to_trace_data;

        let span_data = create_test_span_data();
        let trace_data = span_data_to_trace_data(&span_data);

        assert_eq!(trace_data.name, "test-span");
        assert_eq!(trace_data.span_kind, crate::data::SpanKind::Internal);
        assert!(!trace_data.trace_id.is_empty());
        assert!(!trace_data.span_id.is_empty());
    }

    #[tokio::test]
    async fn test_simd_optimization_with_data() {
        use crate::extensions::simd::SimdSpanExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = SimdSpanExporter::wrap(noop)
            .with_simd_optimization(true);

        let span_data = create_test_span_data();
        let result = exporter.export(vec![span_data]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_multi_tenant_with_data() {
        use crate::extensions::enterprise::MultiTenantExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = MultiTenantExporter::wrap(noop)
            .with_tenant_id("tenant-123".to_string());

        let span_data = create_test_span_data();
        let result = exporter.export(vec![span_data]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_batch_optimization() {
        use crate::extensions::performance::BatchOptimizedExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = BatchOptimizedExporter::wrap(noop)
            .with_batch_size(5);

        // 创建多个span数据
        let mut batch = Vec::new();
        for _ in 0..10 {
            batch.push(create_test_span_data());
        }

        let result = exporter.export(batch).await;
        assert!(result.is_ok());
    }
}
