//! # 扩展性能测试
//!
//! 测试扩展模块的性能表现，对比官方库和扩展版本的性能差异。

#[cfg(test)]
mod tests {
    use opentelemetry_sdk::trace::NoopSpanExporter;
    use opentelemetry::trace::{SpanContext, TraceFlags, TraceState};
    use opentelemetry::trace::SpanKind as OtelSpanKind;
    use opentelemetry_sdk::trace::SpanData;
    use opentelemetry::KeyValue;
    use opentelemetry_sdk::trace::InstrumentationScope;
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
            instrumentation_lib: InstrumentationScope::new("test", None, None),
        }
    }

    fn create_batch(size: usize) -> Vec<SpanData> {
        (0..size).map(|_| create_test_span_data()).collect()
    }

    #[tokio::test]
    async fn test_tracezip_compression_performance() {
        use crate::extensions::tracezip::TracezipSpanExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = TracezipSpanExporter::wrap(noop)
            .with_compression(true);

        let batch = create_batch(100);

        let start = std::time::Instant::now();
        let result = exporter.export(batch).await;
        let duration = start.elapsed();

        assert!(result.is_ok());
        // 压缩应该在合理时间内完成（<100ms for 100 spans）
        assert!(duration.as_millis() < 100);
    }

    #[tokio::test]
    async fn test_simd_optimization_performance() {
        use crate::extensions::simd::SimdSpanExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = SimdSpanExporter::wrap(noop)
            .with_simd_optimization(true);

        let batch = create_batch(1000);

        let start = std::time::Instant::now();
        let result = exporter.export(batch).await;
        let duration = start.elapsed();

        assert!(result.is_ok());
        // SIMD优化应该在合理时间内完成
        assert!(duration.as_millis() < 200);
    }

    #[tokio::test]
    async fn test_batch_optimization_performance() {
        use crate::extensions::performance::BatchOptimizedExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = BatchOptimizedExporter::wrap(noop)
            .with_batch_size(50);

        let batch = create_batch(200);

        let start = std::time::Instant::now();
        let result = exporter.export(batch).await;
        let duration = start.elapsed();

        assert!(result.is_ok());
        // 批量处理应该在合理时间内完成
        assert!(duration.as_millis() < 100);
    }

    #[tokio::test]
    async fn test_all_extensions_combined_performance() {
        use crate::extensions::*;

        let noop = Box::new(NoopSpanExporter::new());

        // 链式组合所有扩展
        let exporter = ComplianceExporter::wrap(noop)
            .with_compliance(true);
        let exporter = MultiTenantExporter::wrap(Box::new(exporter))
            .with_tenant_id("test-tenant".to_string());
        let exporter = SimdSpanExporter::wrap(Box::new(exporter))
            .with_simd_optimization(true);
        let exporter = TracezipSpanExporter::wrap(Box::new(exporter))
            .with_compression(true);
        let mut exporter = BatchOptimizedExporter::wrap(Box::new(exporter))
            .with_batch_size(50);

        let batch = create_batch(500);

        let start = std::time::Instant::now();
        let result = exporter.export(batch).await;
        let duration = start.elapsed();

        assert!(result.is_ok());
        // 所有扩展组合应该在合理时间内完成（<500ms for 500 spans）
        assert!(duration.as_millis() < 500);
    }
}
