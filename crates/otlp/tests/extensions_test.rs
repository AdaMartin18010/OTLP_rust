//! # 扩展模块单元测试
//!
//! 测试各个扩展模块的功能。

#[cfg(test)]
mod tests {
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    #[tokio::test]
    async fn test_simd_exporter() {
        use crate::extensions::simd::SimdSpanExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = SimdSpanExporter::wrap(noop)
            .with_simd_optimization(true);

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_tracezip_exporter() {
        use crate::extensions::tracezip::TracezipSpanExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = TracezipSpanExporter::wrap(noop)
            .with_compression(true);

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_multi_tenant_exporter() {
        use crate::extensions::enterprise::MultiTenantExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = MultiTenantExporter::wrap(noop)
            .with_tenant_id("test-tenant".to_string());

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_compliance_exporter() {
        use crate::extensions::enterprise::ComplianceExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = ComplianceExporter::wrap(noop)
            .with_compliance(true);

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_batch_optimized_exporter() {
        use crate::extensions::performance::BatchOptimizedExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = BatchOptimizedExporter::wrap(noop)
            .with_batch_size(100);

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_connection_pool_exporter() {
        use crate::extensions::performance::ConnectionPoolExporter;

        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = ConnectionPoolExporter::wrap(noop)
            .with_connection_pool(true);

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_extension_chain() {
        use crate::extensions::*;

        // 测试扩展链式组合
        let noop = Box::new(NoopSpanExporter::new());

        // 按顺序应用扩展（从内到外）
        let exporter = ComplianceExporter::wrap(noop)
            .with_compliance(true);
        let exporter = MultiTenantExporter::wrap(Box::new(exporter))
            .with_tenant_id("test-tenant".to_string());
        let exporter = SimdSpanExporter::wrap(Box::new(exporter))
            .with_simd_optimization(true);
        let exporter = TracezipSpanExporter::wrap(Box::new(exporter))
            .with_compression(true);
        let mut exporter = BatchOptimizedExporter::wrap(Box::new(exporter));

        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }
}
