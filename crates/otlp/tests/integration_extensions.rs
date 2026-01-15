//! # 扩展模块集成测试
//!
//! 测试扩展模块与官方opentelemetry-rust库的集成。

#[cfg(test)]
mod tests {
    use opentelemetry_sdk::export::trace::NoopSpanExporter;
    use opentelemetry_sdk::runtime::Tokio;

    #[tokio::test]
    async fn test_simd_exporter_integration() {
        use crate::extensions::simd::SimdSpanExporter;

        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut simd_exporter = SimdSpanExporter::wrap(noop_exporter)
            .with_simd_optimization(true);

        // 测试导出
        let result = simd_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_tracezip_exporter_integration() {
        use crate::extensions::tracezip::TracezipSpanExporter;

        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut tracezip_exporter = TracezipSpanExporter::wrap(noop_exporter)
            .with_compression(true);

        // 测试导出
        let result = tracezip_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_multi_tenant_exporter_integration() {
        use crate::extensions::enterprise::MultiTenantExporter;

        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut multi_tenant_exporter = MultiTenantExporter::wrap(noop_exporter)
            .with_tenant_id("test-tenant".to_string());

        // 测试导出
        let result = multi_tenant_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_extension_chain() {
        use crate::extensions::*;

        // 测试扩展链式组合
        let noop_exporter = Box::new(NoopSpanExporter::new());

        // 按顺序应用扩展
        let exporter = TracezipSpanExporter::wrap(noop_exporter)
            .with_compression(true);
        let exporter = SimdSpanExporter::wrap(Box::new(exporter))
            .with_simd_optimization(true);
        let mut exporter = MultiTenantExporter::wrap(exporter)
            .with_tenant_id("test-tenant".to_string());

        // 测试导出
        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_enhanced_exporter_builder() {
        use crate::wrappers::EnhancedExporter;

        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut enhanced_exporter = EnhancedExporter::new()
            .with_exporter(noop_exporter)
            .with_simd_optimization(true)
            .with_tracezip_compression(true)
            .with_multi_tenant(true)
            .with_tenant_id("test-tenant".to_string())
            .build()
            .expect("Failed to build enhanced exporter");

        // 测试导出
        let result = enhanced_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }
}
