//! # 扩展模块集成测试
//!
//! 测试扩展模块与官方opentelemetry-rust库的集成。
//!
//! 注意: 由于 opentelemetry_sdk 0.31 的 API 变化，测试暂时注释。
//! 主要变化包括：
//! - `opentelemetry_sdk::export::trace` → `opentelemetry_sdk::trace`
//! - `NoopSpanExporter` 路径可能不同或不存在
//! - `SpanExporter` 不再是 dyn 兼容的
//!
//! 测试需要根据新的 API 重新实现。

#[cfg(test)]
mod tests {
    // 注意: opentelemetry_sdk 0.31中API已经改变，测试需要重新实现
    // 以下测试暂时注释，等待API稳定或需要根据新的API重新实现

    // use opentelemetry_sdk::trace::NoopSpanExporter;
    // use opentelemetry_sdk::runtime::Tokio;  // 注意: Runtime可能需要具体类型

    // #[tokio::test]
    // async fn test_simd_exporter_integration() {
    //     use crate::extensions::simd::SimdSpanExporter;
    //     // 需要实际的exporter实现进行测试
    // }

    // #[tokio::test]
    // async fn test_tracezip_exporter_integration() {
    //     use crate::extensions::tracezip::TracezipSpanExporter;
    //     // 需要实际的exporter实现进行测试
    // }

    // #[tokio::test]
    // async fn test_multi_tenant_exporter_integration() {
    //     use crate::extensions::enterprise::MultiTenantExporter;
    //     // 需要实际的exporter实现进行测试
    // }

    // #[tokio::test]
    // async fn test_extension_chain() {
    //     use crate::extensions::*;
    //     // 需要实际的exporter实现进行测试
    // }

    // #[tokio::test]
    // async fn test_enhanced_exporter_builder() {
    //     use crate::wrappers::EnhancedExporter;
    //     // 需要实际的exporter实现进行测试
    // }
}
