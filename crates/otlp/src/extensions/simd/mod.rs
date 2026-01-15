//! # SIMD优化扩展
//!
//! 提供SIMD向量化优化扩展，用于加速OpenTelemetry数据处理。
//! 通过包装官方Exporter和Processor来添加SIMD优化。

use opentelemetry_sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use crate::simd::CpuFeatures;

mod optimization;
use optimization::simd_optimize_batch;

/// SIMD优化的Span Exporter包装器
///
/// 包装官方的SpanExporter，在导出前使用SIMD优化处理数据。
pub struct SimdSpanExporter {
    inner: Box<dyn SpanExporter>,
    simd_enabled: bool,
    cpu_features: CpuFeatures,
}

impl SimdSpanExporter {
    /// 创建新的SIMD Span Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: Box<dyn SpanExporter>) -> Self {
        Self {
            inner: exporter,
            simd_enabled: true,
            cpu_features: CpuFeatures::detect(),
        }
    }

    /// 启用或禁用SIMD优化
    ///
    /// # 参数
    ///
    /// * `enabled` - 是否启用SIMD优化
    pub fn with_simd_optimization(mut self, enabled: bool) -> Self {
        self.simd_enabled = enabled;
        self
    }
}

#[async_trait]
impl SpanExporter for SimdSpanExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        if self.simd_enabled && !batch.is_empty() {
            // 使用SIMD优化处理batch
            let optimized_batch = simd_optimize_batch(batch, &self.cpu_features);
            self.inner.export(optimized_batch).await
        } else {
            // SIMD未启用，直接导出
            self.inner.export(batch).await
        }
    }

    fn shutdown(&mut self) -> opentelemetry_sdk::export::trace::Result<()> {
        self.inner.shutdown()
    }
}

// simd_optimize_batch 函数已移至 optimization.rs 模块

#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    #[tokio::test]
    async fn test_simd_exporter_wrap() {
        let noop_exporter = Box::new(NoopSpanExporter::new());
        let simd_exporter = SimdSpanExporter::wrap(noop_exporter)
            .with_simd_optimization(true);

        // 测试导出空batch
        let result = simd_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_simd_exporter_optimization_disabled() {
        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut simd_exporter = SimdSpanExporter::wrap(noop_exporter)
            .with_simd_optimization(false);

        // 测试SIMD禁用时的导出
        let result = simd_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }
}
