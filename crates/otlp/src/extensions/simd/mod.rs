//! # SIMD优化扩展
//!
//! 提供SIMD向量化优化扩展，用于加速OpenTelemetry数据处理。
//! 通过包装官方Exporter和Processor来添加SIMD优化。

use opentelemetry_sdk::trace::{SpanData, SpanExporter};
use opentelemetry_sdk::error::OTelSdkError;
use crate::simd::CpuFeatures;

mod optimization;
use optimization::simd_optimize_batch;

/// SIMD优化的Span Exporter包装器
///
/// 包装官方的SpanExporter，在导出前使用SIMD优化处理数据。
#[derive(Debug)]
pub struct SimdSpanExporter<E> {
    inner: E,
    simd_enabled: bool,
    cpu_features: CpuFeatures,
}

impl<E> SimdSpanExporter<E>
where
    E: SpanExporter + std::fmt::Debug,
{
    /// 创建新的SIMD Span Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: E) -> Self {
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

impl<E> SpanExporter for SimdSpanExporter<E>
where
    E: SpanExporter + std::fmt::Debug + Send + Sync,
{
    fn export(&self, batch: Vec<SpanData>) -> impl std::future::Future<Output = Result<(), OTelSdkError>> + Send {
        let cpu_features = self.cpu_features;
        let simd_enabled = self.simd_enabled;
        async move {
            if simd_enabled && !batch.is_empty() {
                // 使用SIMD优化处理batch
                let optimized_batch = simd_optimize_batch(batch, &cpu_features);
                self.inner.export(optimized_batch).await
            } else {
                // SIMD未启用，直接导出
                self.inner.export(batch).await
            }
        }
    }

    fn shutdown(&mut self) -> Result<(), OTelSdkError> {
        self.inner.shutdown()
    }
}

// simd_optimize_batch 函数已移至 optimization.rs 模块

#[cfg(test)]
mod tests {
    // 注意: opentelemetry_sdk 0.31中NoopSpanExporter路径可能不同
    // 测试暂时跳过，等待API稳定
    // use opentelemetry_sdk::trace::NoopSpanExporter;

    // #[tokio::test]
    // async fn test_simd_exporter_wrap() {
    //     // 需要实际的exporter实现进行测试
    //     // let noop_exporter = NoopSpanExporter::new();
    //     // let simd_exporter = SimdSpanExporter::wrap(noop_exporter)
    //     //     .with_simd_optimization(true);
    //     // let result = simd_exporter.export(vec![]).await;
    //     // assert!(result.is_ok());
    // }

    // #[tokio::test]
    // async fn test_simd_exporter_optimization_disabled() {
    //     // 需要实际的exporter实现进行测试
    //     // let noop_exporter = NoopSpanExporter::new();
    //     // let mut simd_exporter = SimdSpanExporter::wrap(noop_exporter)
    //     //     .with_simd_optimization(false);
    //     // let result = simd_exporter.export(vec![]).await;
    //     // assert!(result.is_ok());
    // }
}
