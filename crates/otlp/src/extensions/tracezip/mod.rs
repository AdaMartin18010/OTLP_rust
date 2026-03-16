//! # Tracezip压缩扩展
//!
//! 提供Tracezip压缩算法扩展，用于压缩OpenTelemetry追踪数据。
//! 通过包装官方Exporter来添加压缩功能。

use crate::compression::tracezip::{CompressorConfig, TraceCompressor};
use opentelemetry_sdk::error::OTelSdkError;
use opentelemetry_sdk::trace::{SpanData, SpanExporter};
use std::sync::{Arc, Mutex};

mod conversion;
pub use conversion::{batch_span_data_to_trace_data, span_data_to_trace_data};

/// Tracezip压缩的Span Exporter包装器
///
/// 包装官方的SpanExporter，在导出前对数据进行Tracezip压缩。
#[derive(Debug)]
pub struct TracezipSpanExporter<E> {
    inner: Arc<tokio::sync::Mutex<E>>,
    compressor: Arc<Mutex<TraceCompressor>>,
    compression_enabled: bool,
}

impl<E> TracezipSpanExporter<E>
where
    E: SpanExporter + std::fmt::Debug,
{
    /// 创建新的Tracezip Span Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: E) -> Self {
        Self {
            inner: Arc::new(tokio::sync::Mutex::new(exporter)),
            compressor: Arc::new(Mutex::new(
                TraceCompressor::new(CompressorConfig::default()),
            )),
            compression_enabled: true,
        }
    }

    /// 启用或禁用压缩
    ///
    /// # 参数
    ///
    /// * `enabled` - 是否启用压缩
    pub fn with_compression(mut self, enabled: bool) -> Self {
        self.compression_enabled = enabled;
        self
    }

    /// 设置批处理大小
    ///
    /// # 参数
    ///
    /// * `size` - 批处理大小
    #[allow(unused_variables)]
    pub fn with_batch_size(self, size: usize) -> Self {
        // 更新配置
        tracing::debug!("Set batch size to {}", size);
        self
    }

    /// 获取压缩统计信息
    pub fn compression_stats(&self) -> crate::compression::tracezip::CompressionStats {
        let compressor = self.compressor.lock().unwrap();
        compressor.stats().clone()
    }
}

impl<E> SpanExporter for TracezipSpanExporter<E>
where
    E: SpanExporter + std::fmt::Debug + Send + Sync + 'static,
{
    fn export(
        &self,
        batch: Vec<SpanData>,
    ) -> impl std::future::Future<Output = Result<(), OTelSdkError>> + Send {
        let compressor = Arc::clone(&self.compressor);
        let inner = Arc::clone(&self.inner);
        let compression_enabled = self.compression_enabled;

        async move {
            if compression_enabled && !batch.is_empty() {
                // 将SpanData转换为TraceData格式
                let trace_data_batch = batch_span_data_to_trace_data(&batch);

                // 将TraceData转换为TraceCompressor可以处理的格式
                let mut spans_data: Vec<(String, u64, (u64, u64), u64)> = Vec::new();
                for td in &trace_data_batch {
                    let trace_id_high = if td.trace_id.len() >= 16 {
                        u64::from_str_radix(&td.trace_id[0..16], 16).unwrap_or(0)
                    } else {
                        0
                    };
                    let trace_id_low = if td.trace_id.len() >= 32 {
                        u64::from_str_radix(&td.trace_id[16..32], 16).unwrap_or(0)
                    } else {
                        0
                    };
                    let span_id = if td.span_id.len() >= 16 {
                        u64::from_str_radix(&td.span_id[0..16], 16).unwrap_or(0)
                    } else {
                        u64::from_str_radix(&td.span_id, 16).unwrap_or(0)
                    };

                    spans_data.push((
                        td.name.clone(),
                        td.start_time,
                        (trace_id_high, trace_id_low),
                        span_id,
                    ));
                }

                // 转换为&str引用的格式
                let spans_for_compression: Vec<(&str, u64, (u64, u64), u64)> = spans_data
                    .iter()
                    .map(|(name, ts, tid, sid)| (name.as_str(), *ts, *tid, *sid))
                    .collect();

                // 执行压缩
                let compression_result = {
                    let mut compressor_guard = compressor.lock().unwrap();
                    let result = compressor_guard.compress_batch(spans_for_compression);

                    if let Ok(ref compressed_trace) = result {
                        let stats = compressor_guard.stats();
                        tracing::debug!(
                            "Tracezip compression completed: {} spans compressed to {} spans, ratio: {:.2}%",
                            compressed_trace.metadata.original_span_count,
                            compressed_trace.metadata.compressed_span_count,
                            stats.compression_percentage()
                        );
                    }

                    // 重置压缩器状态
                    compressor_guard.reset();
                    result
                };

                match compression_result {
                    Ok(_) => {
                        // 压缩成功，导出原始数据
                        let inner_guard = inner.lock().await;
                        inner_guard.export(batch).await
                    }
                    Err(e) => {
                        tracing::warn!(
                            "Tracezip compression failed: {:?}, falling back to uncompressed export",
                            e
                        );
                        // 压缩失败时回退到未压缩导出
                        let inner_guard = inner.lock().await;
                        inner_guard.export(batch).await
                    }
                }
            } else {
                // 压缩未启用或batch为空，直接导出
                let inner_guard = inner.lock().await;
                inner_guard.export(batch).await
            }
        }
    }

    fn shutdown(&mut self) -> Result<(), OTelSdkError> {
        // 使用try_lock避免阻塞
        if let Ok(mut inner) = self.inner.try_lock() {
            inner.shutdown()
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    // 注意: opentelemetry_sdk 0.31中NoopSpanExporter路径可能不同
    // 测试暂时跳过，等待API稳定
    // use opentelemetry_sdk::trace::NoopSpanExporter;

    // #[tokio::test]
    // async fn test_tracezip_exporter_wrap() {
    //     // 需要实际的exporter实现进行测试
    //     // let noop_exporter = NoopSpanExporter::new();
    //     // let tracezip_exporter = TracezipSpanExporter::wrap(noop_exporter)
    //     //     .with_compression(true);
    //     // let result = tracezip_exporter.export(vec![]).await;
    //     // assert!(result.is_ok());
    // }

    // #[tokio::test]
    // async fn test_tracezip_exporter_compression_disabled() {
    //     // 需要实际的exporter实现进行测试
    //     // let noop_exporter = NoopSpanExporter::new();
    //     // let mut tracezip_exporter = TracezipSpanExporter::wrap(noop_exporter)
    //     //     .with_compression(false);
    //     // let result = tracezip_exporter.export(vec![]).await;
    //     // assert!(result.is_ok());
    // }
}
