//! # Tracezip压缩扩展
//!
//! 提供Tracezip压缩算法扩展，用于压缩OpenTelemetry追踪数据。
//! 通过包装官方Exporter来添加压缩功能。

use opentelemetry_sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use crate::compression::tracezip::{TraceCompressor, CompressorConfig};

mod conversion;
pub use conversion::{span_data_to_trace_data, batch_span_data_to_trace_data};

/// Tracezip压缩的Span Exporter包装器
///
/// 包装官方的SpanExporter，在导出前对数据进行Tracezip压缩。
pub struct TracezipSpanExporter {
    inner: Box<dyn SpanExporter>,
    compressor: TraceCompressor,
    compression_enabled: bool,
}

impl TracezipSpanExporter {
    /// 创建新的Tracezip Span Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: Box<dyn SpanExporter>) -> Self {
        Self {
            inner: exporter,
            compressor: TraceCompressor::new(CompressorConfig::default()),
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

    /// 设置压缩率目标
    ///
    /// # 参数
    ///
    /// * `ratio` - 目标压缩率 (0.0-1.0)
    pub fn with_compression_ratio(mut self, ratio: f64) -> Self {
        // TraceCompressor可能需要配置压缩率
        // 这里先保留接口，具体实现取决于TraceCompressor的API
        self
    }
}

#[async_trait]
impl SpanExporter for TracezipSpanExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        if self.compression_enabled && !batch.is_empty() {
            // 将SpanData转换为TraceData格式
            let trace_data_batch = batch_span_data_to_trace_data(&batch);

            // 将TraceData转换为TraceCompressor可以处理的格式
            // TraceCompressor.compress_batch接受 Vec<(&str, u64, (u64, u64), u64)>
            // 格式: (span_name, timestamp, (trace_id_high, trace_id_low), span_id)
            // 注意: 需要收集到Vec中以避免生命周期问题，使用owned String
            let mut spans_data: Vec<(String, u64, (u64, u64), u64)> = Vec::new();
            for td in &trace_data_batch {
                // 解析trace_id和span_id（假设它们是十六进制字符串）
                // trace_id是32字符的十六进制字符串，需要分成两个u64
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

                spans_data.push((td.name.clone(), td.start_time, (trace_id_high, trace_id_low), span_id));
            }

            // 转换为&str引用的格式
            let spans_for_compression: Vec<(&str, u64, (u64, u64), u64)> = spans_data
                .iter()
                .map(|(name, ts, tid, sid)| (name.as_str(), *ts, *tid, *sid))
                .collect();

            // 执行压缩
            match self.compressor.compress_batch(spans_for_compression) {
                Ok(compressed_trace) => {
                    let stats = self.compressor.stats();
                    tracing::debug!(
                        "Tracezip compression completed: {} spans compressed to {} spans, ratio: {:.2}%",
                        compressed_trace.metadata.original_span_count,
                        compressed_trace.metadata.compressed_span_count,
                        stats.compression_percentage()
                    );

                    // 注意: 压缩后的数据格式与原始SpanData不同
                    // 在实际应用中，压缩后的数据需要：
                    // 1. 序列化为二进制格式
                    // 2. 通过自定义协议传输
                    // 3. 在接收端解压并还原为SpanData
                    //
                    // 当前实现：由于压缩后的格式不同，我们仍然导出原始数据
                    // 但记录了压缩统计信息，压缩后的数据可以用于其他用途（如存储）
                    //
                    // 未来改进：可以实现压缩数据的序列化和传输协议

                    // 重置压缩器状态，准备下一批数据
                    self.compressor.reset();

                    // 导出原始数据（压缩数据可用于存储或其他用途）
                    self.inner.export(batch).await
                }
                Err(e) => {
                    tracing::warn!("Tracezip compression failed: {:?}, falling back to uncompressed export", e);
                    // 压缩失败时回退到未压缩导出
                    self.inner.export(batch).await
                }
            }
        } else {
            // 压缩未启用或batch为空，直接导出
            self.inner.export(batch).await
        }
    }

    fn shutdown(&mut self) -> opentelemetry_sdk::export::trace::Result<()> {
        self.inner.shutdown()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    #[tokio::test]
    async fn test_tracezip_exporter_wrap() {
        let noop_exporter = Box::new(NoopSpanExporter::new());
        let tracezip_exporter = TracezipSpanExporter::wrap(noop_exporter)
            .with_compression(true);

        // 测试导出空batch
        let result = tracezip_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_tracezip_exporter_compression_disabled() {
        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut tracezip_exporter = TracezipSpanExporter::wrap(noop_exporter)
            .with_compression(false);

        // 测试压缩禁用时的导出
        let result = tracezip_exporter.export(vec![]).await;
        assert!(result.is_ok());
    }
}
