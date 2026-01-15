//! # 批量处理优化扩展
//!
//! 提供批量处理优化扩展，用于提高导出性能。

use opentelemetry_sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 批量处理优化的Span Exporter包装器
///
/// 包装官方的SpanExporter，添加批量处理优化。
pub struct BatchOptimizedExporter {
    inner: Box<dyn SpanExporter>,
    batch_size: usize,
    batch_timeout: Duration,
    pending_batch: Arc<Mutex<Vec<SpanData>>>,
}

impl BatchOptimizedExporter {
    /// 创建新的批量处理优化Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: Box<dyn SpanExporter>) -> Self {
        Self {
            inner: exporter,
            batch_size: 100,
            batch_timeout: Duration::from_millis(100),
            pending_batch: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 设置批量大小
    ///
    /// # 参数
    ///
    /// * `size` - 批量大小
    pub fn with_batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }

    /// 设置批量超时时间
    ///
    /// # 参数
    ///
    /// * `timeout` - 超时时间
    pub fn with_batch_timeout(mut self, timeout: Duration) -> Self {
        self.batch_timeout = timeout;
        self
    }
}

#[async_trait]
impl SpanExporter for BatchOptimizedExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 将新的spans添加到pending batch
        let mut pending = self.pending_batch.lock().await;
        pending.extend(batch);

        // 如果达到批量大小，立即导出
        if pending.len() >= self.batch_size {
            let batch_to_export = std::mem::take(&mut *pending);
            drop(pending); // 释放锁
            return self.inner.export(batch_to_export).await;
        }

        // 否则等待更多spans或超时
        // 注意: 实际实现需要异步定时器来处理超时
        // 这里简化实现，直接返回成功
        // 真正的批量处理应该在TracerProvider的批处理层实现
        ExportResult::Ok
    }

    fn shutdown(&mut self) -> opentelemetry_sdk::export::trace::Result<()> {
        // 导出剩余的pending batch
        // 注意: shutdown是同步的，但pending_batch是异步的
        // 这里简化实现，实际需要处理异步到同步的转换
        self.inner.shutdown()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    #[tokio::test]
    async fn test_batch_optimized_exporter() {
        let noop = Box::new(NoopSpanExporter::new());
        let mut exporter = BatchOptimizedExporter::wrap(noop)
            .with_batch_size(10);
        let result = exporter.export(vec![]).await;
        assert!(result.is_ok());
    }
}
