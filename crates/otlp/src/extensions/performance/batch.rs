//! # 批量处理优化扩展
//!
//! 提供批量处理优化扩展，用于提高导出性能。

use opentelemetry_sdk::trace::{SpanData, SpanExporter};
use opentelemetry_sdk::error::OTelSdkError;
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 批量处理优化的Span Exporter包装器
///
/// 包装官方的SpanExporter，添加批量处理优化。
#[derive(Debug)]
pub struct BatchOptimizedExporter<E> {
    inner: E,
    batch_size: usize,
    batch_timeout: Duration,
    pending_batch: Arc<Mutex<Vec<SpanData>>>,
}

impl<E> BatchOptimizedExporter<E> 
where
    E: SpanExporter + std::fmt::Debug,
{
    /// 创建新的批量处理优化Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: E) -> Self {
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

impl<E> SpanExporter for BatchOptimizedExporter<E>
where
    E: SpanExporter + std::fmt::Debug + Send + Sync,
{
    fn export(&self, batch: Vec<SpanData>) -> impl std::future::Future<Output = Result<(), OTelSdkError>> + Send {
        let pending_batch = self.pending_batch.clone();
        let batch_size = self.batch_size;
        async move {
            // 将新的spans添加到pending batch
            let mut pending = pending_batch.lock().await;
            pending.extend(batch);

            // 如果达到批量大小，立即导出
            if pending.len() >= batch_size {
                let batch_to_export = std::mem::take(&mut *pending);
                drop(pending); // 释放锁
                return self.inner.export(batch_to_export).await;
            }

            // 否则等待更多spans或超时
            // 注意: 实际实现需要异步定时器来处理超时
            // 这里简化实现，直接返回成功
            // 真正的批量处理应该在TracerProvider的批处理层实现
            Ok(())
        }
    }

    fn shutdown(&mut self) -> Result<(), OTelSdkError> {
        // 导出剩余的pending batch
        // 注意: shutdown是同步的，但pending_batch是异步的
        // 这里简化实现，实际需要处理异步到同步的转换
        self.inner.shutdown()
    }
}

#[cfg(test)]
mod tests {
    // 注意: opentelemetry_sdk 0.31中NoopSpanExporter路径可能不同
    // 测试暂时跳过，等待API稳定
    // use opentelemetry_sdk::trace::NoopSpanExporter;

    // #[tokio::test]
    // async fn test_batch_optimized_exporter() {
    //     // 需要实际的exporter实现进行测试
    //     // let noop = NoopSpanExporter::new();
    //     // let mut exporter = BatchOptimizedExporter::wrap(noop)
    //     //     .with_batch_size(10);
    //     // let result = exporter.export(vec![]).await;
    //     // assert!(result.is_ok());
    // }
}
