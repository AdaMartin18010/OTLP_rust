//! Collector 核心实现

use crate::{
    buffer::LockFreeBuffer,
    config::Config,
    exporter::{Exporter, ZeroCopyExporter},
    processor::BatchProcessor,
    span::Span,
    CollectorError, Result,
};
use std::sync::Arc;
use tracing::{info, warn};

/// 高性能 OTLP Collector
pub struct Collector {
    config: Config,
    buffer: LockFreeBuffer,
    processor: Arc<BatchProcessor>,
}

impl Collector {
    /// 创建新 Collector
    pub async fn new(config: Config) -> Result<Self> {
        config.validate()?;
        
        info!("初始化 Collector: {:?}", config);
        
        // 创建缓冲区
        let buffer = LockFreeBuffer::new(config.buffer_capacity);
        
        // 创建导出器
        let exporter: Arc<dyn Exporter> = Arc::new(ZeroCopyExporter::new(config.endpoint.clone()));
        
        // 创建处理器
        let processor = Arc::new(BatchProcessor::new(
            config.clone(),
            buffer.clone(),
            exporter,
        ));
        
        // 启动处理循环
        processor.start().await;
        
        Ok(Self {
            config,
            buffer,
            processor,
        })
    }
    
    /// 收集 Span (无锁并发)
    pub fn collect(&self, span: Span) -> Result<()> {
        self.buffer
            .push(span)
            .map_err(|_| CollectorError::BufferFull)
    }
    
    /// 批量收集
    pub fn collect_batch(&self, spans: Vec<Span>) -> Result<usize> {
        let mut success_count = 0;
        
        for span in spans {
            if self.buffer.push(span).is_ok() {
                success_count += 1;
            } else {
                warn!("缓冲区已满，丢弃 span");
            }
        }
        
        Ok(success_count)
    }
    
    /// 强制刷新
    pub async fn flush(&self) -> Result<()> {
        self.processor.flush().await
    }
    
    /// 获取统计信息
    pub fn stats(&self) -> CollectorStats {
        CollectorStats {
            buffer_len: self.buffer.len(),
            buffer_capacity: self.buffer.capacity(),
            buffer_usage_percent: (self.buffer.len() as f64 / self.buffer.capacity() as f64) * 100.0,
        }
    }
    
    /// 优雅关闭
    pub async fn shutdown(self) -> Result<()> {
        info!("关闭 Collector");
        
        // 停止处理器
        self.processor.stop().await;
        
        // 刷新剩余数据
        self.processor.flush().await?;
        
        info!("Collector 已关闭");
        Ok(())
    }
}

/// Collector 统计信息
#[derive(Debug, Clone)]
pub struct CollectorStats {
    pub buffer_len: usize,
    pub buffer_capacity: usize,
    pub buffer_usage_percent: f64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::Duration;
    
    #[tokio::test]
    async fn test_collector_basic() {
        let config = Config {
            batch_size: 10,
            batch_timeout_ms: 1000,
            buffer_capacity: 100,
            endpoint: "http://localhost:4317".to_string(),
            max_retries: 3,
            retry_delay_ms: 100,
        };
        
        let collector = Collector::new(config).await.unwrap();
        
        // 收集一些 spans
        for i in 0..5 {
            let span = Span::new(format!("span-{}", i));
            collector.collect(span).unwrap();
        }
        
        let stats = collector.stats();
        assert_eq!(stats.buffer_len, 5);
        
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        collector.shutdown().await.unwrap();
    }
    
    #[tokio::test]
    async fn test_collector_batch() {
        let config = Config::default();
        let collector = Collector::new(config).await.unwrap();
        
        let spans: Vec<Span> = (0..100)
            .map(|i| Span::new(format!("span-{}", i)))
            .collect();
        
        let count = collector.collect_batch(spans).unwrap();
        assert_eq!(count, 100);
        
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        collector.shutdown().await.unwrap();
    }
    
    #[tokio::test]
    async fn test_collector_overflow() {
        let config = Config {
            buffer_capacity: 10,
            ..Default::default()
        };
        
        let collector = Collector::new(config).await.unwrap();
        
        // 填满缓冲区
        for i in 0..10 {
            let span = Span::new(format!("span-{}", i));
            collector.collect(span).unwrap();
        }
        
        // 尝试添加更多 (应该失败)
        let span = Span::new("overflow".to_string());
        assert!(collector.collect(span).is_err());
        
        collector.shutdown().await.unwrap();
    }
}

