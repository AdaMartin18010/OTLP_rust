//! 批处理器

use crate::{buffer::LockFreeBuffer, config::Config, exporter::Exporter, span::Span, Result};
use std::sync::Arc;
use tokio::time::{interval, Duration};
use tracing::{debug, info, warn};

/// 批处理器
pub struct BatchProcessor {
    config: Config,
    buffer: LockFreeBuffer,
    exporter: Arc<dyn Exporter>,
    running: Arc<tokio::sync::RwLock<bool>>,
}

impl BatchProcessor {
    /// 创建新批处理器
    pub fn new(
        config: Config,
        buffer: LockFreeBuffer,
        exporter: Arc<dyn Exporter>,
    ) -> Self {
        Self {
            config,
            buffer,
            exporter,
            running: Arc::new(tokio::sync::RwLock::new(false)),
        }
    }
    
    /// 启动处理循环
    pub async fn start(&self) {
        let mut is_running = self.running.write().await;
        if *is_running {
            warn!("批处理器已在运行");
            return;
        }
        *is_running = true;
        drop(is_running);
        
        info!("启动批处理器");
        
        let buffer = self.buffer.clone();
        let exporter = Arc::clone(&self.exporter);
        let config = self.config.clone();
        let running = Arc::clone(&self.running);
        
        tokio::spawn(async move {
            Self::process_loop(buffer, exporter, config, running).await;
        });
    }
    
    /// 停止处理循环
    pub async fn stop(&self) {
        let mut is_running = self.running.write().await;
        *is_running = false;
        info!("停止批处理器");
    }
    
    /// 强制刷新
    pub async fn flush(&self) -> Result<()> {
        let batch = self.buffer.pop_batch(self.config.batch_size);
        if !batch.is_empty() {
            debug!("强制刷新 {} spans", batch.len());
            self.exporter.export(batch).await?;
        }
        Ok(())
    }
    
    /// 处理循环
    async fn process_loop(
        buffer: LockFreeBuffer,
        exporter: Arc<dyn Exporter>,
        config: Config,
        running: Arc<tokio::sync::RwLock<bool>>,
    ) {
        let mut ticker = interval(Duration::from_millis(100));
        let mut last_export = std::time::Instant::now();
        
        loop {
            // 检查是否继续运行
            {
                let is_running = running.read().await;
                if !*is_running {
                    break;
                }
            }
            
            ticker.tick().await;
            
            let buffer_len = buffer.len();
            let should_export_by_size = buffer_len >= config.batch_size;
            let should_export_by_time = last_export.elapsed() >= config.batch_timeout();
            
            if should_export_by_size || (should_export_by_time && buffer_len > 0) {
                let batch = buffer.pop_batch(config.batch_size);
                
                if !batch.is_empty() {
                    debug!(
                        "导出批次: {} spans (原因: {})",
                        batch.len(),
                        if should_export_by_size { "大小" } else { "超时" }
                    );
                    
                    if let Err(e) = exporter.export(batch).await {
                        warn!("导出失败: {}", e);
                    }
                    
                    last_export = std::time::Instant::now();
                }
            }
        }
        
        info!("批处理器已停止");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exporter::MockExporter;
    
    #[tokio::test]
    async fn test_processor_basic() {
        let config = Config::default();
        let buffer = LockFreeBuffer::new(config.buffer_capacity);
        let exporter = Arc::new(MockExporter::new());
        
        let processor = BatchProcessor::new(config, buffer.clone(), exporter);
        
        processor.start().await;
        
        // 添加一些 spans
        for i in 0..10 {
            let span = Span::new(format!("span-{}", i));
            buffer.push(span).unwrap();
        }
        
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        processor.stop().await;
    }
}

