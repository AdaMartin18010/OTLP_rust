//! 零拷贝导出器

use crate::{span::Span, CollectorError, Result};
use async_trait::async_trait;
use bytes::Bytes;
use std::sync::Arc;
use tracing::{debug, info};

/// 导出结果
#[derive(Debug, Clone)]
pub struct ExportResult {
    pub success_count: usize,
    pub failed_count: usize,
}

/// Exporter Trait
#[async_trait]
pub trait Exporter: Send + Sync {
    /// 导出 spans
    async fn export(&self, spans: Vec<Span>) -> Result<ExportResult>;
    
    /// 健康检查
    async fn health_check(&self) -> bool {
        true
    }
}

/// 零拷贝导出器
pub struct ZeroCopyExporter {
    endpoint: String,
    client: reqwest::Client,
}

impl ZeroCopyExporter {
    /// 创建新导出器
    pub fn new(endpoint: String) -> Self {
        Self {
            endpoint,
            client: reqwest::Client::new(),
        }
    }
    
    /// 序列化 spans
    fn serialize_spans(spans: &[Span]) -> Result<Bytes> {
        let json = serde_json::to_vec(spans)
            .map_err(|e| CollectorError::SerializationError(e.to_string()))?;
        Ok(Bytes::from(json))
    }
}

#[async_trait]
impl Exporter for ZeroCopyExporter {
    async fn export(&self, spans: Vec<Span>) -> Result<ExportResult> {
        let count = spans.len();
        debug!("导出 {} spans 到 {}", count, self.endpoint);
        
        // 序列化为 Bytes (零拷贝)
        let data = Self::serialize_spans(&spans)?;
        
        // Arc 包装实现多后端零拷贝共享
        let shared_data = Arc::new(data);
        
        // 发送到 OTLP 端点
        let response = self
            .client
            .post(&format!("{}/v1/traces", self.endpoint))
            .header("Content-Type", "application/json")
            .body((*shared_data).clone())
            .send()
            .await
            .map_err(|e| CollectorError::ExportFailed(e.to_string()))?;
        
        if response.status().is_success() {
            debug!("成功导出 {} spans", count);
            Ok(ExportResult {
                success_count: count,
                failed_count: 0,
            })
        } else {
            Err(CollectorError::ExportFailed(format!(
                "HTTP 错误: {}",
                response.status()
            )))
        }
    }
    
    async fn health_check(&self) -> bool {
        self.client
            .get(&format!("{}/health", self.endpoint))
            .send()
            .await
            .map(|r| r.status().is_success())
            .unwrap_or(false)
    }
}

/// Mock 导出器 (用于测试)
pub struct MockExporter {
    exported: Arc<tokio::sync::Mutex<Vec<Span>>>,
}

impl MockExporter {
    pub fn new() -> Self {
        Self {
            exported: Arc::new(tokio::sync::Mutex::new(Vec::new())),
        }
    }
    
    pub async fn get_exported(&self) -> Vec<Span> {
        self.exported.lock().await.clone()
    }
}

#[async_trait]
impl Exporter for MockExporter {
    async fn export(&self, spans: Vec<Span>) -> Result<ExportResult> {
        let count = spans.len();
        info!("Mock 导出 {} spans", count);
        
        let mut exported = self.exported.lock().await;
        exported.extend(spans);
        
        Ok(ExportResult {
            success_count: count,
            failed_count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_mock_exporter() {
        let exporter = MockExporter::new();
        
        let spans = vec![
            Span::new("span1".to_string()),
            Span::new("span2".to_string()),
        ];
        
        let result = exporter.export(spans.clone()).await.unwrap();
        assert_eq!(result.success_count, 2);
        
        let exported = exporter.get_exported().await;
        assert_eq!(exported.len(), 2);
    }
}

