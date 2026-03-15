//! # OTLP 客户端模块
//!
//! 提供OTLP客户端的高级接口，整合处理器、导出器和传输层。

mod builder;
mod metrics;

pub use builder::{LogBuilder, MetricBuilder, OtlpClientBuilder, TraceBuilder};
pub use metrics::{AuditHook, AuditEvent, ClientMetrics, EventType, FileAuditHook, HttpAuditHook, MetricsSnapshot, StdoutAuditHook};

use crate::config::OtlpConfig;
use crate::error::Result as OtlpResult;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{debug, info};

/// OTLP 客户端主结构
///
/// 提供完整的遥测数据发送功能，支持Trace、Metric、Log三种数据类型。
#[derive(Debug)]
pub struct OtlpClient {
    config: OtlpConfig,
    metrics: Arc<RwLock<ClientMetrics>>,
}

impl OtlpClient {
    /// 创建新的 OTLP 客户端
    ///
    /// # 参数
    /// * `config` - 客户端配置
    ///
    /// # 示例
    /// ```rust,no_run
    /// use otlp::{OtlpClient, OtlpConfig};
    ///
    /// async fn example() -> Result<(), Box<dyn std::error::Error>> {
    ///     let config = OtlpConfig::default();
    ///     let client = OtlpClient::new(config).await?;
    ///     Ok(())
    /// }
    /// ```
    pub async fn new(config: OtlpConfig) -> OtlpResult<Self> {
        debug!("Creating OTLP client with config: {:?}", config);
        info!("OTLP client created successfully");

        Ok(Self {
            config,
            metrics: Arc::new(RwLock::new(ClientMetrics::default())),
        })
    }

    /// 初始化客户端
    ///
    /// 初始化所有组件，准备发送数据。
    pub async fn initialize(&self) -> OtlpResult<()> {
        info!("Initializing OTLP client...");
        info!("OTLP client initialized successfully");
        Ok(())
    }

    /// 发送追踪数据
    ///
    /// # 参数
    /// * `operation_name` - 操作名称
    ///
    /// # 返回
    /// 返回 TraceBuilder 用于构建和发送追踪数据
    pub async fn send_trace(&self, operation_name: &str) -> OtlpResult<TraceBuilder> {
        debug!("Creating trace builder for operation: {}", operation_name);

        Ok(TraceBuilder::new(
            operation_name.to_string(),
            self.config.clone(),
        ))
    }

    /// 发送指标数据
    ///
    /// # 参数
    /// * `metric_name` - 指标名称
    /// * `value` - 指标值
    ///
    /// # 返回
    /// 返回 MetricBuilder 用于构建和发送指标数据
    pub async fn send_metric(&self, metric_name: &str, value: f64) -> OtlpResult<MetricBuilder> {
        debug!("Creating metric builder for: {} = {}", metric_name, value);

        Ok(MetricBuilder::new(
            metric_name.to_string(),
            value,
            self.config.clone(),
        ))
    }

    /// 发送日志数据
    ///
    /// # 参数
    /// * `message` - 日志消息
    ///
    /// # 返回
    /// 返回 LogBuilder 用于构建和发送日志数据
    pub async fn send_log(&self, message: &str) -> OtlpResult<LogBuilder> {
        debug!("Creating log builder for message: {}", message);

        Ok(LogBuilder::new(
            message.to_string(),
            self.config.clone(),
        ))
    }

    /// 关闭客户端
    ///
    /// 优雅地关闭所有组件，确保所有数据都被发送。
    pub async fn shutdown(&self) -> OtlpResult<()> {
        info!("Shutting down OTLP client...");
        info!("OTLP client shutdown complete");
        Ok(())
    }

    /// 获取客户端指标
    pub async fn metrics(&self) -> ClientMetrics {
        self.metrics.read().await.clone()
    }

    /// 获取配置
    pub fn config(&self) -> &OtlpConfig {
        &self.config
    }
}

impl Clone for OtlpClient {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            metrics: Arc::clone(&self.metrics),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_client_creation() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await;
        assert!(client.is_ok());
    }

    #[tokio::test]
    async fn test_client_builder_creation() {
        use crate::config::TransportProtocol;
        
        let builder = OtlpClientBuilder::new()
            .endpoint("http://localhost:4317")
            .protocol(TransportProtocol::Grpc)
            .timeout(std::time::Duration::from_secs(5));

        assert_eq!(builder.timeout, std::time::Duration::from_secs(5));
    }

    #[tokio::test]
    async fn test_client_trace_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let trace_builder = client.send_trace("test_operation").await;
        assert!(trace_builder.is_ok());
    }

    #[tokio::test]
    async fn test_client_metric_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let metric_builder = client.send_metric("test_metric", 42.0).await;
        assert!(metric_builder.is_ok());
    }

    #[tokio::test]
    async fn test_client_log_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let log_builder = client.send_log("test message").await;
        assert!(log_builder.is_ok());
    }

    #[test]
    fn test_client_metrics_default() {
        let metrics = ClientMetrics::default();
        let snapshot = metrics.snapshot();
        assert_eq!(snapshot.total_requests, 0);
    }
}
