//! # 优化的OTLP客户端模块
//!
//! 基于Rust 1.90特性优化的OTLP客户端实现，提供更好的性能和可维护性

use crate::config::{OtlpConfig, TransportProtocol};
use crate::data::{AttributeValue, LogData, MetricData, TelemetryData, TraceData};
use crate::error::{OtlpError, Result};
use crate::exporter::{ExportResult, OtlpExporter};
use crate::processor::{OtlpProcessor, ProcessingConfig};
use crate::resilience::{ResilienceConfig, ResilienceManager};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::interval;

/// 优化的OTLP客户端
///
/// 使用Rust 1.90的最新特性，提供更好的性能和内存安全
#[derive(Debug)]
pub struct OtlpClient {
    config: Arc<OtlpConfig>,
    exporter: Arc<OtlpExporter>,
    processor: Arc<RwLock<Option<OtlpProcessor>>>,
    resilience_manager: Arc<ResilienceManager>,
    metrics: Arc<RwLock<ClientMetrics>>,
    concurrency_limiter: Arc<Semaphore>,
    is_initialized: Arc<RwLock<bool>>,
    is_shutdown: Arc<RwLock<bool>>,
}

/// 客户端指标
#[derive(Debug, Default, Clone)]
pub struct ClientMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_data_sent: u64,
    pub active_connections: usize,
    pub start_time: Option<Instant>,
    pub uptime: Duration,
}

/// 客户端构建器
pub struct OtlpClientBuilder {
    config: OtlpConfig,
    processing_config: Option<ProcessingConfig>,
    resilience_config: Option<ResilienceConfig>,
    max_concurrency: Option<usize>,
}

impl OtlpClientBuilder {
    /// 创建新的客户端构建器
    pub fn new() -> Self {
        Self {
            config: OtlpConfig::default(),
            processing_config: None,
            resilience_config: None,
            max_concurrency: None,
        }
    }

    /// 设置配置
    pub fn with_config(mut self, config: OtlpConfig) -> Self {
        self.config = config;
        self
    }

    /// 设置处理配置
    pub fn with_processing_config(mut self, config: ProcessingConfig) -> Self {
        self.processing_config = Some(config);
        self
    }

    /// 设置弹性配置
    pub fn with_resilience_config(mut self, config: ResilienceConfig) -> Self {
        self.resilience_config = Some(config);
        self
    }

    /// 设置最大并发数
    pub fn with_max_concurrency(mut self, max_concurrency: usize) -> Self {
        self.max_concurrency = Some(max_concurrency);
        self
    }

    /// 构建客户端
    pub async fn build(self) -> Result<OtlpClient> {
        let config = Arc::new(self.config);

        // 创建导出器
        let exporter = Arc::new(OtlpExporter::new(config.clone()).await?);

        // 创建处理器
        let processing_config = self.processing_config
            .unwrap_or_else(ProcessingConfig::default);
        let processor = Arc::new(RwLock::new(Some(
            OtlpProcessor::new(processing_config).await?
        )));

        // 创建弹性管理器
        let resilience_config = self.resilience_config
            .unwrap_or_else(ResilienceConfig::default);
        let resilience_manager = Arc::new(ResilienceManager::new(resilience_config));

        // 创建并发限制器
        let max_concurrency = self.max_concurrency.unwrap_or(100);
        let concurrency_limiter = Arc::new(Semaphore::new(max_concurrency));

        // 创建指标
        let metrics = Arc::new(RwLock::new(ClientMetrics {
            start_time: Some(Instant::now()),
            ..Default::default()
        }));

        Ok(OtlpClient {
            config,
            exporter,
            processor,
            resilience_manager,
            metrics,
            concurrency_limiter,
            is_initialized: Arc::new(RwLock::new(false)),
            is_shutdown: Arc::new(RwLock::new(false)),
        })
    }
}

impl Default for OtlpClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl OtlpClient {
    /// 初始化客户端
    pub async fn initialize(&self) -> Result<()> {
        let mut is_initialized = self.is_initialized.write().await;
        if *is_initialized {
            return Ok(());
        }

        // 初始化导出器
        self.exporter.initialize().await?;

        // 初始化处理器
        if let Some(processor) = self.processor.read().await.as_ref() {
            processor.initialize().await?;
        }

        // 初始化弹性管理器
        self.resilience_manager.initialize().await?;

        *is_initialized = true;
        Ok(())
    }

    /// 发送遥测数据
    pub async fn send_data(&self, data: TelemetryData) -> Result<ExportResult> {
        // 检查是否已初始化
        if !*self.is_initialized.read().await {
            return Err(OtlpError::ClientNotInitialized);
        }

        // 检查是否已关闭
        if *self.is_shutdown.read().await {
            return Err(OtlpError::ClientShutdown);
        }

        // 获取并发许可
        let _permit = self.concurrency_limiter.acquire().await
            .map_err(|_| OtlpError::ConcurrencyLimitExceeded)?;

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_requests += 1;
        }

        // 处理数据
        let processed_data = if let Some(processor) = self.processor.read().await.as_ref() {
            processor.process(data).await?
        } else {
            data
        };

        // 导出数据
        let result = self.exporter.export(processed_data).await;

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            match &result {
                Ok(export_result) => {
                    metrics.successful_requests += 1;
                    metrics.total_data_sent += export_result.bytes_sent;
                }
                Err(_) => {
                    metrics.failed_requests += 1;
                }
            }
        }

        result
    }

    /// 批量发送数据
    pub async fn send_batch(&self, batch: Vec<TelemetryData>) -> Result<Vec<ExportResult>> {
        let mut results = Vec::with_capacity(batch.len());

        for data in batch {
            let result = self.send_data(data).await;
            results.push(result);
        }

        Ok(results)
    }

    /// 获取客户端指标
    pub async fn get_metrics(&self) -> ClientMetrics {
        let mut metrics = self.metrics.read().await.clone();

        // 更新运行时间
        if let Some(start_time) = metrics.start_time {
            metrics.uptime = start_time.elapsed();
        }

        metrics
    }

    /// 关闭客户端
    pub async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        if *is_shutdown {
            return Ok(());
        }

        // 关闭处理器
        if let Some(processor) = self.processor.write().await.take() {
            processor.shutdown().await?;
        }

        // 关闭导出器
        self.exporter.shutdown().await?;

        // 关闭弹性管理器
        self.resilience_manager.shutdown().await?;

        *is_shutdown = true;
        Ok(())
    }
}

/// 追踪数据构建器
pub struct TraceBuilder {
    trace_id: String,
    span_id: String,
    parent_span_id: Option<String>,
    name: String,
    span_kind: crate::data::SpanKind,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, AttributeValue>,
    events: Vec<crate::data::SpanEvent>,
    links: Vec<crate::data::SpanLink>,
}

impl TraceBuilder {
    /// 创建新的追踪构建器
    pub fn new(trace_id: String, span_id: String, name: String) -> Self {
        Self {
            trace_id,
            span_id,
            parent_span_id: None,
            name,
            span_kind: crate::data::SpanKind::Internal,
            start_time: 0,
            end_time: 0,
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        }
    }

    /// 设置父级span ID
    pub fn with_parent_span_id(mut self, parent_span_id: String) -> Self {
        self.parent_span_id = Some(parent_span_id);
        self
    }

    /// 设置span类型
    pub fn with_span_kind(mut self, span_kind: crate::data::SpanKind) -> Self {
        self.span_kind = span_kind;
        self
    }

    /// 设置时间范围
    pub fn with_time_range(mut self, start_time: u64, end_time: u64) -> Self {
        self.start_time = start_time;
        self.end_time = end_time;
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.attributes.insert(key, value);
        self
    }

    /// 添加事件
    pub fn with_event(mut self, event: crate::data::SpanEvent) -> Self {
        self.events.push(event);
        self
    }

    /// 添加链接
    pub fn with_link(mut self, link: crate::data::SpanLink) -> Self {
        self.links.push(link);
        self
    }

    /// 构建追踪数据
    pub fn build(self) -> TraceData {
        TraceData {
            trace_id: self.trace_id,
            span_id: self.span_id,
            parent_span_id: self.parent_span_id,
            name: self.name,
            span_kind: self.span_kind,
            start_time: self.start_time,
            end_time: self.end_time,
            status: crate::data::SpanStatus::default(),
            attributes: self.attributes,
            events: self.events,
            links: self.links,
        }
    }
}

/// 指标数据构建器
pub struct MetricBuilder {
    name: String,
    description: String,
    unit: String,
    metric_type: crate::data::MetricType,
    data_points: Vec<crate::data::MetricDataPoint>,
    attributes: HashMap<String, AttributeValue>,
}

impl MetricBuilder {
    /// 创建新的指标构建器
    pub fn new(name: String, metric_type: crate::data::MetricType) -> Self {
        Self {
            name,
            description: String::new(),
            unit: String::new(),
            metric_type,
            data_points: Vec::new(),
            attributes: HashMap::new(),
        }
    }

    /// 设置描述
    pub fn with_description(mut self, description: String) -> Self {
        self.description = description;
        self
    }

    /// 设置单位
    pub fn with_unit(mut self, unit: String) -> Self {
        self.unit = unit;
        self
    }

    /// 添加数据点
    pub fn with_data_point(mut self, data_point: crate::data::MetricDataPoint) -> Self {
        self.data_points.push(data_point);
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.attributes.insert(key, value);
        self
    }

    /// 构建指标数据
    pub fn build(self) -> MetricData {
        MetricData {
            name: self.name,
            description: self.description,
            unit: self.unit,
            metric_type: self.metric_type,
            data_points: self.data_points,
            attributes: self.attributes,
        }
    }
}

/// 日志数据构建器
pub struct LogBuilder {
    timestamp: u64,
    severity: crate::data::LogSeverity,
    body: String,
    attributes: HashMap<String, AttributeValue>,
    resource: HashMap<String, AttributeValue>,
}

impl LogBuilder {
    /// 创建新的日志构建器
    pub fn new(body: String) -> Self {
        Self {
            timestamp: 0,
            severity: crate::data::LogSeverity::Info,
            body,
            attributes: HashMap::new(),
            resource: HashMap::new(),
        }
    }

    /// 设置时间戳
    pub fn with_timestamp(mut self, timestamp: u64) -> Self {
        self.timestamp = timestamp;
        self
    }

    /// 设置严重级别
    pub fn with_severity(mut self, severity: crate::data::LogSeverity) -> Self {
        self.severity = severity;
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.attributes.insert(key, value);
        self
    }

    /// 添加资源属性
    pub fn with_resource_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.resource.insert(key, value);
        self
    }

    /// 构建日志数据
    pub fn build(self) -> LogData {
        LogData {
            timestamp: self.timestamp,
            severity: self.severity,
            body: self.body,
            attributes: self.attributes,
            resource: self.resource,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{AttributeValue, LogSeverity, MetricType, SpanKind};

    #[tokio::test]
    async fn test_client_builder() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Http);

        let client = OtlpClientBuilder::new()
            .with_config(config)
            .with_max_concurrency(50)
            .build()
            .await;

        assert!(client.is_ok());
    }

    #[test]
    fn test_trace_builder() {
        let trace = TraceBuilder::new(
            "trace-123".to_string(),
            "span-456".to_string(),
            "test-operation".to_string(),
        )
        .with_parent_span_id("parent-span-789".to_string())
        .with_span_kind(SpanKind::Server)
        .with_time_range(1000, 2000)
        .with_attribute("key".to_string(), AttributeValue::String("value".to_string()))
        .build();

        assert_eq!(trace.trace_id, "trace-123");
        assert_eq!(trace.span_id, "span-456");
        assert_eq!(trace.parent_span_id, Some("parent-span-789".to_string()));
        assert_eq!(trace.name, "test-operation");
        assert_eq!(trace.span_kind, SpanKind::Server);
        assert_eq!(trace.start_time, 1000);
        assert_eq!(trace.end_time, 2000);
    }

    #[test]
    fn test_metric_builder() {
        let metric = MetricBuilder::new("test-metric".to_string(), MetricType::Counter)
            .with_description("Test metric".to_string())
            .with_unit("count".to_string())
            .with_attribute("key".to_string(), AttributeValue::String("value".to_string()))
            .build();

        assert_eq!(metric.name, "test-metric");
        assert_eq!(metric.description, "Test metric");
        assert_eq!(metric.unit, "count");
        assert_eq!(metric.metric_type, MetricType::Counter);
    }

    #[test]
    fn test_log_builder() {
        let log = LogBuilder::new("Test log message".to_string())
            .with_timestamp(1234567890)
            .with_severity(LogSeverity::Error)
            .with_attribute("key".to_string(), AttributeValue::String("value".to_string()))
            .build();

        assert_eq!(log.body, "Test log message");
        assert_eq!(log.timestamp, 1234567890);
        assert_eq!(log.severity, LogSeverity::Error);
    }
}
