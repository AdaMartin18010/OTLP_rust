//! # 客户端构建器
//!
//! 提供流畅的API用于构建和配置OTLP客户端及遥测数据。

use crate::config::{OtlpConfig, TransportProtocol};
use crate::data::{LogSeverity, StatusCode, TelemetryContent, TelemetryData, TelemetryDataType};
use crate::error::Result as OtlpResult;
use crate::exporter::OtlpExporter;
use std::collections::HashMap;
use std::time::Duration;




/// OTLP 客户端构建器
///
/// 使用构建器模式创建和配置 OTLP 客户端。
///
/// # 示例
/// ```rust,no_run
/// use otlp::client::OtlpClientBuilder;
/// use otlp::config::TransportProtocol;
///
/// async fn example() {
///     let client = OtlpClientBuilder::new()
///         .endpoint("http://localhost:4317")
///         .protocol(TransportProtocol::Grpc)
///         .timeout(std::time::Duration::from_secs(5))
///         .build()
///         .await
///         .expect("Failed to create client");
/// }
/// ```
#[derive(Debug, Default)]
pub struct OtlpClientBuilder {
    pub(crate) endpoint: Option<String>,
    pub(crate) protocol: TransportProtocol,
    pub(crate) timeout: Duration,
    pub(crate) batch_size: usize,
    pub(crate) service_name: String,
    pub(crate) service_version: String,
    pub(crate) attributes: HashMap<String, String>,
}

impl OtlpClientBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            endpoint: None,
            protocol: TransportProtocol::Grpc,
            timeout: Duration::from_secs(30),
            batch_size: 100,
            service_name: "unknown-service".to_string(),
            service_version: "0.1.0".to_string(),
            attributes: HashMap::new(),
        }
    }

    /// 设置端点
    pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = Some(endpoint.into());
        self
    }

    /// 设置传输协议
    pub fn protocol(mut self, protocol: TransportProtocol) -> Self {
        self.protocol = protocol;
        self
    }

    /// 设置超时
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// 设置批处理大小
    pub fn batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }

    /// 设置服务信息
    pub fn service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.service_name = name.into();
        self.service_version = version.into();
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// 构建客户端
    pub async fn build(self) -> OtlpResult<super::OtlpClient> {
        let _ = self.batch_size; // 保留字段，暂不直接使用
        let config = OtlpConfig::default()
            .with_endpoint(self.endpoint.unwrap_or_else(|| "http://localhost:4317".to_string()))
            .with_protocol(format!("{:?}", self.protocol))
            .with_connect_timeout(self.timeout);

        super::OtlpClient::new(config).await
    }
}

/// 追踪数据构建器
#[derive(Debug)]
#[allow(dead_code)]
pub struct TraceBuilder {
    operation_name: String,
    attributes: HashMap<String, String>,
    numeric_attributes: HashMap<String, f64>,
    status: StatusCode,
    status_message: Option<String>,
    duration_ms: u64,
    config: OtlpConfig,
}

impl TraceBuilder {
    /// 创建新的追踪构建器
    pub(crate) fn new(
        operation_name: String,
        config: OtlpConfig,
    ) -> Self {
        Self {
            operation_name,
            attributes: HashMap::new(),
            numeric_attributes: HashMap::new(),
            status: StatusCode::Unset,
            status_message: None,
            duration_ms: 0,
            config,
        }
    }

    /// 添加字符串属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: impl Into<String>, value: f64) -> Self {
        self.numeric_attributes.insert(key.into(), value);
        self
    }

    /// 设置状态
    pub fn with_status(mut self, status: StatusCode, message: Option<String>) -> Self {
        self.status = status;
        self.status_message = message;
        self
    }

    /// 设置持续时间
    pub fn with_duration(mut self, duration_ms: u64) -> Self {
        self.duration_ms = duration_ms;
        self
    }

    /// 完成并发送追踪数据
    pub async fn finish(self) -> OtlpResult<()> {
        use crate::data::{AttributeValue, SpanKind, SpanStatus, TraceData};
        
        tracing::debug!(
            "Finishing trace for operation: {} with {} attributes",
            self.operation_name,
            self.attributes.len()
        );
        
        // 创建追踪数据
        let trace_content = TraceData {
            trace_id: format!("trace_{}", uuid::Uuid::new_v4()),
            span_id: format!("span_{}", uuid::Uuid::new_v4()),
            parent_span_id: None,
            name: self.operation_name,
            span_kind: SpanKind::Internal,
            start_time: 0,
            end_time: self.duration_ms,
            attributes: self.attributes.into_iter()
                .map(|(k, v)| (k, AttributeValue::String(v)))
                .collect(),
            events: Vec::new(),
            links: Vec::new(),
            status: SpanStatus {
                code: self.status,
                message: self.status_message,
            },
        };
        
        let trace_data = TelemetryData {
            data_type: TelemetryDataType::Trace,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            resource_attributes: self.numeric_attributes.iter()
                .map(|(k, v)| (k.clone(), v.to_string()))
                .collect(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Trace(trace_content),
        };
        
        // 使用 exporter 发送数据
        let exporter = OtlpExporter::new(self.config);
        exporter.initialize().await?;
        
        match exporter.export(vec![trace_data]).await {
            Ok(result) => {
                tracing::debug!("Trace exported successfully: {} items", result.success_count);
                Ok(())
            }
            Err(e) => {
                tracing::error!("Failed to export trace: {}", e);
                Err(e)
            }
        }
    }
}

/// 指标数据构建器
#[derive(Debug)]
#[allow(dead_code)]
pub struct MetricBuilder {
    metric_name: String,
    value: f64,
    labels: HashMap<String, String>,
    description: Option<String>,
    unit: Option<String>,
    config: OtlpConfig,
}

impl MetricBuilder {
    /// 创建新的指标构建器
    pub(crate) fn new(
        metric_name: String,
        value: f64,
        config: OtlpConfig,
    ) -> Self {
        Self {
            metric_name,
            value,
            labels: HashMap::new(),
            description: None,
            unit: None,
            config,
        }
    }

    /// 添加标签
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }

    /// 设置描述
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = Some(description.into());
        self
    }

    /// 设置单位
    pub fn with_unit(mut self, unit: impl Into<String>) -> Self {
        self.unit = Some(unit.into());
        self
    }

    /// 发送指标数据
    pub async fn send(self) -> OtlpResult<()> {
        use crate::data::{DataPoint, DataPointValue, MetricData};
        
        tracing::debug!(
            "Sending metric: {} = {} with {} labels",
            self.metric_name,
            self.value,
            self.labels.len()
        );
        
        // 创建指标数据点
        let data_point = DataPoint {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            attributes: self.labels.iter()
                .map(|(k, v)| (k.clone(), crate::data::AttributeValue::String(v.clone())))
                .collect(),
            value: DataPointValue::Number(self.value),
        };
        
        let metric_content = MetricData {
            name: self.metric_name,
            description: self.description.unwrap_or_default(),
            unit: self.unit.unwrap_or_else(|| "count".to_string()),
            metric_type: crate::data::MetricType::Gauge,
            data_points: vec![data_point],
        };
        
        let telemetry_data = TelemetryData {
            data_type: TelemetryDataType::Metric,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Metric(metric_content),
        };
        
        // 使用 exporter 发送数据
        let exporter = OtlpExporter::new(self.config);
        exporter.initialize().await?;
        
        match exporter.export(vec![telemetry_data]).await {
            Ok(result) => {
                tracing::debug!("Metric exported successfully: {} items", result.success_count);
                Ok(())
            }
            Err(e) => {
                tracing::error!("Failed to export metric: {}", e);
                Err(e)
            }
        }
    }
}

/// 日志数据构建器
#[derive(Debug)]
#[allow(dead_code)]
pub struct LogBuilder {
    message: String,
    severity: LogSeverity,
    attributes: HashMap<String, String>,
    config: OtlpConfig,
}

impl LogBuilder {
    /// 创建新的日志构建器
    pub(crate) fn new(
        message: String,
        config: OtlpConfig,
    ) -> Self {
        Self {
            message,
            severity: LogSeverity::Info,
            attributes: HashMap::new(),
            config,
        }
    }

    /// 设置严重级别
    pub fn with_severity(mut self, severity: LogSeverity) -> Self {
        self.severity = severity;
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// 发送日志数据
    pub async fn send(self) -> OtlpResult<()> {
        use crate::data::LogData;
        
        let severity_str = match self.severity {
            LogSeverity::Trace => "TRACE",
            LogSeverity::Debug => "DEBUG",
            LogSeverity::Info => "INFO",
            LogSeverity::Warn => "WARN",
            LogSeverity::Error => "ERROR",
            LogSeverity::Fatal => "FATAL",
        };
        tracing::debug!(
            "Sending log: [{}] {} with {} attributes",
            severity_str,
            self.message,
            self.attributes.len()
        );
        
        // 创建日志数据内容
        let log_content = LogData {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            severity: self.severity,
            severity_text: severity_str.to_string(),
            message: self.message,
            attributes: self.attributes.into_iter()
                .map(|(k, v)| (k, crate::data::AttributeValue::String(v)))
                .collect(),
            resource_attributes: HashMap::new(),
            trace_id: None,
            span_id: None,
        };
        
        let log_data = TelemetryData {
            data_type: TelemetryDataType::Log,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Log(log_content),
        };
        
        // 使用 exporter 发送数据
        let exporter = OtlpExporter::new(self.config);
        exporter.initialize().await?;
        
        match exporter.export(vec![log_data]).await {
            Ok(result) => {
                tracing::debug!("Log exported successfully: {} items", result.success_count);
                Ok(())
            }
            Err(e) => {
                tracing::error!("Failed to export log: {}", e);
                Err(e)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_client_builder_configuration() {
        let builder = OtlpClientBuilder::new()
            .endpoint("http://test:4317")
            .protocol(TransportProtocol::Http)
            .timeout(Duration::from_secs(10))
            .batch_size(50)
            .service("test-service", "1.0.0")
            .with_attribute("env", "test");

        assert_eq!(builder.batch_size, 50);
        assert_eq!(builder.service_name, "test-service");
    }

    #[test]
    fn test_trace_builder_chain() {
        let config = OtlpConfig::default();
        let builder = TraceBuilder::new("test".to_string(), config)
            .with_attribute("key", "value")
            .with_numeric_attribute("num", 42.0)
            .with_duration(100);

        assert_eq!(builder.operation_name, "test");
    }

    #[test]
    fn test_metric_builder_chain() {
        let config = OtlpConfig::default();
        let builder = MetricBuilder::new("metric".to_string(), 42.0, config)
            .with_label("env", "test")
            .with_description("test metric")
            .with_unit("count");

        assert_eq!(builder.metric_name, "metric");
    }

    #[test]
    fn test_log_builder_chain() {
        let config = OtlpConfig::default();
        let builder = LogBuilder::new("message".to_string(), config)
            .with_severity(LogSeverity::Error)
            .with_attribute("key", "value");

        assert_eq!(builder.message, "message");
    }
}
