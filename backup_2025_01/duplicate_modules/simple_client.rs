//! # 简化的OTLP客户端API
//!
//! 提供更简洁、易用的OTLP客户端接口，降低学习成本和使用复杂度。
//! 利用Rust 1.90的新特性实现高性能和类型安全。

use crate::OtlpClient;
use crate::config::OtlpConfig;
use crate::data::{LogSeverity, StatusCode, TelemetryData};
use crate::error::Result;
use std::time::Duration;

/// 简化的OTLP客户端
///
/// 提供更直观的API接口，隐藏复杂的配置和实现细节
pub struct SimpleOtlpClient {
    client: OtlpClient,
}

impl SimpleOtlpClient {
    /// 创建新的简化客户端
    ///
    /// 使用默认配置，只需要指定端点
    pub async fn new(endpoint: impl Into<String>) -> Result<Self> {
        let config = OtlpConfig::default()
            .with_endpoint(endpoint)
            .with_debug(false);

        let client = OtlpClient::new(config).await?;
        client.initialize().await?;

        Ok(Self { client })
    }

    /// 创建带基本配置的客户端
    pub async fn with_config(
        endpoint: impl Into<String>,
        service_name: impl Into<String>,
        service_version: impl Into<String>,
    ) -> Result<Self> {
        let config = OtlpConfig::default()
            .with_endpoint(endpoint)
            .with_service(service_name, service_version)
            .with_debug(false);

        let client = OtlpClient::new(config).await?;
        client.initialize().await?;

        Ok(Self { client })
    }

    /// 发送简单的追踪数据
    ///
    /// # 参数
    /// - `operation`: 操作名称
    /// - `duration_ms`: 持续时间（毫秒）
    /// - `success`: 是否成功
    /// - `error_message`: 错误信息（可选）
    pub async fn trace(
        &self,
        operation: impl Into<String>,
        duration_ms: u64,
        success: bool,
        error_message: Option<impl Into<String>>,
    ) -> Result<()> {
        let status = if success {
            StatusCode::Ok
        } else {
            StatusCode::Error
        };

        let _result = self
            .client
            .send_trace(operation)
            .await?
            .with_numeric_attribute("duration_ms", duration_ms as f64)
            .with_bool_attribute("success", success)
            .with_status(status, error_message.map(|s| s.into()))
            .finish()
            .await?;

        Ok(())
    }

    /// 发送简单的指标数据
    ///
    /// # 参数
    /// - `metric_name`: 指标名称
    /// - `value`: 指标值
    /// - `unit`: 单位（可选）
    pub async fn metric(
        &self,
        metric_name: impl Into<String>,
        value: f64,
        unit: Option<impl Into<String>>,
    ) -> Result<()> {
        let mut builder = self.client.send_metric(metric_name, value).await?;

        if let Some(unit) = unit {
            builder = builder.with_unit(unit);
        }

        let _result = builder.send().await?;
        Ok(())
    }

    /// 发送简单的日志数据
    ///
    /// # 参数
    /// - `message`: 日志消息
    /// - `level`: 日志级别
    /// - `source`: 日志来源（可选）
    pub async fn log(
        &self,
        message: impl Into<String>,
        level: LogLevel,
        source: Option<impl Into<String>>,
    ) -> Result<()> {
        let severity = match level {
            LogLevel::Debug => LogSeverity::Debug,
            LogLevel::Info => LogSeverity::Info,
            LogLevel::Warn => LogSeverity::Warn,
            LogLevel::Error => LogSeverity::Error,
            LogLevel::Fatal => LogSeverity::Fatal,
        };

        let mut builder = self.client.send_log(message, severity).await?;

        if let Some(source) = source {
            builder = builder.with_attribute("source", source);
        }

        let _result = builder.send().await?;
        Ok(())
    }

    /// 批量发送数据
    ///
    /// 使用Rust 1.90的元组收集特性优化批量处理
    pub async fn batch_send(&self, operations: Vec<SimpleOperation>) -> Result<BatchResult> {
        let mut telemetry_data = Vec::new();

        for operation in operations {
            match operation {
                SimpleOperation::Trace {
                    name,
                    duration_ms,
                    success,
                    error,
                } => {
                    let data = TelemetryData::trace(name)
                        .with_numeric_attribute("duration_ms", duration_ms as f64)
                        .with_bool_attribute("success", success);

                    if let Some(error) = error {
                        let data = data.with_status(
                            if success {
                                StatusCode::Ok
                            } else {
                                StatusCode::Error
                            },
                            Some(error),
                        );
                        telemetry_data.push(data);
                    } else {
                        telemetry_data.push(data);
                    }
                }
                SimpleOperation::Metric {
                    name,
                    value: _value,
                    unit,
                } => {
                    let mut data = TelemetryData::metric(name, crate::data::MetricType::Gauge);
                    if let Some(unit) = unit {
                        data = data.with_attribute("unit", unit);
                    }
                    telemetry_data.push(data);
                }
                SimpleOperation::Log {
                    message,
                    level,
                    source,
                } => {
                    let severity = match level {
                        LogLevel::Debug => LogSeverity::Debug,
                        LogLevel::Info => LogSeverity::Info,
                        LogLevel::Warn => LogSeverity::Warn,
                        LogLevel::Error => LogSeverity::Error,
                        LogLevel::Fatal => LogSeverity::Fatal,
                    };

                    let mut data = TelemetryData::log(message, severity);
                    if let Some(source) = source {
                        data = data.with_attribute("source", source);
                    }
                    telemetry_data.push(data);
                }
            }
        }

        let result = self.client.send_batch(telemetry_data).await?;

        Ok(BatchResult {
            total_sent: result.total_count(),
            success_count: result.success_count,
            failure_count: result.failure_count,
            duration: result.duration,
        })
    }

    /// 获取客户端健康状态
    pub async fn health_check(&self) -> HealthStatus {
        let metrics = self.client.get_metrics().await;

        HealthStatus {
            is_healthy: metrics.exporter_metrics.failed_exports == 0,
            uptime: metrics.uptime,
            total_requests: metrics.total_data_sent,
            success_rate: if metrics.total_data_sent > 0 {
                (metrics.total_data_sent - metrics.exporter_metrics.failed_exports) as f64
                    / metrics.total_data_sent as f64
            } else {
                1.0
            },
        }
    }

    /// 关闭客户端
    pub async fn shutdown(self) -> Result<()> {
        self.client.shutdown().await
    }
}

/// 简化的日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

/// 简化的操作类型
#[derive(Debug, Clone)]
pub enum SimpleOperation {
    Trace {
        name: String,
        duration_ms: u64,
        success: bool,
        error: Option<String>,
    },
    Metric {
        name: String,
        value: f64,
        unit: Option<String>,
    },
    Log {
        message: String,
        level: LogLevel,
        source: Option<String>,
    },
}

/// 批量发送结果
#[derive(Debug, Clone)]
pub struct BatchResult {
    pub total_sent: usize,
    pub success_count: usize,
    pub failure_count: usize,
    pub duration: Duration,
}

/// 健康状态
#[derive(Debug, Clone)]
pub struct HealthStatus {
    pub is_healthy: bool,
    pub uptime: Duration,
    pub total_requests: u64,
    pub success_rate: f64,
}

/// 简化的客户端构建器
pub struct SimpleClientBuilder {
    endpoint: Option<String>,
    service_name: Option<String>,
    service_version: Option<String>,
    timeout: Option<Duration>,
    debug: bool,
}

impl SimpleClientBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            endpoint: None,
            service_name: None,
            service_version: None,
            timeout: None,
            debug: false,
        }
    }

    /// 设置端点
    pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = Some(endpoint.into());
        self
    }

    /// 设置服务信息
    pub fn service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.service_name = Some(name.into());
        self.service_version = Some(version.into());
        self
    }

    /// 设置超时
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// 启用调试模式
    pub fn debug(mut self, debug: bool) -> Self {
        self.debug = debug;
        self
    }

    /// 构建客户端
    pub async fn build(self) -> Result<SimpleOtlpClient> {
        let endpoint = self.endpoint.ok_or_else(|| {
            crate::error::OtlpError::Configuration(
                crate::error::ConfigurationError::InvalidEndpoint {
                    url: "endpoint is required".to_string(),
                },
            )
        })?;

        let mut config = OtlpConfig::default()
            .with_endpoint(endpoint)
            .with_debug(self.debug);

        if let Some(name) = self.service_name {
            let version = self.service_version.unwrap_or_else(|| "1.0.0".to_string());
            config = config.with_service(name, version);
        }

        if let Some(timeout) = self.timeout {
            config = config.with_request_timeout(timeout);
        }

        let client = OtlpClient::new(config).await?;
        client.initialize().await?;

        Ok(SimpleOtlpClient { client })
    }
}

impl Default for SimpleClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_simple_client_creation() {
        let client = SimpleOtlpClient::new("http://localhost:4317").await;
        assert!(client.is_ok());
    }

    #[tokio::test]
    async fn test_simple_client_builder() {
        let client = SimpleClientBuilder::new()
            .endpoint("http://localhost:4317")
            .service("test-service", "1.0.0")
            .timeout(Duration::from_secs(5))
            .build()
            .await;

        assert!(client.is_ok());
    }

    #[tokio::test]
    async fn test_simple_operations() {
        let client = SimpleOtlpClient::new("http://localhost:4317")
            .await
            .expect("Failed to create simple OTLP client");

        // 测试追踪
        let result = client
            .trace("test-operation", 100, true, None::<String>)
            .await;
        assert!(result.is_ok());

        // 测试指标
        let result = client.metric("test-metric", 42.0, Some("count")).await;
        assert!(result.is_ok());

        // 测试日志
        let result = client
            .log("test message", LogLevel::Info, Some("test"))
            .await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_batch_operations() {
        let client = SimpleOtlpClient::new("http://localhost:4317")
            .await
            .expect("Failed to create simple OTLP client");

        let operations = vec![
            SimpleOperation::Trace {
                name: "batch-operation-1".to_string(),
                duration_ms: 100,
                success: true,
                error: None,
            },
            SimpleOperation::Metric {
                name: "batch-metric".to_string(),
                value: 10.0,
                unit: Some("count".to_string()),
            },
            SimpleOperation::Log {
                message: "batch log".to_string(),
                level: LogLevel::Info,
                source: Some("batch".to_string()),
            },
        ];

        let result = client.batch_send(operations).await;
        assert!(result.is_ok());
    }
}
