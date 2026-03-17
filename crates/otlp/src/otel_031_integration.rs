//! # OpenTelemetry Rust 0.31 集成示例
//!
//! 本模块展示 OpenTelemetry Rust 0.31 的 API 使用模式。
//! 注意：OpenTelemetry 0.31 的 API 还在演进中，实际使用时请参考官方文档。
//!
//! ## 使用示例
//!
//! ```rust,ignore
//! use otlp::otel_031_integration::OtelConfig;
//!
//! let config = OtelConfig::builder()
//!     .with_endpoint("http://localhost:4317")
//!     .with_service_name("my-service")
//!     .build();
//! ```

use std::time::Duration;

/// OpenTelemetry 配置
#[derive(Debug, Clone)]
pub struct OtelConfig {
    /// OTLP 端点
    pub endpoint: String,
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 是否启用追踪
    pub traces_enabled: bool,
    /// 是否启用指标
    pub metrics_enabled: bool,
    /// 是否启用日志
    pub logs_enabled: bool,
    /// 超时设置
    pub timeout: Duration,
}

impl Default for OtelConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            service_name: "otlp-rust-service".to_string(),
            service_version: "1.0.0".to_string(),
            traces_enabled: true,
            metrics_enabled: true,
            logs_enabled: true,
            timeout: Duration::from_secs(30),
        }
    }
}

impl OtelConfig {
    /// 创建新的配置构建器
    pub fn builder() -> OtelConfigBuilder {
        OtelConfigBuilder::new()
    }
}

/// 配置构建器
#[derive(Debug)]
pub struct OtelConfigBuilder {
    config: OtelConfig,
}

impl OtelConfigBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: OtelConfig::default(),
        }
    }

    /// 设置端点
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config.endpoint = endpoint.into();
        self
    }

    /// 设置服务名称
    pub fn with_service_name(mut self, name: impl Into<String>) -> Self {
        self.config.service_name = name.into();
        self
    }

    /// 设置服务版本
    pub fn with_service_version(mut self, version: impl Into<String>) -> Self {
        self.config.service_version = version.into();
        self
    }

    /// 启用/禁用追踪
    pub fn with_traces(mut self, enabled: bool) -> Self {
        self.config.traces_enabled = enabled;
        self
    }

    /// 启用/禁用指标
    pub fn with_metrics(mut self, enabled: bool) -> Self {
        self.config.metrics_enabled = enabled;
        self
    }

    /// 启用/禁用日志
    pub fn with_logs(mut self, enabled: bool) -> Self {
        self.config.logs_enabled = enabled;
        self
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// 构建配置
    pub fn build(self) -> OtelConfig {
        self.config
    }
}

impl Default for OtelConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 采样配置
#[derive(Debug, Clone)]
pub struct OtelSamplingConfig {
    /// 采样率 (0.0 - 1.0)
    pub ratio: f64,
    /// 是否使用父采样决策
    pub parent_based: bool,
}

impl Default for OtelSamplingConfig {
    fn default() -> Self {
        Self {
            ratio: 1.0,
            parent_based: true,
        }
    }
}

impl OtelSamplingConfig {
    /// 创建新的采样配置
    pub fn new(ratio: f64) -> Self {
        Self {
            ratio: ratio.clamp(0.0, 1.0),
            parent_based: true,
        }
    }

    /// 禁用采样
    pub fn disabled() -> Self {
        Self {
            ratio: 0.0,
            parent_based: true,
        }
    }

    /// 始终采样
    pub fn always_on() -> Self {
        Self {
            ratio: 1.0,
            parent_based: true,
        }
    }
}

/// 批处理配置
#[derive(Debug, Clone)]
pub struct OtelBatchConfig {
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 调度延迟
    pub scheduled_delay: Duration,
    /// 最大批量大小
    pub max_batch_size: usize,
    /// 导出超时
    pub export_timeout: Duration,
}

impl Default for OtelBatchConfig {
    fn default() -> Self {
        Self {
            max_queue_size: 2048,
            scheduled_delay: Duration::from_millis(1000),
            max_batch_size: 512,
            export_timeout: Duration::from_secs(30),
        }
    }
}

/// OpenTelemetry 资源属性
#[derive(Debug, Clone, Default)]
pub struct OtelResource {
    /// 属性列表
    pub attributes: Vec<(String, String)>,
}

impl OtelResource {
    /// 创建新的资源
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.push((key.into(), value.into()));
        self
    }

    /// 设置服务名称
    pub fn with_service_name(self, name: impl Into<String>) -> Self {
        self.with_attribute("service.name", name)
    }

    /// 设置服务版本
    pub fn with_service_version(self, version: impl Into<String>) -> Self {
        self.with_attribute("service.version", version)
    }

    /// 设置部署环境
    pub fn with_deployment_environment(self, env: impl Into<String>) -> Self {
        self.with_attribute("deployment.environment", env)
    }
}

/// OTLP 协议类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OtlpProtocol {
    /// gRPC
    Grpc,
    /// HTTP/Protobuf
    HttpProtobuf,
    /// HTTP/JSON
    HttpJson,
}

impl Default for OtlpProtocol {
    fn default() -> Self {
        Self::Grpc
    }
}

impl std::fmt::Display for OtlpProtocol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtlpProtocol::Grpc => write!(f, "grpc"),
            OtlpProtocol::HttpProtobuf => write!(f, "http/protobuf"),
            OtlpProtocol::HttpJson => write!(f, "http/json"),
        }
    }
}

/// OpenTelemetry 初始化器
///
/// 简化 OpenTelemetry SDK 的初始化过程
pub struct OtelInitializer;

impl OtelInitializer {
    /// 使用配置初始化 OpenTelemetry
    ///
    /// 注意：这是一个示例实现，展示如何配置 OpenTelemetry。
    /// 实际使用时请参考 opentelemetry-rust 官方文档。
    pub fn init(_config: &OtelConfig) -> Result<OtelInitResult, OtelInitError> {
        // 这里应该初始化实际的 OpenTelemetry SDK
        // 由于 API 版本差异，这里仅返回成功
        tracing::info!("OpenTelemetry would be initialized here");
        
        Ok(OtelInitResult {
            traces_enabled: true,
            metrics_enabled: true,
            logs_enabled: true,
        })
    }
}

/// 初始化结果
#[derive(Debug, Clone)]
pub struct OtelInitResult {
    pub traces_enabled: bool,
    pub metrics_enabled: bool,
    pub logs_enabled: bool,
}

/// 初始化错误
#[derive(Debug, thiserror::Error)]
pub enum OtelInitError {
    #[error("Failed to initialize tracer provider: {0}")]
    TracerProviderError(String),
    
    #[error("Failed to initialize meter provider: {0}")]
    MeterProviderError(String),
    
    #[error("Failed to initialize logger provider: {0}")]
    LoggerProviderError(String),
    
    #[error("Invalid configuration: {0}")]
    InvalidConfig(String),
}

/// 便捷宏：创建属性向量
#[macro_export]
macro_rules! otel_attrs {
    ($($key:expr => $value:expr),*) => {
        vec![
            $(($key.to_string(), $value.to_string())),*
        ]
    };
}

/// 便捷函数：创建默认资源
pub fn default_resource(service_name: impl Into<String>) -> OtelResource {
    OtelResource::new()
        .with_service_name(service_name)
        .with_attribute("telemetry.sdk.name", "otlp-rust")
        .with_attribute("telemetry.sdk.language", "rust")
        .with_attribute("telemetry.sdk.version", "0.31.0")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_otel_config_default() {
        let config = OtelConfig::default();
        assert_eq!(config.endpoint, "http://localhost:4317");
        assert_eq!(config.service_name, "otlp-rust-service");
        assert!(config.traces_enabled);
        assert!(config.metrics_enabled);
        assert!(config.logs_enabled);
    }

    #[test]
    fn test_otel_config_builder() {
        let config = OtelConfig::builder()
            .with_endpoint("http://otel-collector:4317")
            .with_service_name("test-service")
            .with_traces(true)
            .with_metrics(false)
            .build();

        assert_eq!(config.endpoint, "http://otel-collector:4317");
        assert_eq!(config.service_name, "test-service");
        assert!(config.traces_enabled);
        assert!(!config.metrics_enabled);
    }

    #[test]
    fn test_sampling_config() {
        let config = OtelSamplingConfig::new(0.5);
        assert_eq!(config.ratio, 0.5);
        assert!(config.parent_based);

        let config = OtelSamplingConfig::disabled();
        assert_eq!(config.ratio, 0.0);

        let config = OtelSamplingConfig::always_on();
        assert_eq!(config.ratio, 1.0);
    }

    #[test]
    fn test_otel_resource() {
        let resource = OtelResource::new()
            .with_service_name("my-service")
            .with_service_version("1.0.0")
            .with_deployment_environment("production");

        assert_eq!(resource.attributes.len(), 3);
    }

    #[test]
    fn test_default_resource() {
        let resource = default_resource("test-service");
        
        assert!(resource.attributes.iter().any(|(k, _)| k == "service.name"));
        assert!(resource.attributes.iter().any(|(k, _)| k == "telemetry.sdk.name"));
    }

    #[test]
    fn test_otel_attrs_macro() {
        let attrs = otel_attrs!(
            "http.method" => "GET",
            "http.status_code" => "200"
        );
        
        assert_eq!(attrs.len(), 2);
        assert_eq!(attrs[0].0, "http.method");
        assert_eq!(attrs[0].1, "GET");
    }

    #[test]
    fn test_otlp_protocol_display() {
        assert_eq!(OtlpProtocol::Grpc.to_string(), "grpc");
        assert_eq!(OtlpProtocol::HttpProtobuf.to_string(), "http/protobuf");
        assert_eq!(OtlpProtocol::HttpJson.to_string(), "http/json");
    }
}
