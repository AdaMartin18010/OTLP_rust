//! # Configuration Management
//!
//! This module provides configuration management for the OTLP crate,
//! including declarative configuration support.

pub mod declarative;

pub use declarative::{
    CONFIG_VERSION, ConfigError, ConfigResult, ExporterConfig, LoggerProviderConfig,
    MeterProviderConfig, OpenTelemetryConfig, OtlpExporterConfig, ResourceConfig,
    TracerProviderConfig,
};

// Rust 1.94: 批处理配置常量
/// 默认批处理大小
pub const DEFAULT_BATCH_SIZE: usize = 512;
/// 最大批处理大小
pub const MAX_BATCH_SIZE: usize = 2048;
/// 最小批处理大小
pub const MIN_BATCH_SIZE: usize = 8;
/// 默认超时 (毫秒)
pub const DEFAULT_TIMEOUT: u64 = 30000;

/// 验证批处理大小 (Rust 1.94: const fn 优化)
pub const fn validate_batch_size(size: usize) -> bool {
    size >= MIN_BATCH_SIZE && size <= MAX_BATCH_SIZE
}

/// 验证超时 (Rust 1.94: const fn 优化)
pub const fn validate_timeout(timeout_ms: u64) -> bool {
    timeout_ms > 0 && timeout_ms <= 300000 // 最大5分钟
}

// 压缩类型
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Compression {
    #[default]
    None,
    Gzip,
    Deflate,
    Brotli,
    Zstd,
}

// 传输协议
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransportProtocol {
    #[default]
    Grpc,
    Http,
    HttpBinary,
    HttpProtobuf,
}

impl TransportProtocol {
    /// 转换为字符串
    pub fn as_str(&self) -> &'static str {
        match self {
            TransportProtocol::Grpc => "grpc",
            TransportProtocol::Http => "http",
            TransportProtocol::HttpBinary => "http_binary",
            TransportProtocol::HttpProtobuf => "http_protobuf",
        }
    }
}

impl std::fmt::Display for TransportProtocol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl From<TransportProtocol> for String {
    fn from(protocol: TransportProtocol) -> Self {
        protocol.as_str().to_string()
    }
}

// 全局批处理配置
#[derive(Debug, Clone, Copy)]
pub struct GlobalBatchConfig {
    pub enabled: bool,
    pub max_queue_size: usize,
    pub max_export_batch_size: usize,
    pub schedule_delay_ms: u64,
    pub export_timeout_ms: u64,
}

impl Default for GlobalBatchConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            max_queue_size: 2048,
            max_export_batch_size: 512,
            schedule_delay_ms: 5000,
            export_timeout_ms: 30000,
        }
    }
}

// 兼容旧版配置类型 (临时，用于 validation 模块)
use serde::{Deserialize, Serialize};
use std::time::Duration;

/// 批处理配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchConfig {
    pub max_queue_size: usize,
    pub max_export_batch_size: usize,
    pub schedule_delay: Duration,
    pub export_timeout: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            max_queue_size: 2048,
            max_export_batch_size: 512,
            schedule_delay: Duration::from_millis(5000),
            export_timeout: Duration::from_secs(30),
        }
    }
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_backoff: Duration,
    pub max_backoff: Duration,
    pub randomize_retry_delay: bool,
    pub retry_delay_multiplier: f64,
    pub initial_retry_delay: Duration,
    pub max_retry_delay: Duration,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff: Duration::from_millis(100),
            max_backoff: Duration::from_secs(10),
            randomize_retry_delay: true,
            retry_delay_multiplier: 2.0,
            initial_retry_delay: Duration::from_millis(100),
            max_retry_delay: Duration::from_secs(60),
        }
    }
}

/// 服务配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ServiceConfig {
    pub name: String,
    pub version: String,
    pub namespace: Option<String>,
}

/// 采样配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SamplingConfig {
    pub ratio: f64,
    pub error_floor: Option<f64>,
}

impl Default for SamplingConfig {
    fn default() -> Self {
        Self {
            ratio: 1.0,
            error_floor: None,
        }
    }
}

/// 聚合配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AggregationConfig {
    pub enable_metrics: bool,
    pub enable_compression: bool,
    pub tenant_id_key: Option<String>,
    pub per_tenant_bucket_capacity: usize,
}

/// 租户限制配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TenantLimitConfig {
    pub refill_per_sec: u32,
    pub qps_limit: Option<u32>,
}

/// 审计配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AuditConfig {
    pub enabled: bool,
    pub log_level: String,
}

/// 调试配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DebugConfig {
    pub enabled: bool,
    pub log_level: String,
}

/// 旧版 OTLP 配置 (用于向后兼容)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpConfig {
    pub endpoint: String,
    pub timeout: u64,
    pub protocol: String,
    pub connect_timeout: Duration,
    pub request_timeout: Duration,
    pub retry_config: RetryConfig,
    pub batch_config: BatchConfig,
    pub compression: Option<String>,
    pub headers: std::collections::HashMap<String, String>,
    pub service: ServiceConfig,
    pub api_key: Option<String>,
    pub max_retries: u32,
    pub enabled: bool,
    pub resource_attributes: std::collections::HashMap<String, String>,
    pub sampling_ratio: f64,
    pub error_sampling_floor: Option<f64>,
    pub aggregation: AggregationConfig,
    pub enable_metrics: bool,
    pub tenant_id_key: Option<String>,
    pub per_tenant_bucket_capacity: usize,
    pub per_tenant_refill_per_sec: u32,
    pub per_tenant_qps_limit: Option<u32>,
    pub audit_enabled: bool,
    pub debug: DebugConfig,
}

impl OtlpConfig {
    /// 创建新的配置构建器
    pub fn new() -> Self {
        Self::default()
    }

    /// 设置 endpoint
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    /// 设置协议
    pub fn with_protocol(mut self, protocol: impl Into<String>) -> Self {
        self.protocol = protocol.into();
        self
    }

    /// 设置连接超时
    pub fn with_connect_timeout(mut self, timeout: Duration) -> Self {
        self.connect_timeout = timeout;
        self
    }

    /// 设置请求超时
    pub fn with_request_timeout(mut self, timeout: Duration) -> Self {
        self.request_timeout = timeout;
        self
    }

    /// 设置压缩方式
    pub fn with_compression(mut self, compression: impl Into<String>) -> Self {
        self.compression = Some(compression.into());
        self
    }

    /// 添加 header
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// 设置服务信息
    pub fn with_service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.service = ServiceConfig {
            name: name.into(),
            version: version.into(),
            namespace: None,
        };
        self
    }

    /// 设置 API key
    pub fn with_api_key(mut self, api_key: impl Into<String>) -> Self {
        self.api_key = Some(api_key.into());
        self
    }

    /// 启用/禁用
    pub fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }

    /// 添加资源属性
    pub fn with_resource_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.resource_attributes.insert(key.into(), value.into());
        self
    }

    /// 设置采样率
    pub fn with_sampling_ratio(mut self, ratio: f64) -> Self {
        self.sampling_ratio = ratio.clamp(0.0, 1.0);
        self
    }

    /// 设置错误采样下限
    pub fn with_error_sampling_floor(mut self, floor: f64) -> Self {
        self.error_sampling_floor = Some(floor);
        self
    }

    /// 设置指标启用
    pub fn with_metrics_enabled(mut self, enabled: bool) -> Self {
        self.enable_metrics = enabled;
        self
    }

    /// 验证配置
    pub fn validate(&self) -> Result<(), crate::error::OtlpError> {
        if self.endpoint.is_empty() {
            return Err(crate::error::OtlpError::ValidationError(
                "endpoint cannot be empty".to_string(),
            ));
        }
        Ok(())
    }

    /// 检查是否启用了压缩
    pub fn is_compression_enabled(&self) -> bool {
        self.compression.is_some() && self.compression.as_ref().unwrap() != "none"
    }

    /// 设置调试模式
    pub fn with_debug(mut self, enabled: bool) -> Self {
        self.debug.enabled = enabled;
        self
    }

    /// 设置批处理配置 (Rust 1.94 兼容)
    pub fn with_batch_config(mut self, config: BatchConfig) -> Self {
        self.batch_config = config;
        self
    }
}

/// OTLP 配置构建器 (向后兼容)
pub struct OtlpConfigBuilder {
    config: OtlpConfig,
}

impl OtlpConfigBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: OtlpConfig::default(),
        }
    }

    /// 设置 endpoint
    pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config.endpoint = endpoint.into();
        self
    }

    /// 设置协议
    pub fn protocol(mut self, protocol: impl Into<String>) -> Self {
        self.config.protocol = protocol.into();
        self
    }

    /// 设置连接超时
    pub fn connect_timeout(mut self, timeout: Duration) -> Self {
        self.config.connect_timeout = timeout;
        self
    }

    /// 设置请求超时
    pub fn request_timeout(mut self, timeout: Duration) -> Self {
        self.config.request_timeout = timeout;
        self
    }

    /// 设置压缩
    pub fn compression(mut self, compression: Compression) -> Self {
        self.config.compression = Some(format!("{:?}", compression).to_lowercase());
        self
    }

    /// 设置批处理配置
    pub fn batch_config(mut self, config: BatchConfig) -> Self {
        self.config.batch_config = config;
        self
    }

    /// 设置重试配置
    pub fn retry_config(mut self, config: RetryConfig) -> Self {
        self.config.retry_config = config;
        self
    }

    /// 添加 header
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.config.headers.insert(key.into(), value.into());
        self
    }

    /// 设置服务名称和版本
    pub fn service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.config.service = ServiceConfig {
            name: name.into(),
            version: version.into(),
            namespace: None,
        };
        self
    }

    /// 设置 API key
    pub fn api_key(mut self, api_key: impl Into<String>) -> Self {
        self.config.api_key = Some(api_key.into());
        self
    }

    /// 设置是否启用
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    /// 构建配置
    pub fn build(self) -> OtlpConfig {
        self.config
    }
}

impl Default for OtlpConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for OtlpConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout: 10000,
            protocol: "grpc".to_string(),
            connect_timeout: Duration::from_secs(10),
            request_timeout: Duration::from_secs(30),
            retry_config: RetryConfig::default(),
            batch_config: BatchConfig::default(),
            compression: None,
            headers: std::collections::HashMap::new(),
            service: ServiceConfig::default(),
            api_key: None,
            max_retries: 3,
            enabled: true,
            resource_attributes: std::collections::HashMap::new(),
            sampling_ratio: 1.0,
            error_sampling_floor: None,
            aggregation: AggregationConfig::default(),
            enable_metrics: true,
            tenant_id_key: None,
            per_tenant_bucket_capacity: 1000,
            per_tenant_refill_per_sec: 100,
            per_tenant_qps_limit: None,
            audit_enabled: false,
            debug: DebugConfig::default(),
        }
    }
}
