//! # 增强的Exporter构建器
//!
//! 提供链式API来配置和构建具有多种功能的Exporter。
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::wrappers::enhanced_exporter::{EnhancedExporter, ExporterConfig};
//!
//! let exporter = EnhancedExporter::new()
//!     .with_compression(true)
//!     .with_batch_size(100)
//!     .with_timeout(Duration::from_secs(30))
//!     .build()?;
//! ```

use std::time::Duration;
use anyhow::{Result, anyhow};

/// Exporter配置
#[derive(Debug, Clone)]
pub struct ExporterConfig {
    /// 是否启用压缩
    pub compression: bool,
    /// 批处理大小
    pub batch_size: usize,
    /// 超时时间
    pub timeout: Duration,
    /// 是否启用重试
    pub retry_enabled: bool,
    /// 最大重试次数
    pub max_retries: u32,
    /// 是否启用连接池
    pub connection_pool: bool,
    /// 是否启用多租户
    pub multi_tenant: bool,
    /// 租户ID
    pub tenant_id: Option<String>,
    /// 端点URL
    pub endpoint: String,
    /// 是否使用gRPC
    pub use_grpc: bool,
}

impl Default for ExporterConfig {
    fn default() -> Self {
        Self {
            compression: true,
            batch_size: 512,
            timeout: Duration::from_secs(30),
            retry_enabled: true,
            max_retries: 3,
            connection_pool: true,
            multi_tenant: false,
            tenant_id: None,
            endpoint: "http://localhost:4317".to_string(),
            use_grpc: true,
        }
    }
}

/// 增强的Exporter构建器
#[derive(Debug, Clone)]
pub struct EnhancedExporter {
    config: ExporterConfig,
}

impl EnhancedExporter {
    /// 创建新的增强Exporter构建器
    pub fn new() -> Self {
        Self {
            config: ExporterConfig::default(),
        }
    }

    /// 从现有配置创建
    pub fn from_config(config: ExporterConfig) -> Self {
        Self { config }
    }

    /// 启用或禁用压缩
    pub fn with_compression(mut self, enabled: bool) -> Self {
        self.config.compression = enabled;
        self
    }

    /// 设置批处理大小
    pub fn with_batch_size(mut self, size: usize) -> Self {
        self.config.batch_size = size;
        self
    }

    /// 设置超时时间
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// 启用或禁用重试
    pub fn with_retry(mut self, enabled: bool) -> Self {
        self.config.retry_enabled = enabled;
        self
    }

    /// 设置最大重试次数
    pub fn with_max_retries(mut self, retries: u32) -> Self {
        self.config.max_retries = retries;
        self
    }

    /// 启用或禁用连接池
    pub fn with_connection_pool(mut self, enabled: bool) -> Self {
        self.config.connection_pool = enabled;
        self
    }

    /// 启用多租户模式
    pub fn with_multi_tenant(mut self, enabled: bool) -> Self {
        self.config.multi_tenant = enabled;
        self
    }

    /// 设置租户ID
    pub fn with_tenant_id(mut self, tenant_id: impl Into<String>) -> Self {
        self.config.tenant_id = Some(tenant_id.into());
        self.config.multi_tenant = true;
        self
    }

    /// 设置端点
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config.endpoint = endpoint.into();
        self
    }

    /// 使用gRPC协议
    pub fn with_grpc(mut self) -> Self {
        self.config.use_grpc = true;
        self
    }

    /// 使用HTTP协议
    pub fn with_http(mut self) -> Self {
        self.config.use_grpc = false;
        self
    }

    /// 构建Exporter配置
    /// 
    /// 返回配置对象，可用于创建具体的Exporter实例
    pub fn build(self) -> Result<ExporterConfig> {
        // 验证配置
        if self.config.batch_size == 0 {
            return Err(anyhow!("批处理大小必须大于0"));
        }
        
        if self.config.timeout.is_zero() {
            return Err(anyhow!("超时时间必须大于0"));
        }
        
        if self.config.endpoint.is_empty() {
            return Err(anyhow!("端点不能为空"));
        }

        // 验证多租户配置
        if self.config.multi_tenant && self.config.tenant_id.is_none() {
            return Err(anyhow!("启用多租户模式时必须提供租户ID"));
        }

        Ok(self.config)
    }

    /// 获取当前配置
    pub fn config(&self) -> &ExporterConfig {
        &self.config
    }
}

impl Default for EnhancedExporter {
    fn default() -> Self {
        Self::new()
    }
}

/// 预定义的Exporter配置预设
pub mod presets {
    use super::*;

    /// 高吞吐量预设
    pub fn high_throughput() -> ExporterConfig {
        ExporterConfig {
            batch_size: 1024,
            compression: true,
            connection_pool: true,
            ..Default::default()
        }
    }

    /// 低延迟预设
    pub fn low_latency() -> ExporterConfig {
        ExporterConfig {
            batch_size: 100,
            timeout: Duration::from_secs(5),
            compression: false, // 禁用压缩以减少延迟
            ..Default::default()
        }
    }

    /// 高可靠性预设
    pub fn high_reliability() -> ExporterConfig {
        ExporterConfig {
            retry_enabled: true,
            max_retries: 5,
            batch_size: 256,
            ..Default::default()
        }
    }

    /// 开发环境预设
    pub fn development() -> ExporterConfig {
        ExporterConfig {
            compression: false,
            retry_enabled: false,
            connection_pool: false,
            endpoint: "http://localhost:4317".to_string(),
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_enhanced_exporter_builder() {
        let exporter = EnhancedExporter::new()
            .with_compression(true)
            .with_batch_size(100)
            .with_timeout(Duration::from_secs(10))
            .with_retry(true)
            .with_max_retries(5)
            .with_endpoint("http://otel-collector:4317");

        let config = exporter.build().unwrap();
        
        assert!(config.compression);
        assert_eq!(config.batch_size, 100);
        assert_eq!(config.timeout, Duration::from_secs(10));
        assert!(config.retry_enabled);
        assert_eq!(config.max_retries, 5);
        assert_eq!(config.endpoint, "http://otel-collector:4317");
    }

    #[test]
    fn test_multi_tenant_config() {
        let exporter = EnhancedExporter::new()
            .with_multi_tenant(true)
            .with_tenant_id("tenant-123");

        let config = exporter.build().unwrap();
        
        assert!(config.multi_tenant);
        assert_eq!(config.tenant_id, Some("tenant-123".to_string()));
    }

    #[test]
    fn test_presets() {
        let high_throughput = presets::high_throughput();
        assert_eq!(high_throughput.batch_size, 1024);
        assert!(high_throughput.compression);

        let low_latency = presets::low_latency();
        assert_eq!(low_latency.batch_size, 100);
        assert!(!low_latency.compression);

        let high_reliability = presets::high_reliability();
        assert_eq!(high_reliability.max_retries, 5);
        assert!(high_reliability.retry_enabled);
    }

    #[test]
    fn test_invalid_config() {
        // 批处理大小为0
        let result = EnhancedExporter::new()
            .with_batch_size(0)
            .build();
        assert!(result.is_err());

        // 空端点
        let result = EnhancedExporter::new()
            .with_endpoint("")
            .build();
        assert!(result.is_err());

        // 多租户但没有租户ID
        let result = EnhancedExporter::new()
            .with_multi_tenant(true)
            .build();
        assert!(result.is_err());
    }
}
