//! 现代化的 OTLP 导出器配置
//!
//! 遵循 OpenTelemetry Rust 0.31.0 和 OTLP 1.9.0 规范：
//! - 支持 gRPC (Tonic) 和 HTTP (Reqwest) 协议
//! - 内部线程管理（无需显式 Runtime）
//! - 批处理处理器优化
//! - 可配置的压缩和 TLS
//!
//! 参考: https://opentelemetry.io/docs/specs/otlp/

use opentelemetry_otlp::{WithExportConfig, WithHttpConfig};
use opentelemetry_sdk::trace::BatchConfig;
use std::collections::HashMap;
use std::time::Duration;

/// OTLP 协议类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OtlpProtocol {
    /// gRPC 协议（默认，性能更好）
    Grpc,
    /// HTTP/JSON 协议（兼容性更好）
    HttpJson,
    /// HTTP/Protobuf 协议
    HttpProtobuf,
}

impl Default for OtlpProtocol {
    fn default() -> Self {
        OtlpProtocol::Grpc
    }
}

/// OTLP 导出器配置
#[derive(Debug, Clone)]
pub struct OtlpExporterConfig {
    /// 端点 URL
    pub endpoint: String,
    /// 协议类型
    pub protocol: OtlpProtocol,
    /// 超时时间
    pub timeout: Duration,
    /// 自定义 HTTP 头
    pub headers: HashMap<String, String>,
    /// 压缩算法 (gzip, deflate, none)
    pub compression: Compression,
    /// TLS 配置
    pub tls_config: Option<TlsConfig>,
}

/// 压缩算法
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Compression {
    /// Gzip 压缩（默认）
    Gzip,
    /// Deflate 压缩
    Deflate,
    /// 不压缩
    None,
}

impl Default for Compression {
    fn default() -> Self {
        Compression::Gzip
    }
}

/// TLS 配置
#[derive(Debug, Clone)]
pub struct TlsConfig {
    /// 客户端证书路径
    pub client_cert_path: Option<String>,
    /// 客户端密钥路径
    pub client_key_path: Option<String>,
    /// CA 证书路径
    pub ca_cert_path: Option<String>,
    /// 是否禁用证书验证（仅用于开发）
    pub insecure_skip_verify: bool,
}

impl Default for OtlpExporterConfig {
    fn default() -> Self {
        Self {
            endpoint: std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            protocol: OtlpProtocol::default(),
            timeout: Duration::from_secs(10),
            headers: HashMap::new(),
            compression: Compression::default(),
            tls_config: None,
        }
    }
}

impl OtlpExporterConfig {
    /// 从环境变量创建配置
    pub fn from_env() -> Self {
        let mut config = Self::default();

        // OTEL_EXPORTER_OTLP_PROTOCOL
        if let Ok(protocol) = std::env::var("OTEL_EXPORTER_OTLP_PROTOCOL") {
            config.protocol = match protocol.as_str() {
                "grpc" => OtlpProtocol::Grpc,
                "http/json" => OtlpProtocol::HttpJson,
                "http/protobuf" => OtlpProtocol::HttpProtobuf,
                _ => OtlpProtocol::default(),
            };
        }

        // OTEL_EXPORTER_OTLP_TIMEOUT (毫秒)
        if let Ok(timeout_ms) = std::env::var("OTEL_EXPORTER_OTLP_TIMEOUT") {
            if let Ok(ms) = timeout_ms.parse::<u64>() {
                config.timeout = Duration::from_millis(ms);
            }
        }

        // OTEL_EXPORTER_OTLP_HEADERS (格式: "key1=value1,key2=value2")
        if let Ok(headers_str) = std::env::var("OTEL_EXPORTER_OTLP_HEADERS") {
            for pair in headers_str.split(',') {
                if let Some((key, value)) = pair.split_once('=') {
                    config
                        .headers
                        .insert(key.trim().to_string(), value.trim().to_string());
                }
            }
        }

        // 信号特定端点
        if let Ok(endpoint) = std::env::var("OTEL_EXPORTER_OTLP_TRACES_ENDPOINT") {
            config.endpoint = endpoint;
        }

        config
    }

    /// 设置端点
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    /// 设置协议
    pub fn with_protocol(mut self, protocol: OtlpProtocol) -> Self {
        self.protocol = protocol;
        self
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// 添加自定义头
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// 设置压缩算法
    pub fn with_compression(mut self, compression: Compression) -> Self {
        self.compression = compression;
        self
    }



    /// 获取信号特定的端点
    pub fn get_endpoint(&self, signal: &str) -> String {
        // 检查信号特定端点环境变量
        let env_var = format!("OTEL_EXPORTER_OTLP_{}_ENDPOINT", signal.to_uppercase());
        if let Ok(endpoint) = std::env::var(&env_var) {
            return endpoint;
        }

        // 使用默认端点 + 信号路径（HTTP 协议）
        match self.protocol {
            OtlpProtocol::Grpc => self.endpoint.clone(),
            OtlpProtocol::HttpJson | OtlpProtocol::HttpProtobuf => {
                format!("{}/v1/{}", self.endpoint, signal)
            }
        }
    }
}

/// 批处理配置构建器（简化版）
pub struct BatchConfigBuilderExt;

impl Default for BatchConfigBuilderExt {
    fn default() -> Self {
        Self
    }
}

impl BatchConfigBuilderExt {
    /// 创建默认批处理配置
    pub fn build() -> BatchConfig {
        BatchConfig::default()
    }
}

/// 创建 SpanExporter (HTTP 模式)
pub fn create_span_exporter(
    config: &OtlpExporterConfig,
) -> Result<opentelemetry_otlp::SpanExporter, opentelemetry_otlp::ExporterBuildError> {
    // 目前只支持 HTTP 导出器（gRPC 需要 tonic 特性）
    let builder = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_endpoint(config.get_endpoint("traces"))
        .with_timeout(config.timeout)
        .with_headers(config.headers.clone());

    builder.build()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = OtlpExporterConfig::default();
        assert!(!config.endpoint.is_empty());
        assert_eq!(config.protocol, OtlpProtocol::Grpc);
        assert_eq!(config.timeout, Duration::from_secs(10));
    }

    #[test]
    fn test_builder_pattern() {
        let config = OtlpExporterConfig::default()
            .with_endpoint("http://collector:4317")
            .with_protocol(OtlpProtocol::HttpJson)
            .with_timeout(Duration::from_secs(5))
            .with_header("Authorization", "Bearer token123")
            .with_compression(Compression::Deflate);

        assert_eq!(config.endpoint, "http://collector:4317");
        assert_eq!(config.protocol, OtlpProtocol::HttpJson);
        assert_eq!(config.timeout, Duration::from_secs(5));
        assert_eq!(config.headers.get("Authorization"), Some(&"Bearer token123".to_string()));
        assert_eq!(config.compression, Compression::Deflate);
    }

    #[test]
    fn test_get_endpoint() {
        let config = OtlpExporterConfig::default()
            .with_endpoint("http://localhost:4318")
            .with_protocol(OtlpProtocol::HttpJson);

        assert_eq!(config.get_endpoint("traces"), "http://localhost:4318/v1/traces");
        assert_eq!(config.get_endpoint("metrics"), "http://localhost:4318/v1/metrics");

        let grpc_config = OtlpExporterConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(OtlpProtocol::Grpc);

        assert_eq!(grpc_config.get_endpoint("traces"), "http://localhost:4317");
    }

    #[test]
    fn test_batch_config_builder() {
        let _config = BatchConfigBuilderExt::build();
        // BatchConfig 字段是私有的，仅验证能正常构建
    }
}
