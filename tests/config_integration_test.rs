//! 配置模块集成测试

use otlp::config::{OtlpConfig, TransportProtocol};
use std::time::Duration;

#[test]
fn test_config_default() {
    let config = OtlpConfig::default();
    assert!(!config.endpoint.is_empty());
}

#[test]
fn test_config_validation() {
    let mut config = OtlpConfig::default();
    config.batch_config.max_export_batch_size = 50000;  // 超出限制
    let result = config.validate();

    // 验证应该失败或调整到合理值
    assert!(result.is_err() || config.batch_config.max_export_batch_size <= 10000);
}

#[test]
fn test_transport_protocol() {
    let mut config = OtlpConfig::default();
    config.protocol = TransportProtocol::Grpc;

    assert_eq!(config.protocol, TransportProtocol::Grpc);
}

#[test]
fn test_compression() {
    let mut config = OtlpConfig::default();
    config.compression = otlp::config::Compression::Gzip;

    // 检查压缩是否启用
    assert!(matches!(config.compression, otlp::config::Compression::Gzip |
                                          otlp::config::Compression::Brotli |
                                          otlp::config::Compression::Zstd));
}
