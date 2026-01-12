//! 错误处理模块集成测试

use otlp::error::{OtlpError, ConfigurationError, Result};

#[test]
fn test_configuration_error() {
    let error = OtlpError::Configuration(
        ConfigurationError::InvalidEndpoint {
            url: "invalid".to_string(),
        }
    );

    assert!(error.to_string().contains("无效的端点"));
}

#[test]
fn test_error_conversion() {
    let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "file not found");
    let otlp_error: OtlpError = io_error.into();

    assert!(matches!(otlp_error, OtlpError::Io(_)));
}

#[test]
fn test_result_type() {
    fn may_fail() -> Result<()> {
        Err(OtlpError::ValidationError("test".to_string()))
    }

    assert!(may_fail().is_err());
}
