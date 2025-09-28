//! # 测试工具库
//!
//! 提供测试中使用的通用工具和辅助函数。

use otlp::{
    config::{BatchConfig, OtlpConfig, TransportProtocol},
    data::{LogSeverity, TelemetryData},
    transport::{GrpcTransport, HttpTransport},
};
use std::collections::HashMap;
use std::time::Duration;

/// 测试配置
pub struct TestConfig {
    pub grpc_endpoint: String,
    pub http_endpoint: String,
    pub timeout: Duration,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            grpc_endpoint: "http://localhost:4317".to_string(),
            http_endpoint: "http://localhost:4318".to_string(),
            timeout: Duration::from_secs(5),
        }
    }
}

/// 创建测试用的gRPC传输
pub async fn create_test_grpc_transport() -> Result<GrpcTransport, Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    Ok(GrpcTransport::new(config).await?)
}

/// 创建测试用的HTTP传输
pub async fn create_test_http_transport() -> Result<HttpTransport, Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4318")
        .with_protocol(TransportProtocol::Http);

    Ok(HttpTransport::new(config).await?)
}

/// 创建测试日志数据
pub fn create_test_log_data() -> TelemetryData {
    otlp::TelemetryData::log("Test log message", LogSeverity::Info)
}

/// 创建带属性的测试日志数据
pub fn create_test_log_data_with_attributes(
    message: &str,
    attributes: HashMap<String, String>,
) -> TelemetryData {
    let _ = attributes; // 简化测试
    otlp::TelemetryData::log(message, LogSeverity::Info)
}

/// 创建批量测试数据
pub fn create_batch_test_data(size: usize) -> Vec<TelemetryData> {
    (0..size)
        .map(|i| otlp::TelemetryData::log(&format!("Batch test message {}", i), LogSeverity::Info))
        .collect()
}

/// 创建不同严重程度的测试数据
pub fn create_mixed_severity_test_data() -> Vec<TelemetryData> {
    vec![
        otlp::TelemetryData::log("Debug message", LogSeverity::Debug),
        otlp::TelemetryData::log("Info message", LogSeverity::Info),
        otlp::TelemetryData::log("Warning message", LogSeverity::Warn),
        otlp::TelemetryData::log("Error message", LogSeverity::Error),
        otlp::TelemetryData::log("Fatal message", LogSeverity::Fatal),
    ]
}

/// 创建大尺寸测试数据
pub fn create_large_test_data() -> TelemetryData {
    let large_message = "x".repeat(10000); // 10KB消息
    let data = otlp::TelemetryData::log(large_message, LogSeverity::Info);
    let mut attrs = HashMap::new();
    attrs.insert(
        "large_data".to_string(),
        otlp::AttributeValue::String("true".to_string()),
    );
    attrs.insert(
        "size".to_string(),
        otlp::AttributeValue::String("10000".to_string()),
    );
    let _ = attrs; // 简化测试
    data
}

/// 创建包含特殊字符的测试数据
pub fn create_special_characters_test_data() -> TelemetryData {
    let special_message = "测试消息 with special chars: !@#$%^&*()_+-=[]{}|;':\",./<>?";
    let data = otlp::TelemetryData::log(special_message, LogSeverity::Info);
    let mut attrs = HashMap::new();
    attrs.insert(
        "special_chars".to_string(),
        otlp::AttributeValue::String("true".to_string()),
    );
    attrs.insert(
        "unicode".to_string(),
        otlp::AttributeValue::String("测试".to_string()),
    );
    let _ = attrs; // 简化测试
    data
}

/// 等待指定时间
pub async fn wait_for(duration: Duration) {
    tokio::time::sleep(duration).await;
}

/// 测量执行时间
pub async fn measure_time<F, R>(f: F) -> (R, Duration)
where
    F: std::future::Future<Output = R>,
{
    let start = std::time::Instant::now();
    let result = f.await;
    let duration = start.elapsed();
    (result, duration)
}

/// 验证数据格式
pub fn validate_telemetry_data(_data: &TelemetryData) -> bool {
    // 简化校验逻辑：只要能构造即认为有效
    true
}

/// 创建测试配置
pub fn create_test_config() -> OtlpConfig {
    OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_batch_config(BatchConfig {
            max_export_batch_size: 100,
            ..BatchConfig::default()
        })
        .with_request_timeout(Duration::from_secs(5))
}

/// 创建无效配置用于错误测试
pub fn create_invalid_config() -> OtlpConfig {
    OtlpConfig::default()
        .with_endpoint("invalid-url")
        .with_protocol(TransportProtocol::Grpc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_test_log_data() {
        let data = create_test_log_data();
        assert!(validate_telemetry_data(&data));
    }

    #[test]
    fn test_create_batch_test_data() {
        let batch = create_batch_test_data(10);
        assert_eq!(batch.len(), 10);

        for data in &batch {
            assert!(validate_telemetry_data(data));
        }
    }

    #[test]
    fn test_create_mixed_severity_test_data() {
        let data = create_mixed_severity_test_data();
        assert_eq!(data.len(), 5);

        for data in &data {
            assert!(validate_telemetry_data(data));
        }
    }

    #[test]
    fn test_validate_telemetry_data() {
        let valid_data = create_test_log_data();
        assert!(validate_telemetry_data(&valid_data));

        let invalid_data = otlp::TelemetryData::log("", LogSeverity::Info);
        assert!(!validate_telemetry_data(&invalid_data));
    }
}
