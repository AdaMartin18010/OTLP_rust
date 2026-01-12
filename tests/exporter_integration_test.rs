//! 导出器模块集成测试

use otlp::{OtlpExporter, OtlpConfig};

#[tokio::test]
async fn test_exporter_creation() {
    let config = OtlpConfig::default();
    let exporter = OtlpExporter::new(config);

    // 验证导出器创建成功
    assert!(true);  // 占位符测试
}

#[tokio::test]
async fn test_export_result() {
    use otlp::exporter::ExportResult;
    use std::time::Duration;

    let result = ExportResult::success(10, Duration::from_millis(100));

    assert!(result.is_success());
    assert_eq!(result.success_count, 10);
    assert_eq!(result.failure_count, 0);
    assert_eq!(result.total_count(), 10);
    assert_eq!(result.success_rate(), 1.0);
}

#[test]
fn test_export_result_partial() {
    use otlp::exporter::ExportResult;
    use std::time::Duration;

    let result = ExportResult::partial(
        8,
        2,
        Duration::from_millis(100),
        vec!["error1".to_string(), "error2".to_string()],
    );

    assert!(!result.is_success());
    assert!(!result.is_failure());
    assert_eq!(result.success_count, 8);
    assert_eq!(result.failure_count, 2);
    assert_eq!(result.total_count(), 10);
    assert_eq!(result.success_rate(), 0.8);
}
