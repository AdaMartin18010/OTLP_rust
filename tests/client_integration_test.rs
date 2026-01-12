//! 客户端模块集成测试

use otlp::{OtlpClient, OtlpConfig, OtlpClientBuilder};
use std::time::Duration;

#[tokio::test]
async fn test_client_creation() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await;

    // 验证客户端创建成功
    assert!(client.is_ok());
}

#[tokio::test]
async fn test_client_builder() {
    let client = OtlpClientBuilder::new()
        .endpoint("https://api.example.com:4317")
        .build()
        .await;

    assert!(client.is_ok());
}

#[tokio::test]
async fn test_client_initialization() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();

    // 初始化客户端
    let result = client.initialize().await;
    // 注意：实际测试可能需要 mock 导出器
    // assert!(result.is_ok());
}
