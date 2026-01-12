//! 测试公共模块
//!
//! 提供测试中使用的共享代码和工具函数

use std::time::Duration;

/// 测试配置
pub struct TestConfig {
    pub timeout: Duration,
    pub retry_count: u32,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(5),
            retry_count: 3,
        }
    }
}

/// 创建测试配置
pub fn create_test_config() -> TestConfig {
    TestConfig::default()
}

/// 等待一小段时间（用于异步测试）
pub async fn small_delay() {
    tokio::time::sleep(Duration::from_millis(10)).await;
}

/// 等待中等时间（用于异步测试）
pub async fn medium_delay() {
    tokio::time::sleep(Duration::from_millis(100)).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_test_config_default() {
        let config = TestConfig::default();
        assert_eq!(config.timeout.as_secs(), 5);
        assert_eq!(config.retry_count, 3);
    }

    #[tokio::test]
    async fn test_delays() {
        let start = std::time::Instant::now();
        small_delay().await;
        let elapsed = start.elapsed();
        assert!(elapsed.as_millis() >= 10);
    }
}
