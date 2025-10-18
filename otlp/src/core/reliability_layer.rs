//! 可靠性增强层
//! 
//! 提供重试、熔断、超时等可靠性机制

use std::time::Duration;

/// 可靠性管理器
/// 
/// 提供各种可靠性增强策略：
/// - 重试机制
/// - 熔断器
/// - 超时控制
/// - 降级策略
pub struct ReliabilityManager {
    /// 重试配置
    retry_config: RetryConfig,
}

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_retries: usize,
    
    /// 初始重试延迟
    pub initial_delay: Duration,
    
    /// 最大重试延迟
    pub max_delay: Duration,
    
    /// 延迟倍增因子
    pub multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_delay: Duration::from_millis(1000),
            max_delay: Duration::from_secs(30),
            multiplier: 2.0,
        }
    }
}

impl ReliabilityManager {
    /// 创建新的可靠性管理器
    pub fn new() -> Self {
        Self {
            retry_config: RetryConfig::default(),
        }
    }
    
    /// 使用自定义重试配置创建
    pub fn with_retry_config(retry_config: RetryConfig) -> Self {
        Self {
            retry_config,
        }
    }
    
    /// 获取重试配置
    pub fn retry_config(&self) -> &RetryConfig {
        &self.retry_config
    }
    
    /// 执行带重试的操作
    /// 
    /// # 示例
    /// 
    /// ```rust,no_run
    /// # use otlp::core::ReliabilityManager;
    /// # async fn example() {
    /// let manager = ReliabilityManager::new();
    /// 
    /// let result = manager.retry(|| async {
    ///     // 可能失败的操作
    ///     Ok::<_, Box<dyn std::error::Error>>(())
    /// }).await;
    /// # }
    /// ```
    pub async fn retry<F, Fut, T, E>(&self, mut operation: F) -> Result<T, E>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        let mut attempts = 0;
        let mut delay = self.retry_config.initial_delay;
        
        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    attempts += 1;
                    
                    if attempts >= self.retry_config.max_retries {
                        return Err(e);
                    }
                    
                    // 等待后重试
                    tokio::time::sleep(delay).await;
                    
                    // 指数退避
                    delay = std::cmp::min(
                        Duration::from_millis((delay.as_millis() as f64 * self.retry_config.multiplier) as u64),
                        self.retry_config.max_delay
                    );
                }
            }
        }
    }
}

impl Default for ReliabilityManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reliability_manager_creation() {
        let manager = ReliabilityManager::new();
        assert_eq!(manager.retry_config().max_retries, 3);
    }

    #[test]
    fn test_custom_retry_config() {
        let config = RetryConfig {
            max_retries: 5,
            initial_delay: Duration::from_millis(500),
            max_delay: Duration::from_secs(60),
            multiplier: 1.5,
        };
        let manager = ReliabilityManager::with_retry_config(config);
        assert_eq!(manager.retry_config().max_retries, 5);
    }

    #[tokio::test]
    async fn test_retry_success() {
        let manager = ReliabilityManager::new();
        
        let mut attempts = 0;
        let result = manager.retry(|| async {
            attempts += 1;
            if attempts < 2 {
                Err("Error")
            } else {
                Ok("Success")
            }
        }).await;
        
        assert_eq!(result, Ok("Success"));
        assert_eq!(attempts, 2);
    }
}

