//! Collector 配置

use serde::{Serialize, Deserialize};
use std::time::Duration;

/// Collector 配置
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Config {
    /// 批量大小
    pub batch_size: usize,
    
    /// 批量超时 (毫秒)
    pub batch_timeout_ms: u64,
    
    /// 缓冲区容量
    pub buffer_capacity: usize,
    
    /// OTLP 端点
    pub endpoint: String,
    
    /// 重试次数
    pub max_retries: u32,
    
    /// 重试延迟 (毫秒)
    pub retry_delay_ms: u64,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            batch_size: 1000,
            batch_timeout_ms: 5000,
            buffer_capacity: 100_000,
            endpoint: "http://localhost:4317".to_string(),
            max_retries: 3,
            retry_delay_ms: 100,
        }
    }
}

impl Config {
    /// 批量超时
    pub fn batch_timeout(&self) -> Duration {
        Duration::from_millis(self.batch_timeout_ms)
    }
    
    /// 重试延迟
    pub fn retry_delay(&self) -> Duration {
        Duration::from_millis(self.retry_delay_ms)
    }
    
    /// 验证配置
    pub fn validate(&self) -> crate::Result<()> {
        if self.batch_size == 0 {
            return Err(crate::CollectorError::ConfigError(
                "batch_size 必须大于 0".to_string()
            ));
        }
        
        if self.buffer_capacity == 0 {
            return Err(crate::CollectorError::ConfigError(
                "buffer_capacity 必须大于 0".to_string()
            ));
        }
        
        if self.endpoint.is_empty() {
            return Err(crate::CollectorError::ConfigError(
                "endpoint 不能为空".to_string()
            ));
        }
        
        Ok(())
    }
}

