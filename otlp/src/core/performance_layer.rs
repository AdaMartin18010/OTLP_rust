//! 性能优化层
//! 
//! 提供对象池、批处理、压缩等性能优化功能

use std::sync::Arc;

/// 性能优化管理器
/// 
/// 提供各种性能优化策略：
/// - 对象池
/// - 批处理
/// - 压缩
/// - 零拷贝
pub struct PerformanceOptimizer {
    /// 批处理配置
    batch_config: BatchConfig,
}

/// 批处理配置
#[derive(Debug, Clone)]
pub struct BatchConfig {
    /// 批处理大小
    pub batch_size: usize,
    
    /// 批处理超时
    pub batch_timeout_ms: u64,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            batch_size: 512,
            batch_timeout_ms: 5000,
        }
    }
}

impl PerformanceOptimizer {
    /// 创建新的性能优化器
    pub fn new() -> Self {
        Self {
            batch_config: BatchConfig::default(),
        }
    }
    
    /// 使用自定义批处理配置创建
    pub fn with_batch_config(batch_config: BatchConfig) -> Self {
        Self {
            batch_config,
        }
    }
    
    /// 获取批处理配置
    pub fn batch_config(&self) -> &BatchConfig {
        &self.batch_config
    }
}

impl Default for PerformanceOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_optimizer_creation() {
        let optimizer = PerformanceOptimizer::new();
        assert_eq!(optimizer.batch_config().batch_size, 512);
    }

    #[test]
    fn test_custom_batch_config() {
        let config = BatchConfig {
            batch_size: 1024,
            batch_timeout_ms: 10000,
        };
        let optimizer = PerformanceOptimizer::with_batch_config(config);
        assert_eq!(optimizer.batch_config().batch_size, 1024);
    }
}

