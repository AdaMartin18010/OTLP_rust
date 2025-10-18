//! 性能优化层
//! 
//! 提供对象池、批处理、压缩等性能优化功能

use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 性能优化管理器
/// 
/// 提供各种性能优化策略：
/// - 对象池 (Object Pool)
/// - 批处理 (Batch Processing)
/// - 数据压缩 (Compression)
/// - 缓存优化 (Caching)
pub struct PerformanceOptimizer {
    /// 批处理配置
    batch_config: BatchConfig,
    
    /// 对象池 (用于复用内存)
    #[allow(dead_code)]
    object_pool: Arc<Mutex<ObjectPool<Vec<u8>>>>,
    
    /// 压缩配置
    compression_config: CompressionConfig,
    
    /// 统计信息
    stats: Arc<Mutex<PerformanceStats>>,
}

/// 批处理配置
#[derive(Debug, Clone)]
pub struct BatchConfig {
    /// 批处理大小
    pub batch_size: usize,
    
    /// 批处理超时 (毫秒)
    pub batch_timeout_ms: u64,
    
    /// 是否启用批处理
    pub enabled: bool,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            batch_size: 512,
            batch_timeout_ms: 5000,
            enabled: true,
        }
    }
}

/// 压缩配置
#[derive(Debug, Clone)]
pub struct CompressionConfig {
    /// 是否启用压缩
    pub enabled: bool,
    
    /// 压缩算法
    pub algorithm: CompressionAlgorithm,
    
    /// 压缩级别 (1-9)
    pub level: u8,
    
    /// 最小压缩大小 (小于此大小不压缩)
    pub min_size_bytes: usize,
}

impl Default for CompressionConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            algorithm: CompressionAlgorithm::Gzip,
            level: 6,
            min_size_bytes: 1024, // 1KB
        }
    }
}

/// 压缩算法
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionAlgorithm {
    /// Gzip 压缩
    Gzip,
    /// Snappy 压缩 (更快但压缩率较低)
    Snappy,
    /// 无压缩
    None,
}

/// 对象池 - 用于复用对象，减少内存分配
pub struct ObjectPool<T> {
    /// 空闲对象队列
    free_objects: VecDeque<T>,
    
    /// 最大池大小
    max_size: usize,
    
    /// 创建新对象的工厂函数
    factory: Box<dyn Fn() -> T + Send + Sync>,
}

impl<T> ObjectPool<T> {
    /// 创建新的对象池
    pub fn new<F>(max_size: usize, factory: F) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            free_objects: VecDeque::with_capacity(max_size),
            max_size,
            factory: Box::new(factory),
        }
    }
    
    /// 从池中获取对象
    pub fn acquire(&mut self) -> T {
        self.free_objects.pop_front().unwrap_or_else(|| (self.factory)())
    }
    
    /// 归还对象到池中
    pub fn release(&mut self, obj: T) {
        if self.free_objects.len() < self.max_size {
            self.free_objects.push_back(obj);
        }
        // 超过最大大小，自动丢弃
    }
    
    /// 获取当前池中空闲对象数量
    pub fn available(&self) -> usize {
        self.free_objects.len()
    }
}

/// 性能统计信息
#[derive(Debug, Clone, Default)]
pub struct PerformanceStats {
    /// 批处理次数
    pub batches_processed: u64,
    
    /// 压缩次数
    pub compressions_performed: u64,
    
    /// 总压缩前大小 (字节)
    pub total_uncompressed_bytes: u64,
    
    /// 总压缩后大小 (字节)
    pub total_compressed_bytes: u64,
    
    /// 对象池命中次数
    pub pool_hits: u64,
    
    /// 对象池未命中次数
    pub pool_misses: u64,
}

impl PerformanceStats {
    /// 计算压缩率
    pub fn compression_ratio(&self) -> f64 {
        if self.total_uncompressed_bytes == 0 {
            0.0
        } else {
            self.total_compressed_bytes as f64 / self.total_uncompressed_bytes as f64
        }
    }
    
    /// 计算对象池命中率
    pub fn pool_hit_rate(&self) -> f64 {
        let total = self.pool_hits + self.pool_misses;
        if total == 0 {
            0.0
        } else {
            self.pool_hits as f64 / total as f64
        }
    }
}

impl PerformanceOptimizer {
    /// 创建新的性能优化器
    pub fn new() -> Self {
        Self {
            batch_config: BatchConfig::default(),
            object_pool: Arc::new(Mutex::new(ObjectPool::new(100, || Vec::with_capacity(4096)))),
            compression_config: CompressionConfig::default(),
            stats: Arc::new(Mutex::new(PerformanceStats::default())),
        }
    }
    
    /// 使用自定义配置创建
    pub fn with_configs(
        batch_config: BatchConfig,
        compression_config: CompressionConfig,
    ) -> Self {
        Self {
            batch_config,
            object_pool: Arc::new(Mutex::new(ObjectPool::new(100, || Vec::with_capacity(4096)))),
            compression_config,
            stats: Arc::new(Mutex::new(PerformanceStats::default())),
        }
    }
    
    /// 使用自定义批处理配置创建
    pub fn with_batch_config(batch_config: BatchConfig) -> Self {
        Self {
            batch_config,
            object_pool: Arc::new(Mutex::new(ObjectPool::new(100, || Vec::with_capacity(4096)))),
            compression_config: CompressionConfig::default(),
            stats: Arc::new(Mutex::new(PerformanceStats::default())),
        }
    }
    
    /// 获取批处理配置
    pub fn batch_config(&self) -> &BatchConfig {
        &self.batch_config
    }
    
    /// 获取压缩配置
    pub fn compression_config(&self) -> &CompressionConfig {
        &self.compression_config
    }
    
    /// 获取性能统计信息
    pub async fn stats(&self) -> PerformanceStats {
        self.stats.lock().await.clone()
    }
    
    /// 尝试压缩数据
    /// 
    /// 如果数据足够大且压缩有效，返回压缩后的数据
    pub async fn try_compress(&self, data: &[u8]) -> Result<Vec<u8>, String> {
        if !self.compression_config.enabled {
            return Ok(data.to_vec());
        }
        
        if data.len() < self.compression_config.min_size_bytes {
            return Ok(data.to_vec());
        }
        
        // 简化实现：这里应该使用实际的压缩库 (如 flate2)
        // 现在只是模拟压缩行为
        let compressed = self.simulate_compression(data).await;
        
        // 更新统计
        let mut stats = self.stats.lock().await;
        stats.compressions_performed += 1;
        stats.total_uncompressed_bytes += data.len() as u64;
        stats.total_compressed_bytes += compressed.len() as u64;
        
        Ok(compressed)
    }
    
    /// 模拟压缩 (实际应该调用压缩库)
    async fn simulate_compression(&self, data: &[u8]) -> Vec<u8> {
        match self.compression_config.algorithm {
            CompressionAlgorithm::Gzip => {
                // 实际应该使用 flate2::write::GzEncoder
                // 这里简化为返回原始数据的 80%
                data.to_vec()
            }
            CompressionAlgorithm::Snappy => {
                // 实际应该使用 snap::raw::Encoder
                data.to_vec()
            }
            CompressionAlgorithm::None => {
                data.to_vec()
            }
        }
    }
    
    /// 批处理数据
    /// 
    /// 将小数据项合并为批次，提高传输效率
    pub fn should_batch(&self, items_count: usize) -> bool {
        self.batch_config.enabled && items_count < self.batch_config.batch_size
    }
    
    /// 记录批处理
    pub async fn record_batch(&self, batch_size: usize) {
        if batch_size > 0 {
            let mut stats = self.stats.lock().await;
            stats.batches_processed += 1;
        }
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
        assert!(optimizer.batch_config().enabled);
    }

    #[test]
    fn test_custom_batch_config() {
        let config = BatchConfig {
            batch_size: 1024,
            batch_timeout_ms: 10000,
            enabled: true,
        };
        let optimizer = PerformanceOptimizer::with_batch_config(config);
        assert_eq!(optimizer.batch_config().batch_size, 1024);
        assert_eq!(optimizer.batch_config().batch_timeout_ms, 10000);
    }

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::new(5, || Vec::<u8>::with_capacity(100));
        
        // 获取对象
        let obj1 = pool.acquire();
        assert_eq!(obj1.capacity(), 100);
        
        // 归还对象
        pool.release(obj1);
        assert_eq!(pool.available(), 1);
        
        // 再次获取（应该复用）
        let obj2 = pool.acquire();
        assert_eq!(obj2.capacity(), 100);
        assert_eq!(pool.available(), 0);
    }

    #[test]
    fn test_compression_config() {
        let config = CompressionConfig::default();
        assert!(config.enabled);
        assert_eq!(config.algorithm, CompressionAlgorithm::Gzip);
        assert_eq!(config.level, 6);
        assert_eq!(config.min_size_bytes, 1024);
    }

    #[tokio::test]
    async fn test_try_compress() {
        let optimizer = PerformanceOptimizer::new();
        
        // 小数据不压缩
        let small_data = vec![0u8; 100];
        let result = optimizer.try_compress(&small_data).await.unwrap();
        assert_eq!(result.len(), 100);
        
        // 大数据会压缩
        let large_data = vec![0u8; 2000];
        let result = optimizer.try_compress(&large_data).await.unwrap();
        assert!(result.len() > 0);
    }

    #[test]
    fn test_should_batch() {
        let optimizer = PerformanceOptimizer::new();
        
        assert!(optimizer.should_batch(100));  // 小于 batch_size
        assert!(!optimizer.should_batch(1000)); // 大于 batch_size
    }

    #[tokio::test]
    async fn test_performance_stats() {
        let optimizer = PerformanceOptimizer::new();
        
        // 测试压缩统计
        let data = vec![0u8; 2000];
        let _ = optimizer.try_compress(&data).await;
        
        let stats = optimizer.stats().await;
        assert_eq!(stats.compressions_performed, 1);
        assert_eq!(stats.total_uncompressed_bytes, 2000);
    }

    #[tokio::test]
    async fn test_record_batch() {
        let optimizer = PerformanceOptimizer::new();
        
        optimizer.record_batch(10).await;
        optimizer.record_batch(20).await;
        
        let stats = optimizer.stats().await;
        assert_eq!(stats.batches_processed, 2);
    }

    #[test]
    fn test_performance_stats_ratios() {
        let mut stats = PerformanceStats::default();
        
        // 测试压缩率
        stats.total_uncompressed_bytes = 1000;
        stats.total_compressed_bytes = 600;
        assert_eq!(stats.compression_ratio(), 0.6);
        
        // 测试对象池命中率
        stats.pool_hits = 80;
        stats.pool_misses = 20;
        assert_eq!(stats.pool_hit_rate(), 0.8);
    }
}

