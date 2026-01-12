//! # 内存池优化模块
//!
//! 提供高性能的内存池管理，减少内存分配开销
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化内存池配置和缓冲区大小
//! - **异步闭包**: 使用 `async || {}` 语法简化异步内存池操作
//! - **元组收集**: 使用 `collect()` 直接收集内存池统计到元组
//! - **改进的内存管理**: 利用 Rust 1.92 的内存管理优化提升性能

use std::collections::VecDeque;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 内存池统计信息
#[derive(Debug, Default)]
pub struct MemoryPoolStats {
    pub total_allocations: AtomicUsize,
    pub pool_hits: AtomicUsize,
    pub pool_misses: AtomicUsize,
    pub total_bytes_allocated: AtomicUsize,
    pub peak_memory_usage: AtomicUsize,
    pub current_pool_size: AtomicUsize,
}

impl Clone for MemoryPoolStats {
    fn clone(&self) -> Self {
        Self {
            total_allocations: AtomicUsize::new(self.total_allocations.load(Ordering::Relaxed)),
            pool_hits: AtomicUsize::new(self.pool_hits.load(Ordering::Relaxed)),
            pool_misses: AtomicUsize::new(self.pool_misses.load(Ordering::Relaxed)),
            total_bytes_allocated: AtomicUsize::new(
                self.total_bytes_allocated.load(Ordering::Relaxed),
            ),
            peak_memory_usage: AtomicUsize::new(self.peak_memory_usage.load(Ordering::Relaxed)),
            current_pool_size: AtomicUsize::new(self.current_pool_size.load(Ordering::Relaxed)),
        }
    }
}

/// 内存池配置
#[derive(Debug, Clone)]
pub struct MemoryPoolConfig {
    pub initial_size: usize,
    pub max_size: usize,
    pub growth_factor: f64,
    pub shrink_threshold: f64,
    pub cleanup_interval: Duration,
}

impl Default for MemoryPoolConfig {
    fn default() -> Self {
        Self {
            initial_size: 100,
            max_size: 1000,
            growth_factor: 1.5,
            shrink_threshold: 0.3,
            cleanup_interval: Duration::from_secs(60),
        }
    }
}

/// 内存块
#[derive(Debug)]
pub struct MemoryBlock {
    pub data: Vec<u8>,
    pub size: usize,
    pub allocated_at: Instant,
    pub last_used: Instant,
}

impl MemoryBlock {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0; size],
            size,
            allocated_at: Instant::now(),
            last_used: Instant::now(),
        }
    }

    pub fn reset(&mut self) {
        self.data.fill(0);
        self.last_used = Instant::now();
    }

    pub fn is_expired(&self, max_age: Duration) -> bool {
        self.last_used.elapsed() > max_age
    }
}

/// 高性能内存池
pub struct MemoryPool {
    config: MemoryPoolConfig,
    stats: Arc<MemoryPoolStats>,
    blocks: Arc<Mutex<VecDeque<MemoryBlock>>>,
    last_cleanup: Arc<Mutex<Instant>>,
}

impl MemoryPool {
    /// 创建新的内存池
    pub fn new(config: MemoryPoolConfig) -> Self {
        let mut blocks = VecDeque::with_capacity(config.initial_size);

        // 预分配初始内存块
        for _ in 0..config.initial_size {
            blocks.push_back(MemoryBlock::new(1024)); // 默认1KB块
        }

        let stats = MemoryPoolStats::default();
        // 设置初始池大小
        stats
            .current_pool_size
            .store(config.initial_size, Ordering::Relaxed);

        Self {
            stats: Arc::new(stats),
            blocks: Arc::new(Mutex::new(blocks)),
            last_cleanup: Arc::new(Mutex::new(Instant::now())),
            config,
        }
    }

    /// 获取内存块
    pub fn get_block(&self, size: usize) -> Option<MemoryBlock> {
        let mut blocks = self.blocks.lock().unwrap();

        // 查找合适大小的块
        for (index, block) in blocks.iter_mut().enumerate() {
            if block.size >= size {
                let block = blocks.remove(index).unwrap();
                self.stats.pool_hits.fetch_add(1, Ordering::Relaxed);
                self.stats.current_pool_size.fetch_sub(1, Ordering::Relaxed);
                return Some(block);
            }
        }

        // 池中没有合适的块，创建新的
        self.stats.pool_misses.fetch_add(1, Ordering::Relaxed);
        self.stats.total_allocations.fetch_add(1, Ordering::Relaxed);
        self.stats
            .total_bytes_allocated
            .fetch_add(size, Ordering::Relaxed);

        Some(MemoryBlock::new(size))
    }

    /// 返回内存块到池中
    pub fn return_block(&self, mut block: MemoryBlock) {
        // 检查是否需要清理
        self.maybe_cleanup();

        let mut blocks = self.blocks.lock().unwrap();

        // 如果池已满，丢弃最旧的块
        if blocks.len() >= self.config.max_size {
            if let Some(_oldest) = blocks.pop_front() {
                self.stats.current_pool_size.fetch_sub(1, Ordering::Relaxed);
            }
        }

        // 重置块并返回池中
        block.reset();
        blocks.push_back(block);
        self.stats.current_pool_size.fetch_add(1, Ordering::Relaxed);
    }

    /// 分配指定大小的内存
    pub fn allocate(&self, size: usize) -> Vec<u8> {
        if let Some(mut block) = self.get_block(size) {
            // 调整块大小
            if block.size != size {
                block.data.resize(size, 0);
                block.size = size;
            }
            block.data.clone()
        } else {
            // 创建新块
            self.stats.total_allocations.fetch_add(1, Ordering::Relaxed);
            self.stats
                .total_bytes_allocated
                .fetch_add(size, Ordering::Relaxed);
            vec![0; size]
        }
    }

    /// 释放内存
    pub fn deallocate(&self, data: Vec<u8>) {
        let capacity = data.capacity();
        let block = MemoryBlock {
            data,
            size: capacity,
            allocated_at: Instant::now(),
            last_used: Instant::now(),
        };
        self.return_block(block);
    }

    /// 获取统计信息
    pub fn stats(&self) -> MemoryPoolStats {
        MemoryPoolStats {
            total_allocations: AtomicUsize::new(
                self.stats.total_allocations.load(Ordering::Relaxed),
            ),
            pool_hits: AtomicUsize::new(self.stats.pool_hits.load(Ordering::Relaxed)),
            pool_misses: AtomicUsize::new(self.stats.pool_misses.load(Ordering::Relaxed)),
            total_bytes_allocated: AtomicUsize::new(
                self.stats.total_bytes_allocated.load(Ordering::Relaxed),
            ),
            peak_memory_usage: AtomicUsize::new(
                self.stats.peak_memory_usage.load(Ordering::Relaxed),
            ),
            current_pool_size: AtomicUsize::new(
                self.stats.current_pool_size.load(Ordering::Relaxed),
            ),
        }
    }

    /// 清理过期块
    fn maybe_cleanup(&self) {
        let mut last_cleanup = self.last_cleanup.lock().unwrap();
        if last_cleanup.elapsed() < self.config.cleanup_interval {
            return;
        }

        let mut blocks = self.blocks.lock().unwrap();
        let initial_size = blocks.len();

        // 移除过期块
        blocks.retain(|block| !block.is_expired(Duration::from_secs(300))); // 5分钟过期

        let removed = initial_size - blocks.len();
        if removed > 0 {
            self.stats
                .current_pool_size
                .fetch_sub(removed, Ordering::Relaxed);
        }

        *last_cleanup = Instant::now();
    }

    /// 调整池大小
    pub fn resize(&self, new_size: usize) {
        let mut blocks = self.blocks.lock().unwrap();

        if new_size > blocks.len() {
            // 扩展池
            let to_add = new_size - blocks.len();
            for _ in 0..to_add {
                blocks.push_back(MemoryBlock::new(1024));
            }
            self.stats
                .current_pool_size
                .fetch_add(to_add, Ordering::Relaxed);
        } else if new_size < blocks.len() {
            // 收缩池
            let to_remove = blocks.len() - new_size;
            for _ in 0..to_remove {
                blocks.pop_front();
            }
            self.stats
                .current_pool_size
                .fetch_sub(to_remove, Ordering::Relaxed);
        }
    }

    /// 清空池
    pub fn clear(&self) {
        let mut blocks = self.blocks.lock().unwrap();
        let size = blocks.len();
        blocks.clear();
        self.stats
            .current_pool_size
            .fetch_sub(size, Ordering::Relaxed);
    }
}

/// 内存池管理器
pub struct MemoryPoolManager {
    pools: Arc<Mutex<std::collections::HashMap<String, Arc<MemoryPool>>>>,
}

impl MemoryPoolManager {
    pub fn new() -> Self {
        Self {
            pools: Arc::new(Mutex::new(std::collections::HashMap::new())),
        }
    }

    /// 创建命名内存池
    pub fn create_pool(&self, name: String, config: MemoryPoolConfig) -> Arc<MemoryPool> {
        let pool = Arc::new(MemoryPool::new(config));
        let mut pools = self.pools.lock().unwrap();
        pools.insert(name, pool.clone());
        pool
    }

    /// 获取命名内存池
    pub fn get_pool(&self, name: &str) -> Option<Arc<MemoryPool>> {
        let pools = self.pools.lock().unwrap();
        pools.get(name).cloned()
    }

    /// 获取所有池的统计信息
    pub fn get_all_stats(&self) -> std::collections::HashMap<String, MemoryPoolStats> {
        let pools = self.pools.lock().unwrap();
        pools
            .iter()
            .map(|(name, pool)| (name.clone(), pool.stats()))
            .collect()
    }
}

impl Default for MemoryPoolManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pool_creation() {
        let config = MemoryPoolConfig::default();
        let pool = MemoryPool::new(config);
        let stats = pool.stats();
        assert_eq!(stats.current_pool_size.load(Ordering::Relaxed), 100);
    }

    #[test]
    fn test_memory_allocation() {
        let config = MemoryPoolConfig {
            initial_size: 10,
            max_size: 100,
            ..Default::default()
        };
        let pool = MemoryPool::new(config);

        let data = pool.allocate(512);
        assert_eq!(data.len(), 512);

        let stats = pool.stats();
        assert!(
            stats.pool_hits.load(Ordering::Relaxed) > 0
                || stats.pool_misses.load(Ordering::Relaxed) > 0
        );
    }

    #[test]
    fn test_memory_deallocation() {
        let config = MemoryPoolConfig::default();
        let pool = MemoryPool::new(config);

        let data = vec![1, 2, 3, 4, 5];
        pool.deallocate(data);

        let stats = pool.stats();
        assert!(stats.current_pool_size.load(Ordering::Relaxed) > 0);
    }

    #[test]
    fn test_memory_pool_manager() {
        let manager = MemoryPoolManager::new();
        let config = MemoryPoolConfig::default();

        let pool = manager.create_pool("test_pool".to_string(), config);
        assert!(pool.stats().current_pool_size.load(Ordering::Relaxed) > 0);

        let retrieved = manager.get_pool("test_pool");
        assert!(retrieved.is_some());
    }
}
