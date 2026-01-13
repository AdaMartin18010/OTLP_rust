//! 内存池单元测试

use otlp::performance::{OptimizedMemoryPool, MemoryPoolConfig};

#[test]
fn test_memory_pool_new() {
    let config = MemoryPoolConfig::default();
    let pool = OptimizedMemoryPool::new(config);
    
    assert_eq!(pool.stats().total_allocations, 0);
}

#[test]
fn test_memory_pool_allocate() {
    let config = MemoryPoolConfig::default();
    let mut pool = OptimizedMemoryPool::new(config);
    
    let size = 1024;
    let result = pool.allocate(size);
    assert!(result.is_ok());
    
    let block = result.unwrap();
    assert_eq!(block.size(), size);
}

#[test]
fn test_memory_pool_deallocate() {
    let config = MemoryPoolConfig::default();
    let mut pool = OptimizedMemoryPool::new(config);
    
    // 分配
    let block = pool.allocate(1024).unwrap();
    
    // 释放
    let result = pool.deallocate(block);
    assert!(result.is_ok());
}

#[test]
fn test_memory_pool_stats() {
    let config = MemoryPoolConfig::default();
    let mut pool = OptimizedMemoryPool::new(config);
    
    let stats = pool.stats();
    assert_eq!(stats.total_allocations, 0);
    assert_eq!(stats.active_allocations, 0);
    
    // 分配
    let _block1 = pool.allocate(1024).unwrap();
    let _block2 = pool.allocate(2048).unwrap();
    
    let stats = pool.stats();
    assert_eq!(stats.total_allocations, 2);
    assert_eq!(stats.active_allocations, 2);
}

#[test]
fn test_memory_pool_reuse() {
    let config = MemoryPoolConfig::default();
    let mut pool = OptimizedMemoryPool::new(config);
    
    // 分配并释放
    let block = pool.allocate(1024).unwrap();
    pool.deallocate(block).unwrap();
    
    // 再次分配相同大小，应该重用
    let block2 = pool.allocate(1024).unwrap();
    assert_eq!(block2.size(), 1024);
}

#[test]
fn test_memory_pool_config() {
    let config = MemoryPoolConfig {
        initial_size: 1024 * 1024,
        max_size: 10 * 1024 * 1024,
        block_size: 4096,
    };
    
    let pool = OptimizedMemoryPool::new(config.clone());
    assert_eq!(pool.config().initial_size, config.initial_size);
}
