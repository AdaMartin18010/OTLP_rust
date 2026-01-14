//! 性能优化示例
//!
//! 演示如何使用性能优化模块

use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm, OptimizedMemoryPool, MemoryPoolConfig};
use std::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("性能优化示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 压缩示例
    println!("1. 压缩性能示例...");
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression ".repeat(100);

    println!("   - 原始数据大小: {} bytes", data.len());

    for algorithm in [CompressionAlgorithm::Gzip, CompressionAlgorithm::Brotli, CompressionAlgorithm::Zstd] {
        let start = Instant::now();
        match manager.compress(&data, algorithm) {
            Ok(compressed) => {
                let duration = start.elapsed();
                let ratio = compressed.len() as f64 / data.len() as f64 * 100.0;
                println!("   ✅ {:?}: {} bytes ({:.1}%), 耗时: {:?}",
                    algorithm, compressed.len(), ratio, duration);
            }
            Err(e) => {
                println!("   ❌ {:?}: 压缩失败: {}", algorithm, e);
            }
        }
    }
    println!();

    // 2. 内存池示例
    println!("2. 内存池示例...");
    let config = MemoryPoolConfig::default();
    let mut pool = OptimizedMemoryPool::new(config);

    println!("   - 初始统计: {:?}", pool.stats());

    // 分配一些内存块
    let mut blocks = Vec::new();
    for i in 0..5 {
        match pool.allocate(1024 * (i + 1)) {
            Ok(block) => {
                println!("   ✅ 分配内存块 {}: {} bytes", i, block.size());
                blocks.push(block);
            }
            Err(e) => {
                println!("   ❌ 分配失败: {}", e);
            }
        }
    }

    println!("   - 分配后统计: {:?}", pool.stats());

    // 释放内存块
    for (i, block) in blocks.into_iter().enumerate() {
        if pool.deallocate(block).is_ok() {
            println!("   ✅ 释放内存块 {}", i);
        }
    }

    println!("   - 释放后统计: {:?}", pool.stats());
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
