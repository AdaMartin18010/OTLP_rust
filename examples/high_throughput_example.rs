//! 高吞吐量场景示例
//!
//! 演示如何在高吞吐量场景下使用 OTLP

use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm, OptimizedMemoryPool, MemoryPoolConfig};
use otlp::profiling::{CpuProfiler, ProfilerConfig};
use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::sync::Semaphore;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("高吞吐量场景示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 批量压缩
    println!("1. 批量压缩测试...");
    let manager = QuickOptimizationsManager::default();
    let data = b"test data ".repeat(1000);

    let start = Instant::now();
    let mut compressed_count = 0;
    for _ in 0..1000 {
        if manager.compress(&data, CompressionAlgorithm::Gzip).is_ok() {
            compressed_count += 1;
        }
    }
    let duration = start.elapsed();
    println!("   ✅ 压缩 {} 次，耗时: {:?}", compressed_count, duration);
    println!("   - 吞吐量: {:.0} ops/s", compressed_count as f64 / duration.as_secs_f64());
    println!();

    // 2. 并发内存池操作
    println!("2. 并发内存池操作...");
    let pool = Arc::new(OptimizedMemoryPool::new(MemoryPoolConfig::default()));
    let semaphore = Arc::new(Semaphore::new(10)); // 限制并发数

    let start = Instant::now();
    let mut handles = Vec::new();

    for i in 0..100 {
        let pool_clone = pool.clone();
        let permit = semaphore.clone().acquire_owned().await?;

        let handle = tokio::spawn(async move {
            let _permit = permit;
            let _block = pool_clone.allocate(1024 * (i % 10 + 1));
            // 模拟一些处理
            tokio::time::sleep(Duration::from_millis(1)).await;
        });

        handles.push(handle);
    }

    for handle in handles {
        let _ = handle.await;
    }

    let duration = start.elapsed();
    println!("   ✅ 100 个并发操作完成，耗时: {:?}", duration);
    println!("   - 吞吐量: {:.0} ops/s", 100.0 / duration.as_secs_f64());
    println!();

    // 3. 高频率性能分析
    println!("3. 高频率性能分析...");
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    profiler.start().await?;

    let start = Instant::now();
    let mut iterations = 0;
    while start.elapsed() < Duration::from_secs(1) {
        // 模拟高负载
        let _ = (0..1000).sum::<i32>();
        iterations += 1;
    }

    let profile = profiler.stop().await?;
    let duration = start.elapsed();

    println!("   ✅ 性能分析完成");
    println!("   - 迭代次数: {}", iterations);
    println!("   - 样本数: {}", profile.samples.len());
    println!("   - 耗时: {:?}", duration);
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
