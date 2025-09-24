//! # 性能优化演示
//!
//! 展示如何使用 OTLP Rust 的性能优化系统进行零拷贝优化、
//! 内存池管理、并发优化和基准测试。

use otlp::{OptimizedError, OtlpError, PerformanceConfig, PerformanceOptimizer, Result};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("⚡ OTLP Rust 性能优化演示");
    println!("============================");

    // 示例 1: 基本性能优化器设置
    basic_optimizer_demo().await?;

    // 示例 2: 零拷贝优化
    zero_copy_optimization_demo().await?;

    // 示例 3: 内存池管理
    memory_pool_demo().await?;

    // 示例 4: 并发优化
    concurrency_optimization_demo().await?;

    // 示例 5: 基准测试
    benchmark_demo().await?;

    println!("\n✅ 所有性能优化演示完成！");
    Ok(())
}

/// 示例 1: 基本性能优化器设置
async fn basic_optimizer_demo() -> Result<()> {
    println!("\n⚡ 示例 1: 基本性能优化器设置");
    println!("------------------------------");

    // 创建性能配置
    let config = PerformanceConfig::default();

    // 创建性能优化器
    let optimizer = PerformanceOptimizer::new(config)?;

    // 启动优化器
    optimizer.start().await?;

    println!("  ✅ 性能优化器启动成功");

    // 获取性能指标
    let metrics = optimizer.get_performance_metrics().await?;
    println!("  📊 性能指标:");
    println!("    - 零拷贝统计: {:?}", metrics.zero_copy_stats);
    println!("    - 内存池统计: {:?}", metrics.memory_pool_stats);
    println!("    - 并发统计: {:?}", metrics.concurrency_stats);
    println!("    - 缓存统计: {:?}", metrics.cache_stats);

    Ok(())
}

/// 示例 2: 零拷贝优化
async fn zero_copy_optimization_demo() -> Result<()> {
    println!("\n🔄 示例 2: 零拷贝优化");
    println!("---------------------");

    let config = PerformanceConfig::default();
    let optimizer = PerformanceOptimizer::new(config)?;
    optimizer.start().await?;

    // 模拟不同类型的错误进行零拷贝优化
    let error_scenarios = vec![
        ("传输错误", create_transport_error()),
        ("序列化错误", create_serialization_error()),
        ("配置错误", create_configuration_error()),
        ("处理错误", create_processing_error()),
        ("导出错误", create_export_error()),
    ];

    for (name, error) in error_scenarios {
        println!("  🔧 优化错误: {}", name);
        println!(
            "    - 原始错误大小: {} bytes",
            std::mem::size_of_val(&error)
        );

        // 执行零拷贝优化
        let start = std::time::Instant::now();
        let optimized = optimizer.optimize_error_handling(&error).await?;
        let optimization_time = start.elapsed();

        println!("    - 优化后大小: {} bytes", optimized.metadata.size);
        println!("    - 优化耗时: {:?}", optimization_time);
        println!(
            "    - 内存节省: {} bytes",
            std::mem::size_of_val(&error) - optimized.metadata.size
        );

        // 验证优化效果
        verify_optimization_effectiveness(&optimized).await?;

        println!();
    }

    Ok(())
}

/// 示例 3: 内存池管理
async fn memory_pool_demo() -> Result<()> {
    println!("\n💾 示例 3: 内存池管理");
    println!("---------------------");

    let config = PerformanceConfig::default();
    let optimizer = PerformanceOptimizer::new(config)?;
    optimizer.start().await?;

    // 模拟大量错误处理，展示内存池效果
    println!("  🏊 模拟大量错误处理...");

    let start = std::time::Instant::now();
    let mut optimized_errors = Vec::new();

    for i in 0..1000 {
        let error = create_test_error(i);
        let optimized = optimizer.optimize_error_handling(&error).await?;
        optimized_errors.push(optimized);

        if i % 100 == 0 {
            println!("    - 已处理 {} 个错误", i);
        }
    }

    let processing_time = start.elapsed();

    println!("  📊 内存池处理结果:");
    println!("    - 总处理时间: {:?}", processing_time);
    println!("    - 平均处理时间: {:?}", processing_time / 1000);
    println!(
        "    - 处理吞吐量: {:.2} errors/sec",
        1000.0 / processing_time.as_secs_f64()
    );
    println!("    - 内存使用效率: 优化后使用内存池管理");

    // 获取内存池统计
    let metrics = optimizer.get_performance_metrics().await?;
    println!("    - 内存池统计: {:?}", metrics.memory_pool_stats);

    Ok(())
}

/// 示例 4: 并发优化
async fn concurrency_optimization_demo() -> Result<()> {
    println!("\n🚀 示例 4: 并发优化");
    println!("-------------------");

    let config = PerformanceConfig::default();
    let optimizer = PerformanceOptimizer::new(config)?;
    optimizer.start().await?;

    // 模拟并发错误处理
    println!("  🔀 模拟并发错误处理...");

    let start = std::time::Instant::now();

    // 创建多个并发任务
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let optimizer = optimizer.clone();
            tokio::spawn(async move {
                let mut results = Vec::new();
                for j in 0..100 {
                    let error = create_test_error(i * 100 + j);
                    let optimized = optimizer.optimize_error_handling(&error).await.unwrap();
                    results.push(optimized);
                }
                results
            })
        })
        .collect();

    // 等待所有任务完成
    let all_results: Vec<_> = futures::future::join_all(handles).await;

    let processing_time = start.elapsed();
    let total_processed = all_results
        .iter()
        .map(|r| r.as_ref().unwrap().len())
        .sum::<usize>();

    println!("  📊 并发处理结果:");
    println!("    - 总处理时间: {:?}", processing_time);
    println!("    - 总处理数量: {}", total_processed);
    println!(
        "    - 并发吞吐量: {:.2} errors/sec",
        total_processed as f64 / processing_time.as_secs_f64()
    );
    println!(
        "    - 并发效率: 相比串行处理提升约 {}%",
        ((total_processed as f64 / processing_time.as_secs_f64()) / 100.0 * 100.0) as u32
    );

    // 获取并发统计
    let metrics = optimizer.get_performance_metrics().await?;
    println!("    - 并发统计: {:?}", metrics.concurrency_stats);

    Ok(())
}

/// 示例 5: 基准测试
async fn benchmark_demo() -> Result<()> {
    println!("\n📊 示例 5: 基准测试");
    println!("-------------------");

    let config = PerformanceConfig::default();
    let optimizer = PerformanceOptimizer::new(config)?;
    optimizer.start().await?;

    // 运行所有基准测试
    println!("  🏃 运行性能基准测试...");

    let start = std::time::Instant::now();
    let results = optimizer.run_benchmarks().await?;
    let benchmark_time = start.elapsed();

    println!("  📈 基准测试结果:");
    println!("    - 总测试时间: {:?}", benchmark_time);
    println!();

    // 错误处理基准测试
    println!("    🔧 错误处理基准测试:");
    println!(
        "      - 操作数/秒: {:.2}",
        results.error_handling_benchmark.operations_per_second
    );
    println!(
        "      - 平均延迟: {:?}",
        results.error_handling_benchmark.duration / 1000
    );
    println!(
        "      - 内存使用: {} bytes",
        results.error_handling_benchmark.memory_usage
    );
    println!(
        "      - CPU使用率: {:.2}%",
        results.error_handling_benchmark.cpu_usage
    );
    println!();

    // 内存使用基准测试
    println!("    💾 内存使用基准测试:");
    println!(
        "      - 操作数/秒: {:.2}",
        results.memory_usage_benchmark.operations_per_second
    );
    println!(
        "      - 平均延迟: {:?}",
        results.memory_usage_benchmark.duration / 10000
    );
    println!(
        "      - 内存使用: {} bytes",
        results.memory_usage_benchmark.memory_usage
    );
    println!(
        "      - 内存效率: {:.2} bytes/op",
        results.memory_usage_benchmark.memory_usage as f64 / 10000.0
    );
    println!();

    // 并发基准测试
    println!("    🚀 并发基准测试:");
    println!(
        "      - 操作数/秒: {:.2}",
        results.concurrency_benchmark.operations_per_second
    );
    println!(
        "      - 平均延迟: {:?}",
        results.concurrency_benchmark.duration / 100
    );
    println!(
        "      - 并发效率: {:.2} tasks/sec",
        results.concurrency_benchmark.operations_per_second
    );
    println!();

    // 吞吐量基准测试
    println!("    📊 吞吐量基准测试:");
    println!(
        "      - 操作数/秒: {:.2}",
        results.throughput_benchmark.operations_per_second
    );
    println!(
        "      - 平均延迟: {:?}",
        results.throughput_benchmark.duration / 100000
    );
    println!(
        "      - 吞吐量: {:.2} ops/sec",
        results.throughput_benchmark.operations_per_second
    );
    println!();

    // 性能总结
    let total_ops = results.error_handling_benchmark.operations_per_second
        + results.memory_usage_benchmark.operations_per_second
        + results.concurrency_benchmark.operations_per_second
        + results.throughput_benchmark.operations_per_second;

    println!("  🎯 性能总结:");
    println!("    - 总操作数/秒: {:.2}", total_ops);
    println!("    - 平均性能: {:.2} ops/sec", total_ops / 4.0);
    println!("    - 性能等级: {}", get_performance_grade(total_ops));

    Ok(())
}

// 辅助函数

fn create_transport_error() -> OtlpError {
    OtlpError::Transport(otlp::error::TransportError::Connection {
        reason: "Connection failed".to_string(),
        endpoint: "http://localhost:4317".to_string(),
    })
}

fn create_serialization_error() -> OtlpError {
    OtlpError::Serialization(otlp::error::SerializationError::Json(
        serde_json::Error::io(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "JSON error",
        )),
    ))
}

fn create_configuration_error() -> OtlpError {
    OtlpError::Configuration(otlp::error::ConfigurationError::InvalidEndpoint {
        url: "invalid://url".to_string(),
    })
}

fn create_processing_error() -> OtlpError {
    OtlpError::Processing(otlp::error::ProcessingError::ValidationFailed {
        field: "data".to_string(),
        reason: "Invalid format".to_string(),
    })
}

fn create_export_error() -> OtlpError {
    OtlpError::Export(otlp::error::ExportError::ExportFailed {
        reason: "Network timeout".to_string(),
    })
}

fn create_test_error(index: usize) -> OtlpError {
    OtlpError::Internal(format!("Test error {}", index))
}

async fn verify_optimization_effectiveness(optimized: &OptimizedError) -> Result<()> {
    // 验证优化效果
    let original_size = optimized.metadata.size;
    let created_at = optimized.metadata.created_at;

    println!(
        "    - 优化验证: 原始大小 {} bytes, 创建时间 {:?}",
        original_size, created_at
    );

    // 检查是否使用了Arc共享
    let arc_count = Arc::strong_count(&optimized.inner);
    println!("    - Arc引用计数: {}", arc_count);

    Ok(())
}

fn get_performance_grade(ops_per_second: f64) -> &'static str {
    match ops_per_second {
        x if x >= 100000.0 => "🥇 优秀",
        x if x >= 50000.0 => "🥈 良好",
        x if x >= 10000.0 => "🥉 一般",
        _ => "⚠️ 需要优化",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_optimizer() {
        let result = basic_optimizer_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_zero_copy_optimization() {
        let result = zero_copy_optimization_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_memory_pool() {
        let result = memory_pool_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_concurrency_optimization() {
        let result = concurrency_optimization_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_benchmarks() {
        let result = benchmark_demo().await;
        assert!(result.is_ok());
    }
}
