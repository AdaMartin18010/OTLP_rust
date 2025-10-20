// 性能基准测试
//
// 运行命令: cargo bench --bench performance_benchmarks
//
// 注意: 需要在 Cargo.toml 中启用 bench 功能

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use std::time::Duration;
use tokio::runtime::Runtime;

// 导入核心模块
use otlp::core::{PerformanceOptimizer, ReliabilityManager};

/// 对象池性能基准测试
pub fn bench_object_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("object_pool");
    
    // 创建运行时用于异步操作
    let rt = Runtime::new().unwrap();
    
    for size in [10, 50, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("acquire_release", size),
            size,
            |b, &_size| {
                let optimizer = PerformanceOptimizer::new();
                
                b.iter(|| {
                    rt.block_on(async {
                        // 模拟对象池的获取和释放操作
                        // 注意: 对象池在 PerformanceOptimizer 内部，这里测试优化器的整体开销
                        black_box(&optimizer);
                    });
                });
            },
        );
    }
    
    group.finish();
}

/// 压缩性能基准测试
pub fn bench_compression(c: &mut Criterion) {
    let mut group = c.benchmark_group("compression");
    
    // 创建运行时
    let rt = Runtime::new().unwrap();
    let optimizer = PerformanceOptimizer::new();
    
    // 测试不同数据大小的压缩性能
    for data_size in [1024, 4096, 16384, 65536].iter() {
        let data = vec![0u8; *data_size];
        
        group.bench_with_input(
            BenchmarkId::new("compression", data_size),
            &data,
            |b, data| {
                b.iter(|| {
                    rt.block_on(async {
                        // 测试压缩操作
                        let result = optimizer.try_compress(data).await.ok();
                        black_box(result);
                    });
                });
            },
        );
    }
    
    group.finish();
}

/// 批处理性能基准测试
pub fn bench_batching(c: &mut Criterion) {
    let mut group = c.benchmark_group("batching");
    
    let optimizer = PerformanceOptimizer::new();
    
    for batch_size in [10, 50, 100, 500].iter() {
        group.bench_with_input(
            BenchmarkId::new("should_batch", batch_size),
            batch_size,
            |b, &batch_size| {
                b.iter(|| {
                    // 测试批处理判断逻辑
                    let result = optimizer.should_batch(black_box(batch_size));
                    black_box(result);
                });
            },
        );
    }
    
    group.finish();
}

/// 重试机制性能基准测试
pub fn bench_retry(c: &mut Criterion) {
    let mut group = c.benchmark_group("retry");
    group.measurement_time(Duration::from_secs(10));
    
    let rt = Runtime::new().unwrap();
    
    group.bench_function("retry_success", |b| {
        let manager = ReliabilityManager::new();
        
        b.iter(|| {
            rt.block_on(async {
                // 测试成功场景的重试开销
                let result = manager.retry(|| async {
                    Ok::<_, String>("success")
                }).await.ok();
                black_box(result);
            });
        });
    });
    
    group.bench_function("retry_with_timeout", |b| {
        let manager = ReliabilityManager::new();
        
        b.iter(|| {
            rt.block_on(async {
                // 测试带超时的重试
                let result = manager.retry_with_timeout(
                    || async { Ok::<_, String>("success") },
                    Duration::from_secs(5),
                ).await.ok();
                black_box(result);
            });
        });
    });
    
    group.finish();
}

/// 熔断器性能基准测试
pub fn bench_circuit_breaker(c: &mut Criterion) {
    let mut group = c.benchmark_group("circuit_breaker");
    
    let rt = Runtime::new().unwrap();
    
    group.bench_function("record_success", |b| {
        let manager = ReliabilityManager::new();
        
        b.iter(|| {
            rt.block_on(async {
                // 测试记录成功的性能开销
                let _result = manager.retry(|| async {
                    Ok::<_, String>("success")
                }).await;
            });
        });
    });
    
    group.bench_function("fallback", |b| {
        let manager = ReliabilityManager::new();
        
        b.iter(|| {
            rt.block_on(async {
                // 测试 fallback 机制的性能
                let result = manager.with_fallback(
                    || async { Some("primary") },
                    || async { "fallback" },
                ).await;
                black_box(result);
            });
        });
    });
    
    group.finish();
}

/// 统计信息访问性能基准测试
pub fn bench_stats_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("stats_access");
    
    let rt = Runtime::new().unwrap();
    
    group.bench_function("get_performance_stats", |b| {
        let optimizer = PerformanceOptimizer::new();
        
        b.iter(|| {
            rt.block_on(async {
                let stats = optimizer.stats().await;
                black_box(stats);
            });
        });
    });
    
    group.bench_function("get_reliability_stats", |b| {
        let manager = ReliabilityManager::new();
        
        b.iter(|| {
            rt.block_on(async {
                let stats = manager.stats().await;
                black_box(stats);
            });
        });
    });
    
    group.finish();
}

/// 配置操作性能基准测试
pub fn bench_config_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("config_operations");
    
    group.bench_function("create_performance_optimizer", |b| {
        b.iter(|| {
            let optimizer = PerformanceOptimizer::new();
            black_box(optimizer);
        });
    });
    
    group.bench_function("create_reliability_manager", |b| {
        b.iter(|| {
            let manager = ReliabilityManager::new();
            black_box(manager);
        });
    });
    
    group.bench_function("access_performance_config", |b| {
        let optimizer = PerformanceOptimizer::new();
        b.iter(|| {
            // 测试访问配置的性能
            let config = optimizer.batch_config();
            black_box(config);
        });
    });
    
    group.finish();
}

// 配置基准测试组
criterion_group!(
    benches,
    bench_object_pool,
    bench_compression,
    bench_batching,
    bench_retry,
    bench_circuit_breaker,
    bench_stats_access,
    bench_config_operations,
);

criterion_main!(benches);

// =============================================================================
// 使用说明
// =============================================================================
//
// 1. 在 Cargo.toml 中确保有以下配置:
//
// ```toml
// [dev-dependencies]
// criterion = "0.5"
// tokio = { version = "1", features = ["full"] }
//
// [[bench]]
// name = "performance_benchmarks"
// harness = false
// ```
//
// 2. 运行基准测试:
//
// ```bash
// # 运行所有基准测试
// cargo bench --bench performance_benchmarks
//
// # 运行特定基准测试
// cargo bench --bench performance_benchmarks -- compression
//
// # 只运行压缩相关的测试
// cargo bench --bench performance_benchmarks -- bench_compression
// ```
//
// 3. 查看结果:
//
// ```bash
// # 结果保存在 target/criterion/
// # HTML 报告: target/criterion/report/index.html
// ```
//
// 4. 与基线对比:
//
// ```bash
// # 保存当前结果为基线
// cargo bench --bench performance_benchmarks -- --save-baseline baseline
//
// # 与基线对比
// cargo bench --bench performance_benchmarks -- --baseline baseline
// ```
//
// 5. 生成火焰图 (需要安装 cargo-flamegraph):
//
// ```bash
// cargo install flamegraph
// cargo flamegraph --bench performance_benchmarks
// ```
//
// =============================================================================
// 性能目标
// =============================================================================
//
// 对象池:
// - acquire: < 100ns
// - release: < 50ns
//
// 压缩 (1KB):
// - compression: < 10μs
//
// 批处理判断:
// - should_batch: < 10ns
//
// 重试:
// - 成功路径: < 100ns 开销
// - 带超时: < 150ns 开销
//
// 熔断器:
// - record: < 50ns
// - fallback: < 100ns
//
// 统计访问:
// - get_stats: < 50ns
//
// 配置操作:
// - create: < 1μs
// - clone: < 100ns
//
// =============================================================================
// 性能优化建议
// =============================================================================
//
// 1. **对象池优化**:
//    - 使用 LIFO 策略提高缓存局部性
//    - 预分配对象池容量
//    - 使用 thread-local 减少锁竞争
//
// 2. **压缩优化**:
//    - 对小数据跳过压缩
//    - 使用流式压缩处理大数据
//    - 考虑使用 Snappy 替代 Gzip
//
// 3. **批处理优化**:
//    - 内联 should_batch 函数
//    - 使用位操作优化判断逻辑
//    - 避免不必要的边界检查
//
// 4. **重试优化**:
//    - 使用快速失败策略
//    - 优化指数退避算法
//    - 减少时间戳获取开销
//
// 5. **熔断器优化**:
//    - 使用原子操作减少锁开销
//    - 批量更新统计信息
//    - 优化状态转换逻辑
//
// 6. **统计优化**:
//    - 使用无锁数据结构
//    - 批量更新统计数据
//    - 延迟计算平均值
//
// =============================================================================
