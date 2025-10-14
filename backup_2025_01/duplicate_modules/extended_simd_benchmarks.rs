//! 扩展SIMD操作基准测试
//!
//! 测试新增的SIMD数学运算性能

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
// 使用performance模块中的类型
use otlp::performance::*;
use std::hint::black_box;

/// 基准测试：扩展SIMD操作性能
fn bench_extended_simd_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("extended_simd_operations");

    let optimizer = AdvancedSimdOptimizer::new();

    // 测试不同大小的数据
    for size in [1000, 10000, 100000].iter() {
        // 测试绝对值运算
        group.bench_with_input(BenchmarkId::new("f64_abs", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Abs)
            })
        });

        // 测试最小值运算
        group.bench_with_input(BenchmarkId::new("f64_min", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Min)
            })
        });

        // 测试最大值运算
        group.bench_with_input(BenchmarkId::new("f64_max", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Max)
            })
        });

        // 测试加法运算
        group.bench_with_input(BenchmarkId::new("f64_add", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Add)
            })
        });

        // 测试减法运算
        group.bench_with_input(
            BenchmarkId::new("f64_subtract", size),
            size,
            |bencher, &size| {
                let data = vec![1.0f64; size];
                bencher.iter(|| unsafe {
                    optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Subtract)
                })
            },
        );

        // 测试乘法运算
        group.bench_with_input(
            BenchmarkId::new("f64_multiply", size),
            size,
            |bencher, &size| {
                let data = vec![1.0f64; size];
                bencher.iter(|| unsafe {
                    optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Multiply)
                })
            },
        );

        // 测试除法运算
        group.bench_with_input(
            BenchmarkId::new("f64_divide", size),
            size,
            |bencher, &size| {
                let data = vec![1.0f64; size];
                bencher.iter(|| unsafe {
                    optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Divide)
                })
            },
        );

        // 测试三角函数运算
        group.bench_with_input(BenchmarkId::new("f64_sin", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Sin)
            })
        });

        group.bench_with_input(BenchmarkId::new("f64_cos", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Cos)
            })
        });

        group.bench_with_input(BenchmarkId::new("f64_tan", size), size, |bencher, &size| {
            let data = vec![1.0f64; size];
            bencher.iter(|| unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Tan)
            })
        });
    }

    group.finish();
}

/// 基准测试：高级内存策略性能
fn bench_advanced_memory_strategy(c: &mut Criterion) {
    let mut group = c.benchmark_group("advanced_memory_strategy");

    // 测试不同大小的内存分配
    for size in [64, 256, 1024, 4096, 16384].iter() {
        group.bench_with_input(
            BenchmarkId::new("smart_allocate", size),
            size,
            |bencher, &size| {
                let mut manager = AdvancedMemoryPoolOptimizer::new();
                bencher.iter(|| {
                    if let Ok(ptr) = manager.smart_allocate(black_box(size)) {
                        manager.return_memory(black_box(size), ptr);
                    }
                })
            },
        );
    }

    // 测试批量分配性能
    group.bench_function("batch_allocation_1000", |bencher| {
        let mut manager = AdvancedMemoryPoolOptimizer::new();
        bencher.iter(|| {
            for _ in 0..1000 {
                if let Ok(ptr) = manager.smart_allocate(1024) {
                    manager.return_memory(1024, ptr);
                }
            }
        })
    });

    group.bench_function("batch_allocation_10000", |bencher| {
        let mut manager = AdvancedMemoryPoolOptimizer::new();
        bencher.iter(|| {
            for _ in 0..10000 {
                if let Ok(ptr) = manager.smart_allocate(1024) {
                    manager.return_memory(1024, ptr);
                }
            }
        })
    });

    // 测试内存压力下的性能
    group.bench_function("memory_pressure_test", |bencher| {
        let mut manager = AdvancedMemoryPoolOptimizer::new();
        bencher.iter(|| {
            // 创建内存压力
            let mut ptrs = Vec::new();
            for _ in 0..5000 {
                if let Ok(ptr) = manager.smart_allocate(1024) {
                    ptrs.push(ptr);
                }
            }

            // 释放一半内存
            for (i, ptr) in ptrs.iter().enumerate() {
                if i % 2 == 0 {
                    manager.return_memory(1024, *ptr);
                }
            }

            // 清理剩余内存
            for ptr in ptrs.into_iter().skip(1).step_by(2) {
                manager.return_memory(1024, ptr);
            }
        })
    });

    group.finish();
}

/// 基准测试：性能对比分析
fn bench_performance_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_comparison");

    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0f64; 100000];

    // 对比不同SIMD操作的性能
    let operations = [
        SimdOperation::Square,
        SimdOperation::Sqrt,
        SimdOperation::Abs,
        SimdOperation::Add,
        SimdOperation::Multiply,
        SimdOperation::Sin,
        SimdOperation::Cos,
    ];

    for operation in operations.iter() {
        group.bench_function(format!("operation_{:?}", operation), |bencher| {
            bencher
                .iter(|| unsafe { optimizer.process_f64_array_simd(black_box(&data), *operation) })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_extended_simd_operations,
    bench_advanced_memory_strategy,
    bench_performance_comparison
);
criterion_main!(benches);
