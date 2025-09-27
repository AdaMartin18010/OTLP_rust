//! 高级性能优化基准测试
//!
//! 测试SIMD优化、缓存优化和内存池优化的性能表现

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use otlp::performance_optimization_advanced::*;
use std::hint::black_box;

/// 基准测试：SIMD优化性能
fn bench_simd_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd_optimization");
    
    let optimizer = AdvancedSimdOptimizer::new();
    
    // 测试不同大小的数据
    for size in [1000, 10000, 100000, 1000000].iter() {
        let _data = vec![1.0f64; *size];
        
        group.bench_with_input(
            BenchmarkId::new("f64_square", size),
            size,
            |bencher, &size| {
                let data = vec![1.0f64; size];
                bencher.iter(|| {
                    unsafe {
                        optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Square)
                    }
                })
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("f64_sqrt", size),
            size,
            |bencher, &size| {
                let data = vec![1.0f64; size];
                bencher.iter(|| {
                    unsafe {
                        optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Sqrt)
                    }
                })
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("i32_add", size),
            size,
            |bencher, &size| {
                let data = vec![1i32; size];
                bencher.iter(|| {
                    unsafe {
                        optimizer.process_i32_array_simd(black_box(&data), SimdIntOperation::Add(5))
                    }
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：缓存优化性能
#[allow(dead_code)]
#[allow(unused_variables)]
fn bench_cache_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_optimization");
    
    let cache_manager = CacheOptimizationManager::new();
    
    // 测试不同大小的数据
    for size in [1024, 10240, 102400, 1024000].iter() {
        let data = vec![0u8; *size];
        
        group.bench_with_input(
            BenchmarkId::new("cache_warm", size),
            size,
            |b, &size| {
                let data = vec![0u8; size];
                b.iter(|| {
                    cache_manager.warm_cache(black_box(&data))
                })
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("cache_analysis", size),
            size,
            |b, &size| {
                let data = vec![0u8; size];
                b.iter(|| {
                    cache_manager.analyze_cache_performance(black_box(&data))
                })
            },
        );
    }
    
    // 矩阵乘法测试
    group.bench_function("matrix_multiply_64x64", |bencher| {
        let n = 64;
        let a = vec![1.0f64; n * n];
        let b = vec![1.0f64; n * n];
        let mut c = vec![0.0f64; n * n];
        
        bencher.iter(|| {
            cache_manager.matrix_multiply_cache_optimized(
                black_box(&a),
                black_box(&b),
                black_box(&mut c),
                black_box(n)
            );
        })
    });
    
    group.bench_function("matrix_multiply_128x128", |bencher| {
        let n = 128;
        let a = vec![1.0f64; n * n];
        let b = vec![1.0f64; n * n];
        let mut c = vec![0.0f64; n * n];
        
        bencher.iter(|| {
            cache_manager.matrix_multiply_cache_optimized(
                black_box(&a),
                black_box(&b),
                black_box(&mut c),
                black_box(n)
            );
        })
    });
    
    group.finish();
}

/// 基准测试：内存池优化性能
fn bench_memory_pool_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_optimization");
    
    // 测试不同大小的内存分配
    for size in [64, 256, 1024, 4096, 16384].iter() {
        group.bench_with_input(
            BenchmarkId::new("smart_allocate", size),
            size,
            |bencher, &size| {
                let mut pool = AdvancedMemoryPoolOptimizer::new();
                bencher.iter(|| {
                    if let Ok(ptr) = pool.smart_allocate(black_box(size)) {
                        pool.return_memory(black_box(size), ptr);
                    }
                })
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("allocate_new", size),
            size,
            |bencher, &size| {
                let pool = AdvancedMemoryPoolOptimizer::new();
                bencher.iter(|| {
                    pool.allocate_new_memory(black_box(size))
                })
            },
        );
    }
    
    // 批量分配测试
    group.bench_function("batch_allocation_1000", |bencher| {
        let mut pool = AdvancedMemoryPoolOptimizer::new();
        bencher.iter(|| {
            for _ in 0..1000 {
                if let Ok(ptr) = pool.smart_allocate(1024) {
                    pool.return_memory(1024, ptr);
                }
            }
        })
    });
    
    group.bench_function("batch_allocation_10000", |bencher| {
        let mut pool = AdvancedMemoryPoolOptimizer::new();
        bencher.iter(|| {
            for _ in 0..10000 {
                if let Ok(ptr) = pool.smart_allocate(1024) {
                    pool.return_memory(1024, ptr);
                }
            }
        })
    });
    
    group.finish();
}

/// 基准测试：综合性能优化
fn bench_comprehensive_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("comprehensive_optimization");
    
    group.bench_function("comprehensive_benchmark", |bencher| {
        bencher.iter(|| {
            let optimizer = ComprehensivePerformanceOptimizer::new();
            // 注意：这里不能使用async，所以简化测试
            let data = vec![1.0f64; 100000];
            unsafe {
                optimizer.simd_optimizer().process_f64_array_simd(black_box(&data), SimdOperation::Square)
            }
        })
    });
    
    group.bench_function("memory_pool_stats", |bencher| {
        bencher.iter(|| {
            let mut optimizer = ComprehensivePerformanceOptimizer::new();
            optimizer.memory_pool().get_stats()
        })
    });
    
    group.bench_function("cache_analysis", |bencher| {
        bencher.iter(|| {
            let optimizer = ComprehensivePerformanceOptimizer::new();
            let data = vec![0u8; 1024 * 1024];
            optimizer.cache_manager().analyze_cache_performance(black_box(&data))
        })
    });
    
    group.finish();
}

/// 基准测试：性能对比
fn bench_performance_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_comparison");
    
    let data = vec![1.0f64; 100000];
    let optimizer = AdvancedSimdOptimizer::new();
    
    // SIMD vs 标量性能对比
    group.bench_function("simd_square", |b| {
        b.iter(|| {
            unsafe {
                optimizer.process_f64_array_simd(black_box(&data), SimdOperation::Square)
            }
        })
    });
    
    group.bench_function("scalar_square", |b| {
        b.iter(|| {
            data.iter().map(|&x| x * x).collect::<Vec<f64>>()
        })
    });
    
    // 缓存优化 vs 普通访问
    let cache_manager = CacheOptimizationManager::new();
    let test_data = vec![0u8; 1024 * 1024];
    
    group.bench_function("cache_optimized_access", |b| {
        b.iter(|| {
            cache_manager.warm_cache(black_box(&test_data));
            cache_manager.analyze_cache_performance(black_box(&test_data))
        })
    });
    
    group.bench_function("normal_access", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &byte in &test_data {
                sum += byte as u64;
            }
            sum
        })
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_simd_optimization,
    bench_cache_optimization,
    bench_memory_pool_optimization,
    bench_comprehensive_optimization,
    bench_performance_comparison
);
criterion_main!(benches);
