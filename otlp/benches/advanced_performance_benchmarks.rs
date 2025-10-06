//! # 高级性能基准测试
//!
//! 基于理论文档中的性能优化模式，测试各种优化技术的性能表现。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.2节

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use otlp::performance::{
    ObjectPool, ObjectPoolConfig, SimdOptimizer, SimdConfig, ZeroCopyTransporter,
    SimdMonitor,
};
use otlp::performance::object_pool::ObjectFactory;
use std::sync::Arc;
use std::time::Duration;

/// 基准测试：对象池性能
fn bench_object_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("object_pool");
    
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("acquire_release", size), size, |b, &size| {
            let config = ObjectPoolConfig {
                max_size: size,
                min_size: size / 2,
                creation_timeout: Duration::from_secs(1),
                acquisition_timeout: Duration::from_secs(1),
                idle_timeout: Duration::from_secs(60),
                enable_stats: true,
            };
            
            // 创建测试工厂
            struct StringFactory;
            impl ObjectFactory<String> for StringFactory {
                fn create(&self) -> Result<String, otlp::performance::ObjectPoolError> {
                    Ok(String::with_capacity(1024))
                }
                fn validate(&self, _object: &String) -> bool { true }
                fn reset(&self, object: &mut String) { object.clear(); }
                fn clone_box(&self) -> Box<dyn ObjectFactory<String>> {
                    Box::new(StringFactory)
                }
            }
            
            let pool = ObjectPool::new(config, Box::new(StringFactory));
            
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let obj = pool.acquire().await.unwrap();
                    black_box(obj);
                });
            });
        });
    }
    
    group.finish();
}

/// 基准测试：SIMD优化性能
fn bench_simd_optimizations(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd_optimizations");
    
    for size in [100, 1000, 10000, 100000].iter() {
        // 生成测试数据
        let data: Vec<f64> = (0..*size).map(|i| (i as f64) * 0.1).collect();
        let data2: Vec<f64> = (0..*size).map(|i| (i as f64) * 0.2).collect();
        
        group.bench_with_input(BenchmarkId::new("vectorized_sum", size), &data, |b, data| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_sum(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("vectorized_dot_product", size), &(data.clone(), data2.clone()), |b, (a, b_vec)| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_dot_product(a, b_vec);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("scalar_sum", size), &data, |b, data| {
            b.iter(|| {
                let result: f64 = data.iter().sum();
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("scalar_dot_product", size), &(data.clone(), data2.clone()), |b, (a, b_vec)| {
            b.iter(|| {
                let result: f64 = a.iter().zip(b_vec.iter()).map(|(x, y)| x * y).sum();
                let _ = black_box(result);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：零拷贝传输性能
fn bench_zero_copy_transmission(c: &mut Criterion) {
    let mut group = c.benchmark_group("zero_copy_transmission");
    
    for size in [1024, 8192, 65536, 524288].iter() {
        let data: Vec<u8> = (0..*size).map(|i| (i % 256) as u8).collect();
        
        group.bench_with_input(BenchmarkId::new("zero_copy_transmit", size), &data, |b, data| {
            let transporter = ZeroCopyTransporter::new();
            
            b.iter(|| {
                let result = transporter.transmit(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("copy_transmit", size), &data, |b, data| {
            let transporter = ZeroCopyTransporter::new();
            
            b.iter(|| {
                let result = transporter.transmit_with_copy(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("manual_copy", size), &data, |b, data| {
            b.iter(|| {
                let result = data.to_vec();
                let _ = black_box(result);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：SIMD监控性能
fn bench_simd_monitoring(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd_monitoring");
    
    for size in [1000, 10000, 100000].iter() {
        let data: Vec<f64> = (0..*size).map(|i| (i as f64) * 0.1).collect();
        
        group.bench_with_input(BenchmarkId::new("monitored_sum", size), &data, |b, data| {
            let monitor = SimdMonitor::new(SimdConfig::default());
            
            b.iter(|| {
                let result = monitor.monitored_sum(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("monitored_dot_product", size), &data, |b, data| {
            let monitor = SimdMonitor::new(SimdConfig::default());
            let data2 = data.clone();
            
            b.iter(|| {
                let result = monitor.monitored_dot_product(data, &data2);
                let _ = black_box(result);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：内存对齐性能
fn bench_memory_alignment(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_alignment");
    
    for size in [1000, 10000, 100000].iter() {
        // 对齐的数据
        let mut aligned_data = Vec::with_capacity(*size);
        aligned_data.resize(*size, 0.0);
        for i in 0..*size {
            aligned_data[i] = (i as f64) * 0.1;
        }
        
        // 非对齐的数据
        let mut unaligned_data = Vec::with_capacity(*size + 1);
        unaligned_data.resize(*size + 1, 0.0);
        for i in 0..*size {
            unaligned_data[i + 1] = (i as f64) * 0.1;
        }
        let unaligned_slice = &unaligned_data[1..*size + 1];
        
        group.bench_with_input(BenchmarkId::new("aligned_data", size), &aligned_data, |b, data| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_sum(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("unaligned_data", size), &unaligned_slice, |b, data| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_sum(data);
                let _ = black_box(result);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：并发性能
fn bench_concurrent_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_performance");
    
    for thread_count in [1, 2, 4, 8, 16].iter() {
        group.bench_with_input(BenchmarkId::new("concurrent_object_pool", thread_count), thread_count, |b, &thread_count| {
            let config = ObjectPoolConfig {
                max_size: 1000,
                min_size: 100,
                creation_timeout: Duration::from_secs(1),
                acquisition_timeout: Duration::from_secs(1),
                idle_timeout: Duration::from_secs(60),
                enable_stats: true,
            };
            
            // 创建测试工厂
            struct StringFactory;
            impl ObjectFactory<String> for StringFactory {
                fn create(&self) -> Result<String, otlp::performance::ObjectPoolError> {
                    Ok(String::with_capacity(1024))
                }
                fn validate(&self, _object: &String) -> bool { true }
                fn reset(&self, object: &mut String) { object.clear(); }
                fn clone_box(&self) -> Box<dyn ObjectFactory<String>> {
                    Box::new(StringFactory)
                }
            }
            
            let pool = Arc::new(ObjectPool::new(config, Box::new(StringFactory)));
            
            b.iter(|| {
                let handles: Vec<_> = (0..thread_count)
                    .map(|_| {
                        let pool = pool.clone();
                        std::thread::spawn(move || {
                            let rt = tokio::runtime::Runtime::new().unwrap();
                            rt.block_on(async {
                                for _ in 0..100 {
                                    let obj = pool.acquire().await.unwrap();
                                    black_box(obj);
                                }
                            });
                        })
                    })
                    .collect();
                
                for handle in handles {
                    handle.join().unwrap();
                }
            });
        });
        
        group.bench_with_input(BenchmarkId::new("concurrent_simd", thread_count), thread_count, |b, &thread_count| {
            let data: Vec<f64> = (0..10000).map(|i| (i as f64) * 0.1).collect();
            let optimizer = Arc::new(SimdOptimizer::default());
            
            b.iter(|| {
                let handles: Vec<_> = (0..thread_count)
                    .map(|_| {
                        let data = data.clone();
                        let optimizer = optimizer.clone();
                        std::thread::spawn(move || {
                            for _ in 0..100 {
                                let result = optimizer.vectorized_sum(&data);
                                let _ = black_box(result);
                            }
                        })
                    })
                    .collect();
                
                for handle in handles {
                    handle.join().unwrap();
                }
            });
        });
    }
    
    group.finish();
}

/// 基准测试：内存使用效率
fn bench_memory_efficiency(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");
    
    for size in [1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("object_pool_memory", size), size, |b, &size| {
            let config = ObjectPoolConfig {
                max_size: size,
                min_size: size / 2,
                creation_timeout: Duration::from_secs(1),
                acquisition_timeout: Duration::from_secs(1),
                idle_timeout: Duration::from_secs(60),
                enable_stats: true,
            };
            
            // 创建测试工厂
            struct StringFactory;
            impl ObjectFactory<String> for StringFactory {
                fn create(&self) -> Result<String, otlp::performance::ObjectPoolError> {
                    Ok(String::with_capacity(1024))
                }
                fn validate(&self, _object: &String) -> bool { true }
                fn reset(&self, object: &mut String) { object.clear(); }
                fn clone_box(&self) -> Box<dyn ObjectFactory<String>> {
                    Box::new(StringFactory)
                }
            }
            
            let pool = ObjectPool::new(config, Box::new(StringFactory));
            
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let mut objects = Vec::new();
                    for _ in 0..size {
                        let obj = pool.acquire().await.unwrap();
                        objects.push(obj);
                    }
                    // 对象会在作用域结束时自动返回池中
                    black_box(objects);
                });
            });
        });
        
        group.bench_with_input(BenchmarkId::new("direct_allocation", size), size, |b, &size| {
            b.iter(|| {
                let mut objects = Vec::new();
                for _ in 0..size {
                    let obj = String::with_capacity(1024);
                    objects.push(obj);
                }
                black_box(objects);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：缓存友好性
fn bench_cache_friendliness(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_friendliness");
    
    for size in [1000, 10000, 100000].iter() {
        // 连续访问模式
        let continuous_data: Vec<f64> = (0..*size).map(|i| (i as f64) * 0.1).collect();
        
        // 随机访问模式
        let mut random_data: Vec<f64> = (0..*size).map(|i| (i as f64) * 0.1).collect();
        use rand::seq::SliceRandom;
        use rand::rng;
        random_data.shuffle(&mut rng());
        
        group.bench_with_input(BenchmarkId::new("continuous_access", size), &continuous_data, |b, data| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_sum(data);
                let _ = black_box(result);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("random_access", size), &random_data, |b, data| {
            let optimizer = SimdOptimizer::default();
            b.iter(|| {
                let result = optimizer.vectorized_sum(data);
                let _ = black_box(result);
            });
        });
    }
    
    group.finish();
}

/// 基准测试：错误处理性能
fn bench_error_handling_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling_performance");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("successful_operations", size), size, |b, &size| {
            let config = ObjectPoolConfig {
                max_size: size * 2,
                min_size: size,
                creation_timeout: Duration::from_secs(1),
                acquisition_timeout: Duration::from_secs(1),
                idle_timeout: Duration::from_secs(60),
                enable_stats: true,
            };
            
            // 创建测试工厂
            struct StringFactory;
            impl ObjectFactory<String> for StringFactory {
                fn create(&self) -> Result<String, otlp::performance::ObjectPoolError> {
                    Ok(String::with_capacity(1024))
                }
                fn validate(&self, _object: &String) -> bool { true }
                fn reset(&self, object: &mut String) { object.clear(); }
                fn clone_box(&self) -> Box<dyn ObjectFactory<String>> {
                    Box::new(StringFactory)
                }
            }
            
            let pool = ObjectPool::new(config, Box::new(StringFactory));
            
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    for _ in 0..size {
                        let result = pool.acquire().await;
                        match result {
                            Ok(obj) => {
                                black_box(obj);
                            },
                            Err(_) => panic!("Unexpected error"),
                        }
                    }
                });
            });
        });
        
        group.bench_with_input(BenchmarkId::new("error_operations", size), size, |b, &size| {
            let config = ObjectPoolConfig {
                max_size: size / 2, // 故意设置较小的池大小
                min_size: size / 4,
                creation_timeout: Duration::from_millis(1), // 很短的超时
                acquisition_timeout: Duration::from_millis(1),
                idle_timeout: Duration::from_secs(60),
                enable_stats: true,
            };
            
            // 创建测试工厂
            struct StringFactory;
            impl ObjectFactory<String> for StringFactory {
                fn create(&self) -> Result<String, otlp::performance::ObjectPoolError> {
                    Ok(String::with_capacity(1024))
                }
                fn validate(&self, _object: &String) -> bool { true }
                fn reset(&self, object: &mut String) { object.clear(); }
                fn clone_box(&self) -> Box<dyn ObjectFactory<String>> {
                    Box::new(StringFactory)
                }
            }
            
            let pool = ObjectPool::new(config, Box::new(StringFactory));
            
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    for _ in 0..size {
                        let result = pool.acquire().await;
                        match result {
                            Ok(obj) => {
                                black_box(obj);
                            },
                            Err(_) => {
                                // 错误处理开销
                                black_box("error");
                            }
                        }
                    }
                });
            });
        });
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_object_pool,
    bench_simd_optimizations,
    bench_zero_copy_transmission,
    bench_simd_monitoring,
    bench_memory_alignment,
    bench_concurrent_performance,
    bench_memory_efficiency,
    bench_cache_friendliness,
    bench_error_handling_performance
);

criterion_main!(benches);
