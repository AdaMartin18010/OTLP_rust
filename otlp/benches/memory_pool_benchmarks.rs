//! 内存池性能基准测试

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use otlp::performance::memory_pool::{MemoryPool, MemoryPoolConfig, MemoryPoolManager};
use std::time::Duration;

fn bench_memory_pool_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_allocation");
    
    let config = MemoryPoolConfig {
        initial_size: 100,
        max_size: 1000,
        ..Default::default()
    };
    let pool = MemoryPool::new(config);

    for size in [64, 256, 1024, 4096, 16384].iter() {
        group.bench_with_input(BenchmarkId::new("allocate", size), size, |b, &size| {
            b.iter(|| {
                let data = pool.allocate(black_box(size));
                black_box(data)
            })
        });
    }
    
    group.finish();
}

fn bench_memory_pool_vs_std_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_vs_std");
    
    let config = MemoryPoolConfig {
        initial_size: 1000,
        max_size: 10000,
        ..Default::default()
    };
    let pool = MemoryPool::new(config);

    group.bench_function("memory_pool_allocate", |b| {
        b.iter(|| {
            let data = pool.allocate(black_box(1024));
            black_box(data)
        })
    });

    group.bench_function("std_vec_allocate", |b| {
        b.iter(|| {
            let data = vec![0u8; black_box(1024)];
            black_box(data)
        })
    });
    
    group.finish();
}

fn bench_memory_pool_reuse(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_reuse");
    
    let config = MemoryPoolConfig {
        initial_size: 100,
        max_size: 1000,
        ..Default::default()
    };
    let pool = MemoryPool::new(config);

    group.bench_function("allocate_and_return", |b| {
        b.iter(|| {
            let data = pool.allocate(black_box(1024));
            pool.deallocate(data);
        })
    });

    group.bench_function("allocate_only", |b| {
        b.iter(|| {
            let _data = pool.allocate(black_box(1024));
        })
    });
    
    group.finish();
}

fn bench_memory_pool_manager(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_manager");
    
    let manager = MemoryPoolManager::new();
    let config = MemoryPoolConfig::default();
    
    group.bench_function("create_pool", |b| {
        b.iter(|| {
            let pool = manager.create_pool(
                black_box("test_pool".to_string()),
                config.clone()
            );
            black_box(pool)
        })
    });

    group.bench_function("get_pool", |b| {
        let _pool = manager.create_pool("test_pool".to_string(), config.clone());
        b.iter(|| {
            let pool = manager.get_pool(black_box("test_pool"));
            black_box(pool)
        })
    });
    
    group.finish();
}

fn bench_memory_pool_concurrent(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_concurrent");
    
    let config = MemoryPoolConfig {
        initial_size: 1000,
        max_size: 10000,
        ..Default::default()
    };
    let pool = std::sync::Arc::new(MemoryPool::new(config));

    group.bench_function("concurrent_allocation", |b| {
        b.iter(|| {
            let pool = pool.clone();
            let handles: Vec<_> = (0..10)
                .map(|_| {
                    let pool = pool.clone();
                    std::thread::spawn(move || {
                        for _ in 0..100 {
                            let data = pool.allocate(black_box(1024));
                            black_box(data);
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }
        })
    });
    
    group.finish();
}

fn bench_memory_pool_cleanup(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_cleanup");
    
    let config = MemoryPoolConfig {
        initial_size: 100,
        max_size: 1000,
        cleanup_interval: Duration::from_millis(1),
        ..Default::default()
    };
    let pool = MemoryPool::new(config);

    group.bench_function("cleanup_trigger", |b| {
        b.iter(|| {
            // 分配大量内存触发清理
            for _ in 0..1000 {
                let data = pool.allocate(black_box(512));
                pool.deallocate(data);
            }
        })
    });
    
    group.finish();
}

fn bench_memory_pool_stats(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool_stats");
    
    let config = MemoryPoolConfig::default();
    let pool = MemoryPool::new(config);

    group.bench_function("get_stats", |b| {
        b.iter(|| {
            let stats = pool.stats();
            black_box(stats)
        })
    });

    group.bench_function("get_stats_with_operations", |b| {
        b.iter(|| {
            let data = pool.allocate(black_box(1024));
            let stats = pool.stats();
            pool.deallocate(data);
            black_box(stats)
        })
    });
    
    group.finish();
}

criterion_group!(
    memory_pool_benches,
    bench_memory_pool_allocation,
    bench_memory_pool_vs_std_allocation,
    bench_memory_pool_reuse,
    bench_memory_pool_manager,
    bench_memory_pool_concurrent,
    bench_memory_pool_cleanup,
    bench_memory_pool_stats
);

criterion_main!(memory_pool_benches);
