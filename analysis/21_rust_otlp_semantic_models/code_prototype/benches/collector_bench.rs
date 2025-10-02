//! Collector 性能基准测试

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use otlp_collector::{Collector, Config, Span};
use tokio::runtime::Runtime;

/// 基准测试: 单线程收集
fn bench_single_thread_collect(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("single_thread_collect_1k", |b| {
        b.to_async(&rt).iter(|| async {
            let config = Config {
                batch_size: 1000,
                batch_timeout_ms: 5000,
                buffer_capacity: 100_000,
                endpoint: "http://localhost:4317".to_string(),
                max_retries: 1,
                retry_delay_ms: 10,
            };
            
            let collector = Collector::new(config).await.unwrap();
            
            for i in 0..1000 {
                let span = Span::new(format!("span-{}", i));
                black_box(collector.collect(span).unwrap());
            }
            
            collector.shutdown().await.unwrap();
        });
    });
}

/// 基准测试: 批量收集
fn bench_batch_collect(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let sizes = vec![100, 1000, 10000];
    
    for size in sizes {
        c.bench_with_input(
            BenchmarkId::new("batch_collect", size),
            &size,
            |b, &size| {
                b.to_async(&rt).iter(|| async move {
                    let config = Config {
                        batch_size: size,
                        batch_timeout_ms: 5000,
                        buffer_capacity: 100_000,
                        endpoint: "http://localhost:4317".to_string(),
                        max_retries: 1,
                        retry_delay_ms: 10,
                    };
                    
                    let collector = Collector::new(config).await.unwrap();
                    
                    let spans: Vec<Span> = (0..size)
                        .map(|i| Span::new(format!("span-{}", i)))
                        .collect();
                    
                    black_box(collector.collect_batch(spans).unwrap());
                    
                    collector.shutdown().await.unwrap();
                });
            },
        );
    }
}

/// 基准测试: 并发收集
fn bench_concurrent_collect(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("concurrent_collect_10_threads", |b| {
        b.to_async(&rt).iter(|| async {
            let config = Config {
                batch_size: 1000,
                batch_timeout_ms: 5000,
                buffer_capacity: 100_000,
                endpoint: "http://localhost:4317".to_string(),
                max_retries: 1,
                retry_delay_ms: 10,
            };
            
            let collector = std::sync::Arc::new(Collector::new(config).await.unwrap());
            
            let mut handles = vec![];
            
            for thread_id in 0..10 {
                let collector_clone = std::sync::Arc::clone(&collector);
                let handle = tokio::spawn(async move {
                    for i in 0..100 {
                        let span = Span::new(format!("thread-{}-span-{}", thread_id, i));
                        collector_clone.collect(span).unwrap();
                    }
                });
                handles.push(handle);
            }
            
            for handle in handles {
                handle.await.unwrap();
            }
            
            let collector = std::sync::Arc::try_unwrap(collector).unwrap();
            collector.shutdown().await.unwrap();
        });
    });
}

criterion_group!(
    benches,
    bench_single_thread_collect,
    bench_batch_collect,
    bench_concurrent_collect
);
criterion_main!(benches);

