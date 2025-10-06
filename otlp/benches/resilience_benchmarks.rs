//! # 容错模式性能基准测试
//!
//! 测试断路器、重试、舱壁和超时模式的性能表现。

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use anyhow;
use otlp::resilience::{
    CircuitBreaker, CircuitBreakerConfig, Retrier, RetryConfig, RetryStrategy,
    Bulkhead, BulkheadConfig, Timeout, TimeoutConfig,
};
use std::time::Duration;
use tokio::runtime::Runtime;

fn bench_circuit_breaker_success(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = CircuitBreakerConfig::default();
    let breaker = CircuitBreaker::new(config);
    
    c.bench_function("circuit_breaker_success", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = breaker
                .execute::<_, i32, anyhow::Error>(async { Ok(42) })
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_circuit_breaker_failure(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = CircuitBreakerConfig {
        failure_threshold: 10, // 高阈值避免快速打开
        ..Default::default()
    };
    let breaker = CircuitBreaker::new(config);
    
    c.bench_function("circuit_breaker_failure", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let result: Result<i32, _> = breaker
                    .execute(async { Err(anyhow::anyhow!("test error")) })
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_retry_success(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::Fixed {
            interval: Duration::from_millis(1),
        },
        total_timeout: None,
        health_check: false,
    };
    let retrier = Retrier::new(config);
    
    c.bench_function("retry_success", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = retrier
                .execute(|| Box::pin(async { Ok::<i32, &str>(42) }))
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_retry_failure(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::Fixed {
            interval: Duration::from_millis(1),
        },
        total_timeout: None,
        health_check: false,
    };
    let retrier = Retrier::new(config);
    
    c.bench_function("retry_failure", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = retrier
                .execute(|| Box::pin(async { Err("test error") }))
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_bulkhead_acquire(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = BulkheadConfig {
        max_concurrent_requests: 10,
        max_queue_size: 100,
        queue_timeout: Duration::from_secs(1),
        enable_stats: true,
    };
    let bulkhead = Bulkhead::new(config);
    
    c.bench_function("bulkhead_acquire", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result = bulkhead.acquire().await;
            black_box(result)
            })
        })
    });
}

fn bench_bulkhead_execute(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = BulkheadConfig::default();
    let bulkhead = Bulkhead::new(config);
    
    c.bench_function("bulkhead_execute", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = bulkhead
                .execute::<_, i32, anyhow::Error>(async { Ok(42) })
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_timeout_success(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = TimeoutConfig {
        default_timeout: Duration::from_secs(1),
        ..Default::default()
    };
    let timeout = Timeout::new(config);
    
    c.bench_function("timeout_success", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = timeout
                .execute::<_, i32, anyhow::Error>(async { Ok(42) })
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_timeout_timeout(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let config = TimeoutConfig {
        default_timeout: Duration::from_millis(1),
        ..Default::default()
    };
    let timeout = Timeout::new(config);
    
    c.bench_function("timeout_timeout", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
            let result: Result<i32, _> = timeout
                .execute::<_, i32, anyhow::Error>(async {
                    tokio::time::sleep(Duration::from_millis(10)).await;  
                    Ok(42)
                })
                .await;
            black_box(result)
            })
        })
    });
}

fn bench_retry_strategies(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("retry_strategies");
    
    let strategies = vec![
        ("fixed", RetryStrategy::Fixed {
            interval: Duration::from_millis(1),
        }),
        ("linear", RetryStrategy::Linear {
            initial_interval: Duration::from_millis(1),
            max_interval: Duration::from_millis(10),
            increment: Duration::from_millis(1),
        }),
        ("exponential", RetryStrategy::Exponential {
            initial_interval: Duration::from_millis(1),
            max_interval: Duration::from_millis(10),
            multiplier: 2.0,
        }),
        ("exponential_jitter", RetryStrategy::ExponentialWithJitter {
            initial_interval: Duration::from_millis(1),
            max_interval: Duration::from_millis(10),
            multiplier: 2.0,
            jitter_factor: 0.1,
        }),
    ];
    
    for (name, strategy) in strategies {
        let config = RetryConfig {
            max_attempts: 3,
            strategy,
            total_timeout: None,
            health_check: false,
        };
        let retrier = Retrier::new(config);
        
        group.bench_with_input(BenchmarkId::new("strategy", name), &retrier, |b, retrier| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let result: Result<i32, _> = retrier
                        .execute(|| Box::pin(async { Ok::<i32, &str>(42) }))
                        .await;
                    black_box(result)
                })
            })
        });
    }
    
    group.finish();
}

fn bench_circuit_breaker_states(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("circuit_breaker_states");
    
    // 测试不同状态下的性能
    let configs = vec![
        ("low_threshold", CircuitBreakerConfig {
            failure_threshold: 2,
            recovery_timeout: Duration::from_millis(100),
            half_open_max_requests: 1,
            success_threshold: 1,
        }),
        ("high_threshold", CircuitBreakerConfig {
            failure_threshold: 100,
            recovery_timeout: Duration::from_secs(30),
            half_open_max_requests: 10,
            success_threshold: 5,
        }),
    ];
    
    for (name, config) in configs {
        let breaker = CircuitBreaker::new(config);
        
        group.bench_with_input(BenchmarkId::new("config", name), &breaker, |b, breaker| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let result: Result<i32, _> = breaker
                        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
                        .await;
                    black_box(result)
                })
            })
        });
    }
    
    group.finish();
}

fn bench_bulkhead_concurrent(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("bulkhead_concurrent");
    
    let configs = vec![
        ("low_concurrency", BulkheadConfig {
            max_concurrent_requests: 2,
            max_queue_size: 10,
            queue_timeout: Duration::from_secs(1),
            enable_stats: true,
        }),
        ("high_concurrency", BulkheadConfig {
            max_concurrent_requests: 20,
            max_queue_size: 100,
            queue_timeout: Duration::from_secs(1),
            enable_stats: true,
        }),
    ];
    
    for (name, config) in configs {
        let bulkhead = Bulkhead::new(config);
        
        group.bench_with_input(BenchmarkId::new("config", name), &bulkhead, |b, bulkhead| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let result = bulkhead.acquire().await;
                    black_box(result)
                })
            })
        });
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_circuit_breaker_success,
    bench_circuit_breaker_failure,
    bench_retry_success,
    bench_retry_failure,
    bench_bulkhead_acquire,
    bench_bulkhead_execute,
    bench_timeout_success,
    bench_timeout_timeout,
    bench_retry_strategies,
    bench_circuit_breaker_states,
    bench_bulkhead_concurrent
);

criterion_main!(benches);
