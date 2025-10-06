//! 网络I/O性能基准测试

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use otlp::network::{
    AsyncIoConfig, AsyncIoManager, ConnectionPool, ConnectionPoolConfig,
    LoadBalancer, LoadBalancerConfig, LoadBalancingStrategy, NetworkConfig, NetworkManager,
};
use std::net::SocketAddr;
use std::sync::Arc;

fn bench_async_io_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("async_io_creation");
    
    let config = AsyncIoConfig::default();
    
    group.bench_function("create_manager", |b| {
        b.iter(|| {
            let manager = AsyncIoManager::new(black_box(config.clone()));
            black_box(manager)
        })
    });
    
    group.finish();
}

fn bench_connection_pool_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("connection_pool_creation");
    
    let config = ConnectionPoolConfig::default();
    let io_config = AsyncIoConfig::default();
    let addresses = vec!["127.0.0.1:8080".parse::<SocketAddr>().unwrap()];
    
    group.bench_function("create_pool", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let pool = ConnectionPool::new(
                    black_box(config.clone()),
                    black_box(io_config.clone()),
                    black_box(addresses.clone()),
                ).await;
                black_box(pool)
            })
        })
    });
    
    group.finish();
}

fn bench_load_balancer_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("load_balancer_creation");
    
    let config = LoadBalancerConfig::default();
    
    group.bench_function("create_balancer", |b| {
        b.iter(|| {
            let balancer = LoadBalancer::new(black_box(config.clone()));
            black_box(balancer)
        })
    });
    
    group.finish();
}

fn bench_network_manager_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("network_manager_creation");
    
    let config = NetworkConfig::default();
    
    group.bench_function("create_manager", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let manager = NetworkManager::new(black_box(config.clone())).await;
                black_box(manager)
            })
        })
    });
    
    group.finish();
}

fn bench_load_balancing_strategies(c: &mut Criterion) {
    let mut group = c.benchmark_group("load_balancing_strategies");
    
    let config = LoadBalancerConfig::default();
    let balancer = LoadBalancer::new(config);
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 添加一些后端服务器
    rt.block_on(async {
        balancer.add_backend("127.0.0.1:8080", 1).await.unwrap();
        balancer.add_backend("127.0.0.1:8081", 1).await.unwrap();
        balancer.add_backend("127.0.0.1:8082", 1).await.unwrap();
    });
    
    let strategies = vec![
        ("round_robin", LoadBalancingStrategy::RoundRobin),
        ("least_connections", LoadBalancingStrategy::LeastConnections),
        ("random", LoadBalancingStrategy::Random),
        ("weighted_round_robin", LoadBalancingStrategy::WeightedRoundRobin(vec![1, 2, 3])),
    ];
    
    for (name, strategy) in strategies {
        group.bench_function(name, |b| {
            b.iter(|| {
                rt.block_on(async {
                    let result = balancer.select_backend(&black_box(strategy.clone())).await;
                    black_box(result)
                })
            })
        });
    }
    
    group.finish();
}

fn bench_connection_pool_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("connection_pool_operations");
    
    let config = ConnectionPoolConfig {
        min_connections: 10,
        max_connections: 100,
        ..Default::default()
    };
    let io_config = AsyncIoConfig::default();
    let addresses = vec!["127.0.0.1:8080".parse::<SocketAddr>().unwrap()];
    
    let rt = tokio::runtime::Runtime::new().unwrap();
    let pool = rt.block_on(async {
        ConnectionPool::new(config, io_config, addresses).await.unwrap()
    });
    
    group.bench_function("get_connection", |b| {
        b.iter(|| {
            rt.block_on(async {
                let result = pool.get_connection().await;
                black_box(result)
            })
        })
    });
    
    group.bench_function("get_stats", |b| {
        b.iter(|| {
            rt.block_on(async {
                let stats = pool.stats().await;
                black_box(stats)
            })
        })
    });
    
    group.finish();
}

fn bench_async_io_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("async_io_operations");
    
    let config = AsyncIoConfig::default();
    let manager = AsyncIoManager::new(config);
    
    group.bench_function("get_stats", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let stats = manager.stats().await;
                black_box(stats)
            })
        })
    });
    
    group.bench_function("get_connections", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let connections = manager.get_connections().await;
                black_box(connections)
            })
        })
    });
    
    group.finish();
}

fn bench_network_manager_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("network_manager_operations");
    
    let config = NetworkConfig::default();
    let rt = tokio::runtime::Runtime::new().unwrap();
    let manager = rt.block_on(async {
        NetworkManager::new(config).await.unwrap()
    });
    
    group.bench_function("get_stats", |b| {
        b.iter(|| {
            rt.block_on(async {
                let stats = manager.get_stats().await;
                black_box(stats)
            })
        })
    });
    
    group.bench_function("add_backend", |b| {
        b.iter(|| {
            rt.block_on(async {
                let result = manager.add_backend("127.0.0.1:8080", 1).await;
                black_box(result)
            })
        })
    });
    
    group.finish();
}

fn bench_concurrent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_operations");
    
    let config = NetworkConfig::default();
    let rt = tokio::runtime::Runtime::new().unwrap();
    let manager = Arc::new(rt.block_on(async {
        NetworkManager::new(config).await.unwrap()
    }));
    
    group.bench_function("concurrent_stats", |b| {
        b.iter(|| {
            rt.block_on(async {
                let handles: Vec<_> = (0..10)
                    .map(|_| {
                        let manager = manager.clone();
                        tokio::spawn(async move {
                            manager.get_stats().await
                        })
                    })
                    .collect();
                
                let results = futures::future::join_all(handles).await;
                black_box(results)
            })
        })
    });
    
    group.finish();
}

fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    
    group.bench_function("create_multiple_managers", |b| {
        b.iter(|| {
            let config = NetworkConfig::default();
            let rt = tokio::runtime::Runtime::new().unwrap();
            let managers: Vec<_> = (0..100)
                .map(|_| {
                    rt.block_on(async {
                        NetworkManager::new(config.clone()).await.unwrap()
                    })
                })
                .collect();
            black_box(managers)
        })
    });
    
    group.finish();
}

criterion_group!(
    network_io_benches,
    bench_async_io_creation,
    bench_connection_pool_creation,
    bench_load_balancer_creation,
    bench_network_manager_creation,
    bench_load_balancing_strategies,
    bench_connection_pool_operations,
    bench_async_io_operations,
    bench_network_manager_operations,
    bench_concurrent_operations,
    bench_memory_usage
);

criterion_main!(network_io_benches);
