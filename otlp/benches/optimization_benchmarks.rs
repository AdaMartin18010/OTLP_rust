//! 优化模块性能基准测试

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use otlp::optimization::{
    OptimizationCategory, OptimizationManager,
    OptimizationPriority, PerformanceMetrics, PerformanceSnapshot,
};
use std::time::Duration;
use std::collections::HashMap;
use std::sync::Arc;

fn bench_optimization_manager_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization_manager_creation");
    
    group.bench_function("create_manager", |b| {
        b.iter(|| {
            let manager = OptimizationManager::new();
            black_box(manager)
        })
    });
    
    group.finish();
}

fn bench_performance_metrics_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_metrics_update");
    
    let manager = OptimizationManager::new();
    let metrics = PerformanceMetrics {
        cpu_usage: 50.0,
        memory_usage: 60.0,
        throughput: 1000,
        latency: Duration::from_millis(50),
        error_rate: 0.1,
        connection_count: 100,
        queue_depth: 10,
        cache_hit_rate: 95.0,
    };
    
    group.bench_function("update_metrics", |b| {
        b.iter(|| {
            let _ = manager.update_performance_metrics(black_box(metrics.clone()));
        })
    });
    
    group.finish();
}

fn bench_performance_snapshot_recording(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_snapshot_recording");
    
    let manager = OptimizationManager::new();
    let snapshot = PerformanceSnapshot {
        timestamp: std::time::Instant::now(),
        cpu_usage: 50.0,
        memory_usage: 60.0,
        throughput: 1000,
        latency: Duration::from_millis(50),
        error_rate: 0.1,
        config_hash: "test_hash".to_string(),
    };
    
    group.bench_function("record_snapshot", |b| {
        b.iter(|| {
            let _ = manager.record_performance_snapshot(black_box(snapshot.clone()));
        })
    });
    
    group.finish();
}

fn bench_optimization_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization_analysis");
    
    let manager = OptimizationManager::new();
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 初始化管理器
    rt.block_on(async {
        manager.initialize().await.unwrap();
    });
    
    // 记录一些性能数据
    for i in 0..50 {
        let metrics = PerformanceMetrics {
            cpu_usage: 90.0 + (i as f64 * 0.1),
            memory_usage: 80.0 + (i as f64 * 0.1),
            throughput: 500 + (i * 10) as u64,
            latency: Duration::from_millis(200 - (i as u64 * 2)),
            error_rate: 2.0 - (i as f64 * 0.01),
            connection_count: 100 + i,
            queue_depth: 10 + i,
            cache_hit_rate: 80.0 + (i as f64 * 0.2),
        };
        
        let snapshot = PerformanceSnapshot {
            timestamp: std::time::Instant::now(),
            cpu_usage: metrics.cpu_usage,
            memory_usage: metrics.memory_usage,
            throughput: metrics.throughput,
            latency: metrics.latency,
            error_rate: metrics.error_rate,
            config_hash: format!("hash_{}", i),
        };
        
        manager.update_performance_metrics(metrics).unwrap();
        manager.record_performance_snapshot(snapshot).unwrap();
    }
    
    group.bench_function("analyze_optimizations", |b| {
        b.iter(|| {
            rt.block_on(async {
                let report = manager.perform_optimization_analysis().await.unwrap();
                black_box(report)
            })
        })
    });
    
    group.finish();
}

fn bench_config_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("config_optimization");
    
    let manager = OptimizationManager::new();
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 初始化管理器
    rt.block_on(async {
        manager.initialize().await.unwrap();
    });
    
    // 记录性能数据
    for i in 0..100 {
        let snapshot = PerformanceSnapshot {
            timestamp: std::time::Instant::now(),
            cpu_usage: 95.0, // 高CPU使用率
            memory_usage: 90.0, // 高内存使用率
            throughput: 500, // 低吞吐量
            latency: Duration::from_millis(300), // 高延迟
            error_rate: 2.0, // 高错误率
            config_hash: format!("hash_{}", i),
        };
        
        manager.record_performance_snapshot(snapshot).unwrap();
    }
    
    group.bench_function("analyze_config_optimizations", |b| {
        b.iter(|| {
            rt.block_on(async {
                let optimizations = manager.smart_config_manager().analyze_and_optimize().await.unwrap();
                black_box(optimizations)
            })
        })
    });
    
    group.finish();
}

fn bench_optimization_application(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization_application");
    
    let manager = OptimizationManager::new();
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 初始化管理器
    rt.block_on(async {
        manager.initialize().await.unwrap();
    });
    
    // 记录性能数据
    for i in 0..50 {
        let metrics = PerformanceMetrics {
            cpu_usage: 95.0,
            memory_usage: 90.0,
            throughput: 500,
            latency: Duration::from_millis(200),
            error_rate: 2.0,
            connection_count: 100,
            queue_depth: 10,
            cache_hit_rate: 80.0,
        };
        
        let snapshot = PerformanceSnapshot {
            timestamp: std::time::Instant::now(),
            cpu_usage: metrics.cpu_usage,
            memory_usage: metrics.memory_usage,
            throughput: metrics.throughput,
            latency: metrics.latency,
            error_rate: metrics.error_rate,
            config_hash: format!("hash_{}", i),
        };
        
        manager.update_performance_metrics(metrics).unwrap();
        manager.record_performance_snapshot(snapshot).unwrap();
    }
    
    // 生成优化报告
    let report = rt.block_on(async {
        manager.perform_optimization_analysis().await.unwrap()
    });
    
    group.bench_function("apply_optimizations", |b| {
        b.iter(|| {
            rt.block_on(async {
                let result = manager.apply_optimizations(&black_box(report.clone())).await.unwrap();
                black_box(result)
            })
        })
    });
    
    group.finish();
}

fn bench_concurrent_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_optimization");
    
    let manager = Arc::new(OptimizationManager::new());
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 初始化管理器
    rt.block_on(async {
        manager.initialize().await.unwrap();
    });
    
    group.bench_function("concurrent_analysis", |b| {
        b.iter(|| {
            rt.block_on(async {
                let handles: Vec<_> = (0..10)
                    .map(|_| {
                        let manager = manager.clone();
                        tokio::spawn(async move {
                            let metrics = PerformanceMetrics {
                                cpu_usage: 90.0,
                                memory_usage: 85.0,
                                throughput: 800,
                                latency: Duration::from_millis(150),
                                error_rate: 1.5,
                                connection_count: 100,
                                queue_depth: 10,
                                cache_hit_rate: 85.0,
                            };
                            
                            manager.update_performance_metrics(metrics).unwrap();
                            manager.perform_optimization_analysis().await.unwrap()
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
            let managers: Vec<_> = (0..100)
                .map(|_| OptimizationManager::new())
                .collect();
            black_box(managers)
        })
    });
    
    group.finish();
}

fn bench_optimization_sorting(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization_sorting");
    
    let optimizations = vec![
        otlp::optimization::OptimizationSuggestion {
            id: "1".to_string(),
            category: OptimizationCategory::Cpu,
            priority: OptimizationPriority::Low,
            description: "Low priority".to_string(),
            expected_improvement: 10.0,
            implementation_effort: otlp::optimization::ImplementationEffort::Low,
            risk_level: otlp::optimization::RiskLevel::Low,
            parameters: HashMap::new(),
        },
        otlp::optimization::OptimizationSuggestion {
            id: "2".to_string(),
            category: OptimizationCategory::Memory,
            priority: OptimizationPriority::Critical,
            description: "Critical priority".to_string(),
            expected_improvement: 50.0,
            implementation_effort: otlp::optimization::ImplementationEffort::High,
            risk_level: otlp::optimization::RiskLevel::Medium,
            parameters: HashMap::new(),
        },
        otlp::optimization::OptimizationSuggestion {
            id: "3".to_string(),
            category: OptimizationCategory::Network,
            priority: OptimizationPriority::High,
            description: "High priority".to_string(),
            expected_improvement: 30.0,
            implementation_effort: otlp::optimization::ImplementationEffort::Medium,
            risk_level: otlp::optimization::RiskLevel::Low,
            parameters: HashMap::new(),
        },
    ];
    
    group.bench_function("sort_optimizations", |b| {
        b.iter(|| {
            let mut opts = optimizations.clone();
            otlp::optimization::sort_optimizations_by_priority(&mut opts);
            black_box(opts)
        })
    });
    
    group.finish();
}

criterion_group!(
    optimization_benches,
    bench_optimization_manager_creation,
    bench_performance_metrics_update,
    bench_performance_snapshot_recording,
    bench_optimization_analysis,
    bench_config_optimization,
    bench_optimization_application,
    bench_concurrent_optimization,
    bench_memory_usage,
    bench_optimization_sorting
);

criterion_main!(optimization_benches);
