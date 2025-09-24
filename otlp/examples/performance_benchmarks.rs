//! # OTLP Rust 性能基准测试程序
//!
//! 本程序提供了OTLP Rust库的全面性能基准测试，
//! 包括微服务性能、负载均衡性能、追踪性能等各个方面的测试。

use std::sync::Arc;
use std::time::Duration;
use tracing::info;

use otlp::{
    benchmarks::{
        BenchmarkConfig, BenchmarkResult, BenchmarkRunner, LoadBalancerBenchmark,
        MicroserviceBenchmark, TracingBenchmark,
    },
    microservices::{
        CircuitBreaker, CircuitBreakerConfig, HealthStatus, LoadBalancer, MicroserviceClient,
        MockConsulClient, RetryConfig, Retryer, RoundRobinLoadBalancer, ServiceEndpoint,
        WeightedRoundRobinLoadBalancer,
    },
};

/// 初始化基准测试环境
async fn init_benchmark_environment() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("🚀 OTLP Rust 性能基准测试环境初始化");

    // 设置Rust性能优化
    std::env::set_var("RUST_LOG", "info");
    std::env::set_var("RUST_BACKTRACE", "1");

    info!("✅ 基准测试环境初始化完成");
    Ok(())
}

/// 微服务性能基准测试
async fn run_microservice_benchmark() -> Result<BenchmarkResult, Box<dyn std::error::Error>> {
    info!("🏗️ 开始微服务性能基准测试");

    let benchmark = MicroserviceBenchmark::new();
    let result = benchmark.run().await?;

    info!("📊 微服务性能基准测试结果:");
    info!(
        "  总迭代次数: {}",
        result.iterations_completed + result.iterations_failed
    );
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P95延迟: {:?}", result.latency_stats.p95);
    info!("  P99延迟: {:?}", result.latency_stats.p99);

    Ok(result)
}

/// 负载均衡器性能基准测试
async fn run_load_balancer_benchmark() -> Result<BenchmarkResult, Box<dyn std::error::Error>> {
    info!("⚖️ 开始负载均衡器性能基准测试");

    let benchmark = LoadBalancerBenchmark::new();
    let result = benchmark.run().await?;

    info!("📊 负载均衡器性能基准测试结果:");
    info!(
        "  总迭代次数: {}",
        result.iterations_completed + result.iterations_failed
    );
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P95延迟: {:?}", result.latency_stats.p95);
    info!("  P99延迟: {:?}", result.latency_stats.p99);

    Ok(result)
}

/// 分布式追踪性能基准测试
async fn run_tracing_benchmark() -> Result<BenchmarkResult, Box<dyn std::error::Error>> {
    info!("🔍 开始分布式追踪性能基准测试");

    let benchmark = TracingBenchmark::new();
    let result = benchmark.run().await?;

    info!("📊 分布式追踪性能基准测试结果:");
    info!(
        "  总迭代次数: {}",
        result.iterations_completed + result.iterations_failed
    );
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P95延迟: {:?}", result.latency_stats.p95);
    info!("  P99延迟: {:?}", result.latency_stats.p99);

    Ok(result)
}

/// 负载均衡器对比基准测试
async fn run_load_balancer_comparison() -> Result<(), Box<dyn std::error::Error>> {
    info!("⚖️ 开始负载均衡器对比基准测试");

    // 测试轮询负载均衡器
    info!("🔄 测试轮询负载均衡器");
    let round_robin_config = BenchmarkConfig {
        name: "round-robin-lb".to_string(),
        description: "轮询负载均衡器性能测试".to_string(),
        iterations: 10000,
        concurrency: 10,
        duration: Duration::ZERO,
        warmup_duration: Duration::from_millis(100),
        cooldown_duration: Duration::from_millis(50),
        metrics: Default::default(),
    };

    let round_robin_runner = BenchmarkRunner::new(round_robin_config);

    let round_robin_result = round_robin_runner
        .run(|_iteration| async {
            let start = std::time::Instant::now();

            // 创建测试端点
            let endpoints = vec![
                ServiceEndpoint {
                    id: "endpoint-1".to_string(),
                    address: "10.0.1.10".to_string(),
                    port: 8080,
                    weight: 100,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
                ServiceEndpoint {
                    id: "endpoint-2".to_string(),
                    address: "10.0.1.11".to_string(),
                    port: 8080,
                    weight: 200,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
                ServiceEndpoint {
                    id: "endpoint-3".to_string(),
                    address: "10.0.1.12".to_string(),
                    port: 8080,
                    weight: 300,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
            ];

            let round_robin_lb = RoundRobinLoadBalancer::new();
            let _selected = round_robin_lb.select_endpoint(&endpoints).await;
            Ok(start.elapsed())
        })
        .await?;

    // 测试加权轮询负载均衡器
    info!("⚖️ 测试加权轮询负载均衡器");
    let weighted_round_robin_config = BenchmarkConfig {
        name: "weighted-round-robin-lb".to_string(),
        description: "加权轮询负载均衡器性能测试".to_string(),
        iterations: 10000,
        concurrency: 10,
        duration: Duration::ZERO,
        warmup_duration: Duration::from_millis(100),
        cooldown_duration: Duration::from_millis(50),
        metrics: Default::default(),
    };

    let weighted_runner = BenchmarkRunner::new(weighted_round_robin_config);

    let weighted_result = weighted_runner
        .run(|_iteration| async {
            let start = std::time::Instant::now();

            // 创建测试端点
            let endpoints = vec![
                ServiceEndpoint {
                    id: "endpoint-1".to_string(),
                    address: "10.0.1.10".to_string(),
                    port: 8080,
                    weight: 100,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
                ServiceEndpoint {
                    id: "endpoint-2".to_string(),
                    address: "10.0.1.11".to_string(),
                    port: 8080,
                    weight: 200,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
                ServiceEndpoint {
                    id: "endpoint-3".to_string(),
                    address: "10.0.1.12".to_string(),
                    port: 8080,
                    weight: 300,
                    metadata: std::collections::HashMap::new(),
                    health_status: HealthStatus::Healthy,
                    last_health_check: std::time::Instant::now(),
                },
            ];

            let weighted_lb = WeightedRoundRobinLoadBalancer::new();
            let _selected = weighted_lb.select_endpoint(&endpoints).await;
            Ok(start.elapsed())
        })
        .await?;

    // 对比结果
    info!("📊 负载均衡器对比结果:");
    info!("  轮询负载均衡器:");
    info!("    吞吐量: {:.2} req/s", round_robin_result.throughput);
    info!("    平均延迟: {:?}", round_robin_result.latency_stats.mean);
    info!("    P95延迟: {:?}", round_robin_result.latency_stats.p95);

    info!("  加权轮询负载均衡器:");
    info!("    吞吐量: {:.2} req/s", weighted_result.throughput);
    info!("    平均延迟: {:?}", weighted_result.latency_stats.mean);
    info!("    P95延迟: {:?}", weighted_result.latency_stats.p95);

    Ok(())
}

/// 熔断器性能基准测试
async fn run_circuit_breaker_benchmark() -> Result<(), Box<dyn std::error::Error>> {
    info!("🔌 开始熔断器性能基准测试");

    let config = BenchmarkConfig {
        name: "circuit-breaker".to_string(),
        description: "熔断器性能基准测试".to_string(),
        iterations: 50000,
        concurrency: 100,
        duration: Duration::ZERO,
        warmup_duration: Duration::from_millis(100),
        cooldown_duration: Duration::from_millis(50),
        metrics: Default::default(),
    };

    let runner = BenchmarkRunner::new(config);

    let result = runner
        .run(|iteration| async move {
            let start = std::time::Instant::now();
            let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());

            // 测试熔断器调用
            let _result = circuit_breaker
                .call(|| {
                    let iteration = iteration;
                    Box::pin(async move {
                        // 模拟请求处理
                        let processing_time = Duration::from_micros(10 + (iteration % 100) as u64);
                        tokio::time::sleep(processing_time).await;

                        // 模拟偶尔的失败
                        if iteration % 1000 == 0 {
                            Err(anyhow::anyhow!("模拟失败"))
                        } else {
                            Ok(())
                        }
                    })
                })
                .await;

            Ok(start.elapsed())
        })
        .await?;

    info!("📊 熔断器性能基准测试结果:");
    info!(
        "  总迭代次数: {}",
        result.iterations_completed + result.iterations_failed
    );
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P95延迟: {:?}", result.latency_stats.p95);

    Ok(())
}

/// 重试机制性能基准测试
async fn run_retry_benchmark() -> Result<(), Box<dyn std::error::Error>> {
    info!("🔄 开始重试机制性能基准测试");

    let config = BenchmarkConfig {
        name: "retry-mechanism".to_string(),
        description: "重试机制性能基准测试".to_string(),
        iterations: 10000,
        concurrency: 50,
        duration: Duration::ZERO,
        warmup_duration: Duration::from_millis(100),
        cooldown_duration: Duration::from_millis(50),
        metrics: Default::default(),
    };

    let runner = BenchmarkRunner::new(config);

    let result = runner
        .run(|iteration| async move {
            let start = std::time::Instant::now();
            let retryer = Retryer::new(RetryConfig::default());

            let _result = retryer
                .execute(|| {
                    let iteration = iteration;
                    Box::pin(async move {
                        // 模拟偶尔失败的操作
                        if iteration % 10 == 0 {
                            Err(anyhow::anyhow!("模拟失败"))
                        } else {
                            Ok(())
                        }
                    })
                })
                .await;

            Ok(start.elapsed())
        })
        .await?;

    info!("📊 重试机制性能基准测试结果:");
    info!(
        "  总迭代次数: {}",
        result.iterations_completed + result.iterations_failed
    );
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P95延迟: {:?}", result.latency_stats.p95);

    Ok(())
}

/// 综合性能基准测试
async fn run_comprehensive_benchmark() -> Result<(), Box<dyn std::error::Error>> {
    info!("🏆 开始综合性能基准测试");

    let config = BenchmarkConfig {
        name: "comprehensive-microservices".to_string(),
        description: "综合微服务架构性能基准测试".to_string(),
        iterations: 0,
        concurrency: 200,
        duration: Duration::from_secs(120),
        warmup_duration: Duration::from_secs(10),
        cooldown_duration: Duration::from_secs(5),
        metrics: Default::default(),
    };

    let runner = BenchmarkRunner::new(config);

    let result = runner
        .run(|iteration| async move {
            let start = std::time::Instant::now();

            // 在闭包内初始化微服务组件
            let load_balancer = std::sync::Arc::new(RoundRobinLoadBalancer::new());
            let circuit_breaker_config = CircuitBreakerConfig::default();
            let retry_config = RetryConfig::default();

            // 创建Mock服务发现客户端
            let mock_consul = Arc::new(MockConsulClient::new());

            // 添加测试服务
            let test_endpoints = vec![ServiceEndpoint {
                id: "test-endpoint-1".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8080,
                weight: 100,
                metadata: std::collections::HashMap::new(),
                health_status: HealthStatus::Healthy,
                last_health_check: std::time::Instant::now(),
            }];
            mock_consul
                .add_service("test-service".to_string(), test_endpoints)
                .await;

            let client = MicroserviceClient::new(
                mock_consul,
                load_balancer,
                circuit_breaker_config,
                retry_config,
            );

            // 模拟完整的微服务调用流程
            let call_time = Duration::from_millis(1 + (iteration % 10) as u64);
            tokio::time::sleep(call_time).await;

            // 模拟偶尔的失败
            if iteration % 1000 == 0 {
                // 模拟调用失败的情况
                return Err(anyhow::anyhow!("模拟服务调用失败").into());
            }

            // 模拟成功的服务调用
            let _response = client
                .call_service("test-service", move |_endpoint| {
                    let iteration = iteration;
                    Box::pin(async move {
                        // 模拟服务调用
                        Ok(format!("success-{}", iteration))
                    })
                })
                .await;

            Ok(start.elapsed())
        })
        .await?;

    info!("📊 综合性能基准测试结果:");
    info!("  总持续时间: {:?}", result.total_duration);
    info!("  完成迭代: {}", result.iterations_completed);
    info!("  失败迭代: {}", result.iterations_failed);
    info!(
        "  成功率: {:.2}%",
        (result.iterations_completed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0
    );
    info!("  吞吐量: {:.2} req/s", result.throughput);
    info!("  平均延迟: {:?}", result.latency_stats.mean);
    info!("  P50延迟: {:?}", result.latency_stats.p50);
    info!("  P95延迟: {:?}", result.latency_stats.p95);
    info!("  P99延迟: {:?}", result.latency_stats.p99);
    info!("  P999延迟: {:?}", result.latency_stats.p999);

    Ok(())
}

/// 导出基准测试报告
async fn export_benchmark_report(
    results: &[BenchmarkResult],
) -> Result<(), Box<dyn std::error::Error>> {
    info!("📄 导出基准测试报告");

    // 生成简化的JSON报告
    let mut json_content = String::new();
    json_content.push_str("[\n");

    for (i, result) in results.iter().enumerate() {
        if i > 0 {
            json_content.push_str(",\n");
        }
        json_content.push_str(&format!(
            r#"  {{
    "test_name": "{}",
    "throughput": {:.2},
    "p50_latency_ms": {},
    "p95_latency_ms": {},
    "p99_latency_ms": {},
    "error_rate_percent": {:.2}
  }}"#,
            result.config.name,
            result.throughput,
            result.latency_stats.p50.as_millis(),
            result.latency_stats.p95.as_millis(),
            result.latency_stats.p99.as_millis(),
            (result.iterations_failed as f64
                / (result.iterations_completed + result.iterations_failed) as f64)
                * 100.0
        ));
    }
    json_content.push_str("\n]");

    tokio::fs::write("benchmark_report.json", json_content).await?;

    // 生成CSV报告
    let mut csv_content = String::new();
    csv_content.push_str("Test Name,Throughput (req/s),P50 Latency (ms),P95 Latency (ms),P99 Latency (ms),Error Rate (%)\n");

    for result in results {
        let p50_ms = result.latency_stats.p50.as_millis();
        let p95_ms = result.latency_stats.p95.as_millis();
        let p99_ms = result.latency_stats.p99.as_millis();
        let error_rate = (result.iterations_failed as f64
            / (result.iterations_completed + result.iterations_failed) as f64)
            * 100.0;

        csv_content.push_str(&format!(
            "{},{:.2},{},{},{},{:.2}\n",
            result.config.name, result.throughput, p50_ms, p95_ms, p99_ms, error_rate
        ));
    }

    tokio::fs::write("benchmark_report.csv", csv_content).await?;

    info!("✅ 基准测试报告已导出:");
    info!("  📊 JSON报告: benchmark_report.json");
    info!("  📈 CSV报告: benchmark_report.csv");

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化基准测试环境
    init_benchmark_environment().await?;

    info!("🚀 OTLP Rust 性能基准测试程序");
    info!("=====================================");

    let mut all_results = Vec::new();

    // 运行各种基准测试
    info!("\n🏗️ 微服务性能基准测试");
    let microservice_result = run_microservice_benchmark().await?;
    all_results.push(microservice_result);

    info!("\n⚖️ 负载均衡器性能基准测试");
    let lb_result = run_load_balancer_benchmark().await?;
    all_results.push(lb_result);

    info!("\n🔍 分布式追踪性能基准测试");
    let tracing_result = run_tracing_benchmark().await?;
    all_results.push(tracing_result);

    info!("\n⚖️ 负载均衡器对比测试");
    run_load_balancer_comparison().await?;

    info!("\n🔌 熔断器性能基准测试");
    run_circuit_breaker_benchmark().await?;

    info!("\n🔄 重试机制性能基准测试");
    run_retry_benchmark().await?;

    info!("\n🏆 综合性能基准测试");
    run_comprehensive_benchmark().await?;

    // 导出基准测试报告
    info!("\n📄 导出基准测试报告");
    export_benchmark_report(&all_results).await?;

    info!("\n🎉 所有基准测试完成！");
    info!("📊 性能基准测试总结:");
    info!("  ✅ 微服务性能测试");
    info!("  ✅ 负载均衡器性能测试");
    info!("  ✅ 分布式追踪性能测试");
    info!("  ✅ 熔断器性能测试");
    info!("  ✅ 重试机制性能测试");
    info!("  ✅ 综合架构性能测试");
    info!("  ✅ 基准测试报告导出");

    Ok(())
}
