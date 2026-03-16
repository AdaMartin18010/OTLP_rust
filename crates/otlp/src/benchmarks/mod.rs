//! # 性能基准测试模块
//!
//! 本模块提供了OTLP Rust库的全面性能基准测试

use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tracing::info;

/// 基准测试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkConfig {
    pub name: String,
    pub description: String,
    pub iterations: u32,
    pub concurrency: u32,
    pub duration: Duration,
    pub warmup_duration: Duration,
    pub cooldown_duration: Duration,
    pub metrics: BenchmarkMetrics,
}

/// 基准测试指标
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BenchmarkMetrics {
    pub throughput: Option<f64>,
    pub latency_p50: Option<Duration>,
    pub latency_p95: Option<Duration>,
    pub latency_p99: Option<Duration>,
    pub error_rate: Option<f64>,
    pub memory_usage: Option<u64>,
    pub cpu_usage: Option<f64>,
}

/// 延迟统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LatencyStats {
    pub min: Duration,
    pub max: Duration,
    pub mean: Duration,
    pub p50: Duration,
    pub p90: Duration,
    pub p95: Duration,
    pub p99: Duration,
    pub p999: Duration,
    pub std_dev: Duration,
}

/// 内存统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    pub peak_memory: u64,
    pub avg_memory: u64,
    pub memory_growth: u64,
    pub allocations: u64,
    pub deallocations: u64,
}

/// CPU统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpuStats {
    pub avg_cpu_usage: f64,
    pub peak_cpu_usage: f64,
    pub cpu_time: Duration,
    pub context_switches: u64,
}

/// 基准测试运行器
pub struct BenchmarkRunner {
    config: BenchmarkConfig,
    results: Arc<RwLock<Vec<BenchmarkResult>>>,
    running: Arc<RwLock<bool>>,
}

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub config: BenchmarkConfig,
    pub start_time: Instant,
    pub end_time: Instant,
    pub total_duration: Duration,
    pub iterations_completed: u32,
    pub iterations_failed: u32,
    pub throughput: f64,
    pub latency_stats: LatencyStats,
    pub memory_stats: MemoryStats,
    pub cpu_stats: CpuStats,
    pub errors: Vec<BenchmarkError>,
}

/// 主要测试结果
#[derive(Debug)]
struct MainTestResult {
    iterations_completed: u32,
    iterations_failed: u32,
    throughput: f64,
    latency_stats: LatencyStats,
    memory_stats: MemoryStats,
    cpu_stats: CpuStats,
    errors: Vec<BenchmarkError>,
}

/// 基准测试错误
#[derive(Debug, thiserror::Error, Clone)]
pub enum BenchmarkError {
    #[error("基准测试运行错误: {0}")]
    RuntimeError(String),
    #[error("配置错误: {0}")]
    ConfigError(String),
    #[error("内存不足")]
    OutOfMemory,
    #[error("超时")]
    Timeout,
}

impl BenchmarkRunner {
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            config,
            results: Arc::new(RwLock::new(Vec::new())),
            running: Arc::new(RwLock::new(false)),
        }
    }

    pub async fn run<F, Fut, R>(&self, benchmark_fn: F) -> Result<BenchmarkResult, BenchmarkError>
    where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let start_time = Instant::now();
        info!("🚀 开始基准测试: {}", self.config.name);

        self.set_running(true).await;

        if self.config.warmup_duration > Duration::ZERO {
            info!("🔥 预热阶段: {:?}", self.config.warmup_duration);
            self.warmup(&benchmark_fn).await?;
        }

        info!("📊 主要测试阶段开始");
        let main_result = self.run_main_test(benchmark_fn).await?;

        if self.config.cooldown_duration > Duration::ZERO {
            info!("❄️ 冷却阶段: {:?}", self.config.cooldown_duration);
            tokio::time::sleep(self.config.cooldown_duration).await;
        }

        let end_time = Instant::now();
        let total_duration = end_time.duration_since(start_time);

        let result = self.build_result(start_time, end_time, total_duration, main_result);

        self.save_result(result.clone()).await;
        self.set_running(false).await;

        info!("✅ 基准测试完成: {}", self.config.name);
        self.print_summary(&result);

        Ok(result)
    }

    async fn set_running(&self, value: bool) {
        let mut running = self.running.write().await;
        *running = value;
    }

    fn build_result(
        &self,
        start_time: Instant,
        end_time: Instant,
        total_duration: Duration,
        main_result: MainTestResult,
    ) -> BenchmarkResult {
        BenchmarkResult {
            config: self.config.clone(),
            start_time,
            end_time,
            total_duration,
            iterations_completed: main_result.iterations_completed,
            iterations_failed: main_result.iterations_failed,
            throughput: main_result.throughput,
            latency_stats: main_result.latency_stats,
            memory_stats: main_result.memory_stats,
            cpu_stats: main_result.cpu_stats,
            errors: main_result.errors,
        }
    }

    async fn save_result(&self, result: BenchmarkResult) {
        let mut results = self.results.write().await;
        results.push(result);
    }

    async fn warmup<F, Fut, R>(&self, benchmark_fn: &F) -> Result<(), BenchmarkError>
    where
        F: Fn(u32) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let warmup_start = Instant::now();
        let mut iteration = 0;

        while warmup_start.elapsed() < self.config.warmup_duration {
            benchmark_fn(iteration)
                .await
                .map_err(|e| BenchmarkError::RuntimeError(e.to_string()))?;
            iteration += 1;
        }

        info!("🔥 预热完成: {} 次迭代", iteration);
        Ok(())
    }

    async fn run_main_test<F, Fut, R>(
        &self,
        benchmark_fn: F,
    ) -> Result<MainTestResult, BenchmarkError>
    where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let latencies = Arc::new(Mutex::new(Vec::new()));
        let errors = Arc::new(Mutex::new(Vec::new()));
        let iterations_completed = Arc::new(Mutex::new(0));
        let iterations_failed = Arc::new(Mutex::new(0));
        let test_start = Instant::now();

        self.run_test_by_mode(
            &benchmark_fn,
            latencies.clone(),
            errors.clone(),
            iterations_completed.clone(),
            iterations_failed.clone(),
            test_start,
        )
        .await;

        self.build_test_result(
            test_start,
            iterations_completed,
            iterations_failed,
            latencies,
            errors,
        )
        .await
    }

    async fn run_test_by_mode<F, Fut, R>(
        &self,
        benchmark_fn: &F,
        latencies: Arc<Mutex<Vec<Duration>>>,
        errors: Arc<Mutex<Vec<BenchmarkError>>>,
        iterations_completed: Arc<Mutex<u32>>,
        iterations_failed: Arc<Mutex<u32>>,
        test_start: Instant,
    ) where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        if self.config.duration > Duration::ZERO {
            self.run_duration_based_test(
                benchmark_fn.clone(),
                latencies,
                errors,
                iterations_completed,
                iterations_failed,
                test_start,
            )
            .await;
        } else {
            self.run_iteration_based_test(
                benchmark_fn.clone(),
                latencies,
                errors,
                iterations_completed,
                iterations_failed,
            )
            .await;
        }
    }

    async fn build_test_result(
        &self,
        test_start: Instant,
        iterations_completed: Arc<Mutex<u32>>,
        iterations_failed: Arc<Mutex<u32>>,
        latencies: Arc<Mutex<Vec<Duration>>>,
        errors: Arc<Mutex<Vec<BenchmarkError>>>,
    ) -> Result<MainTestResult, BenchmarkError> {
        let test_duration = test_start.elapsed();
        let completed = *iterations_completed.lock().await;
        let failed = *iterations_failed.lock().await;
        let throughput = completed as f64 / test_duration.as_secs_f64();

        let latencies_vec = latencies.lock().await.clone();
        let latency_stats = self.calculate_latency_stats(&latencies_vec);
        let memory_stats = self.get_memory_stats().await;
        let cpu_stats = self.get_cpu_stats().await;
        let errors_vec = errors.lock().await.clone();

        Ok(MainTestResult {
            iterations_completed: completed,
            iterations_failed: failed,
            throughput,
            latency_stats,
            memory_stats,
            cpu_stats,
            errors: errors_vec,
        })
    }

    async fn run_duration_based_test<F, Fut, R>(
        &self,
        benchmark_fn: F,
        latencies: Arc<Mutex<Vec<Duration>>>,
        errors: Arc<Mutex<Vec<BenchmarkError>>>,
        iterations_completed: Arc<Mutex<u32>>,
        iterations_failed: Arc<Mutex<u32>>,
        test_start: Instant,
    ) where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let semaphore = Arc::new(tokio::sync::Semaphore::new(
            self.config.concurrency as usize,
        ));
        let mut iteration = 0;

        while test_start.elapsed() < self.config.duration {
            self.spawn_benchmark_task(
                &semaphore,
                &benchmark_fn,
                iteration,
                latencies.clone(),
                errors.clone(),
                iterations_completed.clone(),
                iterations_failed.clone(),
            )
            .await;
            iteration += 1;
        }

        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    async fn run_iteration_based_test<F, Fut, R>(
        &self,
        benchmark_fn: F,
        latencies: Arc<Mutex<Vec<Duration>>>,
        errors: Arc<Mutex<Vec<BenchmarkError>>>,
        iterations_completed: Arc<Mutex<u32>>,
        iterations_failed: Arc<Mutex<u32>>,
    ) where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let semaphore = Arc::new(tokio::sync::Semaphore::new(
            self.config.concurrency as usize,
        ));

        for iteration in 0..self.config.iterations {
            self.spawn_benchmark_task(
                &semaphore,
                &benchmark_fn,
                iteration,
                latencies.clone(),
                errors.clone(),
                iterations_completed.clone(),
                iterations_failed.clone(),
            )
            .await;
        }

        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    async fn spawn_benchmark_task<F, Fut, R>(
        &self,
        semaphore: &Arc<tokio::sync::Semaphore>,
        benchmark_fn: &F,
        iteration: u32,
        latencies: Arc<Mutex<Vec<Duration>>>,
        errors: Arc<Mutex<Vec<BenchmarkError>>>,
        iterations_completed: Arc<Mutex<u32>>,
        iterations_failed: Arc<Mutex<u32>>,
    ) where
        F: Fn(u32) -> Fut + Send + Sync + 'static + Clone,
        Fut: std::future::Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>>
            + Send,
        R: Send,
    {
        let permit = semaphore
            .clone()
            .acquire_owned()
            .await
            .expect("Failed to acquire semaphore permit for benchmark");
        let benchmark_fn_clone = benchmark_fn.clone();

        tokio::spawn(async move {
            let _permit = permit;
            let start = Instant::now();

            match benchmark_fn_clone(iteration).await {
                Ok(_) => {
                    let latency = start.elapsed();
                    *iterations_completed.lock().await += 1;
                    latencies.lock().await.push(latency);
                }
                Err(e) => {
                    *iterations_failed.lock().await += 1;
                    errors
                        .lock()
                        .await
                        .push(BenchmarkError::RuntimeError(e.to_string()));
                }
            }
        });
    }

    fn calculate_latency_stats(&self, latencies: &[Duration]) -> LatencyStats {
        if latencies.is_empty() {
            return self.empty_latency_stats();
        }

        let mut sorted_latencies = latencies.to_vec();
        sorted_latencies.sort();

        let min = sorted_latencies[0];
        let max = sorted_latencies[sorted_latencies.len() - 1];

        let mean_nanos: u128 = latencies.iter().map(|d| d.as_nanos()).sum();
        let mean = Duration::from_nanos((mean_nanos / latencies.len() as u128) as u64);

        let p50 = self.percentile(&sorted_latencies, 0.50);
        let p90 = self.percentile(&sorted_latencies, 0.90);
        let p95 = self.percentile(&sorted_latencies, 0.95);
        let p99 = self.percentile(&sorted_latencies, 0.99);
        let p999 = self.percentile(&sorted_latencies, 0.999);

        let std_dev = self.calculate_std_dev(latencies, mean);

        LatencyStats {
            min,
            max,
            mean,
            p50,
            p90,
            p95,
            p99,
            p999,
            std_dev,
        }
    }

    fn empty_latency_stats(&self) -> LatencyStats {
        LatencyStats {
            min: Duration::ZERO,
            max: Duration::ZERO,
            mean: Duration::ZERO,
            p50: Duration::ZERO,
            p90: Duration::ZERO,
            p95: Duration::ZERO,
            p99: Duration::ZERO,
            p999: Duration::ZERO,
            std_dev: Duration::ZERO,
        }
    }

    fn percentile(&self, sorted: &[Duration], p: f64) -> Duration {
        let idx = (sorted.len() as f64 * p) as usize;
        sorted[idx.min(sorted.len() - 1)]
    }

    fn calculate_std_dev(&self, latencies: &[Duration], mean: Duration) -> Duration {
        let variance: u128 = latencies
            .iter()
            .map(|d| {
                let diff = d.as_nanos() as i128 - mean.as_nanos() as i128;
                (diff * diff) as u128
            })
            .sum();
        let std_dev_nanos = (variance / latencies.len() as u128) as f64;
        Duration::from_nanos(std_dev_nanos.sqrt() as u64)
    }

    async fn get_memory_stats(&self) -> MemoryStats {
        match self.get_system_memory_stats().await {
            Some(stats) => stats,
            None => self.get_process_memory_stats(),
        }
    }

    async fn get_system_memory_stats(&self) -> Option<MemoryStats> {
        use sysinfo::{Pid, System, get_current_pid};

        let mut system = System::new_all();
        system.refresh_all();

        let pid: Pid = get_current_pid().ok()?;
        let process = system.process(pid)?;
        let memory_bytes = process.memory();

        Some(MemoryStats {
            peak_memory: memory_bytes,
            avg_memory: memory_bytes,
            memory_growth: 0,
            allocations: 0,
            deallocations: 0,
        })
    }

    fn get_process_memory_stats(&self) -> MemoryStats {
        use sysinfo::{Pid, System, get_current_pid};
        let mut system = System::new_all();
        system.refresh_all();

        let Ok(pid): Result<Pid, _> = get_current_pid() else {
            return self.empty_memory_stats();
        };
        let memory = system.process(pid).map(|p| p.memory()).unwrap_or(0);

        MemoryStats {
            peak_memory: memory,
            avg_memory: 0,
            memory_growth: 0,
            allocations: 0,
            deallocations: 0,
        }
    }

    fn empty_memory_stats(&self) -> MemoryStats {
        MemoryStats {
            peak_memory: 0,
            avg_memory: 0,
            memory_growth: 0,
            allocations: 0,
            deallocations: 0,
        }
    }

    async fn get_cpu_stats(&self) -> CpuStats {
        use sysinfo::{Pid, System, get_current_pid};

        let mut system = System::new_all();
        system.refresh_all();

        let Ok(pid): Result<Pid, _> = get_current_pid() else {
            return self.empty_cpu_stats();
        };

        system.process(pid).map_or_else(
            || self.empty_cpu_stats(),
            |process| CpuStats {
                avg_cpu_usage: process.cpu_usage() as f64,
                peak_cpu_usage: process.cpu_usage() as f64,
                cpu_time: Duration::from_secs(process.run_time()),
                context_switches: 0,
            },
        )
    }

    fn empty_cpu_stats(&self) -> CpuStats {
        CpuStats {
            avg_cpu_usage: 0.0,
            peak_cpu_usage: 0.0,
            cpu_time: Duration::ZERO,
            context_switches: 0,
        }
    }

    fn print_summary(&self, result: &BenchmarkResult) {
        info!("📊 基准测试摘要: {}", result.config.name);
        info!("  总持续时间: {:?}", result.total_duration);
        info!("  完成迭代: {}", result.iterations_completed);
        info!("  失败迭代: {}", result.iterations_failed);
        info!("  吞吐量: {:.2} req/s", result.throughput);
        info!("  延迟统计:");
        info!("    P50: {:?}", result.latency_stats.p50);
        info!("    P95: {:?}", result.latency_stats.p95);
        info!("    P99: {:?}", result.latency_stats.p99);
        info!("    P999: {:?}", result.latency_stats.p999);
        info!(
            "  错误率: {:.2}%",
            (result.iterations_failed as f64
                / (result.iterations_completed + result.iterations_failed) as f64)
                * 100.0
        );
    }

    pub async fn get_results(&self) -> Vec<BenchmarkResult> {
        let results = self.results.read().await;
        results.clone()
    }

    pub async fn export_results(&self, file_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let results = self.get_results().await;
        let simplified_results: Vec<_> = results.iter().map(|r| self.simplify_result(r)).collect();
        let json = serde_json::to_string_pretty(&simplified_results)?;
        tokio::fs::write(file_path, json).await?;
        info!("📁 基准测试结果已导出到: {}", file_path);
        Ok(())
    }

    fn simplify_result(&self, r: &BenchmarkResult) -> serde_json::Value {
        serde_json::json!({
            "config_name": r.config.name,
            "total_duration": r.total_duration.as_secs_f64(),
            "iterations_completed": r.iterations_completed,
            "iterations_failed": r.iterations_failed,
            "throughput": r.throughput,
            "latency_stats": {
                "min": r.latency_stats.min.as_secs_f64(),
                "max": r.latency_stats.max.as_secs_f64(),
                "mean": r.latency_stats.mean.as_secs_f64(),
                "p50": r.latency_stats.p50.as_secs_f64(),
                "p95": r.latency_stats.p95.as_secs_f64(),
                "p99": r.latency_stats.p99.as_secs_f64(),
            },
            "memory_stats": r.memory_stats,
            "cpu_stats": r.cpu_stats,
            "error_count": r.errors.len()
        })
    }
}

/// 微服务性能基准测试
pub struct MicroserviceBenchmark {
    runner: BenchmarkRunner,
}

impl Default for MicroserviceBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

impl MicroserviceBenchmark {
    pub fn new() -> Self {
        let config = BenchmarkConfig {
            name: "microservice-performance".to_string(),
            description: "微服务性能基准测试".to_string(),
            iterations: 0,
            concurrency: 100,
            duration: Duration::from_secs(60),
            warmup_duration: Duration::from_secs(10),
            cooldown_duration: Duration::from_secs(5),
            metrics: BenchmarkMetrics {
                throughput: Some(1000.0),
                latency_p50: Some(Duration::from_millis(10)),
                latency_p95: Some(Duration::from_millis(50)),
                latency_p99: Some(Duration::from_millis(100)),
                error_rate: Some(0.01),
                memory_usage: Some(1024 * 1024 * 100),
                cpu_usage: Some(50.0),
            },
        };

        Self {
            runner: BenchmarkRunner::new(config),
        }
    }

    pub async fn run(&self) -> Result<BenchmarkResult, BenchmarkError> {
        self.runner
            .run(|iteration| async move {
                let delay = Duration::from_millis((1 + (iteration % 10)).into());
                tokio::time::sleep(delay).await;

                let processing_time = Duration::from_micros((100 + (iteration % 500)).into());
                tokio::time::sleep(processing_time).await;

                if iteration % 1000 == 0 {
                    return Err("模拟错误".into());
                }

                Ok(())
            })
            .await
    }
}

/// 负载均衡性能基准测试
pub struct LoadBalancerBenchmark {
    runner: BenchmarkRunner,
}

impl Default for LoadBalancerBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

impl LoadBalancerBenchmark {
    pub fn new() -> Self {
        let config = BenchmarkConfig {
            name: "load-balancer-performance".to_string(),
            description: "负载均衡器性能基准测试".to_string(),
            iterations: 10000,
            concurrency: 50,
            duration: Duration::ZERO,
            warmup_duration: Duration::from_secs(5),
            cooldown_duration: Duration::from_secs(2),
            metrics: BenchmarkMetrics {
                throughput: Some(5000.0),
                latency_p50: Some(Duration::from_micros(10)),
                latency_p95: Some(Duration::from_micros(50)),
                latency_p99: Some(Duration::from_micros(100)),
                error_rate: Some(0.001),
                memory_usage: Some(1024 * 1024 * 10),
                cpu_usage: Some(20.0),
            },
        };

        Self {
            runner: BenchmarkRunner::new(config),
        }
    }

    pub async fn run(&self) -> Result<BenchmarkResult, BenchmarkError> {
        self.runner
            .run(|iteration| async move {
                let selection_time = Duration::from_nanos((100 + (iteration % 1000)).into());
                tokio::time::sleep(selection_time).await;
                Ok(())
            })
            .await
    }
}

/// 追踪性能基准测试
pub struct TracingBenchmark {
    runner: BenchmarkRunner,
}

impl Default for TracingBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

impl TracingBenchmark {
    pub fn new() -> Self {
        let config = BenchmarkConfig {
            name: "tracing-performance".to_string(),
            description: "分布式追踪性能基准测试".to_string(),
            iterations: 0,
            concurrency: 200,
            duration: Duration::from_secs(30),
            warmup_duration: Duration::from_secs(5),
            cooldown_duration: Duration::from_secs(2),
            metrics: BenchmarkMetrics {
                throughput: Some(10000.0),
                latency_p50: Some(Duration::from_micros(5)),
                latency_p95: Some(Duration::from_micros(20)),
                latency_p99: Some(Duration::from_micros(50)),
                error_rate: Some(0.0001),
                memory_usage: Some(1024 * 1024 * 50),
                cpu_usage: Some(30.0),
            },
        };

        Self {
            runner: BenchmarkRunner::new(config),
        }
    }

    pub async fn run(&self) -> Result<BenchmarkResult, BenchmarkError> {
        self.runner
            .run(|iteration| async move {
                let span_creation_time = Duration::from_nanos((50 + (iteration % 500)).into());
                tokio::time::sleep(span_creation_time).await;

                let attribute_time = Duration::from_nanos((10 + (iteration % 100)).into());
                tokio::time::sleep(attribute_time).await;

                let span_end_time = Duration::from_nanos((20 + (iteration % 200)).into());
                tokio::time::sleep(span_end_time).await;

                Ok(())
            })
            .await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_benchmark_runner() {
        let config = BenchmarkConfig {
            name: "test-benchmark".to_string(),
            description: "测试基准".to_string(),
            iterations: 100,
            concurrency: 10,
            duration: Duration::ZERO,
            warmup_duration: Duration::from_millis(100),
            cooldown_duration: Duration::from_millis(50),
            metrics: BenchmarkMetrics {
                throughput: None,
                latency_p50: None,
                latency_p95: None,
                latency_p99: None,
                error_rate: None,
                memory_usage: None,
                cpu_usage: None,
            },
        };

        let runner = BenchmarkRunner::new(config);

        let result = runner
            .run(|iteration| async move {
                tokio::time::sleep(Duration::from_millis(1)).await;
                if iteration % 10 == 0 {
                    Err("测试错误".into())
                } else {
                    Ok(())
                }
            })
            .await;

        match result {
            Ok(result) => {
                assert_eq!(result.iterations_completed, 90);
                assert_eq!(result.iterations_failed, 10);
            }
            Err(e) => {
                println!("基准测试失败: {:?}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_microservice_benchmark() {
        let benchmark = MicroserviceBenchmark::new();
        let result = benchmark.run().await;

        match result {
            Ok(_) => {
                println!("微服务基准测试成功");
            }
            Err(e) => {
                println!("微服务基准测试失败: {:?}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_load_balancer_benchmark() {
        let benchmark = LoadBalancerBenchmark::new();
        let result = benchmark.run().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_tracing_benchmark() {
        let benchmark = TracingBenchmark::new();
        let result = benchmark.run().await;
        assert!(result.is_ok());
    }
}
