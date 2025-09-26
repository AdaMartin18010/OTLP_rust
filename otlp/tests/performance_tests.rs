//! 性能测试模块

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::time::sleep;
use otlp::performance::*;

/// 性能测试配置
#[derive(Debug, Clone)]
pub struct PerformanceTestConfig {
    pub concurrent_tasks: usize,
    pub batch_size: usize,
    pub memory_limit: usize,
}

impl Default for PerformanceTestConfig {
    fn default() -> Self {
        Self {
            concurrent_tasks: 100,
            batch_size: 1000,
            memory_limit: 100 * 1024 * 1024,
        }
    }
}

/// 性能测试结果
#[derive(Debug, Clone)]
pub struct PerformanceTestResult {
    pub test_name: String,
    pub duration: Duration,
    pub throughput: f64,
    pub success_rate: f64,
    pub average_latency: Duration,
}

/// 性能测试套件
pub struct PerformanceTestSuite {
    config: PerformanceTestConfig,
    results: Vec<PerformanceTestResult>,
}

impl PerformanceTestSuite {
    pub fn new(config: PerformanceTestConfig) -> Self {
        Self {
            config,
            results: Vec::new(),
        }
    }

    pub async fn run_all_tests(&mut self) -> Vec<PerformanceTestResult> {
        println!("开始运行性能测试套件...");
        
        self.run_circuit_breaker_test().await;
        self.run_memory_pool_test().await;
        self.run_batch_processor_test().await;
        self.run_connection_pool_test().await;
        
        println!("性能测试套件完成，共运行 {} 个测试", self.results.len());
        self.results.clone()
    }

    async fn run_circuit_breaker_test(&mut self) {
        println!("运行熔断器性能测试...");
        
        let start_time = Instant::now();
        let config = CircuitBreakerConfig {
            failure_threshold: 10,
            recovery_timeout: Duration::from_millis(100),
            half_open_max_calls: 5,
            sliding_window_size: Duration::from_secs(60),
            minimum_calls: 10,
        };
        
        let circuit_breaker = OptimizedCircuitBreaker::new(config).unwrap();
        let success_count = Arc::new(AtomicUsize::new(0));
        let error_count = Arc::new(AtomicUsize::new(0));
        let latency_sum = Arc::new(AtomicUsize::new(0));
        
        let mut handles = Vec::new();
        for i in 0..self.config.concurrent_tasks {
            let cb = circuit_breaker.clone();
            let success_count = Arc::clone(&success_count);
            let error_count = Arc::clone(&error_count);
            let latency_sum = Arc::clone(&latency_sum);
            
            let handle = tokio::spawn(async move {
                let request_start = Instant::now();
                
                match cb.call(|| async {
                    if i % 10 == 0 {
                        Err(anyhow::anyhow!("模拟错误"))
                    } else {
                        Ok("成功".to_string())
                    }
                }).await {
                    Ok(_) => {
                        success_count.fetch_add(1, Ordering::AcqRel);
                        let latency = request_start.elapsed();
                        latency_sum.fetch_add(latency.as_micros() as usize, Ordering::AcqRel);
                    }
                    Err(_) => {
                        error_count.fetch_add(1, Ordering::AcqRel);
                    }
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        let duration = start_time.elapsed();
        let total_requests = success_count.load(Ordering::Acquire) + error_count.load(Ordering::Acquire);
        let throughput = total_requests as f64 / duration.as_secs_f64();
        let success_rate = success_count.load(Ordering::Acquire) as f64 / total_requests as f64;
        let average_latency = Duration::from_micros(
            latency_sum.load(Ordering::Acquire) as u64 / total_requests as u64
        );
        
        let result = PerformanceTestResult {
            test_name: "熔断器性能测试".to_string(),
            duration,
            throughput,
            success_rate,
            average_latency,
        };
        
        self.results.push(result);
        println!("熔断器性能测试完成: 吞吐量 {:.2} req/s, 成功率 {:.2}%", 
                throughput, success_rate * 100.0);
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn run_memory_pool_test(&mut self) {
        println!("运行内存池性能测试...");
        
        let start_time = Instant::now();
        let config = MemoryPoolConfig {
            max_size: 100,
            initial_size: 10,
            object_ttl: Duration::from_secs(300),
            cleanup_interval: Duration::from_secs(60),
            enable_stats: true,
        };
        
        let memory_pool = OptimizedMemoryPool::new(
            || String::with_capacity(1024),
            config,
        ).await.unwrap();
        
        let success_count = Arc::new(AtomicUsize::new(0));
        let error_count = Arc::new(AtomicUsize::new(0));
        let latency_sum = Arc::new(AtomicUsize::new(0));
        
        let mut handles = Vec::new();
        for i in 0..self.config.concurrent_tasks {
            let mp = memory_pool.clone();
            let success_count = Arc::clone(&success_count);
            let error_count = Arc::clone(&error_count);
            let latency_sum = Arc::clone(&latency_sum);
            
            let handle = tokio::spawn(async move {
                let request_start = Instant::now();
                
                match mp.acquire().await {
                    Ok(obj) => {
                        success_count.fetch_add(1, Ordering::AcqRel);
                        let latency = request_start.elapsed();
                        latency_sum.fetch_add(latency.as_micros() as usize, Ordering::AcqRel);
                        sleep(Duration::from_millis(1)).await;
                        drop(obj);
                    }
                    Err(_) => {
                        error_count.fetch_add(1, Ordering::AcqRel);
                    }
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        let duration = start_time.elapsed();
        let total_requests = success_count.load(Ordering::Acquire) + error_count.load(Ordering::Acquire);
        let throughput = total_requests as f64 / duration.as_secs_f64();
        let success_rate = success_count.load(Ordering::Acquire) as f64 / total_requests as f64;
        let average_latency = Duration::from_micros(
            latency_sum.load(Ordering::Acquire) as u64 / total_requests as u64
        );
        
        let result = PerformanceTestResult {
            test_name: "内存池性能测试".to_string(),
            duration,
            throughput,
            success_rate,
            average_latency,
        };
        
        self.results.push(result);
        println!("内存池性能测试完成: 吞吐量 {:.2} req/s, 成功率 {:.2}%", 
                throughput, success_rate * 100.0);
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn run_batch_processor_test(&mut self) {
        println!("运行批处理器性能测试...");
        
        let start_time = Instant::now();
        let config = BatchProcessorConfig {
            max_batch_size: self.config.batch_size,
            min_batch_size: 10,
            batch_timeout: Duration::from_millis(100),
            max_wait_time: Duration::from_secs(5),
            concurrency: 4,
            enable_compression: true,
            enable_stats: true,
            memory_limit: self.config.memory_limit,
        };
        
        let batch_processor = OptimizedBatchProcessor::new(
            |items| {
                Ok(BatchResult {
                    items,
                    processing_time: Duration::from_millis(10),
                    compressed_size: Some(512),
                    original_size: 1024,
                })
            },
            config,
        ).unwrap();
        
        let success_count = Arc::new(AtomicUsize::new(0));
        let error_count = Arc::new(AtomicUsize::new(0));
        let latency_sum = Arc::new(AtomicUsize::new(0));
        
        let mut handles = Vec::new();
        for i in 0..self.config.concurrent_tasks {
            let bp = batch_processor.clone();
            let success_count = Arc::clone(&success_count);
            let error_count = Arc::clone(&error_count);
            let latency_sum = Arc::clone(&latency_sum);
            
            let handle = tokio::spawn(async move {
                let request_start = Instant::now();
                
                match bp.add_normal_priority(format!("item_{}", i), 100).await {
                    Ok(_) => {
                        success_count.fetch_add(1, Ordering::AcqRel);
                        let latency = request_start.elapsed();
                        latency_sum.fetch_add(latency.as_micros() as usize, Ordering::AcqRel);
                    }
                    Err(_) => {
                        error_count.fetch_add(1, Ordering::AcqRel);
                    }
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        sleep(Duration::from_millis(200)).await;
        
        let duration = start_time.elapsed();
        let total_requests = success_count.load(Ordering::Acquire) + error_count.load(Ordering::Acquire);
        let throughput = total_requests as f64 / duration.as_secs_f64();
        let success_rate = success_count.load(Ordering::Acquire) as f64 / total_requests as f64;
        let average_latency = Duration::from_micros(
            latency_sum.load(Ordering::Acquire) as u64 / total_requests as u64
        );
        
        let result = PerformanceTestResult {
            test_name: "批处理器性能测试".to_string(),
            duration,
            throughput,
            success_rate,
            average_latency,
        };
        
        self.results.push(result);
        println!("批处理器性能测试完成: 吞吐量 {:.2} req/s, 成功率 {:.2}%", 
                throughput, success_rate * 100.0);
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn run_connection_pool_test(&mut self) {
        println!("运行连接池性能测试...");
        
        let start_time = Instant::now();
        let config = ConnectionPoolConfig {
            max_connections: 50,
            min_connections: 5,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(300),
            max_lifetime: Duration::from_secs(3600),
            health_check_interval: Duration::from_secs(60),
            enable_stats: true,
            enable_connection_reuse: true,
        };
        
        let connection_pool = OptimizedConnectionPool::new(
            || Ok(format!("connection_{}", Instant::now().elapsed().as_micros())),
            config,
        ).unwrap();
        
        let success_count = Arc::new(AtomicUsize::new(0));
        let error_count = Arc::new(AtomicUsize::new(0));
        let latency_sum = Arc::new(AtomicUsize::new(0));
        
        let mut handles = Vec::new();
        for i in 0..self.config.concurrent_tasks {
            let cp = connection_pool.clone();
            let success_count = Arc::clone(&success_count);
            let error_count = Arc::clone(&error_count);
            let latency_sum = Arc::clone(&latency_sum);
            
            let handle = tokio::spawn(async move {
                let request_start = Instant::now();
                
                match cp.acquire().await {
                    Ok(conn) => {
                        success_count.fetch_add(1, Ordering::AcqRel);
                        let latency = request_start.elapsed();
                        latency_sum.fetch_add(latency.as_micros() as usize, Ordering::AcqRel);
                        sleep(Duration::from_millis(1)).await;
                        drop(conn);
                    }
                    Err(_) => {
                        error_count.fetch_add(1, Ordering::AcqRel);
                    }
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        let duration = start_time.elapsed();
        let total_requests = success_count.load(Ordering::Acquire) + error_count.load(Ordering::Acquire);
        let throughput = total_requests as f64 / duration.as_secs_f64();
        let success_rate = success_count.load(Ordering::Acquire) as f64 / total_requests as f64;
        let average_latency = Duration::from_micros(
            latency_sum.load(Ordering::Acquire) as u64 / total_requests as u64
        );
        
        let result = PerformanceTestResult {
            test_name: "连接池性能测试".to_string(),
            duration,
            throughput,
            success_rate,
            average_latency,
        };
        
        self.results.push(result);
        println!("连接池性能测试完成: 吞吐量 {:.2} req/s, 成功率 {:.2}%", 
                throughput, success_rate * 100.0);
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("# 性能测试报告\n\n");
        report.push_str("## 测试概览\n\n");
        report.push_str(&format!("- 测试数量: {}\n", self.results.len()));
        report.push_str(&format!("- 测试配置: 并发任务 {}, 批大小 {}, 内存限制 {}MB\n\n", 
                self.config.concurrent_tasks, 
                self.config.batch_size, 
                self.config.memory_limit / 1024 / 1024));
        
        report.push_str("## 详细结果\n\n");
        for result in &self.results {
            report.push_str(&format!("### {}\n\n", result.test_name));
            report.push_str(&format!("- **持续时间**: {:?}\n", result.duration));
            report.push_str(&format!("- **吞吐量**: {:.2} req/s\n", result.throughput));
            report.push_str(&format!("- **成功率**: {:.2}%\n", result.success_rate * 100.0));
            report.push_str(&format!("- **平均延迟**: {:?}\n\n", result.average_latency));
        }
        
        report.push_str("## 性能分析\n\n");
        
        let avg_throughput: f64 = self.results.iter().map(|r| r.throughput).sum::<f64>() / self.results.len() as f64;
        let avg_success_rate: f64 = self.results.iter().map(|r| r.success_rate).sum::<f64>() / self.results.len() as f64;
        
        report.push_str(&format!("- **平均吞吐量**: {:.2} req/s\n", avg_throughput));
        report.push_str(&format!("- **平均成功率**: {:.2}%\n", avg_success_rate * 100.0));
        
        report.push_str("\n## 结论\n\n");
        if avg_success_rate > 0.95 {
            report.push_str("✅ 所有性能测试均通过，系统性能良好。\n");
        } else if avg_success_rate > 0.90 {
            report.push_str("⚠️ 性能测试基本通过，但存在少量错误，建议优化。\n");
        } else {
            report.push_str("❌ 性能测试未通过，存在较多错误，需要重点优化。\n");
        }
        
        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_performance_test_suite() {
        let config = PerformanceTestConfig {
            concurrent_tasks: 50,
            batch_size: 100,
            memory_limit: 10 * 1024 * 1024,
        };
        
        let mut test_suite = PerformanceTestSuite::new(config);
        let results = test_suite.run_all_tests().await;
        
        assert!(!results.is_empty());
        assert!(results.len() >= 4);
        
        for result in &results {
            assert!(result.throughput > 0.0);
            assert!(result.success_rate >= 0.0);
            assert!(result.success_rate <= 1.0);
            assert!(result.duration > Duration::from_millis(0));
        }
        
        let report = test_suite.generate_report();
        assert!(!report.is_empty());
        assert!(report.contains("性能测试报告"));
    }
}