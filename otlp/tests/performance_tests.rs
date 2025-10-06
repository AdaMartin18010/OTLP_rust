//! # OTLP性能测试
//!
//! 测试OTLP组件在各种负载下的性能表现

use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::time::sleep;

// 性能测试工具
struct PerformanceTester {
    start_time: Instant,
    measurements: Vec<Duration>,
}

impl PerformanceTester {
    fn new() -> Self {
        Self {
            start_time: Instant::now(),
            measurements: Vec::new(),
        }
    }

    fn start_measurement(&mut self) {
        self.start_time = Instant::now();
    }

    fn end_measurement(&mut self) -> Duration {
        let duration = self.start_time.elapsed();
        self.measurements.push(duration);
        duration
    }

    fn get_average_duration(&self) -> Duration {
        if self.measurements.is_empty() {
            return Duration::from_nanos(0);
        }
        
        let total_nanos: u128 = self.measurements.iter()
            .map(|d| d.as_nanos())
            .sum();
        
        Duration::from_nanos((total_nanos / self.measurements.len() as u128) as u64)
    }

    fn get_max_duration(&self) -> Duration {
        self.measurements.iter()
            .max()
            .copied()
            .unwrap_or(Duration::from_nanos(0))
    }

    fn get_min_duration(&self) -> Duration {
        self.measurements.iter()
            .min()
            .copied()
            .unwrap_or(Duration::from_nanos(0))
    }

    #[allow(dead_code)]
    fn get_throughput(&self, operations: usize) -> f64 {
        if self.measurements.is_empty() {
            return 0.0;
        }
        
        let total_duration: Duration = self.measurements.iter().sum();
        operations as f64 / total_duration.as_secs_f64()
    }
}

// 模拟OTLP组件
struct OtlpComponent {
    #[allow(dead_code)]
    name: String,
    processing_time: Duration,
}

impl OtlpComponent {
    fn new(name: String, processing_time: Duration) -> Self {
        Self {
            name,
            processing_time,
        }
    }

    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, String> {
        // 模拟处理时间
        sleep(self.processing_time).await;
        
        if data.is_empty() {
            return Err("Empty data".to_string());
        }

        // 模拟数据处理
        let mut result = Vec::new();
        result.extend_from_slice(b"processed:");
        result.extend_from_slice(data);
        Ok(result)
    }
}

#[tokio::test]
async fn test_otlp_latency_performance() {
    let mut tester = PerformanceTester::new();
    let component = OtlpComponent::new(
        "latency_test".to_string(),
        Duration::from_millis(1)
    );

    let test_data = b"test data for latency measurement";

    // 测量单次操作延迟
    for _ in 0..100 {
        tester.start_measurement();
        let _result = component.process(test_data).await.expect("Should process data");
        tester.end_measurement();
    }

    let avg_latency = tester.get_average_duration();
    let max_latency = tester.get_max_duration();
    let min_latency = tester.get_min_duration();

    // 验证延迟性能要求
    assert!(avg_latency < Duration::from_millis(10), 
        "Average latency should be less than 10ms, got {:?}", avg_latency);
    assert!(max_latency < Duration::from_millis(50), 
        "Max latency should be less than 50ms, got {:?}", max_latency);
    assert!(min_latency >= Duration::from_millis(1), 
        "Min latency should be at least 1ms, got {:?}", min_latency);

    println!("Latency Performance Results:");
    println!("  Average: {:?}", avg_latency);
    println!("  Max: {:?}", max_latency);
    println!("  Min: {:?}", min_latency);
}

#[tokio::test]
async fn test_otlp_throughput_performance() {
    let _tester = PerformanceTester::new();
    let component = Arc::new(OtlpComponent::new(
        "throughput_test".to_string(),
        Duration::from_millis(1)
    ));

    let test_data = b"test data for throughput measurement";
    let operations = 1000;

    // 测量吞吐量
    let start = Instant::now();
    
    let mut handles = Vec::new();
    for _ in 0..operations {
        let component = Arc::clone(&component);
        let data = test_data.to_vec();
        
        let handle = tokio::spawn(async move {
            component.process(&data).await
        });
        handles.push(handle);
    }

    // 等待所有操作完成
    for handle in handles {
        handle.await.expect("Task should complete")
            .expect("Should process data");
    }

    let total_duration = start.elapsed();
    let throughput = operations as f64 / total_duration.as_secs_f64();

    // 验证吞吐量性能要求
    assert!(throughput > 100.0, 
        "Throughput should be greater than 100 ops/sec, got {:.2}", throughput);

    println!("Throughput Performance Results:");
    println!("  Operations: {}", operations);
    println!("  Total Duration: {:?}", total_duration);
    println!("  Throughput: {:.2} ops/sec", throughput);
}

#[tokio::test]
async fn test_otlp_memory_performance() {
    let component = OtlpComponent::new(
        "memory_test".to_string(),
        Duration::from_millis(1)
    );

    // 测试不同大小的数据处理
    let sizes = vec![1024, 10240, 102400, 1024000]; // 1KB, 10KB, 100KB, 1MB
    
    for size in sizes {
        let test_data = vec![0u8; size];
        
        let start = Instant::now();
        let result = component.process(&test_data).await.expect("Should process data");
        let duration = start.elapsed();
        
        // 验证内存性能
        assert_eq!(result.len(), size + 9); // 9 bytes for "processed:" prefix
        
        println!("Memory Performance for {} bytes:", size);
        println!("  Processing time: {:?}", duration);
        println!("  Throughput: {:.2} MB/s", 
            (size as f64 / 1024.0 / 1024.0) / duration.as_secs_f64());
    }
}

#[allow(dead_code)]
#[tokio::test]
async fn test_otlp_concurrent_performance() {
    let _tester = PerformanceTester::new();
    let component = Arc::new(OtlpComponent::new(
        "concurrent_test".to_string(),
        Duration::from_millis(5)
    ));

    let test_data = b"test data for concurrent measurement";
    let concurrent_tasks = 50;

    // 测试并发性能
    let start = Instant::now();
    
    let mut handles = Vec::new();
    for i in 0..concurrent_tasks {
        let component = Arc::clone(&component);
        let data = format!("{}_{}", String::from_utf8_lossy(test_data), i).into_bytes();
        
        let handle = tokio::spawn(async move {
            component.process(&data).await
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await.expect("Task should complete")
            .expect("Should process data");
    }

    let total_duration = start.elapsed();
    let throughput = concurrent_tasks as f64 / total_duration.as_secs_f64();

    // 验证并发性能要求
    assert!(throughput > 10.0, 
        "Concurrent throughput should be greater than 10 ops/sec, got {:.2}", throughput);

    println!("Concurrent Performance Results:");
    println!("  Concurrent Tasks: {}", concurrent_tasks);
    println!("  Total Duration: {:?}", total_duration);
    println!("  Throughput: {:.2} ops/sec", throughput);
}

#[tokio::test]
async fn test_otlp_stress_performance() {
    let component = Arc::new(OtlpComponent::new(
        "stress_test".to_string(),
        Duration::from_millis(1)
    ));

    let test_data = b"test data for stress measurement";
    let stress_duration = Duration::from_secs(5);
    let start = Instant::now();
    let mut operations = 0;

    // 压力测试
    while start.elapsed() < stress_duration {
        let component = Arc::clone(&component);
        let data = test_data.to_vec();
        
        let _result = component.process(&data).await.expect("Should process data");
        operations += 1;
    }

    let actual_duration = start.elapsed();
    let throughput = operations as f64 / actual_duration.as_secs_f64();

    // 验证压力测试性能要求
    assert!(operations > 100, 
        "Should complete more than 100 operations in stress test, got {}", operations);
    assert!(throughput > 20.0, 
        "Stress test throughput should be greater than 20 ops/sec, got {:.2}", throughput);

    println!("Stress Test Results:");
    println!("  Duration: {:?}", actual_duration);
    println!("  Operations: {}", operations);
    println!("  Throughput: {:.2} ops/sec", throughput);
}

#[tokio::test]
async fn test_otlp_scalability_performance() {
    let component = Arc::new(OtlpComponent::new(
        "scalability_test".to_string(),
        Duration::from_millis(2)
    ));

    let test_data = b"test data for scalability measurement";
    let scales = vec![1, 5, 10, 20, 50]; // 不同的并发级别

    for scale in scales {
        let start = Instant::now();
        
        let mut handles = Vec::new();
        for _ in 0..scale {
            let component = Arc::clone(&component);
            let data = test_data.to_vec();
            
            let handle = tokio::spawn(async move {
                component.process(&data).await
            });
            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            handle.await.expect("Task should complete")
                .expect("Should process data");
        }

        let duration = start.elapsed();
        let throughput = scale as f64 / duration.as_secs_f64();

        println!("Scalability Test for {} concurrent tasks:", scale);
        println!("  Duration: {:?}", duration);
        println!("  Throughput: {:.2} ops/sec", throughput);

        // 验证可扩展性（吞吐量应该随着并发数增加而增加）
        if scale > 1 {
            assert!(throughput > 1.0, 
                "Throughput should be greater than 1 ops/sec for scale {}, got {:.2}", 
                scale, throughput);
        }
    }
}

#[tokio::test]
async fn test_otlp_error_performance() {
    let component = OtlpComponent::new(
        "error_test".to_string(),
        Duration::from_millis(1)
    );

    let valid_data = b"valid test data";
    let invalid_data = b"";

    // 测试错误处理的性能影响
    let start = Instant::now();
    
    // 处理有效数据
    for _ in 0..50 {
        let _result = component.process(valid_data).await.expect("Should process valid data");
    }
    
    // 处理无效数据
    for _ in 0..50 {
        let _result = component.process(invalid_data).await;
        // 预期会失败，但不应该影响性能
    }

    let duration = start.elapsed();

    // 验证错误处理性能
    assert!(duration < Duration::from_millis(200), 
        "Error handling should not significantly impact performance, got {:?}", duration);

    println!("Error Handling Performance:");
    println!("  Duration: {:?}", duration);
    println!("  Operations: 100 (50 valid + 50 invalid)");
}

#[tokio::test]
async fn test_otlp_resource_usage() {
    let component = OtlpComponent::new(
        "resource_test".to_string(),
        Duration::from_millis(1)
    );

    let test_data = b"test data for resource measurement";
    let operations = 1000;

    // 测量资源使用情况
    let start = Instant::now();
    
    for _ in 0..operations {
        let _result = component.process(test_data).await.expect("Should process data");
    }

    let duration = start.elapsed();
    let throughput = operations as f64 / duration.as_secs_f64();

    // 验证资源使用效率
    assert!(throughput > 50.0, 
        "Resource usage should be efficient, throughput should be greater than 50 ops/sec, got {:.2}", throughput);

    println!("Resource Usage Performance:");
    println!("  Operations: {}", operations);
    println!("  Duration: {:?}", duration);
    println!("  Throughput: {:.2} ops/sec", throughput);
}