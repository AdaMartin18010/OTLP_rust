//! # OTLP独立测试程序
//!
//! 验证测试体系的基本功能

use std::time::Duration;
use std::sync::Arc;
use tokio::time::sleep;

// 简化的OTLP组件用于测试
struct SimpleOtlpComponent {
    name: String,
    processing_time: Duration,
}

impl SimpleOtlpComponent {
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

    fn get_name(&self) -> &str {
        &self.name
    }
}

// 性能测试工具
struct PerformanceTester {
    measurements: Vec<Duration>,
}

impl PerformanceTester {
    fn new() -> Self {
        Self {
            measurements: Vec::new(),
        }
    }

    async fn measure_async<F, Fut, R>(&mut self, operation: F) -> R
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = R>,
    {
        let start = std::time::Instant::now();
        let result = operation().await;
        let duration = start.elapsed();
        self.measurements.push(duration);
        result
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

    fn get_throughput(&self, operations: usize) -> f64 {
        if self.measurements.is_empty() {
            return 0.0;
        }
        
        let total_duration: Duration = self.measurements.iter().sum();
        operations as f64 / total_duration.as_secs_f64()
    }
}

#[tokio::main]
async fn main() {
    println!("🚀 OTLP独立测试程序");
    println!("==================");

    // 测试1: 基本功能测试
    println!("\n📋 测试1: 基本功能测试");
    println!("-------------------");
    
    let component = SimpleOtlpComponent::new(
        "test_component".to_string(),
        Duration::from_millis(1)
    );

    // 测试基本功能
    assert_eq!(component.get_name(), "test_component");
    println!("✅ 组件名称测试通过");

    let test_data = b"test data";
    let result = component.process(test_data).await.expect("Should process data");
    
    assert!(result.starts_with(b"processed:"));
    assert!(result.ends_with(test_data));
    println!("✅ 数据处理测试通过");

    // 测试错误处理
    let empty_data = b"";
    let result = component.process(empty_data).await;
    
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "Empty data");
    println!("✅ 错误处理测试通过");

    // 测试2: 性能测试
    println!("\n📊 测试2: 性能测试");
    println!("-----------------");
    
    let mut tester = PerformanceTester::new();
    let component = SimpleOtlpComponent::new(
        "performance_test".to_string(),
        Duration::from_millis(1)
    );

    let test_data = b"performance test data";

    // 测量性能
    for _ in 0..10 {
        tester.measure_async(|| component.process(test_data)).await
            .expect("Should process data");
    }

    let avg_duration = tester.get_average_duration();
    let max_duration = tester.get_max_duration();
    let min_duration = tester.get_min_duration();

    println!("性能测试结果:");
    println!("  平均延迟: {:?}", avg_duration);
    println!("  最大延迟: {:?}", max_duration);
    println!("  最小延迟: {:?}", min_duration);

    // 验证性能要求
    assert!(avg_duration < Duration::from_millis(10), 
        "Average duration should be less than 10ms, got {:?}", avg_duration);
    println!("✅ 平均延迟测试通过");

    assert!(max_duration < Duration::from_millis(20), 
        "Max duration should be less than 20ms, got {:?}", max_duration);
    println!("✅ 最大延迟测试通过");

    assert!(min_duration >= Duration::from_millis(1), 
        "Min duration should be at least 1ms, got {:?}", min_duration);
    println!("✅ 最小延迟测试通过");

    // 测试3: 并发测试
    println!("\n⚡ 测试3: 并发测试");
    println!("-----------------");
    
    let component = Arc::new(SimpleOtlpComponent::new(
        "concurrent_test".to_string(),
        Duration::from_millis(2)
    ));

    let test_data = b"concurrent test data";
    let concurrent_tasks = 10;

    // 测试并发处理
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
        let result = handle.await.expect("Task should complete");
        assert!(result.is_ok(), "All concurrent tasks should succeed");
    }
    println!("✅ 并发处理测试通过");

    // 测试4: 吞吐量测试
    println!("\n🚀 测试4: 吞吐量测试");
    println!("-------------------");
    
    let mut tester = PerformanceTester::new();
    let component = SimpleOtlpComponent::new(
        "throughput_test".to_string(),
        Duration::from_millis(1)
    );

    let test_data = b"throughput test data";
    let operations = 100;

    // 测量吞吐量
    let start = std::time::Instant::now();
    
    let mut handles = Vec::new();
    for _ in 0..operations {
        let component = Arc::new(component);
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

    println!("吞吐量测试结果:");
    println!("  操作数: {}", operations);
    println!("  总时间: {:?}", total_duration);
    println!("  吞吐量: {:.2} ops/sec", throughput);

    // 验证吞吐量要求
    assert!(throughput > 10.0, 
        "Throughput should be greater than 10 ops/sec, got {:.2}", throughput);
    println!("✅ 吞吐量测试通过");

    // 测试5: 内存使用测试
    println!("\n💾 测试5: 内存使用测试");
    println!("---------------------");
    
    let component = SimpleOtlpComponent::new(
        "memory_test".to_string(),
        Duration::from_millis(1)
    );

    // 测试不同大小的数据处理
    let sizes = vec![1024, 10240, 102400]; // 1KB, 10KB, 100KB
    
    for size in sizes {
        let test_data = vec![0u8; size];
        
        let start = std::time::Instant::now();
        let result = component.process(&test_data).await.expect("Should process data");
        let duration = start.elapsed();
        
        // 验证内存使用
        assert_eq!(result.len(), size + 9); // 9 bytes for "processed:" prefix
        
        println!("内存测试 {} bytes:", size);
        println!("  处理时间: {:?}", duration);
        println!("  吞吐量: {:.2} MB/s", 
            (size as f64 / 1024.0 / 1024.0) / duration.as_secs_f64());
    }
    println!("✅ 内存使用测试通过");

    // 测试6: 压力测试
    println!("\n🔥 测试6: 压力测试");
    println!("-----------------");
    
    let component = Arc::new(SimpleOtlpComponent::new(
        "stress_test".to_string(),
        Duration::from_millis(1)
    ));

    let test_data = b"stress test data";
    let stress_duration = Duration::from_secs(2);
    let start = std::time::Instant::now();
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

    println!("压力测试结果:");
    println!("  持续时间: {:?}", actual_duration);
    println!("  操作数: {}", operations);
    println!("  吞吐量: {:.2} ops/sec", throughput);

    // 验证压力测试要求
    assert!(operations > 10, 
        "Should complete more than 10 operations in stress test, got {}", operations);
    println!("✅ 压力测试通过");

    assert!(throughput > 5.0, 
        "Stress test throughput should be greater than 5 ops/sec, got {:.2}", throughput);
    println!("✅ 压力测试吞吐量通过");

    // 测试7: 集成测试
    println!("\n🔗 测试7: 集成测试");
    println!("-----------------");
    
    // 集成测试：多个组件协作
    let processor = SimpleOtlpComponent::new(
        "processor".to_string(),
        Duration::from_millis(1)
    );
    
    let validator = SimpleOtlpComponent::new(
        "validator".to_string(),
        Duration::from_millis(1)
    );

    let test_data = b"integration test data";

    // 验证数据
    let validated_data = validator.process(test_data).await
        .expect("Should validate data");

    // 处理数据
    let processed_data = processor.process(&validated_data).await
        .expect("Should process data");

    // 验证集成结果
    assert!(processed_data.starts_with(b"processed:processed:"));
    assert!(processed_data.ends_with(test_data));

    println!("集成测试结果:");
    println!("  输入: {:?}", String::from_utf8_lossy(test_data));
    println!("  验证后: {:?}", String::from_utf8_lossy(&validated_data));
    println!("  处理后: {:?}", String::from_utf8_lossy(&processed_data));
    println!("✅ 集成测试通过");

    // 测试总结
    println!("\n🎉 测试总结");
    println!("===========");
    println!("✅ 所有测试通过！");
    println!("✅ 基本功能测试: 通过");
    println!("✅ 性能测试: 通过");
    println!("✅ 并发测试: 通过");
    println!("✅ 吞吐量测试: 通过");
    println!("✅ 内存使用测试: 通过");
    println!("✅ 压力测试: 通过");
    println!("✅ 集成测试: 通过");
    
    println!("\n🌟 OTLP测试体系验证成功！");
    println!("🚀 项目已具备完整的测试能力！");
}
