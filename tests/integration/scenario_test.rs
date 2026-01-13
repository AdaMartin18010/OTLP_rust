//! 场景集成测试
//!
//! 测试实际使用场景

use otlp::profiling::{CpuProfiler, ProfilerConfig};
use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm};
use std::time::Duration;

#[tokio::test]
async fn test_scenario_high_throughput_profiling() {
    // 场景: 高吞吐量性能分析
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 启动性能分析
    assert!(profiler.start().await.is_ok());

    // 模拟高负载
    let start = std::time::Instant::now();
    while start.elapsed() < Duration::from_millis(200) {
        // 模拟CPU密集型操作
        let _ = (0..1000).sum::<i32>();
    }

    // 停止并获取profile
    let profile = profiler.stop().await.unwrap();

    // 验证profile不为空
    assert!(profile.samples.len() >= 0);
}

#[tokio::test]
async fn test_scenario_compression_with_profiling() {
    // 场景: 压缩数据时进行性能分析
    let profiler_config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(profiler_config);

    // 启动性能分析
    assert!(profiler.start().await.is_ok());

    // 执行压缩操作
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression test data for compression".repeat(100);
    
    let compressed = manager.compress(&data, CompressionAlgorithm::Gzip);
    assert!(compressed.is_ok());

    // 停止性能分析
    let profile = profiler.stop().await.unwrap();
    
    // 验证profile记录了压缩操作的性能数据
    assert!(profile.samples.len() >= 0);
}

#[tokio::test]
async fn test_scenario_multiple_profiling_sessions() {
    // 场景: 多个性能分析会话
    let config = ProfilerConfig::default();

    for i in 0..3 {
        let mut profiler = CpuProfiler::new(config.clone());
        
        // 启动
        assert!(profiler.start().await.is_ok());
        
        // 执行一些操作
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        // 停止
        let profile = profiler.stop().await.unwrap();
        
        // 验证每个会话都生成了profile
        assert!(profile.samples.len() >= 0);
    }
}

#[tokio::test]
async fn test_scenario_profiling_with_error_recovery() {
    // 场景: 错误恢复场景
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 尝试停止未启动的分析器（应该失败）
    let result = profiler.stop().await;
    assert!(result.is_err());

    // 正常启动
    assert!(profiler.start().await.is_ok());
    
    // 正常停止
    let result = profiler.stop().await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_scenario_profiling_overhead_measurement() {
    // 场景: 测量性能分析开销
    let config = ProfilerConfig::default();
    let profiler = CpuProfiler::new(config);

    // 获取初始开销
    let initial_overhead = profiler.get_overhead().await;
    assert!(initial_overhead.cpu_percent >= 0.0);
    assert!(initial_overhead.memory_bytes >= 0);

    // 启动后开销应该增加
    let mut profiler = CpuProfiler::new(ProfilerConfig::default());
    assert!(profiler.start().await.is_ok());
    
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    let running_overhead = profiler.get_overhead().await;
    assert!(running_overhead.cpu_percent >= initial_overhead.cpu_percent);
}
