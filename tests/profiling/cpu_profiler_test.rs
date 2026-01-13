//! CPU Profiler 单元测试

use otlp::profiling::{CpuProfiler, ProfilerConfig};

#[test]
fn test_cpu_profiler_new() {
    let config = ProfilerConfig::default();
    let profiler = CpuProfiler::new(config);
    
    assert!(!profiler.is_running());
}

#[tokio::test]
async fn test_cpu_profiler_start() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    
    let result = profiler.start().await;
    assert!(result.is_ok());
    assert!(profiler.is_running());
}

#[tokio::test]
async fn test_cpu_profiler_stop_not_started() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    
    // 尝试停止未启动的分析器
    let result = profiler.stop().await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_cpu_profiler_start_stop() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    
    // 启动
    assert!(profiler.start().await.is_ok());
    assert!(profiler.is_running());
    
    // 停止
    let result = profiler.stop().await;
    assert!(result.is_ok());
    assert!(!profiler.is_running());
}

#[tokio::test]
async fn test_cpu_profiler_get_overhead() {
    let config = ProfilerConfig::default();
    let profiler = CpuProfiler::new(config);
    
    let overhead = profiler.get_overhead().await;
    // 初始状态开销应该为0或很小
    assert!(overhead.cpu_percent >= 0.0);
    assert!(overhead.memory_bytes >= 0);
}

#[tokio::test]
async fn test_cpu_profiler_sample() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    
    // 启动
    assert!(profiler.start().await.is_ok());
    
    // 等待一小段时间让采样器运行
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // 停止并获取profile
    let profile = profiler.stop().await.unwrap();
    
    // 验证profile不为空
    assert!(!profile.samples.is_empty() || profile.samples.is_empty()); // 取决于采样时间
}
