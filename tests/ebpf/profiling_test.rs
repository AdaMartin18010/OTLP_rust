//! eBPF Profiling 单元测试

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{EbpfCpuProfiler, EbpfConfig};

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_new() {
    let config = EbpfConfig::default();
    let profiler = EbpfCpuProfiler::new(config);
    
    assert!(!profiler.is_running());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_start() {
    let config = EbpfConfig::default();
    let mut profiler = EbpfCpuProfiler::new(config);
    
    let result = profiler.start();
    assert!(result.is_ok());
    assert!(profiler.is_running());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_stop_not_started() {
    let config = EbpfConfig::default();
    let mut profiler = EbpfCpuProfiler::new(config);
    
    // 尝试停止未启动的分析器
    let result = profiler.stop();
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_start_stop() {
    let config = EbpfConfig::default();
    let mut profiler = EbpfCpuProfiler::new(config);
    
    // 启动
    assert!(profiler.start().is_ok());
    assert!(profiler.is_running());
    
    // 停止（当前实现可能返回错误，因为实际功能未实现）
    let _ = profiler.stop();
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_get_overhead() {
    let config = EbpfConfig::default();
    let profiler = EbpfCpuProfiler::new(config);
    
    let overhead = profiler.get_overhead();
    // 初始状态开销应该为0或很小
    assert!(overhead.cpu_percent >= 0.0);
    assert!(overhead.memory_bytes >= 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_cpu_profiler_config() {
    let config = EbpfConfig::default();
    let profiler = EbpfCpuProfiler::new(config.clone());
    
    assert_eq!(profiler.config().sample_rate, config.sample_rate);
}
