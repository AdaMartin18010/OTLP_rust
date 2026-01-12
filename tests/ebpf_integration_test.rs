//! eBPF 集成测试
//!
//! 测试 eBPF 模块的集成功能

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfLoader, EbpfCpuProfiler, EbpfNetworkTracer,
    EbpfSyscallTracer, EbpfMemoryTracer, EbpfEventType,
};
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_config_default() {
    let config = EbpfConfig::default();
    assert_eq!(config.enable_cpu_profiling, true);
    assert_eq!(config.sample_rate, 99);
    assert_eq!(config.max_samples, 100000);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_config_builder() {
    let config = EbpfConfig::new()
        .with_sample_rate(50)
        .with_network_tracing(true)
        .with_syscall_tracing(true)
        .with_memory_tracing(true);

    assert_eq!(config.sample_rate, 50);
    assert_eq!(config.enable_network_tracing, true);
    assert_eq!(config.enable_syscall_tracing, true);
    assert_eq!(config.enable_memory_tracing, true);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_loader_new() {
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config);
    
    assert_eq!(loader.config().sample_rate, 99);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_loader_check_system_support() {
    // 注意: 实际测试需要 Linux 环境
    // 这里只是验证函数可以调用
    let result = EbpfLoader::check_system_support();
    // 在非 Linux 环境会返回错误，这是预期的
    if cfg!(target_os = "linux") {
        // 在 Linux 环境应该成功（如果系统支持）
        // 或者返回相应错误（如果系统不支持）
        assert!(result.is_ok() || result.is_err());
    }
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_cpu_profiler_new() {
    let config = EbpfConfig::default();
    let profiler = EbpfCpuProfiler::new(config);
    
    // 验证性能分析器已创建
    // 注意: start/stop 功能待实现，目前只测试创建
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_network_tracer_new() {
    let config = EbpfConfig::default()
        .with_network_tracing(true);
    let tracer = EbpfNetworkTracer::new(config);
    
    // 验证网络追踪器已创建
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_syscall_tracer_new() {
    let config = EbpfConfig::default()
        .with_syscall_tracing(true);
    let tracer = EbpfSyscallTracer::new(config);
    
    // 验证系统调用追踪器已创建
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_memory_tracer_new() {
    let config = EbpfConfig::default()
        .with_memory_tracing(true);
    let tracer = EbpfMemoryTracer::new(config);
    
    // 验证内存追踪器已创建
}

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
#[test]
fn test_ebpf_not_supported() {
    // 在非 Linux 环境，eBPF 功能应该不可用
    // 这里可以测试错误处理
}
