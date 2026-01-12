//! eBPF 完整功能示例
//!
//! 演示如何使用新的 eBPF 模块进行性能分析、网络追踪和系统调用追踪

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfLoader, EbpfCpuProfiler, EbpfNetworkTracer,
    EbpfSyscallTracer, EbpfMemoryTracer,
};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("==========================================");
    println!("  eBPF 完整功能示例");
    println!("==========================================");
    println!();

    // 1. 配置 eBPF
    let config = EbpfConfig::default()
        .with_sample_rate(99) // 99Hz 采样频率
        .with_duration(Duration::from_secs(30));

    println!("📋 配置 eBPF:");
    println!("  采样频率: {}Hz", config.sample_rate);
    println!("  持续时间: {:?}", config.duration);
    println!();

    // 2. CPU 性能分析
    println!("🔍 启动 CPU 性能分析...");
    let mut cpu_profiler = EbpfCpuProfiler::new(config.clone());
    cpu_profiler.start()?;

    // 模拟工作负载
    println!("  执行工作负载...");
    for i in 0..100 {
        let _ = (0..1000).sum::<i32>();
        if i % 20 == 0 {
            println!("    进度: {}/100", i);
        }
    }

    let profile = cpu_profiler.stop()?;
    println!("  ✅ CPU 性能分析完成");
    println!();

    // 3. 网络追踪（如果启用）
    if config.enable_network_tracing {
        println!("🌐 启动网络追踪...");
        let mut network_tracer = EbpfNetworkTracer::new(config.clone());
        network_tracer.start()?;

        // 模拟网络活动
        tokio::time::sleep(Duration::from_secs(5)).await;

        let events = network_tracer.stop()?;
        println!("  ✅ 网络追踪完成，收集到 {} 个事件", events.len());
        println!();
    }

    // 4. 系统调用追踪（如果启用）
    if config.enable_syscall_tracing {
        println!("🔧 启动系统调用追踪...");
        let mut syscall_tracer = EbpfSyscallTracer::new(config.clone());
        syscall_tracer.start()?;

        // 模拟系统调用活动
        tokio::time::sleep(Duration::from_secs(5)).await;

        let events = syscall_tracer.stop()?;
        println!("  ✅ 系统调用追踪完成，收集到 {} 个事件", events.len());
        println!();
    }

    // 5. 内存追踪（如果启用）
    if config.enable_memory_tracing {
        println!("💾 启动内存追踪...");
        let mut memory_tracer = EbpfMemoryTracer::new(config.clone());
        memory_tracer.start()?;

        // 模拟内存分配
        let _ = vec![0u8; 1024 * 1024]; // 1MB

        let events = memory_tracer.stop()?;
        println!("  ✅ 内存追踪完成，收集到 {} 个事件", events.len());
        println!();
    }

    println!("==========================================");
    println!("  ✅ 所有 eBPF 功能演示完成");
    println!("==========================================");

    Ok(())
}

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
fn main() {
    println!("⚠️  eBPF 功能仅在 Linux 平台支持");
    println!("   需要启用 'ebpf' feature 且运行在 Linux 系统上");
}
