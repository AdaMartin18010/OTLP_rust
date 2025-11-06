//! eBPF Profiling使用示例
//!
//! 演示如何使用eBPF性能分析器进行持续性能分析

#[cfg(target_os = "linux")]
use otlp::{EbpfProfiler, EbpfProfilerConfig};
use std::time::Duration;

#[cfg(target_os = "linux")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建eBPF性能分析器配置
    let config = EbpfProfilerConfig::new()
        .with_sample_rate(99) // 99Hz采样频率，符合2025年标准
        .with_duration(Duration::from_secs(60))
        .with_kernel_tracking(false); // 仅跟踪用户空间

    // 2. 创建性能分析器
    let mut profiler = EbpfProfiler::new(config)?;

    // 3. 开始采样
    println!("启动eBPF性能分析...");
    profiler.start()?;

    // 4. 模拟工作负载
    println!("执行工作负载...");
    for i in 0..1000 {
        // 模拟CPU密集型任务
        let _ = (0..1000).sum::<i32>();
        if i % 100 == 0 {
            println!("进度: {}/1000", i);
        }
    }

    // 5. 停止采样并生成profile
    println!("停止采样...");
    let profile = profiler.stop()?;

    // 6. 获取性能开销
    let overhead = profiler.get_overhead();
    println!("\n性能开销:");
    println!("  CPU开销: {:.2}%", overhead.cpu_percent);
    println!("  内存开销: {} MB", overhead.memory_bytes / 1024 / 1024);

    // 7. 验证性能目标
    if overhead.cpu_percent < 1.0 {
        println!("✅ CPU开销 <1%，符合2025年标准");
    } else {
        println!("⚠️  CPU开销 >=1%，需要优化");
    }

    if overhead.memory_bytes < 50 * 1024 * 1024 {
        println!("✅ 内存开销 <50MB，符合2025年标准");
    } else {
        println!("⚠️  内存开销 >=50MB，需要优化");
    }

    // 8. 导出profile (实际应用中)
    println!("\nProfile已生成，可以导出为pprof格式");

    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn main() {
    println!("eBPF Profiling仅在Linux平台支持");
}
