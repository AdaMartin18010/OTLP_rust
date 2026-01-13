//! OTLP Profiling 使用示例
//!
//! 演示如何使用 OTLP Profiling 功能

use otlp::profiling::{CpuProfiler, ProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("OTLP Profiling 使用示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 创建配置
    println!("1. 创建 Profiler 配置...");
    let config = ProfilerConfig::default();
    println!("   ✅ 配置创建成功");
    println!();

    // 2. 创建 CPU Profiler
    println!("2. 创建 CPU Profiler...");
    let mut profiler = CpuProfiler::new(config);
    println!("   ✅ Profiler 创建成功");
    println!();

    // 3. 启动性能分析
    println!("3. 启动性能分析...");
    match profiler.start().await {
        Ok(()) => {
            println!("   ✅ 性能分析启动成功");
            println!("   - 状态: 运行中");
        }
        Err(e) => {
            println!("   ❌ 启动失败: {}", e);
            return Ok(());
        }
    }
    println!();

    // 4. 执行一些工作
    println!("4. 执行一些CPU密集型操作...");
    let start = std::time::Instant::now();
    let mut sum = 0;
    while start.elapsed() < Duration::from_millis(200) {
        for i in 0..1000 {
            sum += i;
        }
    }
    println!("   ✅ 操作完成 (sum = {})", sum);
    println!();

    // 5. 停止并获取 Profile
    println!("5. 停止性能分析并获取 Profile...");
    match profiler.stop().await {
        Ok(profile) => {
            println!("   ✅ Profile 生成成功");
            println!("   - 样本数量: {}", profile.samples.len());
            println!("   - 位置数量: {}", profile.locations.len());
            println!("   - 函数数量: {}", profile.functions.len());
            
            // 6. 导出为 JSON
            println!();
            println!("6. 导出 Profile 为 JSON...");
            match profile.encode_json() {
                Ok(json) => {
                    println!("   ✅ JSON 编码成功");
                    println!("   - JSON 大小: {} bytes", json.len());
                    // 可以保存到文件
                    // std::fs::write("profile.json", &json)?;
                }
                Err(e) => {
                    println!("   ❌ JSON 编码失败: {}", e);
                }
            }
        }
        Err(e) => {
            println!("   ❌ Profile 生成失败: {}", e);
        }
    }
    println!();

    // 7. 获取开销统计
    println!("7. 获取性能分析开销...");
    let overhead = profiler.get_overhead().await;
    println!("   ✅ 开销统计:");
    println!("   - CPU 使用率: {:.2}%", overhead.cpu_percent);
    println!("   - 内存使用: {} bytes", overhead.memory_bytes);
    println!("   - 事件延迟: {} μs", overhead.event_latency_us);
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
