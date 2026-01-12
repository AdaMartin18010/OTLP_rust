//! # eBPF 网络追踪示例
//!
//! 演示如何使用 eBPF 进行网络活动追踪

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfNetworkTracer,
    validate_config, create_recommended_config,
};
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("==========================================");
    println!("  eBPF 网络追踪示例");
    println!("==========================================");
    println!();

    // 1. 创建配置（启用网络追踪）
    let env = std::env::var("ENV").unwrap_or_else(|_| "development".to_string());
    let config = create_recommended_config(&env)
        .with_network_tracing(true)
        .with_cpu_profiling(false);

    println!("📋 eBPF 配置:");
    println!("  - 环境: {}", env);
    println!("  - 网络追踪: 启用");
    println!("  - CPU 性能分析: 禁用");
    println!("  - 采样频率: {} Hz", config.sample_rate);
    println!("  - 持续时间: {:?}", config.duration);

    // 2. 验证配置
    if let Err(e) = validate_config(&config) {
        eprintln!("❌ 配置验证失败: {}", e);
        return Err(e.into());
    }
    println!("✅ 配置验证通过");

    // 3. 创建网络追踪器
    println!("\n🔧 创建网络追踪器...");
    let mut tracer = EbpfNetworkTracer::new(config.clone());
    println!("✅ 网络追踪器创建成功");

    // 4. 启动网络追踪
    println!("\n🚀 启动网络追踪...");
    match tracer.start() {
        Ok(()) => {
            println!("✅ 网络追踪启动成功");
        }
        Err(e) => {
            eprintln!("❌ 网络追踪启动失败: {}", e);
            eprintln!("提示: 需要 CAP_BPF 权限或 root 权限");
            return Err(e.into());
        }
    }

    // 5. 模拟网络活动
    println!("\n⏳ 执行网络活动 (持续 {} 秒)...", config.duration.as_secs());
    println!("💡 提示: 在此期间可以执行网络操作，例如:");
    println!("   - curl http://example.com");
    println!("   - ping 8.8.8.8");
    println!("   - 其他网络活动");

    tokio::time::sleep(config.duration).await;

    // 6. 停止网络追踪并获取结果
    println!("\n🛑 停止网络追踪...");
    let events = match tracer.stop() {
        Ok(events) => {
            println!("✅ 网络追踪停止成功");
            events
        }
        Err(e) => {
            eprintln!("❌ 网络追踪停止失败: {}", e);
            return Err(e.into());
        }
    };

    // 7. 分析结果
    println!("\n📊 网络追踪结果:");
    println!("  - 收集到 {} 个网络事件", events.len());

    if !events.is_empty() {
        println!("\n📋 事件详情:");
        for (i, event) in events.iter().take(10).enumerate() {
            println!("  [{}] 类型: {:?}, PID: {}, TID: {}, 时间戳: {:?}",
                i + 1, event.event_type, event.pid, event.tid, event.timestamp);
        }
        if events.len() > 10 {
            println!("  ... 还有 {} 个事件未显示", events.len() - 10);
        }
    } else {
        println!("  ⚠️  未收集到网络事件");
        println!("  💡 提示: 可能的原因:");
        println!("     - 在追踪期间没有网络活动");
        println!("     - eBPF 程序尚未实现完整功能");
    }

    println!("\n==========================================");
    println!("  🎉 eBPF 网络追踪示例运行成功！");
    println!("==========================================");

    Ok(())
}

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
fn main() {
    println!("eBPF 网络追踪示例仅在 Linux 平台支持，且需要 'ebpf' feature。");
    println!("当前操作系统不是 Linux 或 'ebpf' feature 未启用，跳过示例运行。");
}
