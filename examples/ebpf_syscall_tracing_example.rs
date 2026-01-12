//! # eBPF 系统调用追踪示例
//!
//! 演示如何使用 eBPF 进行系统调用追踪

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfSyscallTracer,
    validate_config, create_recommended_config,
};
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("==========================================");
    println!("  eBPF 系统调用追踪示例");
    println!("==========================================");
    println!();

    // 1. 创建配置（启用系统调用追踪）
    let env = std::env::var("ENV").unwrap_or_else(|_| "development".to_string());
    let config = create_recommended_config(&env)
        .with_syscall_tracing(true)
        .with_cpu_profiling(false)
        .with_network_tracing(false)
        .with_duration(Duration::from_secs(30)); // 较短的持续时间

    println!("📋 eBPF 配置:");
    println!("  - 环境: {}", env);
    println!("  - 系统调用追踪: 启用");
    println!("  - CPU 性能分析: 禁用");
    println!("  - 网络追踪: 禁用");
    println!("  - 持续时间: {:?}", config.duration);

    // 2. 验证配置
    if let Err(e) = validate_config(&config) {
        eprintln!("❌ 配置验证失败: {}", e);
        return Err(e.into());
    }
    println!("✅ 配置验证通过");

    // 3. 创建系统调用追踪器
    println!("\n🔧 创建系统调用追踪器...");
    let mut tracer = EbpfSyscallTracer::new(config.clone());
    println!("✅ 系统调用追踪器创建成功");

    // 4. 启动系统调用追踪
    println!("\n🚀 启动系统调用追踪...");
    match tracer.start() {
        Ok(()) => {
            println!("✅ 系统调用追踪启动成功");
        }
        Err(e) => {
            eprintln!("❌ 系统调用追踪启动失败: {}", e);
            eprintln!("提示: 需要 CAP_BPF 权限或 root 权限");
            return Err(e.into());
        }
    }

    // 5. 模拟系统调用活动
    println!("\n⏳ 执行系统调用活动 (持续 {} 秒)...", config.duration.as_secs());
    println!("💡 提示: 在此期间可以执行系统操作，例如:");
    println!("   - 文件读写操作");
    println!("   - 网络连接");
    println!("   - 其他系统调用");

    // 模拟一些系统调用
    let _ = std::fs::read_to_string("/proc/version"); // 触发系统调用
    let _ = std::env::var("PATH"); // 触发环境变量访问

    tokio::time::sleep(config.duration).await;

    // 6. 停止系统调用追踪并获取结果
    println!("\n🛑 停止系统调用追踪...");
    let events = match tracer.stop() {
        Ok(events) => {
            println!("✅ 系统调用追踪停止成功");
            events
        }
        Err(e) => {
            eprintln!("❌ 系统调用追踪停止失败: {}", e);
            return Err(e.into());
        }
    };

    // 7. 分析结果
    println!("\n📊 系统调用追踪结果:");
    println!("  - 收集到 {} 个系统调用事件", events.len());

    if !events.is_empty() {
        println!("\n📋 事件详情 (前10个):");
        for (i, event) in events.iter().take(10).enumerate() {
            println!("  [{}] 类型: {:?}, PID: {}, TID: {}, 时间戳: {:?}",
                i + 1, event.event_type, event.pid, event.tid, event.timestamp);
        }
        if events.len() > 10 {
            println!("  ... 还有 {} 个事件未显示", events.len() - 10);
        }

        // 统计系统调用类型
        use std::collections::HashMap;
        let mut type_counts: HashMap<String, usize> = HashMap::new();
        for event in &events {
            let type_name = format!("{:?}", event.event_type);
            *type_counts.entry(type_name).or_insert(0) += 1;
        }

        println!("\n📈 系统调用类型统计:");
        for (type_name, count) in type_counts.iter().take(10) {
            println!("  - {}: {}", type_name, count);
        }
    } else {
        println!("  ⚠️  未收集到系统调用事件");
        println!("  💡 提示: 可能的原因:");
        println!("     - 在追踪期间没有系统调用活动");
        println!("     - eBPF 程序尚未实现完整功能");
    }

    println!("\n==========================================");
    println!("  🎉 eBPF 系统调用追踪示例运行成功！");
    println!("==========================================");

    Ok(())
}

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
fn main() {
    println!("eBPF 系统调用追踪示例仅在 Linux 平台支持，且需要 'ebpf' feature。");
    println!("当前操作系统不是 Linux 或 'ebpf' feature 未启用，跳过示例运行。");
}
