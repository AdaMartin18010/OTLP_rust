//! # eBPF CPU 性能分析示例
//!
//! 演示如何使用 eBPF 模块进行 CPU 性能分析。
//!
//! **注意**: 此示例仅在 Linux 平台运行，且需要 CAP_BPF 权限。
//! 运行前请确保已安装 `aya` 或 `libbpf-rs` 依赖，并启用 `ebpf` feature。
//!
//! ```bash
//! # 运行此示例 (需要 root 权限或 CAP_BPF)
//! sudo cargo run --example ebpf_profiling --features ebpf
//! ```

#[cfg(target_os = "linux")]
use otlp::ebpf::{
    EbpfConfig, EbpfCpuProfiler, EbpfError,
    create_recommended_config, validate_config,
};
#[cfg(target_os = "linux")]
use std::time::Duration;
#[cfg(target_os = "linux")]
use tracing::info;

#[cfg(target_os = "linux")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("==========================================");
    println!("  🚀 启动 eBPF CPU 性能分析示例");
    println!("==========================================");

    // 1. 创建推荐的配置（根据环境变量）
    let env = std::env::var("ENV").unwrap_or_else(|_| "development".to_string());
    let config = create_recommended_config(&env);

    println!("\n📋 eBPF 配置:");
    println!("  - 环境: {}", env);
    println!("  - 采样频率: {} Hz", config.sample_rate);
    println!("  - 持续时间: {:?}", config.duration);
    println!("  - 最大采样数: {}", config.max_samples);

    // 2. 验证配置
    if let Err(e) = validate_config(&config) {
        eprintln!("❌ 配置验证失败: {}", e);
        return Err(e.into());
    }
    println!("✅ 配置验证通过");

    // 3. 检查系统支持
    println!("\n🔧 检查系统支持...");
    match EbpfLoader::check_system_support() {
        Ok(()) => {
            println!("✅ 系统支持 eBPF");
        }
        Err(e) => {
            eprintln!("❌ 系统不支持 eBPF: {}", e);
            eprintln!("提示: 需要 Linux 内核 >= 5.8 和 CAP_BPF 权限");
            return Err(e.into());
        }
    }

    // 4. 创建 eBPF 加载器
    println!("\n🔧 创建 eBPF 加载器...");
    let loader = match EbpfLoader::new(config.clone()) {
        Ok(l) => {
            println!("✅ eBPF 加载器创建成功");
            l
        }
        Err(e) => {
            eprintln!("❌ eBPF 加载器创建失败: {}", e);
            return Err(e.into());
        }
    };

    // 5. 执行一些工作负载（模拟性能分析）
    println!("\n⏳ 执行工作负载（持续 {:?}）...", config.duration);
    let work_duration = config.duration.min(Duration::from_secs(30)); // 最多30秒
    let start_time = std::time::Instant::now();

    // 模拟CPU密集型工作
    while start_time.elapsed() < work_duration {
        let _: u64 = (0..1_000_000).sum(); // CPU 密集型任务
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    println!("✅ 工作负载执行完成");
    println!("\n💡 提示: eBPF CPU 性能分析功能正在开发中");
    println!("   当前版本提供了基础框架和配置验证功能");
    println!("   完整的性能分析功能将在后续版本中实现");

    println!("\n==========================================");
    println!("  🎉 eBPF CPU 性能分析示例运行成功！");
    println!("==========================================");

    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn main() {
    println!("eBPF CPU 性能分析示例仅在 Linux 平台支持。");
    println!("当前操作系统不是 Linux，跳过示例运行。");
}
