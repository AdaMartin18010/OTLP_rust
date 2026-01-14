//! eBPF 基础使用示例
//!
//! 演示如何使用 eBPF 模块进行性能分析和追踪

use otlp::ebpf::{EbpfConfig, EbpfLoader, EbpfCpuProfiler, ProbeManager, MapsManager, EventProcessor, MapType};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF 基础使用示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 检查系统支持
    println!("1. 检查系统支持...");
    match EbpfLoader::check_system_support() {
        Ok(()) => println!("   ✅ 系统支持 eBPF"),
        Err(e) => {
            println!("   ❌ 系统不支持 eBPF: {}", e);
            return Ok(()); // 在非Linux环境正常退出
        }
    }
    println!();

    // 2. 创建配置
    println!("2. 创建 eBPF 配置...");
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true)
        .with_network_tracing(true)
        .with_syscall_tracing(true);
    println!("   ✅ 配置创建成功");
    println!("   - 采样频率: {}Hz", config.sample_rate);
    println!("   - CPU性能分析: {}", config.enable_cpu_profiling);
    println!("   - 网络追踪: {}", config.enable_network_tracing);
    println!("   - 系统调用追踪: {}", config.enable_syscall_tracing);
    println!();

    // 3. 创建加载器
    println!("3. 创建 eBPF 加载器...");
    let mut loader = EbpfLoader::new(config.clone());
    println!("   ✅ 加载器创建成功");
    println!();

    // 4. 验证程序（使用模拟ELF）
    println!("4. 验证 eBPF 程序格式...");
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);

    match loader.validate_program(&elf_program) {
        Ok(()) => println!("   ✅ 程序格式验证通过"),
        Err(e) => println!("   ❌ 程序格式验证失败: {}", e),
    }
    println!();

    // 5. 创建探针管理器
    println!("5. 创建探针管理器...");
    let mut probe_manager = ProbeManager::new();

    // 附加一些探针
    if probe_manager.attach_kprobe("tcp_connect", "tcp_v4_connect").is_ok() {
        println!("   ✅ KProbe 附加成功: tcp_connect -> tcp_v4_connect");
    }

    if probe_manager.attach_tracepoint("sys_open", "syscalls", "sys_enter_open").is_ok() {
        println!("   ✅ Tracepoint 附加成功: sys_open -> syscalls:sys_enter_open");
    }

    println!("   - 探针数量: {}", probe_manager.probe_count());
    println!();

    // 6. 创建 Maps 管理器
    println!("6. 创建 Maps 管理器...");
    let mut maps_manager = MapsManager::new();

    // 注册一些 Maps
    maps_manager.register_map("events_map".to_string(), MapType::Hash, 8, 16);
    println!("   ✅ Map 注册成功: events_map (Hash)");

    maps_manager.register_map("stats_map".to_string(), MapType::Array, 4, 8);
    println!("   ✅ Map 注册成功: stats_map (Array)");

    println!("   - Map 数量: {}", maps_manager.map_count());
    println!();

    // 7. 创建事件处理器
    println!("7. 创建事件处理器...");
    let mut event_processor = EventProcessor::new(1000);
    println!("   ✅ 事件处理器创建成功");
    println!("   - 缓冲区大小: 1000");
    println!();

    // 8. CPU 性能分析示例
    println!("8. CPU 性能分析示例...");
    let mut profiler = EbpfCpuProfiler::new(config.clone());

    if profiler.start().is_ok() {
        println!("   ✅ 性能分析器启动成功");

        // 模拟一些工作
        println!("   - 执行一些CPU密集型操作...");
        let start = std::time::Instant::now();
        while start.elapsed() < Duration::from_millis(100) {
            let _ = (0..1000).sum::<i32>();
        }

        // 停止并获取profile
        match profiler.stop() {
            Ok(profile) => {
                println!("   ✅ Profile 生成成功");
                println!("   - 样本数量: {}", profile.samples.len());
            }
            Err(e) => {
                println!("   ⚠️  Profile 生成失败: {}", e);
            }
        }
    }
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
