//! eBPF 探针管理示例
//!
//! 演示如何使用探针管理器进行各种类型的探针附加和管理

use otlp::ebpf::{EbpfConfig, EbpfLoader, ProbeManager, ProbeType};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF 探针管理示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 创建配置和加载器
    println!("1. 初始化 eBPF 环境...");
    let config = EbpfConfig::default()
        .with_cpu_profiling(true)
        .with_network_tracing(true)
        .with_syscall_tracing(true);
    
    let mut loader = EbpfLoader::new(config);
    let _ = loader.check_system_support();
    println!("   ✅ eBPF 环境初始化完成");
    println!();

    // 2. 创建探针管理器
    println!("2. 创建探针管理器...");
    let mut probe_manager = ProbeManager::new();
    println!("   ✅ 探针管理器创建成功");
    println!();

    // 3. 注册 KProbe（内核函数探针）
    println!("3. 注册 KProbe 探针...");
    let kprobes = vec![
        ("tcp_connect", "tcp_v4_connect"),
        ("tcp_send", "tcp_v4_sendmsg"),
        ("tcp_receive", "tcp_v4_do_rcv"),
    ];
    
    for (name, function) in kprobes {
        match probe_manager.attach_kprobe(name, function, None) {
            Ok(()) => println!("   ✅ KProbe 注册成功: {} -> {}", name, function),
            Err(e) => println!("   ⚠️  KProbe 注册失败: {} -> {}: {}", name, function, e),
        }
    }
    println!();

    // 4. 注册 UProbe（用户空间函数探针）
    println!("4. 注册 UProbe 探针...");
    let uprobes = vec![
        ("malloc_trace", "/usr/lib/libc.so.6", "malloc"),
        ("free_trace", "/usr/lib/libc.so.6", "free"),
        ("open_trace", "/usr/lib/libc.so.6", "open"),
    ];
    
    for (name, binary, symbol) in uprobes {
        match probe_manager.attach_uprobe(name, binary, symbol, None) {
            Ok(()) => println!("   ✅ UProbe 注册成功: {} -> {}:{}", name, binary, symbol),
            Err(e) => println!("   ⚠️  UProbe 注册失败: {} -> {}:{}: {}", name, binary, symbol, e),
        }
    }
    println!();

    // 5. 注册 Tracepoint（跟踪点）
    println!("5. 注册 Tracepoint 探针...");
    let tracepoints = vec![
        ("syscall_open", "syscalls", "sys_enter_openat"),
        ("syscall_read", "syscalls", "sys_enter_read"),
        ("syscall_write", "syscalls", "sys_enter_write"),
        ("sched_switch", "sched", "sched_switch"),
    ];
    
    for (name, category, event) in tracepoints {
        match probe_manager.attach_tracepoint(name, category, event, None) {
            Ok(()) => println!("   ✅ Tracepoint 注册成功: {} -> {}:{}", name, category, event),
            Err(e) => println!("   ⚠️  Tracepoint 注册失败: {} -> {}:{}: {}", name, category, event, e),
        }
    }
    println!();

    // 6. 列出所有探针
    println!("6. 列出所有已注册的探针...");
    let probes = probe_manager.list_probes();
    println!("   ✅ 共注册 {} 个探针:", probes.len());
    for (name, probe_type, target, attached) in probes {
        let type_str = match probe_type {
            ProbeType::KProbe => "KProbe",
            ProbeType::UProbe => "UProbe",
            ProbeType::TracePoint => "Tracepoint",
        };
        println!("     - {} ({}) -> {} [{}]", 
            name, type_str, target, 
            if attached { "已附加" } else { "已注册" });
    }
    println!();

    // 7. 按类型统计探针
    println!("7. 探针统计...");
    let kprobe_count = probes.iter().filter(|(_, t, _, _)| *t == ProbeType::KProbe).count();
    let uprobe_count = probes.iter().filter(|(_, t, _, _)| *t == ProbeType::UProbe).count();
    let tracepoint_count = probes.iter().filter(|(_, t, _, _)| *t == ProbeType::TracePoint).count();
    
    println!("   ✅ 探针统计:");
    println!("     - KProbe: {} 个", kprobe_count);
    println!("     - UProbe: {} 个", uprobe_count);
    println!("     - Tracepoint: {} 个", tracepoint_count);
    println!("     - 总计: {} 个", probe_manager.probe_count());
    println!();

    // 8. 分离单个探针
    println!("8. 分离单个探针...");
    match probe_manager.detach("tcp_connect") {
        Ok(()) => println!("   ✅ 探针分离成功: tcp_connect"),
        Err(e) => println!("   ⚠️  探针分离失败: {}", e),
    }
    println!("   - 当前探针数: {}", probe_manager.probe_count());
    println!();

    // 9. 分离所有探针
    println!("9. 分离所有探针...");
    match probe_manager.detach_all() {
        Ok(()) => println!("   ✅ 所有探针分离成功"),
        Err(e) => println!("   ⚠️  探针分离失败: {}", e),
    }
    println!("   - 当前探针数: {}", probe_manager.probe_count());
    println!();

    // 10. 清理资源
    println!("10. 清理资源...");
    loader.unload()?;
    println!("   ✅ 资源清理完成");
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF 探针管理示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
