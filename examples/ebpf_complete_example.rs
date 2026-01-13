//! eBPF 完整功能示例
//!
//! 演示如何使用 eBPF 模块的所有功能，包括：
//! - 程序加载
//! - 探针管理
//! - Maps 操作
//! - 事件处理（包括批处理和异步处理）

use otlp::ebpf::{
    EbpfConfig, EbpfLoader, ProbeManager, MapsManager, EventProcessor,
    EbpfEvent, EbpfEventType, MapType,
};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF 完整功能示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 创建配置
    println!("1. 创建 eBPF 配置...");
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true)
        .with_network_tracing(true)
        .with_syscall_tracing(true);
    println!("   ✅ 配置创建成功");
    println!("   - 采样率: {}%", config.sample_rate);
    println!("   - CPU 性能分析: {}", config.enable_cpu_profiling);
    println!("   - 网络追踪: {}", config.enable_network_tracing);
    println!();

    // 2. 创建加载器并检查系统支持
    println!("2. 创建 eBPF 加载器...");
    let mut loader = EbpfLoader::new(config.clone());
    match loader.check_system_support() {
        Ok(()) => println!("   ✅ 系统支持 eBPF"),
        Err(e) => {
            println!("   ⚠️  系统支持检查失败: {}", e);
            println!("   （继续演示其他功能）");
        }
    }
    println!();

    // 3. 验证程序（使用模拟的 ELF 数据）
    println!("3. 验证 eBPF 程序...");
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);
    
    match loader.validate_program(&elf_program) {
        Ok(()) => println!("   ✅ 程序验证通过"),
        Err(e) => println!("   ⚠️  程序验证失败: {}", e),
    }
    println!();

    // 4. 创建探针管理器
    println!("4. 创建探针管理器...");
    let mut probe_manager = ProbeManager::new();
    
    // 注册多个探针（不提供 Bpf 实例，仅演示注册功能）
    println!("   - 注册 KProbe...");
    probe_manager.attach_kprobe("tcp_connect", "tcp_v4_connect", None)?;
    
    println!("   - 注册 UProbe...");
    probe_manager.attach_uprobe("malloc_trace", "/usr/lib/libc.so.6", "malloc", None)?;
    
    println!("   - 注册 Tracepoint...");
    probe_manager.attach_tracepoint("open_trace", "syscalls", "sys_enter_openat", None)?;
    
    println!("   ✅ 探针管理器创建成功");
    println!("   - 已注册探针数: {}", probe_manager.probe_count());
    
    let probes = probe_manager.list_probes();
    for (name, probe_type, target, attached) in probes {
        println!("     - {} ({:?}): {} [{}]", 
            name, probe_type, target, if attached { "已附加" } else { "已注册" });
    }
    println!();

    // 5. 创建 Maps 管理器
    println!("5. 创建 Maps 管理器...");
    let mut maps_manager = MapsManager::new();
    
    maps_manager.register_map("event_map".to_string(), MapType::Hash, 4, 8);
    maps_manager.register_map("stats_map".to_string(), MapType::Array, 4, 16);
    maps_manager.register_map("perf_map".to_string(), MapType::PerfEvent, 8, 32);
    
    println!("   ✅ Maps 管理器创建成功");
    println!("   - 已注册 Maps 数: {}", maps_manager.map_count());
    
    let maps = maps_manager.list_maps();
    for (name, map_type, key_size, value_size) in maps {
        println!("     - {} ({:?}): key={} bytes, value={} bytes", 
            name, map_type, key_size, value_size);
    }
    println!();

    // 6. 创建事件处理器
    println!("6. 创建事件处理器...");
    let mut event_processor = EventProcessor::with_batch_size(1000, 50);
    println!("   ✅ 事件处理器创建成功");
    println!("   - 最大缓冲区大小: 1000");
    println!("   - 批处理大小: 50");
    println!();

    // 7. 处理单个事件
    println!("7. 处理单个事件...");
    let event1 = EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1234,
        tid: 5678,
        timestamp: std::time::SystemTime::now(),
        data: vec![1, 2, 3, 4, 5],
    };
    event_processor.process_event(event1)?;
    println!("   ✅ 事件处理成功");
    println!("   - 当前事件数: {}", event_processor.event_count());
    println!();

    // 8. 批量处理事件
    println!("8. 批量处理事件...");
    let mut batch_events = Vec::new();
    for i in 0..20 {
        batch_events.push(EbpfEvent {
            event_type: if i % 3 == 0 {
                EbpfEventType::CpuSample
            } else if i % 3 == 1 {
                EbpfEventType::NetworkPacket
            } else {
                EbpfEventType::Syscall
            },
            pid: 1000 + (i % 10),
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![0; 50],
        });
    }
    event_processor.process_batch(batch_events)?;
    println!("   ✅ 批量处理成功");
    println!("   - 当前事件数: {}", event_processor.event_count());
    println!();

    // 9. 事件过滤
    println!("9. 事件过滤...");
    let cpu_events = event_processor.filter_by_type(EbpfEventType::CpuSample);
    let network_events = event_processor.filter_by_type(EbpfEventType::NetworkPacket);
    let pid_1005_events = event_processor.filter_by_pid(1005);
    
    println!("   ✅ 事件过滤成功");
    println!("   - CPU 采样事件: {} 个", cpu_events.len());
    println!("   - 网络包事件: {} 个", network_events.len());
    println!("   - PID 1005 的事件: {} 个", pid_1005_events.len());
    println!();

    // 10. 刷新事件
    println!("10. 刷新事件缓冲区...");
    let flushed_events = event_processor.flush_events()?;
    println!("   ✅ 事件刷新成功");
    println!("   - 刷新事件数: {}", flushed_events.len());
    println!("   - 当前事件数: {}", event_processor.event_count());
    println!();

    // 11. Maps 操作演示
    println!("11. Maps 操作演示...");
    let test_key = vec![1, 2, 3, 4];
    let test_value = vec![5, 6, 7, 8, 9, 10, 11, 12];
    
    // 写入 Map（不提供 Bpf 实例，仅演示 API）
    maps_manager.write_map("event_map", &test_key, &test_value, None)?;
    println!("   ✅ Map 写入成功");
    
    // 读取 Map
    let read_value = maps_manager.read_map("event_map", &test_key, None)?;
    println!("   ✅ Map 读取成功");
    println!("   - 读取的值大小: {} bytes", read_value.len());
    
    // 删除键值对
    maps_manager.delete_map("event_map", &test_key)?;
    println!("   ✅ Map 键值对删除成功");
    println!();

    // 12. 清理资源
    println!("12. 清理资源...");
    probe_manager.detach_all()?;
    loader.unload()?;
    event_processor.clear();
    println!("   ✅ 资源清理完成");
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF 完整功能示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
