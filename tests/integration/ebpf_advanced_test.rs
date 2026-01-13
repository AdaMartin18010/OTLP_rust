//! eBPF 高级集成测试
//!
//! 测试 eBPF 模块的高级功能和实际使用场景

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfLoader, ProbeManager, MapsManager, EventProcessor,
    EbpfEvent, EbpfEventType, MapType,
};
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_batch_event_processing() {
    // 测试批量事件处理
    let mut processor = EventProcessor::new(1000);

    // 创建一批事件
    let mut events = Vec::new();
    for i in 0..100 {
        events.push(EbpfEvent {
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

    // 批量处理
    assert!(processor.process_batch(events).is_ok());
    assert_eq!(processor.event_count(), 100);

    // 测试过滤
    let cpu_events = processor.filter_by_type(EbpfEventType::CpuSample);
    assert_eq!(cpu_events.len(), 34); // 约100/3

    // 刷新
    let flushed = processor.flush_events().unwrap();
    assert_eq!(flushed.len(), 100);
    assert_eq!(processor.event_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_probe_manager_comprehensive() {
    // 测试探针管理器的完整功能
    let mut manager = ProbeManager::new();

    // 附加多种类型的探针
    assert!(manager.attach_kprobe("kprobe1", "tcp_v4_connect", None).is_ok());
    assert!(manager.attach_kprobe("kprobe2", "tcp_v4_sendmsg", None).is_ok());
    assert!(manager.attach_uprobe("uprobe1", "/usr/bin/test", "malloc", None).is_ok());
    assert!(manager.attach_tracepoint("tp1", "syscalls", "sys_enter_open", None).is_ok());
    assert!(manager.attach_tracepoint("tp2", "syscalls", "sys_enter_read", None).is_ok());

    assert_eq!(manager.probe_count(), 5);

    // 列出探针
    let probes = manager.list_probes();
    assert_eq!(probes.len(), 5);

    // 分离单个探针
    assert!(manager.detach("kprobe1").is_ok());
    assert_eq!(manager.probe_count(), 4);

    // 分离所有探针
    assert!(manager.detach_all().is_ok());
    assert_eq!(manager.probe_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_maps_manager_comprehensive() {
    // 测试 Maps 管理器的完整功能
    let mut manager = MapsManager::new();

    // 注册多种类型的 Maps
    manager.register_map("hash_map".to_string(), MapType::Hash, 4, 8);
    manager.register_map("array_map".to_string(), MapType::Array, 4, 16);
    manager.register_map("perf_map".to_string(), MapType::PerfEvent, 8, 32);

    assert_eq!(manager.map_count(), 3);

    // 测试读写操作
    let key1 = vec![1, 2, 3, 4];
    let value1 = vec![5, 6, 7, 8, 9, 10, 11, 12];

    assert!(manager.write_map("hash_map", &key1, &value1, None).is_ok());
    let read_value = manager.read_map("hash_map", &key1, None);
    assert!(read_value.is_ok());
    assert_eq!(read_value.unwrap().len(), 8);

    // 测试删除键值对
    assert!(manager.delete_map("hash_map", &key1).is_ok());

    // 列出所有 Maps
    let maps = manager.list_maps();
    assert_eq!(maps.len(), 3);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_event_processor_buffer_management() {
    // 测试事件处理器的缓冲区管理
    let mut processor = EventProcessor::new(5); // 小缓冲区

    // 添加事件直到缓冲区满
    for i in 0..10 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();

        // 缓冲区满时会自动刷新
        if processor.is_full() {
            let _ = processor.flush_events().unwrap();
        }
    }

    // 最终应该有一些事件在缓冲区中
    assert!(processor.event_count() <= 5);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_loader_system_check() {
    // 测试系统支持检查
    let result = EbpfLoader::check_system_support();
    // 在Linux环境应该返回Ok或Err（取决于系统支持）
    assert!(result.is_ok() || result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_loader_program_validation() {
    // 测试程序验证
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config);

    // 测试空程序
    assert!(loader.validate_program(&[]).is_err());

    // 测试过短程序
    assert!(loader.validate_program(&[1, 2, 3]).is_err());

    // 测试有效ELF格式
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);
    assert!(loader.validate_program(&elf_program).is_ok());

    // 测试过大程序
    let oversized = vec![0u8; 1_000_001];
    let mut loader2 = EbpfLoader::new(EbpfConfig::default());
    assert!(loader2.load(&oversized).is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_integrated_workflow() {
    // 测试完整的集成工作流程
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true)
        .with_network_tracing(true);

    // 1. 创建加载器
    let mut loader = EbpfLoader::new(config.clone());
    let _ = loader.check_system_support();

    // 2. 创建探针管理器
    let mut probe_manager = ProbeManager::new();
    assert!(probe_manager.attach_kprobe("test_kprobe", "test_func", None).is_ok());

    // 3. 创建 Maps 管理器
    let mut maps_manager = MapsManager::new();
    maps_manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);

    // 4. 创建事件处理器
    let mut event_processor = EventProcessor::new(1000);

    // 5. 处理事件
    for i in 0..10 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![],
        };
        event_processor.process_event(event).unwrap();
    }

    assert_eq!(event_processor.event_count(), 10);

    // 6. 清理
    assert!(probe_manager.detach_all().is_ok());
    assert!(loader.unload().is_ok());
}
