//! eBPF 端到端集成测试
//!
//! 测试 eBPF 模块的完整工作流程

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfLoader, EbpfCpuProfiler, ProbeManager, MapsManager, EventProcessor,
    EbpfEvent, EbpfEventType, MapType,
};
use std::time::Duration;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_full_workflow() {
    // 1. 创建配置
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true);

    // 2. 创建加载器
    let mut loader = EbpfLoader::new(config.clone());

    // 3. 检查系统支持
    let _ = loader.check_system_support();

    // 4. 创建CPU性能分析器
    let mut profiler = EbpfCpuProfiler::new(config.clone());

    // 5. 启动性能分析
    assert!(profiler.start().is_ok());
    assert!(profiler.is_running());

    // 6. 等待一小段时间
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 7. 停止性能分析
    let _profile = profiler.stop();

    // 验证工作流程完成
    assert!(!profiler.is_running());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_probe_manager_workflow() {
    let mut manager = ProbeManager::new();

    // 附加多个探针（不提供Bpf实例，仅注册）
    assert!(manager.attach_kprobe("kprobe1", "tcp_v4_connect", None).is_ok());
    assert!(manager.attach_uprobe("uprobe1", "/usr/bin/test", "malloc", None).is_ok());
    assert!(manager.attach_tracepoint("tracepoint1", "syscalls", "sys_enter_open", None).is_ok());

    assert_eq!(manager.probe_count(), 3);

    // 分离所有探针
    assert!(manager.detach_all().is_ok());
    assert_eq!(manager.probe_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_maps_manager_workflow() {
    let mut manager = MapsManager::new();

    // 注册多个Maps
    manager.register_map("map1".to_string(), MapType::Hash, 4, 8);
    manager.register_map("map2".to_string(), MapType::Array, 8, 16);

    assert_eq!(manager.map_count(), 2);

    // 读写操作
    let key = vec![1, 2, 3, 4];
    let value = vec![5, 6, 7, 8, 9, 10, 11, 12];

    assert!(manager.write_map("map1", &key, &value, None).is_ok());
    let read_value = manager.read_map("map1", &key, None);
    assert!(read_value.is_ok());

    // 删除Map中的键值对
    assert!(manager.delete_map("map1", &key).is_ok());
    assert_eq!(manager.map_count(), 2); // Map仍然存在
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_event_processor_workflow() {
    let mut processor = EventProcessor::new(1000);

    // 处理多个事件
    for i in 0..10 {
        let event = EbpfEvent {
            event_type: if i % 2 == 0 {
                EbpfEventType::CpuSample
            } else {
                EbpfEventType::NetworkPacket
            },
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![i as u8; 10],
        };
        assert!(processor.process_event(event).is_ok());
    }

    assert_eq!(processor.event_count(), 10);

    // 过滤事件
    let cpu_events = processor.filter_events_by_type(EbpfEventType::CpuSample);
    assert_eq!(cpu_events.len(), 5);

    // 刷新事件
    let events = processor.flush_events().unwrap();
    assert_eq!(events.len(), 10);
    assert_eq!(processor.event_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[tokio::test]
async fn test_ebpf_integrated_components() {
    // 测试多个组件协同工作
    let config = EbpfConfig::default();

    // 创建各个组件
    let mut loader = EbpfLoader::new(config.clone());
    let mut profiler = EbpfCpuProfiler::new(config.clone());
    let mut probe_manager = ProbeManager::new();
    let mut maps_manager = MapsManager::new();
    let mut event_processor = EventProcessor::new(1000);

    // 初始化各个组件
    let _ = loader.check_system_support();
    assert!(profiler.start().is_ok());
    assert!(probe_manager.attach_kprobe("test", "func", None).is_ok());
    maps_manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);

    // 处理事件
    let event = EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1234,
        tid: 5678,
        timestamp: std::time::SystemTime::now(),
        data: vec![],
    };
    assert!(event_processor.process_event(event).is_ok());

    // 清理
    assert!(profiler.stop().is_ok());
    assert!(probe_manager.detach_all().is_ok());
    let _ = event_processor.flush_events();
}
