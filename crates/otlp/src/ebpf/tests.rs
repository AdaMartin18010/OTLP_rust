//! eBPF 模块单元测试

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ebpf::types::{EbpfConfig, EbpfEvent, EbpfEventType};

    #[test]
    fn test_ebpf_config_default() {
        let config = EbpfConfig::default();
        assert_eq!(config.enable_cpu_profiling, true);
        assert_eq!(config.sample_rate, 99);
        assert_eq!(config.max_samples, 100000);
    }

    #[test]
    fn test_ebpf_config_builder() {
        let config = EbpfConfig::new()
            .with_sample_rate(50)
            .with_network_tracing(true)
            .with_syscall_tracing(true);

        assert_eq!(config.sample_rate, 50);
        assert_eq!(config.enable_network_tracing, true);
        assert_eq!(config.enable_syscall_tracing, true);
    }

    #[test]
    fn test_ebpf_event_new() {
        let event = EbpfEvent::new(
            EbpfEventType::CpuSample,
            1234,
            5678,
            vec![1, 2, 3, 4],
        );

        assert_eq!(event.event_type, EbpfEventType::CpuSample);
        assert_eq!(event.pid, 1234);
        assert_eq!(event.tid, 5678);
        assert_eq!(event.data, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_ebpf_event_types() {
        let types = vec![
            EbpfEventType::CpuSample,
            EbpfEventType::NetworkPacket,
            EbpfEventType::Syscall,
            EbpfEventType::MemoryAlloc,
            EbpfEventType::MemoryFree,
        ];

        for event_type in types {
            let event = EbpfEvent::new(event_type, 1, 1, vec![]);
            assert_eq!(event.event_type, event_type);
        }
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_ebpf_loader_new() {
        let config = EbpfConfig::default();
        let loader = super::loader::EbpfLoader::new(config);

        // 验证加载器已创建
        assert_eq!(loader.config().sample_rate, 99);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_probe_manager_new() {
        let mut manager = super::probes::ProbeManager::new();

        // 验证探针管理器已创建
        assert!(manager.attach_kprobe("test", "test_func").is_ok());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_event_processor_new() {
        let processor = super::events::EventProcessor::new(1000);

        // 验证事件处理器已创建
        assert_eq!(processor.event_count(), 0);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_maps_manager_new() {
        let manager = super::maps::MapsManager::new();

        // 验证 Maps 管理器已创建
        // 可以测试基本功能
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_cpu_profiler_new() {
        let config = EbpfConfig::default();
        let profiler = super::profiling::EbpfCpuProfiler::new(config);

        // 验证性能分析器已创建
        // 注意：实际加载功能待实现
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_network_tracer_new() {
        let config = EbpfConfig::default();
        let tracer = super::networking::EbpfNetworkTracer::new(config);

        // 验证网络追踪器已创建
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_syscall_tracer_new() {
        let config = EbpfConfig::default();
        let tracer = super::syscalls::EbpfSyscallTracer::new(config);

        // 验证系统调用追踪器已创建
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_memory_tracer_new() {
        let config = EbpfConfig::default();
        let tracer = super::memory::EbpfMemoryTracer::new(config);

        // 验证内存追踪器已创建
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_probe_manager_operations() {
        let mut manager = super::probes::ProbeManager::new();

        // 测试附加探针
        assert!(manager.attach_kprobe("test_kprobe", "test_func").is_ok());
        assert!(manager.attach_uprobe("test_uprobe", "/bin/test", "test_symbol").is_ok());
        assert!(manager.attach_tracepoint("test_tp", "syscalls", "sys_enter_open").is_ok());

        // 测试探针数量
        assert_eq!(manager.probe_count(), 3);

        // 测试列出探针
        let probes = manager.list_probes();
        assert_eq!(probes.len(), 3);

        // 测试分离探针
        assert!(manager.detach("test_kprobe").is_ok());
        assert_eq!(manager.probe_count(), 2);

        // 测试分离所有探针
        assert!(manager.detach_all().is_ok());
        assert_eq!(manager.probe_count(), 0);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_event_processor_operations() {
        let mut processor = super::events::EventProcessor::new(100);

        // 测试处理事件
        let event1 = EbpfEvent::new(EbpfEventType::CpuSample, 1000, 2000, vec![1, 2, 3]);
        let event2 = EbpfEvent::new(EbpfEventType::NetworkPacket, 1000, 2000, vec![4, 5, 6]);
        let event3 = EbpfEvent::new(EbpfEventType::Syscall, 2000, 3000, vec![7, 8, 9]);

        assert!(processor.process_event(event1.clone()).is_ok());
        assert!(processor.process_event(event2.clone()).is_ok());
        assert!(processor.process_event(event3.clone()).is_ok());

        // 测试事件数量
        assert_eq!(processor.event_count(), 3);

        // 测试按类型过滤
        let cpu_events = processor.filter_by_type(EbpfEventType::CpuSample);
        assert_eq!(cpu_events.len(), 1);

        // 测试按 PID 过滤
        let pid_events = processor.filter_by_pid(1000);
        assert_eq!(pid_events.len(), 2);

        // 测试刷新事件
        let flushed = processor.flush_events().unwrap();
        assert_eq!(flushed.len(), 3);
        assert_eq!(processor.event_count(), 0);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_maps_manager_operations() {
        let mut manager = super::maps::MapsManager::new();

        // 测试注册 Map
        manager.register_map(
            "test_map".to_string(),
            super::maps::MapType::Hash,
            4,
            8,
        );

        assert_eq!(manager.map_count(), 1);

        // 测试获取 Map 信息
        let info = manager.get_map_info("test_map");
        assert!(info.is_some());
        assert_eq!(info.unwrap().key_size, 4);
        assert_eq!(info.unwrap().value_size, 8);

        // 测试列出 Maps
        let maps = manager.list_maps();
        assert_eq!(maps.len(), 1);

        // 测试读取和写入（占位实现）
        assert!(manager.write_map("test_map", &[1, 2, 3, 4], &[5, 6, 7, 8]).is_ok());
        assert!(manager.read_map("test_map", &[1, 2, 3, 4]).is_ok());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_loader_validation() {
        let config = EbpfConfig::default();
        let loader = super::loader::EbpfLoader::new(config);

        // 测试验证空程序
        let empty_program = vec![];
        assert!(loader.validate_program(&empty_program).is_err());

        // 测试验证过短程序
        let short_program = vec![1, 2, 3];
        assert!(loader.validate_program(&short_program).is_err());

        // 测试验证有效 ELF 格式
        let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
        elf_program.extend(vec![0; 100]);
        assert!(loader.validate_program(&elf_program).is_ok());

        // 测试检查加载状态
        assert!(!loader.is_loaded());
    }

    #[test]
    fn test_ebpf_overhead_metrics_default() {
        use crate::ebpf::types::EbpfOverheadMetrics;
        let metrics = EbpfOverheadMetrics::default();
        assert_eq!(metrics.cpu_percent, 0.0);
        assert_eq!(metrics.memory_bytes, 0);
        assert_eq!(metrics.event_latency_us, 0);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_cpu_profiler_lifecycle() {
        let config = EbpfConfig::default();
        let mut profiler = super::profiling::EbpfCpuProfiler::new(config.clone());

        // 测试初始状态
        assert!(!profiler.is_running());
        assert_eq!(profiler.config().sample_rate, config.sample_rate);

        // 测试启动
        assert!(profiler.start().is_ok());
        assert!(profiler.is_running());

        // 测试暂停和恢复
        assert!(profiler.pause().is_ok());
        assert!(profiler.resume().is_ok());

        // 测试停止
        let profile = profiler.stop();
        assert!(profile.is_ok());
        assert!(!profiler.is_running());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_network_tracer_lifecycle() {
        let config = EbpfConfig::default();
        let mut tracer = super::networking::EbpfNetworkTracer::new(config.clone());

        // 测试初始状态
        assert!(!tracer.is_running());
        assert_eq!(tracer.config().sample_rate, config.sample_rate);

        // 测试启动
        assert!(tracer.start().is_ok());
        assert!(tracer.is_running());

        // 测试获取统计信息
        let stats = tracer.get_stats();
        assert_eq!(stats.packets_captured, 0);

        // 测试停止
        let events = tracer.stop();
        assert!(events.is_ok());
        assert!(!tracer.is_running());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_syscall_tracer_lifecycle() {
        let config = EbpfConfig::default();
        let mut tracer = super::syscalls::EbpfSyscallTracer::new(config.clone());

        // 测试初始状态
        assert!(!tracer.is_running());

        // 测试启动
        assert!(tracer.start().is_ok());
        assert!(tracer.is_running());

        // 测试过滤系统调用
        assert!(tracer.filter_syscall("open", true).is_ok());
        assert!(tracer.filter_syscall("read", false).is_ok());

        // 测试获取统计信息
        let stats = tracer.get_stats();
        assert_eq!(stats.syscalls_traced, 0);

        // 测试停止
        let events = tracer.stop();
        assert!(events.is_ok());
        assert!(!tracer.is_running());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_memory_tracer_lifecycle() {
        let config = EbpfConfig::default();
        let mut tracer = super::memory::EbpfMemoryTracer::new(config.clone());

        // 测试初始状态
        assert!(!tracer.is_running());

        // 测试启动
        assert!(tracer.start().is_ok());
        assert!(tracer.is_running());

        // 测试获取统计信息
        let stats = tracer.get_stats();
        assert_eq!(stats.allocations, 0);
        assert_eq!(stats.frees, 0);

        // 测试停止
        let events = tracer.stop();
        assert!(events.is_ok());
        assert!(!tracer.is_running());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_profiler_stop_before_start() {
        let config = EbpfConfig::default();
        let mut profiler = super::profiling::EbpfCpuProfiler::new(config);

        // 测试未启动时停止应该失败
        let result = profiler.stop();
        assert!(result.is_err());
    }
}
