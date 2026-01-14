//! # eBPF 模块单元测试
//!
//! 提供 eBPF 模块的单元测试和集成测试。
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的测试**: 利用 Rust 1.92 的测试优化提升性能
//! - **类型安全的测试**: 使用 Rust 1.92 的类型系统确保测试的安全性

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
        assert_eq!(profiler.config().sample_rate, 100);  // 默认采样率
        assert!(!profiler.is_running());  // 初始状态未运行

        // 注意：实际加载功能需要Linux平台和aya crate集成
        // 在Linux平台上可以测试:
        // if EbpfLoader::check_system_support().is_ok() {
        //     // 加载eBPF程序并启动
        //     let program_bytes = include_bytes!("../programs/cpu_profiler.bpf.o");
        //     profiler.loader.load(program_bytes)?;
        //     profiler.start()?;
        //     assert!(profiler.is_running());
        // }
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

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_event_processor_buffer_management() {
        let mut processor = super::events::EventProcessor::new(5);

        // 添加事件直到缓冲区满
        for i in 0..5 {
            let event = EbpfEvent::new(
                EbpfEventType::CpuSample,
                1000 + i,
                2000 + i,
                vec![i as u8],
            );
            assert!(processor.process_event(event).is_ok());
        }

        assert_eq!(processor.event_count(), 5);
        assert!(processor.is_full());

        // 添加更多事件应该触发刷新
        let event = EbpfEvent::new(EbpfEventType::NetworkPacket, 1005, 2005, vec![5]);
        assert!(processor.process_event(event).is_ok());

        // 缓冲区应该被刷新，新事件被添加
        assert_eq!(processor.event_count(), 1);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_event_processor_clear() {
        let mut processor = super::events::EventProcessor::new(100);

        // 添加一些事件
        for i in 0..10 {
            let event = EbpfEvent::new(
                EbpfEventType::CpuSample,
                1000 + i,
                2000 + i,
                vec![i as u8],
            );
            processor.process_event(event).unwrap();
        }

        assert_eq!(processor.event_count(), 10);

        // 清空缓冲区
        processor.clear();
        assert_eq!(processor.event_count(), 0);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_maps_manager_registration() {
        let mut manager = super::maps::MapsManager::new();

        // 注册多个 Maps
        manager.register_map("map1".to_string(), super::maps::MapType::Hash, 4, 8);
        manager.register_map("map2".to_string(), super::maps::MapType::Array, 8, 16);
        manager.register_map("map3".to_string(), super::maps::MapType::PerfEvent, 4, 4);

        assert_eq!(manager.map_count(), 3);

        // 获取 Map 信息
        let info1 = manager.get_map_info("map1");
        assert!(info1.is_some());
        assert_eq!(info1.unwrap().map_type, super::maps::MapType::Hash);
        assert_eq!(info1.unwrap().key_size, 4);
        assert_eq!(info1.unwrap().value_size, 8);

        // 列出所有 Maps
        let maps = manager.list_maps();
        assert_eq!(maps.len(), 3);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_loader_program_validation() {
        let config = EbpfConfig::default();
        let loader = super::loader::EbpfLoader::new(config);

        // 测试空程序
        assert!(loader.validate_program(&[]).is_err());

        // 测试过短程序
        assert!(loader.validate_program(&[1, 2, 3]).is_err());

        // 测试有效 ELF 格式
        let mut valid_program = vec![0x7F, b'E', b'L', b'F'];
        valid_program.extend(vec![0; 100]);
        assert!(loader.validate_program(&valid_program).is_ok());

        // 测试无效格式
        let invalid_program = vec![0xFF, 0xFF, 0xFF, 0xFF];
        assert!(loader.validate_program(&invalid_program).is_err());
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_probe_manager_list_and_count() {
        let mut manager = super::probes::ProbeManager::new();

        // 添加多个探针
        manager.attach_kprobe("kprobe1", "func1").unwrap();
        manager.attach_uprobe("uprobe1", "/bin/test", "symbol1").unwrap();
        manager.attach_tracepoint("tp1", "syscalls", "sys_enter_open").unwrap();

        assert_eq!(manager.probe_count(), 3);

        // 列出探针
        let probes = manager.list_probes();
        assert_eq!(probes.len(), 3);
        assert_eq!(probes[0].0, "kprobe1");
        assert_eq!(probes[1].0, "uprobe1");
        assert_eq!(probes[2].0, "tp1");
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_probe_manager_detach_specific() {
        let mut manager = super::probes::ProbeManager::new();

        manager.attach_kprobe("kprobe1", "func1").unwrap();
        manager.attach_kprobe("kprobe2", "func2").unwrap();

        assert_eq!(manager.probe_count(), 2);

        // 分离指定探针
        assert!(manager.detach("kprobe1").is_ok());
        assert_eq!(manager.probe_count(), 1);

        // 分离不存在的探针应该失败
        assert!(manager.detach("nonexistent").is_err());
    }

    #[test]
    fn test_ebpf_config_validation() {
        let config = EbpfConfig::default();
        assert!(config.validate().is_ok());

        // 测试无效配置
        let mut invalid_config = EbpfConfig::default();
        invalid_config.sample_rate = 0;
        assert!(invalid_config.validate().is_err());

        invalid_config = EbpfConfig::default();
        invalid_config.max_samples = 0;
        assert!(invalid_config.validate().is_err());
    }

    #[test]
    fn test_ebpf_config_builder_chain() {
        let config = EbpfConfig::new()
            .with_sample_rate(50)
            .with_duration(std::time::Duration::from_secs(120))
            .with_enable_cpu_profiling(true)
            .with_enable_network_tracing(true)
            .with_enable_syscall_tracing(false)
            .with_enable_memory_tracing(false)
            .with_max_samples(50000);

        assert_eq!(config.sample_rate, 50);
        assert_eq!(config.duration.as_secs(), 120);
        assert!(config.enable_cpu_profiling);
        assert!(config.enable_network_tracing);
        assert!(!config.enable_syscall_tracing);
        assert!(!config.enable_memory_tracing);
        assert_eq!(config.max_samples, 50000);
    }

    #[test]
    fn test_ebpf_error_display() {
        use crate::ebpf::error::EbpfError;

        let error1 = EbpfError::UnsupportedPlatform;
        assert!(error1.to_string().contains("Linux"));

        let error2 = EbpfError::LoadFailed("测试错误".to_string());
        assert!(error2.to_string().contains("测试错误"));

        let error3 = EbpfError::AttachFailed("附加失败".to_string());
        assert!(error3.to_string().contains("附加失败"));
    }

    #[test]
    fn test_ebpf_error_conversion() {
        use crate::ebpf::error::EbpfError;
        use crate::error::OtlpError;

        let ebpf_error = EbpfError::UnsupportedPlatform;
        let otlp_error: OtlpError = ebpf_error.into();

        // 验证错误已转换
        match otlp_error {
            OtlpError::Processing(_) => {},
            _ => panic!("错误类型不匹配"),
        }
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_integration_converter_batch() {
        use super::integration::EbpfOtlpConverter;
        use crate::ebpf::types::{EbpfEvent, EbpfEventType};

        let converter = EbpfOtlpConverter::new();

        // 测试未配置的转换器
        assert!(!converter.is_configured());

        // 创建测试事件
        let events = vec![
            EbpfEvent::new(EbpfEventType::CpuSample, 1000, 2000, vec![1, 2, 3]),
            EbpfEvent::new(EbpfEventType::NetworkPacket, 1001, 2001, vec![4, 5, 6]),
        ];

        // 批量转换（无 Tracer/Meter 时应该返回空）
        let (spans, metric_count) = converter.convert_events_batch(&events).unwrap();
        assert_eq!(spans.len(), 0);
        assert_eq!(metric_count, 2);
    }
}
