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
}
