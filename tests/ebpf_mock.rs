//! eBPF 模拟测试工具
//!
//! 提供 eBPF 相关的模拟数据和测试工具

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{EbpfConfig, EbpfEvent, EbpfEventType};

/// 创建测试用的 eBPF 配置
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_test_ebpf_config() -> EbpfConfig {
    EbpfConfig::default()
        .with_sample_rate(99)
        .with_enable_cpu_profiling(true)
        .with_network_tracing(false)
        .with_syscall_tracing(false)
        .with_memory_tracing(false)
}

/// 创建测试用的 eBPF 事件
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_test_ebpf_event() -> EbpfEvent {
    EbpfEvent::new(
        EbpfEventType::CpuSample,
        1000,  // pid
        2000,  // tid
        vec![0x01, 0x02, 0x03, 0x04],
    )
}

/// 创建多个测试用的 eBPF 事件
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_test_ebpf_events(count: usize) -> Vec<EbpfEvent> {
    (0..count)
        .map(|i| {
            EbpfEvent::new(
                if i % 2 == 0 {
                    EbpfEventType::CpuSample
                } else {
                    EbpfEventType::NetworkPacket
                },
                1000 + i as u32,
                2000 + i as u32,
                vec![i as u8; 4],
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_config() {
        let config = create_test_ebpf_config();
        assert_eq!(config.sample_rate, 99);
        assert!(config.enable_cpu_profiling);
        assert!(!config.enable_network_tracing);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_events_variety() {
        let events = create_test_ebpf_events(10);
        assert_eq!(events.len(), 10);

        // 验证事件类型交替
        assert_eq!(events[0].event_type, EbpfEventType::CpuSample);
        assert_eq!(events[1].event_type, EbpfEventType::NetworkPacket);
        assert_eq!(events[2].event_type, EbpfEventType::CpuSample);

        // 验证 PID 和 TID 递增
        assert_eq!(events[0].pid, 1000);
        assert_eq!(events[1].pid, 1001);
        assert_eq!(events[0].tid, 2000);
        assert_eq!(events[1].tid, 2001);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_event() {
        let event = create_test_ebpf_event();
        assert_eq!(event.event_type, EbpfEventType::CpuSample);
        assert_eq!(event.pid, 1000);
        assert_eq!(event.tid, 2000);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_events() {
        let events = create_test_ebpf_events(5);
        assert_eq!(events.len(), 5);
        assert_eq!(events[0].event_type, EbpfEventType::CpuSample);
        assert_eq!(events[1].event_type, EbpfEventType::NetworkPacket);
    }
}
