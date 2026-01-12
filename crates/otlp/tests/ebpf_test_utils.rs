//! eBPF 测试工具库
//!
//! 提供 eBPF 测试中使用的通用工具和辅助函数

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{
    EbpfConfig, EbpfEvent, EbpfEventType, EbpfLoader,
    create_recommended_config, validate_config,
};
use std::time::Duration;

/// 创建测试用的 eBPF 配置
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_test_ebpf_config() -> EbpfConfig {
    EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true)
        .with_network_tracing(false)
        .with_syscall_tracing(false)
        .with_memory_tracing(false)
        .with_duration(Duration::from_secs(10))
        .with_max_samples(1000)
}

/// 创建生产环境测试配置
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_production_test_config() -> EbpfConfig {
    create_recommended_config("production")
}

/// 创建开发环境测试配置
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_development_test_config() -> EbpfConfig {
    create_recommended_config("development")
}

/// 创建测试用的 eBPF 事件
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn create_test_ebpf_event(event_type: EbpfEventType) -> EbpfEvent {
    EbpfEvent::new(
        event_type,
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
            let event_type = match i % 4 {
                0 => EbpfEventType::CpuSample,
                1 => EbpfEventType::NetworkPacket,
                2 => EbpfEventType::Syscall,
                _ => EbpfEventType::MemoryAlloc,
            };
            create_test_ebpf_event(event_type)
        })
        .collect()
}

/// 验证配置是否有效
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn assert_valid_config(config: &EbpfConfig) {
    assert!(validate_config(config).is_ok(), "配置应该有效");
}

/// 验证配置是否无效
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn assert_invalid_config(config: &EbpfConfig) {
    assert!(validate_config(config).is_err(), "配置应该无效");
}

/// 等待一小段时间（用于异步测试）
pub async fn small_delay() {
    tokio::time::sleep(Duration::from_millis(10)).await;
}

/// 等待中等时间（用于异步测试）
pub async fn medium_delay() {
    tokio::time::sleep(Duration::from_millis(100)).await;
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
    fn test_create_production_test_config() {
        let config = create_production_test_config();
        assert_eq!(config.sample_rate, 19); // 生产环境使用低采样率
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_development_test_config() {
        let config = create_development_test_config();
        assert_eq!(config.sample_rate, 99); // 开发环境使用默认采样率
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_event() {
        let event = create_test_ebpf_event(EbpfEventType::CpuSample);
        assert_eq!(event.event_type, EbpfEventType::CpuSample);
        assert_eq!(event.pid, 1000);
        assert_eq!(event.tid, 2000);
    }

    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    #[test]
    fn test_create_test_ebpf_events() {
        let events = create_test_ebpf_events(10);
        assert_eq!(events.len(), 10);
    }

    #[tokio::test]
    async fn test_delays() {
        let start = std::time::Instant::now();
        small_delay().await;
        let elapsed = start.elapsed();
        assert!(elapsed.as_millis() >= 10);
    }
}
