//! eBPF Events 单元测试

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};
use std::time::SystemTime;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_event_processor_new() {
    let processor = EventProcessor::new(1000);
    assert_eq!(processor.event_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_process_event() {
    let mut processor = EventProcessor::new(1000);
    
    let event = EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1234,
        tid: 5678,
        timestamp: SystemTime::now(),
        data: vec![1, 2, 3, 4],
    };
    
    let result = processor.process_event(event);
    assert!(result.is_ok());
    assert_eq!(processor.event_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_process_event_buffer_full() {
    let mut processor = EventProcessor::new(2); // 小缓冲区
    
    // 添加事件直到缓冲区满
    for i in 0..3 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    // 缓冲区应该已刷新，当前应该只有最后一个事件
    assert!(processor.event_count() <= 2);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_flush_events() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加多个事件
    for i in 0..5 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    assert_eq!(processor.event_count(), 5);
    
    // 刷新事件
    let events = processor.flush_events().unwrap();
    assert_eq!(events.len(), 5);
    assert_eq!(processor.event_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_filter_events() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加不同类型的事件
    for i in 0..5 {
        let event_type = if i % 2 == 0 {
            EbpfEventType::CpuSample
        } else {
            EbpfEventType::NetworkPacket
        };
        
        let event = EbpfEvent {
            event_type,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    // 过滤CPU采样事件
    let cpu_events = processor.filter_events(|e| matches!(e.event_type, EbpfEventType::CpuSample));
    assert_eq!(cpu_events.len(), 3); // 0, 2, 4
    
    // 过滤网络包事件
    let network_events = processor.filter_events(|e| matches!(e.event_type, EbpfEventType::NetworkPacket));
    assert_eq!(network_events.len(), 2); // 1, 3
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_filter_events_by_type() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加不同类型的事件
    processor.process_event(EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1,
        tid: 1,
        timestamp: SystemTime::now(),
        data: vec![],
    }).unwrap();
    
    processor.process_event(EbpfEvent {
        event_type: EbpfEventType::NetworkPacket,
        pid: 2,
        tid: 2,
        timestamp: SystemTime::now(),
        data: vec![],
    }).unwrap();
    
    processor.process_event(EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 3,
        tid: 3,
        timestamp: SystemTime::now(),
        data: vec![],
    }).unwrap();
    
    // 按类型过滤
    let cpu_events = processor.filter_events_by_type(EbpfEventType::CpuSample);
    assert_eq!(cpu_events.len(), 2);
    
    let network_events = processor.filter_events_by_type(EbpfEventType::NetworkPacket);
    assert_eq!(network_events.len(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_get_events() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加事件
    for i in 0..3 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    // 获取事件（不刷新）
    let events = processor.get_events();
    assert_eq!(events.len(), 3);
    assert_eq!(processor.event_count(), 3); // 事件仍在缓冲区
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_event_count() {
    let mut processor = EventProcessor::new(1000);
    
    assert_eq!(processor.event_count(), 0);
    
    for i in 0..5 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
        assert_eq!(processor.event_count(), i + 1);
    }
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_process_batch() {
    use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};
    
    let mut processor = EventProcessor::new(1000);
    
    // 创建一批事件
    let mut events = Vec::new();
    for i in 0..10 {
        events.push(EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        });
    }
    
    // 批量处理
    let result = processor.process_batch(events);
    assert!(result.is_ok());
    assert_eq!(processor.event_count(), 10);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_filter_by_pid() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加不同PID的事件
    for i in 0..5 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + (i % 2), // 交替使用1000和1001
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    // 按PID过滤
    let pid_1000_events = processor.filter_by_pid(1000);
    assert_eq!(pid_1000_events.len(), 3); // 0, 2, 4
    
    let pid_1001_events = processor.filter_by_pid(1001);
    assert_eq!(pid_1001_events.len(), 2); // 1, 3
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_clear() {
    let mut processor = EventProcessor::new(1000);
    
    // 添加事件
    for i in 0..5 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    assert_eq!(processor.event_count(), 5);
    
    // 清空
    processor.clear();
    assert_eq!(processor.event_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_is_full() {
    let mut processor = EventProcessor::new(2); // 小缓冲区
    
    assert!(!processor.is_full());
    
    // 添加事件直到满
    for i in 0..2 {
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: SystemTime::now(),
            data: vec![],
        };
        processor.process_event(event).unwrap();
    }
    
    assert!(processor.is_full());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_with_batch_size() {
    let processor = EventProcessor::with_batch_size(1000, 50);
    assert_eq!(processor.event_count(), 0);
}
