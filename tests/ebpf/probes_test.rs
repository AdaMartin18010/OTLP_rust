//! eBPF Probes 单元测试

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::ProbeManager;
use otlp::error::OtlpError;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_probe_manager_new() {
    let manager = ProbeManager::new();
    // 验证管理器已创建
    assert_eq!(manager.probe_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_kprobe() {
    let mut manager = ProbeManager::new();
    
    // 测试附加kprobe（不提供Bpf实例，仅注册）
    let result = manager.attach_kprobe("test_kprobe", "tcp_v4_connect", None);
    assert!(result.is_ok());
    assert_eq!(manager.probe_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_kprobe_empty_function() {
    let mut manager = ProbeManager::new();
    
    // 测试空函数名
    let result = manager.attach_kprobe("test", "", None);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_kprobe_duplicate() {
    let mut manager = ProbeManager::new();
    
    // 附加第一个探针
    assert!(manager.attach_kprobe("test", "func1", None).is_ok());
    
    // 尝试附加同名探针
    let result = manager.attach_kprobe("test", "func2", None);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_uprobe() {
    let mut manager = ProbeManager::new();
    
    // 测试附加uprobe（不提供Bpf实例，仅注册）
    let result = manager.attach_uprobe("test_uprobe", "/usr/bin/test", "malloc", None);
    assert!(result.is_ok());
    assert_eq!(manager.probe_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_uprobe_empty_binary() {
    let mut manager = ProbeManager::new();
    
    // 测试空二进制路径
    let result = manager.attach_uprobe("test", "", "malloc", None);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_attach_tracepoint() {
    let mut manager = ProbeManager::new();
    
    // 测试附加tracepoint（不提供Bpf实例，仅注册）
    let result = manager.attach_tracepoint("test_tracepoint", "syscalls", "sys_enter_open", None);
    assert!(result.is_ok());
    assert_eq!(manager.probe_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_detach() {
    let mut manager = ProbeManager::new();
    
    // 附加探针
    assert!(manager.attach_kprobe("test", "func", None).is_ok());
    
    // 分离探针
    let result = manager.detach("test");
    assert!(result.is_ok());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_detach_nonexistent() {
    let mut manager = ProbeManager::new();
    
    // 尝试分离不存在的探针
    let result = manager.detach("nonexistent");
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_detach_all() {
    let mut manager = ProbeManager::new();
    
    // 附加多个探针
    assert!(manager.attach_kprobe("test1", "func1", None).is_ok());
    assert!(manager.attach_kprobe("test2", "func2", None).is_ok());
    
    // 分离所有探针
    let result = manager.detach_all();
    assert!(result.is_ok());
    assert_eq!(manager.probe_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_probe_count() {
    let mut manager = ProbeManager::new();
    
    assert_eq!(manager.probe_count(), 0);
    
    assert!(manager.attach_kprobe("test1", "func1", None).is_ok());
    assert_eq!(manager.probe_count(), 1);
    
    assert!(manager.attach_kprobe("test2", "func2", None).is_ok());
    assert_eq!(manager.probe_count(), 2);
}
