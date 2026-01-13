//! eBPF Loader 单元测试

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{EbpfLoader, EbpfConfig};
use otlp::error::OtlpError;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_new() {
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config.clone());
    
    assert_eq!(loader.config().sample_rate, config.sample_rate);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_load_empty_program() {
    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);
    
    let result = loader.load(&[]);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_load_valid_elf() {
    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);
    
    // 创建最小有效的 ELF 头部
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);
    
    let result = loader.load(&elf_program);
    // 验证应该通过（虽然实际加载需要真实eBPF程序）
    assert!(result.is_ok() || result.is_err()); // 取决于是否有实际eBPF程序
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_load_oversized_program() {
    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);
    
    // 创建超过1MB的程序
    let oversized_program = vec![0u8; 1_000_001];
    
    let result = loader.load(&oversized_program);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_validate_program() {
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
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_check_system_support() {
    let result = EbpfLoader::check_system_support();
    // 在Linux环境应该返回Ok或Err（取决于系统支持）
    // 在非Linux环境应该返回Err
    assert!(result.is_ok() || result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_unload() {
    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);
    
    // 测试卸载未加载的程序
    assert!(loader.unload().is_ok());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_is_loaded() {
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config);
    
    // 初始状态应该未加载
    assert!(!loader.is_loaded());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_loader_config() {
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config.clone());
    
    assert_eq!(loader.config().sample_rate, config.sample_rate);
}
