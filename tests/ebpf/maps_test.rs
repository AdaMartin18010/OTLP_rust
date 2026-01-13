//! eBPF Maps 单元测试

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use otlp::ebpf::{MapsManager, MapType};
use otlp::error::OtlpError;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_maps_manager_new() {
    let manager = MapsManager::new();
    assert_eq!(manager.map_count(), 0);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_register_map() {
    let mut manager = MapsManager::new();
    
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    assert_eq!(manager.map_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_read_map() {
    let mut manager = MapsManager::new();
    
    // 注册Map
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    
    // 读取Map（不提供Bpf实例，返回空值）
    let key = vec![1, 2, 3, 4];
    let result = manager.read_map("test_map", &key, None);
    assert!(result.is_ok());
    let value = result.unwrap();
    assert_eq!(value.len(), 8); // value_size
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_read_map_nonexistent() {
    let manager = MapsManager::new();
    
    let result = manager.read_map("nonexistent", &[1, 2, 3, 4], None);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_read_map_invalid_key_size() {
    let mut manager = MapsManager::new();
    
    // 注册Map，key_size=4
    assert!(manager.register_map("test_map".to_string(), MapType::Hash, 4, 8).is_ok());
    
    // 使用错误的key大小
    let result = manager.read_map("test_map", &[1, 2, 3], None); // key_size=3
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_write_map() {
    let mut manager = MapsManager::new();
    
    // 注册Map
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    
    // 写入Map（不提供Bpf实例，仅验证）
    let key = vec![1, 2, 3, 4];
    let value = vec![5, 6, 7, 8, 9, 10, 11, 12];
    let result = manager.write_map("test_map", &key, &value, None);
    assert!(result.is_ok());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_write_map_invalid_value_size() {
    let mut manager = MapsManager::new();
    
    // 注册Map，value_size=8
    assert!(manager.register_map("test_map".to_string(), MapType::Hash, 4, 8).is_ok());
    
    // 使用错误的value大小
    let key = vec![1, 2, 3, 4];
    let value = vec![1, 2, 3]; // value_size=3
    let result = manager.write_map("test_map", &key, &value, None);
    assert!(result.is_err());
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_delete_map() {
    let mut manager = MapsManager::new();
    
    // 注册Map
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    
    // 删除Map（注意：delete_map 方法不存在，应该是删除键值对）
    // 这里测试的是删除键值对，而不是删除Map本身
    let key = vec![1, 2, 3, 4];
    let result = manager.delete_map("test_map", &key);
    assert!(result.is_ok());
    // Map本身仍然存在，只是删除了键值对
    assert_eq!(manager.map_count(), 1);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_get_map_info() {
    let mut manager = MapsManager::new();
    
    // 注册Map
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    
    // 获取Map信息
    let info = manager.get_map_info("test_map");
    assert!(info.is_some());
    let info = info.unwrap();
    assert_eq!(info.key_size, 4);
    assert_eq!(info.value_size, 8);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_list_maps() {
    let mut manager = MapsManager::new();
    
    assert_eq!(manager.list_maps().len(), 0);
    
    // 注册多个Map
    manager.register_map("map1".to_string(), MapType::Hash, 4, 8);
    manager.register_map("map2".to_string(), MapType::Array, 8, 16);
    
    let maps = manager.list_maps();
    assert_eq!(maps.len(), 2);
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[test]
fn test_map_count() {
    let mut manager = MapsManager::new();
    
    assert_eq!(manager.map_count(), 0);
    
    assert!(manager.register_map("map1".to_string(), MapType::Hash, 4, 8).is_ok());
    assert_eq!(manager.map_count(), 1);
    
    assert!(manager.register_map("map2".to_string(), MapType::Array, 8, 16).is_ok());
    assert_eq!(manager.map_count(), 2);
}
