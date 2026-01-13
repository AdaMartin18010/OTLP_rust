//! eBPF Maps 操作示例
//!
//! 演示如何使用 Maps 管理器进行各种类型的 Map 操作

use otlp::ebpf::{EbpfConfig, EbpfLoader, MapsManager, MapType};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF Maps 操作示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 创建配置和加载器
    println!("1. 初始化 eBPF 环境...");
    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);
    let _ = loader.check_system_support();
    println!("   ✅ eBPF 环境初始化完成");
    println!();

    // 2. 创建 Maps 管理器
    println!("2. 创建 Maps 管理器...");
    let mut maps_manager = MapsManager::new();
    println!("   ✅ Maps 管理器创建成功");
    println!();

    // 3. 注册不同类型的 Maps
    println!("3. 注册不同类型的 Maps...");
    
    // Hash Map - 用于键值对存储
    maps_manager.register_map("event_map".to_string(), MapType::Hash, 4, 8);
    println!("   ✅ Hash Map 注册成功: event_map (key: 4 bytes, value: 8 bytes)");
    
    // Array Map - 用于数组存储
    maps_manager.register_map("stats_map".to_string(), MapType::Array, 4, 16);
    println!("   ✅ Array Map 注册成功: stats_map (key: 4 bytes, value: 16 bytes)");
    
    // PerfEvent Map - 用于性能事件
    maps_manager.register_map("perf_map".to_string(), MapType::PerfEvent, 8, 32);
    println!("   ✅ PerfEvent Map 注册成功: perf_map (key: 8 bytes, value: 32 bytes)");
    
    // RingBuffer Map - 用于环形缓冲区
    maps_manager.register_map("ring_buffer".to_string(), MapType::RingBuffer, 0, 64);
    println!("   ✅ RingBuffer Map 注册成功: ring_buffer (value: 64 bytes)");
    
    println!("   - 已注册 Maps 数: {}", maps_manager.map_count());
    println!();

    // 4. 列出所有 Maps
    println!("4. 列出所有已注册的 Maps...");
    let maps = maps_manager.list_maps();
    println!("   ✅ 共注册 {} 个 Maps:", maps.len());
    for (name, map_type, key_size, value_size) in maps {
        let type_str = match map_type {
            MapType::Hash => "Hash",
            MapType::Array => "Array",
            MapType::PerfEvent => "PerfEvent",
            MapType::RingBuffer => "RingBuffer",
        };
        println!("     - {} ({}) -> key: {} bytes, value: {} bytes", 
            name, type_str, key_size, value_size);
    }
    println!();

    // 5. 写入 Hash Map
    println!("5. 写入 Hash Map...");
    let key1 = vec![1, 2, 3, 4];
    let value1 = vec![10, 20, 30, 40, 50, 60, 70, 80];
    
    match maps_manager.write_map("event_map", &key1, &value1, None) {
        Ok(()) => println!("   ✅ Hash Map 写入成功"),
        Err(e) => println!("   ⚠️  Hash Map 写入失败: {}", e),
    }
    println!();

    // 6. 读取 Hash Map
    println!("6. 读取 Hash Map...");
    match maps_manager.read_map("event_map", &key1, None) {
        Ok(value) => {
            println!("   ✅ Hash Map 读取成功");
            println!("   - 读取的值大小: {} bytes", value.len());
        },
        Err(e) => println!("   ⚠️  Hash Map 读取失败: {}", e),
    }
    println!();

    // 7. 写入 Array Map
    println!("7. 写入 Array Map...");
    let array_index = 0u32.to_ne_bytes().to_vec();
    let array_value = vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500, 1600];
    
    match maps_manager.write_map("stats_map", &array_index, &array_value, None) {
        Ok(()) => println!("   ✅ Array Map 写入成功"),
        Err(e) => println!("   ⚠️  Array Map 写入失败: {}", e),
    }
    println!();

    // 8. 读取 Array Map
    println!("8. 读取 Array Map...");
    match maps_manager.read_map("stats_map", &array_index, None) {
        Ok(value) => {
            println!("   ✅ Array Map 读取成功");
            println!("   - 读取的值大小: {} bytes", value.len());
        },
        Err(e) => println!("   ⚠️  Array Map 读取失败: {}", e),
    }
    println!();

    // 9. 删除 Hash Map 中的键值对
    println!("9. 删除 Hash Map 中的键值对...");
    match maps_manager.delete_map("event_map", &key1) {
        Ok(()) => println!("   ✅ 键值对删除成功"),
        Err(e) => println!("   ⚠️  键值对删除失败: {}", e),
    }
    println!("   - 当前 Maps 数: {} (Map 本身仍然存在)", maps_manager.map_count());
    println!();

    // 10. 获取 Map 信息
    println!("10. 获取 Map 信息...");
    if let Some(map_info) = maps_manager.get_map_info("event_map") {
        println!("   ✅ Map 信息获取成功:");
        println!("     - 名称: event_map");
        println!("     - 类型: {:?}", map_info.map_type);
        println!("     - 键大小: {} bytes", map_info.key_size);
        println!("     - 值大小: {} bytes", map_info.value_size);
    } else {
        println!("   ⚠️  Map 不存在");
    }
    println!();

    // 11. 按类型统计 Maps
    println!("11. Maps 统计...");
    let maps = maps_manager.list_maps();
    let hash_count = maps.iter().filter(|(_, t, _, _)| *t == MapType::Hash).count();
    let array_count = maps.iter().filter(|(_, t, _, _)| *t == MapType::Array).count();
    let perf_count = maps.iter().filter(|(_, t, _, _)| *t == MapType::PerfEvent).count();
    let ring_count = maps.iter().filter(|(_, t, _, _)| *t == MapType::RingBuffer).count();
    
    println!("   ✅ Maps 统计:");
    println!("     - Hash Map: {} 个", hash_count);
    println!("     - Array Map: {} 个", array_count);
    println!("     - PerfEvent Map: {} 个", perf_count);
    println!("     - RingBuffer Map: {} 个", ring_count);
    println!("     - 总计: {} 个", maps_manager.map_count());
    println!();

    // 12. 清理资源
    println!("12. 清理资源...");
    loader.unload()?;
    println!("   ✅ 资源清理完成");
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("eBPF Maps 操作示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
