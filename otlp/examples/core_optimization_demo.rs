//! # 核心优化演示
//!
//! 本示例展示OTLP Rust项目中的核心性能优化功能

use otlp::{
    AdvancedSimdOptimizer, SimdOperation, CacheOptimizationManager,
    OptimizedOtlpProcessor, OptimizedProcessorConfig, OtlpDataItem,
};
use std::collections::HashMap;
use std::time::{Duration, Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 OTLP Rust 核心性能优化演示");
    println!("=====================================");

    // 1. 演示SIMD优化
    demonstrate_simd_optimization()?;
    println!("✅ SIMD优化演示完成");

    // 2. 演示缓存优化
    demonstrate_cache_optimization()?;
    println!("✅ 缓存优化演示完成");

    // 3. 演示OTLP数据处理
    demonstrate_otlp_processing()?;
    println!("✅ OTLP数据处理演示完成");

    // 4. 性能基准测试
    run_performance_benchmarks()?;
    println!("✅ 性能基准测试完成");

    println!("\n🎉 核心优化演示完成！");
    Ok(())
}

/// 演示SIMD优化功能
fn demonstrate_simd_optimization() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📊 SIMD优化演示");
    println!("----------------");

    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];

    // 测试不同的SIMD操作
    let operations = [
        (SimdOperation::Square, "平方运算"),
        (SimdOperation::Sqrt, "平方根运算"),
        (SimdOperation::Abs, "绝对值运算"),
        (SimdOperation::Add, "加法运算"),
        (SimdOperation::Multiply, "乘法运算"),
        (SimdOperation::Sin, "正弦运算"),
        (SimdOperation::Cos, "余弦运算"),
    ];

    for (operation, name) in operations.iter() {
        let start_time = Instant::now();
        unsafe {
            let result = optimizer.process_f64_array_simd(&data, *operation)?;
            let duration = start_time.elapsed();
            println!("  {}: {:?} (耗时: {:?})", name, &result[..4], duration);
        }
    }

    Ok(())
}

/// 演示缓存优化功能
fn demonstrate_cache_optimization() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n💾 缓存优化演示");
    println!("----------------");

    let cache_manager = CacheOptimizationManager::new();
    
    // 创建测试数据
    let n = 64;
    let a = vec![1.0f64; n * n];
    let b = vec![2.0f64; n * n];
    let mut c = vec![0.0f64; n * n];

    // 测试缓存友好的矩阵乘法
    let start_time = Instant::now();
    cache_manager.matrix_multiply_cache_optimized(&a, &b, &mut c, n);
    let duration = start_time.elapsed();
    
    println!("  缓存友好的矩阵乘法 ({}x{}): {:?}", n, n, duration);
    println!("  结果示例: {:?}", &c[..4]);

    // 测试缓存性能分析
    let test_data = vec![0u8; 1024 * 1024];
    let metrics = cache_manager.analyze_cache_performance(&test_data);
    println!("  缓存性能分析: 顺序访问 {:?}, 随机访问 {:?}", 
             metrics.sequential_access_time, metrics.random_access_time);

    Ok(())
}

/// 演示OTLP数据处理
fn demonstrate_otlp_processing() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📡 OTLP数据处理演示");
    println!("-------------------");

    // 配置优化的OTLP处理器
    let config = OptimizedProcessorConfig {
        batch_size: 100,
        enable_simd: true,
        enable_cache_optimization: true,
        enable_memory_pool: false, // 暂时禁用内存池
        monitoring_interval: Duration::from_secs(5),
        memory_pressure_threshold: 0.8,
    };

    let mut processor = OptimizedOtlpProcessor::new(config);
    
    // 创建模拟的OTLP数据
    let mut items = Vec::new();
    for i in 0..100 {
        let mut attributes = HashMap::new();
        attributes.insert("service".to_string(), "demo-service".to_string());
        attributes.insert("version".to_string(), "1.0.0".to_string());
        attributes.insert("instance".to_string(), format!("instance-{}", i % 10));
        
        let mut resource_attributes = HashMap::new();
        resource_attributes.insert("host.name".to_string(), format!("host-{}", i % 5));
        resource_attributes.insert("service.name".to_string(), "demo-service".to_string());
        
        items.push(OtlpDataItem {
            timestamp: i as u64,
            value: (i as f64) * 0.1,
            attributes,
            resource_attributes,
        });
    }

    println!("  创建了 {} 个OTLP数据项", items.len());
    
    // 处理单个数据项
    let start_time = Instant::now();
    let result = processor.process_single_item(&items[0])?;
    let single_time = start_time.elapsed();
    
    println!("  单个数据项处理: 值 {} -> {} (耗时: {:?})", 
             items[0].value, result.value, single_time);
    
    // 批量处理数据
    let start_time = Instant::now();
    let results = processor.process_batch(&items)?;
    let batch_time = start_time.elapsed();
    
    println!("  批量处理 {} 个数据项: {:?}", items.len(), batch_time);
    println!("  处理结果示例: 值 {} -> {}", items[0].value, results[0].value);

    // 显示性能指标
    let metrics = processor.get_performance_metrics();
    println!("  性能指标: 总处理 {}, SIMD处理 {}, 缓存命中 {}", 
             metrics.total_processed, metrics.simd_processed, metrics.cache_hits);

    Ok(())
}

/// 性能基准测试
fn run_performance_benchmarks() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 性能基准测试");
    println!("----------------");

    // SIMD性能测试
    let optimizer = AdvancedSimdOptimizer::new();
    let large_data = vec![1.0f64; 100000];
    
    let start_time = Instant::now();
    unsafe {
        let _result = optimizer.process_f64_array_simd(&large_data, SimdOperation::Square)?;
    }
    let simd_time = start_time.elapsed();
    println!("  SIMD处理 100,000 个元素: {:?}", simd_time);

    // 缓存性能测试
    let cache_manager = CacheOptimizationManager::new();
    let test_data = vec![0u8; 1024 * 1024];
    let start_time = Instant::now();
    let _metrics = cache_manager.analyze_cache_performance(&test_data);
    let cache_time = start_time.elapsed();
    println!("  缓存性能分析: {:?}", cache_time);

    // OTLP处理性能测试
    let config = OptimizedProcessorConfig::default();
    let mut processor = OptimizedOtlpProcessor::new(config);
    
    let mut test_items = Vec::new();
    for i in 0..1000 {
        test_items.push(OtlpDataItem {
            timestamp: i as u64,
            value: i as f64,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
        });
    }
    
    let start_time = Instant::now();
    let _results = processor.process_batch(&test_items)?;
    let otlp_time = start_time.elapsed();
    println!("  OTLP批量处理 1,000 个数据项: {:?}", otlp_time);

    Ok(())
}
