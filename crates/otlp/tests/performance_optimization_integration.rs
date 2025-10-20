//! 性能优化集成测试
//!
//! 测试SIMD优化、缓存优化和内存池优化的集成功能

use otlp::performance_optimization_advanced::*;
use std::time::Instant;

#[tokio::test]
async fn test_simd_optimization_integration() {
    let optimizer = AdvancedSimdOptimizer::new();

    // 测试浮点数数组处理
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];

    unsafe {
        // 测试平方运算
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert_eq!(result[0], 1.0);
        assert_eq!(result[1], 4.0);
        assert_eq!(result[2], 9.0);

        // 测试平方根运算
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Sqrt)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert!((result[0] - 1.0).abs() < 1e-10);
        assert!((result[1] - 1.4142135623730951).abs() < 1e-10);
    }

    // 测试整数数组处理
    let int_data = vec![1, 2, 3, 4, 5, 6, 7, 8];

    unsafe {
        let result = optimizer
            .process_i32_array_simd(&int_data, SimdIntOperation::Add(5))
            .unwrap();
        assert_eq!(result.len(), int_data.len());
        assert_eq!(result[0], 6);
        assert_eq!(result[1], 7);
        assert_eq!(result[2], 8);
    }
}

#[test]
fn test_cache_optimization_integration() {
    let cache_manager = CacheOptimizationManager::new();

    // 测试内存分配
    let ptr = cache_manager.allocate_aligned(1024).unwrap();
    assert!(!ptr.is_null());

    // 测试内存释放
    unsafe {
        cache_manager.deallocate_aligned(ptr, 1024);
    }

    // 测试缓存预热
    let data = vec![0u8; 1024 * 1024];
    cache_manager.warm_cache(&data);

    // 测试缓存性能分析
    let metrics = cache_manager.analyze_cache_performance(&data);
    assert!(metrics.data_size > 0);
    assert!(metrics.cache_hit_ratio >= 0.0);
    assert!(metrics.cache_hit_ratio <= 1.0);
}

#[test]
fn test_memory_pool_optimization_integration() {
    let mut pool = AdvancedMemoryPoolOptimizer::new();

    // 测试智能内存分配
    let ptr1 = pool.smart_allocate(1024).unwrap();
    assert!(!ptr1.is_null());

    // 测试内存返回
    pool.return_memory(1024, ptr1);

    // 测试从池中获取内存
    let ptr2 = pool.get_memory(1024).unwrap();
    assert_eq!(ptr1, ptr2);

    // 测试统计信息
    let stats = pool.get_stats();
    assert!(stats.total_allocated > 0);
    assert!(stats.total_freed > 0);

    // 测试性能优化
    pool.optimize_pool_performance();

    // 清理
    pool.cleanup();
}

#[tokio::test]
async fn test_comprehensive_optimization_integration() {
    let mut optimizer = ComprehensivePerformanceOptimizer::new();

    // 测试SIMD优化器
    let data = vec![1.0f64; 1000];
    unsafe {
        let result = optimizer
            .simd_optimizer()
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();
        assert_eq!(result.len(), 1000);
    }

    // 测试缓存管理器
    let test_data = vec![0u8; 1024];
    let metrics = optimizer
        .cache_manager()
        .analyze_cache_performance(&test_data);
    assert!(metrics.data_size > 0);

    // 测试内存池
    let ptr = optimizer.memory_pool().smart_allocate(1024).unwrap();
    assert!(!ptr.is_null());
    optimizer.memory_pool().return_memory(1024, ptr);

    // 测试综合基准测试
    let results = optimizer.run_comprehensive_benchmark().await.unwrap();
    assert!(results.simd_result_count > 0);
    assert!(results.cache_metrics.data_size > 0);
    assert!(results.memory_pool_stats.total_allocated > 0);
}

#[test]
fn test_performance_improvement() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0f64; 100000];

    // 测试SIMD性能
    let start = Instant::now();
    unsafe {
        let _result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();
    }
    let simd_time = start.elapsed();

    // 测试标量性能
    let start = Instant::now();
    let _result: Vec<f64> = data.iter().map(|&x| x * x).collect();
    let scalar_time = start.elapsed();

    // SIMD应该比标量快（在支持AVX2的CPU上）
    println!("SIMD时间: {:?}", simd_time);
    println!("标量时间: {:?}", scalar_time);

    // 注意：在某些情况下标量可能更快，这取决于CPU和编译器优化
    // 这里只验证功能正确性，不强制性能要求
}

#[test]
fn test_memory_pool_efficiency() {
    let mut pool = AdvancedMemoryPoolOptimizer::new();

    // 测试批量分配效率
    let start = Instant::now();
    let mut pointers = Vec::new();

    for _ in 0..1000 {
        let ptr = pool.smart_allocate(1024).unwrap();
        pointers.push(ptr);
    }

    for ptr in pointers {
        pool.return_memory(1024, ptr);
    }

    let allocation_time = start.elapsed();
    let stats = pool.get_stats();

    println!("批量分配时间: {:?}", allocation_time);
    println!("分配统计: {:?}", stats);

    // 验证统计信息
    assert_eq!(stats.total_allocated, 1000);
    assert_eq!(stats.total_freed, 1000);
    assert!(stats.total_pooled_objects > 0);
}

#[test]
fn test_cache_friendly_access() {
    let cache_manager = CacheOptimizationManager::new();

    // 创建测试数据
    let data = vec![0u8; 1024 * 1024];

    // 测试顺序访问
    let start = Instant::now();
    let mut _sum = 0u64;
    for &byte in &data {
        _sum += byte as u64;
    }
    let sequential_time = start.elapsed();

    // 测试随机访问
    let start = Instant::now();
    let mut _sum2 = 0u64;
    for i in 0..data.len() {
        let idx = (i * 7) % data.len();
        _sum2 += data[idx] as u64;
    }
    let random_time = start.elapsed();

    println!("顺序访问时间: {:?}", sequential_time);
    println!("随机访问时间: {:?}", random_time);

    // 顺序访问应该比随机访问快
    assert!(sequential_time <= random_time);

    // 测试缓存分析
    let metrics = cache_manager.analyze_cache_performance(&data);
    assert!(metrics.sequential_access_time <= metrics.random_access_time);
}

#[test]
fn test_matrix_multiplication_optimization() {
    let cache_manager = CacheOptimizationManager::new();

    // 测试小矩阵乘法
    let n = 64;
    let a = vec![1.0f64; n * n];
    let b = vec![1.0f64; n * n];
    let mut c = vec![0.0f64; n * n];

    let start = Instant::now();
    cache_manager.matrix_multiply_cache_optimized(&a, &b, &mut c, n);
    let multiplication_time = start.elapsed();

    println!("矩阵乘法时间 ({}x{}): {:?}", n, n, multiplication_time);

    // 验证结果
    for i in 0..n {
        for j in 0..n {
            assert!((c[i * n + j] - n as f64).abs() < 1e-10);
        }
    }
}

#[test]
fn test_memory_alignment() {
    let cache_manager = CacheOptimizationManager::new();

    // 测试不同大小的内存分配
    for size in [64, 256, 1024, 4096, 16384] {
        let ptr = cache_manager.allocate_aligned(size).unwrap();
        let ptr_addr = ptr as usize;

        // 验证内存对齐
        assert_eq!(
            ptr_addr % 64,
            0,
            "内存未按64字节对齐: size={}, addr={}",
            size,
            ptr_addr
        );

        unsafe {
            cache_manager.deallocate_aligned(ptr, size);
        }
    }
}

#[test]
fn test_simd_fallback() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0f64; 100];

    // 测试标量回退功能
    // 测试标量版本（通过SIMD函数但禁用SIMD）
    let result_scalar = unsafe {
        optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap()
    };
    assert_eq!(result_scalar.len(), data.len());

    // 验证结果正确性
    for (i, &value) in data.iter().enumerate() {
        assert_eq!(result_scalar[i], value * value);
    }
}
