//! 扩展SIMD操作集成测试
//!
//! 测试新增的SIMD数学运算功能

use otlp::performance_optimization_advanced::*;
use std::time::Instant;

#[test]
fn test_extended_simd_operations() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];

    // 测试基础运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert_eq!(result[0], 1.0);
        assert_eq!(result[1], 4.0);
    }

    // 测试平方根运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Sqrt)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert!((result[0] - 1.0).abs() < 1e-10);
        assert!((result[1] - 1.4142135623730951).abs() < 1e-10);
    }

    // 测试绝对值运算
    let negative_data = vec![-1.0, -2.0, -3.0, -4.0];
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&negative_data, SimdOperation::Abs)
            .unwrap();
        assert_eq!(result.len(), negative_data.len());
        assert_eq!(result[0], 1.0);
        assert_eq!(result[1], 2.0);
    }

    // 测试加法运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Add)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert_eq!(result[0], 2.0); // 1.0 + 1.0
        assert_eq!(result[1], 3.0); // 2.0 + 1.0
    }

    // 测试乘法运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Multiply)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert_eq!(result[0], 2.0); // 1.0 * 2.0
        assert_eq!(result[1], 4.0); // 2.0 * 2.0
    }

    // 测试除法运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Divide)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert_eq!(result[0], 0.5); // 1.0 / 2.0
        assert_eq!(result[1], 1.0); // 2.0 / 2.0
    }
}

#[test]
fn test_trigonometric_operations() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![
        0.0,
        std::f64::consts::PI / 4.0,
        std::f64::consts::PI / 2.0,
        std::f64::consts::PI,
    ];

    // 测试正弦运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Sin)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert!((result[0] - 0.0).abs() < 1e-10); // sin(0) = 0
        assert!((result[1] - 0.7071067811865476).abs() < 1e-10); // sin(π/4) ≈ 0.707
    }

    // 测试余弦运算
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&data, SimdOperation::Cos)
            .unwrap();
        assert_eq!(result.len(), data.len());
        assert!((result[0] - 1.0).abs() < 1e-10); // cos(0) = 1
        assert!((result[1] - 0.7071067811865476).abs() < 1e-10); // cos(π/4) ≈ 0.707
    }

    // 测试正切运算
    let tan_data = vec![0.0, std::f64::consts::PI / 4.0];
    unsafe {
        let result = optimizer
            .process_f64_array_simd(&tan_data, SimdOperation::Tan)
            .unwrap();
        assert_eq!(result.len(), tan_data.len());
        assert!((result[0] - 0.0).abs() < 1e-10); // tan(0) = 0
        assert!((result[1] - 1.0).abs() < 1e-10); // tan(π/4) = 1
    }
}

#[test]
fn test_performance_improvement() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0f64; 100000];

    // 测试不同操作的性能
    let operations = [
        SimdOperation::Square,
        SimdOperation::Sqrt,
        SimdOperation::Abs,
        SimdOperation::Add,
        SimdOperation::Multiply,
        SimdOperation::Sin,
        SimdOperation::Cos,
    ];

    for operation in operations.iter() {
        let start_time = Instant::now();
        unsafe {
            let _result = optimizer.process_f64_array_simd(&data, *operation).unwrap();
        }
        let duration = start_time.elapsed();

        // 验证性能：处理10万个元素应该在合理时间内完成
        assert!(
            duration.as_millis() < 100,
            "操作 {:?} 耗时过长: {:?}",
            operation,
            duration
        );
    }
}

#[test]
fn test_result_consistency() {
    let optimizer = AdvancedSimdOptimizer::new();
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];

    // 测试多次执行结果的一致性
    unsafe {
        let result1 = optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();
        let result2 = optimizer
            .process_f64_array_simd(&data, SimdOperation::Square)
            .unwrap();

        assert_eq!(result1.len(), result2.len());
        for (a, b) in result1.iter().zip(result2.iter()) {
            assert!((a - b).abs() < 1e-10);
        }
    }
}

#[test]
fn test_memory_strategy_placeholder() {
    // 内存策略测试暂时禁用，因为AdvancedMemoryStrategyManager已移除
    // 在实际生产环境中，建议使用经过充分测试的内存池库
    println!("内存策略测试暂时禁用 - 建议使用jemalloc或tcmalloc等成熟的内存池库");
}
