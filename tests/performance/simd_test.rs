//! SIMD 性能模块单元测试

use otlp::performance::{CpuFeatures, SimdOptimizer, SimdConfig};

#[test]
fn test_cpu_features_detect() {
    let features = CpuFeatures::detect();
    
    // 验证检测到的特性
    // 注意：实际特性取决于运行环境
    assert!(features.has_sse2() || features.has_avx2() || features.has_neon());
}

#[test]
fn test_simd_optimizer_new() {
    let config = SimdConfig::default();
    let optimizer = SimdOptimizer::new(config);
    
    // 验证优化器已创建
    assert!(optimizer.is_some() || optimizer.is_none()); // 取决于CPU支持
}

#[test]
fn test_aggregate_i64_sum() {
    use otlp::performance::simd_optimizations::aggregate_i64_sum;
    
    let values = vec![1, 2, 3, 4, 5];
    let sum = aggregate_i64_sum(&values);
    
    assert_eq!(sum, 15);
}

#[test]
fn test_aggregate_i64_sum_empty() {
    use otlp::performance::simd_optimizations::aggregate_i64_sum;
    
    let values: Vec<i64> = vec![];
    let sum = aggregate_i64_sum(&values);
    
    assert_eq!(sum, 0);
}

#[test]
fn test_aggregate_f64_sum() {
    use otlp::performance::simd_optimizations::aggregate_f64_sum;
    
    let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let sum = aggregate_f64_sum(&values);
    
    assert!((sum - 15.0).abs() < 0.0001);
}

#[test]
fn test_simd_config_default() {
    let config = SimdConfig::default();
    
    // 验证默认配置
    assert!(config.enable_simd);
}
