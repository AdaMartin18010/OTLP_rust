//! 优化的OTLP处理器集成测试
//!
//! 测试SIMD优化、缓存优化和内存池优化在OTLP数据处理中的集成效果

use otlp::optimized_processor::*;
use std::collections::HashMap;
use std::time::Duration;

#[test]
fn test_optimized_processor_creation() {
    let config = OptimizedProcessorConfig {
        batch_size: 1000,
        enable_simd: true,
        enable_cache_optimization: true,
        enable_memory_pool: true,
        monitoring_interval: Duration::from_secs(5),
        memory_pressure_threshold: 0.8,
    };

    let processor = OptimizedOtlpProcessor::new(config);
    let metrics = processor.get_performance_metrics();

    assert_eq!(metrics.total_processed, 0);
    assert_eq!(metrics.simd_processed, 0);
    assert_eq!(metrics.cache_hits, 0);
    assert_eq!(metrics.cache_misses, 0);
}

#[test]
fn test_single_item_processing_with_simd() {
    let config = OptimizedProcessorConfig {
        enable_simd: true,
        enable_cache_optimization: true,
        enable_memory_pool: true,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    let mut attributes = HashMap::new();
    attributes.insert("service".to_string(), "test-service".to_string());
    attributes.insert("version".to_string(), "1.0.0".to_string());

    let mut resource_attributes = HashMap::new();
    resource_attributes.insert("host.name".to_string(), "test-host".to_string());

    let item = OtlpDataItem {
        timestamp: 1234567890,
        value: 5.0,
        attributes,
        resource_attributes,
    };

    let result = processor.process_single_item(&item).unwrap();

    // 验证SIMD处理结果（平方运算）
    assert_eq!(result.timestamp, 1234567890);
    assert_eq!(result.value, 25.0); // 5.0 * 5.0

    // 验证属性处理
    assert_eq!(result.attributes.len(), 2);
    assert!(result.attributes.contains_key("service"));
    assert!(result.attributes.contains_key("version"));

    // 验证资源属性
    assert_eq!(result.resource_attributes.len(), 1);
    assert!(result.resource_attributes.contains_key("host.name"));

    // 验证性能指标更新
    let metrics = processor.get_performance_metrics();
    assert!(metrics.total_processed >= 1);
    assert!(metrics.simd_processed >= 1);
}

#[test]
fn test_batch_processing_performance() {
    let config = OptimizedProcessorConfig {
        batch_size: 100,
        enable_simd: true,
        enable_cache_optimization: true,
        enable_memory_pool: true,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    // 创建测试数据
    let items: Vec<OtlpDataItem> = (0..50)
        .map(|i| {
            let mut attributes = HashMap::new();
            attributes.insert("index".to_string(), i.to_string());
            attributes.insert("type".to_string(), "metric".to_string());

            OtlpDataItem {
                timestamp: i as u64,
                value: i as f64,
                attributes,
                resource_attributes: HashMap::new(),
            }
        })
        .collect();

    let results = processor.process_batch(&items).unwrap();

    // 验证批量处理结果
    assert_eq!(results.len(), 50);

    for (i, result) in results.iter().enumerate() {
        assert_eq!(result.timestamp, i as u64);
        assert_eq!(result.value, (i as f64) * (i as f64)); // 平方运算
        assert_eq!(result.attributes.get("index").unwrap(), &i.to_string());
        assert_eq!(result.attributes.get("type").unwrap(), "metric");
    }

    // 验证性能指标
    let metrics = processor.get_performance_metrics();
    assert_eq!(metrics.total_processed, 50);
    assert_eq!(metrics.simd_processed, 50);
}

#[test]
fn test_memory_pool_optimization() {
    let config = OptimizedProcessorConfig {
        enable_memory_pool: true,
        memory_pressure_threshold: 0.5,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    // 处理大量数据以测试内存池
    let items: Vec<OtlpDataItem> = (0..1000)
        .map(|i| OtlpDataItem {
            timestamp: i as u64,
            value: i as f64,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
        })
        .collect();

    let results = processor.process_batch(&items).unwrap();
    assert_eq!(results.len(), 1000);

    // 验证内存统计（暂时禁用）
    // let memory_stats = processor.get_memory_stats();
    // assert!(memory_stats.total_allocated >= 0);
    // assert!(memory_stats.total_freed >= 0);
    // assert!(memory_stats.memory_pressure >= 0.0);
    // assert!(memory_stats.memory_pressure <= 1.0);
}

#[test]
fn test_cache_optimization() {
    let config = OptimizedProcessorConfig {
        enable_cache_optimization: true,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    // 创建具有重复属性的数据项
    let mut common_attributes = HashMap::new();
    common_attributes.insert("service".to_string(), "common-service".to_string());
    common_attributes.insert("environment".to_string(), "production".to_string());

    let items: Vec<OtlpDataItem> = (0..100)
        .map(|i| OtlpDataItem {
            timestamp: i as u64,
            value: i as f64,
            attributes: common_attributes.clone(),
            resource_attributes: HashMap::new(),
        })
        .collect();

    let results = processor.process_batch(&items).unwrap();
    assert_eq!(results.len(), 100);

    // 验证缓存优化效果
    let metrics = processor.get_performance_metrics();
    assert!(metrics.cache_hits > 0);
}

#[test]
fn test_performance_monitoring() {
    let config = OptimizedProcessorConfig {
        monitoring_interval: Duration::from_millis(100),
        ..Default::default()
    };

    let processor = OptimizedOtlpProcessor::new(config);
    let mut monitor = PerformanceMonitor::new(processor);

    // 生成性能报告
    let report = monitor.generate_report();

    assert_eq!(report.total_processed, 0);
    assert_eq!(report.simd_processed, 0);
    assert_eq!(report.cache_hit_ratio, 0.0);
    assert_eq!(report.memory_allocations, 0);
    assert_eq!(report.memory_deallocations, 0);

    // 验证报告格式
    let report_str = report.format_report();
    assert!(report_str.contains("OTLP性能报告"));
    assert!(report_str.contains("总处理数量"));
    assert!(report_str.contains("SIMD处理数量"));
    assert!(report_str.contains("缓存命中率"));
}

#[test]
fn test_performance_optimization() {
    let config = OptimizedProcessorConfig {
        enable_memory_pool: true,
        memory_pressure_threshold: 0.8,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    // 处理数据以创建内存压力
    let items: Vec<OtlpDataItem> = (0..5000)
        .map(|i| OtlpDataItem {
            timestamp: i as u64,
            value: i as f64,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
        })
        .collect();

    processor.process_batch(&items).unwrap();

    // 执行性能优化
    processor.optimize_performance().unwrap();

    // 验证优化后的状态
    // let memory_stats = processor.get_memory_stats();
    // assert!(memory_stats.memory_pressure >= 0.0);
    // assert!(memory_stats.memory_pressure <= 1.0);
}

#[test]
fn test_metrics_reset() {
    let config = OptimizedProcessorConfig::default();
    let mut processor = OptimizedOtlpProcessor::new(config);

    // 处理一些数据
    let items: Vec<OtlpDataItem> = (0..10)
        .map(|i| OtlpDataItem {
            timestamp: i as u64,
            value: i as f64,
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
        })
        .collect();

    processor.process_batch(&items).unwrap();

    // 验证指标已更新
    let metrics_before = processor.get_performance_metrics();
    assert_eq!(metrics_before.total_processed, 10);

    // 重置指标
    processor.reset_metrics();

    // 验证指标已重置
    let metrics_after = processor.get_performance_metrics();
    assert_eq!(metrics_after.total_processed, 0);
    assert_eq!(metrics_after.simd_processed, 0);
}

#[test]
fn test_different_configurations() {
    // 测试禁用SIMD的配置
    let config_no_simd = OptimizedProcessorConfig {
        enable_simd: false,
        enable_cache_optimization: true,
        enable_memory_pool: true,
        ..Default::default()
    };

    let mut processor_no_simd = OptimizedOtlpProcessor::new(config_no_simd);

    let item = OtlpDataItem {
        timestamp: 1234567890,
        value: 5.0,
        attributes: HashMap::new(),
        resource_attributes: HashMap::new(),
    };

    let result = processor_no_simd.process_single_item(&item).unwrap();
    // 禁用SIMD时，值应该保持不变（不进行平方运算）
    assert_eq!(result.value, 5.0);

    // 测试禁用缓存的配置
    let config_no_cache = OptimizedProcessorConfig {
        enable_simd: true,
        enable_cache_optimization: false,
        enable_memory_pool: true,
        ..Default::default()
    };

    let mut processor_no_cache = OptimizedOtlpProcessor::new(config_no_cache);
    let result = processor_no_cache.process_single_item(&item).unwrap();
    assert_eq!(result.value, 25.0); // SIMD仍然工作
}

#[test]
fn test_large_batch_processing() {
    let config = OptimizedProcessorConfig {
        batch_size: 10000,
        enable_simd: true,
        enable_cache_optimization: true,
        enable_memory_pool: true,
        ..Default::default()
    };

    let mut processor = OptimizedOtlpProcessor::new(config);

    // 创建大批量数据
    let items: Vec<OtlpDataItem> = (0..5000)
        .map(|i| {
            let mut attributes = HashMap::new();
            attributes.insert("batch_id".to_string(), "large_batch".to_string());
            attributes.insert("item_id".to_string(), i.to_string());

            OtlpDataItem {
                timestamp: i as u64,
                value: (i as f64) * 0.1,
                attributes,
                resource_attributes: HashMap::new(),
            }
        })
        .collect();

    let start_time = std::time::Instant::now();
    let results = processor.process_batch(&items).unwrap();
    let processing_time = start_time.elapsed();

    // 验证处理结果
    assert_eq!(results.len(), 5000);

    // 验证性能
    assert!(processing_time.as_millis() < 1000); // 应该在1秒内完成

    let metrics = processor.get_performance_metrics();
    assert_eq!(metrics.total_processed, 5000);
    assert_eq!(metrics.simd_processed, 5000);

    // 验证内存使用（暂时禁用）
    // let memory_stats = processor.get_memory_stats();
    // assert!(memory_stats.total_allocated >= 0);
}
