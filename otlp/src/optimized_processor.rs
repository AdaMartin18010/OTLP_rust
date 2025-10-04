//! # 优化的OTLP数据处理器
//!
//! 本模块将SIMD优化、缓存优化和内存池优化集成到OTLP数据处理流程中

use crate::performance_optimization_advanced::*;
use anyhow::Result;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// OTLP数据处理器配置
#[derive(Debug, Clone)]
pub struct OptimizedProcessorConfig {
    /// 批处理大小
    pub batch_size: usize,
    /// 是否启用SIMD优化
    pub enable_simd: bool,
    /// 是否启用缓存优化
    pub enable_cache_optimization: bool,
    /// 是否启用内存池优化
    pub enable_memory_pool: bool,
    /// 性能监控间隔
    pub monitoring_interval: Duration,
    /// 内存压力阈值
    pub memory_pressure_threshold: f64,
}

impl Default for OptimizedProcessorConfig {
    fn default() -> Self {
        Self {
            batch_size: 1000,
            enable_simd: true,
            enable_cache_optimization: true,
            enable_memory_pool: true,
            monitoring_interval: Duration::from_secs(5),
            memory_pressure_threshold: 0.8,
        }
    }
}

/// OTLP数据项
#[derive(Debug, Clone)]
pub struct OtlpDataItem {
    pub timestamp: u64,
    pub value: f64,
    pub attributes: HashMap<String, String>,
    pub resource_attributes: HashMap<String, String>,
}

/// 优化的OTLP数据处理器
pub struct OptimizedOtlpProcessor {
    config: OptimizedProcessorConfig,
    simd_optimizer: AdvancedSimdOptimizer,
    cache_manager: CacheOptimizationManager,
    // memory_strategy: AdvancedMemoryStrategyManager, // 暂时禁用以避免线程安全问题
    performance_metrics: PerformanceMetrics,
    last_monitoring_time: Instant,
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub total_processed: u64,
    pub simd_processed: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub memory_allocations: u64,
    pub memory_deallocations: u64,
    pub average_processing_time: Duration,
    pub memory_pressure: f64,
    pub last_update_time: Instant,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            total_processed: 0,
            simd_processed: 0,
            cache_hits: 0,
            cache_misses: 0,
            memory_allocations: 0,
            memory_deallocations: 0,
            average_processing_time: Duration::ZERO,
            memory_pressure: 0.0,
            last_update_time: Instant::now(),
        }
    }
}

impl OptimizedOtlpProcessor {
    /// 创建新的优化处理器
    pub fn new(config: OptimizedProcessorConfig) -> Self {
        Self {
            simd_optimizer: AdvancedSimdOptimizer::new(),
            cache_manager: CacheOptimizationManager::new(),
            // memory_strategy: AdvancedMemoryStrategyManager::new(), // 暂时禁用
            performance_metrics: PerformanceMetrics::default(),
            last_monitoring_time: Instant::now(),
            config,
        }
    }

    /// 处理单个数据项
    pub fn process_single_item(&mut self, item: &OtlpDataItem) -> Result<ProcessedItem> {
        let start_time = Instant::now();

        // 使用内存池分配（暂时禁用）
        // let _processed_data = if self.config.enable_memory_pool {
        //     self.allocate_processed_data()?
        // } else {
        //     Vec::new()
        // };

        // 应用SIMD优化处理数值
        let processed_value = if self.config.enable_simd {
            self.process_value_with_simd(item.value)?
        } else {
            item.value
        };

        // 应用缓存优化处理属性
        let processed_attributes = if self.config.enable_cache_optimization {
            self.process_attributes_with_cache(&item.attributes)?
        } else {
            item.attributes.clone()
        };

        let processed_item = ProcessedItem {
            timestamp: item.timestamp,
            value: processed_value,
            attributes: processed_attributes,
            resource_attributes: item.resource_attributes.clone(),
            processing_time: start_time.elapsed(),
        };

        // 更新性能指标
        self.update_performance_metrics(start_time.elapsed());
        self.performance_metrics.total_processed += 1;

        Ok(processed_item)
    }

    /// 批量处理数据项
    pub fn process_batch(&mut self, items: &[OtlpDataItem]) -> Result<Vec<ProcessedItem>> {
        let start_time = Instant::now();
        let mut results = Vec::with_capacity(items.len());

        // 如果启用SIMD，批量处理数值
        if self.config.enable_simd && items.len() >= 4 {
            let values: Vec<f64> = items.iter().map(|item| item.value).collect();
            let processed_values = self.process_batch_values_with_simd(&values)?;

            for (i, item) in items.iter().enumerate() {
                let processed_attributes = if self.config.enable_cache_optimization {
                    self.process_attributes_with_cache(&item.attributes)?
                } else {
                    item.attributes.clone()
                };

                results.push(ProcessedItem {
                    timestamp: item.timestamp,
                    value: processed_values[i],
                    attributes: processed_attributes,
                    resource_attributes: item.resource_attributes.clone(),
                    processing_time: Duration::ZERO, // 批量处理时间
                });
            }
        } else {
            // 逐个处理
            for item in items {
                results.push(self.process_single_item(item)?);
            }
        }

        // 更新性能指标
        self.update_performance_metrics(start_time.elapsed());
        self.performance_metrics.total_processed += items.len() as u64;

        Ok(results)
    }

    /// 使用SIMD处理单个数值
    fn process_value_with_simd(&mut self, value: f64) -> Result<f64> {
        let data = vec![value];
        unsafe {
            let result = self
                .simd_optimizer
                .process_f64_array_simd(&data, SimdOperation::Square)?;
            self.performance_metrics.simd_processed += 1;
            Ok(result[0])
        }
    }

    /// 使用SIMD批量处理数值
    fn process_batch_values_with_simd(&mut self, values: &[f64]) -> Result<Vec<f64>> {
        unsafe {
            let result = self
                .simd_optimizer
                .process_f64_array_simd(values, SimdOperation::Square)?;
            self.performance_metrics.simd_processed += values.len() as u64;
            Ok(result)
        }
    }

    /// 使用缓存优化处理属性
    fn process_attributes_with_cache(
        &mut self,
        attributes: &HashMap<String, String>,
    ) -> Result<HashMap<String, String>> {
        let mut processed = HashMap::new();

        for (key, value) in attributes {
            // 使用缓存友好的方式处理属性
            let processed_key = self.cache_manager.optimize_string(key)?;
            let processed_value = self.cache_manager.optimize_string(value)?;
            processed.insert(processed_key, processed_value);
        }

        self.performance_metrics.cache_hits += 1;
        Ok(processed)
    }

    /// 分配处理后的数据内存（暂时禁用）
    // fn allocate_processed_data(&mut self) -> Result<Vec<u8>> {
    //     let size = self.config.batch_size * std::mem::size_of::<ProcessedItem>();
    //     let _ptr = self.memory_strategy.smart_allocate(size)?;
    //     self.performance_metrics.memory_allocations += 1;
    //
    //     // 这里简化处理，实际应该使用分配的内存
    //     Ok(Vec::with_capacity(size))
    // }

    /// 更新性能指标
    fn update_performance_metrics(&mut self, processing_time: Duration) {
        self.performance_metrics.average_processing_time =
            (self.performance_metrics.average_processing_time + processing_time) / 2;

        // 定期更新内存压力（暂时禁用）
        if self.last_monitoring_time.elapsed() >= self.config.monitoring_interval {
            // let stats = self.memory_strategy.get_memory_stats();
            // self.performance_metrics.memory_pressure = stats.memory_pressure;
            self.performance_metrics.last_update_time = Instant::now();
            self.last_monitoring_time = Instant::now();
        }
    }

    /// 获取性能指标
    pub fn get_performance_metrics(&self) -> &PerformanceMetrics {
        &self.performance_metrics
    }

    /// 获取内存统计（暂时禁用）
    // pub fn get_memory_stats(&self) -> MemoryStrategyStats {
    //     self.memory_strategy.get_memory_stats()
    // }

    /// 执行性能优化
    pub fn optimize_performance(&mut self) -> Result<()> {
        // 根据内存压力调整策略（暂时禁用）
        // let stats = self.memory_strategy.get_memory_stats();
        // if stats.memory_pressure > self.config.memory_pressure_threshold {
        //     // 执行垃圾回收
        //     self.memory_strategy.perform_garbage_collection();
        // }

        // 优化缓存
        if self.config.enable_cache_optimization {
            self.cache_manager.optimize_cache_layout();
        }

        Ok(())
    }

    /// 重置性能指标
    pub fn reset_metrics(&mut self) {
        self.performance_metrics = PerformanceMetrics::default();
    }
}

/// 处理后的数据项
#[derive(Debug, Clone)]
pub struct ProcessedItem {
    pub timestamp: u64,
    pub value: f64,
    pub attributes: HashMap<String, String>,
    pub resource_attributes: HashMap<String, String>,
    pub processing_time: Duration,
}

/// 性能监控器
pub struct PerformanceMonitor {
    processor: OptimizedOtlpProcessor,
    monitoring_interval: Duration,
    last_report_time: Instant,
}

impl PerformanceMonitor {
    pub fn new(processor: OptimizedOtlpProcessor) -> Self {
        Self {
            monitoring_interval: Duration::from_secs(10),
            last_report_time: Instant::now(),
            processor,
        }
    }

    /// 生成性能报告
    pub fn generate_report(&mut self) -> PerformanceReport {
        let metrics = self.processor.get_performance_metrics();
        // let memory_stats = self.processor.get_memory_stats(); // 暂时禁用

        PerformanceReport {
            timestamp: Instant::now(),
            total_processed: metrics.total_processed,
            simd_processed: metrics.simd_processed,
            cache_hit_ratio: if metrics.cache_hits + metrics.cache_misses > 0 {
                metrics.cache_hits as f64 / (metrics.cache_hits + metrics.cache_misses) as f64
            } else {
                0.0
            },
            average_processing_time: metrics.average_processing_time,
            memory_pressure: metrics.memory_pressure,
            memory_allocations: 0,   // 暂时禁用
            memory_deallocations: 0, // 暂时禁用
            pool_count: 0,           // 暂时禁用
            total_pooled_objects: 0, // 暂时禁用
        }
    }

    /// 检查是否需要报告
    pub fn should_report(&self) -> bool {
        self.last_report_time.elapsed() >= self.monitoring_interval
    }

    /// 更新报告时间
    pub fn update_report_time(&mut self) {
        self.last_report_time = Instant::now();
    }
}

/// 性能报告
#[derive(Debug, Clone)]
pub struct PerformanceReport {
    pub timestamp: Instant,
    pub total_processed: u64,
    pub simd_processed: u64,
    pub cache_hit_ratio: f64,
    pub average_processing_time: Duration,
    pub memory_pressure: f64,
    pub memory_allocations: usize,
    pub memory_deallocations: usize,
    pub pool_count: usize,
    pub total_pooled_objects: usize,
}

impl PerformanceReport {
    /// 格式化报告为字符串
    pub fn format_report(&self) -> String {
        format!(
            "=== OTLP性能报告 ===\n\
            时间: {:?}\n\
            总处理数量: {}\n\
            SIMD处理数量: {}\n\
            缓存命中率: {:.2}%\n\
            平均处理时间: {:?}\n\
            内存压力: {:.2}%\n\
            内存分配: {}\n\
            内存释放: {}\n\
            内存池数量: {}\n\
            池中对象数量: {}\n\
            ===================",
            self.timestamp,
            self.total_processed,
            self.simd_processed,
            self.cache_hit_ratio * 100.0,
            self.average_processing_time,
            self.memory_pressure * 100.0,
            self.memory_allocations,
            self.memory_deallocations,
            self.pool_count,
            self.total_pooled_objects
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_optimized_processor_creation() {
        let config = OptimizedProcessorConfig::default();
        let processor = OptimizedOtlpProcessor::new(config);

        let metrics = processor.get_performance_metrics();
        assert_eq!(metrics.total_processed, 0);
        assert_eq!(metrics.simd_processed, 0);
    }

    #[test]
    fn test_single_item_processing() {
        let config = OptimizedProcessorConfig::default();
        let mut processor = OptimizedOtlpProcessor::new(config);

        let mut attributes = HashMap::new();
        attributes.insert("service".to_string(), "test-service".to_string());

        let item = OtlpDataItem {
            timestamp: 1234567890,
            value: 42.0,
            attributes,
            resource_attributes: HashMap::new(),
        };

        let result = processor.process_single_item(&item).expect("Failed to process single item");
        assert_eq!(result.timestamp, 1234567890);
        assert_eq!(result.value, 42.0 * 42.0); // 平方运算
        assert!(!result.attributes.is_empty());
    }

    #[test]
    fn test_batch_processing() {
        let config = OptimizedProcessorConfig {
            batch_size: 100,
            ..Default::default()
        };
        let mut processor = OptimizedOtlpProcessor::new(config);

        let items: Vec<OtlpDataItem> = (0..10)
            .map(|i| OtlpDataItem {
                timestamp: i as u64,
                value: i as f64,
                attributes: HashMap::new(),
                resource_attributes: HashMap::new(),
            })
            .collect();

        let results = processor.process_batch(&items).expect("Failed to process batch");
        assert_eq!(results.len(), 10);

        for (i, result) in results.iter().enumerate() {
            assert_eq!(result.value, (i as f64) * (i as f64));
        }
    }

    #[test]
    fn test_performance_monitoring() {
        let config = OptimizedProcessorConfig::default();
        let processor = OptimizedOtlpProcessor::new(config);
        let mut monitor = PerformanceMonitor::new(processor);

        let report = monitor.generate_report();
        assert_eq!(report.total_processed, 0);
        assert_eq!(report.simd_processed, 0);
        assert_eq!(report.cache_hit_ratio, 0.0);
    }
}
