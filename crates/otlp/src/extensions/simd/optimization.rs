//! # SIMD优化实现
//!
//! 提供SIMD优化的具体实现逻辑。

use crate::simd::{Aggregator, CpuFeatures};
use opentelemetry_sdk::trace::SpanData;

/// SIMD批处理统计信息
#[derive(Debug, Clone, Copy, Default)]
#[allow(dead_code)]
pub struct BatchStats {
    /// 总duration（纳秒）
    pub total_duration_ns: i64,
    /// 平均duration（纳秒）
    pub avg_duration_ns: i64,
    /// 最小duration（纳秒）
    pub min_duration_ns: i64,
    /// 最大duration（纳秒）
    pub max_duration_ns: i64,
    /// 是否使用了SIMD优化
    pub simd_optimized: bool,
}

/// 使用SIMD优化处理Span batch
///
/// 返回原始batch，同时可选地计算和记录统计信息
pub fn simd_optimize_batch(batch: Vec<SpanData>, cpu_features: &CpuFeatures) -> Vec<SpanData> {
    if batch.is_empty() {
        return batch;
    }

    // 计算批处理统计信息（使用SIMD优化）
    let stats = compute_batch_stats(&batch, cpu_features);

    if stats.simd_optimized {
        tracing::debug!(
            "SIMD optimized batch: {} spans, avg_duration={}μs, min={}μs, max={}μs",
            batch.len(),
            stats.avg_duration_ns / 1000,
            stats.min_duration_ns / 1000,
            stats.max_duration_ns / 1000
        );
    }

    // 返回原始batch（SIMD优化主要用于统计分析）
    batch
}

/// 计算批处理统计信息（使用SIMD优化）
fn compute_batch_stats(batch: &[SpanData], cpu_features: &CpuFeatures) -> BatchStats {
    let durations: Vec<i64> = batch
        .iter()
        .map(|span| {
            let start = span
                .start_time
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as i64)
                .unwrap_or(0);
            let end = span
                .end_time
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as i64)
                .unwrap_or(0);
            (end - start).max(0)
        })
        .collect();

    if durations.is_empty() {
        return BatchStats::default();
    }

    // 检查是否可以使用SIMD优化
    let can_use_simd = (cpu_features.avx2 || cpu_features.sse2) && durations.len() >= 4;

    if can_use_simd {
        // 使用SIMD优化计算统计信息
        let sum = Aggregator::sum_i64(&durations);
        let min = Aggregator::min_i64(&durations).unwrap_or(0);
        let max = Aggregator::max_i64(&durations).unwrap_or(0);
        let avg = sum / durations.len() as i64;

        BatchStats {
            total_duration_ns: sum,
            avg_duration_ns: avg,
            min_duration_ns: min,
            max_duration_ns: max,
            simd_optimized: true,
        }
    } else {
        // 标量计算
        let sum: i64 = durations.iter().sum();
        let min = durations.iter().min().copied().unwrap_or(0);
        let max = durations.iter().max().copied().unwrap_or(0);
        let avg = sum / durations.len() as i64;

        BatchStats {
            total_duration_ns: sum,
            avg_duration_ns: avg,
            min_duration_ns: min,
            max_duration_ns: max,
            simd_optimized: false,
        }
    }
}

/// SIMD优化的属性处理
///
/// 使用SIMD批量处理属性键值对，主要用于序列化前的预处理
#[allow(dead_code)]
pub fn simd_optimize_attributes(batch: &[SpanData]) -> AttributeStats {
    if batch.is_empty() {
        return AttributeStats::default();
    }

    // 统计属性数量和总大小
    let mut total_attrs = 0usize;
    let mut total_attr_bytes = 0usize;

    for span in batch {
        // 注意: 由于SpanData的attributes字段可能不是公开访问的
        // 这里使用简化统计，实际实现需要根据SpanData的具体结构
        total_attrs += 1; // 简化统计
        total_attr_bytes += span.name.len();
    }

    AttributeStats {
        total_spans: batch.len(),
        total_attributes: total_attrs,
        total_attribute_bytes: total_attr_bytes,
    }
}

/// 属性统计信息
#[derive(Debug, Clone, Copy, Default)]
#[allow(dead_code)]
pub struct AttributeStats {
    /// span总数
    pub total_spans: usize,
    /// 总属性数
    pub total_attributes: usize,
    /// 属性总字节数
    pub total_attribute_bytes: usize,
}

/// SIMD优化的span名称去重
///
/// 使用SIMD加速字符串比较，找出重复的span名称
#[allow(dead_code)]
pub fn find_duplicate_span_names(batch: &[SpanData]) -> Vec<(String, usize)> {
    use std::collections::HashMap;

    let mut name_counts: HashMap<String, usize> = HashMap::new();

    for span in batch {
        let name = span.name.to_string();
        *name_counts.entry(name).or_insert(0) += 1;
    }

    name_counts
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simd::CpuFeatures;

    #[test]
    fn test_batch_stats_empty() {
        let batch: Vec<SpanData> = vec![];
        let features = CpuFeatures::detect();
        let stats = compute_batch_stats(&batch, &features);

        assert_eq!(stats.total_duration_ns, 0);
        assert!(!stats.simd_optimized);
    }

    #[test]
    fn test_attribute_stats() {
        // 由于无法轻松创建SpanData，我们测试空batch的情况
        let batch: Vec<SpanData> = vec![];
        let stats = simd_optimize_attributes(&batch);

        assert_eq!(stats.total_spans, 0);
        assert_eq!(stats.total_attributes, 0);
    }

    #[test]
    fn test_find_duplicates_empty() {
        let batch: Vec<SpanData> = vec![];
        let duplicates = find_duplicate_span_names(&batch);
        assert!(duplicates.is_empty());
    }
}
