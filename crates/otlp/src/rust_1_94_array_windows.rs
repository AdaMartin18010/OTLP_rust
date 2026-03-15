//! # Rust 1.94 `array_windows` 特性实现模块
//!
//! 本模块实现 Rust 1.94 稳定化的 `<[T]>::array_windows` 方法，
//! 用于在 OTLP 遥测数据中进行高效的模式检测和序列分析。
//!
//! ## 特性说明
//!
//! `array_windows` 是一个切片迭代方法，类似于 `windows`，但返回固定大小的数组而非切片引用。
//! 这使得编译器可以进行更多的优化，并提供类型安全保证。
//!
//! ## OTLP 应用场景
//!
//! - **Span 模式检测**: 识别追踪数据中的重复或异常模式
//! - **Metrics 趋势分析**: 使用滑动窗口检测指标趋势
//! - **数据验证**: 验证遥测数据的连续性和完整性
//! - **异常检测**: 识别不符合预期的数据序列
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::rust_1_94_array_windows::{
//!     detect_abba_patterns, detect_trends, validate_span_sequence
//! };
//!
//! // 检测 ABBA 模式
//! let data = vec![1u8, 2, 2, 1, 3, 4, 4, 3];
//! let has_pattern = detect_abba_patterns(&data);
//! assert!(has_pattern);
//!
//! // 趋势检测
//! let metrics = vec![1.0, 2.0, 3.0, 4.0, 5.0];
//! let trends = detect_trends(&metrics);
//! ```

use std::fmt::Debug;

/// 趋势类型枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trend {
    /// 上升趋势
    Ascending,
    /// 下降趋势
    Descending,
    /// 稳定趋势
    Stable,
    /// 波动趋势
    Volatile,
}

/// 模式检测结果
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// ABBA 模式（如 [1,2,2,1]）
    Abba,
    /// ABAB 模式（如 [1,2,1,2]）
    Abab,
    /// 递增模式
    Increasing,
    /// 递减模式
    Decreasing,
    /// 峰值模式
    Peak,
    /// 谷值模式
    Valley,
}

/// Span 状态转换
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanTransition {
    /// 正常延续
    Normal,
    /// 状态改变
    StateChange,
    /// 异常跳转
    Anomaly,
}

// ============================================================================
// 模式检测函数
// ============================================================================

/// 检测 ABBA 模式
///
/// ABBA 模式是指形如 `[a, b, b, a]` 的序列，常用于异常检测。
///
/// # 参数
///
/// * `data` - 要检测的字节序列
///
/// # 返回
///
/// 如果检测到 ABBA 模式则返回 `true`，否则返回 `false`
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_array_windows::detect_abba_patterns;
///
/// let data = vec![1u8, 2, 2, 1];
/// assert!(detect_abba_patterns(&data));
///
/// let no_pattern = vec![1u8, 2, 3, 4];
/// assert!(!detect_abba_patterns(&no_pattern));
/// ```
pub fn detect_abba_patterns(data: &[u8]) -> bool {
    if data.len() < 4 {
        return false;
    }
    data.array_windows().any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

/// 检测 ABAB 模式
///
/// ABAB 模式是指形如 `[a, b, a, b]` 的交替序列。
///
/// # 参数
///
/// * `data` - 要检测的字节序列
///
/// # 返回
///
/// 如果检测到 ABAB 模式则返回 `true`，否则返回 `false`
pub fn detect_abab_patterns(data: &[u8]) -> bool {
    if data.len() < 4 {
        return false;
    }
    data.array_windows().any(|[a1, b1, a2, b2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

/// 检测任意重复模式
///
/// 检测长度为 `N` 的重复模式。
///
/// # 类型参数
///
/// * `N` - 模式长度
///
/// # 参数
///
/// * `data` - 要检测的数据序列
///
/// # 返回
///
/// 返回所有检测到重复模式的起始位置
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_array_windows::detect_repeated_patterns_2;
///
/// let data = vec![1u8, 2, 1, 2, 3, 4];
/// let patterns = detect_repeated_patterns_2(&data);
/// assert_eq!(patterns, vec![0]);
/// ```
pub fn detect_repeated_patterns_2<T: PartialEq>(data: &[T]) -> Vec<usize> {
    const N: usize = 2;
    if data.len() < N * 2 {
        return Vec::new();
    }

    data.array_windows::<4>()
        .enumerate()
        .filter_map(|(i, [a, b, c, d])| {
            if a == c && b == d {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}

/// 检测长度为 3 的重复模式
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_array_windows::detect_repeated_patterns_3;
///
/// let data = vec![1u8, 2, 3, 1, 2, 3, 4, 5];
/// let patterns = detect_repeated_patterns_3(&data);
/// assert_eq!(patterns, vec![0]);
/// ```
pub fn detect_repeated_patterns_3<T: PartialEq>(data: &[T]) -> Vec<usize> {
    const N: usize = 3;
    if data.len() < N * 2 {
        return Vec::new();
    }

    data.array_windows::<6>()
        .enumerate()
        .filter_map(|(i, [a, b, c, d, e, f])| {
            if a == d && b == e && c == f {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}

/// 检测长度为 4 的重复模式
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_array_windows::detect_repeated_patterns_4;
///
/// let data = vec![1u8, 2, 3, 4, 1, 2, 3, 4, 5, 6];
/// let patterns = detect_repeated_patterns_4(&data);
/// assert_eq!(patterns, vec![0]);
/// ```
pub fn detect_repeated_patterns_4<T: PartialEq>(data: &[T]) -> Vec<usize> {
    const N: usize = 4;
    if data.len() < N * 2 {
        return Vec::new();
    }

    data.array_windows::<8>()
        .enumerate()
        .filter_map(|(i, [a, b, c, d, e, f, g, h])| {
            if a == e && b == f && c == g && d == h {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}

/// 通用重复模式检测（任意长度）
///
/// 对于非常量长度的模式，使用通用实现。
pub fn detect_repeated_patterns_generic<T: PartialEq>(data: &[T], pattern_len: usize) -> Vec<usize> {
    if data.len() < pattern_len * 2 {
        return Vec::new();
    }

    (0..=data.len().saturating_sub(pattern_len * 2))
        .filter(|&i| data[i..i + pattern_len] == data[i + pattern_len..i + pattern_len * 2])
        .collect()
}

// ============================================================================
// 趋势检测函数
// ============================================================================

/// 检测数值序列中的趋势
///
/// 使用 3 点滑动窗口分析数据趋势。
///
/// # 参数
///
/// * `values` - 数值序列
///
/// # 返回
///
/// 返回每个窗口位置的趋势分析结果
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_array_windows::{detect_trends, Trend};
///
/// let values = vec![1.0, 2.0, 3.0, 4.0, 3.0, 2.0];
/// let trends = detect_trends(&values);
///
/// // 前两个窗口是上升趋势
/// assert_eq!(trends[0], Trend::Ascending);
/// assert_eq!(trends[1], Trend::Ascending);
/// ```
pub fn detect_trends(values: &[f64]) -> Vec<Trend> {
    if values.len() < 3 {
        return Vec::new();
    }

    values
        .array_windows::<3>()
        .map(|[prev, curr, next]| {
            let diff1 = curr - prev;
            let diff2 = next - curr;

            if diff1 > 0.0 && diff2 > 0.0 {
                Trend::Ascending
            } else if diff1 < 0.0 && diff2 < 0.0 {
                Trend::Descending
            } else if diff1.abs() < f64::EPSILON && diff2.abs() < f64::EPSILON {
                Trend::Stable
            } else {
                Trend::Volatile
            }
        })
        .collect()
}

/// 检测峰值和谷值
///
/// 识别序列中的局部极大值和极小值。
///
/// # 参数
///
/// * `values` - 数值序列
///
/// # 返回
///
/// 返回每个窗口位置的模式检测结果
pub fn detect_peaks_and_valleys(values: &[f64]) -> Vec<Option<Pattern>> {
    if values.len() < 3 {
        return Vec::new();
    }

    values
        .array_windows::<3>()
        .map(|[prev, curr, next]| {
            if curr > prev && curr > next {
                Some(Pattern::Peak)
            } else if curr < prev && curr < next {
                Some(Pattern::Valley)
            } else {
                None
            }
        })
        .collect()
}

/// 计算滑动平均
///
/// 使用 `N` 点滑动窗口计算移动平均值。
///
/// # 类型参数
///
/// * `N` - 窗口大小
///
/// # 参数
///
/// * `values` - 数值序列
///
/// # 返回
///
/// 返回滑动平均值序列
pub fn moving_average<const N: usize>(values: &[f64]) -> Vec<f64> {
    if values.len() < N {
        return Vec::new();
    }

    match N {
        2 => values
            .array_windows::<2>()
            .map(|[a, b]| (a + b) / 2.0)
            .collect(),
        3 => values
            .array_windows::<3>()
            .map(|[a, b, c]| (a + b + c) / 3.0)
            .collect(),
        4 => values
            .array_windows::<4>()
            .map(|[a, b, c, d]| (a + b + c + d) / 4.0)
            .collect(),
        5 => values
            .array_windows::<5>()
            .map(|[a, b, c, d, e]| (a + b + c + d + e) / 5.0)
            .collect(),
        _ => values
            .windows(N)
            .map(|w| w.iter().sum::<f64>() / N as f64)
            .collect(),
    }
}

// ============================================================================
// Span 序列分析
// ============================================================================

/// Span ID 类型（8字节）
pub type SpanId = [u8; 8];

/// 简化的 Span 结构
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub id: SpanId,
    pub parent_id: Option<SpanId>,
    pub name: String,
    pub status: SpanStatus,
}

/// Span 状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanStatus {
    Ok,
    Error,
    Unset,
}

/// 验证 Span 序列的连续性
///
/// 检查 Span 序列是否遵循正确的父子关系。
///
/// # 参数
///
/// * `spans` - Span 序列
///
/// # 返回
///
/// 返回每个位置的验证结果
pub fn validate_span_sequence(spans: &[Span]) -> Vec<SpanTransition> {
    if spans.len() < 2 {
        return vec![SpanTransition::Normal; spans.len().saturating_sub(1)];
    }

    spans
        .array_windows::<2>()
        .map(|[prev, curr]| {
            // 检查父子关系
            if let Some(parent_id) = curr.parent_id {
                if parent_id == prev.id {
                    // 当前 span 是前一个 span 的子 span
                    SpanTransition::Normal
                } else {
                    // 检查是否是异常跳转
                    if prev.status == SpanStatus::Error && curr.status == SpanStatus::Error {
                        SpanTransition::Anomaly
                    } else {
                        SpanTransition::StateChange
                    }
                }
            } else {
                // 没有父 span，可能是根 span
                SpanTransition::Normal
            }
        })
        .collect()
}

/// 检测 Span 中的错误模式
///
/// 识别连续的错误 Span 模式。
///
/// # 参数
///
/// * `spans` - Span 序列
///
/// # 返回
///
/// 返回包含错误模式的起始位置
pub fn detect_error_patterns(spans: &[Span]) -> Vec<usize> {
    if spans.len() < 3 {
        return Vec::new();
    }

    spans
        .array_windows::<3>()
        .enumerate()
        .filter_map(|(i, [a, b, c])| {
            // 检测 "错误-错误-正常" 或 "正常-错误-错误" 模式
            match (a.status, b.status, c.status) {
                (SpanStatus::Error, SpanStatus::Error, SpanStatus::Ok)
                | (SpanStatus::Ok, SpanStatus::Error, SpanStatus::Error)
                | (SpanStatus::Error, SpanStatus::Error, SpanStatus::Error) => Some(i),
                _ => None,
            }
        })
        .collect()
}

// ============================================================================
// Metrics 数据处理
// ============================================================================

/// 指标数据点
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetricPoint {
    pub timestamp: u64,
    pub value: f64,
}

/// 检测指标异常
///
/// 使用 3 点窗口检测指标数据中的异常值。
///
/// # 参数
///
/// * `metrics` - 指标数据点序列
/// * `threshold` - 异常阈值（标准差的倍数）
///
/// # 返回
///
/// 返回异常数据点的索引
pub fn detect_anomalies(metrics: &[MetricPoint], threshold: f64) -> Vec<usize> {
    if metrics.len() < 3 {
        return Vec::new();
    }

    let values: Vec<f64> = metrics.iter().map(|m| m.value).collect();
    
    // 计算均值和标准差
    let mean = values.iter().sum::<f64>() / values.len() as f64;
    let variance = values.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / values.len() as f64;
    let std_dev = variance.sqrt();

    metrics
        .array_windows::<3>()
        .enumerate()
        .filter_map(|(i, [a, b, c])| {
            // 检测中间点是否为异常值
            let is_outlier = (b.value - mean).abs() > threshold * std_dev;
            
            // 检测突变模式
            let diff1 = (b.value - a.value).abs();
            let diff2 = (c.value - b.value).abs();
            let is_spike = diff1 > 2.0 * std_dev && diff2 > 2.0 * std_dev;

            if is_outlier || is_spike {
                Some(i + 1) // 返回中间点的索引
            } else {
                None
            }
        })
        .collect()
}

/// 计算变化率
///
/// 使用 2 点窗口计算相邻数据点的变化率。
///
/// # 参数
///
/// * `metrics` - 指标数据点序列
///
/// # 返回
///
/// 返回变化率序列
pub fn calculate_rate_of_change(metrics: &[MetricPoint]) -> Vec<f64> {
    if metrics.len() < 2 {
        return Vec::new();
    }

    metrics
        .array_windows::<2>()
        .map(|[prev, curr]| {
            let time_diff = curr.timestamp.saturating_sub(prev.timestamp) as f64;
            if time_diff > 0.0 {
                (curr.value - prev.value) / time_diff
            } else {
                0.0
            }
        })
        .collect()
}

// ============================================================================
// 数据验证
// ============================================================================

/// 验证时间戳序列的单调性
///
/// 检查时间戳是否按非递减顺序排列。
///
/// # 参数
///
/// * `timestamps` - 时间戳序列
///
/// # 返回
///
/// 如果时间戳单调递增则返回 `true`，否则返回 `false`
pub fn validate_timestamp_order(timestamps: &[u64]) -> bool {
    if timestamps.len() < 2 {
        return true;
    }

    timestamps
        .array_windows::<2>()
        .all(|[prev, curr]| curr >= prev)
}

/// 检测时间戳序列中的跳跃
///
/// 识别时间戳中的异常间隔。
///
/// # 参数
///
/// * `timestamps` - 时间戳序列
/// * `max_gap` - 最大允许间隔
///
/// # 返回
///
/// 返回所有跳跃位置
pub fn detect_timestamp_gaps(timestamps: &[u64], max_gap: u64) -> Vec<usize> {
    if timestamps.len() < 2 {
        return Vec::new();
    }

    timestamps
        .array_windows::<2>()
        .enumerate()
        .filter_map(|(i, [prev, curr])| {
            let gap = curr.saturating_sub(*prev);
            if gap > max_gap {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}

/// 验证数据连续性
///
/// 检查数据序列是否连续（相邻值的差为1）。
///
/// # 参数
///
/// * `data` - 数据序列
///
/// # 返回
///
/// 如果数据连续则返回 `true`，否则返回 `false`
pub fn validate_continuity(data: &[u64]) -> bool {
    if data.len() < 2 {
        return true;
    }

    data.array_windows::<2>()
        .all(|[prev, curr]| curr.saturating_sub(*prev) == 1)
}

// ============================================================================
// 高级模式检测
// ============================================================================

/// 运行长度编码辅助结构
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunLength<T> {
    pub value: T,
    pub length: usize,
}

/// 执行运行长度编码
///
/// 对数据序列进行 RLE 编码。
///
/// # 参数
///
/// * `data` - 数据序列
///
/// # 返回
///
/// 返回 RLE 编码结果
pub fn run_length_encode<T: PartialEq + Clone>(data: &[T]) -> Vec<RunLength<T>> {
    if data.is_empty() {
        return Vec::new();
    }

    let mut result = Vec::new();
    let mut current = RunLength {
        value: data[0].clone(),
        length: 1,
    };

    for [prev, curr] in data.array_windows::<2>() {
        if prev == curr {
            current.length += 1;
        } else {
            result.push(current);
            current = RunLength {
                value: curr.clone(),
                length: 1,
            };
        }
    }
    result.push(current);

    result
}

/// 检测序列相似度
///
/// 使用滑动窗口比较两个序列的相似性。
///
/// # 参数
///
/// * `seq1` - 第一个序列
/// * `seq2` - 第二个序列
///
/// # 返回
///
/// 返回相似度得分（0.0 - 1.0）
pub fn sequence_similarity<T: PartialEq>(seq1: &[T], seq2: &[T]) -> f64 {
    if seq1.is_empty() && seq2.is_empty() {
        return 1.0;
    }
    if seq1.is_empty() || seq2.is_empty() {
        return 0.0;
    }

    let min_len = seq1.len().min(seq2.len());
    let matches: usize = seq1[..min_len]
        .iter()
        .zip(seq2[..min_len].iter())
        .map(|(a, b)| if a == b { 1 } else { 0 })
        .sum();

    matches as f64 / seq1.len().max(seq2.len()) as f64
}

/// 寻找最长连续递增子序列
///
/// 返回最长递增子序列的起始位置和长度。
///
/// # 参数
///
/// * `data` - 数据序列
///
/// # 返回
///
/// 返回 (起始位置, 长度) 元组
pub fn longest_increasing_subsequence(data: &[f64]) -> (usize, usize) {
    if data.len() < 2 {
        return (0, data.len());
    }

    let mut max_start = 0;
    let mut max_len = 1;
    let mut current_start = 0;
    let mut current_len = 1;

    for (i, [prev, curr]) in data.array_windows::<2>().enumerate() {
        if curr > prev {
            current_len += 1;
            if current_len > max_len {
                max_len = current_len;
                max_start = current_start;
            }
        } else {
            current_start = i + 1;
            current_len = 1;
        }
    }

    (max_start, max_len)
}

// ============================================================================
// 测试模块
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // 模式检测测试
    #[test]
    fn test_detect_abba_patterns() {
        let data = vec![1u8, 2, 2, 1];
        assert!(detect_abba_patterns(&data));

        // 包含 ABBA 模式的更大数据集 [1,2,2,1]
        let data2 = vec![1u8, 2, 2, 1, 3, 4];
        assert!(detect_abba_patterns(&data2));

        let no_pattern = vec![1u8, 2, 3, 4];
        assert!(!detect_abba_patterns(&no_pattern));

        let empty: Vec<u8> = vec![];
        assert!(!detect_abba_patterns(&empty));
    }

    #[test]
    fn test_detect_abab_patterns() {
        let data = vec![1u8, 2, 1, 2];
        assert!(detect_abab_patterns(&data));

        let no_pattern = vec![1u8, 2, 3, 4];
        assert!(!detect_abab_patterns(&no_pattern));
    }

    #[test]
    fn test_detect_repeated_patterns() {
        let data = vec![1u8, 2, 1, 2, 3, 4];
        let patterns = detect_repeated_patterns_2(&data);
        assert_eq!(patterns, vec![0]);

        let data2 = vec![1u8, 2, 3, 1, 2, 3, 4, 5];
        let patterns2 = detect_repeated_patterns_3(&data2);
        assert_eq!(patterns2, vec![0]);
        
        let data3 = vec![1u8, 2, 3, 4, 1, 2, 3, 4, 5, 6];
        let patterns3 = detect_repeated_patterns_4(&data3);
        assert_eq!(patterns3, vec![0]);
        
        // 通用模式检测
        let patterns_generic = detect_repeated_patterns_generic(&data, 2);
        assert_eq!(patterns_generic, vec![0]);
    }

    // 趋势检测测试
    #[test]
    fn test_detect_trends() {
        let ascending = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let trends = detect_trends(&ascending);
        assert_eq!(trends.len(), 3);
        assert!(trends.iter().all(|t| *t == Trend::Ascending));

        let descending = vec![5.0, 4.0, 3.0, 2.0, 1.0];
        let trends_desc = detect_trends(&descending);
        assert!(trends_desc.iter().all(|t| *t == Trend::Descending));

        let stable = vec![1.0, 1.0, 1.0, 1.0];
        let trends_stable = detect_trends(&stable);
        assert!(trends_stable.iter().all(|t| *t == Trend::Stable));

        let volatile = vec![1.0, 3.0, 2.0, 4.0];
        let trends_volatile = detect_trends(&volatile);
        assert!(trends_volatile.iter().all(|t| *t == Trend::Volatile));
    }

    #[test]
    fn test_detect_peaks_and_valleys() {
        let data = vec![1.0, 3.0, 1.0, 2.0, 4.0, 2.0];
        let result = detect_peaks_and_valleys(&data);
        
        // 索引 0: [1,3,1] -> Peak
        assert_eq!(result[0], Some(Pattern::Peak));
        // 索引 1: [3,1,2] -> Valley
        assert_eq!(result[1], Some(Pattern::Valley));
        // 索引 2: [1,2,4] -> None (递增)
        assert_eq!(result[2], None);
        // 索引 3: [2,4,2] -> Peak
        assert_eq!(result[3], Some(Pattern::Peak));
    }

    #[test]
    fn test_moving_average() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        
        let ma2 = moving_average::<2>(&data);
        assert_eq!(ma2, vec![1.5, 2.5, 3.5, 4.5]);

        let ma3 = moving_average::<3>(&data);
        assert_eq!(ma3, vec![2.0, 3.0, 4.0]);

        let ma4 = moving_average::<4>(&data);
        assert_eq!(ma4, vec![2.5, 3.5]);
    }

    // Span 序列分析测试
    #[test]
    fn test_validate_span_sequence() {
        let spans = vec![
            Span {
                id: [1, 0, 0, 0, 0, 0, 0, 0],
                parent_id: None,
                name: "root".to_string(),
                status: SpanStatus::Ok,
            },
            Span {
                id: [2, 0, 0, 0, 0, 0, 0, 0],
                parent_id: Some([1, 0, 0, 0, 0, 0, 0, 0]),
                name: "child".to_string(),
                status: SpanStatus::Ok,
            },
        ];

        let transitions = validate_span_sequence(&spans);
        assert_eq!(transitions.len(), 1);
        assert_eq!(transitions[0], SpanTransition::Normal);
    }

    #[test]
    fn test_detect_error_patterns() {
        let spans = vec![
            Span {
                id: [1, 0, 0, 0, 0, 0, 0, 0],
                parent_id: None,
                name: "span1".to_string(),
                status: SpanStatus::Ok,
            },
            Span {
                id: [2, 0, 0, 0, 0, 0, 0, 0],
                parent_id: None,
                name: "span2".to_string(),
                status: SpanStatus::Error,
            },
            Span {
                id: [3, 0, 0, 0, 0, 0, 0, 0],
                parent_id: None,
                name: "span3".to_string(),
                status: SpanStatus::Error,
            },
        ];

        let errors = detect_error_patterns(&spans);
        assert_eq!(errors, vec![0]); // 在索引 0 发现 "OK-Error-Error" 模式
    }

    // Metrics 数据处理测试
    #[test]
    fn test_detect_anomalies() {
        let metrics = vec![
            MetricPoint { timestamp: 1, value: 1.0 },
            MetricPoint { timestamp: 2, value: 1.1 },
            MetricPoint { timestamp: 3, value: 10.0 }, // 异常值
            MetricPoint { timestamp: 4, value: 1.2 },
            MetricPoint { timestamp: 5, value: 1.1 },
        ];

        let anomalies = detect_anomalies(&metrics, 2.0);
        assert!(anomalies.contains(&2)); // 索引 2 是异常值
    }

    #[test]
    fn test_calculate_rate_of_change() {
        let metrics = vec![
            MetricPoint { timestamp: 1000, value: 10.0 },
            MetricPoint { timestamp: 2000, value: 20.0 },
            MetricPoint { timestamp: 3000, value: 25.0 },
        ];

        let rates = calculate_rate_of_change(&metrics);
        assert_eq!(rates.len(), 2);
        assert_eq!(rates[0], 0.01); // (20-10)/1000
        assert_eq!(rates[1], 0.005); // (25-20)/1000
    }

    // 数据验证测试
    #[test]
    fn test_validate_timestamp_order() {
        let timestamps = vec![1u64, 2, 3, 4, 5];
        assert!(validate_timestamp_order(&timestamps));

        let unordered = vec![1u64, 3, 2, 4, 5];
        assert!(!validate_timestamp_order(&unordered));

        let with_duplicates = vec![1u64, 2, 2, 3, 4];
        assert!(validate_timestamp_order(&with_duplicates));
    }

    #[test]
    fn test_detect_timestamp_gaps() {
        let timestamps = vec![1000u64, 2000, 5000, 6000];
        let gaps = detect_timestamp_gaps(&timestamps, 1500);
        assert_eq!(gaps, vec![1]); // 在索引 1 发现跳跃 (5000-2000=3000 > 1500)
    }

    #[test]
    fn test_validate_continuity() {
        let continuous = vec![1u64, 2, 3, 4, 5];
        assert!(validate_continuity(&continuous));

        let discontinuous = vec![1u64, 3, 4, 5];
        assert!(!validate_continuity(&discontinuous));
    }

    // 高级模式检测测试
    #[test]
    fn test_run_length_encode() {
        let data = vec![1u8, 1, 1, 2, 2, 3, 3, 3, 3];
        let encoded = run_length_encode(&data);
        
        assert_eq!(encoded.len(), 3);
        assert_eq!(encoded[0], RunLength { value: 1, length: 3 });
        assert_eq!(encoded[1], RunLength { value: 2, length: 2 });
        assert_eq!(encoded[2], RunLength { value: 3, length: 4 });
    }

    #[test]
    fn test_sequence_similarity() {
        let seq1 = vec![1, 2, 3, 4, 5];
        let seq2 = vec![1, 2, 3, 4, 5];
        assert_eq!(sequence_similarity(&seq1, &seq2), 1.0);

        let seq3 = vec![1, 2, 3, 6, 7];
        assert_eq!(sequence_similarity(&seq1, &seq3), 0.6);

        let empty: Vec<i32> = vec![];
        assert_eq!(sequence_similarity(&empty, &empty), 1.0);
    }

    #[test]
    fn test_longest_increasing_subsequence() {
        let data = vec![1.0, 2.0, 3.0, 1.0, 2.0, 3.0, 4.0, 5.0];
        let (start, len) = longest_increasing_subsequence(&data);
        
        assert_eq!(start, 3);
        assert_eq!(len, 5); // [1.0, 2.0, 3.0, 4.0, 5.0]
    }
}
