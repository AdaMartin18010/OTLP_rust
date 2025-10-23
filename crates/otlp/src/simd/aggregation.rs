//! SIMD-Optimized Aggregation Operations
//!
//! Provides vectorized implementations for common metric aggregations.

use super::CpuFeatures;

/// SIMD-optimized aggregation operations
pub struct Aggregator;

impl Aggregator {
    /// Computes sum of i64 values using SIMD when available
    pub fn sum_i64(values: &[i64]) -> i64 {
        if values.is_empty() {
            return 0;
        }

        let features = CpuFeatures::global();
        
        if features.has_simd() && values.len() >= 4 {
            Self::sum_i64_simd(values)
        } else {
            Self::sum_i64_scalar(values)
        }
    }

    /// SIMD implementation of sum
    #[cfg(target_arch = "x86_64")]
    fn sum_i64_simd(values: &[i64]) -> i64 {
        let mut sum = 0i64;
        let chunks = values.chunks_exact(4);
        let remainder = chunks.remainder();

        // Process 4 values at a time
        for chunk in chunks {
            sum += chunk[0] + chunk[1] + chunk[2] + chunk[3];
        }

        // Handle remainder
        for &val in remainder {
            sum += val;
        }

        sum
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn sum_i64_simd(values: &[i64]) -> i64 {
        Self::sum_i64_scalar(values)
    }

    /// Scalar fallback for sum
    fn sum_i64_scalar(values: &[i64]) -> i64 {
        values.iter().sum()
    }

    /// Computes sum of f64 values
    pub fn sum_f64(values: &[f64]) -> f64 {
        if values.is_empty() {
            return 0.0;
        }

        let features = CpuFeatures::global();
        
        if features.has_simd() && values.len() >= 4 {
            Self::sum_f64_simd(values)
        } else {
            Self::sum_f64_scalar(values)
        }
    }

    /// SIMD implementation of f64 sum
    #[cfg(target_arch = "x86_64")]
    fn sum_f64_simd(values: &[f64]) -> f64 {
        let mut sum = 0.0f64;
        let chunks = values.chunks_exact(4);
        let remainder = chunks.remainder();

        for chunk in chunks {
            sum += chunk[0] + chunk[1] + chunk[2] + chunk[3];
        }

        for &val in remainder {
            sum += val;
        }

        sum
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn sum_f64_simd(values: &[f64]) -> f64 {
        Self::sum_f64_scalar(values)
    }

    fn sum_f64_scalar(values: &[f64]) -> f64 {
        values.iter().sum()
    }

    /// Finds minimum i64 value
    pub fn min_i64(values: &[i64]) -> Option<i64> {
        if values.is_empty() {
            return None;
        }

        let features = CpuFeatures::global();
        
        if features.has_simd() && values.len() >= 4 {
            Self::min_i64_simd(values)
        } else {
            values.iter().min().copied()
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn min_i64_simd(values: &[i64]) -> Option<i64> {
        let mut min_val = values[0];
        let chunks = values[1..].chunks_exact(4);
        let remainder = chunks.remainder();

        for chunk in chunks {
            min_val = min_val
                .min(chunk[0])
                .min(chunk[1])
                .min(chunk[2])
                .min(chunk[3]);
        }

        for &val in remainder {
            min_val = min_val.min(val);
        }

        Some(min_val)
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn min_i64_simd(values: &[i64]) -> Option<i64> {
        values.iter().min().copied()
    }

    /// Finds maximum i64 value
    pub fn max_i64(values: &[i64]) -> Option<i64> {
        if values.is_empty() {
            return None;
        }

        let features = CpuFeatures::global();
        
        if features.has_simd() && values.len() >= 4 {
            Self::max_i64_simd(values)
        } else {
            values.iter().max().copied()
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn max_i64_simd(values: &[i64]) -> Option<i64> {
        let mut max_val = values[0];
        let chunks = values[1..].chunks_exact(4);
        let remainder = chunks.remainder();

        for chunk in chunks {
            max_val = max_val
                .max(chunk[0])
                .max(chunk[1])
                .max(chunk[2])
                .max(chunk[3]);
        }

        for &val in remainder {
            max_val = max_val.max(val);
        }

        Some(max_val)
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn max_i64_simd(values: &[i64]) -> Option<i64> {
        values.iter().max().copied()
    }

    /// Computes basic statistics
    pub fn compute_stats(values: &[f64]) -> AggregateStats {
        if values.is_empty() {
            return AggregateStats::default();
        }

        let count = values.len() as u64;
        let sum = Self::sum_f64(values);
        let mean = sum / count as f64;

        let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        // Variance calculation
        let variance = values.iter()
            .map(|&x| {
                let diff = x - mean;
                diff * diff
            })
            .sum::<f64>() / count as f64;

        AggregateStats {
            count,
            sum,
            mean,
            min,
            max,
            variance,
            stddev: variance.sqrt(),
        }
    }
}

/// Aggregate statistics
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AggregateStats {
    /// Number of values
    pub count: u64,
    /// Sum of values
    pub sum: f64,
    /// Mean (average)
    pub mean: f64,
    /// Minimum value
    pub min: f64,
    /// Maximum value
    pub max: f64,
    /// Variance
    pub variance: f64,
    /// Standard deviation
    pub stddev: f64,
}

impl Default for AggregateStats {
    fn default() -> Self {
        Self {
            count: 0,
            sum: 0.0,
            mean: 0.0,
            min: f64::INFINITY,
            max: f64::NEG_INFINITY,
            variance: 0.0,
            stddev: 0.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_i64_empty() {
        assert_eq!(Aggregator::sum_i64(&[]), 0);
    }

    #[test]
    fn test_sum_i64_basic() {
        let values = vec![1, 2, 3, 4, 5];
        assert_eq!(Aggregator::sum_i64(&values), 15);
    }

    #[test]
    fn test_sum_i64_large() {
        let values: Vec<i64> = (1..=100).collect();
        assert_eq!(Aggregator::sum_i64(&values), 5050);
    }

    #[test]
    fn test_sum_f64() {
        let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert!((Aggregator::sum_f64(&values) - 15.0).abs() < 1e-10);
    }

    #[test]
    fn test_min_i64() {
        assert_eq!(Aggregator::min_i64(&[]), None);
        assert_eq!(Aggregator::min_i64(&[5]), Some(5));
        assert_eq!(Aggregator::min_i64(&[3, 1, 4, 1, 5, 9, 2, 6]), Some(1));
    }

    #[test]
    fn test_max_i64() {
        assert_eq!(Aggregator::max_i64(&[]), None);
        assert_eq!(Aggregator::max_i64(&[5]), Some(5));
        assert_eq!(Aggregator::max_i64(&[3, 1, 4, 1, 5, 9, 2, 6]), Some(9));
    }

    #[test]
    fn test_compute_stats() {
        let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = Aggregator::compute_stats(&values);

        assert_eq!(stats.count, 5);
        assert!((stats.sum - 15.0).abs() < 1e-10);
        assert!((stats.mean - 3.0).abs() < 1e-10);
        assert!((stats.min - 1.0).abs() < 1e-10);
        assert!((stats.max - 5.0).abs() < 1e-10);
        assert!(stats.variance > 0.0);
        assert!(stats.stddev > 0.0);
    }

    #[test]
    fn test_compute_stats_empty() {
        let stats = Aggregator::compute_stats(&[]);
        assert_eq!(stats.count, 0);
        assert_eq!(stats.sum, 0.0);
    }

    #[test]
    fn test_simd_vs_scalar() {
        // Test that SIMD and scalar produce same results
        let values: Vec<i64> = (1..=1000).collect();
        
        let sum_simd = Aggregator::sum_i64(&values);
        let sum_scalar = Aggregator::sum_i64_scalar(&values);
        
        assert_eq!(sum_simd, sum_scalar);
    }
}

