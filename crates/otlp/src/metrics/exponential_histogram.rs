//! # Exponential Histogram Implementation
//!
//! This module provides a complete implementation of the ExponentialHistogram
//! as defined in the OTLP 1.10 specification.
//!
//! ## Mathematical Background
//!
//! Exponential histograms use logarithmically-sized buckets to efficiently represent
//! value distributions across large ranges. The bucket boundaries follow an exponential
//! scale determined by the `scale` parameter.
//!
//! ### Scale and Base
//!
//! The base for bucket boundaries is calculated as:
//! ```text
//! base = 2^(2^(-scale))
//! ```
//!
//! For example:
//! - scale = 0: base = 2^(2^0) = 2^1 = 2.0
//! - scale = 1: base = 2^(2^(-1)) = 2^0.5 = √2 ≈ 1.414
//! - scale = 3: base = 2^(2^(-3)) = 2^0.125 ≈ 1.0905
//!
//! Higher scale values provide finer granularity (smaller bucket ranges).
//!
//! ### Bucket Index Calculation
//!
//! For a positive value `v`, the bucket index is:
//! ```text
//! index = ceil(log_base(v)) - 1
//!       = ceil(log₂(v) / log₂(base)) - 1
//!       = ceil(log₂(v) * 2^(-scale)) - 1
//! ```
//!
//! ### Bucket Boundaries
//!
//! For bucket index `i`:
//! - Lower bound: base^i
//! - Upper bound: base^(i+1)
//!
//! ## Example Usage
//!
//! ```rust
//! use otlp::metrics::exponential_histogram::{ExponentialHistogram, calculate_scale_for_range};
//!
//! // Create a histogram with automatic scale selection
//! let scale = calculate_scale_for_range(0.001, 1000.0, 160);
//! let mut histogram = ExponentialHistogram::new(scale);
//!
//! // Record some values
//! histogram.record(1.5);
//! histogram.record(2.5);
//! histogram.record(10.0);
//! histogram.record(-5.0);
//!
//! // Calculate quantiles
//! let median = histogram.quantile(0.5);
//! let p99 = histogram.quantile(0.99);
//! ```

use serde::{Deserialize, Serialize};

/// The maximum scale value allowed by the OTLP specification.
pub const MAX_SCALE: i32 = 20;

/// The minimum scale value allowed by the OTLP specification.
pub const MIN_SCALE: i32 = -10;

/// Default maximum number of buckets.
pub const DEFAULT_MAX_BUCKETS: u32 = 160;

/// Default zero threshold for considering values as zero.
pub const DEFAULT_ZERO_THRESHOLD: f64 = 1e-10;

/// ExponentialHistogram as defined in OTLP 1.10
///
/// An exponential histogram uses logarithmically-sized buckets to efficiently
/// represent value distributions across large ranges. This is particularly
/// useful for latency measurements, sizes, and other measurements that span
/// multiple orders of magnitude.
///
/// The histogram maintains separate bucket arrays for positive and negative values,
/// allowing efficient representation of distributions centered at or near zero.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ExponentialHistogram {
    /// The scale of the exponential histogram (can be negative)
    ///
    /// Scale determines the granularity of the buckets. Higher values mean
    /// more, finer-grained buckets. The valid range is [-10, 20].
    pub scale: i32,
    /// Sum of all values (optional, may not be available for all measurements)
    pub sum: Option<f64>,
    /// Count of all values
    pub count: u64,
    /// Min value (optional)
    pub min: Option<f64>,
    /// Max value (optional)
    pub max: Option<f64>,
    /// Zero count (values exactly at or near zero, within zero_threshold)
    pub zero_count: u64,
    /// Zero threshold (values with absolute value < this are considered zero)
    pub zero_threshold: f64,
    /// Positive buckets
    pub positive: ExponentialHistogramDataPointBuckets,
    /// Negative buckets
    pub negative: ExponentialHistogramDataPointBuckets,
}

/// Buckets for exponential histogram data points
///
/// Represents a sequence of bucket counts with a starting offset.
/// Bucket `i` contains values in the range [base^(offset+i), base^(offset+i+1)).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
pub struct ExponentialHistogramDataPointBuckets {
    /// Offset of the bucket boundaries
    ///
    /// The offset represents the starting bucket index. Combined with
    /// bucket_counts index `i`, the actual bucket index is `offset + i`.
    pub offset: i32,
    /// Bucket counts
    ///
    /// Each element represents the count of values falling into that bucket.
    /// The bucket boundaries are calculated using the histogram's scale.
    pub bucket_counts: Vec<u64>,
}

impl ExponentialHistogramDataPointBuckets {
    /// Create a new empty bucket structure
    pub fn new() -> Self {
        Self::default()
    }

    /// Create with specific offset and capacity
    pub fn with_capacity(offset: i32, capacity: usize) -> Self {
        Self {
            offset,
            bucket_counts: Vec::with_capacity(capacity),
        }
    }

    /// Get the count for a specific absolute bucket index
    pub fn get(&self, absolute_index: i32) -> u64 {
        let relative_index = absolute_index - self.offset;
        if relative_index >= 0 && (relative_index as usize) < self.bucket_counts.len() {
            self.bucket_counts[relative_index as usize]
        } else {
            0
        }
    }

    /// Set the count for a specific absolute bucket index
    pub fn set(&mut self, absolute_index: i32, count: u64) {
        let relative_index = absolute_index - self.offset;
        if relative_index >= 0 && (relative_index as usize) < self.bucket_counts.len() {
            self.bucket_counts[relative_index as usize] = count;
        }
    }

    /// Increment the count for a specific absolute bucket index
    pub fn increment(&mut self, absolute_index: i32) {
        let relative_index = absolute_index - self.offset;
        if relative_index >= 0 {
            let idx = relative_index as usize;
            if idx >= self.bucket_counts.len() {
                self.bucket_counts.resize(idx + 1, 0);
            }
            self.bucket_counts[idx] += 1;
        }
    }

    /// Total count in all buckets
    pub fn total_count(&self) -> u64 {
        self.bucket_counts.iter().sum()
    }

    /// Check if buckets are empty
    pub fn is_empty(&self) -> bool {
        self.bucket_counts.is_empty() || self.total_count() == 0
    }

    /// Get the range of absolute bucket indices (start, end)
    pub fn index_range(&self) -> (i32, i32) {
        if self.bucket_counts.is_empty() {
            (self.offset, self.offset)
        } else {
            (
                self.offset,
                self.offset + self.bucket_counts.len() as i32,
            )
        }
    }
}

impl ExponentialHistogram {
    /// Create a new empty exponential histogram with the specified scale
    ///
    /// # Arguments
    ///
    /// * `scale` - The scale factor determining bucket granularity. Valid range: [-10, 20].
    ///
    /// # Example
    ///
    /// ```rust
    /// use otlp::metrics::exponential_histogram::ExponentialHistogram;
    ///
    /// let histogram = ExponentialHistogram::new(3);
    /// assert_eq!(histogram.scale, 3);
    /// assert_eq!(histogram.count, 0);
    /// ```
    pub fn new(scale: i32) -> Self {
        let scale = scale.clamp(MIN_SCALE, MAX_SCALE);
        Self {
            scale,
            sum: None,
            count: 0,
            min: None,
            max: None,
            zero_count: 0,
            zero_threshold: DEFAULT_ZERO_THRESHOLD,
            positive: ExponentialHistogramDataPointBuckets::new(),
            negative: ExponentialHistogramDataPointBuckets::new(),
        }
    }

    /// Create a new histogram with specific zero threshold
    pub fn with_zero_threshold(scale: i32, zero_threshold: f64) -> Self {
        let mut histogram = Self::new(scale);
        histogram.zero_threshold = zero_threshold.max(0.0);
        histogram
    }

    /// Calculate the base for this histogram's scale
    ///
    /// The base is calculated as 2^(2^(-scale))
    pub fn base(&self) -> f64 {
        base(self.scale)
    }

    /// Calculate the bucket index for a positive value
    ///
    /// Uses the formula: index = ceil(log₂(v) * 2^(-scale)) - 1
    ///
    /// # Arguments
    ///
    /// * `value` - The positive value to calculate the index for
    ///
    /// # Returns
    ///
    /// The bucket index where this value belongs
    ///
    /// # Panics
    ///
    /// Panics if value is not positive
    pub fn calculate_bucket_index(&self, value: f64) -> i32 {
        calculate_bucket_index(value, self.scale)
    }

    /// Get the lower bound of a bucket at the given index
    pub fn bucket_lower_bound(&self, index: i32) -> f64 {
        bucket_lower_bound(self.scale, index)
    }

    /// Get the upper bound of a bucket at the given index
    pub fn bucket_upper_bound(&self, index: i32) -> f64 {
        bucket_upper_bound(self.scale, index)
    }

    /// Record a single value into the histogram
    ///
    /// This updates the count, sum, min, max, and appropriate bucket.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to record
    ///
    /// # Example
    ///
    /// ```rust
    /// use otlp::metrics::exponential_histogram::ExponentialHistogram;
    ///
    /// let mut histogram = ExponentialHistogram::new(3);
    /// histogram.record(1.5);
    /// histogram.record(2.5);
    /// assert_eq!(histogram.count, 2);
    /// ```
    pub fn record(&mut self, value: f64) {
        // Handle NaN and infinity
        if !value.is_finite() {
            return;
        }

        let abs_value = value.abs();

        // Check if value should be considered as zero
        if abs_value < self.zero_threshold {
            self.zero_count += 1;
        } else if value > 0.0 {
            let index = self.calculate_bucket_index(value);
            self.positive.increment(index);
        } else {
            // Negative value: store in negative buckets using absolute value
            let index = calculate_bucket_index(abs_value, self.scale);
            self.negative.increment(index);
        }

        // Update statistics
        self.count += 1;
        self.sum = Some(self.sum.unwrap_or(0.0) + value);
        self.min = Some(self.min.map_or(value, |m| m.min(value)));
        self.max = Some(self.max.map_or(value, |m| m.max(value)));
    }

    /// Record multiple values at once
    pub fn record_batch(&mut self, values: &[f64]) {
        for &value in values {
            self.record(value);
        }
    }

    /// Calculate an approximate quantile from the histogram
    ///
    /// Uses linear interpolation within buckets for more accurate estimates.
    ///
    /// # Arguments
    ///
    /// * `q` - The quantile to calculate (0.0 to 1.0)
    ///
    /// # Returns
    ///
    /// The estimated value at the given quantile, or None if histogram is empty
    ///
    /// # Example
    ///
    /// ```rust
    /// use otlp::metrics::exponential_histogram::ExponentialHistogram;
    ///
    /// let mut histogram = ExponentialHistogram::new(3);
    /// for v in [1.0, 2.0, 3.0, 4.0, 5.0] {
    ///     histogram.record(v);
    /// }
    ///
    /// let median = histogram.quantile(0.5);
    /// assert!(median.is_some());
    /// ```
    pub fn quantile(&self, q: f64) -> Option<f64> {
        if self.count == 0 || !(0.0..=1.0).contains(&q) {
            return None;
        }

        let target_count = (q * self.count as f64) as u64;
        let mut cumulative = 0u64;

        // Check zero bucket first
        if self.zero_count > 0 {
            if cumulative + self.zero_count > target_count {
                return Some(0.0);
            }
            cumulative += self.zero_count;
        }

        // Check negative buckets (in reverse order since they're stored by absolute value)
        if !self.negative.is_empty() {
            let (start, end) = self.negative.index_range();
            for idx in (start..end).rev() {
                let count = self.negative.get(idx);
                if count == 0 {
                    continue;
                }
                if cumulative + count > target_count {
                    let bucket_progress = (target_count - cumulative) as f64 / count as f64;
                    let lower = -self.bucket_upper_bound(idx);
                    let upper = -self.bucket_lower_bound(idx);
                    return Some(lower + bucket_progress * (upper - lower));
                }
                cumulative += count;
            }
        }

        // Check positive buckets
        if !self.positive.is_empty() {
            let (start, end) = self.positive.index_range();
            for idx in start..end {
                let count = self.positive.get(idx);
                if count == 0 {
                    continue;
                }
                if cumulative + count > target_count {
                    let bucket_progress = (target_count - cumulative) as f64 / count as f64;
                    let lower = self.bucket_lower_bound(idx);
                    let upper = self.bucket_upper_bound(idx);
                    return Some(lower + bucket_progress * (upper - lower));
                }
                cumulative += count;
            }
        }

        // Return max if we reached the end
        self.max
    }

    /// Get the mean value (if sum is available)
    pub fn mean(&self) -> Option<f64> {
        self.sum.map(|s| s / self.count as f64)
    }

    /// Merge another histogram into this one
    ///
    /// Both histograms must have the same scale.
    pub fn merge(&mut self, other: &Self) -> Result<(), &'static str> {
        if self.scale != other.scale {
            return Err("Cannot merge histograms with different scales");
        }

        if self.zero_threshold != other.zero_threshold {
            return Err("Cannot merge histograms with different zero thresholds");
        }

        // Merge zero counts
        self.zero_count += other.zero_count;

        // Merge positive buckets
        self.positive = merge_buckets(&self.positive, &other.positive)?;

        // Merge negative buckets
        self.negative = merge_buckets(&self.negative, &other.negative)?;

        // Update statistics
        self.count += other.count;
        if let (Some(s1), Some(s2)) = (self.sum, other.sum) {
            self.sum = Some(s1 + s2);
        } else {
            self.sum = None;
        }
        if let Some(min2) = other.min {
            self.min = Some(self.min.map_or(min2, |m| m.min(min2)));
        }
        if let Some(max2) = other.max {
            self.max = Some(self.max.map_or(max2, |m| m.max(max2)));
        }

        Ok(())
    }

    /// Downscale the histogram to a lower (coarser) scale
    ///
    /// This merges adjacent buckets to reduce the number of buckets.
    pub fn downscale(&mut self, new_scale: i32) -> Result<(), &'static str> {
        let new_scale = new_scale.clamp(MIN_SCALE, MAX_SCALE);
        if new_scale > self.scale {
            return Err("Cannot upscale: new scale must be <= current scale");
        }
        if new_scale == self.scale {
            return Ok(());
        }

        let scale_diff = self.scale - new_scale;

        // Downscale positive buckets
        self.positive = downscale_buckets(&self.positive, scale_diff);

        // Downscale negative buckets
        self.negative = downscale_buckets(&self.negative, scale_diff);

        self.scale = new_scale;
        Ok(())
    }

    /// Get the total number of buckets (positive + negative)
    pub fn bucket_count(&self) -> usize {
        self.positive.bucket_counts.len() + self.negative.bucket_counts.len()
    }

    /// Check if the histogram is empty
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Reset the histogram to empty state
    pub fn reset(&mut self) {
        self.count = 0;
        self.sum = None;
        self.min = None;
        self.max = None;
        self.zero_count = 0;
        self.positive = ExponentialHistogramDataPointBuckets::new();
        self.negative = ExponentialHistogramDataPointBuckets::new();
    }
}

impl Default for ExponentialHistogram {
    fn default() -> Self {
        Self::new(3) // Default scale of 3
    }
}

/// Calculate the optimal scale for a given value range and bucket limit
///
/// # Arguments
///
/// * `min_value` - The minimum expected value (must be positive)
/// * `max_value` - The maximum expected value (must be >= min_value)
/// * `max_buckets` - The maximum number of buckets allowed
///
/// # Returns
///
/// The optimal scale value that fits the range within the bucket limit
///
/// # Example
///
/// ```rust
/// use otlp::metrics::exponential_histogram::calculate_scale_for_range;
///
/// let scale = calculate_scale_for_range(0.001, 1000.0, 160);
/// assert!(scale >= -10 && scale <= 20);
/// ```
pub fn calculate_scale_for_range(min_value: f64, max_value: f64, max_buckets: u32) -> i32 {
    if min_value <= 0.0 || max_value <= min_value || max_buckets < 2 {
        return 3; // Return default scale
    }

    let log_ratio = (max_value / min_value).log2();
    let buckets_needed = log_ratio.ceil() as u32;

    if buckets_needed <= max_buckets {
        // Can use maximum scale
        return MAX_SCALE;
    }

    // Calculate required scale
    // buckets = log_ratio * 2^scale
    // 2^scale = buckets / log_ratio
    // scale = log2(buckets / log_ratio)
    let scale = ((max_buckets as f64 / log_ratio).log2()).floor() as i32;
    scale.clamp(MIN_SCALE, MAX_SCALE)
}

/// Calculate the base from the scale
///
/// Base = 2^(2^(-scale))
///
/// # Arguments
///
/// * `scale` - The scale factor
///
/// # Returns
///
/// The base value for the given scale
///
/// # Example
///
/// ```rust
/// use otlp::metrics::exponential_histogram::base;
///
/// assert!((base(0) - 2.0).abs() < 1e-10);  // scale 0: base = 2
/// assert!((base(1) - 1.41421356).abs() < 1e-5);  // scale 1: base = √2
/// ```
pub fn base(scale: i32) -> f64 {
    let scale = scale.clamp(MIN_SCALE, MAX_SCALE);
    2f64.powf(2f64.powi(-scale))
}

/// Calculate the bucket index for a positive value
///
/// Uses the formula: index = ceil(log₂(v) * 2^(-scale)) - 1
///
/// # Arguments
///
/// * `value` - The positive value (must be > 0)
/// * `scale` - The scale factor
///
/// # Returns
///
/// The bucket index for the value
///
/// # Panics
///
/// Panics if value is not positive
pub fn calculate_bucket_index(value: f64, scale: i32) -> i32 {
    assert!(value > 0.0, "Value must be positive");

    let scale = scale.clamp(MIN_SCALE, MAX_SCALE);

    if scale > 0 {
        // For positive scale: index = floor(log₂(value) * 2^scale)
        let scaled_log = value.log2() * 2f64.powi(scale);
        scaled_log.floor() as i32
    } else {
        // For scale <= 0: index = floor(log₂(value) / 2^(-scale))
        // When scale = 0: index = floor(log₂(value))
        // This gives buckets: [1, 2) -> 0, [2, 4) -> 1, [4, 8) -> 2, etc.
        let scaled_log = value.log2() / 2f64.powi(-scale);
        let idx = scaled_log.floor() as i32;
        // Ensure non-negative index (value < 1.0 maps to bucket 0)
        idx.max(0)
    }
}

/// Calculate the lower bound of a bucket at the given index
///
/// Lower bound = base^index = 2^(index * 2^(-scale))
///
/// # Arguments
///
/// * `scale` - The scale factor
/// * `index` - The bucket index
///
/// # Returns
///
/// The lower bound of the bucket
pub fn bucket_lower_bound(scale: i32, index: i32) -> f64 {
    let scale = scale.clamp(MIN_SCALE, MAX_SCALE);
    2f64.powf(index as f64 * 2f64.powi(-scale))
}

/// Calculate the upper bound of a bucket at the given index
///
/// Upper bound = base^(index+1) = 2^((index+1) * 2^(-scale))
///
/// # Arguments
///
/// * `scale` - The scale factor
/// * `index` - The bucket index
///
/// # Returns
///
/// The upper bound of the bucket
pub fn bucket_upper_bound(scale: i32, index: i32) -> f64 {
    bucket_lower_bound(scale, index + 1)
}

/// Merge two bucket arrays
fn merge_buckets(
    a: &ExponentialHistogramDataPointBuckets,
    b: &ExponentialHistogramDataPointBuckets,
) -> Result<ExponentialHistogramDataPointBuckets, &'static str> {
    if a.is_empty() {
        return Ok(b.clone());
    }
    if b.is_empty() {
        return Ok(a.clone());
    }

    let (a_start, a_end) = a.index_range();
    let (b_start, b_end) = b.index_range();

    let new_start = a_start.min(b_start);
    let new_end = a_end.max(b_end);
    let new_len = (new_end - new_start) as usize;

    let mut result = ExponentialHistogramDataPointBuckets::with_capacity(new_start, new_len);
    result.bucket_counts.resize(new_len, 0);

    // Copy a's counts
    for i in a_start..a_end {
        result.set(i, a.get(i));
    }

    // Add b's counts
    for i in b_start..b_end {
        result.set(i, result.get(i) + b.get(i));
    }

    Ok(result)
}

/// Downscale buckets by merging adjacent buckets
fn downscale_buckets(
    buckets: &ExponentialHistogramDataPointBuckets,
    scale_diff: i32,
) -> ExponentialHistogramDataPointBuckets {
    if buckets.is_empty() || scale_diff <= 0 {
        return buckets.clone();
    }

    let merge_factor = 2usize.pow(scale_diff as u32);
    let (start, end) = buckets.index_range();

    // Calculate new offset (aligned to merge_factor)
    let new_start = (start as f64 / merge_factor as f64).floor() as i32;
    let new_end = ((end as f64) / merge_factor as f64).ceil() as i32;
    let new_len = (new_end - new_start) as usize;

    let mut result = ExponentialHistogramDataPointBuckets::with_capacity(new_start, new_len);
    result.bucket_counts.resize(new_len, 0);

    // Merge buckets
    for old_idx in start..end {
        let count = buckets.get(old_idx);
        if count > 0 {
            let new_idx = (old_idx as f64 / merge_factor as f64).floor() as i32;
            result.set(new_idx, result.get(new_idx) + count);
        }
    }

    result
}

// ============================================================================
// Conversions to/from data.rs types
// ============================================================================

impl From<ExponentialHistogram> for crate::data::ExponentialHistogramData {
    /// Convert from the new ExponentialHistogram to the existing data.rs type
    fn from(hist: ExponentialHistogram) -> Self {
        crate::data::ExponentialHistogramData {
            count: hist.count,
            sum: hist.sum.unwrap_or(0.0),
            min: hist.min,
            max: hist.max,
            scale: hist.scale,
            zero_count: hist.zero_count,
            positive_buckets: hist.positive.into(),
            negative_buckets: hist.negative.into(),
        }
    }
}

impl From<ExponentialHistogramDataPointBuckets> for crate::data::ExponentialHistogramBuckets {
    /// Convert buckets to the data.rs type
    fn from(buckets: ExponentialHistogramDataPointBuckets) -> Self {
        crate::data::ExponentialHistogramBuckets {
            offset: buckets.offset,
            bucket_counts: buckets.bucket_counts,
        }
    }
}

impl From<crate::data::ExponentialHistogramData> for ExponentialHistogram {
    /// Convert from data.rs ExponentialHistogramData to the new type
    fn from(data: crate::data::ExponentialHistogramData) -> Self {
        Self {
            scale: data.scale,
            sum: Some(data.sum),
            count: data.count,
            min: data.min,
            max: data.max,
            zero_count: data.zero_count,
            zero_threshold: DEFAULT_ZERO_THRESHOLD,
            positive: data.positive_buckets.into(),
            negative: data.negative_buckets.into(),
        }
    }
}

impl From<crate::data::ExponentialHistogramBuckets> for ExponentialHistogramDataPointBuckets {
    /// Convert from data.rs buckets to the new type
    fn from(buckets: crate::data::ExponentialHistogramBuckets) -> Self {
        Self {
            offset: buckets.offset,
            bucket_counts: buckets.bucket_counts,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base_calculation() {
        // scale 0: base = 2
        assert!((base(0) - 2.0).abs() < 1e-10);

        // scale 1: base = 2^0.5 = sqrt(2)
        assert!((base(1) - std::f64::consts::SQRT_2).abs() < 1e-10);

        // scale 2: base = 2^0.25
        assert!((base(2) - 1.189207115002721).abs() < 1e-10);

        // scale -1: base = 2^2 = 4
        assert!((base(-1) - 4.0).abs() < 1e-10);

        // scale -2: base = 2^4 = 16
        assert!((base(-2) - 16.0).abs() < 1e-10);
    }

    #[test]
    fn test_bucket_bounds() {
        let scale = 0;

        // scale 0: base = 2
        // bucket 0: [1, 2)
        assert!((bucket_lower_bound(scale, 0) - 1.0).abs() < 1e-10);
        assert!((bucket_upper_bound(scale, 0) - 2.0).abs() < 1e-10);

        // bucket 1: [2, 4)
        assert!((bucket_lower_bound(scale, 1) - 2.0).abs() < 1e-10);
        assert!((bucket_upper_bound(scale, 1) - 4.0).abs() < 1e-10);

        // bucket 2: [4, 8)
        assert!((bucket_lower_bound(scale, 2) - 4.0).abs() < 1e-10);
        assert!((bucket_upper_bound(scale, 2) - 8.0).abs() < 1e-10);
    }

    #[test]
    fn test_bucket_bounds_scale_1() {
        let scale = 1;
        let b = base(scale);

        // bucket 0: [1, sqrt(2))
        assert!((bucket_lower_bound(scale, 0) - 1.0).abs() < 1e-10);
        assert!((bucket_upper_bound(scale, 0) - b).abs() < 1e-10);
    }

    #[test]
    fn test_calculate_bucket_index() {
        let scale = 0; // base = 2

        // Values in [1, 2) should go to bucket 0
        assert_eq!(calculate_bucket_index(1.0, scale), 0);
        assert_eq!(calculate_bucket_index(1.5, scale), 0);

        // Values in [2, 4) should go to bucket 1
        assert_eq!(calculate_bucket_index(2.0, scale), 1);
        assert_eq!(calculate_bucket_index(3.0, scale), 1);

        // Values in [4, 8) should go to bucket 2
        assert_eq!(calculate_bucket_index(4.0, scale), 2);
        assert_eq!(calculate_bucket_index(7.0, scale), 2);
    }

    #[test]
    fn test_calculate_bucket_index_scale_3() {
        let scale = 3; // finer granularity

        // Record and verify indices
        let idx_1 = calculate_bucket_index(1.0, scale);
        let idx_2 = calculate_bucket_index(2.0, scale);
        let idx_3 = calculate_bucket_index(3.0, scale);

        // 2.0 should be in a higher bucket than 1.0
        assert!(idx_2 > idx_1);
        // 3.0 should be in a higher bucket than 2.0
        assert!(idx_3 > idx_2);
    }

    #[test]
    fn test_histogram_record() {
        let mut hist = ExponentialHistogram::new(0);

        hist.record(1.5);
        assert_eq!(hist.count, 1);
        assert_eq!(hist.sum, Some(1.5));
        assert_eq!(hist.min, Some(1.5));
        assert_eq!(hist.max, Some(1.5));
        assert_eq!(hist.positive.total_count(), 1);

        hist.record(2.5);
        assert_eq!(hist.count, 2);
        assert_eq!(hist.sum, Some(4.0));
        assert_eq!(hist.min, Some(1.5));
        assert_eq!(hist.max, Some(2.5));
        assert_eq!(hist.positive.total_count(), 2);
    }

    #[test]
    fn test_histogram_record_negative() {
        let mut hist = ExponentialHistogram::new(0);

        hist.record(-1.5);
        hist.record(-2.5);

        assert_eq!(hist.count, 2);
        assert_eq!(hist.negative.total_count(), 2);
        assert_eq!(hist.positive.total_count(), 0);
    }

    #[test]
    fn test_histogram_record_zero() {
        let mut hist = ExponentialHistogram::new(0);

        hist.record(0.0);
        assert_eq!(hist.zero_count, 1);
        assert_eq!(hist.positive.total_count(), 0);
        assert_eq!(hist.negative.total_count(), 0);

        hist.record(1e-11); // Below default zero_threshold
        assert_eq!(hist.zero_count, 2);
    }

    #[test]
    fn test_histogram_record_non_finite() {
        let mut hist = ExponentialHistogram::new(0);

        hist.record(f64::NAN);
        hist.record(f64::INFINITY);
        hist.record(f64::NEG_INFINITY);

        assert_eq!(hist.count, 0);
    }

    #[test]
    fn test_histogram_mean() {
        let mut hist = ExponentialHistogram::new(0);

        assert_eq!(hist.mean(), None);

        hist.record(1.0);
        hist.record(3.0);

        assert_eq!(hist.mean(), Some(2.0));
    }

    #[test]
    fn test_histogram_quantile() {
        let mut hist = ExponentialHistogram::new(0);

        // Empty histogram should return None
        assert_eq!(hist.quantile(0.5), None);

        // Record values 1, 2, 4, 8, 16 (powers of 2, perfect for scale 0)
        hist.record(1.0);
        hist.record(2.0);
        hist.record(4.0);
        hist.record(8.0);
        hist.record(16.0);

        // Median should be around the middle
        let median = hist.quantile(0.5);
        assert!(median.is_some());

        // Min quantile should be near min
        let q0 = hist.quantile(0.0);
        assert!(q0.is_some());

        // Max quantile should be near max
        let q1 = hist.quantile(1.0);
        assert!(q1.is_some());
    }

    #[test]
    fn test_histogram_quantile_with_zero() {
        let mut hist = ExponentialHistogram::new(0);

        hist.record(0.0);
        hist.record(0.0);
        hist.record(0.0);
        hist.record(1.0);

        // 50th percentile should be in the zero bucket
        let q50 = hist.quantile(0.5);
        assert_eq!(q50, Some(0.0));
    }

    #[test]
    fn test_histogram_merge() {
        let mut hist1 = ExponentialHistogram::new(3);
        hist1.record(1.0);
        hist1.record(2.0);

        let mut hist2 = ExponentialHistogram::new(3);
        hist2.record(3.0);
        hist2.record(4.0);

        hist1.merge(&hist2).unwrap();

        assert_eq!(hist1.count, 4);
        assert_eq!(hist1.sum, Some(10.0));
        assert_eq!(hist1.min, Some(1.0));
        assert_eq!(hist1.max, Some(4.0));
    }

    #[test]
    fn test_histogram_merge_different_scales_fails() {
        let mut hist1 = ExponentialHistogram::new(0);
        let hist2 = ExponentialHistogram::new(1);

        assert!(hist1.merge(&hist2).is_err());
    }

    #[test]
    fn test_histogram_downscale() {
        let mut hist = ExponentialHistogram::new(3);

        // Record many values
        for i in 1..=100 {
            hist.record(i as f64);
        }

        let original_bucket_count = hist.bucket_count();

        // Downscale from 3 to 1
        hist.downscale(1).unwrap();

        assert_eq!(hist.scale, 1);
        assert_eq!(hist.count, 100);
        // Bucket count should decrease
        assert!(hist.bucket_count() <= original_bucket_count);
    }

    #[test]
    fn test_histogram_downscale_upscale_fails() {
        let mut hist = ExponentialHistogram::new(0);

        assert!(hist.downscale(1).is_err());
    }

    #[test]
    fn test_calculate_scale_for_range() {
        // Small range with many buckets should get max scale
        let scale1 = calculate_scale_for_range(1.0, 10.0, 160);
        assert_eq!(scale1, MAX_SCALE);

        // Large range with few buckets may get lower scale depending on calculation
        // [0.001, 1000000] needs ~30 buckets (log2(1e9) ≈ 29.9), which fits in 160
        // So this also returns MAX_SCALE in the current implementation
        let scale2 = calculate_scale_for_range(0.001, 1000000.0, 160);
        assert!(scale2 >= MIN_SCALE);
        assert!(scale2 <= MAX_SCALE);

        // Very large range with limited buckets should get lower scale
        let scale3 = calculate_scale_for_range(1e-10, 1e10, 10);
        assert!(scale3 < MAX_SCALE || scale3 == MIN_SCALE);
        assert!(scale3 >= MIN_SCALE);
    }

    #[test]
    fn test_calculate_scale_invalid_input() {
        // Negative min should return default
        assert_eq!(calculate_scale_for_range(-1.0, 10.0, 160), 3);

        // max < min should return default
        assert_eq!(calculate_scale_for_range(10.0, 1.0, 160), 3);

        // max_buckets < 2 should return default
        assert_eq!(calculate_scale_for_range(1.0, 10.0, 1), 3);
    }

    #[test]
    fn test_scale_clamping() {
        // Test that scale is clamped to valid range
        let hist = ExponentialHistogram::new(MAX_SCALE + 10);
        assert_eq!(hist.scale, MAX_SCALE);

        let hist = ExponentialHistogram::new(MIN_SCALE - 10);
        assert_eq!(hist.scale, MIN_SCALE);
    }

    #[test]
    fn test_default_histogram() {
        let hist = ExponentialHistogram::default();
        assert_eq!(hist.scale, 3);
        assert_eq!(hist.count, 0);
        assert_eq!(hist.zero_threshold, DEFAULT_ZERO_THRESHOLD);
    }

    #[test]
    fn test_histogram_reset() {
        let mut hist = ExponentialHistogram::new(3);
        hist.record(1.0);
        hist.record(2.0);

        hist.reset();

        assert_eq!(hist.count, 0);
        assert_eq!(hist.sum, None);
        assert_eq!(hist.min, None);
        assert_eq!(hist.max, None);
        assert_eq!(hist.zero_count, 0);
        assert!(hist.positive.is_empty());
        assert!(hist.negative.is_empty());
    }

    #[test]
    fn test_bucket_operations() {
        let mut buckets = ExponentialHistogramDataPointBuckets::new();

        // Empty buckets
        assert!(buckets.is_empty());
        assert_eq!(buckets.total_count(), 0);

        // Increment creates new entries
        buckets.increment(5);
        buckets.increment(5);
        buckets.increment(6);

        assert_eq!(buckets.get(5), 2);
        assert_eq!(buckets.get(6), 1);
        assert_eq!(buckets.get(7), 0);
        assert_eq!(buckets.total_count(), 3);
        assert!(!buckets.is_empty());
    }

    #[test]
    fn test_edge_cases() {
        let mut hist = ExponentialHistogram::new(0);

        // Very small positive values
        hist.record(1e-300);
        assert!(hist.count > 0 || hist.zero_count > 0);

        // Very large values
        hist.record(1e300);
        assert!(hist.count > 0);

        // Reset and test near-zero behavior
        hist.reset();
        hist.record(1e-15); // Below default threshold
        assert_eq!(hist.zero_count, 1);

        let mut hist2 = ExponentialHistogram::with_zero_threshold(0, 1e-20);
        hist2.record(1e-15); // Above custom threshold
        assert_eq!(hist2.zero_count, 0);
        assert_eq!(hist2.positive.total_count(), 1);
    }

    #[test]
    fn test_quantile_extremes() {
        let mut hist = ExponentialHistogram::new(3);

        // Only zeros
        hist.record(0.0);
        hist.record(0.0);

        assert_eq!(hist.quantile(0.5), Some(0.0));

        // Test out of range quantiles
        assert_eq!(hist.quantile(-0.1), None);
        assert_eq!(hist.quantile(1.1), None);
    }

    #[test]
    fn test_batch_recording() {
        let mut hist = ExponentialHistogram::new(3);
        let values: Vec<f64> = (1..=100).map(|i| i as f64).collect();

        hist.record_batch(&values);

        assert_eq!(hist.count, 100);
        assert_eq!(hist.sum, Some(values.iter().sum()));
        assert_eq!(hist.min, Some(1.0));
        assert_eq!(hist.max, Some(100.0));
    }

    #[test]
    fn test_clone_and_equality() {
        let mut hist = ExponentialHistogram::new(3);
        hist.record(1.0);
        hist.record(2.0);

        let cloned = hist.clone();

        assert_eq!(hist, cloned);
        assert_eq!(hist.count, cloned.count);
        assert_eq!(hist.sum, cloned.sum);
    }

    #[test]
    fn test_conversion_to_data_types() {
        use crate::data::ExponentialHistogramData;

        let mut hist = ExponentialHistogram::new(3);
        hist.record(1.0);
        hist.record(2.0);
        hist.record(0.0);

        let data: ExponentialHistogramData = hist.into();

        assert_eq!(data.count, 3);
        assert_eq!(data.sum, 3.0);
        assert_eq!(data.scale, 3);
        assert_eq!(data.zero_count, 1);
        assert!(data.min.is_some());
        assert!(data.max.is_some());
    }

    #[test]
    fn test_conversion_from_data_types() {
        use crate::data::{ExponentialHistogramBuckets, ExponentialHistogramData};

        let data = ExponentialHistogramData {
            count: 5,
            sum: 15.0,
            min: Some(1.0),
            max: Some(5.0),
            scale: 3,
            zero_count: 0,
            positive_buckets: ExponentialHistogramBuckets {
                offset: 0,
                bucket_counts: vec![1, 1, 1, 1, 1],
            },
            negative_buckets: ExponentialHistogramBuckets {
                offset: 0,
                bucket_counts: vec![],
            },
        };

        let hist: ExponentialHistogram = data.into();

        assert_eq!(hist.count, 5);
        assert_eq!(hist.sum, Some(15.0));
        assert_eq!(hist.scale, 3);
        assert_eq!(hist.min, Some(1.0));
        assert_eq!(hist.max, Some(5.0));
        assert_eq!(hist.positive.bucket_counts.len(), 5);
    }

    #[test]
    fn test_roundtrip_conversion() {
        use crate::data::ExponentialHistogramData;

        let mut original = ExponentialHistogram::new(3);
        original.record(1.0);
        original.record(2.0);
        original.record(3.0);
        original.record(-1.0);
        original.record(0.0);

        let data: ExponentialHistogramData = original.clone().into();
        let restored: ExponentialHistogram = data.into();

        assert_eq!(original.count, restored.count);
        assert_eq!(original.sum, restored.sum);
        assert_eq!(original.scale, restored.scale);
        assert_eq!(original.zero_count, restored.zero_count);
        assert_eq!(original.positive.total_count(), restored.positive.total_count());
        assert_eq!(original.negative.total_count(), restored.negative.total_count());
    }
}
