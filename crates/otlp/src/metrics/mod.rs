//! # Metrics Module
//!
//! This module provides implementations for various metric types supported by OTLP,
//! including the ExponentialHistogram for efficient distribution tracking across
//! large value ranges.
//!
//! ## Module Structure
//!
//! - `exponential_histogram` - Exponential histogram implementation following OTLP 1.10
//!
//! ## Example Usage
//!
//! ```rust
//! use otlp::metrics::exponential_histogram::{ExponentialHistogram, calculate_scale_for_range};
//!
//! // Create histogram with optimal scale for expected range
//! let scale = calculate_scale_for_range(1.0, 1000.0, 160);
//! let mut histogram = ExponentialHistogram::new(scale);
//!
//! // Record values
//! histogram.record(42.0);
//! histogram.record(123.0);
//!
//! // Calculate statistics
//! let mean = histogram.mean();
//! let p99 = histogram.quantile(0.99);
//! ```

pub mod exponential_histogram;

// Re-export commonly used types
pub use exponential_histogram::{
    DEFAULT_MAX_BUCKETS, DEFAULT_ZERO_THRESHOLD, ExponentialHistogram,
    ExponentialHistogramDataPointBuckets, MAX_SCALE, MIN_SCALE, base, bucket_lower_bound,
    bucket_upper_bound, calculate_scale_for_range,
};
