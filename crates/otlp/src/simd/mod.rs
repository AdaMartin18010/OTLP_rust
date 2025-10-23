//! SIMD Optimization Module
//!
//! This module provides SIMD-optimized implementations for performance-critical
//! operations in OpenTelemetry data processing.
//!
//! ## Features
//!
//! - **CPU Feature Detection**: Automatic detection of SIMD capabilities
//! - **Batch Serialization**: Vectorized span and metric serialization  
//! - **Aggregation**: SIMD-optimized metric aggregation
//! - **String Operations**: Vectorized string comparisons and operations
//! - **Graceful Degradation**: Automatic fallback to scalar operations
//!
//! ## Performance Targets
//!
//! - Batch processing throughput: +30-50%
//! - CPU usage: -20-30%
//! - Overall throughput: +40%+
//!
//! ## Usage Example
//!
//! ```rust,ignore
//! use otlp::simd::{CpuFeatures, Aggregator};
//!
//! // Check SIMD capabilities
//! let features = CpuFeatures::detect();
//! if features.has_simd() {
//!     println!("SIMD available!");
//! }
//!
//! // Use SIMD aggregation
//! let values = vec![1, 2, 3, 4, 5, 6, 7, 8];
//! let sum = Aggregator::sum_i64(&values);
//! ```

pub mod cpu_features;
pub mod serialization;
pub mod aggregation;
pub mod string_ops;

pub use cpu_features::CpuFeatures;
pub use serialization::{BatchSerializer, SerializationStats};
pub use aggregation::{Aggregator, AggregateStats};
pub use string_ops::StringOps;

