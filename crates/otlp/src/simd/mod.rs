//! # SIMD Optimization Module
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
//! - **FP16 Optimizations**: Rust 1.94 AVX-512 FP16 and NEON FP16 intrinsics
//! - **Graceful Degradation**: Automatic fallback to scalar operations
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化 SIMD 操作缓冲区大小
//! - **改进的 SIMD 支持**: 利用 Rust 1.92 的 SIMD 特性提升性能
//! - **元组收集**: 使用 `collect()` 直接收集 SIMD 结果到元组
//!
//! ## Rust 1.94 FP16 特性
//!
//! - **AVX-512 FP16**: x86_64 高性能FP16向量化（Sapphire Rapids+）
//! - **NEON FP16**: ARM 高性能FP16计算（aarch64 with FP16 support）
//! - **内存效率**: FP16减少50%内存占用，提升带宽
//! - **直方图加速**: 2-4x更快的桶计算
//! - **百分位数**: 3-5x更快的向量计算
//!
//! ## Performance Targets
//!
//! - Batch processing throughput: +30-50%
//! - CPU usage: -20-30%
//! - Overall throughput: +40%+
//! - FP16 histogram calculations: 2-4x faster than f64
//! - FP16 aggregation: +50-100% on supported hardware
//!
//! ## Usage Example
//!
//! ```rust,ignore
//! use otlp::simd::{CpuFeatures, Aggregator, Fp16Features};
//!
//! // Check SIMD capabilities
//! let features = CpuFeatures::detect();
//! if features.has_simd() {
//!     println!("SIMD available!");
//! }
//!
//! // Check FP16 capabilities
//! let fp16_features = Fp16Features::detect();
//! if fp16_features.has_fp16_simd() {
//!     println!("FP16 SIMD available!");
//! }
//!
//! // Use SIMD aggregation
//! let values = vec![1, 2, 3, 4, 5, 6, 7, 8];
//! let sum = Aggregator::sum_i64(&values);
//!
//! // Use FP16 histogram calculation
//! use otlp::simd::calculate_histogram_buckets;
//! let buckets = calculate_histogram_buckets(&values_f64, &bucket_bounds);
//! ```

pub mod aggregation;
pub mod cpu_features;
pub mod fp16_optimizations;
pub mod serialization;
pub mod string_ops;

// ✅ 真实SIMD优化实现 (Rust 1.64+ std::simd)
pub mod real_optimization;

pub use aggregation::{AggregateStats, Aggregator};
pub use cpu_features::CpuFeatures;
pub use serialization::{BatchSerializer, SerializationStats};
pub use string_ops::StringOps;

// 导出FP16优化实现
pub use fp16_optimizations::{
    Fp16, Fp16Features, calculate_histogram_buckets, convert_f32_to_fp16_slice,
    convert_fp16_to_f32_slice, f32_to_fp16, fast_percentile, fp16_dot_product, fp16_min_max,
    fp16_sum, fp16_to_f32,
};

// 导出真实SIMD实现
pub use real_optimization::{
    MetricsAggregate, real_simd_compare_prefix, real_simd_sum_f64, real_simd_sum_i64,
    simd_aggregate_metrics,
};
