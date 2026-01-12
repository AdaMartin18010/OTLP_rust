//! # Compression Module
//!
//! This module provides trace data compression capabilities using Tracezip algorithm.
//! The compression significantly reduces data transmission size while maintaining
//! full OTLP compatibility.
//!
//! ## Features
//!
//! - **Span Deduplication**: Removes duplicate span data
//! - **Delta Encoding**: Encodes timestamps and IDs as deltas
//! - **String Table**: Optimizes repeated strings
//! - **Batch Compression**: Efficient batch processing
//! - **Statistics**: Compression metrics and monitoring
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步压缩操作
//! - **元组收集**: 使用 `collect()` 直接收集压缩数据到元组
//! - **改进的压缩**: 利用 Rust 1.92 的压缩优化提升性能
//!
//! ## Usage Example
//!
//! ```rust,ignore
//! use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};
//!
//! let config = CompressorConfig::default();
//! let mut compressor = TraceCompressor::new(config);
//!
//! let compressed = compressor.compress(&spans)?;
//! let stats = compressor.stats();
//! println!("Compression ratio: {:.2}%", stats.compression_ratio * 100.0);
//! ```

pub mod tracezip;

pub use tracezip::{
    CompressionError, CompressionStats, CompressorConfig, DecompressionError, TraceCompressor,
};
