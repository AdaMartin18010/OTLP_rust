//! Compression Module
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
    CompressorConfig, CompressionStats, TraceCompressor,
    DecompressionError, CompressionError,
};

