//! # 性能基准测试框架
//!
//! 提供系统性能测试和基准测试工具
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步基准测试操作
//! - **元组收集**: 使用 `collect()` 直接收集基准测试数据到元组
//! - **改进的基准测试**: 利用 Rust 1.92 的基准测试优化提升性能

pub mod latency_analyzer;
pub mod load_generator;
pub mod throughput_meter;

// 重新导出常用类型
pub use latency_analyzer::{LatencyAnalyzer, LatencyMetrics};
pub use load_generator::{LoadGenerator, LoadPattern};
pub use throughput_meter::{ThroughputMeter, ThroughputMetrics};
