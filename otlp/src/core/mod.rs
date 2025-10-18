//! 核心模块 - 基于 opentelemetry-otlp 0.31.0
//! 
//! 本模块提供基于官方 `opentelemetry-otlp` 的增强实现，
//! 确保 OTLP 1.0.0 标准兼容性，同时添加性能和可靠性增强。

pub mod enhanced_client;
pub mod performance_layer;
pub mod reliability_layer;

// 重新导出核心类型
pub use enhanced_client::{
    EnhancedOtlpClient, 
    ClientBuilder, 
    ClientConfig, 
    ClientStats
};

pub use performance_layer::PerformanceOptimizer;
pub use reliability_layer::ReliabilityManager;

