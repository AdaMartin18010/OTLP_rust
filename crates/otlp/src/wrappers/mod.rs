//! # OTLP包装器模块
//!
//! 本模块提供官方 `opentelemetry-rust` 库的包装器，用于便捷地使用扩展功能。
//!
//! ## 设计原则
//!
//! 1. **便捷API**: 提供简单易用的API，隐藏复杂性
//! 2. **链式调用**: 支持Builder模式的链式调用
//! 3. **类型安全**: 利用Rust类型系统确保正确使用
//!
//! ## 使用建议
//!
//! - **EnhancedPipeline**: 适用于已有TracingPipeline的情况，但扩展支持有限
//! - **EnhancedPipelineV2**: 推荐使用，提供完整的扩展支持
//! - **EnhancedExporter**: 适用于需要手动构建Exporter的情况

pub mod enhanced_pipeline;
pub mod enhanced_pipeline_v2;
pub mod enhanced_tracer;
pub mod enhanced_exporter;

pub use enhanced_pipeline::EnhancedPipeline;
pub use enhanced_pipeline_v2::EnhancedPipelineV2;
pub use enhanced_tracer::EnhancedTracer;
pub use enhanced_exporter::EnhancedExporter;
