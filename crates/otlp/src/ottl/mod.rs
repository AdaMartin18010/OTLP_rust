//! # OpenTelemetry Transformation Language (OTTL) 支持模块
//!
//! 本模块提供了 OTTL 的完整实现，包括语法解析、表达式求值、数据转换等功能。
//!
//! ## 核心功能
//!
//! - **语法解析**: 完整的 OTTL 语法解析器
//! - **表达式求值**: 支持复杂的表达式计算
//! - **数据转换**: 支持 Traces、Metrics、Logs 的转换
//! - **性能优化**: 基于字节码的高性能执行引擎
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步OTTL操作
//! - **元组收集**: 使用 `collect()` 直接收集OTTL数据到元组
//! - **改进的OTTL**: 利用 Rust 1.92 的OTTL优化提升性能
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::ottl::{OtlpTransform, TransformConfig};
//!
//! let config = TransformConfig::new()
//!     .add_statement("set(attributes[\"service.name\"], \"my-service\")")
//!     .add_statement("where resource.attributes[\"env\"] == \"production\"");
//!
//! let transformer = OtlpTransform::new(config)?;
//! let result = transformer.transform(telemetry_data).await?;
//! ```

pub mod bytecode;
pub mod parser;
pub mod transform;

pub use bytecode::{BytecodeCompiler, BytecodeProgram, Opcode};
pub use parser::{Expression, ParseError, Statement};
pub use transform::{OtlpTransform, TransformConfig, TransformResult};

/// OTTL 转换错误类型
#[derive(Debug, thiserror::Error)]
pub enum OttlError {
    #[error("解析错误: {0}")]
    Parse(#[from] ParseError),

    #[error("求值错误: {0}")]
    Evaluation(String),

    #[error("函数错误: {0}")]
    Function(String),

    #[error("类型错误: 期望 {expected}, 实际 {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("上下文错误: {0}")]
    Context(String),
}

pub type Result<T> = std::result::Result<T, OttlError>;
