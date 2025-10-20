//! # OTLP 测试模块
//!
//! 提供完整的测试框架，包括单元测试、集成测试、性能测试和测试报告生成。

pub mod common;
pub mod test_reporter;

pub use common::*;
pub use test_reporter::*;
