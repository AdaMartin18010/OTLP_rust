//! # 性能优化扩展
//!
//! 提供性能优化扩展，包括批量处理、连接池等优化功能。

// 性能优化扩展将在后续实现
// 当前先提供模块结构

pub mod batch;
pub mod connection_pool;

pub use batch::BatchOptimizedExporter;
pub use connection_pool::ConnectionPoolExporter;
