//! 高性能 OTLP Collector
//! 
//! 设计目标:
//! - 吞吐量: 1M+ spans/s
//! - 延迟 P99: < 10ms
//! - CPU 开销: < 10%
//! - 内存占用: < 100MB (100k spans)

pub mod collector;
pub mod processor;
pub mod exporter;
pub mod buffer;
pub mod span;
pub mod config;

pub use collector::Collector;
pub use config::Config;
pub use span::Span;
pub use exporter::{Exporter, ExportResult};

use thiserror::Error;

/// Collector 错误类型
#[derive(Error, Debug)]
pub enum CollectorError {
    #[error("缓冲区已满")]
    BufferFull,
    
    #[error("导出失败: {0}")]
    ExportFailed(String),
    
    #[error("序列化失败: {0}")]
    SerializationError(String),
    
    #[error("Collector 已关闭")]
    Shutdown,
    
    #[error("配置错误: {0}")]
    ConfigError(String),
}

pub type Result<T> = std::result::Result<T, CollectorError>;

