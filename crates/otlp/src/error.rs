//! # OTLP错误处理模块
//!
//! 提供统一的错误类型和处理机制，支持Rust 1.92的错误处理特性。
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的错误处理**: 利用 Rust 1.92 的错误处理优化提升性能
//! - **类型安全的错误**: 使用 Rust 1.92 的类型系统确保错误处理的安全性
//! - **上下文丰富的错误**: 利用 Rust 1.92 的错误上下文特性提供更详细的错误信息

use std::time::SystemTime;

/// OTLP错误类型
#[derive(Debug, thiserror::Error)]
pub enum OtlpError {
    #[error("校验错误: {0}")]
    ValidationError(String),
    #[error("配置错误: {0}")]
    Configuration(#[from] ConfigurationError),

    #[error("传输错误: {0}")]
    Transport(#[from] TransportError),

    #[error("数据处理错误: {0}")]
    Data(#[from] DataError),

    #[error("导出错误: {0}")]
    Export(#[from] ExportError),

    #[error("处理错误: {0}")]
    Processing(#[from] ProcessingError),

    #[error("性能错误: {0}")]
    Performance(#[from] PerformanceError),

    #[error("并发错误: {0}")]
    Concurrency(#[from] ConcurrencyError),

    #[error("资源错误: {0}")]
    Resource(#[from] ResourceError),

    #[error("兼容性错误: {0}")]
    Compatibility(#[from] CompatibilityError),

    #[error("系统错误: {0}")]
    System(#[from] SystemError),

    #[error("IO错误: {0}")]
    Io(#[from] std::io::Error),
}

/// 配置错误
#[derive(Debug, thiserror::Error)]
pub enum ConfigurationError {
    #[error("无效的端点URL: {url}")]
    InvalidEndpoint { url: String },

    #[error("无效的超时配置: {timeout:?}")]
    InvalidTimeout { timeout: std::time::Duration },

    #[error("无效的批处理配置: {message}")]
    InvalidBatchConfig { message: String },

    #[error("值超出范围: 字段={field}, 值={value}, 最小值={min}, 最大值={max}")]
    ValueOutOfRange {
        field: String,
        value: f64,
        min: f64,
        max: f64,
    },
}

/// 传输错误
#[derive(Debug, thiserror::Error)]
pub enum TransportError {
    #[error("连接错误: 端点={endpoint}, 原因={reason}")]
    Connection { endpoint: String, reason: String },

    #[error("超时错误: 操作={operation}, 超时时间={timeout:?}")]
    Timeout {
        operation: String,
        timeout: std::time::Duration,
    },

    #[error("服务器错误: 状态码={status}, 原因={reason}")]
    Server { status: u16, reason: String },

    #[error("序列化错误: 原因={reason}")]
    Serialization { reason: String },

    #[error("反序列化错误: 原因={reason}")]
    Deserialization { reason: String },
}

/// 数据处理错误
#[derive(Debug, thiserror::Error)]
pub enum DataError {
    #[error("数据验证失败: {reason}")]
    Validation { reason: String },

    #[error("数据格式错误: {reason}")]
    Format { reason: String },

    #[error("数据转换错误: {reason}")]
    Conversion { reason: String },

    #[error("数据大小超限: 实际大小={actual}, 最大大小={max}")]
    SizeLimit { actual: usize, max: usize },
}

/// 导出错误
#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("导出失败: 原因={reason}")]
    Failed { reason: String },

    #[error("部分导出失败: 成功={success}, 失败={failed}")]
    PartialFailure { success: usize, failed: usize },

    #[error("导出队列满: 当前大小={current}, 最大大小={max}")]
    QueueFull { current: usize, max: usize },
}

/// 处理错误
#[derive(Debug, thiserror::Error)]
pub enum ProcessingError {
    #[error("批处理错误: {reason}")]
    Batch { reason: String },

    #[error("过滤错误: {reason}")]
    Filter { reason: String },

    #[error("聚合错误: {reason}")]
    Aggregation { reason: String },

    #[error("压缩错误: {reason}")]
    Compression { reason: String },
}

/// 性能错误
#[derive(Debug, thiserror::Error)]
pub enum PerformanceError {
    #[error("内存不足: 请求={requested}, 可用={available}")]
    OutOfMemory { requested: usize, available: usize },

    #[error("CPU使用率过高: 当前={current}%, 阈值={threshold}%")]
    HighCpuUsage { current: f64, threshold: f64 },

    #[error("延迟过高: 当前={current:?}, 阈值={threshold:?}")]
    HighLatency {
        current: std::time::Duration,
        threshold: std::time::Duration,
    },

    #[error("连接池错误: {0}")]
    ConnectionPoolError(String),
}

/// 并发错误
#[derive(Debug, thiserror::Error)]
pub enum ConcurrencyError {
    #[error("死锁检测: {reason}")]
    Deadlock { reason: String },

    #[error("竞态条件: {reason}")]
    RaceCondition { reason: String },

    #[error("锁超时: 操作={operation}, 超时时间={timeout:?}")]
    LockTimeout {
        operation: String,
        timeout: std::time::Duration,
    },
}

/// 资源错误
#[derive(Debug, thiserror::Error)]
pub enum ResourceError {
    #[error("文件不存在: {path}")]
    FileNotFound { path: String },

    #[error("权限不足: {resource}")]
    PermissionDenied { resource: String },

    #[error("磁盘空间不足: 可用={available}, 需要={required}")]
    InsufficientSpace { available: u64, required: u64 },
}

/// 兼容性错误
#[derive(Debug, thiserror::Error)]
pub enum CompatibilityError {
    #[error("版本不兼容: 当前={current}, 需要={required}")]
    VersionMismatch { current: String, required: String },

    #[error("协议不兼容: {reason}")]
    ProtocolMismatch { reason: String },

    #[error("格式不兼容: {reason}")]
    FormatMismatch { reason: String },
}

/// 系统错误
#[derive(Debug, thiserror::Error)]
pub enum SystemError {
    #[error("系统调用失败: {reason}")]
    SystemCall { reason: String },

    #[error("环境变量未设置: {name}")]
    EnvironmentVariable { name: String },

    #[error("信号处理错误: {signal}")]
    Signal { signal: String },
}

/// 错误严重程度
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize, Hash,
)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

/// 错误分类
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash)]
pub enum ErrorCategory {
    Network,
    Data,
    Configuration,
    Processing,
    Export,
    Performance,
    Concurrency,
    Resource,
    Compatibility,
    System,
}

impl From<anyhow::Error> for OtlpError {
    fn from(err: anyhow::Error) -> Self {
        OtlpError::System(SystemError::SystemCall {
            reason: err.to_string(),
        })
    }
}

/// 错误上下文
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub timestamp: SystemTime,
    pub category: ErrorCategory,
    pub severity: ErrorSeverity,
    pub is_retryable: bool,
    pub recovery_suggestion: Option<String>,
    pub additional_info: std::collections::HashMap<String, String>,
}

impl ErrorContext {
    pub fn new(category: ErrorCategory, severity: ErrorSeverity) -> Self {
        Self {
            timestamp: SystemTime::now(),
            category,
            severity,
            is_retryable: false,
            recovery_suggestion: None,
            additional_info: std::collections::HashMap::new(),
        }
    }

    pub fn with_retryable(mut self, retryable: bool) -> Self {
        self.is_retryable = retryable;
        self
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.recovery_suggestion = Some(suggestion);
        self
    }

    pub fn with_info(mut self, key: String, value: String) -> Self {
        self.additional_info.insert(key, value);
        self
    }
}

impl OtlpError {
    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            OtlpError::ValidationError(_) => ErrorSeverity::Medium,
            OtlpError::Configuration(_) => ErrorSeverity::Medium,
            OtlpError::Transport(_) => ErrorSeverity::High,
            OtlpError::Data(_) => ErrorSeverity::Medium,
            OtlpError::Export(_) => ErrorSeverity::High,
            OtlpError::Processing(_) => ErrorSeverity::Medium,
            OtlpError::Performance(_) => ErrorSeverity::High,
            OtlpError::Concurrency(_) => ErrorSeverity::Critical,
            OtlpError::Resource(_) => ErrorSeverity::High,
            OtlpError::Compatibility(_) => ErrorSeverity::Medium,
            OtlpError::System(_) => ErrorSeverity::Critical,
            OtlpError::Io(_) => ErrorSeverity::High,
        }
    }

    /// 获取错误分类
    pub fn category(&self) -> ErrorCategory {
        match self {
            OtlpError::ValidationError(_) => ErrorCategory::Data,
            OtlpError::Configuration(_) => ErrorCategory::Configuration,
            OtlpError::Transport(_) => ErrorCategory::Network,
            OtlpError::Data(_) => ErrorCategory::Data,
            OtlpError::Export(_) => ErrorCategory::Export,
            OtlpError::Processing(_) => ErrorCategory::Processing,
            OtlpError::Performance(_) => ErrorCategory::Performance,
            OtlpError::Concurrency(_) => ErrorCategory::Concurrency,
            OtlpError::Resource(_) => ErrorCategory::Resource,
            OtlpError::Compatibility(_) => ErrorCategory::Compatibility,
            OtlpError::System(_) => ErrorCategory::System,
            OtlpError::Io(_) => ErrorCategory::System,
        }
    }

    /// 检查是否可重试
    pub fn is_retryable(&self) -> bool {
        match self {
            OtlpError::ValidationError(_) => false,
            OtlpError::Transport(TransportError::Connection { .. }) => true,
            OtlpError::Transport(TransportError::Timeout { .. }) => true,
            OtlpError::Transport(TransportError::Server { status, .. }) => {
                // 5xx错误通常可以重试
                *status >= 500
            }
            OtlpError::Export(ExportError::Failed { .. }) => true,
            OtlpError::Resource(ResourceError::InsufficientSpace { .. }) => false,
            OtlpError::Concurrency(_) => false,
            OtlpError::System(_) => false,
            _ => false,
        }
    }

    /// 获取恢复建议
    pub fn recovery_suggestion(&self) -> Option<String> {
        match self {
            OtlpError::ValidationError(_) => Some("修正输入数据格式或内容后重试".to_string()),
            OtlpError::Transport(TransportError::Connection { .. }) => {
                Some("检查网络连接和端点配置".to_string())
            }
            OtlpError::Transport(TransportError::Timeout { .. }) => {
                Some("增加超时时间或检查网络状况".to_string())
            }
            OtlpError::Configuration(ConfigurationError::InvalidEndpoint { .. }) => {
                Some("检查端点URL格式是否正确".to_string())
            }
            OtlpError::Data(DataError::Validation { .. }) => Some("检查数据格式和内容".to_string()),
            OtlpError::Resource(ResourceError::InsufficientSpace { .. }) => {
                Some("清理磁盘空间或增加存储容量".to_string())
            }
            _ => None,
        }
    }

    /// 获取错误上下文
    pub fn context(&self) -> ErrorContext {
        let mut context =
            ErrorContext::new(self.category(), self.severity()).with_retryable(self.is_retryable());

        if let Some(suggestion) = self.recovery_suggestion() {
            context = context.with_suggestion(suggestion);
        }

        context
    }
}

/// 结果类型别名
pub type Result<T> = std::result::Result<T, OtlpError>;

impl OtlpError {
    pub fn from_anyhow(err: anyhow::Error) -> Self {
        OtlpError::from(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_severity() {
        let config_error = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "invalid".to_string(),
        });
        assert_eq!(config_error.severity(), ErrorSeverity::Medium);

        let transport_error = OtlpError::Transport(TransportError::Connection {
            endpoint: "http://example.com".to_string(),
            reason: "timeout".to_string(),
        });
        assert_eq!(transport_error.severity(), ErrorSeverity::High);
    }

    #[test]
    fn test_error_category() {
        let config_error = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "invalid".to_string(),
        });
        assert_eq!(config_error.category(), ErrorCategory::Configuration);

        let transport_error = OtlpError::Transport(TransportError::Connection {
            endpoint: "http://example.com".to_string(),
            reason: "timeout".to_string(),
        });
        assert_eq!(transport_error.category(), ErrorCategory::Network);
    }

    #[test]
    fn test_error_retryable() {
        let connection_error = OtlpError::Transport(TransportError::Connection {
            endpoint: "http://example.com".to_string(),
            reason: "timeout".to_string(),
        });
        assert!(connection_error.is_retryable());

        let config_error = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "invalid".to_string(),
        });
        assert!(!config_error.is_retryable());
    }

    #[test]
    fn test_error_recovery_suggestion() {
        let connection_error = OtlpError::Transport(TransportError::Connection {
            endpoint: "http://example.com".to_string(),
            reason: "timeout".to_string(),
        });
        assert!(connection_error.recovery_suggestion().is_some());

        let config_error = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "invalid".to_string(),
        });
        assert!(config_error.recovery_suggestion().is_some());
    }

    #[test]
    fn test_error_context() {
        let error = OtlpError::Transport(TransportError::Connection {
            endpoint: "http://example.com".to_string(),
            reason: "timeout".to_string(),
        });

        let context = error.context();
        assert_eq!(context.category, ErrorCategory::Network);
        assert_eq!(context.severity, ErrorSeverity::High);
        assert!(context.is_retryable);
        assert!(context.recovery_suggestion.is_some());
    }
}
