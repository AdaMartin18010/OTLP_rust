//! # OTLP错误处理模块
//!
//! 提供统一的错误类型和处理机制，支持Rust 1.90的错误处理特性。

use std::fmt;
use thiserror::Error;

/// OTLP操作结果类型
pub type Result<T> = std::result::Result<T, OtlpError>;

/// OTLP错误类型定义
#[derive(Error, Debug, Clone)]
pub enum OtlpError {
    /// 网络传输错误
    #[error("网络传输错误: {0}")]
    Transport(#[from] TransportError),

    /// 序列化/反序列化错误
    #[error("序列化错误: {0}")]
    Serialization(#[from] SerializationError),

    /// 配置错误
    #[error("配置错误: {0}")]
    Configuration(#[from] ConfigurationError),

    /// 数据处理错误
    #[error("数据处理错误: {0}")]
    Processing(#[from] ProcessingError),

    /// 导出器错误
    #[error("导出器错误: {0}")]
    Export(#[from] ExportError),

    /// 超时错误
    #[error("操作超时: {operation} (超时时间: {timeout:?})")]
    Timeout {
        operation: String,
        timeout: std::time::Duration,
    },

    /// 并发错误
    #[error("并发操作错误: {0}")]
    Concurrency(String),

    /// 资源不足错误
    #[error("资源不足: {resource} (当前: {current}, 需要: {required})")]
    ResourceExhausted {
        resource: String,
        current: usize,
        required: usize,
    },

    /// 协议版本不兼容
    #[error("协议版本不兼容: 当前版本 {current}, 支持版本 {supported}")]
    VersionMismatch { current: String, supported: String },

    /// 内部错误
    #[error("内部错误: {0}")]
    Internal(String),

    /// 业务逻辑错误
    #[error("业务逻辑错误: {0}")]
    BusinessLogic(String),

    /// 数据验证错误
    #[error("数据验证错误: {field} - {reason}")]
    DataValidation { field: String, reason: String },

    /// 权限错误
    #[error("权限错误: {operation} - {reason}")]
    Permission { operation: String, reason: String },

    /// 限流错误
    #[error("限流错误: {service} - 当前请求数: {current}, 限制: {limit}")]
    RateLimit {
        service: String,
        current: u32,
        limit: u32,
    },

    /// 依赖服务错误
    #[error("依赖服务错误: {service} - {reason}")]
    DependencyService { service: String, reason: String },
}

/// 传输层错误
#[derive(Error, Debug)]
pub enum TransportError {
    /// gRPC错误
    #[error("gRPC错误: {0}")]
    Grpc(#[from] tonic::Status),

    /// HTTP错误
    #[error("HTTP错误: {0}")]
    Http(#[from] reqwest::Error),

    /// 连接错误
    #[error("连接错误: {endpoint} - {reason}")]
    Connection { endpoint: String, reason: String },

    /// TLS错误
    #[error("TLS错误: {0}")]
    Tls(String),

    /// DNS解析错误
    #[error("DNS解析错误: {hostname}")]
    DnsResolution { hostname: String },

    /// 网络不可达
    #[error("网络不可达: {endpoint}")]
    NetworkUnreachable { endpoint: String },
}

impl Clone for TransportError {
    fn clone(&self) -> Self {
        match self {
            Self::Grpc(status) => Self::Grpc(tonic::Status::new(
                status.code(),
                status.message().to_string(),
            )),
            Self::Http(err) => {
                // 创建一个新的错误，保留错误信息
                let error_msg = err.to_string();
                // 创建一个简单的 HTTP 错误
                Self::Tls(format!("HTTP错误: {}", error_msg))
            }
            Self::Connection { endpoint, reason } => Self::Connection {
                endpoint: endpoint.clone(),
                reason: reason.clone(),
            },
            Self::Tls(msg) => Self::Tls(msg.clone()),
            Self::DnsResolution { hostname } => Self::DnsResolution {
                hostname: hostname.clone(),
            },
            Self::NetworkUnreachable { endpoint } => Self::NetworkUnreachable {
                endpoint: endpoint.clone(),
            },
        }
    }
}

/// 序列化错误
#[derive(Error, Debug)]
pub enum SerializationError {
    /// Protobuf序列化错误
    #[error("Protobuf序列化错误: {0}")]
    Protobuf(#[from] prost::EncodeError),

    /// JSON序列化错误
    #[error("JSON序列化错误: {0}")]
    Json(#[from] serde_json::Error),

    /// 数据格式错误
    #[error("数据格式错误: {message}")]
    Format { message: String },

    /// 编码错误
    #[error("编码错误: {encoding} - {reason}")]
    Encoding { encoding: String, reason: String },
}

impl Clone for SerializationError {
    fn clone(&self) -> Self {
        match self {
            Self::Protobuf(_err) => {
                // 创建一个新的 Protobuf 错误，保留错误信息
                Self::Format {
                    message: "Protobuf序列化错误".to_string(),
                }
            }
            Self::Json(_err) => {
                // 创建一个新的 JSON 错误，保留错误信息
                Self::Format {
                    message: "JSON序列化错误".to_string(),
                }
            }
            Self::Format { message } => Self::Format {
                message: message.clone(),
            },
            Self::Encoding { encoding, reason } => Self::Encoding {
                encoding: encoding.clone(),
                reason: reason.clone(),
            },
        }
    }
}

/// 配置错误
#[derive(Error, Debug, Clone)]
pub enum ConfigurationError {
    /// 无效的端点URL
    #[error("无效的端点URL: {url}")]
    InvalidEndpoint { url: String },

    /// 无效的超时配置
    #[error("无效的超时配置: {timeout:?}")]
    InvalidTimeout { timeout: std::time::Duration },

    /// 无效的批处理配置
    #[error("无效的批处理配置: {message}")]
    InvalidBatchConfig { message: String },

    /// 缺少必需的配置项
    #[error("缺少必需的配置项: {field}")]
    MissingRequiredField { field: String },

    /// 配置值超出范围
    #[error("配置值超出范围: {field} = {value} (范围: {min} - {max})")]
    ValueOutOfRange {
        field: String,
        value: f64,
        min: f64,
        max: f64,
    },
}

/// 数据处理错误
#[derive(Error, Debug, Clone)]
pub enum ProcessingError {
    /// 数据验证失败
    #[error("数据验证失败: {field} - {reason}")]
    ValidationFailed { field: String, reason: String },

    /// 数据转换错误
    #[error("数据转换错误: {from} -> {to}")]
    ConversionFailed { from: String, to: String },

    /// 批处理错误
    #[error("批处理错误: {message}")]
    BatchProcessing { message: String },

    /// 过滤错误
    #[error("过滤错误: {filter} - {reason}")]
    Filtering { filter: String, reason: String },

    /// 聚合错误
    #[error("聚合错误: {operation} - {reason}")]
    Aggregation { operation: String, reason: String },
}

/// 导出器错误
#[derive(Error, Debug, Clone)]
pub enum ExportError {
    /// 导出失败
    #[error("导出失败: {reason}")]
    ExportFailed { reason: String },

    /// 部分导出失败
    #[error("部分导出失败: 成功 {success}, 失败 {failed}")]
    PartialExport { success: usize, failed: usize },

    /// 重试次数耗尽
    #[error("重试次数耗尽: 尝试了 {attempts} 次")]
    RetryExhausted { attempts: usize },

    /// 导出器未初始化
    #[error("导出器未初始化")]
    NotInitialized,

    /// 导出器已关闭
    #[error("导出器已关闭")]
    Shutdown,
}

impl OtlpError {
    /// 从 anyhow::Error 创建内部错误
    pub fn from_anyhow(err: anyhow::Error) -> Self {
        Self::Internal(err.to_string())
    }
}

impl From<anyhow::Error> for OtlpError {
    fn from(err: anyhow::Error) -> Self {
        Self::from_anyhow(err)
    }
}

impl OtlpError {
    /// 创建超时错误
    pub fn timeout(operation: impl Into<String>, timeout: std::time::Duration) -> Self {
        Self::Timeout {
            operation: operation.into(),
            timeout,
        }
    }

    /// 创建并发错误
    pub fn concurrency(reason: impl Into<String>) -> Self {
        Self::Concurrency(reason.into())
    }

    /// 创建资源不足错误
    pub fn resource_exhausted(
        resource: impl Into<String>,
        current: usize,
        required: usize,
    ) -> Self {
        Self::ResourceExhausted {
            resource: resource.into(),
            current,
            required,
        }
    }

    /// 创建版本不兼容错误
    pub fn version_mismatch(current: impl Into<String>, supported: impl Into<String>) -> Self {
        Self::VersionMismatch {
            current: current.into(),
            supported: supported.into(),
        }
    }

    /// 判断是否为可重试的错误
    pub fn is_retryable(&self) -> bool {
        match self {
            // 传输类：网络瞬断、连接失败、网络不可达 → 可重试
            Self::Transport(TransportError::Connection { .. }) => true,
            Self::Transport(TransportError::NetworkUnreachable { .. }) => true,
            // gRPC: UNAVAILABLE、RESOURCE_EXHAUSTED、DEADLINE_EXCEEDED → 可重试
            Self::Transport(TransportError::Grpc(status)) => {
                use tonic::Code;
                matches!(
                    status.code(),
                    Code::Unavailable | Code::ResourceExhausted | Code::DeadlineExceeded
                )
            }
            // HTTP：5xx/429 常见可重试
            Self::Transport(TransportError::Http(err)) => {
                if let Some(status) = err.status() {
                    let code = status.as_u16();
                    code == 429 || (500..=599).contains(&code)
                } else {
                    // 无状态码（如超时/连接断开）通常可重试
                    true
                }
            }
            // 操作超时 → 可重试
            Self::Timeout { .. } => true,
            // 导出失败（通用） → 可重试
            Self::Export(ExportError::ExportFailed { .. }) => true,
            // 限流错误 → 可重试（需要等待）
            Self::RateLimit { .. } => true,
            // 依赖服务错误 → 可重试
            Self::DependencyService { .. } => true,
            // 业务逻辑错误 → 不可重试
            Self::BusinessLogic(_) => false,
            // 数据验证错误 → 不可重试
            Self::DataValidation { .. } => false,
            // 权限错误 → 不可重试
            Self::Permission { .. } => false,
            // 其余：默认不可重试
            _ => false,
        }
    }

    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            Self::Transport(_) => ErrorSeverity::High,
            Self::Serialization(_) => ErrorSeverity::Medium,
            Self::Configuration(_) => ErrorSeverity::High,
            Self::Processing(_) => ErrorSeverity::Medium,
            Self::Export(_) => ErrorSeverity::Medium,
            Self::Timeout { .. } => ErrorSeverity::Medium,
            Self::Concurrency(_) => ErrorSeverity::High,
            Self::ResourceExhausted { .. } => ErrorSeverity::High,
            Self::VersionMismatch { .. } => ErrorSeverity::High,
            Self::Internal(_) => ErrorSeverity::Critical,
            Self::BusinessLogic(_) => ErrorSeverity::Medium,
            Self::DataValidation { .. } => ErrorSeverity::Low,
            Self::Permission { .. } => ErrorSeverity::High,
            Self::RateLimit { .. } => ErrorSeverity::Medium,
            Self::DependencyService { .. } => ErrorSeverity::High,
        }
    }

    /// 获取错误恢复建议
    pub fn recovery_suggestion(&self) -> Option<&'static str> {
        match self {
            Self::Transport(TransportError::Connection { .. }) => {
                Some("检查网络连接和端点配置，尝试重新连接")
            }
            Self::Transport(TransportError::NetworkUnreachable { .. }) => {
                Some("检查网络配置和防火墙设置")
            }
            Self::Transport(TransportError::Grpc(_)) => Some("检查gRPC服务状态，可能需要重启服务"),
            Self::Transport(TransportError::Http(_)) => Some("检查HTTP服务状态和端点可访问性"),
            Self::Serialization(_) => Some("检查数据格式和序列化配置"),
            Self::Configuration(ConfigurationError::InvalidEndpoint { .. }) => {
                Some("检查端点URL格式和可访问性")
            }
            Self::Configuration(ConfigurationError::MissingRequiredField { .. }) => {
                Some("检查配置文件中是否包含所有必需字段")
            }
            Self::Processing(ProcessingError::ValidationFailed { .. }) => {
                Some("检查输入数据的格式和内容")
            }
            Self::Export(_) => Some("检查导出器配置和网络连接"),
            Self::Timeout { .. } => Some("增加超时时间或检查网络延迟"),
            Self::ResourceExhausted { .. } => Some("释放资源或增加系统资源"),
            Self::VersionMismatch { .. } => Some("更新到兼容的版本或降级到支持的版本"),
            Self::Internal(_) => Some("检查系统日志，可能需要重启服务"),
            Self::BusinessLogic(_) => Some("检查业务逻辑实现，确认业务规则"),
            Self::DataValidation { .. } => Some("检查输入数据格式，确认数据验证规则"),
            Self::Permission { .. } => Some("检查用户权限，确认访问控制配置"),
            Self::RateLimit { .. } => Some("等待限流重置或调整请求频率"),
            Self::DependencyService { .. } => Some("检查依赖服务状态，确认服务可用性"),
            _ => None,
        }
    }

    /// 判断是否为临时性错误
    pub fn is_temporary(&self) -> bool {
        match self {
            Self::Transport(TransportError::Connection { .. }) => true,
            Self::Transport(TransportError::NetworkUnreachable { .. }) => true,
            Self::Transport(TransportError::Grpc(status)) => {
                use tonic::Code;
                matches!(
                    status.code(),
                    Code::Unavailable
                        | Code::ResourceExhausted
                        | Code::DeadlineExceeded
                        | Code::Aborted
                )
            }
            Self::Transport(TransportError::Http(err)) => {
                if let Some(status) = err.status() {
                    let code = status.as_u16();
                    // 5xx 服务器错误和 429 限流通常是临时的
                    code == 429 || (500..=599).contains(&code)
                } else {
                    // 网络错误通常是临时的
                    true
                }
            }
            Self::Timeout { .. } => true,
            Self::Export(_) => true,
            Self::RateLimit { .. } => true,
            Self::DependencyService { .. } => true,
            _ => false,
        }
    }

    /// 获取错误分类
    pub fn category(&self) -> ErrorCategory {
        match self {
            Self::Transport(_) => ErrorCategory::Network,
            Self::Serialization(_) => ErrorCategory::Data,
            Self::Configuration(_) => ErrorCategory::Configuration,
            Self::Processing(_) => ErrorCategory::Processing,
            Self::Export(_) => ErrorCategory::Export,
            Self::Timeout { .. } => ErrorCategory::Performance,
            Self::Concurrency(_) => ErrorCategory::Concurrency,
            Self::ResourceExhausted { .. } => ErrorCategory::Resource,
            Self::VersionMismatch { .. } => ErrorCategory::Compatibility,
            Self::Internal(_) => ErrorCategory::System,
            Self::BusinessLogic(_) => ErrorCategory::Business,
            Self::DataValidation { .. } => ErrorCategory::Data,
            Self::Permission { .. } => ErrorCategory::Security,
            Self::RateLimit { .. } => ErrorCategory::Performance,
            Self::DependencyService { .. } => ErrorCategory::Dependency,
        }
    }

    /// 获取错误上下文信息
    pub fn context(&self) -> ErrorContext {
        ErrorContext {
            error_type: self.error_type(),
            category: self.category(),
            severity: self.severity(),
            is_retryable: self.is_retryable(),
            is_temporary: self.is_temporary(),
            recovery_suggestion: self.recovery_suggestion().map(|s| s.to_string()),
            timestamp: std::time::SystemTime::now(),
        }
    }

    /// 获取错误类型
    fn error_type(&self) -> &'static str {
        match self {
            Self::Transport(_) => "transport",
            Self::Serialization(_) => "serialization",
            Self::Configuration(_) => "configuration",
            Self::Processing(_) => "processing",
            Self::Export(_) => "export",
            Self::Timeout { .. } => "timeout",
            Self::Concurrency(_) => "concurrency",
            Self::ResourceExhausted { .. } => "resource_exhausted",
            Self::VersionMismatch { .. } => "version_mismatch",
            Self::Internal(_) => "internal",
            Self::BusinessLogic(_) => "business_logic",
            Self::DataValidation { .. } => "data_validation",
            Self::Permission { .. } => "permission",
            Self::RateLimit { .. } => "rate_limit",
            Self::DependencyService { .. } => "dependency_service",
        }
    }
}

/// 错误上下文
#[derive(Debug, Clone)]
pub struct ErrorContext {
    /// 错误类型
    pub error_type: &'static str,
    /// 错误分类
    pub category: ErrorCategory,
    /// 严重程度
    pub severity: ErrorSeverity,
    /// 是否可重试
    pub is_retryable: bool,
    /// 是否为临时错误
    pub is_temporary: bool,
    /// 恢复建议
    pub recovery_suggestion: Option<String>,
    /// 时间戳
    pub timestamp: std::time::SystemTime,
}

/// 错误分类
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ErrorCategory {
    /// 网络相关错误
    Network,
    /// 数据处理错误
    Data,
    /// 配置错误
    Configuration,
    /// 处理逻辑错误
    Processing,
    /// 导出错误
    Export,
    /// 性能相关错误
    Performance,
    /// 并发错误
    Concurrency,
    /// 资源错误
    Resource,
    /// 兼容性错误
    Compatibility,
    /// 系统错误
    System,
    /// 业务逻辑错误
    Business,
    /// 安全相关错误
    Security,
    /// 依赖服务错误
    Dependency,
}

/// 错误严重程度
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ErrorSeverity {
    /// 低严重程度 - 不影响核心功能
    Low,
    /// 中等严重程度 - 影响部分功能
    Medium,
    /// 高严重程度 - 影响主要功能
    High,
    /// 严重程度 - 系统不可用
    Critical,
}

impl fmt::Display for ErrorCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCategory::Network => write!(f, "网络"),
            ErrorCategory::Data => write!(f, "数据"),
            ErrorCategory::Configuration => write!(f, "配置"),
            ErrorCategory::Processing => write!(f, "处理"),
            ErrorCategory::Export => write!(f, "导出"),
            ErrorCategory::Performance => write!(f, "性能"),
            ErrorCategory::Concurrency => write!(f, "并发"),
            ErrorCategory::Resource => write!(f, "资源"),
            ErrorCategory::Compatibility => write!(f, "兼容性"),
            ErrorCategory::System => write!(f, "系统"),
            ErrorCategory::Business => write!(f, "业务"),
            ErrorCategory::Security => write!(f, "安全"),
            ErrorCategory::Dependency => write!(f, "依赖"),
        }
    }
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "低"),
            ErrorSeverity::Medium => write!(f, "中等"),
            ErrorSeverity::High => write!(f, "高"),
            ErrorSeverity::Critical => write!(f, "严重"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_error_creation() {
        let timeout_err = OtlpError::timeout("test_operation", Duration::from_secs(5));
        assert!(matches!(timeout_err, OtlpError::Timeout { .. }));

        let concurrency_err = OtlpError::concurrency("test_reason");
        assert!(matches!(concurrency_err, OtlpError::Concurrency(_)));

        let resource_err = OtlpError::resource_exhausted("memory", 100, 200);
        assert!(matches!(resource_err, OtlpError::ResourceExhausted { .. }));
    }

    #[test]
    fn test_error_retryable() {
        let retryable_err = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert!(retryable_err.is_retryable());

        let non_retryable_err = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "test".to_string(),
        });
        assert!(!non_retryable_err.is_retryable());
    }

    #[test]
    fn test_error_severity() {
        let high_severity = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert_eq!(high_severity.severity(), ErrorSeverity::High);

        let critical_severity = OtlpError::from_anyhow(anyhow::anyhow!("test"));
        assert_eq!(critical_severity.severity(), ErrorSeverity::Critical);
    }
}
