//! # eBPF 错误类型定义
//!
//! 定义 eBPF 相关的错误类型。
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的错误处理**: 利用 Rust 1.92 的错误处理优化提升性能
//! - **类型安全的错误**: 使用 Rust 1.92 的类型系统确保错误处理的安全性

use thiserror::Error;

/// eBPF 相关错误
#[derive(Error, Debug)]
pub enum EbpfError {
    /// 平台不支持
    #[error("eBPF 仅在 Linux 平台支持")]
    UnsupportedPlatform,

    /// 权限不足
    #[error("权限不足: 需要 CAP_BPF 权限或 root")]
    InsufficientPermissions,

    /// 内核版本不兼容
    #[error("内核版本不兼容: 需要 Linux 内核 >= 5.8")]
    IncompatibleKernel,

    /// 程序加载失败
    #[error("eBPF 程序加载失败: {0}")]
    LoadFailed(String),

    /// 探针附加失败
    #[error("探针附加失败: {0}")]
    AttachFailed(String),

    /// Maps 操作失败
    #[error("Maps 操作失败: {0}")]
    MapOperationFailed(String),

    /// 事件处理失败
    #[error("事件处理失败: {0}")]
    EventProcessingFailed(String),

    /// 配置错误
    #[error("配置错误: {0}")]
    ConfigError(String),
}

impl From<EbpfError> for crate::error::OtlpError {
    fn from(err: EbpfError) -> Self {
        match err {
            EbpfError::UnsupportedPlatform => {
                crate::error::OtlpError::Compatibility(
                    crate::error::CompatibilityError::UnsupportedPlatform {
                        platform: "Linux".to_string(),
                        message: "eBPF 仅在 Linux 平台支持".to_string(),
                    },
                )
            }
            EbpfError::InsufficientPermissions => {
                crate::error::OtlpError::System(
                    crate::error::SystemError::PermissionDenied {
                        message: "需要 CAP_BPF 权限或 root".to_string(),
                    },
                )
            }
            EbpfError::IncompatibleKernel => {
                crate::error::OtlpError::Compatibility(
                    crate::error::CompatibilityError::VersionMismatch {
                        required: "Linux 内核 >= 5.8".to_string(),
                        found: "未知".to_string(),
                    },
                )
            }
            _ => crate::error::OtlpError::Processing(
                crate::error::ProcessingError::InvalidState {
                    message: err.to_string(),
                },
            ),
        }
    }
}
