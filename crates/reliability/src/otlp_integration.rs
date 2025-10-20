//! OTLP 语义整合层
//!
//! 目标：在不破坏现有对外 API 的前提下，将 reliability 的错误/监控语义
//! 与 `otlp` crate 的一等语义对齐；提供类型别名与轻量转换，便于逐步迁移。

// 对齐错误类型
pub use otlp::error::ErrorContext as OtlpErrorContext;
pub use otlp::error::ErrorSeverity as OtlpErrorSeverity;
pub use otlp::error::OtlpError as UnifiedOtlpError;

// 指标/监控（按需补充重导出）
pub use otlp::monitoring::MonitoringConfig as OtlpMonitoringConfig;

// 兼容桥接：提供从本地 UnifiedError 轻量转到 OtlpError 的 helper（最小实现）
#[allow(dead_code)]
pub mod convert {
    use super::*;
    use crate::error_handling::{
        ErrorContext as LocalContext, ErrorSeverity as LocalSeverity, UnifiedError,
    };

    // 映射严重度
    fn map_severity(sev: LocalSeverity) -> OtlpErrorSeverity {
        match sev {
            LocalSeverity::Low => OtlpErrorSeverity::Low,
            LocalSeverity::Medium => OtlpErrorSeverity::Medium,
            LocalSeverity::High => OtlpErrorSeverity::High,
            LocalSeverity::Critical => OtlpErrorSeverity::Critical,
        }
    }

    // 简化上下文映射（按需扩展字段）
    fn map_context(ctx: &LocalContext) -> OtlpErrorContext {
        use otlp::error::ErrorCategory;
        // 采用 System 作为默认类别；可根据本地 category 进一步细化
        let base = OtlpErrorContext::new(ErrorCategory::System, map_severity(ctx.severity));
        base
    }

    /// 将本地 UnifiedError 转换为 OtlpError 的最小实现（按分类启发式映射）
    pub fn to_otlp_error(err: &UnifiedError) -> otlp::error::OtlpError {
        use otlp::error::{
            CompatibilityError, DataError, ExportError, OtlpError, PerformanceError,
            ProcessingError, ResourceError, SystemError, TransportError,
        };
        let msg = err.message().to_string();
        let cat = err.category();

        match cat {
            "network" | "transport" => OtlpError::Transport(TransportError::Connection {
                endpoint: "unknown".into(),
                reason: msg,
            }),
            "timeout" => OtlpError::Transport(TransportError::Timeout {
                operation: "unknown".into(),
                timeout: std::time::Duration::from_secs(5),
            }),
            "serialization" | "deserialization" => {
                OtlpError::Transport(TransportError::Serialization { reason: msg })
            }
            "data" | "validation" => OtlpError::Data(DataError::Validation { reason: msg }),
            "export" => OtlpError::Export(ExportError::Failed { reason: msg }),
            "processing" => OtlpError::Processing(ProcessingError::Batch { reason: msg }),
            "resource" => OtlpError::Resource(ResourceError::PermissionDenied { resource: msg }),
            "compatibility" => {
                OtlpError::Compatibility(CompatibilityError::ProtocolMismatch { reason: msg })
            }
            "performance" => OtlpError::Performance(PerformanceError::HighLatency {
                current: std::time::Duration::from_millis(100),
                threshold: std::time::Duration::from_millis(50),
            }),
            _ => OtlpError::System(SystemError::SystemCall { reason: msg }),
        }
    }

    impl From<UnifiedError> for otlp::error::OtlpError {
        fn from(err: UnifiedError) -> Self {
            to_otlp_error(&err)
        }
    }
}
