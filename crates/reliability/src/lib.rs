//! # Rust 统一可靠性框架
#![allow(clippy::excessive_nesting)] // 允许复杂控制流嵌套
#![allow(clippy::result_large_err)] // 允许大型错误类型
#![allow(clippy::should_implement_trait)] // 允许自定义 default 方法名
#![allow(clippy::new_without_default)] // 允许没有 Default 的 new 方法
//!
//! 本库提供了全面的可靠性解决方案，包括：
//! - 统一错误处理系统
//! - 容错机制（断路器、重试、降级）
//! - 运行时监控和自愈
//! - 混沌工程测试工具
//! - Rust 1.94+ 新特性支持
//!
//! ## 核心特性
//!
//! - **统一错误处理**：提供类型安全、上下文丰富的错误处理
//! - **容错机制**：断路器、重试、超时、降级等企业级容错模式
//! - **运行时监控**：健康检查、性能监控、异常检测
//! - **自动恢复**：内存泄漏检测、连接池重建、死锁恢复
//! - **混沌工程**：故障注入、弹性测试、恢复验证
//! - **Rust 1.94+ 特性**：支持 array_windows、LazyLock、数学常数等最新语言特性
//!
//! ## Rust 1.94 特性应用
//!
//! - **array_windows**: 使用 `slice.array_windows()` 检测错误序列中的模式
//! - **element_offset**: 使用 `offset_of!` 进行内存高效的错误追踪
//! - **LazyLock/LazyCell**: 使用延迟初始化管理全局监控状态
//! - **数学常数**: 使用 `GOLDEN_RATIO`、`EULER_GAMMA` 实现自适应重试策略
//! - **const mul_add**: 使用编译时优化的数学计算
//!
//! ## 快速开始
//!
//! ```rust,ignore
//! use c13_reliability::prelude::*;
//! use c13_reliability::error_handling::UnifiedError;
//! use c13_reliability::fault_tolerance::{CircuitBreaker, RetryPolicy};
//! use c13_reliability::runtime_monitoring::HealthChecker;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), UnifiedError> {
//!     // 初始化监控
//!     let health_checker = HealthChecker::new();
//!
//!     // 创建断路器
//!     let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
//!
//!     // 创建重试策略
//!     let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));
//!
//!     // 执行带容错的操作
//!     let result = circuit_breaker
//!         .with_retry(retry_policy)
//!         .execute(|| async {
//!             // 你的业务逻辑
//!             Ok::<String, UnifiedError>("success".to_string())
//!         })
//!         .await?;
//!
//!     println!("操作结果: {}", result);
//!     Ok(())
//! }
//! ```
//!
//! ## Rust 1.92+ 新特性示例
//!
//! ```rust,ignore
//! use c13_reliability::prelude::*;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), UnifiedError> {
//!     // 演示Rust 1.92新特性
//!     let demo = Rust192FeatureDemo::new();
//!
//!     // 异步闭包示例
//!     let results = demo.demonstrate_async_closures().await?;
//!     println!("异步闭包结果: {:?}", results);
//!
//!     // 泛型关联类型示例
//!     let operation_result = demo.demonstrate_generic_associated_types();
//!     println!("泛型关联类型结果: {:?}", operation_result);
//!
//!     // 高级异步组合器
//!     let combinator = AdvancedAsyncCombinator;
//!     let chain_result = combinator.create_operation_chain(
//!         0i32,
//!         vec![
//!             |x| async move { Ok::<i32, UnifiedError>(x + 1) },
//!             |x| async move { Ok::<i32, UnifiedError>(x * 2) },
//!         ]
//!     ).await?;
//!     println!("操作链结果: {}", chain_result);
//!
//!     Ok(())
//! }
//! ```

// 核心模块
pub mod chaos_engineering;
pub mod config;
pub mod error_handling;
pub mod fault_tolerance;
pub mod metrics;
pub mod runtime_monitoring;
pub mod utils;

// 运行时环境支持
pub mod runtime_environments;

// Rust 1.92+ 新特性支持
pub mod rust_192_features;

// Rust 1.94+ 新特性支持
pub mod rust_1_94_features;

// 分布式系统模块
pub mod distributed_systems;

// 并发模型模块
pub mod concurrency_models;

// 微服务架构模块
pub mod microservices;

// 执行流感知系统
pub mod execution_flow;

// 系统自我感知
pub mod self_awareness;

// 设计模式库
pub mod design_patterns;

// 高级可观测性
pub mod observability;

// 性能基准测试
pub mod benchmarking;

// 重新导出常用类型和函数
pub mod prelude {
    pub use crate::chaos_engineering::{
        ChaosScenarios, FaultInjector, RecoveryTester, ResilienceTester,
    };
    pub use crate::config::ReliabilityConfig;
    pub use crate::error_handling::{
        ErrorContext, ErrorMonitor, ErrorRecovery, ErrorSeverity, GlobalErrorMonitor, ResultExt,
        UnifiedError,
    };
    pub use crate::fault_tolerance::{
        Bulkhead, CircuitBreaker, Fallback, FaultToleranceConfig, ResilienceBuilder, RetryPolicy,
        Timeout,
    };
    pub use crate::metrics::ReliabilityMetrics;
    pub use crate::runtime_environments::{
        ContainerEnvironmentAdapter, EmbeddedEnvironmentAdapter, EnvironmentCapabilities,
        HealthLevel, HealthStatus, OSEnvironmentAdapter, RecoveryType, ResourceUsage,
        RuntimeEnvironment, RuntimeEnvironmentAdapter, RuntimeEnvironmentManager, SystemInfo,
    };
    pub use crate::runtime_monitoring::{
        AnomalyDetector, AutoRecovery, HealthChecker, MonitoringConfig, MonitoringDashboard,
        PerformanceMonitor, ResourceMonitor,
    };
    pub use crate::rust_1_94_features::{
        AdaptiveRetryConfig, ConstMathCalculations, ErrorAnalysisResult, ErrorPattern,
        ErrorPatternTracker, ErrorSequenceAnalyzer, ErrorType, EulerConstants,
        EulerGammaHealthScoring, GoldenRatioBackoff, GoldenRatioConstants, MathConstantsDemo,
        MemoryLayoutInfo, ReliabilityMonitor, Rust194FeatureDemo,
    };
    pub use crate::rust_192_features::{
        AdvancedAsyncCombinator, AsyncClosureExample, GenericAssociatedTypeExample,
        OperationMetadata, OperationResult, ReliabilityService, Rust192FeatureDemo,
    };
    pub use crate::utils::{DurationExt, ResultExt as UtilsResultExt};

    // 常用标准库类型
    pub use anyhow::Result;
    pub use std::sync::Arc;
    pub use std::time::Duration;
    pub use tracing::{debug, error, info, trace, warn};
}

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");

/// 获取库版本信息
pub fn version() -> &'static str {
    VERSION
}

/// 获取库名称
pub fn name() -> &'static str {
    NAME
}

/// 初始化可靠性框架
///
/// 这个函数会初始化全局错误监控、指标收集和健康检查系统
pub async fn init() -> Result<(), crate::error_handling::UnifiedError> {
    // 初始化全局错误监控
    crate::error_handling::GlobalErrorMonitor::init().await?;

    // 初始化指标收集
    // crate::metrics::ReliabilityMetrics::init().await?;

    // 初始化健康检查
    crate::runtime_monitoring::GlobalHealthChecker::init_global().await?;

    tracing::info!("可靠性框架初始化完成");
    Ok(())
}

/// 优雅关闭可靠性框架
///
/// 这个函数会清理资源、保存指标数据并关闭监控系统
pub async fn shutdown() -> Result<(), crate::error_handling::UnifiedError> {
    tracing::info!("开始关闭可靠性框架");

    // 保存指标数据
    // crate::metrics::ReliabilityMetrics::shutdown().await?;

    // 关闭健康检查
    crate::runtime_monitoring::GlobalHealthChecker::shutdown_global().await?;

    // 关闭全局错误监控
    crate::error_handling::GlobalErrorMonitor::shutdown().await?;

    tracing::info!("可靠性框架关闭完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_init_and_shutdown() {
        // 测试初始化和关闭
        assert!(init().await.is_ok());
        assert!(shutdown().await.is_ok());
    }

    #[test]
    fn test_version_info() {
        assert!(!version().is_empty());
        assert!(!name().is_empty());
        assert_eq!(name(), env!("CARGO_PKG_NAME"));
    }
}
