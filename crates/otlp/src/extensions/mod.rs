//! # OTLP扩展模块
//!
//! 本模块提供基于官方 `opentelemetry-rust` 库的扩展功能。
//! 这些扩展通过包装官方库的组件来添加独特功能，而非重新实现。
//!
//! ## 设计原则
//!
//! 1. **扩展而非替换**: 通过包装器模式扩展官方库，不替换核心实现
//! 2. **向后兼容**: 保持与官方API的完全兼容
//! 3. **可选功能**: 通过feature flags控制扩展功能
//!
//! ## 模块结构
//!
//! - `ebpf/` - eBPF性能分析和追踪扩展
//! - `simd/` - SIMD向量化优化扩展
//! - `tracezip/` - Tracezip压缩扩展
//! - `enterprise/` - 企业级特性扩展
//! - `performance/` - 性能优化扩展

/// eBPF扩展模块
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub mod ebpf;

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
pub mod ebpf {
    // 非Linux平台或ebpf feature未启用时的占位实现
    pub struct EbpfTracerExtension;
    impl EbpfTracerExtension {
        pub fn wrap<S>(_tracer: S) -> Self
        where
            S: opentelemetry::trace::Tracer,
        {
            Self
        }
        pub fn with_ebpf_profiling(self, _enabled: bool) -> Self {
            Self
        }
    }
}

/// SIMD优化扩展模块
pub mod simd;

/// Tracezip压缩扩展模块
pub mod tracezip;

/// 企业级特性扩展模块
pub mod enterprise;

/// 性能优化扩展模块
pub mod performance;
