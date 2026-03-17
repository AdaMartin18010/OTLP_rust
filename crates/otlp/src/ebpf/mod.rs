//! # eBPF Module
//!
//! OpenTelemetry eBPF Instrumentation (OBI) for Linux systems
//!
//! ## Status: 🔄 ALPHA (2025-2026)
//!
//! OBI (OpenTelemetry eBPF Instrumentation) is currently in **Alpha** stage.
//! This is a rapidly evolving area with active development in the OpenTelemetry community.
//!
//! ## 2025-2026 Developments
//!
//! - **OBI Alpha**: OpenTelemetry eBPF Instrumentation project progress
//! - **Continuous Profiling**: eBPF-based CPU and memory profiling
//! - **Zero-Code Instrumentation**: Kernel-level observability without code changes
//! - **Network Tracing**: TCP/UDP/HTTP/gRPC at kernel level
//! - **Profiling as 4th Pillar**: Joins metrics, logs, and traces
//!
//! ## Features
//!
//! - CPU 性能分析（perf events）
//! - 网络追踪（TCP/UDP/HTTP/gRPC）
//! - 系统调用追踪
//! - 内存分配追踪
//! - OpenTelemetry 集成
//!
//! ## System Requirements
//!
//! - Linux 内核 >= 5.8 (推荐 5.15+)
//! - CAP_BPF 权限（或 root）
//! - BTF (BPF Type Format) 支持
//!
//! ## Platform Support
//!
//! | Feature | Linux | Windows | macOS |
//! |---------|-------|---------|-------|
//! | CPU Profiling | ✅ | ❌ | ❌ |
//! | Network Tracing | ✅ | ❌ | ❌ |
//! | Memory Tracing | ✅ | ❌ | ❌ |
//! | Syscall Tracing | ✅ | ❌ | ❌ |
//!
//! ## Rust 2024 Features
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步eBPF操作
//! - **元组收集**: 使用 `collect()` 直接收集eBPF事件到元组
//! - **改进的eBPF集成**: 利用 Rust 2024 的eBPF集成优化提升性能
//!
//! ## Usage Example
//!
//! ```rust,no_run
//! use otlp::ebpf::{EbpfLoader, EbpfConfig};
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let config = EbpfConfig::default();
//!     let mut loader = EbpfLoader::new(config);
//!
//!     // 加载 eBPF 程序
//!     let program_bytes = include_bytes!("programs/cpu_profiler.bpf.o");
//!     loader.load(program_bytes)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ## References
//!
//! - [OpenTelemetry Profiling](https://opentelemetry.io/docs/specs/semconv/profiling/)
//! - [KubeCon 2025 OBI Update](https://bindplane.com/blog/kubecon-north-america-2025-opentelemetry-recap-from-atlanta/)
//! - [Observability Trends 2025](https://bix-tech.com/observability-in-2025/)

mod error;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod events;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod integration;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod loader;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod maps;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod memory;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod networking;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod probes;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod profiling;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod syscalls;
mod types;
mod utils;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use events::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use integration::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use loader::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use memory::{EbpfMemoryTracer, MemoryStats};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use networking::{EbpfNetworkTracer, NetworkStats};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use probes::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use profiling::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use syscalls::{EbpfSyscallTracer, SyscallStats};

pub use error::*;
pub use types::*;
pub use utils::*;

#[cfg(test)]
mod tests;
