//! # eBPF Module
//!
//! 提供基于 eBPF 的性能分析、网络追踪和系统调用追踪功能。
//!
//! ## 特性
//!
//! - CPU 性能分析（perf events）
//! - 网络追踪（TCP/UDP/HTTP/gRPC）
//! - 系统调用追踪
//! - 内存分配追踪
//! - OpenTelemetry 集成
//!
//! ## 系统要求
//!
//! - Linux 内核 >= 5.8 (推荐 5.15+)
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步eBPF操作
//! - **元组收集**: 使用 `collect()` 直接收集eBPF事件到元组
//! - **改进的eBPF集成**: 利用 Rust 1.92 的eBPF集成优化提升性能
//! - CAP_BPF 权限（或 root）
//! - BTF (BPF Type Format) 支持
//!
//! ## 使用示例
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

#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod loader;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod probes;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod events;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod maps;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod profiling;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod networking;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod syscalls;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod memory;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod integration;
mod utils;
mod types;
mod error;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use loader::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use probes::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use events::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use profiling::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use networking::{EbpfNetworkTracer, NetworkStats};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use syscalls::{EbpfSyscallTracer, SyscallStats};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use memory::{EbpfMemoryTracer, MemoryStats};
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use integration::*;

pub use types::*;
pub use error::*;
pub use utils::*;

#[cfg(test)]
mod tests;
