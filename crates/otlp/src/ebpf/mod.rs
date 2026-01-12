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
pub use networking::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use syscalls::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use memory::*;
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use integration::*;

pub use types::*;
pub use error::*;
pub use utils::*;

#[cfg(test)]
mod tests;
