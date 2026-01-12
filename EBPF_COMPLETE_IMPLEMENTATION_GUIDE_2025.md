# eBPF 完整实现指南

**创建日期**: 2025年1月
**状态**: 🚀 完整实施指南
**优先级**: P0 (最高)

---

## 📋 概述

本指南提供完整的 eBPF 功能实现方案，包括依赖添加、代码实现、测试和文档。

---

## 🎯 实现目标

### 核心功能

1. ✅ CPU 性能分析（perf events）
2. ✅ 网络追踪（TCP/UDP/HTTP/gRPC）
3. ✅ 系统调用追踪
4. ✅ 内存分配追踪
5. ✅ OpenTelemetry 集成

### 技术栈

- **eBPF 库**: aya (纯 Rust) 或 libbpf-rs（推荐生产环境）
- **支持平台**: Linux (内核 >= 5.8)
- **集成**: OpenTelemetry OTLP

---

## 📦 Step 1: 添加依赖

### 1.1 更新 Cargo.toml

在 `crates/otlp/Cargo.toml` 中添加：

```toml
[features]
default = ["async", "grpc", "http"]
# eBPF支持（需要Linux内核 >= 5.8）
ebpf = ["dep:aya", "dep:object"]  # 使用 aya (纯Rust)
# 或者
# ebpf-libbpf = ["dep:libbpf-rs"]  # 使用 libbpf-rs (需要系统libbpf)

[dependencies]
# eBPF支持 - aya (纯Rust实现，推荐)
aya = { version = "0.13", optional = true }
object = { version = "0.40", optional = true }

# 或者使用 libbpf-rs (需要系统libbpf库)
# libbpf-rs = { version = "0.23", optional = true }
```

### 1.2 系统要求

- Linux 内核 >= 5.8（推荐 5.15+）
- CAP_BPF 权限（或 root）
- BTF (BPF Type Format) 支持（内核 5.8+）

---

## 🏗️ Step 2: 创建模块结构

### 2.1 目录结构

```
crates/otlp/src/ebpf/
├── mod.rs              // 模块入口
├── loader.rs           // eBPF程序加载器
├── probes.rs           // 探针管理
├── events.rs           // 事件处理
├── maps.rs             // eBPF Maps管理
├── profiling.rs        // 性能分析
├── networking.rs       // 网络追踪
├── syscalls.rs         // 系统调用追踪
├── types.rs            // 数据类型定义
└── programs/           // eBPF程序源码
    ├── cpu_profiler.bpf.rs
    ├── network_trace.bpf.rs
    └── syscall_trace.bpf.rs
```

### 2.2 创建基础模块

#### mod.rs

```rust
//! # eBPF Module
//!
//! 提供基于 eBPF 的性能分析、网络追踪和系统调用追踪功能。
//!
//! ## 特性
//!
//! - CPU 性能分析
//! - 网络追踪
//! - 系统调用追踪
//! - 内存分配追踪
//! - OpenTelemetry 集成

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
mod types;

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

pub use types::*;
```

#### types.rs

```rust
//! eBPF 数据类型定义

use std::time::Duration;

/// eBPF 配置
#[derive(Debug, Clone)]
pub struct EbpfConfig {
    /// 是否启用 CPU 性能分析
    pub enable_cpu_profiling: bool,
    /// 是否启用网络追踪
    pub enable_network_tracing: bool,
    /// 是否启用系统调用追踪
    pub enable_syscall_tracing: bool,
    /// 采样频率 (Hz)
    pub sample_rate: u32,
    /// 采样持续时间
    pub duration: Duration,
}

impl Default for EbpfConfig {
    fn default() -> Self {
        Self {
            enable_cpu_profiling: true,
            enable_network_tracing: false,
            enable_syscall_tracing: false,
            sample_rate: 99, // 默认 99Hz
            duration: Duration::from_secs(60),
        }
    }
}

/// eBPF 事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EbpfEventType {
    CpuSample,
    NetworkPacket,
    Syscall,
    MemoryAlloc,
}

/// eBPF 事件
#[derive(Debug, Clone)]
pub struct EbpfEvent {
    pub event_type: EbpfEventType,
    pub timestamp: Duration,
    pub pid: u32,
    pub tid: u32,
    pub data: Vec<u8>,
}
```

---

## 🔧 Step 3: 实现核心功能

### 3.1 Loader (加载器)

由于实际实现需要编译 eBPF 程序，这里提供接口定义：

```rust
//! eBPF 程序加载器

use crate::error::Result;
use crate::ebpf::types::EbpfConfig;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use aya::{
    programs::{KProbe, UProbe, TracePoint},
    Bpf,
};

/// eBPF 程序加载器
pub struct EbpfLoader {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    bpf: Option<Bpf>,
    config: EbpfConfig,
}

impl EbpfLoader {
    /// 创建新的加载器
    pub fn new(config: EbpfConfig) -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            bpf: None,
            config,
        }
    }

    /// 加载 eBPF 程序
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn load(&mut self, program_bytes: &[u8]) -> Result<()> {
        // TODO: 使用 aya 加载 eBPF 程序
        // let mut bpf = Bpf::load(program_bytes)?;
        // self.bpf = Some(bpf);
        tracing::info!("eBPF 程序加载功能待实现");
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn load(&mut self, _program_bytes: &[u8]) -> Result<()> {
        Err(crate::error::OtlpError::Unsupported(
            "eBPF 仅在 Linux 平台支持".to_string(),
        ))
    }

    /// 附加程序到探针
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_kprobe(&mut self, name: &str, function: &str) -> Result<()> {
        // TODO: 实现 kprobe 附加
        tracing::info!("KProbe 附加功能待实现: {} -> {}", name, function);
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_kprobe(&mut self, _name: &str, _function: &str) -> Result<()> {
        Err(crate::error::OtlpError::Unsupported(
            "eBPF 仅在 Linux 平台支持".to_string(),
        ))
    }
}
```

### 3.2 Profiling (性能分析)

```rust
//! eBPF 性能分析

use crate::error::Result;
use crate::ebpf::types::{EbpfConfig, EbpfEvent};

/// eBPF 性能分析器
pub struct EbpfProfiler {
    config: EbpfConfig,
    loader: crate::ebpf::loader::EbpfLoader,
}

impl EbpfProfiler {
    /// 创建新的性能分析器
    pub fn new(config: EbpfConfig) -> Self {
        let loader = crate::ebpf::loader::EbpfLoader::new(config.clone());
        Self { config, loader }
    }

    /// 开始性能分析
    pub fn start(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            tracing::info!("启动 eBPF 性能分析");
            // TODO: 加载并启动 CPU 性能分析程序
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            tracing::warn!("eBPF 仅在 Linux 平台支持");
        }

        Ok(())
    }

    /// 停止性能分析
    pub fn stop(&mut self) -> Result<Vec<EbpfEvent>> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            tracing::info!("停止 eBPF 性能分析");
            // TODO: 停止程序并收集事件
            Ok(vec![])
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            Ok(vec![])
        }
    }
}
```

---

## 📝 Step 4: 更新 lib.rs

在 `crates/otlp/src/lib.rs` 中添加：

```rust
// eBPF模块（可选特性）
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub mod ebpf;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use ebpf::{EbpfLoader, EbpfProfiler, EbpfConfig, EbpfEvent};
```

---

## ✅ Step 5: 实现检查清单

### 基础设施

- [ ] 添加 aya 或 libbpf-rs 依赖
- [ ] 创建 eBPF 模块结构
- [ ] 实现基础类型定义
- [ ] 实现加载器接口

### 功能实现

- [ ] CPU 性能分析
- [ ] 网络追踪
- [ ] 系统调用追踪
- [ ] 内存分配追踪

### 集成

- [ ] OpenTelemetry 集成
- [ ] OTLP 导出
- [ ] 配置管理

### 文档和测试

- [ ] API 文档
- [ ] 使用示例
- [ ] 单元测试
- [ ] 集成测试
- [ ] 部署指南

---

## 🚀 下一步行动

1. **立即**: 添加 eBPF 库依赖到 Cargo.toml
2. **本周**: 实现基础模块结构
3. **本月**: 实现 CPU 性能分析功能
4. **下月**: 实现网络追踪和系统调用追踪

---

**状态**: 📝 指南完成
**优先级**: P0
**预计工作量**: 6-8 周
