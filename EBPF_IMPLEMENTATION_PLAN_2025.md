# eBPF 功能实现计划

**创建日期**: 2025年1月
**状态**: 🚀 实施中
**优先级**: P0 (最高)

---

## 📋 执行摘要

项目目前有 eBPF 框架代码，但缺少实际实现。本计划将实现完整的 eBPF 功能，包括性能分析、网络追踪、系统调用追踪等。

---

## 🔍 当前状态分析

### 已有代码

- ✅ `crates/otlp/src/profiling/ebpf.rs` - 框架代码（占位实现）
- ✅ `examples/ebpf_profiling_example.rs` - 示例代码
- ✅ 文档和理论分析

### 缺失功能

- ❌ 实际的 eBPF 程序加载和执行
- ❌ eBPF 库依赖（libbpf-rs 或 aya）
- ❌ 网络追踪功能
- ❌ 系统调用追踪功能
- ❌ 内核事件处理

---

## 🎯 实现目标

### 核心功能

1. **性能分析（Profiling）**
   - CPU 性能分析（perf events）
   - 内存分配追踪
   - 函数调用追踪（kprobes/uprobes）

2. **网络追踪**
   - TCP/UDP 连接追踪
   - HTTP/gRPC 请求追踪
   - 网络包统计

3. **系统调用追踪**
   - 系统调用统计
   - 文件 I/O 追踪
   - 进程创建/销毁追踪

### 性能目标

- CPU 开销: <1%
- 内存开销: <50MB
- 延迟: <100μs
- 零应用代码修改

---

## 📦 技术方案

### 库选择

#### 选项 1: libbpf-rs (推荐用于生产)

- **优势**: 成熟的库，基于 libbpf（C 库）
- **劣势**: 需要系统 libbpf 库
- **适用场景**: 生产环境，稳定性优先

#### 选项 2: aya (推荐用于开发)

- **优势**: 纯 Rust 实现，无需 C 依赖
- **劣势**: 相对较新，生态系统较小
- **适用场景**: 开发环境，易于集成

#### 最终选择: 同时支持两者（可选特性）

- `ebpf-libbpf`: 使用 libbpf-rs
- `ebpf-aya`: 使用 aya
- 默认：优先使用 libbpf-rs，fallback 到 aya

### 架构设计

```rust
crates/otlp/src/ebpf/
├── mod.rs              // 模块入口
├── loader.rs           // eBPF程序加载器
├── probes.rs           // 探针管理（kprobes/uprobes/tracepoints）
├── events.rs           // 事件处理
├── maps.rs             // eBPF Maps管理
├── profiling.rs        // 性能分析
├── networking.rs       // 网络追踪
├── syscalls.rs         // 系统调用追踪
├── types.rs            // 数据类型定义
└── programs/           // eBPF程序（C/Rust）
    ├── cpu_profiler.bpf.c
    ├── network_trace.bpf.c
    └── syscall_trace.bpf.c
```

---

## 🚀 实施计划

### Phase 1: 基础设施（Week 1-2）

#### 1.1 添加依赖

```toml
# Cargo.toml
[dependencies]
# eBPF支持（可选特性）
libbpf-rs = { version = "0.23", optional = true }  # 或 aya = "0.13", optional = true
```

#### 1.2 创建模块结构

- 创建 `crates/otlp/src/ebpf/` 目录
- 实现基础加载器和类型定义

#### 1.3 构建系统集成

- 添加 eBPF 程序编译脚本
- 集成到 Cargo 构建流程

### Phase 2: 性能分析（Week 3-4）

#### 2.1 CPU 性能分析

- 实现 perf events 支持
- 堆栈采样
- pprof 格式导出

#### 2.2 内存追踪

- 内存分配追踪
- 内存泄漏检测

### Phase 3: 网络追踪（Week 5-6）

#### 3.1 TCP/UDP 追踪

- 连接建立/关闭追踪
- 数据包统计

#### 3.2 HTTP/gRPC 追踪

- 请求/响应追踪
- 与 OpenTelemetry Traces 集成

### Phase 4: 系统调用追踪（Week 7-8）

#### 4.1 系统调用统计

- 系统调用频率统计
- 延迟分析

#### 4.2 文件 I/O 追踪

- 文件读写追踪
- I/O 性能分析

### Phase 5: 集成与文档（Week 9-10）

#### 5.1 OpenTelemetry 集成

- 导出到 OTLP
- Metrics/Traces 集成

#### 5.2 文档和示例

- API 文档
- 使用示例
- 部署指南

---

## 📝 实施步骤

### Step 1: 更新 Cargo.toml

```toml
[features]
default = ["async", "grpc", "http"]
ebpf = ["libbpf-rs"]  # 或 ["aya"]
ebpf-aya = ["aya"]    # 使用 aya 实现
ebpf-libbpf = ["libbpf-rs"]  # 使用 libbpf-rs 实现

[dependencies]
# eBPF支持
libbpf-rs = { version = "0.23", optional = true }
# 或者
# aya = { version = "0.13", optional = true }
```

### Step 2: 实现基础模块

创建 `crates/otlp/src/ebpf/mod.rs`:

```rust
//! # eBPF Module
//!
//! 提供基于 eBPF 的性能分析、网络追踪和系统调用追踪功能。

#[cfg(feature = "ebpf")]
mod loader;
#[cfg(feature = "ebpf")]
mod probes;
#[cfg(feature = "ebpf")]
mod events;
#[cfg(feature = "ebpf")]
mod maps;
#[cfg(feature = "ebpf")]
mod profiling;
#[cfg(feature = "ebpf")]
mod networking;
#[cfg(feature = "ebpf")]
mod syscalls;
mod types;

#[cfg(feature = "ebpf")]
pub use loader::*;
#[cfg(feature = "ebpf")]
pub use probes::*;
#[cfg(feature = "ebpf")]
pub use events::*;
#[cfg(feature = "ebpf")]
pub use profiling::*;
#[cfg(feature = "ebpf")]
pub use networking::*;
#[cfg(feature = "ebpf")]
pub use syscalls::*;

pub use types::*;
```

### Step 3: 实现加载器

创建 `crates/otlp/src/ebpf/loader.rs`:

```rust
//! eBPF程序加载器
//!
//! 负责加载和验证 eBPF 程序

use crate::error::Result;

/// eBPF程序加载器
pub struct EbpfLoader {
    // 实现细节
}

impl EbpfLoader {
    /// 加载eBPF程序
    pub fn load_program(&mut self, program_bytes: &[u8]) -> Result<()> {
        // TODO: 实现程序加载逻辑
        todo!("实现 eBPF 程序加载")
    }

    /// 附加程序到探针
    pub fn attach_probe(&mut self, program_fd: i32, probe_name: &str) -> Result<()> {
        // TODO: 实现探针附加逻辑
        todo!("实现探针附加")
    }
}
```

---

## ✅ 验证标准

### 功能验证

- ✅ 能够加载 eBPF 程序
- ✅ 能够附加到内核探针
- ✅ 能够读取 eBPF Maps
- ✅ 性能开销符合目标

### 测试验证

- ✅ 单元测试覆盖 >80%
- ✅ 集成测试通过
- ✅ 性能基准测试通过

---

## 🔗 参考资源

### 官方文档

- eBPF.io: <https://ebpf.io/>
- libbpf-rs: <https://github.com/libbpf/libbpf-rs>
- aya: <https://aya-rs.dev/>

### 教程

- eBPF 开发者教程: <https://github.com/eunomia-bpf/bpf-developer-tutorial>
- Rust eBPF 实践: <https://aya-rs.dev/book/>

---

**状态**: 📝 计划完成，待实施
**下一步**: 开始 Phase 1 实施
