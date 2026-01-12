# eBPF 功能完整实现计划

**创建日期**: 2025年1月
**状态**: 📋 完整计划
**优先级**: P0 (最高)

---

## 📋 执行摘要

项目缺少完整的 eBPF 功能实现。本计划提供完整的实施方案，包括依赖添加、代码实现、测试和文档。

---

## 🔍 当前状态

### ✅ 已有

- 框架代码 (`crates/otlp/src/profiling/ebpf.rs`)
- 示例代码框架 (`examples/ebpf_profiling_example.rs`)
- 理论文档

### ❌ 缺失

- eBPF 库依赖（aya 或 libbpf-rs）
- 实际实现代码
- 网络追踪功能
- 系统调用追踪功能
- 完整的文档

---

## 🎯 实现目标

### 核心功能

1. **CPU 性能分析** (perf events)
2. **网络追踪** (TCP/UDP/HTTP/gRPC)
3. **系统调用追踪** (syscalls)
4. **内存分配追踪** (malloc/free)
5. **OpenTelemetry 集成**

### 技术指标

- CPU 开销: <1%
- 内存开销: <50MB
- 采样频率: 99Hz (默认)
- 零代码侵入

---

## 📦 技术方案

### 库选择

#### 推荐方案：aya (纯 Rust)

**优势**:

- 纯 Rust 实现，无需 C 依赖
- 活跃的社区支持
- 易于集成到 Rust 项目
- 适合快速开发

**版本**: 0.13+ (最新稳定版)

**依赖**:

```toml
aya = { version = "0.13", optional = true }
object = { version = "0.40", optional = true }
```

#### 备选方案：libbpf-rs

**优势**:

- 基于成熟的 libbpf (C 库)
- 生产环境验证
- 更好的性能

**劣势**:

- 需要系统 libbpf 库
- 需要 C 工具链

**版本**: 0.23+ (最新稳定版)

### 最终决策

**推荐使用 aya**:

- 更适合 Rust 生态系统
- 无需外部 C 依赖
- 更易于维护

---

## 🏗️ 模块架构

### 目录结构

```
crates/otlp/src/ebpf/
├── mod.rs              // 模块入口和公共API
├── loader.rs           // eBPF程序加载器
├── probes.rs           // 探针管理（kprobes/uprobes/tracepoints）
├── events.rs           // 事件处理
├── maps.rs             // eBPF Maps管理
├── profiling.rs        // CPU性能分析
├── networking.rs       // 网络追踪
├── syscalls.rs         // 系统调用追踪
├── memory.rs           // 内存分配追踪
├── types.rs            // 数据类型定义
└── error.rs            // 错误类型定义
```

### 功能模块

1. **Profiling (性能分析)**
   - CPU 采样
   - 堆栈追踪
   - pprof 格式导出

2. **Networking (网络追踪)**
   - TCP/UDP 连接追踪
   - HTTP/gRPC 请求追踪
   - 网络包统计

3. **Syscalls (系统调用追踪)**
   - 系统调用统计
   - 文件 I/O 追踪
   - 进程创建/销毁追踪

4. **Memory (内存追踪)**
   - 内存分配追踪
   - 内存泄漏检测

---

## 🚀 实施步骤

### Phase 1: 依赖和基础设施 (1-2天)

#### Step 1.1: 添加依赖

**文件**: `Cargo.toml` (workspace级别)

```toml
[workspace.dependencies]
# eBPF支持 - aya (纯Rust实现，推荐)
aya = { version = "0.13", optional = true }
object = { version = "0.40", optional = true }
```

**文件**: `crates/otlp/Cargo.toml`

```toml
[features]
default = ["async", "grpc", "http"]
# eBPF支持（需要Linux内核 >= 5.8）
ebpf = ["dep:aya", "dep:object"]

[dependencies]
# eBPF支持
aya = { workspace = true, optional = true }
object = { workspace = true, optional = true }
```

#### Step 1.2: 创建模块结构

创建 `crates/otlp/src/ebpf/` 目录和基础模块文件。

### Phase 2: 基础实现 (1周)

#### Step 2.1: 类型定义 (`types.rs`)

定义配置、事件、错误等类型。

#### Step 2.2: 加载器 (`loader.rs`)

实现 eBPF 程序加载和验证。

#### Step 2.3: 探针管理 (`probes.rs`)

实现 kprobes/uprobes/tracepoints 管理。

### Phase 3: 核心功能 (2-3周)

#### Step 3.1: CPU 性能分析 (`profiling.rs`)

- perf events 支持
- 堆栈采样
- pprof 格式导出

#### Step 3.2: 网络追踪 (`networking.rs`)

- TCP/UDP 连接追踪
- HTTP/gRPC 请求追踪

#### Step 3.3: 系统调用追踪 (`syscalls.rs`)

- 系统调用统计
- 文件 I/O 追踪

### Phase 4: 集成和测试 (1-2周)

#### Step 4.1: OpenTelemetry 集成

- OTLP 导出
- Metrics/Traces 集成

#### Step 4.2: 测试

- 单元测试
- 集成测试
- 性能测试

#### Step 4.3: 文档

- API 文档
- 使用示例
- 部署指南

---

## 📝 代码实现模板

### types.rs

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
            sample_rate: 99,
            duration: Duration::from_secs(60),
        }
    }
}
```

### loader.rs (基础框架)

```rust
//! eBPF 程序加载器

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use aya::{Bpf, programs::KProbe};

use crate::error::Result;
use crate::ebpf::types::EbpfConfig;

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
}
```

---

## ✅ 验证标准

### 功能验证

- ✅ 能够加载 eBPF 程序
- ✅ 能够附加到内核探针
- ✅ 能够收集和处理事件
- ✅ 性能开销符合目标

### 测试验证

- ✅ 单元测试覆盖 >80%
- ✅ 集成测试通过
- ✅ 性能基准测试通过

### 文档验证

- ✅ API 文档完整
- ✅ 使用示例可用
- ✅ 部署指南清晰

---

## 🔗 参考资源

### 官方文档

- eBPF.io: <https://ebpf.io/>
- aya: <https://aya-rs.dev/>
- aya Book: <https://aya-rs.dev/book/>

### 教程

- eBPF 开发者教程: <https://github.com/eunomia-bpf/bpf-developer-tutorial>
- Rust eBPF 实践: <https://aya-rs.dev/book/>

### 示例

- aya 示例: <https://github.com/aya-rs/aya/tree/main/examples>

---

## 📅 时间表

### Week 1-2: 基础设施

- 添加依赖
- 创建模块结构
- 实现基础类型

### Week 3-4: 核心功能

- CPU 性能分析
- 基础事件处理

### Week 5-6: 扩展功能

- 网络追踪
- 系统调用追踪

### Week 7-8: 集成和测试

- OpenTelemetry 集成
- 测试和文档

---

**状态**: 📝 计划完成
**下一步**: 开始 Phase 1 实施
