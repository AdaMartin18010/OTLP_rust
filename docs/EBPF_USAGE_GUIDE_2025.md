# eBPF 使用指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [概述](#概述)
- [系统要求](#系统要求)
- [快速开始](#快速开始)
- [配置选项](#配置选项)
- [功能使用](#功能使用)
- [最佳实践](#最佳实践)
- [故障排查](#故障排查)

---

## 概述

eBPF (extended Berkeley Packet Filter) 模块提供了基于内核的性能分析、网络追踪和系统调用追踪功能，无需修改应用代码即可收集详细的性能数据。

### 主要功能

1. **CPU 性能分析** - 基于 perf events 的 CPU 采样
2. **网络追踪** - TCP/UDP/HTTP/gRPC 连接追踪
3. **系统调用追踪** - 系统调用统计和延迟分析
4. **内存追踪** - 内存分配和释放追踪

---

## 系统要求

### 操作系统

- **Linux** (必需)
- 内核版本 >= 5.8 (推荐 5.15+)
- BTF (BPF Type Format) 支持

### 权限

- **CAP_BPF** 权限（或 root）
- 或者使用 `setcap cap_bpf+ep /path/to/binary`

### Rust 版本

- Rust 1.92+ (必需)

---

## 快速开始

### 1. 添加依赖

在 `Cargo.toml` 中启用 eBPF feature:

```toml
[dependencies]
otlp = { path = "../crates/otlp", features = ["ebpf"] }
```

### 2. 基本使用

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_duration(Duration::from_secs(60));

    // 创建性能分析器
    let mut profiler = EbpfCpuProfiler::new(config);

    // 开始分析
    profiler.start()?;

    // 执行工作负载
    // ... 你的代码 ...

    // 停止并获取 profile
    let profile = profiler.stop()?;

    Ok(())
}
```

---

## 配置选项

### EbpfConfig

```rust
pub struct EbpfConfig {
    pub enable_cpu_profiling: bool,      // 启用 CPU 性能分析
    pub enable_network_tracing: bool,    // 启用网络追踪
    pub enable_syscall_tracing: bool,    // 启用系统调用追踪
    pub enable_memory_tracing: bool,     // 启用内存追踪
    pub sample_rate: u32,                // 采样频率 (Hz)
    pub duration: Duration,              // 采样持续时间
    pub max_samples: usize,              // 最大采样数
}
```

### 默认配置

```rust
EbpfConfig::default()
// enable_cpu_profiling: true
// enable_network_tracing: false
// enable_syscall_tracing: false
// enable_memory_tracing: false
// sample_rate: 99 Hz
// duration: 60 seconds
// max_samples: 100000
```

### 自定义配置

```rust
let config = EbpfConfig::new()
    .with_sample_rate(50)           // 50Hz 采样频率
    .with_duration(Duration::from_secs(120))  // 2分钟
    .with_network_tracing(true)     // 启用网络追踪
    .with_syscall_tracing(true)     // 启用系统调用追踪
    .with_memory_tracing(true);     // 启用内存追踪
```

---

## 功能使用

### CPU 性能分析

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};

let config = EbpfConfig::default();
let mut profiler = EbpfCpuProfiler::new(config);

profiler.start()?;
// ... 执行代码 ...
let profile = profiler.stop()?;
```

### 网络追踪

```rust
use otlp::ebpf::{EbpfConfig, EbpfNetworkTracer};

let config = EbpfConfig::default()
    .with_network_tracing(true);

let mut tracer = EbpfNetworkTracer::new(config);
tracer.start()?;
// ... 网络活动 ...
let events = tracer.stop()?;
```

### 系统调用追踪

```rust
use otlp::ebpf::{EbpfConfig, EbpfSyscallTracer};

let config = EbpfConfig::default()
    .with_syscall_tracing(true);

let mut tracer = EbpfSyscallTracer::new(config);
tracer.start()?;
// ... 系统调用活动 ...
let events = tracer.stop()?;
```

### 内存追踪

```rust
use otlp::ebpf::{EbpfConfig, EbpfMemoryTracer};

let config = EbpfConfig::default()
    .with_memory_tracing(true);

let mut tracer = EbpfMemoryTracer::new(config);
tracer.start()?;
// ... 内存分配活动 ...
let events = tracer.stop()?;
```

---

## 最佳实践

### 1. 采样频率选择

- **开发环境**: 99Hz (默认)
- **生产环境**: 19-49Hz (降低开销)
- **调试模式**: 99-199Hz (更高精度)

### 2. 性能开销

- **CPU 开销**: <1% (目标)
- **内存开销**: <50MB (目标)
- 根据实际需求调整采样频率

### 3. 权限管理

```bash
# 使用 setcap 授予权限（推荐）
sudo setcap cap_bpf+ep /path/to/your/binary

# 或使用 root 运行（不推荐用于生产）
sudo ./your_binary
```

### 4. 错误处理

```rust
match profiler.start() {
    Ok(()) => println!("启动成功"),
    Err(e) => {
        eprintln!("启动失败: {}", e);
        // 处理错误（可能是权限不足或内核不支持）
    }
}
```

---

## 故障排查

### 常见问题

#### 1. 权限不足

**错误**: `权限不足: 需要 CAP_BPF 权限或 root`

**解决**:

```bash
# 授予权限
sudo setcap cap_bpf+ep /path/to/binary

# 或使用 root（不推荐）
sudo ./your_binary
```

#### 2. 内核版本不兼容

**错误**: `内核版本不兼容: 需要 Linux 内核 >= 5.8`

**解决**:

```bash
# 检查内核版本
uname -r

# 需要升级内核到 5.8+ 或 5.15+ (推荐)
```

#### 3. BTF 不支持

**错误**: `BTF 不支持`

**解决**:

```bash
# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux

# 如果不存在，需要升级内核或启用 BTF
```

#### 4. Feature 未启用

**错误**: `eBPF 功能不可用`

**解决**:

```toml
# 在 Cargo.toml 中启用 feature
[dependencies]
otlp = { path = "../crates/otlp", features = ["ebpf"] }
```

---

## 示例代码

完整的示例代码请参考:

- `examples/ebpf_profiling_example.rs` - 基础性能分析示例
- `examples/ebpf_complete_example.rs` - 完整功能示例

---

## 参考资源

- [eBPF 官方文档](https://ebpf.io/)
- [aya 文档](https://aya-rs.dev/)
- [项目 eBPF 实施计划](../EBPF_IMPLEMENTATION_PLAN_2025.md)

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
