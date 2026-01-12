# eBPF 示例指南 2025

**创建日期**: 2025年1月
**状态**: 📚 示例指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 示例指南 2025](#ebpf-示例指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [可用示例](#可用示例)
    - [1. 完整功能示例](#1-完整功能示例)
    - [2. CPU 性能分析示例](#2-cpu-性能分析示例)
    - [3. 网络追踪示例](#3-网络追踪示例)
    - [4. 系统调用追踪示例](#4-系统调用追踪示例)
  - [运行示例](#运行示例)
    - [系统要求](#系统要求)
    - [基本步骤](#基本步骤)
  - [示例详解](#示例详解)
    - [完整功能示例结构](#完整功能示例结构)
    - [CPU 性能分析示例结构](#cpu-性能分析示例结构)
  - [常见问题](#常见问题)
    - [Q1: 运行示例时提示权限不足](#q1-运行示例时提示权限不足)
    - [Q2: 运行示例时提示内核版本不兼容](#q2-运行示例时提示内核版本不兼容)
    - [Q3: 如何修改示例配置？](#q3-如何修改示例配置)
    - [Q4: 示例运行很慢怎么办？](#q4-示例运行很慢怎么办)
  - [参考资源](#参考资源)

---

## 概述

本文档介绍项目中的 eBPF 示例，帮助开发者快速理解和使用 eBPF 功能。

---

## 可用示例

项目中提供了 4 个 eBPF 示例，涵盖了不同的使用场景：

1. **完整功能示例** - 演示所有 eBPF 功能
2. **CPU 性能分析示例** - 专注 CPU 性能分析
3. **网络追踪示例** - 专注网络活动追踪
4. **系统调用追踪示例** - 专注系统调用追踪

### 1. 完整功能示例

**文件**: `examples/ebpf_complete_example.rs`
**功能**: 演示 eBPF 的完整功能，包括 CPU 性能分析、网络追踪、系统调用追踪和内存追踪。

**运行**:

```bash
sudo cargo run --example ebpf_complete --features ebpf
```

**适用场景**:

- 了解 eBPF 完整功能
- 学习如何配置和使用各种追踪器
- 参考完整的使用模式

---

### 2. CPU 性能分析示例

**文件**: `examples/ebpf_profiling_example.rs`
**功能**: 演示如何使用 eBPF 进行 CPU 性能分析。

**运行**:

```bash
# 使用默认配置
cargo run --example ebpf_profiling --features ebpf

# 使用生产环境配置
ENV=production cargo run --example ebpf_profiling --features ebpf
```

**适用场景**:

- 专注 CPU 性能分析
- 学习性能分析配置
- 性能瓶颈诊断

### 3. 网络追踪示例

**文件**: `examples/ebpf_network_tracing_example.rs`
**功能**: 演示如何使用 eBPF 进行网络活动追踪。

**运行**:

```bash
# 使用默认配置
cargo run --example ebpf_network_tracing --features ebpf
```

**适用场景**:

- 网络活动监控
- 连接追踪
- 数据包分析

### 4. 系统调用追踪示例

**文件**: `examples/ebpf_syscall_tracing_example.rs`
**功能**: 演示如何使用 eBPF 进行系统调用追踪。

**运行**:

```bash
# 使用默认配置
cargo run --example ebpf_syscall_tracing --features ebpf
```

**适用场景**:

- 系统调用监控
- 性能分析
- 安全审计

**运行**:

```bash
# 使用默认配置
sudo cargo run --example ebpf_profiling --features ebpf

# 指定环境（production/staging/development/debug）
ENV=production sudo cargo run --example ebpf_profiling --features ebpf
```

**适用场景**:

- 专注 CPU 性能分析
- 学习性能分析配置
- 理解性能开销

---

## 运行示例

### 系统要求

1. **操作系统**: Linux（内核 >= 5.8，推荐 5.15+）
2. **权限**: CAP_BPF 或 root
3. **依赖**: 启用 `ebpf` feature

### 基本步骤

1. **检查系统支持**

```bash
# 检查内核版本
uname -r

# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux
```

1. **授予权限（推荐）**

```bash
# 使用 setcap 授予权限
sudo setcap cap_bpf+ep target/debug/examples/ebpf_profiling
```

1. **运行示例**

```bash
# 编译并运行
sudo cargo run --example ebpf_profiling --features ebpf

# 或先编译再运行
cargo build --example ebpf_profiling --features ebpf
sudo ./target/debug/examples/ebpf_profiling
```

---

## 示例详解

### 完整功能示例结构

```rust
// 1. 创建配置
let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_cpu_profiling(true)
    .with_network_tracing(true);

// 2. 创建追踪器
let mut profiler = EbpfCpuProfiler::new(config)?;

// 3. 启动追踪
profiler.start()?;

// 4. 执行工作负载
// ... 你的代码 ...

// 5. 停止追踪
let profile = profiler.stop()?;

// 6. 获取性能开销
let overhead = profiler.get_overhead();
```

### CPU 性能分析示例结构

```rust
// 1. 使用推荐配置
let config = create_recommended_config("development");

// 2. 验证配置
validate_config(&config)?;

// 3. 创建分析器
let mut profiler = EbpfCpuProfiler::new(config)?;

// 4. 启动分析
profiler.start()?;

// 5. 执行工作负载
// ... 你的代码 ...

// 6. 停止分析
let profile_data = profiler.stop()?;

// 7. 获取开销
let overhead = profiler.get_overhead();
```

---

## 常见问题

### Q1: 运行示例时提示权限不足

**错误**: `权限不足: 需要 CAP_BPF 权限或 root`

**解决**:

```bash
# 方案 1: 使用 sudo（简单但不推荐用于生产）
sudo cargo run --example ebpf_profiling --features ebpf

# 方案 2: 使用 setcap（推荐）
sudo setcap cap_bpf+ep target/debug/examples/ebpf_profiling
cargo run --example ebpf_profiling --features ebpf
```

### Q2: 运行示例时提示内核版本不兼容

**错误**: `内核版本不兼容: 需要 Linux 内核 >= 5.8`

**解决**:

```bash
# 检查内核版本
uname -r

# 如果版本低于 5.8，需要升级内核
# Ubuntu/Debian
sudo apt update
sudo apt install linux-generic-hwe-22.04
```

### Q3: 如何修改示例配置？

**方法 1**: 使用环境变量

```bash
ENV=production cargo run --example ebpf_profiling --features ebpf
```

**方法 2**: 修改示例代码

```rust
let config = EbpfConfig::default()
    .with_sample_rate(50)  // 修改采样频率
    .with_max_samples(50_000);  // 修改最大采样数
```

### Q4: 示例运行很慢怎么办？

**可能原因**:

- 采样频率过高
- 工作负载太长
- 系统资源不足

**解决**:

- 降低采样频率: `with_sample_rate(19)`
- 缩短工作负载时间
- 检查系统资源使用情况

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [快速开始](./QUICK_START_EBPF_2025.md)
- [最佳实践](./EBPF_BEST_PRACTICES_2025.md)
- [故障排查](./EBPF_TROUBLESHOOTING_2025.md)

---

**状态**: 📚 示例指南
**最后更新**: 2025年1月
