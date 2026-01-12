# eBPF 迁移指南 2025

**创建日期**: 2025年1月
**状态**: 📚 迁移指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 迁移指南 2025](#ebpf-迁移指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [版本迁移](#版本迁移)
    - [从 v0.0.x 迁移到 v0.1.0](#从-v00x-迁移到-v010)
      - [主要变更](#主要变更)
  - [API 变更](#api-变更)
    - [旧 API (v0.0.x)](#旧-api-v00x)
    - [新 API (v0.1.0+)](#新-api-v010)
  - [配置迁移](#配置迁移)
    - [旧配置](#旧配置)
    - [新配置](#新配置)
    - [使用推荐配置](#使用推荐配置)
  - [代码迁移示例](#代码迁移示例)
    - [示例 1: CPU 性能分析](#示例-1-cpu-性能分析)
      - [旧代码](#旧代码)
      - [新代码](#新代码)
    - [示例 2: 网络追踪](#示例-2-网络追踪)
      - [旧代码](#旧代码-1)
      - [新代码](#新代码-1)
  - [常见问题](#常见问题)
    - [Q1: 如何迁移旧的配置？](#q1-如何迁移旧的配置)
    - [Q2: 旧的 `EbpfProfiler` 在哪里？](#q2-旧的-ebpfprofiler-在哪里)
    - [Q3: 如何同时使用多个追踪器？](#q3-如何同时使用多个追踪器)
    - [Q4: 性能开销如何获取？](#q4-性能开销如何获取)
  - [参考资源](#参考资源)

---

## 概述

本文档提供从旧版本迁移到新版本的指南，帮助用户顺利升级。

---

## 版本迁移

### 从 v0.0.x 迁移到 v0.1.0

#### 主要变更

1. **模块结构重组**
   - 旧的 `profiling::ebpf` 模块已重构为独立的 `ebpf` 模块
   - 新的模块结构更加清晰和模块化

2. **API 变更**
   - `EbpfProfiler` 已拆分为多个专门的追踪器：
     - `EbpfCpuProfiler` - CPU 性能分析
     - `EbpfNetworkTracer` - 网络追踪
     - `EbpfSyscallTracer` - 系统调用追踪
     - `EbpfMemoryTracer` - 内存追踪

3. **配置变更**
   - `EbpfProfilerConfig` 已重命名为 `EbpfConfig`
   - 配置方法名更新

---

## API 变更

### 旧 API (v0.0.x)

```rust
use otlp::profiling::ebpf::{EbpfProfiler, EbpfProfilerConfig};

let config = EbpfProfilerConfig::new()
    .with_sample_rate(99);
let mut profiler = EbpfProfiler::new(config)?;
profiler.start()?;
let profile = profiler.stop()?;
```

### 新 API (v0.1.0+)

```rust
use otlp::ebpf::{EbpfCpuProfiler, EbpfConfig};

let config = EbpfConfig::default()
    .with_sample_rate(99);
let mut profiler = EbpfCpuProfiler::new(config)?;
profiler.start()?;
let profile = profiler.stop()?;
```

---

## 配置迁移

### 旧配置

```rust
let config = EbpfProfilerConfig::new()
    .with_sample_rate(99)
    .with_duration(Duration::from_secs(60));
```

### 新配置

```rust
let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_duration(Duration::from_secs(60));
```

### 使用推荐配置

```rust
use otlp::ebpf::create_recommended_config;

// 根据环境自动配置
let config = create_recommended_config("production");
```

---

## 代码迁移示例

### 示例 1: CPU 性能分析

#### 旧代码

```rust
use otlp::profiling::ebpf::{EbpfProfiler, EbpfProfilerConfig};

let config = EbpfProfilerConfig::new()
    .with_sample_rate(99);
let mut profiler = EbpfProfiler::new(config)?;
profiler.start()?;
let profile = profiler.stop()?;
```

#### 新代码

```rust
use otlp::ebpf::{EbpfCpuProfiler, EbpfConfig, create_recommended_config};

let config = create_recommended_config("development");
let mut profiler = EbpfCpuProfiler::new(config)?;
profiler.start()?;
let profile = profiler.stop()?;
```

### 示例 2: 网络追踪

#### 旧代码

```rust
// 旧版本不支持专门的网络追踪
```

#### 新代码

```rust
use otlp::ebpf::{EbpfNetworkTracer, EbpfConfig, create_recommended_config};

let config = create_recommended_config("development")
    .with_network_tracing(true);
let mut tracer = EbpfNetworkTracer::new(config);
tracer.start()?;
let events = tracer.stop()?;
```

---

## 常见问题

### Q1: 如何迁移旧的配置？

**A**: 使用 `EbpfConfig::default()` 替代 `EbpfProfilerConfig::new()`，然后使用相同的方法链配置。

### Q2: 旧的 `EbpfProfiler` 在哪里？

**A**: 已拆分为多个专门的追踪器。如果是 CPU 性能分析，使用 `EbpfCpuProfiler`。

### Q3: 如何同时使用多个追踪器？

**A**: 创建多个追踪器实例，每个实例可以独立配置和运行。

```rust
let cpu_profiler = EbpfCpuProfiler::new(cpu_config)?;
let network_tracer = EbpfNetworkTracer::new(network_config);

// 可以并行运行
cpu_profiler.start()?;
network_tracer.start()?;
```

### Q4: 性能开销如何获取？

**A**: 对于 CPU 性能分析器，使用 `get_overhead()` 方法：

```rust
let overhead = profiler.get_overhead();
println!("CPU: {:.2}%, Memory: {} MB",
    overhead.cpu_percent,
    overhead.memory_bytes / 1024 / 1024);
```

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [API 参考](./EBPF_API_REFERENCE_2025.md)
- [更新日志](./EBPF_CHANGELOG_2025.md)

---

**状态**: 📚 迁移指南
**最后更新**: 2025年1月
