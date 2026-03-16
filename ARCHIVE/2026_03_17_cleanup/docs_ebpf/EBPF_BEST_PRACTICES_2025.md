# eBPF 最佳实践指南 2025

**创建日期**: 2025年1月
**状态**: 📚 最佳实践指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 最佳实践指南 2025](#ebpf-最佳实践指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [配置最佳实践](#配置最佳实践)
    - [1. 采样频率选择](#1-采样频率选择)
    - [2. 功能启用策略](#2-功能启用策略)
    - [3. 配置验证](#3-配置验证)
  - [性能优化](#性能优化)
    - [1. 采样频率优化](#1-采样频率优化)
    - [2. 内存管理](#2-内存管理)
    - [3. 批处理](#3-批处理)
  - [安全建议](#安全建议)
    - [1. 权限管理](#1-权限管理)
    - [2. 内核版本检查](#2-内核版本检查)
    - [3. 错误处理](#3-错误处理)
  - [故障排查](#故障排查)
    - [1. 权限问题](#1-权限问题)
    - [2. 内核版本问题](#2-内核版本问题)
    - [3. BTF 支持问题](#3-btf-支持问题)
    - [4. 性能开销过高](#4-性能开销过高)
  - [生产部署](#生产部署)
    - [1. 部署检查清单](#1-部署检查清单)
    - [2. 监控指标](#2-监控指标)
    - [3. 日志记录](#3-日志记录)
  - [参考资源](#参考资源)

---

## 概述

本指南提供 eBPF 功能的最佳实践，帮助开发者在不同环境中高效、安全地使用 eBPF 功能。

---

## 配置最佳实践

### 1. 采样频率选择

根据环境选择合适的采样频率：

```rust
use otlp::ebpf::{create_recommended_config, recommended_sample_rate};

// 生产环境：低采样率，降低开销
let prod_config = create_recommended_config("production");
// sample_rate: 19Hz

// 开发环境：默认采样率
let dev_config = create_recommended_config("development");
// sample_rate: 99Hz

// 调试模式：高采样率，获得更详细的数据
let debug_config = create_recommended_config("debug");
// sample_rate: 199Hz
```

### 2. 功能启用策略

```rust
use otlp::ebpf::EbpfConfig;

// 生产环境：只启用 CPU 性能分析
let prod_config = EbpfConfig::default()
    .with_network_tracing(false)
    .with_syscall_tracing(false)
    .with_memory_tracing(false);

// 开发环境：启用所有功能
let dev_config = EbpfConfig::default()
    .with_network_tracing(true)
    .with_syscall_tracing(true)
    .with_memory_tracing(true);
```

### 3. 配置验证

```rust
use otlp::ebpf::EbpfConfig;

let config = EbpfConfig::default()
    .with_sample_rate(99);

// 验证配置
if let Err(e) = config.validate() {
    eprintln!("配置错误: {}", e);
    return;
}
```

---

## 性能优化

### 1. 采样频率优化

| 环境 | 推荐采样频率 | CPU 开销 | 精度 |
|------|-------------|---------|------|
| 生产环境 | 19-49 Hz | <0.5% | 中等 |
| 预发布环境 | 49-99 Hz | <1% | 高 |
| 开发环境 | 99 Hz | <1% | 高 |
| 调试模式 | 99-199 Hz | <2% | 最高 |

### 2. 内存管理

```rust
// 限制最大采样数，避免内存溢出
let config = EbpfConfig::default()
    .with_max_samples(100_000);  // 限制为 10万 个采样

// 定期清理采样数据
// TODO: 实现定期清理逻辑
```

### 3. 批处理

```rust
// 批量处理事件，减少开销
let mut events = Vec::new();
// ... 收集事件 ...
for event in events {
    // 批量处理
}
```

---

## 安全建议

### 1. 权限管理

```bash
# 使用 setcap 授予最小权限（推荐）
sudo setcap cap_bpf+ep /path/to/binary

# 避免使用 root（不推荐用于生产）
# sudo ./your_binary
```

### 2. 内核版本检查

```rust
use otlp::ebpf::EbpfLoader;

// 启动前检查系统支持
if let Err(e) = EbpfLoader::check_system_support() {
    eprintln!("系统不支持 eBPF: {}", e);
    return;
}
```

### 3. 错误处理

```rust
use otlp::ebpf::{EbpfCpuProfiler, EbpfConfig};

match profiler.start() {
    Ok(()) => {
        // 成功启动
    }
    Err(e) => {
        // 处理错误（权限不足、内核不支持等）
        eprintln!("启动失败: {}", e);
        // 使用 fallback 方案
    }
}
```

---

## 故障排查

### 1. 权限问题

**症状**: `权限不足: 需要 CAP_BPF 权限或 root`

**解决**:

```bash
# 授予权限
sudo setcap cap_bpf+ep /path/to/binary

# 验证权限
getcap /path/to/binary
```

### 2. 内核版本问题

**症状**: `内核版本不兼容: 需要 Linux 内核 >= 5.8`

**解决**:

```bash
# 检查内核版本
uname -r

# 需要升级内核到 5.8+ 或 5.15+ (推荐)
```

### 3. BTF 支持问题

**症状**: BTF 不支持

**解决**:

```bash
# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux

# 如果不存在，需要升级内核或启用 BTF
```

### 4. 性能开销过高

**症状**: CPU 开销 >1%

**解决**:

```rust
// 降低采样频率
let config = EbpfConfig::default()
    .with_sample_rate(19);  // 从 99Hz 降低到 19Hz

// 禁用不必要的功能
let config = EbpfConfig::default()
    .with_network_tracing(false)
    .with_syscall_tracing(false);
```

---

## 生产部署

### 1. 部署检查清单

- [ ] 内核版本 >= 5.8 (推荐 5.15+)
- [ ] BTF 支持已启用
- [ ] CAP_BPF 权限已授予
- [ ] 采样频率已优化（生产环境 <50Hz）
- [ ] 配置已验证
- [ ] 错误处理已实现
- [ ] 监控和告警已配置

### 2. 监控指标

```rust
// 监控性能开销
let overhead = profiler.get_overhead();
if overhead.cpu_percent > 1.0 {
    // 告警：CPU 开销过高
}

if overhead.memory_bytes > 50 * 1024 * 1024 {
    // 告警：内存开销过高
}
```

### 3. 日志记录

```rust
use tracing::{info, warn, error};

// 记录启动信息
info!("启动 eBPF 性能分析，采样频率: {}Hz", config.sample_rate);

// 记录警告
if overhead.cpu_percent > 1.0 {
    warn!("CPU 开销过高: {:.2}%", overhead.cpu_percent);
}

// 记录错误
if let Err(e) = profiler.start() {
    error!("启动失败: {}", e);
}
```

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [快速开始](./QUICK_START_EBPF_2025.md)
- [集成指南](./EBPF_INTEGRATION_GUIDE_2025.md)
- [实施计划](../EBPF_IMPLEMENTATION_PLAN_2025.md)

---

**状态**: 📚 最佳实践指南
**最后更新**: 2025年1月
