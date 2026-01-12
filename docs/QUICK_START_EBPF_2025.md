# eBPF 快速开始指南 2025

**创建日期**: 2025年1月
**状态**: 🚀 快速开始
**时间**: 5分钟

---

## 🎯 5分钟快速开始

### 1. 检查系统要求

```bash
# 检查内核版本 (需要 >= 5.8)
uname -r

# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux
```

### 2. 启用 eBPF Feature

在 `Cargo.toml` 中:

```toml
[dependencies]
otlp = { path = "../crates/otlp", features = ["ebpf"] }
```

### 3. 运行示例

```bash
# 运行完整示例
cargo run --example ebpf_complete --features ebpf

# 运行基础示例
cargo run --example ebpf_profiling_example --features ebpf
```

### 4. 基本代码

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};

let config = EbpfConfig::default();
let mut profiler = EbpfCpuProfiler::new(config);
profiler.start()?;
// ... 你的代码 ...
let profile = profiler.stop()?;
```

---

## ⚡ 常见问题

### 权限问题

```bash
sudo setcap cap_bpf+ep target/debug/your_binary
```

### 内核版本

```bash
# 需要 Linux 内核 >= 5.8
uname -r
```

---

## 📚 更多信息

- [完整使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [实施计划](../EBPF_IMPLEMENTATION_PLAN_2025.md)
- [示例代码](../examples/ebpf_complete_example.rs)

---

**状态**: 🚀 快速开始
**更新时间**: 2025年1月
