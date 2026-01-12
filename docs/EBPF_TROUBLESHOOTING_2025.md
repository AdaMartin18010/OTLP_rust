# eBPF 故障排查指南 2025

**创建日期**: 2025年1月
**状态**: 📚 故障排查指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [常见问题](#常见问题)
- [错误代码](#错误代码)
- [诊断步骤](#诊断步骤)
- [解决方案](#解决方案)
- [联系支持](#联系支持)

---

## 常见问题

### 1. 权限问题

#### 错误信息
```
权限不足: 需要 CAP_BPF 权限或 root
```

#### 诊断步骤

1. 检查当前用户权限
```bash
whoami
id
```

2. 检查文件权限
```bash
ls -l /path/to/binary
getcap /path/to/binary
```

3. 检查内核能力
```bash
cat /proc/sys/kernel/cap_last_cap
```

#### 解决方案

**方案 1: 使用 setcap（推荐）**
```bash
sudo setcap cap_bpf+ep /path/to/binary
getcap /path/to/binary  # 验证
```

**方案 2: 使用 sudo（不推荐用于生产）**
```bash
sudo ./your_binary
```

**方案 3: 检查 SELinux/AppArmor**
```bash
# SELinux
getenforce
# AppArmor
aa-status
```

---

### 2. 内核版本不兼容

#### 错误信息
```
内核版本不兼容: 需要 Linux 内核 >= 5.8
```

#### 诊断步骤

1. 检查内核版本
```bash
uname -r
cat /proc/version
```

2. 检查 BTF 支持
```bash
ls /sys/kernel/btf/vmlinux
```

3. 检查 eBPF 支持
```bash
ls /sys/fs/bpf/
```

#### 解决方案

**方案 1: 升级内核（推荐）**
```bash
# Ubuntu/Debian
sudo apt update
sudo apt install linux-generic-hwe-22.04

# CentOS/RHEL
sudo yum update kernel

# 重启后检查
uname -r
```

**方案 2: 使用兼容模式**
- 降低功能要求
- 使用 fallback 实现

---

### 3. BTF 不支持

#### 错误信息
```
BTF 不支持
```

#### 诊断步骤

1. 检查 BTF 文件
```bash
ls -lh /sys/kernel/btf/vmlinux
```

2. 检查内核配置
```bash
zcat /proc/config.gz | grep BTF
# 或
cat /boot/config-$(uname -r) | grep BTF
```

#### 解决方案

**方案 1: 升级内核（推荐）**
- 内核 5.8+ 默认支持 BTF

**方案 2: 重新编译内核**
```bash
# 启用 CONFIG_DEBUG_INFO_BTF
make menuconfig
# 编译并安装内核
```

---

### 4. 程序加载失败

#### 错误信息
```
eBPF 程序加载失败: ...
```

#### 诊断步骤

1. 检查程序字节码
```rust
// 验证程序字节码不为空
assert!(!program_bytes.is_empty());
```

2. 检查验证器日志
```bash
# 查看内核日志
dmesg | tail -20
journalctl -k | tail -20
```

3. 检查内存限制
```bash
ulimit -a
```

#### 解决方案

**方案 1: 检查程序字节码**
- 确保程序字节码有效
- 验证程序大小

**方案 2: 检查内核日志**
```bash
# 查看详细错误信息
dmesg | grep -i bpf
```

**方案 3: 增加内存限制**
```bash
ulimit -m unlimited
```

---

### 5. 性能开销过高

#### 症状
- CPU 使用率 >1%
- 内存使用 >50MB
- 应用延迟增加

#### 诊断步骤

1. 检查当前开销
```rust
let overhead = profiler.get_overhead();
println!("CPU: {:.2}%, Memory: {} MB",
    overhead.cpu_percent,
    overhead.memory_bytes / 1024 / 1024
);
```

2. 分析采样频率
```rust
println!("采样频率: {} Hz", config.sample_rate);
```

3. 检查启用的功能
```rust
println!("CPU分析: {}", config.enable_cpu_profiling);
println!("网络追踪: {}", config.enable_network_tracing);
println!("系统调用追踪: {}", config.enable_syscall_tracing);
```

#### 解决方案

**方案 1: 降低采样频率**
```rust
let config = EbpfConfig::default()
    .with_sample_rate(19);  // 降低到 19Hz
```

**方案 2: 禁用不必要的功能**
```rust
let config = EbpfConfig::default()
    .with_network_tracing(false)
    .with_syscall_tracing(false)
    .with_memory_tracing(false);
```

**方案 3: 限制最大采样数**
```rust
let config = EbpfConfig::default()
    .with_max_samples(10_000);  // 限制采样数
```

---

## 错误代码

### EbpfError

| 错误类型 | 原因 | 解决方案 |
|---------|------|---------|
| `UnsupportedPlatform` | 非 Linux 平台 | 使用 Linux 系统 |
| `InsufficientPermissions` | 权限不足 | 授予 CAP_BPF 权限 |
| `IncompatibleKernel` | 内核版本不兼容 | 升级内核到 5.8+ |
| `LoadFailed` | 程序加载失败 | 检查程序字节码和内核日志 |
| `AttachFailed` | 探针附加失败 | 检查函数名和内核日志 |
| `MapOperationFailed` | Maps 操作失败 | 检查 Map 配置 |
| `EventProcessingFailed` | 事件处理失败 | 检查事件数据格式 |
| `ConfigError` | 配置错误 | 验证配置参数 |

---

## 诊断步骤

### 完整诊断流程

1. **检查系统要求**
   ```bash
   uname -r  # 内核版本
   ls /sys/kernel/btf/vmlinux  # BTF 支持
   getcap /path/to/binary  # 权限
   ```

2. **检查配置**
   ```rust
   config.validate()?;
   ```

3. **检查日志**
   ```bash
   dmesg | tail -50
   journalctl -k | tail -50
   ```

4. **运行测试**
   ```bash
   cargo test --package otlp --lib ebpf
   ```

5. **验证功能**
   ```bash
   cargo run --example ebpf_complete --features ebpf
   ```

---

## 解决方案

### 快速修复

```bash
# 1. 授予权限
sudo setcap cap_bpf+ep /path/to/binary

# 2. 验证系统支持
cargo run --example ebpf_complete --features ebpf

# 3. 检查内核日志
dmesg | grep -i bpf
```

### 详细排查

1. 查看文档
   - [使用指南](./EBPF_USAGE_GUIDE_2025.md)
   - [最佳实践](./EBPF_BEST_PRACTICES_2025.md)

2. 运行诊断脚本
   ```bash
   # TODO: 创建诊断脚本
   ```

3. 收集系统信息
   ```bash
   uname -a
   cat /proc/version
   cat /proc/cpuinfo | head -5
   free -h
   ```

---

## 联系支持

### 获取帮助

1. **查看文档**
   - [使用指南](./EBPF_USAGE_GUIDE_2025.md)
   - [最佳实践](./EBPF_BEST_PRACTICES_2025.md)
   - [集成指南](./EBPF_INTEGRATION_GUIDE_2025.md)

2. **检查示例**
   - `examples/ebpf_complete_example.rs`
   - `examples/ebpf_profiling_example.rs`

3. **提交 Issue**
   - 包含错误信息
   - 包含系统信息
   - 包含复现步骤

---

**状态**: 📚 故障排查指南
**最后更新**: 2025年1月
