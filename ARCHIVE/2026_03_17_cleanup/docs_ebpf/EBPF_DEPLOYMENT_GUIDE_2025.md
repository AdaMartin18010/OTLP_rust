# eBPF 部署指南 2025

**创建日期**: 2025年1月
**状态**: 📚 部署指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 部署指南 2025](#ebpf-部署指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [系统要求](#系统要求)
    - [硬件要求](#硬件要求)
    - [软件要求](#软件要求)
    - [内核特性](#内核特性)
  - [安装步骤](#安装步骤)
    - [1. 检查系统支持](#1-检查系统支持)
    - [2. 安装依赖](#2-安装依赖)
    - [3. 编译项目](#3-编译项目)
    - [4. 授予权限](#4-授予权限)
  - [配置说明](#配置说明)
    - [环境变量](#环境变量)
    - [配置文件](#配置文件)
  - [部署方式](#部署方式)
    - [方式 1: 二进制部署](#方式-1-二进制部署)
    - [方式 2: Docker 部署](#方式-2-docker-部署)
    - [方式 3: Kubernetes 部署](#方式-3-kubernetes-部署)
  - [监控和维护](#监控和维护)
    - [性能监控](#性能监控)
    - [日志监控](#日志监控)
    - [健康检查](#健康检查)
  - [故障排查](#故障排查)
    - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

本文档提供 eBPF 功能的完整部署指南，包括系统要求、安装步骤、配置说明和部署方式。

---

## 系统要求

### 硬件要求

- **CPU**: x86_64 或 ARM64
- **内存**: 至少 512MB 可用内存
- **存储**: 至少 100MB 可用空间

### 软件要求

- **操作系统**: Linux
- **内核版本**: >= 5.8 (推荐 5.15+)
- **Rust 版本**: 1.92+
- **权限**: CAP_BPF 或 root

### 内核特性

- **BTF (BPF Type Format)**: 需要支持
- **eBPF**: 需要支持
- **perf_events**: CPU 性能分析需要

---

## 安装步骤

### 1. 检查系统支持

```bash
# 检查内核版本
uname -r

# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux

# 检查 eBPF 支持
ls /sys/fs/bpf/
```

### 2. 安装依赖

```bash
# 安装 Rust (如果未安装)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装构建工具
sudo apt-get update
sudo apt-get install -y build-essential clang llvm libclang-dev
```

### 3. 编译项目

```bash
# 克隆项目
git clone <repository-url>
cd OTLP_rust

# 编译（启用 eBPF feature）
cargo build --release --features ebpf
```

### 4. 授予权限

```bash
# 使用 setcap 授予权限（推荐）
sudo setcap cap_bpf+ep target/release/your_binary

# 验证权限
getcap target/release/your_binary
```

---

## 配置说明

### 环境变量

```bash
# 设置环境（影响推荐配置）
export ENV=production  # 或 development, staging, debug

# 设置采样频率（可选）
export EBPF_SAMPLE_RATE=99

# 设置最大采样数（可选）
export EBPF_MAX_SAMPLES=100000
```

### 配置文件

```toml
# config.toml
[ebpf]
sample_rate = 99
enable_cpu_profiling = true
enable_network_tracing = false
enable_syscall_tracing = false
enable_memory_tracing = false
max_samples = 100000
duration_seconds = 60
```

---

## 部署方式

### 方式 1: 二进制部署

```bash
# 1. 编译
cargo build --release --features ebpf

# 2. 复制二进制文件
cp target/release/your_binary /usr/local/bin/

# 3. 授予权限
sudo setcap cap_bpf+ep /usr/local/bin/your_binary

# 4. 运行
/usr/local/bin/your_binary
```

### 方式 2: Docker 部署

```dockerfile
FROM rust:1.92 as builder
WORKDIR /app
COPY . .
RUN cargo build --release --features ebpf

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y \
    libc6 \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/your_binary /usr/local/bin/
# 注意: Docker 容器需要 --privileged 或 --cap-add=BPF
CMD ["/usr/local/bin/your_binary"]
```

```bash
# 运行 Docker 容器
docker run --privileged your_image
# 或
docker run --cap-add=BPF your_image
```

### 方式 3: Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-ebpf
spec:
  replicas: 1
  template:
    spec:
      containers:
      - name: otlp-ebpf
        image: your_image:latest
        securityContext:
          capabilities:
            add:
            - BPF
        env:
        - name: ENV
          value: "production"
```

---

## 监控和维护

### 性能监控

```rust
use otlp::ebpf::EbpfCpuProfiler;

let overhead = profiler.get_overhead();
if overhead.cpu_percent > 1.0 {
    // 告警: CPU 开销过高
}
```

### 日志监控

```bash
# 查看日志
journalctl -u your_service -f

# 查看内核日志
dmesg | grep -i bpf
```

### 健康检查

```bash
# 检查进程状态
ps aux | grep your_binary

# 检查权限
getcap /path/to/binary

# 检查系统支持
ls /sys/kernel/btf/vmlinux
```

---

## 故障排查

### 常见问题

1. **权限不足**
   - 错误: `权限不足: 需要 CAP_BPF 权限或 root`
   - 解决: `sudo setcap cap_bpf+ep /path/to/binary`

2. **内核版本不兼容**
   - 错误: `内核版本不兼容: 需要 Linux 内核 >= 5.8`
   - 解决: 升级内核到 5.8+ 或 5.15+

3. **BTF 不支持**
   - 错误: `BTF 不支持`
   - 解决: 升级内核或启用 BTF

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [最佳实践](./EBPF_BEST_PRACTICES_2025.md)
- [故障排查指南](./EBPF_TROUBLESHOOTING_2025.md)

---

**状态**: 📚 部署指南
**最后更新**: 2025年1月
