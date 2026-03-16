# eBPF 部署指南

**版本**: 1.0  
**最后更新**: 2025年1月  
**状态**: ✅ 完成

---

## 📋 目录

1. [系统要求](#系统要求)
2. [安装步骤](#安装步骤)
3. [配置说明](#配置说明)
4. [使用示例](#使用示例)
5. [故障排除](#故障排除)
6. [性能优化](#性能优化)
7. [安全考虑](#安全考虑)

---

## 系统要求

### 最低要求

- **操作系统**: Linux 5.8+ (支持 eBPF)
- **内核版本**: 5.8 或更高
- **权限**: CAP_BPF 或 root 权限
- **Rust 版本**: 1.92+
- **内存**: 至少 512MB 可用内存

### 推荐配置

- **操作系统**: Linux 5.15+ (更好的 eBPF 支持)
- **内核版本**: 5.15 或更高
- **BTF 支持**: 启用 (Better Type Format)
- **内存**: 2GB+ 可用内存
- **CPU**: 多核处理器（用于并行处理）

---

## 安装步骤

### 1. 检查系统支持

首先检查系统是否支持 eBPF：

```bash
# 检查内核版本
uname -r

# 检查 eBPF 支持
ls /sys/fs/bpf

# 检查 BTF 支持
ls /sys/kernel/btf/vmlinux
```

### 2. 安装依赖

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y \
    build-essential \
    clang \
    llvm \
    libbpf-dev \
    libelf-dev \
    zlib1g-dev

# CentOS/RHEL
sudo yum install -y \
    gcc \
    clang \
    llvm \
    kernel-devel \
    elfutils-libelf-devel \
    zlib-devel
```

### 3. 编译项目

```bash
# 克隆仓库
git clone <repository-url>
cd OTLP_rust

# 编译（启用 eBPF 功能）
cargo build --release --features ebpf

# 运行测试
cargo test --features ebpf
```

### 4. 设置权限

eBPF 程序需要特殊权限：

```bash
# 方法1: 使用 sudo（开发环境）
sudo ./target/release/your_app

# 方法2: 设置 CAP_BPF 权限（生产环境）
sudo setcap cap_bpf+ep ./target/release/your_app

# 方法3: 使用 systemd（推荐）
# 创建 systemd 服务文件
sudo nano /etc/systemd/system/otlp-ebpf.service
```

---

## 配置说明

### 基本配置

创建配置文件 `config.toml`:

```toml
[ebpf]
# 启用 CPU 性能分析
enable_cpu_profiling = true

# 采样频率 (Hz)
sample_rate = 99

# 采样持续时间 (秒)
duration = 60

# 最大采样数
max_samples = 100000

# 启用网络追踪
enable_network_tracing = false

# 启用系统调用追踪
enable_syscall_tracing = false

# 启用内存追踪
enable_memory_tracing = false
```

### 高级配置

```toml
[ebpf.performance]
# 事件缓冲区大小
buffer_size = 10000

# 批处理大小
batch_size = 100

# 刷新间隔 (毫秒)
flush_interval = 1000

[ebpf.filters]
# 过滤特定 PID
pid_filter = [1234, 5678]

# 过滤特定进程名
process_filter = ["nginx", "apache"]
```

---

## 使用示例

### 1. CPU 性能分析

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};

// 创建配置
let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_duration(Duration::from_secs(60));

// 创建性能分析器
let mut profiler = EbpfCpuProfiler::new(config);

// 启动性能分析
profiler.start()?;

// 等待一段时间...

// 停止并获取 profile
let profile = profiler.stop()?;

// 导出 profile
// ...
```

### 2. 网络追踪

```rust
use otlp::ebpf::{EbpfConfig, EbpfNetworkTracer};

let config = EbpfConfig::default()
    .with_network_tracing(true);

let mut tracer = EbpfNetworkTracer::new(config);
tracer.start()?;

// 等待收集数据...

let events = tracer.stop()?;
```

### 3. OpenTelemetry 集成

```rust
use otlp::ebpf::integration::EbpfOtlpConverter;
use opentelemetry::trace::Tracer;

// 创建转换器
let converter = EbpfOtlpConverter::new()
    .with_tracer(tracer);

// 转换事件
let span = converter.convert_event_to_span(&event)?;
```

---

## 故障排除

### 常见问题

#### 1. 权限不足

**错误**: `Operation not permitted`

**解决方案**:
```bash
# 检查权限
getcap ./target/release/your_app

# 设置权限
sudo setcap cap_bpf+ep ./target/release/your_app
```

#### 2. 内核版本过低

**错误**: `Kernel version too old`

**解决方案**:
- 升级内核到 5.8+
- 或使用兼容模式（功能受限）

#### 3. BTF 不可用

**警告**: `BTF not available`

**解决方案**:
```bash
# 检查 BTF
ls /sys/kernel/btf/vmlinux

# 如果不存在，需要重新编译内核并启用 BTF
```

#### 4. 内存不足

**错误**: `Out of memory`

**解决方案**:
- 减少 `max_samples` 配置
- 减少 `buffer_size` 配置
- 增加系统内存

### 调试技巧

```bash
# 启用详细日志
RUST_LOG=debug ./your_app

# 检查 eBPF 程序状态
sudo bpftool prog list

# 检查 eBPF maps
sudo bpftool map list

# 检查系统限制
ulimit -l
```

---

## 性能优化

### 1. 采样频率优化

- **低负载**: 99Hz (默认)
- **中等负载**: 199Hz
- **高负载**: 499Hz (注意性能开销)

### 2. 缓冲区优化

```rust
let config = EbpfConfig::default()
    .with_max_samples(50000)  // 减少内存使用
    .with_buffer_size(5000);   // 减少缓冲区大小
```

### 3. 批处理优化

```rust
// 使用批量处理减少开销
event_processor.process_batch(events)?;
```

### 4. 过滤优化

```rust
// 只追踪特定进程
let config = EbpfConfig::default()
    .with_pid_filter(vec![1234]);
```

---

## 安全考虑

### 1. 权限最小化

- 使用 `CAP_BPF` 而不是 root
- 限制文件系统访问
- 使用命名空间隔离

### 2. 资源限制

```bash
# 设置内存限制
ulimit -v 1048576  # 1GB

# 设置 CPU 限制
cpulimit -l 50 ./your_app
```

### 3. 数据安全

- 加密敏感数据
- 限制数据保留时间
- 遵守隐私法规

### 4. 监控和告警

```rust
// 监控性能开销
let overhead = profiler.get_overhead();
if overhead.cpu_percent > 10.0 {
    // 触发告警
}
```

---

## 部署检查清单

- [ ] 系统支持 eBPF (内核 5.8+)
- [ ] 已安装所有依赖
- [ ] 已设置适当权限
- [ ] 配置文件已正确设置
- [ ] 已测试基本功能
- [ ] 已设置监控和告警
- [ ] 已配置日志记录
- [ ] 已设置资源限制
- [ ] 已测试故障恢复
- [ ] 已准备回滚方案

---

## 参考资源

- [eBPF 官方文档](https://ebpf.io/)
- [OpenTelemetry eBPF 规范](https://opentelemetry.io/docs/specs/otel/ebpf/)
- [项目文档](../README.md)
- [API 参考](../crates/otlp/API_REFERENCE.md)

---

**最后更新**: 2025年1月  
**维护者**: OTLP Rust 团队
