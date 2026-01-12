# eBPF API 参考 2025

**创建日期**: 2025年1月
**状态**: 📚 API 参考
**Rust 版本**: 1.92+

---

## 📋 目录

- [概述](#概述)
- [核心类型](#核心类型)
- [配置 API](#配置-api)
- [加载器 API](#加载器-api)
- [性能分析器 API](#性能分析器-api)
- [追踪器 API](#追踪器-api)
- [工具函数 API](#工具函数-api)
- [错误处理](#错误处理)

---

## 概述

本文档提供 eBPF 模块的完整 API 参考。

---

## 核心类型

### EbpfConfig

eBPF 配置结构体。

```rust
pub struct EbpfConfig {
    pub enable_cpu_profiling: bool,
    pub enable_network_tracing: bool,
    pub enable_syscall_tracing: bool,
    pub enable_memory_tracing: bool,
    pub sample_rate: u32,
    pub duration: Duration,
    pub max_samples: usize,
}
```

**方法**:

- `new() -> Self` - 创建新配置
- `with_sample_rate(rate: u32) -> Self` - 设置采样频率
- `with_duration(duration: Duration) -> Self` - 设置持续时间
- `with_cpu_profiling(enabled: bool) -> Self` - 启用/禁用 CPU 性能分析
- `with_network_tracing(enabled: bool) -> Self` - 启用/禁用网络追踪
- `with_syscall_tracing(enabled: bool) -> Self` - 启用/禁用系统调用追踪
- `with_memory_tracing(enabled: bool) -> Self` - 启用/禁用内存追踪
- `with_max_samples(max: usize) -> Self` - 设置最大采样数
- `validate() -> Result<()>` - 验证配置

### EbpfEvent

eBPF 事件结构体。

```rust
pub struct EbpfEvent {
    pub event_type: EbpfEventType,
    pub timestamp: Duration,
    pub pid: u32,
    pub tid: u32,
    pub data: Vec<u8>,
}
```

### EbpfEventType

eBPF 事件类型枚举。

```rust
pub enum EbpfEventType {
    Unknown,
    CpuSample,
    NetworkConnect,
    NetworkDisconnect,
    NetworkPacket,
    Syscall,
    MemoryAlloc,
    MemoryFree,
}
```

---

## 配置 API

### 创建配置

```rust
use otlp::ebpf::EbpfConfig;

// 使用默认配置
let config = EbpfConfig::default();

// 使用推荐配置
let config = create_recommended_config("production");
```

### 配置验证

```rust
use otlp::ebpf::{EbpfConfig, validate_config};

let config = EbpfConfig::default();
validate_config(&config)?;
```

---

## 加载器 API

### EbpfLoader

eBPF 程序加载器。

```rust
use otlp::ebpf::{EbpfLoader, EbpfConfig};

// 创建加载器
let loader = EbpfLoader::new(config);

// 检查系统支持
EbpfLoader::check_system_support()?;

// 加载程序
loader.load(program_bytes)?;
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新加载器
- `load(&mut self, program_bytes: &[u8]) -> Result<()>` - 加载 eBPF 程序
- `check_system_support() -> Result<()>` - 检查系统支持
- `config(&self) -> &EbpfConfig` - 获取配置

---

## 性能分析器 API

### EbpfCpuProfiler

CPU 性能分析器。

```rust
use otlp::ebpf::{EbpfCpuProfiler, EbpfConfig};

let config = EbpfConfig::default();
let mut profiler = EbpfCpuProfiler::new(config);

// 启动性能分析
profiler.start()?;

// 停止性能分析
let profile = profiler.stop()?;

// 获取性能开销
let overhead = profiler.get_overhead();
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新分析器
- `start(&mut self) -> Result<()>` - 启动性能分析
- `stop(&mut self) -> Result<PprofProfile>` - 停止性能分析
- `get_overhead(&self) -> OverheadMetrics` - 获取性能开销

---

## 追踪器 API

### EbpfNetworkTracer

网络追踪器。

```rust
use otlp::ebpf::{EbpfNetworkTracer, EbpfConfig};

let config = EbpfConfig::default();
let mut tracer = EbpfNetworkTracer::new(config);

// 启动追踪
tracer.start()?;

// 停止追踪
let events = tracer.stop()?;
```

### EbpfSyscallTracer

系统调用追踪器。

```rust
use otlp::ebpf::{EbpfSyscallTracer, EbpfConfig};

let config = EbpfConfig::default();
let mut tracer = EbpfSyscallTracer::new(config);

// 启动追踪
tracer.start()?;

// 停止追踪
let events = tracer.stop()?;
```

### EbpfMemoryTracer

内存追踪器。

```rust
use otlp::ebpf::{EbpfMemoryTracer, EbpfConfig};

let config = EbpfConfig::default();
let mut tracer = EbpfMemoryTracer::new(config);

// 启动追踪
tracer.start()?;

// 停止追踪
let events = tracer.stop()?;
```

---

## 工具函数 API

### 推荐配置

```rust
use otlp::ebpf::create_recommended_config;

// 根据环境创建推荐配置
let config = create_recommended_config("production");
let config = create_recommended_config("development");
let config = create_recommended_config("debug");
```

### 推荐采样频率

```rust
use otlp::ebpf::recommended_sample_rate;

let rate = recommended_sample_rate("production");  // 19
let rate = recommended_sample_rate("development");  // 99
```

### 推荐持续时间

```rust
use otlp::ebpf::recommended_duration;

let duration = recommended_duration("production");  // 5分钟
let duration = recommended_duration("development"); // 1分钟
```

---

## 错误处理

### EbpfError

eBPF 错误类型。

```rust
pub enum EbpfError {
    UnsupportedPlatform,
    InsufficientPermissions,
    IncompatibleKernel,
    LoadFailed(String),
    AttachFailed(String),
    MapOperationFailed(String),
    EventProcessingFailed(String),
    ConfigError(String),
}
```

**错误转换**:

- `EbpfError` 可以转换为 `OtlpError`
- 自动处理错误分类和上下文

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [架构设计文档](./EBPF_ARCHITECTURE_2025.md)
- [示例指南](./EBPF_EXAMPLES_GUIDE_2025.md)

---

**状态**: 📚 API 参考
**最后更新**: 2025年1月
