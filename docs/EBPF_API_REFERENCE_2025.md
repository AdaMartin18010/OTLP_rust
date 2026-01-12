# eBPF API 参考 2025

**创建日期**: 2025年1月
**状态**: 📚 API 参考
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF API 参考 2025](#ebpf-api-参考-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心类型](#核心类型)
    - [EbpfConfig](#ebpfconfig)
    - [EbpfEvent](#ebpfevent)
    - [EbpfEventType](#ebpfeventtype)
    - [EbpfOverheadMetrics](#ebpfoverheadmetrics)
  - [配置 API](#配置-api)
    - [创建配置](#创建配置)
    - [配置验证](#配置验证)
  - [加载器 API](#加载器-api)
    - [EbpfLoader](#ebpfloader)
  - [性能分析器 API](#性能分析器-api)
    - [EbpfCpuProfiler](#ebpfcpuprofiler)
  - [追踪器 API](#追踪器-api)
    - [EbpfNetworkTracer](#ebpfnetworktracer)
    - [EbpfSyscallTracer](#ebpfsyscalltracer)
    - [EbpfMemoryTracer](#ebpfmemorytracer)
  - [工具函数 API](#工具函数-api)
    - [推荐配置](#推荐配置)
    - [推荐采样频率](#推荐采样频率)
    - [推荐持续时间](#推荐持续时间)
    - [配置验证](#配置验证-1)
  - [OpenTelemetry 集成 API](#opentelemetry-集成-api)
    - [EbpfOtlpConverter](#ebpfotlpconverter)
  - [错误处理](#错误处理)
    - [EbpfError](#ebpferror)
  - [参考资源](#参考资源)

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
- `with_enable_cpu_profiling(enabled: bool) -> Self` - 启用/禁用 CPU 性能分析
- `with_enable_network_tracing(enabled: bool) -> Self` - 启用/禁用网络追踪
- `with_enable_syscall_tracing(enabled: bool) -> Self` - 启用/禁用系统调用追踪
- `with_enable_memory_tracing(enabled: bool) -> Self` - 启用/禁用内存追踪
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
    CpuSample,        // CPU 采样事件
    NetworkPacket,    // 网络包事件
    Syscall,          // 系统调用事件
    MemoryAlloc,      // 内存分配事件
    MemoryFree,       // 内存释放事件
}
```

### EbpfOverheadMetrics

eBPF 性能开销指标。

```rust
pub struct EbpfOverheadMetrics {
    pub cpu_percent: f64,        // CPU 开销百分比
    pub memory_bytes: usize,     // 内存开销 (字节)
    pub event_latency_us: u64,   // 事件处理延迟 (微秒)
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
let mut loader = EbpfLoader::new(config);

// 检查系统支持
EbpfLoader::check_system_support()?;

// 验证程序字节码
loader.validate_program(program_bytes)?;

// 加载程序
loader.load(program_bytes)?;

// 检查加载状态
let is_loaded = loader.is_loaded();

// 获取配置
let config = loader.config();

// 卸载程序
loader.unload()?;
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新加载器
- `load(&mut self, program_bytes: &[u8]) -> Result<()>` - 加载 eBPF 程序
- `validate_program(&self, program_bytes: &[u8]) -> Result<()>` - 验证程序字节码
- `check_system_support() -> Result<()>` - 检查系统支持
- `is_loaded(&self) -> bool` - 检查程序是否已加载
- `unload(&mut self) -> Result<()>` - 卸载程序
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

// 暂停性能分析
profiler.pause()?;

// 恢复性能分析
profiler.resume()?;

// 停止性能分析
let profile = profiler.stop()?;

// 获取性能开销
let overhead = profiler.get_overhead();

// 检查运行状态
let is_running = profiler.is_running();

// 获取配置
let config = profiler.config();
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新分析器
- `start(&mut self) -> Result<()>` - 启动性能分析
- `stop(&mut self) -> Result<PprofProfile>` - 停止性能分析
- `pause(&mut self) -> Result<()>` - 暂停性能分析
- `resume(&mut self) -> Result<()>` - 恢复性能分析
- `get_overhead(&self) -> EbpfOverheadMetrics` - 获取性能开销
- `is_running(&self) -> bool` - 检查是否正在运行
- `config(&self) -> &EbpfConfig` - 获取配置

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

// 获取统计信息
let stats = tracer.get_stats();
println!("Packets: {}, Bytes: {}", stats.packets_captured, stats.bytes_captured);

// 检查运行状态
let is_running = tracer.is_running();

// 获取配置
let config = tracer.config();

// 停止追踪
let events = tracer.stop()?;
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新追踪器
- `start(&mut self) -> Result<()>` - 启动网络追踪
- `stop(&mut self) -> Result<Vec<EbpfEvent>>` - 停止网络追踪
- `is_running(&self) -> bool` - 检查是否正在运行
- `config(&self) -> &EbpfConfig` - 获取配置
- `get_stats(&self) -> NetworkStats` - 获取网络统计信息

**NetworkStats 结构**:

```rust
pub struct NetworkStats {
    pub packets_captured: u64,
    pub bytes_captured: u64,
    pub tcp_connections: u64,
    pub udp_sessions: u64,
}
```

### EbpfSyscallTracer

系统调用追踪器。

```rust
use otlp::ebpf::{EbpfSyscallTracer, EbpfConfig};

let config = EbpfConfig::default();
let mut tracer = EbpfSyscallTracer::new(config);

// 启动追踪
tracer.start()?;

// 过滤特定系统调用
tracer.filter_syscall("open", true)?;
tracer.filter_syscall("read", false)?;

// 获取统计信息
let stats = tracer.get_stats();
println!("Syscalls traced: {}", stats.syscalls_traced);

// 检查运行状态
let is_running = tracer.is_running();

// 获取配置
let config = tracer.config();

// 停止追踪
let events = tracer.stop()?;
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新追踪器
- `start(&mut self) -> Result<()>` - 启动系统调用追踪
- `stop(&mut self) -> Result<Vec<EbpfEvent>>` - 停止系统调用追踪
- `is_running(&self) -> bool` - 检查是否正在运行
- `config(&self) -> &EbpfConfig` - 获取配置
- `get_stats(&self) -> SyscallStats` - 获取系统调用统计信息
- `filter_syscall(&mut self, syscall_name: &str, enabled: bool) -> Result<()>` - 过滤特定系统调用

**SyscallStats 结构**:

```rust
pub struct SyscallStats {
    pub syscalls_traced: u64,
    pub unique_syscalls: u64,
    pub errors: u64,
}
```

### EbpfMemoryTracer

内存追踪器。

```rust
use otlp::ebpf::{EbpfMemoryTracer, EbpfConfig};

let config = EbpfConfig::default();
let mut tracer = EbpfMemoryTracer::new(config);

// 启动追踪
tracer.start()?;

// 获取统计信息
let stats = tracer.get_stats();
println!("Allocations: {}, Frees: {}", stats.allocations, stats.frees);
println!("Total allocated: {} bytes", stats.total_allocated);

// 检查运行状态
let is_running = tracer.is_running();

// 获取配置
let config = tracer.config();

// 停止追踪
let events = tracer.stop()?;
```

**方法**:

- `new(config: EbpfConfig) -> Self` - 创建新追踪器
- `start(&mut self) -> Result<()>` - 启动内存追踪
- `stop(&mut self) -> Result<Vec<EbpfEvent>>` - 停止内存追踪
- `is_running(&self) -> bool` - 检查是否正在运行
- `config(&self) -> &EbpfConfig` - 获取配置
- `get_stats(&self) -> MemoryStats` - 获取内存统计信息

**MemoryStats 结构**:

```rust
pub struct MemoryStats {
    pub allocations: u64,
    pub frees: u64,
    pub total_allocated: u64,
    pub total_freed: u64,
    pub active_allocations: u64,
}
```

---

## 工具函数 API

### 推荐配置

```rust
use otlp::ebpf::create_recommended_config;

// 根据环境创建推荐配置
let config = create_recommended_config("production");   // 低采样率，长持续时间
let config = create_recommended_config("staging");      // 中等采样率
let config = create_recommended_config("development");  // 默认采样率
let config = create_recommended_config("debug");        // 高采样率，短持续时间
```

### 推荐采样频率

```rust
use otlp::ebpf::recommended_sample_rate;

let rate = recommended_sample_rate("production");   // 19 Hz
let rate = recommended_sample_rate("staging");      // 49 Hz
let rate = recommended_sample_rate("development");  // 99 Hz
let rate = recommended_sample_rate("debug");       // 199 Hz
```

### 推荐持续时间

```rust
use otlp::ebpf::recommended_duration;
use std::time::Duration;

let duration = recommended_duration("production");   // 300秒 (5分钟)
let duration = recommended_duration("staging");      // 120秒 (2分钟)
let duration = recommended_duration("development");  // 60秒 (1分钟)
let duration = recommended_duration("debug");        // 30秒
```

### 配置验证

```rust
use otlp::ebpf::{EbpfConfig, validate_config};

let config = EbpfConfig::default();
validate_config(&config)?;
```

---

## OpenTelemetry 集成 API

### EbpfOtlpConverter

eBPF 事件到 OpenTelemetry 的转换器。

```rust
use otlp::ebpf::{EbpfOtlpConverter, EbpfEvent};
use opentelemetry::trace::Tracer;
use opentelemetry::metrics::Meter;

// 创建转换器
let converter = EbpfOtlpConverter::new()
    .with_tracer(tracer)
    .with_meter(meter);

// 检查配置
if converter.is_configured() {
    // 转换单个事件到 Span
    let span = converter.convert_event_to_span(&event)?;

    // 转换单个事件到 Metric
    converter.convert_event_to_metric(&event)?;

    // 批量转换事件
    let (spans, metric_count) = converter.convert_events_batch(&events)?;

    // 转换 Profile 到 OTLP
    converter.convert_profile_to_otlp(&profile)?;
}
```

**方法**:

- `new() -> Self` - 创建新转换器
- `with_tracer(tracer: Tracer) -> Self` - 设置 Tracer
- `with_meter(meter: Meter) -> Self` - 设置 Meter
- `convert_event_to_span(&self, event: &EbpfEvent) -> Result<Option<Span>>` - 转换事件到 Span
- `convert_event_to_metric(&self, event: &EbpfEvent) -> Result<()>` - 转换事件到 Metric
- `convert_events_batch(&self, events: &[EbpfEvent]) -> Result<(Vec<Span>, u64)>` - 批量转换事件
- `convert_profile_to_otlp(&self, profile: &PprofProfile) -> Result<()>` - 转换 Profile 到 OTLP
- `is_configured(&self) -> bool` - 检查转换器是否已配置

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
