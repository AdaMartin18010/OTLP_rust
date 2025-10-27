# 🔬 Profiling API 参考

**模块**: `otlp::profiling`  
**版本**: 1.0  
**状态**: ✅ 生产就绪  
**最后更新**: 2025年10月26日

> **简介**: 完整的性能分析支持 - CPU profiling、内存profiling和多种采样策略，完全兼容 OpenTelemetry Profiling规范。

---

## 📋 目录

- [🔬 Profiling API 参考](#-profiling-api-参考)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
    - [核心特性](#核心特性)
  - [🚀 快速开始](#-快速开始)
  - [📚 核心类型](#-核心类型)
    - [CpuProfiler](#cpuprofiler)
    - [MemoryProfiler](#memoryprofiler)
    - [ProfileExporter](#profileexporter)
  - [🔧 配置选项](#-配置选项)
  - [💡 使用示例](#-使用示例)
    - [CPU Profiling](#cpu-profiling)
    - [Memory Profiling](#memory-profiling)
    - [Trace关联](#trace关联)
    - [采样策略](#采样策略)
  - [📊 采样策略详解](#-采样策略详解)
  - [🔗 Trace关联](#-trace关联)
  - [📤 导出Profile](#-导出profile)
  - [⚡ 性能考虑](#-性能考虑)
  - [🐛 错误处理](#-错误处理)
  - [📚 参考资源](#-参考资源)

---

## 📋 概述

Profiling 模块提供完整的性能分析支持，包括 CPU profiling、内存profiling和多种采样策略，完全兼容 [OpenTelemetry Profiling规范](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles)和pprof格式。

### 核心特性

- ✅ **CPU Profiling** - 采样调用栈识别CPU热点
- ✅ **Memory Profiling** - 追踪堆分配和内存使用
- ✅ **pprof Format** - 行业标准profile格式支持
- ✅ **OTLP Export** - 导出profiles到OTLP collectors
- ✅ **多种采样策略** - Always/Probabilistic/Rate-based/Adaptive
- ✅ **Trace关联** - 将profiles链接到分布式追踪

---

## 🚀 快速开始

```rust
use otlp::profiling::{CpuProfiler, CpuProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建CPU profiler
    let mut profiler = CpuProfiler::new(CpuProfilerConfig::default());
    
    // 启动profiling
    profiler.start().await?;
    
    // 运行你的代码
    do_some_work().await;
    
    // 停止profiling并生成profile
    profiler.stop().await?;
    let profile = profiler.generate_profile().await?;
    
    // 导出到OTLP collector
    let exporter = ProfileExporter::new(ProfileExporterConfig::default()).await?;
    exporter.export(&profile).await?;
    
    Ok(())
}
```

---

## 📚 核心类型

### CpuProfiler

CPU性能分析器，用于采样和记录CPU调用栈。

```rust
pub struct CpuProfiler {
    // 内部实现
}

impl CpuProfiler {
    /// 创建新的CPU profiler
    pub fn new(config: CpuProfilerConfig) -> Self;
    
    /// 启动profiling
    pub async fn start(&mut self) -> Result<()>;
    
    /// 停止profiling
    pub async fn stop(&mut self) -> Result<()>;
    
    /// 生成profile数据
    pub async fn generate_profile(&self) -> Result<PprofProfile>;
    
    /// 获取profiler统计信息
    pub fn stats(&self) -> CpuProfilerStats;
    
    /// 是否正在运行
    pub fn is_running(&self) -> bool;
}
```

**配置选项**:

```rust
#[derive(Debug, Clone)]
pub struct CpuProfilerConfig {
    /// 采样频率 (Hz)，默认 100Hz
    pub sampling_rate: u32,
    
    /// Profile持续时间，None表示手动停止
    pub duration: Option<Duration>,
    
    /// 最大栈深度，默认 64
    pub max_stack_depth: usize,
    
    /// 采样策略
    pub sampling_strategy: Box<dyn SamplingStrategy>,
    
    /// 是否包含线程名称
    pub include_thread_names: bool,
    
    /// 是否收集线程ID
    pub collect_thread_ids: bool,
}

impl Default for CpuProfilerConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 100,
            duration: None,
            max_stack_depth: 64,
            sampling_strategy: Box::new(AlwaysSample),
            include_thread_names: true,
            collect_thread_ids: true,
        }
    }
}
```

**统计信息**:

```rust
#[derive(Debug, Clone)]
pub struct CpuProfilerStats {
    /// 总采样数
    pub total_samples: u64,
    
    /// 丢失的采样数
    pub dropped_samples: u64,
    
    /// Profiling持续时间
    pub duration: Duration,
    
    /// 平均采样间隔
    pub avg_sample_interval: Duration,
    
    /// 唯一函数数量
    pub unique_functions: usize,
    
    /// 唯一位置数量
    pub unique_locations: usize,
}
```

---

### MemoryProfiler

内存性能分析器，追踪堆分配和内存使用模式。

```rust
pub struct MemoryProfiler {
    // 内部实现
}

impl MemoryProfiler {
    /// 创建新的内存profiler
    pub fn new(config: MemoryProfilerConfig) -> Self;
    
    /// 启动内存profiling
    pub async fn start(&mut self) -> Result<()>;
    
    /// 停止内存profiling
    pub async fn stop(&mut self) -> Result<()>;
    
    /// 生成内存profile
    pub async fn generate_profile(&self) -> Result<PprofProfile>;
    
    /// 获取系统内存信息
    pub fn get_system_memory_info() -> SystemMemoryInfo;
    
    /// 获取profiler统计信息
    pub fn stats(&self) -> MemoryProfilerStats;
}
```

**配置选项**:

```rust
#[derive(Debug, Clone)]
pub struct MemoryProfilerConfig {
    /// 采样率（每N次分配采样一次）
    pub sampling_rate: usize,
    
    /// 最小采样大小（字节）
    pub min_sample_size: usize,
    
    /// 最大栈深度
    pub max_stack_depth: usize,
    
    /// 是否追踪释放
    pub track_deallocations: bool,
    
    /// 是否收集系统内存信息
    pub collect_system_info: bool,
}

impl Default for MemoryProfilerConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 512 * 1024, // 每512KB采样一次
            min_sample_size: 1024,      // 最小1KB
            max_stack_depth: 64,
            track_deallocations: true,
            collect_system_info: true,
        }
    }
}
```

**系统内存信息**:

```rust
#[derive(Debug, Clone)]
pub struct SystemMemoryInfo {
    /// 总内存 (bytes)
    pub total_memory: u64,
    
    /// 可用内存 (bytes)
    pub available_memory: u64,
    
    /// 已用内存 (bytes)
    pub used_memory: u64,
    
    /// 缓存内存 (bytes)
    pub cached_memory: u64,
    
    /// 内存使用百分比
    pub memory_usage_percent: f64,
}
```

---

### ProfileExporter

Profile数据导出器，支持导出到OTLP collector。

```rust
pub struct ProfileExporter {
    // 内部实现
}

impl ProfileExporter {
    /// 创建新的exporter
    pub async fn new(config: ProfileExporterConfig) -> Result<Self>;
    
    /// 导出单个profile
    pub async fn export(&self, profile: &PprofProfile) -> Result<()>;
    
    /// 批量导出profiles
    pub async fn export_batch(&self, profiles: &[PprofProfile]) -> Result<()>;
    
    /// 关闭exporter
    pub async fn shutdown(&self) -> Result<()>;
}
```

**配置选项**:

```rust
#[derive(Debug, Clone)]
pub struct ProfileExporterConfig {
    /// OTLP端点
    pub endpoint: String,
    
    /// 超时时间
    pub timeout: Duration,
    
    /// 是否使用gRPC
    pub use_grpc: bool,
    
    /// 认证配置
    pub auth: Option<AuthConfig>,
    
    /// 批处理配置
    pub batch_config: Option<BatchConfig>,
}
```

---

## 🎯 采样策略

### SamplingStrategy Trait

所有采样策略必须实现的trait。

```rust
pub trait SamplingStrategy: Send + Sync {
    /// 判断是否应该采样当前事件
    fn should_sample(&self) -> bool;
    
    /// 重置采样器状态
    fn reset(&mut self);
    
    /// 获取采样统计信息
    fn stats(&self) -> SamplingStats;
}
```

### 内置采样策略

#### AlwaysSample

总是采样。

```rust
pub struct AlwaysSample;

impl SamplingStrategy for AlwaysSample {
    fn should_sample(&self) -> bool {
        true
    }
}
```

#### NeverSample

从不采样。

```rust
pub struct NeverSample;

impl SamplingStrategy for NeverSample {
    fn should_sample(&self) -> bool {
        false
    }
}
```

#### ProbabilisticSampler

基于概率的采样。

```rust
pub struct ProbabilisticSampler {
    probability: f64,  // 0.0 到 1.0
}

impl ProbabilisticSampler {
    /// 创建新的概率采样器
    /// probability: 采样概率，0.0-1.0之间
    pub fn new(probability: f64) -> Self;
}
```

**使用示例**:

```rust
// 10%概率采样
let sampler = ProbabilisticSampler::new(0.1);
let config = CpuProfilerConfig {
    sampling_strategy: Box::new(sampler),
    ..Default::default()
};
```

#### RateSampler

基于速率的采样。

```rust
pub struct RateSampler {
    rate_per_second: f64,
}

impl RateSampler {
    /// 创建新的速率采样器
    /// rate_per_second: 每秒采样次数
    pub fn new(rate_per_second: f64) -> Self;
}
```

**使用示例**:

```rust
// 每秒采样100次
let sampler = RateSampler::new(100.0);
```

#### AdaptiveSampler

自适应采样，根据系统负载动态调整。

```rust
pub struct AdaptiveSampler {
    target_rate: f64,
    min_probability: f64,
    max_probability: f64,
}

impl AdaptiveSampler {
    /// 创建新的自适应采样器
    pub fn new(
        target_rate: f64,
        min_probability: f64,
        max_probability: f64,
    ) -> Self;
    
    /// 更新采样概率
    pub fn update_probability(&mut self, current_rate: f64);
}
```

---

## 📊 数据模型

### PprofProfile

完整的pprof格式profile数据。

```rust
#[derive(Debug, Clone)]
pub struct PprofProfile {
    /// Profile类型
    pub profile_type: ProfileType,
    
    /// 样本数据
    pub samples: Vec<Sample>,
    
    /// 位置信息
    pub locations: Vec<Location>,
    
    /// 函数信息
    pub functions: Vec<Function>,
    
    /// 映射信息
    pub mappings: Vec<Mapping>,
    
    /// 字符串表
    pub string_table: Vec<String>,
    
    /// 时间信息
    pub time_nanos: i64,
    pub duration_nanos: i64,
    
    /// 周期和单位
    pub period_type: ValueType,
    pub period: i64,
    
    /// 样本类型
    pub sample_types: Vec<ValueType>,
}
```

### Sample

单个采样点数据。

```rust
#[derive(Debug, Clone)]
pub struct Sample {
    /// 位置ID列表（栈帧）
    pub location_ids: Vec<u64>,
    
    /// 样本值
    pub values: Vec<i64>,
    
    /// 标签
    pub labels: Vec<Label>,
}
```

### Location

代码位置信息。

```rust
#[derive(Debug, Clone)]
pub struct Location {
    /// 位置ID
    pub id: u64,
    
    /// 映射ID
    pub mapping_id: u64,
    
    /// 地址
    pub address: u64,
    
    /// 代码行信息
    pub lines: Vec<Line>,
}
```

### Function

函数信息。

```rust
#[derive(Debug, Clone)]
pub struct Function {
    /// 函数ID
    pub id: u64,
    
    /// 函数名称
    pub name: String,
    
    /// 系统名称
    pub system_name: String,
    
    /// 文件名
    pub filename: String,
    
    /// 起始行号
    pub start_line: i64,
}
```

---

## 🔗 Trace关联

### 链接Profile到Trace

```rust
use otlp::profiling::{link_profile_to_current_trace, generate_profile_id};

// 生成profile ID
let profile_id = generate_profile_id();

// 链接profile到当前trace context
link_profile_to_current_trace(&profile_id);

// 在profile数据中包含trace context
let mut profile = profiler.generate_profile().await?;
profile.add_label("trace.id", &current_trace_id);
profile.add_label("span.id", &current_span_id);
```

---

## 📝 完整示例

### CPU Profiling完整示例

```rust
use otlp::profiling::{
    CpuProfiler, CpuProfilerConfig,
    ProfileExporter, ProfileExporterConfig,
    ProbabilisticSampler,
};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 配置profiler
    let config = CpuProfilerConfig {
        sampling_rate: 100,  // 100Hz
        duration: Some(Duration::from_secs(30)),
        max_stack_depth: 64,
        sampling_strategy: Box::new(ProbabilisticSampler::new(0.1)), // 10%采样
        include_thread_names: true,
        collect_thread_ids: true,
    };
    
    // 2. 创建profiler
    let mut profiler = CpuProfiler::new(config);
    
    // 3. 启动profiling
    profiler.start().await?;
    println!("Profiling started");
    
    // 4. 运行负载
    for i in 0..1000 {
        expensive_operation(i).await;
    }
    
    // 5. 停止profiling
    profiler.stop().await?;
    let stats = profiler.stats();
    println!("Total samples: {}", stats.total_samples);
    println!("Dropped samples: {}", stats.dropped_samples);
    
    // 6. 生成profile
    let profile = profiler.generate_profile().await?;
    println!("Profile generated: {} samples", profile.samples.len());
    
    // 7. 导出到OTLP
    let exporter_config = ProfileExporterConfig {
        endpoint: "http://localhost:4317".to_string(),
        timeout: Duration::from_secs(10),
        use_grpc: true,
        auth: None,
        batch_config: None,
    };
    
    let exporter = ProfileExporter::new(exporter_config).await?;
    exporter.export(&profile).await?;
    println!("Profile exported successfully");
    
    // 8. 清理
    exporter.shutdown().await?;
    
    Ok(())
}

async fn expensive_operation(n: i32) {
    // 模拟CPU密集型操作
    let mut sum = 0;
    for i in 0..n * 1000 {
        sum += i;
    }
    tokio::time::sleep(Duration::from_millis(1)).await;
}
```

### Memory Profiling完整示例

```rust
use otlp::profiling::{
    MemoryProfiler, MemoryProfilerConfig,
    get_system_memory_info,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 获取系统内存信息
    let sys_info = get_system_memory_info();
    println!("Total memory: {} MB", sys_info.total_memory / 1024 / 1024);
    println!("Available memory: {} MB", sys_info.available_memory / 1024 / 1024);
    println!("Memory usage: {:.2}%", sys_info.memory_usage_percent);
    
    // 2. 配置memory profiler
    let config = MemoryProfilerConfig {
        sampling_rate: 512 * 1024,  // 每512KB采样
        min_sample_size: 1024,       // 最小1KB
        max_stack_depth: 64,
        track_deallocations: true,
        collect_system_info: true,
    };
    
    // 3. 创建profiler
    let mut profiler = MemoryProfiler::new(config);
    profiler.start().await?;
    
    // 4. 分配内存
    let mut data = Vec::new();
    for i in 0..1000 {
        data.push(vec![0u8; 1024 * 1024]); // 每次分配1MB
        if i % 100 == 0 {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
    
    // 5. 生成profile
    profiler.stop().await?;
    let profile = profiler.generate_profile().await?;
    let stats = profiler.stats();
    
    println!("Memory samples: {}", stats.total_samples);
    println!("Total allocated: {} MB", stats.total_allocated_bytes / 1024 / 1024);
    println!("Current allocated: {} MB", stats.current_allocated_bytes / 1024 / 1024);
    
    Ok(())
}
```

---

## ⚡ 性能考虑

### Profiling开销

| Profile类型 | CPU开销 | 内存开销 | 推荐场景 |
|------------|---------|----------|----------|
| **CPU (100Hz)** | <1% | ~10MB | 生产环境 |
| **CPU (1000Hz)** | ~5% | ~50MB | 开发/测试 |
| **Memory (512KB)** | <2% | ~20MB | 生产环境 |
| **Memory (64KB)** | ~10% | ~100MB | 开发/测试 |

### 优化建议

1. **采样频率**: 生产环境使用100Hz CPU采样
2. **内存采样**: 使用512KB-1MB的采样间隔
3. **栈深度**: 限制在64帧以内
4. **采样策略**: 使用概率采样(10-50%)减少开销
5. **批量导出**: 批量导出profiles减少网络开销

---

## 🔗 相关文档

- [Profile Signal实现指南](../05_IMPLEMENTATION/profile_signal_implementation_guide.md)
- [性能优化指南](../guides/performance-optimization.md)
- [OTLP标准对齐](../08_REFERENCE/otlp_standards_alignment.md)

---

**模块版本**: 0.5.0  
**最后更新**: 2025年10月26日  
**维护状态**: ✅ 活跃维护

