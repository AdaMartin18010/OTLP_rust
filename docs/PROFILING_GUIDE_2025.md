# 性能分析指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

性能分析模块 (`crates/otlp/src/profiling/`) 提供了完整的性能分析功能，包括 CPU 分析、内存分析、pprof 格式支持和 OTLP 导出。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::profiling::{CpuProfiler, CpuProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = CpuProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    profiler.start().await?;

    // 执行代码...

    profiler.stop().await?;
    let profile = profiler.generate_profile().await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### CpuProfiler

CPU 性能分析器。

**方法**:

- `new(config: CpuProfilerConfig) -> Self` - 创建分析器
- `start() -> Result<()>` - 启动分析
- `stop() -> Result<()>` - 停止分析
- `generate_profile() -> Result<PprofProfile>` - 生成 Profile

#### MemoryProfiler

内存性能分析器。

**方法**:

- `new(config: MemoryProfilerConfig) -> Self` - 创建分析器
- `start() -> Result<()>` - 启动分析
- `stop() -> Result<()>` - 停止分析
- `get_stats() -> MemoryProfilerStats` - 获取统计信息

#### PprofProfile

pprof 格式的 Profile 数据。

**字段**:

- `sample_types: Vec<ValueType>` - 样本类型
- `samples: Vec<Sample>` - 样本数据
- `locations: Vec<Location>` - 位置信息
- `functions: Vec<Function>` - 函数信息

---

## 💡 示例代码

### 示例 1: CPU 分析

```rust
use otlp::profiling::{CpuProfiler, CpuProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = CpuProfilerConfig {
        sample_rate: 99,  // 99 Hz
        duration: Duration::from_secs(30),
        ..Default::default()
    };

    let mut profiler = CpuProfiler::new(config);
    profiler.start().await?;

    // 执行 CPU 密集型任务
    for _ in 0..1000000 {
        let _ = (0..1000).sum::<i32>();
    }

    profiler.stop().await?;
    let profile = profiler.generate_profile().await?;

    println!("Profile 样本数: {}", profile.samples.len());
    Ok(())
}
```

### 示例 2: 内存分析

```rust
use otlp::profiling::{MemoryProfiler, MemoryProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = MemoryProfilerConfig::default();
    let mut profiler = MemoryProfiler::new(config);

    profiler.start().await?;

    // 执行内存分配操作
    let mut data = Vec::new();
    for i in 0..10000 {
        data.push(vec![0u8; 1024]);
    }

    profiler.stop().await?;
    let stats = profiler.get_stats();

    println!("总分配: {} bytes", stats.total_allocations);
    Ok(())
}
```

### 示例 3: 采样策略

```rust
use otlp::profiling::{ProbabilisticSampler, SamplingStrategy};

fn create_sampler() -> ProbabilisticSampler {
    ProbabilisticSampler::new(0.1)  // 10% 采样率
}
```

---

## 🎯 最佳实践

### 1. 采样频率

根据场景选择合适的采样频率：

```rust
// 生产环境：低采样频率
let config = CpuProfilerConfig {
    sample_rate: 19,  // 19 Hz
    ..Default::default()
};

// 开发环境：高采样频率
let config = CpuProfilerConfig {
    sample_rate: 99,  // 99 Hz
    ..Default::default()
};
```

### 2. 分析持续时间

控制分析持续时间以平衡性能和开销：

```rust
let config = CpuProfilerConfig {
    duration: Duration::from_secs(60),  // 1 分钟
    ..Default::default()
};
```

### 3. Profile 导出

将 Profile 导出到 OTLP：

```rust
use otlp::profiling::ProfileExporter;

let exporter = ProfileExporter::new(config)?;
exporter.export_profile(profile).await?;
```

---

## ⚠️ 注意事项

### 1. 性能开销

性能分析会带来一定的性能开销：

```rust
// 生产环境：使用较低的采样频率
let config = CpuProfilerConfig {
    sample_rate: 19,  // 降低开销
    ..Default::default()
};
```

### 2. 内存使用

长时间分析会占用较多内存：

```rust
// 定期停止和重启分析器
profiler.stop().await?;
// 处理数据...
profiler.start().await?;
```

---

## 📚 参考资源

### 相关文档

- [pprof 格式](https://github.com/google/pprof)
- [OpenTelemetry Profiling](https://opentelemetry.io/docs/specs/otel/profiles/)

### API 参考

- `CpuProfiler` - CPU 分析器
- `MemoryProfiler` - 内存分析器
- `PprofProfile` - pprof Profile
- `ProfileExporter` - Profile 导出器
- `SamplingStrategy` - 采样策略

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
