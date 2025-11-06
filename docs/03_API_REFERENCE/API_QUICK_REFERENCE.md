# 🚀 API快速参考卡片

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: API 快速参考 - 核心模块、常用代码片段和配置速查卡片。

---

## 📋 目录

- [🚀 API快速参考卡片](#-api快速参考卡片)
  - [📋 目录](#-目录)
  - [📋 核心模块速查](#-核心模块速查)
  - [⚡ 常用代码片段](#-常用代码片段)
    - [1. 创建OTLP客户端](#1-创建otlp客户端)
    - [2. CPU Profiling](#2-cpu-profiling)
    - [3. SIMD聚合](#3-simd聚合)
    - [4. Tracezip压缩](#4-tracezip压缩)
    - [5. HTTP语义约定](#5-http语义约定)
  - [🎯 按场景选择API](#-按场景选择api)
    - [性能问题排查](#性能问题排查)
    - [性能优化](#性能优化)
    - [标准化监控](#标准化监控)
  - [📊 性能参考](#-性能参考)
  - [🔗 完整文档链接](#-完整文档链接)

## 📋 核心模块速查

| 模块 | 用途 | 主要类型 | 文档 |
|------|------|---------|------|
| `profiling` | 性能分析 | `CpuProfiler`, `MemoryProfiler` | [详细](profiling_api.md) |
| `simd` | SIMD优化 | `Aggregator`, `BatchSerializer` | [详细](simd_api.md) |
| `compression` | 数据压缩 | `TraceCompressor` | [详细](compression_api.md) |
| `semantic_conventions` | 语义约定 | `HttpAttributesBuilder`, `DatabaseAttributesBuilder` | [详细](semantic_conventions_api.md) |
| `client` | OTLP客户端 | `OtlpClient`, `ClientBuilder` | [详细](README.md#-客户端-api) |

---

## ⚡ 常用代码片段

### 1. 创建OTLP客户端

```rust
use otlp::{OtlpClient, OtlpConfig};

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(10));

let client = OtlpClient::new(config).await?;
```

### 2. CPU Profiling

```rust
use otlp::profiling::{CpuProfiler, CpuProfilerConfig};

let mut profiler = CpuProfiler::new(CpuProfilerConfig::default());
profiler.start().await?;
// ... your code ...
profiler.stop().await?;
let profile = profiler.generate_profile().await?;
```

### 3. SIMD聚合

```rust
use otlp::simd::Aggregator;

let values = vec![1, 2, 3, 4, 5];
let sum = Aggregator::sum_i64(&values);
let avg = Aggregator::avg_f64(&values).unwrap();
```

### 4. Tracezip压缩

```rust
use otlp::compression::tracezip::TraceCompressor;

let mut compressor = TraceCompressor::default();
let compressed = compressor.compress(&spans)?;
let stats = compressor.stats();
```

### 5. HTTP语义约定

```rust
use otlp::semantic_conventions::http::*;

let attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Get)
    .url("https://api.example.com/users")
    .status_code(200)
    .build()?;
```

---

## 🎯 按场景选择API

### 性能问题排查

```rust
// 1. CPU热点分析
use otlp::profiling::CpuProfiler;
let mut profiler = CpuProfiler::new(config);
profiler.start().await?;

// 2. 内存分析
use otlp::profiling::MemoryProfiler;
let mut mem_profiler = MemoryProfiler::new(config);
```

### 性能优化

```rust
// 1. SIMD加速数据处理
use otlp::simd::Aggregator;
let result = Aggregator::sum_i64(&large_dataset);

// 2. 压缩减少传输
use otlp::compression::tracezip::TraceCompressor;
let compressed = compressor.compress(&spans)?;
```

### 标准化监控

```rust
// HTTP追踪
use otlp::semantic_conventions::http::*;
let http_attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Post)
    .url("https://api.example.com")
    .build()?;

// 数据库追踪
use otlp::semantic_conventions::database::*;
let db_attrs = DatabaseAttributesBuilder::new()
    .system(DatabaseSystem::PostgreSQL)
    .statement("SELECT * FROM users")
    .build()?;
```

---

## 📊 性能参考

| 操作 | 性能指标 | 说明 |
|------|---------|------|
| **CPU Profiling** | <1% overhead | 100Hz采样 |
| **SIMD聚合** | +40% throughput | vs标量实现 |
| **Tracezip压缩** | 70% ratio | 典型场景 |
| **批量序列化** | +50% speed | SIMD优化 |

---

## 🔗 完整文档链接

- [Profiling API完整文档](profiling_api.md) - 500+行
- [SIMD API完整文档](simd_api.md) - 650+行
- [Compression API完整文档](compression_api.md) - 600+行
- [Semantic Conventions完整文档](semantic_conventions_api.md) - 700+行
- [核心API参考](README.md) - 578行

---

**总API文档规模**: 3000+行
**更新频率**: 每个版本更新
**维护状态**: ✅ 活跃维护
