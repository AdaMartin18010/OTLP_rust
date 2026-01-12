# 数据压缩指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

数据压缩模块 (`crates/otlp/src/compression/`) 提供了 Tracezip 压缩算法，用于减少数据传输大小，同时保持完整的 OTLP 兼容性。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = CompressorConfig::default();
    let mut compressor = TraceCompressor::new(config);

    let compressed = compressor.compress(&spans)?;
    let stats = compressor.stats();

    println!("压缩率: {:.2}%", stats.compression_ratio * 100.0);
    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### TraceCompressor

Trace 数据压缩器。

**方法**:

- `new(config: CompressorConfig) -> Self` - 创建压缩器
- `compress(spans: &[Span]) -> Result<Vec<u8>>` - 压缩数据
- `decompress(data: &[u8]) -> Result<Vec<Span>>` - 解压数据
- `stats() -> CompressionStats` - 获取统计信息

#### CompressorConfig

压缩器配置。

**字段**:

- `enable_deduplication: bool` - 启用去重
- `enable_delta_encoding: bool` - 启用增量编码
- `enable_string_table: bool` - 启用字符串表

#### CompressionStats

压缩统计信息。

**字段**:

- `compression_ratio: f64` - 压缩率
- `original_size: usize` - 原始大小
- `compressed_size: usize` - 压缩后大小
- `deduplication_count: usize` - 去重数量

---

## 💡 示例代码

### 示例 1: 基本压缩

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

fn compress_traces(spans: &[Span]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let config = CompressorConfig::default();
    let mut compressor = TraceCompressor::new(config);

    let compressed = compressor.compress(spans)?;
    Ok(compressed)
}
```

### 示例 2: 解压缩

```rust
use otlp::compression::tracezip::TraceCompressor;

fn decompress_traces(data: &[u8]) -> Result<Vec<Span>, Box<dyn std::error::Error>> {
    let compressor = TraceCompressor::new(CompressorConfig::default());
    let spans = compressor.decompress(data)?;
    Ok(spans)
}
```

### 示例 3: 压缩统计

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

fn analyze_compression(spans: &[Span]) -> Result<(), Box<dyn std::error::Error>> {
    let config = CompressorConfig::default();
    let mut compressor = TraceCompressor::new(config);

    let _compressed = compressor.compress(spans)?;
    let stats = compressor.stats();

    println!("原始大小: {} bytes", stats.original_size);
    println!("压缩后大小: {} bytes", stats.compressed_size);
    println!("压缩率: {:.2}%", stats.compression_ratio * 100.0);
    println!("去重数量: {}", stats.deduplication_count);

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 批量压缩

对于多个 Span，使用批量压缩：

```rust
// ✅ 推荐：批量压缩
let compressed = compressor.compress(&all_spans)?;

// ❌ 不推荐：逐个压缩
for span in spans {
    compressor.compress(&[span])?;
}
```

### 2. 配置优化

根据数据特征调整配置：

```rust
let config = CompressorConfig {
    enable_deduplication: true,  // 启用去重
    enable_delta_encoding: true,  // 启用增量编码
    enable_string_table: true,  // 启用字符串表
};
```

### 3. 监控压缩率

定期监控压缩率以评估效果：

```rust
let stats = compressor.stats();
if stats.compression_ratio < 0.5 {
    // 压缩率低于 50%，可能需要调整配置
}
```

---

## ⚠️ 注意事项

### 1. 压缩开销

压缩会带来 CPU 开销：

```rust
// 对于小数据，可能不值得压缩
if spans.len() < 100 {
    // 直接发送，不压缩
} else {
    // 压缩后发送
    let compressed = compressor.compress(&spans)?;
}
```

### 2. 内存使用

压缩过程会占用内存：

```rust
// 对于大数据，分批压缩
for chunk in spans.chunks(1000) {
    let compressed = compressor.compress(chunk)?;
    // 发送压缩数据...
}
```

---

## 📚 参考资源

### 相关文档

- [Tracezip 规范](https://opentelemetry.io/docs/specs/otel/tracezip/)

### API 参考

- `TraceCompressor` - Trace 压缩器
- `CompressorConfig` - 压缩器配置
- `CompressionStats` - 压缩统计信息

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
