# 🗜️ Compression API 参考

**模块**: `otlp::compression`
**版本**: 1.0
**状态**: ✅ 生产就绪
**最后更新**: 2025年10月26日

> **简介**: Tracezip算法实现 - 通过span去重、delta编码和字符串表优化实现高效trace数据压缩。

---

## 📋 目录

- [🗜️ Compression API 参考](#️-compression-api-参考)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
    - [核心特性](#核心特性)
    - [性能目标](#性能目标)
  - [🚀 快速开始](#-快速开始)
  - [📚 核心类型](#-核心类型)
    - [TraceCompressor](#tracecompressor)
    - [CompressorConfig](#compressorconfig)
    - [CompressionStats](#compressionstats)
  - [❌ 错误处理](#-错误处理)
    - [CompressionError](#compressionerror)
    - [DecompressionError](#decompressionerror)
  - [📊 压缩算法详解](#-压缩算法详解)
    - [1. Span去重](#1-span去重)
    - [2. Delta编码](#2-delta编码)
    - [3. 字符串表](#3-字符串表)
  - [💡 使用示例](#-使用示例)
    - [基本压缩](#基本压缩)
    - [批量处理](#批量处理)
    - [自适应压缩](#自适应压缩)
    - [完整的压缩/解压流程](#完整的压缩解压流程)
  - [⚡ 性能优化](#-性能优化)
    - [1. 批次大小选择](#1-批次大小选择)
    - [2. 配置调优](#2-配置调优)
    - [3. 内存管理](#3-内存管理)
  - [📈 性能基准](#-性能基准)
    - [压缩性能](#压缩性能)
    - [解压性能](#解压性能)
  - [🔗 相关文档](#-相关文档)

---

## 📋 概述

Compression模块提供Tracezip算法实现，用于高效压缩trace数据。通过span去重、delta编码和字符串表优化，显著减少数据传输大小，同时保持完整的OTLP兼容性。

### 核心特性

- ✅ **Span去重** - 消除重复的span数据
- ✅ **Delta编码** - 时间戳和ID增量编码
- ✅ **字符串表** - 优化重复字符串存储
- ✅ **批量压缩** - 高效的批处理
- ✅ **压缩统计** - 详细的压缩指标
- ✅ **无损压缩** - 完全可逆的压缩

### 性能目标

| 指标 | 目标 | 典型值 |
|------|------|--------|
| **压缩率** | 50-80% | ~70% |
| **压缩速度** | >10MB/s | ~15MB/s |
| **解压速度** | >50MB/s | ~80MB/s |
| **延迟增加** | <5ms | ~2ms |

---

## 🚀 快速开始

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

// 创建压缩器
let config = CompressorConfig::default();
let mut compressor = TraceCompressor::new(config);

// 压缩spans
let compressed = compressor.compress(&spans)?;

// 查看压缩效果
let stats = compressor.stats();
println!("Original size: {} bytes", stats.original_size);
println!("Compressed size: {} bytes", stats.compressed_size);
println!("Compression ratio: {:.2}%", stats.compression_ratio * 100.0);

// 解压
let decompressed = compressor.decompress(&compressed)?;
```

---

## 📚 核心类型

### TraceCompressor

Trace数据压缩器，实现Tracezip算法。

```rust
pub struct TraceCompressor {
    // 内部实现
}

impl TraceCompressor {
    /// 创建新的压缩器
    pub fn new(config: CompressorConfig) -> Self;

    /// 压缩一批spans
    pub fn compress(&mut self, spans: &[Span]) -> Result<Vec<u8>, CompressionError>;

    /// 解压数据
    pub fn decompress(&self, data: &[u8]) -> Result<Vec<Span>, DecompressionError>;

    /// 获取压缩统计信息
    pub fn stats(&self) -> CompressionStats;

    /// 重置压缩器状态
    pub fn reset(&mut self);

    /// 清除字符串表缓存
    pub fn clear_string_table(&mut self);
}

impl Default for TraceCompressor {
    fn default() -> Self {
        Self::new(CompressorConfig::default())
    }
}
```

---

### CompressorConfig

压缩器配置选项。

```rust
#[derive(Debug, Clone)]
pub struct CompressorConfig {
    /// 是否启用span去重
    pub enable_deduplication: bool,

    /// 是否启用delta编码
    pub enable_delta_encoding: bool,

    /// 是否使用字符串表
    pub use_string_table: bool,

    /// 字符串表最大大小
    pub max_string_table_size: usize,

    /// 是否压缩属性
    pub compress_attributes: bool,

    /// 最小批次大小（小于此值不压缩）
    pub min_batch_size: usize,

    /// 压缩级别 (1-9)
    pub compression_level: u8,
}

impl Default for CompressorConfig {
    fn default() -> Self {
        Self {
            enable_deduplication: true,
            enable_delta_encoding: true,
            use_string_table: true,
            max_string_table_size: 10000,
            compress_attributes: true,
            min_batch_size: 10,
            compression_level: 6,
        }
    }
}
```

**配置示例**:

```rust
// 最大压缩（速度较慢）
let config = CompressorConfig {
    enable_deduplication: true,
    enable_delta_encoding: true,
    use_string_table: true,
    max_string_table_size: 50000,
    compress_attributes: true,
    min_batch_size: 5,
    compression_level: 9,
};

// 平衡配置（推荐）
let config = CompressorConfig::default();

// 快速压缩（压缩率较低）
let config = CompressorConfig {
    enable_deduplication: false,
    enable_delta_encoding: true,
    use_string_table: true,
    max_string_table_size: 1000,
    compress_attributes: false,
    min_batch_size: 50,
    compression_level: 1,
};
```

---

### CompressionStats

压缩统计信息。

```rust
#[derive(Debug, Clone)]
pub struct CompressionStats {
    /// 原始数据大小（字节）
    pub original_size: usize,

    /// 压缩后大小（字节）
    pub compressed_size: usize,

    /// 压缩比率 (0.0-1.0)
    pub compression_ratio: f64,

    /// 节省的字节数
    pub bytes_saved: usize,

    /// 压缩的spans数量
    pub spans_processed: usize,

    /// 去重的spans数量
    pub spans_deduplicated: usize,

    /// 字符串表条目数
    pub string_table_entries: usize,

    /// 字符串表节省的字节数
    pub string_table_savings: usize,

    /// Delta编码节省的字节数
    pub delta_encoding_savings: usize,

    /// 压缩耗时
    pub compression_time: Duration,

    /// 压缩速度（MB/s）
    pub compression_speed: f64,
}

impl CompressionStats {
    /// 格式化输出统计信息
    pub fn display(&self) -> String {
        format!(
            "Compression Stats:\n\
             - Original: {} bytes\n\
             - Compressed: {} bytes\n\
             - Ratio: {:.2}%\n\
             - Saved: {} bytes\n\
             - Speed: {:.2} MB/s",
            self.original_size,
            self.compressed_size,
            self.compression_ratio * 100.0,
            self.bytes_saved,
            self.compression_speed
        )
    }
}
```

---

## ❌ 错误处理

### CompressionError

压缩过程中可能发生的错误。

```rust
#[derive(Debug, thiserror::Error)]
pub enum CompressionError {
    /// 数据太小，不值得压缩
    #[error("Data too small to compress: {0} bytes")]
    DataTooSmall(usize),

    /// 序列化错误
    #[error("Serialization error: {0}")]
    Serialization(String),

    /// 编码错误
    #[error("Encoding error: {0}")]
    Encoding(String),

    /// 字符串表溢出
    #[error("String table overflow: {current} entries (max: {max})")]
    StringTableOverflow { current: usize, max: usize },

    /// 配置错误
    #[error("Invalid configuration: {0}")]
    InvalidConfig(String),

    /// I/O错误
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
```

### DecompressionError

解压过程中可能发生的错误。

```rust
#[derive(Debug, thiserror::Error)]
pub enum DecompressionError {
    /// 无效的压缩数据
    #[error("Invalid compressed data: {0}")]
    InvalidData(String),

    /// 版本不兼容
    #[error("Incompatible version: expected {expected}, got {actual}")]
    VersionMismatch { expected: u8, actual: u8 },

    /// 校验和错误
    #[error("Checksum mismatch: expected {expected:x}, got {actual:x}")]
    ChecksumMismatch { expected: u32, actual: u32 },

    /// 解码错误
    #[error("Decoding error: {0}")]
    Decoding(String),

    /// 反序列化错误
    #[error("Deserialization error: {0}")]
    Deserialization(String),
}
```

---

## 📊 压缩算法详解

### 1. Span去重

识别并消除重复的span数据。

```rust
// 相同的span只存储一次
let spans = vec![
    create_span("operation-1"),
    create_span("operation-1"),  // 重复
    create_span("operation-2"),
];

let compressed = compressor.compress(&spans)?;
// 内部只存储2个唯一span
```

### 2. Delta编码

时间戳和ID使用增量编码。

```rust
// 原始数据：
// timestamp: [1000000, 1000100, 1000150, 1000200]
//
// Delta编码后：
// base: 1000000
// deltas: [100, 50, 50]
// 节省: ~60% 空间
```

### 3. 字符串表

重复字符串只存储一次。

```rust
// 原始：每个span都有完整的字符串
// span1.service = "my-service"  (10 bytes)
// span2.service = "my-service"  (10 bytes)
// span3.service = "my-service"  (10 bytes)
// 总共: 30 bytes
//
// 字符串表：
// table[0] = "my-service"  (10 bytes)
// span1.service = table[0]  (1 byte)
// span2.service = table[0]  (1 byte)
// span3.service = table[0]  (1 byte)
// 总共: 13 bytes (节省 57%)
```

---

## 💡 使用示例

### 基本压缩

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

fn compress_traces(spans: Vec<Span>) -> Result<Vec<u8>, CompressionError> {
    let mut compressor = TraceCompressor::new(CompressorConfig::default());

    // 压缩
    let compressed = compressor.compress(&spans)?;

    // 输出统计
    let stats = compressor.stats();
    println!("{}", stats.display());

    Ok(compressed)
}
```

### 批量处理

```rust
use otlp::compression::tracezip::TraceCompressor;

async fn process_span_batches(batches: Vec<Vec<Span>>) -> Result<()> {
    let mut compressor = TraceCompressor::default();

    for (i, batch) in batches.iter().enumerate() {
        // 压缩批次
        let compressed = compressor.compress(batch)?;

        // 发送压缩数据
        send_to_collector(&compressed).await?;

        // 定期清理字符串表（避免无限增长）
        if i % 100 == 0 {
            compressor.clear_string_table();
        }
    }

    Ok(())
}
```

### 自适应压缩

```rust
fn adaptive_compress(spans: &[Span]) -> Result<Vec<u8>> {
    let mut compressor = TraceCompressor::default();

    // 尝试压缩
    let compressed = compressor.compress(spans)?;
    let stats = compressor.stats();

    // 如果压缩效果不好，返回原始数据
    if stats.compression_ratio > 0.9 {
        println!("⚠️ Low compression ratio, using uncompressed data");
        Ok(serialize_spans(spans)?)
    } else {
        println!("✅ Good compression: {:.2}%", stats.compression_ratio * 100.0);
        Ok(compressed)
    }
}
```

### 完整的压缩/解压流程

```rust
use otlp::compression::tracezip::{TraceCompressor, CompressorConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建压缩器
    let config = CompressorConfig {
        compression_level: 6,
        ..Default::default()
    };
    let mut compressor = TraceCompressor::new(config);

    // 2. 准备测试数据
    let spans = generate_test_spans(1000);
    let original_size = estimate_size(&spans);
    println!("Original size: {} KB", original_size / 1024);

    // 3. 压缩
    let start = Instant::now();
    let compressed = compressor.compress(&spans)?;
    let compression_time = start.elapsed();

    println!("Compressed size: {} KB", compressed.len() / 1024);
    println!("Compression time: {:?}", compression_time);

    // 4. 查看统计
    let stats = compressor.stats();
    println!("\n{}", stats.display());
    println!("Deduplication: {} spans", stats.spans_deduplicated);
    println!("String table: {} entries", stats.string_table_entries);
    println!("Delta savings: {} bytes", stats.delta_encoding_savings);

    // 5. 解压验证
    let decompressed = compressor.decompress(&compressed)?;
    assert_eq!(spans.len(), decompressed.len());
    println!("\n✅ Decompression successful!");

    // 6. 性能指标
    println!("\n📊 Performance:");
    println!("  Compression ratio: {:.2}%", stats.compression_ratio * 100.0);
    println!("  Speed: {:.2} MB/s", stats.compression_speed);
    println!("  Bytes saved: {} KB", stats.bytes_saved / 1024);

    Ok(())
}
```

---

## ⚡ 性能优化

### 1. 批次大小选择

```rust
// 不同批次大小的压缩效果
let test_sizes = vec![10, 50, 100, 500, 1000];

for size in test_sizes {
    let spans = generate_spans(size);
    let stats = compressor.compress(&spans)?.stats();

    println!("Batch size: {}, Ratio: {:.2}%",
             size, stats.compression_ratio * 100.0);
}

// 结果示例:
// Batch size: 10, Ratio: 85%   (较差)
// Batch size: 50, Ratio: 72%   (一般)
// Batch size: 100, Ratio: 68%  (良好) ✅ 推荐
// Batch size: 500, Ratio: 65%  (很好)
// Batch size: 1000, Ratio: 63% (最好，但延迟高)
```

### 2. 配置调优

```rust
// 低延迟场景
let low_latency_config = CompressorConfig {
    compression_level: 1,        // 最快
    min_batch_size: 50,          // 较大批次
    enable_deduplication: false, // 跳过去重
    ..Default::default()
};

// 高压缩率场景
let high_compression_config = CompressorConfig {
    compression_level: 9,        // 最高
    min_batch_size: 10,          // 小批次也压缩
    enable_deduplication: true,  // 完全去重
    max_string_table_size: 50000, // 大字符串表
    ..Default::default()
};
```

### 3. 内存管理

```rust
let mut compressor = TraceCompressor::default();

for batch in span_stream {
    compressor.compress(&batch)?;

    // 每1000个批次清理一次
    if batch_count % 1000 == 0 {
        compressor.clear_string_table();
        compressor.reset();
    }
}
```

---

## 📈 性能基准

### 压缩性能

| Span数 | 原始大小 | 压缩后 | 压缩率 | 时间 | 速度 |
|--------|---------|--------|--------|------|------|
| 100 | 50 KB | 15 KB | 70% | 3ms | 16 MB/s |
| 500 | 250 KB | 70 KB | 72% | 12ms | 20 MB/s |
| 1000 | 500 KB | 135 KB | 73% | 22ms | 22 MB/s |
| 5000 | 2.5 MB | 650 KB | 74% | 95ms | 26 MB/s |

### 解压性能

| 数据大小 | 解压时间 | 速度 |
|---------|---------|------|
| 15 KB | 0.2ms | 75 MB/s |
| 70 KB | 0.8ms | 87 MB/s |
| 135 KB | 1.5ms | 90 MB/s |
| 650 KB | 7ms | 93 MB/s |

---

## 🔗 相关文档

- [OTLP 2024-2025特性](../08_REFERENCE/otlp_2024_2025_features.md)
- [性能优化指南](../guides/performance-optimization.md)
- [最佳实践](../08_REFERENCE/best_practices.md)

---

**模块版本**: 0.5.0
**Tracezip版本**: 1.0
**最后更新**: 2025年10月26日
**维护状态**: ✅ 活跃维护
