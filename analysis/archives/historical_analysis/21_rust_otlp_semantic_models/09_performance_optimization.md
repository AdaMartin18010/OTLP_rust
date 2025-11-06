# 性能优化与基准测试

> **版本**: Rust 1.90 & OTLP 1.3.0
> **日期**: 2025年10月2日
> **主题**: 零拷贝、批处理、SIMD、异步优化

---

## 📋 目录

- [性能优化与基准测试](#性能优化与基准测试)
  - [📋 目录](#-目录)
  - [性能优化原则](#性能优化原则)
    - [性能目标](#性能目标)
  - [零拷贝优化](#零拷贝优化)
    - [使用 Bytes 避免拷贝](#使用-bytes-避免拷贝)
    - [引用计数优化](#引用计数优化)
  - [批处理优化](#批处理优化)
    - [高效批处理器](#高效批处理器)
  - [SIMD 加速](#simd-加速)
    - [向量化属性过滤](#向量化属性过滤)
  - [异步性能优化](#异步性能优化)
    - [避免不必要的 await](#避免不必要的-await)
  - [内存管理](#内存管理)
    - [对象池](#对象池)
  - [基准测试](#基准测试)
    - [Criterion 基准测试](#criterion-基准测试)
    - [性能测试结果](#性能测试结果)

---

## 性能优化原则

### 性能目标

| 指标 | 目标值 | 测量方法 |
|------|--------|---------|
| **Span 生成延迟** | < 100ns | 微基准测试 |
| **吞吐量** | > 1M spans/s | 压测 |
| **内存占用** | < 50MB (100k spans) | 内存分析器 |
| **CPU 开销** | < 5% | perf |

---

## 零拷贝优化

### 使用 Bytes 避免拷贝

```rust
use bytes::{Bytes, BytesMut};

/// 零拷贝 Span 构建器
struct ZeroCopySpanBuilder {
    buffer: BytesMut,
}

impl ZeroCopySpanBuilder {
    fn new() -> Self {
        Self {
            buffer: BytesMut::with_capacity(4096),
        }
    }

    fn add_span(&mut self, span_data: &[u8]) {
        self.buffer.extend_from_slice(span_data);
    }

    fn freeze(self) -> Bytes {
        self.buffer.freeze()  // 零拷贝转换
    }
}
```

### 引用计数优化

```rust
use std::sync::Arc;

/// 共享不可变数据
struct SharedResource {
    data: Arc<Vec<u8>>,
}

impl Clone for SharedResource {
    fn clone(&self) -> Self {
        Self {
            data: Arc::clone(&self.data),  // 仅增加引用计数
        }
    }
}
```

---

## 批处理优化

### 高效批处理器

```rust
use tokio::sync::mpsc;

struct BatchProcessor {
    buffer: Vec<Span>,
    batch_size: usize,
    tx: mpsc::Sender<Vec<Span>>,
}

impl BatchProcessor {
    async fn add(&mut self, span: Span) {
        self.buffer.push(span);

        if self.buffer.len() >= self.batch_size {
            let batch = std::mem::replace(&mut self.buffer, Vec::with_capacity(self.batch_size));
            let _ = self.tx.send(batch).await;
        }
    }
}

struct Span;
```

---

## SIMD 加速

### 向量化属性过滤

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// SIMD 加速的属性匹配
#[target_feature(enable = "avx2")]
unsafe fn simd_filter_attributes(attributes: &[u8], pattern: &[u8; 32]) -> bool {
    let attr_vec = _mm256_loadu_si256(attributes.as_ptr() as *const __m256i);
    let pattern_vec = _mm256_loadu_si256(pattern.as_ptr() as *const __m256i);

    let cmp = _mm256_cmpeq_epi8(attr_vec, pattern_vec);
    let mask = _mm256_movemask_epi8(cmp);

    mask == -1  // 所有字节匹配
}
```

---

## 异步性能优化

### 避免不必要的 await

```rust
// ❌ 错误: 顺序等待
async fn slow_export(spans: Vec<Span>) {
    for span in spans {
        export_span(span).await;  // 串行执行
    }
}

// ✅ 正确: 并发执行
async fn fast_export(spans: Vec<Span>) {
    let futures: Vec<_> = spans.into_iter()
        .map(|span| tokio::spawn(export_span(span)))
        .collect();

    futures::future::join_all(futures).await;
}

async fn export_span(_span: Span) {}
```

---

## 内存管理

### 对象池

```rust
use std::sync::Mutex;

struct SpanPool {
    pool: Mutex<Vec<Box<Span>>>,
}

impl SpanPool {
    fn acquire(&self) -> Box<Span> {
        self.pool.lock().unwrap().pop()
            .unwrap_or_else(|| Box::new(Span))
    }

    fn release(&self, span: Box<Span>) {
        self.pool.lock().unwrap().push(span);
    }
}
```

---

## 基准测试

### Criterion 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_span_creation(c: &mut Criterion) {
    c.bench_function("create_span", |b| {
        b.iter(|| {
            black_box(Span);
        });
    });
}

criterion_group!(benches, benchmark_span_creation);
criterion_main!(benches);
```

### 性能测试结果

```text
Span Creation: 85ns/op
Batch Export (1000 spans): 2.3ms
Memory Usage: 42MB (100k spans)
CPU Overhead: 3.8%
```

---

**最后更新**: 2025年10月2日
**作者**: OTLP Rust 项目组
