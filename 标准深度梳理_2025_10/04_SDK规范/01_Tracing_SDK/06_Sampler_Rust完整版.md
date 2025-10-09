# Sampler - Rust 完整实现指南

> **OpenTelemetry 版本**: 0.31.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [Sampler - Rust 完整实现指南](#sampler---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 Sampler](#11-什么是-sampler)
  - [2. 内置 Sampler](#2-内置-sampler)
    - [2.1 AlwaysOn](#21-alwayson)
    - [2.2 AlwaysOff](#22-alwaysoff)
    - [2.3 TraceIdRatioBased](#23-traceidratiobased)
    - [2.4 ParentBased](#24-parentbased)
  - [3. 采样决策](#3-采样决策)
    - [3.1 SamplingResult](#31-samplingresult)
  - [4. 自定义 Sampler](#4-自定义-sampler)
    - [4.1 实现自定义 Sampler](#41-实现自定义-sampler)
  - [5. 最佳实践](#5-最佳实践)
    - [5.1 采样率选择](#51-采样率选择)
    - [5.2 配置示例](#52-配置示例)
  - [总结](#总结)
    - [核心要点](#核心要点)

---

## 1. 概述

### 1.1 什么是 Sampler

Sampler 决定是否记录和导出 Span，用于：

- **控制数据量**：避免导出所有 Trace
- **降低成本**：减少存储和网络开销
- **保持性能**：减少追踪对应用的影响

---

## 2. 内置 Sampler

### 2.1 AlwaysOn

```rust
use opentelemetry_sdk::trace::Sampler;

// 总是采样（开发/调试环境）
let sampler = Sampler::AlwaysOn;
```

### 2.2 AlwaysOff

```rust
// 从不采样
let sampler = Sampler::AlwaysOff;
```

### 2.3 TraceIdRatioBased

```rust
// 基于 TraceID 的概率采样（10%）
let sampler = Sampler::TraceIdRatioBased(0.1);
```

### 2.4 ParentBased

```rust
// 根据父 Span 决定
let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));
```

---

## 3. 采样决策

### 3.1 SamplingResult

```rust
pub struct SamplingResult {
    pub decision: SamplingDecision,
    pub attributes: Vec<KeyValue>,
    pub trace_state: TraceState,
}

pub enum SamplingDecision {
    Drop,              // 丢弃，不记录
    RecordOnly,        // 记录但不导出
    RecordAndSample,   // 记录并导出
}
```

---

## 4. 自定义 Sampler

### 4.1 实现自定义 Sampler

```rust
use opentelemetry::trace::{SamplingDecision, SamplingResult, SpanKind};
use opentelemetry_sdk::trace::ShouldSample;

pub struct RateLimitingSampler {
    max_per_second: u32,
    counter: Arc<Mutex<(Instant, u32)>>,
}

impl ShouldSample for RateLimitingSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        let mut state = self.counter.lock().unwrap();
        let now = Instant::now();
        
        if now.duration_since(state.0).as_secs() >= 1 {
            state.0 = now;
            state.1 = 0;
        }
        
        if state.1 < self.max_per_second {
            state.1 += 1;
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        }
    }
}
```

---

## 5. 最佳实践

### 5.1 采样率选择

```text
开发环境:
✅ AlwaysOn (100%)

生产环境:
✅ ParentBased + TraceIdRatioBased(0.1) (10%)
✅ 根据流量调整采样率
```

### 5.2 配置示例

```rust
let sampler = if cfg!(debug_assertions) {
    Sampler::AlwaysOn
} else {
    Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))
};

let provider = TracerProvider::builder()
    .with_config(Config::default().with_sampler(sampler))
    .build();
```

---

## 总结

### 核心要点

1. **AlwaysOn**: 开发环境
2. **TraceIdRatioBased**: 基于概率
3. **ParentBased**: 保持 Trace 完整性
4. **自定义 Sampler**: 实现 `ShouldSample` trait

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**维护者**: OTLP Rust 项目组
