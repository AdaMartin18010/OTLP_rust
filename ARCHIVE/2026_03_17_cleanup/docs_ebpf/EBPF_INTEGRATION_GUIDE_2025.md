# eBPF 与 OpenTelemetry 集成指南 2025

**创建日期**: 2025年1月
**状态**: 📚 集成指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 与 OpenTelemetry 集成指南 2025](#ebpf-与-opentelemetry-集成指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [集成优势](#集成优势)
  - [集成架构](#集成架构)
  - [数据转换](#数据转换)
    - [事件到 Span](#事件到-span)
    - [事件到 Metric](#事件到-metric)
    - [Profile 到 OTLP](#profile-到-otlp)
  - [导出配置](#导出配置)
    - [基本配置](#基本配置)
  - [最佳实践](#最佳实践)
    - [1. 采样策略](#1-采样策略)
    - [2. 数据过滤](#2-数据过滤)
    - [3. 批量导出](#3-批量导出)
    - [4. 错误处理](#4-错误处理)
  - [示例代码](#示例代码)
  - [参考资源](#参考资源)

---

## 概述

eBPF 模块可以与 OpenTelemetry 无缝集成，将 eBPF 收集的性能数据转换为 OpenTelemetry 的 Traces、Metrics 和 Profiles。

### 集成优势

1. **统一遥测**: 将 eBPF 数据纳入 OpenTelemetry 生态系统
2. **标准化格式**: 使用 OpenTelemetry 标准格式
3. **完整可观测性**: 结合应用层和内核层数据
4. **易于分析**: 使用标准工具分析数据

---

## 集成架构

```
┌─────────────────────────────────────┐
│      eBPF 程序 (内核空间)          │
│  - CPU 采样                         │
│  - 网络追踪                         │
│  - 系统调用追踪                     │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│   eBPF 模块 (用户空间)              │
│  - 事件收集                         │
│  - 数据转换                         │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│   OpenTelemetry 转换器              │
│  - EbpfOtlpConverter               │
│  - 事件 → Span                      │
│  - 事件 → Metric                    │
│  - Profile → OTLP                   │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│   OTLP Exporter                     │
│  - gRPC/HTTP                        │
│  - 批量导出                         │
└─────────────────────────────────────┘
```

---

## 数据转换

### 事件到 Span

```rust
use otlp::ebpf::{EbpfOtlpConverter, EbpfEvent, EbpfEventType};
use opentelemetry::trace::Tracer;

let converter = EbpfOtlpConverter::new()
    .with_tracer(tracer);

let event = EbpfEvent::new(
    EbpfEventType::NetworkPacket,
    1234,
    5678,
    vec![],
);

if let Some(span) = converter.convert_event_to_span(&event)? {
    // Span 已创建，可以设置更多属性
    span.set_attribute(
        opentelemetry::KeyValue::new("network.protocol", "TCP")
    );
    span.end();
}
```

### 事件到 Metric

```rust
use otlp::ebpf::EbpfOtlpConverter;
use opentelemetry::metrics::Meter;

let converter = EbpfOtlpConverter::new()
    .with_meter(meter);

converter.convert_event_to_metric(&event)?;
```

### Profile 到 OTLP

```rust
use otlp::ebpf::EbpfOtlpConverter;
use otlp::profiling::types::PprofProfile;

let converter = EbpfOtlpConverter::new();
let profile = cpu_profiler.stop()?;

converter.convert_profile_to_otlp(&profile)?;
```

---

## 导出配置

### 基本配置

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler, EbpfOtlpConverter};
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;

// 1. 创建 OpenTelemetry Tracer
let provider = SdkTracerProvider::builder()
    .with_batch_exporter(otlp_exporter)
    .build();
let tracer = provider.tracer("ebpf-profiler");

// 2. 创建转换器
let converter = EbpfOtlpConverter::new()
    .with_tracer(tracer);

// 3. 创建 eBPF 性能分析器
let config = EbpfConfig::default();
let mut profiler = EbpfCpuProfiler::new(config);

// 4. 开始分析
profiler.start()?;

// 5. 执行工作负载
// ... 你的代码 ...

// 6. 停止并转换
let profile = profiler.stop()?;
converter.convert_profile_to_otlp(&profile)?;
```

---

## 最佳实践

### 1. 采样策略

- **开发环境**: 高采样率 (99Hz)
- **生产环境**: 低采样率 (19-49Hz)
- **调试模式**: 最高采样率 (199Hz)

### 2. 数据过滤

```rust
// 只转换重要事件
if event.event_type == EbpfEventType::CpuSample {
    converter.convert_event_to_span(&event)?;
}
```

### 3. 批量导出

```rust
// 收集多个事件后批量转换
let mut events = Vec::new();
// ... 收集事件 ...

for event in events {
    converter.convert_event_to_metric(&event)?;
}
```

### 4. 错误处理

```rust
match converter.convert_event_to_span(&event) {
    Ok(Some(span)) => {
        // 成功转换
    }
    Ok(None) => {
        // Tracer 未设置
    }
    Err(e) => {
        // 处理错误
        tracing::error!("转换失败: {}", e);
    }
}
```

---

## 示例代码

完整示例请参考:

- `examples/ebpf_complete_example.rs` - 完整功能示例
- `docs/EBPF_USAGE_GUIDE_2025.md` - 使用指南

---

## 参考资源

- [OpenTelemetry 文档](https://opentelemetry.io/)
- [eBPF 使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [项目 eBPF 实施计划](../EBPF_IMPLEMENTATION_PLAN_2025.md)

---

**状态**: 📚 集成指南
**最后更新**: 2025年1月
