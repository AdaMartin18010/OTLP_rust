# OTLP扩展模块

本模块提供基于官方 `opentelemetry-rust` 库的扩展功能。

## 设计原则

1. **扩展而非替换**: 通过包装器模式扩展官方库，不替换核心实现
2. **向后兼容**: 保持与官方API的完全兼容
3. **可选功能**: 通过feature flags控制扩展功能

## 模块结构

### 1. eBPF扩展 (`ebpf/`)

提供eBPF性能分析和追踪扩展。

**使用示例**:
```rust
use otlp::extensions::ebpf::EbpfTracerExtension;
use opentelemetry::trace::Tracer;

let tracer: Box<dyn Tracer> = /* ... */;
let enhanced_tracer = EbpfTracerExtension::wrap(tracer)
    .with_ebpf_profiling(true);
```

### 2. SIMD优化扩展 (`simd/`)

提供SIMD向量化优化扩展。

**使用示例**:
```rust
use otlp::extensions::simd::SimdSpanExporter;
use opentelemetry_sdk::export::trace::NoopSpanExporter;

let exporter = Box::new(NoopSpanExporter::new());
let enhanced_exporter = SimdSpanExporter::wrap(exporter)
    .with_simd_optimization(true);
```

### 3. Tracezip压缩扩展 (`tracezip/`)

提供Tracezip压缩算法扩展。

**使用示例**:
```rust
use otlp::extensions::tracezip::TracezipSpanExporter;
use opentelemetry_sdk::export::trace::NoopSpanExporter;

let exporter = Box::new(NoopSpanExporter::new());
let enhanced_exporter = TracezipSpanExporter::wrap(exporter)
    .with_compression(true);
```

### 4. 企业级特性扩展 (`enterprise/`)

提供企业级特性，包括多租户和合规管理。

**使用示例**:
```rust
use otlp::extensions::enterprise::{MultiTenantExporter, ComplianceExporter};
use opentelemetry_sdk::export::trace::NoopSpanExporter;

let exporter = Box::new(NoopSpanExporter::new());
let enhanced_exporter = MultiTenantExporter::wrap(exporter)
    .with_tenant_id("tenant-123".to_string());
```

### 5. 性能优化扩展 (`performance/`)

提供性能优化功能，包括批量处理和连接池。

**使用示例**:
```rust
use otlp::extensions::performance::BatchOptimizedExporter;
use opentelemetry_sdk::export::trace::NoopSpanExporter;

let exporter = Box::new(NoopSpanExporter::new());
let enhanced_exporter = BatchOptimizedExporter::wrap(exporter)
    .with_batch_size(100);
```

## 组合使用

多个扩展可以组合使用：

```rust
use otlp::extensions::*;
use opentelemetry_sdk::export::trace::NoopSpanExporter;

let exporter = Box::new(NoopSpanExporter::new());

// 按顺序应用扩展（从内到外）
let exporter = TracezipSpanExporter::wrap(exporter)
    .with_compression(true);
let exporter = SimdSpanExporter::wrap(exporter)
    .with_simd_optimization(true);
let exporter = MultiTenantExporter::wrap(exporter)
    .with_tenant_id("tenant-123".to_string());
```

## 注意事项

1. **扩展顺序**: 扩展的应用顺序很重要，通常从内到外应用
2. **性能影响**: 每个扩展都会增加一定的开销，需要权衡
3. **兼容性**: 扩展保持与官方API的兼容性，可以随时移除
