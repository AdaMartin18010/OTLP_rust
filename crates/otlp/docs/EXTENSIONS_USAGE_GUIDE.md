# 扩展模块使用指南

**版本**: v0.6.0
**日期**: 2025年1月13日

---

## 📋 概述

本指南详细介绍如何使用基于官方 `opentelemetry-rust` 库的扩展功能。

---

## 🚀 快速开始

### 基础使用

```rust
use otlp::new_enhanced_pipeline_v2;
use opentelemetry_sdk::runtime::Tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = new_enhanced_pipeline_v2()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .install_batch(Tokio)?;

    let span = tracer.start("my-operation");
    // ... 业务逻辑
    drop(span);

    Ok(())
}
```

---

## 🔧 扩展功能详解

### 1. eBPF性能分析

**功能**: 提供低开销的系统级性能分析

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_ebpf_profiling(true)  // 启用eBPF
    .install_batch(Tokio)?;
```

**要求**:

- Linux内核 >= 5.8
- CAP_BPF权限或root权限
- 启用`ebpf` feature flag

**性能影响**: <1% CPU开销

### 2. SIMD优化

**功能**: 使用SIMD指令加速数据处理

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_simd_optimization(true)  // 启用SIMD
    .install_batch(Tokio)?;
```

**性能提升**: 30-50%批处理性能提升

**自动降级**: 如果CPU不支持SIMD，自动使用标量实现

### 3. Tracezip压缩

**功能**: 使用Tracezip算法压缩追踪数据

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_tracezip_compression(true)  // 启用压缩
    .install_batch(Tokio)?;
```

**压缩率**: 50-70%大小减少

**性能影响**: <5% CPU开销，<10ms延迟

### 4. 多租户支持

**功能**: 为不同租户隔离数据

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_multi_tenant(true)
    .with_tenant_id("tenant-123".to_string())  // 设置租户ID
    .install_batch(Tokio)?;
```

**特性**:

- 自动添加租户ID到span attributes
- 支持租户级别的配额和限制

### 5. 合规管理

**功能**: 满足GDPR、HIPAA等合规要求

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_compliance(true)  // 启用合规管理
    .install_batch(Tokio)?;
```

**功能**:

- 数据脱敏
- 访问控制
- 合规审计日志

### 6. 批量处理优化

**功能**: 优化批量导出性能

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_batch_optimization(true)  // 启用批量优化
    .install_batch(Tokio)?;
```

**优化**:

- 智能批量大小
- 批量超时控制
- 减少网络调用

### 7. 连接池优化

**功能**: 复用网络连接

**使用**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_connection_pool(true)  // 启用连接池
    .install_batch(Tokio)?;
```

**优化**:

- 连接复用
- 减少连接建立开销
- 提高并发性能

---

## 🎨 组合使用

### 完整配置示例

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_service_name("production-service")
    .with_service_version("1.0.0")
    // 性能优化
    .with_simd_optimization(true)
    .with_tracezip_compression(true)
    .with_batch_optimization(true)
    .with_connection_pool(true)
    // 企业特性
    .with_multi_tenant(true)
    .with_tenant_id("enterprise-tenant".to_string())
    .with_compliance(true)
    // 高级特性
    .with_ebpf_profiling(true)
    .install_batch(Tokio)?;
```

### 仅性能优化

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_simd_optimization(true)
    .with_tracezip_compression(true)
    .with_batch_optimization(true)
    .with_connection_pool(true)
    .install_batch(Tokio)?;
```

### 仅企业特性

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_multi_tenant(true)
    .with_tenant_id("tenant-123".to_string())
    .with_compliance(true)
    .install_batch(Tokio)?;
```

---

## 🔍 手动组合扩展

如果需要更细粒度的控制，可以手动组合扩展：

```rust
use otlp::extensions::*;
use opentelemetry_otlp::new_exporter;
use opentelemetry_sdk::trace::TracerProviderBuilder;
use opentelemetry_sdk::Resource;
use opentelemetry::KeyValue;

// 创建基础exporter
let base_exporter = new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .build_span_exporter()?;

// 手动组合扩展（从内到外）
let exporter = ComplianceExporter::wrap(base_exporter)
    .with_compliance(true);
let exporter = MultiTenantExporter::wrap(Box::new(exporter))
    .with_tenant_id("tenant-123".to_string());
let exporter = SimdSpanExporter::wrap(Box::new(exporter))
    .with_simd_optimization(true);
let exporter = TracezipSpanExporter::wrap(Box::new(exporter))
    .with_compression(true);

// 构建TracerProvider
let provider = TracerProviderBuilder::default()
    .with_batch_exporter(exporter, Tokio)
    .with_config(
        opentelemetry_sdk::trace::Config::default()
            .with_resource(Resource::new(vec![
                KeyValue::new("service.name", "my-service"),
            ]))
    )
    .build();

let tracer = provider.tracer("my-tracer");
```

---

## ⚙️ 配置选项

### EnhancedPipelineV2配置

| 方法 | 说明 | 默认值 |
|------|------|--------|
| `with_endpoint()` | OTLP端点 | 无 |
| `with_service_name()` | 服务名称 | 无 |
| `with_service_version()` | 服务版本 | 无 |
| `with_ebpf_profiling()` | eBPF性能分析 | false |
| `with_simd_optimization()` | SIMD优化 | false |
| `with_tracezip_compression()` | Tracezip压缩 | false |
| `with_multi_tenant()` | 多租户支持 | false |
| `with_tenant_id()` | 租户ID | 无 |
| `with_compliance()` | 合规管理 | false |
| `with_batch_optimization()` | 批量处理优化 | false |
| `with_connection_pool()` | 连接池优化 | false |

---

## 📊 性能考虑

### 扩展开销

| 扩展 | CPU开销 | 内存开销 | 延迟影响 |
|------|---------|---------|---------|
| eBPF | <1% | <10MB | <1ms |
| SIMD | <2% | 无 | 负延迟（更快） |
| Tracezip | <5% | <20MB | <10ms |
| 多租户 | <1% | <5MB | <1ms |
| 合规管理 | <2% | <10MB | <2ms |
| 批量优化 | <1% | <10MB | 负延迟（更快） |
| 连接池 | <1% | <5MB | 负延迟（更快） |

### 推荐配置

**高性能场景**:

```rust
.with_simd_optimization(true)
.with_tracezip_compression(true)
.with_batch_optimization(true)
.with_connection_pool(true)
```

**企业场景**:

```rust
.with_multi_tenant(true)
.with_compliance(true)
```

**调试场景**:

```rust
.with_ebpf_profiling(true)
```

---

## 🐛 故障排除

### 问题1: eBPF扩展无法启用

**原因**: 缺少权限或内核版本过低

**解决**:

```bash
# 检查内核版本
uname -r  # 需要 >= 5.8

# 检查权限
capsh --print | grep CAP_BPF  # 需要CAP_BPF或root
```

### 问题2: SIMD优化未生效

**原因**: CPU不支持SIMD指令

**解决**: 自动降级到标量实现，无需处理

### 问题3: Tracezip压缩率低

**原因**: 数据重复度低

**解决**: 正常现象，压缩率取决于数据特征

---

## 📚 相关文档

- [扩展模块README](src/extensions/README.md)
- [迁移指南](MIGRATION_GUIDE.md)
- [API参考](API_REFERENCE.md)

---

**最后更新**: 2025年1月13日
