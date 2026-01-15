# 迁移指南：从自定义实现到基于官方库扩展

**版本**: v0.6.0
**日期**: 2025年1月13日

---

## 📋 概述

本指南帮助您从项目的自定义OTLP实现迁移到基于官方 `opentelemetry-rust` 库的扩展实现。

---

## 🎯 迁移收益

### 迁移前（自定义实现）

```rust
use otlp::{OtlpClient, OtlpConfig};

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317");
let client = OtlpClient::new(config).await?;
```

**问题**:

- ❌ 与官方API不兼容
- ❌ 需要维护大量重复代码
- ❌ 无法利用官方库的生态

### 迁移后（基于官方库扩展）

```rust
// 方式1: 使用官方API（完全兼容）
use opentelemetry_otlp::new_pipeline;

let tracer = new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317")
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;

// 方式2: 使用增强API（添加扩展功能）
use otlp::new_enhanced_pipeline_v2;

let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .with_ebpf_profiling(true)      // 添加eBPF支持
    .with_simd_optimization(true)    // 添加SIMD优化
    .with_tracezip_compression(true)  // 添加Tracezip压缩
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

**优势**:

- ✅ 与官方API完全兼容
- ✅ 可以随时移除扩展使用官方API
- ✅ 利用官方库的稳定性和生态
- ✅ 专注于本项目的独特价值

---

## 🔄 迁移步骤

### 步骤1: 更新依赖

**Cargo.toml**:

```toml
[dependencies]
# 确保使用最新版本的opentelemetry-rust
opentelemetry = "0.31"
opentelemetry-sdk = "0.31"
opentelemetry-otlp = "0.31"

# 本项目扩展
otlp = { path = "../otlp" }
```

### 步骤2: 更新导入

**迁移前**:

```rust
use otlp::{OtlpClient, OtlpConfig};
```

**迁移后**:

```rust
// 使用官方API
use opentelemetry_otlp::new_pipeline;
use opentelemetry_sdk::runtime::Tokio;

// 或使用增强API
use otlp::new_enhanced_pipeline_v2;
```

### 步骤3: 更新客户端创建

**迁移前**:

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_batch_size(100);

let client = OtlpClient::new(config).await?;
client.initialize().await?;
```

**迁移后（官方API）**:

```rust
let tracer = new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317")
    )
    .install_batch(Tokio)?;
```

**迁移后（增强API）**:

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .install_batch(Tokio)?;
```

### 步骤4: 更新Span创建

**迁移前**:

```rust
let trace = client.send_trace("my-operation").await?;
trace.with_attribute("key", "value")
     .with_duration(150)
     .finish().await?;
```

**迁移后**:

```rust
let span = tracer.start("my-operation");
span.set_attribute("key".into(), "value".into());
// ... 业务逻辑
drop(span); // 或 span.end()
```

### 步骤5: 添加扩展功能（可选）

如果需要使用本项目的独特功能：

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    // 添加扩展功能
    .with_ebpf_profiling(true)        // eBPF支持
    .with_simd_optimization(true)      // SIMD优化
    .with_tracezip_compression(true)    // Tracezip压缩
    .with_multi_tenant(true)           // 多租户支持
    .with_tenant_id("tenant-123".to_string())
    .install_batch(Tokio)?;
```

---

## 📊 API对比表

| 功能 | 迁移前（自定义） | 迁移后（官方） | 迁移后（增强） |
|------|----------------|--------------|--------------|
| **创建客户端** | `OtlpClient::new()` | `new_pipeline().tracing()` | `new_enhanced_pipeline_v2()` |
| **配置端点** | `.with_endpoint()` | `.with_exporter(...)` | `.with_endpoint()` |
| **创建Span** | `client.send_trace()` | `tracer.start()` | `tracer.start()` |
| **设置属性** | `.with_attribute()` | `.set_attribute()` | `.set_attribute()` |
| **eBPF支持** | ❌ 不支持 | ❌ 不支持 | ✅ `.with_ebpf_profiling()` |
| **SIMD优化** | ⚠️ 部分支持 | ❌ 不支持 | ✅ `.with_simd_optimization()` |
| **Tracezip压缩** | ✅ 支持 | ❌ 不支持 | ✅ `.with_tracezip_compression()` |

---

## ⚠️ 注意事项

### 1. API差异

- **异步初始化**: 官方API不需要显式的`initialize()`调用
- **Span生命周期**: 使用Rust的所有权系统管理，不需要手动`finish()`
- **错误处理**: 使用标准的`Result`类型

### 2. 配置差异

- **批量配置**: 在TracerProvider层面配置，而非客户端层面
- **超时配置**: 在Exporter层面配置
- **资源属性**: 在TracerProvider配置中设置

### 3. 扩展功能

- **可选使用**: 扩展功能是可选的，可以只使用官方API
- **组合使用**: 可以组合多个扩展功能
- **性能影响**: 每个扩展都会增加一定的开销

---

## 🔍 常见问题

### Q1: 如何保持向后兼容？

**A**: 项目的旧API仍然可用，但建议逐步迁移到新API。

### Q2: 扩展功能是否必须？

**A**: 不是。您可以只使用官方API，扩展功能是可选的。

### Q3: 性能会受影响吗？

**A**:

- 使用官方API：性能与官方库相同
- 使用扩展：可能增加少量开销，但带来额外功能

### Q4: 如何测试迁移？

**A**:

1. 先迁移到官方API，确保功能正常
2. 然后逐步添加扩展功能
3. 对比性能和行为

---

## 📚 相关资源

- [opentelemetry-rust文档](https://docs.rs/opentelemetry/)
- [扩展模块文档](src/extensions/README.md)
- [使用示例](examples/enhanced_pipeline_v2_example.rs)

---

**最后更新**: 2025年1月13日
