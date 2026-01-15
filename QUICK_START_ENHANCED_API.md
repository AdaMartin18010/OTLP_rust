# 增强API快速开始指南

**版本**: v0.6.0  
**日期**: 2025年1月13日

---

## 🚀 5分钟快速开始

### 步骤1: 添加依赖

**Cargo.toml**:
```toml
[dependencies]
otlp = { path = "crates/otlp" }
opentelemetry = "0.31"
opentelemetry-sdk = "0.31"
opentelemetry-otlp = "0.31"
tokio = { version = "1.49", features = ["full"] }
```

### 步骤2: 创建增强Pipeline

```rust
use otlp::new_enhanced_pipeline_v2;
use opentelemetry_sdk::runtime::Tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建增强Pipeline
    let tracer = new_enhanced_pipeline_v2()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .with_service_version("1.0.0")
        .install_batch(Tokio)?;

    // 创建span
    let span = tracer.start("my-operation");
    span.set_attribute("key".into(), "value".into());
    
    // 业务逻辑
    println!("Operation executed");
    
    drop(span);
    Ok(())
}
```

### 步骤3: 添加扩展功能（可选）

```rust
let tracer = new_enhanced_pipeline_v2()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    // 性能优化
    .with_simd_optimization(true)      // SIMD优化
    .with_tracezip_compression(true)    // Tracezip压缩
    .with_batch_optimization(true)     // 批量处理优化
    .with_connection_pool(true)        // 连接池优化
    // 企业特性
    .with_multi_tenant(true)           // 多租户支持
    .with_tenant_id("tenant-123".to_string())
    .with_compliance(true)             // 合规管理
    // 高级特性
    .with_ebpf_profiling(true)         // eBPF支持（需要Linux）
    .install_batch(Tokio)?;
```

---

## 📚 更多资源

- [完整使用指南](crates/otlp/docs/EXTENSIONS_USAGE_GUIDE.md)
- [迁移指南](crates/otlp/docs/MIGRATION_GUIDE.md)
- [扩展模块文档](crates/otlp/src/extensions/README.md)

---

**最后更新**: 2025年1月13日
