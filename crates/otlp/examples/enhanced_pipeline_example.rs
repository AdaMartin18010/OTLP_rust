//! # 增强Pipeline使用示例
//!
//! 本示例展示如何使用基于官方 `opentelemetry-rust` 的增强Pipeline。

use opentelemetry::trace::Tracer;
use opentelemetry_sdk::runtime::Tokio;

/// 示例1: 使用增强Pipeline的基础用法
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 使用便捷API创建增强Pipeline
    use otlp::new_enhanced_pipeline;

    let tracer = new_enhanced_pipeline()
        .with_ebpf_profiling(true)        // 启用eBPF性能分析
        .with_simd_optimization(true)      // 启用SIMD优化
        .with_tracezip_compression(true)    // 启用Tracezip压缩
        .with_multi_tenant(true)           // 启用多租户支持
        .with_tenant_id("tenant-123".to_string()) // 设置租户ID
        .with_compliance(true)             // 启用合规管理
        .with_batch_optimization(true)     // 启用批量处理优化
        .with_connection_pool(true)        // 启用连接池优化
        .install_batch(Tokio)?;

    // 使用tracer创建span
    let span = tracer.start("my-operation");
    span.set_attribute("key".into(), "value".into());
    drop(span);

    Ok(())
}

/// 示例2: 仅使用官方API（完全兼容）
#[allow(dead_code)]
async fn example_official_api() -> Result<(), Box<dyn std::error::Error>> {
    use opentelemetry_otlp::new_pipeline;

    // 使用官方API，完全兼容
    let tracer = new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(Tokio)?;

    let span = tracer.start("my-operation");
    drop(span);

    Ok(())
}

/// 示例3: 逐步添加扩展
#[allow(dead_code)]
async fn example_gradual_extension() -> Result<(), Box<dyn std::error::Error>> {
    use opentelemetry_otlp::new_pipeline;
    use otlp::extensions::tracezip::TracezipSpanExporter;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    // 先创建官方pipeline
    let mut pipeline = new_pipeline().tracing();

    // 添加Tracezip压缩扩展
    let exporter = Box::new(NoopSpanExporter::new());
    let enhanced_exporter = TracezipSpanExporter::wrap(exporter)
        .with_compression(true);

    // 注意: 实际使用需要根据opentelemetry_otlp的API调整
    // 这里提供概念性示例

    Ok(())
}

/// 示例4: 使用EnhancedExporter构建器
#[allow(dead_code)]
async fn example_enhanced_exporter() -> Result<(), Box<dyn std::error::Error>> {
    use otlp::wrappers::EnhancedExporter;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    // 使用EnhancedExporter构建器
    let exporter = EnhancedExporter::new()
        .with_exporter(Box::new(NoopSpanExporter::new()))
        .with_simd_optimization(true)
        .with_tracezip_compression(true)
        .with_multi_tenant(true)
        .with_tenant_id("tenant-123".to_string())
        .with_compliance(true)
        .with_batch_optimization(true)
        .with_connection_pool(true)
        .build()?;

    // 使用exporter
    // 注意: 实际使用需要集成到pipeline中

    Ok(())
}
