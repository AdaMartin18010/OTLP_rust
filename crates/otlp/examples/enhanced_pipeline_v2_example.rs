//! # 增强Pipeline V2使用示例
//!
//! 本示例展示如何使用EnhancedPipelineV2创建配置了所有扩展功能的Pipeline。

use opentelemetry::trace::Tracer;
use opentelemetry_sdk::runtime::Tokio;

/// 示例1: 完整配置的增强Pipeline
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    use otlp::new_enhanced_pipeline_v2;

    // 使用EnhancedPipelineV2创建完整的增强Pipeline
    let tracer = new_enhanced_pipeline_v2()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .with_service_version("1.0.0")
        .with_ebpf_profiling(true)        // eBPF支持
        .with_simd_optimization(true)      // SIMD优化
        .with_tracezip_compression(true)    // Tracezip压缩
        .with_multi_tenant(true)           // 多租户支持
        .with_tenant_id("tenant-123".to_string()) // 设置租户ID
        .with_compliance(true)             // 合规管理
        .with_batch_optimization(true)     // 批量处理优化
        .with_connection_pool(true)        // 连接池优化
        .install_batch(Tokio)?;

    // 使用tracer创建span
    let span = tracer.start("my-operation");
    span.set_attribute("key".into(), "value".into());

    // 业务逻辑
    println!("Operation executed");

    drop(span);

    Ok(())
}

/// 示例2: 仅使用性能优化扩展
#[allow(dead_code)]
async fn example_performance_only() -> Result<(), Box<dyn std::error::Error>> {
    use otlp::new_enhanced_pipeline_v2;

    let tracer = new_enhanced_pipeline_v2()
        .with_endpoint("http://localhost:4317")
        .with_service_name("performance-service")
        .with_simd_optimization(true)      // SIMD优化
        .with_tracezip_compression(true)    // Tracezip压缩
        .with_batch_optimization(true)     // 批量处理优化
        .with_connection_pool(true)        // 连接池优化
        .install_batch(Tokio)?;

    let span = tracer.start("performance-test");
    drop(span);

    Ok(())
}

/// 示例3: 仅使用企业特性扩展
#[allow(dead_code)]
async fn example_enterprise_only() -> Result<(), Box<dyn std::error::Error>> {
    use otlp::new_enhanced_pipeline_v2;

    let tracer = new_enhanced_pipeline_v2()
        .with_endpoint("http://localhost:4317")
        .with_service_name("enterprise-service")
        .with_multi_tenant(true)
        .with_tenant_id("enterprise-tenant".to_string())
        .with_compliance(true)
        .install_batch(Tokio)?;

    let span = tracer.start("enterprise-operation");
    drop(span);

    Ok(())
}

/// 示例4: 使用EnhancedExporter手动构建
#[allow(dead_code)]
async fn example_manual_exporter() -> Result<(), Box<dyn std::error::Error>> {
    use otlp::wrappers::EnhancedExporter;
    use opentelemetry_otlp::new_exporter;
    use opentelemetry_sdk::trace::TracerProviderBuilder;
    use opentelemetry_sdk::Resource;
    use opentelemetry::KeyValue;

    // 创建基础exporter
    let base_exporter = new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;

    // 使用EnhancedExporter构建器添加扩展
    let enhanced_exporter = EnhancedExporter::new()
        .with_exporter(base_exporter)
        .with_simd_optimization(true)
        .with_tracezip_compression(true)
        .with_multi_tenant(true)
        .with_tenant_id("manual-tenant".to_string())
        .build()?;

    // 构建TracerProvider
    let provider = TracerProviderBuilder::default()
        .with_batch_exporter(enhanced_exporter, Tokio)
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "manual-service"),
                ]))
        )
        .build();

    let tracer = provider.tracer("manual-tracer");
    let span = tracer.start("manual-operation");
    drop(span);

    Ok(())
}
