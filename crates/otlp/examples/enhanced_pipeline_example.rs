//! # 增强Pipeline使用示例
//!
//! 本示例展示如何使用基于官方 `opentelemetry-rust` 的增强Pipeline。
//!
//! 注意: 由于 opentelemetry_sdk 0.31 的 API 变化，示例暂时注释。
//! 主要变化包括：
//! - `opentelemetry_otlp::new_pipeline` 和 `new_exporter` API可能改变
//! - `opentelemetry_sdk::export::trace` → `opentelemetry_sdk::trace`
//! - `NoopSpanExporter` 路径可能不同或不存在
//! - `Runtime` 可能需要具体类型而不是trait
//! - `Tracer` 和 `SpanExporter` 不再是 dyn 兼容的
//!
//! 示例需要根据新的 API 重新实现。

// 注意: 示例暂时注释，等待API稳定或需要根据新的API重新实现
// use opentelemetry::trace::Tracer;
// use opentelemetry_sdk::runtime::Tokio;

/// 示例1: 使用增强Pipeline的基础用法
// #[tokio::main]
// async fn main() -> Result<(), Box<dyn std::error::Error>> {
//     // 注意: 此示例需要根据opentelemetry_sdk 0.31的新API重新实现
//     // 主要变化：
//     // 1. `install_batch` 返回类型可能改变（Tracer不是dyn兼容的）
//     // 2. Runtime可能需要具体类型
//
//     // use otlp::new_enhanced_pipeline;
//     // let tracer = new_enhanced_pipeline()
//     //     .with_ebpf_profiling(true)
//     //     .with_simd_optimization(true)
//     //     .with_tracezip_compression(true)
//     //     .with_multi_tenant(true)
//     //     .with_tenant_id("tenant-123".to_string())
//     //     .with_compliance(true)
//     //     .with_batch_optimization(true)
//     //     .with_connection_pool(true)
//     //     .install_batch(Tokio)?;
//
//     // let span = tracer.start("my-operation");
//     // span.set_attribute("key".into(), "value".into());
//     // drop(span);
//
//     Ok(())
// }

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("此示例需要根据 opentelemetry_sdk 0.31 的新 API 重新实现");
    println!("请参考文档了解如何使用新的 API");
    Ok(())
}

// 以下示例暂时注释，需要根据opentelemetry_sdk 0.31的新API重新实现

// /// 示例2: 仅使用官方API（完全兼容）
// #[allow(dead_code)]
// async fn example_official_api() -> Result<(), Box<dyn std::error::Error>> {
//     // 注意: opentelemetry_otlp的API在v0.31中可能已经改变
//     // use opentelemetry_otlp::new_pipeline;
//     Ok(())
// }

// /// 示例3: 逐步添加扩展
// #[allow(dead_code)]
// async fn example_gradual_extension() -> Result<(), Box<dyn std::error::Error>> {
//     // 需要根据新的API重新实现
//     Ok(())
// }

// /// 示例4: 使用EnhancedExporter构建器
// #[allow(dead_code)]
// async fn example_enhanced_exporter() -> Result<(), Box<dyn std::error::Error>> {
//     // 注意: EnhancedExporter::build() 当前返回错误，因为SpanExporter不是dyn兼容的
//     // 需要重新设计以使用泛型而不是Box<dyn>
//     Ok(())
// }
