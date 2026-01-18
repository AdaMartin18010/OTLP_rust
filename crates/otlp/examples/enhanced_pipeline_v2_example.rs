//! # 增强Pipeline V2使用示例
//!
//! 本示例展示如何使用EnhancedPipelineV2创建配置了所有扩展功能的Pipeline。
//!
//! 注意: 由于 opentelemetry_sdk 0.31 的 API 变化，示例暂时注释。
//! 主要变化包括：
//! - `opentelemetry_otlp::new_exporter` API可能改变
//! - `Runtime` 可能需要具体类型而不是trait
//! - `Tracer` 和 `SpanExporter` 不再是 dyn 兼容的
//! - `TracerProviderBuilder` API可能改变
//!
//! 示例需要根据新的 API 重新实现。

// 注意: 示例暂时注释，等待API稳定或需要根据新的API重新实现
// use opentelemetry::trace::Tracer;
// use opentelemetry_sdk::runtime::Tokio;

/// 示例1: 完整配置的增强Pipeline
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 注意: 此示例需要根据opentelemetry_sdk 0.31的新API重新实现
    // EnhancedPipelineV2::install_batch() 当前返回错误，因为需要重新设计
    // 以支持非dyn兼容的SpanExporter和Tracer

    println!("此示例需要根据 opentelemetry_sdk 0.31 的新 API 重新实现");
    println!("请参考文档了解如何使用新的 API");
    Ok(())
}

// 以下示例暂时注释，需要根据opentelemetry_sdk 0.31的新API重新实现

// /// 示例2: 仅使用性能优化扩展
// #[allow(dead_code)]
// async fn example_performance_only() -> Result<(), Box<dyn std::error::Error>> {
//     // 需要根据新的API重新实现
//     Ok(())
// }

// /// 示例3: 仅使用企业特性扩展
// #[allow(dead_code)]
// async fn example_enterprise_only() -> Result<(), Box<dyn std::error::Error>> {
//     // 需要根据新的API重新实现
//     Ok(())
// }

// /// 示例4: 使用EnhancedExporter手动构建
// #[allow(dead_code)]
// async fn example_manual_exporter() -> Result<(), Box<dyn std::error::Error>> {
//     // 注意: opentelemetry_otlp::new_exporter API在v0.31中可能已经改变
//     // TracerProviderBuilder API也可能改变
//     // EnhancedExporter::build() 当前返回错误，因为SpanExporter不是dyn兼容的
//     // 需要重新设计以使用泛型而不是Box<dyn>
//     Ok(())
// }
