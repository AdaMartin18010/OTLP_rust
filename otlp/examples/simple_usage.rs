//! # 简化的OTLP使用示例
//!
//! 展示如何使用简化的OTLP客户端API，降低使用复杂度。

use otlp::simple_client::{SimpleOtlpClient, SimpleClientBuilder, LogLevel, SimpleOperation};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 简化OTLP客户端示例");
    println!("📊 使用Rust 1.90新特性优化");
    println!();

    // 方式1: 使用最简单的API
    println!("📝 方式1: 最简单的API");
    let client = SimpleOtlpClient::new("http://localhost:4317").await?;
    
    // 发送追踪数据
    client.trace("simple-operation", 150, true, None::<String>).await?;
    println!("✅ 追踪数据发送成功");

    // 发送指标数据
    client.metric("request_count", 1.0, Some("count")).await?;
    println!("✅ 指标数据发送成功");

    // 发送日志数据
    client.log("Simple log message", LogLevel::Info, Some("example")).await?;
    println!("✅ 日志数据发送成功");
    println!();

    // 方式2: 使用构建器模式
    println!("📝 方式2: 构建器模式");
    let client = SimpleClientBuilder::new()
        .endpoint("http://localhost:4317")
        .service("simple-example", "1.0.0")
        .timeout(Duration::from_secs(10))
        .debug(false)
        .build()
        .await?;

    // 发送带错误信息的追踪
    client.trace("error-operation", 200, false, Some("Connection timeout")).await?;
    println!("✅ 错误追踪数据发送成功");

    // 发送不同级别的日志
    client.log("Debug message", LogLevel::Debug, Some("debug")).await?;
    client.log("Warning message", LogLevel::Warn, Some("warning")).await?;
    client.log("Error message", LogLevel::Error, Some("error")).await?;
    println!("✅ 多级别日志发送成功");
    println!();

    // 方式3: 批量发送
    println!("📝 方式3: 批量发送");
    let operations = vec![
        SimpleOperation::Trace {
            name: "batch-operation-1".to_string(),
            duration_ms: 100,
            success: true,
            error: None,
        },
        SimpleOperation::Trace {
            name: "batch-operation-2".to_string(),
            duration_ms: 250,
            success: false,
            error: Some("Network error".to_string()),
        },
        SimpleOperation::Metric {
            name: "batch_requests".to_string(),
            value: 10.0,
            unit: Some("count".to_string()),
        },
        SimpleOperation::Metric {
            name: "batch_latency".to_string(),
            value: 150.5,
            unit: Some("ms".to_string()),
        },
        SimpleOperation::Log {
            message: "Batch processing started".to_string(),
            level: LogLevel::Info,
            source: Some("batch_processor".to_string()),
        },
        SimpleOperation::Log {
            message: "Batch processing completed".to_string(),
            level: LogLevel::Info,
            source: Some("batch_processor".to_string()),
        },
    ];

    let batch_result = client.batch_send(operations).await?;
    println!("✅ 批量发送完成:");
    println!("   总发送: {} 条", batch_result.total_sent);
    println!("   成功: {} 条", batch_result.success_count);
    println!("   失败: {} 条", batch_result.failure_count);
    println!("   耗时: {:?}", batch_result.duration);
    println!();

    // 健康检查
    println!("📝 健康检查");
    let health = client.health_check().await;
    println!("   健康状态: {}", if health.is_healthy { "✅ 健康" } else { "❌ 不健康" });
    println!("   运行时间: {:?}", health.uptime);
    println!("   总请求数: {}", health.total_requests);
    println!("   成功率: {:.2}%", health.success_rate * 100.0);
    println!();

    // 等待一段时间
    println!("⏳ 等待3秒...");
    sleep(Duration::from_secs(3)).await;

    // 最终健康检查
    let final_health = client.health_check().await;
    println!("📊 最终状态:");
    println!("   运行时间: {:?}", final_health.uptime);
    println!("   总请求数: {}", final_health.total_requests);
    println!("   成功率: {:.2}%", final_health.success_rate * 100.0);
    println!();

    // 关闭客户端
    println!("🔄 关闭客户端...");
    client.shutdown().await?;
    println!("✅ 客户端已关闭");
    println!();

    println!("🎉 简化OTLP示例执行完成!");
    println!("💡 这个示例展示了:");
    println!("   • 简化的API设计，降低学习成本");
    println!("   • 构建器模式提供灵活的配置");
    println!("   • 批量发送提高效率");
    println!("   • 健康检查监控状态");
    println!("   • Rust 1.90新特性的应用");

    Ok(())
}
