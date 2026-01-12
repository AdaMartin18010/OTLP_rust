//! 增强客户端使用示例
//!
//! 演示如何使用基于 opentelemetry-otlp 的增强客户端

// 注意: 这需要在 otlp/src/lib.rs 中添加 pub mod core;
// 和正确的依赖配置后才能编译

/// 基本使用示例
async fn basic_usage_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 基本使用示例 ===\n");

    // 创建基于官方 opentelemetry-otlp 的增强客户端
    println!("创建 Enhanced OTLP Client...");

    /*
    // 取消注释以运行 (需要先完成 lib.rs 集成)
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("demo-service")
        .with_timeout(Duration::from_secs(10))
        .with_performance_optimization(true)
        .with_resilience_enabled(true)
        .build()
        .await?;

    println!("✅ 客户端创建成功\n");

    // 使用标准 OpenTelemetry API
    let tracer = client.tracer("demo-component");

    // 创建 span
    println!("创建 span...");
    let span = tracer.start("demo-operation");

    // 模拟业务逻辑
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Span 自动结束
    drop(span);
    println!("✅ Span 已结束\n");

    // 查看统计
    let stats = client.stats().await;
    println!("客户端统计:");
    println!("  - 导出的 spans: {}", stats.spans_exported);
    println!("  - 导出错误: {}", stats.export_errors);
    println!("  - 平均导出时间: {}ms", stats.avg_export_time_ms);

    // 正确关闭客户端
    client.shutdown().await?;
    println!("\n✅ 客户端已关闭");
    */

    println!("(示例代码待集成后运行)");

    Ok(())
}

/// 高级配置示例
async fn advanced_configuration_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 高级配置示例 ===\n");

    /*
    // 自定义配置
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("https://api.example.com:4317")
        .with_service_name("production-service")
        .with_timeout(Duration::from_secs(30))
        .with_protocol(Protocol::Grpc)
        .with_performance_optimization(true)
        .with_resilience_enabled(true)
        .with_global_provider(true)  // 设置为全局 provider
        .build()
        .await?;

    println!("✅ 高级配置客户端创建成功");

    // 获取配置信息
    let config = client.config();
    println!("配置信息:");
    println!("  - 端点: {}", config.endpoint);
    println!("  - 服务名: {}", config.service_name);
    println!("  - 超时: {:?}", config.timeout);
    println!("  - 性能优化: {}", config.enable_performance);
    println!("  - 可靠性增强: {}", config.enable_reliability);
    */

    println!("(示例代码待集成后运行)");

    Ok(())
}

/// 并发使用示例
async fn concurrent_usage_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 并发使用示例 ===\n");

    /*
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("concurrent-service")
        .build()
        .await?;

    // EnhancedOtlpClient 支持 Clone，可以在多个任务中使用
    let mut tasks = vec![];

    for i in 0..5 {
        let client_clone = client.clone();
        let task = tokio::spawn(async move {
            let tracer = client_clone.tracer(format!("worker-{}", i));
            let span = tracer.start(format!("task-{}", i));

            // 模拟工作
            tokio::time::sleep(Duration::from_millis(50)).await;

            drop(span);
        });

        tasks.push(task);
    }

    // 等待所有任务完成
    for task in tasks {
        task.await?;
    }

    println!("✅ 所有并发任务完成");

    // 查看统计
    let stats = client.stats().await;
    println!("总共导出 {} 个 spans", stats.spans_exported);

    client.shutdown().await?;
    */

    println!("(示例代码待集成后运行)");

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🚀 Enhanced OTLP Client 示例\n");
    println!("基于 opentelemetry-otlp 0.31.0 的增强实现\n");
    println!("{}", "=".repeat(50));

    // 运行示例
    basic_usage_example().await?;
    advanced_configuration_example().await?;
    concurrent_usage_example().await?;

    println!("\n{}", "=".repeat(50));
    println!("\n✨ 所有示例执行完成!\n");

    println!("📝 注意:");
    println!("  1. 示例需要运行 OpenTelemetry Collector");
    println!("  2. 默认端点: http://localhost:4317");
    println!("  3. 使用 docker 启动 Collector:");
    println!("     docker run -p 4317:4317 otel/opentelemetry-collector\n");

    Ok(())
}
