//! 集成测试 - 验证与 OpenTelemetry Collector 的互操作性
//!
//! # 运行前准备
//!
//! 1. 启动 Docker Compose 环境:
//!    ```bash
//!    cd otlp/tests/integration
//!    docker-compose up -d
//!    ```
//!
//! 2. 运行测试:
//!    ```bash
//!    cargo test --test integration_test -- --ignored --nocapture
//!    ```
//!
//! 3. 查看结果:
//!    打开 http://localhost:16686 (Jaeger UI)

use otlp::core::EnhancedOtlpClient;
use opentelemetry::{
    trace::{Tracer, Status},
    KeyValue,
};
use std::time::Duration;

/// 测试基本的 span 导出
#[tokio::test]
#[ignore] // 默认跳过，需要手动运行
async fn test_basic_span_export() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 基本 Span 导出");
    println!("=" .repeat(50));
    
    // 创建客户端
    println!("📝 创建客户端...");
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-basic")
        .with_timeout(Duration::from_secs(10))
        .build()
        .await?;
    
    println!("✅ 客户端创建成功");
    
    // 获取 tracer
    let tracer = client.tracer("test-tracer");
    
    // 创建 span
    println!("📝 创建 Span...");
    let span = tracer.start("test-operation");
    
    // 模拟工作
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    drop(span);
    println!("✅ Span 已创建和结束");
    
    // 等待导出
    println!("⏳ 等待导出...");
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 检查统计
    let stats = client.stats().await;
    println!("\n📊 客户端统计:");
    println!("  - 导出的 spans: {}", stats.spans_exported);
    println!("  - 导出错误: {}", stats.export_errors);
    println!("  - 平均导出时间: {}ms", stats.avg_export_time_ms);
    
    // 关闭客户端
    println!("\n📝 关闭客户端...");
    client.shutdown().await?;
    
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 测试嵌套 spans
#[tokio::test]
#[ignore]
async fn test_nested_spans() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 嵌套 Spans");
    println!("=" .repeat(50));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-nested")
        .build()
        .await?;
    
    let tracer = client.tracer("nested-tracer");
    
    println!("📝 创建父 Span...");
    let parent = tracer.start("parent-operation");
    
    // 子 spans
    for i in 0..3 {
        println!("📝 创建子 Span {}...", i);
        let child = tracer.start(format!("child-operation-{}", i));
        tokio::time::sleep(Duration::from_millis(50)).await;
        drop(child);
    }
    
    drop(parent);
    println!("✅ 所有 Spans 创建完成");
    
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    let stats = client.stats().await;
    println!("\n📊 导出的 spans: {}", stats.spans_exported);
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 测试 span 属性和事件
#[tokio::test]
#[ignore]
async fn test_span_attributes_and_events() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: Span 属性和事件");
    println!("=" .repeat(50));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-attributes")
        .build()
        .await?;
    
    let tracer = client.tracer("attributes-tracer");
    let mut span = tracer.start("operation-with-attributes");
    
    // 添加属性
    println!("📝 添加属性...");
    span.set_attribute(KeyValue::new("user.id", "12345"));
    span.set_attribute(KeyValue::new("request.method", "GET"));
    span.set_attribute(KeyValue::new("response.status", 200));
    println!("✅ 已添加 3 个属性");
    
    // 添加事件
    println!("📝 添加事件...");
    span.add_event("Processing started", vec![
        KeyValue::new("item.count", 10),
        KeyValue::new("batch.size", 100),
    ]);
    
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    span.add_event("Processing completed", vec![
        KeyValue::new("items.processed", 10),
    ]);
    println!("✅ 已添加 2 个事件");
    
    // 设置状态
    span.set_status(Status::Ok);
    
    drop(span);
    
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 测试并发 spans
#[tokio::test]
#[ignore]
async fn test_concurrent_spans() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 并发 Spans (10个任务)");
    println!("=" .repeat(50));
    
    use std::sync::Arc;
    
    let client = Arc::new(
        EnhancedOtlpClient::builder()
            .with_endpoint("http://localhost:4317")
            .with_service_name("integration-test-concurrent")
            .build()
            .await?
    );
    
    let mut handles = vec![];
    
    // 创建 10 个并发任务
    println!("📝 启动 10 个并发任务...");
    for i in 0..10 {
        let client_clone = Arc::clone(&client);
        let handle = tokio::spawn(async move {
            let tracer = client_clone.tracer(format!("worker-{}", i));
            let span = tracer.start(format!("concurrent-task-{}", i));
            
            tokio::time::sleep(Duration::from_millis(100)).await;
            
            drop(span);
        });
        
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for (i, handle) in handles.into_iter().enumerate() {
        handle.await?;
        println!("✅ 任务 {} 完成", i);
    }
    
    println!("✅ 所有并发任务完成");
    
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    let stats = client.stats().await;
    println!("\n📊 总共导出 {} 个 spans", stats.spans_exported);
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 测试错误处理
#[tokio::test]
#[ignore]
async fn test_error_handling() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 错误处理");
    println!("=" .repeat(50));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-error")
        .build()
        .await?;
    
    let tracer = client.tracer("error-tracer");
    let mut span = tracer.start("operation-with-error");
    
    // 模拟错误
    println!("📝 记录错误信息...");
    span.set_attribute(KeyValue::new("error.type", "DatabaseError"));
    span.set_attribute(KeyValue::new("error.message", "Connection timeout"));
    span.set_status(Status::error("Database connection failed"));
    println!("✅ 错误信息已记录");
    
    drop(span);
    
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 性能测试 - 大量 spans
#[tokio::test]
#[ignore]
async fn test_high_volume_spans() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 高容量 Spans (1000个)");
    println!("=" .repeat(50));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-volume")
        .with_performance_optimization(true)
        .build()
        .await?;
    
    let tracer = client.tracer("volume-tracer");
    
    let start = std::time::Instant::now();
    
    // 创建 1000 个 spans
    println!("📝 创建 1000 个 Spans...");
    for i in 0..1000 {
        let span = tracer.start(format!("span-{}", i));
        drop(span);
        
        if (i + 1) % 100 == 0 {
            print!(".");
            std::io::Write::flush(&mut std::io::stdout()).ok();
        }
    }
    
    let duration = start.elapsed();
    println!("\n✅ 创建 1000 个 spans 耗时: {:?}", duration);
    println!("📊 平均每个 span: {:?}", duration / 1000);
    
    println!("⏳ 等待导出...");
    tokio::time::sleep(Duration::from_secs(5)).await;
    
    let stats = client.stats().await;
    println!("\n📊 最终统计:");
    println!("  - 导出的 spans: {}", stats.spans_exported);
    println!("  - 导出错误: {}", stats.export_errors);
    println!("  - 平均导出时间: {}ms", stats.avg_export_time_ms);
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}

/// 测试客户端配置
#[tokio::test]
#[ignore]
async fn test_client_configuration() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 测试: 客户端配置");
    println!("=" .repeat(50));
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("integration-test-config")
        .with_timeout(Duration::from_secs(30))
        .with_performance_optimization(true)
        .with_reliability_enhancement(true)
        .build()
        .await?;
    
    // 获取配置
    let config = client.config();
    
    println!("📊 客户端配置:");
    println!("  - 端点: {}", config.endpoint);
    println!("  - 服务名: {}", config.service_name);
    println!("  - 超时: {:?}", config.timeout);
    println!("  - 协议: {:?}", config.protocol);
    println!("  - 性能优化: {}", config.enable_performance);
    println!("  - 可靠性增强: {}", config.enable_reliability);
    
    assert_eq!(config.endpoint, "http://localhost:4317");
    assert_eq!(config.service_name, "integration-test-config");
    assert_eq!(config.timeout, Duration::from_secs(30));
    assert!(config.enable_performance);
    assert!(config.enable_reliability);
    
    println!("✅ 配置验证通过");
    
    client.shutdown().await?;
    println!("✅ 测试完成\n");
    
    Ok(())
}
