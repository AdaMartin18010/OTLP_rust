//! # OTLP示例程序
//!
//! 演示如何使用OTLP客户端发送遥测数据

use otlp::config::TransportProtocol;
use otlp::data::{
    LogSeverity,
    StatusCode,
    //SpanKind,
};
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP客户端示例程序启动");
    println!("📊 使用Rust 1.90语言特性实现");
    println!("🔗 支持gRPC和HTTP两种传输协议");
    println!("⚡ 异步优先设计，支持高并发处理");
    println!();

    // 创建OTLP配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("otlp-example", "1.0.0")
        .with_request_timeout(Duration::from_secs(10))
        .with_debug(true);

    println!("⚙️  配置信息:");
    println!("   端点: {}", config.endpoint);
    println!("   协议: {}", config.protocol);
    println!(
        "   服务: {} v{}",
        config.service.name, config.service.version
    );
    println!("   超时: {:?}", config.request_timeout);
    println!();

    // 创建OTLP客户端
    println!("🔧 创建OTLP客户端...");
    let client = OtlpClient::new(config).await?;

    // 初始化客户端
    println!("🚀 初始化客户端...");
    client.initialize().await?;
    println!("✅ 客户端初始化完成");
    println!();

    // 示例1: 发送追踪数据
    println!("📈 示例1: 发送追踪数据");
    let trace_result = client
        .send_trace("example-operation")
        .await?
        .with_attribute("service.name", "otlp-example")
        .with_attribute("service.version", "1.0.0")
        .with_attribute("environment", "development")
        .with_numeric_attribute("duration", 150.0)
        .with_bool_attribute("success", true)
        .with_status(StatusCode::Ok, Some("操作成功".to_string()))
        .finish()
        .await?;

    println!(
        "   追踪数据发送结果: 成功 {} 条, 失败 {} 条",
        trace_result.success_count, trace_result.failure_count
    );
    println!();

    // 示例2: 发送指标数据
    println!("📊 示例2: 发送指标数据");
    let metric_result = client
        .send_metric("request_count", 1.0)
        .await?
        .with_label("method", "GET")
        .with_label("endpoint", "/api/health")
        .with_label("status", "200")
        .with_description("HTTP请求计数")
        .with_unit("count")
        .send()
        .await?;

    println!(
        "   指标数据发送结果: 成功 {} 条, 失败 {} 条",
        metric_result.success_count, metric_result.failure_count
    );
    println!();

    // 示例3: 发送日志数据
    println!("📝 示例3: 发送日志数据");
    let log_result = client
        .send_log("用户登录成功", LogSeverity::Info)
        .await?
        .with_attribute("user_id", "12345")
        .with_attribute("ip_address", "192.168.1.100")
        .with_numeric_attribute("login_time", 1640995200.0)
        .with_bool_attribute("is_admin", false)
        .with_trace_context("trace-123", "span-456")
        .send()
        .await?;

    println!(
        "   日志数据发送结果: 成功 {} 条, 失败 {} 条",
        log_result.success_count, log_result.failure_count
    );
    println!();

    // 示例4: 批量发送数据
    println!("📦 示例4: 批量发送数据");
    let mut batch_data = Vec::new();

    for i in 0..5 {
        let trace_data = TelemetryData::trace(format!("batch-operation-{}", i))
            .with_attribute("batch_id", "batch-001")
            .with_attribute("operation_index", i.to_string())
            .with_numeric_attribute("processing_time", (i * 10) as f64);

        batch_data.push(trace_data);
    }

    let batch_result = client.send_batch(batch_data).await?;
    println!(
        "   批量数据发送结果: 成功 {} 条, 失败 {} 条",
        batch_result.success_count, batch_result.failure_count
    );
    println!();

    // 示例5: 异步发送数据
    println!("⚡ 示例5: 异步发送数据");
    let mut futures = Vec::new();

    for i in 0..10 {
        let client_clone = client.clone();
        let future = tokio::spawn(async move {
            let result = client_clone
                .send_trace(format!("async-operation-{}", i))
                .await?
                .with_attribute("async", "true")
                .with_attribute("worker_id", i.to_string())
                .finish()
                .await?;
            Ok::<_, Box<dyn std::error::Error + Send + Sync>>(result)
        });
        futures.push(future);
    }

    let mut success_count = 0;
    let mut failure_count = 0;

    for future in futures {
        match future.await? {
            Ok(result) => {
                success_count += result.success_count;
                failure_count += result.failure_count;
            }
            Err(e) => {
                println!("   异步操作失败: {}", e);
                failure_count += 1;
            }
        }
    }

    println!(
        "   异步数据发送结果: 成功 {} 条, 失败 {} 条",
        success_count, failure_count
    );
    println!();

    // 获取客户端指标
    println!("📊 客户端指标:");
    let metrics = client.get_metrics().await;
    println!("   总发送数据量: {}", metrics.total_data_sent);
    println!("   总接收数据量: {}", metrics.total_data_received);
    println!("   运行时间: {:?}", metrics.uptime);
    println!("   导出器指标:");
    println!(
        "     总导出次数: {}",
        metrics.exporter_metrics.total_exports
    );
    println!(
        "     成功导出次数: {}",
        metrics.exporter_metrics.successful_exports
    );
    println!(
        "     失败导出次数: {}",
        metrics.exporter_metrics.failed_exports
    );
    println!(
        "     平均导出延迟: {:?}",
        metrics.exporter_metrics.average_export_latency
    );
    println!();

    // 等待一段时间以观察指标更新
    println!("⏳ 等待5秒以观察指标更新...");
    sleep(Duration::from_secs(5)).await;

    let final_metrics = client.get_metrics().await;
    println!("📊 最终指标:");
    println!("   总运行时间: {:?}", final_metrics.uptime);
    println!("   总发送数据量: {}", final_metrics.total_data_sent);
    println!();

    // 关闭客户端
    println!("🔄 关闭客户端...");
    client.shutdown().await?;
    println!("✅ 客户端已关闭");
    println!();

    println!("🎉 OTLP示例程序执行完成!");
    println!("💡 这个示例展示了:");
    println!("   • Rust 1.90的异步编程特性");
    println!("   • OTLP协议的完整实现");
    println!("   • 同步和异步结合的OTLP设计模式");
    println!("   • 高性能的遥测数据收集和传输");
    println!("   • 类型安全的API设计");
    println!("   • 完整的错误处理和重试机制");

    Ok(())
}
