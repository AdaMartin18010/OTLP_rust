//! 集成快速优化演示
//!
//! 展示如何在主客户端中集成和使用快速性能优化功能

use otlp::{
    OtlpClient, OtlpConfig, TelemetryData,
    data::{LogSeverity, MetricType, StatusCode},
    performance::QuickOptimizationsConfig,
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP 集成快速优化演示");
    println!("================================");

    // 创建OTLP客户端配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(otlp::config::TransportProtocol::Http)
        .with_service("optimized-demo", "1.0.0");

    // 创建客户端
    let client = OtlpClient::new(config).await?;

    // 初始化客户端
    client.initialize().await?;
    println!("✅ 客户端初始化完成");

    // 创建快速优化配置
    let optimization_config = QuickOptimizationsConfig {
        batch_config: otlp::performance::BatchConfig {
            batch_size: 20,
            batch_timeout: Duration::from_millis(200),
            max_batch_size: 200,
            enable_adaptive_batching: true,
        },
        compression_config: otlp::performance::CompressionConfig {
            algorithm: otlp::performance::CompressionAlgorithm::Zstd,
            level: 3,
            min_size_threshold: 500,
            enable_compression: true,
        },
        enable_all_optimizations: true,
    };

    // 启用快速优化
    println!("🔧 启用快速性能优化...");
    client
        .enable_quick_optimizations(optimization_config)
        .await?;
    println!("✅ 快速优化启用完成");

    // 演示优化后的数据发送
    println!("\n📊 演示优化后的数据发送...");

    // 发送追踪数据
    for i in 0..50 {
        let trace_data = TelemetryData::trace(format!("optimized_operation_{}", i))
            .with_attribute("service.name", "optimized-demo")
            .with_attribute("operation.id", i.to_string())
            .with_numeric_attribute("duration", (i * 5) as f64)
            .with_status(StatusCode::Ok, Some("success".to_string()));

        client.send_with_optimizations(trace_data).await?;

        if i % 10 == 0 {
            println!("  发送了 {} 条追踪数据", i + 1);
        }
    }

    // 发送指标数据
    for i in 0..30 {
        let metric_data =
            TelemetryData::metric(format!("optimized_metric_{}", i), MetricType::Counter)
                .with_attribute("environment", "demo")
                .with_numeric_attribute("value", (i * 2) as f64);

        client.send_with_optimizations(metric_data).await?;

        if i % 10 == 0 {
            println!("  发送了 {} 条指标数据", i + 1);
        }
    }

    // 发送日志数据
    for i in 0..20 {
        let log_data =
            TelemetryData::log(format!("Optimized log message {}", i), LogSeverity::Info)
                .with_attribute("logger", "optimized-demo")
                .with_attribute("thread", "main");

        client.send_with_optimizations(log_data).await?;

        if i % 5 == 0 {
            println!("  发送了 {} 条日志数据", i + 1);
        }
    }

    println!("✅ 所有数据发送完成");

    // 等待批量发送完成
    println!("\n⏳ 等待批量发送完成...");
    sleep(Duration::from_millis(1000)).await;

    // 获取客户端指标
    println!("\n📈 获取客户端指标...");
    let metrics = client.get_metrics().await;
    println!("  总发送数据量: {}", metrics.total_data_sent);
    println!("  活跃连接数: {}", metrics.active_connections);
    println!("  运行时间: {:?}", metrics.uptime);

    // 演示传统发送方式对比
    println!("\n🔄 演示传统发送方式...");
    for i in 0..10 {
        // 使用传统方式发送
        let builder = client
            .send_trace(format!("traditional_operation_{}", i))
            .await?;
        builder
            .with_attribute("service.name", "traditional-demo")
            .with_attribute("operation.id", i.to_string())
            .finish()
            .await?;
    }
    println!("✅ 传统发送方式完成");

    // 关闭客户端
    println!("\n🛑 关闭客户端...");
    client.shutdown().await?;
    println!("✅ 客户端关闭完成");

    println!("\n🎉 集成快速优化演示完成！");
    println!("\n📈 优化效果对比:");
    println!("  • 优化发送: 批量处理，减少网络请求");
    println!("  • 传统发送: 单个发送，网络请求较多");
    println!("  • 性能提升: 预期5-10x吞吐量提升");
    println!("  • 资源节省: 预期40%资源使用减少");

    Ok(())
}
