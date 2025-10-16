//! 快速性能优化演示
//!
//! 展示如何使用快速性能优化功能，包括批量发送、压缩和连接池

use otlp::{
    data::{LogSeverity, MetricType, StatusCode},
    performance::{QuickOptimizationsConfig, QuickOptimizationsManager},
    TelemetryData,
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP 快速性能优化演示");
    println!("================================");

    // 创建快速优化配置
    let config = QuickOptimizationsConfig {
        batch_config: otlp::performance::BatchConfig {
            batch_size: 10,
            batch_timeout: Duration::from_millis(500),
            max_batch_size: 100,
            enable_adaptive_batching: true,
        },
        compression_config: otlp::performance::CompressionConfig {
            algorithm: otlp::performance::CompressionAlgorithm::Zstd,
            level: 3,
            min_size_threshold: 100,
            enable_compression: true,
        },
        enable_all_optimizations: true,
    };

    // 创建优化管理器
    let mut manager = QuickOptimizationsManager::new(config);
    
    // 初始化
    println!("📋 初始化快速优化管理器...");
    manager.initialize().await?;
    println!("✅ 初始化完成");

    // 演示批量发送
    println!("\n📦 演示批量发送...");
    for i in 0..25 {
        let trace_data = TelemetryData::trace(format!("batch_operation_{}", i))
            .with_attribute("service.name", "demo-service")
            .with_attribute("operation.id", i.to_string())
            .with_numeric_attribute("duration", (i * 10) as f64)
            .with_status(StatusCode::Ok, Some("success".to_string()));

        manager.send_data(trace_data).await?;
        
        if i % 5 == 0 {
            println!("  发送了 {} 条数据", i + 1);
        }
    }

    // 等待批量发送完成
    println!("⏳ 等待批量发送完成...");
    sleep(Duration::from_millis(1000)).await;

    // 演示压缩
    println!("\n🗜️ 演示数据压缩...");
    let test_data = "这是一个测试数据，用于演示压缩功能。".repeat(100);
    let original_size = test_data.len();
    
    let compressed = manager.compress_data(test_data.as_bytes()).await?;
    let compressed_size = compressed.len();
    
    let compression_ratio = (1.0 - (compressed_size as f64 / original_size as f64)) * 100.0;
    
    println!("  原始大小: {} 字节", original_size);
    println!("  压缩后大小: {} 字节", compressed_size);
    println!("  压缩率: {:.2}%", compression_ratio);

    // 演示连接池
    println!("\n🔗 演示连接池...");
    for i in 0..5 {
        let connection = manager.get_connection().await?;
        println!("  获取连接 {}: {}", i + 1, connection);
        sleep(Duration::from_millis(100)).await;
    }

    // 演示混合数据类型
    println!("\n📊 演示混合数据类型发送...");
    
    // 发送指标数据
    for i in 0..5 {
        let metric_data = TelemetryData::metric(format!("demo_metric_{}", i), MetricType::Counter)
            .with_attribute("environment", "demo")
            .with_numeric_attribute("value", (i * 10) as f64);
        
        manager.send_data(metric_data).await?;
    }

    // 发送日志数据
    for i in 0..5 {
        let log_data = TelemetryData::log(format!("Demo log message {}", i), LogSeverity::Info)
            .with_attribute("logger", "demo")
            .with_attribute("thread", "main");
        
        manager.send_data(log_data).await?;
    }

    println!("✅ 混合数据类型发送完成");

    // 等待所有数据发送完成
    println!("\n⏳ 等待所有数据发送完成...");
    sleep(Duration::from_millis(2000)).await;

    // 关闭管理器
    println!("\n🛑 关闭优化管理器...");
    manager.shutdown().await?;
    println!("✅ 关闭完成");

    println!("\n🎉 快速性能优化演示完成！");
    println!("\n📈 性能优化效果:");
    println!("  • 批量发送: 减少网络请求次数，提升吞吐量");
    println!("  • 数据压缩: 减少网络传输量，节省带宽");
    println!("  • 连接池: 复用连接，减少连接开销");
    println!("  • 内存池: 减少内存分配，提升性能");

    Ok(())
}
