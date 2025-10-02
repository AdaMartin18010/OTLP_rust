//! 简单 Collector 示例

use otlp_collector::{Collector, Config, Span};
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("=== 高性能 OTLP Collector 示例 ===\n");
    
    // 创建配置
    let config = Config {
        batch_size: 100,
        batch_timeout_ms: 2000,
        buffer_capacity: 10_000,
        endpoint: "http://localhost:4317".to_string(),
        max_retries: 3,
        retry_delay_ms: 100,
    };
    
    println!("配置: {:?}\n", config);
    
    // 启动 Collector
    let collector = Collector::new(config).await?;
    println!("✅ Collector 已启动\n");
    
    // 模拟发送 spans
    println!("📊 发送 1,000 spans...");
    for i in 0..1000 {
        let span = Span::new(format!("operation-{}", i))
            .with_attribute("request.id".to_string(), otlp_collector::span::AttributeValue::Int(i as i64))
            .with_attribute("service.name".to_string(), otlp_collector::span::AttributeValue::String("demo-service".to_string()))
            .end();
        
        collector.collect(span)?;
        
        if (i + 1) % 100 == 0 {
            let stats = collector.stats();
            println!(
                "  进度: {}/1000 | 缓冲区: {}/{} ({:.1}%)",
                i + 1,
                stats.buffer_len,
                stats.buffer_capacity,
                stats.buffer_usage_percent
            );
        }
    }
    
    println!("\n✅ 所有 spans 已发送\n");
    
    // 等待处理
    println!("⏳ 等待批处理...");
    tokio::time::sleep(tokio::time::Duration::from_secs(3)).await;
    
    // 强制刷新
    println!("🔄 强制刷新剩余数据...");
    collector.flush().await?;
    
    // 显示最终统计
    let stats = collector.stats();
    println!("\n📈 最终统计:");
    println!("  缓冲区剩余: {}", stats.buffer_len);
    println!("  缓冲区容量: {}", stats.buffer_capacity);
    println!("  使用率: {:.2}%", stats.buffer_usage_percent);
    
    // 优雅关闭
    println!("\n🛑 关闭 Collector...");
    collector.shutdown().await?;
    
    println!("\n✅ 示例完成！");
    
    Ok(())
}

