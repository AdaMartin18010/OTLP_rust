//! 微服务追踪示例
//!
//! 演示如何在微服务架构中使用 OTLP 进行分布式追踪

use otlp::profiling::{CpuProfiler, ProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("微服务追踪示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 模拟微服务调用链
    println!("模拟微服务调用链:");
    println!();

    // 服务A: API Gateway
    println!("1. API Gateway (服务A)");
    let _ = simulate_service("api-gateway", Duration::from_millis(50)).await;
    println!();

    // 服务B: User Service
    println!("2. User Service (服务B)");
    let _ = simulate_service("user-service", Duration::from_millis(30)).await;
    println!();

    // 服务C: Order Service
    println!("3. Order Service (服务C)");
    let _ = simulate_service("order-service", Duration::from_millis(40)).await;
    println!();

    // 服务D: Payment Service
    println!("4. Payment Service (服务D)");
    let _ = simulate_service("payment-service", Duration::from_millis(20)).await;
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("调用链完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}

async fn simulate_service(service_name: &str, duration: Duration) -> Result<(), Box<dyn std::error::Error>> {
    println!("   📍 服务: {}", service_name);
    
    // 创建 Profiler
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    
    // 启动性能分析
    profiler.start().await?;
    println!("   ✅ 性能分析启动");
    
    // 模拟服务处理
    tokio::time::sleep(duration).await;
    
    // 停止并获取 Profile
    let profile = profiler.stop().await?;
    println!("   ✅ 处理完成");
    println!("   - 样本数: {}", profile.samples.len());
    
    // 在实际场景中，这里会将 Profile 导出到 OTLP Collector
    // let exporter = ProfilesExporter::new("http://otel-collector:4317".to_string());
    // exporter.export(&profile).await?;
    
    Ok(())
}
