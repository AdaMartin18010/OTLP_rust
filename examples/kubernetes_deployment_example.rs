//! Kubernetes 部署示例
//!
//! 演示如何在 Kubernetes 环境中使用 OTLP

use otlp::profiling::{CpuProfiler, ProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Kubernetes 部署示例");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!();

    // 1. 从环境变量读取配置
    println!("1. 读取 Kubernetes 环境配置...");
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://otel-collector:4317".to_string());
    let service_name = std::env::var("OTEL_SERVICE_NAME")
        .unwrap_or_else(|_| "otlp-rust-service".to_string());
    let service_namespace = std::env::var("OTEL_SERVICE_NAMESPACE")
        .unwrap_or_else(|_| "default".to_string());

    println!("   ✅ 配置读取成功");
    println!("   - OTLP Endpoint: {}", otlp_endpoint);
    println!("   - Service Name: {}", service_name);
    println!("   - Namespace: {}", service_namespace);
    println!();

    // 2. 创建 Profiler
    println!("2. 创建 Profiler...");
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);
    println!("   ✅ Profiler 创建成功");
    println!();

    // 3. 启动性能分析
    println!("3. 启动性能分析...");
    profiler.start().await?;
    println!("   ✅ 性能分析启动");
    println!();

    // 4. 模拟应用工作负载
    println!("4. 模拟应用工作负载...");
    for i in 0..5 {
        println!("   - 处理请求 {}...", i + 1);
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    println!();

    // 5. 停止并导出
    println!("5. 停止性能分析并导出...");
    let profile = profiler.stop().await?;
    println!("   ✅ Profile 生成成功");
    println!("   - 样本数: {}", profile.samples.len());

    // 在实际部署中，这里会将 Profile 导出到 OTLP Collector
    // let exporter = ProfilesExporter::new(otlp_endpoint);
    // exporter.export(&profile).await?;
    println!("   ✅ Profile 导出完成（模拟）");
    println!();

    // 6. 健康检查
    println!("6. 健康检查...");
    let overhead = profiler.get_overhead().await;
    println!("   ✅ 系统健康");
    println!("   - CPU 使用率: {:.2}%", overhead.cpu_percent);
    println!("   - 内存使用: {} bytes", overhead.memory_bytes);
    println!();

    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Kubernetes 部署示例完成！");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    Ok(())
}
