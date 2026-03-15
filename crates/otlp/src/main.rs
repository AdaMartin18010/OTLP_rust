//! # OTLP 示例程序
//!
//! 演示如何使用 OTLP 客户端发送遥测数据

#![allow(clippy::excessive_nesting)]

use otlp::client::OtlpClientBuilder;
use otlp::config::TransportProtocol;

use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP 客户端示例程序启动");

    // 使用构建器创建客户端
    let client = OtlpClientBuilder::new()
        .endpoint("http://localhost:4317")
        .protocol(TransportProtocol::Grpc)
        .timeout(Duration::from_secs(5))
        .service("example-service", "1.0.0")
        .with_attribute("environment", "demo")
        .build()
        .await?;

    // 初始化客户端
    client.initialize().await?;
    println!("✅ 客户端初始化完成");

    // 发送追踪数据
    let _trace = client
        .send_trace("user-operation")
        .await?
        .with_attribute("user_id", "12345")
        .with_duration(150)
        .finish()
        .await?;
    println!("📊 追踪数据已发送");

    // 发送指标数据
    let _metric = client
        .send_metric("request_count", 1.0)
        .await?
        .with_label("endpoint", "/api/users")
        .with_description("请求计数")
        .send()
        .await?;
    println!("📈 指标数据已发送");

    // 发送日志数据
    let _log = client
        .send_log("用户登录成功")
        .await?
        .with_attribute("user_id", "12345")
        .send()
        .await?;
    println!("📝 日志数据已发送");

    // 关闭客户端
    client.shutdown().await?;
    println!("👋 客户端已关闭");

    Ok(())
}
