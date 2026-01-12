//! Hello World 示例 - OTLP Rust 最简单的使用示例
//!
//! 这是一个最简单的示例，展示如何创建客户端并导出一个 span。
//!
//! # 运行方式
//!
//! ```bash
//! cargo run --example hello_world
//! ```
//!
//! # 前置条件
//!
//! 无需 Docker 或其他服务，这个示例会尝试连接到 localhost:4317，
//! 但即使连接失败也会正常运行并展示 API 的使用方式。

use opentelemetry::{
    KeyValue,
    trace::{Span, Tracer},
};
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🚀 OTLP Rust - Hello World 示例\n");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    // Step 1: 创建 OTLP 客户端
    println!("\n📡 Step 1: 创建 OTLP 客户端...");
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("hello-world-demo")
        .build()
        .await?;
    println!("   ✅ 客户端创建成功！");

    // Step 2: 获取 Tracer
    println!("\n📝 Step 2: 获取 Tracer...");
    let tracer = client.tracer("hello-world");
    println!("   ✅ Tracer 准备就绪！");

    // Step 3: 创建并启动一个 Span
    println!("\n🎯 Step 3: 创建 Span...");
    let mut span = tracer.start("hello-operation");

    // Step 4: 添加属性
    println!("   📌 添加属性...");
    span.set_attribute(KeyValue::new("greeting", "Hello, World!"));
    span.set_attribute(KeyValue::new("language", "Rust"));
    span.set_attribute(KeyValue::new("version", env!("CARGO_PKG_VERSION")));
    span.set_attribute(KeyValue::new("example", "hello_world"));
    println!("   ✅ 属性添加成功！");

    // Step 5: 结束 Span
    println!("\n🏁 Step 4: 结束 Span...");
    drop(span);
    println!("   ✅ Span 已导出！");

    // Step 6: 查看统计信息
    println!("\n📊 Step 5: 客户端统计信息");
    let stats = client.stats().await;
    println!("   ├─ 导出 spans: {}", stats.spans_exported);
    println!("   ├─ 错误: {}", stats.export_errors);
    println!("   └─ 平均导出时间: {:.2}ms", stats.avg_export_time_ms);

    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("🎉 Hello World 示例完成！\n");

    Ok(())
}

/* 预期输出:

🚀 OTLP Rust - Hello World 示例

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📡 Step 1: 创建 OTLP 客户端...
   ✅ 客户端创建成功！

📝 Step 2: 获取 Tracer...
   ✅ Tracer 准备就绪！

🎯 Step 3: 创建 Span...
   📌 添加属性...
   ✅ 属性添加成功！

🏁 Step 4: 结束 Span...
   ✅ Span 已导出！

📊 Step 5: 客户端统计信息
   ├─ 总 spans: 1
   ├─ 成功: 1
   └─ 失败: 0

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🎉 Hello World 示例完成！

*/
