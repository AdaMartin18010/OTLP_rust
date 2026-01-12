//! 嵌套 Spans 示例
//!
//! 展示如何创建嵌套的 spans 来追踪复杂的操作流程。
//!
//! # 运行方式
//!
//! ```bash
//! cargo run --example nested_spans
//! ```

use opentelemetry::{
    KeyValue,
    trace::{Span, Tracer},
};
use otlp::core::EnhancedOtlpClient;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🌳 OTLP Rust - 嵌套 Spans 示例\n");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    // 创建客户端
    println!("\n📡 创建 OTLP 客户端...");
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("nested-spans-demo")
        .build()
        .await?;
    println!("   ✅ 客户端创建成功！");

    let tracer = client.tracer("nested-spans-example");

    // 根 Span
    println!("\n🎯 创建根 Span: 'process-order'");
    let mut root_span = tracer.start("process-order");
    root_span.set_attribute(KeyValue::new("order.id", "ORDER-12345"));
    root_span.set_attribute(KeyValue::new("order.total", 150.50));

    // 子 Span 1: 验证订单
    println!("   ├─ 子 Span: 'validate-order'");
    {
        let mut validate_span = tracer.start("validate-order");
        validate_span.set_attribute(KeyValue::new("validation.type", "standard"));
        sleep(Duration::from_millis(100)).await;
        println!("      ✅ 订单验证完成");
        drop(validate_span);
    }

    // 子 Span 2: 检查库存
    println!("   ├─ 子 Span: 'check-inventory'");
    {
        let mut inventory_span = tracer.start("check-inventory");
        inventory_span.set_attribute(KeyValue::new("items.count", 3));

        // 子子 Span: 检查每个商品
        for i in 1..=3 {
            let mut item_span = tracer.start(format!("check-item-{}", i));
            item_span.set_attribute(KeyValue::new("item.id", format!("ITEM-{}", i)));
            item_span.set_attribute(KeyValue::new("item.available", true));
            sleep(Duration::from_millis(50)).await;
            println!("      │  └─ 商品 {} 检查完成", i);
            drop(item_span);
        }

        println!("      ✅ 库存检查完成");
        drop(inventory_span);
    }

    // 子 Span 3: 计算运费
    println!("   ├─ 子 Span: 'calculate-shipping'");
    {
        let mut shipping_span = tracer.start("calculate-shipping");
        shipping_span.set_attribute(KeyValue::new("shipping.method", "express"));
        shipping_span.set_attribute(KeyValue::new("shipping.cost", 15.00));
        sleep(Duration::from_millis(80)).await;
        println!("      ✅ 运费计算完成");
        drop(shipping_span);
    }

    // 子 Span 4: 处理支付
    println!("   └─ 子 Span: 'process-payment'");
    {
        let mut payment_span = tracer.start("process-payment");
        payment_span.set_attribute(KeyValue::new("payment.method", "credit_card"));
        payment_span.set_attribute(KeyValue::new("payment.amount", 165.50));

        // 子子 Span: 验证支付
        {
            let mut verify_span = tracer.start("verify-payment");
            verify_span.set_attribute(KeyValue::new("verification.status", "approved"));
            sleep(Duration::from_millis(120)).await;
            println!("      └─ 支付验证完成");
            drop(verify_span);
        }

        println!("      ✅ 支付处理完成");
        drop(payment_span);
    }

    // 结束根 Span
    root_span.set_attribute(KeyValue::new("order.status", "completed"));
    println!("\n✅ 订单处理完成！");
    drop(root_span);

    // 显示统计信息
    println!("\n📊 统计信息:");
    let stats = client.stats().await;
    println!(
        "   ├─ 导出 spans: {} (1 root + 6 children)",
        stats.spans_exported
    );
    println!("   ├─ 错误: {}", stats.export_errors);
    println!("   └─ 平均导出时间: {:.2}ms", stats.avg_export_time_ms);

    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("🎉 嵌套 Spans 示例完成！\n");

    Ok(())
}

/* 预期的 Span 层级结构:

process-order (root)
├── validate-order
├── check-inventory
│   ├── check-item-1
│   ├── check-item-2
│   └── check-item-3
├── calculate-shipping
└── process-payment
    └── verify-payment

在 Jaeger UI 中，你将看到这个完整的追踪树。
*/
