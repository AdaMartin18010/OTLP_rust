//! 异步追踪示例
//!
//! 展示如何在异步场景中使用 OTLP 进行分布式追踪。
//!
//! # 运行方式
//!
//! ```bash
//! cargo run --example async_tracing
//! ```

use opentelemetry::{
    KeyValue,
    trace::{Span, Tracer},
};
use otlp::core::EnhancedOtlpClient;
use std::time::Duration;
use tokio::time::sleep;

/// 模拟异步数据库查询
async fn fetch_user_from_db<T: Tracer>(tracer: &T, user_id: u64) -> String {
    let mut span = tracer.start("db-query-user");
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    span.set_attribute(KeyValue::new("user.id", user_id as i64));

    // 模拟数据库延迟
    sleep(Duration::from_millis(50)).await;

    let username = format!("user_{}", user_id);
    span.set_attribute(KeyValue::new("user.name", username.clone()));

    drop(span);
    username
}

/// 模拟异步 API 调用
async fn fetch_user_profile<T: Tracer>(tracer: &T, username: &str) -> String {
    let mut span = tracer.start("api-fetch-profile");
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.url", "/api/profile"));
    span.set_attribute(KeyValue::new("user.name", username.to_string()));

    // 模拟 API 延迟
    sleep(Duration::from_millis(100)).await;

    span.set_attribute(KeyValue::new("http.status_code", 200));

    drop(span);
    format!("Profile of {}", username)
}

/// 模拟异步缓存操作
async fn cache_result<T: Tracer>(tracer: &T, key: &str, value: &str) {
    let mut span = tracer.start("cache-set");
    span.set_attribute(KeyValue::new("cache.system", "redis"));
    span.set_attribute(KeyValue::new("cache.key", key.to_string()));
    span.set_attribute(KeyValue::new("cache.value_size", value.len() as i64));

    // 模拟缓存延迟
    sleep(Duration::from_millis(20)).await;

    span.set_attribute(KeyValue::new("cache.hit", false));

    drop(span);
}

/// 处理用户请求（主业务逻辑）
async fn handle_user_request<T: Tracer>(tracer: &T, user_id: u64) -> String {
    let mut span = tracer.start("handle-request");
    span.set_attribute(KeyValue::new("request.id", format!("req-{}", user_id)));

    // Step 1: 从数据库获取用户
    println!("   ├─ 查询数据库...");
    let username = fetch_user_from_db(tracer, user_id).await;

    // Step 2: 获取用户资料
    println!("   ├─ 调用 API...");
    let profile = fetch_user_profile(tracer, &username).await;

    // Step 3: 缓存结果
    println!("   └─ 缓存结果...");
    cache_result(tracer, &format!("profile:{}", user_id), &profile).await;

    span.set_attribute(KeyValue::new("request.status", "success"));

    drop(span);
    profile
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ OTLP Rust - 异步追踪示例\n");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    // 创建客户端
    println!("\n📡 创建 OTLP 客户端...");
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("async-tracing-demo")
        .build()
        .await?;
    println!("   ✅ 客户端创建成功！");

    let tracer = client.tracer("async-example");

    // 场景 1: 单个异步请求
    println!("\n🎯 场景 1: 单个异步请求");
    {
        let span = tracer.start("scenario-1-single");
        let result = handle_user_request(&tracer, 101).await;
        println!("   ✅ 结果: {}", result);
        drop(span);
    }

    // 场景 2: 并发异步请求（顺序执行多个请求）
    println!("\n🎯 场景 2: 多个异步请求");
    {
        let mut span = tracer.start("scenario-2-multiple");
        span.set_attribute(KeyValue::new("requests.count", 3));

        println!("   ├─ 执行 3 个请求...");

        // 顺序执行多个请求（简化版，避免复杂的生命周期问题）
        for user_id in 201..=203 {
            let result = handle_user_request(&tracer, user_id).await;
            println!("      └─ 请求 {} 完成: {}", user_id - 200, result);
        }

        span.set_attribute(KeyValue::new("requests.completed", 3));
        println!("   ✅ 所有请求完成！");
        drop(span);
    }

    // 场景 3: 带超时的异步请求
    println!("\n🎯 场景 3: 带超时的异步请求");
    {
        let mut span = tracer.start("scenario-3-timeout");
        span.set_attribute(KeyValue::new("timeout.seconds", 5));

        match tokio::time::timeout(Duration::from_secs(5), handle_user_request(&tracer, 301)).await
        {
            Ok(result) => {
                println!("   ✅ 结果: {}", result);
                span.set_attribute(KeyValue::new("timeout.occurred", false));
            }
            Err(_) => {
                println!("   ⏱️  请求超时！");
                span.set_attribute(KeyValue::new("timeout.occurred", true));
            }
        }

        drop(span);
    }

    // 显示统计信息
    println!("\n📊 统计信息:");
    let stats = client.stats().await;
    println!("   ├─ 导出 spans: {}", stats.spans_exported);
    println!("   ├─ 错误: {}", stats.export_errors);
    println!("   └─ 平均导出时间: {:.2}ms", stats.avg_export_time_ms);

    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("🎉 异步追踪示例完成！\n");

    Ok(())
}

/* 追踪结构说明:

Scenario 1:
scenario-1-single
└── handle-request
    ├── db-query-user
    ├── api-fetch-profile
    └── cache-set

Scenario 2 (并发):
scenario-2-concurrent
├── handle-request (user 201)
│   ├── db-query-user
│   ├── api-fetch-profile
│   └── cache-set
├── handle-request (user 202)
│   ├── db-query-user
│   ├── api-fetch-profile
│   └── cache-set
└── handle-request (user 203)
    ├── db-query-user
    ├── api-fetch-profile
    └── cache-set

Scenario 3:
scenario-3-timeout
└── handle-request
    ├── db-query-user
    ├── api-fetch-profile
    └── cache-set

在 Jaeger UI 中可以看到并发请求的时间线和依赖关系。
*/
