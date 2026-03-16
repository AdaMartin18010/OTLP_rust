//! Rust 1.92+ 新特性演示
//!
//! 本示例展示了如何使用reliability库中的Rust 1.92新特性支持

use reliability::prelude::*;
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.92+ 新特性演示");
    println!("================================");

    // 演示异步闭包特性
    demonstrate_async_closures().await?;

    // 演示泛型关联类型特性
    demonstrate_generic_associated_types()?;

    // 演示高级异步组合器
    demonstrate_advanced_combinators().await?;

    // 演示与可靠性框架的集成
    demonstrate_reliability_integration().await?;

    println!("✅ 所有演示完成！");
    Ok(())
}

/// 演示异步闭包特性
async fn demonstrate_async_closures() -> Result<(), UnifiedError> {
    println!("\n📦 异步闭包特性演示");
    println!("-------------------");

    let demo = Rust192FeatureDemo::new();

    // 演示批量异步操作
    let results = demo.demonstrate_async_closures().await?;
    println!("异步闭包执行结果: {:?}", results);

    // 演示单个异步闭包操作
    let async_example = AsyncClosureExample;
    let single_result = async_example
        .execute_with_async_closure(|| async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<String, UnifiedError>("单个异步操作完成".to_string())
        })
        .await?;

    println!("单个异步闭包结果: {}", single_result);

    Ok(())
}

/// 演示泛型关联类型特性
#[allow(clippy::result_large_err)]
fn demonstrate_generic_associated_types() -> Result<(), UnifiedError> {
    println!("\n🔧 泛型关联类型特性演示");
    println!("------------------------");

    let demo = Rust192FeatureDemo::new();

    // 演示操作结果
    let operation_result = demo.demonstrate_generic_associated_types();
    println!("操作结果: {:?}", operation_result);
    println!("服务名称: {}", operation_result.metadata.service_name);
    println!("输入类型: {}", operation_result.metadata.input_type);
    println!("执行成功: {}", operation_result.metadata.success);

    // 演示配置访问
    let config = demo.demonstrate_config_access();
    println!("服务配置: {}", config);

    // 演示错误处理
    let error = demo.demonstrate_error_handling();
    println!("错误处理示例: {}", error.summary());

    Ok(())
}

/// 演示高级异步组合器
async fn demonstrate_advanced_combinators() -> Result<(), UnifiedError> {
    println!("\n⚡ 高级异步组合器演示");
    println!("----------------------");

    let combinator = AdvancedAsyncCombinator;

    // 演示操作链
    println!("执行操作链: 0 -> +1 -> *2 -> -1");
    let step1: Box<
        dyn FnOnce(i32) -> Pin<Box<dyn Future<Output = Result<i32, UnifiedError>> + Send>> + Send,
    > = Box::new(|x| {
        Box::pin(async move {
            println!("  步骤1: {} + 1 = {}", x, x + 1);
            Ok::<i32, UnifiedError>(x + 1)
        })
    });
    let step2: Box<
        dyn FnOnce(i32) -> Pin<Box<dyn Future<Output = Result<i32, UnifiedError>> + Send>> + Send,
    > = Box::new(|x| {
        Box::pin(async move {
            println!("  步骤2: {} * 2 = {}", x, x * 2);
            Ok::<i32, UnifiedError>(x * 2)
        })
    });
    let step3: Box<
        dyn FnOnce(i32) -> Pin<Box<dyn Future<Output = Result<i32, UnifiedError>> + Send>> + Send,
    > = Box::new(|x| {
        Box::pin(async move {
            println!("  步骤3: {} - 1 = {}", x, x - 1);
            Ok::<i32, UnifiedError>(x - 1)
        })
    });

    let chain_result = combinator
        .create_operation_chain(0i32, vec![step1, step2, step3])
        .await?;

    println!("操作链最终结果: {}", chain_result);

    // 演示并行操作
    println!("\n执行并行操作:");
    let task1: Box<
        dyn FnOnce() -> Pin<Box<dyn Future<Output = Result<String, UnifiedError>> + Send>> + Send,
    > = Box::new(|| {
        Box::pin(async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            println!("  并行任务1完成");
            Ok::<String, UnifiedError>("任务1".to_string())
        })
    });
    let task2: Box<
        dyn FnOnce() -> Pin<Box<dyn Future<Output = Result<String, UnifiedError>> + Send>> + Send,
    > = Box::new(|| {
        Box::pin(async {
            tokio::time::sleep(Duration::from_millis(150)).await;
            println!("  并行任务2完成");
            Ok::<String, UnifiedError>("任务2".to_string())
        })
    });
    let task3: Box<
        dyn FnOnce() -> Pin<Box<dyn Future<Output = Result<String, UnifiedError>> + Send>> + Send,
    > = Box::new(|| {
        Box::pin(async {
            tokio::time::sleep(Duration::from_millis(200)).await;
            println!("  并行任务3完成");
            Ok::<String, UnifiedError>("任务3".to_string())
        })
    });

    let parallel_results = combinator
        .execute_parallel_operations(vec![task1, task2, task3])
        .await?;

    println!("并行操作结果: {:?}", parallel_results);

    Ok(())
}

/// 演示与可靠性框架的集成
async fn demonstrate_reliability_integration() -> Result<(), UnifiedError> {
    println!("\n🛡️  可靠性框架集成演示");
    println!("------------------------");

    // 创建可靠性服务
    let config = serde_json::json!({
        "timeout": 30,
        "retry_count": 3,
        "enable_monitoring": true,
        "circuit_breaker": {
            "failure_threshold": 5,
            "recovery_timeout": 60
        }
    });

    let reliability_service = ReliabilityService::new("demo_service".to_string(), config);

    // 演示不同类型的操作
    let string_result = reliability_service.execute_operation("测试字符串".to_string());
    println!("字符串操作结果: {:?}", string_result);

    let number_result = reliability_service.execute_operation(42i32);
    println!("数字操作结果: {:?}", number_result);

    let struct_result = reliability_service.execute_operation(TestData {
        id: 1,
        name: "测试数据".to_string(),
        value: std::f64::consts::PI,
    });
    println!("结构体操作结果: {:?}", struct_result);

    // 演示配置获取
    let service_config = reliability_service.get_config::<String>();
    println!("服务配置: {}", service_config);

    // 演示错误处理
    let test_error = UnifiedError::new(
        "模拟的业务错误",
        ErrorSeverity::Medium,
        "business_logic",
        ErrorContext::new("demo", "test", "demo.rs", 1, ErrorSeverity::Medium, "demo"),
    );

    let handled_error = reliability_service.handle_error(test_error);
    println!("处理的错误: {}", handled_error.summary());

    Ok(())
}

/// 测试数据结构
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct TestData {
    id: u32,
    name: String,
    value: f64,
}
