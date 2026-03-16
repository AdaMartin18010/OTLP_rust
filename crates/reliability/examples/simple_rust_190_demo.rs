//! 简化的 Rust 1.92+ 新特性演示
//!
//! 本示例展示了reliability库中的Rust 1.92新特性支持

use reliability::prelude::*;
//use std::time::Duration;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.92+ 新特性演示");
    println!("================================");

    // 演示基本功能
    demonstrate_basic_features().await?;

    // 演示可靠性框架集成
    demonstrate_reliability_integration().await?;

    println!("✅ 所有演示完成！");
    Ok(())
}

/// 演示基本功能
async fn demonstrate_basic_features() -> Result<(), UnifiedError> {
    println!("\n📦 基本功能演示");
    println!("-------------------");

    // 创建演示器
    let demo = Rust192FeatureDemo::new();

    // 演示泛型关联类型
    let operation_result = demo.demonstrate_generic_associated_types();
    println!("泛型关联类型结果: {:?}", operation_result);
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
