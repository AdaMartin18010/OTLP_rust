//! # 弹性机制使用示例
//!
//! 展示如何使用 OTLP Rust 的弹性机制来处理各种异常情况。

use anyhow;
use otlp::resilience::{CircuitBreakerConfig, RetryConfig, RetryStrategy, TimeoutConfig};
use otlp::{ResilienceConfig, ResilienceManager, Result};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP Rust 弹性机制使用示例");
    println!("=====================================");

    // 示例 1: 基本弹性配置
    basic_resilience_example().await?;

    // 示例 2: 自定义重试配置
    custom_retry_example().await?;

    // 示例 3: 熔断器示例
    circuit_breaker_example().await?;

    // 示例 4: 优雅降级示例
    graceful_degradation_example().await?;

    // 示例 5: 错误处理示例
    error_handling_example().await?;

    println!("\n✅ 所有示例执行完成！");
    Ok(())
}

/// 示例 1: 基本弹性配置
async fn basic_resilience_example() -> Result<()> {
    println!("\n📋 示例 1: 基本弹性配置");
    println!("------------------------");

    // 使用默认配置创建弹性管理器
    let _config = ResilienceConfig::default();
    let manager = ResilienceManager::new();

    // 使用断路器直接执行操作
    let breaker = manager
        .get_or_create_circuit_breaker("basic_operation", CircuitBreakerConfig::default())
        .await;
    let result = breaker
        .execute(async {
            println!("  执行基本操作...");
            // 模拟一些工作
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<String, anyhow::Error>("操作成功".to_string())
        })
        .await;

    match result {
        Ok(value) => println!("  ✅ 操作成功: {}", value),
        Err(e) => println!("  ❌ 操作失败: {}", e),
    }

    Ok(())
}

/// 示例 2: 自定义重试配置
async fn custom_retry_example() -> Result<()> {
    println!("\n🔄 示例 2: 自定义重试配置");
    println!("---------------------------");

    // 创建自定义重试配置
    let _config = ResilienceConfig {
        retry: RetryConfig {
            max_attempts: 5,
            strategy: RetryStrategy::Exponential {
                initial_interval: Duration::from_millis(100),
                max_interval: Duration::from_secs(2),
                multiplier: 2.0,
            },
            total_timeout: Some(Duration::from_secs(10)),
            health_check: false,
        },
        ..Default::default()
    };

    let manager = ResilienceManager::new();

    // 模拟一个会失败几次的操作
    let attempt = 0;
    let retrier = manager
        .get_or_create_retrier("retry_operation", RetryConfig::default())
        .await;
    let result = retrier
        .execute(move || {
            let mut attempt = attempt;
            Box::pin(async move {
                attempt += 1;
                println!("  尝试第 {} 次...", attempt);

                if attempt < 3 {
                    Err(format!("临时错误 - 尝试 {}", attempt))
                } else {
                    Ok(format!("重试成功，共尝试 {} 次", attempt))
                }
            })
        })
        .await;

    match result {
        Ok(value) => println!("  ✅ {}", value),
        Err(e) => println!("  ❌ 重试失败: {}", e),
    }

    Ok(())
}

/// 示例 3: 熔断器示例
async fn circuit_breaker_example() -> Result<()> {
    println!("\n⚡ 示例 3: 熔断器示例");
    println!("---------------------");

    // 创建熔断器配置
    let _config = ResilienceConfig {
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 3,                     // 3次失败后开启熔断器
            recovery_timeout: Duration::from_secs(5), // 5秒后尝试恢复
            half_open_max_requests: 2,                // 半开状态最多2次调用
            success_threshold: 2,                     // 成功阈值
        },
        ..Default::default()
    };

    let manager = ResilienceManager::new();

    // 模拟多次失败的操作
    for i in 1..=6 {
        println!("  第 {} 次调用:", i);

        let i = i; // 复制变量
        let breaker = manager
            .get_or_create_circuit_breaker("circuit_breaker", CircuitBreakerConfig::default())
            .await;
        let result = breaker
            .execute(async move {
                if i <= 3 {
                    Err(anyhow::anyhow!("服务不可用"))
                } else {
                    Ok("服务恢复正常".to_string())
                }
            })
            .await;

        match result {
            Ok(value) => println!("    ✅ {}", value),
            Err(e) => println!("    ❌ {}", e),
        }

        // 等待一段时间
        tokio::time::sleep(Duration::from_millis(500)).await;
    }

    Ok(())
}

/// 示例 4: 优雅降级示例
async fn graceful_degradation_example() -> Result<()> {
    println!("\n🛡️ 示例 4: 优雅降级示例");
    println!("-------------------------");

    // 创建优雅降级配置
    let _config = ResilienceConfig {
        ..Default::default()
    };

    let manager = ResilienceManager::new();

    // 模拟高延迟操作
    let timeout = manager
        .get_or_create_timeout("timeout", TimeoutConfig::default())
        .await;
    let result = timeout
        .execute::<_, String, anyhow::Error>(async {
            println!("  执行慢操作...");
            tokio::time::sleep(Duration::from_millis(2500)).await; // 超过2秒阈值
            Ok("慢操作完成".to_string())
        })
        .await;

    match result {
        Ok(value) => println!("  ✅ {}", value),
        Err(e) => println!("  ❌ 操作失败: {}", e),
    }

    Ok(())
}

/// 示例 5: 错误处理示例
async fn error_handling_example() -> Result<()> {
    println!("\n🔍 示例 5: 错误处理示例");
    println!("------------------------");

    let _config = ResilienceConfig::default();
    let manager = ResilienceManager::new();

    // 模拟不同类型的错误
    let error_types = vec![
        ("网络错误", "connection_failed"),
        ("超时错误", "timeout"),
        ("配置错误", "invalid_config"),
        ("临时错误", "temporary_error"),
    ];

    for (name, error_type) in error_types {
        println!("  测试 {}:", name);

        let breaker = manager
            .get_or_create_circuit_breaker("error_test", CircuitBreakerConfig::default())
            .await;
        let result = breaker
            .execute(async move {
                let error_type = error_type.to_string();
                Err::<String, anyhow::Error>(anyhow::anyhow!("{}", error_type))
            })
            .await;

        match result {
            Ok(value) => println!("    ✅ {}", value),
            Err(e) => {
                println!("    ❌ 错误: {}", e);

                // 获取错误上下文信息
                println!("      错误详情: {}", e);
            }
        }
    }

    Ok(())
}

/// 辅助函数：创建自定义超时配置
#[allow(dead_code)]
fn create_timeout_config() -> TimeoutConfig {
    TimeoutConfig {
        default_timeout: Duration::from_secs(60),
        max_timeout: Duration::from_secs(30),
        min_timeout: Duration::from_secs(10),
        enable_stats: true,
        enable_adaptive: true,
        adaptive_factor: 1.5,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_resilience() {
        let result = basic_resilience_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_custom_retry() {
        let result = custom_retry_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_circuit_breaker() {
        let result = circuit_breaker_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_graceful_degradation() {
        let result = graceful_degradation_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_error_handling() {
        let result = error_handling_example().await;
        assert!(result.is_ok());
    }
}
