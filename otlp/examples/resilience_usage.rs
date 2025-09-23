//! # 弹性机制使用示例
//! 
//! 展示如何使用 OTLP Rust 的弹性机制来处理各种异常情况。

use std::time::Duration;
use otlp::{
    ResilienceManager, ResilienceConfig, ResilienceError,
    OtlpError, Result
};
use otlp::resilience::{
    RetryConfig, CircuitBreakerConfig, TimeoutConfig,
    GracefulDegradationConfig, DegradationStrategy, TriggerCondition,
};
//use anyhow::anyhow;

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
    let config = ResilienceConfig::default();
    let manager = ResilienceManager::new(config);
    
    // 执行一个简单的操作
    let result = manager.execute_with_resilience("basic_operation", || {
        Box::pin(async move {
            println!("  执行基本操作...");
            // 模拟一些工作
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<String, anyhow::Error>("操作成功".to_string())
        })
    }).await;
    
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
    let config = ResilienceConfig {
        retry: RetryConfig {
            max_attempts: 5,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(2),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection".to_string(),
                "temporary".to_string(),
            ],
        },
        ..Default::default()
    };
    
    let manager = ResilienceManager::new(config);
    
    // 模拟一个会失败几次的操作
    let attempt = 0;
    let result = manager.execute_with_resilience("retry_operation", move || {
        let mut attempt = attempt;
        Box::pin(async move {
            attempt += 1;
            println!("  尝试第 {} 次...", attempt);
            
            if attempt < 3 {
                Err(anyhow::anyhow!("临时错误 - 尝试 {}", attempt))
            } else {
                Ok::<String, anyhow::Error>(format!("重试成功，共尝试 {} 次", attempt))
            }
        })
    }).await;
    
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
    let config = ResilienceConfig {
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 3,  // 3次失败后开启熔断器
            recovery_timeout: Duration::from_secs(5),  // 5秒后尝试恢复
            half_open_max_calls: 2,  // 半开状态最多2次调用
            sliding_window_size: Duration::from_secs(60),
            minimum_calls: 5,
        },
        ..Default::default()
    };
    
    let manager = ResilienceManager::new(config);
    
    // 模拟多次失败的操作
    for i in 1..=6 {
        println!("  第 {} 次调用:", i);
        
        let i = i; // 复制变量
        let result = manager.execute_with_resilience("circuit_breaker_test", move || {
            Box::pin(async move {
                if i <= 3 {
                    Err(anyhow::anyhow!("服务不可用"))
                } else {
                    Ok::<String, anyhow::Error>("服务恢复正常".to_string())
                }
            })
        }).await;
        
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
    let config = ResilienceConfig {
        graceful_degradation: GracefulDegradationConfig {
            enabled: true,
            strategies: vec![
                DegradationStrategy::UseCache,
                DegradationStrategy::UseFallback,
                DegradationStrategy::ReduceQuality,
            ],
            trigger_conditions: vec![
                TriggerCondition::HighErrorRate { threshold: 0.5 },
                TriggerCondition::HighLatency { threshold: Duration::from_secs(2) },
            ],
        },
        ..Default::default()
    };
    
    let manager = ResilienceManager::new(config);
    
    // 模拟高延迟操作
    let result = manager.execute_with_resilience("slow_operation", || {
        Box::pin(async move {
            println!("  执行慢操作...");
            tokio::time::sleep(Duration::from_millis(2500)).await;  // 超过2秒阈值
            Ok::<String, anyhow::Error>("慢操作完成".to_string())
        })
    }).await;
    
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
    
    let config = ResilienceConfig::default();
    let manager = ResilienceManager::new(config);
    
    // 模拟不同类型的错误
    let error_types = vec![
        ("网络错误", "connection_failed"),
        ("超时错误", "timeout"),
        ("配置错误", "invalid_config"),
        ("临时错误", "temporary_error"),
    ];
    
    for (name, error_type) in error_types {
        println!("  测试 {}:", name);
        
        let result = manager.execute_with_resilience(&format!("error_test_{}", error_type), || {
            let error_type = error_type.to_string();
            Box::pin(async move {
                Err::<String, anyhow::Error>(anyhow::anyhow!("{}", error_type))
            })
        }).await;
        
        match result {
            Ok(value) => println!("    ✅ {}", value),
            Err(e) => {
                println!("    ❌ 错误: {}", e);
                
                // 获取错误上下文信息
                if let ResilienceError::OperationFailed(err) = &e {
                    if let Some(otlp_err) = err.downcast_ref::<OtlpError>() {
                        let context = otlp_err.context();
                        println!("      错误类型: {}", context.error_type);
                        println!("      严重程度: {}", context.severity);
                        println!("      可重试: {}", context.is_retryable);
                        println!("      临时错误: {}", context.is_temporary);
                        if let Some(suggestion) = context.recovery_suggestion {
                            println!("      恢复建议: {}", suggestion);
                        }
                    }
                }
            }
        }
    }
    
    Ok(())
}

/// 辅助函数：创建自定义超时配置
#[allow(dead_code)]
fn create_timeout_config() -> TimeoutConfig {
    TimeoutConfig {
        connect_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        operation_timeout: Duration::from_secs(60),
    }
}

/// 辅助函数：创建自定义健康检查配置
#[allow(dead_code)]
fn create_health_check_config() -> otlp::resilience::HealthCheckConfig {
    otlp::resilience::HealthCheckConfig {
        interval: Duration::from_secs(30),
        timeout: Duration::from_secs(5),
        path: "/health".to_string(),
        unhealthy_threshold: 3,
        healthy_threshold: 2,
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
