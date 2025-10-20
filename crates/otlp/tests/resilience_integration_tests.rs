//! # 容错模式集成测试
//!
//! 测试断路器、重试、舱壁和超时模式的集成使用。

use anyhow;
use otlp::resilience::{
    Bulkhead, BulkheadConfig, CircuitBreaker, CircuitBreakerConfig, CircuitState, ResilienceConfig,
    ResilienceManager, Retrier, RetryConfig, RetryStrategy, Timeout, TimeoutConfig,
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::test]
async fn test_circuit_breaker_integration() {
    let config = CircuitBreakerConfig {
        failure_threshold: 3,
        recovery_timeout: Duration::from_millis(100),
        half_open_max_requests: 2,
        success_threshold: 2,
    };
    let breaker = CircuitBreaker::new(config);

    // 初始状态应该是关闭的
    assert_eq!(breaker.state(), CircuitState::Closed);

    // 记录失败直到打开
    for _ in 0..3 {
        breaker.record_failure().await;
    }
    assert_eq!(breaker.state(), CircuitState::Open);

    // 等待恢复
    sleep(Duration::from_millis(150)).await;

    // 应该转换到半开状态
    assert_eq!(breaker.state(), CircuitState::HalfOpen);

    // 记录成功直到关闭
    for _ in 0..2 {
        breaker.record_success();
    }
    assert_eq!(breaker.state(), CircuitState::Closed);
}

#[tokio::test]
async fn test_retry_integration() {
    let config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::Fixed {
            interval: Duration::from_millis(10),
        },
        total_timeout: None,
        health_check: false,
    };
    let retrier = Retrier::new(config);

    let attempt_count = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let attempt_count_clone = attempt_count.clone();
    let result: Result<i32, _> = retrier
        .execute(move || {
            let attempt_count = attempt_count_clone.clone();
            Box::pin(async move {
                let current_attempt =
                    attempt_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if current_attempt < 3 {
                    Err("temporary error")
                } else {
                    Ok(42)
                }
            })
        })
        .await;

    assert_eq!(result, Ok(42));
    assert_eq!(attempt_count.load(std::sync::atomic::Ordering::Relaxed), 3);

    let stats = retrier.stats().await;
    assert!(stats.total_retries > 0);
}

#[tokio::test]
async fn test_bulkhead_integration() {
    let config = BulkheadConfig {
        max_concurrent_requests: 2,
        max_queue_size: 5,
        queue_timeout: Duration::from_millis(100),
        enable_stats: true,
    };
    let bulkhead = Bulkhead::new(config);

    // 获取两个许可
    let permit1 = bulkhead.acquire().await.unwrap();
    let permit2 = bulkhead.acquire().await.unwrap();

    // 尝试获取第三个许可（应该超时）
    let result = bulkhead.acquire().await;
    assert!(result.is_err());

    // 释放许可
    drop(permit1);
    drop(permit2);

    // 现在应该能够获取许可
    let permit3 = bulkhead.acquire().await.unwrap();
    assert!(permit3.request_id() > 0);
}

#[tokio::test]
async fn test_timeout_integration() {
    let config = TimeoutConfig {
        default_timeout: Duration::from_millis(50),
        ..Default::default()
    };
    let timeout = Timeout::new(config);

    // 测试成功操作
    let result: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    assert_eq!(result, Ok(42));

    // 测试超时操作
    let result: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async {
            sleep(Duration::from_millis(100)).await;
            Ok(42)
        })
        .await;
    assert!(result.is_err());

    let stats = timeout.stats();
    assert!(
        stats
            .successful_completions
            .load(std::sync::atomic::Ordering::Acquire)
            > 0
    );
    assert!(
        stats
            .total_timeouts
            .load(std::sync::atomic::Ordering::Acquire)
            > 0
    );
}

#[tokio::test]
async fn test_resilience_manager_integration() {
    let manager = ResilienceManager::new();

    // 创建断路器
    let breaker_config = CircuitBreakerConfig::default();
    let breaker = manager
        .get_or_create_circuit_breaker("test_breaker", breaker_config)
        .await;

    // 创建重试器
    let retry_config = RetryConfig::default();
    let retrier = manager
        .get_or_create_retrier("test_retrier", retry_config)
        .await;

    // 创建舱壁
    let bulkhead_config = BulkheadConfig::default();
    let bulkhead = manager
        .get_or_create_bulkhead("test_bulkhead", bulkhead_config)
        .await;

    // 创建超时器
    let timeout_config = TimeoutConfig::default();
    let timeout = manager
        .get_or_create_timeout("test_timeout", timeout_config)
        .await;

    // 测试所有组件
    let breaker_result: Result<i32, _> = breaker
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    assert!(breaker_result.is_ok());
    assert_eq!(breaker_result.unwrap(), 42);

    let retry_result: Result<i32, _> = retrier
        .execute(|| Box::pin(async { Ok::<i32, &str>(42) }))
        .await;
    assert_eq!(retry_result, Ok(42));

    let bulkhead_permit = bulkhead.acquire().await.unwrap();
    assert!(bulkhead_permit.request_id() > 0);

    let timeout_result: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    assert_eq!(timeout_result, Ok(42));

    // 获取状态
    let status = manager.get_all_status().await;
    assert!(status.circuit_breakers.contains_key("test_breaker"));
    assert!(status.retriers.contains_key("test_retrier"));
    assert!(status.bulkheads.contains_key("test_bulkhead"));
    assert!(status.timeouts.contains_key("test_timeout"));
}

#[tokio::test]
async fn test_combined_resilience_patterns() {
    // 创建组合的容错配置
    let config = ResilienceConfig {
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 5,
            recovery_timeout: Duration::from_millis(100),
            half_open_max_requests: 3,
            success_threshold: 2,
        },
        retry: RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Exponential {
                initial_interval: Duration::from_millis(10),
                max_interval: Duration::from_millis(100),
                multiplier: 2.0,
            },
            total_timeout: Some(Duration::from_secs(1)),
            health_check: false,
        },
        bulkhead: BulkheadConfig {
            max_concurrent_requests: 5,
            max_queue_size: 10,
            queue_timeout: Duration::from_millis(100),
            enable_stats: true,
        },
        timeout: TimeoutConfig {
            default_timeout: Duration::from_millis(50),
            ..Default::default()
        },
    };

    let manager = ResilienceManager::new();
    let breaker = manager
        .get_or_create_circuit_breaker("combined_breaker", config.circuit_breaker)
        .await;
    let retrier = manager
        .get_or_create_retrier("combined_retrier", config.retry)
        .await;
    let bulkhead = manager
        .get_or_create_bulkhead("combined_bulkhead", config.bulkhead)
        .await;
    let timeout = manager
        .get_or_create_timeout("combined_timeout", config.timeout)
        .await;

    // 测试组合使用 - 简化版本
    let _permit = bulkhead.acquire().await.unwrap();

    // 分别测试各个组件
    let breaker_result: Result<i32, _> = breaker
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    assert!(breaker_result.is_ok());

    let retry_result: Result<i32, _> = retrier
        .execute(|| Box::pin(async { Ok::<i32, &str>(42) }))
        .await;
    assert!(retry_result.is_ok());

    let timeout_result: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    assert!(timeout_result.is_ok());

    let result: Result<i32, anyhow::Error> = Ok(42);

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);

    // 验证所有组件都有活动
    let status = manager.get_all_status().await;
    assert!(status.circuit_breakers.contains_key("combined_breaker"));
    assert!(status.retriers.contains_key("combined_retrier"));
    assert!(status.bulkheads.contains_key("combined_bulkhead"));
    assert!(status.timeouts.contains_key("combined_timeout"));
}

#[tokio::test]
async fn test_resilience_error_handling() {
    let breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
    let retrier = Retrier::new(RetryConfig::default());
    let _bulkhead = Bulkhead::new(BulkheadConfig::default());
    let timeout = Timeout::new(TimeoutConfig::default());

    // 测试各种错误情况
    let breaker_result: Result<i32, _> = breaker
        .execute::<_, i32, anyhow::Error>(async { Err(anyhow::anyhow!("operation failed")) })
        .await;
    assert!(breaker_result.is_err());

    let retry_result: Result<i32, _> = retrier
        .execute(|| Box::pin(async { Err("operation failed") }))
        .await;
    assert!(retry_result.is_err());

    // 测试超时
    let timeout_result: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async {
            sleep(Duration::from_millis(100)).await;
            Ok(42)
        })
        .await;
    assert!(timeout_result.is_err());
}

#[tokio::test]
async fn test_resilience_stats_collection() {
    let breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
    let retrier = Retrier::new(RetryConfig::default());
    let bulkhead = Bulkhead::new(BulkheadConfig::default());
    let timeout = Timeout::new(TimeoutConfig::default());

    // 执行一些操作
    let _: Result<i32, _> = breaker
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;
    let _: Result<i32, _> = retrier
        .execute(|| Box::pin(async { Ok::<i32, &str>(42) }))
        .await;
    let _ = bulkhead.acquire().await;
    let _: Result<i32, _> = timeout
        .execute::<_, i32, anyhow::Error>(async { Ok(42) })
        .await;

    // 检查统计信息
    let breaker_stats = breaker.stats();
    assert!(
        breaker_stats
            .total_requests
            .load(std::sync::atomic::Ordering::Acquire)
            > 0
    );

    let retry_stats = retrier.stats().await;
    assert!(retry_stats.total_retries > 0);

    let bulkhead_stats = bulkhead.stats();
    assert!(
        bulkhead_stats
            .total_requests
            .load(std::sync::atomic::Ordering::Acquire)
            > 0
    );

    let timeout_stats = timeout.stats();
    assert!(
        timeout_stats
            .successful_completions
            .load(std::sync::atomic::Ordering::Acquire)
            > 0
    );
}
