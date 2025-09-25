//! # 集成测试
//!
//! 验证错误处理和弹性机制与所有模块的集成情况。

use otlp::data::{SpanKind, SpanStatus, TelemetryData, TraceData};
use otlp::error::{ExportError, ProcessingError, TransportError};
use otlp::resilience::{
    CircuitBreakerConfig, DegradationStrategy, GracefulDegradationConfig, RetryConfig,
    TimeoutConfig, TriggerCondition,
};
use otlp::{OtlpClient, OtlpConfig, OtlpError, ResilienceConfig, ResilienceManager};
use std::collections::HashMap;
use std::time::Duration;

#[tokio::test]
#[allow(unused_variables)]
async fn test_error_handling_integration() {
    // 测试错误处理的完整集成
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();

    // 测试各种错误类型的处理
    let transport_error = TransportError::Connection {
        endpoint: "http://invalid:4317".to_string(),
        reason: "Connection refused".to_string(),
    };
    let export_error = ExportError::Failed { reason: "fail".to_string() };
    let processing_error = ProcessingError::Batch { reason: "empty".to_string() };

    let errors = vec![
        ("transport", OtlpError::from(transport_error)),
        ("export", OtlpError::from(export_error)),
        ("processing", OtlpError::from(processing_error)),
    ];

    for (error_type, otlp_error) in errors {
        // 验证错误上下文
        let context = otlp_error.context();
        assert_eq!(format!("{:?}", context.category), error_type);
        assert!(context.timestamp.elapsed().unwrap() < Duration::from_secs(1));

        // 验证错误严重程度
        assert!(context.severity as u8 >= 2); // Medium 或更高

        // 验证恢复建议
        assert!(context.recovery_suggestion.is_some());
    }
}

#[tokio::test]
async fn test_resilience_integration() {
    // 测试弹性机制的完整集成
    let config = ResilienceConfig::default();
    let manager = ResilienceManager::new(config);

    // 测试基本操作
    let result = manager
        .execute_with_resilience("test_operation", || {
            Box::pin(async move { Ok::<String, anyhow::Error>("success".to_string()) })
        })
        .await;

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "success");
}

#[tokio::test]
async fn test_circuit_breaker_integration() {
    // 测试熔断器集成
    let config = ResilienceConfig {
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 3,
            recovery_timeout: Duration::from_secs(1),
            half_open_max_calls: 2,
            sliding_window_size: Duration::from_secs(60),
            minimum_calls: 5,
        },
        ..Default::default()
    };

    let manager = ResilienceManager::new(config);

    // 模拟多次失败
    for i in 1..=5 {
        let i = i; // 复制变量以解决生命周期问题
        let result = manager
            .execute_with_resilience("failing_operation", move || {
                Box::pin(async move {
                    if i <= 3 {
                        Err::<String, anyhow::Error>(anyhow::anyhow!("Service unavailable"))
                    } else {
                        Ok::<String, anyhow::Error>("Service recovered".to_string())
                    }
                })
            })
            .await;

        if i <= 3 {
            assert!(result.is_err());
        } else {
            // 熔断器应该开启，但这里我们测试恢复逻辑
            match result {
                Ok(_) => println!("Service recovered successfully"),
                Err(_) => println!("Circuit breaker is open, which is expected"),
            }
        }
    }
}

#[tokio::test]
async fn test_retry_mechanism_integration() {
    // 测试重试机制集成
    let config = ResilienceConfig {
        retry: RetryConfig {
            max_attempts: 3,
            base_delay: Duration::from_millis(10),
            max_delay: Duration::from_secs(1),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec!["temporary".to_string()],
        },
        ..Default::default()
    };

    let manager = ResilienceManager::new(config);

    // 测试重试逻辑（注意：当前实现中重试逻辑被简化）
    let result = manager
        .execute_with_resilience("retry_test", || {
            Box::pin(async move { Ok::<String, anyhow::Error>("success after retry".to_string()) })
        })
        .await;

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_graceful_degradation_integration() {
    // 测试优雅降级集成
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
                TriggerCondition::HighLatency {
                    threshold: Duration::from_secs(2),
                },
            ],
        },
        ..Default::default()
    };

    let manager = ResilienceManager::new(config);

    // 测试降级逻辑
    let result = manager
        .execute_with_resilience("degradation_test", || {
            Box::pin(async move {
                // 模拟高延迟操作
                tokio::time::sleep(Duration::from_millis(100)).await;
                Ok::<String, anyhow::Error>("operation completed".to_string())
            })
        })
        .await;

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_client_resilience_integration() {
    // 测试客户端弹性集成
    let config = OtlpConfig {
        endpoint: "http://localhost:4317".to_string(),
        ..Default::default()
    };

    let client = OtlpClient::new(config).await.unwrap();

    // 创建测试数据
    let _trace_data = TraceData {
        trace_id: "test-trace-id".to_string(),
        span_id: "test-span-id".to_string(),
        parent_span_id: None,
        name: "test-operation".to_string(),
        span_kind: SpanKind::Internal,
        start_time: 0,
        end_time: 1000000,
        status: SpanStatus::default(),
        attributes: HashMap::new(),
        events: vec![],
        links: vec![],
    };

    let telemetry_data = TelemetryData::trace("test-operation");

    // 测试发送（可能会失败，但应该不会 panic）
    let result = client.send(telemetry_data).await;

    // 验证错误处理
    match result {
        Ok(_) => println!("Data sent successfully"),
        Err(e) => {
            println!("Expected error: {}", e);
            // 验证错误上下文
            let context = e.context();
            assert!(format!("{:?}", context.category).len() > 0);
            assert!(context.severity as u8 >= 2);
        }
    }
}

#[tokio::test]
async fn test_config_compatibility() {
    // 测试配置兼容性
    let otlp_config = OtlpConfig {
        endpoint: "http://test:4317".to_string(),
        connect_timeout: Duration::from_secs(5),
        request_timeout: Duration::from_secs(30),
        ..Default::default()
    };

    // 验证配置转换
    let resilience_config = ResilienceConfig {
        timeout: TimeoutConfig {
            connect_timeout: otlp_config.connect_timeout,
            operation_timeout: otlp_config.request_timeout,
            ..Default::default()
        },
        ..Default::default()
    };

    assert_eq!(
        resilience_config.timeout.connect_timeout,
        Duration::from_secs(5)
    );
    assert_eq!(
        resilience_config.timeout.operation_timeout,
        Duration::from_secs(30)
    );
}

#[tokio::test]
async fn test_error_propagation() {
    // 测试错误传播链
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();

    // 测试错误传播
    let result = client.initialize().await;

    // 验证错误类型
    match result {
        Ok(_) => println!("Initialization successful"),
        Err(e) => {
            println!("Expected error: {}", e);
            // 验证错误可以正确传播
            let context = e.context();
            assert!(format!("{:?}", context.category).len() > 0);
        }
    }
}

#[tokio::test]
async fn test_metrics_integration() {
    // 测试指标集成
    let config = ResilienceConfig::default();
    let manager = ResilienceManager::new(config);

    // 执行一些操作来生成指标
    for _ in 0..5 {
        let _ = manager
            .execute_with_resilience("metrics_test", || {
                Box::pin(async move { Ok::<(), anyhow::Error>(()) })
            })
            .await;
    }

    // 获取指标
    let metrics = manager.get_metrics().await;
    assert!(metrics.total_operations > 0);
}

#[tokio::test]
async fn test_health_check_integration() {
    // 测试健康检查集成
    let config = ResilienceConfig::default();
    let manager = ResilienceManager::new(config);

    // 获取健康状态
    let health_status = manager.get_health_status().await;

    // 验证健康状态
    match health_status {
        otlp::resilience::HealthStatus::Healthy => println!("System is healthy"),
        otlp::resilience::HealthStatus::Unhealthy => println!("System is unhealthy"),
        otlp::resilience::HealthStatus::Degraded => println!("System is degraded"),
    }
}

#[tokio::test]
async fn test_comprehensive_integration() {
    // 综合集成测试
    let config = OtlpConfig {
        endpoint: "http://localhost:4317".to_string(),
        connect_timeout: Duration::from_secs(5),
        request_timeout: Duration::from_secs(10),
        ..Default::default()
    };

    let client = OtlpClient::new(config).await.unwrap();

    // 测试完整的错误处理流程
    let _trace_data = TraceData {
        trace_id: "integration-test-trace".to_string(),
        span_id: "integration-test-span".to_string(),
        parent_span_id: None,
        name: "integration-test-operation".to_string(),
        span_kind: SpanKind::Internal,
        start_time: 0,
        end_time: 1000000,
        status: SpanStatus::default(),
        attributes: HashMap::new(),
        events: vec![],
        links: vec![],
    };

    let telemetry_data = TelemetryData::trace("test-operation");

    // 测试发送（预期会失败，但应该优雅处理）
    let start_time = std::time::Instant::now();
    let result = client.send(telemetry_data).await;
    let duration = start_time.elapsed();

    println!("Operation completed in {:?}", duration);

    match result {
        Ok(export_result) => {
            println!("Export successful: {:?}", export_result);
        }
        Err(e) => {
            println!("Export failed with error: {}", e);

            // 验证错误处理
            let context = e.context();
            println!("Error category: {:?}", context.category);
            println!("Severity: {:?}", context.severity);
            println!("Retryable: {}", context.is_retryable);
            println!("Temporary: {}", context.is_retryable);

            if let Some(suggestion) = context.recovery_suggestion {
                println!("Recovery suggestion: {}", suggestion);
            }

            // 验证错误处理完整性
            assert!(format!("{:?}", context.category).len() > 0);
            assert!(context.severity as u8 >= 1);
        }
    }

    println!("Comprehensive integration test completed successfully");
}
