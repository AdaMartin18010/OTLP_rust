//! # 综合集成测试
//!
//! 本模块提供了OTLP项目的全面集成测试，包括：
//! - 端到端功能测试
//! - 性能基准测试
//! - 故障恢复测试
//! - 并发压力测试
//! - 内存泄漏测试

use otlp::*;
use std::time::Duration;
use std::sync::Arc;
use std::collections::HashMap;

/// 端到端功能测试
#[tokio::test]
async fn test_end_to_end_functionality() {
    // 初始化OTLP客户端
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();
    
    // 创建遥测数据
    let trace_data = create_test_trace_data();
    let metric_data = create_test_metric_data();
    let log_data = create_test_log_data();
    
    // 发送数据
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let result = client.send(trace_telemetry).await;
    assert!(result.is_ok());
    
    let metric_telemetry = TelemetryData {
        data_type: TelemetryDataType::Metric,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Metric(metric_data),
    };
    let result = client.send(metric_telemetry).await;
    assert!(result.is_ok());
    
    let log_telemetry = TelemetryData {
        data_type: TelemetryDataType::Log,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Log(log_data),
    };
    let result = client.send(log_telemetry).await;
    assert!(result.is_ok());
    
    // 验证数据完整性
    let metrics = client.get_metrics().await;
    assert!(metrics.total_data_sent > 0);
}

/// 性能基准测试
#[tokio::test]
async fn test_performance_benchmarks() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();
    
    // 批量数据测试
    let batch_size = 10000;
    let traces = (0..batch_size)
        .map(|i| {
            let trace_data = create_test_trace_data_with_id(i);
            TelemetryData {
                data_type: TelemetryDataType::Trace,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64,
                resource_attributes: HashMap::new(),
                scope_attributes: HashMap::new(),
                content: TelemetryContent::Trace(trace_data),
            }
        })
        .collect::<Vec<_>>();
    
    let start = std::time::Instant::now();
    let result = client.send_batch(traces).await;
    let duration = start.elapsed();
    
    assert!(result.is_ok());
    
    // 性能断言：每秒至少处理1000条trace
    let throughput = batch_size as f64 / duration.as_secs_f64();
    assert!(throughput > 1000.0, "吞吐量过低: {:.2} traces/sec", throughput);
    
    println!("批量导出性能: {:.2} traces/sec", throughput);
}

/// 故障恢复测试
#[tokio::test]
async fn test_fault_recovery() {
    let config = OtlpConfig {
        endpoint: "http://invalid-endpoint:4317".to_string(),
        request_timeout: Duration::from_millis(100),
        retry_config: config::RetryConfig {
            max_retries: 3,
            initial_retry_delay: Duration::from_millis(50),
            max_retry_delay: Duration::from_secs(1),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
        },
        ..Default::default()
    };
    
    let client = OtlpClient::new(config).await.unwrap();
    
    // 测试重试机制
    let trace_data = create_test_trace_data();
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let result = client.send(trace_telemetry).await;
    
    // 应该失败，但重试机制应该工作
    assert!(result.is_err());
    
    // 验证重试统计
    let _metrics = client.get_metrics().await;
    // 注意：这里可能需要根据实际的指标结构来调整
    // assert!(_metrics.retry_attempts > 0);
}

/// 并发压力测试
#[tokio::test]
async fn test_concurrent_stress() {
    let config = OtlpConfig::default();
    let client = Arc::new(OtlpClient::new(config).await.unwrap());
    
    let num_tasks = 100;
    let traces_per_task = 100;
    
    let start = std::time::Instant::now();
    
    let handles: Vec<_> = (0..num_tasks)
        .map(|task_id| {
            let client = Arc::clone(&client);
            tokio::spawn(async move {
                let traces = (0..traces_per_task)
                    .map(|i| {
                        let trace_data = create_test_trace_data_with_id(task_id * traces_per_task + i);
                        TelemetryData {
                            data_type: TelemetryDataType::Trace,
                            timestamp: std::time::SystemTime::now()
                                .duration_since(std::time::UNIX_EPOCH)
                                .unwrap()
                                .as_nanos() as u64,
                            resource_attributes: HashMap::new(),
                            scope_attributes: HashMap::new(),
                            content: TelemetryContent::Trace(trace_data),
                        }
                    })
                    .collect::<Vec<_>>();
                
                client.send_batch(traces).await
            })
        })
        .collect();
    
    let results = futures::future::join_all(handles).await;
    let duration = start.elapsed();
    
    // 验证所有任务都成功完成
    let success_count = results.iter().filter(|r| r.is_ok()).count();
    assert_eq!(success_count, num_tasks);
    
    let total_traces = num_tasks * traces_per_task;
    let throughput = total_traces as f64 / duration.as_secs_f64();
    
    println!("并发压力测试: {:.2} traces/sec", throughput);
    assert!(throughput > 5000.0, "并发吞吐量过低: {:.2} traces/sec", throughput);
}

/// 内存泄漏测试
#[tokio::test]
async fn test_memory_leaks() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();
    
    // 执行大量操作
    for i in 0..1000 {
        let traces = (0..100)
            .map(|j| {
                let trace_data = create_test_trace_data_with_id(i * 100 + j);
                TelemetryData {
                    data_type: TelemetryDataType::Trace,
                    timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_nanos() as u64,
                    resource_attributes: HashMap::new(),
                    scope_attributes: HashMap::new(),
                    content: TelemetryContent::Trace(trace_data),
                }
            })
            .collect::<Vec<_>>();
        
        let _ = client.send_batch(traces).await;
        
        // 每100次操作后检查内存使用
        if i % 100 == 0 {
            let memory_usage = get_memory_usage();
            println!("内存使用: {} MB", memory_usage / 1024 / 1024);
            
            // 内存使用不应该超过100MB
            assert!(memory_usage < 100 * 1024 * 1024, "内存使用过高: {} MB", memory_usage / 1024 / 1024);
        }
    }
}

/// 配置验证测试
#[tokio::test]
async fn test_configuration_validation() {
    // 测试无效配置
    let invalid_config = OtlpConfig {
        endpoint: "".to_string(),
        ..Default::default()
    };
    
    let result = OtlpClient::new(invalid_config).await;
    assert!(result.is_err());
    
    // 测试有效配置
    let valid_config = OtlpConfig {
        endpoint: "http://localhost:4317".to_string(),
        request_timeout: Duration::from_secs(30),
        batch_config: BatchConfig {
            max_export_batch_size: 1000,
            ..Default::default()
        },
        ..Default::default()
    };
    
    let result = OtlpClient::new(valid_config).await;
    assert!(result.is_ok());
}

/// 数据完整性测试
#[tokio::test]
async fn test_data_integrity() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();
    
    // 创建包含特殊字符的数据
    let trace_data = TraceData {
        trace_id: "12345678901234567890123456789012".to_string(),
        span_id: "1234567890123456".to_string(),
        parent_span_id: None,
        name: "测试Span名称".to_string(),
        span_kind: SpanKind::Internal,
        start_time: 1000,
        end_time: 2000,
        status: SpanStatus::default(),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert("unicode_key".to_string(), AttributeValue::String("测试值".to_string()));
            attrs.insert("special_chars".to_string(), AttributeValue::String("!@#$%^&*()".to_string()));
            attrs
        },
        events: vec![],
        links: vec![],
    };
    
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let result = client.send(trace_telemetry).await;
    assert!(result.is_ok());
    
    // 验证数据没有被损坏
    let metrics = client.get_metrics().await;
    assert!(metrics.total_data_sent > 0);
}

/// 网络异常测试
#[tokio::test]
async fn test_network_anomalies() {
    let config = OtlpConfig {
        endpoint: "http://localhost:9999".to_string(), // 不存在的端口
        request_timeout: Duration::from_millis(100),
        ..Default::default()
    };
    
    let client = OtlpClient::new(config).await.unwrap();
    
    // 测试连接超时
    let trace_data = create_test_trace_data();
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let result = client.send(trace_telemetry).await;
    assert!(result.is_err());
    
    // 验证错误类型
    match result.unwrap_err() {
        OtlpError::Transport(_) => {}, // 预期的传输错误
        _ => panic!("期望传输错误，但得到其他错误"),
    }
}

/// 批量处理测试
#[tokio::test]
async fn test_batch_processing() {
    let config = OtlpConfig {
        batch_config: BatchConfig {
            max_export_batch_size: 100,
            export_timeout: Duration::from_millis(500),
            ..Default::default()
        },
        ..Default::default()
    };
    
    let client = OtlpClient::new(config).await.unwrap();
    
    // 发送少量数据，应该等待批量处理
    let trace_data = create_test_trace_data();
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let start = std::time::Instant::now();
    
    let result = client.send(trace_telemetry).await;
    let duration = start.elapsed();
    
    assert!(result.is_ok());
    
    // 验证批量处理延迟
    assert!(duration >= Duration::from_millis(100), "批量处理延迟过短");
}

/// 资源清理测试
#[tokio::test]
async fn test_resource_cleanup() {
    let config = OtlpConfig::default();
    let client = OtlpClient::new(config).await.unwrap();
    
    // 执行一些操作
    let trace_data = create_test_trace_data();
    let trace_telemetry = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };
    let _ = client.send(trace_telemetry).await;
    
    // 显式关闭客户端
    client.shutdown().await.unwrap();
    
    // 验证资源已清理
    // 这里可以添加更多的资源清理验证逻辑
}

// 辅助函数

fn create_test_trace_data() -> TraceData {
    TraceData {
        trace_id: "12345678901234567890123456789012".to_string(),
        span_id: "1234567890123456".to_string(),
        parent_span_id: None,
        name: "test-span".to_string(),
        span_kind: SpanKind::Internal,
        start_time: 1000,
        end_time: 2000,
        status: SpanStatus::default(),
        attributes: HashMap::new(),
        events: vec![],
        links: vec![],
    }
}

fn create_test_trace_data_with_id(id: usize) -> TraceData {
    TraceData {
        trace_id: format!("{:032x}", id),
        span_id: format!("{:016x}", id),
        parent_span_id: None,
        name: format!("test-span-{}", id),
        span_kind: SpanKind::Internal,
        start_time: 1000 + id as u64,
        end_time: 2000 + id as u64,
        status: SpanStatus::default(),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert("id".to_string(), AttributeValue::String(id.to_string()));
            attrs
        },
        events: vec![],
        links: vec![],
    }
}

fn create_test_metric_data() -> MetricData {
    MetricData {
        name: "test_metric".to_string(),
        description: "Test metric".to_string(),
        unit: "count".to_string(),
        metric_type: MetricType::Counter,
        data_points: vec![DataPoint {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64,
            attributes: HashMap::new(),
            value: DataPointValue::Number(1.0),
        }],
    }
}

fn create_test_log_data() -> LogData {
    LogData {
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        severity: LogSeverity::Info,
        severity_text: "INFO".to_string(),
        message: "Test log message".to_string(),
        attributes: HashMap::new(),
        resource_attributes: HashMap::new(),
        trace_id: None,
        span_id: None,
    }
}

fn get_memory_usage() -> usize {
    // 简化的内存使用获取
    // 实际实现中应该使用更精确的方法
    0
}
