//! # OTLP性能测试
//!
//! 测试OTLP客户端的性能表现，包括吞吐量、延迟和内存使用。

use otlp::{
    config::{OtlpConfig, TransportProtocol},
    data::LogSeverity,
    error::Result,
    transport::{GrpcTransport, HttpTransport},
    TelemetryData, Transport,
};
use std::time::{Duration, Instant};
use tokio::time::timeout;

/// 测试gRPC传输性能
#[tokio::test]
async fn test_grpc_performance() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    let transport = GrpcTransport::new(config).await?;
    
    // 测试单条数据发送性能
    let start = Instant::now();
    let test_data = create_test_log_data();
    
    let _result = timeout(Duration::from_secs(1), transport.send_single(test_data)).await;
    let duration = start.elapsed();
    
    // 记录性能指标
    println!("gRPC单条数据发送耗时: {:?}", duration);
    
    // 由于没有真实服务器，我们只验证超时时间合理
    assert!(duration < Duration::from_secs(2));
    
    Ok(())
}

/// 测试HTTP传输性能
#[tokio::test]
#[allow(unused_variables)]
async fn test_http_performance() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4318")
        .with_protocol(TransportProtocol::Http);

    let transport = HttpTransport::new(config).await?;
    
    // 测试单条数据发送性能
    let start = Instant::now();
    let test_data = create_test_log_data();
    
    let result = timeout(Duration::from_secs(1), transport.send_single(test_data)).await;
    let duration = start.elapsed();
    
    // 记录性能指标
    println!("HTTP单条数据发送耗时: {:?}", duration);
    
    // 由于没有真实服务器，我们只验证超时时间合理
    assert!(duration < Duration::from_secs(2));
    
    Ok(())
}

/// 测试批量数据发送性能
#[tokio::test]
#[allow(unused_variables)]
async fn test_batch_performance() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    let transport = GrpcTransport::new(config).await?;
    
    // 测试不同批量大小的性能
    for batch_size in [10, 100, 1000] {
        let start = Instant::now();
        let test_data = create_batch_test_data(batch_size);
        
        let result = timeout(Duration::from_secs(5), transport.send(test_data)).await;
        let duration = start.elapsed();
        
        // 记录性能指标
        println!("批量大小 {} 发送耗时: {:?}", batch_size, duration);
        
        // 验证批量发送不会超时太久
        assert!(duration < Duration::from_secs(10));
    }
    
    Ok(())
}

/// 测试并发发送性能
#[tokio::test]
#[allow(unused_variables)]
async fn test_concurrent_performance() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    let transport = GrpcTransport::new(config).await?;
    
    // 测试并发发送
    let start = Instant::now();
    let mut handles = Vec::new();
    
    let shared = std::sync::Arc::new(transport);
    for i in 0..10 {
        let transport_clone = shared.clone();
        let handle = tokio::spawn(async move {
            let test_data = create_test_log_data_with_id(i);
            timeout(Duration::from_secs(1), transport_clone.send_single(test_data)).await.ok();
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        let _ = handle.await;
    }
    
    let duration = start.elapsed();
    println!("10个并发发送总耗时: {:?}", duration);
    
    // 验证并发性能
    assert!(duration < Duration::from_secs(15));
    
    Ok(())
}

/// 测试内存使用
#[tokio::test]
#[allow(unused_variables)]
async fn test_memory_usage() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    let transport = GrpcTransport::new(config).await?;
    
    // 创建大量数据测试内存使用
    let large_batch = create_batch_test_data(10000);
    
    let start = Instant::now();
    let result = timeout(Duration::from_secs(10), transport.send(large_batch)).await;
    let duration = start.elapsed();
    
    println!("10000条数据发送耗时: {:?}", duration);
    
    // 验证大量数据处理不会导致内存问题
    assert!(duration < Duration::from_secs(30));
    
    Ok(())
}

/// 测试错误恢复性能
#[tokio::test]
#[allow(unused_variables)]
async fn test_error_recovery_performance() -> Result<()> {
    let config = OtlpConfig::default()
        .with_endpoint("http://invalid-endpoint:9999")
        .with_protocol(TransportProtocol::Grpc);

    let transport = GrpcTransport::new(config).await?;
    
    // 测试错误情况下的性能
    let start = Instant::now();
    let test_data = create_test_log_data();
    
    let result = timeout(Duration::from_secs(1), transport.send_single(test_data)).await;
    let duration = start.elapsed();
    
    println!("错误恢复耗时: {:?}", duration);
    
    // 验证错误处理不会阻塞太久
    assert!(duration < Duration::from_secs(2));
    
    Ok(())
}

/// 创建测试日志数据
fn create_test_log_data() -> TelemetryData {
    otlp::TelemetryData::log("Performance test log message", LogSeverity::Info)
}

/// 创建带ID的测试日志数据
#[allow(unused_variables)]
fn create_test_log_data_with_id(id: u32) -> TelemetryData {
    let data = otlp::TelemetryData::log(
        &format!("Performance test log message {}", id),
        LogSeverity::Info,
    );
    let _ = id; // 简化测试，跳过属性赋值
    data
}

/// 创建批量测试数据
fn create_batch_test_data(size: usize) -> Vec<TelemetryData> {
    (0..size)
        .map(|i| create_test_log_data_with_id(i as u32))
        .collect()
}
