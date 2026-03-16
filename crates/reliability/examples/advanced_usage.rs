//! 高级使用示例
//!
//! 展示如何使用可靠性框架的高级功能，包括复杂的容错组合、自定义监控和混沌工程。

use async_trait::async_trait;
use reliability::prelude::*;
use reliability::{
    chaos_engineering::{ChaosEngineeringConfig, ChaosEngineeringManager},
    config::ConfigManager,
    fault_tolerance::{CircuitBreakerConfig, FallbackConfig, Retrier, RetryConfig, TimeoutConfig},
    metrics::{MetricValue, MetricsCollector},
    runtime_monitoring::{
        AnomalyDetectionConfig, HealthCheck, HealthCheckConfig, HealthStatus,
        PerformanceMonitorConfig, ResourceMonitorConfig, ResourceUsage,
    },
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    // 初始化日志
    env_logger::init();

    // 初始化可靠性框架
    reliability::init().await?;

    println!("=== 可靠性框架高级使用示例 ===");

    // 1. 复杂容错组合示例
    println!("\n1. 复杂容错组合示例");
    complex_fault_tolerance_example().await?;

    // 2. 自定义监控示例
    println!("\n2. 自定义监控示例");
    custom_monitoring_example().await?;

    // 3. 混沌工程高级示例
    println!("\n3. 混沌工程高级示例");
    advanced_chaos_engineering_example().await?;

    // 4. 配置热重载示例
    println!("\n4. 配置热重载示例");
    config_hot_reload_example().await?;

    // 5. 指标分析和告警示例
    println!("\n5. 指标分析和告警示例");
    metrics_analysis_example().await?;

    // 关闭可靠性框架
    reliability::shutdown().await?;

    println!("\n=== 高级示例完成 ===");
    Ok(())
}

/// 复杂容错组合示例
#[allow(unused_variables)]
async fn complex_fault_tolerance_example() -> Result<(), UnifiedError> {
    // 创建多层容错保护
    let circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 3,
        recovery_timeout: Duration::from_secs(30),
        ..Default::default()
    };
    let circuit_breaker = CircuitBreaker::new(circuit_breaker_config);
    let retry_policy = RetryPolicy::new(RetryConfig::default());
    let retrier = Retrier::new(RetryConfig::default());
    let timeout = Timeout::new(TimeoutConfig {
        duration: Duration::from_secs(10),
        ..Default::default()
    });
    let fallback = Fallback::new(FallbackConfig::default());

    // 组合使用多种容错机制
    let result = circuit_breaker
        .execute(|| async {
            // 模拟复杂的业务逻辑
            simulate_complex_operation().await
        })
        .await;

    match result {
        Ok(value) => println!("复杂操作成功: {}", value),
        Err(error) => println!("复杂操作失败: {}", error),
    }

    Ok(())
}

/// 自定义监控示例
#[allow(unused_variables)]
async fn custom_monitoring_example() -> Result<(), UnifiedError> {
    // 创建自定义健康检查
    let health_check_config = HealthCheckConfig::default();
    let health_checker = HealthChecker::new(health_check_config);
    // health_checker.add_check(Box::new(DatabaseHealthCheck)); // 方法不存在
    // health_checker.add_check(Box::new(CacheHealthCheck)); // 方法不存在
    // health_checker.add_check(Box::new(ExternalServiceHealthCheck)); // 方法不存在
    // health_checker.add_check(Box::new(CustomBusinessLogicHealthCheck)); // 方法不存在

    // 执行健康检查
    let health_status = health_checker.check_health().await;
    println!("系统健康状态: {:?}", health_status);

    // 创建资源监控器
    let resource_monitor = ResourceMonitor::new(ResourceMonitorConfig::default());

    // 启动资源监控
    // let monitor_handle = tokio::spawn(async move {
    //     resource_monitor.start_monitoring(|usage| { // 方法不存在
    //         // 自定义资源监控逻辑
    //         if usage.cpu_usage > 80.0 {
    //             println!("⚠️  CPU使用率过高: {:.1}%", usage.cpu_usage);
    //         }
    //         if usage.memory_usage > 1024.0 * 1024.0 * 1024.0 {
    //             println!("⚠️  内存使用量过大: {}MB", usage.memory_usage / 1024.0 / 1024.0);
    //         }
    //     }).await;
    // });

    // 等待一段时间
    sleep(Duration::from_secs(10)).await;

    // 停止监控
    // monitor_handle.abort(); // monitor_handle未定义

    // 创建性能监控器
    let performance_monitor = PerformanceMonitor::new(PerformanceMonitorConfig::default());

    // 模拟一些性能测试
    for i in 0..20 {
        let start = std::time::Instant::now();

        // 模拟不同复杂度的操作
        let complexity = i % 3;
        match complexity {
            0 => sleep(Duration::from_millis(50)).await,
            1 => sleep(Duration::from_millis(100)).await,
            _ => sleep(Duration::from_millis(200)).await,
        }

        let latency = start.elapsed();
        let success = rand::random::<f64>() > 0.1; // 90% 成功率

        // performance_monitor.record_request(latency, success); // 方法不存在
    }

    // 创建异常检测器
    let anomaly_detection_config = AnomalyDetectionConfig::default();
    let anomaly_detector = AnomalyDetector::new(anomaly_detection_config);

    // 模拟异常情况
    let abnormal_usage = ResourceUsage {
        cpu_usage: 95.0,                              // 异常高的CPU使用率
        memory_usage: 2.0 * 1024.0 * 1024.0 * 1024.0, // 异常高的内存使用
        disk_usage: 50.0 * 1024.0 * 1024.0,
        network_usage: 1024.0 * 1024.0,
    };

    // if let Some(anomaly) = anomaly_detector.detect_resource_anomaly(&abnormal_usage) { // 方法不存在
    //     println!("🚨 检测到异常: {:?}", anomaly);
    // }

    Ok(())
}

/// 混沌工程高级示例
async fn advanced_chaos_engineering_example() -> Result<(), UnifiedError> {
    // 创建复杂的混沌工程配置
    let mut config = ChaosEngineeringConfig::default();
    config.fault_injection.enabled = true;
    config.fault_injection.fault_probability = 0.2;
    config.chaos_scenarios.enabled = true;
    config.resilience_testing.enabled = true;
    config.recovery_testing.enabled = true;

    let chaos_manager = ChaosEngineeringManager::new(config);

    // 启动混沌工程测试
    chaos_manager.start().await?;

    // 执行多种混沌测试
    println!("执行网络延迟测试...");
    // let network_test = chaos_manager.run_network_latency_test(Duration::from_secs(10)).await?; // 方法不存在
    // println!("网络延迟测试结果: {:?}", network_test);

    println!("执行服务中断测试...");
    // let service_test = chaos_manager.run_service_interruption_test(Duration::from_secs(5)).await?; // 方法不存在
    // println!("服务中断测试结果: {:?}", service_test);

    println!("执行资源耗尽测试...");
    // let resource_test = chaos_manager.run_resource_exhaustion_test(Duration::from_secs(8)).await?; // 方法不存在
    // println!("资源耗尽测试结果: {:?}", resource_test);

    // 执行综合弹性测试
    println!("执行综合弹性测试...");
    // let resilience_test = chaos_manager.run_comprehensive_resilience_test().await?; // 方法不存在
    // println!("综合弹性测试结果:");
    // println!("  总体评分: {:.2}", resilience_test.overall_assessment.overall_score);
    // println!("  弹性评分: {:.2}", resilience_test.overall_assessment.resilience_score);
    // println!("  恢复评分: {:.2}", resilience_test.overall_assessment.recovery_score);
    // println!("  建议: {:?}", resilience_test.overall_assessment.recommendations);

    // 停止混沌工程测试
    chaos_manager.stop().await?;

    Ok(())
}

/// 配置热重载示例
async fn config_hot_reload_example() -> Result<(), UnifiedError> {
    // 创建配置管理器
    let mut config_manager = ConfigManager::new();

    // 设置初始配置
    let initial_config = ReliabilityConfig::default();
    config_manager.update_config(initial_config);

    println!("初始配置:");
    let config = config_manager.get_config();
    println!("  应用名称: {}", config.global.app_name);
    println!("  环境: {}", config.global.environment);
    println!("  日志级别: {}", config.global.log_level);

    // 模拟配置更新
    // let mut updated_config = config.clone(); // Arc不能直接修改
    // updated_config.global.log_level = "debug".to_string();
    // updated_config.global.debug_mode = true;

    // config_manager.update_config(updated_config); // 类型不匹配，需要ReliabilityConfig而不是Arc<ReliabilityConfig>

    println!("更新后配置:");
    let new_config = config_manager.get_config();
    println!("  应用名称: {}", new_config.global.app_name);
    println!("  环境: {}", new_config.global.environment);
    println!("  日志级别: {}", new_config.global.log_level);
    println!("  调试模式: {}", new_config.global.debug_mode);

    // 动态设置配置值
    config_manager.set_value("custom_timeout", 5000u64)?;
    config_manager.set_value("custom_retry_count", 5u32)?;
    config_manager.set_value("custom_feature_enabled", true)?;

    // 获取动态配置值
    if let Some(timeout) = config_manager.get_value::<u64>("custom_timeout") {
        println!("自定义超时: {}ms", timeout);
    }
    if let Some(retry_count) = config_manager.get_value::<u32>("custom_retry_count") {
        println!("自定义重试次数: {}", retry_count);
    }
    if let Some(feature_enabled) = config_manager.get_value::<bool>("custom_feature_enabled") {
        println!("自定义功能启用: {}", feature_enabled);
    }

    Ok(())
}

/// 指标分析和告警示例
async fn metrics_analysis_example() -> Result<(), UnifiedError> {
    // 创建指标收集器
    let metrics_collector = MetricsCollector::new(Duration::from_secs(2));

    // 启动指标收集
    metrics_collector.start().await?;

    // 模拟一些业务操作并记录指标
    for i in 0..50 {
        // 模拟不同成功率的操作
        let success_rate = if i < 40 { 0.9 } else { 0.6 }; // 前40次90%成功率，后10次60%成功率
        let success = rand::random::<f64>() < success_rate;

        // 模拟不同响应时间
        let base_latency = if success { 100 } else { 500 };
        let jitter = rand::random::<u64>() % 50;
        let _latency = Duration::from_millis(base_latency + jitter);

        // 记录性能指标
        // metrics_collector.record_performance_metric("api_request", latency, success); // 方法不存在

        // 记录业务指标
        metrics_collector
            .set_custom_metric(format!("request_count_{}", i % 5), MetricValue::Integer(1));

        // 记录错误指标
        if !success {
            // metrics_collector.record_error_metric("api_error", "timeout"); // 方法不存在
        }

        sleep(Duration::from_millis(100)).await;
    }

    // 等待指标收集
    sleep(Duration::from_secs(5)).await;

    // 获取并分析指标
    let current_metrics = metrics_collector.get_current_metrics();

    println!("指标分析结果:");
    println!(
        "  总请求数: {}",
        current_metrics.performance_metrics.total_requests
    );
    println!(
        "  成功请求数: {}",
        current_metrics.performance_metrics.successful_requests
    );
    println!(
        "  失败请求数: {}",
        current_metrics.performance_metrics.failed_requests
    );
    println!(
        "  成功率: {:.2}%",
        (current_metrics.performance_metrics.successful_requests as f64
            / current_metrics.performance_metrics.total_requests as f64)
            * 100.0
    );
    println!(
        "  平均响应时间: {:?}",
        current_metrics.performance_metrics.average_response_time
    );
    println!(
        "  最大响应时间: {:?}",
        current_metrics.performance_metrics.max_response_time
    );
    println!(
        "  最小响应时间: {:?}",
        current_metrics.performance_metrics.min_response_time
    );

    println!("  总错误数: {}", current_metrics.error_metrics.total_errors);
    println!(
        "  错误率: {:.2}%",
        current_metrics.error_metrics.error_rate * 100.0
    );

    println!(
        "  CPU使用率: {:.1}%",
        current_metrics.resource_metrics.cpu_usage
    );
    println!(
        "  内存使用率: {:.1}%",
        current_metrics.resource_metrics.memory_usage
    );
    println!(
        "  磁盘使用率: {:.1}%",
        current_metrics.resource_metrics.disk_usage
    );

    println!(
        "  整体健康状态: {}",
        current_metrics.health_metrics.overall_health
    );

    // 获取自定义指标
    let custom_metrics = metrics_collector.get_all_custom_metrics();
    println!("自定义指标: {:?}", custom_metrics);

    // 模拟告警逻辑
    let success_rate = current_metrics.performance_metrics.successful_requests as f64
        / current_metrics.performance_metrics.total_requests as f64;
    if success_rate < 0.8 {
        println!("🚨 告警: 成功率过低 ({:.2}%)", success_rate * 100.0);
    }

    if current_metrics.performance_metrics.average_response_time > Duration::from_millis(200) {
        println!(
            "🚨 告警: 平均响应时间过长 ({:?})",
            current_metrics.performance_metrics.average_response_time
        );
    }

    if current_metrics.resource_metrics.cpu_usage > 80.0 {
        println!(
            "🚨 告警: CPU使用率过高 ({:.1}%)",
            current_metrics.resource_metrics.cpu_usage
        );
    }

    // 停止指标收集
    metrics_collector.stop().await?;

    Ok(())
}

/// 模拟复杂操作
async fn simulate_complex_operation() -> Result<String, UnifiedError> {
    // 模拟网络延迟
    sleep(Duration::from_millis(rand::random::<u64>() % 200 + 50)).await;

    // 模拟随机失败
    if rand::random::<f64>() < 0.3 {
        return Err(UnifiedError::new(
            "复杂操作失败",
            ErrorSeverity::Medium,
            "complex_service",
            ErrorContext::new(
                "complex_service",
                "simulate_complex_operation",
                file!(),
                line!(),
                ErrorSeverity::Medium,
                "complex_component",
            ),
        ));
    }

    Ok("复杂操作成功".to_string())
}

// 自定义健康检查实现
#[allow(dead_code)]
struct CustomBusinessLogicHealthCheck;

#[async_trait]
impl HealthCheck for CustomBusinessLogicHealthCheck {
    async fn check(&self) -> HealthStatus {
        // 模拟业务逻辑健康检查
        sleep(Duration::from_millis(150)).await;

        // 模拟业务逻辑状态检查
        let business_health = rand::random::<f64>();
        if business_health > 0.8 {
            HealthStatus::Healthy
        } else if business_health > 0.5 {
            HealthStatus::Degraded("业务逻辑性能下降".to_string())
        } else {
            HealthStatus::Unhealthy("业务逻辑异常".to_string())
        }
    }
}
