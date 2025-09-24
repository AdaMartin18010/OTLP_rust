//! # 增强错误监控系统演示
//!
//! 展示如何使用 OTLP Rust 的增强错误监控系统进行实时错误监控、
//! 告警管理和趋势分析。

use otlp::error::ErrorSeverity;
use otlp::error::{ConfigurationError, TransportError};
use otlp::{ErrorEvent, ErrorMonitoringSystem, MonitoringConfig, OtlpError, Result};
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 OTLP Rust 增强错误监控系统演示");
    println!("=====================================");

    // 示例 1: 基本监控系统设置
    basic_monitoring_demo().await?;

    // 示例 2: 告警规则配置
    alert_rules_demo().await?;

    // 示例 3: 错误事件处理
    error_event_handling_demo().await?;

    // 示例 4: 趋势分析
    trend_analysis_demo().await?;

    // 示例 5: 热点检测
    hotspot_detection_demo().await?;

    println!("\n✅ 所有监控演示完成！");
    Ok(())
}

/// 示例 1: 基本监控系统设置
async fn basic_monitoring_demo() -> Result<()> {
    println!("\n📊 示例 1: 基本监控系统设置");
    println!("---------------------------");

    // 创建监控配置
    let config = MonitoringConfig::default();

    // 创建监控系统
    let monitoring_system = ErrorMonitoringSystem::new(config)?;

    // 启动监控系统
    monitoring_system.start().await?;

    println!("  ✅ 监控系统启动成功");

    // 获取初始指标
    let metrics = monitoring_system.get_metrics().await?;
    println!("  📈 初始指标:");
    println!("    - 总错误数: {}", metrics.total_errors);
    println!("    - 错误率: {:.2}/分钟", metrics.error_rate_per_minute);
    println!("    - 系统健康评分: {:.2}", metrics.system_health_score);

    Ok(())
}

/// 示例 2: 告警规则配置
async fn alert_rules_demo() -> Result<()> {
    println!("\n🚨 示例 2: 告警规则配置");
    println!("------------------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 创建自定义告警规则
    let custom_rules = vec![
        otlp::monitoring::AlertRule {
            id: "custom_high_error_rate".to_string(),
            name: "自定义高错误率告警".to_string(),
            condition: otlp::monitoring::AlertCondition::ErrorRateThreshold {
                threshold: 0.05,                  // 5%错误率
                window: Duration::from_secs(180), // 3分钟窗口
            },
            severity: ErrorSeverity::High,
            cooldown_period: Duration::from_secs(300),
            notification_channels: vec!["email".to_string(), "slack".to_string()],
            auto_recovery: true,
            enabled: true,
        },
        otlp::monitoring::AlertRule {
            id: "transport_errors".to_string(),
            name: "传输错误告警".to_string(),
            condition: otlp::monitoring::AlertCondition::ErrorTypeSpike {
                error_type: "transport".to_string(),
                multiplier: 3.0, // 3倍增长
            },
            severity: ErrorSeverity::Critical,
            cooldown_period: Duration::from_secs(60),
            notification_channels: vec!["webhook".to_string()],
            auto_recovery: false,
            enabled: true,
        },
    ];

    // 配置告警规则
    monitoring_system
        .alert_manager()
        .configure_rules(custom_rules)
        .await?;
    println!("  ✅ 配置了 {} 条自定义告警规则", 2);

    // 获取活跃告警
    let active_alerts = monitoring_system.alert_manager().get_active_alerts().await;
    println!("  📋 当前活跃告警数: {}", active_alerts.len());

    Ok(())
}

/// 示例 3: 错误事件处理
async fn error_event_handling_demo() -> Result<()> {
    println!("\n🔍 示例 3: 错误事件处理");
    println!("------------------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 模拟不同类型的错误事件
    let error_scenarios = vec![
        ("网络连接错误", create_transport_error()),
        ("配置错误", create_configuration_error()),
        ("处理错误", create_processing_error()),
        ("序列化错误", create_serialization_error()),
        ("资源耗尽错误", create_resource_error()),
    ];

    for (name, error) in error_scenarios {
        println!("  🔥 模拟 {}: {}", name, error.to_string());

        // 创建错误事件
        let error_event = ErrorEvent::from_otlp_error(&error, "demo_service");

        // 处理错误事件
        monitoring_system.handle_error_event(error_event).await?;

        // 等待一小段时间以模拟实时处理
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    // 获取处理后的指标
    let metrics = monitoring_system.get_metrics().await?;
    println!("  📊 处理后的指标:");
    println!("    - 总错误数: {}", metrics.total_errors);
    println!("    - 错误类型分布: {:?}", metrics.error_types_distribution);
    println!("    - 活跃告警数: {}", metrics.active_alerts.len());

    Ok(())
}

/// 示例 4: 趋势分析
async fn trend_analysis_demo() -> Result<()> {
    println!("\n📈 示例 4: 趋势分析");
    println!("-------------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 模拟时间序列错误数据
    println!("  📊 模拟时间序列错误数据...");

    for i in 0..20 {
        let error_type = if i % 3 == 0 {
            "transport"
        } else {
            "processing"
        };
        let severity = if i % 5 == 0 {
            ErrorSeverity::Critical
        } else {
            ErrorSeverity::Medium
        };

        let _error = OtlpError::Internal(format!("模拟错误 {}", i));
        let error_event = ErrorEvent {
            id: format!("trend-{}", i),
            timestamp: std::time::SystemTime::now(),
            error_type: error_type.to_string(),
            severity,
            message: format!("趋势分析测试错误 {}", i),
            source: "trend_analysis_demo".to_string(),
            context: HashMap::new(),
            stack_trace: None,
            recovery_suggestion: None,
            is_retryable: true,
            is_temporary: true,
        };

        monitoring_system.handle_error_event(error_event).await?;

        // 模拟时间间隔
        tokio::time::sleep(Duration::from_millis(50)).await;
    }

    // 执行趋势分析
    let trend_result = monitoring_system.trend_analyzer().analyze_trends().await?;
    println!("  📈 趋势分析结果:");
    println!("    - 错误率: {:.2}/秒", trend_result.error_rate);
    println!("    - 趋势方向: {:?}", trend_result.trend_direction);
    println!("    - 异常数量: {}", trend_result.anomalies.len());

    Ok(())
}

/// 示例 5: 热点检测
async fn hotspot_detection_demo() -> Result<()> {
    println!("\n🔥 示例 5: 热点检测");
    println!("------------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 模拟错误热点
    println!("  🔥 模拟错误热点...");

    // 创建热点错误模式
    for i in 0..15 {
        let error_event = ErrorEvent {
            id: format!("hotspot-{}", i),
            timestamp: std::time::SystemTime::now(),
            error_type: "database_connection".to_string(),
            severity: ErrorSeverity::High,
            message: format!("数据库连接失败 {}", i),
            source: "database_service".to_string(),
            context: HashMap::from([
                ("database".to_string(), "primary_db".to_string()),
                ("connection_pool".to_string(), "exhausted".to_string()),
            ]),
            stack_trace: None,
            recovery_suggestion: Some("增加连接池大小".to_string()),
            is_retryable: true,
            is_temporary: true,
        };

        monitoring_system.handle_error_event(error_event).await?;

        // 快速连续发生错误，形成热点
        tokio::time::sleep(Duration::from_millis(20)).await;
    }

    // 检测热点
    let hotspots = monitoring_system
        .hotspot_detector()
        .detect_hotspots()
        .await?;

    println!("  🔥 检测到的错误热点:");
    for hotspot in &hotspots {
        println!("    - 模式: {}", hotspot.pattern);
        println!("    - 错误率: {:.2}", hotspot.error_rate);
        println!("    - 受影响服务: {:?}", hotspot.affected_services);
        println!("    - 建议措施: {:?}", hotspot.recommended_actions);
        println!("    - 预测升级: {}", hotspot.predicted_escalation);
        println!();
    }

    if hotspots.is_empty() {
        println!("  ✅ 未检测到错误热点");
    } else {
        println!("  ⚠️  检测到 {} 个错误热点", hotspots.len());
    }

    Ok(())
}

// 辅助函数：创建不同类型的错误

fn create_transport_error() -> OtlpError {
    OtlpError::Transport(TransportError::Connection {
        endpoint: "http://example.com:4317".to_string(),
        reason: "连接超时".to_string(),
    })
}

fn create_configuration_error() -> OtlpError {
    OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
        url: "invalid-url".to_string(),
    })
}

fn create_processing_error() -> OtlpError {
    OtlpError::Processing(otlp::error::ProcessingError::ValidationFailed {
        field: "trace_id".to_string(),
        reason: "格式无效".to_string(),
    })
}

fn create_serialization_error() -> OtlpError {
    OtlpError::Serialization(otlp::error::SerializationError::Format {
        message: "JSON解析失败".to_string(),
    })
}

fn create_resource_error() -> OtlpError {
    OtlpError::ResourceExhausted {
        resource: "memory".to_string(),
        current: 1024,
        required: 2048,
    }
}

/// 演示监控系统的实时特性
#[allow(dead_code)]
async fn demonstrate_real_time_features() -> Result<()> {
    println!("\n⏱️  实时特性演示");
    println!("----------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 模拟实时错误流
    println!("  📡 模拟实时错误流...");

    for i in 0..10 {
        let error = create_transport_error();
        let error_event = ErrorEvent::from_otlp_error(&error, &format!("service_{}", i % 3));

        monitoring_system.handle_error_event(error_event).await?;

        // 实时获取指标
        let metrics = monitoring_system.get_metrics().await?;
        println!(
            "    - 第 {} 次错误后，总错误数: {}, 健康评分: {:.2}",
            i + 1,
            metrics.total_errors,
            metrics.system_health_score
        );

        tokio::time::sleep(Duration::from_millis(200)).await;
    }

    Ok(())
}

/// 演示告警触发和处理
#[allow(dead_code)]
async fn demonstrate_alert_handling() -> Result<()> {
    println!("\n🚨 告警处理演示");
    println!("----------------");

    let config = MonitoringConfig::default();
    let monitoring_system = ErrorMonitoringSystem::new(config)?;
    monitoring_system.start().await?;

    // 配置高敏感度告警规则
    let sensitive_rules = vec![otlp::monitoring::AlertRule {
        id: "sensitive_rule".to_string(),
        name: "高敏感度告警".to_string(),
        condition: otlp::monitoring::AlertCondition::ErrorTypeSpike {
            error_type: "transport".to_string(),
            multiplier: 1.0, // 任何传输错误都触发
        },
        severity: ErrorSeverity::Medium,
        cooldown_period: Duration::from_secs(10),
        notification_channels: vec!["slack".to_string()],
        auto_recovery: true,
        enabled: true,
    }];

    monitoring_system
        .alert_manager()
        .configure_rules(sensitive_rules)
        .await?;

    // 触发告警
    println!("  🔥 触发告警...");
    let error = create_transport_error();
    let error_event = ErrorEvent::from_otlp_error(&error, "alert_demo_service");

    monitoring_system.handle_error_event(error_event).await?;

    // 检查告警状态
    let active_alerts = monitoring_system.alert_manager().get_active_alerts().await;
    println!("  📋 活跃告警数: {}", active_alerts.len());

    for alert in &active_alerts {
        println!("    - 告警ID: {}", alert.id);
        println!("    - 规则: {}", alert.rule_id);
        println!("    - 严重程度: {:?}", alert.severity);
        println!("    - 消息: {}", alert.message);
        println!("    - 状态: {:?}", alert.status);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_monitoring() {
        let result = basic_monitoring_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_error_event_handling() {
        let result = error_event_handling_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_alert_rules() {
        let result = alert_rules_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_trend_analysis() {
        let result = trend_analysis_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_hotspot_detection() {
        let result = hotspot_detection_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_real_time_features() {
        let result = demonstrate_real_time_features().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_alert_handling() {
        let result = demonstrate_alert_handling().await;
        assert!(result.is_ok());
    }
}
