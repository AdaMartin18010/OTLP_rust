//! 增强监控系统演示
//!
//! 展示如何使用增强的AlertManager和监控系统

use otlp::monitoring::{
    EnhancedAlertManager, EnhancedNotificationChannel, PredefinedAlertRules,
    EnhancedAlertSeverity,
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚨 OTLP 增强监控系统演示");
    println!("================================");

    // 创建增强告警管理器
    let alert_manager = EnhancedAlertManager::new();
    
    // 添加预定义告警规则
    println!("📋 添加预定义告警规则...");
    alert_manager.add_rule(PredefinedAlertRules::high_cpu_usage()).await?;
    alert_manager.add_rule(PredefinedAlertRules::high_memory_usage()).await?;
    alert_manager.add_rule(PredefinedAlertRules::high_latency()).await?;
    alert_manager.add_rule(PredefinedAlertRules::low_throughput()).await?;
    alert_manager.add_rule(PredefinedAlertRules::high_error_rate()).await?;
    println!("✅ 告警规则添加完成");

    // 配置通知渠道
    println!("\n📧 配置通知渠道...");
    
    // 邮件通知
    let email_channel = EnhancedNotificationChannel::Email {
        recipients: vec![
            "admin@example.com".to_string(),
            "ops@example.com".to_string(),
        ],
        smtp_server: "smtp.example.com".to_string(),
    };
    alert_manager.add_notification_channel("email".to_string(), email_channel).await?;

    // Slack通知
    let slack_channel = EnhancedNotificationChannel::Slack {
        webhook_url: "https://hooks.slack.com/services/...".to_string(),
        channel: "#alerts".to_string(),
    };
    alert_manager.add_notification_channel("slack".to_string(), slack_channel).await?;

    // PagerDuty通知
    let pagerduty_channel = EnhancedNotificationChannel::PagerDuty {
        integration_key: "your-pagerduty-key".to_string(),
    };
    alert_manager.add_notification_channel("pagerduty".to_string(), pagerduty_channel).await?;

    println!("✅ 通知渠道配置完成");

    // 启动告警管理器
    println!("\n🚀 启动告警管理器...");
    alert_manager.start().await?;
    println!("✅ 告警管理器启动完成");

    // 订阅告警事件
    let mut alert_receiver = alert_manager.subscribe_alerts();
    
    // 启动告警处理任务
    let alert_manager_clone = alert_manager.clone();
    tokio::spawn(async move {
        while let Ok(alert) = alert_receiver.recv().await {
            println!("🚨 收到告警: {} (严重程度: {:?})", alert.name, alert.severity);
            
            // 根据严重程度发送通知
            match alert.severity {
                EnhancedAlertSeverity::Info | EnhancedAlertSeverity::Warning => {
                    alert_manager_clone.send_notification(&alert, "slack").await.unwrap();
                }
                EnhancedAlertSeverity::Critical | EnhancedAlertSeverity::Emergency => {
                    alert_manager_clone.send_notification(&alert, "pagerduty").await.unwrap();
                    alert_manager_clone.send_notification(&alert, "email").await.unwrap();
                }
            }
        }
    });

    // 模拟系统监控
    println!("\n📊 开始系统监控...");
    
    // 模拟高CPU使用率告警
    println!("🔥 模拟高CPU使用率...");
    sleep(Duration::from_millis(500)).await;
    
    // 模拟高内存使用率告警
    println!("💾 模拟高内存使用率...");
    sleep(Duration::from_millis(500)).await;
    
    // 模拟高延迟告警
    println!("⏱️ 模拟高延迟...");
    sleep(Duration::from_millis(500)).await;

    // 等待告警处理
    println!("\n⏳ 等待告警处理...");
    sleep(Duration::from_secs(2)).await;

    // 获取告警统计
    println!("\n📈 获取告警统计...");
    let stats = alert_manager.get_stats().await;
    println!("  总告警数: {}", stats.total_alerts);
    println!("  活跃告警: {}", stats.active_alerts);
    println!("  已解决告警: {}", stats.resolved_alerts);
    println!("  已确认告警: {}", stats.acknowledged_alerts);
    println!("  误报数: {}", stats.false_positives);

    // 获取活跃告警
    let active_alerts = alert_manager.get_active_alerts().await;
    println!("\n🚨 当前活跃告警: {} 个", active_alerts.len());
    
    for alert in active_alerts.iter().take(3) {
        println!("  - {}: {} (当前值: {:.1}, 阈值: {:.1})", 
                 alert.name, alert.description, alert.current_value, alert.threshold);
    }

    // 演示告警确认
    if let Some(first_alert) = active_alerts.first() {
        println!("\n✅ 确认告警: {}", first_alert.name);
        alert_manager.acknowledge_alert(&first_alert.id, "demo_user".to_string()).await?;
        
        // 等待确认处理
        sleep(Duration::from_millis(100)).await;
        
        // 获取更新后的统计
        let updated_stats = alert_manager.get_stats().await;
        println!("  确认后活跃告警: {}", updated_stats.active_alerts);
        println!("  已确认告警: {}", updated_stats.acknowledged_alerts);
    }

    // 演示告警解决
    if let Some(first_alert) = active_alerts.get(1) {
        println!("\n🔧 解决告警: {}", first_alert.name);
        alert_manager.resolve_alert(&first_alert.id).await?;
        
        // 等待解决处理
        sleep(Duration::from_millis(100)).await;
        
        // 获取更新后的统计
        let final_stats = alert_manager.get_stats().await;
        println!("  解决后活跃告警: {}", final_stats.active_alerts);
        println!("  已解决告警: {}", final_stats.resolved_alerts);
    }

    // 停止告警管理器
    println!("\n🛑 停止告警管理器...");
    alert_manager.stop().await?;
    println!("✅ 告警管理器停止完成");

    println!("\n🎉 增强监控系统演示完成！");
    println!("\n📈 监控系统特性:");
    println!("  • 智能告警: 基于阈值的自动告警");
    println!("  • 多级通知: 根据严重程度选择通知渠道");
    println!("  • 告警管理: 确认、解决、历史记录");
    println!("  • 统计分析: 完整的告警统计和趋势");
    println!("  • 实时监控: 异步告警处理和通知");

    Ok(())
}

