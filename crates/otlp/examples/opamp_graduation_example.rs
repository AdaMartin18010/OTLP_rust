//! OPAMP灰度策略使用示例
//!
//! 演示如何使用OPAMP灰度策略实现企业级灰度发布

use otlp::{
    GraduationStrategy, LabelSelector, MatchExpression, MatchOperator, OpampHealthStatus,
    RollbackManager,
};
use std::collections::HashMap;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建标签选择器
    let selector = LabelSelector::new()
        .with_label("env".to_string(), "prod".to_string())
        .with_label("region".to_string(), "us-east-1".to_string())
        .with_expression(MatchExpression {
            key: "version".to_string(),
            operator: MatchOperator::In,
            values: vec!["1.0".to_string(), "1.1".to_string()],
        });

    // 2. 创建灰度策略
    let strategy = GraduationStrategy::new(selector)
        .with_weight(0.1) // 10%灰度
        .with_rollback_window(Duration::from_secs(300)) // 5分钟回滚窗口
        .with_min_healthy_instances(2)
        .with_max_instances(50);

    // 3. 模拟Agent标签
    let mut agent_labels = HashMap::new();
    agent_labels.insert("env".to_string(), "prod".to_string());
    agent_labels.insert("region".to_string(), "us-east-1".to_string());
    agent_labels.insert("version".to_string(), "1.0".to_string());

    // 4. 检查是否应该应用策略
    if strategy.should_apply(&agent_labels) {
        println!("Agent匹配灰度策略");

        // 5. 计算目标实例数
        let target = strategy.calculate_target_instances(100, 95);
        println!("目标实例数: {}", target);
    }

    // 6. 创建回滚管理器
    let mut rollback_manager = RollbackManager::new(Duration::from_secs(300));

    // 7. 记录配置快照
    rollback_manager.record_snapshot("config_v1".to_string(), OpampHealthStatus::Healthy);
    rollback_manager.record_snapshot("config_v2".to_string(), OpampHealthStatus::Unhealthy);

    // 8. 检查是否需要回滚
    if let Some(rollback_hash) = rollback_manager.should_rollback(&OpampHealthStatus::Critical) {
        println!("需要回滚到配置: {}", rollback_hash);

        // 9. 执行回滚
        if let Some(previous_config) = rollback_manager.rollback() {
            println!("已回滚到配置: {}", previous_config);
        }
    }

    Ok(())
}
