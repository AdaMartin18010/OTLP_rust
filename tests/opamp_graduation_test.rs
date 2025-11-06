//! OPAMP灰度策略集成测试

use otlp::opamp::graduation::{
    GraduationStrategy, HealthStatus, LabelSelector, MatchExpression, MatchOperator,
    RollbackManager,
};
use std::collections::HashMap;
use std::time::Duration;

#[test]
fn test_label_selector_integration() {
    let selector = LabelSelector::new()
        .with_label("env".to_string(), "prod".to_string())
        .with_expression(MatchExpression {
            key: "version".to_string(),
            operator: MatchOperator::In,
            values: vec!["1.0".to_string(), "1.1".to_string()],
        });

    let mut labels = HashMap::new();
    labels.insert("env".to_string(), "prod".to_string());
    labels.insert("version".to_string(), "1.0".to_string());

    assert!(selector.matches(&labels));
}

#[test]
fn test_graduation_strategy_integration() {
    let selector = LabelSelector::new().with_label("region".to_string(), "us-east-1".to_string());

    let strategy = GraduationStrategy::new(selector)
        .with_weight(0.1) // 10%
        .with_min_healthy_instances(2)
        .with_rollback_window(Duration::from_secs(300));

    // 测试计算目标实例数
    let target = strategy.calculate_target_instances(100, 95);
    assert_eq!(target, 10); // 100 * 0.1 = 10

    // 测试最小实例数限制
    let target_min = strategy.calculate_target_instances(5, 5);
    assert_eq!(target_min, 2); // 最小2个实例
}

#[test]
fn test_rollback_manager_integration() {
    let mut manager = RollbackManager::new(Duration::from_secs(300));

    // 记录健康配置
    manager.record_snapshot("hash1".to_string(), HealthStatus::Healthy);

    // 记录不健康配置
    manager.record_snapshot("hash2".to_string(), HealthStatus::Unhealthy);

    // 检查是否需要回滚
    let rollback_hash = manager.should_rollback(&HealthStatus::Critical);
    assert_eq!(rollback_hash, Some("hash1".to_string()));

    // 执行回滚
    let rollback_result = manager.rollback();
    assert_eq!(rollback_result, Some("hash1".to_string()));
}

#[test]
fn test_graduation_strategy_weight_calculation() {
    let selector = LabelSelector::new();
    let strategy = GraduationStrategy::new(selector).with_weight(0.5); // 50%

    // 测试不同总实例数
    assert_eq!(strategy.calculate_target_instances(100, 100), 50);
    assert_eq!(strategy.calculate_target_instances(200, 200), 100);
    assert_eq!(strategy.calculate_target_instances(10, 10), 5);
}

#[test]
fn test_graduation_strategy_max_instances() {
    let selector = LabelSelector::new();
    let strategy = GraduationStrategy::new(selector)
        .with_weight(1.0) // 100%
        .with_max_instances(50);

    // 即使权重是100%，也不应超过最大实例数
    assert_eq!(strategy.calculate_target_instances(100, 100), 50);
}

#[test]
fn test_label_selector_complex_expressions() {
    let selector = LabelSelector::new()
        .with_label("env".to_string(), "prod".to_string())
        .with_expression(MatchExpression {
            key: "version".to_string(),
            operator: MatchOperator::In,
            values: vec!["1.0".to_string(), "1.1".to_string()],
        })
        .with_expression(MatchExpression {
            key: "region".to_string(),
            operator: MatchOperator::Exists,
            values: vec![],
        });

    let mut labels = HashMap::new();
    labels.insert("env".to_string(), "prod".to_string());
    labels.insert("version".to_string(), "1.0".to_string());
    labels.insert("region".to_string(), "us-east-1".to_string());

    assert!(selector.matches(&labels));

    // 测试不匹配的情况
    labels.insert("version".to_string(), "2.0".to_string());
    assert!(!selector.matches(&labels));
}
