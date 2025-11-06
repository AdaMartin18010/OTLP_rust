//! # OPAMP 灰度策略模块
//!
//! 实现OPAMP灰度发布策略，包括标签选择器、权重分配和回滚窗口。
//!
//! ## 功能
//!
//! - **标签选择器**: 基于标签匹配Agent实例
//! - **权重分配**: 控制灰度发布的比例
//! - **回滚窗口**: 自动回滚不健康的配置

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

/// 标签选择器
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LabelSelector {
    /// 匹配的标签键值对 (精确匹配)
    pub match_labels: HashMap<String, String>,

    /// 匹配表达式 (支持 !=, in, notin, exists)
    pub match_expressions: Vec<MatchExpression>,
}

/// 匹配表达式
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MatchExpression {
    /// 标签键
    pub key: String,

    /// 操作符
    pub operator: MatchOperator,

    /// 值列表 (用于 In/NotIn 操作符)
    pub values: Vec<String>,
}

/// 匹配操作符
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum MatchOperator {
    /// 值在列表中
    In,

    /// 值不在列表中
    NotIn,

    /// 标签存在
    Exists,

    /// 标签不存在
    DoesNotExist,
}

impl LabelSelector {
    /// 创建新的标签选择器
    pub fn new() -> Self {
        Self {
            match_labels: HashMap::new(),
            match_expressions: Vec::new(),
        }
    }

    /// 添加匹配标签
    pub fn with_label(mut self, key: String, value: String) -> Self {
        self.match_labels.insert(key, value);
        self
    }

    /// 添加匹配表达式
    pub fn with_expression(mut self, expression: MatchExpression) -> Self {
        self.match_expressions.push(expression);
        self
    }

    /// 检查Agent是否匹配选择器
    pub fn matches(&self, agent_labels: &HashMap<String, String>) -> bool {
        // 检查精确匹配的标签
        for (key, value) in &self.match_labels {
            if agent_labels.get(key) != Some(value) {
                return false;
            }
        }

        // 检查匹配表达式
        for expr in &self.match_expressions {
            if !self.matches_expression(expr, agent_labels) {
                return false;
            }
        }

        true
    }

    /// 检查单个表达式是否匹配
    fn matches_expression(
        &self,
        expr: &MatchExpression,
        agent_labels: &HashMap<String, String>,
    ) -> bool {
        match expr.operator {
            MatchOperator::In => agent_labels
                .get(&expr.key)
                .map(|v| expr.values.contains(v))
                .unwrap_or(false),
            MatchOperator::NotIn => agent_labels
                .get(&expr.key)
                .map(|v| !expr.values.contains(v))
                .unwrap_or(true),
            MatchOperator::Exists => agent_labels.contains_key(&expr.key),
            MatchOperator::DoesNotExist => !agent_labels.contains_key(&expr.key),
        }
    }
}

impl Default for LabelSelector {
    fn default() -> Self {
        Self::new()
    }
}

/// 灰度策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraduationStrategy {
    /// 标签选择器
    pub label_selector: LabelSelector,

    /// 权重 (0.0 - 1.0)
    pub weight: f64,

    /// 回滚窗口
    pub rollback_window: Duration,

    /// 最小健康实例数
    pub min_healthy_instances: usize,

    /// 最大实例数限制
    pub max_instances: Option<usize>,
}

impl GraduationStrategy {
    /// 创建新的灰度策略
    pub fn new(label_selector: LabelSelector) -> Self {
        Self {
            label_selector,
            weight: 1.0,
            rollback_window: Duration::from_secs(300), // 默认5分钟
            min_healthy_instances: 1,
            max_instances: None,
        }
    }

    /// 设置权重
    pub fn with_weight(mut self, weight: f64) -> Self {
        assert!(weight >= 0.0 && weight <= 1.0, "权重必须在0.0-1.0之间");
        self.weight = weight;
        self
    }

    /// 设置回滚窗口
    pub fn with_rollback_window(mut self, window: Duration) -> Self {
        self.rollback_window = window;
        self
    }

    /// 设置最小健康实例数
    pub fn with_min_healthy_instances(mut self, min: usize) -> Self {
        self.min_healthy_instances = min;
        self
    }

    /// 设置最大实例数
    pub fn with_max_instances(mut self, max: usize) -> Self {
        self.max_instances = Some(max);
        self
    }

    /// 计算应该下发的实例数
    pub fn calculate_target_instances(
        &self,
        total_instances: usize,
        healthy_instances: usize,
    ) -> usize {
        // 基于权重计算目标实例数
        let target = (total_instances as f64 * self.weight).ceil() as usize;

        // 确保不超过健康实例数
        let target = target.min(healthy_instances);

        // 确保不少于最小健康实例数
        let target = target.max(self.min_healthy_instances);

        // 应用最大实例数限制
        if let Some(max) = self.max_instances {
            target.min(max)
        } else {
            target
        }
    }

    /// 检查是否应该应用此策略
    pub fn should_apply(&self, agent_labels: &HashMap<String, String>) -> bool {
        self.label_selector.matches(agent_labels)
    }
}

/// 回滚管理器
#[derive(Debug, Clone)]
pub struct RollbackManager {
    /// 配置历史快照
    config_history: Vec<ConfigSnapshot>,

    /// 回滚窗口
    rollback_window: Duration,
}

/// 配置快照
#[derive(Debug, Clone)]
pub struct ConfigSnapshot {
    /// 配置哈希
    pub config_hash: String,

    /// 时间戳
    pub timestamp: std::time::SystemTime,

    /// 健康状态
    pub health_status: HealthStatus,
}

/// 健康状态
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum HealthStatus {
    /// 健康
    Healthy,

    /// 警告
    Warning,

    /// 不健康
    Unhealthy,

    /// 严重不健康
    Critical,
}

impl HealthStatus {
    /// 检查是否比另一个状态更差
    pub fn is_worse_than(&self, other: &Self) -> bool {
        self > other
    }
}

impl RollbackManager {
    /// 创建新的回滚管理器
    pub fn new(rollback_window: Duration) -> Self {
        Self {
            config_history: Vec::new(),
            rollback_window,
        }
    }

    /// 记录配置快照
    pub fn record_snapshot(&mut self, config_hash: String, health_status: HealthStatus) {
        let snapshot = ConfigSnapshot {
            config_hash,
            timestamp: std::time::SystemTime::now(),
            health_status,
        };
        self.config_history.push(snapshot);

        // 清理超出回滚窗口的历史记录
        self.cleanup_old_snapshots();
    }

    /// 检查是否需要回滚
    pub fn should_rollback(&self, current_health: &HealthStatus) -> Option<String> {
        if let Some(latest) = self.config_history.last() {
            // 如果健康状态下降，且在回滚窗口内
            if current_health.is_worse_than(&latest.health_status) {
                let elapsed = latest.timestamp.elapsed().unwrap_or_default();
                if elapsed < self.rollback_window {
                    // 查找上一个健康的配置
                    for snapshot in self.config_history.iter().rev().skip(1) {
                        if snapshot.health_status == HealthStatus::Healthy {
                            return Some(snapshot.config_hash.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// 执行回滚
    pub fn rollback(&mut self) -> Option<String> {
        // 移除当前不健康的配置
        if let Some(latest) = self.config_history.last() {
            if latest.health_status != HealthStatus::Healthy {
                self.config_history.pop();
            }
        }

        // 查找上一个健康的配置
        for snapshot in self.config_history.iter().rev() {
            if snapshot.health_status == HealthStatus::Healthy {
                return Some(snapshot.config_hash.clone());
            }
        }

        None
    }

    /// 清理超出回滚窗口的历史记录
    fn cleanup_old_snapshots(&mut self) {
        let now = std::time::SystemTime::now();
        self.config_history.retain(|snapshot| {
            now.duration_since(snapshot.timestamp)
                .map(|d| d < self.rollback_window)
                .unwrap_or(false)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_label_selector_exact_match() {
        let selector = LabelSelector::new()
            .with_label("env".to_string(), "prod".to_string())
            .with_label("region".to_string(), "us-east-1".to_string());

        let mut labels = HashMap::new();
        labels.insert("env".to_string(), "prod".to_string());
        labels.insert("region".to_string(), "us-east-1".to_string());

        assert!(selector.matches(&labels));

        labels.insert("env".to_string(), "dev".to_string());
        assert!(!selector.matches(&labels));
    }

    #[test]
    fn test_label_selector_in_operator() {
        let selector = LabelSelector::new().with_expression(MatchExpression {
            key: "version".to_string(),
            operator: MatchOperator::In,
            values: vec!["1.0".to_string(), "1.1".to_string()],
        });

        let mut labels = HashMap::new();
        labels.insert("version".to_string(), "1.0".to_string());
        assert!(selector.matches(&labels));

        labels.insert("version".to_string(), "2.0".to_string());
        assert!(!selector.matches(&labels));
    }

    #[test]
    fn test_graduation_strategy_calculate() {
        let selector = LabelSelector::new();
        let strategy = GraduationStrategy::new(selector)
            .with_weight(0.1) // 10%
            .with_min_healthy_instances(2);

        let target = strategy.calculate_target_instances(100, 95);
        assert_eq!(target, 10); // 100 * 0.1 = 10
    }

    #[test]
    fn test_rollback_manager() {
        let mut manager = RollbackManager::new(Duration::from_secs(300));

        manager.record_snapshot("hash1".to_string(), HealthStatus::Healthy);
        manager.record_snapshot("hash2".to_string(), HealthStatus::Unhealthy);

        let rollback_hash = manager.should_rollback(&HealthStatus::Critical);
        assert_eq!(rollback_hash, Some("hash1".to_string()));
    }
}
