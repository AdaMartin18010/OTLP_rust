//! # 优化模块
//!
//! 提供智能化的性能优化和配置管理
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步优化操作
//! - **元组收集**: 使用 `collect()` 直接收集优化结果到元组
//! - **改进的配置管理**: 利用 Rust 1.92 的配置管理优化提升性能

pub mod performance_tuner;
pub mod smart_config;

// 重新导出主要类型
pub use performance_tuner::{
    ImplementationEffort, OptimizationCategory, OptimizationPriority, OptimizationSuggestion,
    PerformanceMetrics, PerformanceTargets, PerformanceTuner, PerformanceTunerStats, RiskLevel,
    TuningConfig,
};
pub use smart_config::{
    ConfigCategory, ConfigConstraint, ConfigImpact, ConfigItem, ConfigOptimization, ConfigTemplate,
    ConfigValue, ConstraintType, PerformanceProfile, PerformanceSnapshot,
    RiskLevel as ConfigRiskLevel, SmartConfigManager, SmartConfigStats,
};

/// 综合优化管理器
pub struct OptimizationManager {
    performance_tuner: PerformanceTuner,
    smart_config_manager: SmartConfigManager,
    stats: OptimizationStats,
}

/// 优化统计信息
#[derive(Debug, Default, Clone)]
pub struct OptimizationStats {
    pub total_optimizations: u64,
    pub successful_optimizations: u64,
    pub failed_optimizations: u64,
    pub performance_improvements: f64,
    pub configuration_changes: u64,
    pub average_improvement: f64,
    pub peak_improvement: f64,
}

impl Default for OptimizationManager {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationManager {
    /// 创建新的优化管理器
    pub fn new() -> Self {
        Self {
            performance_tuner: PerformanceTuner::new(TuningConfig::default()),
            smart_config_manager: SmartConfigManager::new(),
            stats: OptimizationStats::default(),
        }
    }

    /// 初始化优化管理器
    pub async fn initialize(&self) -> Result<(), anyhow::Error> {
        self.smart_config_manager.initialize_default_config()?;
        Ok(())
    }

    /// 更新性能指标
    pub fn update_performance_metrics(
        &self,
        metrics: PerformanceMetrics,
    ) -> Result<(), anyhow::Error> {
        self.performance_tuner.update_metrics(metrics)?;
        Ok(())
    }

    /// 记录性能快照
    pub fn record_performance_snapshot(
        &self,
        snapshot: PerformanceSnapshot,
    ) -> Result<(), anyhow::Error> {
        self.smart_config_manager.record_performance(snapshot)?;
        Ok(())
    }

    /// 执行综合优化分析
    pub async fn perform_optimization_analysis(&self) -> Result<OptimizationReport, anyhow::Error> {
        // 获取性能调优建议
        let performance_suggestions = self.performance_tuner.analyze_and_suggest().await?;

        // 获取配置优化建议
        let config_optimizations = self.smart_config_manager.analyze_and_optimize().await?;

        // 生成综合报告
        let total_suggestions = performance_suggestions.len() + config_optimizations.len();
        let critical_issues =
            self.count_critical_issues(&performance_suggestions, &config_optimizations);
        let estimated_improvement =
            self.calculate_estimated_improvement(&performance_suggestions, &config_optimizations);

        let report = OptimizationReport {
            timestamp: std::time::Instant::now(),
            performance_suggestions,
            config_optimizations,
            total_suggestions,
            critical_issues,
            estimated_improvement,
        };

        Ok(report)
    }

    /// 应用优化建议
    pub async fn apply_optimizations(
        &self,
        report: &OptimizationReport,
    ) -> Result<OptimizationResult, anyhow::Error> {
        let mut applied_count = 0;
        let mut failed_count = 0;
        let mut total_improvement = 0.0;

        self.apply_performance_suggestions(&report.performance_suggestions, &mut applied_count, &mut failed_count, &mut total_improvement).await;
        self.apply_config_optimizations(&report.config_optimizations, &mut applied_count, &mut failed_count, &mut total_improvement).await;

        let result = OptimizationResult {
            timestamp: std::time::Instant::now(),
            applied_optimizations: applied_count,
            failed_optimizations: failed_count,
            total_improvement,
            success_rate: self.calculate_success_rate(applied_count, failed_count),
        };

        Ok(result)
    }

    async fn apply_performance_suggestions(
        &self,
        suggestions: &[OptimizationSuggestion],
        applied_count: &mut usize,
        failed_count: &mut usize,
        total_improvement: &mut f64,
    ) {
        for suggestion in suggestions {
            match self.performance_tuner.apply_optimization(suggestion).await {
                Ok(true) => {
                    *applied_count += 1;
                    *total_improvement += suggestion.expected_improvement;
                }
                _ => *failed_count += 1,
            }
        }
    }

    async fn apply_config_optimizations(
        &self,
        optimizations: &[ConfigOptimization],
        applied_count: &mut usize,
        failed_count: &mut usize,
        total_improvement: &mut f64,
    ) {
        for optimization in optimizations {
            match self.smart_config_manager.apply_optimization(optimization).await {
                Ok(true) => {
                    *applied_count += 1;
                    *total_improvement += optimization.expected_improvement;
                }
                _ => *failed_count += 1,
            }
        }
    }

    fn calculate_success_rate(&self, applied: usize, failed: usize) -> f64 {
        if applied + failed > 0 {
            applied as f64 / (applied + failed) as f64
        } else {
            0.0
        }
    }

    /// 计算关键问题数量
    fn count_critical_issues(
        &self,
        performance_suggestions: &[OptimizationSuggestion],
        config_optimizations: &[ConfigOptimization],
    ) -> usize {
        let critical_performance = performance_suggestions
            .iter()
            .filter(|s| s.priority == OptimizationPriority::Critical)
            .count();

        let critical_config = config_optimizations
            .iter()
            .filter(|c| c.risk_level == ConfigRiskLevel::VeryHigh)
            .count();

        critical_performance + critical_config
    }

    /// 计算预估改进
    fn calculate_estimated_improvement(
        &self,
        performance_suggestions: &[OptimizationSuggestion],
        config_optimizations: &[ConfigOptimization],
    ) -> f64 {
        let performance_improvement: f64 = performance_suggestions
            .iter()
            .map(|s| s.expected_improvement)
            .sum();

        let config_improvement: f64 = config_optimizations
            .iter()
            .map(|c| c.expected_improvement)
            .sum();

        performance_improvement + config_improvement
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> OptimizationStats {
        self.stats.clone()
    }

    /// 获取性能调优器
    pub fn performance_tuner(&self) -> &PerformanceTuner {
        &self.performance_tuner
    }

    /// 获取智能配置管理器
    pub fn smart_config_manager(&self) -> &SmartConfigManager {
        &self.smart_config_manager
    }
}

/// 优化报告
#[derive(Debug, Clone)]
pub struct OptimizationReport {
    pub timestamp: std::time::Instant,
    pub performance_suggestions: Vec<OptimizationSuggestion>,
    pub config_optimizations: Vec<ConfigOptimization>,
    pub total_suggestions: usize,
    pub critical_issues: usize,
    pub estimated_improvement: f64,
}

/// 优化结果
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    pub timestamp: std::time::Instant,
    pub applied_optimizations: usize,
    pub failed_optimizations: usize,
    pub total_improvement: f64,
    pub success_rate: f64,
}

/// 优化建议优先级排序
pub fn sort_optimizations_by_priority(optimizations: &mut [OptimizationSuggestion]) {
    optimizations.sort_by(compare_by_priority);
}

fn compare_by_priority(a: &OptimizationSuggestion, b: &OptimizationSuggestion) -> std::cmp::Ordering {
    match (&a.priority, &b.priority) {
        (OptimizationPriority::Critical, OptimizationPriority::Critical) => compare_improvement(b, a),
        (OptimizationPriority::Critical, _) => std::cmp::Ordering::Less,
        (_, OptimizationPriority::Critical) => std::cmp::Ordering::Greater,
        (OptimizationPriority::High, OptimizationPriority::High) => compare_improvement(b, a),
        (OptimizationPriority::High, _) => std::cmp::Ordering::Less,
        (_, OptimizationPriority::High) => std::cmp::Ordering::Greater,
        (OptimizationPriority::Medium, OptimizationPriority::Medium) => compare_improvement(b, a),
        (OptimizationPriority::Medium, _) => std::cmp::Ordering::Less,
        (_, OptimizationPriority::Medium) => std::cmp::Ordering::Greater,
        (OptimizationPriority::Low, OptimizationPriority::Low) => compare_improvement(b, a),
    }
}

fn compare_improvement(a: &OptimizationSuggestion, b: &OptimizationSuggestion) -> std::cmp::Ordering {
    a.expected_improvement
        .partial_cmp(&b.expected_improvement)
        .unwrap_or(std::cmp::Ordering::Equal)
}

/// 配置优化优先级排序
pub fn sort_config_optimizations_by_priority(optimizations: &mut [ConfigOptimization]) {
    optimizations.sort_by(compare_config_by_priority);
}

fn compare_config_by_priority(a: &ConfigOptimization, b: &ConfigOptimization) -> std::cmp::Ordering {
    match (&a.risk_level, &b.risk_level) {
        (ConfigRiskLevel::Low, ConfigRiskLevel::Low) => compare_config_improvement(b, a),
        (ConfigRiskLevel::Low, _) => std::cmp::Ordering::Less,
        (_, ConfigRiskLevel::Low) => std::cmp::Ordering::Greater,
        (ConfigRiskLevel::Medium, ConfigRiskLevel::Medium) => compare_config_improvement(b, a),
        (ConfigRiskLevel::Medium, _) => std::cmp::Ordering::Less,
        (_, ConfigRiskLevel::Medium) => std::cmp::Ordering::Greater,
        (ConfigRiskLevel::High, ConfigRiskLevel::High) => compare_config_improvement(b, a),
        (ConfigRiskLevel::High, _) => std::cmp::Ordering::Less,
        (_, ConfigRiskLevel::High) => std::cmp::Ordering::Greater,
        (ConfigRiskLevel::VeryHigh, ConfigRiskLevel::VeryHigh) => compare_config_improvement(b, a),
    }
}

fn compare_config_improvement(a: &ConfigOptimization, b: &ConfigOptimization) -> std::cmp::Ordering {
    a.expected_improvement
        .partial_cmp(&b.expected_improvement)
        .unwrap_or(std::cmp::Ordering::Equal)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_optimization_manager_creation() {
        let manager = OptimizationManager::new();
        let stats = manager.get_stats();
        assert_eq!(stats.total_optimizations, 0);
    }

    #[tokio::test]
    async fn test_optimization_analysis() {
        let manager = OptimizationManager::new();
        manager.initialize().await.unwrap();

        // 记录多次性能数据（至少10次）以便进行分析
        for i in 0..12 {
            let metrics = PerformanceMetrics {
                cpu_usage: 95.0 - (i as f64 * 0.5), // 逐渐降低
                memory_usage: 90.0,
                throughput: 500 + (i * 10),
                latency: Duration::from_millis(200),
                error_rate: 2.0,
                connection_count: 100,
                queue_depth: 10,
                cache_hit_rate: 80.0,
            };

            // 更新性能指标（用于performance_tuner）
            manager.update_performance_metrics(metrics.clone()).unwrap();

            // 记录性能快照（用于smart_config_manager）
            let snapshot = PerformanceSnapshot {
                timestamp: std::time::Instant::now(),
                cpu_usage: metrics.cpu_usage,
                memory_usage: metrics.memory_usage,
                throughput: metrics.throughput,
                latency: metrics.latency,
                error_rate: metrics.error_rate,
                config_hash: format!("test_config_{}", i),
            };
            manager.record_performance_snapshot(snapshot).unwrap();

            // 小延迟以模拟实际场景
            tokio::time::sleep(Duration::from_millis(10)).await;
        }

        let report = manager.perform_optimization_analysis().await.unwrap();
        assert!(report.total_suggestions > 0);
    }

    #[test]
    fn test_optimization_sorting() {
        let mut optimizations = vec![
            OptimizationSuggestion {
                id: "1".to_string(),
                category: OptimizationCategory::Cpu,
                priority: OptimizationPriority::Low,
                description: "Low priority".to_string(),
                expected_improvement: 10.0,
                implementation_effort: ImplementationEffort::Low,
                risk_level: RiskLevel::Low,
                parameters: std::collections::HashMap::new(),
            },
            OptimizationSuggestion {
                id: "2".to_string(),
                category: OptimizationCategory::Memory,
                priority: OptimizationPriority::Critical,
                description: "Critical priority".to_string(),
                expected_improvement: 50.0,
                implementation_effort: ImplementationEffort::High,
                risk_level: RiskLevel::Medium,
                parameters: std::collections::HashMap::new(),
            },
        ];

        sort_optimizations_by_priority(&mut optimizations);
        assert_eq!(optimizations[0].priority, OptimizationPriority::Critical);
    }
}
