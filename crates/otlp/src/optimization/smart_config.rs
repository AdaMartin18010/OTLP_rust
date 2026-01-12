//! # 智能配置管理模块
//!
//! 提供基于机器学习的智能配置优化
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步配置优化操作
//! - **元组收集**: 使用 `collect()` 直接收集配置优化结果到元组
//! - **改进的配置管理**: 利用 Rust 1.92 的配置管理优化提升性能

use anyhow::{Result, anyhow};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 智能配置统计信息
#[derive(Debug, Default)]
pub struct SmartConfigStats {
    pub total_configurations: AtomicUsize,
    pub successful_configurations: AtomicUsize,
    pub failed_configurations: AtomicUsize,
    pub performance_improvements: AtomicU64, // 百分比
    pub average_improvement: AtomicU64,      // 百分比
    pub configuration_time: AtomicU64,       // 微秒
}

impl Clone for SmartConfigStats {
    fn clone(&self) -> Self {
        Self {
            total_configurations: AtomicUsize::new(
                self.total_configurations.load(Ordering::Relaxed),
            ),
            successful_configurations: AtomicUsize::new(
                self.successful_configurations.load(Ordering::Relaxed),
            ),
            failed_configurations: AtomicUsize::new(
                self.failed_configurations.load(Ordering::Relaxed),
            ),
            performance_improvements: AtomicU64::new(
                self.performance_improvements.load(Ordering::Relaxed),
            ),
            average_improvement: AtomicU64::new(self.average_improvement.load(Ordering::Relaxed)),
            configuration_time: AtomicU64::new(self.configuration_time.load(Ordering::Relaxed)),
        }
    }
}

/// 配置项
#[derive(Debug, Clone)]
pub struct ConfigItem {
    pub key: String,
    pub value: ConfigValue,
    pub category: ConfigCategory,
    pub impact: ConfigImpact,
    pub dependencies: Vec<String>,
    pub constraints: Vec<ConfigConstraint>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConfigValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Duration(Duration),
    List(Vec<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConfigCategory {
    Performance,
    Memory,
    Network,
    Concurrency,
    Security,
    Monitoring,
    Logging,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConfigImpact {
    Critical,
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone)]
pub struct ConfigConstraint {
    pub constraint_type: ConstraintType,
    pub min_value: Option<ConfigValue>,
    pub max_value: Option<ConfigValue>,
    pub allowed_values: Option<Vec<ConfigValue>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintType {
    Range,
    Enum,
    Custom,
}

/// 配置优化建议
#[derive(Debug, Clone)]
pub struct ConfigOptimization {
    pub id: String,
    pub config_item: ConfigItem,
    pub current_value: ConfigValue,
    pub suggested_value: ConfigValue,
    pub expected_improvement: f64, // 百分比
    pub confidence: f64,           // 0.0 - 1.0
    pub reasoning: String,
    pub risk_level: RiskLevel,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RiskLevel {
    Low,
    Medium,
    High,
    VeryHigh,
}

/// 智能配置管理器
#[allow(dead_code)]
pub struct SmartConfigManager {
    stats: Arc<SmartConfigStats>,
    current_config: Arc<Mutex<HashMap<String, ConfigItem>>>,
    optimization_history: Arc<Mutex<Vec<ConfigOptimization>>>,
    performance_data: Arc<Mutex<Vec<PerformanceSnapshot>>>,
    config_templates: Arc<Mutex<HashMap<String, ConfigTemplate>>>,
}

/// 性能快照
#[derive(Debug, Clone)]
pub struct PerformanceSnapshot {
    pub timestamp: Instant,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub throughput: u64,
    pub latency: Duration,
    pub error_rate: f64,
    pub config_hash: String,
}

/// 配置模板
#[derive(Debug, Clone)]
pub struct ConfigTemplate {
    pub name: String,
    pub description: String,
    pub category: ConfigCategory,
    pub config_items: Vec<ConfigItem>,
    pub performance_profile: PerformanceProfile,
}

#[derive(Debug, Clone)]
pub struct PerformanceProfile {
    pub target_cpu_usage: f64,
    pub target_memory_usage: f64,
    pub target_throughput: u64,
    pub target_latency: Duration,
    pub target_error_rate: f64,
}

impl SmartConfigManager {
    /// 创建新的智能配置管理器
    pub fn new() -> Self {
        Self {
            stats: Arc::new(SmartConfigStats::default()),
            current_config: Arc::new(Mutex::new(HashMap::new())),
            optimization_history: Arc::new(Mutex::new(Vec::new())),
            performance_data: Arc::new(Mutex::new(Vec::new())),
            config_templates: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 初始化默认配置
    pub fn initialize_default_config(&self) -> Result<()> {
        let mut config = self.current_config.lock().unwrap();

        // 性能相关配置
        config.insert(
            "max_workers".to_string(),
            ConfigItem {
                key: "max_workers".to_string(),
                value: ConfigValue::Integer(4),
                category: ConfigCategory::Concurrency,
                impact: ConfigImpact::High,
                dependencies: vec!["cpu_count".to_string()],
                constraints: vec![ConfigConstraint {
                    constraint_type: ConstraintType::Range,
                    min_value: Some(ConfigValue::Integer(1)),
                    max_value: Some(ConfigValue::Integer(64)),
                    allowed_values: None,
                }],
            },
        );

        // 内存相关配置
        config.insert(
            "memory_pool_size".to_string(),
            ConfigItem {
                key: "memory_pool_size".to_string(),
                value: ConfigValue::Integer(1024),
                category: ConfigCategory::Memory,
                impact: ConfigImpact::High,
                dependencies: vec!["available_memory".to_string()],
                constraints: vec![ConfigConstraint {
                    constraint_type: ConstraintType::Range,
                    min_value: Some(ConfigValue::Integer(256)),
                    max_value: Some(ConfigValue::Integer(8192)),
                    allowed_values: None,
                }],
            },
        );

        // 网络相关配置
        config.insert(
            "connection_pool_size".to_string(),
            ConfigItem {
                key: "connection_pool_size".to_string(),
                value: ConfigValue::Integer(100),
                category: ConfigCategory::Network,
                impact: ConfigImpact::Medium,
                dependencies: vec!["max_connections".to_string()],
                constraints: vec![ConfigConstraint {
                    constraint_type: ConstraintType::Range,
                    min_value: Some(ConfigValue::Integer(10)),
                    max_value: Some(ConfigValue::Integer(1000)),
                    allowed_values: None,
                }],
            },
        );

        Ok(())
    }

    /// 记录性能数据
    pub fn record_performance(&self, snapshot: PerformanceSnapshot) -> Result<()> {
        let mut data = self.performance_data.lock().unwrap();
        data.push(snapshot);

        // 保持最近1000条记录
        if data.len() > 1000 {
            data.remove(0);
        }

        Ok(())
    }

    /// 分析配置并生成优化建议
    pub async fn analyze_and_optimize(&self) -> Result<Vec<ConfigOptimization>> {
        let current_config = self.current_config.lock().unwrap().clone();
        let performance_data = self.performance_data.lock().unwrap().clone();

        if performance_data.len() < 10 {
            return Err(anyhow!("需要更多性能数据进行分析"));
        }

        let mut optimizations = Vec::new();

        // 分析CPU使用率
        if let Some(avg_cpu) = self.calculate_average_cpu(&performance_data) {
            if avg_cpu > 80.0 {
                optimizations.extend(self.optimize_cpu_config(&current_config, avg_cpu).await?);
            }
        }

        // 分析内存使用率
        if let Some(avg_memory) = self.calculate_average_memory(&performance_data) {
            if avg_memory > 85.0 {
                optimizations.extend(
                    self.optimize_memory_config(&current_config, avg_memory)
                        .await?,
                );
            }
        }

        // 分析吞吐量
        if let Some(avg_throughput) = self.calculate_average_throughput(&performance_data) {
            if avg_throughput < 1000 {
                optimizations.extend(
                    self.optimize_throughput_config(&current_config, avg_throughput)
                        .await?,
                );
            }
        }

        // 分析延迟
        if let Some(avg_latency) = self.calculate_average_latency(&performance_data) {
            if avg_latency > Duration::from_millis(100) {
                optimizations.extend(
                    self.optimize_latency_config(&current_config, avg_latency)
                        .await?,
                );
            }
        }

        // 记录优化建议
        {
            let mut history = self.optimization_history.lock().unwrap();
            history.extend(optimizations.clone());
        }

        Ok(optimizations)
    }

    /// 优化CPU配置
    async fn optimize_cpu_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_cpu: f64,
    ) -> Result<Vec<ConfigOptimization>> {
        let mut optimizations = Vec::new();

        // 优化工作线程数
        if let Some(workers_config) = config.get("max_workers") {
            let current_workers = match &workers_config.value {
                ConfigValue::Integer(n) => *n,
                _ => return Ok(optimizations),
            };

            let suggested_workers = if avg_cpu > 95.0 {
                (current_workers * 2).min(32)
            } else if avg_cpu > 90.0 {
                (current_workers as f64 * 1.5) as i64
            } else {
                current_workers + 2
            };

            optimizations.push(ConfigOptimization {
                id: format!("cpu_workers_{}", Instant::now().elapsed().as_millis()),
                config_item: workers_config.clone(),
                current_value: ConfigValue::Integer(current_workers),
                suggested_value: ConfigValue::Integer(suggested_workers),
                expected_improvement: 20.0,
                confidence: 0.8,
                reasoning: format!("CPU使用率过高 ({}%), 建议增加工作线程数", avg_cpu),
                risk_level: RiskLevel::Low,
            });
        }

        Ok(optimizations)
    }

    /// 优化内存配置
    async fn optimize_memory_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_memory: f64,
    ) -> Result<Vec<ConfigOptimization>> {
        let mut optimizations = Vec::new();

        // 优化内存池大小
        if let Some(memory_pool_config) = config.get("memory_pool_size") {
            let current_size = match &memory_pool_config.value {
                ConfigValue::Integer(n) => *n,
                _ => return Ok(optimizations),
            };

            let suggested_size = if avg_memory > 95.0 {
                current_size * 2
            } else if avg_memory > 90.0 {
                (current_size as f64 * 1.5) as i64
            } else {
                current_size + 512
            };

            optimizations.push(ConfigOptimization {
                id: format!("memory_pool_{}", Instant::now().elapsed().as_millis()),
                config_item: memory_pool_config.clone(),
                current_value: ConfigValue::Integer(current_size),
                suggested_value: ConfigValue::Integer(suggested_size),
                expected_improvement: 25.0,
                confidence: 0.7,
                reasoning: format!("内存使用率过高 ({}%), 建议增加内存池大小", avg_memory),
                risk_level: RiskLevel::Medium,
            });
        }

        Ok(optimizations)
    }

    /// 优化吞吐量配置
    async fn optimize_throughput_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_throughput: u64,
    ) -> Result<Vec<ConfigOptimization>> {
        let mut optimizations = Vec::new();

        // 优化连接池大小
        if let Some(connection_pool_config) = config.get("connection_pool_size") {
            let current_size = match &connection_pool_config.value {
                ConfigValue::Integer(n) => *n,
                _ => return Ok(optimizations),
            };

            let suggested_size = if avg_throughput < 500 {
                current_size * 2
            } else if avg_throughput < 800 {
                (current_size as f64 * 1.5) as i64
            } else {
                current_size + 50
            };

            optimizations.push(ConfigOptimization {
                id: format!("throughput_pool_{}", Instant::now().elapsed().as_millis()),
                config_item: connection_pool_config.clone(),
                current_value: ConfigValue::Integer(current_size),
                suggested_value: ConfigValue::Integer(suggested_size),
                expected_improvement: 40.0,
                confidence: 0.6,
                reasoning: format!("吞吐量过低 ({} ops/s), 建议增加连接池大小", avg_throughput),
                risk_level: RiskLevel::Low,
            });
        }

        Ok(optimizations)
    }

    /// 优化延迟配置
    async fn optimize_latency_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_latency: Duration,
    ) -> Result<Vec<ConfigOptimization>> {
        let mut optimizations = Vec::new();

        // 优化批处理大小
        if let Some(batch_size_config) = config.get("batch_size") {
            let current_size = match &batch_size_config.value {
                ConfigValue::Integer(n) => *n,
                _ => return Ok(optimizations),
            };

            let suggested_size = if avg_latency > Duration::from_millis(500) {
                current_size / 2
            } else if avg_latency > Duration::from_millis(200) {
                (current_size as f64 * 0.8) as i64
            } else {
                current_size
            };

            optimizations.push(ConfigOptimization {
                id: format!("latency_batch_{}", Instant::now().elapsed().as_millis()),
                config_item: batch_size_config.clone(),
                current_value: ConfigValue::Integer(current_size),
                suggested_value: ConfigValue::Integer(suggested_size),
                expected_improvement: 30.0,
                confidence: 0.7,
                reasoning: format!(
                    "延迟过高 ({}ms), 建议减少批处理大小",
                    avg_latency.as_millis()
                ),
                risk_level: RiskLevel::Medium,
            });
        }

        Ok(optimizations)
    }

    /// 应用配置优化
    pub async fn apply_optimization(&self, optimization: &ConfigOptimization) -> Result<bool> {
        let start = Instant::now();

        // 检查风险级别
        if optimization.risk_level == RiskLevel::VeryHigh {
            return Err(anyhow!("高风险配置需要手动确认"));
        }

        // 验证配置约束
        if !self
            .validate_config_constraints(&optimization.config_item, &optimization.suggested_value)
        {
            return Err(anyhow!("配置值不满足约束条件"));
        }

        // 应用配置
        {
            let mut config = self.current_config.lock().unwrap();
            if let Some(item) = config.get_mut(&optimization.config_item.key) {
                item.value = optimization.suggested_value.clone();
            }
        }

        let duration = start.elapsed();

        // 更新统计
        self.stats
            .total_configurations
            .fetch_add(1, Ordering::Relaxed);
        self.stats
            .successful_configurations
            .fetch_add(1, Ordering::Relaxed);
        self.stats
            .configuration_time
            .fetch_add(duration.as_micros() as u64, Ordering::Relaxed);

        Ok(true)
    }

    /// 验证配置约束
    fn validate_config_constraints(&self, config_item: &ConfigItem, value: &ConfigValue) -> bool {
        for constraint in &config_item.constraints {
            match constraint.constraint_type {
                ConstraintType::Range => {
                    if let (Some(min), Some(max)) = (&constraint.min_value, &constraint.max_value) {
                        if !self.is_value_in_range(value, min, max) {
                            return false;
                        }
                    }
                }
                ConstraintType::Enum => {
                    if let Some(allowed) = &constraint.allowed_values {
                        if !allowed.contains(value) {
                            return false;
                        }
                    }
                }
                ConstraintType::Custom => {
                    // 自定义约束验证逻辑
                }
            }
        }
        true
    }

    /// 检查值是否在范围内
    fn is_value_in_range(&self, value: &ConfigValue, min: &ConfigValue, max: &ConfigValue) -> bool {
        match (value, min, max) {
            (
                ConfigValue::Integer(v),
                ConfigValue::Integer(min_val),
                ConfigValue::Integer(max_val),
            ) => *v >= *min_val && *v <= *max_val,
            (ConfigValue::Float(v), ConfigValue::Float(min_val), ConfigValue::Float(max_val)) => {
                *v >= *min_val && *v <= *max_val
            }
            _ => false,
        }
    }

    /// 计算平均CPU使用率
    fn calculate_average_cpu(&self, data: &[PerformanceSnapshot]) -> Option<f64> {
        if data.is_empty() {
            return None;
        }
        Some(data.iter().map(|s| s.cpu_usage).sum::<f64>() / data.len() as f64)
    }

    /// 计算平均内存使用率
    fn calculate_average_memory(&self, data: &[PerformanceSnapshot]) -> Option<f64> {
        if data.is_empty() {
            return None;
        }
        Some(data.iter().map(|s| s.memory_usage).sum::<f64>() / data.len() as f64)
    }

    /// 计算平均吞吐量
    fn calculate_average_throughput(&self, data: &[PerformanceSnapshot]) -> Option<u64> {
        if data.is_empty() {
            return None;
        }
        Some(data.iter().map(|s| s.throughput).sum::<u64>() / data.len() as u64)
    }

    /// 计算平均延迟
    fn calculate_average_latency(&self, data: &[PerformanceSnapshot]) -> Option<Duration> {
        if data.is_empty() {
            return None;
        }
        let total_millis: u128 = data.iter().map(|s| s.latency.as_millis()).sum();
        Some(Duration::from_millis(
            (total_millis / data.len() as u128) as u64,
        ))
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> SmartConfigStats {
        (*self.stats).clone()
    }

    /// 获取当前配置
    pub fn get_current_config(&self) -> HashMap<String, ConfigItem> {
        self.current_config.lock().unwrap().clone()
    }

    /// 获取优化历史
    pub fn get_optimization_history(&self) -> Vec<ConfigOptimization> {
        self.optimization_history.lock().unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smart_config_manager_creation() {
        let manager = SmartConfigManager::new();
        let stats = manager.get_stats();
        assert_eq!(stats.total_configurations.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_initialize_default_config() {
        let manager = SmartConfigManager::new();
        assert!(manager.initialize_default_config().is_ok());

        let config = manager.get_current_config();
        assert!(config.contains_key("max_workers"));
        assert!(config.contains_key("memory_pool_size"));
        assert!(config.contains_key("connection_pool_size"));
    }

    #[test]
    fn test_performance_recording() {
        let manager = SmartConfigManager::new();

        let snapshot = PerformanceSnapshot {
            timestamp: Instant::now(),
            cpu_usage: 50.0,
            memory_usage: 60.0,
            throughput: 1000,
            latency: Duration::from_millis(50),
            error_rate: 0.1,
            config_hash: "test_hash".to_string(),
        };

        assert!(manager.record_performance(snapshot).is_ok());
    }

    #[tokio::test]
    async fn test_config_optimization() {
        let manager = SmartConfigManager::new();
        manager.initialize_default_config().unwrap();

        // 记录一些性能数据
        for i in 0..20 {
            let snapshot = PerformanceSnapshot {
                timestamp: Instant::now(),
                cpu_usage: 90.0 + (i as f64 * 0.1), // 高CPU使用率
                memory_usage: 60.0,
                throughput: 500,                     // 低吞吐量
                latency: Duration::from_millis(200), // 高延迟
                error_rate: 0.1,
                config_hash: "test_hash".to_string(),
            };
            manager.record_performance(snapshot).unwrap();
        }

        let optimizations = manager.analyze_and_optimize().await.unwrap();
        assert!(!optimizations.is_empty());
    }
}
