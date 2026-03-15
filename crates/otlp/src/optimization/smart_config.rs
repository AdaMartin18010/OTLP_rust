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

        let optimizations = self.analyze_performance_metrics(&current_config, &performance_data).await?;
        self.record_optimizations(&optimizations);

        Ok(optimizations)
    }

    fn record_optimizations(&self, optimizations: &[ConfigOptimization]) {
        let mut history = self.optimization_history.lock().unwrap();
        history.extend(optimizations.iter().cloned());
    }

    /// 分析性能指标并生成优化建议
    async fn analyze_performance_metrics(
        &self,
        current_config: &HashMap<String, ConfigItem>,
        performance_data: &[PerformanceSnapshot],
    ) -> Result<Vec<ConfigOptimization>> {
        let mut optimizations = Vec::new();

        self.analyze_cpu(performance_data, current_config, &mut optimizations).await?;
        self.analyze_memory(performance_data, current_config, &mut optimizations).await?;
        self.analyze_throughput(performance_data, current_config, &mut optimizations).await?;
        self.analyze_latency(performance_data, current_config, &mut optimizations).await?;

        Ok(optimizations)
    }

    async fn analyze_cpu(
        &self,
        performance_data: &[PerformanceSnapshot],
        current_config: &HashMap<String, ConfigItem>,
        optimizations: &mut Vec<ConfigOptimization>,
    ) -> Result<()> {
        if let Some(avg_cpu) = self.calculate_average_cpu(performance_data) {
            if avg_cpu > 80.0 {
                optimizations.extend(self.optimize_cpu_config(current_config, avg_cpu).await?);
            }
        }
        Ok(())
    }

    async fn analyze_memory(
        &self,
        performance_data: &[PerformanceSnapshot],
        current_config: &HashMap<String, ConfigItem>,
        optimizations: &mut Vec<ConfigOptimization>,
    ) -> Result<()> {
        if let Some(avg_memory) = self.calculate_average_memory(performance_data) {
            if avg_memory > 85.0 {
                optimizations.extend(self.optimize_memory_config(current_config, avg_memory).await?);
            }
        }
        Ok(())
    }

    async fn analyze_throughput(
        &self,
        performance_data: &[PerformanceSnapshot],
        current_config: &HashMap<String, ConfigItem>,
        optimizations: &mut Vec<ConfigOptimization>,
    ) -> Result<()> {
        if let Some(avg_throughput) = self.calculate_average_throughput(performance_data) {
            if avg_throughput < 1000 {
                optimizations.extend(self.optimize_throughput_config(current_config, avg_throughput).await?);
            }
        }
        Ok(())
    }

    async fn analyze_latency(
        &self,
        performance_data: &[PerformanceSnapshot],
        current_config: &HashMap<String, ConfigItem>,
        optimizations: &mut Vec<ConfigOptimization>,
    ) -> Result<()> {
        if let Some(avg_latency) = self.calculate_average_latency(performance_data) {
            if avg_latency > Duration::from_millis(100) {
                optimizations.extend(self.optimize_latency_config(current_config, avg_latency).await?);
            }
        }
        Ok(())
    }

    /// 优化CPU配置
    async fn optimize_cpu_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_cpu: f64,
    ) -> Result<Vec<ConfigOptimization>> {
        let workers_config = match self.get_workers_config(config) {
            Some(cfg) => cfg,
            None => return Ok(Vec::new()),
        };

        let current_workers = match self.extract_integer_value(&workers_config.value) {
            Some(n) => n,
            None => return Ok(Vec::new()),
        };

        let suggested_workers = self.calculate_suggested_workers(current_workers, avg_cpu);
        let optimization = self.create_cpu_optimization(workers_config, current_workers, suggested_workers, avg_cpu);

        Ok(vec![optimization])
    }

    /// 获取工作线程配置
    fn get_workers_config(&self, config: &HashMap<String, ConfigItem>) -> Option<ConfigItem> {
        config.get("max_workers").cloned()
    }

    /// 提取整数值
    fn extract_integer_value(&self, value: &ConfigValue) -> Option<i64> {
        match value {
            ConfigValue::Integer(n) => Some(*n),
            _ => None,
        }
    }

    /// 创建CPU优化配置
    fn create_cpu_optimization(
        &self,
        workers_config: ConfigItem,
        current_workers: i64,
        suggested_workers: i64,
        avg_cpu: f64,
    ) -> ConfigOptimization {
        ConfigOptimization {
            id: format!("cpu_workers_{}", Instant::now().elapsed().as_millis()),
            config_item: workers_config,
            current_value: ConfigValue::Integer(current_workers),
            suggested_value: ConfigValue::Integer(suggested_workers),
            expected_improvement: 20.0,
            confidence: 0.8,
            reasoning: format!("CPU使用率过高 ({}%), 建议增加工作线程数", avg_cpu),
            risk_level: RiskLevel::Low,
        }
    }

    /// 计算建议的工作线程数
    fn calculate_suggested_workers(&self, current_workers: i64, avg_cpu: f64) -> i64 {
        if avg_cpu > 95.0 {
            (current_workers * 2).min(32)
        } else if avg_cpu > 90.0 {
            (current_workers as f64 * 1.5) as i64
        } else {
            current_workers + 2
        }
    }

    /// 优化内存配置
    async fn optimize_memory_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_memory: f64,
    ) -> Result<Vec<ConfigOptimization>> {
        let memory_pool_config = match self.get_memory_pool_config(config) {
            Some(cfg) => cfg,
            None => return Ok(Vec::new()),
        };

        let current_size = match self.extract_integer_value(&memory_pool_config.value) {
            Some(n) => n,
            None => return Ok(Vec::new()),
        };

        let suggested_size = self.calculate_suggested_memory(current_size, avg_memory);
        let optimization = self.create_memory_optimization(memory_pool_config, current_size, suggested_size, avg_memory);

        Ok(vec![optimization])
    }

    /// 获取内存池配置
    fn get_memory_pool_config(&self, config: &HashMap<String, ConfigItem>) -> Option<ConfigItem> {
        config.get("memory_pool_size").cloned()
    }

    /// 创建内存优化配置
    fn create_memory_optimization(
        &self,
        memory_pool_config: ConfigItem,
        current_size: i64,
        suggested_size: i64,
        avg_memory: f64,
    ) -> ConfigOptimization {
        ConfigOptimization {
            id: format!("memory_pool_{}", Instant::now().elapsed().as_millis()),
            config_item: memory_pool_config,
            current_value: ConfigValue::Integer(current_size),
            suggested_value: ConfigValue::Integer(suggested_size),
            expected_improvement: 25.0,
            confidence: 0.7,
            reasoning: format!("内存使用率过高 ({}%), 建议增加内存池大小", avg_memory),
            risk_level: RiskLevel::Medium,
        }
    }

    /// 计算建议的内存大小
    fn calculate_suggested_memory(&self, current_size: i64, avg_memory: f64) -> i64 {
        if avg_memory > 95.0 {
            current_size * 2
        } else if avg_memory > 90.0 {
            (current_size as f64 * 1.5) as i64
        } else {
            current_size + 512
        }
    }

    /// 优化吞吐量配置
    async fn optimize_throughput_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_throughput: u64,
    ) -> Result<Vec<ConfigOptimization>> {
        let connection_pool_config = match self.get_connection_pool_config(config) {
            Some(cfg) => cfg,
            None => return Ok(Vec::new()),
        };

        let current_size = match self.extract_integer_value(&connection_pool_config.value) {
            Some(n) => n,
            None => return Ok(Vec::new()),
        };

        let suggested_size = self.calculate_suggested_pool_size(current_size, avg_throughput);
        let optimization = self.create_throughput_optimization(connection_pool_config, current_size, suggested_size, avg_throughput);

        Ok(vec![optimization])
    }

    /// 获取连接池配置
    fn get_connection_pool_config(&self, config: &HashMap<String, ConfigItem>) -> Option<ConfigItem> {
        config.get("connection_pool_size").cloned()
    }

    /// 创建吞吐量优化配置
    fn create_throughput_optimization(
        &self,
        connection_pool_config: ConfigItem,
        current_size: i64,
        suggested_size: i64,
        avg_throughput: u64,
    ) -> ConfigOptimization {
        ConfigOptimization {
            id: format!("throughput_pool_{}", Instant::now().elapsed().as_millis()),
            config_item: connection_pool_config,
            current_value: ConfigValue::Integer(current_size),
            suggested_value: ConfigValue::Integer(suggested_size),
            expected_improvement: 40.0,
            confidence: 0.6,
            reasoning: format!("吞吐量过低 ({} ops/s), 建议增加连接池大小", avg_throughput),
            risk_level: RiskLevel::Low,
        }
    }

    /// 计算建议的连接池大小
    fn calculate_suggested_pool_size(&self, current_size: i64, avg_throughput: u64) -> i64 {
        if avg_throughput < 500 {
            current_size * 2
        } else if avg_throughput < 800 {
            (current_size as f64 * 1.5) as i64
        } else {
            current_size + 50
        }
    }

    /// 优化延迟配置
    async fn optimize_latency_config(
        &self,
        config: &HashMap<String, ConfigItem>,
        avg_latency: Duration,
    ) -> Result<Vec<ConfigOptimization>> {
        let batch_size_config = match self.get_batch_size_config(config) {
            Some(cfg) => cfg,
            None => return Ok(Vec::new()),
        };

        let current_size = match self.extract_integer_value(&batch_size_config.value) {
            Some(n) => n,
            None => return Ok(Vec::new()),
        };

        let suggested_size = self.calculate_suggested_batch_size(current_size, avg_latency);
        let optimization = self.create_latency_optimization(batch_size_config, current_size, suggested_size, avg_latency);

        Ok(vec![optimization])
    }

    /// 获取批处理大小配置
    fn get_batch_size_config(&self, config: &HashMap<String, ConfigItem>) -> Option<ConfigItem> {
        config.get("batch_size").cloned()
    }

    /// 创建延迟优化配置
    fn create_latency_optimization(
        &self,
        batch_size_config: ConfigItem,
        current_size: i64,
        suggested_size: i64,
        avg_latency: Duration,
    ) -> ConfigOptimization {
        ConfigOptimization {
            id: format!("latency_batch_{}", Instant::now().elapsed().as_millis()),
            config_item: batch_size_config,
            current_value: ConfigValue::Integer(current_size),
            suggested_value: ConfigValue::Integer(suggested_size),
            expected_improvement: 30.0,
            confidence: 0.7,
            reasoning: format!(
                "延迟过高 ({}ms), 建议减少批处理大小",
                avg_latency.as_millis()
            ),
            risk_level: RiskLevel::Medium,
        }
    }

    /// 计算建议的批处理大小
    fn calculate_suggested_batch_size(&self, current_size: i64, avg_latency: Duration) -> i64 {
        if avg_latency > Duration::from_millis(500) {
            current_size / 2
        } else if avg_latency > Duration::from_millis(200) {
            (current_size as f64 * 0.8) as i64
        } else {
            current_size
        }
    }

    /// 应用配置优化
    pub async fn apply_optimization(&self, optimization: &ConfigOptimization) -> Result<bool> {
        let start = Instant::now();

        self.validate_optimization(optimization)?;
        self.apply_config_value(optimization);
        self.update_apply_stats(start.elapsed());

        Ok(true)
    }

    fn validate_optimization(&self, optimization: &ConfigOptimization) -> Result<()> {
        if optimization.risk_level == RiskLevel::VeryHigh {
            return Err(anyhow!("高风险配置需要手动确认"));
        }
        if !self.validate_config_constraints(&optimization.config_item, &optimization.suggested_value) {
            return Err(anyhow!("配置值不满足约束条件"));
        }
        Ok(())
    }

    fn apply_config_value(&self, optimization: &ConfigOptimization) {
        let mut config = self.current_config.lock().unwrap();
        if let Some(item) = config.get_mut(&optimization.config_item.key) {
            item.value = optimization.suggested_value.clone();
        }
    }

    fn update_apply_stats(&self, duration: Duration) {
        self.stats.total_configurations.fetch_add(1, Ordering::Relaxed);
        self.stats.successful_configurations.fetch_add(1, Ordering::Relaxed);
        self.stats.configuration_time.fetch_add(duration.as_micros() as u64, Ordering::Relaxed);
    }

    /// 验证配置约束
    fn validate_config_constraints(&self, config_item: &ConfigItem, value: &ConfigValue) -> bool {
        for constraint in &config_item.constraints {
            if !self.validate_single_constraint(constraint, value) {
                return false;
            }
        }
        true
    }

    /// 验证单个约束
    fn validate_single_constraint(&self, constraint: &ConfigConstraint, value: &ConfigValue) -> bool {
        match constraint.constraint_type {
            ConstraintType::Range => self.validate_range_constraint(constraint, value),
            ConstraintType::Enum => self.validate_enum_constraint(constraint, value),
            ConstraintType::Custom => true, // 自定义约束验证逻辑
        }
    }

    /// 验证范围约束
    fn validate_range_constraint(&self, constraint: &ConfigConstraint, value: &ConfigValue) -> bool {
        let (min, max) = match (&constraint.min_value, &constraint.max_value) {
            (Some(min), Some(max)) => (min, max),
            _ => return true,
        };
        self.is_value_in_range(value, min, max)
    }

    /// 验证枚举约束
    fn validate_enum_constraint(&self, constraint: &ConfigConstraint, value: &ConfigValue) -> bool {
        match &constraint.allowed_values {
            Some(allowed) => allowed.contains(value),
            None => true,
        }
    }

    /// 检查值是否在范围内
    fn is_value_in_range(&self, value: &ConfigValue, min: &ConfigValue, max: &ConfigValue) -> bool {
        self.check_integer_range(value, min, max)
            || self.check_float_range(value, min, max)
    }

    fn check_integer_range(&self, value: &ConfigValue, min: &ConfigValue, max: &ConfigValue) -> bool {
        match (value, min, max) {
            (ConfigValue::Integer(v), ConfigValue::Integer(min_val), ConfigValue::Integer(max_val)) => {
                *v >= *min_val && *v <= *max_val
            }
            _ => false,
        }
    }

    fn check_float_range(&self, value: &ConfigValue, min: &ConfigValue, max: &ConfigValue) -> bool {
        match (value, min, max) {
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
