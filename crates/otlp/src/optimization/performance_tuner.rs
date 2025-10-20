//! 性能调优模块
//!
//! 提供自动化的性能调优和优化建议

use anyhow::{Result, anyhow};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 性能调优统计信息
#[derive(Debug, Default)]
pub struct PerformanceTunerStats {
    pub total_optimizations: AtomicUsize,
    pub successful_optimizations: AtomicUsize,
    pub failed_optimizations: AtomicUsize,
    pub performance_improvements: AtomicU64, // 百分比
    pub average_improvement: AtomicU64,      // 百分比
    pub peak_improvement: AtomicU64,         // 百分比
    pub optimization_time: AtomicU64,        // 微秒
}

impl Clone for PerformanceTunerStats {
    fn clone(&self) -> Self {
        Self {
            total_optimizations: AtomicUsize::new(self.total_optimizations.load(Ordering::Relaxed)),
            successful_optimizations: AtomicUsize::new(
                self.successful_optimizations.load(Ordering::Relaxed),
            ),
            failed_optimizations: AtomicUsize::new(
                self.failed_optimizations.load(Ordering::Relaxed),
            ),
            performance_improvements: AtomicU64::new(
                self.performance_improvements.load(Ordering::Relaxed),
            ),
            average_improvement: AtomicU64::new(self.average_improvement.load(Ordering::Relaxed)),
            peak_improvement: AtomicU64::new(self.peak_improvement.load(Ordering::Relaxed)),
            optimization_time: AtomicU64::new(self.optimization_time.load(Ordering::Relaxed)),
        }
    }
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub throughput: u64,
    pub latency: Duration,
    pub error_rate: f64,
    pub connection_count: usize,
    pub queue_depth: usize,
    pub cache_hit_rate: f64,
}

/// 优化建议
#[derive(Debug, Clone)]
pub struct OptimizationSuggestion {
    pub id: String,
    pub category: OptimizationCategory,
    pub priority: OptimizationPriority,
    pub description: String,
    pub expected_improvement: f64, // 百分比
    pub implementation_effort: ImplementationEffort,
    pub risk_level: RiskLevel,
    pub parameters: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OptimizationCategory {
    Memory,
    Cpu,
    Network,
    Concurrency,
    Caching,
    Algorithm,
    Configuration,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OptimizationPriority {
    Critical,
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImplementationEffort {
    Low,
    Medium,
    High,
    VeryHigh,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RiskLevel {
    Low,
    Medium,
    High,
    VeryHigh,
}

/// 性能调优器
pub struct PerformanceTuner {
    stats: Arc<PerformanceTunerStats>,
    current_metrics: Arc<Mutex<PerformanceMetrics>>,
    historical_metrics: Arc<Mutex<Vec<(Instant, PerformanceMetrics)>>>,
    optimization_history: Arc<Mutex<Vec<OptimizationSuggestion>>>,
    tuning_config: TuningConfig,
}

/// 调优配置
#[derive(Debug, Clone)]
pub struct TuningConfig {
    pub monitoring_interval: Duration,
    pub optimization_threshold: f64, // 性能提升阈值
    pub max_historical_entries: usize,
    pub auto_apply_low_risk: bool,
    pub performance_targets: PerformanceTargets,
}

#[derive(Debug, Clone)]
pub struct PerformanceTargets {
    pub max_cpu_usage: f64,
    pub max_memory_usage: f64,
    pub min_throughput: u64,
    pub max_latency: Duration,
    pub max_error_rate: f64,
    pub min_cache_hit_rate: f64,
}

impl Default for TuningConfig {
    fn default() -> Self {
        Self {
            monitoring_interval: Duration::from_secs(30),
            optimization_threshold: 5.0, // 5%性能提升阈值
            max_historical_entries: 1000,
            auto_apply_low_risk: false,
            performance_targets: PerformanceTargets {
                max_cpu_usage: 80.0,
                max_memory_usage: 85.0,
                min_throughput: 1000,
                max_latency: Duration::from_millis(100),
                max_error_rate: 1.0,
                min_cache_hit_rate: 90.0,
            },
        }
    }
}

impl PerformanceTuner {
    /// 创建新的性能调优器
    pub fn new(config: TuningConfig) -> Self {
        Self {
            stats: Arc::new(PerformanceTunerStats::default()),
            current_metrics: Arc::new(Mutex::new(PerformanceMetrics {
                cpu_usage: 0.0,
                memory_usage: 0.0,
                throughput: 0,
                latency: Duration::ZERO,
                error_rate: 0.0,
                connection_count: 0,
                queue_depth: 0,
                cache_hit_rate: 0.0,
            })),
            historical_metrics: Arc::new(Mutex::new(Vec::new())),
            optimization_history: Arc::new(Mutex::new(Vec::new())),
            tuning_config: config,
        }
    }

    /// 更新性能指标
    pub fn update_metrics(&self, metrics: PerformanceMetrics) -> Result<()> {
        let now = Instant::now();

        // 更新当前指标
        {
            let mut current = self.current_metrics.lock().unwrap();
            *current = metrics.clone();
        }

        // 添加到历史记录
        {
            let mut historical = self.historical_metrics.lock().unwrap();
            historical.push((now, metrics));

            // 保持历史记录在限制范围内
            if historical.len() > self.tuning_config.max_historical_entries {
                historical.remove(0);
            }
        }

        Ok(())
    }

    /// 分析性能并生成优化建议
    pub async fn analyze_and_suggest(&self) -> Result<Vec<OptimizationSuggestion>> {
        let current_metrics = self.current_metrics.lock().unwrap().clone();
        let historical_metrics = self.historical_metrics.lock().unwrap().clone();

        let mut suggestions = Vec::new();

        // 分析CPU使用率
        if current_metrics.cpu_usage > self.tuning_config.performance_targets.max_cpu_usage {
            suggestions.push(self.suggest_cpu_optimization(&current_metrics)?);
        }

        // 分析内存使用率
        if current_metrics.memory_usage > self.tuning_config.performance_targets.max_memory_usage {
            suggestions.push(self.suggest_memory_optimization(&current_metrics)?);
        }

        // 分析吞吐量
        if current_metrics.throughput < self.tuning_config.performance_targets.min_throughput {
            suggestions.push(self.suggest_throughput_optimization(&current_metrics)?);
        }

        // 分析延迟
        if current_metrics.latency > self.tuning_config.performance_targets.max_latency {
            suggestions.push(self.suggest_latency_optimization(&current_metrics)?);
        }

        // 分析错误率
        if current_metrics.error_rate > self.tuning_config.performance_targets.max_error_rate {
            suggestions.push(self.suggest_error_rate_optimization(&current_metrics)?);
        }

        // 分析缓存命中率
        if current_metrics.cache_hit_rate
            < self.tuning_config.performance_targets.min_cache_hit_rate
        {
            suggestions.push(self.suggest_cache_optimization(&current_metrics)?);
        }

        // 分析历史趋势
        if historical_metrics.len() > 10 {
            suggestions.extend(self.analyze_historical_trends(&historical_metrics)?);
        }

        // 记录建议
        {
            let mut history = self.optimization_history.lock().unwrap();
            history.extend(suggestions.clone());
        }

        Ok(suggestions)
    }

    /// 建议CPU优化
    fn suggest_cpu_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = if metrics.cpu_usage > 95.0 {
            30.0
        } else if metrics.cpu_usage > 90.0 {
            20.0
        } else {
            15.0
        };

        Ok(OptimizationSuggestion {
            id: format!("cpu_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Cpu,
            priority: if metrics.cpu_usage > 95.0 {
                OptimizationPriority::Critical
            } else {
                OptimizationPriority::High
            },
            description: format!(
                "CPU使用率过高 ({}%), 建议启用SIMD优化和并发处理",
                metrics.cpu_usage
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::Medium,
            risk_level: RiskLevel::Low,
            parameters: HashMap::from([
                ("enable_simd".to_string(), "true".to_string()),
                ("max_workers".to_string(), "auto".to_string()),
                ("cpu_affinity".to_string(), "true".to_string()),
            ]),
        })
    }

    /// 建议内存优化
    fn suggest_memory_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = if metrics.memory_usage > 95.0 {
            40.0
        } else if metrics.memory_usage > 90.0 {
            25.0
        } else {
            15.0
        };

        Ok(OptimizationSuggestion {
            id: format!("memory_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Memory,
            priority: if metrics.memory_usage > 95.0 {
                OptimizationPriority::Critical
            } else {
                OptimizationPriority::High
            },
            description: format!(
                "内存使用率过高 ({}%), 建议启用内存池和对象池",
                metrics.memory_usage
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::Medium,
            risk_level: RiskLevel::Low,
            parameters: HashMap::from([
                ("enable_memory_pool".to_string(), "true".to_string()),
                ("enable_object_pool".to_string(), "true".to_string()),
                ("gc_threshold".to_string(), "0.8".to_string()),
            ]),
        })
    }

    /// 建议吞吐量优化
    fn suggest_throughput_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = 50.0;

        Ok(OptimizationSuggestion {
            id: format!("throughput_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Concurrency,
            priority: OptimizationPriority::High,
            description: format!(
                "吞吐量过低 ({} ops/s), 建议启用批处理和并发优化",
                metrics.throughput
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::High,
            risk_level: RiskLevel::Medium,
            parameters: HashMap::from([
                ("enable_batching".to_string(), "true".to_string()),
                ("batch_size".to_string(), "100".to_string()),
                ("max_concurrent_requests".to_string(), "1000".to_string()),
            ]),
        })
    }

    /// 建议延迟优化
    fn suggest_latency_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = 60.0;

        Ok(OptimizationSuggestion {
            id: format!("latency_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Network,
            priority: OptimizationPriority::High,
            description: format!(
                "延迟过高 ({}ms), 建议启用零拷贝和连接池",
                metrics.latency.as_millis()
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::Medium,
            risk_level: RiskLevel::Low,
            parameters: HashMap::from([
                ("enable_zero_copy".to_string(), "true".to_string()),
                ("enable_connection_pool".to_string(), "true".to_string()),
                ("tcp_nodelay".to_string(), "true".to_string()),
            ]),
        })
    }

    /// 建议错误率优化
    fn suggest_error_rate_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = 80.0;

        Ok(OptimizationSuggestion {
            id: format!("error_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Configuration,
            priority: OptimizationPriority::Critical,
            description: format!(
                "错误率过高 ({}%), 建议启用熔断器和重试机制",
                metrics.error_rate
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::Low,
            risk_level: RiskLevel::Low,
            parameters: HashMap::from([
                ("enable_circuit_breaker".to_string(), "true".to_string()),
                ("enable_retry".to_string(), "true".to_string()),
                ("timeout_ms".to_string(), "5000".to_string()),
            ]),
        })
    }

    /// 建议缓存优化
    fn suggest_cache_optimization(
        &self,
        metrics: &PerformanceMetrics,
    ) -> Result<OptimizationSuggestion> {
        let improvement = 70.0;

        Ok(OptimizationSuggestion {
            id: format!("cache_opt_{}", Instant::now().elapsed().as_millis()),
            category: OptimizationCategory::Caching,
            priority: OptimizationPriority::Medium,
            description: format!(
                "缓存命中率过低 ({}%), 建议优化缓存策略",
                metrics.cache_hit_rate
            ),
            expected_improvement: improvement,
            implementation_effort: ImplementationEffort::Medium,
            risk_level: RiskLevel::Low,
            parameters: HashMap::from([
                ("cache_size".to_string(), "10000".to_string()),
                ("cache_ttl".to_string(), "3600".to_string()),
                ("eviction_policy".to_string(), "lru".to_string()),
            ]),
        })
    }

    /// 分析历史趋势
    fn analyze_historical_trends(
        &self,
        historical: &[(Instant, PerformanceMetrics)],
    ) -> Result<Vec<OptimizationSuggestion>> {
        let mut suggestions = Vec::new();

        // 分析CPU趋势
        if let Some(trend) = self.calculate_trend(historical, |m| m.cpu_usage) {
            if trend > 5.0 {
                // CPU使用率上升趋势
                suggestions.push(OptimizationSuggestion {
                    id: format!("cpu_trend_opt_{}", Instant::now().elapsed().as_millis()),
                    category: OptimizationCategory::Cpu,
                    priority: OptimizationPriority::Medium,
                    description: "CPU使用率呈上升趋势，建议提前优化".to_string(),
                    expected_improvement: 20.0,
                    implementation_effort: ImplementationEffort::Medium,
                    risk_level: RiskLevel::Low,
                    parameters: HashMap::new(),
                });
            }
        }

        // 分析内存趋势
        if let Some(trend) = self.calculate_trend(historical, |m| m.memory_usage) {
            if trend > 3.0 {
                // 内存使用率上升趋势
                suggestions.push(OptimizationSuggestion {
                    id: format!("memory_trend_opt_{}", Instant::now().elapsed().as_millis()),
                    category: OptimizationCategory::Memory,
                    priority: OptimizationPriority::Medium,
                    description: "内存使用率呈上升趋势，建议提前优化".to_string(),
                    expected_improvement: 25.0,
                    implementation_effort: ImplementationEffort::Medium,
                    risk_level: RiskLevel::Low,
                    parameters: HashMap::new(),
                });
            }
        }

        Ok(suggestions)
    }

    /// 计算趋势
    fn calculate_trend<F>(
        &self,
        historical: &[(Instant, PerformanceMetrics)],
        extractor: F,
    ) -> Option<f64>
    where
        F: Fn(&PerformanceMetrics) -> f64,
    {
        if historical.len() < 5 {
            return None;
        }

        let recent = &historical[historical.len() - 5..];
        let first = extractor(&recent[0].1);
        let last = extractor(&recent[recent.len() - 1].1);

        Some(last - first)
    }

    /// 应用优化建议
    pub async fn apply_optimization(&self, suggestion: &OptimizationSuggestion) -> Result<bool> {
        let start = Instant::now();

        // 检查风险级别
        if suggestion.risk_level == RiskLevel::VeryHigh && !self.tuning_config.auto_apply_low_risk {
            return Err(anyhow!("高风险优化需要手动确认"));
        }

        // 应用优化
        let success = match suggestion.category {
            OptimizationCategory::Cpu => self.apply_cpu_optimization(suggestion).await?,
            OptimizationCategory::Memory => self.apply_memory_optimization(suggestion).await?,
            OptimizationCategory::Network => self.apply_network_optimization(suggestion).await?,
            OptimizationCategory::Concurrency => {
                self.apply_concurrency_optimization(suggestion).await?
            }
            OptimizationCategory::Caching => self.apply_cache_optimization(suggestion).await?,
            OptimizationCategory::Algorithm => {
                self.apply_algorithm_optimization(suggestion).await?
            }
            OptimizationCategory::Configuration => {
                self.apply_configuration_optimization(suggestion).await?
            }
        };

        let duration = start.elapsed();

        // 更新统计
        self.stats
            .total_optimizations
            .fetch_add(1, Ordering::Relaxed);
        if success {
            self.stats
                .successful_optimizations
                .fetch_add(1, Ordering::Relaxed);
        } else {
            self.stats
                .failed_optimizations
                .fetch_add(1, Ordering::Relaxed);
        }
        self.stats
            .optimization_time
            .fetch_add(duration.as_micros() as u64, Ordering::Relaxed);

        Ok(success)
    }

    /// 应用CPU优化
    #[allow(unused_variables)]
    async fn apply_cpu_optimization(&self, suggestion: &OptimizationSuggestion) -> Result<bool> {
        // 模拟CPU优化应用
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok(true)
    }

    /// 应用内存优化
    #[allow(unused_variables)]
    async fn apply_memory_optimization(&self, suggestion: &OptimizationSuggestion) -> Result<bool> {
        // 模拟内存优化应用
        tokio::time::sleep(Duration::from_millis(150)).await;
        Ok(true)
    }

    /// 应用网络优化
    #[allow(unused_variables)]
    async fn apply_network_optimization(
        &self,
        suggestion: &OptimizationSuggestion,
    ) -> Result<bool> {
        // 模拟网络优化应用
        tokio::time::sleep(Duration::from_millis(200)).await;
        Ok(true)
    }

    /// 应用并发优化
    #[allow(unused_variables)]
    async fn apply_concurrency_optimization(
        &self,
        suggestion: &OptimizationSuggestion,
    ) -> Result<bool> {
        // 模拟并发优化应用
        tokio::time::sleep(Duration::from_millis(300)).await;
        Ok(true)
    }

    /// 应用缓存优化
    #[allow(unused_variables)]
    async fn apply_cache_optimization(&self, suggestion: &OptimizationSuggestion) -> Result<bool> {
        // 模拟缓存优化应用
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok(true)
    }

    /// 应用算法优化
    #[allow(unused_variables)]
    async fn apply_algorithm_optimization(
        &self,
        suggestion: &OptimizationSuggestion,
    ) -> Result<bool> {
        // 模拟算法优化应用
        tokio::time::sleep(Duration::from_millis(500)).await;
        Ok(true)
    }

    /// 应用配置优化
    #[allow(unused_variables)]
    async fn apply_configuration_optimization(
        &self,
        suggestion: &OptimizationSuggestion,
    ) -> Result<bool> {
        // 模拟配置优化应用
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(true)
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> PerformanceTunerStats {
        (*self.stats).clone()
    }

    /// 获取当前指标
    pub fn get_current_metrics(&self) -> PerformanceMetrics {
        self.current_metrics.lock().unwrap().clone()
    }

    /// 获取优化历史
    pub fn get_optimization_history(&self) -> Vec<OptimizationSuggestion> {
        self.optimization_history.lock().unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_tuner_creation() {
        let config = TuningConfig::default();
        let tuner = PerformanceTuner::new(config);
        let stats = tuner.get_stats();
        assert_eq!(stats.total_optimizations.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_metrics_update() {
        let config = TuningConfig::default();
        let tuner = PerformanceTuner::new(config);

        let metrics = PerformanceMetrics {
            cpu_usage: 50.0,
            memory_usage: 60.0,
            throughput: 1000,
            latency: Duration::from_millis(50),
            error_rate: 0.1,
            connection_count: 100,
            queue_depth: 10,
            cache_hit_rate: 95.0,
        };

        assert!(tuner.update_metrics(metrics).is_ok());
    }

    #[tokio::test]
    async fn test_optimization_analysis() {
        let config = TuningConfig::default();
        let tuner = PerformanceTuner::new(config);

        let metrics = PerformanceMetrics {
            cpu_usage: 95.0, // 高CPU使用率
            memory_usage: 60.0,
            throughput: 500,                     // 低吞吐量
            latency: Duration::from_millis(200), // 高延迟
            error_rate: 2.0,                     // 高错误率
            connection_count: 100,
            queue_depth: 10,
            cache_hit_rate: 80.0, // 低缓存命中率
        };

        tuner.update_metrics(metrics).unwrap();
        let suggestions = tuner.analyze_and_suggest().await.unwrap();

        assert!(!suggestions.is_empty());
        assert!(
            suggestions
                .iter()
                .any(|s| s.category == OptimizationCategory::Cpu)
        );
    }
}
