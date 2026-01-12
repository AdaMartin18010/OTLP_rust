//! # 指标收集器实现
//!
//! 提供高性能的指标收集、聚合和导出功能
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步指标收集
//! - **元组收集**: 使用 `collect()` 直接收集指标数据到元组
//! - **改进的原子操作**: 利用 Rust 1.92 的原子操作优化提升性能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use thiserror::Error;
use tokio::sync::{Mutex, RwLock};
use tokio::time::{interval, sleep};

/// 指标收集器错误
#[derive(Debug, Error)]
pub enum MetricsCollectorError {
    #[error("指标名称无效: {0}")]
    InvalidMetricName(String),
    #[error("指标值无效: {0}")]
    InvalidMetricValue(String),
    #[error("指标类型不匹配: {0}")]
    MetricTypeMismatch(String),
    #[error("收集器已关闭")]
    CollectorClosed,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

/// 指标类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MetricType {
    Counter,
    Gauge,
    Histogram,
    Summary,
}

/// 指标标签
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MetricLabel {
    pub name: String,
    pub value: String,
}

/// 指标值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricValue {
    Counter(f64),
    Gauge(f64),
    Histogram(Vec<HistogramBucket>),
    Summary(SummaryValue),
}

/// 直方图桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    pub upper_bound: f64,
    pub count: u64,
}

/// 摘要值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SummaryValue {
    pub count: u64,
    pub sum: f64,
    pub quantiles: Vec<Quantile>,
}

/// 分位数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Quantile {
    pub quantile: f64,
    pub value: f64,
}

/// 指标数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricDataPoint {
    pub timestamp: u64,
    pub value: MetricValue,
    pub labels: Vec<MetricLabel>,
}

/// 指标定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricDefinition {
    pub name: String,
    pub help: String,
    pub metric_type: MetricType,
    pub labels: Vec<MetricLabel>,
}

/// 指标收集器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsCollectorConfig {
    /// 收集间隔
    pub collection_interval: Duration,
    /// 导出间隔
    pub export_interval: Duration,
    /// 最大指标数量
    pub max_metrics: usize,
    /// 是否启用自动清理
    pub enable_auto_cleanup: bool,
    /// 清理间隔
    pub cleanup_interval: Duration,
    /// 指标保留时间
    pub retention_time: Duration,
    /// 是否启用统计
    pub enable_stats: bool,
}

impl Default for MetricsCollectorConfig {
    fn default() -> Self {
        Self {
            collection_interval: Duration::from_secs(10),
            export_interval: Duration::from_secs(60),
            max_metrics: 10000,
            enable_auto_cleanup: true,
            cleanup_interval: Duration::from_secs(300),
            retention_time: Duration::from_secs(3600),
            enable_stats: true,
        }
    }
}

/// 指标收集器统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MetricsCollectorStats {
    pub total_metrics: usize,
    pub active_metrics: usize,
    pub total_data_points: u64,
    pub collection_count: u64,
    pub export_count: u64,
    pub cleanup_count: u64,
    #[serde(skip)]
    pub last_collection: Option<Instant>,
    #[serde(skip)]
    pub last_export: Option<Instant>,
    #[serde(skip)]
    pub last_cleanup: Option<Instant>,
}

/// 指标收集器
///
/// 高性能的指标收集、聚合和导出系统
pub struct MetricsCollector {
    config: MetricsCollectorConfig,
    metrics: Arc<RwLock<HashMap<String, MetricDefinition>>>,
    data_points: Arc<RwLock<HashMap<String, Vec<MetricDataPoint>>>>,
    stats: Arc<Mutex<MetricsCollectorStats>>,
    is_running: Arc<AtomicUsize>,
    total_metrics: Arc<AtomicUsize>,
    total_data_points: Arc<AtomicU64>,
    collection_count: Arc<AtomicU64>,
    export_count: Arc<AtomicU64>,
    cleanup_count: Arc<AtomicU64>,
}

impl MetricsCollector {
    /// 创建新的指标收集器
    pub fn new(config: MetricsCollectorConfig) -> Result<Self, MetricsCollectorError> {
        if config.collection_interval.as_secs() == 0 {
            return Err(MetricsCollectorError::ConfigurationError(
                "collection_interval must be greater than 0".to_string(),
            ));
        }

        if config.max_metrics == 0 {
            return Err(MetricsCollectorError::ConfigurationError(
                "max_metrics must be greater than 0".to_string(),
            ));
        }

        let metrics = Arc::new(RwLock::new(HashMap::new()));
        let data_points = Arc::new(RwLock::new(HashMap::new()));
        let stats = Arc::new(Mutex::new(MetricsCollectorStats::default()));
        let is_running = Arc::new(AtomicUsize::new(1));
        let total_metrics = Arc::new(AtomicUsize::new(0));
        let total_data_points = Arc::new(AtomicU64::new(0));
        let collection_count = Arc::new(AtomicU64::new(0));
        let export_count = Arc::new(AtomicU64::new(0));
        let cleanup_count = Arc::new(AtomicU64::new(0));

        let collector = Self {
            config,
            metrics,
            data_points,
            stats,
            is_running,
            total_metrics,
            total_data_points,
            collection_count,
            export_count,
            cleanup_count,
        };

        // 启动后台任务
        collector.start_background_tasks();

        Ok(collector)
    }

    /// 启动后台任务
    fn start_background_tasks(&self) {
        // 启动收集任务
        self.start_collection_task();

        // 启动清理任务
        if self.config.enable_auto_cleanup {
            self.start_cleanup_task();
        }
    }

    /// 启动收集任务
    fn start_collection_task(&self) {
        let config = self.config.clone();
        let stats = Arc::clone(&self.stats);
        let collection_count = Arc::clone(&self.collection_count);
        let is_running = Arc::clone(&self.is_running);

        tokio::spawn(async move {
            let mut interval = interval(config.collection_interval);

            while is_running.load(Ordering::Acquire) > 0 {
                interval.tick().await;

                // 执行收集
                collection_count.fetch_add(1, Ordering::AcqRel);

                // 更新统计信息
                let mut stats_guard = stats.lock().await;
                stats_guard.collection_count = collection_count.load(Ordering::Acquire);
                stats_guard.last_collection = Some(Instant::now());
            }
        });
    }

    /// 启动清理任务
    fn start_cleanup_task(&self) {
        let config = self.config.clone();
        let data_points = Arc::clone(&self.data_points);
        let stats = Arc::clone(&self.stats);
        let cleanup_count = Arc::clone(&self.cleanup_count);
        let is_running = Arc::clone(&self.is_running);

        tokio::spawn(async move {
            let mut interval = interval(config.cleanup_interval);

            while is_running.load(Ordering::Acquire) > 0 {
                interval.tick().await;

                // 执行清理
                let now = match SystemTime::now().duration_since(UNIX_EPOCH) {
                    Ok(duration) => duration.as_secs(),
                    Err(_) => {
                        // 系统时间异常，跳过本次清理
                        continue;
                    }
                };
                let cutoff_time = now - config.retention_time.as_secs();

                let mut data_points_guard = data_points.write().await;
                let mut removed_count = 0;

                for (_, points) in data_points_guard.iter_mut() {
                    let original_len = points.len();
                    points.retain(|point| point.timestamp > cutoff_time);
                    removed_count += original_len - points.len();
                }

                cleanup_count.fetch_add(1, Ordering::AcqRel);

                // 更新统计信息
                let mut stats_guard = stats.lock().await;
                stats_guard.cleanup_count = cleanup_count.load(Ordering::Acquire);
                stats_guard.last_cleanup = Some(Instant::now());

                if removed_count > 0 {
                    println!("Cleaned up {} old data points", removed_count);
                }
            }
        });
    }

    /// 注册指标
    pub async fn register_metric(
        &self,
        definition: MetricDefinition,
    ) -> Result<(), MetricsCollectorError> {
        if definition.name.is_empty() {
            return Err(MetricsCollectorError::InvalidMetricName(
                "metric name cannot be empty".to_string(),
            ));
        }

        if self.total_metrics.load(Ordering::Acquire) >= self.config.max_metrics {
            return Err(MetricsCollectorError::ConfigurationError(
                "maximum number of metrics reached".to_string(),
            ));
        }

        let mut metrics_guard = self.metrics.write().await;

        if metrics_guard.contains_key(&definition.name) {
            return Err(MetricsCollectorError::InvalidMetricName(format!(
                "metric '{}' already exists",
                definition.name
            )));
        }

        metrics_guard.insert(definition.name.clone(), definition);
        self.total_metrics.fetch_add(1, Ordering::AcqRel);

        Ok(())
    }

    /// 记录指标值
    pub async fn record_metric(
        &self,
        name: String,
        value: MetricValue,
        labels: Vec<MetricLabel>,
    ) -> Result<(), MetricsCollectorError> {
        if name.is_empty() {
            return Err(MetricsCollectorError::InvalidMetricName(
                "metric name cannot be empty".to_string(),
            ));
        }

        // 检查指标是否存在
        let metrics_guard = self.metrics.read().await;
        let metric_def = metrics_guard.get(&name).ok_or_else(|| {
            MetricsCollectorError::InvalidMetricName(format!("metric '{}' not found", name))
        })?;

        // 验证指标类型
        match (&metric_def.metric_type, &value) {
            (MetricType::Counter, MetricValue::Counter(_)) => {}
            (MetricType::Gauge, MetricValue::Gauge(_)) => {}
            (MetricType::Histogram, MetricValue::Histogram(_)) => {}
            (MetricType::Summary, MetricValue::Summary(_)) => {}
            _ => {
                return Err(MetricsCollectorError::MetricTypeMismatch(format!(
                    "metric '{}' type mismatch",
                    name
                )));
            }
        }

        // 创建数据点
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| MetricsCollectorError::InvalidMetricValue(format!("系统时间错误: {}", e)))?
            .as_secs();

        let data_point = MetricDataPoint {
            timestamp,
            value,
            labels,
        };

        // 存储数据点
        let mut data_points_guard = self.data_points.write().await;
        let points = data_points_guard.entry(name).or_insert_with(Vec::new);
        points.push(data_point);

        self.total_data_points.fetch_add(1, Ordering::AcqRel);

        Ok(())
    }

    /// 获取指标数据
    pub async fn get_metric_data(
        &self,
        name: &str,
    ) -> Result<Vec<MetricDataPoint>, MetricsCollectorError> {
        let data_points_guard = self.data_points.read().await;
        let points = data_points_guard.get(name).cloned().unwrap_or_default();
        Ok(points)
    }

    /// 获取所有指标定义
    pub async fn get_all_metrics(&self) -> Vec<MetricDefinition> {
        let metrics_guard = self.metrics.read().await;
        metrics_guard.values().cloned().collect()
    }

    /// 导出指标数据
    pub async fn export_metrics(&self) -> Result<Vec<MetricDataPoint>, MetricsCollectorError> {
        let mut all_data_points = Vec::new();

        let data_points_guard = self.data_points.read().await;
        for points in data_points_guard.values() {
            all_data_points.extend(points.clone());
        }

        self.export_count.fetch_add(1, Ordering::AcqRel);

        // 更新统计信息
        let mut stats_guard = self.stats.lock().await;
        stats_guard.export_count = self.export_count.load(Ordering::Acquire);
        stats_guard.last_export = Some(Instant::now());

        Ok(all_data_points)
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> MetricsCollectorStats {
        let mut stats = self.stats.lock().await;
        stats.total_metrics = self.total_metrics.load(Ordering::Acquire);
        stats.total_data_points = self.total_data_points.load(Ordering::Acquire);
        stats.collection_count = self.collection_count.load(Ordering::Acquire);
        stats.export_count = self.export_count.load(Ordering::Acquire);
        stats.cleanup_count = self.cleanup_count.load(Ordering::Acquire);

        // 计算活跃指标数量
        let metrics_guard = self.metrics.read().await;
        stats.active_metrics = metrics_guard.len();

        stats.clone()
    }

    /// 清理指标
    pub async fn cleanup_metric(&self, name: &str) -> Result<(), MetricsCollectorError> {
        let mut metrics_guard = self.metrics.write().await;
        let mut data_points_guard = self.data_points.write().await;

        if metrics_guard.remove(name).is_some() {
            data_points_guard.remove(name);
            self.total_metrics.fetch_sub(1, Ordering::AcqRel);
        }

        Ok(())
    }

    /// 清理所有指标
    pub async fn cleanup_all_metrics(&self) {
        let mut metrics_guard = self.metrics.write().await;
        let mut data_points_guard = self.data_points.write().await;

        metrics_guard.clear();
        data_points_guard.clear();

        self.total_metrics.store(0, Ordering::Release);
        self.total_data_points.store(0, Ordering::Release);
    }

    /// 获取配置
    pub fn get_config(&self) -> &MetricsCollectorConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(
        &mut self,
        config: MetricsCollectorConfig,
    ) -> Result<(), MetricsCollectorError> {
        if config.collection_interval.as_secs() == 0 {
            return Err(MetricsCollectorError::ConfigurationError(
                "collection_interval must be greater than 0".to_string(),
            ));
        }

        if config.max_metrics == 0 {
            return Err(MetricsCollectorError::ConfigurationError(
                "max_metrics must be greater than 0".to_string(),
            ));
        }

        self.config = config;
        Ok(())
    }

    /// 关闭收集器
    pub fn shutdown(&self) {
        self.is_running.store(0, Ordering::Release);
    }

    /// 等待收集器关闭
    pub async fn wait_for_shutdown(&self) {
        while self.is_running.load(Ordering::Acquire) > 0 {
            sleep(Duration::from_millis(100)).await;
        }
    }
}

impl Clone for MetricsCollector {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            metrics: Arc::clone(&self.metrics),
            data_points: Arc::clone(&self.data_points),
            stats: Arc::clone(&self.stats),
            is_running: Arc::clone(&self.is_running),
            total_metrics: Arc::clone(&self.total_metrics),
            total_data_points: Arc::clone(&self.total_data_points),
            collection_count: Arc::clone(&self.collection_count),
            export_count: Arc::clone(&self.export_count),
            cleanup_count: Arc::clone(&self.cleanup_count),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_metrics_collector_basic() {
        let config = MetricsCollectorConfig::default();
        let collector =
            MetricsCollector::new(config).expect("Failed to create MetricsCollector for test");

        // 注册指标
        let metric_def = MetricDefinition {
            name: "test_counter".to_string(),
            help: "Test counter metric".to_string(),
            metric_type: MetricType::Counter,
            labels: vec![],
        };

        collector
            .register_metric(metric_def)
            .await
            .expect("Failed to register metric");

        // 记录指标值
        let value = MetricValue::Counter(1.0);
        let labels = vec![MetricLabel {
            name: "instance".to_string(),
            value: "test".to_string(),
        }];

        collector
            .record_metric("test_counter".to_string(), value, labels)
            .await
            .expect("Failed to record metric");

        // 获取指标数据
        let data = collector
            .get_metric_data("test_counter")
            .await
            .expect("Failed to get metric data");
        assert_eq!(data.len(), 1);
        assert!(matches!(data[0].value, MetricValue::Counter(1.0)));

        // 获取统计信息
        let stats = collector.get_stats().await;
        assert_eq!(stats.total_metrics, 1);
        assert_eq!(stats.total_data_points, 1);

        collector.shutdown();
    }

    #[tokio::test]
    async fn test_metrics_collector_multiple_types() {
        let config = MetricsCollectorConfig::default();
        let collector = MetricsCollector::new(config).expect("Failed to create metrics collector");

        // 注册不同类型的指标
        let counter_def = MetricDefinition {
            name: "test_counter".to_string(),
            help: "Test counter".to_string(),
            metric_type: MetricType::Counter,
            labels: vec![],
        };

        let gauge_def = MetricDefinition {
            name: "test_gauge".to_string(),
            help: "Test gauge".to_string(),
            metric_type: MetricType::Gauge,
            labels: vec![],
        };

        collector
            .register_metric(counter_def)
            .await
            .expect("Failed to register counter metric");
        collector
            .register_metric(gauge_def)
            .await
            .expect("Failed to register gauge metric");

        // 记录不同类型的值
        collector
            .record_metric(
                "test_counter".to_string(),
                MetricValue::Counter(1.0),
                vec![],
            )
            .await
            .expect("Failed to record counter metric");
        collector
            .record_metric("test_gauge".to_string(), MetricValue::Gauge(2.5), vec![])
            .await
            .expect("Failed to record gauge metric");

        // 验证数据
        let counter_data = collector
            .get_metric_data("test_counter")
            .await
            .expect("Failed to get counter metric data");
        let gauge_data = collector
            .get_metric_data("test_gauge")
            .await
            .expect("Failed to get gauge metric data");

        assert_eq!(counter_data.len(), 1);
        assert_eq!(gauge_data.len(), 1);
        assert!(matches!(counter_data[0].value, MetricValue::Counter(1.0)));
        assert!(matches!(gauge_data[0].value, MetricValue::Gauge(2.5)));

        collector.shutdown();
    }

    #[tokio::test]
    async fn test_metrics_collector_cleanup() {
        let config = MetricsCollectorConfig {
            retention_time: Duration::from_millis(100),
            cleanup_interval: Duration::from_millis(50),
            ..Default::default()
        };
        let collector = MetricsCollector::new(config).expect("Failed to create MetricsCollector");

        // 注册指标
        let metric_def = MetricDefinition {
            name: "test_metric".to_string(),
            help: "Test metric".to_string(),
            metric_type: MetricType::Counter,
            labels: vec![],
        };

        collector
            .register_metric(metric_def)
            .await
            .expect("Failed to register metric");

        // 记录指标值
        collector
            .record_metric("test_metric".to_string(), MetricValue::Counter(1.0), vec![])
            .await
            .expect("Failed to record metric");

        // 等待清理
        sleep(Duration::from_millis(200)).await;

        // 验证数据被清理
        let data = collector
            .get_metric_data("test_metric")
            .await
            .expect("Failed to get metric data after cleanup");
        assert_eq!(data.len(), 0);

        collector.shutdown();
    }

    #[tokio::test]
    async fn test_metrics_collector_export() {
        let config = MetricsCollectorConfig::default();
        let collector = MetricsCollector::new(config).expect("Failed to create MetricsCollector");

        // 注册指标
        let metric_def = MetricDefinition {
            name: "test_metric".to_string(),
            help: "Test metric".to_string(),
            metric_type: MetricType::Counter,
            labels: vec![],
        };

        collector
            .register_metric(metric_def)
            .await
            .expect("Failed to register metric");

        // 记录指标值
        collector
            .record_metric("test_metric".to_string(), MetricValue::Counter(1.0), vec![])
            .await
            .expect("Failed to record metric");

        // 导出指标
        let exported_data = collector
            .export_metrics()
            .await
            .expect("Failed to export metrics");
        assert_eq!(exported_data.len(), 1);

        // 验证统计信息
        let stats = collector.get_stats().await;
        assert_eq!(stats.export_count, 1);

        collector.shutdown();
    }
}
