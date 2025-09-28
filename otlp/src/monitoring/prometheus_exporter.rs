//! Prometheus 指标导出器
//!
//! 将收集的指标数据导出为 Prometheus 格式

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use thiserror::Error;
use tokio::sync::Mutex;
use tokio::time::{interval, sleep};

use crate::monitoring::metrics_collector::{
    MetricDataPoint, MetricType, MetricValue, MetricsCollector,
};

/// Prometheus 导出器错误
#[derive(Debug, Error)]
pub enum PrometheusExporterError {
    #[error("导出器已关闭")]
    ExporterClosed,
    #[error("指标格式错误: {0}")]
    InvalidMetricFormat(String),
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("导出失败: {0}")]
    ExportFailed(String),
}

/// Prometheus 导出器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrometheusExporterConfig {
    /// 导出间隔
    pub export_interval: Duration,
    /// 导出端点
    pub export_endpoint: String,
    /// 是否启用 HTTP 服务器
    pub enable_http_server: bool,
    /// HTTP 服务器端口
    pub http_port: u16,
    /// HTTP 服务器路径
    pub http_path: String,
    /// 是否启用标签
    pub enable_labels: bool,
    /// 是否启用时间戳
    pub enable_timestamps: bool,
    /// 最大指标数量
    pub max_metrics: usize,
    /// 是否启用统计
    pub enable_stats: bool,
}

impl Default for PrometheusExporterConfig {
    fn default() -> Self {
        Self {
            export_interval: Duration::from_secs(60),
            export_endpoint: "http://localhost:9090/api/v1/write".to_string(),
            enable_http_server: true,
            http_port: 8080,
            http_path: "/metrics".to_string(),
            enable_labels: true,
            enable_timestamps: true,
            max_metrics: 10000,
            enable_stats: true,
        }
    }
}

/// Prometheus 导出器统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PrometheusExporterStats {
    pub total_exports: u64,
    pub successful_exports: u64,
    pub failed_exports: u64,
    pub total_metrics_exported: u64,
    #[serde(skip)]
    pub last_export: Option<Instant>,
    #[serde(skip)]
    pub last_successful_export: Option<Instant>,
    #[serde(skip)]
    pub last_failed_export: Option<Instant>,
    pub average_export_time: Duration,
    pub export_success_rate: f64,
}

/// Prometheus 指标格式
#[derive(Debug, Clone)]
pub struct PrometheusMetric {
    pub name: String,
    pub help: String,
    pub metric_type: String,
    pub samples: Vec<PrometheusSample>,
}

/// Prometheus 样本
#[derive(Debug, Clone)]
pub struct PrometheusSample {
    pub name: String,
    pub labels: HashMap<String, String>,
    pub value: f64,
    pub timestamp: Option<u64>,
}

/// Prometheus 导出器
///
/// 高性能的 Prometheus 指标导出器
pub struct PrometheusExporter {
    config: PrometheusExporterConfig,
    metrics_collector: Arc<MetricsCollector>,
    stats: Arc<Mutex<PrometheusExporterStats>>,
    is_running: Arc<std::sync::atomic::AtomicUsize>,
    total_exports: Arc<std::sync::atomic::AtomicU64>,
    successful_exports: Arc<std::sync::atomic::AtomicU64>,
    failed_exports: Arc<std::sync::atomic::AtomicU64>,
    total_metrics_exported: Arc<std::sync::atomic::AtomicU64>,
}

impl PrometheusExporter {
    /// 创建新的 Prometheus 导出器
    pub fn new(
        config: PrometheusExporterConfig,
        metrics_collector: Arc<MetricsCollector>,
    ) -> Result<Self, PrometheusExporterError> {
        if config.export_interval.as_secs() == 0 {
            return Err(PrometheusExporterError::ConfigurationError(
                "export_interval must be greater than 0".to_string(),
            ));
        }

        if config.max_metrics == 0 {
            return Err(PrometheusExporterError::ConfigurationError(
                "max_metrics must be greater than 0".to_string(),
            ));
        }

        let stats = Arc::new(Mutex::new(PrometheusExporterStats::default()));
        let is_running = Arc::new(std::sync::atomic::AtomicUsize::new(1));
        let total_exports = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let successful_exports = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let failed_exports = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let total_metrics_exported = Arc::new(std::sync::atomic::AtomicU64::new(0));

        let exporter = Self {
            config,
            metrics_collector,
            stats,
            is_running,
            total_exports,
            successful_exports,
            failed_exports,
            total_metrics_exported,
        };

        // 启动导出任务
        exporter.start_export_task();

        Ok(exporter)
    }

    /// 启动导出任务
    fn start_export_task(&self) {
        let config = self.config.clone();
        let metrics_collector = Arc::clone(&self.metrics_collector);
        let stats = Arc::clone(&self.stats);
        let is_running = Arc::clone(&self.is_running);
        let total_exports = Arc::clone(&self.total_exports);
        let successful_exports = Arc::clone(&self.successful_exports);
        let failed_exports = Arc::clone(&self.failed_exports);
        let total_metrics_exported = Arc::clone(&self.total_metrics_exported);

        tokio::spawn(async move {
            let mut interval = interval(config.export_interval);

            while is_running.load(std::sync::atomic::Ordering::Acquire) > 0 {
                interval.tick().await;

                // 执行导出
                let start_time = Instant::now();
                total_exports.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

                match Self::export_metrics_internal(&metrics_collector, &config).await {
                    Ok(exported_count) => {
                        successful_exports.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                        total_metrics_exported
                            .fetch_add(exported_count, std::sync::atomic::Ordering::AcqRel);

                        // 更新统计信息
                        let mut stats_guard = stats.lock().await;
                        stats_guard.total_exports =
                            total_exports.load(std::sync::atomic::Ordering::Acquire);
                        stats_guard.successful_exports =
                            successful_exports.load(std::sync::atomic::Ordering::Acquire);
                        stats_guard.total_metrics_exported =
                            total_metrics_exported.load(std::sync::atomic::Ordering::Acquire);
                        stats_guard.last_export = Some(Instant::now());
                        stats_guard.last_successful_export = Some(Instant::now());
                        stats_guard.average_export_time = start_time.elapsed();
                        stats_guard.export_success_rate = stats_guard.successful_exports as f64
                            / stats_guard.total_exports as f64;
                    }
                    Err(e) => {
                        failed_exports.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

                        // 更新统计信息
                        let mut stats_guard = stats.lock().await;
                        stats_guard.total_exports =
                            total_exports.load(std::sync::atomic::Ordering::Acquire);
                        stats_guard.failed_exports =
                            failed_exports.load(std::sync::atomic::Ordering::Acquire);
                        stats_guard.last_export = Some(Instant::now());
                        stats_guard.last_failed_export = Some(Instant::now());
                        stats_guard.export_success_rate = stats_guard.successful_exports as f64
                            / stats_guard.total_exports as f64;

                        eprintln!("Export failed: {}", e);
                    }
                }
            }
        });
    }

    /// 内部导出方法
    async fn export_metrics_internal(
        metrics_collector: &MetricsCollector,
        config: &PrometheusExporterConfig,
    ) -> Result<u64, PrometheusExporterError> {
        // 获取所有指标数据
        let all_metrics = metrics_collector.get_all_metrics().await;
        let mut total_exported = 0;

        for metric_def in all_metrics {
            // 获取指标数据点
            let data_points = metrics_collector
                .get_metric_data(&metric_def.name)
                .await
                .map_err(|e| PrometheusExporterError::ExportFailed(e.to_string()))?;

            if data_points.is_empty() {
                continue;
            }

            // 转换为 Prometheus 格式
            let prometheus_metric =
                Self::convert_to_prometheus_format(&metric_def, &data_points, config)?;

            // 导出指标
            Self::export_single_metric(&prometheus_metric, config).await?;

            total_exported += data_points.len() as u64;
        }

        Ok(total_exported)
    }

    /// 转换为 Prometheus 格式
    fn convert_to_prometheus_format(
        metric_def: &crate::monitoring::metrics_collector::MetricDefinition,
        data_points: &[MetricDataPoint],
        config: &PrometheusExporterConfig,
    ) -> Result<PrometheusMetric, PrometheusExporterError> {
        let mut samples = Vec::new();

        for data_point in data_points {
            let sample = Self::convert_data_point_to_sample(data_point, config)?;
            samples.push(sample);
        }

        let metric_type = match metric_def.metric_type {
            MetricType::Counter => "counter",
            MetricType::Gauge => "gauge",
            MetricType::Histogram => "histogram",
            MetricType::Summary => "summary",
        };

        Ok(PrometheusMetric {
            name: metric_def.name.clone(),
            help: metric_def.help.clone(),
            metric_type: metric_type.to_string(),
            samples,
        })
    }

    /// 转换数据点为样本
    fn convert_data_point_to_sample(
        data_point: &MetricDataPoint,
        config: &PrometheusExporterConfig,
    ) -> Result<PrometheusSample, PrometheusExporterError> {
        let mut labels = HashMap::new();

        if config.enable_labels {
            for label in &data_point.labels {
                labels.insert(label.name.clone(), label.value.clone());
            }
        }

        let value = match &data_point.value {
            MetricValue::Counter(v) => *v,
            MetricValue::Gauge(v) => *v,
            MetricValue::Histogram(buckets) => {
                // 计算直方图的总计数
                buckets.iter().map(|b| b.count).sum::<u64>() as f64
            }
            MetricValue::Summary(summary) => summary.sum,
        };

        let timestamp = if config.enable_timestamps {
            Some(data_point.timestamp)
        } else {
            None
        };

        Ok(PrometheusSample {
            name: "otlp_metric".to_string(), // 这里应该使用实际的指标名称
            labels,
            value,
            timestamp,
        })
    }

    /// 导出单个指标
    async fn export_single_metric(
        metric: &PrometheusMetric,
        _config: &PrometheusExporterConfig,
    ) -> Result<(), PrometheusExporterError> {
        // 这里应该实现实际的导出逻辑
        // 例如：发送到 Prometheus Pushgateway 或写入文件

        // 模拟导出过程
        let mut output = String::new();

        // 添加帮助信息
        if !metric.help.is_empty() {
            output.push_str(&format!("# HELP {} {}\n", metric.name, metric.help));
        }

        // 添加类型信息
        output.push_str(&format!("# TYPE {} {}\n", metric.name, metric.metric_type));

        // 添加样本数据
        for sample in &metric.samples {
            output.push_str(&format!("{}", sample.name));

            if !sample.labels.is_empty() {
                output.push_str("{");
                let mut label_pairs = Vec::new();
                for (key, value) in &sample.labels {
                    label_pairs.push(format!("{}=\"{}\"", key, value));
                }
                output.push_str(&label_pairs.join(","));
                output.push_str("}");
            }

            output.push_str(&format!(" {}", sample.value));

            if let Some(timestamp) = sample.timestamp {
                output.push_str(&format!(" {}", timestamp));
            }

            output.push_str("\n");
        }

        // 这里应该将 output 发送到实际的导出目标
        // 例如：HTTP POST 到 Prometheus Pushgateway
        println!("Exporting metric:\n{}", output);

        Ok(())
    }

    /// 手动导出指标
    pub async fn export_metrics(&self) -> Result<u64, PrometheusExporterError> {
        let start_time = Instant::now();
        let result = Self::export_metrics_internal(&self.metrics_collector, &self.config).await;

        match result {
            Ok(exported_count) => {
                self.total_exports
                    .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                self.successful_exports
                    .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                self.total_metrics_exported
                    .fetch_add(exported_count, std::sync::atomic::Ordering::AcqRel);

                // 更新统计信息
                let mut stats_guard = self.stats.lock().await;
                stats_guard.total_exports = self
                    .total_exports
                    .load(std::sync::atomic::Ordering::Acquire);
                stats_guard.successful_exports = self
                    .successful_exports
                    .load(std::sync::atomic::Ordering::Acquire);
                stats_guard.total_metrics_exported = self
                    .total_metrics_exported
                    .load(std::sync::atomic::Ordering::Acquire);
                stats_guard.last_export = Some(Instant::now());
                stats_guard.last_successful_export = Some(Instant::now());
                stats_guard.average_export_time = start_time.elapsed();
                stats_guard.export_success_rate =
                    stats_guard.successful_exports as f64 / stats_guard.total_exports as f64;

                Ok(exported_count)
            }
            Err(e) => {
                self.total_exports
                    .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                self.failed_exports
                    .fetch_add(1, std::sync::atomic::Ordering::AcqRel);

                // 更新统计信息
                let mut stats_guard = self.stats.lock().await;
                stats_guard.total_exports = self
                    .total_exports
                    .load(std::sync::atomic::Ordering::Acquire);
                stats_guard.failed_exports = self
                    .failed_exports
                    .load(std::sync::atomic::Ordering::Acquire);
                stats_guard.last_export = Some(Instant::now());
                stats_guard.last_failed_export = Some(Instant::now());
                stats_guard.export_success_rate =
                    stats_guard.successful_exports as f64 / stats_guard.total_exports as f64;

                Err(e)
            }
        }
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> PrometheusExporterStats {
        let mut stats = self.stats.lock().await;
        stats.total_exports = self
            .total_exports
            .load(std::sync::atomic::Ordering::Acquire);
        stats.successful_exports = self
            .successful_exports
            .load(std::sync::atomic::Ordering::Acquire);
        stats.failed_exports = self
            .failed_exports
            .load(std::sync::atomic::Ordering::Acquire);
        stats.total_metrics_exported = self
            .total_metrics_exported
            .load(std::sync::atomic::Ordering::Acquire);

        if stats.total_exports > 0 {
            stats.export_success_rate =
                stats.successful_exports as f64 / stats.total_exports as f64;
        }

        stats.clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &PrometheusExporterConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(
        &mut self,
        config: PrometheusExporterConfig,
    ) -> Result<(), PrometheusExporterError> {
        if config.export_interval.as_secs() == 0 {
            return Err(PrometheusExporterError::ConfigurationError(
                "export_interval must be greater than 0".to_string(),
            ));
        }

        if config.max_metrics == 0 {
            return Err(PrometheusExporterError::ConfigurationError(
                "max_metrics must be greater than 0".to_string(),
            ));
        }

        self.config = config;
        Ok(())
    }

    /// 关闭导出器
    pub fn shutdown(&self) {
        self.is_running
            .store(0, std::sync::atomic::Ordering::Release);
    }

    /// 等待导出器关闭
    pub async fn wait_for_shutdown(&self) {
        while self.is_running.load(std::sync::atomic::Ordering::Acquire) > 0 {
            sleep(Duration::from_millis(100)).await;
        }
    }
}

impl Clone for PrometheusExporter {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            metrics_collector: Arc::clone(&self.metrics_collector),
            stats: Arc::clone(&self.stats),
            is_running: Arc::clone(&self.is_running),
            total_exports: Arc::clone(&self.total_exports),
            successful_exports: Arc::clone(&self.successful_exports),
            failed_exports: Arc::clone(&self.failed_exports),
            total_metrics_exported: Arc::clone(&self.total_metrics_exported),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monitoring::metrics_collector::{
        MetricDefinition, MetricLabel, MetricType, MetricValue, MetricsCollector,
        MetricsCollectorConfig,
    };

    #[tokio::test]
    async fn test_prometheus_exporter_basic() {
        let collector_config = MetricsCollectorConfig::default();
        let collector = Arc::new(MetricsCollector::new(collector_config).unwrap());

        let exporter_config = PrometheusExporterConfig::default();
        let exporter = PrometheusExporter::new(exporter_config, collector.clone()).unwrap();

        // 注册指标
        let metric_def = MetricDefinition {
            name: "test_counter".to_string(),
            help: "Test counter metric".to_string(),
            metric_type: MetricType::Counter,
            labels: vec![],
        };

        collector.register_metric(metric_def).await.unwrap();

        // 记录指标值
        let value = MetricValue::Counter(1.0);
        let labels = vec![MetricLabel {
            name: "instance".to_string(),
            value: "test".to_string(),
        }];

        collector
            .record_metric("test_counter".to_string(), value, labels)
            .await
            .unwrap();

        // 手动导出
        let exported_count = exporter.export_metrics().await.unwrap();
        assert_eq!(exported_count, 1);

        // 获取统计信息
        let stats = exporter.get_stats().await;
        assert_eq!(stats.total_exports, 1);
        assert_eq!(stats.successful_exports, 1);
        assert_eq!(stats.total_metrics_exported, 1);

        exporter.shutdown();
    }

    #[tokio::test]
    async fn test_prometheus_exporter_multiple_metrics() {
        let collector_config = MetricsCollectorConfig::default();
        let collector = Arc::new(MetricsCollector::new(collector_config).unwrap());

        let exporter_config = PrometheusExporterConfig::default();
        let exporter = PrometheusExporter::new(exporter_config, collector.clone()).unwrap();

        // 注册多个指标
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

        collector.register_metric(counter_def).await.unwrap();
        collector.register_metric(gauge_def).await.unwrap();

        // 记录指标值
        collector
            .record_metric(
                "test_counter".to_string(),
                MetricValue::Counter(1.0),
                vec![],
            )
            .await
            .unwrap();
        collector
            .record_metric("test_gauge".to_string(), MetricValue::Gauge(2.5), vec![])
            .await
            .unwrap();

        // 导出指标
        let exported_count = exporter.export_metrics().await.unwrap();
        assert_eq!(exported_count, 2);

        // 获取统计信息
        let stats = exporter.get_stats().await;
        assert_eq!(stats.total_exports, 1);
        assert_eq!(stats.successful_exports, 1);
        assert_eq!(stats.total_metrics_exported, 2);

        exporter.shutdown();
    }

    #[tokio::test]
    async fn test_prometheus_exporter_config_update() {
        let collector_config = MetricsCollectorConfig::default();
        let collector = Arc::new(MetricsCollector::new(collector_config).unwrap());

        let mut exporter_config = PrometheusExporterConfig::default();
        exporter_config.export_interval = Duration::from_secs(30);
        exporter_config.enable_labels = false;

        let mut exporter = PrometheusExporter::new(exporter_config, collector.clone()).unwrap();

        // 更新配置
        let new_config = PrometheusExporterConfig {
            export_interval: Duration::from_secs(45),
            enable_labels: true,
            ..Default::default()
        };

        exporter.update_config(new_config).unwrap();

        // 验证配置已更新
        let config = exporter.get_config();
        assert_eq!(config.export_interval, Duration::from_secs(45));
        assert!(config.enable_labels);

        exporter.shutdown();
    }
}
