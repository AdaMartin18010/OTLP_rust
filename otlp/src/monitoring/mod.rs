//! 监控和可观测性模块
//!
//! 提供完整的监控、指标收集、日志聚合和分布式追踪功能
//! 包括错误监控系统、实时仪表板、告警管理和趋势分析

pub mod enhanced_alert_manager;
pub mod error_monitoring_types;
pub mod metrics_collector;
pub mod prometheus_exporter;

// 重新导出主要类型
pub use metrics_collector::{
    HistogramBucket, MetricDataPoint, MetricDefinition, MetricLabel, MetricType, MetricValue,
    MetricsCollector, MetricsCollectorConfig, MetricsCollectorError, MetricsCollectorStats,
    Quantile, SummaryValue,
};

pub use prometheus_exporter::{
    PrometheusExporter, PrometheusExporterConfig, PrometheusExporterError, PrometheusExporterStats,
    PrometheusMetric, PrometheusSample,
};

// 错误监控系统相关类型
pub use crate::error::ErrorSeverity;
pub use crate::error::{OtlpError, Result};

// 重新导出错误监控系统类型
pub use error_monitoring_types::{
    AggregatedErrorData, AggregationConfig, Alert, AlertCondition, AlertConfig, AlertEvent,
    AlertManager, AlertRule, AlertStatus, Anomaly, AnomalyDetectionConfig, AnomalyDetector,
    CollectorMetrics, Compression, Correlation, CorrelationConfig, CorrelationEngine,
    CorrelationRule, CorrelationType, DashboardConfig, DashboardMetrics, DashboardUpdate,
    ErrorAggregator, ErrorEvent, ErrorHotspot, ErrorHotspotDetector, ErrorMetricsCollector,
    ErrorMetricsConfig, ErrorMonitoringConfig, ErrorMonitoringMetrics, ErrorMonitoringSystem,
    ErrorPattern, ErrorPrediction, ErrorTrendAnalyzer, HealthMetrics, HealthStatus,
    HotspotDetectionConfig, MonitoringDataPoint, MonitoringError, NotificationChannel,
    NotificationConfig, NotificationService, PredictionModel, PredictionResult, PredictiveConfig,
    PredictiveMonitor, RealTimeDashboard, StreamConfig, StreamProcessingConfig, StreamProcessor,
    TimeSeriesPoint, TrendAnalysisConfig, TrendAnalysisResult, TrendDirection,
};

// 重新导出增强告警管理器
pub use enhanced_alert_manager::{
    Alert as EnhancedAlert, AlertCondition as EnhancedAlertCondition,
    AlertRule as EnhancedAlertRule, AlertSeverity as EnhancedAlertSeverity,
    AlertStatsSnapshot as EnhancedAlertStatsSnapshot, AlertStatus as EnhancedAlertStatus,
    ComparisonOperator, EnhancedAlertManager, NotificationChannel as EnhancedNotificationChannel,
    PredefinedAlertRules,
};

/// 监控系统配置
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MonitoringConfig {
    /// 指标收集器配置
    pub metrics_collector: MetricsCollectorConfig,
    /// Prometheus 导出器配置
    pub prometheus_exporter: PrometheusExporterConfig,
    /// 是否启用监控
    pub enabled: bool,
    /// 监控名称空间
    pub namespace: String,
    /// 监控标签
    pub labels: std::collections::HashMap<String, String>,
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            metrics_collector: MetricsCollectorConfig::default(),
            prometheus_exporter: PrometheusExporterConfig::default(),
            enabled: true,
            namespace: "otlp".to_string(),
            labels: std::collections::HashMap::new(),
        }
    }
}

/// 监控系统
///
/// 统一管理所有监控组件
pub struct MonitoringSystem {
    config: MonitoringConfig,
    metrics_collector: Option<MetricsCollector>,
    prometheus_exporter: Option<PrometheusExporter>,
}

impl MonitoringSystem {
    /// 创建新的监控系统
    pub fn new(config: MonitoringConfig) -> Self {
        Self {
            config,
            metrics_collector: None,
            prometheus_exporter: None,
        }
    }

    /// 初始化监控系统
    pub fn initialize(&mut self) -> std::result::Result<(), Box<dyn std::error::Error>> {
        if !self.config.enabled {
            return Ok(());
        }

        // 初始化指标收集器
        let metrics_collector = MetricsCollector::new(self.config.metrics_collector.clone())?;
        let metrics_collector_arc = std::sync::Arc::new(metrics_collector);

        // 初始化 Prometheus 导出器
        let prometheus_exporter = PrometheusExporter::new(
            self.config.prometheus_exporter.clone(),
            metrics_collector_arc.clone(),
        )?;

        self.metrics_collector = Some(metrics_collector_arc.as_ref().clone());
        self.prometheus_exporter = Some(prometheus_exporter);

        Ok(())
    }

    /// 获取指标收集器
    pub fn get_metrics_collector(&self) -> Option<&MetricsCollector> {
        self.metrics_collector.as_ref()
    }

    /// 获取 Prometheus 导出器
    pub fn get_prometheus_exporter(&self) -> Option<&PrometheusExporter> {
        self.prometheus_exporter.as_ref()
    }

    /// 获取配置
    pub fn get_config(&self) -> &MonitoringConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(
        &mut self,
        config: MonitoringConfig,
    ) -> std::result::Result<(), Box<dyn std::error::Error>> {
        self.config = config;

        // 重新初始化监控系统
        self.initialize()?;

        Ok(())
    }

    /// 关闭监控系统
    pub fn shutdown(&self) {
        if let Some(collector) = &self.metrics_collector {
            collector.shutdown();
        }

        if let Some(exporter) = &self.prometheus_exporter {
            exporter.shutdown();
        }
    }

    /// 等待监控系统关闭
    pub async fn wait_for_shutdown(&self) {
        if let Some(collector) = &self.metrics_collector {
            collector.wait_for_shutdown().await;
        }

        if let Some(exporter) = &self.prometheus_exporter {
            exporter.wait_for_shutdown().await;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monitoring_config_default() {
        let config = MonitoringConfig::default();
        assert!(config.enabled);
        assert_eq!(config.namespace, "otlp");
        assert!(config.labels.is_empty());
    }

    #[tokio::test]
    async fn test_monitoring_system() {
        let config = MonitoringConfig::default();
        let mut monitoring_system = MonitoringSystem::new(config);

        // 初始化监控系统
        monitoring_system
            .initialize()
            .expect("Failed to initialize monitoring system");

        // 验证组件已初始化
        assert!(monitoring_system.get_metrics_collector().is_some());
        assert!(monitoring_system.get_prometheus_exporter().is_some());

        // 关闭监控系统
        monitoring_system.shutdown();
    }

    #[tokio::test]
    async fn test_monitoring_system_disabled() {
        let mut config = MonitoringConfig::default();
        config.enabled = false;

        let mut monitoring_system = MonitoringSystem::new(config);

        // 初始化监控系统
        monitoring_system
            .initialize()
            .expect("Failed to initialize monitoring system");

        // 验证组件未初始化
        assert!(monitoring_system.get_metrics_collector().is_none());
        assert!(monitoring_system.get_prometheus_exporter().is_none());
    }
}
