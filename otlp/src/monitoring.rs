//! # 增强错误监控系统
//!
//! 实现企业级的实时错误监控、告警和趋势分析能力，
//! 支持智能告警规则、实时仪表板和错误热点检测。

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use thiserror::Error;
use tokio::sync::{mpsc, RwLock};
use tokio::time::interval;
use tracing::{debug, error, info, warn};
use uuid::Uuid;

use crate::error::ErrorSeverity;
use crate::error::{OtlpError, Result};

/// 错误监控系统
#[allow(dead_code)]
pub struct ErrorMonitoringSystem {
    real_time_dashboard: Arc<RealTimeDashboard>,
    alert_manager: Arc<AlertManager>,
    metrics_collector: Arc<MetricsCollector>,
    error_aggregator: Arc<ErrorAggregator>,
    notification_service: Arc<NotificationService>,
    trend_analyzer: Arc<ErrorTrendAnalyzer>,
    hotspot_detector: Arc<ErrorHotspotDetector>,
    stream_processor: Arc<StreamProcessor>,
    predictive_monitor: Arc<PredictiveMonitor>,
    anomaly_detector: Arc<AnomalyDetector>,
    correlation_engine: Arc<CorrelationEngine>,
}

impl ErrorMonitoringSystem {
    /// 创建新的错误监控系统
    pub fn new(config: MonitoringConfig) -> Result<Self> {
        let real_time_dashboard = Arc::new(RealTimeDashboard::new(config.dashboard.clone())?);
        let alert_manager = Arc::new(AlertManager::new(config.alerts.clone())?);
        let metrics_collector = Arc::new(MetricsCollector::new(config.metrics.clone())?);
        let error_aggregator = Arc::new(ErrorAggregator::new(config.aggregation.clone())?);
        let notification_service =
            Arc::new(NotificationService::new(config.notifications.clone())?);
        let trend_analyzer = Arc::new(ErrorTrendAnalyzer::new(config.trend_analysis.clone())?);
        let hotspot_detector =
            Arc::new(ErrorHotspotDetector::new(config.hotspot_detection.clone())?);
        let stream_processor = Arc::new(StreamProcessor::new(config.stream_processing.clone())?);
        let predictive_monitor = Arc::new(PredictiveMonitor::new(config.predictive.clone())?);
        let anomaly_detector = Arc::new(AnomalyDetector::new(config.anomaly_detection.clone())?);
        let correlation_engine = Arc::new(CorrelationEngine::new(config.correlation.clone())?);

        Ok(Self {
            real_time_dashboard,
            alert_manager,
            metrics_collector,
            error_aggregator,
            notification_service,
            trend_analyzer,
            hotspot_detector,
            stream_processor,
            predictive_monitor,
            anomaly_detector,
            correlation_engine,
        })
    }

    /// 启动监控系统
    pub async fn start(&self) -> Result<()> {
        info!("启动错误监控系统");

        // 1. 启动实时数据流
        self.start_real_time_stream().await?;

        // 2. 初始化告警规则
        self.initialize_alert_rules().await?;

        // 3. 启动监控服务
        self.start_monitoring_services().await?;

        // 4. 设置通知渠道
        self.setup_notification_channels().await?;

        // 5. 启动趋势分析
        self.start_trend_analysis().await?;

        // 6. 启动热点检测
        self.start_hotspot_detection().await?;

        info!("错误监控系统启动完成");
        Ok(())
    }

    /// 处理错误事件
    pub async fn handle_error_event(&self, error_event: ErrorEvent) -> Result<()> {
        debug!("处理错误事件: {:?}", error_event);

        // 1. 收集指标
        self.metrics_collector.record_error(&error_event).await?;

        // 2. 聚合错误数据
        self.error_aggregator.aggregate_error(&error_event).await?;

        // 3. 更新实时仪表板
        self.real_time_dashboard
            .update_with_error(&error_event)
            .await?;

        // 4. 检查告警条件
        self.alert_manager.check_alerts(&error_event).await?;

        // 5. 分析趋势
        self.trend_analyzer.analyze_error(&error_event).await?;

        // 6. 检测热点
        self.hotspot_detector.check_hotspot(&error_event).await?;

        Ok(())
    }

    /// 获取监控指标
    pub async fn get_metrics(&self) -> Result<MonitoringMetrics> {
        let metrics = MonitoringMetrics {
            total_errors: self.metrics_collector.get_total_errors().await,
            error_rate_per_minute: self.metrics_collector.get_error_rate().await,
            error_types_distribution: self.metrics_collector.get_error_types_distribution().await,
            recovery_success_rate: self.metrics_collector.get_recovery_success_rate().await,
            average_recovery_time: self.metrics_collector.get_average_recovery_time().await,
            circuit_breaker_states: self.metrics_collector.get_circuit_breaker_states().await,
            degradation_events: self.metrics_collector.get_degradation_events().await,
            active_alerts: self.alert_manager.get_active_alerts().await,
            system_health_score: self.calculate_health_score().await,
        };

        Ok(metrics)
    }

    /// 获取告警管理器
    pub fn alert_manager(&self) -> &Arc<AlertManager> {
        &self.alert_manager
    }

    /// 获取趋势分析器
    pub fn trend_analyzer(&self) -> &Arc<ErrorTrendAnalyzer> {
        &self.trend_analyzer
    }

    /// 获取热点检测器
    pub fn hotspot_detector(&self) -> &Arc<ErrorHotspotDetector> {
        &self.hotspot_detector
    }

    async fn start_real_time_stream(&self) -> Result<()> {
        let stream_config = StreamConfig {
            buffer_size: 10000,
            flush_interval: Duration::from_millis(100),
            compression: Compression::Gzip,
        };

        self.metrics_collector
            .configure_stream(stream_config)
            .await?;
        Ok(())
    }

    async fn initialize_alert_rules(&self) -> Result<()> {
        let default_rules = self.create_default_alert_rules();
        self.alert_manager.configure_rules(default_rules).await?;
        Ok(())
    }

    async fn start_monitoring_services(&self) -> Result<()> {
        // 启动定期健康检查
        let health_check_interval = Duration::from_secs(30);
        let dashboard = self.real_time_dashboard.clone();
        tokio::spawn(async move {
            let mut interval = interval(health_check_interval);
            loop {
                interval.tick().await;
                if let Err(e) = dashboard.perform_health_check().await {
                    error!("健康检查失败: {}", e);
                }
            }
        });

        Ok(())
    }

    async fn setup_notification_channels(&self) -> Result<()> {
        let channels = vec![
            NotificationChannel::Email {
                smtp_server: "smtp.example.com".to_string(),
                username: "alerts@example.com".to_string(),
                password: "password".to_string(),
            },
            NotificationChannel::Slack {
                webhook_url: "https://hooks.slack.com/services/...".to_string(),
                channel: "#alerts".to_string(),
            },
            NotificationChannel::Webhook {
                url: "https://api.example.com/webhooks/alerts".to_string(),
                headers: HashMap::new(),
            },
        ];

        self.notification_service
            .configure_channels(channels)
            .await?;
        Ok(())
    }

    async fn start_trend_analysis(&self) -> Result<()> {
        let analyzer = self.trend_analyzer.clone();
        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(60));
            loop {
                interval.tick().await;
                if let Err(e) = analyzer.analyze_trends().await {
                    error!("趋势分析失败: {}", e);
                }
            }
        });

        Ok(())
    }

    async fn start_hotspot_detection(&self) -> Result<()> {
        let detector = self.hotspot_detector.clone();
        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(30));
            loop {
                interval.tick().await;
                if let Err(e) = detector.detect_hotspots().await {
                    error!("热点检测失败: {}", e);
                }
            }
        });

        Ok(())
    }

    fn create_default_alert_rules(&self) -> Vec<AlertRule> {
        vec![
            AlertRule {
                id: "high_error_rate".to_string(),
                name: "高错误率告警".to_string(),
                condition: AlertCondition::ErrorRateThreshold {
                    threshold: 0.1,                   // 10%错误率
                    window: Duration::from_secs(300), // 5分钟窗口
                },
                severity: ErrorSeverity::High,
                cooldown_period: Duration::from_secs(300),
                notification_channels: vec!["email".to_string(), "slack".to_string()],
                auto_recovery: true,
                enabled: true,
            },
            AlertRule {
                id: "circuit_breaker_open".to_string(),
                name: "熔断器开启告警".to_string(),
                condition: AlertCondition::CircuitBreakerOpen {
                    service_name: "*".to_string(),
                },
                severity: ErrorSeverity::Critical,
                cooldown_period: Duration::from_secs(60),
                notification_channels: vec![
                    "email".to_string(),
                    "slack".to_string(),
                    "webhook".to_string(),
                ],
                auto_recovery: false,
                enabled: true,
            },
            AlertRule {
                id: "latency_spike".to_string(),
                name: "延迟突增告警".to_string(),
                condition: AlertCondition::LatencyThreshold {
                    threshold: Duration::from_secs(5),
                    percentile: 95.0,
                },
                severity: ErrorSeverity::Medium,
                cooldown_period: Duration::from_secs(180),
                notification_channels: vec!["slack".to_string()],
                auto_recovery: true,
                enabled: true,
            },
        ]
    }

    async fn calculate_health_score(&self) -> f64 {
        let metrics = self.metrics_collector.get_health_metrics().await;

        let error_rate_score = if metrics.error_rate < 0.01 {
            1.0
        } else if metrics.error_rate < 0.05 {
            0.8
        } else {
            0.5
        };
        let recovery_rate_score = metrics.recovery_success_rate;
        let latency_score = if metrics.avg_latency < Duration::from_millis(100) {
            1.0
        } else if metrics.avg_latency < Duration::from_millis(500) {
            0.8
        } else {
            0.5
        };

        (error_rate_score + recovery_rate_score + latency_score) / 3.0
    }
}

/// 错误事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorEvent {
    pub id: String,
    pub timestamp: SystemTime,
    pub error_type: String,
    pub severity: ErrorSeverity,
    pub message: String,
    pub source: String,
    pub context: HashMap<String, String>,
    pub stack_trace: Option<String>,
    pub recovery_suggestion: Option<String>,
    pub is_retryable: bool,
    pub is_temporary: bool,
}

impl ErrorEvent {
    pub fn from_otlp_error(error: &OtlpError, source: &str) -> Self {
        let error_context = error.context();
        Self {
            id: Uuid::new_v4().to_string(),
            timestamp: SystemTime::now(),
            error_type: format!("{:?}", error_context.category),
            severity: error_context.severity,
            message: error.to_string(),
            source: source.to_string(),
            context: HashMap::new(), // 简化实现，避免复杂的数据转换
            stack_trace: None,       // 简化实现
            recovery_suggestion: error_context.recovery_suggestion,
            is_retryable: error_context.is_retryable,
            is_temporary: error_context.is_retryable,
        }
    }
}

/// 实时仪表板
#[allow(dead_code)]
pub struct RealTimeDashboard {
    config: DashboardConfig,
    current_metrics: Arc<RwLock<DashboardMetrics>>,
    websocket_connections: Arc<RwLock<Vec<mpsc::UnboundedSender<DashboardUpdate>>>>,
}

impl RealTimeDashboard {
    pub fn new(config: DashboardConfig) -> Result<Self> {
        Ok(Self {
            config,
            current_metrics: Arc::new(RwLock::new(DashboardMetrics::default())),
            websocket_connections: Arc::new(RwLock::new(Vec::new())),
        })
    }

    pub async fn update_with_error(&self, error: &ErrorEvent) -> Result<()> {
        let mut metrics = self.current_metrics.write().await;

        // 更新错误计数
        metrics.total_errors += 1;
        *metrics
            .error_types
            .entry(error.error_type.clone())
            .or_insert(0) += 1;

        // 更新严重程度分布
        *metrics
            .severity_distribution
            .entry(error.severity.clone())
            .or_insert(0) += 1;

        // 更新最近错误
        metrics.recent_errors.push_back(error.clone());
        if metrics.recent_errors.len() > self.config.max_recent_errors {
            metrics.recent_errors.pop_front();
        }

        // 广播更新到所有连接的客户端
        self.broadcast_update(DashboardUpdate::ErrorAdded(error.clone()))
            .await?;

        Ok(())
    }

    pub async fn perform_health_check(&self) -> Result<()> {
        let metrics = self.current_metrics.read().await;
        let health_status = if metrics.total_errors < 100 {
            HealthStatus::Healthy
        } else if metrics.total_errors < 500 {
            HealthStatus::Warning
        } else {
            HealthStatus::Critical
        };

        self.broadcast_update(DashboardUpdate::HealthStatusChanged(health_status))
            .await?;
        Ok(())
    }

    async fn broadcast_update(&self, update: DashboardUpdate) -> Result<()> {
        let connections = self.websocket_connections.read().await;
        for connection in connections.iter() {
            if let Err(_) = connection.send(update.clone()) {
                // 连接已断开，将在下次清理时移除
            }
        }
        Ok(())
    }
}

/// 告警管理器
#[allow(dead_code)]
pub struct AlertManager {
    config: AlertConfig,
    rules: Arc<RwLock<Vec<AlertRule>>>,
    active_alerts: Arc<RwLock<HashMap<String, Alert>>>,
    alert_history: Arc<RwLock<VecDeque<AlertEvent>>>,
}

impl AlertManager {
    pub fn new(config: AlertConfig) -> Result<Self> {
        Ok(Self {
            config,
            rules: Arc::new(RwLock::new(Vec::new())),
            active_alerts: Arc::new(RwLock::new(HashMap::new())),
            alert_history: Arc::new(RwLock::new(VecDeque::new())),
        })
    }

    pub async fn configure_rules(&self, rules: Vec<AlertRule>) -> Result<()> {
        let mut rules_guard = self.rules.write().await;
        *rules_guard = rules;
        info!("配置了 {} 条告警规则", rules_guard.len());
        Ok(())
    }

    pub async fn check_alerts(&self, error: &ErrorEvent) -> Result<()> {
        let rules = self.rules.read().await;

        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }

            if self.evaluate_condition(&rule.condition, error).await? {
                self.trigger_alert(rule, error).await?;
            }
        }

        Ok(())
    }

    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        let alerts = self.active_alerts.read().await;
        // 使用Rust 1.90的元组收集特性优化监控数据收集
        alerts.values().cloned().collect()
    }

    async fn evaluate_condition(
        &self,
        condition: &AlertCondition,
        error: &ErrorEvent,
    ) -> Result<bool> {
        match condition {
            AlertCondition::ErrorRateThreshold {
                threshold: _,
                window: _,
            } => {
                // 简化的错误率检查，实际实现需要更复杂的时间窗口计算
                Ok(error.severity >= ErrorSeverity::High)
            }
            AlertCondition::LatencyThreshold {
                threshold: _,
                percentile: _,
            } => {
                // 延迟检查需要从其他地方获取延迟数据
                Ok(false)
            }
            AlertCondition::ErrorTypeSpike {
                error_type,
                multiplier: _,
            } => Ok(error.error_type == *error_type),
            AlertCondition::CircuitBreakerOpen { service_name } => {
                Ok(error.source.contains(service_name))
            }
            AlertCondition::ResourceExhaustion { resource_type: _ } => {
                Ok(error.error_type.contains("resource"))
            }
        }
    }

    async fn trigger_alert(&self, rule: &AlertRule, error: &ErrorEvent) -> Result<()> {
        let alert = Alert {
            id: Uuid::new_v4().to_string(),
            rule_id: rule.id.clone(),
            severity: rule.severity.clone(),
            message: format!("告警: {}", rule.name),
            timestamp: SystemTime::now(),
            source_error: error.clone(),
            status: AlertStatus::Active,
        };

        // 检查冷却期
        if self.is_in_cooldown(&rule.id).await {
            debug!("告警 {} 仍在冷却期，跳过", rule.id);
            return Ok(());
        }

        // 添加到活跃告警
        {
            let mut active_alerts = self.active_alerts.write().await;
            active_alerts.insert(rule.id.clone(), alert.clone());
        }

        // 记录告警历史
        {
            let mut history = self.alert_history.write().await;
            history.push_back(AlertEvent::from_alert(&alert));
            if history.len() > 1000 {
                history.pop_front();
            }
        }

        // 发送通知
        self.send_notifications(&alert, &rule.notification_channels)
            .await?;

        info!("触发告警: {} - {}", rule.name, alert.message);
        Ok(())
    }

    async fn is_in_cooldown(&self, rule_id: &str) -> bool {
        let history = self.alert_history.read().await;
        if let Some(last_alert) = history.iter().rev().find(|a| a.rule_id == rule_id) {
            let elapsed = last_alert
                .timestamp
                .elapsed()
                .unwrap_or(Duration::from_secs(0));
            let rules = self.rules.read().await;
            if let Some(rule) = rules.iter().find(|r| r.id == rule_id) {
                return elapsed < rule.cooldown_period;
            }
        }
        false
    }

    async fn send_notifications(&self, alert: &Alert, channels: &[String]) -> Result<()> {
        for channel in channels {
            // 这里应该调用实际的通知服务
            info!("发送告警通知到渠道 {}: {}", channel, alert.message);
        }
        Ok(())
    }
}

/// 指标收集器
#[allow(dead_code)]
pub struct MetricsCollector {
    config: MetricsConfig,
    metrics: Arc<RwLock<CollectorMetrics>>,
    stream_config: Arc<RwLock<Option<StreamConfig>>>,
}

impl MetricsCollector {
    pub fn new(config: MetricsConfig) -> Result<Self> {
        Ok(Self {
            config,
            metrics: Arc::new(RwLock::new(CollectorMetrics::default())),
            stream_config: Arc::new(RwLock::new(None)),
        })
    }

    pub async fn configure_stream(&self, config: StreamConfig) -> Result<()> {
        let mut stream_config = self.stream_config.write().await;
        *stream_config = Some(config);
        Ok(())
    }

    pub async fn record_error(&self, error: &ErrorEvent) -> Result<()> {
        let mut metrics = self.metrics.write().await;

        metrics.total_errors += 1;
        *metrics
            .error_types
            .entry(error.error_type.clone())
            .or_insert(0) += 1;
        *metrics
            .severity_distribution
            .entry(error.severity.clone())
            .or_insert(0) += 1;

        metrics.recent_errors.push_back(error.clone());
        if metrics.recent_errors.len() > self.config.max_recent_errors {
            metrics.recent_errors.pop_front();
        }

        Ok(())
    }

    pub async fn get_total_errors(&self) -> u64 {
        let metrics = self.metrics.read().await;
        metrics.total_errors
    }

    pub async fn get_error_rate(&self) -> f64 {
        // 简化的错误率计算，实际应该基于时间窗口
        let metrics = self.metrics.read().await;
        if metrics.total_errors > 0 {
            let recent_errors = metrics.recent_errors.len() as f64;
            let time_window_minutes = 1.0; // 1分钟窗口
            recent_errors / time_window_minutes
        } else {
            0.0
        }
    }

    pub async fn get_error_types_distribution(&self) -> HashMap<String, u64> {
        let metrics = self.metrics.read().await;
        metrics.error_types.clone()
    }

    pub async fn get_recovery_success_rate(&self) -> f64 {
        // 简化的恢复成功率，实际需要从恢复系统获取数据
        0.85
    }

    pub async fn get_average_recovery_time(&self) -> Duration {
        // 简化的平均恢复时间
        Duration::from_millis(500)
    }

    pub async fn get_circuit_breaker_states(&self) -> HashMap<String, String> {
        // 简化的熔断器状态，实际需要从熔断器系统获取
        HashMap::new()
    }

    pub async fn get_degradation_events(&self) -> Vec<String> {
        // 简化的降级事件列表
        Vec::new()
    }

    pub async fn get_health_metrics(&self) -> HealthMetrics {
        HealthMetrics {
            error_rate: self.get_error_rate().await,
            recovery_success_rate: self.get_recovery_success_rate().await,
            avg_latency: self.get_average_recovery_time().await,
        }
    }
}

/// 错误聚合器
#[allow(dead_code)]
pub struct ErrorAggregator {
    config: AggregationConfig,
    aggregated_data: Arc<RwLock<HashMap<String, AggregatedErrorData>>>,
}

impl ErrorAggregator {
    pub fn new(config: AggregationConfig) -> Result<Self> {
        Ok(Self {
            config,
            aggregated_data: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    pub async fn aggregate_error(&self, error: &ErrorEvent) -> Result<()> {
        let mut data = self.aggregated_data.write().await;
        let key = format!("{}:{}", error.error_type, error.source);

        let aggregated = data.entry(key).or_insert_with(|| AggregatedErrorData {
            error_type: error.error_type.clone(),
            source: error.source.clone(),
            count: 0,
            first_occurrence: error.timestamp,
            last_occurrence: error.timestamp,
            severity: error.severity.clone(),
            samples: VecDeque::new(),
        });

        aggregated.count += 1;
        aggregated.last_occurrence = error.timestamp;

        aggregated.samples.push_back(error.clone());
        if aggregated.samples.len() > self.config.max_samples_per_error_type {
            aggregated.samples.pop_front();
        }

        Ok(())
    }
}

/// 通知服务
#[allow(dead_code)]
pub struct NotificationService {
    config: NotificationConfig,
    channels: Arc<RwLock<HashMap<String, NotificationChannel>>>,
}

impl NotificationService {
    pub fn new(config: NotificationConfig) -> Result<Self> {
        Ok(Self {
            config,
            channels: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    pub async fn configure_channels(&self, channels: Vec<NotificationChannel>) -> Result<()> {
        let mut channels_map = self.channels.write().await;
        for channel in channels {
            let name = channel.name();
            channels_map.insert(name, channel);
        }
        Ok(())
    }

    pub async fn send_notification(&self, channel_name: &str, message: &str) -> Result<()> {
        let channels = self.channels.read().await;
        if let Some(channel) = channels.get(channel_name) {
            channel.send(message).await?;
        } else {
            warn!("未找到通知渠道: {}", channel_name);
        }
        Ok(())
    }
}

/// 错误趋势分析器
#[allow(dead_code)]
pub struct ErrorTrendAnalyzer {
    config: TrendAnalysisConfig,
    time_series_data: Arc<RwLock<VecDeque<TimeSeriesPoint>>>,
}

impl ErrorTrendAnalyzer {
    pub fn new(config: TrendAnalysisConfig) -> Result<Self> {
        Ok(Self {
            config,
            time_series_data: Arc::new(RwLock::new(VecDeque::new())),
        })
    }

    pub async fn analyze_error(&self, error: &ErrorEvent) -> Result<()> {
        let point = TimeSeriesPoint {
            timestamp: error.timestamp,
            error_count: 1,
            error_types: HashMap::from([(error.error_type.clone(), 1)]),
        };

        let mut data = self.time_series_data.write().await;
        data.push_back(point);

        if data.len() > self.config.max_data_points {
            data.pop_front();
        }

        Ok(())
    }

    pub async fn analyze_trends(&self) -> Result<TrendAnalysisResult> {
        let data = self.time_series_data.read().await;

        if data.is_empty() {
            return Ok(TrendAnalysisResult::default());
        }

        // 简化的趋势分析
        let total_errors: u64 = data.iter().map(|p| p.error_count).sum();
        let error_rate = if data.len() > 1 {
            let duration = data
                .back()
                .unwrap()
                .timestamp
                .duration_since(data.front().unwrap().timestamp)
                .unwrap_or(Duration::from_secs(1));
            total_errors as f64 / duration.as_secs() as f64
        } else {
            0.0
        };

        Ok(TrendAnalysisResult {
            error_rate,
            trend_direction: if error_rate > 1.0 {
                TrendDirection::Increasing
            } else {
                TrendDirection::Stable
            },
            anomalies: Vec::new(),
            predictions: Vec::new(),
        })
    }
}

/// 错误热点检测器
#[allow(dead_code)]
pub struct ErrorHotspotDetector {
    config: HotspotDetectionConfig,
    error_patterns: Arc<RwLock<HashMap<String, ErrorPattern>>>,
}

impl ErrorHotspotDetector {
    pub fn new(config: HotspotDetectionConfig) -> Result<Self> {
        Ok(Self {
            config,
            error_patterns: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    pub async fn check_hotspot(&self, error: &ErrorEvent) -> Result<()> {
        let pattern_key = format!("{}:{}", error.error_type, error.source);
        let mut patterns = self.error_patterns.write().await;

        let pattern = patterns.entry(pattern_key).or_insert_with(|| ErrorPattern {
            error_type: error.error_type.clone(),
            source: error.source.clone(),
            occurrences: VecDeque::new(),
            is_hotspot: false,
        });

        pattern.occurrences.push_back(error.timestamp);

        // 清理旧数据
        let cutoff = SystemTime::now() - self.config.detection_window;
        pattern.occurrences.retain(|&time| time > cutoff);

        // 检查是否成为热点
        if pattern.occurrences.len() > self.config.alert_threshold {
            pattern.is_hotspot = true;
            warn!(
                "检测到错误热点: {} - {} ({} 次)",
                pattern.error_type,
                pattern.source,
                pattern.occurrences.len()
            );
        }

        Ok(())
    }

    pub async fn detect_hotspots(&self) -> Result<Vec<ErrorHotspot>> {
        let patterns = self.error_patterns.read().await;
        let mut hotspots = Vec::new();

        for (key, pattern) in patterns.iter() {
            if pattern.is_hotspot {
                let hotspot = ErrorHotspot {
                    pattern: key.clone(),
                    error_rate: pattern.occurrences.len() as f64,
                    affected_services: vec![pattern.source.clone()],
                    recommended_actions: self.generate_recommendations(pattern),
                    predicted_escalation: false,
                };
                hotspots.push(hotspot);
            }
        }

        Ok(hotspots)
    }

    fn generate_recommendations(&self, pattern: &ErrorPattern) -> Vec<String> {
        match pattern.error_type.as_str() {
            "transport" => vec![
                "增加重试机制".to_string(),
                "实现熔断器".to_string(),
                "检查网络连接".to_string(),
            ],
            "resource" => vec![
                "扩展资源".to_string(),
                "实现负载均衡".to_string(),
                "添加缓存".to_string(),
            ],
            _ => vec!["手动调查".to_string()],
        }
    }
}

// 配置结构体
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct MonitoringConfig {
    pub dashboard: DashboardConfig,
    pub alerts: AlertConfig,
    pub metrics: MetricsConfig,
    pub aggregation: AggregationConfig,
    pub notifications: NotificationConfig,
    pub trend_analysis: TrendAnalysisConfig,
    pub hotspot_detection: HotspotDetectionConfig,
    pub stream_processing: StreamProcessingConfig,
    pub predictive: PredictiveConfig,
    pub anomaly_detection: AnomalyDetectionConfig,
    pub correlation: CorrelationConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct DashboardConfig {
    pub max_recent_errors: usize,
    pub update_interval: Duration,
    pub websocket_port: u16,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct AlertConfig {
    pub default_cooldown: Duration,
    pub max_alerts_per_rule: usize,
    pub alert_history_size: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct MetricsConfig {
    pub max_recent_errors: usize,
    pub collection_interval: Duration,
    pub retention_period: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct AggregationConfig {
    pub max_samples_per_error_type: usize,
    pub aggregation_window: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct NotificationConfig {
    pub retry_attempts: u32,
    pub retry_delay: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct TrendAnalysisConfig {
    pub max_data_points: usize,
    pub analysis_window: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct HotspotDetectionConfig {
    pub detection_window: Duration,
    pub alert_threshold: usize,
}

// 数据结构体
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct MonitoringMetrics {
    pub total_errors: u64,
    pub error_rate_per_minute: f64,
    pub error_types_distribution: HashMap<String, u64>,
    pub recovery_success_rate: f64,
    pub average_recovery_time: Duration,
    pub circuit_breaker_states: HashMap<String, String>,
    pub degradation_events: Vec<String>,
    pub active_alerts: Vec<Alert>,
    pub system_health_score: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct DashboardMetrics {
    pub total_errors: u64,
    pub error_types: HashMap<String, u64>,
    pub severity_distribution: HashMap<ErrorSeverity, u64>,
    pub recent_errors: VecDeque<ErrorEvent>,
}

impl Default for DashboardMetrics {
    fn default() -> Self {
        Self {
            total_errors: 0,
            error_types: HashMap::new(),
            severity_distribution: HashMap::new(),
            recent_errors: VecDeque::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertRule {
    pub id: String,
    pub name: String,
    pub condition: AlertCondition,
    pub severity: ErrorSeverity,
    pub cooldown_period: Duration,
    pub notification_channels: Vec<String>,
    pub auto_recovery: bool,
    pub enabled: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertCondition {
    ErrorRateThreshold {
        threshold: f64,
        window: Duration,
    },
    LatencyThreshold {
        threshold: Duration,
        percentile: f64,
    },
    ErrorTypeSpike {
        error_type: String,
        multiplier: f64,
    },
    CircuitBreakerOpen {
        service_name: String,
    },
    ResourceExhaustion {
        resource_type: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    pub id: String,
    pub rule_id: String,
    pub severity: ErrorSeverity,
    pub message: String,
    pub timestamp: SystemTime,
    pub source_error: ErrorEvent,
    pub status: AlertStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertStatus {
    Active,
    Resolved,
    Suppressed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertEvent {
    pub alert_id: String,
    pub rule_id: String,
    pub timestamp: SystemTime,
    pub message: String,
}

impl AlertEvent {
    pub fn from_alert(alert: &Alert) -> Self {
        Self {
            alert_id: alert.id.clone(),
            rule_id: alert.rule_id.clone(),
            timestamp: alert.timestamp,
            message: alert.message.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NotificationChannel {
    Email {
        smtp_server: String,
        username: String,
        password: String,
    },
    Slack {
        webhook_url: String,
        channel: String,
    },
    Webhook {
        url: String,
        headers: HashMap<String, String>,
    },
}

impl NotificationChannel {
    pub fn name(&self) -> String {
        match self {
            Self::Email { .. } => "email".to_string(),
            Self::Slack { .. } => "slack".to_string(),
            Self::Webhook { .. } => "webhook".to_string(),
        }
    }

    pub async fn send(&self, message: &str) -> Result<()> {
        match self {
            Self::Email { .. } => {
                // 实现邮件发送
                info!("发送邮件: {}", message);
            }
            Self::Slack { .. } => {
                // 实现Slack发送
                info!("发送Slack消息: {}", message);
            }
            Self::Webhook { .. } => {
                // 实现Webhook发送
                info!("发送Webhook: {}", message);
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DashboardUpdate {
    ErrorAdded(ErrorEvent),
    HealthStatusChanged(HealthStatus),
    MetricsUpdated(MonitoringMetrics),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Warning,
    Critical,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamConfig {
    pub buffer_size: usize,
    pub flush_interval: Duration,
    pub compression: Compression,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Compression {
    None,
    Gzip,
    Lz4,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct CollectorMetrics {
    pub total_errors: u64,
    pub error_types: HashMap<String, u64>,
    pub severity_distribution: HashMap<ErrorSeverity, u64>,
    pub recent_errors: VecDeque<ErrorEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AggregatedErrorData {
    pub error_type: String,
    pub source: String,
    pub count: u64,
    pub first_occurrence: SystemTime,
    pub last_occurrence: SystemTime,
    pub severity: ErrorSeverity,
    pub samples: VecDeque<ErrorEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeSeriesPoint {
    pub timestamp: SystemTime,
    pub error_count: u64,
    pub error_types: HashMap<String, u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrendAnalysisResult {
    pub error_rate: f64,
    pub trend_direction: TrendDirection,
    pub anomalies: Vec<String>,
    pub predictions: Vec<String>,
}

impl Default for TrendAnalysisResult {
    fn default() -> Self {
        Self {
            error_rate: 0.0,
            trend_direction: TrendDirection::Stable,
            anomalies: Vec::new(),
            predictions: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TrendDirection {
    Increasing,
    Decreasing,
    Stable,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorPattern {
    pub error_type: String,
    pub source: String,
    pub occurrences: VecDeque<SystemTime>,
    pub is_hotspot: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorHotspot {
    pub pattern: String,
    pub error_rate: f64,
    pub affected_services: Vec<String>,
    pub recommended_actions: Vec<String>,
    pub predicted_escalation: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthMetrics {
    pub error_rate: f64,
    pub recovery_success_rate: f64,
    pub avg_latency: Duration,
}

// 错误类型
#[derive(Error, Debug)]
pub enum MonitoringError {
    #[error("配置错误: {0}")]
    Configuration(String),
    #[error("网络错误: {0}")]
    Network(String),
    #[error("序列化错误: {0}")]
    Serialization(String),
}

impl From<MonitoringError> for OtlpError {
    fn from(err: MonitoringError) -> Self {
        OtlpError::from_anyhow(anyhow::anyhow!(err))
    }
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            dashboard: DashboardConfig {
                max_recent_errors: 100,
                update_interval: Duration::from_secs(1),
                websocket_port: 8080,
            },
            alerts: AlertConfig {
                default_cooldown: Duration::from_secs(300),
                max_alerts_per_rule: 10,
                alert_history_size: 1000,
            },
            metrics: MetricsConfig {
                max_recent_errors: 1000,
                collection_interval: Duration::from_secs(10),
                retention_period: Duration::from_secs(3600),
            },
            aggregation: AggregationConfig {
                max_samples_per_error_type: 50,
                aggregation_window: Duration::from_secs(60),
            },
            notifications: NotificationConfig {
                retry_attempts: 3,
                retry_delay: Duration::from_secs(5),
            },
            trend_analysis: TrendAnalysisConfig {
                max_data_points: 1000,
                analysis_window: Duration::from_secs(300),
            },
            hotspot_detection: HotspotDetectionConfig {
                detection_window: Duration::from_secs(300),
                alert_threshold: 10,
            },
            stream_processing: StreamProcessingConfig::default(),
            predictive: PredictiveConfig::default(),
            anomaly_detection: AnomalyDetectionConfig::default(),
            correlation: CorrelationConfig::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_error_monitoring_system() {
        let config = MonitoringConfig::default();
        let system = ErrorMonitoringSystem::new(config).unwrap();

        let error = ErrorEvent {
            id: "test-error".to_string(),
            timestamp: SystemTime::now(),
            error_type: "test".to_string(),
            severity: ErrorSeverity::Medium,
            message: "Test error".to_string(),
            source: "test".to_string(),
            context: HashMap::new(),
            stack_trace: None,
            recovery_suggestion: None,
            is_retryable: true,
            is_temporary: true,
        };

        assert!(system.handle_error_event(error).await.is_ok());
    }

    #[tokio::test]
    async fn test_alert_manager() {
        let config = AlertConfig {
            default_cooldown: Duration::from_secs(60),
            max_alerts_per_rule: 10,
            alert_history_size: 100,
        };

        let manager = AlertManager::new(config).unwrap();
        let rules = vec![AlertRule {
            id: "test-rule".to_string(),
            name: "Test Rule".to_string(),
            condition: AlertCondition::ErrorTypeSpike {
                error_type: "test".to_string(),
                multiplier: 2.0,
            },
            severity: ErrorSeverity::High,
            cooldown_period: Duration::from_secs(60),
            notification_channels: vec!["email".to_string()],
            auto_recovery: true,
            enabled: true,
        }];

        assert!(manager.configure_rules(rules).await.is_ok());
    }
}

/// 流处理器
#[allow(dead_code)]
pub struct StreamProcessor {
    config: StreamProcessingConfig,
    event_stream: mpsc::UnboundedReceiver<ErrorEvent>,
    processing_pipeline: Vec<Box<dyn Fn(ErrorEvent) -> Result<()> + Send + Sync>>,
}

impl StreamProcessor {
    pub fn new(config: StreamProcessingConfig) -> Result<Self> {
        let (_, event_stream) = mpsc::unbounded_channel();
        Ok(Self {
            config,
            event_stream,
            processing_pipeline: Vec::new(),
        })
    }

    pub async fn process_event(&mut self, event: ErrorEvent) -> Result<()> {
        // 实现流处理逻辑
        info!("处理事件: {}", event.error_type);
        Ok(())
    }

    pub async fn start_processing(&mut self) -> Result<()> {
        // 启动流处理
        info!("启动流处理");
        Ok(())
    }
}

/// 预测性监控器
#[allow(dead_code)]
pub struct PredictiveMonitor {
    config: PredictiveConfig,
    prediction_models: HashMap<String, PredictionModel>,
    historical_data: VecDeque<MonitoringDataPoint>,
}

impl PredictiveMonitor {
    pub fn new(config: PredictiveConfig) -> Result<Self> {
        Ok(Self {
            config,
            prediction_models: HashMap::new(),
            historical_data: VecDeque::new(),
        })
    }

    pub async fn predict_future_errors(&self, time_horizon: Duration) -> Result<PredictionResult> {
        // 实现预测逻辑
        Ok(PredictionResult {
            predicted_error_count: 0,
            confidence: 0.0,
            time_horizon,
            predictions: Vec::new(),
        })
    }

    pub async fn update_model(&mut self, new_data: &[MonitoringDataPoint]) -> Result<()> {
        // 更新预测模型
        for data_point in new_data {
            self.historical_data.push_back(data_point.clone());
            if self.historical_data.len() > self.config.max_history_size {
                self.historical_data.pop_front();
            }
        }
        Ok(())
    }
}

/// 异常检测器
#[allow(dead_code)]
pub struct AnomalyDetector {
    config: AnomalyDetectionConfig,
    baseline_metrics: HashMap<String, f64>,
    anomaly_thresholds: HashMap<String, f64>,
}

impl AnomalyDetector {
    pub fn new(config: AnomalyDetectionConfig) -> Result<Self> {
        Ok(Self {
            config,
            baseline_metrics: HashMap::new(),
            anomaly_thresholds: HashMap::new(),
        })
    }

    pub async fn detect_anomalies(&self, metrics: &HashMap<String, f64>) -> Result<Vec<Anomaly>> {
        let mut anomalies = Vec::new();

        for (metric_name, value) in metrics {
            if let Some(baseline) = self.baseline_metrics.get(metric_name) {
                if let Some(threshold) = self.anomaly_thresholds.get(metric_name) {
                    let deviation = (value - baseline).abs() / baseline;
                    if deviation > *threshold {
                        anomalies.push(Anomaly {
                            metric_name: metric_name.clone(),
                            value: *value,
                            baseline: *baseline,
                            deviation,
                            severity: if deviation > *threshold * 2.0 {
                                ErrorSeverity::High
                            } else {
                                ErrorSeverity::Medium
                            },
                        });
                    }
                }
            }
        }

        Ok(anomalies)
    }

    pub async fn update_baseline(&mut self, metrics: &HashMap<String, f64>) -> Result<()> {
        for (metric_name, value) in metrics {
            if let Some(current_baseline) = self.baseline_metrics.get_mut(metric_name) {
                // 使用指数移动平均更新基线
                *current_baseline = *current_baseline * 0.9 + value * 0.1;
            } else {
                self.baseline_metrics.insert(metric_name.clone(), *value);
            }
        }
        Ok(())
    }
}

/// 关联引擎
#[allow(dead_code)]
pub struct CorrelationEngine {
    config: CorrelationConfig,
    correlation_rules: Vec<CorrelationRule>,
    event_graph: HashMap<String, Vec<String>>,
}

impl CorrelationEngine {
    pub fn new(config: CorrelationConfig) -> Result<Self> {
        Ok(Self {
            config,
            correlation_rules: Vec::new(),
            event_graph: HashMap::new(),
        })
    }

    pub async fn analyze_correlations(&self, events: &[ErrorEvent]) -> Result<Vec<Correlation>> {
        let mut correlations = Vec::new();

        // 实现关联分析逻辑
        for i in 0..events.len() {
            for j in (i + 1)..events.len() {
                if self.are_events_correlated(&events[i], &events[j]) {
                    correlations.push(Correlation {
                        event1_id: events[i].id.clone(),
                        event2_id: events[j].id.clone(),
                        correlation_type: CorrelationType::Temporal,
                        strength: 0.8,
                        confidence: 0.9,
                    });
                }
            }
        }

        Ok(correlations)
    }

    fn are_events_correlated(&self, event1: &ErrorEvent, event2: &ErrorEvent) -> bool {
        // 简单的关联判断逻辑
        let time_diff = event2
            .timestamp
            .duration_since(event1.timestamp)
            .unwrap_or_default();
        time_diff < Duration::from_secs(60) && event1.error_type == event2.error_type
    }
}

/// 流处理配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamProcessingConfig {
    pub buffer_size: usize,
    pub processing_interval: Duration,
    pub max_concurrent_events: usize,
}

impl Default for StreamProcessingConfig {
    fn default() -> Self {
        Self {
            buffer_size: 1000,
            processing_interval: Duration::from_millis(100),
            max_concurrent_events: 10,
        }
    }
}

/// 预测性监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictiveConfig {
    pub prediction_horizon: Duration,
    pub model_update_interval: Duration,
    pub max_history_size: usize,
    pub confidence_threshold: f64,
}

impl Default for PredictiveConfig {
    fn default() -> Self {
        Self {
            prediction_horizon: Duration::from_secs(3600),
            model_update_interval: Duration::from_secs(300),
            max_history_size: 10000,
            confidence_threshold: 0.7,
        }
    }
}

/// 异常检测配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectionConfig {
    pub sensitivity: f64,
    pub baseline_window: Duration,
    pub update_interval: Duration,
}

impl Default for AnomalyDetectionConfig {
    fn default() -> Self {
        Self {
            sensitivity: 0.8,
            baseline_window: Duration::from_secs(3600),
            update_interval: Duration::from_secs(60),
        }
    }
}

/// 关联分析配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorrelationConfig {
    pub max_correlation_distance: Duration,
    pub min_correlation_strength: f64,
    pub correlation_window: Duration,
}

impl Default for CorrelationConfig {
    fn default() -> Self {
        Self {
            max_correlation_distance: Duration::from_secs(300),
            min_correlation_strength: 0.5,
            correlation_window: Duration::from_secs(3600),
        }
    }
}

/// 预测模型
#[derive(Debug, Clone)]
pub struct PredictionModel {
    pub model_type: String,
    pub parameters: HashMap<String, f64>,
    pub accuracy: f64,
}

/// 预测结果
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct PredictionResult {
    pub predicted_error_count: u32,
    pub confidence: f64,
    pub time_horizon: Duration,
    pub predictions: Vec<ErrorPrediction>,
}

/// 错误预测
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ErrorPrediction {
    pub error_type: String,
    pub probability: f64,
    pub expected_time: SystemTime,
    pub severity: ErrorSeverity,
}

/// 监控数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct MonitoringDataPoint {
    pub timestamp: SystemTime,
    pub metrics: HashMap<String, f64>,
    pub error_count: u32,
    pub system_health: f64,
}

/// 异常
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct Anomaly {
    pub metric_name: String,
    pub value: f64,
    pub baseline: f64,
    pub deviation: f64,
    pub severity: ErrorSeverity,
}

/// 关联规则
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct CorrelationRule {
    pub id: String,
    pub pattern: String,
    pub threshold: f64,
    pub enabled: bool,
}

/// 关联
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct Correlation {
    pub event1_id: String,
    pub event2_id: String,
    pub correlation_type: CorrelationType,
    pub strength: f64,
    pub confidence: f64,
}

/// 关联类型
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub enum CorrelationType {
    Temporal,
    Causal,
    Spatial,
    Functional,
}
