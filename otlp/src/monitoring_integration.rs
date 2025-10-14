//! 监控集成模块 - Rust 1.90 企业级监控和可观测性
//! 
//! 本模块实现了基于Rust 1.90的企业级监控和可观测性功能，
//! 包括Prometheus集成、Grafana仪表板、实时监控、告警系统等。

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};

use tokio::sync::{RwLock, broadcast};
use anyhow::{Result, anyhow};
use serde::{Deserialize, Serialize};
// 简化的性能统计类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComprehensivePerformanceStats {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub network_io: u64,
    pub disk_io: u64,
    pub memory_pool: MemoryPoolStats,
    pub simd: SimdStats,
    pub concurrency: ConcurrencyStats,
    pub total_operations: u64,
    pub optimized_operations: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryPoolStats {
    pub hit_rate: f64,
    pub total_allocations: u64,
    pub total_deallocations: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimdStats {
    pub operations_processed: u64,
    pub performance_gain: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcurrencyStats {
    pub tasks_submitted: u64,
    pub tasks_completed: u64,
    pub active_tasks: u64,
}

// 简化的安全统计类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComprehensiveSecurityStats {
    pub auth_attempts: u64,
    pub failed_auth: u64,
    pub security_events: u64,
    pub encryption: EncryptionStats,
    pub authentication: AuthenticationStats,
    pub audit: AuditStats,
    pub policy_violations: u64,
    pub blocked_requests: u64,
    pub allowed_requests: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionStats {
    pub encryptions: u64,
    pub decryptions: u64,
    pub key_rotations: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationStats {
    pub successful_logins: u64,
    pub failed_logins: u64,
    pub token_validations: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditStats {
    pub total_logs: u64,
    pub success_logs: u64,
    pub failure_logs: u64,
}

/// Prometheus指标收集器
pub struct PrometheusCollector {
    metrics: Arc<RwLock<HashMap<String, MetricValue>>>,
    collectors: Arc<RwLock<Vec<Box<dyn MetricCollector + Send + Sync>>>>,
    stats: Arc<PrometheusStats>,
}

#[derive(Debug, Clone)]
pub enum MetricValue {
    Counter(u64),
    Gauge(f64),
    Histogram(Vec<f64>),
    Summary { count: u64, sum: f64 },
}

#[derive(Debug, Default)]
pub struct PrometheusStats {
    pub metrics_collected: AtomicU64,
    pub collection_errors: AtomicU64,
    pub last_collection_time: AtomicU64,
}

pub trait MetricCollector {
    fn collect(&self) -> Result<HashMap<String, MetricValue>>;
    fn get_name(&self) -> &str;
}

impl PrometheusCollector {
    /// 创建新的Prometheus收集器
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            collectors: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(PrometheusStats::default()),
        }
    }

    /// 添加指标收集器
    pub async fn add_collector(&self, collector: Box<dyn MetricCollector + Send + Sync>) {
        let mut collectors = self.collectors.write().await;
        collectors.push(collector);
    }

    /// 收集所有指标
    pub async fn collect_metrics(&self) -> Result<HashMap<String, MetricValue>> {
        let start_time = Instant::now();
        let mut all_metrics = HashMap::new();
        
        let collectors = self.collectors.read().await;
        for collector in collectors.iter() {
            match collector.collect() {
                Ok(metrics) => {
                    for (key, value) in metrics {
                        all_metrics.insert(format!("{}_{}", collector.get_name(), key), value);
                    }
                },
                Err(e) => {
                    self.stats.collection_errors.fetch_add(1, Ordering::Relaxed);
                    eprintln!("指标收集错误 {}: {}", collector.get_name(), e);
                }
            }
        }

        // 更新收集的指标
        let mut metrics = self.metrics.write().await;
        *metrics = all_metrics.clone();

        self.stats.metrics_collected.fetch_add(1, Ordering::Relaxed);
        self.stats.last_collection_time.store(
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs(),
            Ordering::Relaxed
        );

        let collection_time = start_time.elapsed();
        println!("Prometheus指标收集完成: {} 个指标, 耗时: {:?}", all_metrics.len(), collection_time);

        Ok(all_metrics)
    }

    /// 获取指标值
    pub async fn get_metric(&self, name: &str) -> Option<MetricValue> {
        let metrics = self.metrics.read().await;
        metrics.get(name).cloned()
    }

    /// 获取所有指标
    pub async fn get_all_metrics(&self) -> HashMap<String, MetricValue> {
        self.metrics.read().await.clone()
    }

    /// 获取Prometheus格式的指标输出
    pub async fn get_prometheus_format(&self) -> String {
        let metrics = self.metrics.read().await;
        let mut output = String::new();
        
        for (name, value) in metrics.iter() {
            match value {
                MetricValue::Counter(val) => {
                    output.push_str(&format!("{} {}\n", name, val));
                },
                MetricValue::Gauge(val) => {
                    output.push_str(&format!("{} {}\n", name, val));
                },
                MetricValue::Histogram(buckets) => {
                    for (i, bucket) in buckets.iter().enumerate() {
                        output.push_str(&format!("{}_bucket{{le=\"{}\"}} {}\n", name, i, bucket));
                    }
                },
                MetricValue::Summary { count, sum } => {
                    output.push_str(&format!("{}_count {}\n", name, count));
                    output.push_str(&format!("{}_sum {}\n", name, sum));
                }
            }
        }
        
        output
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> PrometheusStatsSnapshot {
        PrometheusStatsSnapshot {
            metrics_collected: self.stats.metrics_collected.load(Ordering::Relaxed),
            collection_errors: self.stats.collection_errors.load(Ordering::Relaxed),
            last_collection_time: self.stats.last_collection_time.load(Ordering::Relaxed),
        }
    }
}

/// Prometheus统计信息快照
#[derive(Debug, Clone)]
pub struct PrometheusStatsSnapshot {
    pub metrics_collected: u64,
    pub collection_errors: u64,
    pub last_collection_time: u64,
}

/// 性能指标收集器
#[derive(Debug)]
pub struct PerformanceMetricCollector {
    performance_stats: Arc<RwLock<Option<ComprehensivePerformanceStats>>>,
}

impl PerformanceMetricCollector {
    pub fn new() -> Self {
        Self {
            performance_stats: Arc::new(RwLock::new(None)),
        }
    }

    pub async fn update_stats(&self, stats: ComprehensivePerformanceStats) {
        let mut performance_stats = self.performance_stats.write().await;
        *performance_stats = Some(stats);
    }
}

impl MetricCollector for PerformanceMetricCollector {
    fn collect(&self) -> Result<HashMap<String, MetricValue>> {
        let performance_stats = self.performance_stats.try_read()
            .map_err(|_| anyhow!("无法获取性能统计信息"))?;
        
        let mut metrics = HashMap::new();
        
        if let Some(stats) = performance_stats.as_ref() {
            // 内存池指标
            metrics.insert("memory_pool_hit_rate".to_string(), MetricValue::Gauge(stats.memory_pool.hit_rate));
            metrics.insert("memory_pool_allocations".to_string(), MetricValue::Counter(stats.memory_pool.total_allocations));
            metrics.insert("memory_pool_evictions".to_string(), MetricValue::Counter(stats.memory_pool.total_deallocations));
            
            // SIMD指标
            metrics.insert("simd_operations_processed".to_string(), MetricValue::Counter(stats.simd.operations_processed));
            metrics.insert("simd_performance_gain".to_string(), MetricValue::Counter(stats.simd.performance_gain));
            
            // 并发指标
            metrics.insert("concurrency_tasks_submitted".to_string(), MetricValue::Counter(stats.concurrency.tasks_submitted));
            metrics.insert("concurrency_tasks_completed".to_string(), MetricValue::Counter(stats.concurrency.tasks_completed));
            metrics.insert("concurrency_active_tasks".to_string(), MetricValue::Gauge(stats.concurrency.active_tasks as f64));
            
            // 综合指标
            metrics.insert("total_operations".to_string(), MetricValue::Counter(stats.total_operations));
            metrics.insert("optimized_operations".to_string(), MetricValue::Counter(stats.optimized_operations));
            metrics.insert("cache_hits".to_string(), MetricValue::Counter(stats.cache_hits));
            metrics.insert("cache_misses".to_string(), MetricValue::Counter(stats.cache_misses));
        }
        
        Ok(metrics)
    }

    fn get_name(&self) -> &str {
        "performance"
    }
}

/// 安全指标收集器
#[derive(Debug)]
pub struct SecurityMetricCollector {
    security_stats: Arc<RwLock<Option<ComprehensiveSecurityStats>>>,
}

impl SecurityMetricCollector {
    pub fn new() -> Self {
        Self {
            security_stats: Arc::new(RwLock::new(None)),
        }
    }

    pub async fn update_stats(&self, stats: ComprehensiveSecurityStats) {
        let mut security_stats = self.security_stats.write().await;
        *security_stats = Some(stats);
    }
}

impl MetricCollector for SecurityMetricCollector {
    fn collect(&self) -> Result<HashMap<String, MetricValue>> {
        let security_stats = self.security_stats.try_read()
            .map_err(|_| anyhow!("无法获取安全统计信息"))?;
        
        let mut metrics = HashMap::new();
        
        if let Some(stats) = security_stats.as_ref() {
            // 加密指标
            metrics.insert("encryption_encryptions".to_string(), MetricValue::Counter(stats.encryption.encryptions));
            metrics.insert("encryption_decryptions".to_string(), MetricValue::Counter(stats.encryption.decryptions));
            metrics.insert("encryption_key_rotations".to_string(), MetricValue::Counter(stats.encryption.key_rotations));
            
            // 认证指标
            metrics.insert("auth_successful_logins".to_string(), MetricValue::Counter(stats.authentication.successful_logins));
            metrics.insert("auth_failed_logins".to_string(), MetricValue::Counter(stats.authentication.failed_logins));
            metrics.insert("auth_token_validations".to_string(), MetricValue::Counter(stats.authentication.token_validations));
            
            // 审计指标
            metrics.insert("audit_total_logs".to_string(), MetricValue::Counter(stats.audit.total_logs));
            metrics.insert("audit_success_logs".to_string(), MetricValue::Counter(stats.audit.success_logs));
            metrics.insert("audit_failure_logs".to_string(), MetricValue::Counter(stats.audit.failure_logs));
            
            // 综合安全指标
            metrics.insert("security_events".to_string(), MetricValue::Counter(stats.security_events));
            metrics.insert("policy_violations".to_string(), MetricValue::Counter(stats.policy_violations));
            metrics.insert("blocked_requests".to_string(), MetricValue::Counter(stats.blocked_requests));
            metrics.insert("allowed_requests".to_string(), MetricValue::Counter(stats.allowed_requests));
        }
        
        Ok(metrics)
    }

    fn get_name(&self) -> &str {
        "security"
    }
}

/// Grafana仪表板管理器
#[derive(Debug)]
pub struct GrafanaDashboardManager {
    dashboards: Arc<RwLock<HashMap<String, Dashboard>>>,
    datasources: Arc<RwLock<Vec<DataSource>>>,
    stats: Arc<GrafanaStats>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dashboard {
    pub id: String,
    pub title: String,
    pub panels: Vec<Panel>,
    pub refresh_interval: Duration,
    pub created_at: SystemTime,
    pub updated_at: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Panel {
    pub id: String,
    pub title: String,
    pub panel_type: PanelType,
    pub targets: Vec<QueryTarget>,
    pub position: PanelPosition,
    pub options: PanelOptions,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PanelType {
    Graph,
    Singlestat,
    Table,
    Heatmap,
    Alertlist,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryTarget {
    pub expr: String,
    pub legend_format: Option<String>,
    pub ref_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PanelPosition {
    pub x: i32,
    pub y: i32,
    pub width: i32,
    pub height: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PanelOptions {
    pub show_legend: bool,
    pub show_grid: bool,
    pub show_axes: bool,
    pub unit: Option<String>,
    pub min_value: Option<f64>,
    pub max_value: Option<f64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataSource {
    pub id: String,
    pub name: String,
    pub ds_type: DataSourceType,
    pub url: String,
    pub access: DataSourceAccess,
    pub is_default: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataSourceType {
    Prometheus,
    InfluxDB,
    Elasticsearch,
    MySQL,
    PostgreSQL,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataSourceAccess {
    Direct,
    Proxy,
}

#[derive(Debug, Default)]
pub struct GrafanaStats {
    pub dashboards_created: AtomicU64,
    pub dashboards_updated: AtomicU64,
    pub panels_created: AtomicU64,
    pub datasources_created: AtomicU64,
}

impl GrafanaDashboardManager {
    /// 创建新的Grafana仪表板管理器
    pub fn new() -> Self {
        Self {
            dashboards: Arc::new(RwLock::new(HashMap::new())),
            datasources: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(GrafanaStats::default()),
        }
    }

    /// 创建仪表板
    pub async fn create_dashboard(&self, dashboard: Dashboard) -> Result<()> {
        let mut dashboards = self.dashboards.write().await;
        dashboards.insert(dashboard.id.clone(), dashboard);
        self.stats.dashboards_created.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// 更新仪表板
    pub async fn update_dashboard(&self, id: &str, dashboard: Dashboard) -> Result<()> {
        let mut dashboards = self.dashboards.write().await;
        if dashboards.contains_key(id) {
            dashboards.insert(id.to_string(), dashboard);
            self.stats.dashboards_updated.fetch_add(1, Ordering::Relaxed);
            Ok(())
        } else {
            Err(anyhow!("仪表板不存在: {}", id))
        }
    }

    /// 获取仪表板
    pub async fn get_dashboard(&self, id: &str) -> Option<Dashboard> {
        let dashboards = self.dashboards.read().await;
        dashboards.get(id).cloned()
    }

    /// 创建性能监控仪表板
    pub async fn create_performance_dashboard(&self) -> Result<String> {
        let dashboard_id = "performance_monitoring".to_string();
        
        let panels = vec![
            Panel {
                id: "memory_pool_hit_rate".to_string(),
                title: "内存池命中率".to_string(),
                panel_type: PanelType::Singlestat,
                targets: vec![QueryTarget {
                    expr: "performance_memory_pool_hit_rate".to_string(),
                    legend_format: Some("命中率".to_string()),
                    ref_id: "A".to_string(),
                }],
                position: PanelPosition { x: 0, y: 0, width: 6, height: 4 },
                options: PanelOptions {
                    show_legend: false,
                    show_grid: false,
                    show_axes: false,
                    unit: Some("percent".to_string()),
                    min_value: Some(0.0),
                    max_value: Some(100.0),
                },
            },
            Panel {
                id: "simd_operations".to_string(),
                title: "SIMD操作数".to_string(),
                panel_type: PanelType::Graph,
                targets: vec![QueryTarget {
                    expr: "rate(performance_simd_operations_processed[5m])".to_string(),
                    legend_format: Some("操作数/秒".to_string()),
                    ref_id: "A".to_string(),
                }],
                position: PanelPosition { x: 6, y: 0, width: 6, height: 4 },
                options: PanelOptions {
                    show_legend: true,
                    show_grid: true,
                    show_axes: true,
                    unit: Some("ops/sec".to_string()),
                    min_value: None,
                    max_value: None,
                },
            },
            Panel {
                id: "concurrency_tasks".to_string(),
                title: "并发任务数".to_string(),
                panel_type: PanelType::Graph,
                targets: vec![
                    QueryTarget {
                        expr: "performance_concurrency_tasks_submitted".to_string(),
                        legend_format: Some("提交任务".to_string()),
                        ref_id: "A".to_string(),
                    },
                    QueryTarget {
                        expr: "performance_concurrency_tasks_completed".to_string(),
                        legend_format: Some("完成任务".to_string()),
                        ref_id: "B".to_string(),
                    },
                ],
                position: PanelPosition { x: 0, y: 4, width: 12, height: 4 },
                options: PanelOptions {
                    show_legend: true,
                    show_grid: true,
                    show_axes: true,
                    unit: Some("count".to_string()),
                    min_value: Some(0.0),
                    max_value: None,
                },
            },
        ];

        let dashboard = Dashboard {
            id: dashboard_id.clone(),
            title: "OTLP性能监控".to_string(),
            panels,
            refresh_interval: Duration::from_secs(30),
            created_at: SystemTime::now(),
            updated_at: SystemTime::now(),
        };

        self.create_dashboard(dashboard).await?;
        Ok(dashboard_id)
    }

    /// 创建安全监控仪表板
    pub async fn create_security_dashboard(&self) -> Result<String> {
        let dashboard_id = "security_monitoring".to_string();
        
        let panels = vec![
            Panel {
                id: "auth_success_rate".to_string(),
                title: "认证成功率".to_string(),
                panel_type: PanelType::Singlestat,
                targets: vec![QueryTarget {
                    expr: "rate(security_auth_successful_logins[5m]) / (rate(security_auth_successful_logins[5m]) + rate(security_auth_failed_logins[5m])) * 100".to_string(),
                    legend_format: Some("成功率".to_string()),
                    ref_id: "A".to_string(),
                }],
                position: PanelPosition { x: 0, y: 0, width: 6, height: 4 },
                options: PanelOptions {
                    show_legend: false,
                    show_grid: false,
                    show_axes: false,
                    unit: Some("percent".to_string()),
                    min_value: Some(0.0),
                    max_value: Some(100.0),
                },
            },
            Panel {
                id: "security_events".to_string(),
                title: "安全事件".to_string(),
                panel_type: PanelType::Graph,
                targets: vec![
                    QueryTarget {
                        expr: "rate(security_security_events[5m])".to_string(),
                        legend_format: Some("安全事件".to_string()),
                        ref_id: "A".to_string(),
                    },
                    QueryTarget {
                        expr: "rate(security_policy_violations[5m])".to_string(),
                        legend_format: Some("策略违规".to_string()),
                        ref_id: "B".to_string(),
                    },
                ],
                position: PanelPosition { x: 6, y: 0, width: 6, height: 4 },
                options: PanelOptions {
                    show_legend: true,
                    show_grid: true,
                    show_axes: true,
                    unit: Some("events/sec".to_string()),
                    min_value: Some(0.0),
                    max_value: None,
                },
            },
            Panel {
                id: "request_blocking".to_string(),
                title: "请求阻止率".to_string(),
                panel_type: PanelType::Graph,
                targets: vec![QueryTarget {
                    expr: "rate(security_blocked_requests[5m]) / (rate(security_blocked_requests[5m]) + rate(security_allowed_requests[5m])) * 100".to_string(),
                    legend_format: Some("阻止率".to_string()),
                    ref_id: "A".to_string(),
                }],
                position: PanelPosition { x: 0, y: 4, width: 12, height: 4 },
                options: PanelOptions {
                    show_legend: true,
                    show_grid: true,
                    show_axes: true,
                    unit: Some("percent".to_string()),
                    min_value: Some(0.0),
                    max_value: Some(100.0),
                },
            },
        ];

        let dashboard = Dashboard {
            id: dashboard_id.clone(),
            title: "OTLP安全监控".to_string(),
            panels,
            refresh_interval: Duration::from_secs(30),
            created_at: SystemTime::now(),
            updated_at: SystemTime::now(),
        };

        self.create_dashboard(dashboard).await?;
        Ok(dashboard_id)
    }

    /// 添加数据源
    pub async fn add_datasource(&self, datasource: DataSource) -> Result<()> {
        let mut datasources = self.datasources.write().await;
        datasources.push(datasource);
        self.stats.datasources_created.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> GrafanaStatsSnapshot {
        GrafanaStatsSnapshot {
            dashboards_created: self.stats.dashboards_created.load(Ordering::Relaxed),
            dashboards_updated: self.stats.dashboards_updated.load(Ordering::Relaxed),
            panels_created: self.stats.panels_created.load(Ordering::Relaxed),
            datasources_created: self.stats.datasources_created.load(Ordering::Relaxed),
        }
    }
}

/// Grafana统计信息快照
#[derive(Debug, Clone)]
pub struct GrafanaStatsSnapshot {
    pub dashboards_created: u64,
    pub dashboards_updated: u64,
    pub panels_created: u64,
    pub datasources_created: u64,
}

/// 实时监控系统
#[derive(Debug)]
pub struct RealtimeMonitoringSystem {
    metrics_stream: broadcast::Sender<MetricUpdate>,
    alert_manager: Arc<AlertManager>,
    stats: Arc<MonitoringStats>,
    is_running: Arc<AtomicBool>,
}

#[derive(Debug, Clone)]
pub struct MetricUpdate {
    pub name: String,
    pub value: MetricValue,
    pub timestamp: SystemTime,
    pub labels: HashMap<String, String>,
}

#[derive(Debug, Default)]
pub struct MonitoringStats {
    pub metrics_received: AtomicU64,
    pub alerts_triggered: AtomicU64,
    pub alerts_resolved: AtomicU64,
    pub monitoring_errors: AtomicU64,
}

impl RealtimeMonitoringSystem {
    /// 创建新的实时监控系统
    pub fn new() -> Self {
        let (metrics_stream, _) = broadcast::channel(1000);
        
        Self {
            metrics_stream,
            alert_manager: Arc::new(AlertManager::new()),
            stats: Arc::new(MonitoringStats::default()),
            is_running: Arc::new(AtomicBool::new(false)),
        }
    }

    /// 启动监控系统
    pub async fn start(&self) -> Result<()> {
        if self.is_running.load(Ordering::Relaxed) {
            return Err(anyhow!("监控系统已在运行"));
        }

        self.is_running.store(true, Ordering::Relaxed);
        let mut receiver = self.metrics_stream.subscribe();
        let alert_manager = self.alert_manager.clone();
        let stats = self.stats.clone();

        // 启动指标处理任务
        tokio::spawn(async move {
            while let Ok(update) = receiver.recv().await {
                stats.metrics_received.fetch_add(1, Ordering::Relaxed);
                
                // 检查告警条件
                if let Err(e) = alert_manager.check_alerts(&update).await {
                    stats.monitoring_errors.fetch_add(1, Ordering::Relaxed);
                    eprintln!("告警检查错误: {}", e);
                }
            }
        });

        println!("实时监控系统已启动");
        Ok(())
    }

    /// 停止监控系统
    pub async fn stop(&self) -> Result<()> {
        if !self.is_running.load(Ordering::Relaxed) {
            return Err(anyhow!("监控系统未在运行"));
        }

        self.is_running.store(false, Ordering::Relaxed);
        println!("实时监控系统已停止");
        Ok(())
    }

    /// 发送指标更新
    pub async fn send_metric_update(&self, update: MetricUpdate) -> Result<()> {
        if !self.is_running.load(Ordering::Relaxed) {
            return Err(anyhow!("监控系统未在运行"));
        }

        self.metrics_stream.send(update)?;
        Ok(())
    }

    /// 获取告警管理器
    pub fn get_alert_manager(&self) -> Arc<AlertManager> {
        self.alert_manager.clone()
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> MonitoringStatsSnapshot {
        MonitoringStatsSnapshot {
            metrics_received: self.stats.metrics_received.load(Ordering::Relaxed),
            alerts_triggered: self.stats.alerts_triggered.load(Ordering::Relaxed),
            alerts_resolved: self.stats.alerts_resolved.load(Ordering::Relaxed),
            monitoring_errors: self.stats.monitoring_errors.load(Ordering::Relaxed),
        }
    }
}

/// 告警管理器
#[derive(Debug)]
pub struct AlertManager {
    rules: Arc<RwLock<Vec<AlertRule>>>,
    active_alerts: Arc<RwLock<HashMap<String, Alert>>>,
    stats: Arc<AlertStats>,
}

#[derive(Debug, Clone)]
pub struct AlertRule {
    pub id: String,
    pub name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
    pub duration: Duration,
    pub is_enabled: bool,
}

#[derive(Debug, Clone)]
pub enum AlertCondition {
    GreaterThan { metric: String, threshold: f64 },
    LessThan { metric: String, threshold: f64 },
    Equal { metric: String, value: f64 },
    NotEqual { metric: String, value: f64 },
}

#[derive(Debug, Clone)]
pub enum AlertSeverity {
    Info,
    Warning,
    Critical,
    Emergency,
}

#[derive(Debug, Clone)]
pub struct Alert {
    pub id: String,
    pub rule_id: String,
    pub name: String,
    pub severity: AlertSeverity,
    pub message: String,
    pub triggered_at: SystemTime,
    pub resolved_at: Option<SystemTime>,
    pub is_active: bool,
}

#[derive(Debug, Default)]
pub struct AlertStats {
    pub rules_created: AtomicU64,
    pub alerts_triggered: AtomicU64,
    pub alerts_resolved: AtomicU64,
    pub false_positives: AtomicU64,
}

impl AlertManager {
    /// 创建新的告警管理器
    pub fn new() -> Self {
        Self {
            rules: Arc::new(RwLock::new(Vec::new())),
            active_alerts: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(AlertStats::default()),
        }
    }

    /// 添加告警规则
    pub async fn add_rule(&self, rule: AlertRule) -> Result<()> {
        let mut rules = self.rules.write().await;
        rules.push(rule);
        self.stats.rules_created.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// 检查告警条件
    pub async fn check_alerts(&self, update: &MetricUpdate) -> Result<()> {
        let rules = self.rules.read().await;
        
        for rule in rules.iter() {
            if !rule.is_enabled {
                continue;
            }

            if self.evaluate_condition(&rule.condition, update)? {
                self.trigger_alert(rule, update).await?;
            }
        }
        
        Ok(())
    }

    /// 评估告警条件
    fn evaluate_condition(&self, condition: &AlertCondition, update: &MetricUpdate) -> Result<bool> {
        match condition {
            AlertCondition::GreaterThan { metric, threshold } => {
                if update.name == *metric {
                    if let MetricValue::Gauge(value) = update.value {
                        return Ok(value > *threshold);
                    }
                }
            },
            AlertCondition::LessThan { metric, threshold } => {
                if update.name == *metric {
                    if let MetricValue::Gauge(value) = update.value {
                        return Ok(value < *threshold);
                    }
                }
            },
            AlertCondition::Equal { metric, value } => {
                if update.name == *metric {
                    if let MetricValue::Gauge(metric_value) = update.value {
                        return Ok((metric_value - value).abs() < f64::EPSILON);
                    }
                }
            },
            AlertCondition::NotEqual { metric, value } => {
                if update.name == *metric {
                    if let MetricValue::Gauge(metric_value) = update.value {
                        return Ok((metric_value - value).abs() >= f64::EPSILON);
                    }
                }
            },
        }
        
        Ok(false)
    }

    /// 触发告警
    async fn trigger_alert(&self, rule: &AlertRule, update: &MetricUpdate) -> Result<()> {
        let alert_id = format!("{}_{}", rule.id, update.timestamp.duration_since(UNIX_EPOCH)?.as_secs());
        
        let alert = Alert {
            id: alert_id.clone(),
            rule_id: rule.id.clone(),
            name: rule.name.clone(),
            severity: rule.severity.clone(),
            message: format!("指标 {} 触发告警规则 {}", update.name, rule.name),
            triggered_at: SystemTime::now(),
            resolved_at: None,
            is_active: true,
        };

        let mut active_alerts = self.active_alerts.write().await;
        active_alerts.insert(alert_id, alert);
        self.stats.alerts_triggered.fetch_add(1, Ordering::Relaxed);

        println!("告警触发: {} - {}", rule.name, update.name);
        Ok(())
    }

    /// 获取活跃告警
    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        let active_alerts = self.active_alerts.read().await;
        active_alerts.values().filter(|alert| alert.is_active).cloned().collect()
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> AlertStatsSnapshot {
        AlertStatsSnapshot {
            rules_created: self.stats.rules_created.load(Ordering::Relaxed),
            alerts_triggered: self.stats.alerts_triggered.load(Ordering::Relaxed),
            alerts_resolved: self.stats.alerts_resolved.load(Ordering::Relaxed),
            false_positives: self.stats.false_positives.load(Ordering::Relaxed),
        }
    }
}

/// 监控统计信息快照
#[derive(Debug, Clone)]
pub struct MonitoringStatsSnapshot {
    pub metrics_received: u64,
    pub alerts_triggered: u64,
    pub alerts_resolved: u64,
    pub monitoring_errors: u64,
}

/// 告警统计信息快照
#[derive(Debug, Clone)]
pub struct AlertStatsSnapshot {
    pub rules_created: u64,
    pub alerts_triggered: u64,
    pub alerts_resolved: u64,
    pub false_positives: u64,
}

/// 综合监控管理器
pub struct ComprehensiveMonitoringManager {
    prometheus_collector: PrometheusCollector,
    grafana_manager: GrafanaDashboardManager,
    monitoring_system: RealtimeMonitoringSystem,
    performance_collector: Arc<PerformanceMetricCollector>,
    security_collector: Arc<SecurityMetricCollector>,
    stats: Arc<ComprehensiveMonitoringStats>,
}

#[derive(Debug, Default)]
pub struct ComprehensiveMonitoringStats {
    pub monitoring_sessions: AtomicU64,
    pub dashboards_created: AtomicU64,
    pub metrics_collected: AtomicU64,
    pub alerts_processed: AtomicU64,
}

impl ComprehensiveMonitoringManager {
    /// 创建新的综合监控管理器
    pub fn new() -> Self {
        let prometheus_collector = PrometheusCollector::new();
        let grafana_manager = GrafanaDashboardManager::new();
        let monitoring_system = RealtimeMonitoringSystem::new();
        let performance_collector = Arc::new(PerformanceMetricCollector::new());
        let security_collector = Arc::new(SecurityMetricCollector::new());

        Self {
            prometheus_collector,
            grafana_manager,
            monitoring_system,
            performance_collector,
            security_collector,
            stats: Arc::new(ComprehensiveMonitoringStats::default()),
        }
    }

    /// 初始化监控系统
    pub async fn initialize(&self) -> Result<()> {
        // 添加指标收集器
        self.prometheus_collector.add_collector(Box::new(PerformanceMetricCollector::new())).await;
        self.prometheus_collector.add_collector(Box::new(SecurityMetricCollector::new())).await;

        // 创建默认仪表板
        self.grafana_manager.create_performance_dashboard().await?;
        self.grafana_manager.create_security_dashboard().await?;

        // 添加Prometheus数据源
        let prometheus_datasource = DataSource {
            id: "prometheus".to_string(),
            name: "Prometheus".to_string(),
            ds_type: DataSourceType::Prometheus,
            url: "http://localhost:9090".to_string(),
            access: DataSourceAccess::Direct,
            is_default: true,
        };
        self.grafana_manager.add_datasource(prometheus_datasource).await?;

        // 启动实时监控系统
        self.monitoring_system.start().await?;

        self.stats.monitoring_sessions.fetch_add(1, Ordering::Relaxed);
        println!("综合监控管理器初始化完成");

        Ok(())
    }

    /// 更新性能指标
    pub async fn update_performance_metrics(&self, stats: ComprehensivePerformanceStats) -> Result<()> {
        self.performance_collector.update_stats(stats).await;
        
        // 收集并发送指标更新
        let metrics = self.prometheus_collector.collect_metrics().await?;
        for (name, value) in metrics {
            let update = MetricUpdate {
                name,
                value,
                timestamp: SystemTime::now(),
                labels: HashMap::new(),
            };
            self.monitoring_system.send_metric_update(update).await?;
        }

        self.stats.metrics_collected.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// 更新安全指标
    pub async fn update_security_metrics(&self, stats: ComprehensiveSecurityStats) -> Result<()> {
        self.security_collector.update_stats(stats).await;
        
        // 收集并发送指标更新
        let metrics = self.prometheus_collector.collect_metrics().await?;
        for (name, value) in metrics {
            let update = MetricUpdate {
                name,
                value,
                timestamp: SystemTime::now(),
                labels: HashMap::new(),
            };
            self.monitoring_system.send_metric_update(update).await?;
        }

        self.stats.metrics_collected.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// 获取Prometheus格式指标
    pub async fn get_prometheus_metrics(&self) -> String {
        self.prometheus_collector.get_prometheus_format().await
    }

    /// 获取活跃告警
    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        self.monitoring_system.get_alert_manager().get_active_alerts().await
    }

    /// 获取综合统计信息
    pub fn get_comprehensive_stats(&self) -> ComprehensiveMonitoringStatsSnapshot {
        ComprehensiveMonitoringStatsSnapshot {
            prometheus: self.prometheus_collector.get_stats(),
            grafana: self.grafana_manager.get_stats(),
            monitoring: self.monitoring_system.get_stats(),
            alerts: self.monitoring_system.get_alert_manager().get_stats(),
            monitoring_sessions: self.stats.monitoring_sessions.load(Ordering::Relaxed),
            dashboards_created: self.stats.dashboards_created.load(Ordering::Relaxed),
            metrics_collected: self.stats.metrics_collected.load(Ordering::Relaxed),
            alerts_processed: self.stats.alerts_processed.load(Ordering::Relaxed),
        }
    }
}

/// 综合监控统计信息快照
#[derive(Debug, Clone)]
pub struct ComprehensiveMonitoringStatsSnapshot {
    pub prometheus: PrometheusStatsSnapshot,
    pub grafana: GrafanaStatsSnapshot,
    pub monitoring: MonitoringStatsSnapshot,
    pub alerts: AlertStatsSnapshot,
    pub monitoring_sessions: u64,
    pub dashboards_created: u64,
    pub metrics_collected: u64,
    pub alerts_processed: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_prometheus_collector() {
        let collector = PrometheusCollector::new();
        
        // 测试指标收集
        let metrics = collector.collect_metrics().await
            .unwrap_or_else(|e| {
                eprintln!("Failed to collect Prometheus metrics: {}", e);
                std::collections::HashMap::new()
            });
        assert!(metrics.is_empty()); // 初始状态应该为空
        
        // 测试统计信息
        let stats = collector.get_stats();
        assert_eq!(stats.metrics_collected, 1); // 收集操作本身会增加计数
    }

    #[tokio::test]
    async fn test_grafana_dashboard_manager() {
        let manager = GrafanaDashboardManager::new();
        
        // 测试创建性能仪表板
        let dashboard_id = manager.create_performance_dashboard().await
            .unwrap_or_else(|e| {
                eprintln!("Failed to create Grafana dashboard: {}", e);
                "error_dashboard".to_string()
            });
        assert_eq!(dashboard_id, "performance_monitoring");
        
        // 测试获取仪表板
        let dashboard = manager.get_dashboard(&dashboard_id).await;
        assert!(dashboard.is_some());
        
        // 测试统计信息
        let stats = manager.get_stats();
        assert_eq!(stats.dashboards_created, 1);
    }

    #[tokio::test]
    async fn test_alert_manager() {
        let manager = AlertManager::new();
        
        // 添加告警规则
        let rule = AlertRule {
            id: "test_rule".to_string(),
            name: "测试规则".to_string(),
            condition: AlertCondition::GreaterThan {
                metric: "test_metric".to_string(),
                threshold: 100.0,
            },
            severity: AlertSeverity::Warning,
            duration: Duration::from_secs(60),
            is_enabled: true,
        };
        
        manager.add_rule(rule).await
            .unwrap_or_else(|e| {
                eprintln!("Failed to add alert rule: {}", e);
            });
        
        // 测试告警触发
        let update = MetricUpdate {
            name: "test_metric".to_string(),
            value: MetricValue::Gauge(150.0),
            timestamp: SystemTime::now(),
            labels: HashMap::new(),
        };
        
        manager.check_alerts(&update).await
            .unwrap_or_else(|e| {
                eprintln!("Failed to check alerts: {}", e);
            });
        
        // 检查活跃告警
        let alerts = manager.get_active_alerts().await;
        assert!(!alerts.is_empty());
    }

    #[tokio::test]
    async fn test_comprehensive_monitoring_manager() {
        let manager = ComprehensiveMonitoringManager::new();
        
        // 测试初始化
        manager.initialize().await
            .unwrap_or_else(|e| {
                eprintln!("Failed to initialize comprehensive monitoring manager: {}", e);
            });
        
        // 测试获取Prometheus指标
        let metrics = manager.get_prometheus_metrics().await;
        assert!(!metrics.is_empty());
        
        // 测试获取统计信息
        let stats = manager.get_comprehensive_stats();
        assert_eq!(stats.monitoring_sessions, 1);
    }
}
