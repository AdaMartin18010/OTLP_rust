//! # Kubernetes 可观测性场景示例
//!
//! 展示在 Kubernetes 环境中使用 OTLP Rust 进行集群监控：
//! - Pod 指标采集
//! - 节点健康检查
//! - 服务发现
//! - 资源使用追踪
//! - 告警和通知

use anyhow::Result;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{interval, sleep, Duration, Instant};

/// ============================================
/// Kubernetes 资源模型
/// ============================================

/// K8s 命名空间
#[derive(Clone, Debug)]
pub struct Namespace {
    pub name: String,
    pub labels: HashMap<String, String>,
    pub status: NamespaceStatus,
}

#[derive(Clone, Debug)]
pub enum NamespaceStatus {
    Active,
    Terminating,
}

/// K8s Pod
#[derive(Clone, Debug)]
pub struct Pod {
    pub name: String,
    pub namespace: String,
    pub node_name: String,
    pub containers: Vec<Container>,
    pub phase: PodPhase,
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub labels: HashMap<String, String>,
}

#[derive(Clone, Debug)]
pub enum PodPhase {
    Pending,
    Running,
    Succeeded,
    Failed,
    Unknown,
}

/// K8s 容器
#[derive(Clone, Debug)]
pub struct Container {
    pub name: String,
    pub image: String,
    pub resources: ResourceRequirements,
    pub status: ContainerStatus,
}

#[derive(Clone, Debug, Default)]
pub struct ResourceRequirements {
    pub cpu_request: Option<String>,
    pub cpu_limit: Option<String>,
    pub memory_request: Option<String>,
    pub memory_limit: Option<String>,
}

#[derive(Clone, Debug)]
pub struct ContainerStatus {
    pub ready: bool,
    pub restart_count: i32,
    pub state: ContainerState,
}

#[derive(Clone, Debug)]
pub enum ContainerState {
    Waiting { reason: String },
    Running { started_at: chrono::DateTime<chrono::Utc> },
    Terminated { exit_code: i32, reason: String },
}

/// K8s 节点
#[derive(Clone, Debug)]
pub struct Node {
    pub name: String,
    pub labels: HashMap<String, String>,
    pub capacity: NodeCapacity,
    pub conditions: Vec<NodeCondition>,
}

#[derive(Clone, Debug)]
pub struct NodeCapacity {
    pub cpu: String,
    pub memory: String,
    pub pods: i32,
}

#[derive(Clone, Debug)]
pub struct NodeCondition {
    pub condition_type: String,
    pub status: ConditionStatus,
    pub last_transition: chrono::DateTime<chrono::Utc>,
    pub reason: String,
}

#[derive(Clone, Debug)]
pub enum ConditionStatus {
    True,
    False,
    Unknown,
}

/// ============================================
/// 遥测基础设施
/// ============================================

/// 指标类型
#[derive(Clone, Debug)]
pub enum Metric {
    PodMetric {
        pod_name: String,
        namespace: String,
        metric_type: PodMetricType,
        value: f64,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
    NodeMetric {
        node_name: String,
        metric_type: NodeMetricType,
        value: f64,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
    ContainerMetric {
        pod_name: String,
        namespace: String,
        container_name: String,
        metric_type: ContainerMetricType,
        value: f64,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
}

#[derive(Clone, Debug)]
pub enum PodMetricType {
    CpuUsage,
    MemoryUsage,
    NetworkReceiveBytes,
    NetworkTransmitBytes,
    Restarts,
}

#[derive(Clone, Debug)]
pub enum NodeMetricType {
    CpuUsage,
    MemoryUsage,
    DiskUsage,
    PodCount,
    ConditionReady,
}

#[derive(Clone, Debug)]
pub enum ContainerMetricType {
    CpuUsage,
    MemoryUsage,
    DiskUsage,
    RestartCount,
}

/// 指标导出器
#[derive(Clone)]
pub struct MetricsExporter {
    sender: mpsc::UnboundedSender<Metric>,
}

impl MetricsExporter {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<Metric>) {
        let (sender, receiver) = mpsc::unbounded_channel();
        (Self { sender }, receiver)
    }

    pub fn export(&self, metric: Metric) -> Result<()> {
        self.sender
            .send(metric)
            .map_err(|_| anyhow::anyhow!("Failed to send metric"))
    }
}

/// 告警
#[derive(Clone, Debug)]
pub struct Alert {
    pub name: String,
    pub severity: AlertSeverity,
    pub resource_type: String,
    pub resource_name: String,
    pub message: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub labels: HashMap<String, String>,
}

#[derive(Clone, Debug)]
pub enum AlertSeverity {
    Critical,
    Warning,
    Info,
}

/// 告警管理器
pub struct AlertManager {
    exporter: MetricsExporter,
    alert_history: Arc<RwLock<Vec<Alert>>>,
    rules: Vec<AlertRule>,
}

pub struct AlertRule {
    pub name: String,
    pub condition: Box<dyn Fn(&Metric) -> bool + Send + Sync>,
    pub severity: AlertSeverity,
    pub message_template: String,
}

impl AlertManager {
    pub fn new(exporter: MetricsExporter) -> Self {
        Self {
            exporter,
            alert_history: Arc::new(RwLock::new(Vec::new())),
            rules: Vec::new(),
        }
    }

    pub fn add_rule<F>(&mut self, name: &str, severity: AlertSeverity, message: &str, condition: F)
    where
        F: Fn(&Metric) -> bool + Send + Sync + 'static,
    {
        self.rules.push(AlertRule {
            name: name.to_string(),
            condition: Box::new(condition),
            severity,
            message_template: message.to_string(),
        });
    }

    pub async fn evaluate(&self, metric: &Metric) {
        for rule in &self.rules {
            if (rule.condition)(metric) {
                let (resource_type, resource_name) = match metric {
                    Metric::PodMetric { pod_name, .. } => ("Pod".to_string(), pod_name.clone()),
                    Metric::NodeMetric { node_name, .. } => ("Node".to_string(), node_name.clone()),
                    Metric::ContainerMetric { container_name, .. } => {
                        ("Container".to_string(), container_name.clone())
                    }
                };

                let alert = Alert {
                    name: rule.name.clone(),
                    severity: rule.severity.clone(),
                    resource_type,
                    resource_name,
                    message: rule.message_template.clone(),
                    timestamp: chrono::Utc::now(),
                    labels: HashMap::new(),
                };

                self.alert_history.write().await.push(alert.clone());
                println!(
                    "🚨 ALERT [{}]: {} - {}: {}",
                    format!("{:?}", alert.severity).to_uppercase(),
                    alert.name,
                    alert.resource_name,
                    alert.message
                );
            }
        }
    }
}

/// ============================================
/// 模拟 K8s API
/// ============================================

pub struct MockKubernetesAPI {
    namespaces: Arc<RwLock<Vec<Namespace>>>,
    pods: Arc<RwLock<Vec<Pod>>>,
    nodes: Arc<RwLock<Vec<Node>>>,
}

impl MockKubernetesAPI {
    pub fn new() -> Self {
        let namespaces = vec![
            Namespace {
                name: "default".to_string(),
                labels: HashMap::new(),
                status: NamespaceStatus::Active,
            },
            Namespace {
                name: "kube-system".to_string(),
                labels: HashMap::new(),
                status: NamespaceStatus::Active,
            },
            Namespace {
                name: "production".to_string(),
                labels: {
                    let mut map = HashMap::new();
                    map.insert("env".to_string(), "prod".to_string());
                    map
                },
                status: NamespaceStatus::Active,
            },
        ];

        let nodes = vec![
            Node {
                name: "worker-1".to_string(),
                labels: {
                    let mut map = HashMap::new();
                    map.insert("node-role".to_string(), "worker".to_string());
                    map
                },
                capacity: NodeCapacity {
                    cpu: "8".to_string(),
                    memory: "32Gi".to_string(),
                    pods: 110,
                },
                conditions: vec![
                    NodeCondition {
                        condition_type: "Ready".to_string(),
                        status: ConditionStatus::True,
                        last_transition: chrono::Utc::now(),
                        reason: "KubeletReady".to_string(),
                    },
                ],
            },
            Node {
                name: "worker-2".to_string(),
                labels: {
                    let mut map = HashMap::new();
                    map.insert("node-role".to_string(), "worker".to_string());
                    map
                },
                capacity: NodeCapacity {
                    cpu: "8".to_string(),
                    memory: "32Gi".to_string(),
                    pods: 110,
                },
                conditions: vec![
                    NodeCondition {
                        condition_type: "Ready".to_string(),
                        status: ConditionStatus::True,
                        last_transition: chrono::Utc::now(),
                        reason: "KubeletReady".to_string(),
                    },
                ],
            },
        ];

        let pods = vec![
            Pod {
                name: "web-server-7d9f4b8c5-x2v9p".to_string(),
                namespace: "production".to_string(),
                node_name: "worker-1".to_string(),
                containers: vec![
                    Container {
                        name: "nginx".to_string(),
                        image: "nginx:1.25".to_string(),
                        resources: ResourceRequirements {
                            cpu_request: Some("100m".to_string()),
                            cpu_limit: Some("500m".to_string()),
                            memory_request: Some("128Mi".to_string()),
                            memory_limit: Some("512Mi".to_string()),
                        },
                        status: ContainerStatus {
                            ready: true,
                            restart_count: 0,
                            state: ContainerState::Running {
                                started_at: chrono::Utc::now(),
                            },
                        },
                    },
                ],
                phase: PodPhase::Running,
                start_time: Some(chrono::Utc::now()),
                labels: {
                    let mut map = HashMap::new();
                    map.insert("app".to_string(), "web-server".to_string());
                    map.insert("tier".to_string(), "frontend".to_string());
                    map
                },
            },
            Pod {
                name: "api-service-5c7d8f9a2-b3m5n".to_string(),
                namespace: "production".to_string(),
                node_name: "worker-2".to_string(),
                containers: vec![
                    Container {
                        name: "api".to_string(),
                        image: "myapp/api:v2.1.0".to_string(),
                        resources: ResourceRequirements {
                            cpu_request: Some("200m".to_string()),
                            cpu_limit: Some("1000m".to_string()),
                            memory_request: Some("256Mi".to_string()),
                            memory_limit: Some("1Gi".to_string()),
                        },
                        status: ContainerStatus {
                            ready: true,
                            restart_count: 2,
                            state: ContainerState::Running {
                                started_at: chrono::Utc::now(),
                            },
                        },
                    },
                ],
                phase: PodPhase::Running,
                start_time: Some(chrono::Utc::now()),
                labels: {
                    let mut map = HashMap::new();
                    map.insert("app".to_string(), "api-service".to_string());
                    map.insert("tier".to_string(), "backend".to_string());
                    map
                },
            },
            Pod {
                name: "memory-hog-9x8y7z6w".to_string(),
                namespace: "production".to_string(),
                node_name: "worker-1".to_string(),
                containers: vec![
                    Container {
                        name: "leaky-app".to_string(),
                        image: "badapp:latest".to_string(),
                        resources: ResourceRequirements {
                            cpu_request: Some("500m".to_string()),
                            cpu_limit: Some("2000m".to_string()),
                            memory_request: Some("512Mi".to_string()),
                            memory_limit: Some("1Gi".to_string()),
                        },
                        status: ContainerStatus {
                            ready: true,
                            restart_count: 5,
                            state: ContainerState::Running {
                                started_at: chrono::Utc::now(),
                            },
                        },
                    },
                ],
                phase: PodPhase::Running,
                start_time: Some(chrono::Utc::now()),
                labels: HashMap::new(),
            },
        ];

        Self {
            namespaces: Arc::new(RwLock::new(namespaces)),
            pods: Arc::new(RwLock::new(pods)),
            nodes: Arc::new(RwLock::new(nodes)),
        }
    }

    pub async fn list_pods(&self, namespace: Option<&str>) -> Vec<Pod> {
        let pods = self.pods.read().await;
        match namespace {
            Some(ns) => pods.iter().filter(|p| p.namespace == ns).cloned().collect(),
            None => pods.clone(),
        }
    }

    pub async fn list_nodes(&self) -> Vec<Node> {
        self.nodes.read().await.clone()
    }

    pub async fn get_pod_metrics(&self, pod: &Pod) -> Vec<Metric> {
        let mut metrics = Vec::new();
        let timestamp = chrono::Utc::now();

        // 模拟 Pod 级指标
        let cpu_usage = match pod.name.as_str() {
            "memory-hog-9x8y7z6w" => 1.8, // 高CPU使用
            _ => rand::random::<f64>() * 0.5,
        };

        let memory_usage = match pod.name.as_str() {
            "memory-hog-9x8y7z6w" => 0.95, // 高内存使用
            _ => rand::random::<f64>() * 0.6,
        };

        metrics.push(Metric::PodMetric {
            pod_name: pod.name.clone(),
            namespace: pod.namespace.clone(),
            metric_type: PodMetricType::CpuUsage,
            value: cpu_usage,
            timestamp,
        });

        metrics.push(Metric::PodMetric {
            pod_name: pod.name.clone(),
            namespace: pod.namespace.clone(),
            metric_type: PodMetricType::MemoryUsage,
            value: memory_usage,
            timestamp,
        });

        // 容器级指标
        for container in &pod.containers {
            metrics.push(Metric::ContainerMetric {
                pod_name: pod.name.clone(),
                namespace: pod.namespace.clone(),
                container_name: container.name.clone(),
                metric_type: ContainerMetricType::RestartCount,
                value: container.status.restart_count as f64,
                timestamp,
            });
        }

        metrics
    }

    pub async fn get_node_metrics(&self, node: &Node) -> Vec<Metric> {
        let mut metrics = Vec::new();
        let timestamp = chrono::Utc::now();

        metrics.push(Metric::NodeMetric {
            node_name: node.name.clone(),
            metric_type: NodeMetricType::CpuUsage,
            value: rand::random::<f64>() * 0.7,
            timestamp,
        });

        metrics.push(Metric::NodeMetric {
            node_name: node.name.clone(),
            metric_type: NodeMetricType::MemoryUsage,
            value: rand::random::<f64>() * 0.6,
            timestamp,
        });

        metrics.push(Metric::NodeMetric {
            node_name: node.name.clone(),
            metric_type: NodeMetricType::PodCount,
            value: rand::random::<f64>() * 20.0,
            timestamp,
        });

        metrics
    }
}

/// ============================================
/// 可观测性控制器
/// ============================================

pub struct ObservabilityController {
    k8s_api: MockKubernetesAPI,
    exporter: MetricsExporter,
    alert_manager: AlertManager,
}

impl ObservabilityController {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<Metric>) {
        let k8s_api = MockKubernetesAPI::new();
        let (exporter, receiver) = MetricsExporter::new();
        let alert_manager = AlertManager::new(exporter.clone());

        let mut controller = Self {
            k8s_api,
            exporter,
            alert_manager,
        };

        // 配置告警规则
        controller.setup_alert_rules();

        (controller, receiver)
    }

    fn setup_alert_rules(&mut self) {
        // CPU 使用率告警
        self.alert_manager.add_rule(
            "HighPodCPU",
            AlertSeverity::Warning,
            "Pod CPU usage is above 80%",
            |metric| {
                if let Metric::PodMetric {
                    metric_type: PodMetricType::CpuUsage,
                    value,
                    ..
                } = metric
                {
                    *value > 0.8
                } else {
                    false
                }
            },
        );

        // 内存使用率告警
        self.alert_manager.add_rule(
            "HighPodMemory",
            AlertSeverity::Critical,
            "Pod memory usage is above 90%",
            |metric| {
                if let Metric::PodMetric {
                    metric_type: PodMetricType::MemoryUsage,
                    value,
                    ..
                } = metric
                {
                    *value > 0.9
                } else {
                    false
                }
            },
        );

        // 容器重启次数告警
        self.alert_manager.add_rule(
            "ContainerCrashLoop",
            AlertSeverity::Critical,
            "Container has restarted more than 3 times",
            |metric| {
                if let Metric::ContainerMetric {
                    metric_type: ContainerMetricType::RestartCount,
                    value,
                    ..
                } = metric
                {
                    *value > 3.0
                } else {
                    false
                }
            },
        );
    }

    pub async fn run_collection_cycle(&self) -> CollectionResult {
        let start = Instant::now();
        let mut total_metrics = 0;

        // 采集 Pod 指标
        let pods = self.k8s_api.list_pods(None).await;
        println!("📦 发现 {} 个 Pods", pods.len());

        for pod in pods {
            let metrics = self.k8s_api.get_pod_metrics(&pod).await;
            for metric in &metrics {
                self.exporter.export(metric.clone()).ok();
                self.alert_manager.evaluate(metric).await;
            }
            total_metrics += metrics.len();
        }

        // 采集节点指标
        let nodes = self.k8s_api.list_nodes().await;
        println!("🖥️  发现 {} 个 Nodes", nodes.len());

        for node in nodes {
            let metrics = self.k8s_api.get_node_metrics(&node).await;
            for metric in &metrics {
                self.exporter.export(metric.clone()).ok();
            }
            total_metrics += metrics.len();
        }

        CollectionResult {
            duration_ms: start.elapsed().as_millis() as u64,
            metrics_collected: total_metrics,
            pods_scanned: pods.len(),
            nodes_scanned: nodes.len(),
        }
    }
}

pub struct CollectionResult {
    pub duration_ms: u64,
    pub metrics_collected: usize,
    pub pods_scanned: usize,
    pub nodes_scanned: usize,
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Kubernetes 可观测性示例 ===\n");

    // 创建控制器
    let (controller, mut receiver) = ObservabilityController::new();

    // 启动指标处理任务
    let processor = tokio::spawn(async move {
        let mut counts: HashMap<String, usize> = HashMap::new();

        while let Some(metric) = receiver.recv().await {
            let key = match &metric {
                Metric::PodMetric { metric_type, .. } => format!("Pod:{:?}", metric_type),
                Metric::NodeMetric { metric_type, .. } => format!("Node:{:?}", metric_type),
                Metric::ContainerMetric { metric_type, .. } => format!("Container:{:?}", metric_type),
            };
            *counts.entry(key).or_insert(0) += 1;
        }

        counts
    });

    // 运行多个采集周期
    for cycle in 1..=3 {
        println!("\n--- 采集周期 #{} ---", cycle);
        let result = controller.run_collection_cycle().await;

        println!("✅ 采集完成:");
        println!("   耗时: {}ms", result.duration_ms);
        println!("   Pod数: {}", result.pods_scanned);
        println!("   Node数: {}", result.nodes_scanned);
        println!("   指标数: {}", result.metrics_collected);

        sleep(Duration::from_millis(500)).await;
    }

    // 关闭并等待处理完成
    drop(controller);
    
    println!("\n--- 指标统计 ---");
    match processor.await {
        Ok(counts) => {
            for (metric_type, count) in counts {
                println!("  {}: {}", metric_type, count);
            }
        }
        Err(e) => println!("处理器错误: {}", e),
    }

    println!("\n=== 示例完成 ===");
    Ok(())
}
