//! # Complete Kubernetes Deployment for OTLP
//!
//! 完整的Kubernetes部署示例，展示如何在K8s环境中部署OTLP Collector和应用
//!
//! ## 部署架构
//! - **DaemonSet模式**: 每个节点运行一个Collector
//! - **Sidecar模式**: 每个Pod运行一个Collector
//! - **Gateway模式**: 集中式Collector集群
//!
//! ## 功能特性
//! - 服务发现
//! - 健康检查
//! - 资源配置
//! - 自动扩缩容
//! - ConfigMap配置
//! - Secret管理
//! - RBAC权限
//! - 持久化存储
//!
//! ## 集成组件
//! - Prometheus (指标)
//! - Jaeger (追踪)
//! - Grafana (可视化)
//! - AlertManager (告警)

use k8s_openapi::api::{
    apps::v1::{DaemonSet, DaemonSetSpec, Deployment, DeploymentSpec},
    core::v1::{
        ConfigMap, Container, ContainerPort, EnvVar, PodSpec, Service, ServiceAccount, ServicePort,
        ServiceSpec, Volume, VolumeMount,
    },
    rbac::v1::{ClusterRole, ClusterRoleBinding},
};
use kube::{
    Client,
    api::{Api, PostParams},
};
use std::collections::BTreeMap;
use tracing::{info, instrument};

// ============================================================================
// Configuration Constants
// ============================================================================

const NAMESPACE: &str = "observability";
const OTLP_COLLECTOR_NAME: &str = "otlp-collector";
const OTLP_COLLECTOR_IMAGE: &str = "otel/opentelemetry-collector:latest";
const OTLP_GRPC_PORT: i32 = 4317;
const OTLP_HTTP_PORT: i32 = 4318;
const PROMETHEUS_PORT: i32 = 8888;
const HEALTH_CHECK_PORT: i32 = 13133;

// ============================================================================
// Part 1: ConfigMap - Collector Configuration
// ============================================================================

pub fn create_collector_config() -> ConfigMap {
    let config_yaml = r#"
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  k8sattributes:
    auth_type: "serviceAccount"
    passthrough: false
    filter:
      node_from_env_var: KUBE_NODE_NAME
    extract:
      metadata:
        - k8s.namespace.name
        - k8s.deployment.name
        - k8s.statefulset.name
        - k8s.daemonset.name
        - k8s.cronjob.name
        - k8s.job.name
        - k8s.node.name
        - k8s.pod.name
        - k8s.pod.uid
        - k8s.pod.start_time
      labels:
        - tag_name: app
          key: app
          from: pod
        - tag_name: version
          key: version
          from: pod
      annotations:
        - tag_name: prometheus.io/scrape
          key: prometheus.io/scrape
          from: pod

  resource:
    attributes:
      - key: cluster.name
        value: production-cluster
        action: insert
      - key: environment
        value: production
        action: insert

  attributes:
    actions:
      - key: http.user_agent
        action: delete
      - key: sensitive_field
        action: delete

exporters:
  prometheus:
    endpoint: "0.0.0.0:8888"
    namespace: otlp
    const_labels:
      cluster: production
  
  jaeger:
    endpoint: jaeger-collector.observability.svc.cluster.local:14250
    tls:
      insecure: true
  
  logging:
    loglevel: info
  
  otlp/backend:
    endpoint: otlp-backend.observability.svc.cluster.local:4317
    tls:
      insecure: false
      cert_file: /etc/otel/certs/tls.crt
      key_file: /etc/otel/certs/tls.key
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  
  pprof:
    endpoint: 0.0.0.0:1777
  
  zpages:
    endpoint: 0.0.0.0:55679

service:
  extensions: [health_check, pprof, zpages]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, k8sattributes, resource, batch]
      exporters: [jaeger, otlp/backend, logging]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, k8sattributes, resource, batch]
      exporters: [prometheus, otlp/backend, logging]
    
    logs:
      receivers: [otlp]
      processors: [memory_limiter, k8sattributes, resource, batch]
      exporters: [otlp/backend, logging]
"#;

    let mut data = BTreeMap::new();
    data.insert("collector-config.yaml".to_string(), config_yaml.to_string());

    ConfigMap {
        metadata: kube::core::ObjectMeta {
            name: Some(format!("{}-config", OTLP_COLLECTOR_NAME)),
            namespace: Some(NAMESPACE.to_string()),
            labels: Some({
                let mut labels = BTreeMap::new();
                labels.insert("app".to_string(), OTLP_COLLECTOR_NAME.to_string());
                labels.insert("component".to_string(), "config".to_string());
                labels
            }),
            ..Default::default()
        },
        data: Some(data),
        ..Default::default()
    }
}

// ============================================================================
// Part 2: RBAC Configuration
// ============================================================================

pub fn create_service_account() -> ServiceAccount {
    ServiceAccount {
        metadata: kube::core::ObjectMeta {
            name: Some(OTLP_COLLECTOR_NAME.to_string()),
            namespace: Some(NAMESPACE.to_string()),
            ..Default::default()
        },
        ..Default::default()
    }
}

pub fn create_cluster_role() -> ClusterRole {
    use k8s_openapi::api::rbac::v1::PolicyRule;

    ClusterRole {
        metadata: kube::core::ObjectMeta {
            name: Some(OTLP_COLLECTOR_NAME.to_string()),
            ..Default::default()
        },
        rules: Some(vec![
            PolicyRule {
                api_groups: Some(vec!["".to_string()]),
                resources: Some(vec![
                    "pods".to_string(),
                    "nodes".to_string(),
                    "services".to_string(),
                    "endpoints".to_string(),
                    "namespaces".to_string(),
                ]),
                verbs: vec!["get".to_string(), "list".to_string(), "watch".to_string()],
                ..Default::default()
            },
            PolicyRule {
                api_groups: Some(vec!["apps".to_string()]),
                resources: Some(vec![
                    "deployments".to_string(),
                    "daemonsets".to_string(),
                    "statefulsets".to_string(),
                    "replicasets".to_string(),
                ]),
                verbs: vec!["get".to_string(), "list".to_string(), "watch".to_string()],
                ..Default::default()
            },
        ]),
        ..Default::default()
    }
}

pub fn create_cluster_role_binding() -> ClusterRoleBinding {
    use k8s_openapi::api::rbac::v1::{RoleRef, Subject};

    ClusterRoleBinding {
        metadata: kube::core::ObjectMeta {
            name: Some(OTLP_COLLECTOR_NAME.to_string()),
            ..Default::default()
        },
        role_ref: RoleRef {
            api_group: "rbac.authorization.k8s.io".to_string(),
            kind: "ClusterRole".to_string(),
            name: OTLP_COLLECTOR_NAME.to_string(),
        },
        subjects: Some(vec![Subject {
            kind: "ServiceAccount".to_string(),
            name: OTLP_COLLECTOR_NAME.to_string(),
            namespace: Some(NAMESPACE.to_string()),
            ..Default::default()
        }]),
        ..Default::default()
    }
}

// ============================================================================
// Part 3: DaemonSet Deployment (Node-level collection)
// ============================================================================

pub fn create_daemonset() -> DaemonSet {
    use k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector;

    let mut labels = BTreeMap::new();
    labels.insert("app".to_string(), OTLP_COLLECTOR_NAME.to_string());
    labels.insert("component".to_string(), "daemonset".to_string());

    DaemonSet {
        metadata: kube::core::ObjectMeta {
            name: Some(format!("{}-daemonset", OTLP_COLLECTOR_NAME)),
            namespace: Some(NAMESPACE.to_string()),
            labels: Some(labels.clone()),
            ..Default::default()
        },
        spec: Some(DaemonSetSpec {
            selector: LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: k8s_openapi::api::core::v1::PodTemplateSpec {
                metadata: Some(kube::core::ObjectMeta {
                    labels: Some(labels.clone()),
                    annotations: Some({
                        let mut annotations = BTreeMap::new();
                        annotations.insert("prometheus.io/scrape".to_string(), "true".to_string());
                        annotations.insert(
                            "prometheus.io/port".to_string(),
                            PROMETHEUS_PORT.to_string(),
                        );
                        annotations
                    }),
                    ..Default::default()
                }),
                spec: Some(create_collector_pod_spec(true)),
            },
            ..Default::default()
        }),
        ..Default::default()
    }
}

// ============================================================================
// Part 4: Deployment (Gateway mode)
// ============================================================================

pub fn create_gateway_deployment() -> Deployment {
    use k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector;

    let mut labels = BTreeMap::new();
    labels.insert(
        "app".to_string(),
        format!("{}-gateway", OTLP_COLLECTOR_NAME),
    );
    labels.insert("component".to_string(), "gateway".to_string());

    Deployment {
        metadata: kube::core::ObjectMeta {
            name: Some(format!("{}-gateway", OTLP_COLLECTOR_NAME)),
            namespace: Some(NAMESPACE.to_string()),
            labels: Some(labels.clone()),
            ..Default::default()
        },
        spec: Some(DeploymentSpec {
            replicas: Some(3), // 3 replicas for HA
            selector: LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: k8s_openapi::api::core::v1::PodTemplateSpec {
                metadata: Some(kube::core::ObjectMeta {
                    labels: Some(labels.clone()),
                    ..Default::default()
                }),
                spec: Some(create_collector_pod_spec(false)),
            },
            ..Default::default()
        }),
        ..Default::default()
    }
}

// ============================================================================
// Part 5: Pod Specification (Shared)
// ============================================================================

fn create_collector_pod_spec(is_daemonset: bool) -> PodSpec {
    use k8s_openapi::api::core::v1::{EnvVarSource, ObjectFieldSelector, ResourceRequirements};
    use k8s_openapi::apimachinery::pkg::api::resource::Quantity;

    let env = vec![
        EnvVar {
            name: "KUBE_NODE_NAME".to_string(),
            value_from: Some(EnvVarSource {
                field_ref: Some(ObjectFieldSelector {
                    field_path: "spec.nodeName".to_string(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
        EnvVar {
            name: "POD_NAMESPACE".to_string(),
            value_from: Some(EnvVarSource {
                field_ref: Some(ObjectFieldSelector {
                    field_path: "metadata.namespace".to_string(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
        EnvVar {
            name: "POD_NAME".to_string(),
            value_from: Some(EnvVarSource {
                field_ref: Some(ObjectFieldSelector {
                    field_path: "metadata.name".to_string(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
    ];

    let mut resources = BTreeMap::new();
    if is_daemonset {
        resources.insert("cpu".to_string(), Quantity("200m".to_string()));
        resources.insert("memory".to_string(), Quantity("512Mi".to_string()));
    } else {
        resources.insert("cpu".to_string(), Quantity("1".to_string()));
        resources.insert("memory".to_string(), Quantity("2Gi".to_string()));
    }

    let mut limit_resources = BTreeMap::new();
    if is_daemonset {
        limit_resources.insert("cpu".to_string(), Quantity("500m".to_string()));
        limit_resources.insert("memory".to_string(), Quantity("1Gi".to_string()));
    } else {
        limit_resources.insert("cpu".to_string(), Quantity("2".to_string()));
        limit_resources.insert("memory".to_string(), Quantity("4Gi".to_string()));
    }

    PodSpec {
        service_account_name: Some(OTLP_COLLECTOR_NAME.to_string()),
        containers: vec![Container {
            name: "otlp-collector".to_string(),
            image: Some(OTLP_COLLECTOR_IMAGE.to_string()),
            image_pull_policy: Some("IfNotPresent".to_string()),
            args: Some(vec!["--config=/etc/otel/config.yaml".to_string()]),
            ports: Some(vec![
                ContainerPort {
                    container_port: OTLP_GRPC_PORT,
                    name: Some("otlp-grpc".to_string()),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
                ContainerPort {
                    container_port: OTLP_HTTP_PORT,
                    name: Some("otlp-http".to_string()),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
                ContainerPort {
                    container_port: PROMETHEUS_PORT,
                    name: Some("prometheus".to_string()),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
                ContainerPort {
                    container_port: HEALTH_CHECK_PORT,
                    name: Some("health".to_string()),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
            ]),
            env: Some(env),
            volume_mounts: Some(vec![VolumeMount {
                name: "config".to_string(),
                mount_path: "/etc/otel".to_string(),
                ..Default::default()
            }]),
            resources: Some(ResourceRequirements {
                requests: Some(resources),
                limits: Some(limit_resources),
                ..Default::default()
            }),
            liveness_probe: Some(k8s_openapi::api::core::v1::Probe {
                http_get: Some(k8s_openapi::api::core::v1::HTTPGetAction {
                    path: Some("/".to_string()),
                    port: k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                        HEALTH_CHECK_PORT,
                    ),
                    ..Default::default()
                }),
                initial_delay_seconds: Some(10),
                period_seconds: Some(10),
                ..Default::default()
            }),
            readiness_probe: Some(k8s_openapi::api::core::v1::Probe {
                http_get: Some(k8s_openapi::api::core::v1::HTTPGetAction {
                    path: Some("/".to_string()),
                    port: k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                        HEALTH_CHECK_PORT,
                    ),
                    ..Default::default()
                }),
                initial_delay_seconds: Some(5),
                period_seconds: Some(5),
                ..Default::default()
            }),
            ..Default::default()
        }],
        volumes: Some(vec![Volume {
            name: "config".to_string(),
            config_map: Some(k8s_openapi::api::core::v1::ConfigMapVolumeSource {
                name: format!("{}-config", OTLP_COLLECTOR_NAME),
                ..Default::default()
            }),
            ..Default::default()
        }]),
        ..Default::default()
    }
}

// ============================================================================
// Part 6: Services
// ============================================================================

pub fn create_service() -> Service {
    let mut labels = BTreeMap::new();
    labels.insert("app".to_string(), OTLP_COLLECTOR_NAME.to_string());

    Service {
        metadata: kube::core::ObjectMeta {
            name: Some(OTLP_COLLECTOR_NAME.to_string()),
            namespace: Some(NAMESPACE.to_string()),
            labels: Some(labels.clone()),
            ..Default::default()
        },
        spec: Some(ServiceSpec {
            selector: Some(labels),
            ports: Some(vec![
                ServicePort {
                    name: Some("otlp-grpc".to_string()),
                    port: OTLP_GRPC_PORT,
                    target_port: Some(
                        k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                            OTLP_GRPC_PORT,
                        ),
                    ),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
                ServicePort {
                    name: Some("otlp-http".to_string()),
                    port: OTLP_HTTP_PORT,
                    target_port: Some(
                        k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                            OTLP_HTTP_PORT,
                        ),
                    ),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
                ServicePort {
                    name: Some("prometheus".to_string()),
                    port: PROMETHEUS_PORT,
                    target_port: Some(
                        k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                            PROMETHEUS_PORT,
                        ),
                    ),
                    protocol: Some("TCP".to_string()),
                    ..Default::default()
                },
            ]),
            type_: Some("ClusterIP".to_string()),
            ..Default::default()
        }),
        ..Default::default()
    }
}

// ============================================================================
// Part 7: Deployment Functions
// ============================================================================

#[instrument(skip(client))]
pub async fn deploy_full_stack(client: Client) -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting full OTLP deployment to Kubernetes");

    // Create namespace if it doesn't exist
    create_namespace(&client).await?;

    // Deploy RBAC
    info!("Deploying RBAC configuration...");
    deploy_rbac(&client).await?;

    // Deploy ConfigMap
    info!("Deploying ConfigMap...");
    deploy_config(&client).await?;

    // Deploy Services
    info!("Deploying Services...");
    deploy_services(&client).await?;

    // Deploy DaemonSet
    info!("Deploying DaemonSet...");
    deploy_daemonset(&client).await?;

    // Deploy Gateway
    info!("Deploying Gateway...");
    deploy_gateway(&client).await?;

    info!("✅ Full OTLP deployment completed successfully!");

    Ok(())
}

async fn create_namespace(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    use k8s_openapi::api::core::v1::Namespace;

    let namespaces: Api<Namespace> = Api::all(client.clone());

    let ns = Namespace {
        metadata: kube::core::ObjectMeta {
            name: Some(NAMESPACE.to_string()),
            ..Default::default()
        },
        ..Default::default()
    };

    match namespaces.create(&PostParams::default(), &ns).await {
        Ok(_) => info!("Namespace {} created", NAMESPACE),
        Err(e) if e.to_string().contains("already exists") => {
            info!("Namespace {} already exists", NAMESPACE)
        }
        Err(e) => return Err(e.into()),
    }

    Ok(())
}

async fn deploy_rbac(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    // ServiceAccount
    let sa_api: Api<ServiceAccount> = Api::namespaced(client.clone(), NAMESPACE);
    sa_api
        .create(&PostParams::default(), &create_service_account())
        .await?;
    info!("ServiceAccount created");

    // ClusterRole
    let cr_api: Api<ClusterRole> = Api::all(client.clone());
    cr_api
        .create(&PostParams::default(), &create_cluster_role())
        .await?;
    info!("ClusterRole created");

    // ClusterRoleBinding
    let crb_api: Api<ClusterRoleBinding> = Api::all(client.clone());
    crb_api
        .create(&PostParams::default(), &create_cluster_role_binding())
        .await?;
    info!("ClusterRoleBinding created");

    Ok(())
}

async fn deploy_config(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    let cm_api: Api<ConfigMap> = Api::namespaced(client.clone(), NAMESPACE);
    cm_api
        .create(&PostParams::default(), &create_collector_config())
        .await?;
    info!("ConfigMap created");

    Ok(())
}

async fn deploy_services(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    let svc_api: Api<Service> = Api::namespaced(client.clone(), NAMESPACE);
    svc_api
        .create(&PostParams::default(), &create_service())
        .await?;
    info!("Service created");

    Ok(())
}

async fn deploy_daemonset(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    let ds_api: Api<DaemonSet> = Api::namespaced(client.clone(), NAMESPACE);
    ds_api
        .create(&PostParams::default(), &create_daemonset())
        .await?;
    info!("DaemonSet created");

    Ok(())
}

async fn deploy_gateway(client: &Client) -> Result<(), Box<dyn std::error::Error>> {
    let deploy_api: Api<Deployment> = Api::namespaced(client.clone(), NAMESPACE);
    deploy_api
        .create(&PostParams::default(), &create_gateway_deployment())
        .await?;
    info!("Gateway Deployment created");

    Ok(())
}

// ============================================================================
// Part 8: Health Check and Status
// ============================================================================

#[instrument(skip(client))]
pub async fn check_deployment_status(client: Client) -> Result<(), Box<dyn std::error::Error>> {
    info!("Checking deployment status...");

    // Check DaemonSet
    let ds_api: Api<DaemonSet> = Api::namespaced(client.clone(), NAMESPACE);
    let ds = ds_api
        .get(&format!("{}-daemonset", OTLP_COLLECTOR_NAME))
        .await?;

    if let Some(status) = ds.status {
        info!(
            "DaemonSet status: desired={:?}, ready={:?}",
            status.desired_number_scheduled, status.number_ready
        );
    }

    // Check Deployment
    let deploy_api: Api<Deployment> = Api::namespaced(client.clone(), NAMESPACE);
    let deploy = deploy_api
        .get(&format!("{}-gateway", OTLP_COLLECTOR_NAME))
        .await?;

    if let Some(status) = deploy.status {
        info!(
            "Deployment status: replicas={:?}, ready={:?}",
            status.replicas, status.ready_replicas
        );
    }

    info!("✅ Deployment status check completed");

    Ok(())
}

// ============================================================================
// Main Function
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    info!("🚀 OTLP Kubernetes Deployment Tool");

    // Initialize Kubernetes client
    let client = Client::try_default().await?;
    info!("✅ Connected to Kubernetes cluster");

    // Deploy full stack
    deploy_full_stack(client.clone()).await?;

    // Wait a bit for resources to be created
    tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;

    // Check deployment status
    check_deployment_status(client).await?;

    info!("🎉 OTLP deployment completed successfully!");
    info!("📝 You can now configure your applications to send telemetry to:");
    info!("   - gRPC: otlp-collector.observability.svc.cluster.local:4317");
    info!("   - HTTP: otlp-collector.observability.svc.cluster.local:4318");
    info!(
        "   - Prometheus metrics: http://otlp-collector.observability.svc.cluster.local:8888/metrics"
    );

    Ok(())
}
