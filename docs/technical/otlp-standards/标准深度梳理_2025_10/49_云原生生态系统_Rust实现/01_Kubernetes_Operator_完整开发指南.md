# Kubernetes Operator 完整开发指南 (Rust + kube-rs 0.95)

## 目录

- [Kubernetes Operator 完整开发指南 (Rust + kube-rs 0.95)](#kubernetes-operator-完整开发指南-rust--kube-rs-095)
  - [目录](#目录)
  - [1. Operator 模式理论](#1-operator-模式理论)
    - [1.1 Kubernetes Operator 定义](#11-kubernetes-operator-定义)
    - [1.2 国际标准对标](#12-国际标准对标)
  - [2. kube-rs 生态系统](#2-kube-rs-生态系统)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 kube-rs 核心模块](#22-kube-rs-核心模块)
  - [3. 完整 Operator 实现](#3-完整-operator-实现)
    - [3.1 项目结构](#31-项目结构)
  - [4. CRD 设计与注册](#4-crd-设计与注册)
    - [4.1 定义 CRD](#41-定义-crd)
    - [4.2 生成 CRD YAML](#42-生成-crd-yaml)
  - [5. Controller 核心逻辑](#5-controller-核心逻辑)
    - [5.1 Reconcile 函数](#51-reconcile-函数)
    - [5.2 Controller 启动](#52-controller-启动)
  - [6. OTLP 可观测性集成](#6-otlp-可观测性集成)
  - [7. 生产部署](#7-生产部署)
    - [7.1 RBAC 配置](#71-rbac-配置)
    - [7.2 Operator Deployment](#72-operator-deployment)
  - [8. 测试策略](#8-测试策略)
  - [总结](#总结)

## 1. Operator 模式理论

### 1.1 Kubernetes Operator 定义

**Operator = CRD (自定义资源) + Controller (控制循环)**:

```text
┌─────────────────────────────────────────────────────────┐
│              Kubernetes Operator 架构                   │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  用户 → kubectl apply -f myapp.yaml                     │
│           │                                             │
│           ▼                                             │
│  ┌──────────────────┐                                   │
│  │  API Server      │                                   │
│  │  (CRD: MyApp)    │                                   │
│  └──────────────────┘                                   │
│           │                                             │
│           ▼ (Watch Event)                               │
│  ┌──────────────────┐                                   │
│  │   Controller     │ ◄─────── Reconcile Loop           │
│  │   (Rust Operator)│                                   │
│  └──────────────────┘                                   │
│           │                                             │
│           ▼ (Create/Update/Delete)                      │
│  ┌──────────────────────────────────────┐               │
│  │  Kubernetes Resources                │               │
│  │  • Deployment                        │               │
│  │  • Service                           │               │
│  │  • ConfigMap                         │               │
│  └──────────────────────────────────────┘               │
└─────────────────────────────────────────────────────────┘
```

### 1.2 国际标准对标

| 标准 | 实现 | 文档 |
|------|------|------|
| **Kubernetes API Conventions** | kube-rs API 客户端 | [API Conventions](https://github.com/kubernetes/community/blob/master/contributors/devel/sig-architecture/api-conventions.md) |
| **Custom Resource Definition (CRD)** | `#[derive(CustomResource)]` | [CRD Spec](https://kubernetes.io/docs/tasks/extend-kubernetes/custom-resources/custom-resource-definitions/) |
| **Operator Pattern** | Controller + Reconcile Loop | [Operator Pattern](https://kubernetes.io/docs/concepts/extend-kubernetes/operator/) |
| **OpenTelemetry** | 完整 OTLP 集成 | [OTLP Spec](https://opentelemetry.io/docs/specs/otel/) |

---

## 2. kube-rs 生态系统

### 2.1 Cargo.toml

```toml
[package]
name = "myapp-operator"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Kubernetes 客户端核心
kube = { version = "0.95", features = ["runtime", "derive", "client", "ws"] }
k8s-openapi = { version = "0.23", features = ["v1_31"] }

# Controller Runtime
kube-runtime = "0.95"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde_yaml = "0.9"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"
opentelemetry = { version = "0.31", features = ["trace", "metrics"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

# Schema 验证
schemars = "0.8"
validator = { version = "0.18", features = ["derive"] }

[dev-dependencies]
tokio-test = "0.4"
```

### 2.2 kube-rs 核心模块

```rust
use kube::{
    Api,              // 资源 API 客户端
    Client,           // Kubernetes 集群连接
    CustomResource,   // CRD 定义宏
    ResourceExt,      // 资源扩展方法
};
use kube::runtime::{
    controller::{Controller, Action},  // Controller 运行时
    watcher,          // 资源监听器
    reflector,        // 本地缓存
};
use k8s_openapi::api::apps::v1::Deployment;  // 标准资源
```

---

## 3. 完整 Operator 实现

### 3.1 项目结构

```text
myapp-operator/
├── Cargo.toml
├── src/
│   ├── main.rs                    # 入口
│   ├── crd.rs                     # CRD 定义
│   ├── controller.rs              # Controller 逻辑
│   ├── reconciler.rs              # Reconcile 函数
│   ├── error.rs                   # 错误处理
│   └── telemetry.rs               # OTLP 集成
├── manifests/
│   ├── crd.yaml                   # CRD 清单
│   ├── rbac.yaml                  # RBAC 权限
│   └── deployment.yaml            # Operator 部署
└── tests/
    └── integration.rs
```

---

## 4. CRD 设计与注册

### 4.1 定义 CRD

```rust
// src/crd.rs
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use validator::Validate;

/// MyApp 自定义资源
#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema, Validate)]
#[kube(
    group = "example.com",
    version = "v1",
    kind = "MyApp",
    plural = "myapps",
    namespaced,
    status = "MyAppStatus",
    shortname = "ma",
    printcolumn = r#"{"name":"Ready", "type":"string", "jsonPath":".status.phase"}"#,
    printcolumn = r#"{"name":"Age", "type":"date", "jsonPath":".metadata.creationTimestamp"}"#
)]
#[serde(rename_all = "camelCase")]
pub struct MyAppSpec {
    /// 应用镜像
    #[validate(length(min = 1))]
    pub image: String,

    /// 副本数
    #[validate(range(min = 1, max = 100))]
    pub replicas: i32,

    /// 资源配置
    #[serde(default)]
    pub resources: ResourceRequirements,

    /// 环境变量
    #[serde(default)]
    pub env: Vec<EnvVar>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ResourceRequirements {
    pub cpu: String,
    pub memory: String,
}

impl Default for ResourceRequirements {
    fn default() -> Self {
        Self {
            cpu: "100m".to_string(),
            memory: "128Mi".to_string(),
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct EnvVar {
    pub name: String,
    pub value: String,
}

/// MyApp 状态
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MyAppStatus {
    pub phase: Phase,
    pub replicas: i32,
    pub ready_replicas: i32,
    pub last_update_time: Option<chrono::DateTime<chrono::Utc>>,
    pub message: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub enum Phase {
    Pending,
    Running,
    Failed,
}
```

### 4.2 生成 CRD YAML

```rust
// src/main.rs
use kube::CustomResourceExt;

fn generate_crd() -> anyhow::Result<()> {
    let crd = MyApp::crd();
    println!("{}", serde_yaml::to_string(&crd)?);
    Ok(())
}

// 运行: cargo run --bin gen-crd > manifests/crd.yaml
```

---

## 5. Controller 核心逻辑

### 5.1 Reconcile 函数

```rust
// src/reconciler.rs
use kube::{Api, Client, ResourceExt};
use kube::runtime::controller::Action;
use tracing::{info, warn, instrument};
use std::sync::Arc;
use std::time::Duration;

use crate::crd::{MyApp, MyAppStatus, Phase};
use crate::error::Error;

pub struct Context {
    pub client: Client,
}

#[instrument(skip(ctx), fields(name = %myapp.name_any(), namespace = %myapp.namespace().unwrap_or_default()))]
pub async fn reconcile(myapp: Arc<MyApp>, ctx: Arc<Context>) -> Result<Action, Error> {
    let client = ctx.client.clone();
    let name = myapp.name_any();
    let namespace = myapp.namespace().ok_or_else(|| Error::MissingNamespace)?;

    info!("Reconciling MyApp");

    // 1. 验证 Spec
    myapp.spec.validate()
        .map_err(|e| Error::Validation(e.to_string()))?;

    // 2. 确保 Deployment 存在
    let deployment_api: Api<k8s_openapi::api::apps::v1::Deployment> = 
        Api::namespaced(client.clone(), &namespace);

    let deployment = build_deployment(&myapp)?;

    match deployment_api.get(&name).await {
        Ok(existing) => {
            // 更新 Deployment
            info!("Updating existing Deployment");
            deployment_api.replace(&name, &Default::default(), &deployment).await?;
        }
        Err(_) => {
            // 创建 Deployment
            info!("Creating new Deployment");
            deployment_api.create(&Default::default(), &deployment).await?;
        }
    }

    // 3. 确保 Service 存在
    let service_api: Api<k8s_openapi::api::core::v1::Service> = 
        Api::namespaced(client.clone(), &namespace);

    let service = build_service(&myapp)?;

    if service_api.get(&name).await.is_err() {
        info!("Creating Service");
        service_api.create(&Default::default(), &service).await?;
    }

    // 4. 更新状态
    update_status(&client, &myapp, &namespace, &name).await?;

    // 5. 重新排队 (60秒后再次 reconcile)
    Ok(Action::requeue(Duration::from_secs(60)))
}

/// 构建 Deployment
fn build_deployment(myapp: &MyApp) -> Result<k8s_openapi::api::apps::v1::Deployment, Error> {
    use k8s_openapi::api::apps::v1::*;
    use k8s_openapi::api::core::v1::*;
    use k8s_openapi::apimachinery::pkg::apis::meta::v1::*;
    use std::collections::BTreeMap;

    let name = myapp.name_any();
    let spec = &myapp.spec;

    let labels: BTreeMap<String, String> = [
        ("app".to_string(), name.clone()),
        ("managed-by".to_string(), "myapp-operator".to_string()),
    ].into_iter().collect();

    Ok(Deployment {
        metadata: ObjectMeta {
            name: Some(name.clone()),
            labels: Some(labels.clone()),
            owner_references: Some(vec![myapp.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(DeploymentSpec {
            replicas: Some(spec.replicas),
            selector: LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: PodTemplateSpec {
                metadata: Some(ObjectMeta {
                    labels: Some(labels.clone()),
                    ..Default::default()
                }),
                spec: Some(PodSpec {
                    containers: vec![Container {
                        name: "app".to_string(),
                        image: Some(spec.image.clone()),
                        ports: Some(vec![ContainerPort {
                            container_port: 8080,
                            ..Default::default()
                        }]),
                        env: Some(spec.env.iter().map(|e| EnvVar {
                            name: e.name.clone(),
                            value: Some(e.value.clone()),
                            ..Default::default()
                        }).collect()),
                        resources: Some(ResourceRequirements {
                            requests: Some([
                                ("cpu".to_string(), k8s_openapi::apimachinery::pkg::api::resource::Quantity(spec.resources.cpu.clone())),
                                ("memory".to_string(), k8s_openapi::apimachinery::pkg::api::resource::Quantity(spec.resources.memory.clone())),
                            ].into_iter().collect()),
                            ..Default::default()
                        }),
                        ..Default::default()
                    }],
                    ..Default::default()
                }),
            },
            ..Default::default()
        }),
        ..Default::default()
    })
}

/// 构建 Service
fn build_service(myapp: &MyApp) -> Result<k8s_openapi::api::core::v1::Service, Error> {
    use k8s_openapi::api::core::v1::*;
    use k8s_openapi::apimachinery::pkg::apis::meta::v1::*;
    use std::collections::BTreeMap;

    let name = myapp.name_any();
    let labels: BTreeMap<String, String> = [
        ("app".to_string(), name.clone()),
    ].into_iter().collect();

    Ok(Service {
        metadata: ObjectMeta {
            name: Some(name.clone()),
            labels: Some(labels.clone()),
            owner_references: Some(vec![myapp.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(ServiceSpec {
            selector: Some(labels.clone()),
            ports: Some(vec![ServicePort {
                port: 80,
                target_port: Some(k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(8080)),
                ..Default::default()
            }]),
            type_: Some("ClusterIP".to_string()),
            ..Default::default()
        }),
        ..Default::default()
    })
}

/// 更新状态
async fn update_status(
    client: &Client,
    myapp: &MyApp,
    namespace: &str,
    name: &str,
) -> Result<(), Error> {
    let api: Api<MyApp> = Api::namespaced(client.clone(), namespace);

    // 获取 Deployment 状态
    let deployment_api: Api<k8s_openapi::api::apps::v1::Deployment> = 
        Api::namespaced(client.clone(), namespace);

    let deployment = deployment_api.get(name).await?;
    let deployment_status = deployment.status.unwrap_or_default();

    let status = MyAppStatus {
        phase: if deployment_status.ready_replicas == Some(myapp.spec.replicas) {
            Phase::Running
        } else {
            Phase::Pending
        },
        replicas: deployment_status.replicas.unwrap_or(0),
        ready_replicas: deployment_status.ready_replicas.unwrap_or(0),
        last_update_time: Some(chrono::Utc::now()),
        message: Some(format!("{}/{} replicas ready", 
            deployment_status.ready_replicas.unwrap_or(0),
            myapp.spec.replicas
        )),
    };

    let mut updated = myapp.as_ref().clone();
    updated.status = Some(status);

    api.replace_status(name, &Default::default(), serde_json::to_vec(&updated)?).await?;

    Ok(())
}

/// 错误处理
pub fn error_policy(_myapp: Arc<MyApp>, error: &Error, _ctx: Arc<Context>) -> Action {
    warn!("Reconcile error: {:?}", error);
    Action::requeue(Duration::from_secs(30))
}
```

### 5.2 Controller 启动

```rust
// src/controller.rs
use kube::Client;
use kube::runtime::{controller::Controller, watcher};
use std::sync::Arc;
use tracing::info;

use crate::crd::MyApp;
use crate::reconciler::{self, Context};

pub async fn run(client: Client) -> anyhow::Result<()> {
    info!("Starting MyApp Controller");

    let myapps = kube::Api::<MyApp>::all(client.clone());
    let context = Arc::new(Context { client });

    Controller::new(myapps, watcher::Config::default())
        .run(reconciler::reconcile, reconciler::error_policy, context)
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("Reconciled {:?}", o),
                Err(e) => warn!("Reconcile error: {:?}", e),
            }
        })
        .await;

    Ok(())
}
```

---

## 6. OTLP 可观测性集成

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{trace, Resource, runtime};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otel-collector:4317")
        )
        .with_trace_config(
            trace::config().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "myapp-operator"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info,myapp_operator=debug"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

---

## 7. 生产部署

### 7.1 RBAC 配置

```yaml
# manifests/rbac.yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: myapp-operator
  namespace: default
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: myapp-operator
rules:
- apiGroups: ["example.com"]
  resources: ["myapps", "myapps/status"]
  verbs: ["get", "list", "watch", "create", "update", "patch", "delete"]
- apiGroups: ["apps"]
  resources: ["deployments"]
  verbs: ["get", "list", "watch", "create", "update", "patch", "delete"]
- apiGroups: [""]
  resources: ["services"]
  verbs: ["get", "list", "watch", "create", "update", "patch", "delete"]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: myapp-operator
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: myapp-operator
subjects:
- kind: ServiceAccount
  name: myapp-operator
  namespace: default
```

### 7.2 Operator Deployment

```yaml
# manifests/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: myapp-operator
  namespace: default
spec:
  replicas: 1
  selector:
    matchLabels:
      app: myapp-operator
  template:
    metadata:
      labels:
        app: myapp-operator
    spec:
      serviceAccountName: myapp-operator
      containers:
      - name: operator
        image: myapp-operator:latest
        env:
        - name: RUST_LOG
          value: "info,myapp_operator=debug"
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        resources:
          requests:
            cpu: "100m"
            memory: "128Mi"
          limits:
            cpu: "500m"
            memory: "512Mi"
```

---

## 8. 测试策略

```rust
// tests/integration.rs
use kube::Client;

#[tokio::test]
async fn test_myapp_creation() -> anyhow::Result<()> {
    let client = Client::try_default().await?;
    let myapps: Api<MyApp> = Api::default_namespaced(client);

    let myapp = MyApp::new("test-app", MyAppSpec {
        image: "nginx:latest".to_string(),
        replicas: 2,
        resources: ResourceRequirements::default(),
        env: vec![],
    });

    let created = myapps.create(&Default::default(), &myapp).await?;
    assert_eq!(created.spec.replicas, 2);

    Ok(())
}
```

---

## 总结

✅ **完整 Operator 实现** (CRD + Controller + Reconcile Loop)  
✅ **深度 OTLP 集成** (分布式追踪)  
✅ **生产级部署** (RBAC + Deployment)  
✅ **国际标准对标** (K8s API Conventions)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
