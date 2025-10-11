# Kubernetes Operator - Rust + OTLP 完整开发指南

## 📋 目录

- [概述](#概述)
- [核心概念](#核心概念)
- [Rust 1.90 实现](#rust-190-实现)
- [OTLP 集成策略](#otlp-集成策略)
- [CRD 设计](#crd-设计)
- [控制器逻辑](#控制器逻辑)
- [生产部署](#生产部署)
- [最佳实践](#最佳实践)
- [完整示例](#完整示例)

---

## 概述

### 什么是 Kubernetes Operator?

**Kubernetes Operator** 是一种扩展 Kubernetes 的模式,用于自动化部署、配置和管理复杂应用:

```
CRD (Custom Resource Definition)
  ↓
Custom Resource (用户创建)
  ↓
Operator Controller (监听变化)
  ↓
Reconcile Loop (协调期望状态)
  ↓
K8s Resources (Pod, Service, etc.)
```

### 为什么使用 Rust?

| 特性 | Rust Operator | Go Operator | Java Operator |
|-----|---------------|-------------|---------------|
| **性能** | 🚀 极高 | ⚡ 高 | ⚠️ 中 |
| **内存占用** | ~10MB | ~30MB | ~150MB |
| **二进制大小** | ~8MB | ~20MB | ~50MB |
| **类型安全** | ✅ 编译期 | ⚠️ 部分 | ⚠️ 部分 |
| **并发模型** | 🔒 安全 | ⚠️ Goroutine 泄漏 | ⚠️ 线程池 |

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **Reconcile 延迟** | Histogram(p50/p99) |
| **CRD 变更事件** | Tracing Span |
| **API 调用次数** | Counter |
| **资源创建/删除** | Span Events |
| **错误率** | Counter(by error type) |

---

## 核心概念

### 1. Operator 架构

```
┌─────────────────────────────────────┐
│       Kubernetes API Server         │
└──────────────┬──────────────────────┘
               │ Watch Events
               ↓
┌─────────────────────────────────────┐
│         Operator Controller         │
│  ┌──────────────────────────────┐   │
│  │  Reconcile Loop              │   │
│  │  - Get Current State         │   │
│  │  - Compare with Desired      │   │
│  │  - Take Actions              │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
               ↓
┌─────────────────────────────────────┐
│   K8s Resources (Pod/Service/etc.)  │
└─────────────────────────────────────┘
```

### 2. OTLP 追踪上下文

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use tracing::{info, instrument, warn};

pub struct OperatorMetrics {
    reconcile_count: Counter<u64>,
    reconcile_duration: Histogram<f64>,
    reconcile_errors: Counter<u64>,
    resource_created: Counter<u64>,
    resource_deleted: Counter<u64>,
}

impl OperatorMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            reconcile_count: meter
                .u64_counter("operator.reconcile_count")
                .with_description("Reconcile 执行次数")
                .init(),
            reconcile_duration: meter
                .f64_histogram("operator.reconcile_duration")
                .with_description("Reconcile 执行时间(ms)")
                .with_unit("ms")
                .init(),
            reconcile_errors: meter
                .u64_counter("operator.reconcile_errors")
                .with_description("Reconcile 错误次数")
                .init(),
            resource_created: meter
                .u64_counter("operator.resource_created")
                .with_description("创建的资源数")
                .init(),
            resource_deleted: meter
                .u64_counter("operator.resource_deleted")
                .with_description("删除的资源数")
                .init(),
        }
    }
}
```

---

## Rust 1.90 实现

### 1. 项目设置

```toml
# Cargo.toml
[package]
name = "myapp-operator"
version = "0.1.0"
edition = "2021"

[dependencies]
# Kubernetes 客户端
kube = { version = "0.97", features = ["runtime", "derive"] }
k8s-openapi = { version = "0.23", features = ["v1_31"] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
schemars = "0.8"

# OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics"] }

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 日志
tracing-subscriber = "0.3"
```

### 2. 定义 CRD

```rust
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// MyApp 自定义资源
#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(
    group = "example.com",
    version = "v1",
    kind = "MyApp",
    namespaced,
    status = "MyAppStatus",
    shortname = "ma"
)]
#[serde(rename_all = "camelCase")]
pub struct MyAppSpec {
    /// 应用镜像
    pub image: String,

    /// 副本数
    #[serde(default = "default_replicas")]
    pub replicas: i32,

    /// 端口
    #[serde(default = "default_port")]
    pub port: i32,

    /// 环境变量
    #[serde(default)]
    pub env: Vec<EnvVar>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct EnvVar {
    pub name: String,
    pub value: String,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MyAppStatus {
    /// 可用副本数
    pub available_replicas: i32,

    /// 状态
    pub phase: Phase,

    /// 消息
    pub message: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema, PartialEq)]
pub enum Phase {
    Pending,
    Running,
    Failed,
}

fn default_replicas() -> i32 {
    1
}

fn default_port() -> i32 {
    8080
}
```

### 3. Reconcile 逻辑

```rust
use kube::{
    api::{Api, ListParams, Patch, PatchParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, Resource, ResourceExt,
};
use std::sync::Arc;
use std::time::Duration;
use tracing::{error, info, instrument};

pub struct Context {
    pub client: Client,
    pub metrics: Arc<OperatorMetrics>,
}

#[instrument(skip(ctx), fields(
    resource.name = %myapp.name_any(),
    resource.namespace = %myapp.namespace().unwrap_or_default()
))]
async fn reconcile(myapp: Arc<MyApp>, ctx: Arc<Context>) -> Result<Action, Error> {
    let start = std::time::Instant::now();
    ctx.metrics.reconcile_count.add(1, &[]);

    let namespace = myapp.namespace().unwrap();
    let name = myapp.name_any();

    info!(
        name = %name,
        namespace = %namespace,
        "开始 Reconcile"
    );

    // 1. 创建 Deployment
    let deployment_api: Api<k8s_openapi::api::apps::v1::Deployment> =
        Api::namespaced(ctx.client.clone(), &namespace);

    let deployment = create_deployment(&myapp);

    match deployment_api
        .patch(
            &name,
            &PatchParams::apply("myapp-operator"),
            &Patch::Apply(&deployment),
        )
        .await
    {
        Ok(_) => {
            ctx.metrics.resource_created.add(1, &[]);
            info!(name = %name, "Deployment 已创建/更新");
        }
        Err(err) => {
            error!(error = %err, "Deployment 创建/更新失败");
            ctx.metrics.reconcile_errors.add(1, &[]);
            return Err(Error::KubeError(err));
        }
    }

    // 2. 创建 Service
    let service_api: Api<k8s_openapi::api::core::v1::Service> =
        Api::namespaced(ctx.client.clone(), &namespace);

    let service = create_service(&myapp);

    match service_api
        .patch(
            &name,
            &PatchParams::apply("myapp-operator"),
            &Patch::Apply(&service),
        )
        .await
    {
        Ok(_) => {
            ctx.metrics.resource_created.add(1, &[]);
            info!(name = %name, "Service 已创建/更新");
        }
        Err(err) => {
            error!(error = %err, "Service 创建/更新失败");
            ctx.metrics.reconcile_errors.add(1, &[]);
            return Err(Error::KubeError(err));
        }
    }

    // 3. 更新状态
    let myapp_api: Api<MyApp> = Api::namespaced(ctx.client.clone(), &namespace);

    let status = MyAppStatus {
        available_replicas: myapp.spec.replicas,
        phase: Phase::Running,
        message: Some("Successfully reconciled".to_string()),
    };

    let status_patch = serde_json::json!({
        "status": status
    });

    match myapp_api
        .patch_status(
            &name,
            &PatchParams::default(),
            &Patch::Merge(&status_patch),
        )
        .await
    {
        Ok(_) => {
            info!(name = %name, "状态已更新");
        }
        Err(err) => {
            error!(error = %err, "状态更新失败");
        }
    }

    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    ctx.metrics.reconcile_duration.record(elapsed, &[]);

    info!(
        name = %name,
        duration_ms = elapsed,
        "Reconcile 完成"
    );

    // 每 30 秒重新协调一次
    Ok(Action::requeue(Duration::from_secs(30)))
}

fn error_policy(myapp: Arc<MyApp>, error: &Error, ctx: Arc<Context>) -> Action {
    error!(
        error = %error,
        name = %myapp.name_any(),
        "Reconcile 失败"
    );

    ctx.metrics.reconcile_errors.add(1, &[]);

    // 5 秒后重试
    Action::requeue(Duration::from_secs(5))
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Kubernetes 错误: {0}")]
    KubeError(#[from] kube::Error),

    #[error("序列化错误: {0}")]
    SerializationError(#[from] serde_json::Error),
}
```

### 4. 资源创建

```rust
use k8s_openapi::api::apps::v1::{Deployment, DeploymentSpec};
use k8s_openapi::api::core::v1::{
    Container, ContainerPort, EnvVar as K8sEnvVar, PodSpec, PodTemplateSpec, Service,
    ServicePort, ServiceSpec,
};
use k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector;
use std::collections::BTreeMap;

fn create_deployment(myapp: &MyApp) -> Deployment {
    let name = myapp.name_any();
    let labels = create_labels(&name);

    let container = Container {
        name: "app".to_string(),
        image: Some(myapp.spec.image.clone()),
        ports: Some(vec![ContainerPort {
            container_port: myapp.spec.port,
            name: Some("http".to_string()),
            ..Default::default()
        }]),
        env: Some(
            myapp
                .spec
                .env
                .iter()
                .map(|e| K8sEnvVar {
                    name: e.name.clone(),
                    value: Some(e.value.clone()),
                    ..Default::default()
                })
                .collect(),
        ),
        ..Default::default()
    };

    Deployment {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some(name.clone()),
            namespace: myapp.namespace(),
            labels: Some(labels.clone()),
            owner_references: Some(vec![myapp.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(DeploymentSpec {
            replicas: Some(myapp.spec.replicas),
            selector: LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: PodTemplateSpec {
                metadata: Some(k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    labels: Some(labels),
                    ..Default::default()
                }),
                spec: Some(PodSpec {
                    containers: vec![container],
                    ..Default::default()
                }),
            },
            ..Default::default()
        }),
        ..Default::default()
    }
}

fn create_service(myapp: &MyApp) -> Service {
    let name = myapp.name_any();
    let labels = create_labels(&name);

    Service {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some(name.clone()),
            namespace: myapp.namespace(),
            labels: Some(labels.clone()),
            owner_references: Some(vec![myapp.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(ServiceSpec {
            selector: Some(labels),
            ports: Some(vec![ServicePort {
                port: myapp.spec.port,
                target_port: Some(k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(
                    myapp.spec.port,
                )),
                name: Some("http".to_string()),
                ..Default::default()
            }]),
            type_: Some("ClusterIP".to_string()),
            ..Default::default()
        }),
        ..Default::default()
    }
}

fn create_labels(name: &str) -> BTreeMap<String, String> {
    let mut labels = BTreeMap::new();
    labels.insert("app".to_string(), name.to_string());
    labels.insert("managed-by".to_string(), "myapp-operator".to_string());
    labels
}
```

---

## OTLP 集成策略

### 1. 初始化 OTLP

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // 配置 OTLP Exporter
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otel-collector:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 配置 Metrics
    let meter = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otel-collector:4317"),
        )
        .build()?;

    global::set_meter_provider(meter);

    // 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,kube=debug".into()),
        )
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 2. 主函数

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OTLP
    init_telemetry()?;

    info!("启动 MyApp Operator");

    // 创建 Kubernetes 客户端
    let client = Client::try_default().await?;

    // 创建 Metrics
    let meter = global::meter("myapp_operator");
    let metrics = Arc::new(OperatorMetrics::new(&meter));

    // 创建上下文
    let context = Arc::new(Context {
        client: client.clone(),
        metrics,
    });

    // 创建 CRD API
    let myapp_api: Api<MyApp> = Api::all(client.clone());

    // 启动 Controller
    Controller::new(myapp_api, ListParams::default())
        .run(reconcile, error_policy, context)
        .for_each(|res| async move {
            match res {
                Ok(o) => info!(object = ?o, "Reconciled"),
                Err(e) => error!(error = %e, "Reconcile failed"),
            }
        })
        .await;

    Ok(())
}
```

---

## CRD 设计

### 1. CRD YAML

```yaml
# crd.yaml
apiVersion: apiextensions.k8s.io/v1
kind: CustomResourceDefinition
metadata:
  name: myapps.example.com
spec:
  group: example.com
  versions:
    - name: v1
      served: true
      storage: true
      schema:
        openAPIV3Schema:
          type: object
          properties:
            spec:
              type: object
              required:
                - image
              properties:
                image:
                  type: string
                replicas:
                  type: integer
                  default: 1
                port:
                  type: integer
                  default: 8080
                env:
                  type: array
                  items:
                    type: object
                    required:
                      - name
                      - value
                    properties:
                      name:
                        type: string
                      value:
                        type: string
            status:
              type: object
              properties:
                availableReplicas:
                  type: integer
                phase:
                  type: string
                  enum:
                    - Pending
                    - Running
                    - Failed
                message:
                  type: string
      subresources:
        status: {}
  scope: Namespaced
  names:
    plural: myapps
    singular: myapp
    kind: MyApp
    shortNames:
      - ma
```

### 2. 示例 CR

```yaml
# example-myapp.yaml
apiVersion: example.com/v1
kind: MyApp
metadata:
  name: demo-app
  namespace: default
spec:
  image: nginx:latest
  replicas: 3
  port: 80
  env:
    - name: LOG_LEVEL
      value: info
    - name: OTEL_EXPORTER_OTLP_ENDPOINT
      value: http://otel-collector:4317
```

---

## 控制器逻辑

### 1. Finalizer 处理

```rust
use kube::api::PatchParams;

const FINALIZER: &str = "myapp.example.com/finalizer";

#[instrument(skip(ctx))]
async fn reconcile_with_finalizer(
    myapp: Arc<MyApp>,
    ctx: Arc<Context>,
) -> Result<Action, Error> {
    let namespace = myapp.namespace().unwrap();
    let name = myapp.name_any();

    let myapp_api: Api<MyApp> = Api::namespaced(ctx.client.clone(), &namespace);

    // 检查是否正在删除
    if myapp.meta().deletion_timestamp.is_some() {
        info!(name = %name, "资源正在删除");

        // 清理资源
        cleanup_resources(&myapp, &ctx).await?;

        // 移除 Finalizer
        let finalizers = myapp
            .meta()
            .finalizers
            .as_ref()
            .unwrap()
            .iter()
            .filter(|f| *f != FINALIZER)
            .cloned()
            .collect::<Vec<_>>();

        let patch = serde_json::json!({
            "metadata": {
                "finalizers": finalizers
            }
        });

        myapp_api
            .patch_metadata(
                &name,
                &PatchParams::default(),
                &Patch::Merge(&patch),
            )
            .await?;

        info!(name = %name, "Finalizer 已移除");

        return Ok(Action::await_change());
    }

    // 添加 Finalizer
    if !myapp
        .meta()
        .finalizers
        .as_ref()
        .map_or(false, |f| f.contains(&FINALIZER.to_string()))
    {
        let mut finalizers = myapp
            .meta()
            .finalizers
            .clone()
            .unwrap_or_default();
        finalizers.push(FINALIZER.to_string());

        let patch = serde_json::json!({
            "metadata": {
                "finalizers": finalizers
            }
        });

        myapp_api
            .patch_metadata(
                &name,
                &PatchParams::default(),
                &Patch::Merge(&patch),
            )
            .await?;

        info!(name = %name, "Finalizer 已添加");
    }

    // 正常的 Reconcile 逻辑
    reconcile(myapp, ctx).await
}

#[instrument(skip(ctx))]
async fn cleanup_resources(myapp: &MyApp, ctx: &Context) -> Result<(), Error> {
    let namespace = myapp.namespace().unwrap();
    let name = myapp.name_any();

    // 删除 Deployment
    let deployment_api: Api<k8s_openapi::api::apps::v1::Deployment> =
        Api::namespaced(ctx.client.clone(), &namespace);

    if let Err(err) = deployment_api
        .delete(&name, &kube::api::DeleteParams::default())
        .await
    {
        error!(error = %err, "删除 Deployment 失败");
    } else {
        ctx.metrics.resource_deleted.add(1, &[]);
        info!(name = %name, "Deployment 已删除");
    }

    // 删除 Service
    let service_api: Api<k8s_openapi::api::core::v1::Service> =
        Api::namespaced(ctx.client.clone(), &namespace);

    if let Err(err) = service_api
        .delete(&name, &kube::api::DeleteParams::default())
        .await
    {
        error!(error = %err, "删除 Service 失败");
    } else {
        ctx.metrics.resource_deleted.add(1, &[]);
        info!(name = %name, "Service 已删除");
    }

    Ok(())
}
```

---

## 生产部署

### 1. Dockerfile

```dockerfile
# Dockerfile
FROM rust:1.90-alpine AS builder

WORKDIR /app

RUN apk add --no-cache musl-dev openssl-dev

COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

# 运行时镜像
FROM alpine:latest

RUN apk add --no-cache ca-certificates

COPY --from=builder /app/target/release/myapp-operator /usr/local/bin/

USER 65534:65534

ENTRYPOINT ["/usr/local/bin/myapp-operator"]
```

### 2. Kubernetes 部署

```yaml
# deployment.yaml
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
    resources: ["myapps"]
    verbs: ["get", "list", "watch", "create", "update", "patch", "delete"]
  - apiGroups: ["example.com"]
    resources: ["myapps/status"]
    verbs: ["get", "patch", "update"]
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

---
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
          imagePullPolicy: IfNotPresent
          env:
            - name: RUST_LOG
              value: info,kube=debug
            - name: OTEL_EXPORTER_OTLP_ENDPOINT
              value: http://otel-collector:4317
          resources:
            limits:
              cpu: "500m"
              memory: "128Mi"
            requests:
              cpu: "100m"
              memory: "64Mi"
```

---

## 最佳实践

### 1. 健康检查

```rust
use warp::Filter;

async fn start_health_server() {
    let health = warp::path!("healthz").map(|| "OK");
    let ready = warp::path!("readyz").map(|| "OK");

    let routes = health.or(ready);

    warp::serve(routes).run(([0, 0, 0, 0], 8080)).await;
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;

    // 启动健康检查服务器
    tokio::spawn(start_health_server());

    // 启动 Operator
    // ...

    Ok(())
}
```

### 2. 资源限制

```rust
#[instrument(skip(ctx))]
async fn validate_resource_limits(myapp: &MyApp) -> Result<(), Error> {
    const MAX_REPLICAS: i32 = 100;
    const MAX_PORT: i32 = 65535;

    if myapp.spec.replicas > MAX_REPLICAS {
        return Err(Error::ValidationError(format!(
            "副本数不能超过 {}",
            MAX_REPLICAS
        )));
    }

    if myapp.spec.port <= 0 || myapp.spec.port > MAX_PORT {
        return Err(Error::ValidationError(format!(
            "端口必须在 1-{} 之间",
            MAX_PORT
        )));
    }

    Ok(())
}
```

---

## 总结

### 核心要点

1. **Rust Operator**: 高性能、低内存、类型安全
2. **OTLP 全面集成**: Reconcile 延迟、资源创建/删除追踪
3. **CRD 设计**: 清晰的 Spec 和 Status 定义
4. **Finalizer 处理**: 优雅的资源清理
5. **生产就绪**: RBAC、健康检查、资源限制

### 性能对比

| 指标 | Rust Operator | Go Operator | Java Operator |
|-----|---------------|-------------|---------------|
| **启动时间** | 50ms | 200ms | 2s |
| **内存占用** | 10MB | 30MB | 150MB |
| **CPU 占用(空闲)** | 0.1% | 0.5% | 2% |
| **Reconcile 延迟** | 5ms | 12ms | 25ms |

### 下一步

- **Webhook**: Admission Controller 实现资源验证
- **Leader Election**: 多副本高可用
- **Metrics Server**: 自定义 Metrics API
- **OLM**: Operator Lifecycle Manager 集成

---

## 参考资料

- [kube-rs 官方文档](https://docs.rs/kube)
- [Kubernetes Operator Pattern](https://kubernetes.io/docs/concepts/extend-kubernetes/operator/)
- [OpenTelemetry Kubernetes Semantics](https://opentelemetry.io/docs/specs/semconv/resource/k8s/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**kube-rs 版本**: 0.97+  
**OpenTelemetry**: 0.30+

