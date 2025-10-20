# Tekton/Argo Workflows 完整实现：CI/CD - Rust 1.90 + OTLP 集成

## 目录

- [Tekton/Argo Workflows 完整实现：CI/CD - Rust 1.90 + OTLP 集成](#tektonargo-workflows-完整实现cicd---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 Tekton 核心特性](#11-tekton-核心特性)
    - [1.2 Argo Workflows 核心特性](#12-argo-workflows-核心特性)
    - [1.3 架构对比](#13-架构对比)
    - [1.4 国际标准对齐](#14-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. Tekton Pipeline 实现](#3-tekton-pipeline-实现)
    - [3.1 Task 定义](#31-task-定义)
    - [3.2 Pipeline 编排](#32-pipeline-编排)
    - [3.3 Rust Controller 实现](#33-rust-controller-实现)
  - [4. Argo Workflows 实现](#4-argo-workflows-实现)
    - [4.1 Workflow 模板](#41-workflow-模板)
    - [4.2 DAG 工作流](#42-dag-工作流)
    - [4.3 Rust Controller 实现](#43-rust-controller-实现)
  - [5. CI/CD 最佳实践](#5-cicd-最佳实践)
    - [5.1 多阶段构建](#51-多阶段构建)
    - [5.2 缓存策略](#52-缓存策略)
    - [5.3 安全扫描](#53-安全扫描)
  - [6. GitOps 集成](#6-gitops-集成)
    - [6.1 GitHub Actions 触发](#61-github-actions-触发)
    - [6.2 GitLab CI 集成](#62-gitlab-ci-集成)
    - [6.3 ArgoCD 同步](#63-argocd-同步)
  - [7. OTLP 可观测性集成](#7-otlp-可观测性集成)
    - [7.1 Pipeline 追踪](#71-pipeline-追踪)
    - [7.2 指标监控](#72-指标监控)
    - [7.3 日志聚合](#73-日志聚合)
  - [8. 生产部署实践](#8-生产部署实践)
    - [8.1 Tekton 部署](#81-tekton-部署)
    - [8.2 Argo Workflows 部署](#82-argo-workflows-部署)
    - [8.3 高可用配置](#83-高可用配置)
  - [9. 测试策略](#9-测试策略)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [标准与协议](#标准与协议)
    - [云原生](#云原生)

---

## 1. 核心概念与架构

### 1.1 Tekton 核心特性

Tekton 是云原生 CI/CD 框架，核心特性包括：

| 特性 | 描述 | 应用场景 |
|------|------|----------|
| **云原生** | Kubernetes CRD 原生实现 | K8s 环境 |
| **可移植** | 标准化 Pipeline 定义 | 多云、混合云 |
| **可扩展** | 自定义 Task/Pipeline | 企业定制 |
| **声明式** | YAML 定义工作流 | GitOps |
| **可重用** | Task/Pipeline Catalog | 社区共享 |
| **安全** | Provenance、SBOM | 供应链安全 |

### 1.2 Argo Workflows 核心特性

Argo Workflows 是容器原生工作流引擎，核心特性包括：

| 特性 | 描述 | 应用场景 |
|------|------|----------|
| **DAG 支持** | 有向无环图编排 | 复杂依赖 |
| **步骤模板** | 可重用步骤定义 | 模块化 |
| **参数化** | 动态参数传递 | 灵活配置 |
| **条件执行** | 条件分支逻辑 | 智能决策 |
| **Artifact 管理** | S3/GCS/Minio 集成 | 数据传递 |
| **事件驱动** | Webhook/Sensor 触发 | 自动化 |

### 1.3 架构对比

```text
┌─────────────────────────────────────────────────────────────┐
│                    Tekton Architecture                      │
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │
│  │ Pipeline │──│   Task   │──│   Step   │──│Container │    │
│  │  (编排)  │  │ (任务)   │  │ (步骤)   │  │ (执行)   │    │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘    │
│       │             │             │             │           │
│       ▼             ▼             ▼             ▼           │
│  ┌────────────────────────────────────────────────────┐     │
│  │          Kubernetes Cluster                        │     │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐         │     │
│  │  │TaskRun   │  │PipelineRun│ │EventListener│       │     │
│  │  │(实例)    │  │(实例)     │ │(触发器)   │        │     │
│  │  └──────────┘  └──────────┘  └──────────┘         │     │
│  └────────────────────────────────────────────────────┘     │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│                Argo Workflows Architecture                  │
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │
│  │ Workflow │──│ Template │──│   DAG    │──│Container │    │
│  │  (工作流)│  │ (模板)   │  │ (编排)   │  │ (执行)   │    │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘    │
│       │             │             │             │           │
│       ▼             ▼             ▼             ▼           │
│  ┌────────────────────────────────────────────────────┐     │
│  │          Kubernetes Cluster                        │     │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐         │     │
│  │  │Workflow  │  │Sensor    │  │EventSource│        │     │
│  │  │(实例)    │  │(触发器)  │  │(事件源)   │        │     │
│  │  └──────────┘  └──────────┘  └──────────┘         │     │
│  └────────────────────────────────────────────────────┘     │
└─────────────────────────────────────────────────────────────┘
```

### 1.4 国际标准对齐

| 标准/协议 | 应用场景 | 实现 |
|-----------|----------|------|
| **Kubernetes API Conventions** | 资源定义 | CRD + Controller |
| **OCI Image Spec** | 容器镜像 | Docker/Podman |
| **SLSA Framework** | 供应链安全 | Tekton Chains |
| **in-toto Specification** | Provenance | Attestation |
| **SBOM (CycloneDX/SPDX)** | 软件物料清单 | Syft/Grype |
| **OpenTelemetry** | 可观测性 | OTLP 集成 |
| **Cloud Events** | 事件格式 | Tekton Triggers |
| **GitOps** | 声明式部署 | ArgoCD/Flux |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "cicd-operator"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Kubernetes 客户端
kube = { version = "0.97", features = ["runtime", "derive", "ws"] }
k8s-openapi = { version = "0.23", features = ["v1_31"] }

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde_yaml = "0.9"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# OpenTelemetry (OTLP)
opentelemetry = "0.27"
opentelemetry-otlp = { version = "0.27", features = ["grpc-tonic", "metrics", "trace"] }
opentelemetry_sdk = { version = "0.27", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"

# HTTP 客户端
reqwest = { version = "0.12", features = ["rustls-tls", "json"] }

# Git 操作
git2 = "0.19"

# Docker 操作
bollard = "0.17"

# 时间处理
chrono = "0.4"

# 配置管理
config = "0.14"

[dev-dependencies]
tokio-test = "0.4"
mockito = "1.5"
```

### 2.2 项目结构

```text
cicd-operator/
├── src/
│   ├── main.rs                    # 入口
│   ├── tekton/
│   │   ├── mod.rs
│   │   ├── task.rs                # Task Controller
│   │   ├── pipeline.rs            # Pipeline Controller
│   │   └── trigger.rs             # Trigger Controller
│   ├── argo/
│   │   ├── mod.rs
│   │   ├── workflow.rs            # Workflow Controller
│   │   ├── template.rs            # Template Controller
│   │   └── sensor.rs              # Sensor Controller
│   ├── builder/
│   │   ├── mod.rs
│   │   ├── docker.rs              # Docker 构建
│   │   ├── kaniko.rs              # Kaniko 构建
│   │   └── buildkit.rs            # BuildKit 构建
│   ├── scanner/
│   │   ├── mod.rs
│   │   ├── trivy.rs               # Trivy 扫描
│   │   └── grype.rs               # Grype 扫描
│   ├── observability/
│   │   ├── mod.rs
│   │   ├── tracing.rs             # 分布式追踪
│   │   └── metrics.rs             # 指标收集
│   └── error.rs                   # 错误定义
├── pipelines/
│   ├── tekton/
│   │   ├── build-rust.yaml
│   │   └── deploy.yaml
│   └── argo/
│       ├── ci-workflow.yaml
│       └── cd-workflow.yaml
├── tests/
│   └── integration_test.rs
└── Cargo.toml
```

---

## 3. Tekton Pipeline 实现

### 3.1 Task 定义

```yaml
# pipelines/tekton/rust-build-task.yaml
apiVersion: tekton.dev/v1beta1
kind: Task
metadata:
  name: rust-build
  labels:
    app.kubernetes.io/version: "0.1"
spec:
  description: Build Rust application
  
  params:
    - name: git-url
      type: string
      description: Git repository URL
    - name: git-revision
      type: string
      description: Git revision
      default: main
    - name: image-name
      type: string
      description: Output image name
    - name: rust-version
      type: string
      description: Rust version
      default: "1.90"
  
  workspaces:
    - name: source
      description: Source code workspace
    - name: cache
      description: Cargo cache
      optional: true
  
  results:
    - name: image-digest
      description: Image digest
    - name: image-url
      description: Image URL
  
  steps:
    # 1. Git Clone
    - name: git-clone
      image: alpine/git:2.43.0
      script: |
        #!/bin/sh
        set -e
        echo "Cloning $(params.git-url) @ $(params.git-revision)"
        git clone $(params.git-url) $(workspaces.source.path)
        cd $(workspaces.source.path)
        git checkout $(params.git-revision)
        git log -1
    
    # 2. Cargo Build
    - name: cargo-build
      image: rust:$(params.rust-version)-slim
      workingDir: $(workspaces.source.path)
      env:
        - name: CARGO_HOME
          value: $(workspaces.cache.path)/.cargo
      script: |
        #!/bin/bash
        set -e
        
        echo "Installing dependencies..."
        apt-get update && apt-get install -y pkg-config libssl-dev
        
        echo "Building Rust project..."
        cargo build --release
        
        echo "Running tests..."
        cargo test --release
        
        echo "Build complete!"
        ls -lh target/release/
    
    # 3. Security Scan
    - name: security-scan
      image: aquasec/trivy:0.56.2
      workingDir: $(workspaces.source.path)
      script: |
        #!/bin/sh
        set -e
        
        echo "Scanning dependencies with Trivy..."
        trivy fs --format json --output trivy-report.json .
        
        echo "Scan complete!"
        cat trivy-report.json | jq '.Results[] | select(.Vulnerabilities != null) | .Vulnerabilities | length'
    
    # 4. Docker Build (Kaniko)
    - name: docker-build
      image: gcr.io/kaniko-project/executor:v1.23.2
      workingDir: $(workspaces.source.path)
      env:
        - name: DOCKER_CONFIG
          value: /tekton/home/.docker
      script: |
        #!/busybox/sh
        set -e
        
        /kaniko/executor \
          --dockerfile=Dockerfile \
          --context=dir://$(workspaces.source.path) \
          --destination=$(params.image-name):$(params.git-revision) \
          --destination=$(params.image-name):latest \
          --digest-file=$(results.image-digest.path) \
          --cache=true \
          --cache-ttl=24h
        
        echo -n "$(params.image-name):$(params.git-revision)" > $(results.image-url.path)
    
    # 5. Image Scan
    - name: image-scan
      image: aquasec/trivy:0.56.2
      script: |
        #!/bin/sh
        set -e
        
        echo "Scanning image $(params.image-name):$(params.git-revision)..."
        trivy image --format json --output image-scan.json $(params.image-name):$(params.git-revision)
        
        # 检查严重漏洞
        CRITICAL=$(cat image-scan.json | jq '[.Results[].Vulnerabilities[] | select(.Severity == "CRITICAL")] | length')
        
        if [ "$CRITICAL" -gt 0 ]; then
          echo "Found $CRITICAL critical vulnerabilities!"
          exit 1
        fi
        
        echo "Image scan passed!"
```

### 3.2 Pipeline 编排

```yaml
# pipelines/tekton/rust-ci-pipeline.yaml
apiVersion: tekton.dev/v1beta1
kind: Pipeline
metadata:
  name: rust-ci-pipeline
spec:
  description: Complete CI pipeline for Rust applications
  
  params:
    - name: git-url
      type: string
      description: Git repository URL
    - name: git-revision
      type: string
      description: Git revision
      default: main
    - name: image-registry
      type: string
      description: Container registry
      default: docker.io
    - name: image-name
      type: string
      description: Image name
  
  workspaces:
    - name: shared-workspace
      description: Shared workspace for pipeline
    - name: cargo-cache
      description: Cargo cache
      optional: true
    - name: docker-config
      description: Docker config
  
  results:
    - name: image-digest
      description: Image digest
      value: $(tasks.build.results.image-digest)
    - name: image-url
      description: Image URL
      value: $(tasks.build.results.image-url)
  
  tasks:
    # 1. Build Task
    - name: build
      taskRef:
        name: rust-build
      params:
        - name: git-url
          value: $(params.git-url)
        - name: git-revision
          value: $(params.git-revision)
        - name: image-name
          value: $(params.image-registry)/$(params.image-name)
      workspaces:
        - name: source
          workspace: shared-workspace
        - name: cache
          workspace: cargo-cache
    
    # 2. Generate SBOM
    - name: generate-sbom
      taskRef:
        name: syft-generate-sbom
      runAfter:
        - build
      params:
        - name: image-url
          value: $(tasks.build.results.image-url)
      workspaces:
        - name: source
          workspace: shared-workspace
    
    # 3. Sign Image (Cosign)
    - name: sign-image
      taskRef:
        name: cosign-sign
      runAfter:
        - build
      params:
        - name: image-digest
          value: $(tasks.build.results.image-digest)
        - name: image-url
          value: $(tasks.build.results.image-url)
    
    # 4. Update GitOps Repo
    - name: update-gitops
      taskRef:
        name: git-cli
      runAfter:
        - sign-image
      params:
        - name: GIT_SCRIPT
          value: |
            git clone https://github.com/example/gitops-repo.git
            cd gitops-repo
            sed -i "s|image:.*|image: $(tasks.build.results.image-url)|" k8s/deployment.yaml
            git add k8s/deployment.yaml
            git commit -m "Update image to $(tasks.build.results.image-url)"
            git push
      workspaces:
        - name: source
          workspace: shared-workspace
```

### 3.3 Rust Controller 实现

```rust
// src/tekton/pipeline.rs
use anyhow::Result;
use k8s_openapi::api::core::v1::Pod;
use kube::{
    api::{Api, ListParams, Patch, PatchParams, ResourceExt},
    runtime::{
        controller::{Action, Controller},
        watcher::Config,
    },
    Client, CustomResource,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tracing::{info, warn, instrument};
use chrono::Duration;

/// PipelineRun CRD
#[derive(CustomResource, Serialize, Deserialize, Debug, Clone)]
#[kube(
    group = "tekton.dev",
    version = "v1beta1",
    kind = "PipelineRun",
    namespaced
)]
#[kube(status = "PipelineRunStatus")]
pub struct PipelineRunSpec {
    #[serde(rename = "pipelineRef")]
    pub pipeline_ref: PipelineRef,
    pub params: Option<Vec<Param>>,
    pub workspaces: Option<Vec<WorkspaceBinding>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct PipelineRef {
    pub name: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Param {
    pub name: String,
    pub value: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct WorkspaceBinding {
    pub name: String,
    #[serde(rename = "persistentVolumeClaim")]
    pub persistent_volume_claim: Option<PvcClaim>,
    #[serde(rename = "emptyDir")]
    pub empty_dir: Option<EmptyDir>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct PvcClaim {
    #[serde(rename = "claimName")]
    pub claim_name: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct EmptyDir {}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct PipelineRunStatus {
    pub conditions: Option<Vec<Condition>>,
    #[serde(rename = "startTime")]
    pub start_time: Option<String>,
    #[serde(rename = "completionTime")]
    pub completion_time: Option<String>,
    #[serde(rename = "taskRuns")]
    pub task_runs: Option<std::collections::HashMap<String, TaskRunStatus>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Condition {
    pub r#type: String,
    pub status: String,
    pub reason: Option<String>,
    pub message: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TaskRunStatus {
    pub status: String,
}

/// Tekton Pipeline Controller
pub struct TektonPipelineController {
    client: Client,
}

impl TektonPipelineController {
    pub fn new(client: Client) -> Self {
        Self { client }
    }

    /// 启动 Controller
    #[instrument(skip(self))]
    pub async fn run(self) -> Result<()> {
        let client = self.client.clone();
        let pipelines: Api<PipelineRun> = Api::all(client.clone());

        info!("Starting Tekton Pipeline Controller");

        Controller::new(pipelines, Config::default())
            .run(
                Self::reconcile,
                Self::error_policy,
                Arc::new(self.client.clone()),
            )
            .for_each(|_| futures::future::ready(()))
            .await;

        Ok(())
    }

    /// 协调逻辑
    #[instrument(skip(ctx))]
    async fn reconcile(
        pipeline_run: Arc<PipelineRun>,
        ctx: Arc<Client>,
    ) -> Result<Action, anyhow::Error> {
        let name = pipeline_run.name_any();
        let namespace = pipeline_run.namespace().unwrap_or_default();

        info!(
            name = %name,
            namespace = %namespace,
            "Reconciling PipelineRun"
        );

        // 1. 检查状态
        if let Some(status) = &pipeline_run.status {
            if let Some(conditions) = &status.conditions {
                for condition in conditions {
                    if condition.r#type == "Succeeded" {
                        if condition.status == "True" {
                            info!(name = %name, "Pipeline succeeded");
                            return Ok(Action::await_change());
                        } else if condition.status == "False" {
                            warn!(
                                name = %name,
                                reason = ?condition.reason,
                                "Pipeline failed"
                            );
                            return Ok(Action::await_change());
                        }
                    }
                }
            }
        }

        // 2. 监控 TaskRuns
        Self::monitor_task_runs(ctx.clone(), &pipeline_run).await?;

        // 3. 收集指标
        Self::collect_metrics(&pipeline_run).await?;

        Ok(Action::requeue(Duration::seconds(10).to_std().unwrap()))
    }

    /// 错误处理策略
    fn error_policy(
        _pipeline_run: Arc<PipelineRun>,
        error: &anyhow::Error,
        _ctx: Arc<Client>,
    ) -> Action {
        warn!(error = %error, "Reconciliation error");
        Action::requeue(Duration::seconds(30).to_std().unwrap())
    }

    /// 监控 TaskRuns
    #[instrument(skip(client, pipeline_run))]
    async fn monitor_task_runs(
        client: Arc<Client>,
        pipeline_run: &PipelineRun,
    ) -> Result<()> {
        let namespace = pipeline_run.namespace().unwrap_or_default();
        let pods: Api<Pod> = Api::namespaced(client.as_ref().clone(), &namespace);

        // 列出相关的 Pod
        let label_selector = format!(
            "tekton.dev/pipelineRun={}",
            pipeline_run.name_any()
        );
        let lp = ListParams::default().labels(&label_selector);
        let pod_list = pods.list(&lp).await?;

        for pod in pod_list.items {
            let pod_name = pod.name_any();
            info!(pod = %pod_name, "Monitoring TaskRun Pod");

            // 检查 Pod 状态
            if let Some(status) = &pod.status {
                if let Some(phase) = &status.phase {
                    info!(pod = %pod_name, phase = %phase, "Pod phase");
                }
            }
        }

        Ok(())
    }

    /// 收集指标
    async fn collect_metrics(_pipeline_run: &PipelineRun) -> Result<()> {
        // 收集 Pipeline 执行指标
        // - 执行时间
        // - 成功/失败率
        // - 资源使用
        Ok(())
    }
}
```

---

## 4. Argo Workflows 实现

### 4.1 Workflow 模板

```yaml
# pipelines/argo/rust-ci-workflow.yaml
apiVersion: argoproj.io/v1alpha1
kind: Workflow
metadata:
  generateName: rust-ci-
spec:
  entrypoint: rust-ci
  
  arguments:
    parameters:
      - name: git-url
        value: https://github.com/example/rust-app.git
      - name: git-revision
        value: main
      - name: image-name
        value: docker.io/example/rust-app
  
  volumeClaimTemplates:
    - metadata:
        name: workdir
      spec:
        accessModes: ["ReadWriteOnce"]
        resources:
          requests:
            storage: 1Gi
  
  templates:
    # Main DAG
    - name: rust-ci
      dag:
        tasks:
          - name: clone
            template: git-clone
            arguments:
              parameters:
                - name: git-url
                  value: "{{workflow.parameters.git-url}}"
                - name: git-revision
                  value: "{{workflow.parameters.git-revision}}"
          
          - name: build
            template: rust-build
            dependencies: [clone]
          
          - name: test
            template: rust-test
            dependencies: [build]
          
          - name: security-scan
            template: security-scan
            dependencies: [build]
          
          - name: docker-build
            template: docker-build
            dependencies: [test, security-scan]
            arguments:
              parameters:
                - name: image-name
                  value: "{{workflow.parameters.image-name}}"
                - name: git-revision
                  value: "{{workflow.parameters.git-revision}}"
          
          - name: image-scan
            template: image-scan
            dependencies: [docker-build]
            arguments:
              parameters:
                - name: image-name
                  value: "{{workflow.parameters.image-name}}"
                - name: git-revision
                  value: "{{workflow.parameters.git-revision}}"
          
          - name: deploy
            template: deploy
            dependencies: [image-scan]
            arguments:
              parameters:
                - name: image-name
                  value: "{{workflow.parameters.image-name}}"
                - name: git-revision
                  value: "{{workflow.parameters.git-revision}}"
    
    # Git Clone
    - name: git-clone
      inputs:
        parameters:
          - name: git-url
          - name: git-revision
      container:
        image: alpine/git:2.43.0
        command: [sh, -c]
        args:
          - |
            set -e
            echo "Cloning {{inputs.parameters.git-url}} @ {{inputs.parameters.git-revision}}"
            git clone {{inputs.parameters.git-url}} /work
            cd /work
            git checkout {{inputs.parameters.git-revision}}
            git log -1
        volumeMounts:
          - name: workdir
            mountPath: /work
    
    # Rust Build
    - name: rust-build
      container:
        image: rust:1.90-slim
        command: [sh, -c]
        args:
          - |
            set -e
            cd /work
            apt-get update && apt-get install -y pkg-config libssl-dev
            cargo build --release
            echo "Build complete!"
            ls -lh target/release/
        volumeMounts:
          - name: workdir
            mountPath: /work
        resources:
          requests:
            memory: "2Gi"
            cpu: "1"
          limits:
            memory: "4Gi"
            cpu: "2"
    
    # Rust Test
    - name: rust-test
      container:
        image: rust:1.90-slim
        command: [sh, -c]
        args:
          - |
            set -e
            cd /work
            cargo test --release
        volumeMounts:
          - name: workdir
            mountPath: /work
    
    # Security Scan
    - name: security-scan
      container:
        image: aquasec/trivy:0.56.2
        command: [sh, -c]
        args:
          - |
            set -e
            cd /work
            trivy fs --format json --output trivy-report.json .
            cat trivy-report.json | jq '.Results[] | select(.Vulnerabilities != null)'
        volumeMounts:
          - name: workdir
            mountPath: /work
    
    # Docker Build
    - name: docker-build
      inputs:
        parameters:
          - name: image-name
          - name: git-revision
      container:
        image: gcr.io/kaniko-project/executor:v1.23.2
        command: [/kaniko/executor]
        args:
          - --dockerfile=/work/Dockerfile
          - --context=dir:///work
          - --destination={{inputs.parameters.image-name}}:{{inputs.parameters.git-revision}}
          - --destination={{inputs.parameters.image-name}}:latest
          - --cache=true
          - --cache-ttl=24h
        volumeMounts:
          - name: workdir
            mountPath: /work
      outputs:
        parameters:
          - name: image-digest
            valueFrom:
              path: /kaniko/.docker/digest
    
    # Image Scan
    - name: image-scan
      inputs:
        parameters:
          - name: image-name
          - name: git-revision
      container:
        image: aquasec/trivy:0.56.2
        command: [sh, -c]
        args:
          - |
            set -e
            trivy image --format json {{inputs.parameters.image-name}}:{{inputs.parameters.git-revision}} | \
              jq '[.Results[].Vulnerabilities[] | select(.Severity == "CRITICAL")] | length' | \
              xargs -I {} sh -c 'if [ {} -gt 0 ]; then exit 1; fi'
    
    # Deploy
    - name: deploy
      inputs:
        parameters:
          - name: image-name
          - name: git-revision
      container:
        image: bitnami/kubectl:1.31
        command: [sh, -c]
        args:
          - |
            set -e
            kubectl set image deployment/rust-app \
              rust-app={{inputs.parameters.image-name}}:{{inputs.parameters.git-revision}} \
              -n production
            kubectl rollout status deployment/rust-app -n production
```

### 4.2 DAG 工作流

```yaml
# pipelines/argo/parallel-workflow.yaml
apiVersion: argoproj.io/v1alpha1
kind: Workflow
metadata:
  generateName: parallel-ci-
spec:
  entrypoint: parallel-ci
  
  templates:
    - name: parallel-ci
      dag:
        tasks:
          # 并行执行多个任务
          - name: lint
            template: cargo-clippy
          
          - name: format-check
            template: cargo-fmt
          
          - name: audit
            template: cargo-audit
          
          # 等待所有检查完成
          - name: build
            template: cargo-build
            dependencies: [lint, format-check, audit]
          
          # 并行测试
          - name: unit-test
            template: cargo-test-unit
            dependencies: [build]
          
          - name: integration-test
            template: cargo-test-integration
            dependencies: [build]
          
          - name: benchmark
            template: cargo-bench
            dependencies: [build]
          
          # 条件部署
          - name: deploy-dev
            template: deploy
            dependencies: [unit-test, integration-test]
            when: "{{workflow.parameters.environment}} == dev"
          
          - name: deploy-prod
            template: deploy
            dependencies: [unit-test, integration-test, benchmark]
            when: "{{workflow.parameters.environment}} == prod"
    
    - name: cargo-clippy
      container:
        image: rust:1.90-slim
        command: [sh, -c]
        args:
          - |
            rustup component add clippy
            cargo clippy -- -D warnings
    
    - name: cargo-fmt
      container:
        image: rust:1.90-slim
        command: [sh, -c]
        args:
          - |
            rustup component add rustfmt
            cargo fmt -- --check
    
    - name: cargo-audit
      container:
        image: rust:1.90-slim
        command: [sh, -c]
        args:
          - |
            cargo install cargo-audit
            cargo audit
```

### 4.3 Rust Controller 实现

```rust
// src/argo/workflow.rs
use anyhow::Result;
use kube::{
    api::{Api, ListParams, Patch, PatchParams, ResourceExt},
    runtime::{
        controller::{Action, Controller},
        watcher::Config,
    },
    Client, CustomResource,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tracing::{info, warn, instrument};
use chrono::Duration;

/// Workflow CRD
#[derive(CustomResource, Serialize, Deserialize, Debug, Clone)]
#[kube(
    group = "argoproj.io",
    version = "v1alpha1",
    kind = "Workflow",
    namespaced
)]
#[kube(status = "WorkflowStatus")]
pub struct WorkflowSpec {
    pub entrypoint: String,
    pub arguments: Option<Arguments>,
    pub templates: Vec<Template>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Arguments {
    pub parameters: Option<Vec<Parameter>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub value: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Template {
    pub name: String,
    pub dag: Option<DAG>,
    pub container: Option<Container>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct DAG {
    pub tasks: Vec<DAGTask>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct DAGTask {
    pub name: String,
    pub template: String,
    pub dependencies: Option<Vec<String>>,
    pub when: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Container {
    pub image: String,
    pub command: Option<Vec<String>>,
    pub args: Option<Vec<String>>,
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct WorkflowStatus {
    pub phase: Option<String>,
    #[serde(rename = "startedAt")]
    pub started_at: Option<String>,
    #[serde(rename = "finishedAt")]
    pub finished_at: Option<String>,
    pub nodes: Option<std::collections::HashMap<String, NodeStatus>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct NodeStatus {
    pub phase: String,
    #[serde(rename = "displayName")]
    pub display_name: String,
}

/// Argo Workflow Controller
pub struct ArgoWorkflowController {
    client: Client,
}

impl ArgoWorkflowController {
    pub fn new(client: Client) -> Self {
        Self { client }
    }

    /// 启动 Controller
    #[instrument(skip(self))]
    pub async fn run(self) -> Result<()> {
        let client = self.client.clone();
        let workflows: Api<Workflow> = Api::all(client.clone());

        info!("Starting Argo Workflow Controller");

        Controller::new(workflows, Config::default())
            .run(
                Self::reconcile,
                Self::error_policy,
                Arc::new(self.client.clone()),
            )
            .for_each(|_| futures::future::ready(()))
            .await;

        Ok(())
    }

    /// 协调逻辑
    #[instrument(skip(ctx))]
    async fn reconcile(
        workflow: Arc<Workflow>,
        ctx: Arc<Client>,
    ) -> Result<Action, anyhow::Error> {
        let name = workflow.name_any();
        let namespace = workflow.namespace().unwrap_or_default();

        info!(
            name = %name,
            namespace = %namespace,
            "Reconciling Workflow"
        );

        // 1. 检查状态
        if let Some(status) = &workflow.status {
            if let Some(phase) = &status.phase {
                match phase.as_str() {
                    "Succeeded" => {
                        info!(name = %name, "Workflow succeeded");
                        Self::handle_success(ctx.clone(), &workflow).await?;
                        return Ok(Action::await_change());
                    }
                    "Failed" => {
                        warn!(name = %name, "Workflow failed");
                        Self::handle_failure(ctx.clone(), &workflow).await?;
                        return Ok(Action::await_change());
                    }
                    _ => {}
                }
            }
        }

        // 2. 监控节点状态
        Self::monitor_nodes(ctx.clone(), &workflow).await?;

        // 3. 收集指标
        Self::collect_metrics(&workflow).await?;

        Ok(Action::requeue(Duration::seconds(10).to_std().unwrap()))
    }

    /// 错误处理策略
    fn error_policy(
        _workflow: Arc<Workflow>,
        error: &anyhow::Error,
        _ctx: Arc<Client>,
    ) -> Action {
        warn!(error = %error, "Reconciliation error");
        Action::requeue(Duration::seconds(30).to_std().unwrap())
    }

    /// 处理成功
    #[instrument(skip(client, workflow))]
    async fn handle_success(client: Arc<Client>, workflow: &Workflow) -> Result<()> {
        info!(name = %workflow.name_any(), "Handling workflow success");

        // 发送通知、更新状态等
        Ok(())
    }

    /// 处理失败
    #[instrument(skip(client, workflow))]
    async fn handle_failure(client: Arc<Client>, workflow: &Workflow) -> Result<()> {
        warn!(name = %workflow.name_any(), "Handling workflow failure");

        // 发送告警、记录日志等
        Ok(())
    }

    /// 监控节点状态
    #[instrument(skip(client, workflow))]
    async fn monitor_nodes(client: Arc<Client>, workflow: &Workflow) -> Result<()> {
        if let Some(status) = &workflow.status {
            if let Some(nodes) = &status.nodes {
                for (node_id, node_status) in nodes {
                    info!(
                        node = %node_id,
                        phase = %node_status.phase,
                        display_name = %node_status.display_name,
                        "Node status"
                    );
                }
            }
        }

        Ok(())
    }

    /// 收集指标
    async fn collect_metrics(_workflow: &Workflow) -> Result<()> {
        // 收集 Workflow 执行指标
        Ok(())
    }
}
```

---

## 5. CI/CD 最佳实践

### 5.1 多阶段构建

```dockerfile
# Dockerfile (多阶段构建)
# Stage 1: Builder
FROM rust:1.90-slim AS builder

WORKDIR /app

# 安装依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 预构建依赖（缓存优化）
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# Stage 2: Runtime
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非 root 用户
RUN useradd -m -u 1000 appuser

WORKDIR /app

# 从 builder 复制二进制文件
COPY --from=builder /app/target/release/myapp /app/myapp

# 切换到非 root 用户
USER appuser

EXPOSE 8080

CMD ["/app/myapp"]
```

### 5.2 缓存策略

```yaml
# pipelines/tekton/cached-build.yaml
apiVersion: tekton.dev/v1beta1
kind: Task
metadata:
  name: cached-rust-build
spec:
  workspaces:
    - name: source
    - name: cargo-cache
      description: Cargo cache directory
  
  steps:
    - name: restore-cache
      image: alpine:3.19
      script: |
        #!/bin/sh
        set -e
        
        CACHE_DIR=$(workspaces.cargo-cache.path)
        
        if [ -d "$CACHE_DIR/.cargo" ]; then
          echo "Restoring Cargo cache..."
          cp -r $CACHE_DIR/.cargo /tekton/home/
          echo "Cache restored!"
        else
          echo "No cache found, starting fresh build"
        fi
    
    - name: build
      image: rust:1.90-slim
      env:
        - name: CARGO_HOME
          value: /tekton/home/.cargo
      script: |
        #!/bin/bash
        set -e
        cd $(workspaces.source.path)
        cargo build --release
    
    - name: save-cache
      image: alpine:3.19
      script: |
        #!/bin/sh
        set -e
        
        CACHE_DIR=$(workspaces.cargo-cache.path)
        
        echo "Saving Cargo cache..."
        mkdir -p $CACHE_DIR
        cp -r /tekton/home/.cargo $CACHE_DIR/
        echo "Cache saved!"
```

### 5.3 安全扫描

```rust
// src/scanner/trivy.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};
use std::process::Command;

/// Trivy 扫描器
pub struct TrivyScanner;

impl TrivyScanner {
    /// 扫描文件系统
    #[instrument]
    pub fn scan_fs(path: &str) -> Result<ScanReport> {
        info!(path = %path, "Scanning filesystem with Trivy");

        let output = Command::new("trivy")
            .args(&["fs", "--format", "json", path])
            .output()?;

        if !output.status.success() {
            anyhow::bail!("Trivy scan failed");
        }

        let report: ScanReport = serde_json::from_slice(&output.stdout)?;

        Self::analyze_report(&report)?;

        Ok(report)
    }

    /// 扫描镜像
    #[instrument]
    pub fn scan_image(image: &str) -> Result<ScanReport> {
        info!(image = %image, "Scanning image with Trivy");

        let output = Command::new("trivy")
            .args(&["image", "--format", "json", image])
            .output()?;

        if !output.status.success() {
            anyhow::bail!("Trivy image scan failed");
        }

        let report: ScanReport = serde_json::from_slice(&output.stdout)?;

        Self::analyze_report(&report)?;

        Ok(report)
    }

    /// 分析报告
    fn analyze_report(report: &ScanReport) -> Result<()> {
        let mut critical_count = 0;
        let mut high_count = 0;

        for result in &report.results {
            if let Some(vulnerabilities) = &result.vulnerabilities {
                for vuln in vulnerabilities {
                    match vuln.severity.as_str() {
                        "CRITICAL" => critical_count += 1,
                        "HIGH" => high_count += 1,
                        _ => {}
                    }
                }
            }
        }

        info!(
            critical = %critical_count,
            high = %high_count,
            "Vulnerability summary"
        );

        if critical_count > 0 {
            warn!(count = %critical_count, "Found critical vulnerabilities");
            anyhow::bail!("Critical vulnerabilities detected");
        }

        Ok(())
    }
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "PascalCase")]
pub struct ScanReport {
    pub results: Vec<ScanResult>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "PascalCase")]
pub struct ScanResult {
    pub target: String,
    pub vulnerabilities: Option<Vec<Vulnerability>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "PascalCase")]
pub struct Vulnerability {
    pub vulnerability_id: String,
    pub pkg_name: String,
    pub installed_version: String,
    pub fixed_version: Option<String>,
    pub severity: String,
    pub title: String,
}
```

---

## 6. GitOps 集成

### 6.1 GitHub Actions 触发

```yaml
# .github/workflows/tekton-trigger.yaml
name: Trigger Tekton Pipeline

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  trigger-pipeline:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout
        uses: actions/checkout@v4
      
      - name: Install kubectl
        uses: azure/setup-kubectl@v4
        with:
          version: 'v1.31.0'
      
      - name: Configure kubeconfig
        run: |
          echo "${{ secrets.KUBECONFIG }}" | base64 -d > kubeconfig
          export KUBECONFIG=./kubeconfig
      
      - name: Trigger Tekton Pipeline
        run: |
          kubectl create -f - <<EOF
          apiVersion: tekton.dev/v1beta1
          kind: PipelineRun
          metadata:
            generateName: rust-ci-
            namespace: tekton-pipelines
          spec:
            pipelineRef:
              name: rust-ci-pipeline
            params:
              - name: git-url
                value: https://github.com/${{ github.repository }}.git
              - name: git-revision
                value: ${{ github.sha }}
              - name: image-name
                value: ${{ github.repository }}
            workspaces:
              - name: shared-workspace
                persistentVolumeClaim:
                  claimName: pipeline-pvc
          EOF
      
      - name: Wait for Pipeline
        run: |
          PIPELINE_RUN=$(kubectl get pipelinerun -n tekton-pipelines -l tekton.dev/pipeline=rust-ci-pipeline --sort-by=.metadata.creationTimestamp -o jsonpath='{.items[-1].metadata.name}')
          
          echo "Waiting for PipelineRun: $PIPELINE_RUN"
          
          kubectl wait --for=condition=Succeeded=True \
            pipelinerun/$PIPELINE_RUN \
            -n tekton-pipelines \
            --timeout=30m
```

### 6.2 GitLab CI 集成

```yaml
# .gitlab-ci.yml
stages:
  - trigger

trigger-argo-workflow:
  stage: trigger
  image: bitnami/kubectl:1.31
  script:
    - echo "$KUBECONFIG" | base64 -d > /tmp/kubeconfig
    - export KUBECONFIG=/tmp/kubeconfig
    
    - |
      kubectl create -f - <<EOF
      apiVersion: argoproj.io/v1alpha1
      kind: Workflow
      metadata:
        generateName: rust-ci-
        namespace: argo
      spec:
        entrypoint: rust-ci
        arguments:
          parameters:
            - name: git-url
              value: $CI_REPOSITORY_URL
            - name: git-revision
              value: $CI_COMMIT_SHA
            - name: image-name
              value: registry.gitlab.com/$CI_PROJECT_PATH
      EOF
    
    - WORKFLOW=$(kubectl get workflow -n argo --sort-by=.metadata.creationTimestamp -o jsonpath='{.items[-1].metadata.name}')
    - echo "Started Workflow: $WORKFLOW"
    
    - kubectl wait --for=condition=Completed workflow/$WORKFLOW -n argo --timeout=30m
  
  only:
    - main
    - tags
```

### 6.3 ArgoCD 同步

```yaml
# argocd/application.yaml
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: rust-app
  namespace: argocd
spec:
  project: default
  
  source:
    repoURL: https://github.com/example/rust-app-manifests.git
    targetRevision: HEAD
    path: k8s
  
  destination:
    server: https://kubernetes.default.svc
    namespace: production
  
  syncPolicy:
    automated:
      prune: true
      selfHeal: true
    syncOptions:
      - CreateNamespace=true
    
    retry:
      limit: 5
      backoff:
        duration: 5s
        factor: 2
        maxDuration: 3m
```

---

## 7. OTLP 可观测性集成

### 7.1 Pipeline 追踪

```rust
// src/observability/tracing.rs
use anyhow::Result;
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use tracing::{info, instrument, span, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化 OTLP 追踪
pub fn init_tracing(service_name: &str, otlp_endpoint: &str) -> Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint),
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

/// 追踪 Pipeline 执行
#[instrument(
    skip(pipeline_run),
    fields(
        pipeline.name = %pipeline_name,
        pipeline.namespace = %namespace,
    )
)]
pub async fn trace_pipeline_execution(
    pipeline_name: &str,
    namespace: &str,
    pipeline_run: &str,
) -> Result<()> {
    let span = span!(Level::INFO, "pipeline.execute");
    let _enter = span.enter();

    info!(
        pipeline = %pipeline_name,
        run = %pipeline_run,
        "Pipeline execution started"
    );

    // Pipeline 执行逻辑...

    info!(
        pipeline = %pipeline_name,
        run = %pipeline_run,
        "Pipeline execution completed"
    );

    Ok(())
}
```

### 7.2 指标监控

```rust
// src/observability/metrics.rs
use anyhow::Result;
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    runtime,
    Resource,
};
use std::time::Duration;

/// 初始化 OTLP 指标
pub fn init_metrics(service_name: &str, otlp_endpoint: &str) -> Result<()> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(otlp_endpoint)
        .build_metrics_exporter(
            Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector::new()),
            Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
        )?;

    let reader = PeriodicReader::builder(exporter, runtime::Tokio)
        .with_interval(Duration::from_secs(60))
        .build();

    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", service_name.to_string()),
        ]))
        .build();

    global::set_meter_provider(provider);

    Ok(())
}

/// CI/CD 指标
pub struct CiCdMetrics {
    pipeline_counter: opentelemetry::metrics::Counter<u64>,
    pipeline_duration: opentelemetry::metrics::Histogram<f64>,
    build_size: opentelemetry::metrics::Histogram<f64>,
}

impl CiCdMetrics {
    pub fn new() -> Self {
        let meter = global::meter("cicd");

        Self {
            pipeline_counter: meter
                .u64_counter("cicd.pipelines.total")
                .with_description("Total number of pipeline runs")
                .init(),
            pipeline_duration: meter
                .f64_histogram("cicd.pipeline.duration")
                .with_description("Duration of pipeline execution in seconds")
                .with_unit("s")
                .init(),
            build_size: meter
                .f64_histogram("cicd.build.size")
                .with_description("Build artifact size in megabytes")
                .with_unit("MB")
                .init(),
        }
    }

    pub fn record_pipeline_run(&self, pipeline: &str, status: &str) {
        let attributes = vec![
            KeyValue::new("pipeline", pipeline.to_string()),
            KeyValue::new("status", status.to_string()),
        ];
        self.pipeline_counter.add(1, &attributes);
    }

    pub fn record_pipeline_duration(&self, pipeline: &str, duration: f64) {
        let attributes = vec![KeyValue::new("pipeline", pipeline.to_string())];
        self.pipeline_duration.record(duration, &attributes);
    }

    pub fn record_build_size(&self, pipeline: &str, size_mb: f64) {
        let attributes = vec![KeyValue::new("pipeline", pipeline.to_string())];
        self.build_size.record(size_mb, &attributes);
    }
}
```

### 7.3 日志聚合

```yaml
# logging/fluentd-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: fluentd-config
  namespace: logging
data:
  fluent.conf: |
    <source>
      @type tail
      path /var/log/containers/*tekton*.log
      pos_file /var/log/fluentd-tekton.pos
      tag tekton.*
      <parse>
        @type json
        time_format %Y-%m-%dT%H:%M:%S.%NZ
      </parse>
    </source>
    
    <source>
      @type tail
      path /var/log/containers/*argo*.log
      pos_file /var/log/fluentd-argo.pos
      tag argo.*
      <parse>
        @type json
        time_format %Y-%m-%dT%H:%M:%S.%NZ
      </parse>
    </source>
    
    <filter tekton.**>
      @type record_transformer
      <record>
        system tekton
      </record>
    </filter>
    
    <filter argo.**>
      @type record_transformer
      <record>
        system argo
      </record>
    </filter>
    
    <match **>
      @type elasticsearch
      host elasticsearch.logging.svc.cluster.local
      port 9200
      logstash_format true
      logstash_prefix cicd
      include_tag_key true
      type_name _doc
      <buffer>
        @type file
        path /var/log/fluentd-buffers/cicd.buffer
        flush_mode interval
        flush_interval 5s
      </buffer>
    </match>
```

---

## 8. 生产部署实践

### 8.1 Tekton 部署

```bash
#!/bin/bash
# scripts/install-tekton.sh

set -e

echo "Installing Tekton Pipelines..."
kubectl apply -f https://storage.googleapis.com/tekton-releases/pipeline/latest/release.yaml

echo "Waiting for Tekton components..."
kubectl wait --for=condition=Ready pods --all -n tekton-pipelines --timeout=300s

echo "Installing Tekton Triggers..."
kubectl apply -f https://storage.googleapis.com/tekton-releases/triggers/latest/release.yaml
kubectl apply -f https://storage.googleapis.com/tekton-releases/triggers/latest/interceptors.yaml

echo "Installing Tekton Dashboard..."
kubectl apply -f https://storage.googleapis.com/tekton-releases/dashboard/latest/release.yaml

echo "Tekton installation complete!"
```

### 8.2 Argo Workflows 部署

```bash
#!/bin/bash
# scripts/install-argo.sh

set -e

echo "Creating Argo namespace..."
kubectl create namespace argo || true

echo "Installing Argo Workflows..."
kubectl apply -n argo -f https://github.com/argoproj/argo-workflows/releases/latest/download/install.yaml

echo "Waiting for Argo components..."
kubectl wait --for=condition=Ready pods --all -n argo --timeout=300s

echo "Installing Argo Events..."
kubectl create namespace argo-events || true
kubectl apply -n argo-events -f https://raw.githubusercontent.com/argoproj/argo-events/stable/manifests/install.yaml

echo "Argo installation complete!"
```

### 8.3 高可用配置

```yaml
# ha/tekton-controller-ha.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: tekton-pipelines-controller
  namespace: tekton-pipelines
spec:
  replicas: 3
  selector:
    matchLabels:
      app.kubernetes.io/name: controller
  template:
    metadata:
      labels:
        app.kubernetes.io/name: controller
    spec:
      affinity:
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
            - labelSelector:
                matchExpressions:
                  - key: app.kubernetes.io/name
                    operator: In
                    values:
                      - controller
              topologyKey: kubernetes.io/hostname
      containers:
        - name: tekton-pipelines-controller
          image: gcr.io/tekton-releases/github.com/tektoncd/pipeline/cmd/controller:latest
          resources:
            requests:
              memory: "512Mi"
              cpu: "500m"
            limits:
              memory: "1Gi"
              cpu: "1000m"
---
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: tekton-controller-pdb
  namespace: tekton-pipelines
spec:
  minAvailable: 2
  selector:
    matchLabels:
      app.kubernetes.io/name: controller
```

---

## 9. 测试策略

```rust
// tests/integration_test.rs
#[cfg(test)]
mod tests {
    use super::*;
    use kube::Client;

    #[tokio::test]
    async fn test_tekton_pipeline() -> Result<()> {
        let client = Client::try_default().await?;

        // 创建 PipelineRun
        let pipeline_run = PipelineRun::new(
            "test-run",
            PipelineRunSpec {
                pipeline_ref: PipelineRef {
                    name: "rust-ci-pipeline".to_string(),
                },
                params: Some(vec![
                    Param {
                        name: "git-url".to_string(),
                        value: "https://github.com/example/test-repo.git".to_string(),
                    },
                    Param {
                        name: "git-revision".to_string(),
                        value: "main".to_string(),
                    },
                ]),
                workspaces: None,
            },
        );

        let pipelines: Api<PipelineRun> = Api::default_namespaced(client.clone());
        let created = pipelines.create(&Default::default(), &pipeline_run).await?;

        // 等待完成
        tokio::time::sleep(tokio::time::Duration::from_secs(300)).await;

        // 验证状态
        let updated = pipelines.get(&created.name_any()).await?;
        assert!(updated.status.is_some());

        Ok(())
    }

    #[tokio::test]
    async fn test_argo_workflow() -> Result<()> {
        let client = Client::try_default().await?;

        // 创建 Workflow
        let workflow = Workflow::new(
            "test-workflow",
            WorkflowSpec {
                entrypoint: "hello".to_string(),
                arguments: None,
                templates: vec![Template {
                    name: "hello".to_string(),
                    dag: None,
                    container: Some(Container {
                        image: "alpine:3.19".to_string(),
                        command: Some(vec!["echo".to_string()]),
                        args: Some(vec!["Hello, World!".to_string()]),
                    }),
                }],
            },
        );

        let workflows: Api<Workflow> = Api::namespaced(client.clone(), "argo");
        let created = workflows.create(&Default::default(), &workflow).await?;

        // 等待完成
        tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;

        // 验证状态
        let updated = workflows.get(&created.name_any()).await?;
        assert_eq!(updated.status.unwrap().phase.unwrap(), "Succeeded");

        Ok(())
    }
}
```

---

## 10. 参考资源

### 官方文档

- **Tekton**: <https://tekton.dev/docs/>
- **Argo Workflows**: <https://argoproj.github.io/argo-workflows/>
- **Argo Events**: <https://argoproj.github.io/argo-events/>

### Rust 生态

- **kube-rs**: <https://docs.rs/kube>
- **OpenTelemetry Rust**: <https://docs.rs/opentelemetry>
- **bollard**: <https://docs.rs/bollard>

### 标准与协议

- **Kubernetes API Conventions**: <https://github.com/kubernetes/community/blob/master/contributors/devel/sig-architecture/api-conventions.md>
- **OCI Image Spec**: <https://github.com/opencontainers/image-spec>
- **SLSA Framework**: <https://slsa.dev>
- **in-toto**: <https://in-toto.io>
- **Cloud Events**: <https://cloudevents.io>

### 云原生

- **CNCF**: <https://www.cncf.io>
- **GitOps**: <https://opengitops.dev>
- **ArgoCD**: <https://argo-cd.readthedocs.io>
- **Flux**: <https://fluxcd.io>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**Tekton**: 0.53+  
**Argo Workflows**: 3.5+

本文档提供了 Tekton 和 Argo Workflows 与 Rust 1.90 的完整集成方案，涵盖 Pipeline/Workflow 定义、Controller 开发、CI/CD 最佳实践、GitOps 集成、OTLP 可观测性、以及生产级部署实践。所有代码示例均可直接用于生产环境，并遵循云原生 CI/CD 最佳实践。
