# GitOps 与自动化运维

## 目录

- [GitOps 与自动化运维](#gitops-与自动化运维)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [🎯 GitOps 核心原则](#-gitops-核心原则)
  - [🏗️ GitOps 架构](#️-gitops-架构)
  - [🔧 ArgoCD 实践](#-argocd-实践)
  - [🤖 自动化运维](#-自动化运维)
  - [🎯 最佳实践](#-最佳实践)

## 📋 概述

GitOps 是一种以 Git 为单一事实来源的声明式基础设施和应用管理方法,通过 Git 仓库管理所有配置,实现自动化部署和运维。

## 🎯 GitOps 核心原则

1. **声明式**: 所有配置以声明式方式定义
2. **版本化**: 所有配置存储在 Git 中
3. **自动化**: 自动同步 Git 状态到集群
4. **可审计**: 所有变更可追溯

## 🏗️ GitOps 架构

```text
┌─────────────────────────────────────────────────────────────────┐
│                      GitOps 工作流                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐                                               │
│  │ Developer    │                                               │
│  └──────┬───────┘                                               │
│         │ git push                                              │
│         ▼                                                       │
│  ┌──────────────┐                                               │
│  │ Git Repo     │◄────────┐                                     │
│  │ (manifests)  │         │ sync                                │
│  └──────┬───────┘         │                                     │
│         │                 │                                     │
│         │ webhook         │                                     │
│         ▼                 │                                     │
│  ┌──────────────┐         │                                     │
│  │ ArgoCD       │─────────┘                                     │
│  │ (GitOps      │                                               │
│  │  Operator)   │                                               │
│  └──────┬───────┘                                               │
│         │ kubectl apply                                         │
│         ▼                                                       │
│  ┌──────────────┐                                               │
│  │ Kubernetes   │                                               │
│  │ Cluster      │                                               │
│  └──────────────┘                                               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## 🔧 ArgoCD 实践

```yaml
# ArgoCD Application 定义
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: my-service
  namespace: argocd
spec:
  project: default
  source:
    repoURL: https://github.com/myorg/my-service
    targetRevision: HEAD
    path: k8s/overlays/production
  destination:
    server: https://kubernetes.default.svc
    namespace: production
  syncPolicy:
    automated:
      prune: true
      selfHeal: true
      allowEmpty: false
    syncOptions:
    - Validate=true
    - CreateNamespace=true
    - PrunePropagationPolicy=foreground
    - PruneLast=true
    retry:
      limit: 5
      backoff:
        duration: 5s
        factor: 2
        maxDuration: 3m
```

```rust
/// ArgoCD 应用配置
pub struct ArgoCDApplication {
    pub name: String,
    pub namespace: String,
    pub repo_url: String,
    pub path: String,
    pub target_revision: String,
    pub destination: Destination,
    pub sync_policy: SyncPolicy,
}

#[derive(Debug, Clone)]
pub struct SyncPolicy {
    pub automated: bool,
    pub prune: bool,
    pub self_heal: bool,
}

impl ArgoCDApplication {
    /// 生成 ArgoCD Application manifest
    pub fn to_yaml(&self) -> String {
        format!(r#"
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: {}
  namespace: {}
spec:
  project: default
  source:
    repoURL: {}
    targetRevision: {}
    path: {}
  destination:
    server: {}
    namespace: {}
  syncPolicy:
    automated:
      prune: {}
      selfHeal: {}
"#,
            self.name,
            self.namespace,
            self.repo_url,
            self.target_revision,
            self.path,
            self.destination.server,
            self.destination.namespace,
            self.sync_policy.prune,
            self.sync_policy.self_heal,
        )
    }
}
```

## 🤖 自动化运维

```rust
/// 自动化运维任务
pub struct AutomationTask {
    pub name: String,
    pub schedule: String,
    pub action: AutomationAction,
}

#[derive(Debug, Clone)]
pub enum AutomationAction {
    ScaleReplicas { min: u32, max: u32 },
    CleanupOldPods { age_days: u32 },
    BackupDatabase { retention_days: u32 },
    RotateCertificates,
    UpdateDependencies,
}

impl AutomationTask {
    /// 生成 Kubernetes CronJob
    pub fn to_cronjob(&self) -> String {
        format!(r#"
apiVersion: batch/v1
kind: CronJob
metadata:
  name: {}
spec:
  schedule: "{}"
  jobTemplate:
    spec:
      template:
        spec:
          containers:
          - name: automation
            image: automation-runner:latest
            command: ["run-automation"]
            args: ["{}"]
          restartPolicy: OnFailure
"#,
            self.name,
            self.schedule,
            serde_json::to_string(&self.action).unwrap()
        )
    }
}
```

## 🎯 最佳实践

1. **环境隔离**: 不同环境使用不同的 Git 分支或目录
2. **密钥管理**: 使用 Sealed Secrets 或 External Secrets
3. **渐进式交付**: 结合 Argo Rollouts 实现金丝雀发布
4. **监控告警**: 监控 GitOps 同步状态
5. **灾难恢复**: 定期备份 Git 仓库和集群状态

---

**总结**: GitOps 通过 Git 作为单一事实来源,实现了声明式、自动化的基础设施和应用管理。
