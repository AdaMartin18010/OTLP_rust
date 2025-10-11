# Helm Charts + GitOps - Rust + OTLP 部署自动化完整指南

## 📋 目录

- [Helm Charts + GitOps - Rust + OTLP 部署自动化完整指南](#helm-charts--gitops---rust--otlp-部署自动化完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Helm?](#什么是-helm)
    - [什么是 GitOps?](#什么是-gitops)
    - [为什么使用 Rust?](#为什么使用-rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Helm 架构](#1-helm-架构)
    - [2. GitOps 工作流](#2-gitops-工作流)
  - [Helm Charts 开发](#helm-charts-开发)
    - [1. Chart 结构](#1-chart-结构)
    - [2. Chart.yaml](#2-chartyaml)
    - [3. values.yaml](#3-valuesyaml)
    - [4. Deployment 模板](#4-deployment-模板)
    - [5. Service 模板](#5-service-模板)
    - [6. ConfigMap 模板](#6-configmap-模板)
  - [ArgoCD 集成](#argocd-集成)
    - [1. ArgoCD 安装](#1-argocd-安装)
    - [2. Application 定义](#2-application-定义)
    - [3. 多环境部署](#3-多环境部署)
    - [4. 自动同步策略](#4-自动同步策略)
  - [Flux 集成](#flux-集成)
    - [1. Flux 安装](#1-flux-安装)
    - [2. HelmRelease 定义](#2-helmrelease-定义)
    - [3. Kustomization](#3-kustomization)
    - [4. Image Automation](#4-image-automation)
  - [OTLP 配置管理](#otlp-配置管理)
    - [1. OpenTelemetry Operator](#1-opentelemetry-operator)
    - [2. OpenTelemetry Collector](#2-opentelemetry-collector)
    - [3. 自动注入](#3-自动注入)
  - [CI/CD 流水线](#cicd-流水线)
    - [1. GitHub Actions](#1-github-actions)
    - [2. 镜像构建](#2-镜像构建)
    - [3. Helm Chart 发布](#3-helm-chart-发布)
  - [高级特性](#高级特性)
    - [1. Helm Hooks](#1-helm-hooks)
    - [2. 蓝绿部署](#2-蓝绿部署)
    - [3. 回滚策略](#3-回滚策略)
  - [监控与告警](#监控与告警)
    - [1. ArgoCD Metrics](#1-argocd-metrics)
    - [2. 部署事件追踪](#2-部署事件追踪)
  - [最佳实践](#最佳实践)
    - [1. Chart 版本管理](#1-chart-版本管理)
    - [2. 密钥管理](#2-密钥管理)
    - [3. 多租户隔离](#3-多租户隔离)
  - [完整示例](#完整示例)
    - [1. Rust 微服务 Helm Chart](#1-rust-微服务-helm-chart)
    - [2. GitOps Repository 结构](#2-gitops-repository-结构)
    - [3. 完整部署流程](#3-完整部署流程)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [ArgoCD vs Flux](#argocd-vs-flux)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Helm?

**Helm** 是 Kubernetes 的包管理器,类似于 Linux 的 apt/yum:

```text
Helm Chart
  ├─ Chart.yaml         (元数据)
  ├─ values.yaml        (配置)
  └─ templates/         (K8s 资源模板)
       ├─ deployment.yaml
       ├─ service.yaml
       └─ configmap.yaml
```

### 什么是 GitOps?

**GitOps** 是一种声明式的持续交付方法,以 Git 为单一真实来源:

```text
Git Repository (Desired State)
    ↓
GitOps Tool (ArgoCD/Flux)
    ↓
Kubernetes Cluster (Actual State)
```

### 为什么使用 Rust?

- **快速部署**: 小镜像(10-20MB)、快速启动(<100ms)
- **资源高效**: 低内存占用,适合大规模部署
- **云原生**: 天然适配容器化和 K8s
- **可靠性**: 无 GC,稳定的性能表现

### OTLP 集成价值

| 可观测性维度 | OTLP + GitOps |
|------------|--------------|
| **部署追踪** | Trace 部署流程 |
| **配置变更** | Span Events 记录 |
| **服务健康** | Metrics(就绪探针) |
| **回滚追踪** | 分布式 Trace |
| **部署指标** | 部署频率/成功率 |

---

## 核心概念

### 1. Helm 架构

```text
┌─────────────────────────────────────┐
│         Helm CLI (Client)           │
└──────────────┬──────────────────────┘
               │ kubectl apply
┌──────────────▼──────────────────────┐
│      Kubernetes API Server          │
└──────────────┬──────────────────────┘
               │ Deploy
┌──────────────▼──────────────────────┐
│    Kubernetes Resources (Pods...)   │
└─────────────────────────────────────┘
```

**Helm 核心概念**:

- **Chart**: 包含所有资源定义的包
- **Release**: Chart 的一次部署实例
- **Repository**: Chart 存储仓库

### 2. GitOps 工作流

```text
Developer Push → Git Repository
                      ↓
              GitOps Controller
              (ArgoCD/Flux)
                      ↓
              Sync to Cluster
                      ↓
              Kubernetes Apply
                      ↓
              Monitor & Alert
```

---

## Helm Charts 开发

### 1. Chart 结构

```bash
# 创建 Helm Chart
helm create rust-otlp-service

# 生成的结构
rust-otlp-service/
├── Chart.yaml
├── values.yaml
├── charts/
├── templates/
│   ├── deployment.yaml
│   ├── service.yaml
│   ├── serviceaccount.yaml
│   ├── configmap.yaml
│   ├── ingress.yaml
│   ├── hpa.yaml
│   ├── _helpers.tpl
│   └── NOTES.txt
└── .helmignore
```

### 2. Chart.yaml

```yaml
# Chart.yaml
apiVersion: v2
name: rust-otlp-service
description: A Helm chart for Rust microservice with OTLP support
type: application
version: 1.0.0
appVersion: "1.0.0"

keywords:
  - rust
  - otlp
  - observability
  - microservice

maintainers:
  - name: Your Team
    email: team@example.com

dependencies:
  - name: opentelemetry-collector
    version: "0.95.0"
    repository: https://open-telemetry.github.io/opentelemetry-helm-charts
    condition: collector.enabled
```

### 3. values.yaml

```yaml
# values.yaml
replicaCount: 3

image:
  repository: myregistry/rust-otlp-service
  pullPolicy: IfNotPresent
  tag: "1.0.0"

imagePullSecrets: []
nameOverride: ""
fullnameOverride: ""

serviceAccount:
  create: true
  automount: true
  annotations: {}
  name: ""

podAnnotations:
  prometheus.io/scrape: "true"
  prometheus.io/port: "8080"
  prometheus.io/path: "/metrics"

podLabels:
  app.kubernetes.io/part-of: rust-microservices

podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1000
  fsGroup: 1000

securityContext:
  allowPrivilegeEscalation: false
  capabilities:
    drop:
    - ALL
  readOnlyRootFilesystem: true

service:
  type: ClusterIP
  port: 8080
  targetPort: 8080
  annotations: {}

ingress:
  enabled: true
  className: "nginx"
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
  hosts:
    - host: api.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: api-tls
      hosts:
        - api.example.com

resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 100m
    memory: 128Mi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80

livenessProbe:
  httpGet:
    path: /health
    port: http
  initialDelaySeconds: 10
  periodSeconds: 10

readinessProbe:
  httpGet:
    path: /health
    port: http
  initialDelaySeconds: 5
  periodSeconds: 5

# OTLP 配置
otlp:
  enabled: true
  endpoint: "http://otel-collector:4317"
  serviceName: "rust-otlp-service"
  environment: "production"

# OpenTelemetry Collector
collector:
  enabled: true
  mode: sidecar  # sidecar 或 standalone

env:
  - name: RUST_LOG
    value: "info"
  - name: OTEL_EXPORTER_OTLP_ENDPOINT
    value: "{{ .Values.otlp.endpoint }}"
  - name: OTEL_SERVICE_NAME
    value: "{{ .Values.otlp.serviceName }}"
  - name: OTEL_RESOURCE_ATTRIBUTES
    value: "deployment.environment={{ .Values.otlp.environment }}"

nodeSelector: {}
tolerations: []
affinity: {}
```

### 4. Deployment 模板

```yaml
# templates/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: {{ include "rust-otlp-service.fullname" . }}
  labels:
    {{- include "rust-otlp-service.labels" . | nindent 4 }}
spec:
  {{- if not .Values.autoscaling.enabled }}
  replicas: {{ .Values.replicaCount }}
  {{- end }}
  selector:
    matchLabels:
      {{- include "rust-otlp-service.selectorLabels" . | nindent 6 }}
  template:
    metadata:
      annotations:
        checksum/config: {{ include (print $.Template.BasePath "/configmap.yaml") . | sha256sum }}
        {{- with .Values.podAnnotations }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
      labels:
        {{- include "rust-otlp-service.labels" . | nindent 8 }}
        {{- with .Values.podLabels }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
    spec:
      {{- with .Values.imagePullSecrets }}
      imagePullSecrets:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      serviceAccountName: {{ include "rust-otlp-service.serviceAccountName" . }}
      securityContext:
        {{- toYaml .Values.podSecurityContext | nindent 8 }}
      containers:
      - name: {{ .Chart.Name }}
        securityContext:
          {{- toYaml .Values.securityContext | nindent 12 }}
        image: "{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"
        imagePullPolicy: {{ .Values.image.pullPolicy }}
        ports:
        - name: http
          containerPort: {{ .Values.service.targetPort }}
          protocol: TCP
        {{- if .Values.livenessProbe }}
        livenessProbe:
          {{- toYaml .Values.livenessProbe | nindent 12 }}
        {{- end }}
        {{- if .Values.readinessProbe }}
        readinessProbe:
          {{- toYaml .Values.readinessProbe | nindent 12 }}
        {{- end }}
        resources:
          {{- toYaml .Values.resources | nindent 12 }}
        env:
          {{- toYaml .Values.env | nindent 12 }}
        volumeMounts:
        - name: tmp
          mountPath: /tmp
        - name: config
          mountPath: /etc/config
          readOnly: true
      
      {{- if and .Values.collector.enabled (eq .Values.collector.mode "sidecar") }}
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.98.0
        args:
          - "--config=/etc/otel-collector-config.yaml"
        ports:
        - name: otlp-grpc
          containerPort: 4317
          protocol: TCP
        - name: otlp-http
          containerPort: 4318
          protocol: TCP
        volumeMounts:
        - name: otel-collector-config
          mountPath: /etc/otel-collector-config.yaml
          subPath: otel-collector-config.yaml
        resources:
          limits:
            cpu: 200m
            memory: 256Mi
          requests:
            cpu: 50m
            memory: 128Mi
      {{- end }}
      
      volumes:
      - name: tmp
        emptyDir: {}
      - name: config
        configMap:
          name: {{ include "rust-otlp-service.fullname" . }}
      {{- if and .Values.collector.enabled (eq .Values.collector.mode "sidecar") }}
      - name: otel-collector-config
        configMap:
          name: {{ include "rust-otlp-service.fullname" . }}-otel-collector
      {{- end }}
      
      {{- with .Values.nodeSelector }}
      nodeSelector:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.affinity }}
      affinity:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.tolerations }}
      tolerations:
        {{- toYaml . | nindent 8 }}
      {{- end }}
```

### 5. Service 模板

```yaml
# templates/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: {{ include "rust-otlp-service.fullname" . }}
  labels:
    {{- include "rust-otlp-service.labels" . | nindent 4 }}
  {{- with .Values.service.annotations }}
  annotations:
    {{- toYaml . | nindent 4 }}
  {{- end }}
spec:
  type: {{ .Values.service.type }}
  ports:
    - port: {{ .Values.service.port }}
      targetPort: http
      protocol: TCP
      name: http
  selector:
    {{- include "rust-otlp-service.selectorLabels" . | nindent 4 }}
```

### 6. ConfigMap 模板

```yaml
# templates/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: {{ include "rust-otlp-service.fullname" . }}
  labels:
    {{- include "rust-otlp-service.labels" . | nindent 4 }}
data:
  app-config.yaml: |
    server:
      port: {{ .Values.service.targetPort }}
    otlp:
      endpoint: {{ .Values.otlp.endpoint }}
      service_name: {{ .Values.otlp.serviceName }}
      environment: {{ .Values.otlp.environment }}
    logging:
      level: {{ .Values.env | default "info" }}

---
{{- if and .Values.collector.enabled (eq .Values.collector.mode "sidecar") }}
apiVersion: v1
kind: ConfigMap
metadata:
  name: {{ include "rust-otlp-service.fullname" . }}-otel-collector
  labels:
    {{- include "rust-otlp-service.labels" . | nindent 4 }}
data:
  otel-collector-config.yaml: |
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
      
      resource:
        attributes:
          - key: deployment.environment
            value: {{ .Values.otlp.environment }}
            action: upsert
    
    exporters:
      otlp:
        endpoint: otel-collector-gateway:4317
        tls:
          insecure: true
      
      prometheus:
        endpoint: "0.0.0.0:8889"
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [batch, resource]
          exporters: [otlp]
        metrics:
          receivers: [otlp]
          processors: [batch, resource]
          exporters: [otlp, prometheus]
        logs:
          receivers: [otlp]
          processors: [batch, resource]
          exporters: [otlp]
{{- end }}
```

---

## ArgoCD 集成

### 1. ArgoCD 安装

```bash
# 安装 ArgoCD
kubectl create namespace argocd
kubectl apply -n argocd -f https://raw.githubusercontent.com/argoproj/argo-cd/stable/manifests/install.yaml

# 访问 ArgoCD UI
kubectl port-forward svc/argocd-server -n argocd 8080:443

# 获取初始密码
kubectl -n argocd get secret argocd-initial-admin-secret -o jsonpath="{.data.password}" | base64 -d
```

### 2. Application 定义

```yaml
# argocd/rust-otlp-service-app.yaml
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: rust-otlp-service
  namespace: argocd
  finalizers:
    - resources-finalizer.argocd.argoproj.io
spec:
  project: default
  
  source:
    repoURL: https://github.com/myorg/helm-charts.git
    targetRevision: main
    path: charts/rust-otlp-service
    helm:
      releaseName: rust-otlp-service
      valueFiles:
        - values-production.yaml
      parameters:
        - name: image.tag
          value: "1.0.0"
        - name: replicaCount
          value: "3"
  
  destination:
    server: https://kubernetes.default.svc
    namespace: production
  
  syncPolicy:
    automated:
      prune: true
      selfHeal: true
      allowEmpty: false
    syncOptions:
      - CreateNamespace=true
      - PruneLast=true
    retry:
      limit: 5
      backoff:
        duration: 5s
        factor: 2
        maxDuration: 3m
  
  ignoreDifferences:
    - group: apps
      kind: Deployment
      jsonPointers:
        - /spec/replicas  # 忽略 HPA 管理的 replicas
```

### 3. 多环境部署

```yaml
# argocd/applicationset.yaml
apiVersion: argoproj.io/v1alpha1
kind: ApplicationSet
metadata:
  name: rust-otlp-service-envs
  namespace: argocd
spec:
  generators:
  - list:
      elements:
      - env: development
        cluster: dev-cluster
        replicaCount: "1"
      - env: staging
        cluster: staging-cluster
        replicaCount: "2"
      - env: production
        cluster: prod-cluster
        replicaCount: "3"
  
  template:
    metadata:
      name: 'rust-otlp-service-{{env}}'
    spec:
      project: default
      source:
        repoURL: https://github.com/myorg/helm-charts.git
        targetRevision: main
        path: charts/rust-otlp-service
        helm:
          releaseName: rust-otlp-service
          valueFiles:
            - values-{{env}}.yaml
          parameters:
            - name: replicaCount
              value: '{{replicaCount}}'
            - name: otlp.environment
              value: '{{env}}'
      destination:
        server: '{{cluster}}'
        namespace: '{{env}}'
      syncPolicy:
        automated:
          prune: true
          selfHeal: true
```

### 4. 自动同步策略

```yaml
# argocd/sync-policy.yaml
apiVersion: argoproj.io/v1alpha1
kind: AppProject
metadata:
  name: rust-microservices
  namespace: argocd
spec:
  description: Rust Microservices Project
  
  sourceRepos:
    - 'https://github.com/myorg/*'
  
  destinations:
    - namespace: '*'
      server: https://kubernetes.default.svc
  
  clusterResourceWhitelist:
    - group: ''
      kind: Namespace
    - group: 'rbac.authorization.k8s.io'
      kind: ClusterRole
  
  namespaceResourceWhitelist:
    - group: '*'
      kind: '*'
  
  syncWindows:
    - kind: allow
      schedule: '0 9 * * 1-5'  # 工作日 9AM
      duration: 8h
      applications:
        - rust-otlp-service-production
```

---

## Flux 集成

### 1. Flux 安装

```bash
# 安装 Flux CLI
brew install fluxcd/tap/flux

# 引导 Flux
flux bootstrap github \
  --owner=myorg \
  --repository=fleet-infra \
  --branch=main \
  --path=./clusters/production \
  --personal
```

### 2. HelmRelease 定义

```yaml
# flux/helmrelease.yaml
apiVersion: helm.toolkit.fluxcd.io/v2beta1
kind: HelmRelease
metadata:
  name: rust-otlp-service
  namespace: production
spec:
  interval: 5m
  chart:
    spec:
      chart: rust-otlp-service
      version: '1.0.x'
      sourceRef:
        kind: HelmRepository
        name: my-charts
        namespace: flux-system
      interval: 1m
  
  values:
    replicaCount: 3
    image:
      repository: myregistry/rust-otlp-service
      tag: 1.0.0
    
    otlp:
      enabled: true
      endpoint: "http://otel-collector:4317"
  
  install:
    remediation:
      retries: 3
  
  upgrade:
    remediation:
      retries: 3
      remediateLastFailure: true
  
  rollback:
    cleanupOnFail: true
  
  test:
    enable: true
  
  postRenderers:
    - kustomize:
        patches:
          - target:
              kind: Deployment
            patch: |
              - op: add
                path: /spec/template/metadata/labels/deployed-by
                value: flux
```

### 3. Kustomization

```yaml
# flux/kustomization.yaml
apiVersion: kustomize.toolkit.fluxcd.io/v1
kind: Kustomization
metadata:
  name: rust-otlp-service
  namespace: flux-system
spec:
  interval: 10m
  sourceRef:
    kind: GitRepository
    name: fleet-infra
  path: ./apps/rust-otlp-service/production
  prune: true
  wait: true
  timeout: 5m
  
  healthChecks:
    - apiVersion: apps/v1
      kind: Deployment
      name: rust-otlp-service
      namespace: production
  
  postBuild:
    substitute:
      IMAGE_TAG: "1.0.0"
      ENVIRONMENT: "production"
```

### 4. Image Automation

```yaml
# flux/image-automation.yaml
apiVersion: image.toolkit.fluxcd.io/v1beta2
kind: ImageRepository
metadata:
  name: rust-otlp-service
  namespace: flux-system
spec:
  image: myregistry/rust-otlp-service
  interval: 1m

---
apiVersion: image.toolkit.fluxcd.io/v1beta2
kind: ImagePolicy
metadata:
  name: rust-otlp-service
  namespace: flux-system
spec:
  imageRepositoryRef:
    name: rust-otlp-service
  policy:
    semver:
      range: 1.0.x

---
apiVersion: image.toolkit.fluxcd.io/v1beta1
kind: ImageUpdateAutomation
metadata:
  name: rust-otlp-service
  namespace: flux-system
spec:
  interval: 1m
  sourceRef:
    kind: GitRepository
    name: fleet-infra
  git:
    checkout:
      ref:
        branch: main
    commit:
      author:
        email: fluxcdbot@example.com
        name: Flux CD Bot
      messageTemplate: |
        Update {{range .Updated.Images}}{{println .}}{{end}}
    push:
      branch: main
  update:
    path: ./apps/rust-otlp-service
    strategy: Setters
```

---

## OTLP 配置管理

### 1. OpenTelemetry Operator

```bash
# 安装 OpenTelemetry Operator
kubectl apply -f https://github.com/open-telemetry/opentelemetry-operator/releases/latest/download/opentelemetry-operator.yaml
```

### 2. OpenTelemetry Collector

```yaml
# otlp/collector.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: otel-collector
  namespace: observability
spec:
  mode: deployment
  replicas: 3
  
  config: |
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
      
      k8sattributes:
        auth_type: "serviceAccount"
        passthrough: false
        extract:
          metadata:
            - k8s.namespace.name
            - k8s.deployment.name
            - k8s.pod.name
            - k8s.pod.uid
    
    exporters:
      otlp/jaeger:
        endpoint: jaeger-collector:4317
        tls:
          insecure: true
      
      prometheusremotewrite:
        endpoint: http://prometheus:9090/api/v1/write
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [k8sattributes, batch]
          exporters: [otlp/jaeger]
        metrics:
          receivers: [otlp]
          processors: [k8sattributes, batch]
          exporters: [prometheusremotewrite]
```

### 3. 自动注入

```yaml
# otlp/instrumentation.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: Instrumentation
metadata:
  name: rust-otlp-instrumentation
  namespace: production
spec:
  exporter:
    endpoint: http://otel-collector:4317
  
  propagators:
    - tracecontext
    - baggage
  
  sampler:
    type: parentbased_traceidratio
    argument: "0.1"  # 10% 采样
  
  env:
    - name: OTEL_SERVICE_NAME
      valueFrom:
        fieldRef:
          fieldPath: metadata.labels['app.kubernetes.io/name']
    - name: OTEL_RESOURCE_ATTRIBUTES_POD_NAME
      valueFrom:
        fieldRef:
          fieldPath: metadata.name
    - name: OTEL_RESOURCE_ATTRIBUTES_NODE_NAME
      valueFrom:
        fieldRef:
          fieldPath: spec.nodeName
```

使用自动注入:

```yaml
# 在 Pod 中添加 annotation
apiVersion: apps/v1
kind: Deployment
spec:
  template:
    metadata:
      annotations:
        instrumentation.opentelemetry.io/inject-sdk: "rust-otlp-instrumentation"
```

---

## CI/CD 流水线

### 1. GitHub Actions

```yaml
# .github/workflows/deploy.yml
name: Build and Deploy

on:
  push:
    branches: [ main ]
    tags: [ 'v*' ]

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  build:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      packages: write
    
    steps:
      - name: Checkout
        uses: actions/checkout@v4
      
      - name: Set up Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          profile: minimal
      
      - name: Cache
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/bin/
            ~/.cargo/registry/index/
            ~/.cargo/registry/cache/
            ~/.cargo/git/db/
            target/
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Build
        run: cargo build --release
      
      - name: Test
        run: cargo test --release
      
      - name: Docker meta
        id: meta
        uses: docker/metadata-action@v5
        with:
          images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
          tags: |
            type=ref,event=branch
            type=ref,event=pr
            type=semver,pattern={{version}}
            type=semver,pattern={{major}}.{{minor}}
            type=sha,prefix={{branch}}-
      
      - name: Login to Registry
        uses: docker/login-action@v3
        with:
          registry: ${{ env.REGISTRY }}
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}
      
      - name: Build and push
        uses: docker/build-push-action@v5
        with:
          context: .
          push: true
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
  
  update-helm:
    needs: build
    runs-on: ubuntu-latest
    if: startsWith(github.ref, 'refs/tags/v')
    
    steps:
      - name: Checkout helm-charts
        uses: actions/checkout@v4
        with:
          repository: myorg/helm-charts
          token: ${{ secrets.HELM_CHARTS_TOKEN }}
      
      - name: Update Chart version
        run: |
          VERSION=${GITHUB_REF#refs/tags/v}
          sed -i "s/version: .*/version: $VERSION/" charts/rust-otlp-service/Chart.yaml
          sed -i "s/appVersion: .*/appVersion: \"$VERSION\"/" charts/rust-otlp-service/Chart.yaml
      
      - name: Commit and push
        run: |
          git config user.name "GitHub Actions"
          git config user.email "actions@github.com"
          git add charts/rust-otlp-service/Chart.yaml
          git commit -m "Update rust-otlp-service to ${GITHUB_REF#refs/tags/v}"
          git push
```

### 2. 镜像构建

```dockerfile
# Dockerfile (多阶段构建)
FROM rust:1.90-alpine AS builder

WORKDIR /app

RUN apk add --no-cache musl-dev openssl-dev

COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

# 运行时镜像
FROM alpine:latest

RUN apk add --no-cache ca-certificates

COPY --from=builder /app/target/release/rust-otlp-service /usr/local/bin/

USER 1000:1000

EXPOSE 8080

ENTRYPOINT ["/usr/local/bin/rust-otlp-service"]
```

### 3. Helm Chart 发布

```bash
# 打包 Helm Chart
helm package charts/rust-otlp-service

# 上传到 Chart Repository (示例: Harbor)
helm push rust-otlp-service-1.0.0.tgz oci://harbor.example.com/charts

# 或使用 GitHub Pages
helm repo index . --url https://myorg.github.io/helm-charts
git add .
git commit -m "Release charts"
git push
```

---

## 高级特性

### 1. Helm Hooks

```yaml
# templates/pre-upgrade-job.yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: "{{ .Release.Name }}-pre-upgrade"
  annotations:
    "helm.sh/hook": pre-upgrade
    "helm.sh/hook-weight": "-5"
    "helm.sh/hook-delete-policy": before-hook-creation,hook-succeeded
spec:
  template:
    spec:
      restartPolicy: Never
      containers:
      - name: db-migrate
        image: "{{ .Values.image.repository }}:{{ .Values.image.tag }}"
        command: ["/usr/local/bin/migrate"]
        args: ["up"]
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-secret
              key: url
```

### 2. 蓝绿部署

```yaml
# Blue-Green Deployment with ArgoCD
apiVersion: argoproj.io/v1alpha1
kind: Rollout
metadata:
  name: rust-otlp-service
spec:
  replicas: 3
  strategy:
    blueGreen:
      activeService: rust-otlp-service
      previewService: rust-otlp-service-preview
      autoPromotionEnabled: false
      scaleDownDelaySeconds: 30
  
  selector:
    matchLabels:
      app: rust-otlp-service
  
  template:
    metadata:
      labels:
        app: rust-otlp-service
    spec:
      containers:
      - name: rust-otlp-service
        image: myregistry/rust-otlp-service:1.0.0
```

### 3. 回滚策略

```bash
# Helm 回滚
helm rollback rust-otlp-service 0

# ArgoCD 回滚
argocd app rollback rust-otlp-service

# Flux 回滚
flux suspend helmrelease rust-otlp-service
kubectl -n production rollout undo deployment/rust-otlp-service
flux resume helmrelease rust-otlp-service
```

---

## 监控与告警

### 1. ArgoCD Metrics

```promql
# 部署成功率
sum(rate(argocd_app_sync_total{phase="Succeeded"}[5m])) /
sum(rate(argocd_app_sync_total[5m])) * 100

# 平均同步时间
rate(argocd_app_sync_duration_seconds_sum[5m]) /
rate(argocd_app_sync_duration_seconds_count[5m])

# 应用健康状态
sum(argocd_app_info{health_status="Healthy"}) by (name, namespace)
```

### 2. 部署事件追踪

```rust
// src/telemetry.rs
use opentelemetry::trace::{Span, Tracer};

pub async fn trace_deployment_event(
    version: &str,
    environment: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = opentelemetry::global::tracer("deployment");
    
    let mut span = tracer.span_builder("deployment")
        .with_kind(opentelemetry::trace::SpanKind::Internal)
        .start(&tracer);
    
    span.set_attribute(opentelemetry::KeyValue::new("deployment.version", version.to_string()));
    span.set_attribute(opentelemetry::KeyValue::new("deployment.environment", environment.to_string()));
    span.add_event("deployment_started", vec![]);
    
    // 部署逻辑...
    
    span.add_event("deployment_completed", vec![]);
    span.end();
    
    Ok(())
}
```

---

## 最佳实践

### 1. Chart 版本管理

```yaml
# 使用语义化版本
Chart.yaml:
  version: 1.2.3  # Chart 版本
  appVersion: 1.2.3  # 应用版本

# Chart 版本变更规则:
# - MAJOR: 不兼容的 API 变更
# - MINOR: 向后兼容的功能新增
# - PATCH: 向后兼容的问题修正
```

### 2. 密钥管理

```bash
# 使用 Sealed Secrets
kubectl create secret generic db-secret \
  --from-literal=username=admin \
  --from-literal=password=secretpass \
  --dry-run=client -o yaml | \
kubeseal -o yaml > sealed-secret.yaml

# 使用 External Secrets Operator
kubectl apply -f - <<EOF
apiVersion: external-secrets.io/v1beta1
kind: ExternalSecret
metadata:
  name: db-secret
spec:
  secretStoreRef:
    name: aws-secrets-manager
    kind: SecretStore
  target:
    name: db-secret
  data:
  - secretKey: username
    remoteRef:
      key: prod/db/username
  - secretKey: password
    remoteRef:
      key: prod/db/password
EOF
```

### 3. 多租户隔离

```yaml
# AppProject for multi-tenancy
apiVersion: argoproj.io/v1alpha1
kind: AppProject
metadata:
  name: team-a
  namespace: argocd
spec:
  sourceRepos:
    - 'https://github.com/team-a/*'
  
  destinations:
    - namespace: team-a-*
      server: https://kubernetes.default.svc
  
  clusterResourceWhitelist:
    - group: ''
      kind: Namespace
  
  namespaceResourceBlacklist:
    - group: ''
      kind: ResourceQuota
    - group: ''
      kind: LimitRange
```

---

## 完整示例

### 1. Rust 微服务 Helm Chart

(见上文完整 Chart 结构)

### 2. GitOps Repository 结构

```text
fleet-infra/
├── clusters/
│   ├── development/
│   │   ├── flux-system/
│   │   └── apps/
│   │       └── rust-otlp-service/
│   ├── staging/
│   └── production/
├── apps/
│   └── rust-otlp-service/
│       ├── base/
│       │   ├── helmrelease.yaml
│       │   └── kustomization.yaml
│       ├── development/
│       │   ├── values.yaml
│       │   └── kustomization.yaml
│       ├── staging/
│       └── production/
└── infrastructure/
    ├── otel-collector/
    ├── prometheus/
    └── grafana/
```

### 3. 完整部署流程

```bash
# 1. 开发代码并提交
git add .
git commit -m "feat: add new endpoint"
git push

# 2. CI/CD 自动构建镜像
# GitHub Actions 自动触发

# 3. 更新 Helm Chart
git tag v1.1.0
git push --tags

# 4. GitOps 自动部署
# ArgoCD/Flux 检测到变更,自动同步

# 5. 验证部署
kubectl get pods -n production
helm list -n production

# 6. 监控追踪
# 访问 Kibana/Grafana 查看 OTLP 数据
```

---

## 总结

### 核心要点

1. **Helm**: 标准化 K8s 应用打包和部署
2. **GitOps**: Git 作为单一真实来源
3. **自动化**: CI/CD 流水线全自动部署
4. **可观测性**: OTLP 集成追踪部署全流程
5. **多环境**: 统一 Chart,环境差异化配置

### ArgoCD vs Flux

| 特性 | ArgoCD | Flux |
|-----|--------|------|
| **UI** | ✅ 强大的 Web UI | ❌ 无 UI |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **GitOps 能力** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **镜像自动更新** | ❌ | ✅ |
| **多租户** | ✅ AppProject | ⚠️ 需额外配置 |
| **学习曲线** | 平缓 | 陡峭 |
| **适用场景** | 企业级,多团队 | Cloud Native,自动化 |

### 下一步

- **Progressive Delivery**: 使用 Flagger 实现金丝雀/蓝绿部署
- **Policy as Code**: 集成 OPA/Kyverno
- **Cost Optimization**: Kubecost 成本分析
- **Disaster Recovery**: Velero 备份恢复

---

## 参考资料

- [Helm 官方文档](https://helm.sh/docs/)
- [ArgoCD 文档](https://argo-cd.readthedocs.io/)
- [Flux 文档](https://fluxcd.io/docs/)
- [OpenTelemetry Operator](https://github.com/open-telemetry/opentelemetry-operator)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Helm 版本**: 3.15+  
**ArgoCD 版本**: 2.11+  
**Flux 版本**: 2.3+  
**OpenTelemetry**: 0.30+
