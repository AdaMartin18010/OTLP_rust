# OTLP on Kubernetes with Istio/Envoy - 完整生产实践指南

> **版本**: v2.0  
> **状态**: ✅ 生产就绪  
> **最后更新**: 2025年10月17日

---

## 📋 目录

- [OTLP on Kubernetes with Istio/Envoy - 完整生产实践指南](#otlp-on-kubernetes-with-istioenvoy---完整生产实践指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
    - [核心目标](#核心目标)
    - [技术栈](#技术栈)
  - [🏗️ 架构设计](#️-架构设计)
    - [整体架构](#整体架构)
    - [数据流向](#数据流向)
  - [🚀 快速开始](#-快速开始)
    - [前置要求](#前置要求)
    - [1. 部署OpenTelemetry Collector](#1-部署opentelemetry-collector)
    - [2. 启用Istio注入](#2-启用istio注入)
    - [3. 部署示例应用](#3-部署示例应用)
    - [4. 验证数据流](#4-验证数据流)
  - [📦 生产级部署](#-生产级部署)
    - [Helm Chart部署](#helm-chart部署)
    - [高可用配置](#高可用配置)
    - [HPA自动伸缩](#hpa自动伸缩)
  - [🌐 Istio/Envoy集成](#-istioenvoy集成)
    - [TraceContext传播](#tracecontext传播)
    - [VirtualService配置](#virtualservice配置)
    - [PeerAuthentication (mTLS)](#peerauthentication-mtls)
    - [DestinationRule配置](#destinationrule配置)
    - [Envoy Access Log](#envoy-access-log)
  - [🔒 安全加固](#-安全加固)
    - [mTLS配置](#mtls配置)
    - [认证策略](#认证策略)
    - [授权策略](#授权策略)
    - [网络策略](#网络策略)
  - [📊 监控和告警](#-监控和告警)
    - [Prometheus监控](#prometheus监控)
    - [Grafana仪表板](#grafana仪表板)
    - [告警规则](#告警规则)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [问题1: Collector无法接收数据](#问题1-collector无法接收数据)
      - [问题2: mTLS认证失败](#问题2-mtls认证失败)
    - [诊断工具](#诊断工具)
    - [日志分析](#日志分析)
  - [⚡ 性能优化](#-性能优化)
    - [Collector优化](#collector优化)
    - [Envoy优化](#envoy优化)
    - [网络优化](#网络优化)
  - [📚 完整配置示例](#-完整配置示例)
    - [基础部署](#基础部署)
    - [Helm Values](#helm-values)
  - [🧪 测试验证](#-测试验证)
    - [功能测试](#功能测试)
    - [性能测试](#性能测试)
    - [混沌测试](#混沌测试)
  - [📝 运维手册](#-运维手册)
    - [日常运维](#日常运维)
    - [故障恢复](#故障恢复)
    - [升级流程](#升级流程)
  - [📚 相关资源](#-相关资源)
  - [📅 变更历史](#-变更历史)

---

## 📋 概述

### 核心目标

1. ✅ 在Kubernetes中部署生产级OpenTelemetry Collector
2. ✅ 集成Istio服务网格实现流量治理
3. ✅ 通过Envoy Sidecar实现统一可观测性
4. ✅ 使用OTLP协议传输Traces/Metrics/Logs
5. ✅ 实现安全、高可用、可扩展的可观测性平台

### 技术栈

| 组件 | 版本 | 用途 |
|------|------|------|
| Kubernetes | v1.28+ | 容器编排平台 |
| Istio | v1.20+ | 服务网格 |
| OpenTelemetry Collector | v0.95+ | 遥测数据收集 |
| Envoy | v1.29+ | Service Proxy |
| Prometheus | v2.49+ | 指标存储 |
| Jaeger | v1.54+ | 追踪后端 |
| Grafana | v10.3+ | 可视化 |

---

## 🏗️ 架构设计

### 整体架构

```text
┌─────────────────────────────────────────────────────────────┐
│                    Kubernetes Cluster                        │
│                                                              │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Namespace: observability                │   │
│  │                                                      │   │
│  │  ┌──────────────────────────────────────────────┐  │   │
│  │  │      OpenTelemetry Collector (DaemonSet)     │  │   │
│  │  │  ┌─────────────┐  ┌─────────────┐           │  │   │
│  │  │  │  Receivers  │  │ Processors  │           │  │   │
│  │  │  │  • OTLP     │→│ • Batch     │→Exporters │  │   │
│  │  │  │  • Jaeger   │  │ • Filter    │           │  │   │
│  │  │  └─────────────┘  └─────────────┘           │  │   │
│  │  └──────────────────────────────────────────────┘  │   │
│  │           ↓           ↓           ↓                 │   │
│  │    ┌──────────┐ ┌──────────┐ ┌──────────┐         │   │
│  │    │ Jaeger   │ │Prometheus│ │  Loki    │         │   │
│  │    └──────────┘ └──────────┘ └──────────┘         │   │
│  └─────────────────────────────────────────────────────┘   │
│                           ↑                                  │
│  ┌─────────────────────────────────────────────────────┐   │
│  │           Namespace: default (with Istio)            │   │
│  │                                                      │   │
│  │  ┌────────────────────────────────────────────┐    │   │
│  │  │           Application Pod                   │    │   │
│  │  │  ┌──────────────┐    ┌──────────────┐     │    │   │
│  │  │  │ Application  │    │ Envoy Proxy  │     │    │   │
│  │  │  │  Container   │←──→│  (Sidecar)   │     │    │   │
│  │  │  │              │    │              │     │    │   │
│  │  │  │ OTLP Export  │    │ TraceContext │     │    │   │
│  │  │  │   ↓          │    │ Propagation  │     │    │   │
│  │  │  └──────────────┘    └──────────────┘     │    │   │
│  │  └────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 数据流向

```text
Application → Envoy Sidecar → OTLP Collector → Backend
     │            │                  │              │
     │            │                  │              ├─→ Jaeger (Traces)
     │            │                  │              ├─→ Prometheus (Metrics)
     │            │                  │              └─→ Loki (Logs)
     │            │                  │
     │            │                  └─→ Batch Processing
     │            │                       • Filtering
     │            │                       • Sampling
     │            │                       • Enrichment
     │            │
     │            └─→ TraceContext Propagation
     │                • traceparent
     │                • b3 headers
     │
     └─→ OTLP/gRPC or OTLP/HTTP
         • Traces
         • Metrics
         • Logs
```

---

## 🚀 快速开始

### 前置要求

```bash
# 1. Kubernetes集群（v1.28+）
kubectl version --client

# 2. Istio安装（v1.20+）
istioctl version

# 3. Helm（v3.12+）
helm version

# 4. 可访问的容器registry
# 例如：docker.io, gcr.io, 或私有registry
```

### 1. 部署OpenTelemetry Collector

**创建命名空间**:

```bash
kubectl create namespace observability
```

**部署Collector (DaemonSet模式)**:

```yaml
# otel-collector.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: observability
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: observability
data:
  otel-collector-config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
            cors:
              allowed_origins:
                - "*"
      
      # Kubernetes集群指标
      k8s_cluster:
        auth_type: serviceAccount
        node_conditions_to_report: [Ready, MemoryPressure, DiskPressure]
      
      # Kubelet指标
      kubeletstats:
        collection_interval: 30s
        auth_type: serviceAccount
        endpoint: "${K8S_NODE_NAME}:10250"
        insecure_skip_verify: true
    
    processors:
      # 批处理
      batch:
        timeout: 10s
        send_batch_size: 1024
      
      # 内存限制
      memory_limiter:
        check_interval: 1s
        limit_mib: 512
        spike_limit_mib: 128
      
      # 资源检测
      resourcedetection/env:
        detectors: [env, system]
        timeout: 2s
      
      # Kubernetes属性
      k8sattributes:
        auth_type: serviceAccount
        passthrough: false
        extract:
          metadata:
            - k8s.namespace.name
            - k8s.deployment.name
            - k8s.pod.name
            - k8s.pod.uid
            - k8s.node.name
          labels:
            - tag_name: app
              key: app
              from: pod
      
      # 采样
      probabilistic_sampler:
        hash_seed: 22
        sampling_percentage: 10
    
    exporters:
      # 日志导出（调试）
      logging:
        loglevel: info
        sampling_initial: 5
        sampling_thereafter: 200
      
      # Jaeger导出
      otlp/jaeger:
        endpoint: jaeger-collector.observability.svc.cluster.local:4317
        tls:
          insecure: true
      
      # Prometheus导出
      prometheusremotewrite:
        endpoint: http://prometheus.observability.svc.cluster.local:9090/api/v1/write
        tls:
          insecure: true
      
      # Loki导出
      loki:
        endpoint: http://loki.observability.svc.cluster.local:3100/loki/api/v1/push
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resourcedetection/env, probabilistic_sampler, batch]
          exporters: [logging, otlp/jaeger]
        
        metrics:
          receivers: [otlp, k8s_cluster, kubeletstats]
          processors: [memory_limiter, k8sattributes, resourcedetection/env, batch]
          exporters: [logging, prometheusremotewrite]
        
        logs:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resourcedetection/env, batch]
          exporters: [logging, loki]
      
      telemetry:
        logs:
          level: info
        metrics:
          address: :8888
---
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: observability
  labels:
    app: otel-collector
spec:
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      serviceAccountName: otel-collector
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-k8s:0.95.0
        command:
          - "/otelcol-k8s"
          - "--config=/conf/otel-collector-config.yaml"
          ports:
        - name: otlp-grpc
          containerPort: 4317
          protocol: TCP
        - name: otlp-http
          containerPort: 4318
          protocol: TCP
        - name: metrics
          containerPort: 8888
          protocol: TCP
        env:
        - name: K8S_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        - name: K8S_POD_IP
          valueFrom:
            fieldRef:
              fieldPath: status.podIP
          volumeMounts:
        - name: otel-collector-config-vol
          mountPath: /conf
        resources:
          limits:
            cpu: 500m
            memory: 1Gi
          requests:
            cpu: 200m
            memory: 512Mi
        livenessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 10
          periodSeconds: 5
      volumes:
      - name: otel-collector-config-vol
          configMap:
          name: otel-collector-config
          items:
          - key: otel-collector-config.yaml
            path: otel-collector-config.yaml
---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
  labels:
    app: otel-collector
spec:
  type: ClusterIP
  selector:
    app: otel-collector
  ports:
  - name: otlp-grpc
      port: 4317
      targetPort: 4317
    protocol: TCP
  - name: otlp-http
      port: 4318
      targetPort: 4318
    protocol: TCP
  - name: metrics
    port: 8888
    targetPort: 8888
    protocol: TCP
---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: otel-collector
rules:
- apiGroups: [""]
  resources:
  - nodes
  - nodes/proxy
  - nodes/stats
  - services
  - endpoints
  - pods
  - events
  - namespaces
  verbs: ["get", "list", "watch"]
- apiGroups: ["apps"]
  resources:
  - replicasets
  - deployments
  - daemonsets
  - statefulsets
  verbs: ["get", "list", "watch"]
- apiGroups: ["batch"]
  resources:
  - jobs
  - cronjobs
  verbs: ["get", "list", "watch"]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: otel-collector
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: otel-collector
subjects:
- kind: ServiceAccount
  name: otel-collector
  namespace: observability
```

**应用配置**:

```bash
kubectl apply -f otel-collector.yaml

# 验证部署
kubectl get pods -n observability
kubectl logs -n observability -l app=otel-collector --tail=50
```

### 2. 启用Istio注入

```bash
# 为default命名空间启用Istio sidecar注入
kubectl label namespace default istio-injection=enabled

# 验证
kubectl get namespace default --show-labels
```

### 3. 部署示例应用

```yaml
# demo-app.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-demo
  namespace: default
spec:
  replicas: 2
  selector:
    matchLabels:
      app: otlp-demo
      version: v1
  template:
    metadata:
      labels:
        app: otlp-demo
        version: v1
    spec:
      containers:
        - name: app
          image: your-registry/otlp-demo:latest
        ports:
        - containerPort: 8080
          env:
            - name: OTLP_ENDPOINT
          value: "http://otel-collector.observability.svc.cluster.local:4318"
            - name: OTLP_PROTOCOL
          value: "http"
        - name: SERVICE_NAME
          value: "otlp-demo"
        - name: SERVICE_VERSION
          value: "v1"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector.observability.svc.cluster.local:4318"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "service.name=otlp-demo,service.version=v1,deployment.environment=production"
        resources:
          limits:
            cpu: 200m
            memory: 256Mi
          requests:
            cpu: 100m
            memory: 128Mi
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-demo
  namespace: default
spec:
  selector:
    app: otlp-demo
  ports:
  - port: 8080
    targetPort: 8080
    name: http
```

**应用配置**:

```bash
kubectl apply -f demo-app.yaml

# 验证Istio sidecar注入
kubectl get pods -l app=otlp-demo
# 应该看到2/2 READY（app + envoy）

# 检查sidecar
kubectl describe pod -l app=otlp-demo | grep -A 5 "istio-proxy"
```

### 4. 验证数据流

```bash
# 1. 检查Collector是否接收数据
kubectl logs -n observability -l app=otel-collector --tail=100 | grep "TracesExporter"

# 2. 生成测试流量
kubectl run -it --rm debug --image=curlimages/curl --restart=Never -- \
  curl -X POST http://otlp-demo.default.svc.cluster.local:8080/api/test

# 3. 检查Jaeger UI
kubectl port-forward -n observability svc/jaeger-query 16686:16686

# 4. 检查Prometheus指标
kubectl port-forward -n observability svc/prometheus 9090:9090

# 访问 http://localhost:16686 查看traces
# 访问 http://localhost:9090 查询metrics
```

---

## 📦 生产级部署

### Helm Chart部署

**Chart结构**:

```text
otlp-chart/
├── Chart.yaml
├── values.yaml
├── templates/
│   ├── collector-daemonset.yaml
│   ├── collector-service.yaml
│   ├── collector-configmap.yaml
│   ├── collector-serviceaccount.yaml
│   ├── collector-clusterrole.yaml
│   ├── collector-clusterrolebinding.yaml
│   ├── hpa.yaml
│   ├── pdb.yaml
│   ├── servicemonitor.yaml
│   └── NOTES.txt
└── README.md
```

**安装命令**:

```bash
# 添加Helm repo
helm repo add opentelemetry https://open-telemetry.github.io/opentelemetry-helm-charts
helm repo update

# 安装Collector
helm install otel-collector opentelemetry/opentelemetry-collector \
  --namespace observability \
  --create-namespace \
  --values values-production.yaml

# 或使用本地chart
helm install otel-collector ./otlp-chart \
  --namespace observability \
  --create-namespace \
  --values values-production.yaml
```

### 高可用配置

```yaml
# values-production.yaml
replicaCount: 3

mode: deployment  # 使用Deployment而非DaemonSet

podDisruptionBudget:
  enabled: true
  minAvailable: 2

affinity:
  podAntiAffinity:
    preferredDuringSchedulingIgnoredDuringExecution:
    - weight: 100
      podAffinityTerm:
        labelSelector:
          matchExpressions:
          - key: app
            operator: In
            values:
            - otel-collector
        topologyKey: kubernetes.io/hostname

resources:
  limits:
    cpu: 1000m
    memory: 2Gi
  requests:
    cpu: 500m
    memory: 1Gi

persistence:
  enabled: true
  storageClass: "fast-ssd"
  size: 10Gi
```

### HPA自动伸缩

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  - type: Pods
    pods:
      metric:
        name: otelcol_receiver_accepted_spans
      target:
        type: AverageValue
        averageValue: "1000"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15
      - type: Pods
        value: 2
        periodSeconds: 15
      selectPolicy: Max
```

---

## 🌐 Istio/Envoy集成

### TraceContext传播

**Envoy配置（通过Istio注入）**:

```yaml
# istio-telemetry.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: mesh-default
  namespace: istio-system
spec:
  tracing:
  - providers:
    - name: otlp
    randomSamplingPercentage: 10.0
    customTags:
      environment:
        literal:
          value: production
      version:
        header:
          name: x-app-version
          defaultValue: unknown
---
apiVersion: install.istio.io/v1alpha1
kind: IstioOperator
metadata:
  name: istio-install
  namespace: istio-system
spec:
  meshConfig:
    defaultConfig:
      tracing:
        tlsSettings:
          mode: DISABLE
        zipkin:
          address: otel-collector.observability.svc.cluster.local:9411
        sampling: 10.0
        custom_tags:
          environment:
            literal:
              value: production
    enableTracing: true
    extensionProviders:
    - name: otlp
      envoyOtelAls:
        service: otel-collector.observability.svc.cluster.local
        port: 4317
```

**应用配置**:

```bash
kubectl apply -f istio-telemetry.yaml

# 重启Envoy sidecars以应用新配置
kubectl rollout restart deployment -n default
```

### VirtualService配置

```yaml
# virtualservice.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: otel-collector
  namespace: observability
spec:
  hosts:
  - otel-collector.observability.svc.cluster.local
  http:
  - match:
    - uri:
        prefix: /v1/traces
    route:
    - destination:
        host: otel-collector.observability.svc.cluster.local
        port:
          number: 4318
      weight: 100
    timeout: 10s
    retries:
      attempts: 3
      perTryTimeout: 2s
      retryOn: 5xx,reset,connect-failure,refused-stream
  - match:
    - uri:
        prefix: /v1/metrics
    route:
    - destination:
        host: otel-collector.observability.svc.cluster.local
        port:
          number: 4318
      weight: 100
    timeout: 5s
  - match:
    - uri:
        prefix: /v1/logs
    route:
    - destination:
        host: otel-collector.observability.svc.cluster.local
        port:
          number: 4318
      weight: 100
    timeout: 5s
  tcp:
  - match:
    - port: 4317
    route:
    - destination:
        host: otel-collector.observability.svc.cluster.local
        port:
          number: 4317
```

### PeerAuthentication (mTLS)

```yaml
# peerauthentication.yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
  namespace: observability
spec:
  mtls:
    mode: STRICT
---
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: otel-collector-mtls
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  mtls:
    mode: PERMISSIVE  # 允许mTLS和plaintext
  portLevelMtls:
    4317:
      mode: PERMISSIVE  # gRPC port
    4318:
      mode: PERMISSIVE  # HTTP port
```

### DestinationRule配置

```yaml
# destinationrule.yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: otel-collector
  namespace: observability
spec:
  host: otel-collector.observability.svc.cluster.local
  trafficPolicy:
    tls:
      mode: ISTIO_MUTUAL
    connectionPool:
      tcp:
        maxConnections: 100
        connectTimeout: 3s
      http:
        http1MaxPendingRequests: 1024
        http2MaxRequests: 1024
        maxRequestsPerConnection: 100
        maxRetries: 3
    loadBalancer:
      simple: LEAST_REQUEST
      localityLbSetting:
        enabled: true
        distribute:
        - from: us-west-1
          to:
            us-west-1: 80
            us-east-1: 20
    outlierDetection:
      consecutive5xxErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
      minHealthPercent: 50
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2
```

### Envoy Access Log

```yaml
# envoy-filter.yaml
apiVersion: networking.istio.io/v1alpha3
kind: EnvoyFilter
metadata:
  name: otel-access-log
  namespace: istio-system
spec:
  configPatches:
  - applyTo: NETWORK_FILTER
    match:
      context: ANY
      listener:
        filterChain:
          filter:
            name: envoy.filters.network.http_connection_manager
    patch:
      operation: MERGE
      value:
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          access_log:
          - name: envoy.access_loggers.open_telemetry
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.access_loggers.open_telemetry.v3.OpenTelemetryAccessLogConfig
              common_config:
                log_name: otel_envoy_accesslog
                transport_api_version: V3
                grpc_service:
                  envoy_grpc:
                    cluster_name: outbound|4317||otel-collector.observability.svc.cluster.local
              body:
                string_value: |
                  {
                    "start_time": "%START_TIME%",
                    "method": "%REQ(:METHOD)%",
                    "path": "%REQ(X-ENVOY-ORIGINAL-PATH?:PATH)%",
                    "protocol": "%PROTOCOL%",
                    "response_code": "%RESPONSE_CODE%",
                    "bytes_sent": "%BYTES_SENT%",
                    "duration": "%DURATION%",
                    "trace_id": "%REQ(X-B3-TRACEID)%",
                    "span_id": "%REQ(X-B3-SPANID)%"
                  }
```

---

## 🔒 安全加固

### mTLS配置

```yaml
# mtls-strict.yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: strict-mtls
  namespace: observability
spec:
  mtls:
    mode: STRICT
```

### 认证策略

```yaml
# requestauthentication.yaml
apiVersion: security.istio.io/v1beta1
kind: RequestAuthentication
metadata:
  name: jwt-auth
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  jwtRules:
  - issuer: "https://your-issuer.com"
    jwksUri: "https://your-issuer.com/.well-known/jwks.json"
    audiences:
    - "otel-collector"
    forwardOriginalToken: true
```

### 授权策略

```yaml
# authorizationpolicy.yaml
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: otel-collector-authz
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  action: ALLOW
  rules:
  # 允许来自同一命名空间的请求
  - from:
    - source:
        namespaces: ["observability"]
    to:
    - operation:
        ports: ["4317", "4318"]
  # 允许来自default命名空间的应用
  - from:
    - source:
        namespaces: ["default"]
        principals: ["cluster.local/ns/default/sa/otlp-demo"]
    to:
    - operation:
        methods: ["POST"]
        paths: ["/v1/traces", "/v1/metrics", "/v1/logs"]
```

### 网络策略

```yaml
# networkpolicy.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otel-collector-netpol
  namespace: observability
spec:
  podSelector:
    matchLabels:
      app: otel-collector
  policyTypes:
  - Ingress
  - Egress
  ingress:
  # 允许来自应用的OTLP流量
  - from:
    - namespaceSelector:
        matchLabels:
          name: default
    ports:
    - protocol: TCP
      port: 4317
    - protocol: TCP
      port: 4318
  # 允许Prometheus scrape
  - from:
    - namespaceSelector:
        matchLabels:
          name: observability
      podSelector:
        matchLabels:
          app: prometheus
    ports:
    - protocol: TCP
      port: 8888
  egress:
  # 允许访问Jaeger
  - to:
    - podSelector:
        matchLabels:
          app: jaeger
    ports:
    - protocol: TCP
      port: 4317
  # 允许访问Prometheus
  - to:
    - podSelector:
        matchLabels:
          app: prometheus
    ports:
    - protocol: TCP
      port: 9090
  # 允许DNS查询
  - to:
    - namespaceSelector: {}
      podSelector:
        matchLabels:
          k8s-app: kube-dns
    ports:
    - protocol: UDP
      port: 53
```

---

## 📊 监控和告警

### Prometheus监控

```yaml
# servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  endpoints:
  - port: metrics
    interval: 30s
    path: /metrics
```

**关键指标**:

```promql
# Collector接收速率
rate(otelcol_receiver_accepted_spans[5m])

# Collector导出速率
rate(otelcol_exporter_sent_spans[5m])

# 失败率
rate(otelcol_exporter_send_failed_spans[5m]) / rate(otelcol_exporter_sent_spans[5m])

# 队列大小
otelcol_exporter_queue_size

# 内存使用
process_resident_memory_bytes{job="otel-collector"}

# CPU使用
rate(process_cpu_seconds_total{job="otel-collector"}[5m])
```

### Grafana仪表板

**导入仪表板**:

```bash
# 官方仪表板ID: 15983
# 或使用自定义仪表板
kubectl apply -f dashboards/otel-collector-dashboard.json
```

### 告警规则

```yaml
# prometheusrule.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: otel-collector-alerts
  namespace: observability
spec:
  groups:
  - name: otel-collector
    interval: 30s
    rules:
    - alert: OTLPCollectorDown
      expr: up{job="otel-collector"} == 0
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "OTLP Collector实例宕机"
        description: "Collector {{ $labels.instance }} 已宕机超过5分钟"
    
    - alert: OTLPCollectorHighErrorRate
      expr: |
        rate(otelcol_exporter_send_failed_spans[5m]) /
        rate(otelcol_exporter_sent_spans[5m]) > 0.05
      for: 10m
      labels:
        severity: warning
      annotations:
        summary: "OTLP Collector错误率过高"
        description: "错误率: {{ $value | humanizePercentage }}"
    
    - alert: OTLPCollectorHighMemory
      expr: |
        process_resident_memory_bytes{job="otel-collector"} /
        on(pod) container_spec_memory_limit_bytes{container="otel-collector"} > 0.9
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "OTLP Collector内存使用过高"
        description: "内存使用: {{ $value | humanizePercentage }}"
    
    - alert: OTLPCollectorQueueBacklog
      expr: otelcol_exporter_queue_size > 1000
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "OTLP Collector队列积压"
        description: "队列大小: {{ $value }}"
```

---

## 🔍 故障排查

### 常见问题

#### 问题1: Collector无法接收数据

**症状**:

- 应用日志显示OTLP发送失败
- Collector日志无incoming traces

**诊断**:

```bash
# 1. 检查Collector日志
kubectl logs -n observability -l app=otel-collector --tail=100

# 2. 检查Service是否正常
kubectl get svc -n observability otel-collector
kubectl get endpoints -n observability otel-collector

# 3. 测试连通性
kubectl run -it --rm debug --image=curlimages/curl --restart=Never -- \
  curl -v http://otel-collector.observability.svc.cluster.local:4318/v1/traces

# 4. 检查NetworkPolicy
kubectl get networkpolicy -n observability
```

**解决方案**:

- 确认端口配置正确（4317 gRPC, 4318 HTTP）
- 检查NetworkPolicy是否阻止流量
- 验证DNS解析正常
- 检查Istio sidecar是否正确注入

#### 问题2: mTLS认证失败

**症状**:

- 503 Service Unavailable
- Envoy日志显示TLS handshake failed

**诊断**:

```bash
# 检查mTLS状态
istioctl x describe pod <pod-name> -n <namespace>

# 检查PeerAuthentication
kubectl get peerauthentication -A

# 检查证书
kubectl exec -it <pod-name> -c istio-proxy -n <namespace> -- \
  cat /etc/certs/cert-chain.pem | openssl x509 -text -noout
```

**解决方案**:

- 确认PeerAuthentication配置为PERMISSIVE或STRICT
- 检查证书有效期
- 验证Istio控制平面正常
- 确认所有pod都注入了sidecar

### 诊断工具

```bash
# 1. Istioctl分析
istioctl analyze -n observability

# 2. Envoy配置dump
kubectl exec -it <pod-name> -c istio-proxy -n <namespace> -- \
  curl localhost:15000/config_dump > envoy-config.json

# 3. 查看Envoy访问日志
kubectl logs <pod-name> -c istio-proxy -n <namespace> --tail=100

# 4. 实时监控Collector指标
kubectl port-forward -n observability svc/otel-collector 8888:8888
# 访问 http://localhost:8888/metrics

# 5. 测试gRPC连接
grpcurl -plaintext \
  otel-collector.observability.svc.cluster.local:4317 \
  list
```

### 日志分析

```bash
# 查找错误
kubectl logs -n observability -l app=otel-collector \
  --tail=1000 | grep -i error

# 分析拒绝原因
kubectl logs -n observability -l app=otel-collector \
  --tail=1000 | grep "refused\|rejected\|denied"

# 查看采样情况
kubectl logs -n observability -l app=otel-collector \
  --tail=1000 | grep "sampled"

# 分析性能
kubectl logs -n observability -l app=otel-collector \
  --tail=1000 | grep "duration\|latency"
```

---

## ⚡ 性能优化

### Collector优化

```yaml
# 优化的Collector配置
processors:
  batch:
    timeout: 5s                    # 降低延迟
    send_batch_size: 2048          # 增加批大小
    send_batch_max_size: 4096
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048                # 增加内存限制
    spike_limit_mib: 512
  
  # 仅处理必要的属性
  resource:
    attributes:
    - key: unnecessary_attribute
      action: delete

resources:
  limits:
    cpu: 2000m                     # 增加CPU
    memory: 4Gi                    # 增加内存
  requests:
    cpu: 1000m
    memory: 2Gi
```

### Envoy优化

```yaml
# Envoy资源优化
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-sidecar-injector
  namespace: istio-system
data:
  values: |
    global:
      proxy:
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 2000m
            memory: 1024Mi
        concurrency: 2             # CPU核心数
```

### 网络优化

```yaml
# 使用NodePort或LoadBalancer暴露Collector
apiVersion: v1
kind: Service
metadata:
  name: otel-collector-external
  namespace: observability
spec:
  type: LoadBalancer
  selector:
    app: otel-collector
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
    protocol: TCP
  - name: otlp-http
    port: 4318
    targetPort: 4318
    protocol: TCP
  externalTrafficPolicy: Local     # 保留源IP
  sessionAffinity: ClientIP        # 会话亲和性
  sessionAffinityConfig:
    clientIP:
      timeoutSeconds: 10800
```

---

## 📚 完整配置示例

### 基础部署

参见上文"快速开始"部分的完整YAML配置。

### Helm Values

```yaml
# values-production.yaml
mode: daemonset

image:
  repository: otel/opentelemetry-collector-k8s
  tag: 0.95.0
  pullPolicy: IfNotPresent

replicaCount: 1

resources:
  limits:
    cpu: 1000m
    memory: 2Gi
  requests:
    cpu: 500m
    memory: 1Gi

podAnnotations:
  prometheus.io/scrape: "true"
  prometheus.io/port: "8888"
  prometheus.io/path: "/metrics"

service:
  type: ClusterIP
  ports:
    otlp-grpc:
      enabled: true
      containerPort: 4317
      servicePort: 4317
      protocol: TCP
    otlp-http:
      enabled: true
      containerPort: 4318
      servicePort: 4318
      protocol: TCP
    metrics:
      enabled: true
      containerPort: 8888
      servicePort: 8888
      protocol: TCP

ingress:
  enabled: false

podDisruptionBudget:
  enabled: true
  minAvailable: 1

autoscaling:
  enabled: true
  minReplicas: 2
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70

serviceMonitor:
  enabled: true
  interval: 30s

config:
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
    memory_limiter:
      check_interval: 1s
      limit_mib: 1536
      spike_limit_mib: 512
  
  exporters:
    logging:
      loglevel: info
    otlp/jaeger:
      endpoint: jaeger-collector:4317
      tls:
        insecure: true
  
  service:
    pipelines:
      traces:
        receivers: [otlp]
        processors: [memory_limiter, batch]
        exporters: [logging, otlp/jaeger]
```

---

## 🧪 测试验证

### 功能测试

```bash
#!/bin/bash
# test-otlp-k8s.sh

set -e

echo "=== OTLP K8s功能测试 ==="

# 1. 测试gRPC端点
echo "测试gRPC端点..."
grpcurl -plaintext \
  otel-collector.observability.svc.cluster.local:4317 \
  list

# 2. 测试HTTP端点
echo "测试HTTP端点..."
curl -v -X POST \
  http://otel-collector.observability.svc.cluster.local:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{
    "resourceSpans": [
      {
        "resource": {
          "attributes": [
            {"key": "service.name", "value": {"stringValue": "test-service"}}
          ]
        },
        "scopeSpans": [
          {
            "spans": [
              {
                "traceId": "5B8EFFF798038103D269B633813FC60C",
                "spanId": "EEE19B7EC3C1B174",
                "name": "test-span",
                "startTimeUnixNano": "1544712660000000000",
                "endTimeUnixNano": "1544712661000000000"
              }
            ]
          }
        ]
      }
    ]
  }'

# 3. 检查Collector日志
echo "检查Collector日志..."
kubectl logs -n observability -l app=otel-collector --tail=50 | grep "test-service"

echo "✅ 功能测试完成"
```

### 性能测试

```bash
#!/bin/bash
# benchmark-otlp.sh

echo "=== OTLP性能基准测试 ==="

# 使用k6进行负载测试
kubectl run k6 --image=grafana/k6 --rm -it --restart=Never -- \
  run - <<EOF
import http from 'k6/http';
import { check } from 'k6';

export let options = {
  stages: [
    { duration: '1m', target: 100 },
    { duration: '3m', target: 100 },
    { duration: '1m', target: 0 },
  ],
};

export default function() {
  let url = 'http://otel-collector.observability.svc.cluster.local:4318/v1/traces';
  let payload = JSON.stringify({
    resourceSpans: [{
      resource: {
        attributes: [
          {key: "service.name", value: {stringValue: "load-test"}}
        ]
      },
      scopeSpans: [{
        spans: [{
          traceId: "5B8EFFF798038103D269B633813FC60C",
          spanId: "EEE19B7EC3C1B174",
          name: "test-span",
          startTimeUnixNano: "1544712660000000000",
          endTimeUnixNano: "1544712661000000000"
        }]
      }]
    }]
  });
  
  let res = http.post(url, payload, {
    headers: { 'Content-Type': 'application/json' },
  });
  
  check(res, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });
}
EOF
```

### 混沌测试

```bash
# 使用Chaos Mesh测试故障恢复
kubectl apply -f - <<EOF
apiVersion: chaos-mesh.org/v1alpha1
kind: PodChaos
metadata:
  name: otel-collector-pod-failure
  namespace: observability
spec:
  action: pod-failure
  mode: one
  duration: "30s"
  selector:
    namespaces:
      - observability
    labelSelectors:
      app: otel-collector
  scheduler:
    cron: "@every 5m"
EOF

# 监控恢复过程
kubectl get pods -n observability -w
```

---

## 📝 运维手册

### 日常运维

**每日检查**:

```bash
#!/bin/bash
# daily-check.sh

echo "=== OTLP每日检查 ==="

# 1. 检查Pod状态
echo "1. Pod状态:"
kubectl get pods -n observability -l app=otel-collector

# 2. 检查错误率
echo "2. 错误率:"
kubectl logs -n observability -l app=otel-collector --since=24h | \
  grep -c "error" || echo "0"

# 3. 检查资源使用
echo "3. 资源使用:"
kubectl top pods -n observability -l app=otel-collector

# 4. 检查HPA状态
echo "4. HPA状态:"
kubectl get hpa -n observability

# 5. 检查告警
echo "5. 活跃告警:"
curl -s http://prometheus.observability:9090/api/v1/alerts | \
  jq '.data.alerts[] | select(.state=="firing") | .labels.alertname'

echo "✅ 每日检查完成"
```

### 故障恢复

**Collector重启**:

```bash
# 优雅重启
kubectl rollout restart daemonset/otel-collector -n observability

# 强制重启
kubectl delete pods -n observability -l app=otel-collector

# 验证恢复
kubectl rollout status daemonset/otel-collector -n observability
```

**配置回滚**:

```bash
# 查看历史版本
kubectl rollout history daemonset/otel-collector -n observability

# 回滚到上一版本
kubectl rollout undo daemonset/otel-collector -n observability

# 回滚到指定版本
kubectl rollout undo daemonset/otel-collector -n observability --to-revision=3
```

### 升级流程

```bash
#!/bin/bash
# upgrade-collector.sh

set -e

VERSION="0.96.0"

echo "=== 升级OTLP Collector到 $VERSION ==="

# 1. 备份当前配置
kubectl get configmap -n observability otel-collector-config -o yaml > \
  backup-config-$(date +%Y%m%d).yaml

# 2. 更新镜像
kubectl set image daemonset/otel-collector -n observability \
  otel-collector=otel/opentelemetry-collector-k8s:$VERSION

# 3. 监控滚动更新
kubectl rollout status daemonset/otel-collector -n observability

# 4. 验证新版本
kubectl get pods -n observability -l app=otel-collector -o \
  jsonpath='{.items[0].spec.containers[0].image}'

# 5. 运行健康检查
./daily-check.sh

echo "✅ 升级完成"
```

---

## 📚 相关资源

**官方文档**:

- [OpenTelemetry Documentation](https://opentelemetry.io/docs/)
- [OpenTelemetry Collector](https://opentelemetry.io/docs/collector/)
- [Istio Documentation](https://istio.io/latest/docs/)
- [Envoy Proxy Documentation](https://www.envoyproxy.io/docs/envoy/latest/)

**Helm Charts**:

- [OpenTelemetry Helm Charts](https://github.com/open-telemetry/opentelemetry-helm-charts)
- [Jaeger Helm Chart](https://github.com/jaegertracing/helm-charts)
- [Prometheus Helm Chart](https://github.com/prometheus-community/helm-charts)

**示例和教程**:

- [OpenTelemetry Demo](https://github.com/open-telemetry/opentelemetry-demo)
- [Istio Telemetry](https://istio.io/latest/docs/tasks/observability/)

**社区支持**:

- [CNCF Slack - OpenTelemetry](https://cloud-native.slack.com/archives/C01N3AT62SJ)
- [Istio Discuss](https://discuss.istio.io/)

---

## 📅 变更历史

| 版本 | 日期 | 变更内容 | 作者 |
|------|------|---------|------|
| v2.0 | 2025-10-17 | 完整生产级指南：架构、部署、监控、故障排查 | OTLP团队 |
| v1.0 | 2025-01-20 | 初始版本：基础指引 | OTLP团队 |

---

**文档状态**: ✅ 生产就绪  
**完成时间**: 2025年10月17日  
**维护团队**: OTLP Cloud Native团队
