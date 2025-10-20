# Istio Service Mesh Rust 应用集成指南

## 目录

- [Istio Service Mesh Rust 应用集成指南](#istio-service-mesh-rust-应用集成指南)
  - [目录](#目录)
  - [1. Istio 架构概述](#1-istio-架构概述)
    - [1.1 国际标准对标](#11-国际标准对标)
  - [2. Rust 应用 Istio 集成](#2-rust-应用-istio-集成)
    - [2.1 Kubernetes Deployment (Istio 注入)](#21-kubernetes-deployment-istio-注入)
  - [3. 流量管理](#3-流量管理)
    - [3.1 VirtualService (金丝雀发布)](#31-virtualservice-金丝雀发布)
    - [3.2 故障注入 (混沌工程)](#32-故障注入-混沌工程)
    - [3.3 超时与重试](#33-超时与重试)
  - [4. 安全策略](#4-安全策略)
    - [4.1 PeerAuthentication (mTLS)](#41-peerauthentication-mtls)
    - [4.2 AuthorizationPolicy (访问控制)](#42-authorizationpolicy-访问控制)
  - [5. 可观测性集成](#5-可观测性集成)
    - [5.1 Rust 应用 OpenTelemetry 配置](#51-rust-应用-opentelemetry-配置)
    - [5.2 Telemetry (Prometheus + Jaeger)](#52-telemetry-prometheus--jaeger)
  - [6. 完整部署示例](#6-完整部署示例)
    - [6.1 Istio 安装](#61-istio-安装)
    - [6.2 部署 Rust 应用](#62-部署-rust-应用)
    - [6.3 验证](#63-验证)
  - [总结](#总结)

## 1. Istio 架构概述

```text
┌──────────────────────────────────────────────────────────┐
│                    Istio 控制平面                         │
│  • Pilot (流量管理)                                       │
│  • Citadel (证书管理)                                     │
│  • Galley (配置验证)                                      │
└──────────────────────────────────────────────────────────┘
                           │
          ┌────────────────┼────────────────┐
          ▼                ▼                ▼
┌──────────────┐  ┌──────────────┐  ┌──────────────┐
│  Envoy Proxy │  │  Envoy Proxy │  │  Envoy Proxy │
│  (Sidecar)   │  │  (Sidecar)   │  │  (Sidecar)   │
├──────────────┤  ├──────────────┤  ├──────────────┤
│  Rust App A  │  │  Rust App B  │  │  Rust App C  │
└──────────────┘  └──────────────┘  └──────────────┘
```

### 1.1 国际标准对标

| 标准 | Istio 实现 | 文档 |
|------|------------|------|
| **Service Mesh** | Istio 1.24 | [Istio Docs](https://istio.io/latest/docs/) |
| **Envoy Proxy** | xDS API | [Envoy API](https://www.envoyproxy.io/docs/envoy/latest/api/api) |
| **mTLS** | SPIFFE/SPIRE | [SPIFFE](https://spiffe.io/) |
| **OpenTelemetry** | 原生支持 | [OTLP](https://opentelemetry.io/docs/specs/otel/) |

---

## 2. Rust 应用 Istio 集成

### 2.1 Kubernetes Deployment (Istio 注入)

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  namespace: default
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
      version: v1
  template:
    metadata:
      labels:
        app: rust-app
        version: v1
      annotations:
        # Istio Sidecar 注入
        sidecar.istio.io/inject: "true"
        # Prometheus 抓取配置
        prometheus.io/scrape: "true"
        prometheus.io/port: "15020"
        prometheus.io/path: "/stats/prometheus"
    spec:
      containers:
      - name: rust-app
        image: rust-app:latest
        ports:
        - containerPort: 8080
          name: http
          protocol: TCP
        env:
        # OpenTelemetry 配置
        - name: OTLP_ENDPOINT
          value: "http://localhost:4317"  # Envoy OTLP 代理
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 30
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 10
---
apiVersion: v1
kind: Service
metadata:
  name: rust-app
  namespace: default
  labels:
    app: rust-app
spec:
  selector:
    app: rust-app
  ports:
  - port: 80
    targetPort: 8080
    protocol: TCP
    name: http
  type: ClusterIP
```

---

## 3. 流量管理

### 3.1 VirtualService (金丝雀发布)

```yaml
# virtualservice.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: rust-app
  namespace: default
spec:
  hosts:
  - rust-app.default.svc.cluster.local
  http:
  - match:
    - headers:
        x-canary:
          exact: "true"
    route:
    - destination:
        host: rust-app.default.svc.cluster.local
        subset: v2
      weight: 100
  - route:
    - destination:
        host: rust-app.default.svc.cluster.local
        subset: v1
      weight: 90
    - destination:
        host: rust-app.default.svc.cluster.local
        subset: v2
      weight: 10
---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: rust-app
  namespace: default
spec:
  host: rust-app.default.svc.cluster.local
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        http2MaxRequests: 100
    loadBalancer:
      simple: LEAST_REQUEST
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2
```

### 3.2 故障注入 (混沌工程)

```yaml
# fault-injection.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: rust-app-fault
spec:
  hosts:
  - rust-app.default.svc.cluster.local
  http:
  - fault:
      delay:
        percentage:
          value: 10  # 10% 请求延迟
        fixedDelay: 5s
      abort:
        percentage:
          value: 5  # 5% 请求返回 500
        httpStatus: 500
    route:
    - destination:
        host: rust-app.default.svc.cluster.local
```

### 3.3 超时与重试

```yaml
# timeout-retry.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: rust-app-timeout
spec:
  hosts:
  - rust-app.default.svc.cluster.local
  http:
  - timeout: 10s
    retries:
      attempts: 3
      perTryTimeout: 2s
      retryOn: 5xx,reset,connect-failure,refused-stream
    route:
    - destination:
        host: rust-app.default.svc.cluster.local
```

---

## 4. 安全策略

### 4.1 PeerAuthentication (mTLS)

```yaml
# peer-authentication.yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
  namespace: default
spec:
  mtls:
    mode: STRICT  # 强制 mTLS
---
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: rust-app
  namespace: default
spec:
  selector:
    matchLabels:
      app: rust-app
  mtls:
    mode: STRICT
  portLevelMtls:
    8080:
      mode: PERMISSIVE  # HTTP 端口允许明文
```

### 4.2 AuthorizationPolicy (访问控制)

```yaml
# authorization-policy.yaml
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: rust-app-authz
  namespace: default
spec:
  selector:
    matchLabels:
      app: rust-app
  action: ALLOW
  rules:
  # 允许来自 frontend 服务的请求
  - from:
    - source:
        principals: ["cluster.local/ns/default/sa/frontend"]
    to:
    - operation:
        methods: ["GET", "POST"]
        paths: ["/api/*"]
  # 拒绝所有其他请求
  - {}
---
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: deny-all
  namespace: default
spec:
  action: DENY
  rules:
  - from:
    - source:
        notNamespaces: ["default"]
```

---

## 5. 可观测性集成

### 5.1 Rust 应用 OpenTelemetry 配置

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{trace, Resource, runtime};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> anyhow::Result<()> {
    // Envoy Sidecar 会自动代理 OTLP 流量到 Istio Telemetry
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());

    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint)
        )
        .with_trace_config(
            trace::config().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "rust-app"),
                KeyValue::new("service.namespace", "default"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                // Istio 标签传播
                KeyValue::new("istio.mesh_id", "cluster.local"),
                KeyValue::new("istio.canonical_service", "rust-app"),
                KeyValue::new("istio.canonical_revision", "v1"),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 5.2 Telemetry (Prometheus + Jaeger)

```yaml
# telemetry.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: mesh-default
  namespace: istio-system
spec:
  tracing:
  - providers:
    - name: jaeger
    randomSamplingPercentage: 10.0  # 10% 采样
    customTags:
      http.method:
        header:
          name: ":method"
      http.status_code:
        header:
          name: ":status"
  metrics:
  - providers:
    - name: prometheus
    dimensions:
      request_protocol: istio_request_protocol
      response_code: response_code
---
apiVersion: install.istio.io/v1alpha1
kind: IstioOperator
spec:
  meshConfig:
    defaultConfig:
      tracing:
        zipkin:
          address: jaeger-collector.istio-system:9411
        sampling: 10.0
```

---

## 6. 完整部署示例

### 6.1 Istio 安装

```bash
# 安装 Istio
curl -L https://istio.io/downloadIstio | sh -
cd istio-1.24.0
export PATH=$PWD/bin:$PATH

# 安装 Demo Profile
istioctl install --set profile=demo -y

# 启用 Sidecar 自动注入
kubectl label namespace default istio-injection=enabled
```

### 6.2 部署 Rust 应用

```bash
# 部署应用
kubectl apply -f deployment.yaml

# 配置流量管理
kubectl apply -f virtualservice.yaml

# 配置安全策略
kubectl apply -f peer-authentication.yaml
kubectl apply -f authorization-policy.yaml

# 配置可观测性
kubectl apply -f telemetry.yaml
```

### 6.3 验证

```bash
# 查看 Pod (应该有 2 个容器: app + istio-proxy)
kubectl get pods

# 查看流量
kubectl logs -l app=rust-app -c istio-proxy --tail=100

# Jaeger UI
istioctl dashboard jaeger

# Kiali (服务拓扑)
istioctl dashboard kiali

# Prometheus
istioctl dashboard prometheus
```

---

## 总结

✅ **Istio Service Mesh 完整集成**  
✅ **流量管理** (金丝雀发布 + 故障注入)  
✅ **mTLS 安全** (自动证书管理)  
✅ **分布式追踪** (Jaeger + OpenTelemetry)  
✅ **服务拓扑** (Kiali 可视化)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
