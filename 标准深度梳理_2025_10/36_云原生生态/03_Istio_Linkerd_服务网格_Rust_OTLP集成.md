# Istio & Linkerd 服务网格 - Rust + OTLP 完整集成

## 📋 目录

- [Istio \& Linkerd 服务网格 - Rust + OTLP 完整集成](#istio--linkerd-服务网格---rust--otlp-完整集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是服务网格?](#什么是服务网格)
    - [Istio vs Linkerd](#istio-vs-linkerd)
    - [为什么使用 Rust?](#为什么使用-rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. 服务网格架构](#1-服务网格架构)
    - [2. Envoy Sidecar 配置](#2-envoy-sidecar-配置)
  - [Istio 集成](#istio-集成)
    - [1. Rust 服务部署](#1-rust-服务部署)
    - [2. VirtualService 路由](#2-virtualservice-路由)
    - [3. DestinationRule 策略](#3-destinationrule-策略)
    - [4. mTLS 配置](#4-mtls-配置)
  - [Linkerd 集成](#linkerd-集成)
    - [1. Rust 服务注入](#1-rust-服务注入)
    - [2. ServiceProfile 配置](#2-serviceprofile-配置)
    - [3. TrafficSplit 金丝雀发布](#3-trafficsplit-金丝雀发布)
  - [OTLP 集成策略](#otlp-集成策略)
    - [1. Envoy Trace Context 传播](#1-envoy-trace-context-传播)
    - [2. Rust 应用追踪](#2-rust-应用追踪)
  - [流量管理](#流量管理)
    - [1. 金丝雀发布](#1-金丝雀发布)
    - [2. 超时与重试](#2-超时与重试)
    - [3. 熔断](#3-熔断)
  - [安全](#安全)
    - [1. mTLS 双向认证](#1-mtls-双向认证)
    - [2. JWT 认证](#2-jwt-认证)
  - [可观测性](#可观测性)
    - [1. Prometheus Metrics](#1-prometheus-metrics)
    - [2. Jaeger 分布式追踪](#2-jaeger-分布式追踪)
    - [3. Kiali 可视化](#3-kiali-可视化)
  - [最佳实践](#最佳实践)
    - [1. Sidecar 资源优化](#1-sidecar-资源优化)
    - [2. 渐进式迁移](#2-渐进式迁移)
    - [3. 多集群部署](#3-多集群部署)
  - [完整示例](#完整示例)
    - [1. 微服务架构](#1-微服务架构)
    - [2. Rust 订单服务](#2-rust-订单服务)
    - [3. Kubernetes 部署](#3-kubernetes-部署)
    - [4. Istio 配置](#4-istio-配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Istio vs Linkerd 对比](#istio-vs-linkerd-对比)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是服务网格?

**服务网格**(Service Mesh)是一个专用的基础设施层,用于处理服务间通信:

```text
┌─────────────────────────────────────┐
│    Application (Rust Service)      │
└──────────────┬──────────────────────┘
               │ localhost
┌──────────────▼──────────────────────┐
│      Sidecar Proxy (Envoy)          │
│  - Load Balancing                   │
│  - Retry & Timeout                  │
│  - mTLS                             │
│  - Observability                    │
└──────────────┬──────────────────────┘
               │ Service Network
               ▼
        Other Services
```

### Istio vs Linkerd

| 特性 | Istio | Linkerd |
|-----|-------|---------|
| **复杂度** | 高 | 低 |
| **性能开销** | ~5-10ms | ~1-2ms |
| **内存占用** | ~100MB | ~30MB |
| **功能丰富度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **学习曲线** | 陡峭 | 平缓 |
| **生态** | CNCF 毕业 | CNCF 毕业 |
| **代理** | Envoy | Linkerd2-proxy(Rust) |

### 为什么使用 Rust?

- **高性能**: 低延迟服务,减少 Sidecar 开销
- **零成本抽象**: 编译期优化
- **内存安全**: 避免服务崩溃
- **Async-First**: Tokio 异步 I/O

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **服务调用链** | 分布式 Trace(通过 Envoy) |
| **请求延迟** | Histogram(应用+Sidecar) |
| **流量拓扑** | Metrics(请求/响应) |
| **错误率** | Counter(by status code) |
| **mTLS 状态** | Gauge(连接安全性) |

---

## 核心概念

### 1. 服务网格架构

```text
Control Plane (istiod / linkerd-control-plane)
    ↓
    ├─ Service Discovery
    ├─ Configuration
    └─ Certificate Management

Data Plane (Envoy / linkerd2-proxy Sidecars)
    ↓
    ├─ Traffic Routing
    ├─ Load Balancing
    ├─ mTLS Encryption
    └─ Observability
```

### 2. Envoy Sidecar 配置

Istio 使用 Envoy 作为 Sidecar 代理,支持 OTLP:

```yaml
# ConfigMap: istio-sidecar-injector
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-sidecar-injector
  namespace: istio-system
data:
  config: |
    policy: enabled
    alwaysInjectSelector: []
    neverInjectSelector: []
    template: |
      containers:
      - name: istio-proxy
        image: docker.io/istio/proxyv2:1.22.0
        args:
        - proxy
        - sidecar
        - --configPath=/etc/istio/proxy
        - --binaryPath=/usr/local/bin/envoy
        - --serviceCluster={{ .Values.global.proxy.cluster }}
        env:
        - name: ISTIO_META_TRACER
          value: "opentelemetry"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector:4317"
```

---

## Istio 集成

### 1. Rust 服务部署

```toml
# Cargo.toml
[dependencies]
axum = "0.7"
tokio = { version = "1.40", features = ["full"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["trace"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.28"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics"] }
```

```rust
// src/main.rs
use axum::{
    extract::State,
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
    routing::get,
    Json, Router,
};
use opentelemetry::{global, trace::TraceContextExt, KeyValue};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tower_http::trace::TraceLayer;
use tracing::{info, instrument};

#[derive(Clone)]
struct AppState {
    http_client: reqwest::Client,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OTLP
    global::set_text_map_propagator(TraceContextPropagator::new());

    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"), // Envoy 会转发到 Collector
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    let state = AppState {
        http_client: reqwest::Client::new(),
    };

    let app = Router::new()
        .route("/orders", get(list_orders).post(create_order))
        .route("/health", get(health_check))
        .layer(TraceLayer::new_for_http())
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    info!("订单服务启动在 http://0.0.0.0:8080");

    axum::serve(listener, app).await?;

    Ok(())
}

#[derive(Debug, Serialize, Deserialize)]
struct Order {
    id: String,
    user_id: i64,
    total: f64,
}

#[instrument(skip(state))]
async fn list_orders(State(state): State<AppState>) -> impl IntoResponse {
    info!("获取订单列表");

    // 模拟数据
    let orders = vec![
        Order {
            id: "order-1".to_string(),
            user_id: 123,
            total: 99.99,
        },
        Order {
            id: "order-2".to_string(),
            user_id: 456,
            total: 149.99,
        },
    ];

    Json(orders)
}

#[instrument(skip(state, headers))]
async fn create_order(
    State(state): State<AppState>,
    headers: HeaderMap,
    Json(order): Json<Order>,
) -> Result<Json<Order>, StatusCode> {
    info!(order.id = %order.id, "创建订单");

    // 调用库存服务检查
    let inventory_url = "http://inventory-service:8080/check";

    // 传播 Trace Context (Istio Envoy 会自动注入)
    let response = state
        .http_client
        .post(inventory_url)
        .json(&serde_json::json!({ "order_id": order.id }))
        .send()
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    if !response.status().is_success() {
        return Err(StatusCode::BAD_REQUEST);
    }

    Ok(Json(order))
}

async fn health_check() -> &'static str {
    "OK"
}
```

### 2. VirtualService 路由

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: order-service
spec:
  hosts:
  - order-service
  http:
  - match:
    - headers:
        canary:
          exact: "true"
    route:
    - destination:
        host: order-service
        subset: v2
      weight: 100
  - route:
    - destination:
        host: order-service
        subset: v1
      weight: 90
    - destination:
        host: order-service
        subset: v2
      weight: 10
  - timeout: 3s
    retries:
      attempts: 3
      perTryTimeout: 1s
      retryOn: 5xx,reset,connect-failure,refused-stream
```

### 3. DestinationRule 策略

```yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: order-service
spec:
  host: order-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        http2MaxRequests: 100
        maxRequestsPerConnection: 2
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
    trafficPolicy:
      loadBalancer:
        consistentHash:
          httpHeaderName: "x-user-id"
```

### 4. mTLS 配置

```yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
  namespace: default
spec:
  mtls:
    mode: STRICT

---
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: order-service-authz
spec:
  selector:
    matchLabels:
      app: order-service
  action: ALLOW
  rules:
  - from:
    - source:
        principals: ["cluster.local/ns/default/sa/frontend-sa"]
    to:
    - operation:
        methods: ["GET", "POST"]
        paths: ["/orders*"]
```

---

## Linkerd 集成

### 1. Rust 服务注入

Linkerd 自动注入 Sidecar(使用 Rust 编写的 linkerd2-proxy):

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
  annotations:
    linkerd.io/inject: enabled  # 自动注入
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-service
  template:
    metadata:
      labels:
        app: order-service
    spec:
      containers:
      - name: order-service
        image: myregistry/order-service:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://localhost:4317"  # linkerd2-proxy 转发
        - name: RUST_LOG
          value: "info"
```

### 2. ServiceProfile 配置

```yaml
apiVersion: linkerd.io/v1alpha2
kind: ServiceProfile
metadata:
  name: order-service.default.svc.cluster.local
spec:
  routes:
  - name: list_orders
    condition:
      method: GET
      pathRegex: /orders
    responseClasses:
    - condition:
        status:
          min: 200
          max: 299
      isFailure: false
    - condition:
        status:
          min: 500
          max: 599
      isFailure: true
    timeout: 3s
    retryBudget:
      retryRatio: 0.2
      minRetriesPerSecond: 10
      ttl: 30s

  - name: create_order
    condition:
      method: POST
      pathRegex: /orders
    isRetryable: false  # POST 不可重试
    timeout: 5s
```

### 3. TrafficSplit 金丝雀发布

```yaml
apiVersion: split.smi-spec.io/v1alpha1
kind: TrafficSplit
metadata:
  name: order-service-split
spec:
  service: order-service
  backends:
  - service: order-service-v1
    weight: 900  # 90%
  - service: order-service-v2
    weight: 100  # 10%

---
apiVersion: v1
kind: Service
metadata:
  name: order-service-v1
spec:
  selector:
    app: order-service
    version: v1
  ports:
  - port: 8080

---
apiVersion: v1
kind: Service
metadata:
  name: order-service-v2
spec:
  selector:
    app: order-service
    version: v2
  ports:
  - port: 8080
```

---

## OTLP 集成策略

### 1. Envoy Trace Context 传播

Envoy/linkerd2-proxy 自动传播以下 Header:

```text
x-request-id
x-b3-traceid
x-b3-spanid
x-b3-parentspanid
x-b3-sampled
traceparent (W3C Trace Context)
tracestate
```

Rust 应用无需手动处理,OTLP SDK 自动识别。

### 2. Rust 应用追踪

```rust
use opentelemetry::global;
use opentelemetry::propagation::Extractor;

// 自定义 Extractor (可选,SDK 已内置)
struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

#[instrument(skip(headers))]
async fn handle_request(headers: HeaderMap) {
    // 提取上游 Trace Context
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let parent_cx = propagator.extract(&HeaderExtractor(&headers));

    // 创建子 Span
    let span = tracing::Span::current();
    span.in_scope(|| {
        info!("处理请求");
    });
}
```

---

## 流量管理

### 1. 金丝雀发布

**Istio 方式**:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: order-service-canary
spec:
  hosts:
  - order-service
  http:
  - match:
    - headers:
        x-canary-user:
          exact: "internal"
    route:
    - destination:
        host: order-service
        subset: v2
      weight: 100
  - route:
    - destination:
        host: order-service
        subset: v1
      weight: 95
    - destination:
        host: order-service
        subset: v2
      weight: 5
```

**Linkerd 方式**:

```bash
# 使用 Flagger 自动化金丝雀
kubectl apply -f - <<EOF
apiVersion: flagger.app/v1beta1
kind: Canary
metadata:
  name: order-service
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: order-service
  service:
    port: 8080
  analysis:
    interval: 1m
    threshold: 5
    maxWeight: 50
    stepWeight: 10
    metrics:
    - name: request-success-rate
      thresholdRange:
        min: 99
      interval: 1m
    - name: request-duration
      thresholdRange:
        max: 500
      interval: 1m
EOF
```

### 2. 超时与重试

**Istio**:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: order-service-timeout
spec:
  hosts:
  - order-service
  http:
  - timeout: 3s
    retries:
      attempts: 3
      perTryTimeout: 1s
      retryOn: 5xx,reset,connect-failure
    route:
    - destination:
        host: order-service
```

**Linkerd** (使用 ServiceProfile,见上文)

### 3. 熔断

**Istio**:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: order-service-circuit-breaker
spec:
  host: order-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 1
        maxRequestsPerConnection: 1
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
```

---

## 安全

### 1. mTLS 双向认证

**Istio**:

```yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
spec:
  mtls:
    mode: STRICT  # 强制 mTLS

---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: order-service-mtls
spec:
  host: order-service
  trafficPolicy:
    tls:
      mode: ISTIO_MUTUAL
```

**Linkerd**:

```bash
# Linkerd 默认启用 mTLS,无需额外配置
linkerd check --proxy

# 验证 mTLS
linkerd tap deploy/order-service | grep tls
```

### 2. JWT 认证

**Istio**:

```yaml
apiVersion: security.istio.io/v1beta1
kind: RequestAuthentication
metadata:
  name: jwt-auth
spec:
  selector:
    matchLabels:
      app: order-service
  jwtRules:
  - issuer: "https://auth.example.com"
    jwksUri: "https://auth.example.com/.well-known/jwks.json"
    audiences:
    - "order-service"

---
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: require-jwt
spec:
  selector:
    matchLabels:
      app: order-service
  action: ALLOW
  rules:
  - from:
    - source:
        requestPrincipals: ["*"]
    when:
    - key: request.auth.claims[role]
      values: ["admin", "user"]
```

---

## 可观测性

### 1. Prometheus Metrics

**Istio 暴露的 Metrics**:

```promql
# 请求成功率
sum(rate(istio_requests_total{response_code="200"}[5m])) /
sum(rate(istio_requests_total[5m])) * 100

# P99 延迟
histogram_quantile(0.99,
  sum(rate(istio_request_duration_milliseconds_bucket[5m])) by (le, destination_service_name)
)

# mTLS 使用率
sum(istio_tcp_connections_opened_total{security_policy="mutual_tls"}) /
sum(istio_tcp_connections_opened_total) * 100
```

**Linkerd Metrics**:

```promql
# 请求成功率
sum(rate(response_total{classification="success"}[5m])) /
sum(rate(response_total[5m])) * 100

# P99 延迟
histogram_quantile(0.99,
  sum(rate(response_latency_ms_bucket[5m])) by (le, dst_service)
)
```

### 2. Jaeger 分布式追踪

配置 Istio 导出到 Jaeger:

```yaml
apiVersion: install.istio.io/v1alpha1
kind: IstioOperator
spec:
  meshConfig:
    enableTracing: true
    defaultConfig:
      tracing:
        opentelemetry:
          endpoint: "otel-collector.observability:4317"
        sampling: 100.0
```

### 3. Kiali 可视化

```bash
# Istio - 安装 Kiali
kubectl apply -f https://raw.githubusercontent.com/istio/istio/release-1.22/samples/addons/kiali.yaml

# 访问 Kiali
kubectl port-forward -n istio-system svc/kiali 20001:20001

# Linkerd - Viz Extension
linkerd viz install | kubectl apply -f -
linkerd viz dashboard
```

---

## 最佳实践

### 1. Sidecar 资源优化

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-sidecar-injector
data:
  values: |
    sidecarInjectorWebhook:
      neverInjectSelector:
      - matchExpressions:
        - key: job-name
          operator: Exists
      injectedAnnotations:
        sidecar.istio.io/proxyCPU: "100m"
        sidecar.istio.io/proxyMemory: "128Mi"
        sidecar.istio.io/proxyCPULimit: "500m"
        sidecar.istio.io/proxyMemoryLimit: "512Mi"
```

### 2. 渐进式迁移

```yaml
# 阶段1: 仅监控,不拦截流量
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
spec:
  mtls:
    mode: PERMISSIVE  # 允许明文+mTLS

# 阶段2: 强制 mTLS
# ... 等待所有服务迁移完成后 ...
spec:
  mtls:
    mode: STRICT
```

### 3. 多集群部署

**Istio 多集群**:

```bash
# 主集群
istioctl install --set values.global.meshID=mesh1 \
  --set values.global.multiCluster.clusterName=cluster1 \
  --set values.global.network=network1

# 从集群
istioctl install --set values.global.meshID=mesh1 \
  --set values.global.multiCluster.clusterName=cluster2 \
  --set values.global.network=network2
```

---

## 完整示例

### 1. 微服务架构

```text
Frontend (Rust + Yew)
    ↓
API Gateway (Rust + Axum)
    ↓
    ├─> Order Service (Rust)
    │       ↓
    │   Inventory Service (Rust)
    │
    └─> Payment Service (Rust)
```

### 2. Rust 订单服务

(代码见上文 "Rust 服务部署")

### 3. Kubernetes 部署

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: ecommerce
  labels:
    istio-injection: enabled  # Istio 自动注入

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
  namespace: ecommerce
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-service
      version: v1
  template:
    metadata:
      labels:
        app: order-service
        version: v1
    spec:
      containers:
      - name: order-service
        image: myregistry/order-service:v1
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://localhost:4317"
        resources:
          requests:
            cpu: "100m"
            memory: "128Mi"
          limits:
            cpu: "500m"
            memory: "512Mi"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 5

---
apiVersion: v1
kind: Service
metadata:
  name: order-service
  namespace: ecommerce
spec:
  selector:
    app: order-service
  ports:
  - port: 8080
    targetPort: 8080
```

### 4. Istio 配置

```yaml
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: ecommerce-gateway
spec:
  selector:
    istio: ingressgateway
  servers:
  - port:
      number: 80
      name: http
      protocol: HTTP
    hosts:
    - "api.example.com"

---
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: order-service
spec:
  hosts:
  - "api.example.com"
  gateways:
  - ecommerce-gateway
  http:
  - match:
    - uri:
        prefix: /orders
    route:
    - destination:
        host: order-service
        port:
          number: 8080
    timeout: 3s
    retries:
      attempts: 3
      perTryTimeout: 1s
```

---

## 总结

### 核心要点

1. **服务网格价值**: 流量管理、安全、可观测性与业务逻辑解耦
2. **Rust 优势**: 低延迟、高性能,与 Linkerd2-proxy 同语言
3. **OTLP 自动传播**: Envoy/Linkerd 自动注入 Trace Context
4. **mTLS 零配置**: 服务网格自动启用加密通信
5. **金丝雀发布**: VirtualService/TrafficSplit 实现流量控制

### Istio vs Linkerd 对比

| 场景 | 推荐 | 理由 |
|-----|------|------|
| **大型企业** | Istio | 功能全面,生态丰富 |
| **中小团队** | Linkerd | 简单易用,性能高 |
| **混合云** | Istio | 多集群支持更好 |
| **性能敏感** | Linkerd | Rust 代理,延迟更低 |
| **复杂路由** | Istio | 路由规则更灵活 |

### 下一步

- **Wasm 扩展**: 使用 Rust 编写 Envoy Wasm 插件
- **多租户**: 使用 Namespace 隔离 + AuthorizationPolicy
- **混沌工程**: Fault Injection 测试
- **成本优化**: Sidecar 资源调优

---

## 参考资料

- [Istio 官方文档](https://istio.io/latest/docs/)
- [Linkerd 官方文档](https://linkerd.io/docs/)
- [Envoy OTLP Tracer](https://www.envoyproxy.io/docs/envoy/latest/api-v3/config/trace/v3/opentelemetry.proto)
- [Service Mesh Comparison](https://servicemesh.es/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Istio 版本**: 1.22+  
**Linkerd 版本**: 2.15+  
**OpenTelemetry**: 0.30+
