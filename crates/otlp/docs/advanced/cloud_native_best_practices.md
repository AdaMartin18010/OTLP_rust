# 云原生最佳实践完整指南

**Crate:** c10_otlp
**主题:** Cloud Native Best Practices
**Rust 版本:** 1.90.0
**最后更新:** 2025年10月28日

---

## 📋 目录

- [云原生最佳实践完整指南](#云原生最佳实践完整指南)
  - [📋 目录](#-目录)
  - [🎯 云原生概述](#-云原生概述)
    - [云原生定义](#云原生定义)
    - [核心原则](#核心原则)
  - [📝 12-Factor App](#-12-factor-app)
    - [1. Codebase (代码库)](#1-codebase-代码库)
    - [2. Dependencies (依赖)](#2-dependencies-依赖)
    - [3. Config (配置)](#3-config-配置)
    - [4. Backing Services (后端服务)](#4-backing-services-后端服务)
    - [5. Build, Release, Run (构建、发布、运行)](#5-build-release-run-构建发布运行)
    - [6. Processes (进程)](#6-processes-进程)
    - [7. Port Binding (端口绑定)](#7-port-binding-端口绑定)
    - [8. Concurrency (并发)](#8-concurrency-并发)
    - [9. Disposability (易处理)](#9-disposability-易处理)
    - [10. Dev/Prod Parity (开发环境与线上环境等价)](#10-devprod-parity-开发环境与线上环境等价)
    - [11. Logs (日志)](#11-logs-日志)
    - [12. Admin Processes (管理进程)](#12-admin-processes-管理进程)
  - [🐳 容器化最佳实践](#-容器化最佳实践)
    - [1. 优化的 Dockerfile](#1-优化的-dockerfile)
    - [2. 镜像大小优化](#2-镜像大小优化)
    - [3. 安全最佳实践](#3-安全最佳实践)
  - [☸️ Kubernetes 部署](#️-kubernetes-部署)
    - [1. Deployment 配置](#1-deployment-配置)
    - [2. Service 和 Ingress](#2-service-和-ingress)
    - [3. PodDisruptionBudget](#3-poddisruptionbudget)
  - [🕸️ 服务网格](#️-服务网格)
    - [1. Istio 集成](#1-istio-集成)
    - [2. 服务网格观测性](#2-服务网格观测性)
  - [⚙️ 配置管理](#️-配置管理)
    - [1. Helm Charts](#1-helm-charts)
    - [2. Kustomize](#2-kustomize)
  - [🔄 CI/CD 流水线](#-cicd-流水线)
    - [1. GitHub Actions](#1-github-actions)
  - [📂 GitOps](#-gitops)
    - [1. ArgoCD](#1-argocd)
    - [2. Flux](#2-flux)
  - [📚 总结](#-总结)
    - [云原生清单](#云原生清单)
    - [最佳实践](#最佳实践)

---

## 🎯 云原生概述

### 云原生定义

**CNCF 定义**: 云原生技术有利于各组织在公有云、私有云和混合云等现代动态环境中，构建和运行可弹性扩展的应用。

```text
┌──────────────────────────────────────────────┐
│         云原生技术栈 (CNCF Landscape)         │
├────────────┬────────────┬─────────┬──────────┤
│ 容器化      │ 编排       │ 服务网格 │  可观测性 │
│ Docker     │  K8s       │ Istio   │ Prometheus│
│ containerd │ Nomad      │ Linkerd │ Jaeger   │
├────────────┼────────────┼─────────┼──────────┤
│ CI/CD      │  配置管理   │  安全   │  存储    │
│ ArgoCD     │ Helm       │ Falco   │ Rook     │
│ Flux       │ Kustomize  │ OPA     │ Ceph     │
└────────────┴────────────┴─────────┴──────────┘
```

### 核心原则

```rust
pub struct CloudNativeApplication {
    /// 1. 可观测性
    observability: ObservabilityConfig,
    /// 2. 弹性
    resilience: ResilienceConfig,
    /// 3. 可扩展性
    scalability: ScalabilityConfig,
    /// 4. 安全性
    security: SecurityConfig,
}

#[derive(Debug, Clone)]
pub struct ObservabilityConfig {
    pub metrics_enabled: bool,
    pub tracing_enabled: bool,
    pub logging_level: LogLevel,
}

#[derive(Debug, Clone)]
pub struct ResilienceConfig {
    pub retry_policy: RetryPolicy,
    pub circuit_breaker: CircuitBreakerConfig,
    pub timeout: Duration,
}
```

---

## 📝 12-Factor App

### 1. Codebase (代码库)

**原则**: 一份代码库，多份部署

```bash
# Git 仓库结构
my-otlp-app/
├── .git/
├── src/
├── tests/
├── Cargo.toml
├── Dockerfile
└── k8s/
    ├── dev/
    ├── staging/
    └── prod/
```

---

### 2. Dependencies (依赖)

**原则**: 显式声明依赖关系

```toml
# Cargo.toml
[package]
name = "otlp-collector"
version = "1.0.0"
edition = "2021"

[dependencies]
tokio = { version = "1.35", features = ["full"] }
opentelemetry = "0.20"
axum = "0.7"

[build-dependencies]
protobuf-codegen-pure = "3.3"

# 锁定版本
[dependencies.sqlx]
version = "=0.7.3"  # 精确版本
```

---

### 3. Config (配置)

**原则**: 在环境中存储配置

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub struct AppConfig {
    #[serde(env = "DATABASE_URL")]
    pub database_url: String,

    #[serde(env = "REDIS_URL")]
    pub redis_url: String,

    #[serde(env = "LOG_LEVEL", default = "info")]
    pub log_level: String,

    #[serde(env = "PORT", default = "8080")]
    pub port: u16,
}

impl AppConfig {
    pub fn from_env() -> Result<Self> {
        envy::from_env().map_err(Into::into)
    }
}

// Kubernetes ConfigMap
// apiVersion: v1
// kind: ConfigMap
// metadata:
//   name: app-config
// data:
//   DATABASE_URL: "postgresql://..."
//   LOG_LEVEL: "debug"
```

---

### 4. Backing Services (后端服务)

**原则**: 把后端服务当作附加资源

```rust
pub struct BackingServices {
    database: PgPool,
    cache: RedisPool,
    message_queue: KafkaProducer,
}

impl BackingServices {
    pub async fn from_env() -> Result<Self> {
        let database = PgPool::connect(&env::var("DATABASE_URL")?).await?;
        let cache = RedisPool::connect(&env::var("REDIS_URL")?).await?;
        let message_queue = KafkaProducer::new(&env::var("KAFKA_BROKERS")?)?;

        Ok(Self {
            database,
            cache,
            message_queue,
        })
    }
}

// 在 K8s 中使用 Service 抽象后端服务
// apiVersion: v1
// kind: Service
// metadata:
//   name: postgres
// spec:
//   selector:
//     app: postgres
//   ports:
//     - port: 5432
```

---

### 5. Build, Release, Run (构建、发布、运行)

**原则**: 严格分离构建和运行

```bash
# 1. Build 阶段：编译代码
cargo build --release

# 2. Release 阶段：构建容器镜像
docker build -t myapp:v1.2.3 .
docker push myapp:v1.2.3

# 3. Run 阶段：部署到 K8s
kubectl set image deployment/myapp myapp=myapp:v1.2.3
```

```dockerfile
# Multi-stage Dockerfile
# Stage 1: Build
FROM rust:1.90 as builder
WORKDIR /app
COPY . .
RUN cargo build --release

# Stage 2: Runtime
FROM debian:bookworm-slim
COPY --from=builder /app/target/release/myapp /usr/local/bin/
CMD ["myapp"]
```

---

### 6. Processes (进程)

**原则**: 以一个或多个无状态进程运行应用

```rust
// ❌ 不好：在内存中保存会话状态
static mut SESSION_STORE: Option<HashMap<String, Session>> = None;

// ✅ 好：使用外部存储
pub struct StatelessApp {
    session_store: RedisPool,  // 外部会话存储
}

impl StatelessApp {
    pub async fn get_session(&self, session_id: &str) -> Result<Option<Session>> {
        let mut conn = self.session_store.get().await?;
        let data: Option<String> = conn.get(session_id).await?;

        data.map(|s| serde_json::from_str(&s))
            .transpose()
            .map_err(Into::into)
    }
}
```

---

### 7. Port Binding (端口绑定)

**原则**: 通过端口绑定提供服务

```rust
use axum::{Router, Server};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/metrics", get(metrics));

    // 从环境变量读取端口
    let port = env::var("PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse::<u16>()
        .unwrap();

    let addr = SocketAddr::from(([0, 0, 0, 0], port));

    println!("Server listening on {}", addr);

    Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

---

### 8. Concurrency (并发)

**原则**: 通过进程模型进行扩展

```yaml
# Horizontal Pod Autoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: myapp-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: myapp
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
```

---

### 9. Disposability (易处理)

**原则**: 快速启动和优雅终止

```rust
use tokio::signal;

pub async fn run_with_graceful_shutdown(app: Router) {
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));

    let server = Server::bind(&addr)
        .serve(app.into_make_service())
        .with_graceful_shutdown(shutdown_signal());

    println!("Server starting on {}", addr);

    if let Err(e) = server.await {
        eprintln!("Server error: {}", e);
    }

    println!("Server shut down gracefully");
}

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("Failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    println!("Shutdown signal received");
}
```

---

### 10. Dev/Prod Parity (开发环境与线上环境等价)

**原则**: 尽可能保持开发、预发布、线上环境相同

```bash
# 使用 Docker Compose 本地开发
docker-compose up -d

# 使用相同的容器镜像部署到不同环境
docker build -t myapp:latest .

# 开发环境
kubectl config use-context dev
kubectl apply -f k8s/dev/

# 生产环境
kubectl config use-context prod
kubectl apply -f k8s/prod/
```

---

### 11. Logs (日志)

**原则**: 把日志当作事件流

```rust
use tracing::{info, error};
use tracing_subscriber::fmt;

fn init_logging() {
    // 输出到 stdout，不写文件
    fmt()
        .json()  // JSON 格式便于聚合
        .with_target(false)
        .init();
}

pub async fn handle_request(req: Request) -> Response {
    info!(
        method = %req.method(),
        uri = %req.uri(),
        "Incoming request"
    );

    let response = process(req).await;

    info!(
        status = response.status().as_u16(),
        "Request completed"
    );

    response
}

// Kubernetes 自动收集 stdout/stderr 日志
// 使用 Fluentd/Fluent Bit 收集和转发
```

---

### 12. Admin Processes (管理进程)

**原则**: 后台管理任务当作一次性进程运行

```rust
// 数据库迁移
#[tokio::main]
async fn main() {
    let args: Vec<String> = env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("migrate") => {
            run_migrations().await?;
        }
        Some("seed") => {
            seed_database().await?;
        }
        _ => {
            run_server().await?;
        }
    }

    Ok(())
}

// Kubernetes Job
// apiVersion: batch/v1
// kind: Job
// metadata:
//   name: db-migrate
// spec:
//   template:
//     spec:
//       containers:
//       - name: migrate
//         image: myapp:v1.2.3
//         command: ["myapp", "migrate"]
//       restartPolicy: OnFailure
```

---

## 🐳 容器化最佳实践

### 1. 优化的 Dockerfile

```dockerfile
# 生产级 Dockerfile
# Stage 1: Build dependencies
FROM rust:1.90-alpine as deps
WORKDIR /app
RUN apk add --no-cache musl-dev openssl-dev

# 只复制依赖文件，利用缓存
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# Stage 2: Build application
FROM deps as builder
COPY src ./src
# 只重新编译应用代码
RUN touch src/main.rs && cargo build --release

# Stage 3: Runtime
FROM alpine:latest
RUN apk add --no-cache ca-certificates

# 创建非 root 用户
RUN addgroup -g 1000 appuser && \
    adduser -D -u 1000 -G appuser appuser

WORKDIR /app
COPY --from=builder /app/target/release/myapp ./

# 切换到非 root 用户
USER appuser

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

EXPOSE 8080
CMD ["./myapp"]
```

---

### 2. 镜像大小优化

```dockerfile
# ❌ 不好：大镜像 (500MB+)
FROM rust:1.90
COPY . .
RUN cargo build --release
CMD ["./target/release/myapp"]

# ✅ 好：小镜像 (<20MB)
FROM rust:1.90-alpine as builder
WORKDIR /app
COPY . .
RUN cargo build --release --target x86_64-unknown-linux-musl

FROM scratch
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/myapp /
CMD ["/myapp"]
```

---

### 3. 安全最佳实践

```dockerfile
# 扫描漏洞
# docker scan myapp:latest

# 使用非 root 用户
USER appuser

# 只读文件系统
VOLUME /app/data
# ... then in Kubernetes:
# securityContext:
#   readOnlyRootFilesystem: true

# 限制能力
# ... in Kubernetes:
# securityContext:
#   capabilities:
#     drop:
#     - ALL
#     add:
#     - NET_BIND_SERVICE
```

---

## ☸️ Kubernetes 部署

### 1. Deployment 配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
  namespace: observability
  labels:
    app: otlp-collector
    version: v1.0.0
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0  # 零停机部署
  selector:
    matchLabels:
      app: otlp-collector
  template:
    metadata:
      labels:
        app: otlp-collector
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8888"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: otlp-collector

      # Anti-affinity: 分散到不同节点
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
                  - otlp-collector
              topologyKey: kubernetes.io/hostname

      containers:
      - name: collector
        image: myapp:v1.0.0
        imagePullPolicy: IfNotPresent

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
        - name: LOG_LEVEL
          valueFrom:
            configMapKeyRef:
              name: otlp-config
              key: log_level
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: otlp-secrets
              key: database_url

        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "2000m"

        # 健康检查
        livenessProbe:
          httpGet:
            path: /health/live
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 3

        readinessProbe:
          httpGet:
            path: /health/ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3

        # 安全上下文
        securityContext:
          runAsNonRoot: true
          runAsUser: 1000
          readOnlyRootFilesystem: true
          capabilities:
            drop:
            - ALL

        volumeMounts:
        - name: config
          mountPath: /etc/otlp
          readOnly: true
        - name: tmp
          mountPath: /tmp

      volumes:
      - name: config
        configMap:
          name: otlp-config
      - name: tmp
        emptyDir: {}
```

---

### 2. Service 和 Ingress

```yaml
# Service
apiVersion: v1
kind: Service
metadata:
  name: otlp-collector
  namespace: observability
spec:
  selector:
    app: otlp-collector
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
    protocol: TCP
  - name: otlp-http
    port: 4318
    targetPort: 4318
    protocol: TCP
  type: ClusterIP
  sessionAffinity: ClientIP

---
# Ingress
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: otlp-collector
  namespace: observability
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/backend-protocol: "GRPC"
spec:
  ingressClassName: nginx
  tls:
  - hosts:
    - otlp.example.com
    secretName: otlp-tls
  rules:
  - host: otlp.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: otlp-collector
            port:
              number: 4317
```

---

### 3. PodDisruptionBudget

```yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: otlp-collector-pdb
  namespace: observability
spec:
  minAvailable: 2  # 至少保持 2 个 Pod 可用
  selector:
    matchLabels:
      app: otlp-collector
```

---

## 🕸️ 服务网格

### 1. Istio 集成

```yaml
# VirtualService: 流量路由
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: otlp-collector
spec:
  hosts:
  - otlp-collector
  http:
  - match:
    - headers:
        version:
          exact: canary
    route:
    - destination:
        host: otlp-collector
        subset: v2
      weight: 10
  - route:
    - destination:
        host: otlp-collector
        subset: v1
      weight: 90

---
# DestinationRule: 负载均衡和熔断
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: otlp-collector
spec:
  host: otlp-collector
  trafficPolicy:
    loadBalancer:
      consistentHash:
        httpHeaderName: x-session-id
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 1024
        http2MaxRequests: 1024
        maxRequestsPerConnection: 10
    outlierDetection:
      consecutiveErrors: 5
      interval: 10s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
  subsets:
  - name: v1
    labels:
      version: v1.0.0
  - name: v2
    labels:
      version: v2.0.0
```

---

### 2. 服务网格观测性

```rust
// 自动注入追踪 Headers
use opentelemetry::propagation::{Injector, Extractor};

pub struct IstioTracing;

impl IstioTracing {
    pub fn inject_headers(headers: &mut HeaderMap) {
        // Istio 会自动传播这些 headers
        // x-request-id
        // x-b3-traceid
        // x-b3-spanid
        // x-b3-parentspanid
        // x-b3-sampled
        // x-b3-flags

        if !headers.contains_key("x-request-id") {
            headers.insert(
                "x-request-id",
                uuid::Uuid::new_v4().to_string().parse().unwrap(),
            );
        }
    }
}
```

---

## ⚙️ 配置管理

### 1. Helm Charts

```yaml
# Chart.yaml
apiVersion: v2
name: otlp-collector
description: OTLP Collector Helm Chart
version: 1.0.0
appVersion: "1.0.0"

# values.yaml
replicaCount: 3

image:
  repository: myregistry/otlp-collector
  tag: "1.0.0"
  pullPolicy: IfNotPresent

resources:
  limits:
    cpu: 2000m
    memory: 2Gi
  requests:
    cpu: 500m
    memory: 512Mi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70

ingress:
  enabled: true
  className: nginx
  hosts:
    - host: otlp.example.com
      paths:
        - path: /
          pathType: Prefix

# 安装
# helm install otlp-collector ./charts/otlp-collector \
#   --namespace observability \
#   --create-namespace \
#   --values values-prod.yaml
```

---

### 2. Kustomize

```yaml
# base/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
- deployment.yaml
- service.yaml
- configmap.yaml

# overlays/prod/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

bases:
- ../../base

replicas:
- name: otlp-collector
  count: 10

images:
- name: otlp-collector
  newTag: v1.2.3

patchesStrategicMerge:
- resources.yaml

# kubectl apply -k overlays/prod
```

---

## 🔄 CI/CD 流水线

### 1. GitHub Actions

```yaml
# .github/workflows/ci-cd.yaml
name: CI/CD Pipeline

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Setup Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable

    - name: Run tests
      run: cargo test --all-features

    - name: Run clippy
      run: cargo clippy -- -D warnings

    - name: Check formatting
      run: cargo fmt -- --check

  build:
    needs: test
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Setup Docker Buildx
      uses: docker/setup-buildx-action@v2

    - name: Login to Registry
      uses: docker/login-action@v2
      with:
        registry: ${{ env.REGISTRY }}
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}

    - name: Build and push
      uses: docker/build-push-action@v4
      with:
        context: .
        push: true
        tags: |
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }}
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:latest
        cache-from: type=gha
        cache-to: type=gha,mode=max

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    steps:
    - uses: actions/checkout@v3

    - name: Setup kubectl
      uses: azure/setup-kubectl@v3

    - name: Configure kubectl
      run: |
        echo "${{ secrets.KUBECONFIG }}" | base64 -d > kubeconfig
        export KUBECONFIG=kubeconfig

    - name: Deploy to Kubernetes
      run: |
        kubectl set image deployment/otlp-collector \
          otlp-collector=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }} \
          -n observability

        kubectl rollout status deployment/otlp-collector -n observability
```

---

## 📂 GitOps

### 1. ArgoCD

```yaml
# Application
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: otlp-collector
  namespace: argocd
spec:
  project: default

  source:
    repoURL: https://github.com/myorg/otlp-collector
    targetRevision: HEAD
    path: k8s/overlays/prod

  destination:
    server: https://kubernetes.default.svc
    namespace: observability

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

### 2. Flux

```yaml
# GitRepository
apiVersion: source.toolkit.fluxcd.io/v1beta2
kind: GitRepository
metadata:
  name: otlp-collector
  namespace: flux-system
spec:
  interval: 1m
  url: https://github.com/myorg/otlp-collector
  ref:
    branch: main

---
# Kustomization
apiVersion: kustomize.toolkit.fluxcd.io/v1beta2
kind: Kustomization
metadata:
  name: otlp-collector
  namespace: flux-system
spec:
  interval: 10m
  path: ./k8s/overlays/prod
  prune: true
  sourceRef:
    kind: GitRepository
    name: otlp-collector
  healthChecks:
  - apiVersion: apps/v1
    kind: Deployment
    name: otlp-collector
    namespace: observability
```

---

## 📚 总结

### 云原生清单

- ✅ **12-Factor App**: 遵循云原生应用原则
- ✅ **容器化**: Docker 最佳实践
- ✅ **Kubernetes**: 生产级部署配置
- ✅ **服务网格**: Istio 集成
- ✅ **配置管理**: Helm, Kustomize
- ✅ **CI/CD**: 自动化流水线
- ✅ **GitOps**: 声明式部署

### 最佳实践

1. **不可变基础设施**: 容器镜像不可变
2. **声明式配置**: Kubernetes YAML
3. **自动化一切**: CI/CD + GitOps
4. **可观测性优先**: Metrics + Logs + Traces
5. **安全第一**: 最小权限、扫描漏洞

---

**文档贡献者:** AI Assistant
**审核状态:** ✅ 已完成
**最后更新:** 2025年10月28日
