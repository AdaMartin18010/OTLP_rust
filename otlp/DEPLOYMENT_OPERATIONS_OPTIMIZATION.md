# 🚀 OTLP Rust 部署和运维优化方案

## 📋 优化概览

**优化目标**: 实现云原生部署、自动化运维、高可用性和可观测性  
**优化范围**: 容器化、Kubernetes、监控告警、CI/CD、安全加固  
**实施周期**: 4-6周  
**预期收益**: 企业级生产环境部署标准

## 🎯 云原生部署架构

### 整体架构图

```text
┌─────────────────────────────────────────────────────────┐
│                    Kubernetes Cluster                   │
│                                                         │
│  ┌─────────────────┐  ┌─────────────────┐  ┌──────────┐ │
│  │   OTLP Client   │  │   OTLP Server   │  │  Jaeger  │ │
│  │     Pods        │  │     Pods        │  │   Pods   │ │
│  └─────────────────┘  └─────────────────┘  └──────────┘ │
│           │                     │               │       │
│  ┌─────────────────┐  ┌─────────────────┐  ┌──────────┐ │
│  │   Service       │  │   Service       │  │ Service  │ │
│  │   Mesh          │  │   Mesh          │  │  Mesh    │ │
│  └─────────────────┘  └─────────────────┘  └──────────┘ │
│                                                         │
│  ┌─────────────────────────────────────────────────────┐ │
│  │              Monitoring & Observability             │ │
│  │  Prometheus + Grafana + Jaeger + ELK Stack         │ │
│  └─────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
```

## 🐳 容器化优化

### 1. 多阶段Dockerfile

```dockerfile
# 构建阶段
FROM rust:1.90-slim as builder

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖（利用Docker缓存）
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# 复制源代码
COPY src ./src
COPY examples ./examples
COPY tests ./tests

# 构建应用
RUN cargo build --release --bin otlp-client

# 运行时阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r otlp && useradd -r -g otlp otlp

# 设置工作目录
WORKDIR /app

# 复制二进制文件
COPY --from=builder /app/target/release/otlp-client /app/otlp-client

# 设置权限
RUN chown -R otlp:otlp /app
USER otlp

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 暴露端口
EXPOSE 8080 4317 4318

# 启动命令
CMD ["./otlp-client"]
```

### 2. 优化构建配置

```dockerfile
# 优化版本 - 使用distroless镜像
FROM gcr.io/distroless/cc-debian12

# 复制二进制文件
COPY --from=builder /app/target/release/otlp-client /app/otlp-client

# 设置工作目录
WORKDIR /app

# 暴露端口
EXPOSE 8080 4317 4318

# 启动命令
ENTRYPOINT ["/app/otlp-client"]
```

### 3. 构建优化脚本

```bash
#!/bin/bash
# build.sh - 优化的构建脚本

set -e

# 配置变量
IMAGE_NAME="otlp-rust"
VERSION=${1:-latest}
REGISTRY=${2:-docker.io/your-org}

# 构建参数
BUILD_ARGS="--build-arg RUST_VERSION=1.90"
BUILD_ARGS="$BUILD_ARGS --build-arg CARGO_PROFILE=release"
BUILD_ARGS="$BUILD_ARGS --build-arg CARGO_FEATURES=full"

# 多平台构建
PLATFORMS="linux/amd64,linux/arm64"

echo "Building OTLP Rust image..."
docker buildx build \
    --platform $PLATFORMS \
    --tag $REGISTRY/$IMAGE_NAME:$VERSION \
    --tag $REGISTRY/$IMAGE_NAME:latest \
    --push \
    $BUILD_ARGS \
    .

echo "Build completed successfully!"
```

## ☸️ Kubernetes部署配置

### 1. 命名空间配置

```yaml
# namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: otlp-system
  labels:
    name: otlp-system
    app.kubernetes.io/name: otlp
    app.kubernetes.io/version: "1.0.0"
```

### 2. 配置映射

```yaml
# configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-config
  namespace: otlp-system
data:
  config.toml: |
    [otlp]
    endpoint = "http://jaeger-collector:14268"
    protocol = "grpc"
    batch_size = 100
    timeout = "5s"
    
    [resilience]
    max_retries = 3
    retry_delay = "100ms"
    circuit_breaker_threshold = 5
    
    [monitoring]
    metrics_enabled = true
    health_check_interval = "30s"
    
  logging.yaml: |
    version: 1
    disable_existing_loggers: false
    formatters:
      standard:
        format: '%(asctime)s [%(levelname)s] %(name)s: %(message)s'
    handlers:
      console:
        class: logging.StreamHandler
        level: INFO
        formatter: standard
        stream: ext://sys.stdout
    root:
      level: INFO
      handlers: [console]
```

### 3. 部署配置

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-client
  namespace: otlp-system
  labels:
    app: otlp-client
    app.kubernetes.io/name: otlp-client
    app.kubernetes.io/version: "1.0.0"
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-client
  template:
    metadata:
      labels:
        app: otlp-client
        app.kubernetes.io/name: otlp-client
        app.kubernetes.io/version: "1.0.0"
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: otlp-client
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        runAsGroup: 1000
        fsGroup: 1000
      containers:
      - name: otlp-client
        image: docker.io/your-org/otlp-rust:latest
        imagePullPolicy: Always
        ports:
        - name: http
          containerPort: 8080
          protocol: TCP
        - name: grpc
          containerPort: 4317
          protocol: TCP
        - name: http-otlp
          containerPort: 4318
          protocol: TCP
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_CONFIG_PATH
          value: "/etc/otlp/config.toml"
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        volumeMounts:
        - name: config
          mountPath: /etc/otlp
          readOnly: true
        - name: tmp
          mountPath: /tmp
        livenessProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 30
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /ready
            port: http
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3
        startupProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 30
      volumes:
      - name: config
        configMap:
          name: otlp-config
      - name: tmp
        emptyDir: {}
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
                  - otlp-client
              topologyKey: kubernetes.io/hostname
      nodeSelector:
        kubernetes.io/os: linux
      tolerations:
      - key: "node-role.kubernetes.io/master"
        operator: "Exists"
        effect: "NoSchedule"
```

### 4. 服务配置

```yaml
# service.yaml
apiVersion: v1
kind: Service
metadata:
  name: otlp-client
  namespace: otlp-system
  labels:
    app: otlp-client
    app.kubernetes.io/name: otlp-client
    app.kubernetes.io/version: "1.0.0"
  annotations:
    prometheus.io/scrape: "true"
    prometheus.io/port: "8080"
    prometheus.io/path: "/metrics"
spec:
  type: ClusterIP
  ports:
  - name: http
    port: 8080
    targetPort: http
    protocol: TCP
  - name: grpc
    port: 4317
    targetPort: grpc
    protocol: TCP
  - name: http-otlp
    port: 4318
    targetPort: http-otlp
    protocol: TCP
  selector:
    app: otlp-client
```

### 5. 服务账户和RBAC

```yaml
# rbac.yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otlp-client
  namespace: otlp-system
  labels:
    app: otlp-client
---
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  name: otlp-client
  namespace: otlp-system
rules:
- apiGroups: [""]
  resources: ["pods", "services", "endpoints"]
  verbs: ["get", "list", "watch"]
- apiGroups: ["apps"]
  resources: ["deployments", "replicasets"]
  verbs: ["get", "list", "watch"]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: otlp-client
  namespace: otlp-system
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: Role
  name: otlp-client
subjects:
- kind: ServiceAccount
  name: otlp-client
  namespace: otlp-system
```

## 📊 监控和可观测性

### 1. Prometheus监控配置

```yaml
# prometheus-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: prometheus-config
  namespace: monitoring
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
      evaluation_interval: 15s
    
    rule_files:
      - "otlp_rules.yml"
    
    scrape_configs:
    - job_name: 'otlp-client'
      kubernetes_sd_configs:
      - role: endpoints
        namespaces:
          names:
          - otlp-system
      relabel_configs:
      - source_labels: [__meta_kubernetes_service_annotation_prometheus_io_scrape]
        action: keep
        regex: true
      - source_labels: [__meta_kubernetes_service_annotation_prometheus_io_path]
        action: replace
        target_label: __metrics_path__
        regex: (.+)
      - source_labels: [__address__, __meta_kubernetes_service_annotation_prometheus_io_port]
        action: replace
        regex: ([^:]+)(?::\d+)?;(\d+)
        replacement: $1:$2
        target_label: __address__
      - action: labelmap
        regex: __meta_kubernetes_service_label_(.+)
      - source_labels: [__meta_kubernetes_namespace]
        action: replace
        target_label: kubernetes_namespace
      - source_labels: [__meta_kubernetes_service_name]
        action: replace
        target_label: kubernetes_name
    
    alerting:
      alertmanagers:
      - static_configs:
        - targets:
          - alertmanager:9093
```

### 2. 告警规则

```yaml
# otlp-rules.yml
groups:
- name: otlp.rules
  rules:
  - alert: OTLPClientDown
    expr: up{job="otlp-client"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "OTLP Client is down"
      description: "OTLP Client has been down for more than 1 minute."
  
  - alert: OTLPClientHighErrorRate
    expr: rate(otlp_requests_failed_total[5m]) / rate(otlp_requests_total[5m]) > 0.1
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "OTLP Client high error rate"
      description: "OTLP Client error rate is {{ $value | humanizePercentage }} for more than 2 minutes."
  
  - alert: OTLPClientHighLatency
    expr: histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m])) > 1
    for: 3m
    labels:
      severity: warning
    annotations:
      summary: "OTLP Client high latency"
      description: "OTLP Client 95th percentile latency is {{ $value }}s for more than 3 minutes."
  
  - alert: OTLPClientCircuitBreakerOpen
    expr: otlp_circuit_breaker_state == 1
    for: 30s
    labels:
      severity: critical
    annotations:
      summary: "OTLP Client circuit breaker is open"
      description: "OTLP Client circuit breaker has been open for more than 30 seconds."
```

### 3. Grafana仪表板

```json
{
  "dashboard": {
    "title": "OTLP Client Dashboard",
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_requests_total[5m])",
            "legendFormat": "{{instance}}"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_requests_failed_total[5m]) / rate(otlp_requests_total[5m])",
            "legendFormat": "{{instance}}"
          }
        ]
      },
      {
        "title": "Response Time",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          },
          {
            "expr": "histogram_quantile(0.50, rate(otlp_request_duration_seconds_bucket[5m]))",
            "legendFormat": "50th percentile"
          }
        ]
      },
      {
        "title": "Circuit Breaker Status",
        "type": "stat",
        "targets": [
          {
            "expr": "otlp_circuit_breaker_state",
            "legendFormat": "State"
          }
        ]
      }
    ]
  }
}
```

## 🔄 CI/CD流水线

### 1. GitHub Actions工作流

```yaml
# .github/workflows/ci-cd.yml
name: CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  REGISTRY: docker.io/your-org
  IMAGE_NAME: otlp-rust

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: 1.90
        components: rustfmt, clippy
    
    - name: Cache dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
    
    - name: Run tests
      run: |
        cargo test --lib
        cargo test --test integration_tests
        cargo test --test e2e_tests
    
    - name: Run clippy
      run: cargo clippy -- -D warnings
    
    - name: Run fmt check
      run: cargo fmt -- --check
    
    - name: Generate coverage
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Html --output-dir coverage
    
    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: coverage/tarpaulin-report.html

  build:
    needs: test
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v2
    
    - name: Login to Docker Hub
      uses: docker/login-action@v2
      with:
        username: ${{ secrets.DOCKER_USERNAME }}
        password: ${{ secrets.DOCKER_PASSWORD }}
    
    - name: Build and push
      uses: docker/build-push-action@v4
      with:
        context: .
        platforms: linux/amd64,linux/arm64
        push: true
        tags: |
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:latest
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }}

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Configure kubectl
      uses: azure/k8s-set-context@v3
      with:
        method: kubeconfig
        kubeconfig: ${{ secrets.KUBE_CONFIG }}
    
    - name: Deploy to Kubernetes
      run: |
        kubectl set image deployment/otlp-client otlp-client=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }} -n otlp-system
        kubectl rollout status deployment/otlp-client -n otlp-system
    
    - name: Run smoke tests
      run: |
        kubectl run smoke-test --image=curlimages/curl --rm -i --restart=Never -- \
          curl -f http://otlp-client.otlp-system.svc.cluster.local:8080/health
```

### 2. Helm Chart

```yaml
# helm/otlp-client/Chart.yaml
apiVersion: v2
name: otlp-client
description: OTLP Rust Client Helm Chart
type: application
version: 1.0.0
appVersion: "1.0.0"

dependencies:
- name: prometheus
  version: 19.0.0
  repository: https://prometheus-community.github.io/helm-charts
  condition: prometheus.enabled
- name: grafana
  version: 6.50.0
  repository: https://grafana.github.io/helm-charts
  condition: grafana.enabled
```

```yaml
# helm/otlp-client/values.yaml
replicaCount: 3

image:
  repository: docker.io/your-org/otlp-rust
  tag: latest
  pullPolicy: Always

service:
  type: ClusterIP
  port: 8080
  grpcPort: 4317
  httpOtlpPort: 4318

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

nodeSelector: {}

tolerations: []

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
            - otlp-client
        topologyKey: kubernetes.io/hostname

config:
  endpoint: "http://jaeger-collector:14268"
  protocol: "grpc"
  batch_size: 100
  timeout: "5s"

monitoring:
  enabled: true
  serviceMonitor:
    enabled: true
    interval: 30s
    scrapeTimeout: 10s

prometheus:
  enabled: true
  server:
    persistentVolume:
      enabled: true
      size: 10Gi

grafana:
  enabled: true
  adminPassword: "admin"
  persistence:
    enabled: true
    size: 5Gi
```

## 🔒 安全加固

### 1. 安全策略

```yaml
# security-policy.yaml
apiVersion: policy/v1beta1
kind: PodSecurityPolicy
metadata:
  name: otlp-client-psp
spec:
  privileged: false
  allowPrivilegeEscalation: false
  requiredDropCapabilities:
    - ALL
  volumes:
    - 'configMap'
    - 'emptyDir'
    - 'projected'
    - 'secret'
    - 'downwardAPI'
    - 'persistentVolumeClaim'
  runAsUser:
    rule: 'MustRunAsNonRoot'
  seLinux:
    rule: 'RunAsAny'
  fsGroup:
    rule: 'RunAsAny'
```

### 2. 网络策略

```yaml
# network-policy.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-client-netpol
  namespace: otlp-system
spec:
  podSelector:
    matchLabels:
      app: otlp-client
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: monitoring
    ports:
    - protocol: TCP
      port: 8080
  - from:
    - namespaceSelector:
        matchLabels:
          name: istio-system
    ports:
    - protocol: TCP
      port: 4317
    - protocol: TCP
      port: 4318
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: jaeger
    ports:
    - protocol: TCP
      port: 14268
  - to: []
    ports:
    - protocol: TCP
      port: 53
    - protocol: UDP
      port: 53
```

## 📈 性能优化

### 1. 资源调优

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-client-hpa
  namespace: otlp-system
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-client
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
        name: otlp_requests_per_second
      target:
        type: AverageValue
        averageValue: "100"
```

### 2. 垂直扩缩容

```yaml
# vpa.yaml
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: otlp-client-vpa
  namespace: otlp-system
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-client
  updatePolicy:
    updateMode: "Auto"
  resourcePolicy:
    containerPolicies:
    - containerName: otlp-client
      minAllowed:
        cpu: 100m
        memory: 128Mi
      maxAllowed:
        cpu: 1000m
        memory: 1Gi
```

## 🛠️ 运维工具

### 1. 部署脚本

```bash
#!/bin/bash
# deploy.sh - 自动化部署脚本

set -e

NAMESPACE="otlp-system"
RELEASE_NAME="otlp-client"
CHART_PATH="./helm/otlp-client"
VALUES_FILE="./helm/otlp-client/values.yaml"

echo "Deploying OTLP Client to Kubernetes..."

# 检查kubectl连接
kubectl cluster-info

# 创建命名空间
kubectl create namespace $NAMESPACE --dry-run=client -o yaml | kubectl apply -f -

# 部署Helm Chart
helm upgrade --install $RELEASE_NAME $CHART_PATH \
    --namespace $NAMESPACE \
    --values $VALUES_FILE \
    --wait \
    --timeout 10m

# 等待部署完成
kubectl rollout status deployment/otlp-client -n $NAMESPACE

# 运行健康检查
kubectl run health-check --image=curlimages/curl --rm -i --restart=Never -n $NAMESPACE -- \
    curl -f http://otlp-client:8080/health

echo "Deployment completed successfully!"
```

### 2. 监控脚本

```bash
#!/bin/bash
# monitor.sh - 监控脚本

NAMESPACE="otlp-system"

echo "OTLP Client Status:"
kubectl get pods -n $NAMESPACE -l app=otlp-client

echo -e "\nOTLP Client Logs (last 10 lines):"
kubectl logs -n $NAMESPACE -l app=otlp-client --tail=10

echo -e "\nOTLP Client Metrics:"
kubectl top pods -n $NAMESPACE -l app=otlp-client

echo -e "\nOTLP Client Events:"
kubectl get events -n $NAMESPACE --sort-by='.lastTimestamp' | grep otlp-client
```

## 📊 性能基准

### 部署性能指标

| 指标 | 目标值 | 监控方式 |
|------|--------|----------|
| 部署时间 | <5分钟 | CI/CD |
| 启动时间 | <30秒 | 健康检查 |
| 内存使用 | <512Mi | Prometheus |
| CPU使用 | <500m | Prometheus |
| 可用性 | >99.9% | 监控告警 |

### 运维效率指标

| 指标 | 目标值 | 改进措施 |
|------|--------|----------|
| 部署频率 | 每日多次 | 自动化CI/CD |
| 故障恢复时间 | <5分钟 | 自动扩缩容 |
| 配置变更时间 | <2分钟 | GitOps |
| 监控覆盖率 | >95% | 全面监控 |

---

**部署负责人**: OTLP Rust 团队  
**预计完成时间**: 2025年4月  
**状态**: 🚀 进行中
