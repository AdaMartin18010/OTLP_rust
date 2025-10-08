# Rust OTLP Kubernetes 完整部署指南

> **Rust版本**: 1.90+  
> **Kubernetes**: 1.30+  
> **Helm**: 3.16+  
> **Kustomize**: 5.5+  
> **最后更新**: 2025年10月8日

---

## 📋 目录

- [Rust OTLP Kubernetes 完整部署指南](#rust-otlp-kubernetes-完整部署指南)
  - [📋 目录](#-目录)
  - [1. 容器化基础](#1-容器化基础)
    - [1.1 多阶段Dockerfile优化](#11-多阶段dockerfile优化)
    - [1.2 .dockerignore优化](#12-dockerignore优化)
    - [1.3 构建脚本](#13-构建脚本)
  - [2. Kubernetes基础部署](#2-kubernetes基础部署)
    - [2.1 Namespace配置](#21-namespace配置)
    - [2.2 ConfigMap配置](#22-configmap配置)
    - [2.3 Secret配置](#23-secret配置)
    - [2.4 Deployment配置](#24-deployment配置)
    - [2.5 Service配置](#25-service配置)
    - [2.6 Ingress配置](#26-ingress配置)
  - [3. Helm Chart完整实现](#3-helm-chart完整实现)
    - [3.1 Chart.yaml](#31-chartyaml)
    - [3.2 values.yaml](#32-valuesyaml)
    - [3.3 部署模板](#33-部署模板)
    - [3.4 安装脚本](#34-安装脚本)
  - [4. 自动伸缩配置](#4-自动伸缩配置)
    - [4.1 HPA配置](#41-hpa配置)
    - [4.2 VPA配置](#42-vpa配置)
  - [5. 服务网格集成](#5-服务网格集成)
    - [5.1 Istio配置](#51-istio配置)

---

## 1. 容器化基础

### 1.1 多阶段Dockerfile优化

`Dockerfile`:

```dockerfile
# ================================
# Stage 1: Builder
# ================================
FROM rust:1.90-slim AS builder

WORKDIR /build

# 安装编译依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    protobuf-compiler \
    && rm -rf /var/lib/apt/lists/*

# 缓存依赖层
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码并构建
COPY src ./src
COPY build.rs ./
RUN touch src/main.rs && \
    cargo build --release --bin otlp-service

# 优化二进制大小
RUN strip target/release/otlp-service

# ================================
# Stage 2: Runtime
# ================================
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -m -u 1000 otlp && \
    mkdir -p /app /data && \
    chown -R otlp:otlp /app /data

WORKDIR /app

# 复制二进制文件
COPY --from=builder /build/target/release/otlp-service /usr/local/bin/

# 复制配置文件
COPY config/ /app/config/

# 切换到非root用户
USER otlp

# 环境变量
ENV RUST_LOG=info \
    RUST_BACKTRACE=1 \
    CONFIG_PATH=/app/config/production.yaml

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=10s --retries=3 \
    CMD ["/usr/local/bin/otlp-service", "health"]

EXPOSE 8080 9090

CMD ["/usr/local/bin/otlp-service"]
```

### 1.2 .dockerignore优化

`.dockerignore`:

```plaintext
# Git
.git/
.gitignore

# 构建产物
target/
**/*.rs.bk
**/*.pdb

# IDE
.vscode/
.idea/
*.swp
*.swo

# 文档
*.md
docs/
examples/

# 测试
tests/
benches/
fixtures/

# CI/CD
.github/
.gitlab-ci.yml

# 本地配置
.env
.env.local
config/local.yaml
```

### 1.3 构建脚本

`scripts/build-docker.sh`:

```bash
#!/bin/bash

set -e

VERSION=${1:-latest}
REGISTRY=${REGISTRY:-ghcr.io/your-org}
IMAGE_NAME=otlp-service

echo "🐳 构建Docker镜像..."
echo "  版本: $VERSION"
echo "  仓库: $REGISTRY"

# 构建镜像
docker build \
    --build-arg RUST_VERSION=1.90 \
    --build-arg BUILD_DATE=$(date -u +'%Y-%m-%dT%H:%M:%SZ') \
    --build-arg VCS_REF=$(git rev-parse --short HEAD) \
    --tag ${REGISTRY}/${IMAGE_NAME}:${VERSION} \
    --tag ${REGISTRY}/${IMAGE_NAME}:latest \
    --platform linux/amd64,linux/arm64 \
    .

echo "✅ 镜像构建完成"

# 推送镜像
if [ "$PUSH" = "true" ]; then
    echo "📤 推送镜像到仓库..."
    docker push ${REGISTRY}/${IMAGE_NAME}:${VERSION}
    docker push ${REGISTRY}/${IMAGE_NAME}:latest
    echo "✅ 镜像推送完成"
fi

# 镜像信息
echo "📊 镜像信息:"
docker images ${REGISTRY}/${IMAGE_NAME}:${VERSION}
```

---

## 2. Kubernetes基础部署

### 2.1 Namespace配置

`k8s/base/namespace.yaml`:

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: otlp-system
  labels:
    name: otlp-system
    environment: production
    managed-by: kubectl
```

### 2.2 ConfigMap配置

`k8s/base/configmap.yaml`:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-config
  namespace: otlp-system
data:
  production.yaml: |
    server:
      host: "0.0.0.0"
      port: 8080
      grpc_port: 4317
      
    exporter:
      endpoint: "http://otel-collector:4318"
      timeout: 30s
      batch_size: 1000
      
    tracing:
      service_name: "otlp-service"
      sampling_rate: 1.0
      
    logging:
      level: "info"
      format: "json"
      
    metrics:
      enabled: true
      port: 9090
      path: "/metrics"

---
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-env
  namespace: otlp-system
data:
  RUST_LOG: "info,otlp_service=debug"
  RUST_BACKTRACE: "1"
  OTEL_EXPORTER_OTLP_ENDPOINT: "http://otel-collector:4318"
```

### 2.3 Secret配置

`k8s/base/secret.yaml`:

```yaml
apiVersion: v1
kind: Secret
metadata:
  name: otlp-secrets
  namespace: otlp-system
type: Opaque
stringData:
  # TLS证书
  tls.crt: |
    -----BEGIN CERTIFICATE-----
    ...
    -----END CERTIFICATE-----
  
  tls.key: |
    -----BEGIN PRIVATE KEY-----
    ...
    -----END PRIVATE KEY-----
  
  # API密钥
  api-key: "your-secret-api-key"
  
  # 数据库连接
  database-url: "postgresql://user:pass@postgres:5432/otlp"
```

### 2.4 Deployment配置

`k8s/base/deployment.yaml`:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-service
  namespace: otlp-system
  labels:
    app: otlp-service
    version: v1.0.0
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  
  selector:
    matchLabels:
      app: otlp-service
  
  template:
    metadata:
      labels:
        app: otlp-service
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    
    spec:
      serviceAccountName: otlp-service
      
      # 安全上下文
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        fsGroup: 1000
        seccompProfile:
          type: RuntimeDefault
      
      # Init容器
      initContainers:
      - name: check-dependencies
        image: busybox:1.36
        command: 
        - sh
        - -c
        - |
          until nc -z otel-collector 4318; do
            echo "等待otel-collector就绪..."
            sleep 2
          done
      
      containers:
      - name: otlp-service
        image: ghcr.io/your-org/otlp-service:latest
        imagePullPolicy: IfNotPresent
        
        ports:
        - name: http
          containerPort: 8080
          protocol: TCP
        - name: grpc
          containerPort: 4317
          protocol: TCP
        - name: metrics
          containerPort: 9090
          protocol: TCP
        
        env:
        - name: CONFIG_PATH
          value: /app/config/production.yaml
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: POD_IP
          valueFrom:
            fieldRef:
              fieldPath: status.podIP
        
        envFrom:
        - configMapRef:
            name: otlp-env
        - secretRef:
            name: otlp-secrets
        
        resources:
          requests:
            cpu: 250m
            memory: 512Mi
          limits:
            cpu: 1000m
            memory: 1Gi
        
        # 存活探针
        livenessProbe:
          httpGet:
            path: /health/live
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
          timeoutSeconds: 5
          successThreshold: 1
          failureThreshold: 3
        
        # 就绪探针
        readinessProbe:
          httpGet:
            path: /health/ready
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
          timeoutSeconds: 3
          successThreshold: 1
          failureThreshold: 3
        
        # 启动探针
        startupProbe:
          httpGet:
            path: /health/startup
            port: 8080
          initialDelaySeconds: 0
          periodSeconds: 5
          timeoutSeconds: 3
          successThreshold: 1
          failureThreshold: 30
        
        volumeMounts:
        - name: config
          mountPath: /app/config
          readOnly: true
        - name: tls
          mountPath: /app/tls
          readOnly: true
        - name: data
          mountPath: /data
        
        securityContext:
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          runAsNonRoot: true
          runAsUser: 1000
          capabilities:
            drop:
            - ALL
      
      volumes:
      - name: config
        configMap:
          name: otlp-config
      - name: tls
        secret:
          secretName: otlp-secrets
          items:
          - key: tls.crt
            path: tls.crt
          - key: tls.key
            path: tls.key
      - name: data
        emptyDir:
          sizeLimit: 1Gi
      
      # 亲和性配置
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
                  - otlp-service
              topologyKey: kubernetes.io/hostname
```

### 2.5 Service配置

`k8s/base/service.yaml`:

```yaml
apiVersion: v1
kind: Service
metadata:
  name: otlp-service
  namespace: otlp-system
  labels:
    app: otlp-service
  annotations:
    service.beta.kubernetes.io/aws-load-balancer-type: "nlb"
spec:
  type: ClusterIP
  selector:
    app: otlp-service
  ports:
  - name: http
    protocol: TCP
    port: 8080
    targetPort: 8080
  - name: grpc
    protocol: TCP
    port: 4317
    targetPort: 4317
  - name: metrics
    protocol: TCP
    port: 9090
    targetPort: 9090
  
  sessionAffinity: ClientIP
  sessionAffinityConfig:
    clientIP:
      timeoutSeconds: 10800

---
# Headless Service for StatefulSet
apiVersion: v1
kind: Service
metadata:
  name: otlp-service-headless
  namespace: otlp-system
  labels:
    app: otlp-service
spec:
  clusterIP: None
  selector:
    app: otlp-service
  ports:
  - name: http
    port: 8080
  - name: grpc
    port: 4317
```

### 2.6 Ingress配置

`k8s/base/ingress.yaml`:

```yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: otlp-service
  namespace: otlp-system
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/backend-protocol: "GRPC"
    nginx.ingress.kubernetes.io/grpc-backend: "true"
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
            name: otlp-service
            port:
              number: 8080
      - path: /v1/traces
        pathType: Prefix
        backend:
          service:
            name: otlp-service
            port:
              number: 4317
```

---

## 3. Helm Chart完整实现

### 3.1 Chart.yaml

`helm/otlp-service/Chart.yaml`:

```yaml
apiVersion: v2
name: otlp-service
description: Rust OTLP Service Helm Chart
type: application
version: 1.0.0
appVersion: "1.0.0"
keywords:
  - opentelemetry
  - otlp
  - observability
  - rust
home: https://github.com/your-org/otlp-service
sources:
  - https://github.com/your-org/otlp-service
maintainers:
  - name: Your Team
    email: team@example.com
dependencies:
  - name: opentelemetry-collector
    version: "0.111.0"
    repository: "https://open-telemetry.github.io/opentelemetry-helm-charts"
    condition: collector.enabled
```

### 3.2 values.yaml

`helm/otlp-service/values.yaml`:

```yaml
# 镜像配置
image:
  repository: ghcr.io/your-org/otlp-service
  pullPolicy: IfNotPresent
  tag: "latest"

imagePullSecrets: []

# 副本数
replicaCount: 3

# 服务配置
service:
  type: ClusterIP
  http:
    port: 8080
    targetPort: 8080
  grpc:
    port: 4317
    targetPort: 4317
  metrics:
    port: 9090
    targetPort: 9090

# Ingress配置
ingress:
  enabled: true
  className: "nginx"
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
  hosts:
    - host: otlp.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: otlp-tls
      hosts:
        - otlp.example.com

# 资源配置
resources:
  requests:
    cpu: 250m
    memory: 512Mi
  limits:
    cpu: 1000m
    memory: 1Gi

# 自动伸缩
autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80

# 配置
config:
  server:
    host: "0.0.0.0"
    port: 8080
    grpc_port: 4317
  
  exporter:
    endpoint: "http://otel-collector:4318"
    timeout: 30s
    batch_size: 1000
  
  tracing:
    service_name: "otlp-service"
    sampling_rate: 1.0

# 环境变量
env:
  - name: RUST_LOG
    value: "info"
  - name: RUST_BACKTRACE
    value: "1"

# 健康检查
livenessProbe:
  httpGet:
    path: /health/live
    port: 8080
  initialDelaySeconds: 30
  periodSeconds: 10

readinessProbe:
  httpGet:
    path: /health/ready
    port: 8080
  initialDelaySeconds: 10
  periodSeconds: 5

startupProbe:
  httpGet:
    path: /health/startup
    port: 8080
  initialDelaySeconds: 0
  periodSeconds: 5
  failureThreshold: 30

# 安全上下文
podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1000
  fsGroup: 1000
  seccompProfile:
    type: RuntimeDefault

securityContext:
  allowPrivilegeEscalation: false
  readOnlyRootFilesystem: true
  runAsNonRoot: true
  runAsUser: 1000
  capabilities:
    drop:
    - ALL

# 持久化存储
persistence:
  enabled: false
  storageClass: ""
  accessMode: ReadWriteOnce
  size: 10Gi

# ServiceMonitor (Prometheus Operator)
serviceMonitor:
  enabled: true
  interval: 30s
  scrapeTimeout: 10s

# PodDisruptionBudget
podDisruptionBudget:
  enabled: true
  minAvailable: 1

# NetworkPolicy
networkPolicy:
  enabled: true
  policyTypes:
    - Ingress
    - Egress

# OpenTelemetry Collector
collector:
  enabled: true
  mode: deployment
```

### 3.3 部署模板

`helm/otlp-service/templates/deployment.yaml`:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: {{ include "otlp-service.fullname" . }}
  namespace: {{ .Release.Namespace }}
  labels:
    {{- include "otlp-service.labels" . | nindent 4 }}
spec:
  {{- if not .Values.autoscaling.enabled }}
  replicas: {{ .Values.replicaCount }}
  {{- end }}
  
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  
  selector:
    matchLabels:
      {{- include "otlp-service.selectorLabels" . | nindent 6 }}
  
  template:
    metadata:
      annotations:
        checksum/config: {{ include (print $.Template.BasePath "/configmap.yaml") . | sha256sum }}
        {{- with .Values.podAnnotations }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
      labels:
        {{- include "otlp-service.selectorLabels" . | nindent 8 }}
    
    spec:
      {{- with .Values.imagePullSecrets }}
      imagePullSecrets:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      
      serviceAccountName: {{ include "otlp-service.serviceAccountName" . }}
      
      securityContext:
        {{- toYaml .Values.podSecurityContext | nindent 8 }}
      
      containers:
      - name: {{ .Chart.Name }}
        image: "{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"
        imagePullPolicy: {{ .Values.image.pullPolicy }}
        
        ports:
        - name: http
          containerPort: {{ .Values.service.http.targetPort }}
          protocol: TCP
        - name: grpc
          containerPort: {{ .Values.service.grpc.targetPort }}
          protocol: TCP
        - name: metrics
          containerPort: {{ .Values.service.metrics.targetPort }}
          protocol: TCP
        
        env:
        {{- range .Values.env }}
        - name: {{ .name }}
          value: {{ .value | quote }}
        {{- end }}
        
        livenessProbe:
          {{- toYaml .Values.livenessProbe | nindent 10 }}
        
        readinessProbe:
          {{- toYaml .Values.readinessProbe | nindent 10 }}
        
        startupProbe:
          {{- toYaml .Values.startupProbe | nindent 10 }}
        
        resources:
          {{- toYaml .Values.resources | nindent 10 }}
        
        securityContext:
          {{- toYaml .Values.securityContext | nindent 10 }}
        
        volumeMounts:
        - name: config
          mountPath: /app/config
          readOnly: true
        {{- if .Values.persistence.enabled }}
        - name: data
          mountPath: /data
        {{- end }}
      
      volumes:
      - name: config
        configMap:
          name: {{ include "otlp-service.fullname" . }}
      {{- if .Values.persistence.enabled }}
      - name: data
        persistentVolumeClaim:
          claimName: {{ include "otlp-service.fullname" . }}
      {{- end }}
```

### 3.4 安装脚本

`scripts/helm-install.sh`:

```bash
#!/bin/bash

set -e

NAMESPACE=${NAMESPACE:-otlp-system}
RELEASE_NAME=${RELEASE_NAME:-otlp-service}
CHART_PATH=${CHART_PATH:-./helm/otlp-service}

echo "📦 安装 Helm Chart..."
echo "  Namespace: $NAMESPACE"
echo "  Release: $RELEASE_NAME"

# 创建命名空间
kubectl create namespace $NAMESPACE --dry-run=client -o yaml | kubectl apply -f -

# 添加依赖仓库
helm repo add open-telemetry https://open-telemetry.github.io/opentelemetry-helm-charts
helm repo update

# 安装Chart
helm upgrade --install $RELEASE_NAME $CHART_PATH \
    --namespace $NAMESPACE \
    --create-namespace \
    --wait \
    --timeout 10m \
    --values ${CHART_PATH}/values.yaml

echo "✅ Helm Chart安装完成"

# 验证部署
echo "🔍 验证部署..."
kubectl wait --for=condition=available --timeout=5m \
    deployment/$RELEASE_NAME -n $NAMESPACE

kubectl get all -n $NAMESPACE

echo "🎉 部署成功！"
```

---

## 4. 自动伸缩配置

### 4.1 HPA配置

`k8s/base/hpa.yaml`:

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-service-hpa
  namespace: otlp-system
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-service
  
  minReplicas: 3
  maxReplicas: 20
  
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
      - type: Pods
        value: 2
        periodSeconds: 60
      selectPolicy: Min
    
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 30
      - type: Pods
        value: 4
        periodSeconds: 30
      selectPolicy: Max
  
  metrics:
  # CPU利用率
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  
  # 内存利用率
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  
  # 自定义指标：请求数
  - type: Pods
    pods:
      metric:
        name: http_requests_per_second
      target:
        type: AverageValue
        averageValue: "1k"
```

### 4.2 VPA配置

`k8s/base/vpa.yaml`:

```yaml
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: otlp-service-vpa
  namespace: otlp-system
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-service
  
  updatePolicy:
    updateMode: "Auto"
  
  resourcePolicy:
    containerPolicies:
    - containerName: otlp-service
      minAllowed:
        cpu: 250m
        memory: 512Mi
      maxAllowed:
        cpu: 2000m
        memory: 4Gi
      controlledResources:
        - cpu
        - memory
```

---

## 5. 服务网格集成

### 5.1 Istio配置

`k8s/istio/virtual-service.yaml`:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: otlp-service
  namespace: otlp-system
spec:
  hosts:
  - otlp-service
  - otlp.example.com
  
  http:
  - match:
    - uri:
        prefix: "/v1/traces"
    route:
    - destination:
        host: otlp-service
        port:
          number: 8080
      weight: 100
    retries:
      attempts: 3
      perTryTimeout: 5s
      retryOn: 5xx,reset,connect-failure,refused-stream
    timeout: 30s
    
  - match:
    - uri:
        prefix: "/"
    route:
    - destination:
        host: otlp-service
        port:
          number: 8080
      weight: 100

---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: otlp-service
  namespace: otlp-system
spec:
  host: otlp-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 1000
      http:
        http1MaxPendingRequests: 1000
        http2MaxRequests: 1000
        maxRequestsPerConnection: 2
    loadBalancer:
      simple: LEAST_REQUEST
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
      minHealthPercent: 40
```

---

**文档未完待续，由于篇幅限制，请查看完整版本...**

---

**文档日期**: 2025年10月8日  
**创建者**: AI Assistant  
**项目**: OTLP Rust 标准深度梳理  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [📊 监控与告警](../20_监控与告警/01_Prometheus_Grafana完整集成指南.md)
