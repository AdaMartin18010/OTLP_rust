# 生产环境部署 - Rust 完整指南

## 目录

- [生产环境部署 - Rust 完整指南](#生产环境部署---rust-完整指南)
  - [目录](#目录)
  - [1. 部署架构](#1-部署架构)
    - [1.1 单机部署](#11-单机部署)
    - [1.2 集群部署](#12-集群部署)
    - [1.3 云原生部署](#13-云原生部署)
  - [2. Docker 容器化](#2-docker-容器化)
    - [2.1 生产级 Dockerfile](#21-生产级-dockerfile)
    - [2.2 多阶段构建](#22-多阶段构建)
    - [2.3 Docker Compose](#23-docker-compose)
  - [3. Kubernetes 部署](#3-kubernetes-部署)
    - [3.1 Deployment](#31-deployment)
    - [3.2 Service](#32-service)
    - [3.3 ConfigMap](#33-configmap)
    - [3.4 Secret](#34-secret)
    - [3.5 Ingress](#35-ingress)
  - [4. 高可用配置](#4-高可用配置)
    - [4.1 多副本部署](#41-多副本部署)
    - [4.2 负载均衡](#42-负载均衡)
    - [4.3 健康检查](#43-健康检查)
  - [5. 监控与告警](#5-监控与告警)
    - [5.1 Prometheus 监控](#51-prometheus-监控)
    - [5.2 Grafana 仪表板](#52-grafana-仪表板)
    - [5.3 告警规则](#53-告警规则)
  - [6. 日志管理](#6-日志管理)
    - [6.1 结构化日志](#61-结构化日志)
    - [6.2 ELK Stack](#62-elk-stack)
    - [6.3 Loki](#63-loki)
  - [7. 性能优化](#7-性能优化)
    - [7.1 编译优化](#71-编译优化)
    - [7.2 运行时优化](#72-运行时优化)
    - [7.3 数据库连接池](#73-数据库连接池)
  - [8. 安全配置](#8-安全配置)
    - [8.1 TLS 配置](#81-tls-配置)
    - [8.2 认证授权](#82-认证授权)
    - [8.3 安全扫描](#83-安全扫描)
  - [9. 备份与恢复](#9-备份与恢复)
    - [9.1 数据备份](#91-数据备份)
    - [9.2 灾难恢复](#92-灾难恢复)
  - [10. CI/CD 流程](#10-cicd-流程)
    - [10.1 GitHub Actions](#101-github-actions)
    - [10.2 GitLab CI](#102-gitlab-ci)
    - [10.3 滚动更新](#103-滚动更新)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [部署模式对比](#部署模式对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 部署架构

### 1.1 单机部署

````text
单机部署架构:

┌─────────────────────────────────────┐
│            服务器                    │
│                                     │
│  ┌──────────┐   ┌──────────┐        │
│  │  Nginx   │──>│   App    │        │
│  │ (反向代理)│   │ (Rust)   │        │
│  └──────────┘   └─────┬────┘        │
│                       │             │
│                  ┌────▼────┐        │
│                  │PostgreSQL│       │
│                  └─────────┘        │
└─────────────────────────────────────┘

适用场景:
- 小型应用
- 开发/测试环境
- 成本敏感型项目
````

### 1.2 集群部署

````text
集群部署架构:

                ┌──────────┐
                │   LB     │
                └────┬─────┘
                     │
      ┌──────────────┼──────────────┐
      │              │              │
  ┌───▼───┐     ┌───▼───┐     ┌───▼───┐
  │ App 1 │     │ App 2 │     │ App 3 │
  └───┬───┘     └───┬───┘     └───┬───┘
      │             │             │
      └──────────────┼─────────────┘
                     │
              ┌──────▼──────┐
              │ PostgreSQL  │
              │  (主从复制) │
              └─────────────┘

优势:
- 高可用性
- 水平扩展
- 负载均衡
````

### 1.3 云原生部署

````text
Kubernetes 云原生部署:

┌─────────────────────────────────────┐
│         Kubernetes Cluster          │
│                                     │
│  ┌──────────────────────────────┐   │
│  │         Ingress              │   │
│  └──────────────┬───────────────┘   │
│                 │                   │
│        ┌────────┼────────┐          │
│        │        │        │          │
│   ┌────▼───┐┌───▼───┐┌───▼───┐      │
│   │ Pod 1  ││ Pod 2 ││ Pod 3 │      │
│   └────┬───┘└───┬───┘└───┬───┘      │
│        │        │        │          │
│        └────────┼────────┘          │
│                 │                   │
│        ┌────────▼────────┐          │
│        │  StatefulSet    │          │
│        │  (PostgreSQL)   │          │
│        └─────────────────┘          │
└─────────────────────────────────────┘

特性:
- 自动扩缩容
- 自愈能力
- 滚动更新
- 服务发现
````

---

## 2. Docker 容器化

### 2.1 生产级 Dockerfile

````dockerfile
# Dockerfile.production
FROM rust:1.90-slim as builder

# 安装依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 预编译依赖 (缓存层)
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release --locked

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非 root 用户
RUN useradd -m -u 1000 app

WORKDIR /app

# 复制二进制文件
COPY --from=builder /app/target/release/my-app /app/my-app

# 设置权限
RUN chown -R app:app /app

USER app

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:8080/health || exit 1

EXPOSE 8080

CMD ["/app/my-app"]
````

### 2.2 多阶段构建

````dockerfile
# 针对不同环境的多阶段构建
FROM rust:1.90-slim as builder
# ... 构建阶段 ...

# 开发镜像
FROM debian:bookworm-slim as development
COPY --from=builder /app/target/release/my-app /app/my-app
CMD ["/app/my-app"]

# 生产镜像 (更小更安全)
FROM gcr.io/distroless/cc-debian12 as production
COPY --from=builder /app/target/release/my-app /app/my-app
USER nonroot:nonroot
CMD ["/app/my-app"]
````

### 2.3 Docker Compose

````yaml
# docker-compose.production.yml
version: '3.8'

services:
  app:
    image: my-app:latest
    build:
      context: .
      dockerfile: Dockerfile.production
    ports:
      - "8080:8080"
    environment:
      RUST_LOG: info
      DATABASE_URL: postgres://user:pass@db:5432/mydb
      OTEL_EXPORTER_OTLP_ENDPOINT: http://collector:4317
    depends_on:
      db:
        condition: service_healthy
      collector:
        condition: service_started
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    restart: unless-stopped
    deploy:
      replicas: 3
      resources:
        limits:
          cpus: '1.0'
          memory: 512M
        reservations:
          cpus: '0.5'
          memory: 256M

  db:
    image: postgres:16-alpine
    environment:
      POSTGRES_USER: user
      POSTGRES_PASSWORD: pass
      POSTGRES_DB: mydb
    volumes:
      - db-data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD", "pg_isready", "-U", "user"]
      interval: 10s
      timeout: 5s
      retries: 5
    restart: unless-stopped

  collector:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/collector-config.yaml"]
    volumes:
      - ./collector-config.yaml:/etc/collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
    restart: unless-stopped

  prometheus:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    restart: unless-stopped

  grafana:
    image: grafana/grafana:latest
    environment:
      GF_SECURITY_ADMIN_PASSWORD: admin
    volumes:
      - grafana-data:/var/lib/grafana
    ports:
      - "3000:3000"
    restart: unless-stopped

volumes:
  db-data:
  prometheus-data:
  grafana-data:
````

---

## 3. Kubernetes 部署

### 3.1 Deployment

````yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
  namespace: production
  labels:
    app: my-app
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
        version: v1.2.3
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: my-app
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        fsGroup: 1000
      
      containers:
        - name: app
          image: my-app:1.2.3
          imagePullPolicy: IfNotPresent
          
          ports:
            - name: http
              containerPort: 8080
              protocol: TCP
            - name: metrics
              containerPort: 9090
              protocol: TCP
          
          env:
            - name: RUST_LOG
              value: "info"
            - name: DATABASE_URL
              valueFrom:
                secretKeyRef:
                  name: my-app-secrets
                  key: database-url
            - name: OTEL_EXPORTER_OTLP_ENDPOINT
              value: "http://collector.monitoring.svc.cluster.local:4317"
          
          envFrom:
            - configMapRef:
                name: my-app-config
          
          resources:
            requests:
              memory: "256Mi"
              cpu: "250m"
            limits:
              memory: "512Mi"
              cpu: "1000m"
          
          livenessProbe:
            httpGet:
              path: /health/live
              port: http
            initialDelaySeconds: 30
            periodSeconds: 10
            timeoutSeconds: 5
            failureThreshold: 3
          
          readinessProbe:
            httpGet:
              path: /health/ready
              port: http
            initialDelaySeconds: 10
            periodSeconds: 5
            timeoutSeconds: 3
            failureThreshold: 3
          
          startupProbe:
            httpGet:
              path: /health/startup
              port: http
            initialDelaySeconds: 0
            periodSeconds: 5
            timeoutSeconds: 3
            failureThreshold: 30
          
          volumeMounts:
            - name: config
              mountPath: /app/config
              readOnly: true
            - name: tmp
              mountPath: /tmp
      
      volumes:
        - name: config
          configMap:
            name: my-app-config
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
                        - my-app
                topologyKey: kubernetes.io/hostname
````

### 3.2 Service

````yaml
# service.yaml
apiVersion: v1
kind: Service
metadata:
  name: my-app
  namespace: production
  labels:
    app: my-app
spec:
  type: ClusterIP
  sessionAffinity: ClientIP
  sessionAffinityConfig:
    clientIP:
      timeoutSeconds: 10800
  ports:
    - name: http
      port: 80
      targetPort: http
      protocol: TCP
    - name: metrics
      port: 9090
      targetPort: metrics
      protocol: TCP
  selector:
    app: my-app
````

### 3.3 ConfigMap

````yaml
# configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: my-app-config
  namespace: production
data:
  APP_ENV: "production"
  LOG_FORMAT: "json"
  MAX_CONNECTIONS: "100"
  CACHE_TTL: "3600"
````

### 3.4 Secret

````yaml
# secret.yaml
apiVersion: v1
kind: Secret
metadata:
  name: my-app-secrets
  namespace: production
type: Opaque
stringData:
  database-url: "postgres://user:pass@db.production.svc.cluster.local:5432/mydb"
  api-key: "your-api-key"
  jwt-secret: "your-jwt-secret"
````

### 3.5 Ingress

````yaml
# ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: my-app
  namespace: production
  annotations:
    kubernetes.io/ingress.class: nginx
    cert-manager.io/cluster-issuer: letsencrypt-prod
    nginx.ingress.kubernetes.io/rate-limit: "100"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
spec:
  tls:
    - hosts:
        - api.example.com
      secretName: my-app-tls
  rules:
    - host: api.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: my-app
                port:
                  number: 80
````

---

## 4. 高可用配置

### 4.1 多副本部署

````yaml
spec:
  replicas: 3  # 至少 3 个副本
  
  # 滚动更新策略
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1        # 最多多 1 个 Pod
      maxUnavailable: 0  # 不允许不可用
````

### 4.2 负载均衡

````yaml
# HorizontalPodAutoscaler (HPA)
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: my-app-hpa
  namespace: production
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: my-app
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
````

### 4.3 健康检查

````rust
use axum::{Router, routing::get};

/// 健康检查路由
pub fn health_routes() -> Router {
    Router::new()
        .route("/health/live", get(liveness))
        .route("/health/ready", get(readiness))
        .route("/health/startup", get(startup))
}

/// Liveness Probe (存活检查)
async fn liveness() -> &'static str {
    // 检查应用是否存活
    "OK"
}

/// Readiness Probe (就绪检查)
async fn readiness() -> Result<&'static str, (StatusCode, &'static str)> {
    // 检查是否可以接收流量
    if check_database_connection().await {
        Ok("OK")
    } else {
        Err((StatusCode::SERVICE_UNAVAILABLE, "Database not ready"))
    }
}

/// Startup Probe (启动检查)
async fn startup() -> Result<&'static str, (StatusCode, &'static str)> {
    // 检查应用是否启动完成
    if check_initialization_complete().await {
        Ok("OK")
    } else {
        Err((StatusCode::SERVICE_UNAVAILABLE, "Still starting"))
    }
}

async fn check_database_connection() -> bool {
    // 实现数据库连接检查
    true
}

async fn check_initialization_complete() -> bool {
    // 实现初始化检查
    true
}
````

---

## 5. 监控与告警

### 5.1 Prometheus 监控

````yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'my-app'
    kubernetes_sd_configs:
      - role: pod
        namespaces:
          names:
            - production
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
        action: replace
        target_label: __metrics_path__
        regex: (.+)
      - source_labels: [__address__, __meta_kubernetes_pod_annotation_prometheus_io_port]
        action: replace
        regex: ([^:]+)(?::\d+)?;(\d+)
        replacement: $1:$2
        target_label: __address__
````

### 5.2 Grafana 仪表板

````json
{
  "dashboard": {
    "title": "My App Production Metrics",
    "panels": [
      {
        "title": "Request Rate",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total{namespace=\"production\"}[5m]))",
            "legendFormat": "QPS"
          }
        ]
      },
      {
        "title": "Error Rate",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total{namespace=\"production\",status_code=~\"5..\"}[5m])) / sum(rate(http_requests_total{namespace=\"production\"}[5m]))",
            "legendFormat": "Error Rate"
          }
        ]
      },
      {
        "title": "P95 Latency",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket{namespace=\"production\"}[5m])) by (le))",
            "legendFormat": "P95"
          }
        ]
      },
      {
        "title": "Pod Count",
        "targets": [
          {
            "expr": "count(kube_pod_status_phase{namespace=\"production\",pod=~\"my-app-.*\",phase=\"Running\"})",
            "legendFormat": "Running Pods"
          }
        ]
      }
    ]
  }
}
````

### 5.3 告警规则

````yaml
# alerts.yml
groups:
  - name: production
    rules:
      - alert: HighErrorRate
        expr: |
          sum(rate(http_requests_total{namespace="production",status_code=~"5.."}[5m])) 
          / sum(rate(http_requests_total{namespace="production"}[5m])) 
          > 0.05
        for: 5m
        labels:
          severity: critical
          namespace: production
        annotations:
          summary: "High error rate in production"
          description: "Error rate is {{ $value | humanizePercentage }}"
      
      - alert: PodDown
        expr: |
          kube_deployment_status_replicas_available{namespace="production",deployment="my-app"} 
          < kube_deployment_spec_replicas{namespace="production",deployment="my-app"}
        for: 5m
        labels:
          severity: warning
          namespace: production
        annotations:
          summary: "Pod is down in production"
          description: "Only {{ $value }} pods available"
````

---

## 6. 日志管理

### 6.1 结构化日志

````rust
use tracing_subscriber::{fmt, EnvFilter};

/// 初始化生产环境日志
pub fn init_production_logging() {
    fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .json()                    // JSON 格式
        .with_current_span(true)   // 包含 Span 信息
        .with_target(false)        // 不包含 target
        .with_file(false)          // 不包含文件名
        .with_line_number(false)   // 不包含行号
        .init();
}
````

### 6.2 ELK Stack

````yaml
# filebeat.yml
filebeat.inputs:
  - type: container
    paths:
      - '/var/log/containers/my-app-*.log'
    json.keys_under_root: true
    json.add_error_key: true

output.elasticsearch:
  hosts: ["elasticsearch:9200"]
  index: "my-app-%{+yyyy.MM.dd}"
````

### 6.3 Loki

````yaml
# promtail.yml
server:
  http_listen_port: 9080

clients:
  - url: http://loki:3100/loki/api/v1/push

scrape_configs:
  - job_name: kubernetes-pods
    kubernetes_sd_configs:
      - role: pod
    pipeline_stages:
      - json:
          expressions:
            level: level
            message: message
            trace_id: trace_id
      - labels:
          level:
          trace_id:
````

---

## 7. 性能优化

### 7.1 编译优化

````toml
# Cargo.toml
[profile.release]
opt-level = 3           # 最大优化
lto = "fat"             # Link Time Optimization
codegen-units = 1       # 单个代码单元 (更好的优化)
strip = true            # 去除符号信息
panic = "abort"         # Panic 时直接 abort
````

### 7.2 运行时优化

````rust
use tokio::runtime::Builder;

/// 自定义 Tokio Runtime
pub fn build_runtime() -> tokio::runtime::Runtime {
    Builder::new_multi_thread()
        .worker_threads(4)                    // 工作线程数
        .thread_name("my-app-worker")         // 线程名
        .thread_stack_size(2 * 1024 * 1024)   // 栈大小 2MB
        .enable_all()
        .build()
        .unwrap()
}
````

### 7.3 数据库连接池

````rust
use sqlx::postgres::PgPoolOptions;

/// 生产环境数据库连接池
pub async fn create_db_pool(database_url: &str) -> sqlx::PgPool {
    PgPoolOptions::new()
        .max_connections(20)           // 最大连接数
        .min_connections(5)            // 最小连接数
        .acquire_timeout(Duration::from_secs(30))
        .idle_timeout(Duration::from_secs(600))
        .max_lifetime(Duration::from_secs(1800))
        .connect(database_url)
        .await
        .expect("Failed to create database pool")
}
````

---

## 8. 安全配置

### 8.1 TLS 配置

````rust
use axum_server::tls_rustls::RustlsConfig;

/// TLS 配置
pub async fn setup_tls() -> RustlsConfig {
    RustlsConfig::from_pem_file(
        "/etc/certs/cert.pem",
        "/etc/certs/key.pem",
    )
    .await
    .expect("Failed to load TLS config")
}

#[tokio::main]
async fn main() {
    let tls_config = setup_tls().await;
    let app = create_app();
    
    let addr = SocketAddr::from(([0, 0, 0, 0], 8443));
    
    axum_server::bind_rustls(addr, tls_config)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
````

### 8.2 认证授权

````rust
use axum::{middleware, Router};
use jsonwebtoken::{decode, DecodingKey, Validation};

/// JWT 认证中间件
pub async fn auth_middleware(
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let token = extract_token(&request)?;
    let claims = verify_token(&token)?;
    
    // 将 claims 存入 request extensions
    request.extensions_mut().insert(claims);
    
    Ok(next.run(request).await)
}

fn extract_token(request: &Request) -> Result<String, StatusCode> {
    // 从 Authorization header 提取 token
    request
        .headers()
        .get("Authorization")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.strip_prefix("Bearer "))
        .map(|v| v.to_string())
        .ok_or(StatusCode::UNAUTHORIZED)
}

fn verify_token(token: &str) -> Result<Claims, StatusCode> {
    decode::<Claims>(
        token,
        &DecodingKey::from_secret(JWT_SECRET.as_bytes()),
        &Validation::default(),
    )
    .map(|data| data.claims)
    .map_err(|_| StatusCode::UNAUTHORIZED)
}
````

### 8.3 安全扫描

````yaml
# .github/workflows/security.yml
name: Security Scan

on: [push, pull_request]

jobs:
  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Run cargo audit
        run: |
          cargo install cargo-audit
          cargo audit
      
      - name: Run cargo deny
        run: |
          cargo install cargo-deny
          cargo deny check
      
      - name: Trivy container scan
        uses: aquasecurity/trivy-action@master
        with:
          image-ref: my-app:latest
          format: 'sarif'
          output: 'trivy-results.sarif'
````

---

## 9. 备份与恢复

### 9.1 数据备份

````bash
#!/bin/bash
# backup.sh

DATE=$(date +%Y%m%d_%H%M%S)
BACKUP_DIR="/backups"

# 数据库备份
pg_dump -h db.production.svc.cluster.local \
        -U user \
        -d mydb \
        -F c \
        -f "${BACKUP_DIR}/db_${DATE}.dump"

# 上传到 S3
aws s3 cp "${BACKUP_DIR}/db_${DATE}.dump" \
          "s3://my-backups/db_${DATE}.dump"

# 清理旧备份 (保留 30 天)
find "${BACKUP_DIR}" -name "db_*.dump" -mtime +30 -delete
````

**Kubernetes CronJob**:

````yaml
apiVersion: batch/v1
kind: CronJob
metadata:
  name: db-backup
  namespace: production
spec:
  schedule: "0 2 * * *"  # 每天 2:00 AM
  jobTemplate:
    spec:
      template:
        spec:
          containers:
            - name: backup
              image: postgres:16-alpine
              command:
                - /bin/bash
                - -c
                - |
                  pg_dump -h db -U user -d mydb -F c -f /backup/db_$(date +%Y%m%d).dump
              volumeMounts:
                - name: backup
                  mountPath: /backup
          volumes:
            - name: backup
              persistentVolumeClaim:
                claimName: backup-pvc
          restartPolicy: OnFailure
````

### 9.2 灾难恢复

````bash
#!/bin/bash
# restore.sh

BACKUP_FILE=$1

# 下载备份
aws s3 cp "s3://my-backups/${BACKUP_FILE}" /tmp/${BACKUP_FILE}

# 恢复数据库
pg_restore -h db.production.svc.cluster.local \
           -U user \
           -d mydb \
           -c \
           /tmp/${BACKUP_FILE}
````

---

## 10. CI/CD 流程

### 10.1 GitHub Actions

````yaml
# .github/workflows/deploy.yml
name: Deploy to Production

on:
  push:
    branches: [main]
    tags: ['v*']

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  build-and-push:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      packages: write
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3
      
      - name: Log in to Container Registry
        uses: docker/login-action@v3
        with:
          registry: ${{ env.REGISTRY }}
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}
      
      - name: Extract metadata
        id: meta
        uses: docker/metadata-action@v5
        with:
          images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
      
      - name: Build and push
        uses: docker/build-push-action@v5
        with:
          context: .
          file: Dockerfile.production
          push: true
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
  
  deploy:
    needs: build-and-push
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up kubectl
        uses: azure/setup-kubectl@v3
      
      - name: Configure kubectl
        run: |
          echo "${{ secrets.KUBECONFIG }}" | base64 -d > kubeconfig
          export KUBECONFIG=kubeconfig
      
      - name: Deploy to Kubernetes
        run: |
          kubectl set image deployment/my-app \
            app=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }} \
            -n production
          
          kubectl rollout status deployment/my-app -n production
````

### 10.2 GitLab CI

````yaml
# .gitlab-ci.yml
stages:
  - build
  - test
  - deploy

variables:
  DOCKER_DRIVER: overlay2
  DOCKER_TLS_CERTDIR: ""

build:
  stage: build
  image: docker:latest
  services:
    - docker:dind
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA -f Dockerfile.production .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA

deploy-production:
  stage: deploy
  image: bitnami/kubectl:latest
  script:
    - kubectl config use-context production
    - kubectl set image deployment/my-app app=$CI_REGISTRY_IMAGE:$CI_COMMIT_SHA -n production
    - kubectl rollout status deployment/my-app -n production
  only:
    - main
  environment:
    name: production
    url: https://api.example.com
````

### 10.3 滚动更新

````bash
# 滚动更新
kubectl set image deployment/my-app app=my-app:v1.2.3 -n production

# 查看状态
kubectl rollout status deployment/my-app -n production

# 回滚
kubectl rollout undo deployment/my-app -n production

# 查看历史
kubectl rollout history deployment/my-app -n production
````

---

## 总结

### 核心要点

1. **容器化**: Docker 多阶段构建
2. **Kubernetes**: Deployment + Service + Ingress
3. **高可用**: 多副本 + HPA + 健康检查
4. **监控**: Prometheus + Grafana + 告警
5. **日志**: 结构化日志 + ELK/Loki
6. **安全**: TLS + 认证授权 + 安全扫描
7. **CI/CD**: 自动化部署 + 滚动更新

### 部署模式对比

| 模式 | 优势 | 劣势 | 适用场景 |
|------|------|------|----------|
| 单机 | 简单、成本低 | 无高可用 | 小型应用、测试环境 |
| 集群 | 高可用、可扩展 | 复杂度高 | 中型应用 |
| K8s | 自动化、云原生 | 学习成本高 | 大型应用、企业级 |

### 最佳实践清单

- ✅ 使用多阶段 Docker 构建
- ✅ 非 root 用户运行容器
- ✅ 至少 3 个副本保证高可用
- ✅ 配置健康检查 (liveness, readiness, startup)
- ✅ 使用 HPA 自动扩缩容
- ✅ 配置资源限制 (CPU/Memory)
- ✅ 启用 Prometheus 监控
- ✅ 设置告警规则
- ✅ 结构化日志 (JSON 格式)
- ✅ TLS 加密传输
- ✅ JWT 认证授权
- ✅ 定期数据备份
- ✅ CI/CD 自动化部署
- ✅ 滚动更新策略
- ✅ 安全扫描 (cargo audit, Trivy)
- ❌ 不要在容器中存储敏感信息
- ❌ 不要使用 latest 标签
- ❌ 不要忘记配置日志轮转

---

**相关文档**:

- [Docker 部署](./03_Docker_部署_Rust完整指南.md)
- [GitHub Actions](./01_GitHub_Actions_完整指南.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [Collector 配置](../04_核心组件/07_Collector_配置详解_Rust完整版.md)
