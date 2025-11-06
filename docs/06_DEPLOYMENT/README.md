# 🚀 部署运维指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 部署运维指南 - 生产环境部署、监控设置、故障排除和性能调优。

---

## 📋 目录

- [🚀 部署运维指南](#-部署运维指南)
  - [📋 目录](#-目录)
  - [🏭 生产部署](#-生产部署)
    - [环境准备](#环境准备)
      - [系统要求](#系统要求)
      - [依赖安装](#依赖安装)
    - [容器化部署](#容器化部署)
      - [Dockerfile 优化](#dockerfile-优化)
      - [Docker Compose 配置](#docker-compose-配置)
    - [Kubernetes 部署](#kubernetes-部署)
      - [Deployment 配置](#deployment-配置)
      - [Service 配置](#service-配置)
      - [ConfigMap 配置](#configmap-配置)
    - [云原生部署](#云原生部署)
      - [Helm Chart](#helm-chart)
  - [📊 监控设置](#-监控设置)
    - [指标收集](#指标收集)
      - [Prometheus 配置](#prometheus-配置)
      - [自定义指标](#自定义指标)
    - [日志聚合](#日志聚合)
      - [结构化日志](#结构化日志)
    - [分布式追踪](#分布式追踪)
      - [Jaeger 集成](#jaeger-集成)
    - [告警配置](#告警配置)
      - [AlertManager 规则](#alertmanager-规则)
  - [🔧 故障排除](#-故障排除)
    - [常见问题](#常见问题)
      - [连接问题](#连接问题)
      - [性能问题](#性能问题)
    - [诊断工具](#诊断工具)
      - [健康检查端点](#健康检查端点)
      - [调试模式](#调试模式)
    - [故障恢复](#故障恢复)
      - [自动恢复机制](#自动恢复机制)
  - [⚡ 性能调优](#-性能调优)
    - [系统调优](#系统调优)
      - [内核参数优化](#内核参数优化)
    - [应用调优](#应用调优)
      - [运行时优化](#运行时优化)
    - [网络调优](#网络调优)
      - [连接池优化](#连接池优化)
  - [🔒 安全配置](#-安全配置)
    - [认证授权](#认证授权)
      - [RBAC 配置](#rbac-配置)
    - [网络安全](#网络安全)
      - [NetworkPolicy 配置](#networkpolicy-配置)
  - [🔄 运维自动化](#-运维自动化)
    - [CI/CD 流水线](#cicd-流水线)
      - [GitHub Actions](#github-actions)
    - [自动化部署](#自动化部署)
      - [ArgoCD 配置](#argocd-配置)
  - [🔗 相关文档](#-相关文档)

## 🏭 生产部署

### 环境准备

#### 系统要求

```bash
# 检查系统要求
echo "=== 系统信息 ==="
uname -a
cat /etc/os-release

echo "=== 内存信息 ==="
free -h

echo "=== CPU 信息 ==="
nproc
lscpu | grep "Model name"

echo "=== 磁盘空间 ==="
df -h

echo "=== 网络配置 ==="
ip addr show
```

#### 依赖安装

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install -y curl wget git build-essential pkg-config libssl-dev

# CentOS/RHEL
sudo yum update -y
sudo yum install -y curl wget git gcc openssl-devel

# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# 验证安装
rustc --version
cargo --version
```

### 容器化部署

#### Dockerfile 优化

```dockerfile
# 多阶段构建优化
FROM rust:1.90-alpine AS builder

# 安装构建依赖
RUN apk add --no-cache musl-dev openssl-dev pkgconfig

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖缓存
RUN cargo fetch

# 复制源代码
COPY src ./src
COPY otlp ./otlp

# 构建应用
RUN cargo build --release --target x86_64-unknown-linux-musl

# 运行时镜像
FROM alpine:latest

# 安装运行时依赖
RUN apk --no-cache add ca-certificates tzdata

# 创建非 root 用户
RUN addgroup -g 1001 -S otlp && \
    adduser -u 1001 -S otlp -G otlp

WORKDIR /app

# 复制二进制文件
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/otlp-client ./

# 设置权限
RUN chown -R otlp:otlp /app
USER otlp

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

# 暴露端口
EXPOSE 8080

# 启动应用
CMD ["./otlp-client"]
```

#### Docker Compose 配置

```yaml
version: '3.8'

services:
  otlp-client:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://collector:4317
      - OTLP_PROTOCOL=grpc
    volumes:
      - ./config:/app/config:ro
      - ./logs:/app/logs
    depends_on:
      - collector
      - redis
    restart: unless-stopped
    deploy:
      resources:
        limits:
          memory: 512M
          cpus: '0.5'
        reservations:
          memory: 256M
          cpus: '0.25'

  collector:
    image: otel/opentelemetry-collector:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./collector-config.yaml:/etc/collector-config.yaml:ro
    command: ["--config=/etc/collector-config.yaml"]
    restart: unless-stopped

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    restart: unless-stopped

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml:ro
      - prometheus-data:/prometheus
    restart: unless-stopped

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-data:/var/lib/grafana
    restart: unless-stopped

volumes:
  redis-data:
  prometheus-data:
  grafana-data:
```

### Kubernetes 部署

#### Deployment 配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-client
  namespace: otlp
  labels:
    app: otlp-client
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
      app: otlp-client
  template:
    metadata:
      labels:
        app: otlp-client
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: otlp-client
      securityContext:
        runAsNonRoot: true
        runAsUser: 1001
        runAsGroup: 1001
        fsGroup: 1001
      containers:
      - name: otlp-client
        image: otlp-client:latest
        imagePullPolicy: Always
        ports:
        - containerPort: 8080
          name: http
          protocol: TCP
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_ENDPOINT
          value: "http://collector:4317"
        - name: OTLP_PROTOCOL
          value: "grpc"
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3
        volumeMounts:
        - name: config
          mountPath: /app/config
          readOnly: true
        - name: logs
          mountPath: /app/logs
      volumes:
      - name: config
        configMap:
          name: otlp-client-config
      - name: logs
        emptyDir: {}
      nodeSelector:
        kubernetes.io/arch: amd64
      tolerations:
      - key: "node.kubernetes.io/not-ready"
        operator: "Exists"
        effect: "NoExecute"
        tolerationSeconds: 300
      - key: "node.kubernetes.io/unreachable"
        operator: "Exists"
        effect: "NoExecute"
        tolerationSeconds: 300
```

#### Service 配置

```yaml
apiVersion: v1
kind: Service
metadata:
  name: otlp-client
  namespace: otlp
  labels:
    app: otlp-client
spec:
  type: ClusterIP
  ports:
  - port: 8080
    targetPort: 8080
    protocol: TCP
    name: http
  selector:
    app: otlp-client
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-client-headless
  namespace: otlp
  labels:
    app: otlp-client
spec:
  type: ClusterIP
  clusterIP: None
  ports:
  - port: 8080
    targetPort: 8080
    protocol: TCP
    name: http
  selector:
    app: otlp-client
```

#### ConfigMap 配置

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-client-config
  namespace: otlp
data:
  config.yaml: |
    server:
      host: "0.0.0.0"
      port: 8080
      workers: 4

    otlp:
      endpoint: "http://collector:4317"
      protocol: "grpc"
      timeout: "10s"
      retry:
        max_retries: 3
        initial_delay: "100ms"
        max_delay: "30s"
        multiplier: 2.0

    batch:
      max_size: 512
      timeout: "5s"
      max_queue_size: 2048

    metrics:
      enabled: true
      port: 9090
      path: "/metrics"

    logging:
      level: "info"
      format: "json"
      output: "stdout"
```

### 云原生部署

#### Helm Chart

```yaml
# values.yaml
replicaCount: 3

image:
  repository: otlp-client
  tag: "latest"
  pullPolicy: IfNotPresent
  pullSecrets: []

nameOverride: ""
fullnameOverride: ""

service:
  type: ClusterIP
  port: 8080
  targetPort: 8080

ingress:
  enabled: false
  className: ""
  annotations: {}
  hosts:
    - host: otlp-client.local
      paths:
        - path: /
          pathType: Prefix
  tls: []

resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 250m
    memory: 256Mi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80

nodeSelector: {}

tolerations: []

affinity: {}

podAnnotations: {}

podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1001
  runAsGroup: 1001
  fsGroup: 1001

securityContext:
  allowPrivilegeEscalation: false
  readOnlyRootFilesystem: true
  runAsNonRoot: true
  runAsUser: 1001
  capabilities:
    drop:
    - ALL

config:
  otlp:
    endpoint: "http://collector:4317"
    protocol: "grpc"
    timeout: "10s"

  batch:
    max_size: 512
    timeout: "5s"

  metrics:
    enabled: true
    port: 9090
```

## 📊 监控设置

### 指标收集

#### Prometheus 配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "alert_rules.yml"

scrape_configs:
  - job_name: 'otlp-client'
    static_configs:
      - targets: ['otlp-client:8080']
    metrics_path: '/metrics'
    scrape_interval: 10s
    scrape_timeout: 5s

  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093
```

#### 自定义指标

```rust
use prometheus::{Counter, Histogram, Gauge, register_counter, register_histogram, register_gauge};

// 自定义指标定义
pub struct Metrics {
    pub requests_total: Counter,
    pub request_duration: Histogram,
    pub active_connections: Gauge,
    pub batch_size: Histogram,
    pub errors_total: Counter,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            requests_total: register_counter!(
                "otlp_requests_total",
                "Total number of requests"
            ).unwrap(),
            request_duration: register_histogram!(
                "otlp_request_duration_seconds",
                "Request duration in seconds"
            ).unwrap(),
            active_connections: register_gauge!(
                "otlp_active_connections",
                "Number of active connections"
            ).unwrap(),
            batch_size: register_histogram!(
                "otlp_batch_size",
                "Batch size distribution"
            ).unwrap(),
            errors_total: register_counter!(
                "otlp_errors_total",
                "Total number of errors"
            ).unwrap(),
        }
    }
}
```

### 日志聚合

#### 结构化日志

```rust
use tracing::{info, warn, error, debug};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

// 日志配置
pub fn init_logging() {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "otlp_client=info".into()),
        )
        .with(tracing_subscriber::fmt::layer()
            .with_target(false)
            .with_thread_ids(true)
            .with_file(true)
            .with_line_number(true)
            .json()
        )
        .init();
}

// 结构化日志使用
pub async fn process_request(request: &Request) -> Result<Response, Error> {
    let span = tracing::info_span!("process_request",
        request_id = %request.id,
        method = %request.method,
        path = %request.path
    );

    let _enter = span.enter();

    info!(
        request_id = %request.id,
        method = %request.method,
        path = %request.path,
        "Processing request"
    );

    // 处理逻辑
    let result = handle_request(request).await;

    match &result {
        Ok(response) => {
            info!(
                request_id = %request.id,
                status_code = response.status_code,
                duration_ms = response.duration.as_millis(),
                "Request completed successfully"
            );
        }
        Err(error) => {
            error!(
                request_id = %request.id,
                error = %error,
                "Request failed"
            );
        }
    }

    result
}
```

### 分布式追踪

#### Jaeger 集成

```rust
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry_jaeger::new_agent_pipeline;
use tracing_opentelemetry::OpenTelemetrySpanExt;

// Jaeger 配置
pub fn init_tracing() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = new_agent_pipeline()
        .with_service_name("otlp-client")
        .with_endpoint("http://jaeger:14268/api/traces")
        .install_simple()?;

    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    Ok(())
}

// 追踪使用
pub async fn send_trace_data(&self, data: TelemetryData) -> Result<(), OtlpError> {
    let span = tracing::info_span!("send_trace_data");
    let _enter = span.enter();

    // 创建子 span
    let child_span = tracing::info_span!("serialize_data");
    let _child_enter = child_span.enter();

    let serialized = serde_json::to_string(&data)?;
    drop(_child_enter);

    // 发送数据
    let send_span = tracing::info_span!("send_to_collector");
    let _send_enter = send_span.enter();

    self.transport.send(&serialized).await?;

    Ok(())
}
```

### 告警配置

#### AlertManager 规则

```yaml
# alert_rules.yml
groups:
- name: otlp_client_alerts
  rules:
  - alert: HighErrorRate
    expr: rate(otlp_errors_total[5m]) > 0.1
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High error rate detected"
      description: "Error rate is {{ $value }} errors per second"

  - alert: HighLatency
    expr: histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m])) > 1
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High latency detected"
      description: "95th percentile latency is {{ $value }} seconds"

  - alert: ServiceDown
    expr: up{job="otlp-client"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "OTLP Client service is down"
      description: "Service has been down for more than 1 minute"

  - alert: HighMemoryUsage
    expr: (container_memory_usage_bytes{name="otlp-client"} / container_spec_memory_limit_bytes) > 0.8
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High memory usage"
      description: "Memory usage is {{ $value | humanizePercentage }}"
```

## 🔧 故障排除

### 常见问题

#### 连接问题

```bash
# 检查网络连接
curl -v http://collector:4317/health

# 检查 DNS 解析
nslookup collector

# 检查端口连通性
telnet collector 4317

# 检查防火墙规则
iptables -L -n
```

#### 性能问题

```bash
# 检查系统资源
top
htop
iostat -x 1
vmstat 1

# 检查网络统计
ss -tuln
netstat -i
iftop

# 检查应用指标
curl http://localhost:8080/metrics
```

### 诊断工具

#### 健康检查端点

```rust
use axum::{Router, routing::get, Json};
use serde_json::{json, Value};

// 健康检查实现
pub fn create_health_router() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check))
        .route("/metrics", get(metrics_endpoint))
}

async fn health_check() -> Json<Value> {
    Json(json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now(),
        "version": env!("CARGO_PKG_VERSION"),
        "uptime": get_uptime(),
    }))
}

async fn readiness_check() -> Json<Value> {
    let checks = vec![
        ("database", check_database().await),
        ("collector", check_collector().await),
        ("redis", check_redis().await),
    ];

    let all_ready = checks.iter().all(|(_, ready)| *ready);

    Json(json!({
        "status": if all_ready { "ready" } else { "not_ready" },
        "checks": checks.into_iter().collect::<std::collections::HashMap<_, _>>(),
    }))
}
```

#### 调试模式

```rust
// 调试配置
pub struct DebugConfig {
    pub enable_profiling: bool,
    pub enable_tracing: bool,
    pub log_level: tracing::Level,
    pub dump_config: bool,
}

impl DebugConfig {
    pub fn from_env() -> Self {
        Self {
            enable_profiling: std::env::var("ENABLE_PROFILING")
                .unwrap_or_default()
                .parse()
                .unwrap_or(false),
            enable_tracing: std::env::var("ENABLE_TRACING")
                .unwrap_or_default()
                .parse()
                .unwrap_or(false),
            log_level: std::env::var("LOG_LEVEL")
                .unwrap_or_else(|_| "info".to_string())
                .parse()
                .unwrap_or(tracing::Level::INFO),
            dump_config: std::env::var("DUMP_CONFIG")
                .unwrap_or_default()
                .parse()
                .unwrap_or(false),
        }
    }
}
```

### 故障恢复

#### 自动恢复机制

```rust
use tokio::time::{sleep, Duration};

// 自动恢复实现
pub struct AutoRecovery {
    max_retries: u32,
    base_delay: Duration,
    max_delay: Duration,
}

impl AutoRecovery {
    pub async fn recover<F, T>(&self, mut operation: F) -> Result<T, OtlpError>
    where
        F: FnMut() -> Pin<Box<dyn Future<Output = Result<T, OtlpError>> + Send>>,
    {
        let mut delay = self.base_delay;

        for attempt in 0..self.max_retries {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    if attempt < self.max_retries - 1 {
                        warn!("Attempt {} failed: {}, retrying in {:?}", attempt + 1, e, delay);
                        sleep(delay).await;
                        delay = std::cmp::min(delay * 2, self.max_delay);
                    } else {
                        error!("All {} attempts failed, giving up", self.max_retries);
                        return Err(e);
                    }
                }
            }
        }

        Err(OtlpError::Custom("Max retries exceeded".to_string()))
    }
}
```

## ⚡ 性能调优

### 系统调优

#### 内核参数优化

```bash
# /etc/sysctl.conf
# 网络优化
net.core.rmem_max = 134217728
net.core.wmem_max = 134217728
net.ipv4.tcp_rmem = 4096 65536 134217728
net.ipv4.tcp_wmem = 4096 65536 134217728
net.core.netdev_max_backlog = 5000
net.ipv4.tcp_congestion_control = bbr

# 文件描述符限制
fs.file-max = 2097152
fs.nr_open = 2097152

# 内存管理
vm.swappiness = 10
vm.dirty_ratio = 15
vm.dirty_background_ratio = 5

# 应用配置
echo "* soft nofile 65536" >> /etc/security/limits.conf
echo "* hard nofile 65536" >> /etc/security/limits.conf
```

### 应用调优

#### 运行时优化

```rust
// 运行时配置优化
pub fn optimize_runtime() -> Result<Runtime, std::io::Error> {
    Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_name("otlp-worker")
        .thread_stack_size(3 * 1024 * 1024) // 3MB stack
        .enable_all()
        .build()
}

// 内存池配置
pub struct MemoryConfig {
    pub pool_size: usize,
    pub buffer_size: usize,
    pub max_memory: usize,
}

impl Default for MemoryConfig {
    fn default() -> Self {
        Self {
            pool_size: 1000,
            buffer_size: 64 * 1024, // 64KB
            max_memory: 512 * 1024 * 1024, // 512MB
        }
    }
}
```

### 网络调优

#### 连接池优化

```rust
// 连接池配置
pub struct ConnectionPoolConfig {
    pub max_connections: usize,
    pub max_connections_per_host: usize,
    pub connection_timeout: Duration,
    pub idle_timeout: Duration,
    pub keep_alive: bool,
}

impl Default for ConnectionPoolConfig {
    fn default() -> Self {
        Self {
            max_connections: 100,
            max_connections_per_host: 10,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(90),
            keep_alive: true,
        }
    }
}
```

## 🔒 安全配置

### 认证授权

#### RBAC 配置

```yaml
# rbac.yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otlp-client
  namespace: otlp
---
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  namespace: otlp
  name: otlp-client-role
rules:
- apiGroups: [""]
  resources: ["configmaps", "secrets"]
  verbs: ["get", "list", "watch"]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: otlp-client-rolebinding
  namespace: otlp
subjects:
- kind: ServiceAccount
  name: otlp-client
  namespace: otlp
roleRef:
  kind: Role
  name: otlp-client-role
  apiGroup: rbac.authorization.k8s.io
```

### 网络安全

#### NetworkPolicy 配置

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-client-netpol
  namespace: otlp
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
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: otlp
    ports:
    - protocol: TCP
      port: 4317
  - to: []
    ports:
    - protocol: TCP
      port: 53
    - protocol: UDP
      port: 53
```

## 🔄 运维自动化

### CI/CD 流水线

#### GitHub Actions

```yaml
# .github/workflows/ci.yml
name: CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: 1.90.0
        override: true

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
        cargo test --all-features
        cargo clippy --all-features -- -D warnings
        cargo fmt -- --check

    - name: Run benchmarks
      run: cargo bench

  build:
    needs: test
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4

    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v3

    - name: Login to Container Registry
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
        tags: |
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:latest
          ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }}
        cache-from: type=gha
        cache-to: type=gha,mode=max

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    steps:
    - uses: actions/checkout@v4

    - name: Deploy to Kubernetes
      run: |
        kubectl set image deployment/otlp-client \
          otlp-client=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.sha }}
        kubectl rollout status deployment/otlp-client
```

### 自动化部署

#### ArgoCD 配置

```yaml
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: otlp-client
  namespace: argocd
spec:
  project: default
  source:
    repoURL: https://github.com/example/otlp-client
    targetRevision: HEAD
    path: k8s
    helm:
      valueFiles:
      - values.yaml
  destination:
    server: https://kubernetes.default.svc
    namespace: otlp
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

## 🔗 相关文档

- [快速开始指南](../01_GETTING_STARTED/README.md)
- [API 参考文档](../03_API_REFERENCE/README.md)
- [架构设计文档](../04_ARCHITECTURE/README.md)
- [实现指南](../05_IMPLEMENTATION/README.md)
- [集成指南](../07_INTEGRATION/README.md)

---

**部署运维指南版本**: 1.0.0
**最后更新**: 2025年1月
**维护者**: OTLP Rust 运维团队
