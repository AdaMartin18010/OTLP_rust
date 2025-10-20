# Prometheus Operator深度集成：Kubernetes自动化监控完整指南 (Rust 1.90)

## 目录

- [Prometheus Operator深度集成：Kubernetes自动化监控完整指南 (Rust 1.90)](#prometheus-operator深度集成kubernetes自动化监控完整指南-rust-190)
  - [目录](#目录)
  - [一、Prometheus Operator核心概念](#一prometheus-operator核心概念)
    - [1.1 Operator模式](#11-operator模式)
    - [1.2 核心CRD](#12-核心crd)
    - [1.3 服务发现](#13-服务发现)
  - [二、环境准备](#二环境准备)
    - [2.1 安装Prometheus Operator](#21-安装prometheus-operator)
    - [2.2 验证安装](#22-验证安装)
  - [三、ServiceMonitor实现](#三servicemonitor实现)
    - [3.1 ServiceMonitor定义](#31-servicemonitor定义)
    - [3.2 Rust应用集成](#32-rust应用集成)
    - [3.3 多端口监控](#33-多端口监控)
  - [四、PodMonitor实现](#四podmonitor实现)
    - [4.1 PodMonitor vs ServiceMonitor](#41-podmonitor-vs-servicemonitor)
    - [4.2 StatefulSet监控](#42-statefulset监控)
  - [五、PrometheusRule实现](#五prometheusrule实现)
    - [5.1 告警规则定义](#51-告警规则定义)
    - [5.2 Recording Rules](#52-recording-rules)
    - [5.3 告警分组](#53-告警分组)
  - [六、AlertmanagerConfig实现](#六alertmanagerconfig实现)
    - [6.1 告警路由](#61-告警路由)
    - [6.2 多通知渠道](#62-多通知渠道)
    - [6.3 告警静默](#63-告警静默)
  - [七、高可用配置](#七高可用配置)
    - [7.1 Prometheus高可用](#71-prometheus高可用)
    - [7.2 Thanos集成](#72-thanos集成)
    - [7.3 远程存储](#73-远程存储)
  - [八、Rust应用完整集成](#八rust应用完整集成)
    - [8.1 应用代码](#81-应用代码)
    - [8.2 Kubernetes Deployment](#82-kubernetes-deployment)
    - [8.3 完整监控栈](#83-完整监控栈)
  - [九、高级特性](#九高级特性)
    - [9.1 自定义指标](#91-自定义指标)
    - [9.2 联邦集群](#92-联邦集群)
    - [9.3 PushGateway集成](#93-pushgateway集成)
  - [十、生产最佳实践](#十生产最佳实践)
    - [10.1 资源配额](#101-资源配额)
    - [10.2 数据保留](#102-数据保留)
    - [10.3 安全配置](#103-安全配置)
  - [十一、故障排查](#十一故障排查)
    - [常见问题](#常见问题)
      - [1. ServiceMonitor未生效](#1-servicemonitor未生效)
      - [2. 指标未显示](#2-指标未显示)
      - [3. 告警未触发](#3-告警未触发)
  - [十二、参考资源](#十二参考资源)
    - [官方文档](#官方文档)
    - [国际标准](#国际标准)
    - [工具](#工具)
  - [总结](#总结)

---

## 一、Prometheus Operator核心概念

### 1.1 Operator模式

**Operator是什么？**

- Kubernetes原生的应用管理模式
- 封装运维知识到代码中
- 自动化部署、配置、升级、故障恢复

**Prometheus Operator职责**：

- 自动化Prometheus实例部署
- 动态服务发现（通过CRD）
- 告警规则管理
- Alertmanager配置

### 1.2 核心CRD

Prometheus Operator定义了7个自定义资源：

| CRD | 用途 | 示例 |
|-----|------|------|
| `Prometheus` | Prometheus实例定义 | 副本数、存储、资源 |
| `ServiceMonitor` | 基于Service的监控目标 | 自动发现Service端点 |
| `PodMonitor` | 基于Pod的监控目标 | 监控特定Pod |
| `PrometheusRule` | 告警和记录规则 | PromQL规则定义 |
| `Alertmanager` | Alertmanager实例 | 告警接收器配置 |
| `AlertmanagerConfig` | Alertmanager路由配置 | 告警路由规则 |
| `Probe` | Blackbox探测 | HTTP/TCP健康检查 |

### 1.3 服务发现

**传统方式**：

```yaml
# prometheus.yml（手动配置）
scrape_configs:
  - job_name: 'my-app'
    static_configs:
      - targets: ['app-1:9090', 'app-2:9090']
```

**Operator方式**：

```yaml
# ServiceMonitor（自动发现）
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: my-app
spec:
  selector:
    matchLabels:
      app: my-app
  endpoints:
    - port: metrics
```

**优势**：

- ✅ 自动发现新Pod
- ✅ 无需重启Prometheus
- ✅ 声明式配置

---

## 二、环境准备

### 2.1 安装Prometheus Operator

**方法一：Helm安装（推荐）**:

```bash
# 添加Helm仓库
helm repo add prometheus-community https://prometheus-community.github.io/helm-charts
helm repo update

# 安装kube-prometheus-stack（包含Operator + Prometheus + Grafana）
helm install prometheus prometheus-community/kube-prometheus-stack \
  --namespace monitoring \
  --create-namespace \
  --set prometheus.prometheusSpec.serviceMonitorSelectorNilUsesHelmValues=false \
  --set prometheus.prometheusSpec.podMonitorSelectorNilUsesHelmValues=false

# 验证安装
kubectl get pods -n monitoring
```

**方法二：kubectl安装**:

```bash
# 下载YAML
curl -sL https://github.com/prometheus-operator/prometheus-operator/releases/download/v0.70.0/bundle.yaml | kubectl create -f -

# 创建Prometheus实例
kubectl apply -f - <<EOF
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus
  namespace: monitoring
spec:
  replicas: 2
  serviceAccountName: prometheus
  serviceMonitorSelector: {}
  podMonitorSelector: {}
  ruleSelector: {}
  resources:
    requests:
      memory: 400Mi
  storage:
    volumeClaimTemplate:
      spec:
        accessModes:
          - ReadWriteOnce
        resources:
          requests:
            storage: 10Gi
EOF
```

### 2.2 验证安装

```bash
# 检查CRD
kubectl get crd | grep monitoring.coreos.com

# 预期输出
alertmanagerconfigs.monitoring.coreos.com
alertmanagers.monitoring.coreos.com
podmonitors.monitoring.coreos.com
probes.monitoring.coreos.com
prometheuses.monitoring.coreos.com
prometheusrules.monitoring.coreos.com
servicemonitors.monitoring.coreos.com

# 检查Prometheus实例
kubectl get prometheus -n monitoring

# 端口转发访问Prometheus UI
kubectl port-forward -n monitoring svc/prometheus-operated 9090:9090

# 访问 http://localhost:9090
```

---

## 三、ServiceMonitor实现

### 3.1 ServiceMonitor定义

ServiceMonitor用于自动发现Kubernetes Service并抓取指标：

```yaml
# servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: rust-app-monitor
  namespace: default
  labels:
    release: prometheus  # 重要：匹配Prometheus的serviceMonitorSelector
spec:
  # 选择要监控的Service
  selector:
    matchLabels:
      app: rust-app
  
  # 监控端点配置
  endpoints:
    - port: metrics  # Service中定义的端口名
      interval: 30s  # 抓取间隔
      path: /metrics # 指标路径
      scheme: http
      
      # 可选：重新标记
      relabelings:
        - sourceLabels: [__meta_kubernetes_pod_name]
          targetLabel: pod
        - sourceLabels: [__meta_kubernetes_namespace]
          targetLabel: namespace
```

**关键字段**：

- `selector`: 匹配Service的标签选择器
- `endpoints.port`: Service中定义的端口名称（不是端口号）
- `interval`: 抓取频率
- `relabelings`: 重新标记Prometheus标签

### 3.2 Rust应用集成

**步骤1：Rust应用暴露指标**:

```rust
// src/main.rs
use axum::{routing::get, Router};
use metrics_exporter_prometheus::PrometheusHandle;
use std::net::SocketAddr;

#[tokio::main]
async fn main() {
    // 初始化Prometheus导出器
    let prometheus_handle = metrics_exporter_prometheus::PrometheusBuilder::new()
        .install_recorder()
        .unwrap();

    // 创建路由
    let app = Router::new()
        .route("/", get(|| async { "Hello, Kubernetes!" }))
        .route("/metrics", get(move || async move { prometheus_handle.render() }))
        .route("/health", get(|| async { "OK" }));

    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    println!("Listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

**步骤2：创建Kubernetes Service**:

```yaml
# service.yaml
apiVersion: v1
kind: Service
metadata:
  name: rust-app
  namespace: default
  labels:
    app: rust-app  # ServiceMonitor的selector匹配这个标签
spec:
  selector:
    app: rust-app
  ports:
    - name: http
      port: 80
      targetPort: 8080
    - name: metrics  # 指标端口（ServiceMonitor引用此名称）
      port: 9090
      targetPort: 8080
  type: ClusterIP
```

**步骤3：部署Deployment**:

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
  template:
    metadata:
      labels:
        app: rust-app
      annotations:
        prometheus.io/scrape: "true"  # 可选，便于识别
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      containers:
        - name: rust-app
          image: my-rust-app:latest
          ports:
            - containerPort: 8080
              name: http
          livenessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 10
            periodSeconds: 5
          readinessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 5
          resources:
            requests:
              memory: "128Mi"
              cpu: "100m"
            limits:
              memory: "256Mi"
              cpu: "500m"
```

**步骤4：应用所有资源**:

```bash
kubectl apply -f deployment.yaml
kubectl apply -f service.yaml
kubectl apply -f servicemonitor.yaml

# 验证ServiceMonitor被Prometheus识别
kubectl port-forward -n monitoring svc/prometheus-operated 9090:9090

# 访问 http://localhost:9090/targets
# 应该看到 serviceMonitor/default/rust-app-monitor/0
```

### 3.3 多端口监控

监控同一Service的多个端口：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: multi-port-monitor
spec:
  selector:
    matchLabels:
      app: multi-service
  endpoints:
    # 业务指标
    - port: metrics
      interval: 30s
      path: /metrics
      
    # JVM指标（如果有）
    - port: jmx
      interval: 60s
      path: /jmx-metrics
      
    # 自定义探针
    - port: probe
      interval: 10s
      path: /probe
```

---

## 四、PodMonitor实现

### 4.1 PodMonitor vs ServiceMonitor

**ServiceMonitor**:

- 基于Service发现
- 适用于通过Service暴露的应用

**PodMonitor**:

- 直接监控Pod
- 适用于StatefulSet、DaemonSet
- 无需创建Service

### 4.2 StatefulSet监控

监控StatefulSet部署的Rust应用：

```yaml
# statefulset.yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: rust-stateful-app
spec:
  serviceName: rust-stateful-app
  replicas: 3
  selector:
    matchLabels:
      app: rust-stateful-app
  template:
    metadata:
      labels:
        app: rust-stateful-app
    spec:
      containers:
        - name: app
          image: my-rust-app:latest
          ports:
            - containerPort: 8080
              name: metrics
          volumeMounts:
            - name: data
              mountPath: /data
  volumeClaimTemplates:
    - metadata:
        name: data
      spec:
        accessModes: ["ReadWriteOnce"]
        resources:
          requests:
            storage: 1Gi
---
# podmonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: PodMonitor
metadata:
  name: rust-stateful-monitor
  labels:
    release: prometheus
spec:
  selector:
    matchLabels:
      app: rust-stateful-app
  podMetricsEndpoints:
    - port: metrics
      interval: 30s
      path: /metrics
      
      # 添加StatefulSet特有标签
      relabelings:
        - sourceLabels: [__meta_kubernetes_pod_name]
          targetLabel: pod
        - sourceLabels: [__meta_kubernetes_pod_name]
          regex: '(.*)-([0-9]+)'
          replacement: '$2'
          targetLabel: pod_ordinal
```

**验证PodMonitor**：

```bash
kubectl get podmonitor
kubectl port-forward -n monitoring svc/prometheus-operated 9090:9090

# 在Prometheus UI的Targets页面查找 podMonitor/default/rust-stateful-monitor/0
```

---

## 五、PrometheusRule实现

### 5.1 告警规则定义

创建告警规则：

```yaml
# prometheusrule.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: rust-app-alerts
  namespace: default
  labels:
    release: prometheus
spec:
  groups:
    - name: rust-app
      interval: 30s
      rules:
        # 高错误率告警
        - alert: HighErrorRate
          expr: |
            rate(http_errors_total[5m]) / rate(http_requests_total[5m]) > 0.05
          for: 5m
          labels:
            severity: warning
            team: backend
          annotations:
            summary: "High error rate detected"
            description: "Error rate is {{ $value | humanizePercentage }} (threshold: 5%)"
            dashboard_url: "https://grafana.example.com/d/rust-app"

        # 高延迟告警
        - alert: HighLatency
          expr: |
            histogram_quantile(0.95, 
              rate(http_request_duration_seconds_bucket[5m])
            ) > 1.0
          for: 10m
          labels:
            severity: warning
            team: backend
          annotations:
            summary: "High API latency"
            description: "P95 latency is {{ $value }}s (threshold: 1s)"

        # Pod不可用
        - alert: PodDown
          expr: |
            up{job="rust-app"} == 0
          for: 1m
          labels:
            severity: critical
            team: sre
          annotations:
            summary: "Pod {{ $labels.pod }} is down"
            description: "Instance {{ $labels.instance }} has been down for more than 1 minute"

        # 内存使用过高
        - alert: HighMemoryUsage
          expr: |
            container_memory_usage_bytes{pod=~"rust-app-.*"} 
              / 
            container_spec_memory_limit_bytes{pod=~"rust-app-.*"} 
              > 0.9
          for: 5m
          labels:
            severity: warning
            team: backend
          annotations:
            summary: "High memory usage in {{ $labels.pod }}"
            description: "Memory usage is {{ $value | humanizePercentage }}"
```

### 5.2 Recording Rules

预计算常用查询以提升性能：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: rust-app-recordings
  labels:
    release: prometheus
spec:
  groups:
    - name: rust-app-recordings
      interval: 30s
      rules:
        # 预计算请求速率
        - record: job:http_requests:rate5m
          expr: |
            sum by (job, method, status) (
              rate(http_requests_total[5m])
            )

        # 预计算错误率
        - record: job:http_errors:rate5m
          expr: |
            sum by (job) (
              rate(http_errors_total[5m])
            )

        # 预计算P95延迟
        - record: job:http_request_duration:p95
          expr: |
            histogram_quantile(0.95,
              sum by (job, le) (
                rate(http_request_duration_seconds_bucket[5m])
              )
            )
```

### 5.3 告警分组

按严重级别和团队分组：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: grouped-alerts
spec:
  groups:
    # 关键告警（1分钟评估）
    - name: critical-alerts
      interval: 60s
      rules:
        - alert: ServiceDown
          expr: up == 0
          for: 1m
          labels:
            severity: critical

    # 警告告警（5分钟评估）
    - name: warning-alerts
      interval: 300s
      rules:
        - alert: HighCPU
          expr: rate(process_cpu_seconds_total[5m]) > 0.8
          for: 10m
          labels:
            severity: warning
```

**应用规则**：

```bash
kubectl apply -f prometheusrule.yaml

# 验证规则加载
kubectl port-forward -n monitoring svc/prometheus-operated 9090:9090

# 访问 http://localhost:9090/rules
```

---

## 六、AlertmanagerConfig实现

### 6.1 告警路由

配置Alertmanager路由：

```yaml
# alertmanagerconfig.yaml
apiVersion: monitoring.coreos.com/v1alpha1
kind: AlertmanagerConfig
metadata:
  name: rust-app-alerting
  namespace: default
spec:
  route:
    groupBy: ['alertname', 'severity']
    groupWait: 30s
    groupInterval: 5m
    repeatInterval: 12h
    
    # 根据严重级别路由
    routes:
      # 关键告警 -> PagerDuty
      - match:
          severity: critical
        receiver: pagerduty
        continue: true  # 继续匹配其他路由
      
      # 警告 -> Slack
      - match:
          severity: warning
        receiver: slack-warnings
      
      # 团队路由
      - match:
          team: backend
        receiver: backend-team-slack

  receivers:
    # PagerDuty接收器
    - name: pagerduty
      pagerdutyConfigs:
        - serviceKey:
            name: pagerduty-secret
            key: service-key
          description: '{{ .CommonAnnotations.summary }}'

    # Slack接收器
    - name: slack-warnings
      slackConfigs:
        - apiURL:
            name: slack-webhook-secret
            key: webhook-url
          channel: '#alerts-warnings'
          title: '{{ .CommonLabels.alertname }}'
          text: '{{ .CommonAnnotations.description }}'

    - name: backend-team-slack
      slackConfigs:
        - apiURL:
            name: slack-webhook-secret
            key: webhook-url
          channel: '#backend-team'
          title: '🚨 {{ .CommonLabels.alertname }}'
```

**创建Secret**：

```bash
# PagerDuty Secret
kubectl create secret generic pagerduty-secret \
  --from-literal=service-key=YOUR_PAGERDUTY_KEY \
  -n default

# Slack Webhook Secret
kubectl create secret generic slack-webhook-secret \
  --from-literal=webhook-url=https://hooks.slack.com/services/YOUR/WEBHOOK/URL \
  -n default
```

### 6.2 多通知渠道

配置多个通知渠道：

```yaml
spec:
  receivers:
    - name: multi-channel
      emailConfigs:
        - to: 'alerts@example.com'
          from: 'prometheus@example.com'
          smarthost: 'smtp.gmail.com:587'
          authUsername: 'alerts@example.com'
          authPassword:
            name: email-secret
            key: password
      
      slackConfigs:
        - apiURL:
            name: slack-webhook-secret
            key: webhook-url
          channel: '#alerts'
      
      webhookConfigs:
        - url: 'http://custom-alert-handler/webhook'
          sendResolved: true
```

### 6.3 告警静默

创建静默规则（维护窗口）：

```yaml
apiVersion: monitoring.coreos.com/v1alpha1
kind: Silence
metadata:
  name: maintenance-window
spec:
  matchers:
    - name: alertname
      value: HighLatency
      isRegex: false
  startsAt: "2025-10-11T20:00:00Z"
  endsAt: "2025-10-11T22:00:00Z"
  createdBy: "sre-team"
  comment: "Planned maintenance window"
```

---

## 七、高可用配置

### 7.1 Prometheus高可用

部署多副本Prometheus：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-ha
  namespace: monitoring
spec:
  replicas: 2  # 高可用：2个副本
  
  # 使用外部标签区分实例
  externalLabels:
    cluster: production
    replica: $(POD_NAME)
  
  # Pod反亲和性（避免调度到同一节点）
  affinity:
    podAntiAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
        - labelSelector:
            matchLabels:
              app.kubernetes.io/name: prometheus
          topologyKey: kubernetes.io/hostname
  
  # 持久化存储
  storage:
    volumeClaimTemplate:
      spec:
        accessModes:
          - ReadWriteOnce
        resources:
          requests:
            storage: 50Gi
        storageClassName: fast-ssd
  
  # 资源配额
  resources:
    requests:
      memory: 2Gi
      cpu: 1000m
    limits:
      memory: 4Gi
      cpu: 2000m
```

### 7.2 Thanos集成

使用Thanos实现长期存储和全局查询：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-with-thanos
spec:
  replicas: 2
  
  # Thanos Sidecar配置
  thanos:
    image: quay.io/thanos/thanos:v0.35.0
    version: v0.35.0
    objectStorageConfig:
      key: thanos.yaml
      name: thanos-objstore-config
  
  # 数据保留（本地2天，远程永久）
  retention: 2d
```

**Thanos对象存储配置**：

```yaml
# thanos-objstore-config.yaml
apiVersion: v1
kind: Secret
metadata:
  name: thanos-objstore-config
  namespace: monitoring
stringData:
  thanos.yaml: |
    type: S3
    config:
      bucket: prometheus-metrics
      endpoint: s3.amazonaws.com
      region: us-west-2
      access_key: ${AWS_ACCESS_KEY}
      secret_key: ${AWS_SECRET_KEY}
```

### 7.3 远程存储

配置Prometheus远程写入（Victoria Metrics）：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-remote-write
spec:
  remoteWrite:
    - url: http://victoria-metrics:8428/api/v1/write
      queueConfig:
        capacity: 10000
        maxShards: 10
        minShards: 1
        maxSamplesPerSend: 5000
        batchSendDeadline: 5s
      writeRelabelConfigs:
        - sourceLabels: [__name__]
          regex: 'expensive_metric.*'
          action: drop  # 不写入昂贵指标
```

---

## 八、Rust应用完整集成

### 8.1 应用代码

完整的Rust应用示例（带业务指标）：

```rust
// src/main.rs
use axum::{
    extract::State,
    http::StatusCode,
    routing::{get, post},
    Json, Router,
};
use metrics::{counter, histogram, gauge};
use metrics_exporter_prometheus::PrometheusHandle;
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;

#[derive(Clone)]
struct AppState {
    prometheus_handle: PrometheusHandle,
}

#[derive(Deserialize)]
struct CreateOrderRequest {
    product_id: u64,
    quantity: u32,
}

#[derive(Serialize)]
struct CreateOrderResponse {
    order_id: u64,
}

async fn create_order(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateOrderRequest>,
) -> Result<Json<CreateOrderResponse>, StatusCode> {
    let start = Instant::now();

    // 业务指标
    counter!("orders_total", "status" => "created").increment(1);
    
    // 模拟业务逻辑
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;

    let response = CreateOrderResponse { order_id: 12345 };

    // 延迟指标
    let duration = start.elapsed().as_secs_f64();
    histogram!("order_creation_duration_seconds").record(duration);

    // 活跃订单数（Gauge）
    gauge!("active_orders").increment(1.0);

    Ok(Json(response))
}

async fn health() -> &'static str {
    "OK"
}

async fn metrics_handler(State(state): State<Arc<AppState>>) -> String {
    state.prometheus_handle.render()
}

#[tokio::main]
async fn main() {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 初始化Prometheus
    let prometheus_handle = metrics_exporter_prometheus::PrometheusBuilder::new()
        .install_recorder()
        .expect("Failed to install Prometheus recorder");

    let state = Arc::new(AppState { prometheus_handle });

    // 路由
    let app = Router::new()
        .route("/api/orders", post(create_order))
        .route("/health", get(health))
        .route("/metrics", get(metrics_handler))
        .with_state(state);

    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    tracing::info!("Listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 8.2 Kubernetes Deployment

完整的Kubernetes资源：

```yaml
# namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: rust-app
---
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  namespace: rust-app
  labels:
    app: rust-app
    version: v1
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
        version: v1
    spec:
      containers:
        - name: rust-app
          image: my-rust-app:v1.0.0
          ports:
            - containerPort: 8080
              name: http
          env:
            - name: RUST_LOG
              value: info
          livenessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 10
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 5
          resources:
            requests:
              memory: "256Mi"
              cpu: "250m"
            limits:
              memory: "512Mi"
              cpu: "1000m"
---
# service.yaml
apiVersion: v1
kind: Service
metadata:
  name: rust-app
  namespace: rust-app
  labels:
    app: rust-app
spec:
  selector:
    app: rust-app
  ports:
    - name: http
      port: 80
      targetPort: 8080
    - name: metrics
      port: 9090
      targetPort: 8080
  type: ClusterIP
---
# servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: rust-app
  namespace: rust-app
  labels:
    release: prometheus
spec:
  selector:
    matchLabels:
      app: rust-app
  endpoints:
    - port: metrics
      interval: 30s
      path: /metrics
---
# prometheusrule.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: rust-app-alerts
  namespace: rust-app
  labels:
    release: prometheus
spec:
  groups:
    - name: rust-app
      interval: 30s
      rules:
        - alert: RustAppDown
          expr: up{job="rust-app/rust-app"} == 0
          for: 1m
          labels:
            severity: critical
          annotations:
            summary: "Rust app is down"
---
# ingress.yaml (可选)
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: rust-app
  namespace: rust-app
spec:
  rules:
    - host: rust-app.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: rust-app
                port:
                  number: 80
```

**应用资源**：

```bash
kubectl apply -f namespace.yaml
kubectl apply -f deployment.yaml
kubectl apply -f service.yaml
kubectl apply -f servicemonitor.yaml
kubectl apply -f prometheusrule.yaml

# 验证
kubectl get all -n rust-app
kubectl get servicemonitor -n rust-app
kubectl get prometheusrule -n rust-app
```

### 8.3 完整监控栈

一键部署完整监控栈：

```bash
# deploy-monitoring.sh
#!/bin/bash

# 1. 安装Prometheus Operator
helm install prometheus prometheus-community/kube-prometheus-stack \
  --namespace monitoring \
  --create-namespace \
  --set prometheus.prometheusSpec.serviceMonitorSelectorNilUsesHelmValues=false

# 2. 部署Rust应用
kubectl apply -f rust-app/

# 3. 等待Pod就绪
kubectl wait --for=condition=ready pod -l app=rust-app -n rust-app --timeout=300s

# 4. 端口转发
kubectl port-forward -n monitoring svc/prometheus-operated 9090:9090 &
kubectl port-forward -n monitoring svc/prometheus-grafana 3000:80 &

echo "✅ Monitoring stack deployed!"
echo "Prometheus: http://localhost:9090"
echo "Grafana: http://localhost:3000 (admin/prom-operator)"
```

---

## 九、高级特性

### 9.1 自定义指标

导出自定义业务指标：

```rust
// src/custom_metrics.rs
use metrics::{describe_counter, describe_histogram, Unit};

pub fn init_custom_metrics() {
    // 订单指标
    describe_counter!("orders_total", Unit::Count, "Total orders");
    describe_counter!("orders_revenue_cents", Unit::Count, "Total revenue in cents");
    
    // 支付指标
    describe_histogram!(
        "payment_processing_duration_seconds",
        Unit::Seconds,
        "Payment processing duration"
    );
    
    // 库存指标
    describe_counter!("inventory_updates_total", Unit::Count, "Inventory updates");
}
```

### 9.2 联邦集群

配置Prometheus联邦（多集群聚合）：

```yaml
# prometheus-federation.yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-global
spec:
  replicas: 2
  
  # 从其他Prometheus实例拉取数据
  additionalScrapeConfigs:
    name: additional-scrape-configs
    key: prometheus-additional.yaml
---
# additional-scrape-configs Secret
apiVersion: v1
kind: Secret
metadata:
  name: additional-scrape-configs
  namespace: monitoring
stringData:
  prometheus-additional.yaml: |
    - job_name: 'federate-cluster-1'
      honor_labels: true
      metrics_path: '/federate'
      params:
        'match[]':
          - '{job="rust-app"}'
      static_configs:
        - targets: ['prometheus-cluster-1.example.com:9090']
    
    - job_name: 'federate-cluster-2'
      honor_labels: true
      metrics_path: '/federate'
      params:
        'match[]':
          - '{job="rust-app"}'
      static_configs:
        - targets: ['prometheus-cluster-2.example.com:9090']
```

### 9.3 PushGateway集成

用于短生命周期任务（Batch Job）：

```rust
// src/batch_job.rs
use prometheus::{Encoder, Registry, TextEncoder, Counter};
use reqwest::Client;

async fn push_metrics_to_gateway(job_name: &str) -> anyhow::Result<()> {
    let registry = Registry::new();

    let counter = Counter::new("job_executions_total", "Total job executions")?;
    registry.register(Box::new(counter.clone()))?;

    counter.inc();

    // 编码指标
    let encoder = TextEncoder::new();
    let mut buffer = Vec::new();
    let metric_families = registry.gather();
    encoder.encode(&metric_families, &mut buffer)?;

    // 推送到PushGateway
    let client = Client::new();
    client
        .post(format!(
            "http://pushgateway.monitoring.svc:9091/metrics/job/{}",
            job_name
        ))
        .body(buffer)
        .send()
        .await?;

    Ok(())
}
```

**PushGateway ServiceMonitor**：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: pushgateway
  namespace: monitoring
spec:
  selector:
    matchLabels:
      app: pushgateway
  endpoints:
    - port: metrics
      interval: 30s
```

---

## 十、生产最佳实践

### 10.1 资源配额

为Prometheus设置合理资源：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-production
spec:
  replicas: 2
  
  resources:
    requests:
      memory: 4Gi   # 基准：1000 series = 1MB
      cpu: 2000m
    limits:
      memory: 8Gi
      cpu: 4000m
  
  # 存储大小计算：
  # retention * scrape_interval * series_count * bytes_per_sample
  # 15d * 30s * 100k * 2 bytes ≈ 100GB
  retention: 15d
  
  storage:
    volumeClaimTemplate:
      spec:
        accessModes:
          - ReadWriteOnce
        resources:
          requests:
            storage: 100Gi
        storageClassName: fast-ssd
```

### 10.2 数据保留

配置数据保留策略：

```yaml
spec:
  # 时间保留
  retention: 15d
  
  # 大小保留（优先级更高）
  retentionSize: "90GB"
  
  # WAL压缩
  walCompression: true
```

### 10.3 安全配置

启用TLS和认证：

```yaml
apiVersion: monitoring.coreos.com/v1
kind: Prometheus
metadata:
  name: prometheus-secure
spec:
  # TLS配置
  web:
    tlsConfig:
      cert:
        secret:
          name: prometheus-tls
          key: tls.crt
      keySecret:
        name: prometheus-tls
        key: tls.key
  
  # 启用RBAC
  securityContext:
    runAsNonRoot: true
    runAsUser: 1000
    fsGroup: 2000
  
  # 服务账户
  serviceAccountName: prometheus
```

---

## 十一、故障排查

### 常见问题

#### 1. ServiceMonitor未生效

**症状**：Prometheus Targets页面没有显示ServiceMonitor

**排查步骤**：

```bash
# 1. 检查ServiceMonitor是否存在
kubectl get servicemonitor -A

# 2. 检查标签选择器
kubectl get prometheus -n monitoring -o yaml | grep -A5 serviceMonitorSelector

# 3. 查看Prometheus日志
kubectl logs -n monitoring prometheus-prometheus-0 -c prometheus | grep servicemonitor

# 4. 验证Service标签
kubectl get svc rust-app -o yaml | grep labels -A5
```

**解决方案**：确保ServiceMonitor的`metadata.labels`包含Prometheus的`serviceMonitorSelector`匹配的标签（通常是`release: prometheus`）。

#### 2. 指标未显示

**症状**：Prometheus能抓取，但指标查询不到

**排查**：

```bash
# 1. 验证指标端点
kubectl port-forward pod/rust-app-xxx 8080:8080
curl http://localhost:8080/metrics

# 2. 检查标签基数
# 访问 Prometheus UI -> Status -> TSDB Status
# 查看 "Series Cardinality"

# 3. 检查抓取错误
# 访问 Prometheus UI -> Targets
# 查看 "Last Scrape" 和 "Last Error"
```

#### 3. 告警未触发

**排查**：

```bash
# 1. 检查PrometheusRule
kubectl get prometheusrule -A

# 2. 查看规则状态
# Prometheus UI -> Alerts

# 3. 检查规则语法
promtool check rules prometheusrule.yaml

# 4. 验证Alertmanager连接
kubectl logs -n monitoring prometheus-prometheus-0 | grep alertmanager
```

---

## 十二、参考资源

### 官方文档

1. **Prometheus Operator**: <https://prometheus-operator.dev/>
2. **Prometheus**: <https://prometheus.io/docs/>
3. **Alertmanager**: <https://prometheus.io/docs/alerting/latest/alertmanager/>

### 国际标准

1. **Kubernetes Operator Pattern**: <https://kubernetes.io/docs/concepts/extend-kubernetes/operator/>
2. **CNCF Prometheus Best Practices**: <https://www.cncf.io/blog/2021/11/18/prometheus-best-practices/>
3. **Google SRE Monitoring**: <https://sre.google/sre-book/monitoring-distributed-systems/>

### 工具

1. **kube-prometheus-stack Helm Chart**: <https://github.com/prometheus-community/helm-charts/tree/main/charts/kube-prometheus-stack>
2. **Thanos**: <https://thanos.io/>
3. **VictoriaMetrics**: <https://victoriametrics.com/>

---

## 总结

本文档提供了Prometheus Operator与Rust应用的完整集成指南，涵盖：

✅ **核心CRD**：ServiceMonitor、PodMonitor、PrometheusRule、AlertmanagerConfig  
✅ **自动化服务发现**：无需手动配置scrape targets  
✅ **告警管理**：PromQL规则、多渠道通知、告警路由  
✅ **高可用**：多副本、Thanos集成、远程存储  
✅ **Rust应用集成**：完整示例代码与Kubernetes资源  
✅ **生产最佳实践**：资源配额、数据保留、安全配置  
✅ **故障排查**：常见问题与解决方案  

**核心优势**：

- 声明式配置，GitOps友好
- 自动服务发现，无需重启
- 深度集成Kubernetes生态
- 生产级高可用配置

**下一步**：

- 探索OpenFaaS Serverless集成
- 学习HashiCorp Vault密钥管理
- 构建Kubernetes Operator
