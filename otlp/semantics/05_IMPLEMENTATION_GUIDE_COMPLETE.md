# 项目实施与验证完整指南

> **版本**: 1.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 目录

- [项目实施与验证完整指南](#项目实施与验证完整指南)
  - [📋 目录](#-目录)
  - [第一部分: 实施规划](#第一部分-实施规划)
    - [1.1 实施阶段](#11-实施阶段)
    - [1.2 规划检查清单](#12-规划检查清单)
    - [1.3 技术选型决策](#13-技术选型决策)
  - [第二部分: 环境准备](#第二部分-环境准备)
    - [2.1 基础设施需求](#21-基础设施需求)
      - [2.1.1 硬件资源](#211-硬件资源)
      - [2.1.2 网络配置](#212-网络配置)
    - [2.2 软件安装](#22-软件安装)
      - [2.2.1 Docker环境](#221-docker环境)
      - [2.2.2 Kubernetes环境](#222-kubernetes环境)
  - [第三部分: Collector部署](#第三部分-collector部署)
    - [3.1 Docker Compose部署](#31-docker-compose部署)
      - [3.1.1 完整示例](#311-完整示例)
    - [3.2 Kubernetes部署](#32-kubernetes部署)
      - [3.2.1 使用Helm Chart](#321-使用helm-chart)
      - [3.2.2 手动部署清单](#322-手动部署清单)
  - [第四部分: 应用仪表化](#第四部分-应用仪表化)
    - [4.1 自动仪表化](#41-自动仪表化)
      - [4.1.1 Java应用](#411-java应用)
      - [4.1.2 Python应用](#412-python应用)
      - [4.1.3 Node.js应用](#413-nodejs应用)
    - [4.2 手动仪表化(Rust)](#42-手动仪表化rust)
  - [第五部分: 后端集成](#第五部分-后端集成)
    - [5.1 Jaeger集成](#51-jaeger集成)
    - [5.2 Prometheus集成](#52-prometheus集成)
    - [5.3 Grafana配置](#53-grafana配置)
  - [第六部分: 功能验证](#第六部分-功能验证)
    - [6.1 Traces验证](#61-traces验证)
    - [6.2 Metrics验证](#62-metrics验证)
    - [6.3 Logs验证](#63-logs验证)
  - [第七部分: 性能测试](#第七部分-性能测试)
    - [7.1 压力测试](#71-压力测试)
    - [7.2 性能指标监控](#72-性能指标监控)
    - [7.3 基准测试报告](#73-基准测试报告)
  - [第八部分: 生产上线](#第八部分-生产上线)
    - [8.1 灰度发布计划](#81-灰度发布计划)
    - [8.2 上线检查清单](#82-上线检查清单)
    - [8.3 运维手册](#83-运维手册)
  - [📚 参考资源](#-参考资源)

---

## 第一部分: 实施规划

### 1.1 实施阶段

```text
完整实施路线:
┌────────────────────────────────────────────────┐
│ Phase 1: 规划与设计 (1-2周)                      │
│  - 需求分析                                     │
│  - 架构设计                                     │
│  - 技术选型                                     │
└────────────────────────────────────────────────┘
            ▼
┌────────────────────────────────────────────────┐
│ Phase 2: 环境准备 (1周)                         │
│  - 基础设施准备                                 │
│  - 工具安装                                     │
│  - 网络配置                                     │
└────────────────────────────────────────────────┘
            ▼
┌────────────────────────────────────────────────┐
│ Phase 3: Pilot试点 (2-3周)                      │
│  - 单个应用仪表化                               │
│  - Collector部署                                │
│  - 功能验证                                     │
└────────────────────────────────────────────────┘
            ▼
┌────────────────────────────────────────────────┐
│ Phase 4: 扩展推广 (4-6周)                       │
│  - 多应用覆盖                                   │
│  - 性能优化                                     │
│  - 最佳实践总结                                 │
└────────────────────────────────────────────────┘
            ▼
┌────────────────────────────────────────────────┐
│ Phase 5: 生产上线 (2-4周)                       │
│  - 灰度发布                                     │
│  - 全量上线                                     │
│  - 持续优化                                     │
└────────────────────────────────────────────────┘
```

### 1.2 规划检查清单

```yaml
planning_checklist:
  需求分析:
    □ 确定监控目标(Traces/Metrics/Logs/Profiles)
    □ 识别关键服务和依赖
    □ 评估现有监控方案
    □ 定义成功标准和KPI
  
  架构设计:
    □ 选择部署模式(Agent/Gateway/Sidecar)
    □ 规划Collector架构(集中式/分层/混合)
    □ 选择后端存储(Jaeger/Prometheus/Loki/...)
    □ 设计数据流和采样策略
  
  资源评估:
    □ 计算资源需求(CPU/内存/存储)
    □ 网络带宽需求
    □ 人力资源(开发/运维/SRE)
    □ 预算和成本
  
  风险评估:
    □ 性能影响评估
    □ 安全和合规要求
    □ 数据保留策略
    □ 故障恢复计划
```

### 1.3 技术选型决策

| 维度 | 选项 | 推荐场景 |
|------|------|---------|
| **Collector部署** | Agent模式 | 每个主机一个Collector |
|  | Gateway模式 | 集中式处理和路由 |
|  | Sidecar模式 | Kubernetes环境 |
| **传输协议** | gRPC | 高性能、低延迟 |
|  | HTTP/JSON | 易调试、兼容性好 |
| **采样策略** | 头部采样 | 简单、低开销 |
|  | 尾部采样 | 智能、基于完整Trace |
| **后端存储** | Jaeger | Traces |
|  | Tempo | Traces(对象存储) |
|  | Prometheus | Metrics |
|  | Loki | Logs |
|  | 商业方案 | Datadog/New Relic/... |

---

## 第二部分: 环境准备

### 2.1 基础设施需求

#### 2.1.1 硬件资源

```yaml
# OTel Collector资源需求(参考值)
collector_resources:
  # Agent模式(每个主机)
  agent:
    cpu: 0.5-1 core
    memory: 512MB-1GB
    disk: 10GB(日志和缓存)
    network: 100Mbps
  
  # Gateway模式(集中式)
  gateway:
    cpu: 4-8 cores
    memory: 8-16GB
    disk: 50GB
    network: 1Gbps
  
  # 后端存储(取决于数据量)
  backend:
    jaeger:
      cpu: 4+ cores
      memory: 8+ GB
      disk: 100GB+ (SSD推荐)
    
    prometheus:
      cpu: 2+ cores
      memory: 4+ GB
      disk: 50GB+ per million samples/day
```

#### 2.1.2 网络配置

```yaml
# 端口规划
network_ports:
  collector:
    - 4317/tcp: OTLP gRPC
    - 4318/tcp: OTLP HTTP
    - 8888/tcp: Metrics (Prometheus)
    - 8889/tcp: Health check
    - 13133/tcp: Health extension
  
  jaeger:
    - 16686/tcp: UI
    - 14250/tcp: gRPC
    - 14268/tcp: HTTP
  
  prometheus:
    - 9090/tcp: Web UI / API
  
  loki:
    - 3100/tcp: HTTP

# 防火墙规则
firewall_rules:
  - allow: app -> collector (4317, 4318)
  - allow: collector -> backend (Jaeger:14250, Prometheus:9090)
  - allow: monitoring -> collector:8888 (metrics)
```

### 2.2 软件安装

#### 2.2.1 Docker环境

```bash
# 安装Docker
curl -fsSL https://get.docker.com | sh
sudo usermod -aG docker $USER

# 安装Docker Compose
sudo curl -L "https://github.com/docker/compose/releases/download/v2.23.0/docker-compose-$(uname -s)-$(uname -m)" \
  -o /usr/local/bin/docker-compose
sudo chmod +x /usr/local/bin/docker-compose
```

#### 2.2.2 Kubernetes环境

```bash
# 安装kubectl
curl -LO "https://dl.k8s.io/release/$(curl -L -s https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl"
sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl

# 安装Helm
curl https://raw.githubusercontent.com/helm/helm/main/scripts/get-helm-3 | bash

# 添加OTel Helm Repo
helm repo add open-telemetry https://open-telemetry.github.io/opentelemetry-helm-charts
helm repo update
```

---

## 第三部分: Collector部署

### 3.1 Docker Compose部署

#### 3.1.1 完整示例

```yaml
# docker-compose.yml
version: '3.8'

services:
  # OTel Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.89.0
    command: ["--config=/etc/otelcol/config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otelcol/config.yaml:ro
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Metrics
    networks:
      - otel
    restart: unless-stopped
  
  # Jaeger (Traces后端)
  jaeger:
    image: jaegertracing/all-in-one:1.51
    ports:
      - "16686:16686"  # UI
      - "14250:14250"  # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - otel
    restart: unless-stopped
  
  # Prometheus (Metrics后端)
  prometheus:
    image: prom/prometheus:v2.47.0
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--storage.tsdb.retention.time=30d'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml:ro
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    networks:
      - otel
    restart: unless-stopped
  
  # Loki (Logs后端)
  loki:
    image: grafana/loki:2.9.0
    ports:
      - "3100:3100"
    command: -config.file=/etc/loki/local-config.yaml
    networks:
      - otel
    restart: unless-stopped
  
  # Grafana (可视化)
  grafana:
    image: grafana/grafana:10.1.0
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml:ro
    networks:
      - otel
    depends_on:
      - prometheus
      - loki
      - jaeger
    restart: unless-stopped

volumes:
  prometheus-data:
  grafana-data:

networks:
  otel:
    driver: bridge
```

```yaml
# otel-collector-config.yaml
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
    limit_mib: 512
  
  resource:
    attributes:
      - key: deployment.environment
        value: dev
        action: upsert

exporters:
  # Jaeger导出
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true
  
  # Prometheus导出
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: otel
  
  # Loki导出
  loki:
    endpoint: http://loki:3100/loki/api/v1/push
  
  # 调试输出
  logging:
    loglevel: info

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [otlp/jaeger, logging]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [prometheus]
    
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [loki, logging]
  
  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888
```

```bash
# 启动
docker-compose up -d

# 查看日志
docker-compose logs -f otel-collector

# 访问UI
# Grafana: http://localhost:3000 (admin/admin)
# Jaeger: http://localhost:16686
# Prometheus: http://localhost:9090
```

### 3.2 Kubernetes部署

#### 3.2.1 使用Helm Chart

```bash
# 创建命名空间
kubectl create namespace observability

# 安装Cert Manager(如果使用webhook)
kubectl apply -f https://github.com/cert-manager/cert-manager/releases/download/v1.13.0/cert-manager.yaml

# 安装OTel Operator
helm install opentelemetry-operator open-telemetry/opentelemetry-operator \
  --namespace observability \
  --set admissionWebhooks.certManager.enabled=true

# 安装Collector
helm install otel-collector open-telemetry/opentelemetry-collector \
  --namespace observability \
  --values otel-collector-values.yaml
```

```yaml
# otel-collector-values.yaml
mode: daemonset  # 或 deployment, statefulset

image:
  repository: otel/opentelemetry-collector-contrib
  tag: 0.89.0

config:
  receivers:
    otlp:
      protocols:
        grpc:
          endpoint: ${env:MY_POD_IP}:4317
        http:
          endpoint: ${env:MY_POD_IP}:4318
    
    # Kubernetes Metrics
    kubeletstats:
      collection_interval: 30s
      auth_type: "serviceAccount"
      endpoint: "https://${env:K8S_NODE_NAME}:10250"
      insecure_skip_verify: true
  
  processors:
    batch:
      timeout: 10s
    
    # K8s属性处理器
    k8sattributes:
      auth_type: "serviceAccount"
      passthrough: false
      extract:
        metadata:
          - k8s.namespace.name
          - k8s.pod.name
          - k8s.pod.uid
          - k8s.deployment.name
          - k8s.node.name
        labels:
          - tag_name: app
            key: app
            from: pod
    
    resource:
      attributes:
        - key: cluster.name
          value: prod-k8s
          action: upsert
  
  exporters:
    otlp:
      endpoint: jaeger.observability.svc.cluster.local:4317
      tls:
        insecure: true
    
    prometheusremotewrite:
      endpoint: http://prometheus.observability.svc.cluster.local:9090/api/v1/write
  
  service:
    pipelines:
      traces:
        receivers: [otlp]
        processors: [k8sattributes, batch, resource]
        exporters: [otlp]
      
      metrics:
        receivers: [otlp, kubeletstats]
        processors: [k8sattributes, batch]
        exporters: [prometheusremotewrite]

# 资源配置
resources:
  limits:
    cpu: 1000m
    memory: 1Gi
  requests:
    cpu: 200m
    memory: 256Mi

# ServiceMonitor(Prometheus Operator)
serviceMonitor:
  enabled: true

# 节点选择器
nodeSelector: {}

# 容忍度
tolerations: []

# Affinity
affinity: {}
```

#### 3.2.2 手动部署清单

```yaml
# otel-collector-k8s.yaml
---
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
  config.yaml: |
    # (完整配置,同上)

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
    resources: ["nodes", "nodes/proxy", "services", "endpoints", "pods"]
    verbs: ["get", "list", "watch"]
  - apiGroups: ["apps"]
    resources: ["deployments", "daemonsets", "replicasets", "statefulsets"]
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

---
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: observability
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
        - name: collector
          image: otel/opentelemetry-collector-contrib:0.89.0
          command: ["--config=/etc/otelcol/config.yaml"]
          
          env:
            - name: MY_POD_IP
              valueFrom:
                fieldRef:
                  fieldPath: status.podIP
            - name: K8S_NODE_NAME
              valueFrom:
                fieldRef:
                  fieldPath: spec.nodeName
          
          ports:
            - containerPort: 4317
              name: otlp-grpc
            - containerPort: 4318
              name: otlp-http
            - containerPort: 8888
              name: metrics
          
          volumeMounts:
            - name: config
              mountPath: /etc/otelcol
          
          resources:
            requests:
              cpu: 200m
              memory: 256Mi
            limits:
              cpu: 1000m
              memory: 1Gi
      
      volumes:
        - name: config
          configMap:
            name: otel-collector-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    app: otel-collector
  ports:
    - name: otlp-grpc
      port: 4317
      targetPort: 4317
    - name: otlp-http
      port: 4318
      targetPort: 4318
    - name: metrics
      port: 8888
      targetPort: 8888
  type: ClusterIP
```

```bash
# 部署
kubectl apply -f otel-collector-k8s.yaml

# 验证
kubectl get pods -n observability
kubectl logs -n observability -l app=otel-collector

# 端口转发测试
kubectl port-forward -n observability svc/otel-collector 4317:4317
```

---

## 第四部分: 应用仪表化

### 4.1 自动仪表化

#### 4.1.1 Java应用

```bash
# 下载Java Agent
wget https://github.com/open-telemetry/opentelemetry-java-instrumentation/releases/latest/download/opentelemetry-javaagent.jar

# 启动应用
java -javaagent:opentelemetry-javaagent.jar \
  -Dotel.service.name=my-java-app \
  -Dotel.traces.exporter=otlp \
  -Dotel.metrics.exporter=otlp \
  -Dotel.logs.exporter=otlp \
  -Dotel.exporter.otlp.endpoint=http://localhost:4317 \
  -jar myapp.jar
```

```dockerfile
# Dockerfile
FROM openjdk:17-jdk-slim
ADD https://github.com/open-telemetry/opentelemetry-java-instrumentation/releases/latest/download/opentelemetry-javaagent.jar /app/
COPY myapp.jar /app/
WORKDIR /app
ENV JAVA_TOOL_OPTIONS="-javaagent:/app/opentelemetry-javaagent.jar"
ENV OTEL_SERVICE_NAME=my-java-app
ENV OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
CMD ["java", "-jar", "myapp.jar"]
```

#### 4.1.2 Python应用

```bash
# 安装
pip install opentelemetry-distro opentelemetry-exporter-otlp

# 自动仪表化
opentelemetry-bootstrap -a install

# 运行应用
opentelemetry-instrument \
  --traces_exporter otlp \
  --metrics_exporter otlp \
  --service_name my-python-app \
  --exporter_otlp_endpoint http://localhost:4317 \
  python app.py
```

#### 4.1.3 Node.js应用

```javascript
// package.json
{
  "dependencies": {
    "@opentelemetry/sdk-node": "^0.45.0",
    "@opentelemetry/auto-instrumentations-node": "^0.40.0",
    "@opentelemetry/exporter-trace-otlp-grpc": "^0.45.0"
  }
}

// tracing.js
const { NodeSDK } = require('@opentelemetry/sdk-node');
const { getNodeAutoInstrumentations } = require('@opentelemetry/auto-instrumentations-node');
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');

const sdk = new NodeSDK({
  serviceName: 'my-node-app',
  traceExporter: new OTLPTraceExporter({
    url: 'http://localhost:4317',
  }),
  instrumentations: [getNodeAutoInstrumentations()],
});

sdk.start();

process.on('SIGTERM', () => {
  sdk.shutdown()
    .then(() => console.log('Tracing terminated'))
    .catch((error) => console.log('Error terminating tracing', error))
    .finally(() => process.exit(0));
});

// 启动
node --require ./tracing.js app.js
```

### 4.2 手动仪表化(Rust)

```rust
// Cargo.toml
[dependencies]
opentelemetry = "0.21"
opentelemetry-otlp = "0.14"
opentelemetry_sdk = "0.21"
tokio = { version = "1", features = ["full"] }
tracing = "0.1"
tracing-opentelemetry = "0.22"
tracing-subscriber = "0.3"

// main.rs
use opentelemetry::global;
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{trace, Resource};
use opentelemetry::KeyValue;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OTel
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::config()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "my-rust-app"),
                    KeyValue::new("service.version", "1.0.0"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 配置tracing
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = Registry::default().with(telemetry);
    tracing::subscriber::set_global_default(subscriber)?;
    
    // 应用逻辑
    run_app().await;
    
    // 清理
    global::shutdown_tracer_provider();
    Ok(())
}

#[tracing::instrument]
async fn run_app() {
    println!("App running with OTel!");
    // ...
}
```

---

## 第五部分: 后端集成

### 5.1 Jaeger集成

```yaml
# Jaeger完整部署(生产级)
apiVersion: jaegertracing.io/v1
kind: Jaeger
metadata:
  name: jaeger
  namespace: observability
spec:
  strategy: production
  
  storage:
    type: elasticsearch
    options:
      es:
        server-urls: http://elasticsearch:9200
        index-prefix: jaeger
    
    elasticsearch:
      nodeCount: 3
      redundancyPolicy: MultipleRedundancy
      storage:
        storageClassName: fast-ssd
        size: 100Gi
  
  query:
    replicas: 2
    resources:
      requests:
        cpu: 500m
        memory: 512Mi
      limits:
        cpu: 1000m
        memory: 1Gi
  
  collector:
    replicas: 3
    maxReplicas: 10
    autoscale: true
    resources:
      requests:
        cpu: 500m
        memory: 512Mi
      limits:
        cpu: 2000m
        memory: 2Gi
```

### 5.2 Prometheus集成

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  # OTel Collector自身指标
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
    
  # 通过OTel Collector导出的应用指标
  - job_name: 'otel-apps'
    static_configs:
      - targets: ['otel-collector:8889']
```

### 5.3 Grafana配置

```yaml
# grafana-datasources.yml
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
    editable: true
  
  - name: Jaeger
    type: jaeger
    access: proxy
    url: http://jaeger-query:16686
    editable: true
  
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    editable: true
```

---

## 第六部分: 功能验证

### 6.1 Traces验证

```bash
# 1. 生成测试Trace
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{
    "resourceSpans": [{
      "resource": {
        "attributes": [{
          "key": "service.name",
          "value": { "stringValue": "test-service" }
        }]
      },
      "scopeSpans": [{
        "spans": [{
          "traceId": "5b8aa5a2d2c872e8321cf37308d69df2",
          "spanId": "051581bf3cb55c13",
          "name": "test-span",
          "kind": 1,
          "startTimeUnixNano": "1697500000000000000",
          "endTimeUnixNano": "1697500001000000000",
          "attributes": [{
            "key": "http.method",
            "value": { "stringValue": "GET" }
          }]
        }]
      }]
    }]
  }'

# 2. 在Jaeger UI查询
open http://localhost:16686
# 搜索service="test-service"

# 3. 验证Trace完整性
# - Trace ID正确
# - Span层级关系正确
# - 属性完整
# - 时间戳合理
```

### 6.2 Metrics验证

```bash
# 1. 查看Collector导出的指标
curl http://localhost:8888/metrics

# 2. 查询Prometheus
curl 'http://localhost:9090/api/v1/query?query=up'

# 3. 验证应用指标
curl 'http://localhost:9090/api/v1/query?query=http_requests_total'

# 4. 在Grafana创建Dashboard
# - 添加Panel
# - 查询: rate(http_requests_total[5m])
# - 可视化类型: Graph
```

### 6.3 Logs验证

```bash
# 1. 发送测试Log
curl -X POST http://localhost:4318/v1/logs \
  -H "Content-Type: application/json" \
  -d '{
    "resourceLogs": [{
      "resource": {
        "attributes": [{
          "key": "service.name",
          "value": { "stringValue": "test-service" }
        }]
      },
      "scopeLogs": [{
        "logRecords": [{
          "timeUnixNano": "1697500000000000000",
          "severityText": "INFO",
          "body": {
            "stringValue": "Test log message"
          }
        }]
      }]
    }]
  }'

# 2. 在Loki查询
curl -G -s 'http://localhost:3100/loki/api/v1/query' \
  --data-urlencode 'query={service_name="test-service"}'

# 3. 在Grafana Explore查看
# - 选择Loki数据源
# - 查询: {service_name="test-service"}
```

---

## 第七部分: 性能测试

### 7.1 压力测试

```bash
# 使用k6进行压力测试
npm install -g k6

# test-script.js
import { check } from 'k6';
import http from 'k6/http';

export let options = {
  stages: [
    { duration: '2m', target: 100 }, // 2分钟内增加到100 VU
    { duration: '5m', target: 100 }, // 维持5分钟
    { duration: '2m', target: 0 },   // 2分钟内降到0
  ],
  thresholds: {
    'http_req_duration': ['p(95)<500'], // 95%请求<500ms
    'http_req_failed': ['rate<0.01'],   // 错误率<1%
  },
};

export default function () {
  let response = http.get('http://my-app:8080/api/test');
  check(response, {
    'status is 200': (r) => r.status === 200,
  });
}

# 运行
k6 run test-script.js
```

### 7.2 性能指标监控

```yaml
# 关键性能指标
performance_metrics:
  collector:
    - otelcol_receiver_accepted_spans (spans接收数)
    - otelcol_receiver_refused_spans (spans拒绝数)
    - otelcol_processor_batch_batch_send_size (批处理大小)
    - otelcol_exporter_sent_spans (spans发送数)
    - otelcol_exporter_send_failed_spans (发送失败数)
    - process_cpu_seconds_total (CPU使用)
    - process_resident_memory_bytes (内存使用)
  
  application:
    - http_server_duration_milliseconds (请求延迟)
    - http_server_active_requests (活跃请求)
    - process_cpu_seconds_total (CPU使用)
    - process_resident_memory_bytes (内存使用)
    - jvm_gc_pause_seconds (GC暂停时间, Java)
```

### 7.3 基准测试报告

```markdown
# 性能基准测试报告

## 测试环境
- Collector: 2 CPU, 4GB RAM
- 应用: 10个实例, 各1 CPU, 2GB RAM
- 负载: 1000 RPS, 持续10分钟

## 测试结果

| 指标 | 目标 | 实际 | 状态 |
|------|------|------|------|
| 应用P95延迟 | <200ms | 145ms | ✅ |
| 应用P99延迟 | <500ms | 312ms | ✅ |
| Collector CPU | <50% | 32% | ✅ |
| Collector内存 | <2GB | 1.2GB | ✅ |
| Traces吞吐 | >10k/s | 12.5k/s | ✅ |
| 数据丢失率 | <0.1% | 0.02% | ✅ |
| E2E延迟 | <5s | 2.3s | ✅ |

## 结论
系统在目标负载下表现良好,满足生产要求。
```

---

## 第八部分: 生产上线

### 8.1 灰度发布计划

```yaml
rollout_plan:
  phase_1: # 灰度5%
    duration: 2天
    targets:
      - 1个非关键服务
    validation:
      - 功能正常
      - 无性能劣化
      - 错误率<0.1%
  
  phase_2: # 扩展到20%
    duration: 1周
    targets:
      - 3-5个服务
    validation:
      - Traces完整性>95%
      - E2E延迟<5s
      - 成本可控
  
  phase_3: # 全量50%
    duration: 2周
    targets:
      - 所有非核心服务
    validation:
      - 监控覆盖度>80%
      - 运维团队培训完成
  
  phase_4: # 100%
    duration: 1个月
    targets:
      - 所有服务
    validation:
      - 全面替代旧监控
      - 文档完善
      - On-call流程建立
```

### 8.2 上线检查清单

```yaml
production_checklist:
  部署前:
    □ 性能测试通过
    □ 安全审计完成
    □ 备份和回滚方案测试
    □ 监控告警配置
    □ 文档更新
    □ 团队培训完成
    □ 变更审批通过
  
  部署中:
    □ 灰度发布执行
    □ 实时监控指标
    □ 日志检查
    □ 功能验证
    □ 性能对比
  
  部署后:
    □ 全量验证
    □ 用户反馈收集
    □ 性能优化
    □ 成本分析
    □ 经验总结
```

### 8.3 运维手册

```markdown
    # OTel运维手册

    ## 日常运维

    ### 健康检查
    ```bash
    # Collector健康检查
    curl http://collector:13133/

    # 查看Collector日志
    kubectl logs -n observability -l app=otel-collector --tail=100

    # 监控关键指标
    # - Collector CPU/内存
    # - Traces吞吐量
    # - 错误率
    ```

    ### 常见问题

    #### 1. Collector OOM

    **症状**: Collector pod重启频繁
    **原因**: 内存限制过低或数据量激增
    **解决**:

    ```bash
    # 增加内存限制
    kubectl set resources deployment/otel-collector \
    --limits=memory=4Gi \
    -n observability

    # 或调整批处理配置
    # batch.send_batch_size: 减小
    # batch.timeout: 减小
    ```

    #### 2. 数据丢失

    **症状**: Traces不完整或缺失
    **原因**: Collector过载或网络问题
    **解决**:

    - 检查Collector指标: otelcol_receiver_refused_spans
    - 扩展Collector副本数
    - 调整采样率

    #### 3. 查询慢

    **症状**: Jaeger/Grafana查询超时
    **原因**: 后端存储负载高
    **解决**:

    - 增加Elasticsearch节点
    - 优化索引策略
    - 减少数据保留期

    ### 应急响应

    **P0故障(服务不可用)**:

    1. 禁用OTel仪表化(恢复应用)
    2. 定位根因
    3. 修复后灰度启用

    **P1故障(部分功能异常)**:

    1. 隔离问题Collector
    2. 调整配置
    3. 监控恢复

    ### 升级流程

    1. 测试环境验证新版本
    2. 备份配置
    3. 灰度升级Collector
    4. 验证功能
    5. 全量升级

```

---

## 📚 参考资源

- [OTel官方文档](https://opentelemetry.io/docs/)
- [Collector配置参考](https://opentelemetry.io/docs/collector/configuration/)
- [最佳实践](https://opentelemetry.io/docs/concepts/best-practices/)

---

**完整的实施与验证指南!** 🎓
