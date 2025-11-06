# OpAMP部署完整指南

> **版本**: 1.0
> **日期**: 2025年10月17日
> **状态**: ✅ 完整版

---

## 📋 目录

- [OpAMP部署完整指南](#opamp部署完整指南)
  - [📋 目录](#-目录)
  - [第一部分：OpAMP概述](#第一部分opamp概述)
    - [1.1 什么是OpAMP?](#11-什么是opamp)
      - [核心能力](#核心能力)
      - [OpAMP vs 传统管理方式](#opamp-vs-传统管理方式)
    - [1.2 OpAMP协议架构](#12-opamp协议架构)
    - [1.3 OpAMP消息类型](#13-opamp消息类型)
  - [第二部分：架构设计](#第二部分架构设计)
    - [2.1 部署架构选型](#21-部署架构选型)
      - [2.1.1 中心化架构](#211-中心化架构)
      - [2.1.2 分层架构](#212-分层架构)
      - [2.1.3 混合架构(推荐)](#213-混合架构推荐)
    - [2.2 高可用设计](#22-高可用设计)
      - [2.2.1 服务器高可用](#221-服务器高可用)
      - [2.2.2 数据持久化](#222-数据持久化)
  - [第三部分：部署方案](#第三部分部署方案)
    - [3.1 Docker部署](#31-docker部署)
      - [3.1.1 OpAMP Server](#311-opamp-server)
      - [3.1.2 OpAMP Agent(Collector集成)](#312-opamp-agentcollector集成)
    - [3.2 Kubernetes部署](#32-kubernetes部署)
      - [3.2.1 完整部署清单](#321-完整部署清单)
      - [3.2.2 Collector DaemonSet部署](#322-collector-daemonset部署)
  - [第四部分：配置管理](#第四部分配置管理)
    - [4.1 配置下发流程](#41-配置下发流程)
    - [4.2 配置模板管理](#42-配置模板管理)
    - [4.3 灰度发布策略](#43-灰度发布策略)
  - [第五部分：安全与认证](#第五部分安全与认证)
    - [5.1 TLS/mTLS配置](#51-tlsmtls配置)
      - [5.1.1 生成证书](#511-生成证书)
      - [5.1.2 证书轮换](#512-证书轮换)
    - [5.2 认证机制](#52-认证机制)
      - [5.2.1 JWT认证](#521-jwt认证)
      - [5.2.2 API Key认证](#522-api-key认证)
  - [第六部分：监控与运维](#第六部分监控与运维)
    - [6.1 关键指标](#61-关键指标)
      - [6.1.1 Server端指标](#611-server端指标)
      - [6.1.2 Agent端指标](#612-agent端指标)
    - [6.2 告警规则](#62-告警规则)
    - [6.3 日志示例](#63-日志示例)
  - [第七部分：故障排查](#第七部分故障排查)
    - [7.1 常见问题](#71-常见问题)
      - [7.1.1 连接问题](#711-连接问题)
      - [7.1.2 认证问题](#712-认证问题)
    - [7.2 调试工具](#72-调试工具)
  - [第八部分：最佳实践](#第八部分最佳实践)
    - [8.1 部署检查清单](#81-部署检查清单)
    - [8.2 性能优化](#82-性能优化)
    - [8.3 安全加固](#83-安全加固)
  - [📚 参考资源](#-参考资源)

---

## 第一部分：OpAMP概述

### 1.1 什么是OpAMP?

**OpAMP (Open Agent Management Protocol)** 是OpenTelemetry定义的代理管理协议,用于远程管理和配置遥测数据采集代理(如OpenTelemetry Collector)。

#### 核心能力

```text
OpAMP核心能力:
├── 配置管理: 远程下发和更新配置
├── 包管理: 自动更新Agent和插件
├── 状态监控: 实时健康检查和性能监控
├── 远程控制: 重启、停止、调试
├── 证书轮换: 自动化证书管理
└── 连接管理: 断线重连、负载均衡
```

#### OpAMP vs 传统管理方式

| 维度 | 传统方式 | OpAMP |
|------|---------|-------|
| **配置更新** | 手动SSH/配置管理工具 | 自动推送,实时生效 |
| **扩展性** | 难以管理大规模集群 | 支持数万节点 |
| **安全性** | 依赖外部工具 | 内置TLS、mTLS |
| **状态可见性** | 需要额外监控 | 实时健康和指标上报 |
| **灰度发布** | 复杂脚本 | 内置灰度策略 |

### 1.2 OpAMP协议架构

```text
┌─────────────────────────────────────────────────────────┐
│                    OpAMP Server                         │
│  ┌────────────┐  ┌──────────────┐  ┌────────────────┐   │
│  │ Config Mgr │  │ Package Repo │  │ Health Monitor │   │
│  └────────────┘  └──────────────┘  └────────────────┘   │
└──────────────────────┬──────────────────────────────────┘
                       │ WebSocket/HTTP/gRPC
                       │ (TLS/mTLS)
    ┌──────────────────┼──────────────────┐
    │                  │                  │
    ▼                  ▼                  ▼
┌─────────┐      ┌─────────┐      ┌─────────┐
│ Agent 1 │      │ Agent 2 │      │ Agent N │
│ (OTel   │      │ (OTel   │      │ (OTel   │
│ Colllec)│      │ Colllec)│      │ Colllec)│
└─────────┘      └─────────┘      └─────────┘
```

### 1.3 OpAMP消息类型

| 消息类型 | 方向 | 说明 |
|---------|------|------|
| **AgentToServer** | Agent → Server | 状态上报、配置确认、健康心跳 |
| **ServerToAgent** | Server → Agent | 配置下发、包更新、控制命令 |
| **EffectiveConfig** | Agent → Server | 当前生效的配置 |
| **RemoteConfig** | Server → Agent | 新配置内容 |
| **PackagesAvailable** | Server → Agent | 可用的包和版本 |
| **ConnectionSettings** | Server → Agent | 连接参数更新 |

---

## 第二部分：架构设计

### 2.1 部署架构选型

#### 2.1.1 中心化架构

```text
              ┌──────────────────┐
              │  OpAMP Server    │
              │  (Central)       │
              └────────┬─────────┘
                       │
         ┌─────────────┼─────────────┐
         │             │             │
    ┌────▼───┐    ┌───▼────┐   ┌───▼────┐
    │ Region │    │ Region │   │ Region │
    │  US    │    │  EU    │   │  APAC  │
    └────┬───┘    └───┬────┘   └───┬────┘
         │            │            │
    Collectors   Collectors   Collectors
```

**优点**:

- 统一管理视图
- 配置一致性强
- 成本效率高

**缺点**:

- 单点故障风险
- 跨区域延迟
- 扩展性限制

#### 2.1.2 分层架构

```text
┌──────────────────────────────────────┐
│      Global OpAMP Control Plane      │
└────────────────┬─────────────────────┘
                 │
     ┌───────────┼───────────┐
     │           │           │
┌────▼────┐ ┌───▼────┐ ┌────▼────┐
│Regional │ │Regional│ │Regional │
│OpAMP US │ │OpAMP EU│ │OpAMP AP │
└────┬────┘ └───┬────┘ └────┬────┘
     │          │           │
Collectors  Collectors  Collectors
```

**优点**:

- 就近接入,低延迟
- 区域故障隔离
- 良好扩展性

**缺点**:

- 复杂度更高
- 运维成本增加
- 配置同步挑战

#### 2.1.3 混合架构(推荐)

```text
┌────────────────────────────────────────┐
│    Global OpAMP Control Plane          │
│    (配置管理、策略制定)                  │
└────────────────┬───────────────────────┘
                 │
     ┌───────────┼──────────┐
     │           │          │
┌────▼─────┐ ┌──▼──────┐ ┌─▼────────┐
│Regional  │ │Regional │ │Regional  │
│OpAMP Srv │ │OpAMP Srv│ │OpAMP Srv │
│+ 缓存    │ │+ 缓存   │ │+ 缓存    │
└────┬─────┘ └──┬──────┘ └─┬────────┘
     │          │          │
 Edge Agents  Edge Agents  Edge Agents
```

### 2.2 高可用设计

#### 2.2.1 服务器高可用

```yaml
# Kubernetes部署示例
apiVersion: apps/v1
kind: Deployment
metadata:
  name: opamp-server
spec:
  replicas: 3  # 多副本
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 1
      maxSurge: 1

  selector:
    matchLabels:
      app: opamp-server

  template:
    metadata:
      labels:
        app: opamp-server
    spec:
      affinity:
        # Pod反亲和性,分散到不同节点
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
            - labelSelector:
                matchExpressions:
                  - key: app
                    operator: In
                    values:
                      - opamp-server
              topologyKey: kubernetes.io/hostname

      containers:
        - name: opamp-server
          image: opamp-server:v1.0.0
          ports:
            - containerPort: 4320
              name: opamp-ws
            - containerPort: 4321
              name: opamp-http

          livenessProbe:
            httpGet:
              path: /health
              port: 4321
            initialDelaySeconds: 10
            periodSeconds: 10

          readinessProbe:
            httpGet:
              path: /ready
              port: 4321
            initialDelaySeconds: 5
            periodSeconds: 5

          resources:
            requests:
              cpu: "500m"
              memory: "512Mi"
            limits:
              cpu: "2000m"
              memory: "2Gi"

---
apiVersion: v1
kind: Service
metadata:
  name: opamp-server
spec:
  type: LoadBalancer
  selector:
    app: opamp-server
  ports:
    - name: opamp-ws
      port: 4320
      targetPort: 4320
    - name: opamp-http
      port: 4321
      targetPort: 4321
```

#### 2.2.2 数据持久化

```yaml
# PostgreSQL状态存储
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: opamp-db-pvc
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 100Gi
  storageClassName: fast-ssd

---
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: opamp-postgres
spec:
  serviceName: opamp-postgres
  replicas: 3  # 主从复制
  selector:
    matchLabels:
      app: opamp-postgres

  template:
    metadata:
      labels:
        app: opamp-postgres
    spec:
      containers:
        - name: postgres
          image: postgres:15
          env:
            - name: POSTGRES_DB
              value: opamp
            - name: POSTGRES_USER
              valueFrom:
                secretKeyRef:
                  name: opamp-db-secret
                  key: username
            - name: POSTGRES_PASSWORD
              valueFrom:
                secretKeyRef:
                  name: opamp-db-secret
                  key: password

          volumeMounts:
            - name: data
              mountPath: /var/lib/postgresql/data

  volumeClaimTemplates:
    - metadata:
        name: data
      spec:
        accessModes: ["ReadWriteOnce"]
        resources:
          requests:
            storage: 100Gi
```

---

## 第三部分：部署方案

### 3.1 Docker部署

#### 3.1.1 OpAMP Server

```dockerfile
# Dockerfile
FROM golang:1.21 AS builder
WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download
COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -o opamp-server ./cmd/server

FROM alpine:3.18
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/opamp-server .
COPY config.yaml .
EXPOSE 4320 4321
CMD ["./opamp-server", "--config", "config.yaml"]
```

```yaml
# config.yaml
server:
  # WebSocket端点
  websocket:
    endpoint: 0.0.0.0:4320
    max_connections: 10000

  # HTTP端点
  http:
    endpoint: 0.0.0.0:4321

  # TLS配置
  tls:
    enabled: true
    cert_file: /certs/server.crt
    key_file: /certs/server.key
    client_ca_file: /certs/ca.crt  # mTLS

# 数据库
database:
  type: postgres
  connection_string: "postgres://user:pass@postgres:5432/opamp?sslmode=require"

# 存储
storage:
  # 配置存储
  config:
    type: s3
    bucket: opamp-configs
    region: us-east-1

  # 包存储
  packages:
    type: s3
    bucket: opamp-packages
    region: us-east-1

# 认证
auth:
  type: jwt
  secret_key_file: /secrets/jwt-key

# 策略
policies:
  # 配置更新策略
  config_update:
    approval_required: true
    rollback_on_error: true

  # 包更新策略
  package_update:
    approval_required: true
    canary_percentage: 5
    canary_duration: 1h

# 监控
telemetry:
  metrics:
    endpoint: 0.0.0.0:8888
  traces:
    endpoint: jaeger:4318
  logs:
    level: info
```

```bash
# 启动命令
docker run -d \
  --name opamp-server \
  -p 4320:4320 \
  -p 4321:4321 \
  -p 8888:8888 \
  -v $(pwd)/config.yaml:/root/config.yaml:ro \
  -v $(pwd)/certs:/certs:ro \
  -v $(pwd)/secrets:/secrets:ro \
  opamp-server:v1.0.0
```

#### 3.1.2 OpAMP Agent(Collector集成)

```yaml
# otel-collector-config.yaml
extensions:
  # OpAMP扩展
  opamp:
    server:
      ws:
        endpoint: wss://opamp-server:4320/v1/opamp
        headers:
          Authorization: Bearer ${OPAMP_AUTH_TOKEN}
        tls:
          insecure: false
          ca_file: /certs/ca.crt
          cert_file: /certs/client.crt
          key_file: /certs/client.key

    # Agent标识
    instance_uid: ${INSTANCE_UID}

    # 能力声明
    capabilities:
      - ReportsEffectiveConfig
      - AcceptsRemoteConfig
      - ReportsHealth
      - ReportsRemoteConfig
      - AcceptsPackages
      - ReportsPackageStatuses

    # 本地配置(初始)
    own_telemetry:
      logs_endpoint: ${OPAMP_LOGS_ENDPOINT}
      metrics_endpoint: ${OPAMP_METRICS_ENDPOINT}

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false

service:
  extensions: [opamp]

  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]

    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]

    logs:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

```bash
# 启动Collector with OpAMP
docker run -d \
  --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  -e OPAMP_AUTH_TOKEN=$(cat /secrets/token) \
  -e INSTANCE_UID=$(uuidgen) \
  -e OPAMP_LOGS_ENDPOINT=http://opamp-server:4321/logs \
  -e OPAMP_METRICS_ENDPOINT=http://opamp-server:4321/metrics \
  -v $(pwd)/otel-collector-config.yaml:/etc/otelcol/config.yaml:ro \
  -v $(pwd)/certs:/certs:ro \
  otel/opentelemetry-collector-contrib:0.89.0 \
  --config=/etc/otelcol/config.yaml
```

### 3.2 Kubernetes部署

#### 3.2.1 完整部署清单

```yaml
# opamp-namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: opamp-system

---
# opamp-secrets.yaml
apiVersion: v1
kind: Secret
metadata:
  name: opamp-tls
  namespace: opamp-system
type: kubernetes.io/tls
data:
  tls.crt: <base64-encoded-cert>
  tls.key: <base64-encoded-key>
  ca.crt: <base64-encoded-ca>

---
apiVersion: v1
kind: Secret
metadata:
  name: opamp-db
  namespace: opamp-system
type: Opaque
data:
  username: <base64-encoded-user>
  password: <base64-encoded-pass>

---
# opamp-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: opamp-server-config
  namespace: opamp-system
data:
  config.yaml: |
    # (完整的server配置,同上)

---
# opamp-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: opamp-server
  namespace: opamp-system
spec:
  replicas: 3
  selector:
    matchLabels:
      app: opamp-server
  template:
    metadata:
      labels:
        app: opamp-server
    spec:
      containers:
        - name: opamp-server
          image: opamp-server:v1.0.0
          ports:
            - containerPort: 4320
              name: ws
            - containerPort: 4321
              name: http
            - containerPort: 8888
              name: metrics

          env:
            - name: DB_USER
              valueFrom:
                secretKeyRef:
                  name: opamp-db
                  key: username
            - name: DB_PASSWORD
              valueFrom:
                secretKeyRef:
                  name: opamp-db
                  key: password

          volumeMounts:
            - name: config
              mountPath: /etc/opamp
            - name: tls
              mountPath: /certs

          livenessProbe:
            httpGet:
              path: /health
              port: 4321
            initialDelaySeconds: 10
            periodSeconds: 10

          readinessProbe:
            httpGet:
              path: /ready
              port: 4321
            initialDelaySeconds: 5
            periodSeconds: 5

          resources:
            requests:
              cpu: 500m
              memory: 512Mi
            limits:
              cpu: 2000m
              memory: 2Gi

      volumes:
        - name: config
          configMap:
            name: opamp-server-config
        - name: tls
          secret:
            secretName: opamp-tls

---
# opamp-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: opamp-server
  namespace: opamp-system
spec:
  type: LoadBalancer
  selector:
    app: opamp-server
  ports:
    - name: ws
      port: 4320
      targetPort: 4320
    - name: http
      port: 4321
      targetPort: 4321

---
# opamp-servicemonitor.yaml (Prometheus监控)
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: opamp-server
  namespace: opamp-system
spec:
  selector:
    matchLabels:
      app: opamp-server
  endpoints:
    - port: metrics
      interval: 30s
```

#### 3.2.2 Collector DaemonSet部署

```yaml
# otel-collector-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: opamp-system
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
          image: otel/opentelemetry-collector-contrib:0.89.0

          env:
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
            - name: INSTANCE_UID
              value: "$(NODE_NAME)-$(POD_NAME)"
            - name: OPAMP_AUTH_TOKEN
              valueFrom:
                secretKeyRef:
                  name: opamp-token
                  key: token

          ports:
            - containerPort: 4317
              hostPort: 4317
              name: otlp-grpc
            - containerPort: 4318
              hostPort: 4318
              name: otlp-http

          volumeMounts:
            - name: config
              mountPath: /etc/otelcol
            - name: tls
              mountPath: /certs

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
        - name: tls
          secret:
            secretName: opamp-tls

---
# RBAC
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: opamp-system

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
    namespace: opamp-system
```

---

## 第四部分：配置管理

### 4.1 配置下发流程

```text
1. 管理员在控制台创建/修改配置
         │
         ▼
2. 配置存储到数据库/对象存储
         │
         ▼
3. OpAMP Server生成RemoteConfig消息
         │
         ▼
4. 通过WebSocket推送给Agent
         │
         ▼
5. Agent接收并验证配置
         │
         ├──── 验证失败 ──► 返回错误,使用旧配置
         │
         ▼
6. Agent应用新配置,重启Collector
         │
         ▼
7. Agent报告EffectiveConfig
         │
         ▼
8. Server确认配置生效
```

### 4.2 配置模板管理

```yaml
# 配置模板示例
apiVersion: opamp.io/v1
kind: ConfigTemplate
metadata:
  name: standard-collector
  version: v1.0.0
spec:
  # 变量定义
  variables:
    - name: environment
      type: string
      required: true
      enum: [dev, staging, prod]

    - name: backend_endpoint
      type: string
      required: true

    - name: sampling_rate
      type: float
      default: 0.1
      min: 0.01
      max: 1.0

  # 配置内容
  config:
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317

    processors:
      # 环境标签
      attributes:
        actions:
          - key: deployment.environment
            value: "{{.environment}}"
            action: upsert

      # 采样
      probabilistic_sampler:
        sampling_percentage: "{{.sampling_rate}}"

      batch:
        timeout: 1s

    exporters:
      otlp:
        endpoint: "{{.backend_endpoint}}"
        tls:
          insecure: false

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [attributes, probabilistic_sampler, batch]
          exporters: [otlp]
```

### 4.3 灰度发布策略

```yaml
# 灰度发布配置
apiVersion: opamp.io/v1
kind: RolloutStrategy
metadata:
  name: config-update-canary
spec:
  # 阶段定义
  stages:
    - name: canary
      percentage: 5
      duration: 30m
      success_criteria:
        error_rate_threshold: 0.01
        health_check_pass_rate: 0.99

    - name: pilot
      percentage: 20
      duration: 1h
      success_criteria:
        error_rate_threshold: 0.01
        health_check_pass_rate: 0.99

    - name: rollout
      percentage: 100
      duration: 2h
      success_criteria:
        error_rate_threshold: 0.01
        health_check_pass_rate: 0.99

  # 失败策略
  failure_policy:
    action: rollback
    notification:
      - slack
      - email

  # 目标选择
  target_selector:
    # 按标签选择
    labels:
      region: us-east-1
      tier: production

    # 按Agent ID选择
    agent_ids:
      - agent-001
      - agent-002
```

---

## 第五部分：安全与认证

### 5.1 TLS/mTLS配置

#### 5.1.1 生成证书

```bash
# 生成CA
openssl req -x509 -newkey rsa:4096 -days 365 -nodes \
  -keyout ca.key -out ca.crt \
  -subj "/CN=OpAMP CA"

# 生成服务器证书
openssl req -newkey rsa:4096 -nodes \
  -keyout server.key -out server.csr \
  -subj "/CN=opamp-server.example.com"

openssl x509 -req -in server.csr -CA ca.crt -CAkey ca.key \
  -CAcreateserial -out server.crt -days 365

# 生成客户端证书
openssl req -newkey rsa:4096 -nodes \
  -keyout client.key -out client.csr \
  -subj "/CN=opamp-agent-001"

openssl x509 -req -in client.csr -CA ca.crt -CAkey ca.key \
  -CAcreateserial -out client.crt -days 365
```

#### 5.1.2 证书轮换

```yaml
# 自动证书轮换配置
certificate_rotation:
  enabled: true

  # 轮换策略
  strategy:
    # 提前轮换时间
    rotation_before_expiry: 720h  # 30天

    # 检查间隔
    check_interval: 24h

  # 证书来源
  provider:
    type: cert-manager  # 或 vault, aws-acm

    # cert-manager配置
    cert_manager:
      issuer: letsencrypt-prod
      dns_names:
        - opamp-server.example.com

  # 轮换通知
  notifications:
    - type: slack
      webhook_url: https://hooks.slack.com/...
    - type: email
      recipients:
        - ops@example.com
```

### 5.2 认证机制

#### 5.2.1 JWT认证

```yaml
# OpAMP Server配置
auth:
  type: jwt
  jwt:
    # 签名密钥
    secret_key_file: /secrets/jwt-key

    # JWT参数
    issuer: opamp-server.example.com
    audience: opamp-agents
    expiration: 24h

    # 刷新策略
    refresh_enabled: true
    refresh_before_expiry: 1h

    # Claims要求
    required_claims:
      - sub  # Agent ID
      - exp  # 过期时间
      - iat  # 签发时间
```

```go
// Agent端JWT使用
package main

import (
    "context"
    "crypto/tls"
    "time"

    "github.com/golang-jwt/jwt/v5"
    "go.opentelemetry.io/collector/extension/opamp"
)

func createOpAMPClient() *opamp.Client {
    // 生成JWT token
    token := jwt.NewWithClaims(jwt.SigningMethodHS256, jwt.MapClaims{
        "sub": "agent-001",
        "iat": time.Now().Unix(),
        "exp": time.Now().Add(24 * time.Hour).Unix(),
        "iss": "opamp-server.example.com",
        "aud": "opamp-agents",
    })

    tokenString, _ := token.SignedString([]byte("secret-key"))

    // 配置客户端
    cfg := opamp.ClientConfig{
        ServerURL: "wss://opamp-server.example.com:4320/v1/opamp",

        // 认证头
        Headers: map[string]string{
            "Authorization": "Bearer " + tokenString,
        },

        // TLS配置
        TLSConfig: &tls.Config{
            InsecureSkipVerify: false,
            MinVersion:         tls.VersionTLS13,
        },

        InstanceUID: "agent-001",
    }

    client := opamp.NewClient(cfg)
    return client
}
```

#### 5.2.2 API Key认证

```yaml
# 简化认证方式
auth:
  type: api_key
  api_key:
    # Key存储
    storage: redis
    redis:
      endpoint: redis:6379
      db: 0

    # Key格式
    prefix: opamp_
    length: 32

    # 过期策略
    expiration: 90d
    rotation_warning: 30d
```

---

## 第六部分：监控与运维

### 6.1 关键指标

#### 6.1.1 Server端指标

```yaml
# Prometheus指标
- opamp_server_connected_agents{region="us-east-1"}
  # 当前连接的Agent数量

- opamp_server_config_updates_total{status="success|failure"}
  # 配置更新总数

- opamp_server_config_update_duration_seconds
  # 配置更新延迟

- opamp_server_package_downloads_total
  # 包下载总数

- opamp_server_websocket_connections_total
  # WebSocket连接总数

- opamp_server_messages_received_total{type="AgentToServer"}
  # 接收消息总数

- opamp_server_messages_sent_total{type="ServerToAgent"}
  # 发送消息总数

- opamp_server_health_check_failures_total{agent_id="xxx"}
  # 健康检查失败次数
```

#### 6.1.2 Agent端指标

```yaml
- opamp_agent_connection_status{server="xxx"}
  # 连接状态 (1=connected, 0=disconnected)

- opamp_agent_config_updates_total{status="success|failure"}
  # 配置更新总数

- opamp_agent_effective_config_hash
  # 当前配置哈希

- opamp_agent_last_heartbeat_timestamp_seconds
  # 最后心跳时间

- opamp_agent_package_install_duration_seconds
  # 包安装耗时
```

### 6.2 告警规则

```yaml
# Prometheus告警规则
groups:
  - name: opamp_server
    interval: 30s
    rules:
      # Agent大量断连
      - alert: OpAMPAgentDisconnected
        expr: |
          rate(opamp_server_connected_agents[5m]) <
          0.95 * rate(opamp_server_connected_agents[1h] offset 1h)
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "大量Agent断连"
          description: "过去5分钟Agent断连超过5%"

      # 配置更新失败率高
      - alert: OpAMPConfigUpdateFailureHigh
        expr: |
          rate(opamp_server_config_updates_total{status="failure"}[5m]) /
          rate(opamp_server_config_updates_total[5m]) > 0.05
        for: 10m
        labels:
          severity: critical
        annotations:
          summary: "配置更新失败率过高"
          description: "配置更新失败率 > 5%"

      # 配置更新延迟高
      - alert: OpAMPConfigUpdateLatencyHigh
        expr: |
          histogram_quantile(0.95,
            rate(opamp_server_config_update_duration_seconds_bucket[5m])
          ) > 5
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "配置更新延迟过高"
          description: "P95延迟 > 5秒"
```

### 6.3 日志示例

```json
// Server日志
{
  "timestamp": "2025-10-17T10:00:00Z",
  "level": "INFO",
  "component": "opamp-server",
  "event": "agent_connected",
  "agent_id": "agent-001",
  "agent_version": "0.89.0",
  "remote_addr": "10.0.1.100:52345",
  "duration_ms": 123
}

{
  "timestamp": "2025-10-17T10:00:05Z",
  "level": "INFO",
  "component": "opamp-server",
  "event": "config_updated",
  "agent_id": "agent-001",
  "config_version": "v2.1.0",
  "config_hash": "abc123...",
  "duration_ms": 456
}

{
  "timestamp": "2025-10-17T10:00:10Z",
  "level": "ERROR",
  "component": "opamp-server",
  "event": "config_update_failed",
  "agent_id": "agent-002",
  "error": "validation failed: invalid receiver config",
  "config_version": "v2.1.0"
}

// Agent日志
{
  "timestamp": "2025-10-17T10:00:00Z",
  "level": "INFO",
  "component": "opamp-agent",
  "event": "connected_to_server",
  "server_url": "wss://opamp-server:4320/v1/opamp",
  "instance_uid": "agent-001"
}

{
  "timestamp": "2025-10-17T10:00:05Z",
  "level": "INFO",
  "component": "opamp-agent",
  "event": "config_received",
  "config_hash": "abc123...",
  "config_size_bytes": 4096
}

{
  "timestamp": "2025-10-17T10:00:06Z",
  "level": "INFO",
  "component": "opamp-agent",
  "event": "collector_restarted",
  "duration_ms": 1234
}
```

---

## 第七部分：故障排查

### 7.1 常见问题

#### 7.1.1 连接问题

```bash
# 检查网络连通性
telnet opamp-server 4320

# 检查TLS证书
openssl s_client -connect opamp-server:4320 -showcerts

# 检查DNS解析
nslookup opamp-server

# 检查防火墙
iptables -L -n | grep 4320
```

#### 7.1.2 认证问题

```bash
# 验证JWT token
curl -H "Authorization: Bearer $TOKEN" \
  https://opamp-server:4321/api/v1/agents

# 检查证书有效期
openssl x509 -in client.crt -noout -dates

# 查看Agent日志
kubectl logs -n opamp-system otel-collector-xxx | grep auth
```

### 7.2 调试工具

```bash
# 启用详细日志
# Server
./opamp-server --config config.yaml --log-level debug

# Agent (Collector)
otelcol --config config.yaml --set service.telemetry.logs.level=debug

# 抓包分析WebSocket流量
tcpdump -i any -w opamp.pcap port 4320
wireshark opamp.pcap

# 监控连接状态
watch -n 1 'curl -s http://opamp-server:4321/metrics | grep opamp_server_connected_agents'
```

---

## 第八部分：最佳实践

### 8.1 部署检查清单

```yaml
部署前检查:
□ 网络连通性测试
□ TLS证书准备和验证
□ 认证机制配置
□ 数据库初始化
□ 存储桶创建(S3/GCS)
□ 监控和告警配置
□ 备份和恢复测试

部署后验证:
□ Agent连接成功
□ 配置下发功能
□ 健康检查正常
□ 监控指标正常
□ 日志输出正常
□ 灰度发布测试
□ 故障恢复测试
□ 性能压测
```

### 8.2 性能优化

```yaml
# Server优化
server:
  # 连接池大小
  max_connections: 10000

  # 消息批处理
  batching:
    enabled: true
    max_batch_size: 100
    timeout: 1s

  # 压缩
  compression:
    enabled: true
    algorithm: gzip

  # 缓存
  caching:
    config_cache_ttl: 5m
    agent_status_cache_ttl: 30s

# 数据库优化
database:
  # 连接池
  max_open_conns: 100
  max_idle_conns: 10
  conn_max_lifetime: 1h

  # 索引
  indexes:
    - agent_id
    - config_version
    - timestamp

# Agent优化
extensions:
  opamp:
    # 心跳间隔
    heartbeat_interval: 30s

    # 重连策略
    retry:
      initial_interval: 1s
      max_interval: 30s
      max_elapsed_time: 5m
```

### 8.3 安全加固

```yaml
安全措施:
□ 启用mTLS
□ 使用强JWT密钥
□ 定期轮换证书
□ 限制API访问(IP白名单)
□ 审计日志记录
□ 加密敏感配置
□ 最小权限原则(RBAC)
□ 定期安全扫描
□ 漏洞修复流程
□ 应急响应预案
```

---

## 📚 参考资源

- [OpAMP规范](https://github.com/open-telemetry/opamp-spec)
- [OpAMP Go实现](https://github.com/open-telemetry/opamp-go)
- [Collector OpAMP扩展](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/extension/opampextension)

---

**完整的OpAMP部署指南!** 🎓
