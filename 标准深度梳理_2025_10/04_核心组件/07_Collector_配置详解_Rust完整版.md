# OpenTelemetry Collector 配置详解 - Rust 完整版

## 目录

- [OpenTelemetry Collector 配置详解 - Rust 完整版](#opentelemetry-collector-配置详解---rust-完整版)
  - [目录](#目录)
  - [1. Collector 概述](#1-collector-概述)
    - [1.1 架构](#11-架构)
    - [1.2 使用场景](#12-使用场景)
  - [2. Receivers (接收器)](#2-receivers-接收器)
    - [2.1 OTLP Receiver](#21-otlp-receiver)
    - [2.2 Jaeger Receiver](#22-jaeger-receiver)
    - [2.3 Prometheus Receiver](#23-prometheus-receiver)
  - [3. Processors (处理器)](#3-processors-处理器)
    - [3.1 Batch Processor](#31-batch-processor)
    - [3.2 Memory Limiter](#32-memory-limiter)
    - [3.3 Resource Processor](#33-resource-processor)
    - [3.4 Attributes Processor](#34-attributes-processor)
  - [4. Exporters (导出器)](#4-exporters-导出器)
    - [4.1 OTLP Exporter](#41-otlp-exporter)
    - [4.2 Jaeger Exporter](#42-jaeger-exporter)
    - [4.3 Prometheus Exporter](#43-prometheus-exporter)
    - [4.4 Logging Exporter](#44-logging-exporter)
  - [5. Pipelines (管道)](#5-pipelines-管道)
    - [5.1 Traces Pipeline](#51-traces-pipeline)
    - [5.2 Metrics Pipeline](#52-metrics-pipeline)
    - [5.3 Logs Pipeline](#53-logs-pipeline)
  - [6. 扩展功能](#6-扩展功能)
    - [6.1 Health Check](#61-health-check)
    - [6.2 pprof](#62-pprof)
    - [6.3 zpages](#63-zpages)
  - [7. 完整配置示例](#7-完整配置示例)
    - [7.1 基础配置](#71-基础配置)
    - [7.2 生产环境配置](#72-生产环境配置)
  - [8. 部署模式](#8-部署模式)
    - [8.1 Agent 模式](#81-agent-模式)
    - [8.2 Gateway 模式](#82-gateway-模式)
    - [8.3 混合模式](#83-混合模式)
  - [9. Kubernetes 部署](#9-kubernetes-部署)
    - [9.1 DaemonSet (Agent)](#91-daemonset-agent)
    - [9.2 Deployment (Gateway)](#92-deployment-gateway)
  - [10. 性能优化](#10-性能优化)
    - [10.1 批处理配置](#101-批处理配置)
    - [10.2 并发控制](#102-并发控制)
    - [10.3 内存优化](#103-内存优化)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [组件对比](#组件对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Collector 概述

### 1.1 架构

````text
OpenTelemetry Collector 架构:

┌─────────────┐
│ Application │
└──────┬──────┘
       │ OTLP
       ▼
┌─────────────────────────────────────┐
│   OpenTelemetry Collector           │
│                                     │
│  ┌──────────┐   ┌──────────┐        │
│  │Receivers │──>│Processors│──┐     │
│  └──────────┘   └──────────┘  │     │
│                               ▼     │
│                        ┌──────────┐ │
│                        │Exporters │ │
│                        └──────────┘ │
└─────────────────────────────────────┘
       │            │            │
       ▼            ▼            ▼
   Jaeger      Prometheus   Logging

核心组件:
1. Receivers: 接收遥测数据 (OTLP, Jaeger, Prometheus)
2. Processors: 处理数据 (批处理, 过滤, 采样)
3. Exporters: 导出数据 (Jaeger, Prometheus, 日志)
4. Extensions: 扩展功能 (健康检查, pprof, zpages)
5. Pipelines: 数据流水线 (traces, metrics, logs)
````

### 1.2 使用场景

````text
Collector 使用场景:

1. 数据聚合
   - 从多个应用收集遥测数据
   - 统一导出到后端

2. 协议转换
   - Jaeger → OTLP
   - Prometheus → OTLP
   - OTLP → Jaeger/Prometheus

3. 数据处理
   - 批处理优化
   - 采样控制
   - 数据过滤

4. 负载均衡
   - 分布式部署
   - 流量分发

5. 多后端导出
   - 同时导出到 Jaeger + Prometheus
   - 数据备份
````

---

## 2. Receivers (接收器)

### 2.1 OTLP Receiver

````yaml
# config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - "http://localhost:*"
            - "https://*.example.com"
````

**Rust 客户端配置**:

````rust
use opentelemetry_otlp::WithExportConfig;

let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://collector:4317")
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
````

### 2.2 Jaeger Receiver

````yaml
receivers:
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
      thrift_compact:
        endpoint: 0.0.0.0:6831
      thrift_binary:
        endpoint: 0.0.0.0:6832
````

### 2.3 Prometheus Receiver

````yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'my-app'
          scrape_interval: 15s
          static_configs:
            - targets: ['app:9090']
````

---

## 3. Processors (处理器)

### 3.1 Batch Processor

````yaml
processors:
  batch:
    # 批处理超时 (默认: 200ms)
    timeout: 200ms
    
    # 批次大小 (默认: 8192)
    send_batch_size: 8192
    
    # 最大批次大小
    send_batch_max_size: 10000
````

**作用**: 批量发送数据，减少网络开销

### 3.2 Memory Limiter

````yaml
processors:
  memory_limiter:
    # 检查间隔
    check_interval: 1s
    
    # 内存软限制 (80%)
    limit_mib: 512
    
    # 内存硬限制 (90%)
    spike_limit_mib: 128
````

**作用**: 防止内存溢出，超过限制时拒绝新数据

### 3.3 Resource Processor

````yaml
processors:
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: insert
      - key: service.version
        value: 1.2.3
        action: upsert
      - key: internal.key
        action: delete
````

**作用**: 添加、修改、删除 Resource 属性

### 3.4 Attributes Processor

````yaml
processors:
  attributes:
    actions:
      # 插入属性
      - key: team
        value: backend
        action: insert
      
      # 更新属性
      - key: region
        value: us-west-2
        action: update
      
      # 删除属性
      - key: password
        action: delete
      
      # 从其他属性提取
      - key: user_type
        from_attribute: http.user_agent
        pattern: ^(mobile|desktop).*
        action: extract
      
      # Hash 敏感信息
      - key: user_id
        action: hash
````

**作用**: 处理 Span/Metric 属性

---

## 4. Exporters (导出器)

### 4.1 OTLP Exporter

````yaml
exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      cert_file: /etc/certs/cert.pem
      key_file: /etc/certs/key.pem
    headers:
      api-key: "your-api-key"
    compression: gzip
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
````

### 4.2 Jaeger Exporter

````yaml
exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
````

### 4.3 Prometheus Exporter

````yaml
exporters:
  prometheus:
    endpoint: 0.0.0.0:8889
    namespace: my_app
    const_labels:
      environment: production
````

### 4.4 Logging Exporter

````yaml
exporters:
  logging:
    loglevel: debug
    sampling_initial: 5
    sampling_thereafter: 200
````

**作用**: 调试用，输出到控制台

---

## 5. Pipelines (管道)

### 5.1 Traces Pipeline

````yaml
service:
  pipelines:
    traces:
      receivers: [otlp, jaeger]
      processors: [memory_limiter, batch, attributes]
      exporters: [otlp, jaeger, logging]
````

### 5.2 Metrics Pipeline

````yaml
service:
  pipelines:
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, batch, resource]
      exporters: [otlp, prometheus]
````

### 5.3 Logs Pipeline

````yaml
service:
  pipelines:
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch, attributes]
      exporters: [otlp, logging]
````

---

## 6. 扩展功能

### 6.1 Health Check

````yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
````

**检查健康状态**:

````bash
curl http://localhost:13133/health
````

### 6.2 pprof

````yaml
extensions:
  pprof:
    endpoint: 0.0.0.0:1777
````

**性能分析**:

````bash
go tool pprof http://localhost:1777/debug/pprof/heap
````

### 6.3 zpages

````yaml
extensions:
  zpages:
    endpoint: 0.0.0.0:55679
````

**查看内部状态**:

````bash
# 浏览器访问
http://localhost:55679/debug/tracez
http://localhost:55679/debug/pipelinez
````

---

## 7. 完整配置示例

### 7.1 基础配置

````yaml
# config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 200ms
    send_batch_size: 1024
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: true
  
  logging:
    loglevel: debug

extensions:
  health_check:
    endpoint: 0.0.0.0:13133

service:
  extensions: [health_check]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp, logging]
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp]
````

### 7.2 生产环境配置

````yaml
# production-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 32
        max_concurrent_streams: 100
        read_buffer_size: 524288
        write_buffer_size: 524288
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - "https://*.example.com"

processors:
  # 内存限制 (优先级最高)
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
  
  # Resource 处理
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: insert
      - key: cluster.name
        value: prod-cluster-1
        action: insert
  
  # 属性处理
  attributes:
    actions:
      # 删除敏感信息
      - key: password
        action: delete
      - key: token
        action: delete
      
      # Hash 用户 ID
      - key: user_id
        action: hash
  
  # 批处理 (优先级最低)
  batch:
    timeout: 200ms
    send_batch_size: 8192
    send_batch_max_size: 10000

exporters:
  # 主后端
  otlp/primary:
    endpoint: backend-primary:4317
    tls:
      insecure: false
      cert_file: /etc/certs/cert.pem
      key_file: /etc/certs/key.pem
    compression: gzip
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
  
  # 备份后端
  otlp/backup:
    endpoint: backend-backup:4317
    tls:
      insecure: true
    timeout: 10s
  
  # Prometheus
  prometheus:
    endpoint: 0.0.0.0:8889
    namespace: my_app
    const_labels:
      environment: production
      cluster: prod-cluster-1
  
  # Jaeger
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  
  pprof:
    endpoint: 0.0.0.0:1777
  
  zpages:
    endpoint: 0.0.0.0:55679

service:
  extensions: [health_check, pprof, zpages]
  
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, attributes, batch]
      exporters: [otlp/primary, otlp/backup, jaeger]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [otlp/primary, prometheus]
    
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, attributes, batch]
      exporters: [otlp/primary]
  
  # 遥测配置
  telemetry:
    logs:
      level: info
    metrics:
      level: detailed
      address: 0.0.0.0:8888
````

---

## 8. 部署模式

### 8.1 Agent 模式

````text
Agent 模式 (每个节点一个 Collector):

┌──────────┐
│  App 1   │──┐
└──────────┘  │
              ├──> Collector Agent ──> Backend
┌──────────┐  │
│  App 2   │──┘
└──────────┘

优点:
- 低延迟
- 应用侧零配置
- 本地数据缓冲

缺点:
- 资源占用高
- 配置管理复杂
````

**Docker Compose**:

````yaml
version: '3.8'

services:
  app:
    image: my-app:latest
    environment:
      OTEL_EXPORTER_OTLP_ENDPOINT: http://collector-agent:4317
  
  collector-agent:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/collector-config.yaml"]
    volumes:
      - ./agent-config.yaml:/etc/collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
````

### 8.2 Gateway 模式

````text
Gateway 模式 (集中式 Collector):

┌──────────┐
│  App 1   │──┐
└──────────┘  │
              │
┌──────────┐  ├──> Collector Gateway ──> Backend
│  App 2   │──┤
└──────────┘  │
              │
┌──────────┐  │
│  App 3   │──┘
└──────────┘

优点:
- 统一配置
- 资源共享
- 负载均衡

缺点:
- 单点故障
- 网络延迟
````

**Kubernetes Service**:

````yaml
apiVersion: v1
kind: Service
metadata:
  name: collector-gateway
spec:
  type: ClusterIP
  ports:
    - name: otlp-grpc
      port: 4317
      targetPort: 4317
    - name: otlp-http
      port: 4318
      targetPort: 4318
  selector:
    app: collector-gateway
````

### 8.3 混合模式

````text
混合模式 (Agent + Gateway):

┌──────────┐
│  App 1   │──> Agent 1 ──┐
└──────────┘               │
                           ├──> Gateway ──> Backend
┌──────────┐               │
│  App 2   │──> Agent 2 ──┘
└──────────┘

优点:
- 低延迟 + 统一配置
- 高可用性
- 灵活扩展

缺点:
- 架构复杂
- 运维成本高
````

---

## 9. Kubernetes 部署

### 9.1 DaemonSet (Agent)

````yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: collector-agent
  namespace: monitoring
spec:
  selector:
    matchLabels:
      app: collector-agent
  template:
    metadata:
      labels:
        app: collector-agent
    spec:
      containers:
        - name: collector
          image: otel/opentelemetry-collector:latest
          command:
            - "/otelcol"
            - "--config=/conf/config.yaml"
          ports:
            - containerPort: 4317
              name: otlp-grpc
            - containerPort: 4318
              name: otlp-http
            - containerPort: 13133
              name: health-check
          volumeMounts:
            - name: config
              mountPath: /conf
          resources:
            requests:
              memory: "256Mi"
              cpu: "100m"
            limits:
              memory: "512Mi"
              cpu: "500m"
          livenessProbe:
            httpGet:
              path: /
              port: 13133
            initialDelaySeconds: 10
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /
              port: 13133
            initialDelaySeconds: 5
            periodSeconds: 5
      volumes:
        - name: config
          configMap:
            name: collector-agent-config
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: collector-agent-config
  namespace: monitoring
data:
  config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
    
    processors:
      batch:
        timeout: 200ms
        send_batch_size: 1024
      memory_limiter:
        check_interval: 1s
        limit_mib: 256
    
    exporters:
      otlp:
        endpoint: collector-gateway.monitoring.svc.cluster.local:4317
        tls:
          insecure: true
    
    extensions:
      health_check:
        endpoint: 0.0.0.0:13133
    
    service:
      extensions: [health_check]
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, batch]
          exporters: [otlp]
        metrics:
          receivers: [otlp]
          processors: [memory_limiter, batch]
          exporters: [otlp]
````

### 9.2 Deployment (Gateway)

````yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: collector-gateway
  namespace: monitoring
spec:
  replicas: 3
  selector:
    matchLabels:
      app: collector-gateway
  template:
    metadata:
      labels:
        app: collector-gateway
    spec:
      containers:
        - name: collector
          image: otel/opentelemetry-collector:latest
          command:
            - "/otelcol"
            - "--config=/conf/config.yaml"
          ports:
            - containerPort: 4317
              name: otlp-grpc
            - containerPort: 4318
              name: otlp-http
            - containerPort: 8889
              name: prometheus
            - containerPort: 13133
              name: health-check
          volumeMounts:
            - name: config
              mountPath: /conf
          resources:
            requests:
              memory: "1Gi"
              cpu: "500m"
            limits:
              memory: "2Gi"
              cpu: "2000m"
          livenessProbe:
            httpGet:
              path: /
              port: 13133
          readinessProbe:
            httpGet:
              path: /
              port: 13133
      volumes:
        - name: config
          configMap:
            name: collector-gateway-config
---
apiVersion: v1
kind: Service
metadata:
  name: collector-gateway
  namespace: monitoring
spec:
  type: ClusterIP
  ports:
    - name: otlp-grpc
      port: 4317
      targetPort: 4317
    - name: otlp-http
      port: 4318
      targetPort: 4318
    - name: prometheus
      port: 8889
      targetPort: 8889
  selector:
    app: collector-gateway
````

---

## 10. 性能优化

### 10.1 批处理配置

````yaml
processors:
  batch:
    # 平衡延迟和吞吐量
    timeout: 200ms          # 延迟优先: 100ms
    send_batch_size: 8192   # 吞吐量优先: 16384
    send_batch_max_size: 10000
````

### 10.2 并发控制

````yaml
exporters:
  otlp:
    endpoint: backend:4317
    sending_queue:
      enabled: true
      num_consumers: 10    # 并发数
      queue_size: 5000     # 队列大小
````

### 10.3 内存优化

````yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048        # 根据可用内存调整
    spike_limit_mib: 512   # 预留 spike 空间
````

---

## 总结

### 核心要点

1. **Receivers**: 接收遥测数据 (OTLP, Jaeger, Prometheus)
2. **Processors**: 处理数据 (批处理, 过滤, 采样)
3. **Exporters**: 导出数据 (OTLP, Jaeger, Prometheus)
4. **Pipelines**: 数据流水线 (traces, metrics, logs)
5. **Extensions**: 扩展功能 (健康检查, pprof)

### 组件对比

| 组件 | 作用 | 示例 |
|------|------|------|
| Receivers | 接收数据 | OTLP, Jaeger, Prometheus |
| Processors | 处理数据 | Batch, Memory Limiter, Attributes |
| Exporters | 导出数据 | OTLP, Jaeger, Prometheus, Logging |
| Extensions | 扩展功能 | Health Check, pprof, zpages |

### 最佳实践清单

- ✅ 使用 Agent + Gateway 混合模式
- ✅ 配置 Memory Limiter 防止 OOM
- ✅ 启用批处理优化性能
- ✅ 设置健康检查端点
- ✅ 配置多个 Exporter 备份
- ✅ 使用 TLS 加密传输
- ✅ 删除敏感信息 (password, token)
- ✅ Hash 高基数属性 (user_id)
- ✅ Kubernetes 部署使用 DaemonSet/Deployment
- ✅ 配置资源限制 (CPU/Memory)
- ✅ 启用重试机制
- ✅ 监控 Collector 自身指标
- ❌ 不要在 Collector 中做复杂计算
- ❌ 不要设置过大的批处理大小
- ❌ 不要忘记配置超时

---

**相关文档**:

- [OpenTelemetry Collector 完整版](./01_Collector_完整版.md)
- [Context 完整版](./03_Context_完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [Kubernetes 部署](../10_云平台/03_Kubernetes_集成.md)
