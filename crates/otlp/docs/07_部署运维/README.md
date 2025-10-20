# 部署运维指南

> **版本**: v2.0  
> **最后更新**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 概述

本目录包含OTLP Rust项目的部署和运维相关文档，涵盖容器化部署、Kubernetes集成、监控告警、故障排查等生产环境必需的内容。

**创建时间**: 2025年9月26日  
**维护者**: OTLP运维团队  

---

## 🚀 快速导航

### 核心运维文档

| 文档 | 说明 | 优先级 | 状态 |
|------|------|--------|------|
| [K8s/Istio/Envoy完整指南](../OTLP_K8S_ISTIO_ENVOY_GUIDE.md) | 生产级云原生部署方案 | ⭐⭐⭐⭐⭐ | ✅ 完整 |
| [故障排查和性能调优](../OTLP_RUST_故障排查和性能调优指南.md) | 问题诊断与解决 | ⭐⭐⭐⭐⭐ | ✅ 完整 |
| [安全配置最佳实践](../OTLP_RUST_安全配置和最佳实践指南.md) | 安全加固指南 | ⭐⭐⭐⭐⭐ | ✅ 完整 |
| [生产就绪检查清单](../PRODUCTION_CHECKLIST.md) | 上线前检查 | ⭐⭐⭐⭐⭐ | ✅ 完整 |

### Semantics运维文档（推荐）

| 文档 | 说明 | 优先级 |
|------|------|--------|
| [告警与仪表板配置](../../semantics/ALERTING_BASELINE.md) | Prometheus告警和Grafana仪表板 | ⭐⭐⭐⭐⭐ |
| [运维手册](../../semantics/RUNBOOK.md) | 标准化运维流程 | ⭐⭐⭐⭐⭐ |
| [自动伸缩策略](../../semantics/SCALING_STRATEGY.md) | HPA配置和容量规划 | ⭐⭐⭐⭐ |
| [OpAMP发布策略](../../semantics/OPAMP_ROLLOUT_STRATEGY.md) | 灰度发布和回滚 | ⭐⭐⭐⭐ |

---

## 🎯 部署场景

### 1. 容器化部署

#### Docker部署

**Dockerfile示例**:

```dockerfile
# 多阶段构建
FROM rust:1.90-alpine AS builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN apk add --no-cache musl-dev && \
    cargo build --release

FROM alpine:latest
RUN apk add --no-cache ca-certificates

COPY --from=builder /app/target/release/otlp /usr/local/bin/

EXPOSE 4317 4318
CMD ["otlp"]
```

**构建和运行**:

```bash
# 构建镜像
docker build -t otlp-rust:latest .

# 运行容器
docker run -d \
  --name otlp-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  -e OTLP_ENDPOINT=http://backend:4317 \
  otlp-rust:latest
```

#### Docker Compose部署

**docker-compose.yml**:

```yaml
version: '3.8'

services:
  otlp-collector:
    image: otlp-rust:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://jaeger:4317
    volumes:
      - ./config:/etc/otlp
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8888/health"]
      interval: 30s
      timeout: 10s
      retries: 3

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "4317:4317"
    environment:
      - COLLECTOR_OTLP_ENABLED=true

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
```

### 2. Kubernetes部署

#### 基础部署

**deployment.yaml**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-collector
  template:
    metadata:
      labels:
        app: otlp-collector
        version: v1
    spec:
      containers:
      - name: otlp-collector
        image: otlp-rust:latest
        ports:
        - containerPort: 4317
          name: grpc
        - containerPort: 4318
          name: http
        - containerPort: 8888
          name: metrics
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_ENDPOINT
          valueFrom:
            configMapKeyRef:
              name: otlp-config
              key: endpoint
        resources:
          requests:
            cpu: 500m
            memory: 1Gi
          limits:
            cpu: 2000m
            memory: 4Gi
        livenessProbe:
          httpGet:
            path: /health
            port: 8888
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8888
          initialDelaySeconds: 10
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-collector
  namespace: observability
spec:
  selector:
    app: otlp-collector
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
  - name: http
    port: 4318
    targetPort: 4318
  - name: metrics
    port: 8888
    targetPort: 8888
  type: ClusterIP
```

#### HPA自动伸缩

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-collector
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

### 3. Helm部署（推荐）

**安装步骤**:

```bash
# 1. 添加Helm仓库
helm repo add otlp-rust https://charts.otlp-rust.io
helm repo update

# 2. 查看可用版本
helm search repo otlp-rust

# 3. 安装
helm install otlp-collector otlp-rust/otlp-collector \
  --namespace observability \
  --create-namespace \
  --values values-production.yaml

# 4. 升级
helm upgrade otlp-collector otlp-rust/otlp-collector \
  --namespace observability \
  --values values-production.yaml

# 5. 查看状态
helm status otlp-collector -n observability

# 6. 回滚
helm rollback otlp-collector -n observability
```

**values-production.yaml**:

```yaml
replicaCount: 3

image:
  repository: otlp-rust
  tag: "1.0.0"
  pullPolicy: IfNotPresent

service:
  type: ClusterIP
  grpc:
    port: 4317
  http:
    port: 4318

resources:
  limits:
    cpu: 2000m
    memory: 4Gi
  requests:
    cpu: 500m
    memory: 1Gi

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

monitoring:
  enabled: true
  serviceMonitor:
    enabled: true
```

---

## 📊 监控告警

### Prometheus监控

**prometheus.yml配置**:

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'otlp-collector'
    kubernetes_sd_configs:
      - role: pod
        namespaces:
          names:
            - observability
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_label_app]
        action: keep
        regex: otlp-collector
      - source_labels: [__meta_kubernetes_pod_name]
        target_label: pod
      - source_labels: [__meta_kubernetes_namespace]
        target_label: namespace
```

**关键指标查询**:

```promql
# 接收速率
rate(otlp_receiver_accepted_spans_total[5m])

# 导出速率
rate(otlp_exporter_sent_spans_total[5m])

# 错误率
rate(otlp_exporter_send_failed_spans_total[5m]) / 
rate(otlp_exporter_sent_spans_total[5m])

# CPU使用率
rate(process_cpu_seconds_total{job="otlp-collector"}[5m])

# 内存使用
process_resident_memory_bytes{job="otlp-collector"}

# 队列大小
otlp_exporter_queue_size
```

### Grafana仪表板

**导入仪表板**:

```bash
# 使用Grafana API导入
curl -X POST http://grafana:3000/api/dashboards/db \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer $GRAFANA_TOKEN" \
  -d @otlp-dashboard.json
```

**关键面板**:

1. **吞吐量面板** - Spans接收/发送速率
2. **延迟面板** - P50/P95/P99延迟分布
3. **错误率面板** - 失败率趋势
4. **资源使用面板** - CPU/内存/网络
5. **队列面板** - 队列大小和积压

### 告警规则

完整告警配置请参考：[告警基线配置](../../semantics/ALERTING_BASELINE.md)

**PrometheusRule示例**:

```yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: otlp-collector-alerts
  namespace: observability
spec:
  groups:
  - name: otlp-collector
    interval: 30s
    rules:
    - alert: OTLPCollectorDown
      expr: up{job="otlp-collector"} == 0
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "OTLP Collector实例宕机"
    
    - alert: OTLPCollectorHighErrorRate
      expr: |
        rate(otlp_exporter_send_failed_spans_total[5m]) /
        rate(otlp_exporter_sent_spans_total[5m]) > 0.05
      for: 10m
      labels:
        severity: warning
      annotations:
        summary: "错误率过高: {{ $value | humanizePercentage }}"
```

---

## 🔍 故障排查

### 常见问题快速诊断

| 症状 | 可能原因 | 诊断命令 | 解决方案 |
|------|---------|---------|---------|
| Pod无法启动 | 镜像拉取失败 | `kubectl describe pod` | 检查镜像仓库和凭证 |
| 数据丢失 | 队列积压 | `kubectl logs` + PromQL | 扩容或调整批大小 |
| 高延迟 | 资源不足 | `kubectl top pod` | 增加资源限制 |
| 连接失败 | 网络策略 | `kubectl get networkpolicy` | 检查NetworkPolicy |

### 诊断脚本

**健康检查脚本**:

```bash
#!/bin/bash
# health-check.sh

echo "=== OTLP Collector健康检查 ==="

# 1. 检查Pod状态
echo "1. Pod状态:"
kubectl get pods -n observability -l app=otlp-collector

# 2. 检查日志错误
echo "2. 最近错误:"
kubectl logs -n observability -l app=otlp-collector --tail=100 | grep -i error | tail -10

# 3. 检查资源使用
echo "3. 资源使用:"
kubectl top pods -n observability -l app=otlp-collector

# 4. 检查Service可用性
echo "4. Service状态:"
kubectl get svc -n observability otlp-collector

# 5. 检查HPA
echo "5. HPA状态:"
kubectl get hpa -n observability

echo "✅ 健康检查完成"
```

**性能诊断脚本**:

```bash
#!/bin/bash
# performance-check.sh

echo "=== 性能诊断 ==="

# 查询关键指标
PROMETHEUS_URL="http://prometheus:9090"

echo "1. 吞吐量（最近5分钟）:"
curl -s "$PROMETHEUS_URL/api/v1/query?query=rate(otlp_receiver_accepted_spans_total[5m])" | \
  jq '.data.result[0].value[1]'

echo "2. 错误率:"
curl -s "$PROMETHEUS_URL/api/v1/query?query=rate(otlp_exporter_send_failed_spans_total[5m])/rate(otlp_exporter_sent_spans_total[5m])" | \
  jq '.data.result[0].value[1]'

echo "3. 平均延迟:"
curl -s "$PROMETHEUS_URL/api/v1/query?query=histogram_quantile(0.95,rate(otlp_export_duration_seconds_bucket[5m]))" | \
  jq '.data.result[0].value[1]'

echo "✅ 性能诊断完成"
```

完整故障排查指南：[故障排查和性能调优](../OTLP_RUST_故障排查和性能调优指南.md)

---

## 🔒 安全加固

### mTLS配置

```yaml
# 使用cert-manager管理证书
apiVersion: cert-manager.io/v1
kind: Certificate
metadata:
  name: otlp-collector-cert
  namespace: observability
spec:
  secretName: otlp-collector-tls
  issuerRef:
    name: ca-issuer
    kind: ClusterIssuer
  dnsNames:
  - otlp-collector.observability.svc.cluster.local
```

### NetworkPolicy

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-collector-netpol
  namespace: observability
spec:
  podSelector:
    matchLabels:
      app: otlp-collector
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: default
    ports:
    - protocol: TCP
      port: 4317
    - protocol: TCP
      port: 4318
```

完整安全配置：[安全配置最佳实践](../OTLP_RUST_安全配置和最佳实践指南.md)

---

## ⚡ 性能优化

### 容量规划

**基准性能**:

- 单Pod: ~10k spans/s @ 500m CPU / 1Gi Memory
- 延迟: P95 < 10ms, P99 < 50ms
- 推荐配置: 3-5个副本

**计算公式**:

```text
所需副本数 = (预期峰值TPS / 单Pod容量) × 安全系数(1.5-2.0)

例如：
预期峰值: 50k spans/s
单Pod容量: 10k spans/s
安全系数: 1.5
所需副本数 = (50k / 10k) × 1.5 = 7.5 ≈ 8个
```

### 批处理优化

```yaml
# 优化的批处理配置
env:
- name: OTLP_BATCH_SIZE
  value: "2048"
- name: OTLP_BATCH_TIMEOUT
  value: "5s"
- name: OTLP_QUEUE_SIZE
  value: "10000"
```

---

## 📝 运维手册

### 日常运维任务

**每日检查**:

```bash
./scripts/daily-check.sh
```

**每周任务**:

- 检查资源使用趋势
- 审查告警历史
- 更新文档

**每月任务**:

- 性能基准测试
- 容量规划复核
- 依赖更新检查

### 应急响应

**响应流程**:

1. 接收告警
2. 确认影响范围
3. 执行诊断脚本
4. 实施缓解措施
5. 根因分析
6. 更新文档

**紧急联系人**:

- 运维团队: <ops@example.com>
- 开发团队: <dev@example.com>
- 值班电话: +86-xxx-xxxx

完整运维手册：[运维手册](../../semantics/RUNBOOK.md)

---

## 📚 相关文档

### 核心文档

- [K8s/Istio/Envoy完整指南](../OTLP_K8S_ISTIO_ENVOY_GUIDE.md)
- [故障排查指南](../OTLP_RUST_故障排查和性能调优指南.md)
- [安全配置指南](../OTLP_RUST_安全配置和最佳实践指南.md)
- [生产检查清单](../PRODUCTION_CHECKLIST.md)

### Semantics运维文档

- [告警基线](../../semantics/ALERTING_BASELINE.md)
- [运维手册](../../semantics/RUNBOOK.md)
- [伸缩策略](../../semantics/SCALING_STRATEGY.md)
- [OpAMP发布](../../semantics/OPAMP_ROLLOUT_STRATEGY.md)

### 项目管理

- [项目路线图](../PROJECT_ROADMAP_2025.md)
- [进度跟踪](../PROJECT_PROGRESS_TRACKER.md)

---

## 🔄 变更历史

| 版本 | 日期 | 变更内容 | 作者 |
|------|------|---------|------|
| v2.0 | 2025-10-17 | 完整版：部署脚本、监控配置、故障排查 | OTLP团队 |
| v1.0 | 2025-09-26 | 初始版本：框架结构 | OTLP团队 |

---

**文档版本**: v2.0  
**最后更新**: 2025年10月17日  
**维护者**: OTLP运维团队
