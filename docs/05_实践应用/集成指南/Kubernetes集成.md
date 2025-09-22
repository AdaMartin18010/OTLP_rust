# Kubernetes 集成指南

## 📚 概述

本文档详细介绍了如何在Kubernetes环境中部署和配置OTLP Rust应用，包括容器化、服务发现、配置管理、监控和日志收集等。

## 🐳 容器化部署

### 1. Dockerfile 配置

```dockerfile
# 多阶段构建Dockerfile
FROM rust:1.90-slim as builder

# 安装构建依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖（利用Docker缓存）
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release && rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -r -s /bin/false appuser

# 复制二进制文件
COPY --from=builder /app/target/release/my-otlp-app /usr/local/bin/
RUN chmod +x /usr/local/bin/my-otlp-app

# 设置用户
USER appuser

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["my-otlp-app"]
```

### 2. 构建和推送镜像

```bash
# 构建镜像
docker build -t my-registry/my-otlp-app:latest .

# 推送镜像
docker push my-registry/my-otlp-app:latest
```

## ☸️ Kubernetes 部署

### 1. 基础部署配置

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-app
  namespace: default
  labels:
    app: otlp-app
    version: v1.0.0
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-app
  template:
    metadata:
      labels:
        app: otlp-app
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      containers:
      - name: otlp-app
        image: my-registry/my-otlp-app:latest
        ports:
        - containerPort: 8080
          name: http
        env:
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: SERVICE_NAME
          value: "otlp-app"
        - name: SERVICE_VERSION
          value: "1.0.0"
        - name: DEPLOYMENT_ENVIRONMENT
          value: "production"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
        volumeMounts:
        - name: config-volume
          mountPath: /etc/config
          readOnly: true
      volumes:
      - name: config-volume
        configMap:
          name: otlp-app-config
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-app-service
  labels:
    app: otlp-app
spec:
  selector:
    app: otlp-app
  ports:
  - name: http
    port: 80
    targetPort: 8080
    protocol: TCP
  type: ClusterIP
```

### 2. 配置管理

```yaml
# configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-app-config
  namespace: default
data:
  config.yaml: |
    endpoint: "http://otel-collector:4317"
    protocol: "grpc"
    service_name: "otlp-app"
    service_version: "1.0.0"
    sampling_ratio: 0.1
    batch_config:
      max_export_batch_size: 512
      export_timeout_ms: 5000
      max_queue_size: 2048
      scheduled_delay_ms: 5000
    retry_config:
      max_retries: 5
      initial_retry_delay_ms: 1000
      max_retry_delay_ms: 30000
      retry_delay_multiplier: 2.0
    security:
      tls_enabled: false
---
apiVersion: v1
kind: Secret
metadata:
  name: otlp-app-secrets
  namespace: default
type: Opaque
data:
  api-key: <base64-encoded-api-key>
  bearer-token: <base64-encoded-bearer-token>
```

### 3. 环境特定配置

```yaml
# deployment-dev.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-app-dev
  namespace: development
spec:
  replicas: 1
  selector:
    matchLabels:
      app: otlp-app-dev
  template:
    metadata:
      labels:
        app: otlp-app-dev
        environment: development
    spec:
      containers:
      - name: otlp-app
        image: my-registry/my-otlp-app:dev
        env:
        - name: OTLP_ENDPOINT
          value: "http://otel-collector-dev:4317"
        - name: DEBUG
          value: "true"
        - name: SAMPLING_RATIO
          value: "1.0"  # 100%采样用于开发
        resources:
          requests:
            memory: "64Mi"
            cpu: "50m"
          limits:
            memory: "256Mi"
            cpu: "200m"
---
# deployment-prod.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-app-prod
  namespace: production
spec:
  replicas: 5
  selector:
    matchLabels:
      app: otlp-app-prod
  template:
    metadata:
      labels:
        app: otlp-app-prod
        environment: production
    spec:
      containers:
      - name: otlp-app
        image: my-registry/my-otlp-app:latest
        env:
        - name: OTLP_ENDPOINT
          value: "https://api.honeycomb.io:443"
        - name: API_KEY
          valueFrom:
            secretKeyRef:
              name: otlp-app-secrets
              key: api-key
        - name: SAMPLING_RATIO
          value: "0.1"  # 10%采样用于生产
        resources:
          requests:
            memory: "256Mi"
            cpu: "200m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 60
          periodSeconds: 30
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 3
          failureThreshold: 3
```

## 📊 OpenTelemetry Collector 集成

### 1. Collector 部署

```yaml
# otel-collector.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: default
spec:
  replicas: 2
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector:latest
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        - containerPort: 8888
          name: metrics
        - containerPort: 8889
          name: pprof
        env:
        - name: HONEYCOMB_API_KEY
          valueFrom:
            secretKeyRef:
              name: honeycomb-secrets
              key: api-key
        volumeMounts:
        - name: config-volume
          mountPath: /etc/collector-config.yaml
          subPath: collector-config.yaml
        resources:
          requests:
            memory: "256Mi"
            cpu: "200m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
      volumes:
      - name: config-volume
        configMap:
          name: otel-collector-config
---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
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

### 2. Collector 配置

```yaml
# otel-collector-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
data:
  collector-config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
    
    processors:
      batch:
        send_batch_size: 1024
        timeout: 1s
      memory_limiter:
        limit_mib: 512
      resource:
        attributes:
        - key: k8s.cluster.name
          value: "production-cluster"
          action: insert
        - key: k8s.namespace.name
          from_attribute: k8s.namespace.name
          action: insert
      k8sattributes:
        auth_type: serviceAccount
        passthrough: false
        filter:
          node_from_env_var: KUBE_NODE_NAME
        extract:
          metadata:
            - k8s.pod.name
            - k8s.pod.uid
            - k8s.deployment.name
            - k8s.namespace.name
            - k8s.node.name
            - k8s.pod.start_time
        pod_association:
          - sources:
              - from: resource_attribute
                name: k8s.pod.uid
          - sources:
              - from: resource_attribute
                name: k8s.pod.name
              - from: resource_attribute
                name: k8s.namespace.name
    
    exporters:
      logging:
        loglevel: debug
      otlp:
        endpoint: "https://api.honeycomb.io:443"
        headers:
          "x-honeycomb-team": "${HONEYCOMB_API_KEY}"
          "x-honeycomb-dataset": "kubernetes"
        tls:
          insecure: false
      prometheus:
        endpoint: "0.0.0.0:8889"
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp, logging]
        metrics:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp, prometheus]
        logs:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp, logging]
```

## 🔄 自动扩缩容

### 1. Horizontal Pod Autoscaler

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-app-hpa
  namespace: default
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-app
  minReplicas: 3
  maxReplicas: 20
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
        name: http_requests_per_second
      target:
        type: AverageValue
        averageValue: "100"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 100
        periodSeconds: 30
```

### 2. Vertical Pod Autoscaler

```yaml
# vpa.yaml
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: otlp-app-vpa
  namespace: default
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-app
  updatePolicy:
    updateMode: "Auto"
  resourcePolicy:
    containerPolicies:
    - containerName: otlp-app
      maxAllowed:
        cpu: "2"
        memory: "2Gi"
      minAllowed:
        cpu: "100m"
        memory: "128Mi"
      controlledResources: ["cpu", "memory"]
```

## 📈 监控和告警

### 1. ServiceMonitor (Prometheus)

```yaml
# servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: otlp-app-monitor
  namespace: default
  labels:
    app: otlp-app
spec:
  selector:
    matchLabels:
      app: otlp-app
  endpoints:
  - port: http
    path: /metrics
    interval: 30s
    scrapeTimeout: 10s
    honorLabels: true
    relabelings:
    - sourceLabels: [__meta_kubernetes_pod_name]
      targetLabel: pod_name
    - sourceLabels: [__meta_kubernetes_namespace]
      targetLabel: namespace
    - sourceLabels: [__meta_kubernetes_service_name]
      targetLabel: service_name
```

### 2. PrometheusRule

```yaml
# prometheusrule.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: otlp-app-rules
  namespace: default
  labels:
    app: otlp-app
spec:
  groups:
  - name: otlp-app.rules
    rules:
    - alert: OtlpAppHighErrorRate
      expr: rate(otlp_requests_total{status="error"}[5m]) > 0.1
      for: 2m
      labels:
        severity: warning
      annotations:
        summary: "High error rate detected"
        description: "Error rate is {{ $value }} errors per second"
    
    - alert: OtlpAppHighLatency
      expr: histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m])) > 1
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "High latency detected"
        description: "95th percentile latency is {{ $value }} seconds"
    
    - alert: OtlpAppDown
      expr: up{job="otlp-app"} == 0
      for: 1m
      labels:
        severity: critical
      annotations:
        summary: "OTLP App is down"
        description: "OTLP App has been down for more than 1 minute"
```

### 3. Grafana Dashboard

```yaml
# grafana-dashboard.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-app-dashboard
  namespace: monitoring
  labels:
    grafana_dashboard: "1"
data:
  otlp-app-dashboard.json: |
    {
      "dashboard": {
        "id": null,
        "title": "OTLP App Dashboard",
        "tags": ["otlp", "rust"],
        "timezone": "browser",
        "panels": [
          {
            "id": 1,
            "title": "Request Rate",
            "type": "graph",
            "targets": [
              {
                "expr": "rate(otlp_requests_total[5m])",
                "legendFormat": "Requests/sec"
              }
            ]
          },
          {
            "id": 2,
            "title": "Error Rate",
            "type": "graph",
            "targets": [
              {
                "expr": "rate(otlp_requests_total{status=\"error\"}[5m])",
                "legendFormat": "Errors/sec"
              }
            ]
          },
          {
            "id": 3,
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
          }
        ]
      }
    }
```

## 🔐 安全配置

### 1. NetworkPolicy

```yaml
# networkpolicy.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-app-netpol
  namespace: default
spec:
  podSelector:
    matchLabels:
      app: otlp-app
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: monitoring
    - podSelector:
        matchLabels:
          app: otel-collector
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - podSelector:
        matchLabels:
          app: otel-collector
    ports:
    - protocol: TCP
      port: 4317
  - to: []
    ports:
    - protocol: TCP
      port: 443  # HTTPS for external APIs
```

### 2. PodSecurityPolicy

```yaml
# psp.yaml
apiVersion: policy/v1beta1
kind: PodSecurityPolicy
metadata:
  name: otlp-app-psp
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

### 3. RBAC

```yaml
# rbac.yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otlp-app-sa
  namespace: default
---
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  name: otlp-app-role
  namespace: default
rules:
- apiGroups: [""]
  resources: ["configmaps", "secrets"]
  verbs: ["get", "list", "watch"]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: otlp-app-rolebinding
  namespace: default
subjects:
- kind: ServiceAccount
  name: otlp-app-sa
  namespace: default
roleRef:
  kind: Role
  name: otlp-app-role
  apiGroup: rbac.authorization.k8s.io
```

## 🚀 部署脚本

### 1. 部署脚本

```bash
#!/bin/bash
# deploy.sh

set -e

NAMESPACE=${1:-default}
ENVIRONMENT=${2:-development}
IMAGE_TAG=${3:-latest}

echo "Deploying OTLP App to namespace: $NAMESPACE"
echo "Environment: $ENVIRONMENT"
echo "Image tag: $IMAGE_TAG"

# 创建命名空间
kubectl create namespace $NAMESPACE --dry-run=client -o yaml | kubectl apply -f -

# 应用配置
kubectl apply -f configmap.yaml -n $NAMESPACE
kubectl apply -f secret.yaml -n $NAMESPACE

# 应用RBAC
kubectl apply -f rbac.yaml -n $NAMESPACE

# 部署应用
kubectl apply -f deployment-$ENVIRONMENT.yaml -n $NAMESPACE

# 应用服务
kubectl apply -f service.yaml -n $NAMESPACE

# 应用网络策略
kubectl apply -f networkpolicy.yaml -n $NAMESPACE

# 等待部署完成
kubectl wait --for=condition=available --timeout=300s deployment/otlp-app -n $NAMESPACE

echo "Deployment completed successfully!"
```

### 2. 回滚脚本

```bash
#!/bin/bash
# rollback.sh

NAMESPACE=${1:-default}
REVISION=${2:-}

if [ -z "$REVISION" ]; then
    echo "Usage: $0 <namespace> <revision>"
    echo "Available revisions:"
    kubectl rollout history deployment/otlp-app -n $NAMESPACE
    exit 1
fi

echo "Rolling back to revision $REVISION in namespace $NAMESPACE"

kubectl rollout undo deployment/otlp-app --to-revision=$REVISION -n $NAMESPACE

kubectl rollout status deployment/otlp-app -n $NAMESPACE

echo "Rollback completed!"
```

## 📊 监控脚本

### 1. 健康检查脚本

```bash
#!/bin/bash
# health-check.sh

NAMESPACE=${1:-default}
POD_NAME=$(kubectl get pods -n $NAMESPACE -l app=otlp-app -o jsonpath='{.items[0].metadata.name}')

if [ -z "$POD_NAME" ]; then
    echo "No OTLP app pods found in namespace $NAMESPACE"
    exit 1
fi

echo "Checking health of pod: $POD_NAME"

# 检查pod状态
kubectl get pod $POD_NAME -n $NAMESPACE

# 检查日志
echo "Recent logs:"
kubectl logs $POD_NAME -n $NAMESPACE --tail=20

# 检查健康端点
kubectl exec $POD_NAME -n $NAMESPACE -- curl -f http://localhost:8080/health

echo "Health check completed!"
```

### 2. 性能监控脚本

```bash
#!/bin/bash
# performance-monitor.sh

NAMESPACE=${1:-default}

echo "Performance monitoring for OTLP App in namespace: $NAMESPACE"

# 获取资源使用情况
echo "Resource usage:"
kubectl top pods -n $NAMESPACE -l app=otlp-app

# 获取指标
echo "Metrics:"
kubectl port-forward -n $NAMESPACE svc/otlp-app-service 8080:80 &
PORT_FORWARD_PID=$!

sleep 5

curl -s http://localhost:8080/metrics | grep otlp_

kill $PORT_FORWARD_PID

echo "Performance monitoring completed!"
```

## 📚 最佳实践

### 1. 资源管理

- **合理设置资源限制**: 避免资源争用
- **使用HPA和VPA**: 自动调整资源使用
- **监控资源使用**: 及时发现资源瓶颈

### 2. 配置管理1

- **使用ConfigMap和Secret**: 分离配置和敏感信息
- **环境特定配置**: 不同环境使用不同配置
- **配置热更新**: 支持配置的动态更新

### 3. 监控和告警

- **全面监控**: 监控应用、基础设施和业务指标
- **合理告警**: 设置合适的告警阈值
- **日志收集**: 统一日志收集和分析

### 4. 安全实践

- **最小权限原则**: 使用RBAC限制权限
- **网络隔离**: 使用NetworkPolicy限制网络访问
- **安全镜像**: 使用安全的基础镜像

## 🚀 下一步

### 深入学习

1. **[微服务集成](微服务集成.md)** - 微服务环境部署
2. **[服务网格集成](服务网格集成.md)** - Istio集成
3. **[数据库集成](数据库集成.md)** - 数据库操作监控

### 运维实践

1. **[监控告警设置](../部署运维/监控告警.md)** - 建立监控体系
2. **[故障排查指南](../部署运维/故障排查.md)** - 快速定位问题
3. **[性能优化策略](../性能调优/优化策略.md)** - 提升应用性能

---

**Kubernetes集成指南版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP 2025 文档团队
