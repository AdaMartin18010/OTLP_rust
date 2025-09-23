# OTLP on Kubernetes with Istio/Envoy - 实践指引

## 目标

- 在 K8s 中部署应用与 OpenTelemetry Collector
- 通过 Istio/Envoy Sidecar 注入统一出入口
- 采用 OTLP (HTTP 4318 / gRPC 4317) 进行 traces/metrics/logs 上报

## 快速开始

1) 部署 OpenTelemetry Collector（最小化配置）

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: observability
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
spec:
  replicas: 1
  selector:
    matchLabels: { app: otel-collector }
  template:
    metadata:
      labels: { app: otel-collector }
    spec:
      containers:
        - name: otelcol
          image: otel/opentelemetry-collector:latest
          args: ["--config=/etc/otelcol-config.yaml"]
          ports:
            - containerPort: 4317 # gRPC
            - containerPort: 4318 # HTTP
          volumeMounts:
            - name: config
              mountPath: /etc/otelcol-config.yaml
              subPath: otelcol-config.yaml
      volumes:
        - name: config
          configMap:
            name: otelcol-config
---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector: { app: otel-collector }
  ports:
    - name: grpc
      port: 4317
      targetPort: 4317
    - name: http
      port: 4318
      targetPort: 4318
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: otelcol-config
  namespace: observability
data:
  otelcol-config.yaml: |
    receivers:
      otlp:
        protocols:
          http:
            endpoint: 0.0.0.0:4318
          grpc:
            endpoint: 0.0.0.0:4317
    processors:
      batch: {}
    exporters:
      logging: { loglevel: info }
    service:
      pipelines:
        traces: { receivers: [otlp], processors: [batch], exporters: [logging] }
        metrics: { receivers: [otlp], processors: [batch], exporters: [logging] }
        logs: { receivers: [otlp], processors: [batch], exporters: [logging] }
```

1. 为业务命名空间开启 Istio 注入

```bash
kubectl label namespace default istio-injection=enabled
```

1. 部署示例应用（通过环境变量配置 OTLP 端点）

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-demo
spec:
  replicas: 1
  selector:
    matchLabels: { app: otlp-demo }
  template:
    metadata:
      labels: { app: otlp-demo }
    spec:
      containers:
        - name: app
          image: your-registry/otlp-demo:latest
          env:
            - name: OTLP_ENDPOINT
              value: http://otel-collector.observability.svc.cluster.local:4318
            - name: OTLP_PROTOCOL
              value: http
```

## Istio/Envoy 集成要点

- 传递 TraceContext：确保网关/Sidecar 透传 `traceparent`/`b3` 头
- Envoy ALS 日志可作为补充（转 OTLP）
- mTLS 建议：Istio PeerAuthentication + DestinationRule 启用

## 故障排查

- 采集失败：检查 4317/4318 连通、Collector 日志；对比 `content-type` 与路径 `/v1/{traces|metrics|logs}`
- 丢数/背压：调整 batch 队列、限流与采样策略

## 后续

- 提供 Helm Chart 与 Istio VirtualService/PeerAuthentication 模板
- 扩展 gRPC metrics/logs 与生产级 TLS/mTLS 示例
