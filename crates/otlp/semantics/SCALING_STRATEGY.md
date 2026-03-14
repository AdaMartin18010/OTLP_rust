# OTLP Collector自动伸缩策略指南

> **版本**: 2.0
> **日期**: 2025年10月17日
> **状态**: ✅ 完整版

---

## 📋 目录

- [OTLP Collector自动伸缩策略指南](#otlp-collector自动伸缩策略指南)
  - [📋 目录](#-目录)
  - [📋 文档概述](#-文档概述)
  - [🎯 伸缩目标](#-伸缩目标)
    - [核心原则](#核心原则)
  - [📊 指标选择](#-指标选择)
    - [1. CPU驱动（推荐）](#1-cpu驱动推荐)
    - [2. 吞吐量驱动（高级）](#2-吞吐量驱动高级)
  - [🔧 Prometheus Adapter配置](#-prometheus-adapter配置)
    - [安装Prometheus Adapter](#安装prometheus-adapter)
    - [Adapter配置](#adapter配置)
  - [⚙️ 反抖动配置](#️-反抖动配置)
    - [关键参数](#关键参数)
    - [渐进式扩缩容](#渐进式扩缩容)
  - [📈 容量规划](#-容量规划)
    - [单Pod基准](#单pod基准)
    - [计算副本数](#计算副本数)
  - [🔍 监控伸缩行为](#-监控伸缩行为)
    - [关键指标](#关键指标)
    - [Grafana仪表板](#grafana仪表板)
  - [⚠️ 最佳实践](#️-最佳实践)
    - [1. 资源配置](#1-资源配置)
    - [2. PodDisruptionBudget](#2-poddisruptionbudget)
    - [3. 亲和性配置](#3-亲和性配置)
  - [📚 相关文档](#-相关文档)
  - [📝 变更历史](#-变更历史)

## 📋 文档概述

本文档提供OTLP Collector在Kubernetes环境中的**自动伸缩策略**和**HPA配置指南**。

---

## 🎯 伸缩目标

### 核心原则

1. **响应式**: 根据负载自动扩缩容
2. **成本优化**: 避免过度配置
3. **稳定性**: 防止频繁抖动
4. **可预测**: 基于明确的指标

---

## 📊 指标选择

### 1. CPU驱动（推荐）

**优势**: 简单、可靠、Kubernetes原生支持

```yaml
# hpa-cpu.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector

  minReplicas: 2
  maxReplicas: 10

  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70  # 目标70% CPU使用率

  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60  # 1分钟稳定期
      policies:
      - type: Percent
        value: 50  # 每次增加50%
        periodSeconds: 60
      - type: Pods
        value: 2  # 或增加2个Pod
        periodSeconds: 60
      selectPolicy: Max  # 选择最激进的策略

    scaleDown:
      stabilizationWindowSeconds: 300  # 5分钟稳定期
      policies:
      - type: Percent
        value: 10  # 每次减少10%
        periodSeconds: 60
      selectPolicy: Min  # 选择最保守的策略
```

### 2. 吞吐量驱动（高级）

**需要**: Prometheus Adapter

```yaml
# hpa-custom-metrics.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa-throughput
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector

  minReplicas: 2
  maxReplicas: 20

  metrics:
  # CPU基线
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70

  # 自定义指标：接收速率
  - type: Pods
    pods:
      metric:
        name: otelcol_receiver_accepted_spans_rate
      target:
        type: AverageValue
        averageValue: "10000"  # 每Pod处理10k spans/s

  # 自定义指标：队列使用率
  - type: Pods
    pods:
      metric:
        name: otelcol_exporter_queue_utilization
      target:
        type: AverageValue
        averageValue: "50"  # 队列使用率<50%
```

---

## 🔧 Prometheus Adapter配置

### 安装Prometheus Adapter

```bash
helm repo add prometheus-community https://prometheus-community.github.io/helm-charts
helm install prometheus-adapter prometheus-community/prometheus-adapter \
  --namespace observability \
  --values prometheus-adapter-values.yaml
```

### Adapter配置

```yaml
# prometheus-adapter-values.yaml
rules:
  custom:
  # Span接收速率
  - seriesQuery: 'otelcol_receiver_accepted_spans'
    resources:
      overrides:
        namespace: {resource: "namespace"}
        pod: {resource: "pod"}
    name:
      matches: "^(.*)$"
      as: "otelcol_receiver_accepted_spans_rate"
    metricsQuery: 'sum(rate(<<.Series>>{<<.LabelMatchers>>}[1m])) by (<<.GroupBy>>)'

  # 队列使用率
  - seriesQuery: 'otelcol_exporter_queue_size'
    resources:
      overrides:
        namespace: {resource: "namespace"}
        pod: {resource: "pod"}
    name:
      matches: "^(.*)$"
      as: "otelcol_exporter_queue_utilization"
    metricsQuery: |
      sum(otelcol_exporter_queue_size{<<.LabelMatchers>>}) by (<<.GroupBy>>)
      /
      sum(otelcol_exporter_queue_capacity{<<.LabelMatchers>>}) by (<<.GroupBy>>)
      * 100
```

---

## ⚙️ 反抖动配置

### 关键参数

| 参数 | 建议值 | 说明 |
|------|--------|------|
| **scaleUp.stabilizationWindowSeconds** | 60-120s | 扩容前观察窗口 |
| **scaleDown.stabilizationWindowSeconds** | 300-600s | 缩容前观察窗口（更长） |
| **minReplicas** | 2-3 | 最小副本数（保证高可用） |
| **maxReplicas** | 10-20 | 最大副本数（防止失控） |

### 渐进式扩缩容

```yaml
behavior:
  scaleUp:
    policies:
    # 策略1: 每分钟最多增加50%
    - type: Percent
      value: 50
      periodSeconds: 60
    # 策略2: 每分钟最多增加2个Pod
    - type: Pods
      value: 2
      periodSeconds: 60
    # 选择最大值（更激进）
    selectPolicy: Max

  scaleDown:
    policies:
    # 策略1: 每分钟最多减少10%
    - type: Percent
      value: 10
      periodSeconds: 60
    # 策略2: 每分钟最多减少1个Pod
    - type: Pods
        value: 1
        periodSeconds: 60
    # 选择最小值（更保守）
    selectPolicy: Min
```

---

## 📈 容量规划

### 单Pod基准

基于性能测试结果（参考[MEASUREMENT_GUIDE.md](./MEASUREMENT_GUIDE.md)）：

| 资源配置 | 吞吐量 | CPU | 内存 |
|---------|--------|-----|------|
| **小型** (0.5核/512MB) | 5k spans/s | ~40% | ~400MB |
| **中型** (1核/1GB) | 10k spans/s | ~60% | ~700MB |
| **大型** (2核/2GB) | 20k spans/s | ~70% | ~1.2GB |

### 计算副本数

```python
# 计算所需副本数
def calculate_replicas(total_throughput_sps, per_pod_capacity_sps=10000, safety_factor=1.3):
    """
    total_throughput_sps: 总吞吐量（spans/s）
    per_pod_capacity_sps: 单Pod容量
    safety_factor: 安全系数（留余量）
    """
    return math.ceil(total_throughput_sps / per_pod_capacity_sps * safety_factor)

# 示例
total_load = 80000  # 80k spans/s
replicas = calculate_replicas(80000)  # 计算结果: 11个副本
```

---

## 🔍 监控伸缩行为

### 关键指标

```promql
# HPA当前副本数
kube_horizontalpodautoscaler_status_current_replicas{name="otel-collector-hpa"}

# HPA期望副本数
kube_horizontalpodautoscaler_status_desired_replicas{name="otel-collector-hpa"}

# 伸缩事件
changes(kube_horizontalpodautoscaler_status_current_replicas[1h])

# CPU使用率
avg(rate(process_cpu_seconds_total{job="otel-collector"}[5m]))

# 每Pod吞吐量
sum(rate(otelcol_receiver_accepted_spans[1m])) by (pod)
```

### Grafana仪表板

参考: `scaffold/grafana/dashboards/otel-collector-scaling.json`

**关键面板**:

- 副本数变化趋势
- CPU/内存使用率
- 每Pod吞吐量
- 伸缩事件时间线

---

## ⚠️ 最佳实践

### 1. 资源配置

```yaml
# 合理的资源限制
resources:
  requests:
    cpu: 500m
    memory: 512Mi
  limits:
    cpu: 1000m
    memory: 1Gi
```

### 2. PodDisruptionBudget

```yaml
# 确保高可用
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: otel-collector-pdb
spec:
  minAvailable: 1
  selector:
    matchLabels:
      app: otel-collector
```

### 3. 亲和性配置

```yaml
# 分散到不同节点
affinity:
  podAntiAffinity:
    preferredDuringSchedulingIgnoredDuringExecution:
    - weight: 100
      podAffinityTerm:
        labelSelector:
          matchLabels:
            app: otel-collector
        topologyKey: kubernetes.io/hostname
```

---

## 📚 相关文档

- [性能测量](./MEASUREMENT_GUIDE.md) - 基准测试
- [告警基线](./ALERTING_BASELINE.md) - 监控告警
- [运维手册](./RUNBOOK.md) - 日常运维
- [性能优化](./PERFORMANCE_OPTIMIZATION_MANUAL.md) - 优化指南

---

## 📝 变更历史

| 版本 | 日期 | 说明 |
|------|------|------|
| 2.0 | 2025-10-17 | 完整版发布：扩展为生产级伸缩策略 |
| 1.0 | 2025-09-XX | 初始版本 |

---

**智能伸缩，优化成本！** ⚖️✨
