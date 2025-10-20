# OTLP Rust 部署运维指南

## 目录

- [OTLP Rust 部署运维指南](#otlp-rust-部署运维指南)
  - [目录](#目录)
  - [📚 目录结构](#-目录结构)
  - [🎯 部署架构概览](#-部署架构概览)
    - [整体架构图](#整体架构图)
    - [核心组件](#核心组件)
  - [🚀 快速部署](#-快速部署)
    - [前置要求](#前置要求)
    - [一键部署脚本](#一键部署脚本)
  - [📊 监控配置](#-监控配置)
    - [Prometheus 配置示例](#prometheus-配置示例)
    - [Grafana 仪表板配置](#grafana-仪表板配置)
  - [🔧 故障排查](#-故障排查)
    - [常见问题诊断](#常见问题诊断)
  - [🛡️ 安全配置](#️-安全配置)
    - [RBAC 配置示例](#rbac-配置示例)
    - [网络策略配置](#网络策略配置)
  - [📈 性能调优](#-性能调优)
    - [资源配置建议](#资源配置建议)
    - [HPA 配置](#hpa-配置)
  - [📚 运维最佳实践](#-运维最佳实践)
    - [1. 监控和告警](#1-监控和告警)
    - [2. 日志管理](#2-日志管理)
    - [3. 备份和恢复](#3-备份和恢复)
    - [4. 安全运维](#4-安全运维)
    - [5. 性能优化](#5-性能优化)
  - [🔗 相关资源](#-相关资源)

本指南提供了OTLP Rust微服务可观测性平台的完整部署和运维解决方案，包括容器化部署、Kubernetes编排、监控告警、故障排查等企业级运维实践。

## 📚 目录结构

```text
docs/08_部署运维指南/
├── README.md                          # 本文件
├── 01_容器化部署/
│   ├── Docker最佳实践.md              # Docker容器化最佳实践
│   ├── 多阶段构建优化.md              # 多阶段构建和镜像优化
│   └── 容器安全配置.md                # 容器安全配置和扫描
├── 02_Kubernetes部署/
│   ├── Kubernetes集群部署.md          # K8s集群部署和配置
│   ├── Helm包管理.md                  # Helm包管理和版本控制
│   ├── 服务网格集成.md                # Istio/Linkerd服务网格集成
│   └── 自动扩缩容.md                  # HPA和VPA自动扩缩容
├── 03_监控告警/
│   ├── Prometheus监控.md              # Prometheus指标监控配置
│   ├── Grafana可视化.md               # Grafana仪表板配置
│   ├── 告警规则配置.md                # 告警规则和通知配置
│   └── 日志聚合分析.md                # ELK/Fluentd日志聚合
├── 04_故障排查/
│   ├── 常见问题诊断.md                # 常见问题和诊断方法
│   ├── 性能调优指南.md                # 性能调优和优化建议
│   ├── 网络问题排查.md                # 网络连接和通信问题
│   └── 数据一致性检查.md              # 数据一致性和完整性检查
├── 05_安全运维/
│   ├── 安全配置管理.md                # 安全配置和密钥管理
│   ├── 访问控制策略.md                # RBAC和网络策略
│   ├── 审计日志管理.md                # 审计日志和合规性
│   └── 漏洞扫描修复.md                # 安全漏洞扫描和修复
├── 06_备份恢复/
│   ├── 数据备份策略.md                # 数据备份和恢复策略
│   ├── 灾难恢复计划.md                # 灾难恢复和业务连续性
│   └── 版本回滚管理.md                # 版本回滚和回退策略
└── 07_运维自动化/
    ├── CI_CD流水线.md                 # 持续集成和部署流水线
    ├── 自动化测试.md                  # 自动化测试和验证
    ├── 配置管理.md                    # 配置管理和模板化
    └── 运维脚本.md                    # 运维脚本和工具
```

## 🎯 部署架构概览

### 整体架构图

```text
┌─────────────────────────────────────────────────────────────────┐
│                        Kubernetes 集群                          │
│                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────┐ │
│  │   Ingress       │    │   Service Mesh  │    │   OTLP      │ │
│  │   Controller    │    │   (Istio)       │    │   Services  │ │
│  └─────────────────┘    └─────────────────┘    └─────────────┘ │
│           │                       │                       │     │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────┐ │
│  │   API Gateway   │    │   Load Balancer │    │   Tracing   │ │
│  │   (Kong/Nginx)  │    │   (Envoy)       │    │   Collector │ │
│  └─────────────────┘    └─────────────────┘    └─────────────┘ │
│           │                       │                       │     │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────┐ │
│  │   Microservices │    │   Database      │    │   Cache     │ │
│  │   (OTLP Rust)   │    │   (PostgreSQL)  │    │   (Redis)   │ │
│  └─────────────────┘    └─────────────────┘    └─────────────┘ │
└─────────────────────────────────────────────────────────────────┘
                                │
                    ┌─────────────────┐
                    │   监控告警层     │
                    │                 │
                    │ • Prometheus    │
                    │ • Grafana       │
                    │ • AlertManager  │
                    │ • ELK Stack     │
                    └─────────────────┘
```

### 核心组件

1. **应用层**
   - OTLP Rust微服务
   - API网关和路由
   - 服务网格通信

2. **基础设施层**
   - Kubernetes集群
   - 容器运行时
   - 存储和网络

3. **监控层**
   - 指标收集(Prometheus)
   - 日志聚合(ELK)
   - 分布式追踪(Jaeger)

4. **安全层**
   - RBAC访问控制
   - 网络策略
   - 密钥管理

## 🚀 快速部署

### 前置要求

- Kubernetes 1.24+
- Helm 3.0+
- Docker 20.10+
- kubectl 1.24+

### 一键部署脚本

```bash
#!/bin/bash
# OTLP Rust 一键部署脚本

set -e

echo "🚀 开始部署 OTLP Rust 微服务可观测性平台"

# 1. 检查环境
echo "🔍 检查部署环境..."
kubectl version --client
helm version

# 2. 创建命名空间
echo "📦 创建命名空间..."
kubectl create namespace otlp-system --dry-run=client -o yaml | kubectl apply -f -

# 3. 部署服务网格
echo "🕸️ 部署 Istio 服务网格..."
helm repo add istio https://istio-release.storage.googleapis.com/charts
helm repo update
helm upgrade --install istio-base istio/base -n istio-system --create-namespace
helm upgrade --install istiod istio/istiod -n istio-system --wait

# 4. 部署 OTLP 服务
echo "🔧 部署 OTLP Rust 服务..."
helm upgrade --install otlp-rust ./helm/otlp-rust -n otlp-system --wait

# 5. 部署监控组件
echo "📊 部署监控组件..."
helm repo add prometheus-community https://prometheus-community.github.io/helm-charts
helm upgrade --install prometheus prometheus-community/kube-prometheus-stack \
  -n monitoring --create-namespace --wait

# 6. 配置 Ingress
echo "🌐 配置 Ingress..."
kubectl apply -f ./k8s/ingress.yaml -n otlp-system

# 7. 验证部署
echo "✅ 验证部署状态..."
kubectl get pods -n otlp-system
kubectl get svc -n otlp-system

echo "🎉 OTLP Rust 平台部署完成！"
echo "📱 访问地址: https://otlp.example.com"
echo "📊 监控地址: https://grafana.example.com"
```

## 📊 监控配置

### Prometheus 配置示例

```yaml
# prometheus-config.yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "otlp-rules.yml"

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093

scrape_configs:
  - job_name: 'otlp-rust'
    static_configs:
      - targets: ['otlp-service:8080']
    metrics_path: '/metrics'
    scrape_interval: 10s

  - job_name: 'kubernetes-pods'
    kubernetes_sd_configs:
      - role: pod
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true
```

### Grafana 仪表板配置

```json
{
  "dashboard": {
    "title": "OTLP Rust 微服务监控",
    "panels": [
      {
        "title": "请求吞吐量",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_requests_total[5m])",
            "legendFormat": "{{service}}"
          }
        ]
      },
      {
        "title": "响应时间",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P95"
          }
        ]
      }
    ]
  }
}
```

## 🔧 故障排查

### 常见问题诊断

1. **服务启动失败**

   ```bash
   # 检查 Pod 状态
   kubectl get pods -n otlp-system
   
   # 查看详细日志
   kubectl logs -f deployment/otlp-service -n otlp-system
   
   # 检查事件
   kubectl get events -n otlp-system --sort-by='.lastTimestamp'
   ```

2. **网络连接问题**

   ```bash
   # 测试服务间连通性
   kubectl exec -it pod-name -n otlp-system -- curl http://service-name:port/health
   
   # 检查网络策略
   kubectl get networkpolicy -n otlp-system
   
   # 查看 Istio 配置
   istioctl analyze -n otlp-system
   ```

3. **性能问题**

   ```bash
   # 查看资源使用情况
   kubectl top pods -n otlp-system
   
   # 检查 HPA 状态
   kubectl get hpa -n otlp-system
   
   # 分析性能指标
   kubectl exec -it pod-name -n otlp-system -- curl http://localhost:9090/metrics
   ```

## 🛡️ 安全配置

### RBAC 配置示例

```yaml
# rbac.yaml
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  namespace: otlp-system
  name: otlp-service-role
rules:
- apiGroups: [""]
  resources: ["pods", "services", "endpoints"]
  verbs: ["get", "list", "watch"]
- apiGroups: ["apps"]
  resources: ["deployments"]
  verbs: ["get", "list", "watch", "update"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: otlp-service-binding
  namespace: otlp-system
subjects:
- kind: ServiceAccount
  name: otlp-service-account
  namespace: otlp-system
roleRef:
  kind: Role
  name: otlp-service-role
  apiGroup: rbac.authorization.k8s.io
```

### 网络策略配置

```yaml
# network-policy.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-network-policy
  namespace: otlp-system
spec:
  podSelector:
    matchLabels:
      app: otlp-service
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: istio-system
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: monitoring
    ports:
    - protocol: TCP
      port: 9090
```

## 📈 性能调优

### 资源配置建议

```yaml
# resource-config.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-service
spec:
  replicas: 3
  template:
    spec:
      containers:
      - name: otlp-service
        image: otlp-rust:latest
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        env:
        - name: RUST_LOG
          value: "info"
        - name: RUST_BACKTRACE
          value: "1"
```

### HPA 配置

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-service-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-service
  minReplicas: 2
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

## 📚 运维最佳实践

### 1. 监控和告警

- 设置关键指标监控
- 配置合理的告警阈值
- 建立告警升级机制
- 定期审查告警规则

### 2. 日志管理

- 统一日志格式
- 集中日志收集
- 日志轮转和清理
- 日志分析和搜索

### 3. 备份和恢复

- 定期数据备份
- 测试恢复流程
- 异地备份存储
- 灾难恢复计划

### 4. 安全运维

- 定期安全扫描
- 及时更新补丁
- 访问权限审查
- 审计日志分析

### 5. 性能优化

- 定期性能评估
- 资源使用监控
- 瓶颈识别和优化
- 容量规划

## 🔗 相关资源

- [Kubernetes 官方文档](https://kubernetes.io/docs/)
- [Istio 服务网格文档](https://istio.io/docs/)
- [Prometheus 监控指南](https://prometheus.io/docs/)
- [Grafana 仪表板](https://grafana.com/docs/)
- [Helm 包管理](https://helm.sh/docs/)

---

**注意**: 本指南基于最新的Kubernetes和云原生技术栈，建议定期更新以保持最佳实践。
