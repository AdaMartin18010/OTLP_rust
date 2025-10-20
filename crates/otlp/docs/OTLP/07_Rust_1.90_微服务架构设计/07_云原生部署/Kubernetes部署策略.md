# Kubernetes 部署策略

## 目录

- [Kubernetes 部署策略](#kubernetes-部署策略)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [🎯 部署策略类型](#-部署策略类型)
    - [1. 滚动更新 (Rolling Update)](#1-滚动更新-rolling-update)
    - [2. 蓝绿部署 (Blue-Green)](#2-蓝绿部署-blue-green)
    - [3. 金丝雀部署 (Canary)](#3-金丝雀部署-canary)
  - [🔧 Helm Chart 管理](#-helm-chart-管理)
  - [📊 部署监控](#-部署监控)
  - [🎯 最佳实践](#-最佳实践)

## 📋 概述

Kubernetes 提供了多种部署策略,以满足不同场景下的应用发布需求。
选择合适的部署策略可以最小化停机时间,降低发布风险。

## 🎯 部署策略类型

### 1. 滚动更新 (Rolling Update)

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-service
spec:
  replicas: 10
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 2        # 最多超出期望副本数 2 个
      maxUnavailable: 1  # 最多 1 个副本不可用
  template:
    metadata:
      labels:
        app: my-service
        version: v2
    spec:
      containers:
      - name: my-service
        image: my-service:v2
        ports:
        - containerPort: 8080
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
```

### 2. 蓝绿部署 (Blue-Green)

```yaml
# 蓝色部署 (当前版本)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-service-blue
spec:
  replicas: 10
  selector:
    matchLabels:
      app: my-service
      version: blue
  template:
    metadata:
      labels:
        app: my-service
        version: blue
    spec:
      containers:
      - name: my-service
        image: my-service:v1

---
# 绿色部署 (新版本)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-service-green
spec:
  replicas: 10
  selector:
    matchLabels:
      app: my-service
      version: green
  template:
    metadata:
      labels:
        app: my-service
        version: green
    spec:
      containers:
      - name: my-service
        image: my-service:v2

---
# Service 切换
apiVersion: v1
kind: Service
metadata:
  name: my-service
spec:
  selector:
    app: my-service
    version: green  # 切换到绿色版本
  ports:
  - port: 80
    targetPort: 8080
```

### 3. 金丝雀部署 (Canary)

```yaml
# Argo Rollouts 金丝雀部署
apiVersion: argoproj.io/v1alpha1
kind: Rollout
metadata:
  name: my-service
spec:
  replicas: 10
  strategy:
    canary:
      steps:
      - setWeight: 10    # 10% 流量到新版本
      - pause: {duration: 5m}
      - setWeight: 50    # 50% 流量到新版本
      - pause: {duration: 10m}
      - setWeight: 100   # 100% 流量到新版本
      canaryService: my-service-canary
      stableService: my-service-stable
      trafficRouting:
        istio:
          virtualService:
            name: my-service
            routes:
            - primary
  selector:
    matchLabels:
      app: my-service
  template:
    metadata:
      labels:
        app: my-service
    spec:
      containers:
      - name: my-service
        image: my-service:v2
```

## 🔧 Helm Chart 管理

```yaml
# Chart.yaml
apiVersion: v2
name: my-service
description: A Helm chart for my-service
type: application
version: 1.0.0
appVersion: "2.0.0"

---
# values.yaml
replicaCount: 10

image:
  repository: my-service
  pullPolicy: IfNotPresent
  tag: "v2"

service:
  type: ClusterIP
  port: 80
  targetPort: 8080

resources:
  limits:
    cpu: 1000m
    memory: 512Mi
  requests:
    cpu: 100m
    memory: 128Mi

autoscaling:
  enabled: true
  minReplicas: 2
  maxReplicas: 20
  targetCPUUtilizationPercentage: 80
```

## 📊 部署监控

```rust
/// 部署状态监控
pub struct DeploymentMonitor {
    pub deployment_name: String,
    pub namespace: String,
    pub kube_client: Arc<KubeClient>,
}

impl DeploymentMonitor {
    /// 检查部署状态
    pub async fn check_deployment_status(&self) -> Result<DeploymentStatus, MonitorError> {
        let deployment = self.kube_client
            .get_deployment(&self.deployment_name, &self.namespace)
            .await?;
        
        Ok(DeploymentStatus {
            desired_replicas: deployment.spec.replicas,
            current_replicas: deployment.status.replicas,
            ready_replicas: deployment.status.ready_replicas,
            available_replicas: deployment.status.available_replicas,
            conditions: deployment.status.conditions,
        })
    }
    
    /// 等待部署完成
    pub async fn wait_for_rollout(&self, timeout: Duration) -> Result<(), MonitorError> {
        let start = Instant::now();
        
        loop {
            if start.elapsed() > timeout {
                return Err(MonitorError::Timeout);
            }
            
            let status = self.check_deployment_status().await?;
            
            if status.is_ready() {
                return Ok(());
            }
            
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    }
}
```

## 🎯 最佳实践

1. **健康检查**: 配置 readiness 和 liveness 探针
2. **资源限制**: 设置合理的 CPU 和内存限制
3. **自动扩缩容**: 使用 HPA 实现自动扩缩容
4. **Pod 中断预算**: 使用 PDB 保证最小可用副本数
5. **优雅终止**: 处理 SIGTERM 信号,优雅关闭服务

---

**总结**: 选择合适的 Kubernetes 部署策略,可以实现零停机时间的应用发布,降低发布风险。
