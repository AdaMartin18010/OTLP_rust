# 部署核心概念

**版本**: 2.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

1. [容器化部署](#1-容器化部署)
2. [Kubernetes部署](#2-kubernetes部署)
3. [服务发现](#3-服务发现)
4. [配置管理](#4-配置管理)

---

## 1. 容器化部署

### 1.1 Docker多阶段构建

#### 定义

**形式化定义**: Multi-stage Build = (build_stage, runtime_stage, artifacts)，其中：
- build_stage: 编译阶段
- runtime_stage: 运行阶段
- artifacts: build → runtime 传递的文件

**优化目标**:
```
minimize(image_size)
maximize(build_cache_hit_rate)
ensure(reproducibility)
```

**通俗解释**: 使用多个Dockerfile阶段，构建阶段编译，运行阶段只包含必要文件，大幅减小镜像大小。

#### 内涵（本质特征）

- **分离编译和运行**: 构建工具不进入最终镜像
- **最小化镜像**: 只包含运行时依赖
- **层缓存优化**: 合理安排层顺序
- **安全性**: 减少攻击面

#### 外延（涵盖范围）

- 包含: Rust二进制构建、静态链接、Alpine基础镜像
- 不包含: 开发工具、源代码、构建缓存

#### 属性

| 属性 | 单阶段 | 多阶段 | 优化 |
|------|--------|--------|------|
| 镜像大小 | 2GB | 50MB | **40倍** |
| 构建时间 | 10min | 2min | **5倍** |
| 层数 | 20+ | 5-8 | **简化** |
| 安全性 | 低 | 高 | **提升** |

#### 关系

- 与**CI/CD**的关系: 多阶段构建是CI/CD的基础
- 与**缓存**的关系: 合理分层提升缓存命中率
- 与**安全**的关系: 最小化镜像减少漏洞

#### 示例

```dockerfile
# ============================================
# 多阶段Dockerfile - OTLP Rust服务
# ============================================

# ==================== 阶段1: 依赖缓存 ====================
FROM rust:1.90-slim AS chef
WORKDIR /app

# 安装cargo-chef用于依赖缓存
RUN cargo install cargo-chef

# ==================== 阶段2: 计划依赖 ====================
FROM chef AS planner
COPY . .
# 生成依赖清单
RUN cargo chef prepare --recipe-path recipe.json

# ==================== 阶段3: 构建依赖 ====================
FROM chef AS dependencies
COPY --from=planner /app/recipe.json recipe.json

# 构建依赖（会被缓存）
RUN cargo chef cook --release --recipe-path recipe.json

# ==================== 阶段4: 构建应用 ====================
FROM chef AS builder

# 复制依赖构建结果
COPY --from=dependencies /app/target target
COPY --from=dependencies /usr/local/cargo /usr/local/cargo

# 复制源代码
COPY . .

# 构建应用（依赖已缓存）
RUN cargo build --release --bin otlp-receiver

# 验证二进制
RUN ls -lh /app/target/release/otlp-receiver

# ==================== 阶段5: 运行时镜像 ====================
FROM debian:bookworm-slim AS runtime

# 安装运行时依赖
RUN apt-get update && \
    apt-get install -y \
        ca-certificates \
        libssl3 \
        && \
    rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -m -u 1000 otlp && \
    mkdir -p /app /data && \
    chown -R otlp:otlp /app /data

WORKDIR /app

# 从构建阶段复制二进制
COPY --from=builder --chown=otlp:otlp \
    /app/target/release/otlp-receiver /app/otlp-receiver

# 复制配置文件（如果需要）
COPY --chown=otlp:otlp config/production.yaml /app/config.yaml

# 切换到非root用户
USER otlp

# 暴露端口
EXPOSE 4317 4318

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD ["/app/otlp-receiver", "--health-check"]

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1

# 启动命令
ENTRYPOINT ["/app/otlp-receiver"]
CMD ["--config", "/app/config.yaml"]

# ==================== 元数据 ====================
LABEL maintainer="otlp-team@example.com"
LABEL version="1.0.0"
LABEL description="OTLP Receiver - OpenTelemetry Protocol Receiver"
```

```bash
# 构建脚本
#!/bin/bash

# 构建开发镜像（带调试符号）
docker build \
    --target builder \
    --tag otlp-receiver:dev \
    --file Dockerfile \
    .

# 构建生产镜像（优化）
docker build \
    --target runtime \
    --tag otlp-receiver:1.0.0 \
    --tag otlp-receiver:latest \
    --build-arg BUILDKIT_INLINE_CACHE=1 \
    --file Dockerfile \
    .

# 检查镜像大小
docker images otlp-receiver

# 输出示例:
# REPOSITORY       TAG       SIZE
# otlp-receiver    dev       2.1GB
# otlp-receiver    1.0.0     48MB    <- 多阶段优化
# otlp-receiver    latest    48MB

# 运行容器
docker run -d \
    --name otlp-receiver \
    --restart unless-stopped \
    -p 4317:4317 \
    -p 4318:4318 \
    -v /path/to/config.yaml:/app/config.yaml:ro \
    -v /path/to/data:/data \
    --memory 512m \
    --cpus 2 \
    otlp-receiver:latest
```

---

## 2. Kubernetes部署

### 2.1 Deployment资源

#### 定义

**形式化定义**: K8s Deployment D = (replicas, selector, template, strategy)，其中：
- replicas: 副本数量
- selector: Pod选择器
- template: Pod模板
- strategy: 更新策略 (RollingUpdate | Recreate)

**高可用要求**:
```
replicas ≥ 3
spread_across_zones = true
anti_affinity = preferred
```

**通俗解释**: Kubernetes Deployment管理Pod副本的创建、更新和扩缩容。

#### 内涵（本质特征）

- **声明式**: 描述期望状态
- **自动化**: K8s确保实际符合期望
- **滚动更新**: 零停机部署
- **自愈**: 自动重启失败Pod

#### 外延（涵盖范围）

- 包含: Pod管理、副本控制、版本管理
- 不包含: 有状态服务（使用StatefulSet）

#### 属性

| 属性 | 推荐值 | 说明 |
|------|--------|------|
| replicas | 3-10 | 副本数 |
| maxUnavailable | 25% | 更新时最大不可用 |
| maxSurge | 25% | 更新时最大超额 |
| minReadySeconds | 10 | 就绪等待时间 |

#### 关系

- 与**Service**的关系: Service负载均衡到Deployment的Pod
- 与**HPA**的关系: HPA自动调整Deployment的replicas
- 与**ConfigMap**的关系: ConfigMap注入配置到Pod

#### 示例

```yaml
# ==================== OTLP Receiver Deployment ====================
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-receiver
  namespace: observability
  labels:
    app: otlp-receiver
    version: v1.0.0
    component: collector
spec:
  # 副本数
  replicas: 3
  
  # 选择器（匹配Pod标签）
  selector:
    matchLabels:
      app: otlp-receiver
  
  # 更新策略
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 1  # 最多1个Pod不可用
      maxSurge: 1        # 最多额外1个Pod
  
  # 最小就绪时间（防止快速失败）
  minReadySeconds: 10
  
  # Pod模板
  template:
    metadata:
      labels:
        app: otlp-receiver
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8888"
        prometheus.io/path: "/metrics"
    
    spec:
      # 服务账户
      serviceAccountName: otlp-receiver
      
      # Pod反亲和性（分散到不同节点）
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - otlp-receiver
              topologyKey: kubernetes.io/hostname
      
      # 容器配置
      containers:
      - name: otlp-receiver
        image: otlp-receiver:1.0.0
        imagePullPolicy: IfNotPresent
        
        # 端口
        ports:
        - name: grpc
          containerPort: 4317
          protocol: TCP
        - name: http
          containerPort: 4318
          protocol: TCP
        - name: metrics
          containerPort: 8888
          protocol: TCP
        
        # 环境变量
        env:
        - name: RUST_LOG
          value: "info"
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        
        # 资源限制
        resources:
          requests:
            memory: "256Mi"
            cpu: "500m"
          limits:
            memory: "512Mi"
            cpu: "1000m"
        
        # 存活探针
        livenessProbe:
          httpGet:
            path: /health
            port: 8888
          initialDelaySeconds: 15
          periodSeconds: 20
          timeoutSeconds: 3
          failureThreshold: 3
        
        # 就绪探针
        readinessProbe:
          httpGet:
            path: /ready
            port: 8888
          initialDelaySeconds: 5
          periodSeconds: 10
          timeoutSeconds: 3
          successThreshold: 1
          failureThreshold: 3
        
        # 启动探针（处理慢启动）
        startupProbe:
          httpGet:
            path: /health
            port: 8888
          initialDelaySeconds: 0
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 30
        
        # 挂载配置
        volumeMounts:
        - name: config
          mountPath: /app/config.yaml
          subPath: config.yaml
          readOnly: true
        - name: data
          mountPath: /data
      
      # 卷配置
      volumes:
      - name: config
        configMap:
          name: otlp-receiver-config
      - name: data
        emptyDir: {}

---
# ==================== Service ====================
apiVersion: v1
kind: Service
metadata:
  name: otlp-receiver
  namespace: observability
  labels:
    app: otlp-receiver
spec:
  type: ClusterIP
  selector:
    app: otlp-receiver
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
    protocol: TCP
  - name: http
    port: 4318
    targetPort: 4318
    protocol: TCP
  - name: metrics
    port: 8888
    targetPort: 8888
    protocol: TCP

---
# ==================== HPA (自动扩缩容) ====================
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-receiver
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-receiver
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
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300  # 5分钟稳定期
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 30
      - type: Pods
        value: 2
        periodSeconds: 30

---
# ==================== ConfigMap ====================
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-receiver-config
  namespace: observability
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
        timeout: 5s
        send_batch_size: 512
    
    exporters:
      logging:
        loglevel: info
      otlp:
        endpoint: backend:4317
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [batch]
          exporters: [logging, otlp]
```

```bash
# 部署脚本
#!/bin/bash

# 创建命名空间
kubectl create namespace observability

# 应用配置
kubectl apply -f deployment.yaml

# 查看状态
kubectl get deployments -n observability
kubectl get pods -n observability
kubectl get hpa -n observability

# 查看Pod详情
kubectl describe pod otlp-receiver-xxx -n observability

# 查看日志
kubectl logs -f otlp-receiver-xxx -n observability

# 滚动更新
kubectl set image deployment/otlp-receiver \
    otlp-receiver=otlp-receiver:1.1.0 \
    -n observability

# 查看更新状态
kubectl rollout status deployment/otlp-receiver -n observability

# 回滚
kubectl rollout undo deployment/otlp-receiver -n observability

# 手动扩缩容
kubectl scale deployment/otlp-receiver --replicas=5 -n observability
```

---

## 3. 服务发现

### 3.1 Consul服务注册

#### 定义

**形式化定义**: Service Discovery SD = (register, deregister, query, health_check)

**服务注册信息**:
```json
{
  "ID": "otlp-receiver-1",
  "Name": "otlp-receiver",
  "Address": "10.0.1.5",
  "Port": 4317,
  "Tags": ["v1.0.0", "grpc"],
  "Check": {
    "HTTP": "http://10.0.1.5:8888/health",
    "Interval": "10s",
    "Timeout": "3s"
  }
}
```

**通俗解释**: 服务自动注册到注册中心，客户端动态发现可用服务实例。

#### 内涵（本质特征）

- **动态发现**: 无需hardcode地址
- **健康检查**: 自动剔除不健康实例
- **负载均衡**: 客户端选择实例
- **故障转移**: 自动切换到健康实例

#### 外延（涵盖范围）

- 包含: Consul、etcd、Eureka、Kubernetes Service
- 不包含: 静态配置文件

#### 属性

| 属性 | 值 | 说明 |
|------|-----|------|
| TTL | 30s | 心跳间隔 |
| 检查间隔 | 10s | 健康检查 |
| 注销延迟 | 1min | 失败后注销 |
| 缓存TTL | 30s | 客户端缓存 |

#### 关系

- 与**负载均衡**的关系: 服务发现提供实例列表
- 与**健康检查**的关系: 健康检查决定实例可用性
- 与**配置中心**的关系: 通常集成在一起

#### 示例

```rust
use consul::{Client, ServiceEntry, AgentServiceRegistration};
use std::net::SocketAddr;

// Consul服务注册客户端
pub struct ConsulRegistry {
    client: Client,
    service_id: String,
    service_name: String,
    address: SocketAddr,
}

impl ConsulRegistry {
    pub async fn new(
        consul_addr: &str,
        service_name: String,
        address: SocketAddr,
    ) -> Result<Self> {
        let client = Client::new(consul_addr)?;
        let service_id = format!("{}-{}", service_name, uuid::Uuid::new_v4());
        
        Ok(Self {
            client,
            service_id,
            service_name,
            address,
        })
    }
    
    // 注册服务
    pub async fn register(&self) -> Result<()> {
        let registration = AgentServiceRegistration {
            id: Some(self.service_id.clone()),
            name: self.service_name.clone(),
            address: Some(self.address.ip().to_string()),
            port: Some(self.address.port()),
            tags: Some(vec![
                "v1.0.0".to_string(),
                "grpc".to_string(),
                "otlp".to_string(),
            ]),
            check: Some(AgentServiceCheck {
                http: Some(format!(
                    "http://{}:{}/health",
                    self.address.ip(),
                    self.address.port() + 1
                )),
                interval: Some("10s".to_string()),
                timeout: Some("3s".to_string()),
                deregister_critical_service_after: Some("1m".to_string()),
                ..Default::default()
            }),
            ..Default::default()
        };
        
        self.client.agent().service_register(&registration).await?;
        
        tracing::info!(
            service_id = %self.service_id,
            "Service registered with Consul"
        );
        
        Ok(())
    }
    
    // 注销服务
    pub async fn deregister(&self) -> Result<()> {
        self.client.agent().service_deregister(&self.service_id).await?;
        
        tracing::info!(
            service_id = %self.service_id,
            "Service deregistered from Consul"
        );
        
        Ok(())
    }
    
    // 发现服务
    pub async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>> {
        let services = self.client
            .health()
            .service(service_name, None, true) // only_passing=true
            .await?;
        
        let instances = services.into_iter()
            .map(|entry| ServiceInstance {
                id: entry.service.id,
                address: format!(
                    "{}:{}",
                    entry.service.address,
                    entry.service.port
                ),
                tags: entry.service.tags,
            })
            .collect();
        
        Ok(instances)
    }
}

// 服务实例
#[derive(Debug, Clone)]
pub struct ServiceInstance {
    pub id: String,
    pub address: String,
    pub tags: Vec<String>,
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    // 启动服务
    let addr = "0.0.0.0:4317".parse()?;
    let server = OtlpServer::new(addr);
    
    // 注册到Consul
    let registry = ConsulRegistry::new(
        "http://consul:8500",
        "otlp-receiver".to_string(),
        addr,
    ).await?;
    
    registry.register().await?;
    
    // 优雅关闭
    tokio::select! {
        _ = server.serve() => {},
        _ = tokio::signal::ctrl_c() => {
            registry.deregister().await?;
        }
    }
    
    Ok(())
}

// 客户端发现示例
pub async fn create_client_with_discovery() -> Result<OtlpClient> {
    let registry = ConsulRegistry::new(
        "http://consul:8500",
        "otlp-receiver".to_string(),
        "0.0.0.0:0".parse()?,
    ).await?;
    
    // 发现服务实例
    let instances = registry.discover("otlp-receiver").await?;
    
    if instances.is_empty() {
        return Err(Error::NoInstancesAvailable);
    }
    
    // 选择一个实例（轮询/随机/最少连接）
    let instance = &instances[0];
    
    // 创建客户端
    let client = OtlpClient::connect(&instance.address).await?;
    
    Ok(client)
}
```

---

## 4. 配置管理

### 4.1 12-Factor配置

#### 定义

**形式化定义**: Config C = environment_variables | config_files | secrets

**优先级**: env_vars > config_file > defaults

**通俗解释**: 遵循12-Factor原则，配置与代码分离，通过环境变量或配置文件管理。

#### 内涵（本质特征）

- **环境隔离**: dev/staging/prod不同配置
- **敏感信息**: Secrets单独管理
- **动态更新**: 支持热加载
- **版本控制**: 配置文件纳入Git

#### 外延（涵盖范围）

- 包含: 环境变量、YAML/TOML文件、Kubernetes ConfigMap/Secret
- 不包含: Hardcoded值

#### 属性

| 配置方式 | 灵活性 | 安全性 | 动态更新 |
|---------|--------|--------|----------|
| 环境变量 | 中 | 中 | 需重启 |
| 配置文件 | 高 | 低 | 支持 |
| ConfigMap | 高 | 低 | 支持 |
| Secret | 中 | 高 | 支持 |

#### 关系

- 与**部署**的关系: 配置影响部署流程
- 与**安全**的关系: Secrets需加密存储
- 与**运维**的关系: 配置管理是运维基础

#### 示例

```rust
use config::{Config, Environment, File};
use serde::{Deserialize, Serialize};

// 配置结构
#[derive(Debug, Deserialize, Serialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub otlp: OtlpConfig,
    pub database: DatabaseConfig,
    pub logging: LoggingConfig,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct OtlpConfig {
    pub grpc_endpoint: String,
    pub http_endpoint: String,
    pub batch_size: usize,
    pub timeout_seconds: u64,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct DatabaseConfig {
    pub url: String,  // 从环境变量读取
    pub max_connections: u32,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String,
}

impl AppConfig {
    // 加载配置（支持多种来源）
    pub fn load() -> Result<Self> {
        let mut builder = Config::builder()
            // 1. 默认配置
            .set_default("server.host", "0.0.0.0")?
            .set_default("server.port", 4317)?
            .set_default("server.workers", num_cpus::get())?
            .set_default("logging.level", "info")?
            .set_default("logging.format", "json")?;
        
        // 2. 从配置文件加载（按环境）
        let env = std::env::var("ENV").unwrap_or_else(|_| "development".to_string());
        
        builder = builder
            .add_source(File::with_name("config/default").required(false))
            .add_source(File::with_name(&format!("config/{}", env)).required(false));
        
        // 3. 从环境变量覆盖（前缀APP_）
        builder = builder
            .add_source(
                Environment::with_prefix("APP")
                    .separator("__")  // APP__SERVER__PORT
            );
        
        let config = builder.build()?;
        
        config.try_deserialize()
    }
    
    // 验证配置
    pub fn validate(&self) -> Result<()> {
        if self.server.port == 0 {
            return Err(Error::InvalidConfig("port must be > 0"));
        }
        
        if self.otlp.batch_size == 0 || self.otlp.batch_size > 10000 {
            return Err(Error::InvalidConfig("batch_size must be 1-10000"));
        }
        
        Ok(())
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    // 加载配置
    let config = AppConfig::load()?;
    config.validate()?;
    
    tracing::info!("Config loaded: {:?}", config);
    
    // 使用配置
    let server = OtlpServer::new(
        format!("{}:{}", config.server.host, config.server.port).parse()?,
        config.otlp,
    );
    
    server.serve().await
}
```

```yaml
# config/default.yaml
server:
  host: "0.0.0.0"
  port: 4317
  workers: 4

otlp:
  grpc_endpoint: "0.0.0.0:4317"
  http_endpoint: "0.0.0.0:4318"
  batch_size: 512
  timeout_seconds: 30

logging:
  level: "info"
  format: "json"

# config/production.yaml (覆盖默认值)
server:
  workers: 16

otlp:
  batch_size: 2048

logging:
  level: "warn"
```

```bash
# 环境变量配置
export ENV=production
export APP__SERVER__PORT=4317
export APP__DATABASE__URL="postgres://user:pass@db:5432/otlp"
export APP__LOGGING__LEVEL=info

# Docker环境变量
docker run \
    -e ENV=production \
    -e APP__SERVER__PORT=4317 \
    -e APP__DATABASE__URL="postgres://..." \
    otlp-receiver:latest

# Kubernetes ConfigMap + Secret
kubectl create configmap otlp-config \
    --from-file=config/production.yaml

kubectl create secret generic otlp-secrets \
    --from-literal=DATABASE_URL="postgres://..."
```

---

## 🔗 相关资源

- [知识图谱](./KNOWLEDGE_GRAPH.md)
- [对比矩阵](./COMPARISON_MATRIX.md)
- [部署指南README](./README.md)
- [生产就绪检查清单](../10_DEVELOPMENT/production_readiness.md)

---

**版本**: 2.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28  
**维护团队**: OTLP_rust部署团队

---

> **💡 提示**: 本文档包含完整的部署配置示例，包括Dockerfile、Kubernetes YAML、服务发现和配置管理，可直接用于生产环境。
