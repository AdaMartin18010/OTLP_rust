# 生产环境部署 - Production Deployment

**创建日期**: 2025年10月29日  
**适用环境**: Kubernetes, Docker, Cloud Native  
**状态**: ✅ 生产验证

---

## 📋 目录

- [概述](#概述)
- [容器化部署](#容器化部署)
- [Kubernetes部署](#kubernetes部署)
- [负载均衡](#负载均衡)
- [自动扩缩容](#自动扩缩容)
- [故障恢复](#故障恢复)
- [安全监控](#安全监控)
- [运维最佳实践](#运维最佳实践)

---

## 概述

生产级Web服务部署指南：

- ✅ **容器化**: Docker多阶段构建
- ✅ **编排**: Kubernetes部署和服务
- ✅ **可观测**: 完整的追踪和监控
- ✅ **高可用**: 故障恢复和降级
- ✅ **可扩展**: 自动扩缩容

---

## 容器化部署

### 多阶段Docker构建

```dockerfile
# Dockerfile
# 构建阶段
FROM rust:1.90-bookworm as builder

WORKDIR /usr/src/app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./
COPY crates ./crates

# 构建依赖 (缓存层)
RUN cargo build --release --workspace

# 复制源代码
COPY . .

# 构建应用
RUN cargo build --release --bin web-api

# 运行时阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -m -u 1000 appuser

WORKDIR /app

# 复制二进制文件
COPY --from=builder /usr/src/app/target/release/web-api /app/web-api

# 复制配置文件
COPY config /app/config

# 切换到非root用户
USER appuser

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:8080/health || exit 1

# 启动应用
CMD ["/app/web-api"]
```

### Docker Compose开发环境

```yaml
# docker-compose.yml
version: '3.8'

services:
  web-api:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://otel-collector:4317
      - DATABASE_URL=postgres://user:pass@postgres:5432/app
      - REDIS_URL=redis://redis:6379
    depends_on:
      - postgres
      - redis
      - otel-collector
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 10s
      timeout: 3s
      retries: 3
    deploy:
      resources:
        limits:
          cpus: '2.0'
          memory: 2G
        reservations:
          cpus: '0.5'
          memory: 512M
  
  postgres:
    image: postgres:16-alpine
    environment:
      POSTGRES_USER: user
      POSTGRES_PASSWORD: pass
      POSTGRES_DB: app
    volumes:
      - postgres_data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user"]
      interval: 10s
      timeout: 5s
      retries: 5
  
  redis:
    image: redis:7-alpine
    volumes:
      - redis_data:/data
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 3s
      retries: 3
  
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    command: ["--config=/etc/otel-collector-config.yml"]
    volumes:
      - ./otel-collector-config.yml:/etc/otel-collector-config.yml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
  
  # Jaeger (可选)
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"  # Jaeger UI
      - "14250:14250"  # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true

volumes:
  postgres_data:
  redis_data:
```

---

## Kubernetes部署

### Deployment配置

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-api
  labels:
    app: web-api
    version: v1.0.0
spec:
  replicas: 3
  revisionHistoryLimit: 10
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: web-api
  template:
    metadata:
      labels:
        app: web-api
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      # 反亲和性 - 避免pod调度到同一节点
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
                  - web-api
              topologyKey: kubernetes.io/hostname
      
      containers:
      - name: web-api
        image: your-registry/web-api:1.0.0
        imagePullPolicy: IfNotPresent
        
        ports:
        - name: http
          containerPort: 8080
          protocol: TCP
        - name: metrics
          containerPort: 9090
          protocol: TCP
        
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-credentials
              key: url
        - name: REDIS_URL
          valueFrom:
            secretKeyRef:
              name: redis-credentials
              key: url
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
        
        # 资源限制
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "2000m"
        
        # 健康检查
        livenessProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 3
          failureThreshold: 3
        
        readinessProbe:
          httpGet:
            path: /ready
            port: http
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3
        
        # 启动探针 (给应用足够启动时间)
        startupProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 0
          periodSeconds: 10
          timeoutSeconds: 3
          failureThreshold: 30
        
        # 生命周期钩子
        lifecycle:
          preStop:
            exec:
              command: ["/bin/sh", "-c", "sleep 15"]
        
        # 安全上下文
        securityContext:
          runAsNonRoot: true
          runAsUser: 1000
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          capabilities:
            drop:
            - ALL
        
        # 挂载卷
        volumeMounts:
        - name: tmp
          mountPath: /tmp
        - name: config
          mountPath: /app/config
          readOnly: true
      
      volumes:
      - name: tmp
        emptyDir: {}
      - name: config
        configMap:
          name: web-api-config
---
# Service
apiVersion: v1
kind: Service
metadata:
  name: web-api
  labels:
    app: web-api
spec:
  type: ClusterIP
  ports:
  - name: http
    port: 80
    targetPort: http
    protocol: TCP
  - name: metrics
    port: 9090
    targetPort: metrics
    protocol: TCP
  selector:
    app: web-api
---
# HorizontalPodAutoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: web-api-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-api
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
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Pods
        value: 1
        periodSeconds: 60
---
# PodDisruptionBudget
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: web-api-pdb
spec:
  minAvailable: 2
  selector:
    matchLabels:
      app: web-api
```

### ConfigMap和Secret

```yaml
# k8s/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: web-api-config
data:
  app.yaml: |
    server:
      host: 0.0.0.0
      port: 8080
      workers: 4
    
    observability:
      otlp_endpoint: http://otel-collector:4317
      service_name: web-api
      service_version: 1.0.0
      sampling_rate: 0.1  # 10% 采样率
    
    database:
      max_connections: 20
      min_connections: 5
      connect_timeout: 10s
      idle_timeout: 60s
    
    cache:
      ttl: 300s
      max_size: 1000
---
# k8s/secret.yaml
apiVersion: v1
kind: Secret
metadata:
  name: db-credentials
type: Opaque
stringData:
  url: postgres://user:password@postgres:5432/app
---
apiVersion: v1
kind: Secret
metadata:
  name: redis-credentials
type: Opaque
stringData:
  url: redis://redis:6379/0
```

### Ingress配置

```yaml
# k8s/ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: web-api
  annotations:
    kubernetes.io/ingress.class: nginx
    cert-manager.io/cluster-issuer: letsencrypt-prod
    nginx.ingress.kubernetes.io/rate-limit: "100"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/proxy-body-size: "10m"
    nginx.ingress.kubernetes.io/proxy-connect-timeout: "30"
    nginx.ingress.kubernetes.io/proxy-read-timeout: "60"
    nginx.ingress.kubernetes.io/proxy-send-timeout: "60"
spec:
  tls:
  - hosts:
    - api.example.com
    secretName: api-tls
  rules:
  - host: api.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: web-api
            port:
              number: 80
```

---

## 负载均衡

### 客户端负载均衡

```rust
use tower::balance::p2c::Balance;
use tower::discover::ServiceList;

// 创建负载均衡的HTTP客户端
pub fn create_load_balanced_client(endpoints: Vec<String>) -> impl Service {
    // 创建服务列表
    let services: Vec<_> = endpoints
        .into_iter()
        .map(|endpoint| {
            Client::builder()
                .build()
                .unwrap()
        })
        .collect();
    
    // P2C (Power of Two Choices) 负载均衡
    Balance::new(ServiceList::new(services))
}

// 使用示例
#[instrument]
async fn call_backend_service(client: &Balance, request: Request) -> Result<Response> {
    let response = client.call(request).await?;
    Ok(response)
}
```

---

## 自动扩缩容

### 基于自定义指标的扩缩容

```yaml
# k8s/custom-metrics-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: web-api-custom-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-api
  minReplicas: 3
  maxReplicas: 50
  metrics:
  # CPU和内存
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  
  # 自定义指标: 请求延迟
  - type: Pods
    pods:
      metric:
        name: http_request_duration_p99
      target:
        type: AverageValue
        averageValue: "200m"  # 200ms
  
  # 自定义指标: 活跃连接数
  - type: Pods
    pods:
      metric:
        name: active_connections
      target:
        type: AverageValue
        averageValue: "1000"
  
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 100  # 最多翻倍
        periodSeconds: 60
      - type: Pods
        value: 5    # 或者增加5个pod
        periodSeconds: 60
      selectPolicy: Max
    
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Pods
        value: 1
        periodSeconds: 60
      selectPolicy: Min
```

---

## 故障恢复

### 熔断器实现

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq)]
enum CircuitState {
    Closed,   // 正常
    Open,     // 熔断
    HalfOpen, // 半开(尝试恢复)
}

// 熔断器
#[derive(Clone)]
pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitBreakerState>>,
    config: CircuitBreakerConfig,
    meter: Meter,
}

struct CircuitBreakerState {
    state: CircuitState,
    failure_count: u32,
    success_count: u32,
    last_failure_time: Option<Instant>,
}

pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub success_threshold: u32,
    pub timeout: Duration,
    pub half_open_timeout: Duration,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig, meter: Meter) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitBreakerState {
                state: CircuitState::Closed,
                failure_count: 0,
                success_count: 0,
                last_failure_time: None,
            })),
            config,
            meter,
        }
    }
    
    // 执行with熔断保护
    #[instrument(skip(self, f))]
    pub async fn call<F, T>(&self, f: F) -> Result<T>
    where
        F: Future<Output = Result<T>>,
    {
        // 检查状态
        {
            let state = self.state.read().await;
            
            match state.state {
                CircuitState::Open => {
                    // 检查是否应该进入半开状态
                    if let Some(last_failure) = state.last_failure_time {
                        if last_failure.elapsed() > self.config.timeout {
                            drop(state);
                            self.transition_to_half_open().await;
                        } else {
                            tracing::warn!("Circuit breaker is OPEN, rejecting request");
                            self.record_state("open");
                            return Err(anyhow::anyhow!("Circuit breaker open"));
                        }
                    }
                }
                CircuitState::HalfOpen => {
                    tracing::debug!("Circuit breaker is HALF_OPEN, allowing request");
                }
                CircuitState::Closed => {
                    // 正常状态
                }
            }
        }
        
        // 执行请求
        match f.await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(e)
            }
        }
    }
    
    async fn on_success(&self) {
        let mut state = self.state.write().await;
        
        match state.state {
            CircuitState::HalfOpen => {
                state.success_count += 1;
                
                if state.success_count >= self.config.success_threshold {
                    tracing::info!("Circuit breaker transitioning to CLOSED");
                    state.state = CircuitState::Closed;
                    state.failure_count = 0;
                    state.success_count = 0;
                    state.last_failure_time = None;
                    self.record_state("closed");
                }
            }
            CircuitState::Closed => {
                state.failure_count = 0;
            }
            _ => {}
        }
    }
    
    async fn on_failure(&self) {
        let mut state = self.state.write().await;
        
        match state.state {
            CircuitState::Closed => {
                state.failure_count += 1;
                
                if state.failure_count >= self.config.failure_threshold {
                    tracing::warn!("Circuit breaker transitioning to OPEN");
                    state.state = CircuitState::Open;
                    state.last_failure_time = Some(Instant::now());
                    self.record_state("open");
                }
            }
            CircuitState::HalfOpen => {
                tracing::warn!("Circuit breaker transitioning back to OPEN");
                state.state = CircuitState::Open;
                state.failure_count = 0;
                state.success_count = 0;
                state.last_failure_time = Some(Instant::now());
                self.record_state("open");
            }
            _ => {}
        }
    }
    
    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        tracing::info!("Circuit breaker transitioning to HALF_OPEN");
        state.state = CircuitState::HalfOpen;
        state.success_count = 0;
        self.record_state("half_open");
    }
    
    fn record_state(&self, state: &str) {
        self.meter
            .u64_counter("circuit_breaker.state_changes")
            .add(1, &[KeyValue::new("state", state.to_string())]);
    }
}
```

---

## 安全监控

### 安全事件追踪

```rust
// 安全事件类型
#[derive(Debug)]
enum SecurityEvent {
    AuthFailure { user: String, reason: String },
    RateLimitExceeded { client_id: String, endpoint: String },
    SuspiciousActivity { details: String },
    DataAccess { user: String, resource: String },
}

// 安全监控中间件
#[instrument]
async fn security_middleware(
    request: Request,
    next: Next,
) -> Response {
    let client_ip = extract_client_ip(&request);
    let user_id = extract_user_id(&request);
    
    // 检查IP黑名单
    if is_blacklisted(&client_ip).await {
        tracing::warn!(
            client_ip = %client_ip,
            "Blocked request from blacklisted IP"
        );
        
        record_security_event(SecurityEvent::SuspiciousActivity {
            details: format!("Blacklisted IP: {}", client_ip),
        });
        
        return Response::builder()
            .status(403)
            .body("Forbidden".into())
            .unwrap();
    }
    
    // 执行请求
    let response = next.run(request).await;
    
    // 记录敏感操作
    if is_sensitive_operation(&request) {
        record_security_event(SecurityEvent::DataAccess {
            user: user_id.unwrap_or_default(),
            resource: request.uri().path().to_string(),
        });
    }
    
    response
}

fn record_security_event(event: SecurityEvent) {
    tracing::warn!(event = ?event, "Security event recorded");
    
    // 发送到SIEM系统
    // send_to_siem(event);
}
```

---

## 运维最佳实践

### 优雅关闭

```rust
use tokio::signal;

async fn graceful_shutdown(server: Server) {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("Failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {
            tracing::info!("Received Ctrl+C signal");
        },
        _ = terminate => {
            tracing::info!("Received terminate signal");
        },
    }

    tracing::info!("Starting graceful shutdown...");
    
    // 等待所有请求完成 (最多30秒)
    tokio::time::timeout(
        Duration::from_secs(30),
        server.graceful_shutdown()
    ).await.ok();
    
    // 关闭追踪提供者
    global::shutdown_tracer_provider();
    
    tracing::info!("Shutdown complete");
}
```

---

## 总结

生产环境部署的关键要素：

1. **容器化**: 多阶段构建，优化镜像大小
2. **编排**: Kubernetes完整配置
3. **可观测**: 追踪、监控、日志集成
4. **高可用**: 多副本、健康检查、故障恢复
5. **安全**: 非root运行、安全上下文、审计日志
6. **弹性**: 自动扩缩容、熔断器、降级
7. **运维**: 优雅关闭、零停机部署

**生产就绪检查清单**:

- [ ] 容器镜像安全扫描通过
- [ ] 资源限制合理配置
- [ ] 健康检查配置正确
- [ ] HPA配置并测试
- [ ] PDB防止过度驱逐
- [ ] 监控告警规则配置
- [ ] 日志收集和聚合
- [ ] 追踪数据采样配置
- [ ] 熔断器和降级策略
- [ ] 灾难恢复计划

**恭喜！您已完成Web可观测性全套文档学习** 🎉
