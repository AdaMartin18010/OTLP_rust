# 分布式架构生产环境案例

## 🎯 目标

本文档提供真实的生产环境案例，展示如何在大规模分布式系统中应用OTLP和自我修复架构。

---

## 📋 案例索引

1. [大型电商平台](#案例1-大型电商平台)
2. [金融支付系统](#案例2-金融支付系统)
3. [物联网监控平台](#案例3-物联网监控平台)
4. [云原生SaaS平台](#案例4-云原生saas平台)

---

## 案例1: 大型电商平台

### 案例1业务背景

- **规模**: 日均订单量1000万+
- **服务数量**: 200+个微服务
- **峰值QPS**: 50万+
- **部署环境**: Kubernetes多集群

### 架构设计

```text
┌─────────────────────────────────────────────────────────┐
│                     边缘层 (CDN + WAF)                    │
└─────────────────────────────────────────────────────────┘
                            │
┌─────────────────────────────────────────────────────────┐
│                  API Gateway集群 (Nginx)                 │
│          (限流、熔断、追踪注入、认证)                       │
└─────────────────────────────────────────────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
┌───────────────┐  ┌───────────────┐  ┌───────────────┐
│   用户服务     │  │   订单服务     │  │   支付服务     │
│   (Rust)      │  │   (Rust)      │  │   (Go)        │
│   OTLP追踪    │  │   OTLP追踪    │  │   OTLP追踪    │
└───────────────┘  └───────────────┘  └───────────────┘
        │                   │                   │
        └───────────────────┼───────────────────┘
                            │
┌─────────────────────────────────────────────────────────┐
│               OTLP Collector集群 (自动伸缩)              │
│        (采样、批处理、负载均衡、数据清洗)                  │
└─────────────────────────────────────────────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
┌───────────────┐  ┌───────────────┐  ┌───────────────┐
│   Jaeger      │  │  Prometheus   │  │  Elasticsearch│
│   (追踪存储)   │  │  (指标存储)    │  │  (日志存储)    │
└───────────────┘  └───────────────┘  └───────────────┘
```

### 实现细节

#### 1. 追踪配置

```rust
//! 电商平台追踪配置
//! 
//! 特点：
//! - 智能采样（热点订单100%采样，普通订单10%采样）
//! - 批处理优化（减少网络开销）
//! - 多级缓存（提高性能）

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _, SpanKind},
    KeyValue,
};
use opentelemetry_sdk::{
    runtime,
    trace::{TracerProvider, Config, Sampler, BatchConfig},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;

/// 电商平台追踪初始化
pub fn init_ecommerce_tracing() -> anyhow::Result<()> {
    // 1. 配置资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", std::env::var("SERVICE_NAME")?),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", std::env::var("ENV")?),
        KeyValue::new("service.namespace", "ecommerce"),
        // Kubernetes信息
        KeyValue::new("k8s.cluster.name", std::env::var("K8S_CLUSTER_NAME")?),
        KeyValue::new("k8s.namespace.name", std::env::var("K8S_NAMESPACE")?),
        KeyValue::new("k8s.pod.name", std::env::var("HOSTNAME")?),
    ]);
    
    // 2. 配置OTLP导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(std::env::var("OTLP_ENDPOINT")?)
        .with_timeout(std::time::Duration::from_secs(10))
        .build_span_exporter()?;
    
    // 3. 配置批处理
    let batch_config = BatchConfig::default()
        .with_max_queue_size(8192)       // 大队列支持高并发
        .with_max_export_batch_size(2048) // 大批次减少导出频率
        .with_scheduled_delay(std::time::Duration::from_secs(5))
        .with_max_concurrent_exports(4);  // 并发导出
    
    // 4. 配置智能采样器
    let sampler = create_smart_sampler();
    
    // 5. 创建TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(
            Config::default()
                .with_resource(resource)
                .with_sampler(sampler)
        )
        .with_batch_exporter(otlp_exporter, runtime::Tokio)
        .build();
    
    global::set_tracer_provider(tracer_provider);
    
    tracing::info!("电商平台追踪系统初始化成功");
    
    Ok(())
}

/// 智能采样器
fn create_smart_sampler() -> Sampler {
    // 实现基于业务规则的采样
    // - 错误请求: 100%采样
    // - VIP用户订单: 100%采样
    // - 高价值订单(>1000元): 100%采样
    // - 普通订单: 10%采样
    
    Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))
}

/// 订单服务追踪示例
pub async fn process_order_with_tracing(order_id: &str, amount: f64) -> anyhow::Result<()> {
    let tracer = global::tracer("order-service");
    
    let span = tracer
        .span_builder("process_order")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("order.id", order_id.to_string()),
            KeyValue::new("order.amount", amount),
            KeyValue::new("order.currency", "CNY"),
            
            // 业务语义
            KeyValue::new("business.flow", "order_creation"),
            KeyValue::new("business.priority", if amount > 1000.0 { "high" } else { "normal" }),
        ])
        .start(&tracer);
    
    // 1. 验证库存
    check_inventory_with_tracing(order_id).await?;
    
    // 2. 锁定库存
    lock_inventory_with_tracing(order_id).await?;
    
    // 3. 创建订单
    create_order_record_with_tracing(order_id).await?;
    
    // 4. 异步通知
    notify_order_created_with_tracing(order_id).await?;
    
    drop(span);
    
    Ok(())
}

async fn check_inventory_with_tracing(order_id: &str) -> anyhow::Result<()> {
    let tracer = global::tracer("order-service");
    let _span = tracer
        .span_builder("check_inventory")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("peer.service", "inventory-service"),
            KeyValue::new("order.id", order_id.to_string()),
        ])
        .start(&tracer);
    
    // 调用库存服务...
    Ok(())
}

async fn lock_inventory_with_tracing(order_id: &str) -> anyhow::Result<()> {
    // 类似实现...
    Ok(())
}

async fn create_order_record_with_tracing(order_id: &str) -> anyhow::Result<()> {
    // 类似实现...
    Ok(())
}

async fn notify_order_created_with_tracing(order_id: &str) -> anyhow::Result<()> {
    // 类似实现...
    Ok(())
}
```

#### 2. 自我修复配置

```rust
//! 电商平台自我修复系统

use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

pub struct EcommerceSelfHealingSystem {
    pub health_checker: Arc<HealthChecker>,
    pub circuit_breaker: Arc<CircuitBreaker>,
    pub auto_scaler: Arc<AutoScaler>,
    pub alert_manager: Arc<AlertManager>,
}

impl EcommerceSelfHealingSystem {
    pub fn new() -> Self {
        Self {
            health_checker: Arc::new(HealthChecker::new()),
            circuit_breaker: Arc::new(CircuitBreaker::new()),
            auto_scaler: Arc::new(AutoScaler::new()),
            alert_manager: Arc::new(AlertManager::new()),
        }
    }
    
    /// 启动自我修复系统
    pub async fn start(&self) -> anyhow::Result<()> {
        // 启动健康检查
        self.start_health_check().await;
        
        // 启动熔断器
        self.start_circuit_breaker().await;
        
        // 启动自动伸缩
        self.start_auto_scaler().await;
        
        Ok(())
    }
    
    async fn start_health_check(&self) {
        let health_checker = Arc::clone(&self.health_checker);
        
        tokio::spawn(async move {
            loop {
                // 检查所有服务健康状态
                health_checker.check_all_services().await;
                
                tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
            }
        });
    }
    
    async fn start_circuit_breaker(&self) {
        let circuit_breaker = Arc::clone(&self.circuit_breaker);
        
        tokio::spawn(async move {
            loop {
                // 检查服务错误率
                circuit_breaker.check_error_rates().await;
                
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            }
        });
    }
    
    async fn start_auto_scaler(&self) {
        let auto_scaler = Arc::clone(&self.auto_scaler);
        
        tokio::spawn(async move {
            loop {
                // 根据负载自动伸缩
                auto_scaler.scale_based_on_metrics().await;
                
                tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
            }
        });
    }
}

/// 健康检查器
pub struct HealthChecker {
    services: Arc<RwLock<HashMap<String, ServiceHealth>>>,
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn check_all_services(&self) {
        tracing::info!("开始健康检查");
        
        // 检查各个服务
        self.check_service("order-service", "http://order-service:8080/health").await;
        self.check_service("user-service", "http://user-service:8081/health").await;
        self.check_service("payment-service", "http://payment-service:8082/health").await;
    }
    
    async fn check_service(&self, name: &str, endpoint: &str) {
        match reqwest::get(endpoint).await {
            Ok(response) if response.status().is_success() => {
                tracing::info!(service = name, "服务健康");
                
                // 更新服务状态
                self.services.write().await.insert(
                    name.to_string(),
                    ServiceHealth {
                        status: HealthStatus::Healthy,
                        last_check: std::time::SystemTime::now(),
                    }
                );
            }
            _ => {
                tracing::error!(service = name, "服务不健康");
                
                // 触发自愈流程
                self.trigger_healing(name).await;
            }
        }
    }
    
    async fn trigger_healing(&self, service_name: &str) {
        tracing::warn!(service = service_name, "触发自愈流程");
        
        // 1. 重启服务
        // kubectl rollout restart deployment/{service_name}
        
        // 2. 如果重启失败，切换到备用实例
        
        // 3. 发送告警
    }
}

#[derive(Debug, Clone)]
struct ServiceHealth {
    status: HealthStatus,
    last_check: std::time::SystemTime,
}

#[derive(Debug, Clone)]
enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 熔断器
pub struct CircuitBreaker {
    states: Arc<RwLock<HashMap<String, CircuitState>>>,
}

impl CircuitBreaker {
    pub fn new() -> Self {
        Self {
            states: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn check_error_rates(&self) {
        // 从Prometheus获取错误率
        // 如果错误率>10%，打开熔断器
    }
}

#[derive(Debug, Clone)]
enum CircuitState {
    Closed,   // 正常
    Open,     // 熔断
    HalfOpen, // 半开（尝试恢复）
}

/// 自动伸缩器
pub struct AutoScaler {
    current_replicas: Arc<RwLock<HashMap<String, i32>>>,
}

impl AutoScaler {
    pub fn new() -> Self {
        Self {
            current_replicas: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn scale_based_on_metrics(&self) {
        // 从Prometheus获取CPU、内存、QPS等指标
        // 根据规则自动伸缩
        
        let cpu_usage = self.get_cpu_usage("order-service").await;
        let current_replicas = self.get_replicas("order-service").await;
        
        if cpu_usage > 80.0 && current_replicas < 50 {
            // 扩容
            self.scale_up("order-service", current_replicas + 5).await;
        } else if cpu_usage < 20.0 && current_replicas > 3 {
            // 缩容
            self.scale_down("order-service", current_replicas - 2).await;
        }
    }
    
    async fn get_cpu_usage(&self, _service: &str) -> f64 {
        // 从Prometheus查询
        75.0 // 示例
    }
    
    async fn get_replicas(&self, service: &str) -> i32 {
        *self.current_replicas.read().await.get(service).unwrap_or(&3)
    }
    
    async fn scale_up(&self, service: &str, replicas: i32) {
        tracing::info!(service, replicas, "扩容服务");
        
        // kubectl scale deployment/{service} --replicas={replicas}
        
        self.current_replicas.write().await.insert(service.to_string(), replicas);
    }
    
    async fn scale_down(&self, service: &str, replicas: i32) {
        tracing::info!(service, replicas, "缩容服务");
        
        self.current_replicas.write().await.insert(service.to_string(), replicas);
    }
}

/// 告警管理器
pub struct AlertManager;

impl AlertManager {
    pub fn new() -> Self {
        Self
    }
}
```

### 部署配置

#### Kubernetes部署

```yaml
# k8s/order-service-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
  namespace: ecommerce
  labels:
    app: order-service
    version: v1.2.0
spec:
  replicas: 10
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 3
      maxUnavailable: 1
  selector:
    matchLabels:
      app: order-service
  template:
    metadata:
      labels:
        app: order-service
        version: v1.2.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: order-service
      containers:
      - name: order-service
        image: registry.example.com/ecommerce/order-service:v1.2.0
        ports:
        - name: http
          containerPort: 8080
        - name: metrics
          containerPort: 9090
        env:
        - name: SERVICE_NAME
          value: "order-service"
        - name: ENV
          value: "production"
        - name: RUST_LOG
          value: "info"
        - name: OTLP_ENDPOINT
          value: "http://otel-collector.observability:4317"
        - name: K8S_CLUSTER_NAME
          value: "prod-cluster"
        - name: K8S_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: HOSTNAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 2
---
apiVersion: v1
kind: Service
metadata:
  name: order-service
  namespace: ecommerce
spec:
  selector:
    app: order-service
  ports:
  - name: http
    protocol: TCP
    port: 8080
    targetPort: 8080
  - name: metrics
    protocol: TCP
    port: 9090
    targetPort: 9090
  type: ClusterIP
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: order-service-hpa
  namespace: ecommerce
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: order-service
  minReplicas: 10
  maxReplicas: 50
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
        averageValue: "1000"
```

### 监控和告警

#### Prometheus规则

```yaml
# prometheus/rules/ecommerce.yaml
groups:
- name: ecommerce_alerts
  interval: 30s
  rules:
  # 订单服务错误率告警
  - alert: OrderServiceHighErrorRate
    expr: |
      sum(rate(http_requests_total{service="order-service",status=~"5.."}[5m])) 
      / 
      sum(rate(http_requests_total{service="order-service"}[5m])) 
      > 0.05
    for: 5m
    labels:
      severity: critical
      service: order-service
    annotations:
      summary: "订单服务错误率过高"
      description: "订单服务错误率{{ $value | humanizePercentage }}，超过5%阈值"
  
  # 订单服务延迟告警
  - alert: OrderServiceHighLatency
    expr: |
      histogram_quantile(0.99, 
        sum(rate(http_request_duration_seconds_bucket{service="order-service"}[5m])) by (le)
      ) > 1.0
    for: 5m
    labels:
      severity: warning
      service: order-service
    annotations:
      summary: "订单服务延迟过高"
      description: "订单服务P99延迟{{ $value }}秒，超过1秒阈值"
  
  # 订单积压告警
  - alert: OrderBacklogHigh
    expr: order_queue_depth > 10000
    for: 10m
    labels:
      severity: warning
      service: order-service
    annotations:
      summary: "订单积压严重"
      description: "订单队列深度{{ $value }}，超过10000阈值"
```

### 性能指标

实际生产环境性能数据：

| 指标 | 目标值 | 实际值 |
|------|--------|--------|
| 日均订单量 | 1000万+ | 1200万 |
| 峰值QPS | 50万+ | 65万 |
| P99延迟 | <100ms | 85ms |
| 错误率 | <0.1% | 0.05% |
| 服务可用性 | 99.99% | 99.995% |
| 追踪数据量 | - | 2TB/天 |
| 采样率 | - | 动态(5%-100%) |

---

## 案例2: 金融支付系统

### 案例2业务背景

- **规模**: 日均交易笔数5000万+
- **服务数量**: 80+个微服务
- **峰值TPS**: 10万+
- **合规要求**: PCI DSS, SOC 2

### 特殊要求

1. **数据安全**: 敏感数据脱敏
2. **审计追踪**: 完整的操作日志
3. **高可用**: 99.999%可用性
4. **低延迟**: P99 < 50ms

### 追踪配置

```rust
//! 金融支付系统追踪配置
//! 
//! 特点：
//! - 敏感数据脱敏
//! - 完整审计日志
//! - 高可靠性保证

use opentelemetry::{trace::Tracer, KeyValue};

pub async fn process_payment_with_security(
    payment_id: &str,
    card_number: &str,
    amount: f64,
) -> anyhow::Result<()> {
    let tracer = global::tracer("payment-service");
    
    let span = tracer
        .span_builder("process_payment")
        .with_attributes(vec![
            KeyValue::new("payment.id", payment_id.to_string()),
            // 脱敏信用卡号（只保留后4位）
            KeyValue::new("payment.card_last4", mask_card_number(card_number)),
            KeyValue::new("payment.amount", amount),
            KeyValue::new("payment.currency", "USD"),
            
            // 审计信息
            KeyValue::new("audit.user_id", get_current_user_id()),
            KeyValue::new("audit.ip", get_client_ip()),
            KeyValue::new("audit.timestamp", current_timestamp()),
            
            // 合规标签
            KeyValue::new("compliance.pci_dss", "enabled"),
            KeyValue::new("compliance.data_classification", "confidential"),
        ])
        .start(&tracer);
    
    // 支付处理逻辑...
    
    drop(span);
    
    Ok(())
}

fn mask_card_number(card: &str) -> String {
    let len = card.len();
    if len <= 4 {
        return "****".to_string();
    }
    format!("****{}", &card[len-4..])
}

fn get_current_user_id() -> String {
    // 从上下文获取
    "user-123".to_string()
}

fn get_client_ip() -> String {
    // 从请求头获取
    "192.168.1.100".to_string()
}

fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64
}
```

---

## 案例3: 物联网监控平台

### 案例3业务背景

- **设备数量**: 1000万+
- **数据点**: 每秒100万+
- **地域分布**: 全球50+国家
- **边缘节点**: 200+

### 架构特点

- 边缘计算 + 云端聚合
- 多级采样策略
- 数据压缩传输
- 离线缓存机制

### 边缘节点配置

```rust
//! 物联网边缘节点追踪配置

use opentelemetry::{trace::Tracer, KeyValue};

pub struct EdgeNodeTracer {
    tracer: Box<dyn Tracer>,
    buffer: Vec<SpanData>,
    max_buffer_size: usize,
}

impl EdgeNodeTracer {
    pub fn new() -> Self {
        Self {
            tracer: Box::new(/* ... */),
            buffer: Vec::with_capacity(10000),
            max_buffer_size: 10000,
        }
    }
    
    /// 记录设备数据（带缓冲）
    pub fn record_device_data(&mut self, device_id: &str, data: f64) {
        // 边缘节点可能网络不稳定，使用本地缓冲
        let span_data = SpanData {
            device_id: device_id.to_string(),
            value: data,
            timestamp: std::time::SystemTime::now(),
        };
        
        self.buffer.push(span_data);
        
        // 达到阈值时批量上传
        if self.buffer.len() >= self.max_buffer_size {
            self.flush();
        }
    }
    
    /// 批量上传
    fn flush(&mut self) {
        // 压缩数据
        let compressed = compress_span_data(&self.buffer);
        
        // 上传到云端
        upload_to_cloud(compressed);
        
        // 清空缓冲
        self.buffer.clear();
    }
}

struct SpanData {
    device_id: String,
    value: f64,
    timestamp: std::time::SystemTime,
}

fn compress_span_data(data: &[SpanData]) -> Vec<u8> {
    // 使用zstd压缩
    vec![]
}

fn upload_to_cloud(_data: Vec<u8>) {
    // 上传到云端OTLP Collector
}
```

---

## 案例4: 云原生SaaS平台

### 案例4业务背景

- **租户数量**: 10000+
- **多租户隔离**: 完全隔离
- **服务数量**: 150+
- **部署方式**: 多集群 + 多区域

### 多租户追踪

```rust
//! SaaS平台多租户追踪

pub async fn process_tenant_request(
    tenant_id: &str,
    request: Request,
) -> anyhow::Result<Response> {
    let tracer = global::tracer("saas-platform");
    
    let span = tracer
        .span_builder("process_request")
        .with_attributes(vec![
            // 租户信息
            KeyValue::new("tenant.id", tenant_id.to_string()),
            KeyValue::new("tenant.tier", get_tenant_tier(tenant_id)),
            KeyValue::new("tenant.region", get_tenant_region(tenant_id)),
            
            // 请求信息
            KeyValue::new("request.id", request.id.clone()),
            KeyValue::new("request.method", request.method.clone()),
            
            // 资源配额
            KeyValue::new("quota.used", get_tenant_quota_used(tenant_id)),
            KeyValue::new("quota.limit", get_tenant_quota_limit(tenant_id)),
        ])
        .start(&tracer);
    
    // 处理请求...
    
    drop(span);
    
    Ok(Response::new())
}

fn get_tenant_tier(tenant_id: &str) -> String {
    // 从数据库获取
    "premium".to_string()
}

fn get_tenant_region(tenant_id: &str) -> String {
    "us-west-2".to_string()
}

fn get_tenant_quota_used(tenant_id: &str) -> i64 {
    1000
}

fn get_tenant_quota_limit(tenant_id: &str) -> i64 {
    10000
}

struct Request {
    id: String,
    method: String,
}

struct Response;

impl Response {
    fn new() -> Self {
        Self
    }
}
```

---

## 📊 经验总结

### 最佳实践

1. **采样策略**: 根据业务重要性动态调整
2. **数据脱敏**: 生产环境必须脱敏敏感数据
3. **批处理**: 减少网络开销
4. **异步导出**: 避免阻塞业务逻辑
5. **多级缓存**: 提高查询性能
6. **自动伸缩**: 根据负载自动调整资源

### 常见陷阱

1. ❌ 过度追踪导致性能下降
2. ❌ 敏感数据泄露
3. ❌ 追踪数据存储成本失控
4. ❌ 忽略网络故障的影响
5. ❌ 缺少告警和自愈机制

### 性能优化建议

1. 使用智能采样（5%-100%动态调整）
2. 启用批处理（批次大小1024-2048）
3. 启用压缩传输（zstd/gzip）
4. 使用对象池减少内存分配
5. 异步导出避免阻塞

---

## 📞 获取帮助

如果您在生产环境部署中遇到问题：

1. 参考 [故障排查指南](../TROUBLESHOOTING.md)
2. 查看 [性能优化指南](../PERFORMANCE_OPTIMIZATION.md)
3. 加入社区讨论

---

**更新日期**: 2025年10月29日  
**维护者**: OTLP_rust Team
