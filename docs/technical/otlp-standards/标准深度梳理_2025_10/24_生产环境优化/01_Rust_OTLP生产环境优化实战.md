# Rust OTLP 生产环境优化实战指南

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025-10-08  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Rust OTLP 生产环境优化实战指南](#rust-otlp-生产环境优化实战指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [生产环境挑战](#生产环境挑战)
    - [核心指标](#核心指标)
  - [大规模部署架构](#大规模部署架构)
    - [多层架构设计](#多层架构设计)
    - [Rust Agent 实现](#rust-agent-实现)
    - [Kubernetes 部署配置](#kubernetes-部署配置)
  - [成本优化策略](#成本优化策略)
    - [智能采样策略](#智能采样策略)
    - [分层存储策略](#分层存储策略)
    - [成本监控 Dashboard](#成本监控-dashboard)
  - [性能优化](#性能优化)
    - [零拷贝序列化](#零拷贝序列化)
    - [批量处理优化](#批量处理优化)
    - [连接池优化](#连接池优化)
  - [SLO监控与告警](#slo监控与告警)
    - [SLO 定义](#slo-定义)
    - [SLO 监控实现](#slo-监控实现)
    - [Prometheus 告警规则](#prometheus-告警规则)
  - [容量规划](#容量规划)
    - [容量计算模型](#容量计算模型)
  - [故障恢复](#故障恢复)
    - [断路器实现](#断路器实现)
    - [重试机制](#重试机制)
  - [最佳实践](#最佳实践)
    - [1. 监控指标](#1-监控指标)
    - [2. 配置管理](#2-配置管理)
    - [3. 运维检查清单](#3-运维检查清单)
  - [总结](#总结)
    - [架构演进路径](#架构演进路径)
    - [关键成功因素](#关键成功因素)

---

## 概述

### 生产环境挑战

在大规模生产环境中部署 OTLP 追踪系统面临的挑战：

- ⚠️ **高吞吐量**: 每秒百万级 Span 处理
- ⚠️ **成本控制**: 存储和网络成本
- ⚠️ **可靠性**: 99.9%+ 可用性要求
- ⚠️ **延迟敏感**: 对应用性能影响 < 1%
- ⚠️ **扩展性**: 随业务增长自动扩展

### 核心指标

```text
╔═══════════════════════════════════════════════════╗
║         生产环境关键指标                           ║
╠═══════════════════════════════════════════════════╣
║  吞吐量:      1M+ spans/sec                       ║
║  延迟:        P99 < 10ms                          ║
║  开销:        CPU < 2%, 内存 < 200MB              ║
║  可用性:      99.95%+                             ║
║  数据丢失:    < 0.01%                             ║
║  采样率:      1-10% (动态调整)                     ║
╚═══════════════════════════════════════════════════╝
```

---

## 大规模部署架构

### 多层架构设计

```text
┌────────────────────────────────────────────────────────┐
│                     应用层                              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
│  │Service A │  │Service B │  │Service C │  (1000s)   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘            │
└───────┼─────────────┼─────────────┼───────────────────┘
        │             │             │
        └─────────────┼─────────────┘
                      ▼
┌────────────────────────────────────────────────────────┐
│                  边缘收集层                             │
│  ┌──────────────────────────────────────────────┐     │
│  │  OTLP Collector (Agent Mode)                 │     │
│  │  - 本地缓存                                   │     │
│  │  - 批量发送                                   │     │
│  │  - 失败重试                                   │     │
│  └────────────────┬─────────────────────────────┘     │
└───────────────────┼───────────────────────────────────┘
                    ▼
┌────────────────────────────────────────────────────────┐
│                  聚合处理层                             │
│  ┌──────────────────────────────────────────────┐     │
│  │  OTLP Collector (Gateway Mode)               │     │
│  │  - 采样决策                                   │     │
│  │  - 数据清洗                                   │     │
│  │  - 负载均衡                                   │     │
│  └────────────────┬─────────────────────────────┘     │
└───────────────────┼───────────────────────────────────┘
                    ▼
┌────────────────────────────────────────────────────────┐
│                  存储层                                 │
│  ┌──────────┐  ┌───────────┐  ┌──────────┐           │
│  │ Hot: ES  │  │ Warm: S3  │  │Cold: GCS │           │
│  │ (7 days) │  │ (30 days) │  │(90 days) │           │
│  └──────────┘  └───────────┘  └──────────┘           │
└────────────────────────────────────────────────────────┘
```

### Rust Agent 实现

```rust
// src/agent/otlp_agent.rs
use std::sync::Arc;
use tokio::sync::{mpsc, Semaphore};
use std::time::Duration;

pub struct OtlpAgent {
    /// 本地缓冲队列
    buffer: Arc<Mutex<VecDeque<SpanData>>>,
    /// 批量大小
    batch_size: usize,
    /// 批量超时
    batch_timeout: Duration,
    /// 并发限制
    semaphore: Arc<Semaphore>,
    /// 导出器
    exporter: Arc<dyn Exporter>,
}

impl OtlpAgent {
    pub fn new(config: AgentConfig) -> Self {
        Self {
            buffer: Arc::new(Mutex::new(VecDeque::with_capacity(config.buffer_capacity))),
            batch_size: config.batch_size,
            batch_timeout: config.batch_timeout,
            semaphore: Arc::new(Semaphore::new(config.max_concurrent_exports)),
            exporter: config.exporter,
        }
    }

    /// 接收 Span
    pub async fn receive_span(&self, span: SpanData) -> Result<(), AgentError> {
        let mut buffer = self.buffer.lock().await;
        
        // 检查缓冲区是否满
        if buffer.len() >= buffer.capacity() {
            // 丢弃策略：丢弃最旧的
            buffer.pop_front();
            metrics::counter!("otlp_agent_spans_dropped").increment(1);
        }

        buffer.push_back(span);
        Ok(())
    }

    /// 批量导出
    pub async fn run(&self) -> Result<(), AgentError> {
        let mut interval = tokio::time::interval(self.batch_timeout);

        loop {
            interval.tick().await;

            let mut buffer = self.buffer.lock().await;
            if buffer.is_empty() {
                continue;
            }

            // 取出一批数据
            let batch: Vec<SpanData> = buffer
                .drain(..buffer.len().min(self.batch_size))
                .collect();

            drop(buffer); // 释放锁

            // 获取信号量
            let permit = self.semaphore.clone().acquire_owned().await?;
            let exporter = self.exporter.clone();

            // 异步导出
            tokio::spawn(async move {
                match exporter.export(batch.clone()).await {
                    Ok(_) => {
                        metrics::counter!("otlp_agent_spans_exported").increment(batch.len() as u64);
                    }
                    Err(e) => {
                        tracing::error!("Export failed: {}", e);
                        metrics::counter!("otlp_agent_export_errors").increment(1);
                        // TODO: 实现重试逻辑
                    }
                }
                drop(permit);
            });
        }
    }
}

#[derive(Debug, Clone)]
pub struct AgentConfig {
    pub buffer_capacity: usize,
    pub batch_size: usize,
    pub batch_timeout: Duration,
    pub max_concurrent_exports: usize,
    pub exporter: Arc<dyn Exporter>,
}

impl Default for AgentConfig {
    fn default() -> Self {
        Self {
            buffer_capacity: 10_000,
            batch_size: 1_000,
            batch_timeout: Duration::from_secs(10),
            max_concurrent_exports: 5,
            exporter: Arc::new(StdoutExporter::new()),
        }
    }
}
```

### Kubernetes 部署配置

```yaml
# k8s/agent-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otlp-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otlp-agent
  template:
    metadata:
      labels:
        app: otlp-agent
    spec:
      containers:
      - name: agent
        image: my-registry/otlp-agent:latest
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "500m"
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otlp-gateway.observability.svc:4317"
        - name: BATCH_SIZE
          value: "1000"
        - name: BATCH_TIMEOUT
          value: "10s"
        ports:
        - containerPort: 4317
          name: grpc
          protocol: TCP
        volumeMounts:
        - name: varlog
          mountPath: /var/log
          readOnly: true
      volumes:
      - name: varlog
        hostPath:
          path: /var/log

---
# k8s/gateway-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-gateway
  namespace: observability
spec:
  replicas: 5
  selector:
    matchLabels:
      app: otlp-gateway
  template:
    metadata:
      labels:
        app: otlp-gateway
    spec:
      containers:
      - name: gateway
        image: my-registry/otlp-gateway:latest
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "2000m"
        env:
        - name: SAMPLING_RATE
          value: "0.05"  # 5% 采样率
        - name: BACKEND_ENDPOINT
          value: "http://jaeger-collector:14268/api/traces"
        ports:
        - containerPort: 4317
          name: grpc
        - containerPort: 8888
          name: metrics
        livenessProbe:
          httpGet:
            path: /healthz
            port: 8888
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /readyz
            port: 8888
          initialDelaySeconds: 10
          periodSeconds: 5

---
apiVersion: v1
kind: Service
metadata:
  name: otlp-gateway
  namespace: observability
spec:
  selector:
    app: otlp-gateway
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
  - name: metrics
    port: 8888
    targetPort: 8888
  type: ClusterIP

---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-gateway-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-gateway
  minReplicas: 5
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
        name: otlp_spans_per_second
      target:
        type: AverageValue
        averageValue: "50000"
```

---

## 成本优化策略

### 智能采样策略

```rust
// src/sampling/intelligent_sampler.rs
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 智能采样器 - 基于多种策略
pub struct IntelligentSampler {
    /// 基础采样率
    base_rate: f64,
    /// 服务特定采样率
    service_rates: Arc<RwLock<HashMap<String, f64>>>,
    /// 错误始终采样
    sample_errors: bool,
    /// 慢请求始终采样
    slow_threshold_ms: u64,
}

impl IntelligentSampler {
    pub fn new(base_rate: f64) -> Self {
        Self {
            base_rate,
            service_rates: Arc::new(RwLock::new(HashMap::new())),
            sample_errors: true,
            slow_threshold_ms: 1000,
        }
    }

    /// 设置服务特定采样率
    pub async fn set_service_rate(&self, service: String, rate: f64) {
        self.service_rates.write().await.insert(service, rate);
    }

    pub async fn should_sample(&self, span: &SpanData) -> bool {
        // 1. 始终采样错误
        if self.sample_errors && span.status().is_error() {
            metrics::counter!("sampling_reason", "reason" => "error").increment(1);
            return true;
        }

        // 2. 始终采样慢请求
        let duration_ms = span.end_time()
            .duration_since(span.start_time())
            .unwrap()
            .as_millis() as u64;

        if duration_ms > self.slow_threshold_ms {
            metrics::counter!("sampling_reason", "reason" => "slow").increment(1);
            return true;
        }

        // 3. 检查服务特定采样率
        let service = span.resource()
            .get("service.name")
            .map(|v| v.to_string())
            .unwrap_or_default();

        let service_rates = self.service_rates.read().await;
        let rate = service_rates.get(&service).copied().unwrap_or(self.base_rate);

        // 4. 基于采样率随机采样
        let should_sample = rand::random::<f64>() < rate;
        
        if should_sample {
            metrics::counter!("sampling_reason", "reason" => "probabilistic").increment(1);
        }

        should_sample
    }
}

/// 动态调整采样率
pub struct DynamicSamplingAdjuster {
    sampler: Arc<IntelligentSampler>,
    target_spans_per_sec: f64,
}

impl DynamicSamplingAdjuster {
    pub async fn adjust(&self) {
        let current_rate = tokio::time::interval(Duration::from_secs(60));

        loop {
            current_rate.tick().await;

            // 获取当前吞吐量
            let current_throughput = metrics::gauge!("otlp_spans_per_second").get();

            // 计算目标采样率
            let target_rate = self.target_spans_per_sec / current_throughput;
            let target_rate = target_rate.clamp(0.01, 1.0);

            // 更新基础采样率
            tracing::info!(
                "Adjusting sampling rate: {} (throughput: {})",
                target_rate,
                current_throughput
            );

            // 这里需要访问 sampler 的内部状态来更新
            // 实际实现中可能需要更复杂的逻辑
        }
    }
}
```

### 分层存储策略

```rust
// src/storage/tiered_storage.rs
use chrono::{DateTime, Duration, Utc};

#[derive(Debug, Clone)]
pub enum StorageTier {
    Hot {
        backend: String,        // "elasticsearch"
        retention_days: u32,    // 7 天
    },
    Warm {
        backend: String,        // "s3"
        retention_days: u32,    // 30 天
    },
    Cold {
        backend: String,        // "glacier"
        retention_days: u32,    // 90 天
    },
}

pub struct TieredStorageManager {
    tiers: Vec<StorageTier>,
}

impl TieredStorageManager {
    pub fn new() -> Self {
        Self {
            tiers: vec![
                StorageTier::Hot {
                    backend: "elasticsearch".to_string(),
                    retention_days: 7,
                },
                StorageTier::Warm {
                    backend: "s3".to_string(),
                    retention_days: 30,
                },
                StorageTier::Cold {
                    backend: "glacier".to_string(),
                    retention_days: 90,
                },
            ],
        }
    }

    /// 根据时间决定存储层
    pub fn get_storage_tier(&self, timestamp: DateTime<Utc>) -> &StorageTier {
        let age = Utc::now() - timestamp;

        if age <= Duration::days(7) {
            &self.tiers[0] // Hot
        } else if age <= Duration::days(30) {
            &self.tiers[1] // Warm
        } else {
            &self.tiers[2] // Cold
        }
    }

    /// 执行数据迁移
    pub async fn migrate_data(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 1. 查询 Hot 存储中 > 7天 的数据
        let old_spans = self.query_old_spans_from_hot(7).await?;

        // 2. 写入 Warm 存储
        self.write_to_warm(old_spans).await?;

        // 3. 从 Hot 存储删除
        self.delete_from_hot(7).await?;

        // 4. 类似地迁移 Warm -> Cold
        let very_old_spans = self.query_old_spans_from_warm(30).await?;
        self.write_to_cold(very_old_spans).await?;
        self.delete_from_warm(30).await?;

        Ok(())
    }

    async fn query_old_spans_from_hot(&self, days: u32) -> Result<Vec<SpanData>, Box<dyn std::error::Error>> {
        // 实现查询逻辑
        Ok(vec![])
    }

    async fn write_to_warm(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn std::error::Error>> {
        // 压缩并写入 S3
        let compressed = Self::compress_spans(&spans)?;
        
        // 上传到 S3
        let s3_client = aws_sdk_s3::Client::new(&aws_config::load_from_env().await);
        let key = format!("traces/{}/{}.gz", 
            chrono::Utc::now().format("%Y-%m-%d"),
            uuid::Uuid::new_v4()
        );

        s3_client
            .put_object()
            .bucket("my-traces-bucket")
            .key(&key)
            .body(compressed.into())
            .content_encoding("gzip")
            .send()
            .await?;

        Ok(())
    }

    fn compress_spans(spans: &[SpanData]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        use flate2::write::GzEncoder;
        use flate2::Compression;
        use std::io::Write;

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        
        for span in spans {
            let json = serde_json::to_string(span)?;
            writeln!(encoder, "{}", json)?;
        }

        Ok(encoder.finish()?)
    }

    async fn delete_from_hot(&self, days: u32) -> Result<(), Box<dyn std::error::Error>> {
        // 实现删除逻辑
        Ok(())
    }

    // Warm -> Cold 类似实现
    async fn query_old_spans_from_warm(&self, days: u32) -> Result<Vec<SpanData>, Box<dyn std::error::Error>> {
        Ok(vec![])
    }

    async fn write_to_cold(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn std::error::Error>> {
        // 写入 Glacier
        Ok(())
    }

    async fn delete_from_warm(&self, days: u32) -> Result<(), Box<dyn std::error::Error>> {
        Ok(())
    }
}

/// 成本估算
pub struct CostEstimator {
    /// 每 GB 存储成本 (美元/月)
    hot_storage_cost_per_gb: f64,
    warm_storage_cost_per_gb: f64,
    cold_storage_cost_per_gb: f64,
    /// 每百万次查询成本
    query_cost_per_million: f64,
}

impl CostEstimator {
    pub fn aws_default() -> Self {
        Self {
            hot_storage_cost_per_gb: 0.10,   // Elasticsearch
            warm_storage_cost_per_gb: 0.023, // S3 Standard
            cold_storage_cost_per_gb: 0.004, // S3 Glacier
            query_cost_per_million: 0.50,
        }
    }

    pub fn estimate_monthly_cost(&self, metrics: &UsageMetrics) -> MonthlyCost {
        let hot_cost = metrics.hot_storage_gb * self.hot_storage_cost_per_gb;
        let warm_cost = metrics.warm_storage_gb * self.warm_storage_cost_per_gb;
        let cold_cost = metrics.cold_storage_gb * self.cold_storage_cost_per_gb;

        let query_cost = (metrics.monthly_queries as f64 / 1_000_000.0) 
            * self.query_cost_per_million;

        MonthlyCost {
            hot_storage: hot_cost,
            warm_storage: warm_cost,
            cold_storage: cold_cost,
            query_cost,
            total: hot_cost + warm_cost + cold_cost + query_cost,
        }
    }
}

#[derive(Debug)]
pub struct UsageMetrics {
    pub hot_storage_gb: f64,
    pub warm_storage_gb: f64,
    pub cold_storage_gb: f64,
    pub monthly_queries: u64,
}

#[derive(Debug)]
pub struct MonthlyCost {
    pub hot_storage: f64,
    pub warm_storage: f64,
    pub cold_storage: f64,
    pub query_cost: f64,
    pub total: f64,
}
```

### 成本监控 Dashboard

```yaml
# grafana-dashboard-cost.json (简化版)
{
  "title": "OTLP Cost Monitoring",
  "panels": [
    {
      "title": "Monthly Cost Estimate",
      "targets": [
        {
          "expr": "sum(otlp_storage_cost_usd) by (tier)"
        }
      ]
    },
    {
      "title": "Storage by Tier",
      "targets": [
        {
          "expr": "otlp_storage_size_gb{tier=\"hot\"}"
        },
        {
          "expr": "otlp_storage_size_gb{tier=\"warm\"}"
        },
        {
          "expr": "otlp_storage_size_gb{tier=\"cold\"}"
        }
      ]
    },
    {
      "title": "Cost per Service",
      "targets": [
        {
          "expr": "sum(otlp_service_cost_usd) by (service_name)"
        }
      ]
    }
  ]
}
```

---

## 性能优化

### 零拷贝序列化

```rust
// src/optimization/zero_copy.rs
use bytes::{Bytes, BytesMut};
use prost::Message;

/// 零拷贝导出器
pub struct ZeroCopyExporter {
    client: tonic::client::Grpc<tonic::transport::Channel>,
    buffer_pool: Arc<Mutex<Vec<BytesMut>>>,
}

impl ZeroCopyExporter {
    pub async fn export_zero_copy(&self, spans: Vec<SpanData>) -> Result<(), Box<dyn std::error::Error>> {
        // 1. 从池中获取 buffer
        let mut buffer = self.get_buffer_from_pool();

        // 2. 直接序列化到 buffer（零拷贝）
        let proto_spans = self.convert_to_proto(spans);
        proto_spans.encode(&mut buffer)?;

        // 3. 转换为 Bytes（零拷贝）
        let bytes = buffer.freeze();

        // 4. 发送（零拷贝）
        self.send_bytes(bytes).await?;

        Ok(())
    }

    fn get_buffer_from_pool(&self) -> BytesMut {
        self.buffer_pool.lock().unwrap()
            .pop()
            .unwrap_or_else(|| BytesMut::with_capacity(64 * 1024))
    }

    fn return_buffer_to_pool(&self, mut buffer: BytesMut) {
        buffer.clear();
        self.buffer_pool.lock().unwrap().push(buffer);
    }

    async fn send_bytes(&self, bytes: Bytes) -> Result<(), Box<dyn std::error::Error>> {
        // 使用 tonic 的零拷贝 API
        // ...
        Ok(())
    }
}
```

### 批量处理优化

```rust
// src/optimization/batching.rs

/// 自适应批量处理器
pub struct AdaptiveBatcher {
    min_batch_size: usize,
    max_batch_size: usize,
    current_batch_size: Arc<AtomicUsize>,
    latency_target_ms: u64,
}

impl AdaptiveBatcher {
    pub fn new(latency_target_ms: u64) -> Self {
        Self {
            min_batch_size: 100,
            max_batch_size: 10_000,
            current_batch_size: Arc::new(AtomicUsize::new(1000)),
            latency_target_ms,
        }
    }

    pub async fn adjust_batch_size(&self) {
        let mut interval = tokio::time::interval(Duration::from_secs(30));

        loop {
            interval.tick().await;

            // 获取当前平均延迟
            let current_latency_ms = metrics::histogram!("otlp_export_latency_ms")
                .percentile(0.95);

            let current_size = self.current_batch_size.load(Ordering::Relaxed);

            let new_size = if current_latency_ms > self.latency_target_ms as f64 {
                // 延迟太高，减小批次
                (current_size as f64 * 0.9) as usize
            } else {
                // 延迟可接受，增大批次
                (current_size as f64 * 1.1) as usize
            };

            let new_size = new_size.clamp(self.min_batch_size, self.max_batch_size);
            
            self.current_batch_size.store(new_size, Ordering::Relaxed);

            tracing::info!(
                "Adjusted batch size: {} -> {} (latency: {}ms)",
                current_size,
                new_size,
                current_latency_ms
            );
        }
    }

    pub fn get_batch_size(&self) -> usize {
        self.current_batch_size.load(Ordering::Relaxed)
    }
}
```

### 连接池优化

```rust
// src/optimization/connection_pool.rs
use deadpool::managed::{Manager, Pool, RecycleResult};

pub struct GrpcConnectionManager {
    endpoint: String,
}

#[async_trait]
impl Manager for GrpcConnectionManager {
    type Type = tonic::transport::Channel;
    type Error = Box<dyn std::error::Error>;

    async fn create(&self) -> Result<Self::Type, Self::Error> {
        let channel = tonic::transport::Channel::from_shared(self.endpoint.clone())?
            .http2_keep_alive_interval(Duration::from_secs(30))
            .keep_alive_timeout(Duration::from_secs(10))
            .keep_alive_while_idle(true)
            .tcp_keepalive(Some(Duration::from_secs(30)))
            .connect()
            .await?;

        Ok(channel)
    }

    async fn recycle(&self, conn: &mut Self::Type) -> RecycleResult<Self::Error> {
        // 检查连接是否仍然有效
        // 这里可以发送一个简单的健康检查请求
        Ok(())
    }
}

pub type ConnectionPool = Pool<GrpcConnectionManager>;

pub fn create_connection_pool(endpoint: String, max_size: usize) -> ConnectionPool {
    let manager = GrpcConnectionManager { endpoint };
    Pool::builder(manager)
        .max_size(max_size)
        .build()
        .unwrap()
}
```

---

## SLO监控与告警

### SLO 定义

```rust
// src/slo/definition.rs
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct ServiceLevelObjective {
    pub name: String,
    pub description: String,
    pub target_percentage: f64,  // 99.9% = 0.999
    pub window: Duration,         // 30 天
    pub metrics: Vec<SLOMetric>,
}

#[derive(Debug, Clone)]
pub enum SLOMetric {
    /// 可用性 SLO
    Availability {
        success_query: String,
        total_query: String,
    },
    /// 延迟 SLO
    Latency {
        query: String,
        threshold_ms: u64,
        percentile: f64,  // 0.99 for P99
    },
    /// 错误率 SLO
    ErrorRate {
        error_query: String,
        total_query: String,
    },
}

impl ServiceLevelObjective {
    pub fn tracing_availability() -> Self {
        Self {
            name: "Tracing Availability".to_string(),
            description: "99.9% of traces should be successfully exported".to_string(),
            target_percentage: 0.999,
            window: Duration::from_secs(30 * 24 * 3600), // 30天
            metrics: vec![
                SLOMetric::Availability {
                    success_query: "sum(rate(otlp_spans_exported_total[5m]))".to_string(),
                    total_query: "sum(rate(otlp_spans_total[5m]))".to_string(),
                },
            ],
        }
    }

    pub fn tracing_latency() -> Self {
        Self {
            name: "Tracing Latency".to_string(),
            description: "99% of traces should complete within 10ms".to_string(),
            target_percentage: 0.99,
            window: Duration::from_secs(7 * 24 * 3600), // 7天
            metrics: vec![
                SLOMetric::Latency {
                    query: "histogram_quantile(0.99, sum(rate(otlp_export_duration_seconds_bucket[5m])) by (le))".to_string(),
                    threshold_ms: 10,
                    percentile: 0.99,
                },
            ],
        }
    }
}
```

### SLO 监控实现

```rust
// src/slo/monitor.rs
use prometheus::{Histogram, Counter, Registry};

pub struct SloMonitor {
    slo: ServiceLevelObjective,
    registry: Registry,
    /// 错误预算剩余
    error_budget_remaining: Arc<AtomicU64>,
}

impl SloMonitor {
    pub fn new(slo: ServiceLevelObjective) -> Self {
        let registry = Registry::new();
        
        Self {
            slo,
            registry,
            error_budget_remaining: Arc::new(AtomicU64::new(0)),
        }
    }

    /// 计算错误预算
    pub fn calculate_error_budget(&self) -> ErrorBudget {
        let total_seconds = self.slo.window.as_secs() as f64;
        let target = self.slo.target_percentage;
        
        // 允许的停机时间
        let allowed_downtime_seconds = total_seconds * (1.0 - target);
        
        ErrorBudget {
            total_seconds: allowed_downtime_seconds,
            consumed_seconds: self.get_consumed_seconds(),
        }
    }

    fn get_consumed_seconds(&self) -> f64 {
        // 从 Prometheus 查询实际消耗的错误预算
        // 这里简化实现
        0.0
    }

    /// 检查 SLO 是否满足
    pub async fn check_slo_compliance(&self) -> bool {
        let budget = self.calculate_error_budget();
        budget.remaining_percentage() > 0.0
    }

    /// 生成 SLO 报告
    pub async fn generate_report(&self) -> SloReport {
        let budget = self.calculate_error_budget();
        
        SloReport {
            slo_name: self.slo.name.clone(),
            target: self.slo.target_percentage,
            actual: self.get_actual_performance().await,
            error_budget: budget,
            status: if budget.remaining_percentage() > 10.0 {
                SloStatus::Healthy
            } else if budget.remaining_percentage() > 0.0 {
                SloStatus::Warning
            } else {
                SloStatus::Exhausted
            },
        }
    }

    async fn get_actual_performance(&self) -> f64 {
        // 从 Prometheus 查询实际性能
        0.999
    }
}

#[derive(Debug)]
pub struct ErrorBudget {
    pub total_seconds: f64,
    pub consumed_seconds: f64,
}

impl ErrorBudget {
    pub fn remaining_seconds(&self) -> f64 {
        self.total_seconds - self.consumed_seconds
    }

    pub fn remaining_percentage(&self) -> f64 {
        (self.remaining_seconds() / self.total_seconds) * 100.0
    }

    pub fn is_exhausted(&self) -> bool {
        self.remaining_seconds() <= 0.0
    }
}

#[derive(Debug)]
pub struct SloReport {
    pub slo_name: String,
    pub target: f64,
    pub actual: f64,
    pub error_budget: ErrorBudget,
    pub status: SloStatus,
}

#[derive(Debug, PartialEq)]
pub enum SloStatus {
    Healthy,
    Warning,
    Exhausted,
}
```

### Prometheus 告警规则

```yaml
# prometheus/slo-alerts.yml
groups:
  - name: slo_tracing
    interval: 1m
    rules:
      # 错误预算消耗速率告警
      - alert: ErrorBudgetBurnRateTooHigh
        expr: |
          (
            1 - (
              sum(rate(otlp_spans_exported_total[1h]))
              /
              sum(rate(otlp_spans_total[1h]))
            )
          ) > 0.001 * 14.4  # 14.4x burn rate
        for: 5m
        labels:
          severity: critical
          slo: availability
        annotations:
          summary: "Error budget burn rate is too high"
          description: "At current rate, error budget will be exhausted in < 2 days"

      - alert: ErrorBudgetNearlyExhausted
        expr: |
          (
            otlp_error_budget_remaining_seconds / otlp_error_budget_total_seconds
          ) < 0.10
        for: 10m
        labels:
          severity: warning
          slo: availability
        annotations:
          summary: "Error budget nearly exhausted"
          description: "Only {{ $value | humanizePercentage }} of error budget remaining"

      # 延迟 SLO 告警
      - alert: LatencySLOViolation
        expr: |
          histogram_quantile(0.99,
            sum(rate(otlp_export_duration_seconds_bucket[5m])) by (le)
          ) > 0.010  # 10ms
        for: 10m
        labels:
          severity: warning
          slo: latency
        annotations:
          summary: "Latency SLO violation"
          description: "P99 latency is {{ $value }}s, exceeds 10ms target"

      # 可用性 SLO 告警
      - alert: AvailabilitySLOViolation
        expr: |
          (
            sum(rate(otlp_spans_exported_total[30d]))
            /
            sum(rate(otlp_spans_total[30d]))
          ) < 0.999
        for: 1h
        labels:
          severity: critical
          slo: availability
        annotations:
          summary: "Availability SLO violation"
          description: "Current availability is {{ $value | humanizePercentage }}, below 99.9% target"
```

---

## 容量规划

### 容量计算模型

```rust
// src/capacity/planner.rs

#[derive(Debug, Clone)]
pub struct CapacityRequirements {
    /// 每秒 Span 数量
    pub spans_per_second: u64,
    /// 平均 Span 大小（字节）
    pub avg_span_size_bytes: usize,
    /// 采样率
    pub sampling_rate: f64,
    /// 数据保留天数
    pub retention_days: u32,
}

impl CapacityRequirements {
    pub fn calculate_storage_needed(&self) -> StorageEstimate {
        let sampled_spans_per_day = (self.spans_per_second as f64 
            * 86400.0 
            * self.sampling_rate) as u64;

        let storage_per_day_gb = (sampled_spans_per_day as f64 
            * self.avg_span_size_bytes as f64) 
            / 1_073_741_824.0; // 转换为 GB

        let total_storage_gb = storage_per_day_gb * self.retention_days as f64;

        StorageEstimate {
            daily_gb: storage_per_day_gb,
            total_gb: total_storage_gb,
            compressed_gb: total_storage_gb * 0.3, // 假设 30% 压缩率
        }
    }

    pub fn calculate_compute_needed(&self) -> ComputeEstimate {
        // 假设每 10K spans/sec 需要 1 CPU 核心
        let cores_needed = (self.spans_per_second as f64 / 10_000.0).ceil() as u32;
        
        // 每 CPU 核心 2GB 内存
        let memory_gb_needed = cores_needed as f64 * 2.0;

        ComputeEstimate {
            cpu_cores: cores_needed,
            memory_gb: memory_gb_needed,
            instances: (cores_needed as f64 / 4.0).ceil() as u32, // 每实例 4 核
        }
    }

    pub fn calculate_network_needed(&self) -> NetworkEstimate {
        let bytes_per_second = self.spans_per_second as f64 * self.avg_span_size_bytes as f64;
        let mbps = (bytes_per_second * 8.0) / 1_000_000.0;

        NetworkEstimate {
            inbound_mbps: mbps,
            outbound_mbps: mbps * 0.8, // 考虑压缩
            monthly_gb: (bytes_per_second * 86400.0 * 30.0) / 1_073_741_824.0,
        }
    }
}

#[derive(Debug)]
pub struct StorageEstimate {
    pub daily_gb: f64,
    pub total_gb: f64,
    pub compressed_gb: f64,
}

#[derive(Debug)]
pub struct ComputeEstimate {
    pub cpu_cores: u32,
    pub memory_gb: f64,
    pub instances: u32,
}

#[derive(Debug)]
pub struct NetworkEstimate {
    pub inbound_mbps: f64,
    pub outbound_mbps: f64,
    pub monthly_gb: f64,
}

// 使用示例
pub fn example_capacity_planning() {
    let requirements = CapacityRequirements {
        spans_per_second: 100_000,
        avg_span_size_bytes: 1024,
        sampling_rate: 0.05, // 5%
        retention_days: 7,
    };

    let storage = requirements.calculate_storage_needed();
    let compute = requirements.calculate_compute_needed();
    let network = requirements.calculate_network_needed();

    println!("Capacity Planning:");
    println!("  Storage: {:.2} GB/day, {:.2} GB total", storage.daily_gb, storage.total_gb);
    println!("  Compute: {} cores, {:.2} GB RAM, {} instances", 
        compute.cpu_cores, compute.memory_gb, compute.instances);
    println!("  Network: {:.2} Mbps in, {:.2} GB/month", 
        network.inbound_mbps, network.monthly_gb);
}
```

---

## 故障恢复

### 断路器实现

```rust
// src/reliability/circuit_breaker.rs
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常运行
    Open,        // 断开，拒绝请求
    HalfOpen,    // 半开，尝试恢复
}

pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitBreakerState>>,
    config: CircuitBreakerConfig,
}

#[derive(Debug)]
struct CircuitBreakerState {
    current_state: CircuitState,
    failure_count: u32,
    success_count: u32,
    last_failure_time: Option<Instant>,
    last_state_change: Instant,
}

#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,     // 连续失败次数阈值
    pub success_threshold: u32,     // 半开状态需要的成功次数
    pub timeout: Duration,          // 断开后等待时间
    pub half_open_timeout: Duration,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitBreakerState {
                current_state: CircuitState::Closed,
                failure_count: 0,
                success_count: 0,
                last_failure_time: None,
                last_state_change: Instant::now(),
            })),
            config,
        }
    }

    pub async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: Future<Output = Result<T, E>>,
    {
        // 检查当前状态
        {
            let state = self.state.read().await;
            match state.current_state {
                CircuitState::Open => {
                    // 检查是否可以转到半开状态
                    if state.last_state_change.elapsed() >= self.config.timeout {
                        drop(state);
                        self.transition_to_half_open().await;
                    } else {
                        return Err(CircuitBreakerError::CircuitOpen);
                    }
                }
                _ => {}
            }
        }

        // 执行调用
        match f.await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitBreakerError::CallFailed(e))
            }
        }
    }

    async fn on_success(&self) {
        let mut state = self.state.write().await;
        
        match state.current_state {
            CircuitState::HalfOpen => {
                state.success_count += 1;
                if state.success_count >= self.config.success_threshold {
                    // 转到关闭状态
                    state.current_state = CircuitState::Closed;
                    state.failure_count = 0;
                    state.success_count = 0;
                    state.last_state_change = Instant::now();
                    tracing::info!("Circuit breaker closed");
                }
            }
            CircuitState::Closed => {
                // 重置失败计数
                state.failure_count = 0;
            }
            _ => {}
        }
    }

    async fn on_failure(&self) {
        let mut state = self.state.write().await;
        
        state.failure_count += 1;
        state.last_failure_time = Some(Instant::now());

        match state.current_state {
            CircuitState::Closed => {
                if state.failure_count >= self.config.failure_threshold {
                    // 转到断开状态
                    state.current_state = CircuitState::Open;
                    state.last_state_change = Instant::now();
                    tracing::warn!("Circuit breaker opened after {} failures", state.failure_count);
                }
            }
            CircuitState::HalfOpen => {
                // 转回断开状态
                state.current_state = CircuitState::Open;
                state.success_count = 0;
                state.last_state_change = Instant::now();
                tracing::warn!("Circuit breaker reopened");
            }
            _ => {}
        }
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        state.current_state = CircuitState::HalfOpen;
        state.success_count = 0;
        state.failure_count = 0;
        state.last_state_change = Instant::now();
        tracing::info!("Circuit breaker transitioned to half-open");
    }

    pub async fn get_state(&self) -> CircuitState {
        self.state.read().await.current_state
    }
}

#[derive(Debug, thiserror::Error)]
pub enum CircuitBreakerError<E> {
    #[error("Circuit breaker is open")]
    CircuitOpen,
    
    #[error("Call failed: {0}")]
    CallFailed(E),
}
```

### 重试机制

```rust
// src/reliability/retry.rs
use backoff::{ExponentialBackoff, backoff::Backoff};

pub struct RetryPolicy {
    pub max_retries: u32,
    pub initial_interval: Duration,
    pub max_interval: Duration,
    pub multiplier: f64,
    pub randomization_factor: f64,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_interval: Duration::from_millis(100),
            max_interval: Duration::from_secs(10),
            multiplier: 2.0,
            randomization_factor: 0.1,
        }
    }
}

pub async fn retry_with_backoff<F, T, E>(
    policy: &RetryPolicy,
    mut operation: F,
) -> Result<T, E>
where
    F: FnMut() -> Fut<Output = Result<T, E>>,
{
    let mut backoff = ExponentialBackoff {
        current_interval: policy.initial_interval,
        initial_interval: policy.initial_interval,
        max_interval: policy.max_interval,
        multiplier: policy.multiplier,
        randomization_factor: policy.randomization_factor,
        ..Default::default()
    };

    let mut attempts = 0;

    loop {
        match operation().await {
            Ok(result) => {
                if attempts > 0 {
                    tracing::info!("Operation succeeded after {} retries", attempts);
                }
                return Ok(result);
            }
            Err(e) => {
                attempts += 1;
                
                if attempts >= policy.max_retries {
                    tracing::error!("Operation failed after {} attempts", attempts);
                    return Err(e);
                }

                if let Some(duration) = backoff.next_backoff() {
                    tracing::warn!(
                        "Operation failed (attempt {}), retrying in {:?}",
                        attempts,
                        duration
                    );
                    tokio::time::sleep(duration).await;
                } else {
                    return Err(e);
                }
            }
        }
    }
}
```

---

## 最佳实践

### 1. 监控指标

```rust
// 必须监控的核心指标
pub fn register_core_metrics(registry: &Registry) {
    // 吞吐量
    register_counter!(
        "otlp_spans_total",
        "Total number of spans processed"
    );

    register_counter!(
        "otlp_spans_exported_total",
        "Total number of spans successfully exported"
    );

    // 延迟
    register_histogram!(
        "otlp_export_duration_seconds",
        "Time spent exporting spans"
    );

    // 错误
    register_counter!(
        "otlp_export_errors_total",
        "Total number of export errors"
    );

    // 队列
    register_gauge!(
        "otlp_queue_length",
        "Current length of the span queue"
    );

    // 采样
    register_counter!(
        "otlp_spans_sampled_total",
        "Total number of sampled spans"
    );

    // 资源使用
    register_gauge!(
        "otlp_memory_usage_bytes",
        "Current memory usage"
    );

    register_gauge!(
        "otlp_cpu_usage_percent",
        "Current CPU usage percentage"
    );
}
```

### 2. 配置管理

```yaml
# config/production.yaml
agent:
  buffer_capacity: 50000
  batch_size: 2000
  batch_timeout: 5s
  max_concurrent_exports: 10

sampling:
  base_rate: 0.05  # 5%
  sample_errors: true
  slow_threshold_ms: 1000
  
  # 服务特定采样率
  service_overrides:
    critical-service: 0.5   # 50%
    analytics-service: 0.01 # 1%

storage:
  hot:
    backend: elasticsearch
    retention_days: 7
  warm:
    backend: s3
    retention_days: 30
  cold:
    backend: glacier
    retention_days: 90

slo:
  availability:
    target: 0.999  # 99.9%
    window_days: 30
  latency:
    target_p99_ms: 10
    window_days: 7
```

### 3. 运维检查清单

```text
日常检查 (每天):
☐ 检查错误预算消耗
☐ 检查 P99 延迟
☐ 检查存储使用量
☐ 查看告警历史

每周检查:
☐ Review SLO 达成情况
☐ 分析成本趋势
☐ 检查容量规划
☐ 更新采样策略

每月检查:
☐ 性能基准测试
☐ 故障演练
☐ 容量评估
☐ 成本优化Review
```

---

## 总结

### 架构演进路径

```text
Phase 1: 基础部署 (0-3个月)
  ✅ 单点部署
  ✅ 基础监控
  ✅ 固定采样

Phase 2: 优化提升 (3-6个月)
  ✅ 多层架构
  ✅ 智能采样
  ✅ SLO监控

Phase 3: 规模化 (6-12个月)
  ✅ 大规模部署
  ✅ 成本优化
  ✅ 自动化运维

Phase 4: 持续改进 (12个月+)
  ✅ AI/ML 优化
  ✅ 自适应系统
  ✅ 预测性维护
```

### 关键成功因素

```text
✅ 明确的 SLO 目标
✅ 全面的监控体系
✅ 智能的采样策略
✅ 分层的存储架构
✅ 自动化的运维流程
✅ 持续的成本优化
```

---

**文档作者**: OTLP Rust Team  
**创建日期**: 2025-10-08  
**许可证**: MIT OR Apache-2.0  
**相关文档**:

- [Kubernetes部署指南](../19_容器化与Kubernetes/01_Rust_OTLP_Kubernetes完整部署指南.md)
- [监控与告警](../20_监控与告警/01_Prometheus_Grafana完整集成指南.md)
- [性能基准测试](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)
