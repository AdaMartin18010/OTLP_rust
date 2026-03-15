# OTLP Rust 场景用例指南

本文档提供 OTLP Rust 在不同场景下的实际应用示例。

## 目录

- [OTLP Rust 场景用例指南](#otlp-rust-场景用例指南)
  - [目录](#目录)
  - [1. 微服务架构](#1-微服务架构)
    - [场景描述](#场景描述)
    - [核心需求](#核心需求)
    - [架构图](#架构图)
    - [关键代码](#关键代码)
    - [示例文件](#示例文件)
  - [2. 数据处理管道](#2-数据处理管道)
    - [场景描述](#场景描述-1)
    - [核心需求](#核心需求-1)
    - [架构图](#架构图-1)
    - [关键代码](#关键代码-1)
    - [示例文件](#示例文件-1)
  - [3. 云原生/Kubernetes](#3-云原生kubernetes)
    - [场景描述](#场景描述-2)
    - [核心需求](#核心需求-2)
    - [架构图](#架构图-2)
    - [关键代码](#关键代码-2)
    - [示例文件](#示例文件-2)
  - [4. Serverless 环境](#4-serverless-环境)
    - [场景描述](#场景描述-3)
    - [核心需求](#核心需求-3)
    - [关键代码](#关键代码-3)
  - [5. 边缘计算](#5-边缘计算)
    - [场景描述](#场景描述-4)
    - [核心需求](#核心需求-4)
    - [关键代码](#关键代码-4)
  - [6. 物联网 (IoT)](#6-物联网-iot)
    - [场景描述](#场景描述-5)
    - [核心需求](#核心需求-5)
    - [关键代码](#关键代码-5)
  - [7. 金融交易系统](#7-金融交易系统)
    - [场景描述](#场景描述-6)
    - [核心需求](#核心需求-6)
    - [关键代码](#关键代码-6)
  - [8. 游戏服务器](#8-游戏服务器)
    - [场景描述](#场景描述-7)
    - [核心需求](#核心需求-7)
    - [关键代码](#关键代码-7)
  - [场景选择指南](#场景选择指南)
  - [相关资源](#相关资源)

---

## 1. 微服务架构

### 场景描述

电商系统包含多个微服务：用户服务、订单服务、支付服务、库存服务。

### 核心需求

- 分布式链路追踪
- 跨服务上下文传递
- 错误追踪和故障定位
- 性能监控

### 架构图

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   API网关    │────▶│  订单服务    │────▶│  支付服务    │
└─────────────┘     └─────────────┘     └─────────────┘
                            │
                            ▼
                     ┌─────────────┐
                     │  库存服务    │
                     └─────────────┘
```

### 关键代码

```rust
// 分布式上下文传递
#[derive(Clone, Debug)]
pub struct TraceContext {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub baggage: HashMap<String, String>,
}

impl TraceContext {
    pub fn child(&self) -> Self {
        Self {
            trace_id: self.trace_id.clone(),
            span_id: Uuid::new_v4().to_string(),
            parent_span_id: Some(self.span_id.clone()),
            baggage: self.baggage.clone(),
        }
    }
}

// 订单服务
pub async fn create_order(
    ctx: TraceContext,
    order_request: OrderRequest,
) -> Result<Order> {
    let span = Span::new(ctx.child(), "create_order");

    // 1. 验证用户
    let user = user_service.get_user(ctx.child(), &order_request.user_id).await?;

    // 2. 检查库存
    inventory_service.check_stock(ctx.child(), &order_request.items).await?;

    // 3. 处理支付
    payment_service.process(ctx.child(), &order_request.payment).await?;

    span.finish();
    Ok(order)
}
```

### 示例文件

- [电商微服务场景](../examples/scenario_ecommerce_microservices.rs)

---

## 2. 数据处理管道

### 场景描述

实时数据流处理系统，包含采集、转换、验证、加载等阶段。

### 核心需求

- 高吞吐量处理
- 数据质量保证
- 错误处理和重试
- 处理延迟监控

### 架构图

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  数据源   │───▶│  转换器   │───▶│  验证器   │───▶│  加载器   │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
                      │
                      ▼
               ┌──────────┐
               │ 死信队列  │
               └──────────┘
```

### 关键代码

```rust
pub struct DataPipeline {
    collector: DataCollector,
    transformer: DataTransformer,
    validator: DataValidator,
    loader: DataLoader,
    retry_handler: RetryHandler,
}

impl DataPipeline {
    pub async fn process_record(&self, record: DataRecord) -> ProcessingResult {
        // 转换
        let transformed = self.transformer.transform(record).await?;

        // 验证
        let validated = self.validator.validate(&transformed).await?;

        // 加载（带重试）
        self.retry_handler
            .execute_with_retry(|r| self.loader.load(r), validated)
            .await
    }
}
```

### 示例文件

- [数据管道场景](../examples/scenario_data_pipeline.rs)

---

## 3. 云原生/Kubernetes

### 场景描述

在 Kubernetes 集群中运行的应用程序监控。

### 核心需求

- Pod 级指标采集
- 节点健康监控
- 自动发现
- 告警管理

### 架构图

```
┌─────────────────────────────────────┐
│         Kubernetes Cluster          │
│  ┌─────────┐    ┌─────────┐        │
│  │  Pod 1  │    │  Pod 2  │        │
│  │ (App)   │    │ (App)   │        │
│  └────┬────┘    └────┬────┘        │
│       │              │              │
│       └──────────────┘              │
│              │                      │
│       ┌──────┴──────┐               │
│       │ OTLP Agent  │               │
│       └──────┬──────┘               │
│              │                      │
│       ┌──────┴──────┐               │
│       │  Collector  │               │
│       └─────────────┘               │
└─────────────────────────────────────┘
```

### 关键代码

```rust
pub struct K8sObserver {
    k8s_api: KubernetesClient,
    exporter: MetricsExporter,
    alert_manager: AlertManager,
}

impl K8sObserver {
    pub async fn collect_pod_metrics(&self, pod: &Pod) -> Vec<Metric> {
        let mut metrics = vec![];

        // CPU 使用
        metrics.push(Metric::PodMetric {
            pod_name: pod.name.clone(),
            namespace: pod.namespace.clone(),
            metric_type: PodMetricType::CpuUsage,
            value: self.k8s_api.get_cpu_usage(pod).await,
            timestamp: chrono::Utc::now(),
        });

        // 内存使用
        metrics.push(Metric::PodMetric {
            pod_name: pod.name.clone(),
            namespace: pod.namespace.clone(),
            metric_type: PodMetricType::MemoryUsage,
            value: self.k8s_api.get_memory_usage(pod).await,
            timestamp: chrono::Utc::now(),
        });

        metrics
    }
}
```

### 示例文件

- [Kubernetes 可观测性](../examples/scenario_kubernetes_observability.rs)

---

## 4. Serverless 环境

### 场景描述

在 AWS Lambda、Azure Functions 或 Google Cloud Functions 中使用。

### 核心需求

- 冷启动优化
- 快速导出（函数结束前完成）
- 资源受限环境下的高效运行

### 关键代码

```rust
use lambda_runtime::{service_fn, Error, LambdaEvent};
use serde_json::Value;

struct TelemetryGuard {
    provider: TracerProvider,
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        // 确保在函数结束前导出所有遥测数据
        self.provider.force_flush().ok();
        self.provider.shutdown().ok();
    }
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let func = service_fn(handler);
    lambda_runtime::run(func).await?;
    Ok(())
}

async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    // 初始化遥测（冷启动时执行）
    let guard = init_telemetry().await?;

    let tracer = global::tracer("lambda-handler");

    let result = tracer.in_span("process_request", |ctx| {
        // 处理请求
        process_event(event.payload)
    });

    // guard 在 drop 时自动刷新数据
    drop(guard);

    Ok(result?)
}
```

---

## 5. 边缘计算

### 场景描述

在边缘设备上运行的轻量级监控。

### 核心需求

- 极低资源占用
- 离线缓存
- 批量上传
- 网络不稳定处理

### 关键代码

```rustnpub struct EdgeExporter {
    local_storage: LocalStorage,
    batch_processor: BatchProcessor,
    connectivity_checker: ConnectivityChecker,
}

impl EdgeExporter {
    pub async fn export(&self, data: TelemetryData) -> Result<()> {
        if self.connectivity_checker.is_online().await {
            // 在线：直接发送
            self.send_to_cloud(data).await?;

            // 同时发送缓存的数据
            self.flush_local_storage().await?;
        } else {
            // 离线：本地存储
            self.local_storage.store(data).await?;
        }
        Ok(())
    }

    async fn flush_local_storage(&self) -> Result<()> {
        let cached = self.local_storage.read_all().await?;
        self.send_batch(cached).await?;
        self.local_storage.clear().await?;
        Ok(())
    }
}
```

---

## 6. 物联网 (IoT)

### 场景描述

大规模 IoT 设备遥测数据采集。

### 核心需求

- 海量设备接入
- 数据聚合
- 低功耗优化
- 时序数据处理

### 关键代码

```rustnpub struct IoTGateway {
    device_registry: DeviceRegistry,
    aggregator: MetricsAggregator,
    exporter: OTLPExporter,
}

impl IoTGateway {
    pub async fn handle_device_data(
        &self,
        device_id: &str,
        data: SensorData,
    ) -> Result<()> {
        // 验证设备
        let device = self.device_registry.get(device_id).await?;

        // 添加设备属性
        let enriched_data = data
            .with_attribute("device.model", &device.model)
            .with_attribute("device.location", &device.location);

        // 聚合
        self.aggregator.add(enriched_data).await;

        // 定期批量导出
        if self.aggregator.should_flush() {
            let batch = self.aggregator.flush().await;
            self.exporter.export_batch(batch).await?;
        }

        Ok(())
    }
}
```

---

## 7. 金融交易系统

### 场景描述

高频交易系统的低延迟监控。

### 核心需求

- 微秒级延迟
- 数据完整性
- 审计追踪
- 合规性

### 关键代码

```rustnpub struct TradingSystem {
    span_exporter: LowLatencyExporter,
    audit_log: AuditLogger,
}

impl TradingSystem {
    pub async fn execute_trade(&self, order: Order) -> Result<TradeResult> {
        let span = self.start_span("execute_trade")
            .with_attribute("order.id", &order.id)
            .with_attribute("order.symbol", &order.symbol)
            .with_attribute("order.quantity", order.quantity);

        // 风控检查
        self.risk_check(&order).await?;

        // 执行交易
        let result = self.matching_engine.execute(order.clone()).await?;

        // 审计日志
        self.audit_log.record(&order, &result).await?;

        span.finish();
        Ok(result)
    }
}

// 使用 pprof 进行性能分析
#[cfg(feature = "profiling")]
pub fn start_cpu_profiling() -> ProfilerGuard {
    pprof::ProfilerGuard::new(100).unwrap()
}
```

---

## 8. 游戏服务器

### 场景描述

多人在线游戏服务器的玩家行为追踪。

### 核心需求

- 玩家会话追踪
- 实时性能监控
- 异常检测
- 业务指标分析

### 关键代码

```rustnpub struct GameServer {
    session_manager: SessionManager,
    metrics: GameMetrics,
}

impl GameServer {
    pub async fn handle_player_action(
        &self,
        player_id: &str,
        action: GameAction,
    ) -> Result<()> {
        let session = self.session_manager.get_session(player_id).await?;

        let span = session.create_span("player_action")
            .with_attribute("action.type", format!("{:?}", action))
            .with_attribute("player.level", session.player_level)
            .with_attribute("session.duration", session.duration());

        match action {
            GameAction::Move { x, y } => {
                self.process_movement(player_id, x, y).await?;
                self.metrics.record_movement(player_id, x, y).await;
            }
            GameAction::Attack { target } => {
                self.process_attack(player_id, target).await?;
                self.metrics.record_combat(player_id, target).await;
            }
            // ...
        }

        span.finish();
        Ok(())
    }
}
```

---

## 场景选择指南

| 场景 | 主要挑战 | 推荐功能 |
|------|---------|---------|
| 微服务 | 分布式追踪 | Context 传播 |
| 数据管道 | 可靠性 | 重试、死信队列 |
| K8s | 自动发现 | 标签、选择器 |
| Serverless | 冷启动 | 快速初始化 |
| 边缘计算 | 离线处理 | 本地缓存 |
| IoT | 规模 | 数据聚合 |
| 金融 | 延迟 | 异步导出 |
| 游戏 | 实时性 | 内存优化 |

---

## 相关资源

- [微服务示例](../examples/scenario_ecommerce_microservices.rs)
- [数据管道示例](../examples/scenario_data_pipeline.rs)
- [Kubernetes 示例](../examples/scenario_kubernetes_observability.rs)
- [最佳实践](../examples/best_practices_example.rs)
