# Dapr 分布式应用运行时 - Rust + OTLP 完整集成

## 📋 目录

- [概述](#概述)
- [核心概念](#核心概念)
- [Rust 1.90 实现](#rust-190-实现)
- [OTLP 集成策略](#otlp-集成策略)
- [Building Blocks](#building-blocks)
- [服务调用](#服务调用)
- [状态管理](#状态管理)
- [发布订阅](#发布订阅)
- [最佳实践](#最佳实践)
- [完整示例](#完整示例)

---

## 概述

### 什么是 Dapr?

**Dapr**(Distributed Application Runtime)是一个可移植的、事件驱动的运行时,用于构建分布式应用:

```
┌────────────────────────────────────┐
│        Your Application            │
│         (Any Language)             │
└───────────┬────────────────────────┘
            │ HTTP/gRPC
┌───────────▼────────────────────────┐
│         Dapr Sidecar               │
│  ┌──────────────────────────────┐  │
│  │  Service Invocation          │  │
│  │  State Management            │  │
│  │  Pub/Sub                     │  │
│  │  Bindings                    │  │
│  │  Actors                      │  │
│  │  Secrets                     │  │
│  │  Configuration               │  │
│  └──────────────────────────────┘  │
└────────────────────────────────────┘
            │
            ▼
   Infrastructure (Redis/Kafka/etc.)
```

### 为什么使用 Dapr + Rust?

| 特性 | Dapr + Rust | Spring Cloud | Service Mesh |
|-----|-------------|--------------|--------------|
| **性能** | 🚀 极高 | ⚠️ 中 | ⚡ 高 |
| **语言无关** | ✅ 是 | ❌ Java Only | ✅ 是 |
| **学习曲线** | ⚡ 低 | ⚠️ 高 | ⚠️ 高 |
| **基础设施依赖** | ⚡ 低 | ⚠️ 高 | ⚠️ 高(需 K8s) |
| **可观测性** | ✅ 内置 | ⚠️ 需配置 | ✅ 内置 |

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **服务调用链** | 分布式 Trace |
| **状态操作延迟** | Histogram |
| **消息发布/订阅** | Span Events |
| **组件健康** | Metrics(gauge) |
| **错误率** | Counter(by component) |

---

## 核心概念

### 1. Dapr Building Blocks

| Building Block | 功能 | 使用场景 |
|---------------|------|---------|
| **Service Invocation** | 服务间调用(服务发现+负载均衡+重试) | 微服务通信 |
| **State Management** | 分布式状态存储(Redis/Cosmos DB/etc.) | 用户会话、缓存 |
| **Pub/Sub** | 发布订阅(Kafka/RabbitMQ/etc.) | 事件驱动 |
| **Bindings** | 输入/输出绑定(HTTP/MQTT/S3/etc.) | 外部系统集成 |
| **Actors** | 虚拟 Actor 模式 | 游戏、IoT |
| **Secrets** | 密钥管理(Vault/AWS Secrets/etc.) | 配置管理 |
| **Configuration** | 动态配置 | 特性开关 |

### 2. OTLP 追踪上下文

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use tracing::{info, instrument, warn};

pub struct DaprMetrics {
    service_invocations: Counter<u64>,
    invocation_duration: Histogram<f64>,
    state_operations: Counter<u64>,
    state_duration: Histogram<f64>,
    pubsub_published: Counter<u64>,
    pubsub_consumed: Counter<u64>,
}

impl DaprMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            service_invocations: meter
                .u64_counter("dapr.service_invocations")
                .with_description("服务调用次数")
                .init(),
            invocation_duration: meter
                .f64_histogram("dapr.invocation_duration")
                .with_description("服务调用延迟(ms)")
                .with_unit("ms")
                .init(),
            state_operations: meter
                .u64_counter("dapr.state_operations")
                .with_description("状态操作次数")
                .init(),
            state_duration: meter
                .f64_histogram("dapr.state_duration")
                .with_description("状态操作延迟(ms)")
                .with_unit("ms")
                .init(),
            pubsub_published: meter
                .u64_counter("dapr.pubsub_published")
                .with_description("发布的消息数")
                .init(),
            pubsub_consumed: meter
                .u64_counter("dapr.pubsub_consumed")
                .with_description("消费的消息数")
                .init(),
        }
    }
}
```

---

## Rust 1.90 实现

### 1. 项目设置

```toml
# Cargo.toml
[dependencies]
# Dapr SDK
dapr = "0.15"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
tonic = "0.12"
prost = "0.13"

# HTTP 客户端/服务器
axum = "0.7"
reqwest = { version = "0.12", features = ["json"] }

# OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"
```

### 2. Dapr 客户端初始化

```rust
use dapr::client::TonicClient;
use std::sync::Arc;
use tracing::{info, instrument};

pub struct DaprContext {
    pub client: dapr::Client<TonicClient>,
    pub metrics: Arc<DaprMetrics>,
}

impl DaprContext {
    #[instrument]
    pub async fn new(
        dapr_grpc_address: &str,
        metrics: Arc<DaprMetrics>,
    ) -> Result<Self, dapr::error::Error> {
        info!(address = dapr_grpc_address, "连接 Dapr Sidecar");

        let client = dapr::Client::<TonicClient>::connect(dapr_grpc_address).await?;

        info!("Dapr 客户端连接成功");

        Ok(Self { client, metrics })
    }
}
```

---

## OTLP 集成策略

### 1. 初始化 OTLP

```rust
use opentelemetry::global;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // Dapr 自动注入 Trace Context,我们只需配置导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    let meter = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .build()?;

    global::set_meter_provider(meter);

    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

---

## Building Blocks

### 1. Service Invocation(服务调用)

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateOrderRequest {
    pub user_id: i64,
    pub items: Vec<OrderItem>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: i64,
    pub quantity: u32,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateOrderResponse {
    pub order_id: String,
    pub total: f64,
}

impl DaprContext {
    #[instrument(skip(self, request), fields(
        dapr.app_id = %app_id,
        dapr.method = %method_name
    ))]
    pub async fn invoke_service<Req, Res>(
        &self,
        app_id: &str,
        method_name: &str,
        request: Req,
    ) -> Result<Res, DaprError>
    where
        Req: Serialize,
        Res: for<'de> Deserialize<'de>,
    {
        let start = std::time::Instant::now();
        self.metrics.service_invocations.add(1, &[]);

        info!(
            app_id = app_id,
            method = method_name,
            "调用服务"
        );

        let response = self
            .client
            .invoke_service(app_id, method_name, Some(request))
            .await?;

        let result: Res = serde_json::from_slice(&response)?;

        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.invocation_duration.record(elapsed, &[]);

        info!(
            app_id = app_id,
            method = method_name,
            duration_ms = elapsed,
            "服务调用成功"
        );

        Ok(result)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DaprError {
    #[error("Dapr 错误: {0}")]
    Dapr(#[from] dapr::error::Error),

    #[error("序列化错误: {0}")]
    Serialization(#[from] serde_json::Error),
}
```

### 2. State Management(状态管理)

```rust
use dapr::dapr::dapr::proto::runtime::v1::state_item::StateOptions;

impl DaprContext {
    #[instrument(skip(self, value), fields(
        dapr.store_name = %store_name,
        dapr.key = %key
    ))]
    pub async fn save_state<T: Serialize>(
        &self,
        store_name: &str,
        key: &str,
        value: &T,
    ) -> Result<(), DaprError> {
        let start = std::time::Instant::now();
        self.metrics.state_operations.add(1, &[]);

        info!(
            store = store_name,
            key = key,
            "保存状态"
        );

        let json = serde_json::to_vec(value)?;

        self.client
            .save_state(store_name, vec![(key.to_string(), json)])
            .await?;

        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.state_duration.record(elapsed, &[]);

        info!(
            store = store_name,
            key = key,
            duration_ms = elapsed,
            "状态已保存"
        );

        Ok(())
    }

    #[instrument(skip(self), fields(
        dapr.store_name = %store_name,
        dapr.key = %key
    ))]
    pub async fn get_state<T>(
        &self,
        store_name: &str,
        key: &str,
    ) -> Result<Option<T>, DaprError>
    where
        T: for<'de> Deserialize<'de>,
    {
        let start = std::time::Instant::now();
        self.metrics.state_operations.add(1, &[]);

        info!(
            store = store_name,
            key = key,
            "获取状态"
        );

        let response = self.client.get_state(store_name, key, None).await?;

        let result = if response.data.is_empty() {
            None
        } else {
            Some(serde_json::from_slice(&response.data)?)
        };

        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.state_duration.record(elapsed, &[]);

        info!(
            store = store_name,
            key = key,
            found = result.is_some(),
            duration_ms = elapsed,
            "状态查询完成"
        );

        Ok(result)
    }

    #[instrument(skip(self), fields(
        dapr.store_name = %store_name,
        dapr.key = %key
    ))]
    pub async fn delete_state(
        &self,
        store_name: &str,
        key: &str,
    ) -> Result<(), DaprError> {
        let start = std::time::Instant::now();
        self.metrics.state_operations.add(1, &[]);

        info!(
            store = store_name,
            key = key,
            "删除状态"
        );

        self.client
            .delete_state(store_name, key, None)
            .await?;

        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.state_duration.record(elapsed, &[]);

        info!(
            store = store_name,
            key = key,
            duration_ms = elapsed,
            "状态已删除"
        );

        Ok(())
    }
}
```

### 3. Pub/Sub(发布订阅)

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    pub order_id: String,
    pub user_id: i64,
    pub total: f64,
    pub timestamp: i64,
}

impl DaprContext {
    #[instrument(skip(self, event), fields(
        dapr.pubsub_name = %pubsub_name,
        dapr.topic = %topic
    ))]
    pub async fn publish_event<T: Serialize>(
        &self,
        pubsub_name: &str,
        topic: &str,
        event: &T,
    ) -> Result<(), DaprError> {
        let start = std::time::Instant::now();
        self.metrics.pubsub_published.add(1, &[]);

        info!(
            pubsub = pubsub_name,
            topic = topic,
            "发布事件"
        );

        let json = serde_json::to_vec(event)?;

        self.client
            .publish_event(pubsub_name, topic, "application/json", json)
            .await?;

        info!(
            pubsub = pubsub_name,
            topic = topic,
            "事件已发布"
        );

        Ok(())
    }
}

// 订阅处理器
use axum::{
    extract::{Json, State},
    http::StatusCode,
    response::IntoResponse,
    routing::post,
    Router,
};

#[derive(Debug, Deserialize)]
struct DaprSubscription {
    pubsubname: String,
    topic: String,
    route: String,
}

#[derive(Debug, Deserialize)]
struct DaprCloudEvent<T> {
    id: String,
    source: String,
    #[serde(rename = "type")]
    event_type: String,
    specversion: String,
    datacontenttype: String,
    data: T,
}

async fn subscribe_handler() -> impl IntoResponse {
    let subscriptions = vec![DaprSubscription {
        pubsubname: "pubsub".to_string(),
        topic: "orders".to_string(),
        route: "/events/orders".to_string(),
    }];

    Json(subscriptions)
}

async fn order_event_handler(
    State(ctx): State<Arc<DaprContext>>,
    Json(cloud_event): Json<DaprCloudEvent<OrderCreatedEvent>>,
) -> impl IntoResponse {
    ctx.metrics.pubsub_consumed.add(1, &[]);

    info!(
        event_id = %cloud_event.id,
        order_id = %cloud_event.data.order_id,
        "收到订单事件"
    );

    // 处理事件
    match handle_order_created(cloud_event.data).await {
        Ok(_) => {
            info!(event_id = %cloud_event.id, "事件处理成功");
            StatusCode::OK
        }
        Err(err) => {
            tracing::error!(error = %err, "事件处理失败");
            StatusCode::INTERNAL_SERVER_ERROR
        }
    }
}

#[instrument]
async fn handle_order_created(event: OrderCreatedEvent) -> Result<(), Box<dyn std::error::Error>> {
    info!(order_id = %event.order_id, "处理订单创建事件");

    // 业务逻辑...

    Ok(())
}
```

---

## 服务调用

### 1. 订单服务(发起调用)

```rust
use axum::{
    extract::{Json, State},
    http::StatusCode,
    routing::post,
    Router,
};

#[derive(Clone)]
struct AppState {
    dapr: Arc<DaprContext>,
}

async fn create_order_handler(
    State(state): State<AppState>,
    Json(request): Json<CreateOrderRequest>,
) -> Result<Json<CreateOrderResponse>, StatusCode> {
    info!(user_id = request.user_id, "创建订单");

    // 1. 调用库存服务检查库存
    let inventory_check = state
        .dapr
        .invoke_service::<_, InventoryCheckResponse>(
            "inventory-service",
            "check",
            &request.items,
        )
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    if !inventory_check.available {
        return Err(StatusCode::BAD_REQUEST);
    }

    // 2. 创建订单
    let order_id = uuid::Uuid::new_v4().to_string();
    let total = request.items.iter().map(|i| i.quantity as f64 * 10.0).sum();

    let order = Order {
        id: order_id.clone(),
        user_id: request.user_id,
        items: request.items,
        total,
    };

    // 3. 保存订单状态
    state
        .dapr
        .save_state("statestore", &format!("order:{}", order_id), &order)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // 4. 发布订单创建事件
    let event = OrderCreatedEvent {
        order_id: order_id.clone(),
        user_id: order.user_id,
        total: order.total,
        timestamp: chrono::Utc::now().timestamp(),
    };

    state
        .dapr
        .publish_event("pubsub", "orders", &event)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(Json(CreateOrderResponse {
        order_id,
        total,
    }))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;

    let meter = opentelemetry::global::meter("order_service");
    let metrics = Arc::new(DaprMetrics::new(&meter));

    let dapr = Arc::new(DaprContext::new("http://localhost:50001", metrics).await?);

    let app_state = AppState { dapr };

    let app = Router::new()
        .route("/orders", post(create_order_handler))
        .route("/dapr/subscribe", axum::routing::get(subscribe_handler))
        .route("/events/orders", post(order_event_handler))
        .with_state(app_state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("订单服务运行在 http://localhost:3000");

    axum::serve(listener, app).await?;

    Ok(())
}
```

---

## 状态管理

### 1. 会话管理

```rust
#[derive(Debug, Serialize, Deserialize)]
struct UserSession {
    user_id: i64,
    username: String,
    login_at: i64,
    expires_at: i64,
}

impl DaprContext {
    #[instrument(skip(self))]
    pub async fn create_session(
        &self,
        user_id: i64,
        username: String,
    ) -> Result<String, DaprError> {
        let session_id = uuid::Uuid::new_v4().to_string();
        let now = chrono::Utc::now().timestamp();

        let session = UserSession {
            user_id,
            username,
            login_at: now,
            expires_at: now + 3600, // 1 小时
        };

        self.save_state("statestore", &format!("session:{}", session_id), &session)
            .await?;

        info!(
            session_id = %session_id,
            user_id = user_id,
            "会话已创建"
        );

        Ok(session_id)
    }

    #[instrument(skip(self))]
    pub async fn get_session(
        &self,
        session_id: &str,
    ) -> Result<Option<UserSession>, DaprError> {
        let session: Option<UserSession> = self
            .get_state("statestore", &format!("session:{}", session_id))
            .await?;

        if let Some(ref s) = session {
            let now = chrono::Utc::now().timestamp();
            if s.expires_at < now {
                info!(session_id = %session_id, "会话已过期");
                self.delete_state("statestore", &format!("session:{}", session_id))
                    .await?;
                return Ok(None);
            }
        }

        Ok(session)
    }
}
```

---

## 发布订阅

### 1. 事件驱动架构

```
[Order Service] --publish--> [Dapr Pub/Sub] --subscribe--> [Inventory Service]
                                    │
                                    ├--subscribe--> [Payment Service]
                                    │
                                    └--subscribe--> [Notification Service]
```

### 2. 库存服务(订阅者)

```rust
async fn inventory_event_handler(
    State(ctx): State<Arc<DaprContext>>,
    Json(cloud_event): Json<DaprCloudEvent<OrderCreatedEvent>>,
) -> impl IntoResponse {
    info!(order_id = %cloud_event.data.order_id, "处理库存扣减");

    // 扣减库存逻辑...

    StatusCode::OK
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;

    let meter = opentelemetry::global::meter("inventory_service");
    let metrics = Arc::new(DaprMetrics::new(&meter));

    let dapr = Arc::new(DaprContext::new("http://localhost:50002", metrics).await?);

    let app_state = AppState { dapr };

    let app = Router::new()
        .route("/dapr/subscribe", axum::routing::get(inventory_subscribe_handler))
        .route("/events/orders", post(inventory_event_handler))
        .with_state(app_state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await?;
    info!("库存服务运行在 http://localhost:3001");

    axum::serve(listener, app).await?;

    Ok(())
}
```

---

## 最佳实践

### 1. 重试策略

```yaml
# components/pubsub.yaml
apiVersion: dapr.io/v1alpha1
kind: Component
metadata:
  name: pubsub
spec:
  type: pubsub.redis
  version: v1
  metadata:
    - name: redisHost
      value: localhost:6379
    - name: redisPassword
      value: ""
    - name: maxRetries
      value: "3"
    - name: maxRetryBackoff
      value: "5s"
```

### 2. 错误处理

```rust
async fn resilient_invoke<Req, Res>(
    ctx: &DaprContext,
    app_id: &str,
    method: &str,
    request: Req,
) -> Result<Res, DaprError>
where
    Req: Serialize + Clone,
    Res: for<'de> Deserialize<'de>,
{
    let mut retries = 0;
    const MAX_RETRIES: u32 = 3;

    loop {
        match ctx.invoke_service(app_id, method, request.clone()).await {
            Ok(response) => return Ok(response),
            Err(err) => {
                retries += 1;
                if retries >= MAX_RETRIES {
                    return Err(err);
                }

                warn!(
                    app_id = app_id,
                    method = method,
                    retry = retries,
                    error = %err,
                    "服务调用失败,重试中"
                );

                tokio::time::sleep(tokio::time::Duration::from_secs(1 << retries)).await;
            }
        }
    }
}
```

---

## 完整示例

### 1. Dapr 组件配置

```yaml
# components/statestore.yaml
apiVersion: dapr.io/v1alpha1
kind: Component
metadata:
  name: statestore
spec:
  type: state.redis
  version: v1
  metadata:
    - name: redisHost
      value: localhost:6379
    - name: redisPassword
      value: ""
    - name: actorStateStore
      value: "true"

---
# components/pubsub.yaml
apiVersion: dapr.io/v1alpha1
kind: Component
metadata:
  name: pubsub
spec:
  type: pubsub.redis
  version: v1
  metadata:
    - name: redisHost
      value: localhost:6379
    - name: redisPassword
      value: ""

---
# components/tracing.yaml
apiVersion: dapr.io/v1alpha1
kind: Component
metadata:
  name: tracing
spec:
  type: exporters.otlp
  version: v1
  metadata:
    - name: endpoint
      value: http://localhost:4317
    - name: protocol
      value: grpc
```

### 2. Docker Compose 部署

```yaml
version: '3.8'

services:
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  order-service:
    build: ./order-service
    ports:
      - "3000:3000"
    environment:
      DAPR_HTTP_PORT: 3500
      DAPR_GRPC_PORT: 50001
      OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
    depends_on:
      - redis
      - otel-collector

  order-service-dapr:
    image: "daprio/daprd:1.14.0"
    command: [
      "./daprd",
      "-app-id", "order-service",
      "-app-port", "3000",
      "-dapr-http-port", "3500",
      "-dapr-grpc-port", "50001",
      "-components-path", "/components",
      "-config", "/config/dapr-config.yaml"
    ]
    volumes:
      - "./components:/components"
      - "./config:/config"
    depends_on:
      - order-service
    network_mode: "service:order-service"

  inventory-service:
    build: ./inventory-service
    ports:
      - "3001:3001"
    environment:
      DAPR_HTTP_PORT: 3501
      DAPR_GRPC_PORT: 50002
      OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
    depends_on:
      - redis
      - otel-collector

  inventory-service-dapr:
    image: "daprio/daprd:1.14.0"
    command: [
      "./daprd",
      "-app-id", "inventory-service",
      "-app-port", "3001",
      "-dapr-http-port", "3501",
      "-dapr-grpc-port", "50002",
      "-components-path", "/components",
      "-config", "/config/dapr-config.yaml"
    ]
    volumes:
      - "./components:/components"
      - "./config:/config"
    depends_on:
      - inventory-service
    network_mode: "service:inventory-service"

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.98.0
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]
    ports:
      - "4317:4317"

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
```

---

## 总结

### 核心要点

1. **Dapr Building Blocks**: 服务调用、状态管理、发布订阅
2. **OTLP 全链路追踪**: Dapr 自动传播 Trace Context
3. **语言无关**: Rust 通过 HTTP/gRPC 与 Dapr Sidecar 通信
4. **基础设施抽象**: 切换 Redis/Kafka 无需改代码
5. **生产就绪**: 内置重试、超时、熔断

### 性能对比

| 指标 | Dapr + Rust | Spring Cloud | Service Mesh |
|-----|-------------|--------------|--------------|
| **服务调用延迟** | +2ms | +15ms | +5ms |
| **内存占用(Sidecar)** | 25MB | N/A | 50MB |
| **启动时间** | 100ms | 3s | 500ms |
| **吞吐量影响** | <5% | <20% | <10% |

### 下一步

- **Dapr Actors**: 虚拟 Actor 模式实现
- **Dapr Workflows**: 工作流编排(Saga)
- **安全**: mTLS + API Token
- **多云部署**: AWS/Azure/GCP 统一接口

---

## 参考资料

- [Dapr 官方文档](https://docs.dapr.io/)
- [Dapr Rust SDK](https://github.com/dapr/rust-sdk)
- [Dapr + OpenTelemetry](https://docs.dapr.io/operations/observability/tracing/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Dapr 版本**: 1.14+  
**OpenTelemetry**: 0.30+

