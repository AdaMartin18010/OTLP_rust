# 分布式追踪进阶 - Rust 完整版

## 目录

- [分布式追踪进阶 - Rust 完整版](#分布式追踪进阶---rust-完整版)
  - [目录](#目录)
  - [1. 分布式追踪架构](#1-分布式追踪架构)
    - [1.1 调用链示例](#11-调用链示例)
    - [1.2 核心概念](#12-核心概念)
  - [2. 跨服务追踪](#2-跨服务追踪)
    - [2.1 HTTP 传播](#21-http-传播)
    - [2.2 gRPC 传播](#22-grpc-传播)
    - [2.3 消息队列传播](#23-消息队列传播)
  - [3. Span 关系管理](#3-span-关系管理)
    - [3.1 父子 Span](#31-父子-span)
    - [3.2 兄弟 Span](#32-兄弟-span)
    - [3.3 跟随 Span (FollowsFrom)](#33-跟随-span-followsfrom)
  - [4. 上下文传播详解](#4-上下文传播详解)
    - [4.1 W3C Trace Context](#41-w3c-trace-context)
    - [4.2 Baggage 传播](#42-baggage-传播)
    - [4.3 自定义传播器](#43-自定义传播器)
  - [5. 异步任务追踪](#5-异步任务追踪)
    - [5.1 Tokio Task 追踪](#51-tokio-task-追踪)
    - [5.2 跨 Task 上下文传递](#52-跨-task-上下文传递)
    - [5.3 并行任务追踪](#53-并行任务追踪)
  - [6. 复杂场景处理](#6-复杂场景处理)
    - [6.1 重试机制追踪](#61-重试机制追踪)
    - [6.2 断路器追踪](#62-断路器追踪)
    - [6.3 分布式事务追踪](#63-分布式事务追踪)
  - [7. 性能优化](#7-性能优化)
    - [7.1 Span 复用](#71-span-复用)
    - [7.2 惰性属性](#72-惰性属性)
    - [7.3 采样策略](#73-采样策略)
  - [8. 微服务追踪架构](#8-微服务追踪架构)
    - [8.1 服务网格集成](#81-服务网格集成)
    - [8.2 API Gateway 追踪](#82-api-gateway-追踪)
  - [9. 调试与可视化](#9-调试与可视化)
    - [9.1 Jaeger 查询](#91-jaeger-查询)
    - [9.2 依赖关系图](#92-依赖关系图)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
    - [10.1 完整微服务示例](#101-完整微服务示例)
    - [10.2 Docker Compose 部署](#102-docker-compose-部署)
  - [11. Rust 1.90 高级特性](#11-rust-190-高级特性)
    - [11.1 AFIT 在追踪中间件](#111-afit-在追踪中间件)
    - [11.2 RPITIT 在 Span 管理](#112-rpitit-在-span-管理)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能指标](#性能指标)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 分布式追踪架构

### 1.1 调用链示例

````text
用户请求 → API Gateway → User Service → Database
                      ↓
                Order Service → Kafka → Notification Service
                      ↓
                Payment Service → External API
````

**Trace 结构**:

````text
Trace (trace_id: abc123)
├─ Span 1: API Gateway [root]
│  ├─ Span 2: User Service
│  │  └─ Span 3: PostgreSQL Query
│  └─ Span 4: Order Service
│     ├─ Span 5: Kafka Publish
│     └─ Span 6: Payment Service
│        └─ Span 7: External API Call
└─ Span 8: Notification Service (FollowsFrom Span 5)
````

### 1.2 核心概念

- **Trace**: 完整的分布式调用链，唯一的 `trace_id`
- **Span**: 单个操作单元，唯一的 `span_id`
- **Parent Span**: 调用方 Span
- **Child Span**: 被调用方 Span
- **SpanContext**: 包含 `trace_id`、`span_id`、`trace_flags`、`trace_state`

---

## 2. 跨服务追踪

### 2.1 HTTP 传播

**服务 A (调用方)**:

````rust
use reqwest::{Client, header::HeaderMap};
use opentelemetry::global;
use opentelemetry::propagation::Injector;
use tracing::{info, instrument};

struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}

#[instrument(name = "service_a.call_service_b")]
pub async fn call_service_b(client: &Client) -> Result<String, anyhow::Error> {
    let mut headers = HeaderMap::new();

    // 注入追踪上下文到 HTTP Header
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut HeaderInjector(&mut headers),
        );
    });

    info!("Calling Service B with trace context");

    let response = client
        .get("http://service-b:8080/api/data")
        .headers(headers)
        .send()
        .await?;

    let body = response.text().await?;
    Ok(body)
}
````

**服务 B (被调用方)**:

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
    Router,
};
use opentelemetry::global;
use opentelemetry::propagation::Extractor;
use tracing::{info, info_span, Instrument};

struct HeaderExtractor<'a>(&'a axum::http::HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key)?.to_str().ok()
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

async fn trace_middleware(request: Request, next: Next) -> Response {
    // 从 HTTP Header 提取追踪上下文
    let parent_context = global::get_text_map_propagator(|propagator| {
        propagator.extract(&HeaderExtractor(request.headers()))
    });

    // 创建新的 Span 并关联父上下文
    let span = info_span!(
        "service_b.handle_request",
        "http.method" = %request.method(),
        "http.url" = %request.uri(),
    );

    span.in_scope(|| {
        info!("Received request with trace context");
    });

    async move { next.run(request).await }
        .instrument(span)
        .await
}

pub fn app() -> Router {
    Router::new()
        .route("/api/data", axum::routing::get(handler))
        .layer(middleware::from_fn(trace_middleware))
}

async fn handler() -> &'static str {
    info!("Processing request in Service B");
    "Response from Service B"
}
````

### 2.2 gRPC 传播

**客户端拦截器**:

````rust
use tonic::{Request, Status, metadata::MetadataMap};
use opentelemetry::global;
use opentelemetry::propagation::Injector;

struct MetadataInjector<'a>(&'a mut MetadataMap);

impl<'a> Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.0.insert(key, val);
            }
        }
    }
}

#[tracing::instrument(name = "grpc.client.call", skip(request))]
pub async fn call_grpc_service<T>(
    mut request: Request<T>,
) -> Request<T> {
    // 注入追踪上下文到 gRPC Metadata
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut MetadataInjector(request.metadata_mut()),
        );
    });

    tracing::info!("Sending gRPC request with trace context");
    request
}
````

**服务端拦截器**:

````rust
use tonic::{Request, Response, Status};
use opentelemetry::global;
use opentelemetry::propagation::Extractor;
use tracing::{info_span, Instrument};

struct MetadataExtractor<'a>(&'a tonic::metadata::MetadataMap);

impl<'a> Extractor for MetadataExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key)?.to_str().ok()
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

pub async fn trace_interceptor<T>(
    request: Request<T>,
) -> Result<Request<T>, Status> {
    // 从 gRPC Metadata 提取追踪上下文
    let parent_context = global::get_text_map_propagator(|propagator| {
        propagator.extract(&MetadataExtractor(request.metadata()))
    });

    let span = info_span!("grpc.server.handle_request");
    span.in_scope(|| {
        tracing::info!("Received gRPC request with trace context");
    });

    Ok(request)
}
````

### 2.3 消息队列传播

**Kafka Producer (发布消息)**:

````rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::message::OwnedHeaders;
use opentelemetry::global;
use opentelemetry::propagation::Injector;
use tracing::{info, instrument};

struct KafkaHeaderInjector<'a>(&'a mut OwnedHeaders);

impl<'a> Injector for KafkaHeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(rdkafka::message::Header {
            key,
            value: Some(value.as_bytes()),
        });
    }
}

#[instrument(name = "kafka.publish", skip(producer))]
pub async fn publish_order_event(
    producer: &FutureProducer,
    order_id: &str,
) -> Result<(), anyhow::Error> {
    let mut headers = OwnedHeaders::new();

    // 注入追踪上下文到 Kafka Headers
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut KafkaHeaderInjector(&mut headers),
        );
    });

    info!(order_id, "Publishing order event to Kafka");

    let payload = format!(r#"{{"order_id": "{}"}}"#, order_id);
    let record = FutureRecord::to("orders")
        .key(order_id)
        .payload(&payload)
        .headers(headers);

    producer.send(record, std::time::Duration::from_secs(5)).await
        .map_err(|(e, _)| anyhow::anyhow!("Kafka send error: {:?}", e))?;

    Ok(())
}
````

**Kafka Consumer (消费消息)**:

````rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;
use opentelemetry::global;
use opentelemetry::propagation::Extractor;
use tracing::{info, info_span, Instrument};

struct KafkaHeaderExtractor<'a>(&'a rdkafka::message::BorrowedHeaders<'a>);

impl<'a> Extractor for KafkaHeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        for header in self.0.iter() {
            if header.key == key {
                return header.value.and_then(|v| std::str::from_utf8(v).ok());
            }
        }
        None
    }

    fn keys(&self) -> Vec<&str> {
        self.0.iter().map(|h| h.key).collect()
    }
}

pub async fn consume_orders(consumer: StreamConsumer) {
    loop {
        match consumer.recv().await {
            Ok(message) => {
                // 从 Kafka Headers 提取追踪上下文
                let parent_context = if let Some(headers) = message.headers() {
                    global::get_text_map_propagator(|propagator| {
                        propagator.extract(&KafkaHeaderExtractor(headers))
                    })
                } else {
                    opentelemetry::Context::current()
                };

                let span = info_span!(
                    "kafka.consume",
                    "messaging.system" = "kafka",
                    "messaging.destination" = "orders",
                );

                async {
                    if let Some(payload) = message.payload_view::<str>().ok().flatten() {
                        info!(payload, "Processing order event");
                        // 处理消息...
                    }
                }
                .instrument(span)
                .await;
            }
            Err(e) => {
                tracing::error!(error = %e, "Kafka consume error");
            }
        }
    }
}
````

---

## 3. Span 关系管理

### 3.1 父子 Span

````rust
use tracing::{info, instrument};

#[instrument(name = "process_order")]
pub async fn process_order(order_id: &str) -> Result<(), anyhow::Error> {
    info!(order_id, "Processing order");

    // 子 Span：验证订单
    validate_order(order_id).await?;

    // 子 Span：扣减库存
    deduct_inventory(order_id).await?;

    // 子 Span：创建支付
    create_payment(order_id).await?;

    info!(order_id, "Order processed successfully");
    Ok(())
}

#[instrument(name = "validate_order")]
async fn validate_order(order_id: &str) -> Result<(), anyhow::Error> {
    info!(order_id, "Validating order");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}

#[instrument(name = "deduct_inventory")]
async fn deduct_inventory(order_id: &str) -> Result<(), anyhow::Error> {
    info!(order_id, "Deducting inventory");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}

#[instrument(name = "create_payment")]
async fn create_payment(order_id: &str) -> Result<(), anyhow::Error> {
    info!(order_id, "Creating payment");
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    Ok(())
}
````

### 3.2 兄弟 Span

````rust
use tracing::{info, info_span, Instrument};

pub async fn parallel_operations() {
    let span1 = info_span!("operation_1");
    let span2 = info_span!("operation_2");

    let task1 = async {
        info!("Executing operation 1");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
    .instrument(span1);

    let task2 = async {
        info!("Executing operation 2");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
    .instrument(span2);

    // 两个 Span 并行执行（兄弟关系）
    tokio::join!(task1, task2);
}
````

### 3.3 跟随 Span (FollowsFrom)

````rust
use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};
use opentelemetry::global;
use tracing::info;

pub async fn publish_with_followsfrom() {
    let tracer = global::tracer("my-service");

    // 父 Span：发布消息
    let parent_span = tracer
        .span_builder("kafka.publish")
        .with_kind(SpanKind::Producer)
        .start(&tracer);

    let parent_context = opentelemetry::Context::current_with_span(parent_span);

    // 子 Span (FollowsFrom)：异步处理
    let child_span = tracer
        .span_builder("async.process")
        .with_kind(SpanKind::Consumer)
        .start_with_context(&tracer, &parent_context);

    let _guard = child_span.attach();
    info!("Processing message asynchronously");
}
````

---

## 4. 上下文传播详解

### 4.1 W3C Trace Context

**Header 格式**:

````text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
             └─ version   trace_id (32 hex)          span_id (16 hex)    flags

tracestate: vendor1=value1,vendor2=value2
````

**Rust 实现**:

````rust
use opentelemetry::propagation::TextMapPropagator;
use opentelemetry_sdk::propagation::TraceContextPropagator;

pub fn init_w3c_propagator() {
    let propagator = TraceContextPropagator::new();
    opentelemetry::global::set_text_map_propagator(propagator);
}
````

### 4.2 Baggage 传播

````rust
use opentelemetry::baggage::BaggageExt;
use opentelemetry::Context;
use tracing::{info, instrument};

#[instrument]
pub async fn service_a() {
    // 设置 Baggage
    let context = Context::current()
        .with_baggage(vec![
            ("user.id".to_string(), "12345".to_string()),
            ("user.role".to_string(), "admin".to_string()),
        ]);

    let _guard = context.attach();

    info!("Service A: Baggage set");
    service_b().await;
}

#[instrument]
async fn service_b() {
    // 读取 Baggage
    let context = Context::current();
    if let Some(user_id) = context.get("user.id") {
        info!(user_id = %user_id, "Service B: Baggage received");
    }
}
````

### 4.3 自定义传播器

````rust
use opentelemetry::{
    propagation::{Extractor, Injector, TextMapPropagator},
    Context,
};

pub struct CustomPropagator;

impl TextMapPropagator for CustomPropagator {
    fn inject_context(&self, context: &Context, injector: &mut dyn Injector) {
        // 自定义注入逻辑
        if let Some(span) = context.span().span_context() {
            injector.set(
                "x-custom-trace-id",
                span.trace_id().to_string(),
            );
            injector.set(
                "x-custom-span-id",
                span.span_id().to_string(),
            );
        }
    }

    fn extract_with_context(
        &self,
        context: &Context,
        extractor: &dyn Extractor,
    ) -> Context {
        // 自定义提取逻辑
        let trace_id = extractor.get("x-custom-trace-id");
        let span_id = extractor.get("x-custom-span-id");
        // ... 解析并创建新的 SpanContext
        context.clone()
    }

    fn fields(&self) -> Vec<String> {
        vec![
            "x-custom-trace-id".to_string(),
            "x-custom-span-id".to_string(),
        ]
    }
}
````

---

## 5. 异步任务追踪

### 5.1 Tokio Task 追踪

````rust
use tracing::{info, info_span, Instrument};

pub async fn spawn_traced_tasks() {
    let parent_span = info_span!("parent_task");

    // 方法 1: 使用 Instrument trait
    tokio::spawn(
        async {
            info!("Task 1 executing");
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
        .instrument(parent_span.clone())
    );

    // 方法 2: 手动传递 Span
    let span = parent_span.clone();
    tokio::spawn(async move {
        let _enter = span.enter();
        info!("Task 2 executing");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    });
}
````

### 5.2 跨 Task 上下文传递

````rust
use opentelemetry::Context;
use tracing::{info, Span};

pub async fn pass_context_across_tasks() {
    // 保存当前上下文
    let context = Context::current();
    let span = Span::current();

    tokio::spawn(async move {
        // 在新 Task 中恢复上下文
        let _guard = context.attach();
        let _enter = span.enter();

        info!("Executing in spawned task with parent context");
    });
}
````

### 5.3 并行任务追踪

````rust
use futures::future::join_all;
use tracing::{info, info_span, Instrument};

pub async fn parallel_traced_tasks() {
    let tasks: Vec<_> = (0..5)
        .map(|i| {
            let span = info_span!("parallel_task", task_id = i);
            async move {
                info!(task_id = i, "Task started");
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                info!(task_id = i, "Task completed");
                i
            }
            .instrument(span)
        })
        .collect();

    let results = join_all(tasks).await;
    info!(?results, "All tasks completed");
}
````

---

## 6. 复杂场景处理

### 6.1 重试机制追踪

````rust
use tracing::{error, info, warn, instrument};

#[instrument(name = "api.call_with_retry", skip(client))]
pub async fn call_with_retry(
    client: &reqwest::Client,
    url: &str,
    max_retries: u32,
) -> Result<String, anyhow::Error> {
    let mut attempts = 0;

    loop {
        attempts += 1;
        info!(attempt = attempts, url, "Attempting API call");

        match client.get(url).send().await {
            Ok(response) => {
                info!(attempt = attempts, status = response.status().as_u16(), "API call successful");
                return Ok(response.text().await?);
            }
            Err(e) if attempts < max_retries => {
                warn!(
                    attempt = attempts,
                    error = %e,
                    "API call failed, retrying"
                );
                tokio::time::sleep(tokio::time::Duration::from_secs(2_u64.pow(attempts))).await;
            }
            Err(e) => {
                error!(
                    attempt = attempts,
                    error = %e,
                    "API call failed after max retries"
                );
                return Err(e.into());
            }
        }
    }
}
````

### 6.2 断路器追踪

````rust
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::{error, info, warn, instrument};

#[derive(Clone)]
pub struct CircuitBreaker {
    failure_count: Arc<Mutex<u32>>,
    threshold: u32,
    state: Arc<Mutex<CircuitState>>,
}

#[derive(Clone, PartialEq)]
enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub fn new(threshold: u32) -> Self {
        Self {
            failure_count: Arc::new(Mutex::new(0)),
            threshold,
            state: Arc::new(Mutex::new(CircuitState::Closed)),
        }
    }

    #[instrument(name = "circuit_breaker.execute", skip(self, f))]
    pub async fn execute<F, T, E>(&self, f: F) -> Result<T, anyhow::Error>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        let state = self.state.lock().await.clone();

        match state {
            CircuitState::Open => {
                warn!("Circuit breaker is OPEN, rejecting request");
                return Err(anyhow::anyhow!("Circuit breaker is open"));
            }
            CircuitState::HalfOpen => {
                info!("Circuit breaker is HALF-OPEN, trying request");
            }
            CircuitState::Closed => {
                info!("Circuit breaker is CLOSED, processing request");
            }
        }

        match f.await {
            Ok(result) => {
                *self.failure_count.lock().await = 0;
                *self.state.lock().await = CircuitState::Closed;
                info!("Request succeeded, circuit breaker reset");
                Ok(result)
            }
            Err(e) => {
                let mut count = self.failure_count.lock().await;
                *count += 1;

                if *count >= self.threshold {
                    *self.state.lock().await = CircuitState::Open;
                    error!(failure_count = *count, "Circuit breaker opened");
                }

                Err(anyhow::anyhow!("Request failed: {}", e))
            }
        }
    }
}
````

### 6.3 分布式事务追踪

````rust
use tracing::{error, info, instrument, Span};
use sqlx::{PgPool, Postgres, Transaction};

#[instrument(name = "distributed_transaction", skip(pool))]
pub async fn execute_distributed_transaction(
    pool: &PgPool,
) -> Result<(), anyhow::Error> {
    info!("Starting distributed transaction");

    // 开始事务
    let mut tx = pool.begin().await?;
    Span::current().record("transaction.started", true);

    // 操作 1: 更新订单
    if let Err(e) = update_order(&mut tx, "ORD-001").await {
        error!(error = %e, "Failed to update order, rolling back");
        tx.rollback().await?;
        return Err(e);
    }

    // 操作 2: 扣减库存
    if let Err(e) = deduct_inventory(&mut tx, "PROD-001").await {
        error!(error = %e, "Failed to deduct inventory, rolling back");
        tx.rollback().await?;
        return Err(e);
    }

    // 提交事务
    tx.commit().await?;
    info!("Distributed transaction committed");

    Ok(())
}

#[instrument(name = "update_order", skip(tx))]
async fn update_order(
    tx: &mut Transaction<'_, Postgres>,
    order_id: &str,
) -> Result<(), anyhow::Error> {
    info!(order_id, "Updating order");
    sqlx::query("UPDATE orders SET status = 'paid' WHERE id = $1")
        .bind(order_id)
        .execute(&mut **tx)
        .await?;
    Ok(())
}

#[instrument(name = "deduct_inventory", skip(tx))]
async fn deduct_inventory(
    tx: &mut Transaction<'_, Postgres>,
    product_id: &str,
) -> Result<(), anyhow::Error> {
    info!(product_id, "Deducting inventory");
    sqlx::query("UPDATE inventory SET quantity = quantity - 1 WHERE product_id = $1")
        .bind(product_id)
        .execute(&mut **tx)
        .await?;
    Ok(())
}
````

---

## 7. 性能优化

### 7.1 Span 复用

````rust
use tracing::{info, Span};

pub async fn reuse_span() {
    let span = tracing::info_span!("database_operation");

    for i in 0..10 {
        let _enter = span.enter();
        info!(iteration = i, "Executing query");
        // 执行数据库查询...
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}
````

### 7.2 惰性属性

````rust
use tracing::{info, info_span};

pub async fn lazy_attributes() {
    let span = info_span!("process_request");
    let _enter = span.enter();

    // 仅在需要时记录昂贵的属性
    if tracing::enabled!(tracing::Level::DEBUG) {
        let expensive_data = compute_expensive_data();
        span.record("debug.data", expensive_data.as_str());
    }

    info!("Request processed");
}

fn compute_expensive_data() -> String {
    "expensive_computation_result".to_string()
}
````

### 7.3 采样策略

````rust
use opentelemetry::trace::TraceId;
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct AdaptiveSampler {
    base_probability: f64,
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 高优先级请求总是采样
        if attributes.iter().any(|kv| kv.key.as_str() == "priority" && kv.value.as_str() == "high") {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: None,
            };
        }

        // 基于 trace_id 的概率采样
        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < self.base_probability {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: Vec::new(),
                trace_state: None,
            }
        }
    }
}
````

---

## 8. 微服务追踪架构

### 8.1 服务网格集成

````rust
// Istio/Linkerd 自动注入 Sidecar 后，只需配置传播器
use opentelemetry_sdk::propagation::TraceContextPropagator;

pub fn init_service_mesh_tracing() {
    opentelemetry::global::set_text_map_propagator(
        TraceContextPropagator::new()
    );
}
````

### 8.2 API Gateway 追踪

````rust
use axum::{
    extract::{Request, Path},
    middleware::{self, Next},
    response::Response,
    Router,
    routing::get,
};
use tracing::{info, info_span, Instrument};
use opentelemetry::global;

async fn gateway_middleware(request: Request, next: Next) -> Response {
    // 创建根 Span
    let span = info_span!(
        "api_gateway",
        "http.method" = %request.method(),
        "http.url" = %request.uri(),
        "http.route" = tracing::field::Empty,
    );

    let response = async move {
        info!("Incoming request to API Gateway");
        next.run(request).await
    }
    .instrument(span)
    .await;

    response
}

async fn proxy_to_service_a() -> &'static str {
    info!("Proxying to Service A");
    // 调用 Service A...
    "Response from Service A"
}

async fn proxy_to_service_b() -> &'static str {
    info!("Proxying to Service B");
    // 调用 Service B...
    "Response from Service B"
}

pub fn app() -> Router {
    Router::new()
        .route("/service-a/*path", get(proxy_to_service_a))
        .route("/service-b/*path", get(proxy_to_service_b))
        .layer(middleware::from_fn(gateway_middleware))
}
````

---

## 9. 调试与可视化

### 9.1 Jaeger 查询

````bash
# 按 Trace ID 查询
curl "http://localhost:16686/api/traces/4bf92f3577b34da6a3ce929d0e0e4736"

# 按服务名查询
curl "http://localhost:16686/api/traces?service=my-service&limit=20"

# 按标签查询
curl "http://localhost:16686/api/traces?service=my-service&tags={\"http.status_code\":\"500\"}"
````

### 9.2 依赖关系图

Jaeger UI 自动生成服务依赖关系图：

````text
API Gateway → User Service → PostgreSQL
           ↓
           Order Service → Kafka
           ↓
           Payment Service → External API
````

---

## 10. 生产环境最佳实践

### 10.1 完整微服务示例

````rust
// src/tracing.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{RandomIdGenerator, Sampler, Tracer},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_tracing(service_name: &str) -> anyhow::Result<()> {
    // 创建 OTLP 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1))))
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 设置全局 Tracer
    global::set_tracer_provider(tracer.provider().unwrap());

    // 初始化 tracing-subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

pub fn shutdown_tracing() {
    global::shutdown_tracer_provider();
}
````

### 10.2 Docker Compose 部署

````yaml
version: '3.8'
services:
  api-gateway:
    build: ./api-gateway
    environment:
      - SERVICE_NAME=api-gateway
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    ports:
      - "8080:8080"
    depends_on:
      - otel-collector

  service-a:
    build: ./service-a
    environment:
      - SERVICE_NAME=service-a
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317

  service-b:
    build: ./service-b
    environment:
      - SERVICE_NAME=service-b
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317

  otel-collector:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "14250:14250"
    environment:
      - COLLECTOR_OTLP_ENABLED=true
````

---

## 11. Rust 1.90 高级特性

### 11.1 AFIT 在追踪中间件

````rust
// Rust 1.90: async fn in Traits (AFIT)
pub trait TracedService {
    async fn call(&self, request: &str) -> Result<String, anyhow::Error>;
}

pub struct UserService;

impl TracedService for UserService {
    #[tracing::instrument(name = "user_service.call", skip(self))]
    async fn call(&self, request: &str) -> Result<String, anyhow::Error> {
        tracing::info!(request, "UserService processing request");
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        Ok("UserService response".to_string())
    }
}

pub struct OrderService;

impl TracedService for OrderService {
    #[tracing::instrument(name = "order_service.call", skip(self))]
    async fn call(&self, request: &str) -> Result<String, anyhow::Error> {
        tracing::info!(request, "OrderService processing request");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Ok("OrderService response".to_string())
    }
}
````

### 11.2 RPITIT 在 Span 管理

````rust
use tracing::Span;

// Rust 1.90: Return Position Impl Trait in Trait (RPITIT)
pub trait SpanProvider {
    fn create_span(&self, name: &str) -> impl std::future::Future<Output = Span> + Send;
}

pub struct DefaultSpanProvider;

impl SpanProvider for DefaultSpanProvider {
    async fn create_span(&self, name: &str) -> Span {
        tracing::info_span!(
            "custom_span",
            span_name = name,
            timestamp = %chrono::Utc::now()
        )
    }
}
````

---

## 总结

### 核心要点

1. **跨服务传播**: 使用 W3C Trace Context 在 HTTP/gRPC/Kafka 间传递上下文
2. **Span 关系**: 正确管理父子、兄弟、FollowsFrom 关系
3. **异步追踪**: 使用 `Instrument` trait 和 `in_scope` 传递 Span
4. **性能优化**: 采样、Span 复用、惰性属性
5. **错误处理**: 记录重试、断路器、分布式事务失败
6. **服务网格**: 与 Istio/Linkerd 集成实现自动追踪

### 性能指标

| 场景 | 开销 | 优化后 |
|------|------|--------|
| 无追踪 | 0µs | - |
| 同步 Span | 5µs | - |
| 异步 Span | 10µs | 5µs (复用) |
| 跨服务 HTTP | 50µs | 30µs (连接池) |
| Kafka 传播 | 100µs | 50µs (批量) |

### 最佳实践清单

- ✅ 使用 `#[instrument]` 自动创建 Span
- ✅ 正确传播 TraceContext（HTTP Header/gRPC Metadata/Kafka Header）
- ✅ 使用 `Instrument` trait 追踪异步任务
- ✅ 配置采样策略（生产环境 10-20%）
- ✅ 记录结构化属性（`http.status_code`、`db.statement`）
- ✅ 使用 Baggage 传递业务上下文（user.id）
- ✅ 监控 Span 生成速率和队列大小
- ✅ 实现自定义采样器（基于优先级）
- ✅ 集成 Jaeger/Tempo 可视化追踪链路
- ✅ 使用 Service Mesh 自动注入追踪

---

**相关文档**:

- [Context Propagation 详解](../04_核心组件/04_Context_Propagation详解_Rust完整版.md)
- [Logging 最佳实践](./01_Logging_Rust完整版.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
- [性能优化指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
