# 错误处理 - Rust 完整版

## 目录

- [错误处理 - Rust 完整版](#错误处理---rust-完整版)
  - [目录](#目录)
  - [1. OpenTelemetry 错误模型](#1-opentelemetry-错误模型)
    - [1.1 Span Status](#11-span-status)
    - [1.2 Span Events](#12-span-events)
  - [2. Rust 错误处理基础](#2-rust-错误处理基础)
    - [2.1 Result 与 anyhow](#21-result-与-anyhow)
    - [2.2 thiserror 自定义错误](#22-thiserror-自定义错误)
  - [3. 错误追踪集成](#3-错误追踪集成)
    - [3.1 记录错误到 Span](#31-记录错误到-span)
    - [3.2 错误属性](#32-错误属性)
    - [3.3 错误链追踪](#33-错误链追踪)
  - [4. gRPC 错误处理](#4-grpc-错误处理)
    - [4.1 Status Codes](#41-status-codes)
    - [4.2 错误转换](#42-错误转换)
    - [4.3 重试机制](#43-重试机制)
  - [5. HTTP 错误处理](#5-http-错误处理)
    - [5.1 Axum 错误处理](#51-axum-错误处理)
    - [5.2 Reqwest 错误处理](#52-reqwest-错误处理)
  - [6. 数据库错误处理](#6-数据库错误处理)
    - [6.1 SQLx 错误](#61-sqlx-错误)
    - [6.2 连接池错误](#62-连接池错误)
    - [6.3 事务回滚](#63-事务回滚)
  - [7. 消息队列错误处理](#7-消息队列错误处理)
    - [7.1 Kafka 错误](#71-kafka-错误)
    - [7.2 死信队列 (DLQ)](#72-死信队列-dlq)
  - [8. Panic 处理](#8-panic-处理)
    - [8.1 全局 Panic Hook](#81-全局-panic-hook)
    - [8.2 Tokio Task Panic](#82-tokio-task-panic)
  - [9. 超时处理](#9-超时处理)
    - [9.1 Tokio Timeout](#91-tokio-timeout)
    - [9.2 gRPC Timeout](#92-grpc-timeout)
  - [10. 容错模式](#10-容错模式)
    - [10.1 重试 (Retry)](#101-重试-retry)
    - [10.2 断路器 (Circuit Breaker)](#102-断路器-circuit-breaker)
    - [10.3 降级 (Fallback)](#103-降级-fallback)
  - [11. 错误监控](#11-错误监控)
    - [11.1 错误率指标](#111-错误率指标)
    - [11.2 错误告警](#112-错误告警)
  - [12. 生产环境最佳实践](#12-生产环境最佳实践)
    - [12.1 完整示例](#121-完整示例)
    - [12.2 Docker Compose 测试](#122-docker-compose-测试)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [错误分类](#错误分类)
    - [最佳实践清单](#最佳实践清单)

---

## 1. OpenTelemetry 错误模型

### 1.1 Span Status

````rust
use opentelemetry::trace::{Status, StatusCode};

pub fn span_status_example() {
    let span = tracing::Span::current();

    // 成功
    span.set_status(Status::Ok);

    // 错误
    span.set_status(Status::error("Database connection failed"));

    // 未设置 (默认)
    // span.set_status(Status::Unset);
}
````

**StatusCode 枚举**:

- `Unset`: 默认状态
- `Ok`: 操作成功
- `Error`: 操作失败

### 1.2 Span Events

````rust
use tracing::{error, Span};
use opentelemetry::trace::TraceContextExt;

pub async fn record_error_event() -> Result<(), anyhow::Error> {
    match risky_operation().await {
        Ok(result) => Ok(result),
        Err(e) => {
            // 记录错误事件
            let span = Span::current();
            span.record("error", true);
            span.record("error.type", e.to_string().as_str());

            error!(
                error = %e,
                error_chain = ?e.chain().collect::<Vec<_>>(),
                "Operation failed"
            );

            Err(e)
        }
    }
}

async fn risky_operation() -> Result<(), anyhow::Error> {
    Err(anyhow::anyhow!("Something went wrong"))
}
````

---

## 2. Rust 错误处理基础

### 2.1 Result 与 anyhow

````toml
[dependencies]
anyhow = "1.0"
````

````rust
use anyhow::{Context, Result};

pub async fn load_config(path: &str) -> Result<String> {
    std::fs::read_to_string(path)
        .context(format!("Failed to load config from {}", path))?;

    Ok("config_data".to_string())
}

pub async fn process_order(order_id: &str) -> Result<()> {
    validate_order(order_id)
        .context("Order validation failed")?;

    save_order(order_id)
        .context("Failed to save order")?;

    Ok(())
}

fn validate_order(order_id: &str) -> Result<()> {
    if order_id.is_empty() {
        anyhow::bail!("Order ID cannot be empty");
    }
    Ok(())
}

async fn save_order(order_id: &str) -> Result<()> {
    Ok(())
}
````

### 2.2 thiserror 自定义错误

````toml
[dependencies]
thiserror = "2.0"
````

````rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OrderError {
    #[error("Order not found: {0}")]
    NotFound(String),

    #[error("Invalid order amount: {0}")]
    InvalidAmount(f64),

    #[error("Payment failed: {0}")]
    PaymentFailed(String),

    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),

    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),
}

pub async fn get_order(order_id: &str) -> Result<Order, OrderError> {
    if order_id.is_empty() {
        return Err(OrderError::NotFound(order_id.to_string()));
    }

    // 查询数据库...
    Ok(Order {
        id: order_id.to_string(),
        amount: 99.99,
    })
}

#[derive(Debug)]
pub struct Order {
    pub id: String,
    pub amount: f64,
}
````

---

## 3. 错误追踪集成

### 3.1 记录错误到 Span

````rust
use tracing::{error, instrument, Span};
use opentelemetry::trace::{Status, TraceContextExt};

#[instrument(name = "process_payment", skip(amount))]
pub async fn process_payment(order_id: &str, amount: f64) -> Result<(), OrderError> {
    let span = Span::current();

    match charge_payment(order_id, amount).await {
        Ok(_) => {
            span.set_status(Status::Ok);
            tracing::info!(order_id, amount, "Payment successful");
            Ok(())
        }
        Err(e) => {
            // 设置 Span 状态为错误
            span.set_status(Status::error(e.to_string()));

            // 记录错误属性
            span.record("error", true);
            span.record("error.type", "PaymentError");
            span.record("error.message", e.to_string().as_str());

            error!(
                order_id,
                amount,
                error = %e,
                "Payment processing failed"
            );

            Err(OrderError::PaymentFailed(e.to_string()))
        }
    }
}

async fn charge_payment(order_id: &str, amount: f64) -> Result<(), anyhow::Error> {
    Err(anyhow::anyhow!("Payment gateway timeout"))
}
````

### 3.2 错误属性

````rust
use tracing::{error, Span};

pub async fn record_error_attributes() -> Result<(), anyhow::Error> {
    match external_api_call().await {
        Ok(response) => Ok(response),
        Err(e) => {
            let span = Span::current();

            // OpenTelemetry 标准错误属性
            span.record("error.type", "ExternalAPIError");
            span.record("error.message", e.to_string().as_str());
            span.record("error.stack", format!("{:?}", e.backtrace()).as_str());

            // 自定义属性
            span.record("retry_count", 3);
            span.record("api.endpoint", "https://api.example.com");

            error!(
                error = %e,
                error_type = "ExternalAPIError",
                retry_count = 3,
                "External API call failed"
            );

            Err(e)
        }
    }
}

async fn external_api_call() -> Result<(), anyhow::Error> {
    Err(anyhow::anyhow!("API error"))
}
````

### 3.3 错误链追踪

````rust
use anyhow::{Context, Result};
use tracing::error;

pub async fn execute_business_logic() -> Result<()> {
    database_operation()
        .await
        .context("Business logic failed")?;
    Ok(())
}

async fn database_operation() -> Result<()> {
    query_database()
        .await
        .context("Database operation failed")?;
    Ok(())
}

async fn query_database() -> Result<()> {
    connect_database()
        .await
        .context("Failed to execute query")?;
    Ok(())
}

async fn connect_database() -> Result<()> {
    Err(anyhow::anyhow!("Connection refused"))
}

pub async fn handle_with_error_chain() {
    match execute_business_logic().await {
        Ok(_) => {}
        Err(e) => {
            // 记录完整错误链
            let chain: Vec<String> = e.chain().map(|e| e.to_string()).collect();
            error!(
                error = %e,
                error_chain = ?chain,
                "Operation failed with error chain"
            );
        }
    }
}
````

---

## 4. gRPC 错误处理

### 4.1 Status Codes

````rust
use tonic::{Code, Status};
use tracing::error;

pub fn map_error_to_grpc_status(err: OrderError) -> Status {
    match err {
        OrderError::NotFound(id) => {
            Status::not_found(format!("Order {} not found", id))
        }
        OrderError::InvalidAmount(amount) => {
            Status::invalid_argument(format!("Invalid amount: {}", amount))
        }
        OrderError::PaymentFailed(msg) => {
            Status::internal(format!("Payment failed: {}", msg))
        }
        OrderError::DatabaseError(e) => {
            error!(error = %e, "Database error");
            Status::internal("Internal server error")
        }
        OrderError::NetworkError(e) => {
            error!(error = %e, "Network error");
            Status::unavailable("Service temporarily unavailable")
        }
    }
}

// gRPC 服务实现
use tonic::{Request, Response};

pub struct OrderService;

#[tonic::async_trait]
impl order_service_server::OrderService for OrderService {
    #[tracing::instrument(name = "grpc.get_order", skip(self, request))]
    async fn get_order(
        &self,
        request: Request<GetOrderRequest>,
    ) -> Result<Response<Order>, Status> {
        let order_id = &request.get_ref().order_id;

        match get_order(order_id).await {
            Ok(order) => Ok(Response::new(order)),
            Err(e) => Err(map_error_to_grpc_status(e)),
        }
    }
}
````

### 4.2 错误转换

````rust
use tonic::Status;

impl From<OrderError> for Status {
    fn from(err: OrderError) -> Self {
        map_error_to_grpc_status(err)
    }
}

// 使用 ? 自动转换
pub async fn create_order_grpc(
    request: Request<CreateOrderRequest>,
) -> Result<Response<Order>, Status> {
    let order = create_order(&request.get_ref().order_id).await?;
    Ok(Response::new(order))
}

async fn create_order(order_id: &str) -> Result<Order, OrderError> {
    Ok(Order {
        id: order_id.to_string(),
        amount: 99.99,
    })
}
````

### 4.3 重试机制

````rust
use tonic::{Request, Response, Status, Code};
use tracing::{info, warn};

pub async fn call_grpc_with_retry<T, R>(
    mut call: impl FnMut(Request<T>) -> Result<Response<R>, Status>,
    request: T,
    max_retries: u32,
) -> Result<Response<R>, Status>
where
    T: Clone,
{
    let mut attempts = 0;

    loop {
        attempts += 1;
        let req = Request::new(request.clone());

        match call(req) {
            Ok(response) => {
                info!(attempts, "gRPC call successful");
                return Ok(response);
            }
            Err(status) if should_retry(&status) && attempts < max_retries => {
                warn!(
                    attempts,
                    code = ?status.code(),
                    "gRPC call failed, retrying"
                );
                tokio::time::sleep(tokio::time::Duration::from_secs(2_u64.pow(attempts))).await;
            }
            Err(status) => {
                tracing::error!(
                    attempts,
                    code = ?status.code(),
                    message = %status.message(),
                    "gRPC call failed after max retries"
                );
                return Err(status);
            }
        }
    }
}

fn should_retry(status: &Status) -> bool {
    matches!(
        status.code(),
        Code::Unavailable | Code::DeadlineExceeded | Code::ResourceExhausted
    )
}
````

---

## 5. HTTP 错误处理

### 5.1 Axum 错误处理

````rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde::Serialize;

#[derive(Serialize)]
pub struct ErrorResponse {
    error: String,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    trace_id: Option<String>,
}

impl IntoResponse for OrderError {
    fn into_response(self) -> Response {
        let (status, error_type) = match &self {
            OrderError::NotFound(_) => (StatusCode::NOT_FOUND, "NotFound"),
            OrderError::InvalidAmount(_) => (StatusCode::BAD_REQUEST, "InvalidAmount"),
            OrderError::PaymentFailed(_) => (StatusCode::PAYMENT_REQUIRED, "PaymentFailed"),
            OrderError::DatabaseError(_) => (StatusCode::INTERNAL_SERVER_ERROR, "DatabaseError"),
            OrderError::NetworkError(_) => (StatusCode::BAD_GATEWAY, "NetworkError"),
        };

        // 获取 trace_id
        let trace_id = opentelemetry::Context::current()
            .span()
            .span_context()
            .trace_id()
            .to_string();

        let body = Json(ErrorResponse {
            error: error_type.to_string(),
            message: self.to_string(),
            trace_id: Some(trace_id),
        });

        (status, body).into_response()
    }
}

// Axum handler
use axum::extract::Path;

#[tracing::instrument(name = "http.get_order")]
pub async fn get_order_handler(
    Path(order_id): Path<String>,
) -> Result<Json<Order>, OrderError> {
    let order = get_order(&order_id).await?;
    Ok(Json(order))
}
````

### 5.2 Reqwest 错误处理

````rust
use reqwest::Client;
use tracing::{error, info, instrument};

#[instrument(name = "http.client.call", skip(client))]
pub async fn call_external_api(client: &Client, url: &str) -> Result<String, anyhow::Error> {
    match client.get(url).send().await {
        Ok(response) => {
            if response.status().is_success() {
                let body = response.text().await?;
                info!(url, "API call successful");
                Ok(body)
            } else {
                let status = response.status();
                let error_body = response.text().await.unwrap_or_default();

                error!(
                    url,
                    status = status.as_u16(),
                    error_body,
                    "API call failed with non-2xx status"
                );

                Err(anyhow::anyhow!(
                    "API returned {}: {}",
                    status,
                    error_body
                ))
            }
        }
        Err(e) => {
            error!(url, error = %e, "API call failed");
            Err(e.into())
        }
    }
}
````

---

## 6. 数据库错误处理

### 6.1 SQLx 错误

````rust
use sqlx::{PgPool, Error as SqlxError};
use tracing::{error, instrument};

#[instrument(name = "db.query_user", skip(pool))]
pub async fn query_user(pool: &PgPool, user_id: i64) -> Result<User, OrderError> {
    match sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
        .bind(user_id)
        .fetch_one(pool)
        .await
    {
        Ok(user) => Ok(user),
        Err(SqlxError::RowNotFound) => {
            error!(user_id, "User not found");
            Err(OrderError::NotFound(format!("User {}", user_id)))
        }
        Err(e) => {
            error!(user_id, error = %e, "Database query failed");
            Err(OrderError::DatabaseError(e))
        }
    }
}

#[derive(sqlx::FromRow, Debug)]
pub struct User {
    pub id: i64,
    pub name: String,
}
````

### 6.2 连接池错误

````rust
use sqlx::{PgPool, postgres::PgPoolOptions};
use tracing::{error, info};

pub async fn create_pool(database_url: &str) -> Result<PgPool, anyhow::Error> {
    match PgPoolOptions::new()
        .max_connections(10)
        .acquire_timeout(std::time::Duration::from_secs(5))
        .connect(database_url)
        .await
    {
        Ok(pool) => {
            info!("Database connection pool created");
            Ok(pool)
        }
        Err(e) => {
            error!(error = %e, "Failed to create database pool");
            Err(e.into())
        }
    }
}
````

### 6.3 事务回滚

````rust
use sqlx::{PgPool, Postgres, Transaction};
use tracing::{error, info, instrument};

#[instrument(name = "db.transaction", skip(pool))]
pub async fn execute_transaction(pool: &PgPool) -> Result<(), anyhow::Error> {
    let mut tx = pool.begin().await?;

    match process_in_transaction(&mut tx).await {
        Ok(_) => {
            tx.commit().await?;
            info!("Transaction committed");
            Ok(())
        }
        Err(e) => {
            error!(error = %e, "Transaction failed, rolling back");
            tx.rollback().await?;
            Err(e)
        }
    }
}

async fn process_in_transaction(tx: &mut Transaction<'_, Postgres>) -> Result<(), anyhow::Error> {
    sqlx::query("INSERT INTO orders (id) VALUES ($1)")
        .bind("ORD-001")
        .execute(&mut **tx)
        .await?;

    // 模拟错误
    if rand::random::<bool>() {
        return Err(anyhow::anyhow!("Random error"));
    }

    Ok(())
}
````

---

## 7. 消息队列错误处理

### 7.1 Kafka 错误

````rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use tracing::{error, info, instrument};

#[instrument(name = "kafka.publish", skip(producer))]
pub async fn publish_with_retry(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
    max_retries: u32,
) -> Result<(), anyhow::Error> {
    let mut attempts = 0;

    loop {
        attempts += 1;
        let record = FutureRecord::to(topic).key(key).payload(payload);

        match producer.send(record, std::time::Duration::from_secs(5)).await {
            Ok((partition, offset)) => {
                info!(
                    topic,
                    partition,
                    offset,
                    attempts,
                    "Kafka message published"
                );
                return Ok(());
            }
            Err((e, _)) if attempts < max_retries => {
                error!(
                    topic,
                    attempts,
                    error = ?e,
                    "Kafka publish failed, retrying"
                );
                tokio::time::sleep(tokio::time::Duration::from_secs(2_u64.pow(attempts))).await;
            }
            Err((e, _)) => {
                error!(
                    topic,
                    attempts,
                    error = ?e,
                    "Kafka publish failed after max retries"
                );
                return Err(anyhow::anyhow!("Kafka error: {:?}", e));
            }
        }
    }
}
````

### 7.2 死信队列 (DLQ)

````rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::producer::FutureProducer;
use rdkafka::Message;
use tracing::{error, warn, instrument};

#[instrument(name = "kafka.consume_with_dlq", skip(consumer, producer))]
pub async fn consume_with_dlq(
    consumer: StreamConsumer,
    producer: FutureProducer,
    max_retries: u32,
) {
    loop {
        match consumer.recv().await {
            Ok(message) => {
                let payload = message.payload_view::<str>().unwrap_or(Ok("")).unwrap_or("");

                match process_message(payload, max_retries).await {
                    Ok(_) => {
                        tracing::info!(payload, "Message processed successfully");
                    }
                    Err(e) => {
                        error!(payload, error = %e, "Message processing failed, sending to DLQ");

                        // 发送到死信队列
                        send_to_dlq(&producer, payload, &e).await;
                    }
                }
            }
            Err(e) => {
                error!(error = ?e, "Kafka consume error");
            }
        }
    }
}

async fn process_message(payload: &str, max_retries: u32) -> Result<(), anyhow::Error> {
    // 业务逻辑...
    Ok(())
}

async fn send_to_dlq(producer: &FutureProducer, payload: &str, error: &anyhow::Error) {
    let dlq_payload = format!(r#"{{"original": "{}", "error": "{}"}}"#, payload, error);
    let record = rdkafka::producer::FutureRecord::to("orders-dlq")
        .payload(&dlq_payload);

    match producer.send(record, std::time::Duration::from_secs(5)).await {
        Ok(_) => {
            warn!(payload, "Message sent to DLQ");
        }
        Err(e) => {
            error!(payload, error = ?e, "Failed to send message to DLQ");
        }
    }
}
````

---

## 8. Panic 处理

### 8.1 全局 Panic Hook

````rust
use tracing::error;

pub fn init_panic_hook() {
    let default_panic = std::panic::take_hook();

    std::panic::set_hook(Box::new(move |panic_info| {
        let payload = panic_info.payload();
        let message = if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "Unknown panic payload".to_string()
        };

        let location = panic_info
            .location()
            .map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column()))
            .unwrap_or_else(|| "Unknown location".to_string());

        error!(
            panic_message = %message,
            panic_location = %location,
            backtrace = ?std::backtrace::Backtrace::capture(),
            "Application panicked"
        );

        default_panic(panic_info);
    }));
}
````

### 8.2 Tokio Task Panic

````rust
use tokio::task::JoinHandle;
use tracing::{error, info};

pub async fn spawn_with_error_handling() {
    let handle: JoinHandle<Result<(), anyhow::Error>> = tokio::spawn(async {
        // 可能 panic 的代码
        std::panic::catch_unwind(|| {
            // 业务逻辑...
        })
        .map_err(|_| anyhow::anyhow!("Task panicked"))?;

        Ok(())
    });

    match handle.await {
        Ok(Ok(_)) => {
            info!("Task completed successfully");
        }
        Ok(Err(e)) => {
            error!(error = %e, "Task failed with error");
        }
        Err(e) => {
            error!(error = %e, "Task panicked or was cancelled");
        }
    }
}
````

---

## 9. 超时处理

### 9.1 Tokio Timeout

````rust
use tokio::time::{timeout, Duration};
use tracing::{error, info, instrument};

#[instrument(name = "operation_with_timeout")]
pub async fn operation_with_timeout() -> Result<(), anyhow::Error> {
    match timeout(Duration::from_secs(5), slow_operation()).await {
        Ok(result) => {
            info!("Operation completed within timeout");
            result
        }
        Err(_) => {
            error!("Operation timed out after 5 seconds");
            Err(anyhow::anyhow!("Operation timeout"))
        }
    }
}

async fn slow_operation() -> Result<(), anyhow::Error> {
    tokio::time::sleep(Duration::from_secs(10)).await;
    Ok(())
}
````

### 9.2 gRPC Timeout

````rust
use tonic::{Request, Response, Status};
use tokio::time::{timeout, Duration};

pub async fn call_grpc_with_timeout<T, R>(
    mut call: impl FnOnce(Request<T>) -> Result<Response<R>, Status>,
    request: T,
    timeout_secs: u64,
) -> Result<Response<R>, Status> {
    let request = Request::new(request);

    match timeout(Duration::from_secs(timeout_secs), call(request)).await {
        Ok(result) => result,
        Err(_) => Err(Status::deadline_exceeded("Request timeout")),
    }
}
````

---

## 10. 容错模式

### 10.1 重试 (Retry)

````rust
use tracing::{info, warn, instrument};

#[instrument(name = "retry_with_exponential_backoff", skip(operation))]
pub async fn retry_with_exponential_backoff<F, T, E>(
    operation: F,
    max_retries: u32,
) -> Result<T, E>
where
    F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>>>>,
    E: std::fmt::Display,
{
    let mut attempts = 0;

    loop {
        attempts += 1;
        match operation().await {
            Ok(result) => {
                info!(attempts, "Operation successful");
                return Ok(result);
            }
            Err(e) if attempts < max_retries => {
                let delay = 2_u64.pow(attempts);
                warn!(
                    attempts,
                    error = %e,
                    delay_secs = delay,
                    "Operation failed, retrying"
                );
                tokio::time::sleep(tokio::time::Duration::from_secs(delay)).await;
            }
            Err(e) => {
                tracing::error!(
                    attempts,
                    error = %e,
                    "Operation failed after max retries"
                );
                return Err(e);
            }
        }
    }
}
````

### 10.2 断路器 (Circuit Breaker)

````rust
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::{error, info, warn};

#[derive(Clone, PartialEq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

pub struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: Arc<Mutex<u32>>,
    threshold: u32,
    timeout: std::time::Duration,
    last_failure_time: Arc<Mutex<Option<std::time::Instant>>>,
}

impl CircuitBreaker {
    pub fn new(threshold: u32, timeout: std::time::Duration) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            threshold,
            timeout,
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }

    #[tracing::instrument(name = "circuit_breaker.execute", skip(self, f))]
    pub async fn execute<F, T, E>(&self, f: F) -> Result<T, anyhow::Error>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        // 检查断路器状态
        let mut state = self.state.lock().await;

        match *state {
            CircuitState::Open => {
                // 检查是否可以进入半开状态
                if let Some(last_failure) = *self.last_failure_time.lock().await {
                    if last_failure.elapsed() > self.timeout {
                        *state = CircuitState::HalfOpen;
                        info!("Circuit breaker entering HALF-OPEN state");
                    } else {
                        warn!("Circuit breaker is OPEN, rejecting request");
                        return Err(anyhow::anyhow!("Circuit breaker is open"));
                    }
                }
            }
            CircuitState::HalfOpen => {
                info!("Circuit breaker is HALF-OPEN, trying request");
            }
            CircuitState::Closed => {
                info!("Circuit breaker is CLOSED, processing request");
            }
        }

        drop(state);

        // 执行操作
        match f.await {
            Ok(result) => {
                // 成功：重置计数器
                *self.failure_count.lock().await = 0;
                *self.state.lock().await = CircuitState::Closed;
                info!("Request succeeded, circuit breaker reset");
                Ok(result)
            }
            Err(e) => {
                // 失败：增加计数器
                let mut count = self.failure_count.lock().await;
                *count += 1;

                if *count >= self.threshold {
                    *self.state.lock().await = CircuitState::Open;
                    *self.last_failure_time.lock().await = Some(std::time::Instant::now());
                    error!(failure_count = *count, "Circuit breaker opened");
                }

                Err(anyhow::anyhow!("Request failed: {}", e))
            }
        }
    }
}
````

### 10.3 降级 (Fallback)

````rust
use tracing::{info, warn, instrument};

#[instrument(name = "get_user_with_fallback")]
pub async fn get_user_with_fallback(user_id: i64) -> Result<User, anyhow::Error> {
    match get_user_from_database(user_id).await {
        Ok(user) => {
            info!(user_id, "User fetched from database");
            Ok(user)
        }
        Err(e) => {
            warn!(user_id, error = %e, "Database unavailable, using fallback");
            Ok(get_default_user(user_id))
        }
    }
}

async fn get_user_from_database(user_id: i64) -> Result<User, anyhow::Error> {
    Err(anyhow::anyhow!("Database unavailable"))
}

fn get_default_user(user_id: i64) -> User {
    User {
        id: user_id,
        name: "Guest User".to_string(),
    }
}
````

---

## 11. 错误监控

### 11.1 错误率指标

````rust
use opentelemetry::metrics::{Counter, Meter};

pub struct ErrorMetrics {
    error_count: Counter<u64>,
    total_count: Counter<u64>,
}

impl ErrorMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            error_count: meter
                .u64_counter("errors.count")
                .with_description("Total number of errors")
                .build(),
            total_count: meter
                .u64_counter("requests.count")
                .with_description("Total number of requests")
                .build(),
        }
    }

    pub fn record_success(&self, operation: &str) {
        self.total_count.add(1, &[("operation", operation.to_string()).into()]);
    }

    pub fn record_error(&self, operation: &str, error_type: &str) {
        self.error_count.add(1, &[
            ("operation", operation.to_string()).into(),
            ("error.type", error_type.to_string()).into(),
        ]);
        self.total_count.add(1, &[("operation", operation.to_string()).into()]);
    }
}
````

### 11.2 错误告警

````rust
use tracing::error;

pub async fn check_error_rate_and_alert(threshold: f64) {
    let error_rate = calculate_error_rate().await;

    if error_rate > threshold {
        error!(
            error_rate,
            threshold,
            "Error rate exceeds threshold, sending alert"
        );

        // 发送告警（Slack/PagerDuty/Email）
        send_alert(&format!(
            "Error rate {}% exceeds threshold {}%",
            error_rate * 100.0,
            threshold * 100.0
        ))
        .await;
    }
}

async fn calculate_error_rate() -> f64 {
    0.05  // 5%
}

async fn send_alert(message: &str) {
    tracing::warn!(alert_message = message, "Alert sent");
}
````

---

## 12. 生产环境最佳实践

### 12.1 完整示例

````rust
use anyhow::Result;
use tracing::{error, info, instrument};

#[instrument(name = "production.process_order", skip(pool, producer))]
pub async fn production_process_order(
    pool: &sqlx::PgPool,
    producer: &rdkafka::producer::FutureProducer,
    order_id: &str,
) -> Result<()> {
    // 1. 验证订单
    let order = match validate_order(order_id).await {
        Ok(order) => order,
        Err(e) => {
            error!(order_id, error = %e, "Order validation failed");
            return Err(e);
        }
    };

    // 2. 数据库事务
    let mut tx = pool.begin().await?;
    match save_order_to_db(&mut tx, &order).await {
        Ok(_) => {}
        Err(e) => {
            error!(order_id, error = %e, "Failed to save order, rolling back");
            tx.rollback().await?;
            return Err(e);
        }
    }

    // 3. 发布事件到 Kafka（带重试）
    match publish_with_retry(producer, "orders", order_id, "{}", 3).await {
        Ok(_) => {
            tx.commit().await?;
            info!(order_id, "Order processed successfully");
            Ok(())
        }
        Err(e) => {
            error!(order_id, error = %e, "Failed to publish event, rolling back");
            tx.rollback().await?;
            Err(e)
        }
    }
}

async fn validate_order(order_id: &str) -> Result<Order> {
    Ok(Order {
        id: order_id.to_string(),
        amount: 99.99,
    })
}

async fn save_order_to_db(
    tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
    order: &Order,
) -> Result<()> {
    Ok(())
}
````

### 12.2 Docker Compose 测试

````yaml
version: '3.8'
services:
  app:
    build: .
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/mydb
      - KAFKA_BROKERS=kafka:9092
      - RUST_LOG=info,my_app=debug
    depends_on:
      - postgres
      - kafka

  postgres:
    image: postgres:16
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=mydb
    ports:
      - "5432:5432"

  kafka:
    image: bitnami/kafka:latest
    ports:
      - "9092:9092"
    environment:
      - KAFKA_CFG_NODE_ID=0
      - KAFKA_CFG_PROCESS_ROLES=controller,broker
      - KAFKA_CFG_LISTENERS=PLAINTEXT://:9092,CONTROLLER://:9093
      - KAFKA_CFG_LISTENER_SECURITY_PROTOCOL_MAP=CONTROLLER:PLAINTEXT,PLAINTEXT:PLAINTEXT
      - KAFKA_CFG_CONTROLLER_QUORUM_VOTERS=0@kafka:9093
      - KAFKA_CFG_CONTROLLER_LISTENER_NAMES=CONTROLLER
````

---

## 总结

### 核心要点

1. **Span Status**: 使用 `Status::error()` 标记错误 Span
2. **结构化错误**: 使用 `thiserror` 定义领域特定错误类型
3. **错误链**: 使用 `anyhow::Context` 添加上下文信息
4. **重试机制**: 指数退避策略，区分可重试和不可重试错误
5. **断路器**: 防止级联失败，保护下游服务
6. **超时处理**: 使用 `tokio::time::timeout` 避免永久阻塞
7. **错误监控**: 记录错误指标，配置告警阈值

### 错误分类

| 错误类型 | HTTP | gRPC | 可重试 | 示例 |
|---------|------|------|--------|------|
| 客户端错误 | 400 | INVALID_ARGUMENT | ❌ | 参数验证失败 |
| 未找到 | 404 | NOT_FOUND | ❌ | 资源不存在 |
| 未授权 | 401 | UNAUTHENTICATED | ❌ | Token 失效 |
| 服务不可用 | 503 | UNAVAILABLE | ✅ | 数据库连接失败 |
| 超时 | 504 | DEADLINE_EXCEEDED | ✅ | 请求超时 |
| 内部错误 | 500 | INTERNAL | ✅ | 未预期异常 |

### 最佳实践清单

- ✅ 使用 `thiserror` 定义自定义错误类型
- ✅ 使用 `anyhow::Context` 添加错误上下文
- ✅ 在 Span 中记录 `error`, `error.type`, `error.message` 属性
- ✅ 设置 Span Status 为 `Error` 当操作失败
- ✅ 记录完整错误链 (`e.chain()`)
- ✅ 实现重试机制（指数退避）
- ✅ 使用断路器保护外部依赖
- ✅ 配置超时避免永久阻塞
- ✅ 数据库事务失败时回滚
- ✅ 使用死信队列处理消费失败的消息
- ✅ 注册全局 Panic Hook 记录 panic 信息
- ✅ 监控错误率并配置告警
- ✅ gRPC 错误正确映射到 Status Code
- ✅ HTTP 错误返回 trace_id 便于追踪

---

**相关文档**:

- [分布式追踪进阶](../02_Semantic_Conventions/03_日志与事件/02_分布式追踪进阶_Rust完整版.md)
- [Logging 最佳实践](../02_Semantic_Conventions/03_日志与事件/01_Logging_Rust完整版.md)
- [故障排查指南](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
- [性能优化指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
