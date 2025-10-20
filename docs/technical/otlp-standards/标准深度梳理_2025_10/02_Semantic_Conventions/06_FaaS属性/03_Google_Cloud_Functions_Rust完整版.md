# Google Cloud Functions 语义约定 - Rust 完整实现

> **Serverless 计算**: Google Cloud Functions 完整 Tracing 与 Metrics 规范 (Rust 版本)  
> **最后更新**: 2025年10月10日

---

## 目录

- [Google Cloud Functions 语义约定 - Rust 完整实现](#google-cloud-functions-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. Cloud Functions 概述](#1-cloud-functions-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 执行模型](#12-执行模型)
  - [2. Functions Resource 属性](#2-functions-resource-属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Functions Span 属性](#3-functions-span-属性)
  - [4. Rust 完整实现](#4-rust-完整实现)
    - [4.1 基础设施](#41-基础设施)
      - [Cargo.toml](#cargotoml)
      - [核心 OTLP 模块](#核心-otlp-模块)
    - [4.2 HTTP Functions](#42-http-functions)
      - [基本 HTTP Handler](#基本-http-handler)
    - [4.3 CloudEvent Functions](#43-cloudevent-functions)
    - [4.4 Pub/Sub 触发](#44-pubsub-触发)
    - [4.5 Cloud Storage 触发](#45-cloud-storage-触发)
    - [4.6 Firestore 触发](#46-firestore-触发)
  - [5. OTLP 与 Cloud Trace 集成](#5-otlp-与-cloud-trace-集成)
    - [5.1 同时使用 OTLP 和 Cloud Trace](#51-同时使用-otlp-和-cloud-trace)
    - [5.2 Cloud Logging 集成](#52-cloud-logging-集成)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 冷启动优化](#61-冷启动优化)
    - [6.2 并发处理](#62-并发处理)
    - [6.3 错误处理](#63-错误处理)
  - [7. 性能优化](#7-性能优化)
    - [7.1 内存优化](#71-内存优化)
    - [7.2 二进制大小优化](#72-二进制大小优化)
  - [8. 部署](#8-部署)
    - [8.1 Dockerfile](#81-dockerfile)
    - [8.2 部署到 Cloud Functions 2nd Gen](#82-部署到-cloud-functions-2nd-gen)
    - [8.3 使用 Cloud Build](#83-使用-cloud-build)
  - [参考资源](#参考资源)

---

## 1. Cloud Functions 概述

### 1.1 核心特性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Google Cloud Functions - FaaS 平台

核心特性:
✅ 事件驱动
✅ 自动扩展 (0-1000+ 实例)
✅ 多语言支持 (Node.js/Python/Go/Java/Ruby/.NET/PHP)
✅ Rust 支持 (2nd Gen, 通过 Cloud Run)
✅ Cloud Run 集成 (2nd gen)
✅ VPC 连接
✅ 内置 Cloud Trace 集成
✅ Cloud Logging 自动集成

Rust 优势:
✅ 超快冷启动 (< 100ms)
✅ 极低内存占用 (< 15MB)
✅ 高并发处理能力
✅ 类型安全
✅ 零成本抽象

版本对比:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
| 特性          | 1st Gen      | 2nd Gen (推荐) |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
| 最大时长      | 9 分钟       | 60 分钟         |
| 最大内存      | 8 GB         | 16 GB           |
| 并发          | 1/实例       | 1000/实例       |
| 底层          | 自定义       | Cloud Run       |
| Rust 支持     | ❌           | ✅              |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 执行模型

```text
┌─────────────────────────────────────────┐
│     Cloud Functions 2nd Gen             │
│                                         │
│  ┌─────────────────────────────────┐  │
│  │   Cloud Run 容器                │  │
│  │   ┌─────────────────────────┐  │  │
│  │   │   Rust HTTP Server      │  │  │
│  │   │   - actix-web/warp      │  │  │
│  │   │   - 处理 HTTP/CloudEvent│  │  │
│  │   │   - OTLP Tracing        │  │  │
│  │   └─────────────────────────┘  │  │
│  └─────────────────────────────────┘  │
│                                         │
│  事件源:                                │
│  - HTTP(S) 请求                         │
│  - Cloud Pub/Sub                        │
│  - Cloud Storage                        │
│  - Firestore                            │
│  - Firebase                             │
│  - Cloud Scheduler                      │
└─────────────────────────────────────────┘
```

---

## 2. Functions Resource 属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"gcp"` |
| `cloud.platform` | string | 平台类型 | `"gcp_cloud_functions"` |
| `cloud.region` | string | GCP 区域 | `"us-central1"` |
| `faas.name` | string | 函数名称 | `"my-function"` |
| `faas.version` | string | 函数版本 | `"1"` |
| `gcp.project_id` | string | 项目 ID | `"my-project"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.instance` | string | 实例 ID | GCP 自动生成 |
| `gcp.cloud_functions.generation` | string | 函数代数 | `"1"`, `"2"` |
| `service.name` | string | 服务名称 | 函数名称 |
| `cloud.availability_zone` | string | 可用区 | `"us-central1-a"` |

---

## 3. Functions Span 属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.trigger` | string | 触发类型 | `"http"`, `"pubsub"`, `"datasource"` |
| `faas.invocation_id` | string | 调用 ID | GCP 提供 |
| `faas.coldstart` | boolean | 是否冷启动 | `true`/`false` |
| `gcp.cloud_functions.trigger_type` | string | GCP 触发器类型 | `"http"`, `"event"` |

---

## 4. Rust 完整实现

### 4.1 基础设施

#### Cargo.toml

```toml
[package]
name = "gcp-function-rust"
version = "0.1.0"
edition = "2021"

[dependencies]
# HTTP 框架
actix-web = "4"
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"

# CloudEvent 支持
cloudevents-sdk = "0.7"

# GCP SDK
google-cloud-googleapis = "0.11"
google-cloud-pubsub = "0.19"
google-cloud-storage = "0.15"
google-cloud-firestore = "0.10"

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.15", features = ["grpc-tonic"] }
opentelemetry-stackdriver = "0.19"
opentelemetry-semantic-conventions = "0.14"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.23"
tracing-actix-web = "0.7"

# 实用工具
base64 = "0.21"
chrono = "0.4"
```

#### 核心 OTLP 模块

```rust
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _, SpanKind, Status},
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{Tracer as SdkTracer, TracerProvider, Config},
    Resource,
};
use std::time::Duration;

/// GCP Functions OTLP 配置
pub struct GcpFunctionsOtlpConfig {
    pub otlp_endpoint: String,
    pub service_name: String,
    pub service_version: String,
    pub use_cloud_trace: bool,
}

impl Default for GcpFunctionsOtlpConfig {
    fn default() -> Self {
        Self {
            otlp_endpoint: std::env::var("OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            service_name: std::env::var("K_SERVICE")
                .or_else(|_| std::env::var("FUNCTION_NAME"))
                .unwrap_or_else(|_| "cloud-function".to_string()),
            service_version: std::env::var("K_REVISION")
                .unwrap_or_else(|_| "1".to_string()),
            use_cloud_trace: std::env::var("USE_CLOUD_TRACE")
                .map(|v| v == "true")
                .unwrap_or(false),
        }
    }
}

/// 初始化 OTLP Tracer
pub fn init_tracer(config: GcpFunctionsOtlpConfig) -> anyhow::Result<SdkTracer> {
    // 构建 GCP Functions Resource 属性
    let resource = Resource::new(vec![
        // 云平台属性
        KeyValue::new("cloud.provider", "gcp"),
        KeyValue::new("cloud.platform", "gcp_cloud_functions"),
        KeyValue::new(
            "cloud.region",
            std::env::var("FUNCTION_REGION")
                .or_else(|_| std::env::var("GCP_REGION"))
                .unwrap_or_else(|_| "us-central1".to_string()),
        ),
        KeyValue::new(
            "cloud.availability_zone",
            std::env::var("FUNCTION_ZONE").unwrap_or_default(),
        ),
        
        // FaaS 属性
        KeyValue::new("faas.name", config.service_name.clone()),
        KeyValue::new("faas.version", config.service_version.clone()),
        KeyValue::new(
            "faas.instance",
            std::env::var("K_INSTANCE").unwrap_or_default(),
        ),
        
        // GCP 特定属性
        KeyValue::new(
            "gcp.project_id",
            std::env::var("GCP_PROJECT")
                .or_else(|_| std::env::var("GOOGLE_CLOUD_PROJECT"))
                .unwrap_or_default(),
        ),
        KeyValue::new(
            "gcp.cloud_functions.generation",
            detect_generation(),
        ),
        
        // 服务属性
        KeyValue::new("service.name", config.service_name.clone()),
        KeyValue::new("service.version", config.service_version),
        KeyValue::new("service.namespace", "cloud-functions"),
    ]);

    // 选择 Exporter: Cloud Trace 或 OTLP
    let tracer = if config.use_cloud_trace {
        // 使用 Cloud Trace
        let exporter = opentelemetry_stackdriver::StackdriverExporter::builder()
            .build()?;
        
        let tracer_provider = TracerProvider::builder()
            .with_config(Config::default().with_resource(resource))
            .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
            .build();
        
        let tracer = tracer_provider.tracer(config.service_name);
        global::set_tracer_provider(tracer_provider);
        
        tracer
    } else {
        // 使用 OTLP
        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(&config.otlp_endpoint)
            .with_timeout(Duration::from_secs(3));

        let tracer_provider = TracerProvider::builder()
            .with_config(Config::default().with_resource(resource))
            .with_batch_exporter(exporter.build_span_exporter()?, opentelemetry_sdk::runtime::Tokio)
            .build();

        let tracer = tracer_provider.tracer(config.service_name);
        global::set_tracer_provider(tracer_provider);
        
        tracer
    };

    Ok(tracer)
}

/// 检测 Cloud Functions 代数
fn detect_generation() -> String {
    if std::env::var("K_SERVICE").is_ok() {
        "2".to_string() // 2nd Gen (Cloud Run)
    } else if std::env::var("FUNCTION_NAME").is_ok() {
        "1".to_string() // 1st Gen
    } else {
        "unknown".to_string()
    }
}

/// 检测是否为冷启动
pub fn is_cold_start() -> bool {
    static COLD_START: std::sync::Once = std::sync::Once::new();
    let mut is_cold = false;
    
    COLD_START.call_once(|| {
        is_cold = true;
    });
    
    is_cold
}

/// 从环境变量获取 trace context (Cloud Trace)
pub fn extract_trace_context_from_header(header_value: &str) -> Option<String> {
    // Cloud Trace 格式: "TRACE_ID/SPAN_ID;o=TRACE_TRUE"
    Some(header_value.to_string())
}
```

---

### 4.2 HTTP Functions

#### 基本 HTTP Handler

```rust
use actix_web::{web, App, HttpRequest, HttpResponse, HttpServer, middleware};
use opentelemetry::trace::{TraceContextExt, Tracer, SpanKind};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct CreateUserRequest {
    name: String,
    email: String,
}

#[derive(Serialize)]
struct CreateUserResponse {
    id: String,
    name: String,
    email: String,
    created_at: String,
}

async fn handle_http_request(
    req: HttpRequest,
    body: web::Json<CreateUserRequest>,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("cloud-functions");
    
    // 创建 span
    let mut span = tracer
        .span_builder("cloud_functions.http_invocation")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 添加 FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "http"));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    span.set_attribute(KeyValue::new("gcp.cloud_functions.trigger_type", "http"));
    
    // 从 Cloud Trace header 提取 trace context
    if let Some(trace_header) = req.headers().get("x-cloud-trace-context") {
        if let Ok(trace_value) = trace_header.to_str() {
            span.set_attribute(KeyValue::new(
                "gcp.cloud_trace.trace_context",
                trace_value.to_string(),
            ));
        }
    }
    
    // HTTP 请求属性
    span.set_attribute(KeyValue::new("http.method", req.method().as_str()));
    span.set_attribute(KeyValue::new("http.target", req.uri().path()));
    span.set_attribute(KeyValue::new("http.scheme", req.connection_info().scheme()));
    span.set_attribute(KeyValue::new("http.host", req.connection_info().host()));
    
    if let Some(user_agent) = req.headers().get("user-agent") {
        if let Ok(ua) = user_agent.to_str() {
            span.set_attribute(KeyValue::new("http.user_agent", ua));
        }
    }
    
    // 处理请求
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let result = process_http_request_with_context(&body, cx).await;
    
    match &result {
        Ok(response) => {
            span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.set_attribute(KeyValue::new("error", true));
            span.set_attribute(KeyValue::new("error.message", e.to_string()));
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    span.end();
    result
}

async fn process_http_request_with_context(
    request: &CreateUserRequest,
    cx: opentelemetry::Context,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("cloud-functions");
    let _guard = cx.attach();
    
    // 创建子 span
    let span = tracer
        .span_builder("create_user")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    // 业务逻辑
    let user_id = uuid::Uuid::new_v4().to_string();
    let response = CreateUserResponse {
        id: user_id,
        name: request.name.clone(),
        email: request.email.clone(),
        created_at: chrono::Utc::now().to_rfc3339(),
    };
    
    tracing::info!("Created user: {}", response.id);
    
    Ok(HttpResponse::Created()
        .content_type("application/json")
        .json(response))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化 OTLP
    let config = GcpFunctionsOtlpConfig::default();
    init_tracer(config).expect("Failed to initialize tracer");
    
    // 初始化日志
    tracing_subscriber::fmt()
        .json()
        .with_env_filter(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string())
        )
        .init();
    
    // Cloud Functions 端口
    let port = std::env::var("PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse::<u16>()
        .unwrap_or(8080);
    
    println!("Cloud Function listening on port {}", port);
    
    HttpServer::new(|| {
        App::new()
            .wrap(middleware::Logger::default())
            .wrap(tracing_actix_web::TracingLogger::default())
            .route("/", web::post().to(handle_http_request))
    })
    .bind(("0.0.0.0", port))?
    .run()
    .await
}
```

---

### 4.3 CloudEvent Functions

```rust
use cloudevents::{Event as CloudEvent, EventBuilder, EventBuilderV10};

async fn handle_cloudevent(
    req: HttpRequest,
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("cloud-functions");
    
    // 解析 CloudEvent
    let event = cloudevents::event::Event::from_http_request(
        req.method().as_str(),
        req.uri().to_string(),
        req.headers(),
        Some(body.to_vec()),
    )
    .map_err(|e| actix_web::error::ErrorBadRequest(e))?;
    
    let mut span = tracer
        .span_builder("cloud_functions.cloudevent_invocation")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "pubsub"));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    
    // CloudEvent 属性
    span.set_attribute(KeyValue::new("cloudevents.event_id", event.id().to_string()));
    span.set_attribute(KeyValue::new("cloudevents.event_type", event.ty().to_string()));
    span.set_attribute(KeyValue::new("cloudevents.source", event.source().to_string()));
    span.set_attribute(KeyValue::new("cloudevents.specversion", event.specversion().to_string()));
    
    // 处理事件
    let result = process_cloudevent(&event).await;
    
    if result.is_err() {
        span.set_attribute(KeyValue::new("error", true));
        span.set_status(Status::error("Event processing failed"));
    }
    
    span.end();
    
    Ok(HttpResponse::NoContent().finish())
}

async fn process_cloudevent(event: &CloudEvent) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let span = tracer
        .span_builder("process_cloudevent_data")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Processing CloudEvent: {} (type: {})", event.id(), event.ty());
    
    // 根据事件类型处理
    match event.ty() {
        "google.cloud.pubsub.topic.v1.messagePublished" => {
            process_pubsub_message(event).await?;
        }
        "google.cloud.storage.object.v1.finalized" => {
            process_storage_object(event).await?;
        }
        "google.cloud.firestore.document.v1.created" => {
            process_firestore_document(event).await?;
        }
        _ => {
            tracing::warn!("Unknown event type: {}", event.ty());
        }
    }
    
    Ok(())
}
```

---

### 4.4 Pub/Sub 触发

```rust
use serde::{Deserialize, Serialize};
use base64::{Engine as _, engine::general_purpose};

#[derive(Deserialize)]
struct PubSubMessage {
    message: PubSubMessageData,
    subscription: String,
}

#[derive(Deserialize)]
struct PubSubMessageData {
    data: String, // Base64 编码
    #[serde(rename = "messageId")]
    message_id: String,
    #[serde(rename = "publishTime")]
    publish_time: String,
    attributes: Option<std::collections::HashMap<String, String>>,
}

async fn process_pubsub_message(event: &CloudEvent) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let mut span = tracer
        .span_builder("process_pubsub_message")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // 解析 Pub/Sub 消息
    let message: PubSubMessage = serde_json::from_value(event.data().unwrap().clone())?;
    
    // 添加 Pub/Sub 特定属性
    span.set_attribute(KeyValue::new("messaging.system", "gcp_pubsub"));
    span.set_attribute(KeyValue::new("messaging.message_id", message.message.message_id.clone()));
    span.set_attribute(KeyValue::new("messaging.destination", message.subscription.clone()));
    span.set_attribute(KeyValue::new(
        "gcp.pubsub.publish_time",
        message.message.publish_time.clone(),
    ));
    
    // 解码消息数据
    let decoded_data = general_purpose::STANDARD.decode(&message.message.data)?;
    let data_str = String::from_utf8(decoded_data)?;
    
    tracing::info!("Processing Pub/Sub message: {}", data_str);
    
    // 提取 trace context (如果有)
    if let Some(attributes) = &message.message.attributes {
        if let Some(trace_context) = attributes.get("googclient_traceparent") {
            span.set_attribute(KeyValue::new("gcp.pubsub.trace_context", trace_context.clone()));
        }
    }
    
    // 业务逻辑
    // ...
    
    span.end();
    Ok(())
}
```

---

### 4.5 Cloud Storage 触发

```rust
#[derive(Deserialize)]
struct StorageObject {
    name: String,
    bucket: String,
    #[serde(rename = "contentType")]
    content_type: Option<String>,
    size: String,
    #[serde(rename = "timeCreated")]
    time_created: String,
    updated: String,
}

async fn process_storage_object(event: &CloudEvent) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let mut span = tracer
        .span_builder("process_storage_object")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // 解析 Storage 对象
    let object: StorageObject = serde_json::from_value(event.data().unwrap().clone())?;
    
    // 添加 Cloud Storage 特定属性
    span.set_attribute(KeyValue::new("gcp.storage.bucket", object.bucket.clone()));
    span.set_attribute(KeyValue::new("gcp.storage.object.name", object.name.clone()));
    span.set_attribute(KeyValue::new(
        "gcp.storage.object.size",
        object.size.parse::<i64>().unwrap_or(0),
    ));
    
    if let Some(content_type) = &object.content_type {
        span.set_attribute(KeyValue::new("gcp.storage.object.content_type", content_type.clone()));
    }
    
    tracing::info!("Processing Storage object: gs://{}/{}", object.bucket, object.name);
    
    // 根据事件类型处理
    match event.ty() {
        "google.cloud.storage.object.v1.finalized" => {
            // 对象创建完成
            process_new_object(&object).await?;
        }
        "google.cloud.storage.object.v1.deleted" => {
            // 对象删除
            process_deleted_object(&object).await?;
        }
        _ => {}
    }
    
    span.end();
    Ok(())
}

async fn process_new_object(object: &StorageObject) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let span = tracer
        .span_builder("download_and_process")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    // 使用 Cloud Storage SDK 下载对象
    // let storage_client = ...;
    // let data = storage_client.download(&object.bucket, &object.name).await?;
    
    tracing::info!("Downloaded object: {}", object.name);
    
    // 处理数据
    // ...
    
    Ok(())
}

async fn process_deleted_object(object: &StorageObject) -> anyhow::Result<()> {
    tracing::info!("Object deleted: gs://{}/{}", object.bucket, object.name);
    Ok(())
}
```

---

### 4.6 Firestore 触发

```rust
#[derive(Deserialize)]
struct FirestoreDocument {
    name: String,
    fields: serde_json::Value,
    #[serde(rename = "createTime")]
    create_time: Option<String>,
    #[serde(rename = "updateTime")]
    update_time: String,
}

async fn process_firestore_document(event: &CloudEvent) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let mut span = tracer
        .span_builder("process_firestore_document")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // 解析 Firestore 文档
    let document: FirestoreDocument = serde_json::from_value(event.data().unwrap().clone())?;
    
    // 添加 Firestore 特定属性
    span.set_attribute(KeyValue::new("gcp.firestore.document.name", document.name.clone()));
    span.set_attribute(KeyValue::new("db.system", "firestore"));
    
    // 提取文档路径组件
    let path_parts: Vec<&str> = document.name.split('/').collect();
    if path_parts.len() >= 6 {
        let collection = path_parts[path_parts.len() - 2];
        let doc_id = path_parts[path_parts.len() - 1];
        
        span.set_attribute(KeyValue::new("gcp.firestore.collection", collection));
        span.set_attribute(KeyValue::new("gcp.firestore.document_id", doc_id));
    }
    
    tracing::info!("Processing Firestore document: {}", document.name);
    
    // 根据事件类型处理
    match event.ty() {
        "google.cloud.firestore.document.v1.created" => {
            process_document_created(&document).await?;
        }
        "google.cloud.firestore.document.v1.updated" => {
            process_document_updated(&document).await?;
        }
        "google.cloud.firestore.document.v1.deleted" => {
            process_document_deleted(&document).await?;
        }
        _ => {}
    }
    
    span.end();
    Ok(())
}

async fn process_document_created(document: &FirestoreDocument) -> anyhow::Result<()> {
    let tracer = global::tracer("cloud-functions");
    let span = tracer
        .span_builder("handle_document_created")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Document created: {}", document.name);
    tracing::debug!("Fields: {:?}", document.fields);
    
    // 业务逻辑
    // ...
    
    Ok(())
}

async fn process_document_updated(document: &FirestoreDocument) -> anyhow::Result<()> {
    tracing::info!("Document updated: {}", document.name);
    Ok(())
}

async fn process_document_deleted(document: &FirestoreDocument) -> anyhow::Result<()> {
    tracing::info!("Document deleted: {}", document.name);
    Ok(())
}
```

---

## 5. OTLP 与 Cloud Trace 集成

### 5.1 同时使用 OTLP 和 Cloud Trace

```rust
use opentelemetry::trace::{Span, SpanContext, TraceId, SpanId};

/// 从 Cloud Trace header 创建 span context
pub fn parse_cloud_trace_context(header: &str) -> Option<SpanContext> {
    // 格式: "TRACE_ID/SPAN_ID;o=TRACE_TRUE"
    let parts: Vec<&str> = header.split('/').collect();
    if parts.len() != 2 {
        return None;
    }
    
    let trace_id = TraceId::from_hex(parts[0]).ok()?;
    
    let span_parts: Vec<&str> = parts[1].split(';').collect();
    let span_id = SpanId::from_hex(span_parts[0]).ok()?;
    
    Some(SpanContext::new(
        trace_id,
        span_id,
        opentelemetry::trace::TraceFlags::SAMPLED,
        true,
        Default::default(),
    ))
}

/// 将 OpenTelemetry trace context 转换为 Cloud Trace 格式
pub fn to_cloud_trace_header(cx: &opentelemetry::Context) -> String {
    let span = cx.span();
    let span_context = span.span_context();
    
    format!(
        "{}/{}",
        span_context.trace_id(),
        span_context.span_id()
    )
}
```

### 5.2 Cloud Logging 集成

```rust
use serde_json::json;

/// 输出结构化日志 (Cloud Logging 格式)
pub fn log_with_trace(message: &str, severity: &str, cx: &opentelemetry::Context) {
    let span = cx.span();
    let span_context = span.span_context();
    
    let log_entry = json!({
        "severity": severity,
        "message": message,
        "logging.googleapis.com/trace": format!(
            "projects/{}/traces/{}",
            std::env::var("GCP_PROJECT").unwrap_or_default(),
            span_context.trace_id()
        ),
        "logging.googleapis.com/spanId": span_context.span_id().to_string(),
        "logging.googleapis.com/trace_sampled": span_context.trace_flags().is_sampled(),
    });
    
    println!("{}", log_entry);
}
```

---

## 6. 最佳实践

### 6.1 冷启动优化

```rust
// 1. 使用 lazy_static 预初始化
use lazy_static::lazy_static;

lazy_static! {
    static ref STORAGE_CLIENT: google_cloud_storage::client::Client = {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            google_cloud_storage::client::Client::default().await.unwrap()
        })
    };
}

// 2. 编译优化
// Cargo.toml
[profile.release]
opt-level = 'z'     # 优化大小
lto = true          # 链接时优化
codegen-units = 1   # 更好的优化
strip = true        # 去除调试符号
panic = 'abort'     # 更小的二进制

// 3. 使用 musl 目标
// 编译命令
// rustup target add x86_64-unknown-linux-musl
// cargo build --release --target x86_64-unknown-linux-musl
```

### 6.2 并发处理

```rust
// 利用 Cloud Functions 2nd Gen 的并发能力
use std::sync::Arc;
use tokio::sync::Semaphore;

lazy_static! {
    static ref CONCURRENCY_SEMAPHORE: Arc<Semaphore> = {
        // 限制并发数
        let max_concurrent = std::env::var("MAX_CONCURRENT_REQUESTS")
            .unwrap_or_else(|_| "100".to_string())
            .parse::<usize>()
            .unwrap_or(100);
        Arc::new(Semaphore::new(max_concurrent))
    };
}

async fn handle_request_with_concurrency_control(
    /* ... */
) -> Result<HttpResponse, actix_web::Error> {
    // 获取信号量许可
    let _permit = CONCURRENCY_SEMAPHORE.acquire().await.unwrap();
    
    // 处理请求
    handle_http_request(/* ... */).await
}
```

### 6.3 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum FunctionError {
    #[error("GCP Storage error: {0}")]
    StorageError(String),
    
    #[error("Pub/Sub error: {0}")]
    PubSubError(String),
    
    #[error("Firestore error: {0}")]
    FirestoreError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    
    #[error("Business logic error: {0}")]
    BusinessError(String),
}

impl actix_web::error::ResponseError for FunctionError {
    fn error_response(&self) -> HttpResponse {
        // 记录到 span
        let span = opentelemetry::Context::current().span();
        span.set_attribute(KeyValue::new("error", true));
        span.set_attribute(KeyValue::new("error.message", self.to_string()));
        
        HttpResponse::InternalServerError().json(serde_json::json!({
            "error": self.to_string()
        }))
    }
}
```

---

## 7. 性能优化

### 7.1 内存优化

```rust
// 使用 jemalloc
use tikv_jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
```

### 7.2 二进制大小优化

```bash
# 使用 cargo-strip
cargo install cargo-strip
cargo build --release --target x86_64-unknown-linux-musl
cargo strip

# 使用 UPX 压缩
upx --best --lzma target/x86_64-unknown-linux-musl/release/gcp-function-rust

# 最终大小对比
# 未优化: ~20MB
# strip + UPX: ~3MB
```

---

## 8. 部署

### 8.1 Dockerfile

```dockerfile
# 多阶段构建
FROM rust:1.75 as builder

WORKDIR /app
COPY . .

# 编译
RUN cargo build --release --target x86_64-unknown-linux-musl

# 运行时镜像
FROM gcr.io/distroless/static-debian11

COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/gcp-function-rust /app

EXPOSE 8080
CMD ["/app"]
```

### 8.2 部署到 Cloud Functions 2nd Gen

```bash
# 使用 gcloud CLI
gcloud functions deploy my-rust-function \
  --gen2 \
  --runtime=gcfv2 \
  --region=us-central1 \
  --source=. \
  --entry-point=main \
  --trigger-http \
  --allow-unauthenticated \
  --set-env-vars "OTLP_ENDPOINT=https://collector:4317,RUST_LOG=info"

# 查看日志
gcloud functions logs read my-rust-function --region=us-central1
```

### 8.3 使用 Cloud Build

```yaml
# cloudbuild.yaml
steps:
  # 构建 Docker 镜像
  - name: 'gcr.io/cloud-builders/docker'
    args:
      - 'build'
      - '-t'
      - 'gcr.io/$PROJECT_ID/rust-function:$BUILD_ID'
      - '.'
  
  # 推送到 Container Registry
  - name: 'gcr.io/cloud-builders/docker'
    args:
      - 'push'
      - 'gcr.io/$PROJECT_ID/rust-function:$BUILD_ID'
  
  # 部署到 Cloud Functions
  - name: 'gcr.io/google.com/cloudsdktool/cloud-sdk'
    args:
      - 'gcloud'
      - 'functions'
      - 'deploy'
      - 'rust-function'
      - '--gen2'
      - '--runtime=gcfv2'
      - '--region=us-central1'
      - '--source=gs://$PROJECT_ID-gcf-source'
      - '--entry-point=main'
      - '--trigger-http'

images:
  - 'gcr.io/$PROJECT_ID/rust-function:$BUILD_ID'
```

---

## 参考资源

1. **Cloud Functions 2nd Gen**: <https://cloud.google.com/functions/docs/2nd-gen/overview>
2. **CloudEvents**: <https://cloudevents.io/>
3. **Google Cloud Rust SDK**: <https://github.com/googleapis/google-cloud-rust>
4. **OpenTelemetry Stackdriver**: <https://github.com/open-telemetry/opentelemetry-rust-contrib/tree/main/opentelemetry-stackdriver>
5. **Cloud Trace**: <https://cloud.google.com/trace/docs>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
