# Azure Functions 语义约定 - Rust 完整实现

> **Serverless 计算**: Azure Functions 完整 Tracing 与 Metrics 规范 (Rust 版本)  
> **最后更新**: 2025年10月10日

---

## 目录

- [Azure Functions 语义约定 - Rust 完整实现](#azure-functions-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. Azure Functions 概述](#1-azure-functions-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 Custom Handler 架构](#12-custom-handler-架构)
  - [2. Functions Resource 属性](#2-functions-resource-属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Functions Span 属性](#3-functions-span-属性)
  - [4. Rust 完整实现](#4-rust-完整实现)
    - [4.1 基础设施](#41-基础设施)
      - [Cargo.toml](#cargotoml)
      - [核心 OTLP 模块](#核心-otlp-模块)
    - [4.2 HTTP 触发器](#42-http-触发器)
      - [function.json](#functionjson)
      - [Rust 实现](#rust-实现)
    - [4.3 Timer 触发器](#43-timer-触发器)
      - [4.3.1 function.json](#431-functionjson)
      - [4.3.2 Rust 实现](#432-rust-实现)
    - [4.4 Blob Storage 触发器](#44-blob-storage-触发器)
    - [4.5 Queue Storage 触发器](#45-queue-storage-触发器)
    - [4.6 Event Hub 触发器](#46-event-hub-触发器)
  - [5. OTLP 集成](#5-otlp-集成)
    - [5.1 host.json 配置](#51-hostjson-配置)
    - [5.2 local.settings.json (开发)](#52-localsettingsjson-开发)
  - [6. Durable Functions 支持](#6-durable-functions-支持)
    - [6.1 Orchestrator 实现](#61-orchestrator-实现)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 冷启动优化](#71-冷启动优化)
    - [7.2 错误处理](#72-错误处理)
    - [7.3 并发处理](#73-并发处理)
  - [8. 部署与监控](#8-部署与监控)
    - [8.1 Docker 部署](#81-docker-部署)
    - [8.2 Azure 部署](#82-azure-部署)
  - [参考资源](#参考资源)

---

## 1. Azure Functions 概述

### 1.1 核心特性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Functions - Serverless 计算平台

核心特性:
✅ 事件驱动
✅ 自动扩展
✅ 多语言支持 (C#/Java/JavaScript/Python/PowerShell)
✅ Rust 支持 (通过 Custom Handler)
✅ 与 Azure 服务集成
✅ Durable Functions (有状态工作流)
✅ 混合部署

托管计划:
1. Consumption (消费型)
   - 按需付费
   - 自动扩展
   - 冷启动

2. Premium
   - 预热实例
   - 无冷启动
   - VNet 集成
   - 最大实例数可配置

3. Dedicated (App Service Plan)
   - 专用 VM
   - 可预测成本
   - 可用于长时间运行的任务

Rust 优势:
✅ 极快启动时间
✅ 低内存占用
✅ 高性能
✅ 类型安全
✅ 零成本抽象

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 Custom Handler 架构

```text
┌─────────────────────────────────────────┐
│       Azure Functions Host              │
│                                         │
│  ┌─────────────────────────────────┐  │
│  │   Functions Runtime             │  │
│  │   - 触发器管理                   │  │
│  │   - 绑定处理                     │  │
│  │   - 日志聚合                     │  │
│  └───────────────┬─────────────────┘  │
│                  │ HTTP                │
│                  ▼                     │
│  ┌─────────────────────────────────┐  │
│  │   Custom Handler (Rust)         │  │
│  │   - 接收 HTTP 请求               │  │
│  │   - 处理业务逻辑                 │  │
│  │   - 返回 JSON 响应               │  │
│  │   - OTLP Tracing                │  │
│  └─────────────────────────────────┘  │
└─────────────────────────────────────────┘
```

---

## 2. Functions Resource 属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"azure"` |
| `cloud.platform` | string | 平台类型 | `"azure_functions"` |
| `cloud.region` | string | Azure 区域 | `"eastus"` |
| `faas.name` | string | 函数名称 | `"MyFunction"` |
| `faas.version` | string | 函数版本 | `"1.0.0"` |
| `azure.functions.app_name` | string | 函数应用名称 | `"my-func-app"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.instance` | string | 实例ID | Azure 自动生成 |
| `azure.subscription_id` | string | 订阅ID | - |
| `azure.resource_group` | string | 资源组 | `"my-rg"` |
| `azure.functions.plan` | string | 托管计划 | `"Consumption"`, `"Premium"` |

---

## 3. Functions Span 属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.trigger` | string | 触发类型 | `"http"`, `"timer"`, `"datasource"` |
| `faas.invocation_id` | string | 调用ID | 函数运行时提供 |
| `faas.coldstart` | boolean | 是否冷启动 | `true`/`false` |
| `azure.functions.trigger_type` | string | Azure 触发器类型 | `"httpTrigger"`, `"blobTrigger"` |

---

## 4. Rust 完整实现

### 4.1 基础设施

#### Cargo.toml

```toml
[package]
name = "azure-function-rust"
version = "0.1.0"
edition = "2021"

[dependencies]
# HTTP 服务器
actix-web = "4"
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
uuid = { version = "1.0", features = ["v4", "serde"] }

# Azure SDK
azure_core = "0.19"
azure_storage = "0.19"
azure_storage_blobs = "0.19"
azure_storage_queues = "0.19"
azure_messaging_eventhubs = "0.18"

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.15", features = ["grpc-tonic"] }
opentelemetry-semantic-conventions = "0.14"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.23"
tracing-actix-web = "0.7"

# 实用工具
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

/// Azure Functions OTLP 配置
pub struct AzureFunctionsOtlpConfig {
    pub otlp_endpoint: String,
    pub service_name: String,
    pub service_version: String,
}

impl Default for AzureFunctionsOtlpConfig {
    fn default() -> Self {
        Self {
            otlp_endpoint: std::env::var("OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            service_name: std::env::var("AZURE_FUNCTIONS_APP_NAME")
                .or_else(|_| std::env::var("WEBSITE_SITE_NAME"))
                .unwrap_or_else(|_| "azure-function".to_string()),
            service_version: std::env::var("FUNCTION_VERSION")
                .unwrap_or_else(|_| "1.0.0".to_string()),
        }
    }
}

/// 初始化 OTLP Tracer
pub fn init_tracer(config: AzureFunctionsOtlpConfig) -> anyhow::Result<SdkTracer> {
    // 构建 Azure Functions Resource 属性
    let resource = Resource::new(vec![
        // 云平台属性
        KeyValue::new("cloud.provider", "azure"),
        KeyValue::new("cloud.platform", "azure_functions"),
        KeyValue::new(
            "cloud.region",
            std::env::var("REGION_NAME").unwrap_or_else(|_| "eastus".to_string()),
        ),
        
        // FaaS 属性
        KeyValue::new("faas.name", config.service_name.clone()),
        KeyValue::new("faas.version", config.service_version.clone()),
        
        // Azure 特定属性
        KeyValue::new(
            "azure.functions.app_name",
            std::env::var("WEBSITE_SITE_NAME").unwrap_or_default(),
        ),
        KeyValue::new(
            "azure.subscription_id",
            std::env::var("WEBSITE_OWNER_NAME")
                .unwrap_or_default()
                .split('+')
                .next()
                .unwrap_or(""),
        ),
        KeyValue::new(
            "azure.resource_group",
            std::env::var("WEBSITE_RESOURCE_GROUP").unwrap_or_default(),
        ),
        KeyValue::new(
            "azure.functions.plan",
            detect_plan_type(),
        ),
        
        // 服务属性
        KeyValue::new("service.name", config.service_name),
        KeyValue::new("service.version", config.service_version),
    ]);

    // 配置 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&config.otlp_endpoint)
        .with_timeout(Duration::from_secs(3));

    // 创建 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_batch_exporter(exporter.build_span_exporter()?, opentelemetry_sdk::runtime::Tokio)
        .build();

    let tracer = tracer_provider.tracer("azure-functions");

    // 设置全局 tracer provider
    global::set_tracer_provider(tracer_provider);

    Ok(tracer)
}

/// 检测托管计划类型
fn detect_plan_type() -> String {
    if std::env::var("WEBSITE_SKU").is_ok() {
        std::env::var("WEBSITE_SKU").unwrap_or_else(|_| "Dynamic".to_string())
    } else {
        "Unknown".to_string()
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
```

---

### 4.2 HTTP 触发器

#### function.json

```json
{
  "bindings": [
    {
      "authLevel": "function",
      "type": "httpTrigger",
      "direction": "in",
      "name": "req",
      "methods": ["get", "post"],
      "route": "users/{id?}"
    },
    {
      "type": "http",
      "direction": "out",
      "name": "res"
    }
  ]
}
```

#### Rust 实现

```rust
use actix_web::{web, App, HttpRequest, HttpResponse, HttpServer};
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
}

#[derive(Deserialize)]
struct FunctionRequest {
    #[serde(rename = "Data")]
    data: serde_json::Value,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct RequestMetadata {
    #[serde(rename = "InvocationId")]
    invocation_id: String,
    #[serde(rename = "sys")]
    sys: SystemMetadata,
}

#[derive(Deserialize)]
struct SystemMetadata {
    #[serde(rename = "MethodName")]
    method_name: String,
}

async fn handle_http_request(
    req: HttpRequest,
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    
    // 解析 Azure Functions 请求格式
    let function_req: FunctionRequest = serde_json::from_slice(&body)?;
    
    // 创建 span
    let mut span = tracer
        .span_builder("azure_functions.invocation")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 添加 FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "http"));
    span.set_attribute(KeyValue::new(
        "faas.invocation_id",
        function_req.metadata.invocation_id.clone(),
    ));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    span.set_attribute(KeyValue::new(
        "azure.functions.trigger_type",
        "httpTrigger",
    ));
    
    // HTTP 属性
    span.set_attribute(KeyValue::new("http.method", req.method().as_str()));
    span.set_attribute(KeyValue::new("http.target", req.uri().path()));
    span.set_attribute(KeyValue::new("http.scheme", req.connection_info().scheme()));
    
    // 处理请求
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let result = process_http_request_with_context(&function_req, cx).await;
    
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
    request: &FunctionRequest,
    cx: opentelemetry::Context,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let _guard = cx.attach();
    
    // 解析请求数据
    let data = &request.data;
    
    // 根据 HTTP 方法处理
    if let Some(method) = data.get("Method").and_then(|v| v.as_str()) {
        match method {
            "POST" => {
                let span = tracer
                    .span_builder("create_user")
                    .with_kind(SpanKind::Internal)
                    .start(&tracer);
                let _cx = opentelemetry::Context::current_with_span(span);
                
                // 解析用户数据
                let user_req: CreateUserRequest = 
                    serde_json::from_value(data["Body"].clone())?;
                
                let user_id = uuid::Uuid::new_v4().to_string();
                let response = CreateUserResponse {
                    id: user_id,
                    name: user_req.name,
                    email: user_req.email,
                };
                
                Ok(HttpResponse::Ok()
                    .content_type("application/json")
                    .json(serde_json::json!({
                        "Outputs": {
                            "res": {
                                "StatusCode": 201,
                                "Body": response
                            }
                        }
                    })))
            }
            "GET" => {
                let span = tracer
                    .span_builder("get_users")
                    .with_kind(SpanKind::Internal)
                    .start(&tracer);
                let _cx = opentelemetry::Context::current_with_span(span);
                
                Ok(HttpResponse::Ok()
                    .content_type("application/json")
                    .json(serde_json::json!({
                        "Outputs": {
                            "res": {
                                "StatusCode": 200,
                                "Body": {"users": []}
                            }
                        }
                    })))
            }
            _ => Ok(HttpResponse::MethodNotAllowed().finish()),
        }
    } else {
        Ok(HttpResponse::BadRequest().finish())
    }
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化 OTLP
    let config = AzureFunctionsOtlpConfig::default();
    init_tracer(config).expect("Failed to initialize tracer");
    
    // Custom Handler 端口
    let port = std::env::var("FUNCTIONS_CUSTOMHANDLER_PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse::<u16>()
        .unwrap_or(8080);
    
    println!("Azure Functions Custom Handler listening on port {}", port);
    
    HttpServer::new(|| {
        App::new()
            .route("/{function_name}", web::post().to(handle_http_request))
    })
    .bind(("127.0.0.1", port))?
    .run()
    .await
}
```

---

### 4.3 Timer 触发器

#### 4.3.1 function.json

```json
{
  "bindings": [
    {
      "name": "timer",
      "type": "timerTrigger",
      "direction": "in",
      "schedule": "0 */5 * * * *"
    }
  ]
}
```

#### 4.3.2 Rust 实现

```rust
#[derive(Deserialize)]
struct TimerRequest {
    #[serde(rename = "Data")]
    data: TimerData,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct TimerData {
    #[serde(rename = "ScheduleStatus")]
    schedule_status: ScheduleStatus,
    #[serde(rename = "IsPastDue")]
    is_past_due: bool,
}

#[derive(Deserialize)]
struct ScheduleStatus {
    #[serde(rename = "Last")]
    last: String,
    #[serde(rename = "Next")]
    next: String,
}

async fn handle_timer_trigger(
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let timer_req: TimerRequest = serde_json::from_slice(&body)?;
    
    let mut span = tracer
        .span_builder("azure_functions.timer_invocation")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "timer"));
    span.set_attribute(KeyValue::new(
        "faas.invocation_id",
        timer_req.metadata.invocation_id.clone(),
    ));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    span.set_attribute(KeyValue::new("azure.functions.trigger_type", "timerTrigger"));
    
    // Timer 特定属性
    span.set_attribute(KeyValue::new(
        "azure.functions.timer.is_past_due",
        timer_req.data.is_past_due,
    ));
    span.set_attribute(KeyValue::new(
        "azure.functions.timer.last_execution",
        timer_req.data.schedule_status.last.clone(),
    ));
    span.set_attribute(KeyValue::new(
        "azure.functions.timer.next_execution",
        timer_req.data.schedule_status.next.clone(),
    ));
    
    // 执行定时任务
    let result = execute_scheduled_task().await;
    
    if result.is_err() {
        span.set_attribute(KeyValue::new("error", true));
        span.set_status(Status::error("Task failed"));
    } else {
        span.set_status(Status::Ok);
    }
    
    span.end();
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "Outputs": {},
        "Logs": ["Timer task completed"]
    })))
}

async fn execute_scheduled_task() -> anyhow::Result<()> {
    let tracer = global::tracer("azure-functions");
    let span = tracer
        .span_builder("scheduled_task")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Executing scheduled task");
    
    // 任务逻辑
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    Ok(())
}
```

---

### 4.4 Blob Storage 触发器

```rust
use azure_storage_blobs::prelude::*;

#[derive(Deserialize)]
struct BlobTriggerRequest {
    #[serde(rename = "Data")]
    data: BlobData,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct BlobData {
    #[serde(rename = "BlobTrigger")]
    blob_trigger: String,
    #[serde(rename = "Uri")]
    uri: String,
    #[serde(rename = "Properties")]
    properties: BlobProperties,
}

#[derive(Deserialize)]
struct BlobProperties {
    #[serde(rename = "Length")]
    length: i64,
    #[serde(rename = "ContentType")]
    content_type: Option<String>,
}

async fn handle_blob_trigger(
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let blob_req: BlobTriggerRequest = serde_json::from_slice(&body)?;
    
    let mut span = tracer
        .span_builder("azure_functions.blob_invocation")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "datasource"));
    span.set_attribute(KeyValue::new(
        "faas.invocation_id",
        blob_req.metadata.invocation_id.clone(),
    ));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    
    // Blob 特定属性
    span.set_attribute(KeyValue::new("azure.storage.blob.name", blob_req.data.blob_trigger.clone()));
    span.set_attribute(KeyValue::new("azure.storage.blob.uri", blob_req.data.uri.clone()));
    span.set_attribute(KeyValue::new("azure.storage.blob.size", blob_req.data.properties.length));
    
    if let Some(content_type) = &blob_req.data.properties.content_type {
        span.set_attribute(KeyValue::new("azure.storage.blob.content_type", content_type.clone()));
    }
    
    // 处理 Blob
    let result = process_blob(&blob_req.data).await;
    
    match result {
        Ok(_) => span.set_status(Status::Ok),
        Err(e) => {
            span.set_attribute(KeyValue::new("error", true));
            span.set_attribute(KeyValue::new("error.message", e.to_string()));
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    span.end();
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "Outputs": {},
        "Logs": ["Blob processed"]
    })))
}

async fn process_blob(blob_data: &BlobData) -> anyhow::Result<()> {
    let tracer = global::tracer("azure-functions");
    let span = tracer
        .span_builder("download_and_process_blob")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Processing blob: {}", blob_data.blob_trigger);
    
    // 下载并处理 Blob
    // 使用 Azure Storage SDK
    
    Ok(())
}
```

---

### 4.5 Queue Storage 触发器

```rust
#[derive(Deserialize)]
struct QueueTriggerRequest {
    #[serde(rename = "Data")]
    data: QueueData,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct QueueData {
    #[serde(rename = "QueueTrigger")]
    queue_trigger: String,
    #[serde(rename = "DequeueCount")]
    dequeue_count: i32,
    #[serde(rename = "Id")]
    id: String,
    #[serde(rename = "PopReceipt")]
    pop_receipt: String,
}

async fn handle_queue_trigger(
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let queue_req: QueueTriggerRequest = serde_json::from_slice(&body)?;
    
    let mut span = tracer
        .span_builder("azure_functions.queue_invocation")
        .with_kind(SpanKind::Consumer)
        .start(&tracer);
    
    // FaaS 属性
    span.set_attribute(KeyValue::new("faas.trigger", "pubsub"));
    span.set_attribute(KeyValue::new(
        "faas.invocation_id",
        queue_req.metadata.invocation_id.clone(),
    ));
    
    // Queue 特定属性
    span.set_attribute(KeyValue::new("messaging.system", "azure_storage_queue"));
    span.set_attribute(KeyValue::new("messaging.message_id", queue_req.data.id.clone()));
    span.set_attribute(KeyValue::new(
        "azure.storage.queue.dequeue_count",
        queue_req.data.dequeue_count as i64,
    ));
    
    // 处理消息
    let result = process_queue_message(&queue_req.data).await;
    
    match result {
        Ok(_) => span.set_status(Status::Ok),
        Err(e) => {
            span.set_attribute(KeyValue::new("error", true));
            span.set_status(Status::error(e.to_string()));
        }
    }
    
    span.end();
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "Outputs": {},
        "Logs": ["Queue message processed"]
    })))
}

async fn process_queue_message(queue_data: &QueueData) -> anyhow::Result<()> {
    let tracer = global::tracer("azure-functions");
    let span = tracer
        .span_builder("process_queue_message")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Processing queue message: {}", queue_data.queue_trigger);
    
    // 业务逻辑
    
    Ok(())
}
```

---

### 4.6 Event Hub 触发器

```rust
#[derive(Deserialize)]
struct EventHubTriggerRequest {
    #[serde(rename = "Data")]
    data: EventHubData,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct EventHubData {
    #[serde(rename = "Events")]
    events: Vec<EventHubEvent>,
}

#[derive(Deserialize)]
struct EventHubEvent {
    #[serde(rename = "Body")]
    body: serde_json::Value,
    #[serde(rename = "PartitionKey")]
    partition_key: Option<String>,
    #[serde(rename = "SequenceNumber")]
    sequence_number: i64,
    #[serde(rename = "Offset")]
    offset: String,
}

async fn handle_eventhub_trigger(
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let eh_req: EventHubTriggerRequest = serde_json::from_slice(&body)?;
    
    // 处理每个事件
    for event in &eh_req.data.events {
        let mut span = tracer
            .span_builder("azure_functions.eventhub_process_event")
            .with_kind(SpanKind::Consumer)
            .start(&tracer);
        
        // FaaS 属性
        span.set_attribute(KeyValue::new("faas.trigger", "pubsub"));
        span.set_attribute(KeyValue::new(
            "faas.invocation_id",
            eh_req.metadata.invocation_id.clone(),
        ));
        
        // Event Hub 特定属性
        span.set_attribute(KeyValue::new("messaging.system", "azure_eventhubs"));
        span.set_attribute(KeyValue::new(
            "messaging.azure.eventhubs.sequence_number",
            event.sequence_number,
        ));
        span.set_attribute(KeyValue::new(
            "messaging.azure.eventhubs.offset",
            event.offset.clone(),
        ));
        
        if let Some(partition_key) = &event.partition_key {
            span.set_attribute(KeyValue::new(
                "messaging.azure.eventhubs.partition_key",
                partition_key.clone(),
            ));
        }
        
        // 处理事件
        let result = process_eventhub_event(event).await;
        
        if result.is_err() {
            span.set_attribute(KeyValue::new("error", true));
            span.set_status(Status::error("Event processing failed"));
        }
        
        span.end();
    }
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "Outputs": {},
        "Logs": ["Events processed"]
    })))
}

async fn process_eventhub_event(event: &EventHubEvent) -> anyhow::Result<()> {
    let tracer = global::tracer("azure-functions");
    let span = tracer
        .span_builder("process_event_body")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    tracing::info!("Processing event: {:?}", event.body);
    
    // 业务逻辑
    
    Ok(())
}
```

---

## 5. OTLP 集成

### 5.1 host.json 配置

```json
{
  "version": "2.0",
  "customHandler": {
    "description": {
      "defaultExecutablePath": "handler",
      "workingDirectory": "",
      "arguments": []
    },
    "enableForwardingHttpRequest": true
  },
  "logging": {
    "logLevel": {
      "default": "Information"
    }
  }
}
```

### 5.2 local.settings.json (开发)

```json
{
  "IsEncrypted": false,
  "Values": {
    "AzureWebJobsStorage": "UseDevelopmentStorage=true",
    "FUNCTIONS_WORKER_RUNTIME": "custom",
    "OTLP_ENDPOINT": "http://localhost:4317",
    "RUST_LOG": "info"
  }
}
```

---

## 6. Durable Functions 支持

### 6.1 Orchestrator 实现

```rust
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct OrchestrationRequest {
    #[serde(rename = "Data")]
    data: OrchestrationData,
    #[serde(rename = "Metadata")]
    metadata: RequestMetadata,
}

#[derive(Deserialize)]
struct OrchestrationData {
    #[serde(rename = "Input")]
    input: serde_json::Value,
    #[serde(rename = "InstanceId")]
    instance_id: String,
}

#[derive(Serialize)]
struct ActivityCallAction {
    #[serde(rename = "actionType")]
    action_type: String,
    #[serde(rename = "functionName")]
    function_name: String,
    #[serde(rename = "input")]
    input: serde_json::Value,
}

async fn handle_orchestrator(
    body: web::Bytes,
) -> Result<HttpResponse, actix_web::Error> {
    let tracer = global::tracer("azure-functions");
    let orch_req: OrchestrationRequest = serde_json::from_slice(&body)?;
    
    let mut span = tracer
        .span_builder("azure_functions.orchestration")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("faas.trigger", "orchestration"));
    span.set_attribute(KeyValue::new(
        "azure.durable_functions.instance_id",
        orch_req.data.instance_id.clone(),
    ));
    
    // 编排逻辑：调用多个活动函数
    let actions = vec![
        ActivityCallAction {
            action_type: "CallActivity".to_string(),
            function_name: "Activity1".to_string(),
            input: serde_json::json!({"step": 1}),
        },
        ActivityCallAction {
            action_type: "CallActivity".to_string(),
            function_name: "Activity2".to_string(),
            input: serde_json::json!({"step": 2}),
        },
    ];
    
    span.end();
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "actions": actions
    })))
}
```

---

## 7. 最佳实践

### 7.1 冷启动优化

```rust
// 使用 lazy_static 预初始化
use lazy_static::lazy_static;

lazy_static! {
    static ref BLOB_CLIENT: ContainerClient = {
        let connection_string = std::env::var("AzureWebJobsStorage").unwrap();
        let storage_account = StorageAccountClient::new_connection_string(&connection_string);
        storage_account.container_client("my-container")
    };
}

// 编译优化
// Cargo.toml
[profile.release]
opt-level = 'z'
lto = true
codegen-units = 1
strip = true
```

### 7.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum FunctionError {
    #[error("Azure Storage error: {0}")]
    StorageError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    
    #[error("Business logic error: {0}")]
    BusinessError(String),
}

// 统一错误响应
impl From<FunctionError> for HttpResponse {
    fn from(error: FunctionError) -> Self {
        let span = opentelemetry::Context::current().span();
        span.set_attribute(KeyValue::new("error", true));
        span.set_attribute(KeyValue::new("error.message", error.to_string()));
        
        HttpResponse::InternalServerError().json(serde_json::json!({
            "Outputs": {
                "res": {
                    "StatusCode": 500,
                    "Body": {"error": error.to_string()}
                }
            }
        }))
    }
}
```

### 7.3 并发处理

```rust
// 并发处理多个事件
use futures::stream::{self, StreamExt};

async fn process_events_concurrently(events: Vec<EventHubEvent>) -> anyhow::Result<()> {
    stream::iter(events)
        .map(|event| async move {
            process_eventhub_event(&event).await
        })
        .buffer_unordered(10) // 最多 10 个并发
        .collect::<Vec<_>>()
        .await;
    
    Ok(())
}
```

---

## 8. 部署与监控

### 8.1 Docker 部署

```dockerfile
FROM rust:1.75 as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates
COPY --from=builder /app/target/release/handler /usr/local/bin/handler
CMD ["handler"]
```

### 8.2 Azure 部署

```bash
# 编译
cargo build --release --target x86_64-unknown-linux-musl

# 创建部署包
mkdir -p deploy
cp target/x86_64-unknown-linux-musl/release/handler deploy/
cp host.json deploy/
cp -r functions deploy/

# 部署到 Azure
az functionapp deployment source config-zip \
  -g MyResourceGroup \
  -n MyFunctionApp \
  --src deploy.zip
```

---

## 参考资源

1. **Azure Functions Custom Handlers**: <https://docs.microsoft.com/azure/azure-functions/functions-custom-handlers>
2. **Azure SDK for Rust**: <https://github.com/Azure/azure-sdk-for-rust>
3. **OpenTelemetry Rust**: <https://github.com/open-telemetry/opentelemetry-rust>
4. **Actix Web**: <https://actix.rs/>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
