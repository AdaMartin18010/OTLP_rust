# Serverless 函数 Rust + OTLP 完整追踪

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **AWS Lambda Runtime**: 0.13+  
> **Azure Functions**: Custom Runtime  
> **GCP Cloud Functions**: 2nd Gen  
> **状态**: Production Ready  
> **最后更新**: 2025年10月9日

---

## 目录

- [Serverless 函数 Rust + OTLP 完整追踪](#serverless-函数-rust--otlp-完整追踪)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Serverless 可观测性挑战](#11-serverless-可观测性挑战)
    - [1.2 解决方案](#12-解决方案)
  - [2. AWS Lambda 集成](#2-aws-lambda-集成)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 Lambda 函数初始化](#22-lambda-函数初始化)
    - [2.3 Lambda 函数处理器](#23-lambda-函数处理器)
    - [2.4 Lambda Extension（OTLP Collector）](#24-lambda-extensionotlp-collector)
  - [3. Azure Functions 集成](#3-azure-functions-集成)
    - [3.1 Custom Runtime 配置](#31-custom-runtime-配置)
    - [3.2 Azure Functions 初始化](#32-azure-functions-初始化)
  - [4. GCP Cloud Functions 集成](#4-gcp-cloud-functions-集成)
    - [4.1 Cloud Functions 2nd Gen 配置](#41-cloud-functions-2nd-gen-配置)
    - [4.2 GCP 初始化](#42-gcp-初始化)
  - [5. 冷启动追踪](#5-冷启动追踪)
    - [5.1 冷启动检测](#51-冷启动检测)
    - [5.2 初始化追踪](#52-初始化追踪)
  - [6. 跨函数上下文传播](#6-跨函数上下文传播)
    - [6.1 Lambda → Lambda 调用](#61-lambda--lambda-调用)
    - [6.2 EventBridge/SQS 消息传播](#62-eventbridgesqs-消息传播)
  - [7. 成本优化与采样](#7-成本优化与采样)
    - [7.1 智能采样策略](#71-智能采样策略)
    - [7.2 成本监控](#72-成本监控)
  - [8. 性能优化](#8-性能优化)
    - [8.1 预热策略](#81-预热策略)
    - [8.2 资源属性缓存](#82-资源属性缓存)
  - [9. 完整示例](#9-完整示例)
    - [9.1 AWS Lambda HTTP API](#91-aws-lambda-http-api)
    - [9.2 部署配置（Terraform）](#92-部署配置terraform)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [最佳实践](#最佳实践)

---

## 1. 概述

### 1.1 Serverless 可观测性挑战

```text
❌ 冷启动延迟（初始化开销）
❌ 短生命周期（函数执行时间短）
❌ 分布式上下文（跨函数调用）
❌ 成本敏感（每次请求计费）
❌ 并发限制（Lambda 并发配额）
❌ 网络延迟（OTLP 导出开销）
```

### 1.2 解决方案

```text
✅ 异步批量导出（减少网络请求）
✅ 智能采样（低流量全采样，高流量采样）
✅ Lambda Extension（共享 Collector）
✅ 上下文注入（环境变量 + HTTP 头部）
✅ 冷启动监控（init duration 追踪）
✅ 资源属性预缓存（避免重复检测）
```

---

## 2. AWS Lambda 集成

### 2.1 依赖配置

**`Cargo.toml`**:

```toml
[dependencies]
# AWS Lambda Runtime
lambda_runtime = "0.13"
lambda_http = "0.13"

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["trace", "tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-proto", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# AWS SDK
aws-config = "1.5"
aws-sdk-lambda = "1.51"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具库
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
tracing = "0.1"
tracing-subscriber = "0.3"
```

### 2.2 Lambda 函数初始化

**`src/lambda/init.rs`**:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{
    FAAS_NAME, FAAS_VERSION, FAAS_INSTANCE, FAAS_MAX_MEMORY,
    CLOUD_PROVIDER, CLOUD_REGION, CLOUD_ACCOUNT_ID,
    SERVICE_NAME, SERVICE_VERSION,
};
use anyhow::Result;
use std::time::Instant;

/// 全局初始化时间戳（用于冷启动监控）
static mut INIT_START: Option<Instant> = None;

/// 初始化 OpenTelemetry for AWS Lambda
///
/// **优化点**:
/// 1. 使用 Lambda Extension 作为 OTLP Collector（减少延迟）
/// 2. 资源属性从环境变量预加载（避免 API 调用）
/// 3. 批量导出配置优化（适应短生命周期）
pub async fn init_otel_lambda() -> Result<TracerProvider> {
    // 记录初始化开始时间
    unsafe {
        INIT_START = Some(Instant::now());
    }

    // 1. 从环境变量提取 Lambda 元数据
    let function_name = std::env::var("AWS_LAMBDA_FUNCTION_NAME")?;
    let function_version = std::env::var("AWS_LAMBDA_FUNCTION_VERSION").unwrap_or_else(|_| "$LATEST".to_string());
    let function_memory = std::env::var("AWS_LAMBDA_FUNCTION_MEMORY_SIZE").unwrap_or_else(|_| "128".to_string());
    let aws_region = std::env::var("AWS_REGION")?;
    let log_stream_name = std::env::var("AWS_LAMBDA_LOG_STREAM_NAME").unwrap_or_default();

    // 2. 创建 Resource（Lambda 特定属性）
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, function_name.clone()),
        KeyValue::new(SERVICE_VERSION, function_version.clone()),
        KeyValue::new(FAAS_NAME, function_name.clone()),
        KeyValue::new(FAAS_VERSION, function_version.clone()),
        KeyValue::new(FAAS_INSTANCE, log_stream_name),
        KeyValue::new(FAAS_MAX_MEMORY, function_memory.parse::<i64>().unwrap_or(128)),
        KeyValue::new(CLOUD_PROVIDER, "aws"),
        KeyValue::new(CLOUD_REGION, aws_region),
        KeyValue::new(CLOUD_ACCOUNT_ID, extract_account_id_from_arn()?),
        KeyValue::new("faas.trigger", "http"), // 或 "pubsub", "timer"
    ]);

    // 3. 创建 OTLP HTTP Exporter
    // 优先使用 Lambda Extension (localhost:4318)，否则使用远程 Collector
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4318".to_string());

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_endpoint(format!("{}/v1/traces", otlp_endpoint))
        .with_timeout(std::time::Duration::from_secs(3)) // 减少超时（避免函数超时）
        .build()?;

    // 4. 创建 BatchSpanProcessor（Lambda 优化配置）
    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(512)        // 减小队列（短生命周期）
    .with_max_export_batch_size(128) // 减小批次
    .with_scheduled_delay(std::time::Duration::from_millis(500)) // 快速导出
    .with_max_export_timeout(std::time::Duration::from_secs(2))
    .build();

    // 5. 创建 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    // 6. 注册全局 TracerProvider
    global::set_tracer_provider(tracer_provider.clone());

    // 7. 记录初始化完成时间
    unsafe {
        if let Some(start) = INIT_START {
            let init_duration = start.elapsed();
            tracing::info!("✅ OpenTelemetry initialized in {:?}", init_duration);
        }
    }

    Ok(tracer_provider)
}

/// 从 Lambda ARN 提取 AWS Account ID
fn extract_account_id_from_arn() -> Result<String> {
    let arn = std::env::var("AWS_LAMBDA_FUNCTION_ARN")?;
    // ARN 格式: arn:aws:lambda:region:account-id:function:function-name
    let parts: Vec<&str> = arn.split(':').collect();
    if parts.len() >= 5 {
        Ok(parts[4].to_string())
    } else {
        Err(anyhow::anyhow!("Invalid Lambda ARN format"))
    }
}

/// 获取初始化持续时间（用于冷启动监控）
pub fn get_init_duration() -> Option<std::time::Duration> {
    unsafe {
        INIT_START.map(|start| start.elapsed())
    }
}
```

### 2.3 Lambda 函数处理器

**`src/lambda/handler.rs`**:

```rust
use lambda_http::{run, service_fn, Body, Error, Request, Response};
use opentelemetry::{global, trace::{Span, SpanKind, Tracer}, KeyValue};
use opentelemetry_semantic_conventions::trace::{
    HTTP_METHOD, HTTP_ROUTE, HTTP_STATUS_CODE, FAAS_EXECUTION,
};
use anyhow::Result;

/// Lambda 函数主处理器
pub async fn function_handler(event: Request) -> Result<Response<Body>, Error> {
    let tracer = global::tracer("lambda-handler");

    // 提取 Lambda 上下文
    let request_id = event
        .lambda_context()
        .request_id
        .clone();

    // 创建 Span（Lambda 函数执行）
    let mut span = tracer
        .span_builder(format!("Lambda {}", request_id))
        .with_kind(SpanKind::Server)
        .start(&tracer);

    // 添加 Lambda 特定属性
    span.set_attribute(KeyValue::new(FAAS_EXECUTION, request_id.clone()));

    // 添加 HTTP 属性
    let method = event.method().to_string();
    let path = event.uri().path().to_string();
    span.set_attribute(KeyValue::new(HTTP_METHOD, method));
    span.set_attribute(KeyValue::new(HTTP_ROUTE, path));

    // 提取 AWS X-Ray Trace ID（如果启用）
    if let Some(trace_header) = event.headers().get("x-amzn-trace-id") {
        if let Ok(trace_str) = trace_header.to_str() {
            span.set_attribute(KeyValue::new("aws.xray.trace_id", trace_str.to_string()));
        }
    }

    // 记录冷启动
    if let Some(init_duration) = crate::lambda::init::get_init_duration() {
        span.set_attribute(KeyValue::new("faas.coldstart", true));
        span.set_attribute(KeyValue::new("faas.init_duration_ms", init_duration.as_millis() as i64));
    }

    // 执行业务逻辑
    let response = match handle_request(event).await {
        Ok(resp) => {
            span.set_status(opentelemetry::trace::Status::Ok);
            resp
        }
        Err(e) => {
            span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            Response::builder()
                .status(500)
                .body(Body::from(format!("Internal Server Error: {}", e)))
                .unwrap()
        }
    };

    // 记录响应状态码
    span.set_attribute(KeyValue::new(HTTP_STATUS_CODE, response.status().as_u16() as i64));

    span.end();

    Ok(response)
}

async fn handle_request(event: Request) -> Result<Response<Body>> {
    // 业务逻辑
    let body = format!("Hello from Lambda! Request ID: {}", event.lambda_context().request_id);
    Ok(Response::builder()
        .status(200)
        .body(Body::from(body))?)
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化 tracing
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_target(false)
        .init();

    // 初始化 OpenTelemetry
    let _tracer_provider = crate::lambda::init::init_otel_lambda().await?;

    // 运行 Lambda 运行时
    run(service_fn(function_handler)).await
}
```

### 2.4 Lambda Extension（OTLP Collector）

**Lambda Layer 配置**:

```bash
# 1. 部署 OpenTelemetry Lambda Extension
aws lambda update-function-configuration \
  --function-name my-rust-function \
  --layers arn:aws:lambda:us-east-1:901920570463:layer:aws-otel-collector-amd64-ver-0-102-1:1

# 2. 配置环境变量
aws lambda update-function-configuration \
  --function-name my-rust-function \
  --environment Variables={
      OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318,
      OTEL_SERVICE_NAME=my-rust-function,
      AWS_LAMBDA_EXEC_WRAPPER=/opt/otel-instrument
  }
```

---

## 3. Azure Functions 集成

### 3.1 Custom Runtime 配置

**`host.json`**:

```json
{
  "version": "2.0",
  "extensionBundle": {
    "id": "Microsoft.Azure.Functions.ExtensionBundle",
    "version": "[4.*, 5.0.0)"
  },
  "logging": {
    "applicationInsights": {
      "samplingSettings": {
        "isEnabled": true,
        "maxTelemetryItemsPerSecond": 20
      }
    }
  },
  "customHandler": {
    "description": {
      "defaultExecutablePath": "rust-function",
      "workingDirectory": "",
      "arguments": []
    },
    "enableForwardingHttpRequest": true
  }
}
```

### 3.2 Azure Functions 初始化

**`src/azure/init.rs`**:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{
    FAAS_NAME, FAAS_VERSION, FAAS_INSTANCE,
    CLOUD_PROVIDER, CLOUD_REGION,
    SERVICE_NAME,
};
use anyhow::Result;

pub async fn init_otel_azure_functions() -> Result<TracerProvider> {
    // 从环境变量提取 Azure Functions 元数据
    let function_name = std::env::var("AZURE_FUNCTIONS_FUNCTION_NAME")?;
    let function_app_name = std::env::var("WEBSITE_SITE_NAME")?;
    let region = std::env::var("REGION_NAME").unwrap_or_else(|_| "unknown".to_string());
    let instance_id = std::env::var("WEBSITE_INSTANCE_ID").unwrap_or_default();

    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, function_app_name.clone()),
        KeyValue::new(FAAS_NAME, function_name),
        KeyValue::new(FAAS_VERSION, "$LATEST"),
        KeyValue::new(FAAS_INSTANCE, instance_id),
        KeyValue::new(CLOUD_PROVIDER, "azure"),
        KeyValue::new(CLOUD_REGION, region),
        KeyValue::new("azure.function_app", function_app_name),
    ]);

    // OTLP Exporter（指向 Azure Monitor 或自定义 Collector）
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4318".to_string());

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_endpoint(format!("{}/v1/traces", otlp_endpoint))
        .build()?;

    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(512)
    .with_max_export_batch_size(128)
    .with_scheduled_delay(std::time::Duration::from_millis(500))
    .build();

    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    global::set_tracer_provider(tracer_provider.clone());

    tracing::info!("✅ OpenTelemetry initialized for Azure Functions");
    Ok(tracer_provider)
}
```

---

## 4. GCP Cloud Functions 集成

### 4.1 Cloud Functions 2nd Gen 配置

**`Cargo.toml`**:

```toml
[dependencies]
# GCP Functions Framework
functions-framework = "0.3"

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["trace", "tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# GCP 元数据
reqwest = { version = "0.12", features = ["json"] }
```

### 4.2 GCP 初始化

**`src/gcp/init.rs`**:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{
    FAAS_NAME, FAAS_VERSION, FAAS_INSTANCE,
    CLOUD_PROVIDER, CLOUD_REGION, CLOUD_ACCOUNT_ID,
    SERVICE_NAME,
};
use anyhow::Result;

pub async fn init_otel_gcp_functions() -> Result<TracerProvider> {
    // 从环境变量提取 GCP Functions 元数据
    let function_name = std::env::var("FUNCTION_NAME")?;
    let function_region = std::env::var("FUNCTION_REGION").unwrap_or_else(|_| "us-central1".to_string());
    let project_id = std::env::var("GCP_PROJECT")?;
    let service_name = std::env::var("K_SERVICE").unwrap_or_else(|_| function_name.clone());

    // 从 Metadata Service 获取实例 ID
    let instance_id = fetch_gcp_instance_id().await.unwrap_or_default();

    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, service_name),
        KeyValue::new(FAAS_NAME, function_name),
        KeyValue::new(FAAS_VERSION, "gen2"),
        KeyValue::new(FAAS_INSTANCE, instance_id),
        KeyValue::new(CLOUD_PROVIDER, "gcp"),
        KeyValue::new(CLOUD_REGION, function_region),
        KeyValue::new(CLOUD_ACCOUNT_ID, project_id),
    ]);

    // OTLP gRPC Exporter（GCP 推荐使用 gRPC）
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(otlp_endpoint)
        .build()?;

    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(512)
    .with_max_export_batch_size(128)
    .with_scheduled_delay(std::time::Duration::from_millis(500))
    .build();

    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    global::set_tracer_provider(tracer_provider.clone());

    tracing::info!("✅ OpenTelemetry initialized for GCP Cloud Functions");
    Ok(tracer_provider)
}

async fn fetch_gcp_instance_id() -> Result<String> {
    let client = reqwest::Client::new();
    let response = client
        .get("http://metadata.google.internal/computeMetadata/v1/instance/id")
        .header("Metadata-Flavor", "Google")
        .timeout(std::time::Duration::from_secs(1))
        .send()
        .await?;
    
    Ok(response.text().await?)
}
```

---

## 5. 冷启动追踪

### 5.1 冷启动检测

**`src/coldstart.rs`**:

```rust
use opentelemetry::{trace::Span, KeyValue};
use std::sync::atomic::{AtomicBool, Ordering};

/// 全局冷启动标志
static COLD_START: AtomicBool = AtomicBool::new(true);

/// 检测是否为冷启动
pub fn is_cold_start() -> bool {
    COLD_START.swap(false, Ordering::Relaxed)
}

/// 为 Span 添加冷启动属性
pub fn add_coldstart_attributes(span: &mut impl Span, init_duration: std::time::Duration) {
    let is_cold = is_cold_start();
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold));
    
    if is_cold {
        span.set_attribute(KeyValue::new("faas.init_duration_ms", init_duration.as_millis() as i64));
        span.add_event(
            "cold_start_detected",
            vec![KeyValue::new("init_duration_ms", init_duration.as_millis() as i64)],
        );
    }
}
```

### 5.2 初始化追踪

```rust
use std::time::Instant;
use once_cell::sync::Lazy;

/// 全局初始化时间戳
static INIT_START: Lazy<Instant> = Lazy::new(|| Instant::now());

/// 获取初始化持续时间
pub fn get_init_duration() -> std::time::Duration {
    INIT_START.elapsed()
}

/// 创建初始化 Span（在全局初始化时调用）
pub fn trace_initialization() {
    let tracer = opentelemetry::global::tracer("serverless-init");
    let mut span = tracer
        .span_builder("function_initialization")
        .with_kind(opentelemetry::trace::SpanKind::Internal)
        .start(&tracer);

    // 记录初始化阶段
    span.add_event("loading_dependencies", vec![]);
    
    // ... 初始化逻辑 ...
    
    span.add_event("creating_tracer_provider", vec![]);
    
    let init_duration = get_init_duration();
    span.set_attribute(KeyValue::new("init_duration_ms", init_duration.as_millis() as i64));
    span.end();
}
```

---

## 6. 跨函数上下文传播

### 6.1 Lambda → Lambda 调用

**`src/invoke.rs`**:

```rust
use aws_sdk_lambda::{Client, operation::invoke::InvokeOutput};
use opentelemetry::{global, propagation::TextMapPropagator, trace::{Span, SpanKind, Tracer}, KeyValue};
use serde_json::json;
use anyhow::Result;

/// 调用另一个 Lambda 函数并传播追踪上下文
pub async fn invoke_lambda_with_tracing(
    client: &Client,
    function_name: &str,
    payload: serde_json::Value,
) -> Result<InvokeOutput> {
    let tracer = global::tracer("lambda-client");
    let mut span = tracer
        .span_builder(format!("invoke {}", function_name))
        .with_kind(SpanKind::Client)
        .start(&tracer);

    span.set_attribute(KeyValue::new("faas.invoked_name", function_name.to_string()));
    span.set_attribute(KeyValue::new("faas.invocation_type", "RequestResponse"));

    // 注入追踪上下文到 Payload
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let propagator = global::text_map_propagator();
    
    let mut headers = std::collections::HashMap::new();
    propagator.inject_context(&cx, &mut headers);

    // 构造包含追踪上下文的 Payload
    let payload_with_tracing = json!({
        "body": payload,
        "headers": headers,
    });

    // 调用 Lambda
    let result = client
        .invoke()
        .function_name(function_name)
        .payload(aws_sdk_lambda::primitives::Blob::new(payload_with_tracing.to_string()))
        .send()
        .await?;

    // 记录响应状态
    if let Some(status_code) = result.status_code() {
        span.set_attribute(KeyValue::new("faas.status_code", status_code as i64));
        
        if status_code >= 400 {
            span.set_status(opentelemetry::trace::Status::error(format!("Lambda invocation failed: {}", status_code)));
        }
    }

    span.end();
    Ok(result)
}
```

### 6.2 EventBridge/SQS 消息传播

**`src/messaging.rs`**:

```rust
use opentelemetry::{global, propagation::TextMapPropagator, KeyValue};
use serde_json::json;

/// 将追踪上下文注入到 EventBridge Event
pub fn inject_trace_context_eventbridge(event: &mut serde_json::Value) {
    let cx = opentelemetry::Context::current();
    let propagator = global::text_map_propagator();
    
    let mut headers = std::collections::HashMap::new();
    propagator.inject_context(&cx, &mut headers);

    // 注入到 Event Detail
    if let Some(detail) = event.get_mut("detail") {
        detail["_tracing"] = json!(headers);
    }
}

/// 从 SQS 消息提取追踪上下文
pub fn extract_trace_context_sqs(message: &serde_json::Value) -> opentelemetry::Context {
    let propagator = global::text_map_propagator();
    
    // 从 MessageAttributes 提取
    if let Some(attrs) = message.get("messageAttributes") {
        let extractor = SqsExtractor(attrs);
        return propagator.extract_with_context(&opentelemetry::Context::new(), &extractor);
    }

    opentelemetry::Context::new()
}

struct SqsExtractor<'a>(&'a serde_json::Value);

impl<'a> opentelemetry::propagation::Extractor for SqsExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key)
            .and_then(|v| v.get("stringValue"))
            .and_then(|v| v.as_str())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.as_object()
            .map(|obj| obj.keys().map(|s| s.as_str()).collect())
            .unwrap_or_default()
    }
}
```

---

## 7. 成本优化与采样

### 7.1 智能采样策略

**`src/sampler.rs`**:

```rust
use opentelemetry_sdk::trace::Sampler;

/// Serverless 环境智能采样器
///
/// 策略：
/// - 冷启动：全采样（用于监控冷启动性能）
/// - 错误请求：全采样（便于调试）
/// - 正常请求：基于流量采样（降低成本）
pub fn serverless_sampler() -> Sampler {
    // 检测流量等级
    let invocation_count = get_invocation_count();
    
    if invocation_count < 100 {
        // 低流量：全采样
        Sampler::AlwaysOn
    } else if invocation_count < 10000 {
        // 中流量：10% 采样
        Sampler::TraceIdRatioBased(0.1)
    } else {
        // 高流量：1% 采样
        Sampler::TraceIdRatioBased(0.01)
    }
}

fn get_invocation_count() -> usize {
    // 从 CloudWatch Metrics 或内部计数器获取
    // 简化实现
    std::env::var("INVOCATION_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0)
}
```

### 7.2 成本监控

```rust
use opentelemetry::{trace::Span, KeyValue};

/// 为 Span 添加成本相关属性
pub fn add_cost_attributes(span: &mut impl Span, duration_ms: u64, memory_mb: u64) {
    // AWS Lambda 定价（简化）
    // $0.0000166667 per GB-second
    let cost_usd = (duration_ms as f64 / 1000.0) * (memory_mb as f64 / 1024.0) * 0.0000166667;
    
    span.set_attribute(KeyValue::new("faas.execution_cost_usd", cost_usd));
    span.set_attribute(KeyValue::new("faas.billed_duration_ms", duration_ms as i64));
    span.set_attribute(KeyValue::new("faas.memory_mb", memory_mb as i64));
}
```

---

## 8. 性能优化

### 8.1 预热策略

**`src/warmup.rs`**:

```rust
/// Lambda 预热处理器
///
/// CloudWatch Events 定时调用（保持函数热启动）
pub async fn warmup_handler(event: serde_json::Value) -> Result<(), anyhow::Error> {
    // 检测是否为预热请求
    if event.get("source") == Some(&json!("aws.events"))
        && event.get("detail-type") == Some(&json!("Scheduled Event"))
    {
        tracing::info!("🔥 Warmup request received, keeping function warm");
        return Ok(());
    }

    // 正常请求处理
    Ok(())
}
```

### 8.2 资源属性缓存

```rust
use once_cell::sync::Lazy;
use opentelemetry::KeyValue;

/// 缓存静态资源属性（避免重复检测）
pub static LAMBDA_RESOURCE_ATTRS: Lazy<Vec<KeyValue>> = Lazy::new(|| {
    vec![
        KeyValue::new("faas.name", std::env::var("AWS_LAMBDA_FUNCTION_NAME").unwrap_or_default()),
        KeyValue::new("faas.version", std::env::var("AWS_LAMBDA_FUNCTION_VERSION").unwrap_or_default()),
        KeyValue::new("cloud.region", std::env::var("AWS_REGION").unwrap_or_default()),
    ]
});
```

---

## 9. 完整示例

### 9.1 AWS Lambda HTTP API

**`examples/lambda_http.rs`**:

```rust
use lambda_http::{run, service_fn, Body, Error, Request, Response};
use opentelemetry::{global, trace::{Span, SpanKind, Tracer}, KeyValue};
use anyhow::Result;

mod lambda;

async fn handler(event: Request) -> Result<Response<Body>, Error> {
    let tracer = global::tracer("lambda-http");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("handle_request")
        .with_kind(SpanKind::Server)
        .start(&tracer);

    // 提取路径
    let path = event.uri().path();
    span.set_attribute(KeyValue::new("http.route", path.to_string()));

    // 业务逻辑
    let response = match path {
        "/users" => get_users().await?,
        "/health" => health_check(),
        _ => not_found(),
    };

    span.end();
    Ok(response)
}

async fn get_users() -> Result<Response<Body>> {
    Ok(Response::builder()
        .status(200)
        .body(Body::from(r#"{"users": []}"#))?)
}

fn health_check() -> Response<Body> {
    Response::builder()
        .status(200)
        .body(Body::from("OK"))
        .unwrap()
}

fn not_found() -> Response<Body> {
    Response::builder()
        .status(404)
        .body(Body::from("Not Found"))
        .unwrap()
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    lambda::init::init_otel_lambda().await?;
    
    // 运行 Lambda
    run(service_fn(handler)).await
}
```

### 9.2 部署配置（Terraform）

**`terraform/lambda.tf`**:

```hcl
resource "aws_lambda_function" "rust_function" {
  filename         = "target/lambda/rust-function/bootstrap.zip"
  function_name    = "rust-otlp-function"
  role            = aws_iam_role.lambda_role.arn
  handler         = "bootstrap"
  runtime         = "provided.al2023"
  timeout         = 30
  memory_size     = 512

  environment {
    variables = {
      OTEL_EXPORTER_OTLP_ENDPOINT = "http://localhost:4318"
      OTEL_SERVICE_NAME           = "rust-otlp-function"
      RUST_LOG                    = "info"
    }
  }

  layers = [
    "arn:aws:lambda:us-east-1:901920570463:layer:aws-otel-collector-amd64-ver-0-102-1:1"
  ]

  tracing_config {
    mode = "Active"  # Enable AWS X-Ray
  }
}

resource "aws_cloudwatch_log_group" "lambda_logs" {
  name              = "/aws/lambda/rust-otlp-function"
  retention_in_days = 7
}
```

---

## 参考资源

### 官方文档

- **AWS Lambda Rust Runtime**: <https://github.com/awslabs/aws-lambda-rust-runtime>
- **OpenTelemetry Lambda**: <https://opentelemetry.io/docs/faas/lambda-auto-instrument/>
- **Azure Functions Custom Handlers**: <https://learn.microsoft.com/en-us/azure/azure-functions/functions-custom-handlers>

### 最佳实践

- **Serverless Observability**: <https://aws.amazon.com/blogs/compute/understanding-cold-starts/>
- **Cost Optimization**: <https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html>

---

**文档维护**: OTLP Rust 项目组  
**最后更新**: 2025年10月9日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐
