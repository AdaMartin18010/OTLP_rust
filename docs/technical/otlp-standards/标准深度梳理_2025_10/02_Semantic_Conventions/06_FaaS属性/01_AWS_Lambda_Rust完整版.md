# AWS Lambda 语义约定 - Rust 完整实现

> **Serverless 计算**: AWS Lambda 完整 Tracing 与 Metrics 规范 (Rust 版本)  
> **最后更新**: 2025年10月10日

---

## 目录

- [AWS Lambda 语义约定 - Rust 完整实现](#aws-lambda-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. AWS Lambda 概述](#1-aws-lambda-概述)
    - [1.1 Lambda 特点](#11-lambda-特点)
  - [2. Lambda Resource 属性](#2-lambda-resource-属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Lambda Span 属性](#3-lambda-span-属性)
    - [3.1 调用属性](#31-调用属性)
  - [4. Rust 完整实现](#4-rust-完整实现)
    - [4.1 基础设施](#41-基础设施)
      - [Cargo.toml](#cargotoml)
      - [核心 OTLP 模块](#核心-otlp-模块)
    - [4.2 API Gateway 触发](#42-api-gateway-触发)
      - [基本 HTTP Handler](#基本-http-handler)
    - [4.3 SQS 触发](#43-sqs-触发)
    - [4.4 DynamoDB Streams 触发](#44-dynamodb-streams-触发)
    - [4.5 S3 事件触发](#45-s3-事件触发)
  - [5. OTLP 集成](#5-otlp-集成)
    - [5.1 环境变量配置](#51-环境变量配置)
    - [5.2 Layer 部署](#52-layer-部署)
  - [6. Metrics 实现](#6-metrics-实现)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 冷启动优化](#71-冷启动优化)
    - [7.2 错误处理](#72-错误处理)
    - [7.3 Trace Context 传播](#73-trace-context-传播)
  - [8. 性能优化](#8-性能优化)
    - [8.1 内存优化](#81-内存优化)
    - [8.2 批处理优化](#82-批处理优化)
    - [8.3 二进制大小优化](#83-二进制大小优化)
  - [参考资源](#参考资源)

---

## 1. AWS Lambda 概述

### 1.1 Lambda 特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AWS Lambda - Serverless 计算服务

核心特性:
✅ 无服务器 (零运维)
✅ 按请求付费 (毫秒级计费)
✅ 自动扩展 (并发1000+)
✅ 事件驱动
✅ Rust 支持 (通过 Custom Runtime)
✅ 内置容错
✅ 与AWS服务深度集成

Rust 优势:
✅ 极快冷启动 (< 50ms)
✅ 低内存占用 (< 10MB)
✅ 零成本抽象
✅ 类型安全
✅ 高性能

限制:
⚠️  执行时间: 最长15分钟
⚠️  内存: 128MB - 10GB
⚠️  部署包: 50MB (压缩), 250MB (解压)
⚠️  临时存储: /tmp 最大10GB

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Lambda Resource 属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"aws"` |
| `cloud.platform` | string | 平台类型 | `"aws_lambda"` |
| `cloud.region` | string | AWS区域 | `"us-east-1"` |
| `faas.name` | string | Lambda函数名称 | `"my-function"` |
| `faas.version` | string | 函数版本 | `"$LATEST"` |
| `faas.instance` | string | 实例ID | 自动获取 |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `aws.lambda.invoked_arn` | string | 调用ARN | Lambda自动注入 |
| `aws.log.group.names` | string[] | 日志组 | `["/aws/lambda/my-function"]` |
| `aws.log.stream.names` | string[] | 日志流 | - |

---

## 3. Lambda Span 属性

### 3.1 调用属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.trigger` | string | 触发类型 | `"http"`, `"pubsub"`, `"datasource"` |
| `faas.invocation_id` | string | 请求ID | AWS_REQUEST_ID |
| `faas.coldstart` | boolean | 是否冷启动 | `true`/`false` |
| `faas.execution` | string | 执行环境 | Lambda运行时 |

---

## 4. Rust 完整实现

### 4.1 基础设施

#### Cargo.toml

```toml
[package]
name = "lambda-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Lambda Runtime
lambda_runtime = "0.11"
lambda_http = "0.11"
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"

# AWS SDK
aws-config = "1.1"
aws-sdk-s3 = "1.19"
aws-sdk-dynamodb = "1.18"
aws-sdk-sqs = "1.17"

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.15", features = ["grpc-tonic", "tls"] }
opentelemetry-semantic-conventions = "0.14"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.23"

# Lambda 工具
lambda_runtime_api_client = "0.11"
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
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// Lambda OTLP 配置
pub struct LambdaOtlpConfig {
    pub otlp_endpoint: String,
    pub service_name: String,
    pub service_version: String,
}

impl Default for LambdaOtlpConfig {
    fn default() -> Self {
        Self {
            otlp_endpoint: std::env::var("OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            service_name: std::env::var("AWS_LAMBDA_FUNCTION_NAME")
                .unwrap_or_else(|_| "lambda-function".to_string()),
            service_version: std::env::var("AWS_LAMBDA_FUNCTION_VERSION")
                .unwrap_or_else(|_| "$LATEST".to_string()),
        }
    }
}

/// 初始化 OTLP Tracer
pub fn init_tracer(config: LambdaOtlpConfig) -> anyhow::Result<SdkTracer> {
    // 构建 Lambda Resource 属性
    let resource = Resource::new(vec![
        // 云平台属性
        KeyValue::new("cloud.provider", "aws"),
        KeyValue::new("cloud.platform", "aws_lambda"),
        KeyValue::new(
            "cloud.region",
            std::env::var("AWS_REGION").unwrap_or_else(|_| "us-east-1".to_string()),
        ),
        
        // FaaS 属性
        KeyValue::new("faas.name", config.service_name.clone()),
        KeyValue::new("faas.version", config.service_version.clone()),
        KeyValue::new(
            "faas.instance",
            std::env::var("AWS_LAMBDA_LOG_STREAM_NAME").unwrap_or_default(),
        ),
        
        // 服务属性
        KeyValue::new("service.name", config.service_name.clone()),
        KeyValue::new("service.version", config.service_version),
        
        // AWS 特定属性
        KeyValue::new(
            "aws.lambda.invoked_arn",
            std::env::var("AWS_LAMBDA_FUNCTION_ARN").unwrap_or_default(),
        ),
        KeyValue::new(
            "aws.log.group.names",
            std::env::var("AWS_LAMBDA_LOG_GROUP_NAME").unwrap_or_default(),
        ),
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

    let tracer = tracer_provider.tracer(config.service_name);

    // 设置全局 tracer provider
    global::set_tracer_provider(tracer_provider);

    Ok(tracer)
}

/// 初始化 tracing subscriber (可选)
pub fn init_tracing_subscriber() {
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
        ))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer())
        .init();
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

### 4.2 API Gateway 触发

#### 基本 HTTP Handler

```rust
use lambda_http::{run, service_fn, Body, Error, Request, Response, RequestExt};
use opentelemetry::trace::{TraceContextExt, Tracer};
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

async fn handle_request(event: Request) -> Result<Response<Body>, Error> {
    // 获取 tracer
    let tracer = global::tracer("lambda-handler");
    
    // 创建 span
    let mut span = tracer
        .span_builder("lambda.invocation")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    
    // 添加 Lambda 特定属性
    span.set_attribute(KeyValue::new("faas.trigger", "http"));
    span.set_attribute(KeyValue::new(
        "faas.invocation_id",
        event.lambda_context().request_id.clone(),
    ));
    span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
    
    // HTTP 请求属性
    span.set_attribute(KeyValue::new("http.method", event.method().as_str()));
    span.set_attribute(KeyValue::new("http.target", event.uri().path()));
    span.set_attribute(KeyValue::new("http.scheme", "https"));
    
    if let Some(user_agent) = event.headers().get("user-agent") {
        span.set_attribute(KeyValue::new(
            "http.user_agent",
            user_agent.to_str().unwrap_or(""),
        ));
    }
    
    // API Gateway 特定属性
    if let Some(request_context) = event.request_context() {
        if let Some(api_id) = request_context.apiid() {
            span.set_attribute(KeyValue::new("aws.apigateway.api_id", api_id));
        }
        if let Some(stage) = request_context.stage() {
            span.set_attribute(KeyValue::new("aws.apigateway.stage", stage));
        }
    }
    
    // 处理请求
    let result = process_request_with_context(&event, cx).await;
    
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

async fn process_request_with_context(
    event: &Request,
    cx: opentelemetry::Context,
) -> Result<Response<Body>, Error> {
    let tracer = global::tracer("lambda-handler");
    let _guard = cx.attach();
    
    match event.method().as_str() {
        "POST" => {
            // 创建子 span
            let span = tracer
                .span_builder("create_user")
                .with_kind(SpanKind::Internal)
                .start(&tracer);
            let _cx = opentelemetry::Context::current_with_span(span);
            
            // 解析请求体
            let body = event.body();
            let user_req: CreateUserRequest = serde_json::from_slice(body)?;
            
            // 业务逻辑
            let user_id = uuid::Uuid::new_v4().to_string();
            let response = CreateUserResponse {
                id: user_id,
                name: user_req.name,
                email: user_req.email,
            };
            
            Ok(Response::builder()
                .status(201)
                .header("content-type", "application/json")
                .body(Body::from(serde_json::to_string(&response)?))?)
        }
        "GET" => {
            let span = tracer
                .span_builder("get_users")
                .with_kind(SpanKind::Internal)
                .start(&tracer);
            let _cx = opentelemetry::Context::current_with_span(span);
            
            // 返回用户列表
            Ok(Response::builder()
                .status(200)
                .header("content-type", "application/json")
                .body(Body::from(r#"{"users": []}"#))?)
        }
        _ => {
            Ok(Response::builder()
                .status(405)
                .body(Body::from("Method Not Allowed"))?)
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化 OTLP
    let config = LambdaOtlpConfig::default();
    init_tracer(config)?;
    init_tracing_subscriber();
    
    // 运行 Lambda
    run(service_fn(handle_request)).await
}
```

---

### 4.3 SQS 触发

```rust
use aws_lambda_events::event::sqs::{SqsEvent, SqsMessage};
use lambda_runtime::{run, service_fn, Error, LambdaEvent};
use opentelemetry::trace::{Tracer, SpanKind, Status};
use opentelemetry::KeyValue;

async fn handle_sqs_event(event: LambdaEvent<SqsEvent>) -> Result<(), Error> {
    let tracer = global::tracer("sqs-handler");
    
    // 为每条消息创建 span
    for record in event.payload.records {
        let mut span = tracer
            .span_builder("sqs.process_message")
            .with_kind(SpanKind::Consumer)
            .start(&tracer);
        
        // 添加 FaaS 属性
        span.set_attribute(KeyValue::new("faas.trigger", "pubsub"));
        span.set_attribute(KeyValue::new(
            "faas.invocation_id",
            event.context.request_id.clone(),
        ));
        span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
        
        // 添加 SQS 特定属性
        span.set_attribute(KeyValue::new("messaging.system", "aws_sqs"));
        span.set_attribute(KeyValue::new("messaging.destination", record.event_source_arn.clone()));
        span.set_attribute(KeyValue::new("messaging.message_id", record.message_id.clone()));
        
        if let Some(receipt_handle) = &record.receipt_handle {
            span.set_attribute(KeyValue::new("aws.sqs.receipt_handle", receipt_handle.clone()));
        }
        
        // 提取 trace context (如果存在)
        if let Some(attributes) = record.message_attributes {
            if let Some(trace_parent) = attributes.get("traceparent") {
                // 从消息属性中提取 trace context
                span.add_event(
                    "message_trace_context",
                    vec![KeyValue::new("traceparent", trace_parent.string_value.clone().unwrap_or_default())],
                );
            }
        }
        
        // 处理消息
        match process_sqs_message(&record).await {
            Ok(_) => {
                span.set_attribute(KeyValue::new("messaging.operation", "process"));
                span.set_status(Status::Ok);
            }
            Err(e) => {
                span.set_attribute(KeyValue::new("error", true));
                span.set_attribute(KeyValue::new("error.message", e.to_string()));
                span.set_status(Status::error(e.to_string()));
                
                // SQS 会自动重试失败的消息
                tracing::error!("Failed to process message: {}", e);
            }
        }
        
        span.end();
    }
    
    Ok(())
}

async fn process_sqs_message(record: &SqsMessage) -> anyhow::Result<()> {
    let tracer = global::tracer("sqs-handler");
    let span = tracer
        .span_builder("process_message_body")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    // 解析消息体
    if let Some(body) = &record.body {
        tracing::info!("Processing message: {}", body);
        
        // 业务逻辑
        // ...
        
        Ok(())
    } else {
        anyhow::bail!("Empty message body")
    }
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let config = LambdaOtlpConfig::default();
    init_tracer(config)?;
    init_tracing_subscriber();
    
    run(service_fn(handle_sqs_event)).await
}
```

---

### 4.4 DynamoDB Streams 触发

```rust
use aws_lambda_events::event::dynamodb::{Event, EventRecord};
use lambda_runtime::{run, service_fn, Error, LambdaEvent};
use opentelemetry::trace::{Tracer, SpanKind};

async fn handle_dynamodb_event(event: LambdaEvent<Event>) -> Result<(), Error> {
    let tracer = global::tracer("dynamodb-handler");
    
    for record in event.payload.records {
        let mut span = tracer
            .span_builder("dynamodb.process_stream_record")
            .with_kind(SpanKind::Consumer)
            .start(&tracer);
        
        // FaaS 属性
        span.set_attribute(KeyValue::new("faas.trigger", "datasource"));
        span.set_attribute(KeyValue::new(
            "faas.invocation_id",
            event.context.request_id.clone(),
        ));
        span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
        
        // DynamoDB 特定属性
        span.set_attribute(KeyValue::new("aws.dynamodb.table_name", 
            extract_table_name(&record.event_source_arn)));
        span.set_attribute(KeyValue::new("aws.dynamodb.event_name", 
            record.event_name.clone()));
        span.set_attribute(KeyValue::new("db.system", "dynamodb"));
        span.set_attribute(KeyValue::new("db.operation", 
            map_event_to_operation(&record.event_name)));
        
        // 处理记录
        match record.event_name.as_str() {
            "INSERT" => {
                if let Some(new_image) = record.dynamodb.new_image {
                    process_insert(new_image).await?;
                }
            }
            "MODIFY" => {
                if let (Some(old_image), Some(new_image)) = 
                    (record.dynamodb.old_image, record.dynamodb.new_image) 
                {
                    process_update(old_image, new_image).await?;
                }
            }
            "REMOVE" => {
                if let Some(old_image) = record.dynamodb.old_image {
                    process_delete(old_image).await?;
                }
            }
            _ => {}
        }
        
        span.end();
    }
    
    Ok(())
}

fn extract_table_name(arn: &str) -> String {
    arn.split('/').nth(1).unwrap_or("unknown").to_string()
}

fn map_event_to_operation(event_name: &str) -> &str {
    match event_name {
        "INSERT" => "INSERT",
        "MODIFY" => "UPDATE",
        "REMOVE" => "DELETE",
        _ => "UNKNOWN",
    }
}

async fn process_insert(new_image: HashMap<String, AttributeValue>) -> anyhow::Result<()> {
    // 处理新插入的记录
    tracing::info!("Processing INSERT: {:?}", new_image);
    Ok(())
}

async fn process_update(
    old_image: HashMap<String, AttributeValue>,
    new_image: HashMap<String, AttributeValue>,
) -> anyhow::Result<()> {
    // 处理更新的记录
    tracing::info!("Processing UPDATE: old={:?}, new={:?}", old_image, new_image);
    Ok(())
}

async fn process_delete(old_image: HashMap<String, AttributeValue>) -> anyhow::Result<()> {
    // 处理删除的记录
    tracing::info!("Processing DELETE: {:?}", old_image);
    Ok(())
}
```

---

### 4.5 S3 事件触发

```rust
use aws_lambda_events::event::s3::{S3Event, S3Entity};
use lambda_runtime::{run, service_fn, Error, LambdaEvent};
use aws_sdk_s3::Client as S3Client;

async fn handle_s3_event(event: LambdaEvent<S3Event>) -> Result<(), Error> {
    let tracer = global::tracer("s3-handler");
    
    // 创建 S3 客户端
    let config = aws_config::load_from_env().await;
    let s3_client = S3Client::new(&config);
    
    for record in event.payload.records {
        let mut span = tracer
            .span_builder("s3.process_event")
            .with_kind(SpanKind::Consumer)
            .start(&tracer);
        
        // FaaS 属性
        span.set_attribute(KeyValue::new("faas.trigger", "datasource"));
        span.set_attribute(KeyValue::new(
            "faas.invocation_id",
            event.context.request_id.clone(),
        ));
        span.set_attribute(KeyValue::new("faas.coldstart", is_cold_start()));
        
        // S3 特定属性
        let s3 = &record.s3;
        span.set_attribute(KeyValue::new("aws.s3.bucket", s3.bucket.name.clone()));
        span.set_attribute(KeyValue::new("aws.s3.key", s3.object.key.clone()));
        span.set_attribute(KeyValue::new("aws.s3.size", s3.object.size as i64));
        span.set_attribute(KeyValue::new("aws.s3.event_name", record.event_name.clone()));
        
        // 处理 S3 对象
        match record.event_name.as_str() {
            name if name.starts_with("ObjectCreated") => {
                process_object_created(&s3_client, &s3.bucket.name, &s3.object.key).await?;
            }
            name if name.starts_with("ObjectRemoved") => {
                process_object_removed(&s3.bucket.name, &s3.object.key).await?;
            }
            _ => {}
        }
        
        span.end();
    }
    
    Ok(())
}

async fn process_object_created(
    s3_client: &S3Client,
    bucket: &str,
    key: &str,
) -> anyhow::Result<()> {
    let tracer = global::tracer("s3-handler");
    let span = tracer
        .span_builder("download_and_process")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    let _cx = opentelemetry::Context::current_with_span(span);
    
    // 下载对象
    let output = s3_client
        .get_object()
        .bucket(bucket)
        .key(key)
        .send()
        .await?;
    
    // 读取内容
    let data = output.body.collect().await?;
    let bytes = data.into_bytes();
    
    tracing::info!("Downloaded {} bytes from s3://{}/{}", bytes.len(), bucket, key);
    
    // 处理数据
    // ...
    
    Ok(())
}

async fn process_object_removed(bucket: &str, key: &str) -> anyhow::Result<()> {
    tracing::info!("Object removed: s3://{}/{}", bucket, key);
    Ok(())
}
```

---

## 5. OTLP 集成

### 5.1 环境变量配置

```bash
# Lambda 环境变量
OTLP_ENDPOINT=https://otlp-collector.example.com:4317
OTLP_PROTOCOL=grpc
RUST_LOG=info

# AWS Lambda 自动注入的变量
# AWS_LAMBDA_FUNCTION_NAME
# AWS_LAMBDA_FUNCTION_VERSION
# AWS_REGION
# AWS_LAMBDA_LOG_GROUP_NAME
# AWS_LAMBDA_LOG_STREAM_NAME
```

### 5.2 Layer 部署

创建 Lambda Layer 包含 OTLP 依赖：

```bash
# 编译 Lambda 函数
cargo build --release --target x86_64-unknown-linux-musl

# 创建部署包
mkdir -p layer/lib
cp target/x86_64-unknown-linux-musl/release/bootstrap layer/bootstrap
zip -j lambda.zip layer/bootstrap

# 部署
aws lambda create-function \
  --function-name my-rust-lambda \
  --runtime provided.al2 \
  --handler bootstrap \
  --zip-file fileb://lambda.zip \
  --role arn:aws:iam::ACCOUNT_ID:role/lambda-role \
  --environment Variables="{OTLP_ENDPOINT=https://collector:4317}"
```

---

## 6. Metrics 实现

```rust
use opentelemetry::{global, metrics::{Counter, Histogram, Meter}};
use std::sync::Arc;

pub struct LambdaMetrics {
    invocations: Counter<u64>,
    duration: Histogram<f64>,
    errors: Counter<u64>,
    cold_starts: Counter<u64>,
    memory_used: Histogram<f64>,
}

impl LambdaMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            invocations: meter
                .u64_counter("faas.invocations")
                .with_description("Number of Lambda invocations")
                .init(),
            
            duration: meter
                .f64_histogram("faas.invoke_duration")
                .with_description("Lambda invocation duration")
                .with_unit("ms")
                .init(),
            
            errors: meter
                .u64_counter("faas.errors")
                .with_description("Number of invocation errors")
                .init(),
            
            cold_starts: meter
                .u64_counter("faas.cold_starts")
                .with_description("Number of cold starts")
                .init(),
            
            memory_used: meter
                .f64_histogram("faas.memory_usage")
                .with_description("Memory usage in MB")
                .with_unit("MB")
                .init(),
        }
    }
    
    pub fn record_invocation(&self, trigger: &str) {
        self.invocations.add(
            1,
            &[KeyValue::new("faas.trigger", trigger.to_string())],
        );
    }
    
    pub fn record_duration(&self, duration_ms: f64, trigger: &str) {
        self.duration.record(
            duration_ms,
            &[KeyValue::new("faas.trigger", trigger.to_string())],
        );
    }
    
    pub fn record_error(&self, error_type: &str) {
        self.errors.add(
            1,
            &[KeyValue::new("error.type", error_type.to_string())],
        );
    }
    
    pub fn record_cold_start(&self) {
        self.cold_starts.add(1, &[]);
    }
}

// 使用示例
async fn instrumented_handler(event: Request) -> Result<Response<Body>, Error> {
    let start = std::time::Instant::now();
    let meter = global::meter("lambda-metrics");
    let metrics = LambdaMetrics::new(&meter);
    
    // 记录调用
    metrics.record_invocation("http");
    
    // 记录冷启动
    if is_cold_start() {
        metrics.record_cold_start();
    }
    
    // 处理请求
    let result = handle_request(event).await;
    
    // 记录持续时间
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    metrics.record_duration(duration, "http");
    
    // 记录错误
    if result.is_err() {
        metrics.record_error("handler_error");
    }
    
    result
}
```

---

## 7. 最佳实践

### 7.1 冷启动优化

```rust
// 1. 使用 lazy_static 预初始化连接
use lazy_static::lazy_static;

lazy_static! {
    static ref S3_CLIENT: S3Client = {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let config = aws_config::load_from_env().await;
            S3Client::new(&config)
        })
    };
}

// 2. 缓存 OTLP Tracer
lazy_static! {
    static ref TRACER: SdkTracer = {
        let config = LambdaOtlpConfig::default();
        init_tracer(config).expect("Failed to initialize tracer")
    };
}

// 3. 使用编译优化
// Cargo.toml
[profile.release]
opt-level = 'z'     # 优化二进制大小
lto = true          # 链接时优化
codegen-units = 1   # 更好的优化
strip = true        # 去除符号信息
```

### 7.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LambdaError {
    #[error("S3 error: {0}")]
    S3Error(#[from] aws_sdk_s3::Error),
    
    #[error("DynamoDB error: {0}")]
    DynamoDBError(#[from] aws_sdk_dynamodb::Error),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    
    #[error("Business logic error: {0}")]
    BusinessError(String),
}

// 统一错误处理
impl From<LambdaError> for Response<Body> {
    fn from(error: LambdaError) -> Self {
        // 记录到 span
        let span = opentelemetry::Context::current().span();
        span.set_attribute(KeyValue::new("error", true));
        span.set_attribute(KeyValue::new("error.message", error.to_string()));
        
        Response::builder()
            .status(500)
            .body(Body::from(format!(r#"{{"error": "{}"}}"#, error)))
            .unwrap()
    }
}
```

### 7.3 Trace Context 传播

```rust
use opentelemetry::propagation::{Injector, TextMapPropagator};
use opentelemetry_sdk::propagation::TraceContextPropagator;

// 从 HTTP Headers 提取 trace context
fn extract_trace_context(headers: &HeaderMap) -> opentelemetry::Context {
    let propagator = TraceContextPropagator::new();
    let extractor = HeaderExtractor(headers);
    propagator.extract(&extractor)
}

struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

// 注入 trace context 到 SQS 消息
async fn send_sqs_message_with_trace(
    sqs_client: &aws_sdk_sqs::Client,
    queue_url: &str,
    message_body: &str,
) -> Result<(), aws_sdk_sqs::Error> {
    let propagator = TraceContextPropagator::new();
    let cx = opentelemetry::Context::current();
    
    let mut carrier = HashMap::new();
    propagator.inject_context(&cx, &mut carrier);
    
    // 将 trace context 添加到消息属性
    let message_attributes: HashMap<_, _> = carrier
        .into_iter()
        .map(|(k, v)| {
            (
                k,
                aws_sdk_sqs::types::MessageAttributeValue::builder()
                    .string_value(v)
                    .data_type("String")
                    .build()
                    .unwrap(),
            )
        })
        .collect();
    
    sqs_client
        .send_message()
        .queue_url(queue_url)
        .message_body(message_body)
        .set_message_attributes(Some(message_attributes))
        .send()
        .await?;
    
    Ok(())
}
```

---

## 8. 性能优化

### 8.1 内存优化

```rust
// 使用 jemalloc 作为分配器
use tikv_jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

// 优化 Tokio runtime
#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Error> {
    // 单线程 runtime 更适合 Lambda
    run(service_fn(handle_request)).await
}
```

### 8.2 批处理优化

```rust
// 批量处理 SQS 消息
async fn handle_sqs_batch(event: LambdaEvent<SqsEvent>) -> Result<(), Error> {
    let messages = event.payload.records;
    
    // 并发处理消息（限制并发数）
    let semaphore = Arc::new(tokio::sync::Semaphore::new(10));
    let tasks: Vec<_> = messages
        .into_iter()
        .map(|msg| {
            let sem = semaphore.clone();
            tokio::spawn(async move {
                let _permit = sem.acquire().await.unwrap();
                process_sqs_message(&msg).await
            })
        })
        .collect();
    
    // 等待所有任务完成
    let results = futures::future::join_all(tasks).await;
    
    // 处理结果
    for result in results {
        if let Err(e) = result {
            tracing::error!("Task failed: {}", e);
        }
    }
    
    Ok(())
}
```

### 8.3 二进制大小优化

```bash
# 使用 cargo-strip
cargo install cargo-strip
cargo build --release
cargo strip

# 使用 UPX 压缩（可选）
upx --best --lzma target/x86_64-unknown-linux-musl/release/bootstrap

# 最终大小对比
# 未优化: ~15MB
# strip: ~3MB
# UPX: ~1MB
```

---

## 参考资源

1. **AWS Lambda Rust Runtime**: <https://github.com/awslabs/aws-lambda-rust-runtime>
2. **OpenTelemetry Rust**: <https://github.com/open-telemetry/opentelemetry-rust>
3. **AWS SDK for Rust**: <https://github.com/awslabs/aws-sdk-rust>
4. **Lambda 最佳实践**: <https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
