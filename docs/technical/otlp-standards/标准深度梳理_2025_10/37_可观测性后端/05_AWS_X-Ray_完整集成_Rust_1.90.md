# AWS X-Ray - Rust + OTLP 完整集成指南

## 📋 目录

- [AWS X-Ray - Rust + OTLP 完整集成指南](#aws-x-ray---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 AWS X-Ray?](#什么是-aws-x-ray)
    - [为什么使用 X-Ray + Rust?](#为什么使用-x-ray--rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. X-Ray 架构](#1-x-ray-架构)
    - [2. 关键术语](#2-关键术语)
  - [环境准备](#环境准备)
    - [1. AWS 配置](#1-aws-配置)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. X-Ray SDK 初始化](#1-x-ray-sdk-初始化)
    - [2. 基本追踪](#2-基本追踪)
    - [3. 段和子段](#3-段和子段)
  - [OTLP 集成](#otlp-集成)
    - [1. OpenTelemetry + X-Ray](#1-opentelemetry--x-ray)
    - [2. ADOT Collector 配置](#2-adot-collector-配置)
    - [3. 自动注入](#3-自动注入)
  - [AWS 服务集成](#aws-服务集成)
    - [1. DynamoDB 追踪](#1-dynamodb-追踪)
    - [2. S3 操作追踪](#2-s3-操作追踪)
    - [3. Lambda 集成](#3-lambda-集成)
    - [4. SQS/SNS 追踪](#4-sqssns-追踪)
  - [HTTP 服务追踪](#http-服务追踪)
    - [1. Axum 集成](#1-axum-集成)
    - [2. 外部 HTTP 调用](#2-外部-http-调用)
  - [高级特性](#高级特性)
    - [1. 采样规则](#1-采样规则)
    - [2. 注解和元数据](#2-注解和元数据)
    - [3. 错误追踪](#3-错误追踪)
  - [Service Map](#service-map)
    - [1. 服务图构建](#1-服务图构建)
    - [2. 依赖关系](#2-依赖关系)
  - [EKS/ECS 部署](#eksecs-部署)
    - [1. EKS 集成](#1-eks-集成)
    - [2. ECS 集成](#2-ecs-集成)
  - [性能优化](#性能优化)
    - [1. 采样优化](#1-采样优化)
    - [2. 批量发送](#2-批量发送)
  - [监控与告警](#监控与告警)
    - [1. X-Ray Insights](#1-x-ray-insights)
    - [2. CloudWatch 集成](#2-cloudwatch-集成)
  - [完整示例](#完整示例)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 调试技巧](#2-调试技巧)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [X-Ray vs 其他 APM](#x-ray-vs-其他-apm)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 AWS X-Ray?

**AWS X-Ray** 是 AWS 的分布式追踪服务:

```text
┌────────────────────────────────────┐
│         AWS X-Ray Console          │
│  • Service Map (服务地图)          │
│  • Trace Timeline (追踪时间线)     │
│  • Analytics (分析)                │
│  • Insights (洞察)                 │
└────────────────────────────────────┘
         ↑ Traces
┌────────────────────────────────────┐
│       X-Ray Daemon/Collector       │
└────────────────────────────────────┘
         ↑ Segments
┌────────────────────────────────────┐
│      Rust Application (OTLP)       │
└────────────────────────────────────┘
```

**核心功能**:

- **分布式追踪**: 跨服务的请求追踪
- **Service Map**: 可视化服务依赖
- **性能分析**: 延迟和错误分析
- **AWS 集成**: 原生支持 AWS 服务
- **采样**: 智能采样规则

### 为什么使用 X-Ray + Rust?

| 优势 | 说明 |
|------|------|
| **AWS 原生** | 与 AWS 服务深度集成 |
| **零服务器** | 无需维护后端 |
| **成本优化** | 按使用付费 |
| **高性能** | Rust 低开销 SDK |
| **OTLP 兼容** | OpenTelemetry 标准 |

### OTLP 集成价值

```text
Rust App → OpenTelemetry SDK → OTLP → ADOT Collector → X-Ray
    ↓              ↓                ↓         ↓            ↓
  业务逻辑      标准化追踪        统一协议  转换格式    AWS追踪
```

**优势**:

- **供应商中立**: 可切换到其他后端
- **生态丰富**: OpenTelemetry 生态
- **自动注入**: 自动化仪表盘
- **标准化**: 统一追踪规范

---

## 核心概念

### 1. X-Ray 架构

```text
┌─────────────────────────────────────────┐
│          Application (Rust)             │
│  ┌─────────────────────────────────┐   │
│  │  OpenTelemetry SDK (OTLP)       │   │
│  └──────────────┬──────────────────┘   │
└─────────────────┼────────────────────────┘
                  │ UDP/TCP
┌─────────────────▼────────────────────────┐
│         X-Ray Daemon / ADOT              │
│  ┌──────────────────────────────────┐   │
│  │  • 接收 Segments                 │   │
│  │  • 批量上传到 X-Ray API          │   │
│  │  • 本地缓存                      │   │
│  └──────────────────────────────────┘   │
└─────────────────┬────────────────────────┘
                  │ HTTPS
┌─────────────────▼────────────────────────┐
│          AWS X-Ray Service               │
│  • 存储 Traces                           │
│  • 生成 Service Map                      │
│  • 提供 Console UI                       │
└──────────────────────────────────────────┘
```

### 2. 关键术语

| 术语 | 说明 |
|------|------|
| **Trace** | 一次完整请求的端到端追踪 |
| **Segment** | 一个服务内的工作单元 |
| **Subsegment** | Segment 内的更细粒度单元 |
| **Annotation** | 可索引的键值对 (用于过滤) |
| **Metadata** | 不可索引的额外信息 |
| **Sampling** | 采样规则 (控制追踪比例) |

---

## 环境准备

### 1. AWS 配置

```bash
# 安装 AWS CLI
brew install awscli  # macOS
# 或
sudo apt-get install awscli  # Ubuntu

# 配置 AWS 凭证
aws configure
# AWS Access Key ID: YOUR_ACCESS_KEY
# AWS Secret Access Key: YOUR_SECRET_KEY
# Default region name: us-east-1
# Default output format: json

# 安装 X-Ray Daemon (本地测试)
wget https://s3.us-east-2.amazonaws.com/aws-xray-assets.us-east-2/xray-daemon/aws-xray-daemon-linux-3.x.zip
unzip aws-xray-daemon-linux-3.x.zip
./xray -o -n us-east-1

# 或使用 Docker
docker run --attach STDOUT -d -p 2000:2000/udp --name xray-daemon \
  -e AWS_ACCESS_KEY_ID=$AWS_ACCESS_KEY_ID \
  -e AWS_SECRET_ACCESS_KEY=$AWS_SECRET_ACCESS_KEY \
  -e AWS_REGION=us-east-1 \
  amazon/aws-xray-daemon:latest
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "xray-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = "0.30"

# AWS X-Ray Propagator
opentelemetry-aws = "0.30"

# Tracing
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }

# AWS SDK
aws-config = "1.1"
aws-sdk-dynamodb = "1.17"
aws-sdk-s3 = "1.19"
aws-sdk-sqs = "1.13"

# HTTP
axum = "0.7"
reqwest = { version = "0.12", features = ["json"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["trace"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. X-Ray SDK 初始化

```rust
// src/xray.rs
use opentelemetry::{
    global,
    trace::TracerProvider,
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_aws::trace::XrayPropagator;
use anyhow::Result;

pub fn init_xray_tracing(service_name: &str) -> Result<()> {
    // 设置 X-Ray Propagator (用于 AWS 特定的 Trace Context)
    global::set_text_map_propagator(XrayPropagator::default());
    
    // 初始化 OTLP Tracer Provider
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),  // ADOT Collector
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)  // 生产环境使用智能采样
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.namespace", "production"),
                    KeyValue::new("deployment.environment", "prod"),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 设置全局 Tracer Provider
    global::set_tracer_provider(tracer_provider);
    
    // 初始化 Tracing Subscriber
    let telemetry = tracing_opentelemetry::layer().with_tracer(
        global::tracer(service_name)
    );
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}

pub fn shutdown_xray_tracing() {
    global::shutdown_tracer_provider();
}
```

### 2. 基本追踪

```rust
// src/main.rs
use tracing::{info, instrument, warn};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 X-Ray
    init_xray_tracing("rust-xray-app")?;
    
    // 处理请求
    handle_request("user123").await?;
    
    // 关闭
    shutdown_xray_tracing();
    Ok(())
}

#[instrument]
async fn handle_request(user_id: &str) -> Result<()> {
    info!("Handling request for user: {}", user_id);
    
    // 调用其他服务
    let user_data = fetch_user_data(user_id).await?;
    let orders = fetch_user_orders(user_id).await?;
    
    info!("Request completed");
    Ok(())
}

#[instrument]
async fn fetch_user_data(user_id: &str) -> Result<UserData> {
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Ok(UserData {
        id: user_id.to_string(),
        name: "John Doe".to_string(),
    })
}

#[instrument]
async fn fetch_user_orders(user_id: &str) -> Result<Vec<Order>> {
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    Ok(vec![])
}
```

### 3. 段和子段

```rust
use opentelemetry::trace::{Span, Tracer};

#[instrument]
async fn complex_operation() -> Result<()> {
    let tracer = global::tracer("rust-xray-app");
    
    // 创建主 Segment
    let mut span = tracer
        .span_builder("complex_operation")
        .with_kind(opentelemetry::trace::SpanKind::Internal)
        .start(&tracer);
    
    // Subsegment 1: 数据库查询
    {
        let mut db_span = tracer
            .span_builder("database_query")
            .start(&tracer);
        
        db_span.set_attribute(KeyValue::new("db.system", "postgresql"));
        db_span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users"));
        
        // 执行查询...
        tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
        
        db_span.end();
    }
    
    // Subsegment 2: 外部 API 调用
    {
        let mut api_span = tracer
            .span_builder("external_api_call")
            .with_kind(opentelemetry::trace::SpanKind::Client)
            .start(&tracer);
        
        api_span.set_attribute(KeyValue::new("http.url", "https://api.example.com"));
        api_span.set_attribute(KeyValue::new("http.method", "GET"));
        
        // 调用 API...
        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
        
        api_span.set_attribute(KeyValue::new("http.status_code", 200));
        api_span.end();
    }
    
    span.end();
    Ok(())
}
```

---

## OTLP 集成

### 1. OpenTelemetry + X-Ray

```rust
// src/otlp_xray.rs
use opentelemetry_sdk::trace::{Config, XrayIdGenerator};

pub fn init_otlp_xray(service_name: &str) -> Result<()> {
    // 使用 X-Ray ID 生成器 (兼容 X-Ray Trace ID 格式)
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            Config::default()
                .with_id_generator(XrayIdGenerator::default())  // X-Ray ID 格式
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 设置 X-Ray Propagator
    global::set_text_map_propagator(XrayPropagator::default());
    
    global::set_tracer_provider(tracer_provider);
    Ok(())
}
```

### 2. ADOT Collector 配置

```yaml
# adot-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  # X-Ray 特定处理器
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: upsert

exporters:
  # 导出到 X-Ray
  awsxray:
    region: us-east-1
    no_verify_ssl: false
    endpoint: ""  # 使用默认 X-Ray endpoint
    index_all_attributes: false  # 仅索引 annotations
  
  # 同时导出到 CloudWatch Logs (可选)
  awscloudwatchlogs:
    region: us-east-1
    log_group_name: /aws/xray/traces
    log_stream_name: rust-app

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, resource]
      exporters: [awsxray, awscloudwatchlogs]
```

启动 ADOT Collector:

```bash
# Docker 方式
docker run --rm -d \
  -p 4317:4317 \
  -p 4318:4318 \
  -v $(pwd)/adot-config.yaml:/etc/otel-collector-config.yaml \
  -e AWS_ACCESS_KEY_ID=$AWS_ACCESS_KEY_ID \
  -e AWS_SECRET_ACCESS_KEY=$AWS_SECRET_ACCESS_KEY \
  -e AWS_REGION=us-east-1 \
  amazon/aws-otel-collector:latest \
  --config=/etc/otel-collector-config.yaml
```

### 3. 自动注入

```rust
// 使用 tracing 宏自动注入
use tracing::instrument;

#[instrument(
    name = "process_order",
    fields(
        order_id = %order_id,
        user_id = %user_id,
    )
)]
async fn process_order(order_id: &str, user_id: &str) -> Result<()> {
    // 自动创建 Span,包含 order_id 和 user_id 作为 attributes
    Ok(())
}
```

---

## AWS 服务集成

### 1. DynamoDB 追踪

```rust
// src/aws/dynamodb.rs
use aws_sdk_dynamodb::Client as DynamoDbClient;
use tracing::{info, instrument};

pub struct DynamoDbService {
    client: DynamoDbClient,
}

impl DynamoDbService {
    #[instrument(skip(self))]
    pub async fn get_item(&self, table: &str, key: &str) -> Result<Option<serde_json::Value>> {
        let tracer = global::tracer("rust-xray-app");
        
        let mut span = tracer
            .span_builder("DynamoDB.GetItem")
            .with_kind(opentelemetry::trace::SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("aws.service", "DynamoDB"),
                KeyValue::new("aws.operation", "GetItem"),
                KeyValue::new("aws.table_name", table.to_string()),
                KeyValue::new("aws.region", "us-east-1"),
            ])
            .start(&tracer);
        
        let result = self.client
            .get_item()
            .table_name(table)
            .key("id", aws_sdk_dynamodb::types::AttributeValue::S(key.to_string()))
            .send()
            .await;
        
        match &result {
            Ok(output) => {
                span.set_attribute(KeyValue::new("aws.status_code", 200));
                span.set_attribute(KeyValue::new("dynamodb.consumed_capacity", 
                    output.consumed_capacity().map(|c| c.capacity_units()).flatten().unwrap_or(0.0)));
            }
            Err(e) => {
                span.record_error(e);
                span.set_attribute(KeyValue::new("aws.status_code", 500));
            }
        }
        
        span.end();
        
        // 转换结果...
        Ok(None)
    }
    
    #[instrument(skip(self, item))]
    pub async fn put_item(&self, table: &str, item: serde_json::Value) -> Result<()> {
        let mut span = global::tracer("rust-xray-app")
            .span_builder("DynamoDB.PutItem")
            .with_attributes(vec![
                KeyValue::new("aws.service", "DynamoDB"),
                KeyValue::new("aws.operation", "PutItem"),
                KeyValue::new("aws.table_name", table.to_string()),
            ])
            .start(&global::tracer("rust-xray-app"));
        
        // 执行 PutItem...
        
        span.end();
        Ok(())
    }
}
```

### 2. S3 操作追踪

```rust
// src/aws/s3.rs
use aws_sdk_s3::Client as S3Client;

pub struct S3Service {
    client: S3Client,
}

impl S3Service {
    #[instrument(skip(self))]
    pub async fn get_object(&self, bucket: &str, key: &str) -> Result<Vec<u8>> {
        let mut span = global::tracer("rust-xray-app")
            .span_builder("S3.GetObject")
            .with_attributes(vec![
                KeyValue::new("aws.service", "S3"),
                KeyValue::new("aws.operation", "GetObject"),
                KeyValue::new("aws.s3.bucket", bucket.to_string()),
                KeyValue::new("aws.s3.key", key.to_string()),
            ])
            .start(&global::tracer("rust-xray-app"));
        
        let result = self.client
            .get_object()
            .bucket(bucket)
            .key(key)
            .send()
            .await;
        
        match &result {
            Ok(output) => {
                let content_length = output.content_length().unwrap_or(0);
                span.set_attribute(KeyValue::new("aws.s3.content_length", content_length));
                span.set_attribute(KeyValue::new("http.status_code", 200));
            }
            Err(e) => {
                span.record_error(e);
            }
        }
        
        span.end();
        
        let bytes = result?.body.collect().await?.into_bytes().to_vec();
        Ok(bytes)
    }
}
```

### 3. Lambda 集成

```rust
// src/lambda_handler.rs (在 Lambda 函数中)
use lambda_runtime::{service_fn, Error, LambdaEvent};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct Request {
    pub user_id: String,
}

#[derive(Serialize)]
struct Response {
    pub message: String,
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化 X-Ray (Lambda 环境自动配置)
    init_xray_tracing("rust-lambda-function")?;
    
    lambda_runtime::run(service_fn(handler)).await
}

#[instrument]
async fn handler(event: LambdaEvent<Request>) -> Result<Response, Error> {
    // Lambda 自动创建根 Segment
    info!("Processing request for user: {}", event.payload.user_id);
    
    // 业务逻辑...
    let result = process_user(&event.payload.user_id).await?;
    
    Ok(Response {
        message: format!("Processed user {}", event.payload.user_id),
    })
}
```

### 4. SQS/SNS 追踪

```rust
// src/aws/sqs.rs
use aws_sdk_sqs::Client as SqsClient;

pub struct SqsService {
    client: SqsClient,
}

impl SqsService {
    #[instrument(skip(self, message_body))]
    pub async fn send_message(&self, queue_url: &str, message_body: &str) -> Result<()> {
        let mut span = global::tracer("rust-xray-app")
            .span_builder("SQS.SendMessage")
            .with_attributes(vec![
                KeyValue::new("aws.service", "SQS"),
                KeyValue::new("aws.operation", "SendMessage"),
                KeyValue::new("aws.queue_url", queue_url.to_string()),
            ])
            .start(&global::tracer("rust-xray-app"));
        
        // 传播 Trace Context 到消息属性
        let mut message_attributes = std::collections::HashMap::new();
        
        // 提取当前 Trace Context
        let propagator = global::get_text_map_propagator(|propagator| {
            let mut carrier = std::collections::HashMap::new();
            propagator.inject_context(&opentelemetry::Context::current(), &mut carrier);
            carrier
        });
        
        for (key, value) in propagator {
            message_attributes.insert(
                key,
                aws_sdk_sqs::types::MessageAttributeValue::builder()
                    .data_type("String")
                    .string_value(value)
                    .build()
                    .unwrap(),
            );
        }
        
        let result = self.client
            .send_message()
            .queue_url(queue_url)
            .message_body(message_body)
            .set_message_attributes(Some(message_attributes))
            .send()
            .await;
        
        match &result {
            Ok(output) => {
                if let Some(message_id) = output.message_id() {
                    span.set_attribute(KeyValue::new("aws.sqs.message_id", message_id.to_string()));
                }
            }
            Err(e) => {
                span.record_error(e);
            }
        }
        
        span.end();
        Ok(())
    }
}
```

---

## HTTP 服务追踪

### 1. Axum 集成

```rust
// src/http/server.rs
use axum::{
    routing::get,
    Router,
    extract::State,
    Json,
};
use tower_http::trace::{TraceLayer, DefaultMakeSpan, DefaultOnResponse};
use std::sync::Arc;

pub async fn start_server() -> Result<()> {
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/users/:id", get(get_user))
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::new().include_headers(true))
                .on_response(DefaultOnResponse::new().include_headers(true))
        );
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument]
async fn health_check() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

#[instrument]
async fn get_user(
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Json<User> {
    // 查询用户...
    Json(User {
        id,
        name: "John Doe".to_string(),
    })
}
```

### 2. 外部 HTTP 调用

```rust
// src/http/client.rs
use reqwest::Client;

pub struct HttpClient {
    client: Client,
}

impl HttpClient {
    #[instrument(skip(self))]
    pub async fn get(&self, url: &str) -> Result<String> {
        let tracer = global::tracer("rust-xray-app");
        
        let mut span = tracer
            .span_builder("HTTP GET")
            .with_kind(opentelemetry::trace::SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "GET"),
                KeyValue::new("http.url", url.to_string()),
            ])
            .start(&tracer);
        
        // 注入 Trace Context 到 HTTP Headers
        let mut headers = reqwest::header::HeaderMap::new();
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(
                &opentelemetry::Context::current(),
                &mut headers,
            );
        });
        
        let result = self.client
            .get(url)
            .headers(headers)
            .send()
            .await;
        
        match &result {
            Ok(response) => {
                span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
            }
            Err(e) => {
                span.record_error(e);
            }
        }
        
        span.end();
        
        let text = result?.text().await?;
        Ok(text)
    }
}
```

---

## 高级特性

### 1. 采样规则

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision};

// 自定义采样器
pub struct CustomSampler {
    default_sampler: Sampler,
}

impl CustomSampler {
    pub fn new(sampling_rate: f64) -> Self {
        Self {
            default_sampler: Sampler::TraceIdRatioBased(sampling_rate),
        }
    }
}

// 根据路径采样
pub fn path_based_sampler(path: &str) -> Sampler {
    match path {
        "/health" => Sampler::AlwaysOff,  // 健康检查不采样
        "/critical" => Sampler::AlwaysOn,  // 关键路径100%采样
        _ => Sampler::TraceIdRatioBased(0.1),  // 其他10%采样
    }
}
```

### 2. 注解和元数据

```rust
#[instrument]
async fn process_payment(amount: f64, currency: &str) -> Result<()> {
    let span = tracing::Span::current();
    
    // Annotations (可索引,用于过滤)
    span.record("payment.amount", &amount);
    span.record("payment.currency", &currency);
    span.record("payment.processor", &"stripe");
    
    // Metadata (不可索引,仅用于查看)
    span.record("debug.info", &"Additional details here");
    
    Ok(())
}
```

### 3. 错误追踪

```rust
#[instrument]
async fn risky_operation() -> Result<()> {
    let span = tracing::Span::current();
    
    match perform_operation().await {
        Ok(result) => {
            span.record("status", &"success");
            Ok(result)
        }
        Err(e) => {
            // 标记为错误
            span.record("error", &true);
            span.record("error.type", &format!("{:?}", e));
            span.record("error.message", &e.to_string());
            
            // 添加异常事件
            span.add_event(
                "exception",
                vec![
                    KeyValue::new("exception.type", format!("{:?}", e)),
                    KeyValue::new("exception.message", e.to_string()),
                ],
            );
            
            Err(e)
        }
    }
}
```

---

## Service Map

### 1. 服务图构建

X-Ray 自动根据 Trace 数据生成 Service Map:

```text
┌─────────┐      ┌─────────┐      ┌─────────┐
│  User   │ ───→ │API Gateway──→ │ Lambda  │
└─────────┘      └─────────┘      └────┬────┘
                                        │
                                        ↓
                      ┌─────────────────┼─────────────────┐
                      ↓                 ↓                 ↓
                 ┌─────────┐     ┌──────────┐     ┌─────────┐
                 │DynamoDB │     │   SQS    │     │   S3    │
                 └─────────┘     └──────────┘     └─────────┘
```

### 2. 依赖关系

```rust
// 显式标记服务依赖
#[instrument]
async fn call_downstream_service(service_name: &str) -> Result<()> {
    let span = tracing::Span::current();
    
    // 标记为外部服务调用
    span.record("service.name", &service_name);
    span.record("peer.service", &service_name);
    
    Ok(())
}
```

---

## EKS/ECS 部署

### 1. EKS 集成

```yaml
# kubernetes/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-xray-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-xray-app
  template:
    metadata:
      labels:
        app: rust-xray-app
    spec:
      serviceAccountName: rust-xray-app-sa
      containers:
      - name: app
        image: myregistry/rust-xray-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://adot-collector:4317"
        - name: AWS_REGION
          value: "us-east-1"
      
      # ADOT Collector Sidecar
      - name: adot-collector
        image: amazon/aws-otel-collector:latest
        command:
          - "/awscollector"
          - "--config=/etc/otel-collector-config.yaml"
        ports:
        - containerPort: 4317  # OTLP gRPC
        - containerPort: 4318  # OTLP HTTP
        env:
        - name: AWS_REGION
          value: "us-east-1"
        volumeMounts:
        - name: adot-config
          mountPath: /etc/otel-collector-config.yaml
          subPath: adot-config.yaml
      
      volumes:
      - name: adot-config
        configMap:
          name: adot-collector-config

---
# ServiceAccount with X-Ray permissions
apiVersion: v1
kind: ServiceAccount
metadata:
  name: rust-xray-app-sa
  annotations:
    eks.amazonaws.com/role-arn: arn:aws:iam::ACCOUNT_ID:role/rust-xray-app-role
```

### 2. ECS 集成

```json
// ecs-task-definition.json
{
  "family": "rust-xray-app",
  "executionRoleArn": "arn:aws:iam::ACCOUNT_ID:role/ecsTaskExecutionRole",
  "taskRoleArn": "arn:aws:iam::ACCOUNT_ID:role/rust-xray-app-role",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "256",
  "memory": "512",
  "containerDefinitions": [
    {
      "name": "rust-app",
      "image": "myregistry/rust-xray-app:latest",
      "portMappings": [
        {
          "containerPort": 8080,
          "protocol": "tcp"
        }
      ],
      "environment": [
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "value": "http://localhost:4317"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/rust-xray-app",
          "awslogs-region": "us-east-1",
          "awslogs-stream-prefix": "ecs"
        }
      }
    },
    {
      "name": "adot-collector",
      "image": "amazon/aws-otel-collector:latest",
      "command": [
        "--config=/etc/otel-collector-config.yaml"
      ],
      "environment": [
        {
          "name": "AWS_REGION",
          "value": "us-east-1"
        }
      ]
    }
  ]
}
```

---

## 性能优化

### 1. 采样优化

```rust
// 智能采样
pub fn adaptive_sampler(error_rate: f64) -> Sampler {
    if error_rate > 0.01 {
        // 错误率高时,增加采样
        Sampler::AlwaysOn
    } else {
        // 正常时,使用10%采样
        Sampler::TraceIdRatioBased(0.1)
    }
}
```

### 2. 批量发送

```yaml
# ADOT Collector 配置优化
processors:
  batch:
    timeout: 10s
    send_batch_size: 1024  # 批量大小
    send_batch_max_size: 2048
```

---

## 监控与告警

### 1. X-Ray Insights

```python
# CloudWatch Alarm for X-Ray (Terraform)
resource "aws_cloudwatch_metric_alarm" "xray_high_error_rate" {
  alarm_name          = "xray-high-error-rate"
  comparison_operator = "GreaterThanThreshold"
  evaluation_periods  = "2"
  metric_name         = "ErrorRate"
  namespace           = "AWS/XRay"
  period              = "300"
  statistic           = "Average"
  threshold           = "5.0"
  alarm_description   = "Alert when error rate > 5%"
  
  dimensions = {
    ServiceName = "rust-xray-app"
  }
}
```

### 2. CloudWatch 集成

```rust
// 同时发送指标到 CloudWatch
use aws_sdk_cloudwatch::Client as CloudWatchClient;

pub async fn send_custom_metric(
    client: &CloudWatchClient,
    metric_name: &str,
    value: f64,
) -> Result<()> {
    client
        .put_metric_data()
        .namespace("RustXRayApp")
        .metric_data(
            aws_sdk_cloudwatch::types::MetricDatum::builder()
                .metric_name(metric_name)
                .value(value)
                .unit(aws_sdk_cloudwatch::types::StandardUnit::Count)
                .timestamp(aws_smithy_types::DateTime::from(chrono::Utc::now()))
                .build(),
        )
        .send()
        .await?;
    
    Ok(())
}
```

---

## 完整示例

(见上文各部分代码)

---

## 故障排查

### 1. 常见问题

```bash
# 1. Traces 未出现在 X-Ray Console
# 检查 IAM 权限
aws iam get-role-policy --role-name YourRole --policy-name XRayPolicy

# 2. ADOT Collector 无法连接
# 查看日志
kubectl logs -f deployment/adot-collector

# 3. X-Ray Daemon 状态
docker logs xray-daemon
```

### 2. 调试技巧

```rust
// 启用详细日志
use tracing_subscriber::EnvFilter;

tracing_subscriber::fmt()
    .with_env_filter(EnvFilter::from_default_env()
        .add_directive("opentelemetry=trace".parse()?))
    .init();
```

---

## 总结

### 核心要点

1. **X-Ray**: AWS 原生分布式追踪
2. **OTLP**: 标准化追踪协议
3. **ADOT**: AWS OpenTelemetry Distro
4. **Service Map**: 自动服务依赖图
5. **AWS 集成**: 深度集成 AWS 服务

### X-Ray vs 其他 APM

| 特性 | X-Ray | Jaeger | Zipkin | Datadog |
|------|-------|--------|--------|---------|
| **AWS集成** | ⭐⭐⭐⭐⭐ | ⭐ | ⭐ | ⭐⭐⭐ |
| **价格** | 按量付费 | 免费 | 免费 | 付费 |
| **部署** | 托管 | 自托管 | 自托管 | 托管 |
| **Service Map** | ✅ | ✅ | ❌ | ✅ |
| **OTLP支持** | ✅ | ✅ | ✅ | ✅ |

### 下一步

- **X-Ray Analytics**: 高级查询和分析
- **X-Ray Insights**: 异常检测
- **Multi-Region**: 跨区域追踪

---

## 参考资料

- [AWS X-Ray 官方文档](https://docs.aws.amazon.com/xray/)
- [ADOT Collector](https://aws-otel.github.io/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.30+  
**AWS SDK**: 1.x
