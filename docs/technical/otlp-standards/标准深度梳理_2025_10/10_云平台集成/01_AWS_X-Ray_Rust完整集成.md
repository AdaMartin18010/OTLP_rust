# AWS X-Ray - Rust 完整集成

> **Rust版本**: 1.90+  
> **AWS SDK**: 1.0+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [AWS X-Ray - Rust 完整集成](#aws-x-ray---rust-完整集成)
  - [目录](#目录)
  - [1. AWS X-Ray 概述](#1-aws-x-ray-概述)
    - [X-Ray 架构](#x-ray-架构)
    - [X-Ray ID 格式](#x-ray-id-格式)
  - [2. 依赖配置](#2-依赖配置)
  - [3. X-Ray Exporter 配置](#3-x-ray-exporter-配置)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 X-Ray Daemon 配置](#32-x-ray-daemon-配置)
  - [4. Lambda 集成](#4-lambda-集成)
    - [4.1 Lambda 函数追踪](#41-lambda-函数追踪)
    - [4.2 Lambda Layer 配置](#42-lambda-layer-配置)
  - [5. ECS/Fargate 集成](#5-ecsfargate-集成)
    - [5.1 ECS Task Definition](#51-ecs-task-definition)
    - [5.2 Fargate 应用代码](#52-fargate-应用代码)
  - [6. EC2 集成](#6-ec2-集成)
    - [6.1 EC2 启动脚本](#61-ec2-启动脚本)
  - [7. API Gateway 追踪](#7-api-gateway-追踪)
    - [7.1 完整请求追踪](#71-完整请求追踪)
  - [8. DynamoDB 追踪](#8-dynamodb-追踪)
    - [8.1 DynamoDB 操作追踪](#81-dynamodb-操作追踪)
  - [9. 完整示例](#9-完整示例)

---

## 1. AWS X-Ray 概述

### X-Ray 架构

```text
┌─────────────┐
│   应用      │
│  (Rust)     │
└──────┬──────┘
       │ OTLP
       ▼
┌─────────────┐
│ X-Ray Daemon│
│  (本地/ECS) │
└──────┬──────┘
       │ UDP 2000
       ▼
┌─────────────┐
│  AWS X-Ray  │
│   Service   │
└─────────────┘
```

### X-Ray ID 格式

```rust
/// X-Ray Trace ID 格式: 1-{epoch}-{random}
/// 例如: 1-67891233-abcdef012345678912345678
pub struct XRayTraceId {
    version: u8,       // 固定为 1
    timestamp: u32,    // Unix 时间戳
    random: [u8; 12],  // 96-bit 随机数
}

impl XRayTraceId {
    pub fn generate() -> String {
        use std::time::{SystemTime, UNIX_EPOCH};
        
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;
        
        let random: [u8; 12] = rand::random();
        
        format!(
            "1-{:08x}-{}",
            timestamp,
            hex::encode(random)
        )
    }
}
```

---

## 2. 依赖配置

```toml
[dependencies]
# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-aws = "0.31.0"  # AWS X-Ray 支持

# AWS SDK
aws-config = "1.0"
aws-sdk-xray = "1.0"
aws-sdk-dynamodb = "1.0"
aws-sdk-s3 = "1.0"

# Async runtime
tokio = { version = "1.47", features = ["full"] }

# Tracing
tracing = "0.1"
tracing-opentelemetry = "0.31"
tracing-subscriber = "0.3"

# Lambda (可选)
lambda_runtime = "0.8"
```

---

## 3. X-Ray Exporter 配置

### 3.1 基础配置

```rust
use opentelemetry_aws::trace::XrayPropagator;
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::{Config, TracerProvider};

/// 初始化 X-Ray 追踪
pub async fn init_xray() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. 设置 X-Ray propagator
    global::set_text_map_propagator(XrayPropagator::default());
    
    // 2. 创建 X-Ray exporter (通过 OTLP)
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317") // X-Ray Daemon endpoint
        .build_span_exporter()?;
    
    // 3. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_config(
            Config::default()
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    KeyValue::new("service.name", "rust-xray-app"),
                    KeyValue::new("cloud.provider", "aws"),
                ]))
        )
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 4. 集成 tracing
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_opentelemetry::layer().with_tracer(global::tracer("xray")))
        .init();
    
    Ok(provider)
}
```

### 3.2 X-Ray Daemon 配置

```yaml
# xray-daemon.yaml
TotalBufferSizeMB: 50
Concurrency: 8
Region: us-east-1
Socket:
  UDPAddress: "127.0.0.1:2000"
Logging:
  LogLevel: "info"
```

**Docker 运行 X-Ray Daemon**:

```bash
docker run -d \
  --name xray-daemon \
  -p 2000:2000/udp \
  -p 2000:2000/tcp \
  -e AWS_REGION=us-east-1 \
  amazon/aws-xray-daemon:latest
```

---

## 4. Lambda 集成

### 4.1 Lambda 函数追踪

```rust
use lambda_runtime::{service_fn, Error, LambdaEvent};
use serde::{Deserialize, Serialize};
use tracing::info;

#[derive(Deserialize)]
struct Request {
    name: String,
}

#[derive(Serialize)]
struct Response {
    message: String,
}

/// Lambda 处理函数
#[tracing::instrument(skip(event))]
async fn handler(event: LambdaEvent<Request>) -> Result<Response, Error> {
    info!("Processing request for: {}", event.payload.name);
    
    // 业务逻辑
    let result = process_request(&event.payload.name).await?;
    
    Ok(Response {
        message: format!("Hello, {}! Result: {}", event.payload.name, result),
    })
}

#[tracing::instrument]
async fn process_request(name: &str) -> Result<String, Error> {
    // 模拟处理
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    Ok(format!("Processed: {}", name))
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化 X-Ray (Lambda 自动提供 daemon)
    init_xray().await?;
    
    // 运行 Lambda
    lambda_runtime::run(service_fn(handler)).await?;
    
    Ok(())
}
```

### 4.2 Lambda Layer 配置

```yaml
# serverless.yml
service: rust-xray-lambda

provider:
  name: aws
  runtime: provided.al2
  tracing:
    lambda: true
    apiGateway: true
  environment:
    RUST_LOG: info
    AWS_XRAY_DAEMON_ADDRESS: 169.254.79.129:2000

functions:
  main:
    handler: bootstrap
    layers:
      - arn:aws:lambda:us-east-1:111111111111:layer:xray-daemon:1
```

---

## 5. ECS/Fargate 集成

### 5.1 ECS Task Definition

```json
{
  "family": "rust-xray-app",
  "containerDefinitions": [
    {
      "name": "app",
      "image": "myorg/rust-app:latest",
      "memory": 512,
      "cpu": 256,
      "environment": [
        {
          "name": "AWS_XRAY_DAEMON_ADDRESS",
          "value": "xray-daemon:2000"
        },
        {
          "name": "RUST_LOG",
          "value": "info"
        }
      ],
      "links": ["xray-daemon"]
    },
    {
      "name": "xray-daemon",
      "image": "amazon/aws-xray-daemon:latest",
      "memory": 256,
      "cpu": 128,
      "portMappings": [
        {
          "containerPort": 2000,
          "protocol": "udp"
        }
      ]
    }
  ]
}
```

### 5.2 Fargate 应用代码

```rust
use aws_config::meta::region::RegionProviderChain;
use aws_sdk_dynamodb::Client as DynamoDbClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 X-Ray
    let provider = init_xray().await?;
    
    // 初始化 AWS SDK
    let region_provider = RegionProviderChain::default_provider().or_else("us-east-1");
    let config = aws_config::from_env().region(region_provider).load().await;
    let dynamodb = DynamoDbClient::new(&config);
    
    // 启动应用
    run_app(dynamodb).await?;
    
    // 关闭
    provider.shutdown()?;
    
    Ok(())
}

#[tracing::instrument(skip(dynamodb))]
async fn run_app(dynamodb: DynamoDbClient) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("Starting ECS application");
    
    // 应用逻辑
    query_dynamodb(&dynamodb, "users", "123").await?;
    
    Ok(())
}
```

---

## 6. EC2 集成

### 6.1 EC2 启动脚本

```bash
#!/bin/bash
# user-data.sh

# 安装 X-Ray Daemon
curl https://s3.us-east-2.amazonaws.com/aws-xray-assets.us-east-2/xray-daemon/aws-xray-daemon-linux-3.x.zip -o /tmp/xray.zip
unzip /tmp/xray.zip -d /tmp/xray
sudo cp /tmp/xray/xray /usr/local/bin/
sudo chmod +x /usr/local/bin/xray

# 启动 X-Ray Daemon
sudo tee /etc/systemd/system/xray.service << EOF
[Unit]
Description=AWS X-Ray Daemon
After=network.target

[Service]
Type=simple
ExecStart=/usr/local/bin/xray -o -n us-east-1
Restart=on-failure

[Install]
WantedBy=multi-user.target
EOF

sudo systemctl start xray
sudo systemctl enable xray

# 部署 Rust 应用
# ...
```

---

## 7. API Gateway 追踪

### 7.1 完整请求追踪

```rust
use axum::{
    Router,
    routing::get,
    extract::Path,
    http::{HeaderMap, StatusCode},
};
use opentelemetry::propagation::Extractor;

/// API Gateway 请求处理
#[tracing::instrument(skip(headers))]
async fn api_handler(
    Path(user_id): Path<String>,
    headers: HeaderMap,
) -> Result<String, StatusCode> {
    // 提取 X-Ray trace context
    extract_xray_context(&headers);
    
    tracing::info!("Processing request for user: {}", user_id);
    
    // 调用 DynamoDB
    let user = get_user_from_dynamodb(&user_id).await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(format!("User: {:?}", user))
}

/// 提取 X-Ray context
fn extract_xray_context(headers: &HeaderMap) {
    struct HeaderExtractor<'a>(&'a HeaderMap);
    
    impl<'a> Extractor for HeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.get(key)?.to_str().ok()
        }
        
        fn keys(&self) -> Vec<&str> {
            self.0.keys().map(|k| k.as_str()).collect()
        }
    }
    
    let extractor = HeaderExtractor(headers);
    let context = opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.extract(&extractor)
    });
    
    let _guard = context.attach();
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_xray().await?;
    
    let app = Router::new()
        .route("/users/:id", get(api_handler));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

---

## 8. DynamoDB 追踪

### 8.1 DynamoDB 操作追踪

```rust
use aws_sdk_dynamodb::{Client, types::AttributeValue};
use std::collections::HashMap;

/// DynamoDB 客户端包装器
pub struct TracedDynamoDb {
    client: Client,
}

impl TracedDynamoDb {
    pub fn new(client: Client) -> Self {
        Self { client }
    }
    
    /// 查询项目
    #[tracing::instrument(skip(self))]
    pub async fn get_item(
        &self,
        table: &str,
        key: HashMap<String, AttributeValue>,
    ) -> Result<Option<HashMap<String, AttributeValue>>, aws_sdk_dynamodb::Error> {
        let span = tracing::Span::current();
        
        // 设置 X-Ray 属性
        span.record("aws.service", "DynamoDB");
        span.record("aws.operation", "GetItem");
        span.record("aws.table_name", table);
        
        let result = self.client
            .get_item()
            .table_name(table)
            .set_key(Some(key))
            .send()
            .await?;
        
        Ok(result.item)
    }
    
    /// 扫描表
    #[tracing::instrument(skip(self))]
    pub async fn scan(
        &self,
        table: &str,
    ) -> Result<Vec<HashMap<String, AttributeValue>>, aws_sdk_dynamodb::Error> {
        span_attributes!(
            "aws.service" => "DynamoDB",
            "aws.operation" => "Scan",
            "aws.table_name" => table
        );
        
        let result = self.client
            .scan()
            .table_name(table)
            .send()
            .await?;
        
        Ok(result.items.unwrap_or_default())
    }
}

/// 使用示例
async fn query_users(dynamodb: &TracedDynamoDb) -> Result<(), Box<dyn std::error::Error>> {
    let mut key = HashMap::new();
    key.insert("id".to_string(), AttributeValue::S("123".to_string()));
    
    let item = dynamodb.get_item("users", key).await?;
    
    println!("User: {:?}", item);
    
    Ok(())
}
```

---

## 9. 完整示例

**生产级 AWS X-Ray 集成**:

```rust
use aws_config::meta::region::RegionProviderChain;
use aws_sdk_dynamodb::Client as DynamoDbClient;
use axum::{Router, routing::get};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 X-Ray
    let provider = init_xray().await?;
    
    // 2. 初始化 AWS SDK
    let region = RegionProviderChain::default_provider().or_else("us-east-1");
    let aws_config = aws_config::from_env()
        .region(region)
        .load()
        .await;
    
    let dynamodb = DynamoDbClient::new(&aws_config);
    let traced_db = TracedDynamoDb::new(dynamodb);
    
    // 3. 创建应用
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/users/:id", get(get_user_handler));
    
    // 4. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    
    tracing::info!("Server started on port 8080");
    
    axum::serve(listener, app).await?;
    
    // 5. 关闭
    provider.shutdown()?;
    
    Ok(())
}

async fn health_check() -> &'static str {
    "OK"
}

#[tracing::instrument]
async fn get_user_handler(Path(id): Path<String>) -> String {
    format!("User: {}", id)
}
```

---

**相关文档**:

- [GCP Cloud Trace](02_GCP_Cloud_Trace_Rust完整集成.md)
- [Azure Monitor](03_Azure_Monitor_Rust完整集成.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
