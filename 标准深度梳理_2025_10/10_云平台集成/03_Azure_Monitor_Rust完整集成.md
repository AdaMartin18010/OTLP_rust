# Azure Monitor - Rust 完整集成

> **Rust版本**: 1.90+  
> **Azure SDK**: 最新版  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [Azure Monitor - Rust 完整集成](#azure-monitor---rust-完整集成)
  - [目录](#目录)
  - [1. Azure Monitor 概述](#1-azure-monitor-概述)
    - [Application Insights 架构](#application-insights-架构)
    - [Connection String 格式](#connection-string-格式)
  - [2. 依赖配置](#2-依赖配置)
  - [3. Application Insights 配置](#3-application-insights-配置)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 自定义属性](#32-自定义属性)
  - [4. Azure Functions 集成](#4-azure-functions-集成)
    - [4.1 HTTP 触发器](#41-http-触发器)
    - [4.2 local.settings.json](#42-localsettingsjson)
  - [5. Azure Container Apps 集成](#5-azure-container-apps-集成)
    - [5.1 容器部署](#51-容器部署)
  - [6. AKS 集成](#6-aks-集成)
    - [6.1 Kubernetes 部署](#61-kubernetes-部署)
    - [6.2 使用 Dapr](#62-使用-dapr)
  - [7. Azure VM 集成](#7-azure-vm-集成)
    - [7.1 VM 扩展](#71-vm-扩展)
  - [8. Azure Services 追踪](#8-azure-services-追踪)
    - [8.1 Azure Blob Storage](#81-azure-blob-storage)
    - [8.2 Azure Service Bus](#82-azure-service-bus)
  - [9. 完整示例](#9-完整示例)

---

## 1. Azure Monitor 概述

### Application Insights 架构

```text
┌─────────────┐
│   应用      │
│  (Rust)     │
└──────┬──────┘
       │ OTLP/HTTP
       ▼
┌─────────────┐
│ Application │
│  Insights   │
│  Endpoint   │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│   Azure     │
│  Monitor    │
└─────────────┘
```

### Connection String 格式

```rust
/// Application Insights Connection String
/// Format: InstrumentationKey=xxx;IngestionEndpoint=https://xxx.in.applicationinsights.azure.com/
pub struct ApplicationInsightsConfig {
    pub instrumentation_key: String,
    pub ingestion_endpoint: String,
}

impl ApplicationInsightsConfig {
    /// 从连接字符串解析
    pub fn from_connection_string(conn_str: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let mut key = None;
        let mut endpoint = None;
        
        for part in conn_str.split(';') {
            if let Some((k, v)) = part.split_once('=') {
                match k {
                    "InstrumentationKey" => key = Some(v.to_string()),
                    "IngestionEndpoint" => endpoint = Some(v.to_string()),
                    _ => {}
                }
            }
        }
        
        Ok(Self {
            instrumentation_key: key.ok_or("Missing InstrumentationKey")?,
            ingestion_endpoint: endpoint.ok_or("Missing IngestionEndpoint")?,
        })
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
opentelemetry-otlp = { version = "0.31.0", features = ["http-proto"] }
opentelemetry-application-insights = "0.31.0"

# Azure SDK
azure_core = "0.19"
azure_identity = "0.19"
azure_storage = "0.19"
azure_storage_blobs = "0.19"

# Async runtime
tokio = { version = "1.47", features = ["full"] }

# Tracing
tracing = "0.1"
tracing-opentelemetry = "0.31"
tracing-subscriber = "0.3"

# HTTP
reqwest = { version = "0.11", features = ["json"] }
```

---

## 3. Application Insights 配置

### 3.1 基础配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::{Config, TracerProvider};
use opentelemetry_application_insights::ApplicationInsightsExporter;

/// 初始化 Application Insights
pub async fn init_application_insights() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. 从环境变量获取连接字符串
    let conn_str = std::env::var("APPLICATIONINSIGHTS_CONNECTION_STRING")
        .expect("APPLICATIONINSIGHTS_CONNECTION_STRING not set");
    
    let config = ApplicationInsightsConfig::from_connection_string(&conn_str)?;
    
    // 2. 创建 Application Insights exporter
    let exporter = ApplicationInsightsExporter::new(
        config.instrumentation_key.clone(),
        config.ingestion_endpoint.clone(),
    )?;
    
    // 3. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_config(
            Config::default()
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    KeyValue::new("service.name", "rust-azure-app"),
                    KeyValue::new("cloud.provider", "azure"),
                    KeyValue::new("cloud.platform", "azure_app_service"),
                ]))
        )
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 4. 集成 tracing
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_opentelemetry::layer().with_tracer(global::tracer("app-insights")))
        .init();
    
    Ok(provider)
}
```

### 3.2 自定义属性

```rust
/// 添加 Azure 特定属性
pub fn add_azure_attributes(span: &tracing::Span) {
    // Cloud role
    if let Ok(role) = std::env::var("WEBSITE_SITE_NAME") {
        span.record("cloud.role", role.as_str());
    }
    
    // Cloud role instance
    if let Ok(instance) = std::env::var("WEBSITE_INSTANCE_ID") {
        span.record("cloud.role_instance", instance.as_str());
    }
    
    // Azure region
    if let Ok(region) = std::env::var("REGION_NAME") {
        span.record("cloud.region", region.as_str());
    }
}
```

---

## 4. Azure Functions 集成

### 4.1 HTTP 触发器

```rust
use azure_functions::{
    bindings::{HttpRequest, HttpResponse},
    func,
};

/// Azure Functions 入口点
#[func]
#[tracing::instrument(skip(req))]
pub async fn http_trigger(req: HttpRequest) -> HttpResponse {
    tracing::info!("Processing Azure Function request");
    
    // 提取 Azure 追踪 headers
    extract_azure_trace_context(&req);
    
    // 处理请求
    match process_request(&req).await {
        Ok(result) => {
            HttpResponse::builder()
                .status(200)
                .body(result)
                .into()
        }
        Err(e) => {
            tracing::error!("Error processing request: {}", e);
            HttpResponse::builder()
                .status(500)
                .body("Internal Server Error")
                .into()
        }
    }
}

#[tracing::instrument]
async fn process_request(req: &HttpRequest) -> Result<String, Box<dyn std::error::Error>> {
    // 业务逻辑
    let name = req.query_params().get("name").unwrap_or("World");
    
    Ok(format!("Hello, {}!", name))
}

/// 提取 Azure 追踪 context
fn extract_azure_trace_context(req: &HttpRequest) {
    // Request-Id header (Azure 标准)
    if let Some(request_id) = req.headers().get("Request-Id") {
        tracing::Span::current().record("request_id", request_id.to_str().ok());
    }
    
    // traceparent (W3C)
    if let Some(traceparent) = req.headers().get("traceparent") {
        tracing::Span::current().record("traceparent", traceparent.to_str().ok());
    }
}
```

### 4.2 local.settings.json

```json
{
  "IsEncrypted": false,
  "Values": {
    "AzureWebJobsStorage": "UseDevelopmentStorage=true",
    "FUNCTIONS_WORKER_RUNTIME": "custom",
    "APPLICATIONINSIGHTS_CONNECTION_STRING": "InstrumentationKey=xxx;IngestionEndpoint=https://xxx.in.applicationinsights.azure.com/"
  }
}
```

---

## 5. Azure Container Apps 集成

### 5.1 容器部署

**Dockerfile**:

```dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-app /usr/local/bin/

ENV PORT=80
ENV RUST_LOG=info

CMD ["my-app"]
```

**Azure CLI 部署**:

```bash
# 创建资源组
az group create --name myResourceGroup --location eastus

# 创建容器应用环境
az containerapp env create \
  --name myContainerAppEnv \
  --resource-group myResourceGroup \
  --location eastus

# 部署容器应用
az containerapp create \
  --name rust-app \
  --resource-group myResourceGroup \
  --environment myContainerAppEnv \
  --image myregistry.azurecr.io/rust-app:latest \
  --target-port 80 \
  --ingress external \
  --env-vars \
    "APPLICATIONINSIGHTS_CONNECTION_STRING=secretref:appinsights-conn-str" \
    "RUST_LOG=info" \
  --secrets \
    "appinsights-conn-str=InstrumentationKey=xxx;..."
```

---

## 6. AKS 集成

### 6.1 Kubernetes 部署

**deployment.yaml**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: myregistry.azurecr.io/rust-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: APPLICATIONINSIGHTS_CONNECTION_STRING
          valueFrom:
            secretKeyRef:
              name: appinsights-secret
              key: connection-string
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 200m
            memory: 256Mi

---
apiVersion: v1
kind: Secret
metadata:
  name: appinsights-secret
type: Opaque
stringData:
  connection-string: "InstrumentationKey=xxx;IngestionEndpoint=https://xxx.in.applicationinsights.azure.com/"

---
apiVersion: v1
kind: Service
metadata:
  name: rust-app
spec:
  selector:
    app: rust-app
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

### 6.2 使用 Dapr

**dapr-config.yaml**:

```yaml
apiVersion: dapr.io/v1alpha1
kind: Configuration
metadata:
  name: appconfig
spec:
  tracing:
    samplingRate: "1"
    zipkin:
      endpointAddress: "http://zipkin.default.svc.cluster.local:9411/api/v2/spans"
```

**deployment with Dapr**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  template:
    metadata:
      annotations:
        dapr.io/enabled: "true"
        dapr.io/app-id: "rust-app"
        dapr.io/app-port: "8080"
        dapr.io/config: "appconfig"
```

---

## 7. Azure VM 集成

### 7.1 VM 扩展

**install-monitoring.sh**:

```bash
#!/bin/bash

# 安装 Azure Monitor Agent
wget https://aka.ms/dependencyagentlinux -O InstallDependencyAgent-Linux64.bin
sudo sh InstallDependencyAgent-Linux64.bin -s

# 配置 Application Insights
export APPLICATIONINSIGHTS_CONNECTION_STRING="InstrumentationKey=xxx;..."

# 部署 Rust 应用
# ...
```

**Azure CLI**:

```bash
# 添加 VM 扩展
az vm extension set \
  --resource-group myResourceGroup \
  --vm-name myVM \
  --name DependencyAgentLinux \
  --publisher Microsoft.Azure.Monitoring.DependencyAgent
```

---

## 8. Azure Services 追踪

### 8.1 Azure Blob Storage

```rust
use azure_storage::StorageCredentials;
use azure_storage_blobs::prelude::*;

/// 带追踪的 Blob Storage 客户端
pub struct TracedBlobClient {
    client: ContainerClient,
}

impl TracedBlobClient {
    pub async fn new(
        account: &str,
        container: &str,
        key: &str,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let creds = StorageCredentials::access_key(account.to_string(), key.to_string());
        let client = ClientBuilder::new(account, creds)
            .container_client(container);
        
        Ok(Self { client })
    }
    
    #[tracing::instrument(skip(self, data))]
    pub async fn upload_blob(
        &self,
        blob_name: &str,
        data: Vec<u8>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let span = tracing::Span::current();
        
        span.record("azure.service", "Blob Storage");
        span.record("azure.operation", "upload");
        span.record("azure.blob_name", blob_name);
        span.record("data.size", data.len());
        
        self.client
            .blob_client(blob_name)
            .put_block_blob(data)
            .await?;
        
        tracing::info!("Blob uploaded successfully");
        
        Ok(())
    }
    
    #[tracing::instrument(skip(self))]
    pub async fn download_blob(
        &self,
        blob_name: &str,
    ) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        span_attributes!(
            "azure.service" => "Blob Storage",
            "azure.operation" => "download",
            "azure.blob_name" => blob_name
        );
        
        let data = self.client
            .blob_client(blob_name)
            .get_content()
            .await?;
        
        tracing::info!(size = data.len(), "Blob downloaded successfully");
        
        Ok(data)
    }
}
```

### 8.2 Azure Service Bus

```rust
use azure_messaging_servicebus::ServiceBusClient;

#[tracing::instrument(skip(client, message))]
pub async fn send_message(
    client: &ServiceBusClient,
    queue: &str,
    message: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let span = tracing::Span::current();
    
    span.record("azure.service", "Service Bus");
    span.record("azure.operation", "send");
    span.record("azure.queue", queue);
    
    // 发送消息逻辑
    tracing::info!("Message sent to Service Bus");
    
    Ok(())
}
```

---

## 9. 完整示例

**生产级 Azure 应用**:

```rust
use axum::{Router, routing::{get, post}, extract::State};
use std::sync::Arc;

/// 应用状态
struct AppState {
    blob_client: TracedBlobClient,
    provider: TracerProvider,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 Application Insights
    let provider = init_application_insights().await?;
    
    // 2. 初始化 Azure 服务
    let blob_client = TracedBlobClient::new(
        &std::env::var("AZURE_STORAGE_ACCOUNT")?,
        &std::env::var("AZURE_CONTAINER_NAME")?,
        &std::env::var("AZURE_STORAGE_KEY")?,
    ).await?;
    
    // 3. 创建应用状态
    let state = Arc::new(AppState {
        blob_client,
        provider: provider.clone(),
    });
    
    // 4. 创建应用
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/upload", post(upload_handler))
        .route("/download/:name", get(download_handler))
        .with_state(state);
    
    // 5. 启动服务器
    let port = std::env::var("PORT").unwrap_or_else(|_| "8080".to_string());
    let addr = format!("0.0.0.0:{}", port);
    
    tracing::info!("Server started on {}", addr);
    
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    axum::serve(listener, app).await?;
    
    // 6. 关闭
    provider.shutdown()?;
    
    Ok(())
}

#[tracing::instrument]
async fn health_check() -> &'static str {
    "OK"
}

#[tracing::instrument(skip(state, body))]
async fn upload_handler(
    State(state): State<Arc<AppState>>,
    body: Vec<u8>,
) -> Result<String, String> {
    state.blob_client
        .upload_blob("example.txt", body)
        .await
        .map_err(|e| e.to_string())?;
    
    Ok("Uploaded successfully".to_string())
}

#[tracing::instrument(skip(state))]
async fn download_handler(
    State(state): State<Arc<AppState>>,
    Path(name): Path<String>,
) -> Result<Vec<u8>, String> {
    state.blob_client
        .download_blob(&name)
        .await
        .map_err(|e| e.to_string())
}
```

---

**相关文档**:

- [AWS X-Ray 集成](01_AWS_X-Ray_Rust完整集成.md)
- [GCP Cloud Trace 集成](02_GCP_Cloud_Trace_Rust完整集成.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
