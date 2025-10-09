# GCP Cloud Trace - Rust 完整集成

> **Rust版本**: 1.90+  
> **GCP SDK**: 最新版  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [GCP Cloud Trace - Rust 完整集成](#gcp-cloud-trace---rust-完整集成)
  - [目录](#目录)
  - [1. Cloud Trace 概述](#1-cloud-trace-概述)
    - [Cloud Trace 架构](#cloud-trace-架构)
    - [Trace ID 格式](#trace-id-格式)
  - [2. 依赖配置](#2-依赖配置)
  - [3. Cloud Trace Exporter 配置](#3-cloud-trace-exporter-配置)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 认证配置](#32-认证配置)
  - [4. Cloud Run 集成](#4-cloud-run-集成)
    - [4.1 Cloud Run 服务](#41-cloud-run-服务)
  - [5. Cloud Functions 集成](#5-cloud-functions-集成)
    - [5.1 HTTP 触发器](#51-http-触发器)
  - [6. GKE 集成](#6-gke-集成)
    - [6.1 Kubernetes 部署](#61-kubernetes-部署)
  - [7. Compute Engine 集成](#7-compute-engine-集成)
    - [7.1 VM 启动脚本](#71-vm-启动脚本)
  - [8. Cloud APIs 追踪](#8-cloud-apis-追踪)
    - [8.1 Cloud Storage](#81-cloud-storage)
    - [8.2 Pub/Sub](#82-pubsub)
  - [9. 完整示例](#9-完整示例)

---

## 1. Cloud Trace 概述

### Cloud Trace 架构

```text
┌─────────────┐
│   应用      │
│  (Rust)     │
└──────┬──────┘
       │ OTLP/gRPC
       ▼
┌─────────────┐
│   OTLP      │
│  Collector  │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ Cloud Trace │
│   Service   │
└─────────────┘
```

### Trace ID 格式

```rust
/// Cloud Trace ID 格式: 32-character hex string
/// 例如: 4bf92f3577b34da6a3ce929d0e0e4736
pub struct CloudTraceId(String);

impl CloudTraceId {
    pub fn new() -> Self {
        let random: [u8; 16] = rand::random();
        Self(hex::encode(random))
    }
    
    pub fn from_opentelemetry(trace_id: opentelemetry::trace::TraceId) -> Self {
        Self(trace_id.to_string())
    }
}

/// Cloud Trace Context Header
/// Format: X-Cloud-Trace-Context: TRACE_ID/SPAN_ID;o=TRACE_TRUE
pub fn format_cloud_trace_context(
    trace_id: &str,
    span_id: u64,
    sampled: bool,
) -> String {
    format!(
        "{}/{};o={}",
        trace_id,
        span_id,
        if sampled { "1" } else { "0" }
    )
}
```

---

## 2. 依赖配置

```toml
[dependencies]
# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic"] }

# GCP
google-cloud-trace = "0.5"
google-cloud-googleapis = "0.12"
tonic = "0.14"

# Authentication
gcp_auth = "0.10"

# Async runtime
tokio = { version = "1.47", features = ["full"] }

# Tracing
tracing = "0.1"
tracing-opentelemetry = "0.31"
tracing-subscriber = "0.3"
```

---

## 3. Cloud Trace Exporter 配置

### 3.1 基础配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::{Config, TracerProvider};
use opentelemetry_otlp::WithExportConfig;

/// 初始化 Cloud Trace
pub async fn init_cloud_trace() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. 获取 GCP 项目 ID
    let project_id = std::env::var("GCP_PROJECT_ID")
        .or_else(|_| get_project_id_from_metadata())
        .expect("GCP_PROJECT_ID not set");
    
    // 2. 创建 OTLP exporter (指向 Cloud Trace endpoint)
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("https://cloudtrace.googleapis.com")
        .build_span_exporter()?;
    
    // 3. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_config(
            Config::default()
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    KeyValue::new("service.name", "rust-gcp-app"),
                    KeyValue::new("cloud.provider", "gcp"),
                    KeyValue::new("cloud.platform", "cloud_run"),
                    KeyValue::new("gcp.project_id", project_id),
                ]))
        )
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    // 4. 集成 tracing
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_opentelemetry::layer().with_tracer(global::tracer("cloud-trace")))
        .init();
    
    Ok(provider)
}

/// 从 GCP 元数据服务获取项目 ID
async fn get_project_id_from_metadata() -> Result<String, Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();
    let response = client
        .get("http://metadata.google.internal/computeMetadata/v1/project/project-id")
        .header("Metadata-Flavor", "Google")
        .send()
        .await?;
    
    Ok(response.text().await?)
}
```

### 3.2 认证配置

```rust
use gcp_auth::AuthenticationManager;

/// 配置 GCP 认证
pub async fn setup_gcp_auth() -> Result<(), Box<dyn std::error::Error>> {
    // 方式1: 使用 Application Default Credentials (ADC)
    let _auth_manager = AuthenticationManager::new().await?;
    
    // 方式2: 使用服务账号密钥文件
    std::env::set_var(
        "GOOGLE_APPLICATION_CREDENTIALS",
        "/path/to/service-account-key.json"
    );
    
    // 方式3: 在 GKE/Cloud Run 上自动使用 Workload Identity
    // 无需额外配置
    
    Ok(())
}
```

---

## 4. Cloud Run 集成

### 4.1 Cloud Run 服务

**Dockerfile**:

```dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

COPY src ./src
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-app /usr/local/bin/

ENV PORT=8080
ENV RUST_LOG=info

CMD ["my-app"]
```

**main.rs**:

```rust
use axum::{Router, routing::get, extract::Query};
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Cloud Trace
    let provider = init_cloud_trace().await?;
    
    // 从环境变量获取端口 (Cloud Run 自动设置)
    let port: u16 = std::env::var("PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse()?;
    
    // 创建应用
    let app = Router::new()
        .route("/", get(root_handler))
        .route("/api/users/:id", get(get_user));
    
    // 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    
    tracing::info!("Cloud Run service listening on {}", addr);
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    // 关闭
    provider.shutdown()?;
    
    Ok(())
}

#[tracing::instrument]
async fn root_handler() -> &'static str {
    "Hello from Cloud Run!"
}

#[tracing::instrument]
async fn get_user(Path(id): Path<String>) -> String {
    format!("User: {}", id)
}
```

**部署**:

```bash
# 构建容器
gcloud builds submit --tag gcr.io/PROJECT_ID/rust-app

# 部署到 Cloud Run
gcloud run deploy rust-app \
  --image gcr.io/PROJECT_ID/rust-app \
  --platform managed \
  --region us-central1 \
  --allow-unauthenticated \
  --set-env-vars "GCP_PROJECT_ID=PROJECT_ID"
```

---

## 5. Cloud Functions 集成

### 5.1 HTTP 触发器

```rust
use functions_framework::http::{Request, Response};

/// Cloud Functions 入口点
#[functions_framework::main]
async fn http_function(req: Request) -> Result<Response, Box<dyn std::error::Error>> {
    // 初始化 Cloud Trace
    init_cloud_trace().await?;
    
    // 提取 Cloud Trace context
    extract_cloud_trace_context(&req);
    
    // 处理请求
    let result = process_request(req).await?;
    
    Ok(result)
}

#[tracing::instrument]
async fn process_request(req: Request) -> Result<Response, Box<dyn std::error::Error>> {
    tracing::info!("Processing Cloud Function request");
    
    // 业务逻辑
    let body = "Hello from Cloud Functions!";
    
    Ok(Response::builder()
        .status(200)
        .body(body.into())?)
}

/// 提取 Cloud Trace context
fn extract_cloud_trace_context(req: &Request) {
    if let Some(trace_header) = req.headers().get("X-Cloud-Trace-Context") {
        if let Ok(trace_str) = trace_header.to_str() {
            tracing::info!("Cloud Trace Context: {}", trace_str);
            
            // 解析并设置 trace context
            // Format: TRACE_ID/SPAN_ID;o=TRACE_TRUE
            if let Some((trace_id, rest)) = trace_str.split_once('/') {
                tracing::Span::current().record("trace_id", trace_id);
            }
        }
    }
}
```

---

## 6. GKE 集成

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
      serviceAccountName: rust-app-sa
      containers:
      - name: rust-app
        image: gcr.io/PROJECT_ID/rust-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: GCP_PROJECT_ID
          value: "PROJECT_ID"
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 200m
            memory: 256Mi
        
      # OTLP Collector sidecar
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        ports:
        - containerPort: 4317  # OTLP gRPC
        volumeMounts:
        - name: otel-config
          mountPath: /etc/otelcol
      
      volumes:
      - name: otel-config
        configMap:
          name: otel-collector-config

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

**otel-collector-config.yaml**:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
data:
  config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
    
    exporters:
      googlecloud:
        project: PROJECT_ID
        use_insecure: false
    
    processors:
      batch:
        timeout: 10s
        send_batch_size: 1024
      
      resource:
        attributes:
        - key: cloud.platform
          value: gke
          action: upsert
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [batch, resource]
          exporters: [googlecloud]
```

---

## 7. Compute Engine 集成

### 7.1 VM 启动脚本

```bash
#!/bin/bash
# startup-script.sh

# 安装依赖
apt-get update
apt-get install -y curl

# 安装 OTLP Collector
curl -L https://github.com/open-telemetry/opentelemetry-collector-releases/releases/download/v0.91.0/otelcol-contrib_0.91.0_linux_amd64.tar.gz -o otelcol.tar.gz
tar -xvf otelcol.tar.gz
mv otelcol-contrib /usr/local/bin/

# 配置 OTLP Collector
cat > /etc/otelcol-config.yaml <<EOF
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

exporters:
  googlecloud:
    project: PROJECT_ID

processors:
  batch:

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [googlecloud]
EOF

# 启动 OTLP Collector
/usr/local/bin/otelcol-contrib --config /etc/otelcol-config.yaml &

# 部署 Rust 应用
# ...
```

---

## 8. Cloud APIs 追踪

### 8.1 Cloud Storage

```rust
use google_cloud_storage::client::Client as GcsClient;

/// 带追踪的 GCS 客户端
pub struct TracedGcsClient {
    client: GcsClient,
}

impl TracedGcsClient {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let client = GcsClient::default().await?;
        Ok(Self { client })
    }
    
    #[tracing::instrument(skip(self, data))]
    pub async fn upload(
        &self,
        bucket: &str,
        object: &str,
        data: Vec<u8>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let span = tracing::Span::current();
        
        span.record("gcp.service", "Cloud Storage");
        span.record("gcp.operation", "upload");
        span.record("gcp.bucket", bucket);
        span.record("gcp.object", object);
        span.record("data.size", data.len());
        
        self.client
            .upload_object(
                &google_cloud_storage::http::objects::upload::UploadObjectRequest {
                    bucket: bucket.to_string(),
                    ..Default::default()
                },
                data,
                &google_cloud_storage::http::objects::upload::UploadType::Simple(
                    google_cloud_storage::http::objects::Metadata {
                        name: object.to_string(),
                        ..Default::default()
                    }
                ),
            )
            .await?;
        
        Ok(())
    }
}
```

### 8.2 Pub/Sub

```rust
use google_cloud_pubsub::client::Client as PubsubClient;

#[tracing::instrument(skip(client, data))]
pub async fn publish_message(
    client: &PubsubClient,
    topic: &str,
    data: Vec<u8>,
) -> Result<String, Box<dyn std::error::Error>> {
    let span = tracing::Span::current();
    
    span.record("gcp.service", "Pub/Sub");
    span.record("gcp.operation", "publish");
    span.record("gcp.topic", topic);
    
    let topic = client.topic(topic);
    let message_id = topic.publish(data).await?.await?;
    
    Ok(message_id)
}
```

---

## 9. 完整示例

**生产级 GCP 应用**:

```rust
use axum::{Router, routing::get};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 Cloud Trace
    let provider = init_cloud_trace().await?;
    
    // 2. 初始化 GCP 服务
    let gcs = TracedGcsClient::new().await?;
    
    // 3. 创建应用
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/upload", post(upload_handler));
    
    // 4. 启动服务器
    let port = std::env::var("PORT").unwrap_or_else(|_| "8080".to_string());
    let addr = format!("0.0.0.0:{}", port);
    
    tracing::info!("Server started on {}", addr);
    
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    axum::serve(listener, app).await?;
    
    // 5. 关闭
    provider.shutdown()?;
    
    Ok(())
}
```

---

**相关文档**:

- [AWS X-Ray 集成](01_AWS_X-Ray_Rust完整集成.md)
- [Azure Monitor 集成](03_Azure_Monitor_Rust完整集成.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
