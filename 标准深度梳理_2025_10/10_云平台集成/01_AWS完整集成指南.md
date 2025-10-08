# AWS 完整集成指南 - Rust OTLP

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - aws-sdk-rust: 1.x
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08

## 目录

- [AWS 完整集成指南 - Rust OTLP](#aws-完整集成指南---rust-otlp)
  - [目录](#目录)
  - [概述](#概述)
  - [1. AWS X-Ray 集成](#1-aws-x-ray-集成)
    - [1.1 X-Ray 追踪配置](#11-x-ray-追踪配置)
    - [1.2 采样规则](#12-采样规则)
  - [2. CloudWatch 集成](#2-cloudwatch-集成)
    - [2.1 日志集成](#21-日志集成)
    - [2.2 指标集成](#22-指标集成)
  - [3. ECS/Fargate 部署](#3-ecsfargate-部署)
    - [3.1 ECS 任务定义](#31-ecs-任务定义)
    - [3.2 Sidecar 模式](#32-sidecar-模式)
  - [4. Lambda 集成](#4-lambda-集成)
  - [5. EKS 集成](#5-eks-集成)
  - [6. 完整示例](#6-完整示例)
  - [总结](#总结)

---

## 概述

本指南提供 Rust OTLP 应用与 AWS 服务的完整集成方案：

- ✅ AWS X-Ray 分布式追踪
- ✅ CloudWatch Logs 日志集成
- ✅ CloudWatch Metrics 指标集成
- ✅ ECS/Fargate 部署配置
- ✅ Lambda 函数集成
- ✅ EKS 集群集成

---

## 1. AWS X-Ray 集成

### 1.1 X-Ray 追踪配置

**Cargo.toml**:

```toml
[dependencies]
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = "0.24.0"
opentelemetry-aws = "0.10.0"
aws-sdk-xray = "1.0"
aws-config = "1.0"
tracing = "0.1.41"
tracing-opentelemetry = "0.27.0"
```

**初始化 X-Ray 追踪**:

```rust
use opentelemetry::{global, trace::TracerProvider};
use opentelemetry_aws::trace::XrayPropagator;
use opentelemetry_sdk::{
    propagation::TraceContextPropagator,
    trace::{Config, TracerProvider as SdkTracerProvider},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_xray_tracer() -> Result<SdkTracerProvider, Box<dyn std::error::Error>> {
    // 1. 配置资源属性
    let resource = Resource::new(vec![
        opentelemetry::KeyValue::new("service.name", "my-rust-app"),
        opentelemetry::KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        opentelemetry::KeyValue::new("deployment.environment", "production"),
    ]);
    
    // 2. 创建 TracerProvider
    let tracer_provider = SdkTracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_simple_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://xray-daemon:2000")
        )
        .build();
    
    // 3. 设置 X-Ray 传播器
    global::set_text_map_propagator(XrayPropagator::default());
    global::set_tracer_provider(tracer_provider.clone());
    
    // 4. 配置 tracing
    let telemetry = tracing_opentelemetry::layer().with_tracer(
        global::tracer_provider().tracer("my-rust-app")
    );
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(tracer_provider)
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let _provider = init_xray_tracer()?;
    
    // 应用逻辑
    run_application().await?;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

#[tracing::instrument]
async fn run_application() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("Application started");
    // 业务逻辑
    Ok(())
}
```

---

### 1.2 采样规则

```rust
use opentelemetry_sdk::trace::{Sampler, SamplerDecision};

// 自定义采样器
pub struct XRaySampler {
    default_rate: f64,
}

impl XRaySampler {
    pub fn new(default_rate: f64) -> Self {
        Self { default_rate }
    }
}

impl Sampler for XRaySampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> opentelemetry_sdk::trace::SamplingResult {
        use opentelemetry::trace::TraceState;
        use std::borrow::Cow;
        
        // 根据路径决定采样率
        let sample = if name.contains("/health") {
            false // 不采样健康检查
        } else if name.contains("/api/") {
            true // 总是采样 API 请求
        } else {
            // 基于 trace_id 的随机采样
            let hash = trace_id.to_bytes()[0] as f64 / 255.0;
            hash < self.default_rate
        };
        
        opentelemetry_sdk::trace::SamplingResult {
            decision: if sample {
                SamplerDecision::RecordAndSample
            } else {
                SamplerDecision::Drop
            },
            attributes: Vec::new(),
            trace_state: TraceState::default(),
        }
    }
}

// 使用自定义采样器
pub fn init_with_custom_sampler() -> Result<SdkTracerProvider, Box<dyn std::error::Error>> {
    let sampler = XRaySampler::new(0.1); // 10% 采样率
    
    let provider = SdkTracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(sampler)
        )
        .build();
    
    Ok(provider)
}
```

---

## 2. CloudWatch 集成

### 2.1 日志集成

```rust
use aws_sdk_cloudwatchlogs::{
    Client as CloudWatchClient,
    types::{InputLogEvent, PutLogEventsRequest},
};
use tracing_subscriber::fmt::MakeWriter;

pub struct CloudWatchWriter {
    client: CloudWatchClient,
    log_group: String,
    log_stream: String,
    buffer: tokio::sync::Mutex<Vec<String>>,
}

impl CloudWatchWriter {
    pub async fn new(
        log_group: impl Into<String>,
        log_stream: impl Into<String>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let config = aws_config::load_from_env().await;
        let client = CloudWatchClient::new(&config);
        
        let log_group = log_group.into();
        let log_stream = log_stream.into();
        
        // 创建日志组（如果不存在）
        client
            .create_log_group()
            .log_group_name(&log_group)
            .send()
            .await
            .ok();
        
        // 创建日志流
        client
            .create_log_stream()
            .log_group_name(&log_group)
            .log_stream_name(&log_stream)
            .send()
            .await
            .ok();
        
        Ok(Self {
            client,
            log_group,
            log_stream,
            buffer: tokio::sync::Mutex::new(Vec::new()),
        })
    }
    
    pub async fn flush(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = self.buffer.lock().await;
        
        if buffer.is_empty() {
            return Ok(());
        }
        
        let events: Vec<_> = buffer
            .drain(..)
            .enumerate()
            .map(|(i, message)| {
                InputLogEvent::builder()
                    .message(message)
                    .timestamp(
                        std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap()
                            .as_millis() as i64
                    )
                    .build()
            })
            .collect();
        
        self.client
            .put_log_events()
            .log_group_name(&self.log_group)
            .log_stream_name(&self.log_stream)
            .set_log_events(Some(events))
            .send()
            .await?;
        
        Ok(())
    }
}

impl std::io::Write for CloudWatchWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let message = String::from_utf8_lossy(buf).to_string();
        
        // 异步写入需要在运行时中执行
        tokio::task::block_in_place(|| {
            tokio::runtime::Handle::current().block_on(async {
                let mut buffer = self.buffer.lock().await;
                buffer.push(message);
                
                // 达到批次大小时刷新
                if buffer.len() >= 100 {
                    drop(buffer);
                    self.flush().await.ok();
                }
            })
        });
        
        Ok(buf.len())
    }
    
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

// 使用 CloudWatch Writer
pub async fn init_cloudwatch_logging() -> Result<(), Box<dyn std::error::Error>> {
    let writer = CloudWatchWriter::new(
        "/aws/rust-app/production",
        "main-stream",
    ).await?;
    
    tracing_subscriber::fmt()
        .with_writer(move || writer.clone())
        .init();
    
    Ok(())
}
```

---

### 2.2 指标集成

```rust
use aws_sdk_cloudwatch::{
    Client as CloudWatchClient,
    types::{Dimension, MetricDatum, StandardUnit},
};
use opentelemetry::metrics::{Meter, MeterProvider};

pub struct CloudWatchMetrics {
    client: CloudWatchClient,
    namespace: String,
}

impl CloudWatchMetrics {
    pub async fn new(namespace: impl Into<String>) -> Result<Self, Box<dyn std::error::Error>> {
        let config = aws_config::load_from_env().await;
        let client = CloudWatchClient::new(&config);
        
        Ok(Self {
            client,
            namespace: namespace.into(),
        })
    }
    
    pub async fn put_metric(
        &self,
        name: impl Into<String>,
        value: f64,
        unit: StandardUnit,
        dimensions: Vec<(String, String)>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut datum = MetricDatum::builder()
            .metric_name(name.into())
            .value(value)
            .unit(unit)
            .timestamp(
                aws_smithy_types::DateTime::from(
                    std::time::SystemTime::now()
                )
            );
        
        for (name, value) in dimensions {
            datum = datum.dimensions(
                Dimension::builder()
                    .name(name)
                    .value(value)
                    .build()
            );
        }
        
        self.client
            .put_metric_data()
            .namespace(&self.namespace)
            .metric_data(datum.build())
            .send()
            .await?;
        
        Ok(())
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let metrics = CloudWatchMetrics::new("MyApp/Production").await?;
    
    // 发送指标
    metrics
        .put_metric(
            "RequestCount",
            1.0,
            StandardUnit::Count,
            vec![
                ("Service".to_string(), "API".to_string()),
                ("Endpoint".to_string(), "/users".to_string()),
            ],
        )
        .await?;
    
    Ok(())
}
```

---

## 3. ECS/Fargate 部署

### 3.1 ECS 任务定义

`task-definition.json`:

```json
{
  "family": "rust-otlp-app",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "256",
  "memory": "512",
  "containerDefinitions": [
    {
      "name": "app",
      "image": "myregistry/rust-app:latest",
      "essential": true,
      "portMappings": [
        {
          "containerPort": 8080,
          "protocol": "tcp"
        }
      ],
      "environment": [
        {
          "name": "RUST_LOG",
          "value": "info"
        },
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "value": "http://localhost:4317"
        },
        {
          "name": "AWS_REGION",
          "value": "us-east-1"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/rust-app",
          "awslogs-region": "us-east-1",
          "awslogs-stream-prefix": "ecs"
        }
      },
      "healthCheck": {
        "command": ["CMD-SHELL", "curl -f http://localhost:8080/health || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3,
        "startPeriod": 60
      }
    },
    {
      "name": "xray-daemon",
      "image": "amazon/aws-xray-daemon:latest",
      "essential": true,
      "portMappings": [
        {
          "containerPort": 2000,
          "protocol": "udp"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/xray-daemon",
          "awslogs-region": "us-east-1",
          "awslogs-stream-prefix": "xray"
        }
      }
    }
  ],
  "taskRoleArn": "arn:aws:iam::123456789012:role/ecsTaskRole",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole"
}
```

---

### 3.2 Sidecar 模式

`Dockerfile`:

```dockerfile
# 构建阶段
FROM rust:1.90-slim as builder

WORKDIR /app
COPY . .

RUN cargo build --release

# 运行阶段
FROM debian:bookworm-slim

# 安装必要的运行时依赖
RUN apt-get update && \
    apt-get install -y ca-certificates curl && \
    rm -rf /var/lib/apt/lists/*

# 复制二进制文件
COPY --from=builder /app/target/release/my-app /usr/local/bin/

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

EXPOSE 8080

CMD ["my-app"]
```

---

## 4. Lambda 集成

```rust
use aws_lambda_events::event::apigw::{ApiGatewayProxyRequest, ApiGatewayProxyResponse};
use lambda_runtime::{run, service_fn, Error, LambdaEvent};
use opentelemetry::global;
use tracing::{info, instrument};

#[instrument]
async fn function_handler(event: LambdaEvent<ApiGatewayProxyRequest>) -> Result<ApiGatewayProxyResponse, Error> {
    // 提取追踪上下文
    let headers = &event.payload.headers;
    
    info!("Processing request");
    
    // 业务逻辑
    let response = ApiGatewayProxyResponse {
        status_code: 200,
        headers: Default::default(),
        multi_value_headers: Default::default(),
        body: Some("Hello from Lambda!".into()),
        is_base64_encoded: false,
    };
    
    Ok(response)
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化追踪
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .without_time()
        .init();
    
    // 运行 Lambda 函数
    run(service_fn(function_handler)).await
}
```

`Cargo.toml` for Lambda:

```toml
[package]
name = "lambda-function"
version = "0.1.0"
edition = "2024"

[dependencies]
lambda_runtime = "0.13"
aws-lambda-events = "0.15"
tokio = { version = "1", features = ["macros"] }
tracing = "0.1"
tracing-subscriber = "0.3"
opentelemetry = "0.31"
```

---

## 5. EKS 集成

`deployment.yaml`:

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
    
    processors:
      batch:
    
    exporters:
      awsxray:
        region: us-east-1
      awsemf:
        region: us-east-1
        namespace: RustApp
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [batch]
          exporters: [awsxray]
        metrics:
          receivers: [otlp]
          processors: [batch]
          exporters: [awsemf]
---
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
        - name: app
          image: myregistry/rust-app:latest
          ports:
            - containerPort: 8080
          env:
            - name: OTEL_EXPORTER_OTLP_ENDPOINT
              value: "http://localhost:4317"
            - name: AWS_REGION
              value: "us-east-1"
          resources:
            requests:
              memory: "256Mi"
              cpu: "250m"
            limits:
              memory: "512Mi"
              cpu: "500m"
        
        - name: otel-collector
          image: otel/opentelemetry-collector-contrib:latest
          ports:
            - containerPort: 4317
          volumeMounts:
            - name: config
              mountPath: /etc/otel
          command:
            - /otelcol-contrib
            - --config=/etc/otel/config.yaml
      
      volumes:
        - name: config
          configMap:
            name: otel-collector-config
---
apiVersion: v1
kind: Service
metadata:
  name: rust-app
spec:
  type: LoadBalancer
  ports:
    - port: 80
      targetPort: 8080
  selector:
    app: rust-app
```

---

## 6. 完整示例

完整的 AWS 集成应用：

```rust
use aws_config::BehaviorVersion;
use opentelemetry::global;
use opentelemetry_aws::trace::XrayPropagator;
use opentelemetry_sdk::Resource;
use tracing::{info, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化追踪
    init_tracing()?;
    
    // 2. 加载 AWS 配置
    let config = aws_config::defaults(BehaviorVersion::latest()).load().await;
    
    info!("Starting Rust OTLP app on AWS");
    
    // 3. 运行应用
    run_application().await?;
    
    // 4. 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

fn init_tracing() -> Result<(), Box<dyn std::error::Error>> {
    let resource = Resource::new(vec![
        opentelemetry::KeyValue::new("service.name", "rust-aws-app"),
        opentelemetry::KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            opentelemetry_sdk::trace::config()
                .with_resource(resource)
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_text_map_propagator(XrayPropagator::default());
    
    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}

#[instrument]
async fn run_application() -> Result<(), Box<dyn std::error::Error>> {
    // 应用逻辑
    info!("Application is running");
    Ok(())
}
```

---

## 总结

本指南提供了 Rust OTLP 应用与 AWS 的完整集成方案：

1. ✅ **X-Ray 追踪**
   - 分布式追踪配置
   - 自定义采样规则

2. ✅ **CloudWatch 集成**
   - 日志集成
   - 指标集成

3. ✅ **ECS/Fargate 部署**
   - 任务定义
   - Sidecar 模式

4. ✅ **Lambda 集成**
   - 无服务器函数追踪

5. ✅ **EKS 集成**
   - Kubernetes 部署配置

通过这些配置，您可以在 AWS 上运行生产级的 Rust OTLP 应用。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0

