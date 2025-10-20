# AWS 云平台属性 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **AWS SDK**: 1.61+  
> **最后更新**: 2025年10月9日

---

## 目录

- [AWS 云平台属性 - Rust 完整实现](#aws-云平台属性---rust-完整实现)
  - [目录](#目录)
  - [1. AWS 云平台概述](#1-aws-云平台概述)
  - [2. EC2 实例属性](#2-ec2-实例属性)
  - [3. Lambda 函数属性](#3-lambda-函数属性)
  - [4. ECS 容器属性](#4-ecs-容器属性)
  - [5. EKS 集群属性](#5-eks-集群属性)
  - [6. 完整AWS资源检测器](#6-完整aws资源检测器)
  - [7. X-Ray 集成](#7-x-ray-集成)
  - [8. CloudWatch 集成](#8-cloudwatch-集成)
  - [9. 完整示例](#9-完整示例)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 IMDSv2 使用](#101-imdsv2-使用)
    - [10.2 超时处理](#102-超时处理)
    - [10.3 Cargo.toml 配置](#103-cargotoml-配置)
  - [总结](#总结)

---

## 1. AWS 云平台概述

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::resource::{
    CLOUD_PROVIDER, CLOUD_PLATFORM, CLOUD_REGION,
    CLOUD_ACCOUNT_ID, CLOUD_AVAILABILITY_ZONE,
};

/// AWS 平台类型
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AwsPlatform {
    Ec2,
    Lambda,
    Ecs,
    EcsFargate,
    Eks,
    ElasticBeanstalk,
    AppRunner,
}

impl AwsPlatform {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Ec2 => "aws_ec2",
            Self::Lambda => "aws_lambda",
            Self::Ecs => "aws_ecs",
            Self::EcsFargate => "aws_ecs_fargate",
            Self::Eks => "aws_eks",
            Self::ElasticBeanstalk => "aws_elastic_beanstalk",
            Self::AppRunner => "aws_app_runner",
        }
    }
    
    /// 自动检测当前 AWS 平台
    pub fn detect() -> Option<Self> {
        if Self::is_lambda() {
            Some(Self::Lambda)
        } else if Self::is_ecs_fargate() {
            Some(Self::EcsFargate)
        } else if Self::is_ecs() {
            Some(Self::Ecs)
        } else if Self::is_eks() {
            Some(Self::Eks)
        } else if Self::is_elastic_beanstalk() {
            Some(Self::ElasticBeanstalk)
        } else if Self::is_app_runner() {
            Some(Self::AppRunner)
        } else if Self::is_ec2() {
            Some(Self::Ec2)
        } else {
            None
        }
    }
    
    fn is_lambda() -> bool {
        std::env::var("AWS_LAMBDA_FUNCTION_NAME").is_ok()
    }
    
    fn is_ecs() -> bool {
        std::env::var("ECS_CONTAINER_METADATA_URI").is_ok()
            || std::env::var("ECS_CONTAINER_METADATA_URI_V4").is_ok()
    }
    
    fn is_ecs_fargate() -> bool {
        Self::is_ecs() && std::env::var("AWS_EXECUTION_ENV")
            .map(|v| v.contains("Fargate"))
            .unwrap_or(false)
    }
    
    fn is_eks() -> bool {
        std::env::var("KUBERNETES_SERVICE_HOST").is_ok()
            && std::path::Path::new("/var/run/secrets/kubernetes.io").exists()
            && Self::is_ec2()
    }
    
    fn is_elastic_beanstalk() -> bool {
        std::env::var("AWS_ELASTICBEANSTALK_APPLICATION_NAME").is_ok()
    }
    
    fn is_app_runner() -> bool {
        std::env::var("AWS_APPRUNNER_SERVICE_ID").is_ok()
    }
    
    fn is_ec2() -> bool {
        // 尝试访问 EC2 metadata endpoint
        std::fs::read_to_string("/sys/hypervisor/uuid")
            .map(|content| content.starts_with("ec2"))
            .unwrap_or(false)
            || std::fs::read_to_string("/sys/class/dmi/id/product_uuid")
                .map(|content| content.to_lowercase().starts_with("ec2"))
                .unwrap_or(false)
    }
}
```

---

## 2. EC2 实例属性

```rust
use reqwest::Client;
use std::time::Duration;

/// EC2 Metadata 服务客户端
pub struct Ec2MetadataClient {
    client: Client,
    base_url: String,
    token: Option<String>,
}

impl Ec2MetadataClient {
    pub fn new() -> Self {
        Self {
            client: Client::builder()
                .timeout(Duration::from_secs(1))
                .build()
                .unwrap(),
            base_url: "http://169.254.169.254/latest/meta-data".to_string(),
            token: None,
        }
    }
    
    /// 获取 IMDSv2 token
    pub async fn get_token(&mut self) -> anyhow::Result<String> {
        if let Some(ref token) = self.token {
            return Ok(token.clone());
        }
        
        let response = self.client
            .put("http://169.254.169.254/latest/api/token")
            .header("X-aws-ec2-metadata-token-ttl-seconds", "21600")
            .send()
            .await?;
        
        let token = response.text().await?;
        self.token = Some(token.clone());
        Ok(token)
    }
    
    /// 获取 metadata
    async fn get_metadata(&mut self, path: &str) -> anyhow::Result<String> {
        let url = format!("{}/{}", self.base_url, path);
        let token = self.get_token().await?;
        
        let response = self.client
            .get(&url)
            .header("X-aws-ec2-metadata-token", token)
            .send()
            .await?;
        
        Ok(response.text().await?)
    }
    
    /// 检测 EC2 资源属性
    pub async fn detect_attributes(&mut self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "aws"),
            KeyValue::new(CLOUD_PLATFORM, "aws_ec2"),
        ];
        
        // Region
        if let Ok(region) = self.get_metadata("placement/region").await {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        // Availability Zone
        if let Ok(az) = self.get_metadata("placement/availability-zone").await {
            attrs.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, az));
        }
        
        // Instance ID
        if let Ok(instance_id) = self.get_metadata("instance-id").await {
            attrs.push(KeyValue::new("host.id", instance_id));
        }
        
        // Instance Type
        if let Ok(instance_type) = self.get_metadata("instance-type").await {
            attrs.push(KeyValue::new("host.type", instance_type));
        }
        
        // AMI ID
        if let Ok(ami_id) = self.get_metadata("ami-id").await {
            attrs.push(KeyValue::new("host.image.id", ami_id));
        }
        
        // Account ID (从 IAM info)
        if let Ok(iam_info) = self.get_metadata("iam/info").await {
            if let Ok(info) = serde_json::from_str::<serde_json::Value>(&iam_info) {
                if let Some(account_id) = info["AccountId"].as_str() {
                    attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, account_id.to_string()));
                }
            }
        }
        
        attrs
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut client = Ec2MetadataClient::new();
    let attrs = client.detect_attributes().await;
    
    for attr in attrs {
        println!("{}: {}", attr.key, attr.value);
    }
    
    Ok(())
}
```

---

## 3. Lambda 函数属性

```rust
use opentelemetry_semantic_conventions::resource::{
    FAAS_NAME, FAAS_VERSION, FAAS_INSTANCE, FAAS_MAX_MEMORY,
};

/// Lambda 资源检测器
pub struct LambdaResourceDetector;

impl LambdaResourceDetector {
    /// 检测 Lambda 函数属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "aws"),
            KeyValue::new(CLOUD_PLATFORM, "aws_lambda"),
        ];
        
        // 函数名称
        if let Ok(func_name) = std::env::var("AWS_LAMBDA_FUNCTION_NAME") {
            attrs.push(KeyValue::new(FAAS_NAME, func_name));
        }
        
        // 函数版本
        if let Ok(func_version) = std::env::var("AWS_LAMBDA_FUNCTION_VERSION") {
            attrs.push(KeyValue::new(FAAS_VERSION, func_version));
        }
        
        // 函数内存限制
        if let Ok(memory) = std::env::var("AWS_LAMBDA_FUNCTION_MEMORY_SIZE") {
            if let Ok(memory_mb) = memory.parse::<i64>() {
                attrs.push(KeyValue::new(FAAS_MAX_MEMORY, memory_mb));
            }
        }
        
        // Region
        if let Ok(region) = std::env::var("AWS_REGION") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        // Log Stream (作为实例 ID)
        if let Ok(log_stream) = std::env::var("AWS_LAMBDA_LOG_STREAM_NAME") {
            attrs.push(KeyValue::new(FAAS_INSTANCE, log_stream));
        }
        
        // 执行环境
        if let Ok(exec_env) = std::env::var("AWS_EXECUTION_ENV") {
            attrs.push(KeyValue::new("faas.runtime", exec_env));
        }
        
        attrs
    }
}

/// Lambda 追踪包装器
pub async fn with_lambda_tracing<F, T>(
    function_name: &str,
    handler: F,
) -> Result<T, Box<dyn std::error::Error>>
where
    F: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
{
    use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}};
    
    let tracer = global::tracer("lambda-handler");
    let mut span = tracer
        .span_builder(function_name)
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 从 X-Ray 提取 trace context
    if let Ok(trace_header) = std::env::var("_X_AMZN_TRACE_ID") {
        // 解析 X-Ray trace header
        // Format: Root=1-5e645f3e-1234567890abcdef;Parent=abcdef1234567890;Sampled=1
        span.set_attribute(KeyValue::new("aws.xray.trace_id", trace_header));
    }
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let _guard = cx.attach();
    
    let result = handler.await;
    
    match &result {
        Ok(_) => {
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err(e) => {
            span.record_error(&**e);
            span.set_status(opentelemetry::trace::Status::error(e.to_string()));
        }
    }
    
    span.end();
    result
}
```

---

## 4. ECS 容器属性

```rust
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct EcsMetadata {
    #[serde(rename = "TaskARN")]
    task_arn: String,
    
    #[serde(rename = "Family")]
    family: String,
    
    #[serde(rename = "Revision")]
    revision: String,
    
    #[serde(rename = "Cluster")]
    cluster: String,
    
    #[serde(rename = "AvailabilityZone")]
    availability_zone: Option<String>,
}

/// ECS 资源检测器
pub struct EcsResourceDetector {
    client: Client,
}

impl EcsResourceDetector {
    pub fn new() -> Self {
        Self {
            client: Client::builder()
                .timeout(Duration::from_secs(1))
                .build()
                .unwrap(),
        }
    }
    
    /// 检测 ECS 任务属性
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "aws"),
        ];
        
        // 检测是否是 Fargate
        let is_fargate = std::env::var("AWS_EXECUTION_ENV")
            .map(|v| v.contains("Fargate"))
            .unwrap_or(false);
        
        if is_fargate {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_ecs_fargate"));
        } else {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_ecs"));
        }
        
        // 从 ECS metadata endpoint 获取信息
        if let Ok(metadata_uri) = std::env::var("ECS_CONTAINER_METADATA_URI_V4") {
            if let Ok(metadata) = Self::fetch_metadata(&metadata_uri).await {
                attrs.extend(Self::parse_metadata(metadata));
            }
        }
        
        // Region
        if let Ok(region) = std::env::var("AWS_REGION") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        attrs
    }
    
    async fn fetch_metadata(uri: &str) -> anyhow::Result<EcsMetadata> {
        let client = Client::new();
        let response = client
            .get(format!("{}/task", uri))
            .send()
            .await?;
        
        let metadata = response.json::<EcsMetadata>().await?;
        Ok(metadata)
    }
    
    fn parse_metadata(metadata: EcsMetadata) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        // Task ARN
        attrs.push(KeyValue::new("aws.ecs.task.arn", metadata.task_arn.clone()));
        
        // Task Family
        attrs.push(KeyValue::new("aws.ecs.task.family", metadata.family));
        
        // Task Revision
        attrs.push(KeyValue::new("aws.ecs.task.revision", metadata.revision));
        
        // Cluster ARN
        attrs.push(KeyValue::new("aws.ecs.cluster.arn", metadata.cluster));
        
        // Availability Zone
        if let Some(az) = metadata.availability_zone {
            attrs.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, az));
        }
        
        // 从 ARN 提取 Account ID
        // ARN format: arn:aws:ecs:region:account-id:task/cluster-name/task-id
        if let Some(account_id) = Self::extract_account_id(&metadata.task_arn) {
            attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, account_id));
        }
        
        attrs
    }
    
    fn extract_account_id(arn: &str) -> Option<String> {
        let parts: Vec<&str> = arn.split(':').collect();
        if parts.len() >= 5 {
            Some(parts[4].to_string())
        } else {
            None
        }
    }
}
```

---

## 5. EKS 集群属性

```rust
/// EKS 资源检测器
pub struct EksResourceDetector;

impl EksResourceDetector {
    /// 检测 EKS 集群属性
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "aws"),
            KeyValue::new(CLOUD_PLATFORM, "aws_eks"),
        ];
        
        // Kubernetes 属性
        attrs.extend(Self::detect_k8s_attributes());
        
        // EKS 特定属性
        // Cluster 名称 (从 AWS API 或配置)
        if let Ok(cluster_name) = std::env::var("EKS_CLUSTER_NAME") {
            attrs.push(KeyValue::new("aws.eks.cluster.name", cluster_name));
        }
        
        // Region (从 EC2 metadata)
        if let Ok(region) = Self::detect_region().await {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        attrs
    }
    
    fn detect_k8s_attributes() -> Vec<KeyValue> {
        use opentelemetry_semantic_conventions::resource::{
            K8S_POD_NAME, K8S_NAMESPACE_NAME, K8S_NODE_NAME,
        };
        
        let mut attrs = Vec::new();
        
        if let Ok(pod_name) = std::env::var("K8S_POD_NAME") {
            attrs.push(KeyValue::new(K8S_POD_NAME, pod_name));
        }
        if let Ok(namespace) = std::env::var("K8S_NAMESPACE_NAME") {
            attrs.push(KeyValue::new(K8S_NAMESPACE_NAME, namespace));
        }
        if let Ok(node_name) = std::env::var("K8S_NODE_NAME") {
            attrs.push(KeyValue::new(K8S_NODE_NAME, node_name));
        }
        
        attrs
    }
    
    async fn detect_region() -> anyhow::Result<String> {
        let client = Client::new();
        let response = client
            .get("http://169.254.169.254/latest/meta-data/placement/region")
            .timeout(Duration::from_secs(1))
            .send()
            .await?;
        
        Ok(response.text().await?)
    }
}
```

---

## 6. 完整AWS资源检测器

```rust
use opentelemetry::Resource;

/// 完整的 AWS 资源检测器
pub struct AwsResourceDetector;

impl AwsResourceDetector {
    /// 自动检测并构建 AWS 资源
    pub async fn detect() -> Resource {
        let platform = AwsPlatform::detect();
        
        let attrs = match platform {
            Some(AwsPlatform::Lambda) => {
                LambdaResourceDetector::detect()
            }
            Some(AwsPlatform::Ecs) | Some(AwsPlatform::EcsFargate) => {
                EcsResourceDetector::detect().await
            }
            Some(AwsPlatform::Eks) => {
                EksResourceDetector::detect().await
            }
            Some(AwsPlatform::Ec2) => {
                let mut client = Ec2MetadataClient::new();
                client.detect_attributes().await
            }
            _ => {
                vec![KeyValue::new(CLOUD_PROVIDER, "aws")]
            }
        };
        
        Resource::new(attrs)
    }
}
```

---

## 7. X-Ray 集成

```rust
use opentelemetry::propagation::{Extractor, Injector};

/// X-Ray Trace ID 转换
pub struct XRayPropagator;

impl XRayPropagator {
    /// 解析 X-Ray Trace Header
    /// Format: Root=1-5e645f3e-1234567890abcdef;Parent=abcdef1234567890;Sampled=1
    pub fn parse_trace_header(header: &str) -> Option<(String, String, bool)> {
        let mut root = None;
        let mut parent = None;
        let mut sampled = false;
        
        for part in header.split(';') {
            let kv: Vec<&str> = part.split('=').collect();
            if kv.len() == 2 {
                match kv[0] {
                    "Root" => root = Some(kv[1].to_string()),
                    "Parent" => parent = Some(kv[1].to_string()),
                    "Sampled" => sampled = kv[1] == "1",
                    _ => {}
                }
            }
        }
        
        if let (Some(root), Some(parent)) = (root, parent) {
            Some((root, parent, sampled))
        } else {
            None
        }
    }
    
    /// 生成 X-Ray Trace Header
    pub fn format_trace_header(trace_id: &str, parent_id: &str, sampled: bool) -> String {
        format!(
            "Root={};Parent={};Sampled={}",
            trace_id,
            parent_id,
            if sampled { "1" } else { "0" }
        )
    }
}
```

---

## 8. CloudWatch 集成

```rust
use aws_sdk_cloudwatch::{Client as CloudWatchClient, types::MetricDatum};
use opentelemetry::metrics::{Meter, MeterProvider};

/// CloudWatch Metrics 导出器
pub struct CloudWatchMetricsExporter {
    client: CloudWatchClient,
    namespace: String,
}

impl CloudWatchMetricsExporter {
    pub async fn new(namespace: impl Into<String>) -> Self {
        let config = aws_config::load_from_env().await;
        let client = CloudWatchClient::new(&config);
        
        Self {
            client,
            namespace: namespace.into(),
        }
    }
    
    /// 发送指标到 CloudWatch
    pub async fn export_metric(
        &self,
        name: &str,
        value: f64,
        unit: &str,
    ) -> anyhow::Result<()> {
        let datum = MetricDatum::builder()
            .metric_name(name)
            .value(value)
            .unit(unit.parse().unwrap())
            .build();
        
        self.client
            .put_metric_data()
            .namespace(&self.namespace)
            .metric_data(datum)
            .send()
            .await?;
        
        Ok(())
    }
}
```

---

## 9. 完整示例

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{Resource, trace::TracerProvider};
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 检测 AWS 资源
    let aws_resource = AwsResourceDetector::detect().await;
    
    // 2. 合并服务资源
    let service_resource = Resource::new(vec![
        KeyValue::new("service.name", "my-aws-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);
    
    let resource = service_resource.merge(&aws_resource);
    
    // 3. 初始化 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_resource(resource)
        .with_simple_exporter(opentelemetry_stdout::SpanExporter::default())
        .build();
    
    global::set_tracer_provider(tracer_provider);
    
    // 4. 创建 tracer
    let tracer = global::tracer("aws-service");
    
    // 5. 创建 span
    let span = tracer.start("process_request");
    let cx = opentelemetry::Context::current_with_span(span);
    let _guard = cx.attach();
    
    // 业务逻辑
    println!("Processing request in AWS...");
    
    Ok(())
}
```

---

## 10. 最佳实践

### 10.1 IMDSv2 使用

```rust
// ✅ 推荐: 使用 IMDSv2 (token-based)
let token = client
    .put("http://169.254.169.254/latest/api/token")
    .header("X-aws-ec2-metadata-token-ttl-seconds", "21600")
    .send()
    .await?
    .text()
    .await?;

let metadata = client
    .get("http://169.254.169.254/latest/meta-data/instance-id")
    .header("X-aws-ec2-metadata-token", token)
    .send()
    .await?;

// ❌ 不推荐: 使用 IMDSv1 (不安全)
let metadata = client
    .get("http://169.254.169.254/latest/meta-data/instance-id")
    .send()
    .await?;
```

### 10.2 超时处理

```rust
// ✅ 设置合理的超时
let client = Client::builder()
    .timeout(Duration::from_secs(1))  // 快速失败
    .build()?;
```

### 10.3 Cargo.toml 配置

```toml
[dependencies]
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"

# AWS SDK
aws-config = "1.61"
aws-sdk-cloudwatch = "1.61"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

---

## 总结

本文档提供了完整的 AWS 平台 OpenTelemetry 集成方案：

1. **EC2**: IMDSv2 metadata 检测
2. **Lambda**: 函数属性和追踪包装
3. **ECS/Fargate**: 容器 metadata 检测
4. **EKS**: Kubernetes + EC2 组合
5. **X-Ray**: Trace context 转换
6. **CloudWatch**: Metrics 导出

所有实现都基于 **Rust 1.90**、**async/await** 和最新的 AWS SDK。

**下一步**: 查看 [Azure 属性](02_Azure属性详解_Rust完整版.md) 和 [GCP 属性](03_GCP属性详解_Rust完整版.md)。
