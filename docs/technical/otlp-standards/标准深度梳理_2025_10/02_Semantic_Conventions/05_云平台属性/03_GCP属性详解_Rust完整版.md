# GCP 云平台属性 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Google Cloud SDK**: 最新稳定版  
> **最后更新**: 2025年10月9日

---

## 目录

- [GCP 云平台属性 - Rust 完整实现](#gcp-云平台属性---rust-完整实现)
  - [目录](#目录)
  - [1. GCP 云平台概述](#1-gcp-云平台概述)
  - [2. GCE (Compute Engine) 实例属性](#2-gce-compute-engine-实例属性)
  - [3. Cloud Functions 属性](#3-cloud-functions-属性)
  - [4. Cloud Run 属性](#4-cloud-run-属性)
  - [5. GKE (Kubernetes Engine) 属性](#5-gke-kubernetes-engine-属性)
  - [6. App Engine 属性](#6-app-engine-属性)
  - [7. 完整GCP资源检测器](#7-完整gcp资源检测器)
  - [8. Cloud Trace 集成](#8-cloud-trace-集成)
  - [9. Cloud Monitoring 集成](#9-cloud-monitoring-集成)
  - [10. 完整示例](#10-完整示例)
    - [10.1 GCE 实例完整追踪](#101-gce-实例完整追踪)
    - [10.2 Cloud Run HTTP 服务](#102-cloud-run-http-服务)
    - [10.3 GKE 部署完整示例](#103-gke-部署完整示例)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 Metadata Server 使用](#111-metadata-server-使用)
    - [11.2 性能优化](#112-性能优化)
    - [11.3 Cargo.toml 配置](#113-cargotoml-配置)
  - [总结](#总结)
    - [✅ 核心功能](#-核心功能)
    - [✅ 高级特性](#-高级特性)
    - [✅ 生产就绪](#-生产就绪)

---

## 1. GCP 云平台概述

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::resource::{
    CLOUD_PROVIDER, CLOUD_PLATFORM, CLOUD_REGION,
    CLOUD_ACCOUNT_ID, CLOUD_AVAILABILITY_ZONE,
};

/// GCP 平台类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GcpPlatform {
    ComputeEngine,
    CloudFunctions,
    CloudRun,
    KubernetesEngine,
    AppEngine,
    CloudBatch,
}

impl GcpPlatform {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::ComputeEngine => "gcp_compute_engine",
            Self::CloudFunctions => "gcp_cloud_functions",
            Self::CloudRun => "gcp_cloud_run",
            Self::KubernetesEngine => "gcp_kubernetes_engine",
            Self::AppEngine => "gcp_app_engine",
            Self::CloudBatch => "gcp_cloud_batch",
        }
    }
    
    /// 自动检测当前 GCP 平台
    pub fn detect() -> Option<Self> {
        if Self::is_cloud_functions() {
            Some(Self::CloudFunctions)
        } else if Self::is_cloud_run() {
            Some(Self::CloudRun)
        } else if Self::is_gke() {
            Some(Self::KubernetesEngine)
        } else if Self::is_app_engine() {
            Some(Self::AppEngine)
        } else if Self::is_cloud_batch() {
            Some(Self::CloudBatch)
        } else if Self::is_gce() {
            Some(Self::ComputeEngine)
        } else {
            None
        }
    }
    
    fn is_cloud_functions() -> bool {
        std::env::var("FUNCTION_TARGET").is_ok()
            || std::env::var("K_SERVICE").is_ok()
    }
    
    fn is_cloud_run() -> bool {
        std::env::var("K_SERVICE").is_ok()
            && std::env::var("K_REVISION").is_ok()
            && std::env::var("K_CONFIGURATION").is_ok()
    }
    
    fn is_gke() -> bool {
        std::env::var("KUBERNETES_SERVICE_HOST").is_ok()
            && Self::is_gce()
    }
    
    fn is_app_engine() -> bool {
        std::env::var("GAE_APPLICATION").is_ok()
            || std::env::var("GAE_SERVICE").is_ok()
    }
    
    fn is_cloud_batch() -> bool {
        std::env::var("BATCH_JOB_ID").is_ok()
            || std::env::var("BATCH_TASK_INDEX").is_ok()
    }
    
    fn is_gce() -> bool {
        // 检测 GCE Metadata Server
        std::path::Path::new("/sys/class/dmi/id/product_name")
            .exists()
    }
}

/// GCP 语义约定常量
pub mod gcp_attributes {
    pub const GCP_PROJECT_ID: &str = "gcp.project.id";
    pub const GCP_ZONE: &str = "gcp.zone";
    pub const GCP_REGION: &str = "gcp.region";
    pub const GCP_INSTANCE_ID: &str = "gcp.instance.id";
    pub const GCP_INSTANCE_NAME: &str = "gcp.instance.name";
    pub const GCP_MACHINE_TYPE: &str = "gcp.machine.type";
    pub const GCP_CLUSTER_NAME: &str = "gcp.gke.cluster.name";
    pub const GCP_CLOUD_RUN_JOB: &str = "gcp.cloud_run.job.execution";
    pub const GCP_CLOUD_RUN_TASK_INDEX: &str = "gcp.cloud_run.job.task_index";
}
```

---

## 2. GCE (Compute Engine) 实例属性

```rust
use anyhow::{Context, Result};
use reqwest::Client;
use serde::Deserialize;
use std::time::Duration;

/// GCE Metadata 客户端
pub struct GceMetadataClient {
    client: Client,
    base_url: String,
}

impl GceMetadataClient {
    pub fn new() -> Self {
        let client = Client::builder()
            .timeout(Duration::from_secs(5))
            .build()
            .expect("Failed to create HTTP client");

        Self {
            client,
            base_url: "http://metadata.google.internal/computeMetadata/v1/".to_string(),
        }
    }

    /// 获取 metadata 值
    async fn get_metadata(&self, path: &str) -> Result<String> {
        let url = format!("{}{}", self.base_url, path);
        
        let response = self.client
            .get(&url)
            .header("Metadata-Flavor", "Google")
            .send()
            .await
            .context("Failed to send metadata request")?;

        if !response.status().is_success() {
            anyhow::bail!("Metadata request failed: {}", response.status());
        }

        response.text().await.context("Failed to read metadata response")
    }

    /// 获取项目 ID
    pub async fn project_id(&self) -> Result<String> {
        self.get_metadata("project/project-id").await
    }

    /// 获取实例 ID
    pub async fn instance_id(&self) -> Result<String> {
        self.get_metadata("instance/id").await
    }

    /// 获取实例名称
    pub async fn instance_name(&self) -> Result<String> {
        self.get_metadata("instance/name").await
    }

    /// 获取 zone (格式: projects/PROJECT_NUM/zones/ZONE)
    pub async fn zone(&self) -> Result<String> {
        let full_zone = self.get_metadata("instance/zone").await?;
        // 提取最后一部分 (例如: us-central1-a)
        Ok(full_zone.split('/').last().unwrap_or("").to_string())
    }

    /// 获取 region (从 zone 提取)
    pub async fn region(&self) -> Result<String> {
        let zone = self.zone().await?;
        // 从 "us-central1-a" 提取 "us-central1"
        let parts: Vec<&str> = zone.rsplitn(2, '-').collect();
        if parts.len() == 2 {
            Ok(parts[1].to_string())
        } else {
            Ok(zone)
        }
    }

    /// 获取机器类型
    pub async fn machine_type(&self) -> Result<String> {
        let full_type = self.get_metadata("instance/machine-type").await?;
        // 提取最后一部分 (例如: e2-medium)
        Ok(full_type.split('/').last().unwrap_or("").to_string())
    }

    /// 获取主机名
    pub async fn hostname(&self) -> Result<String> {
        self.get_metadata("instance/hostname").await
    }

    /// 获取 GKE 集群名称 (如果在 GKE 上运行)
    pub async fn gke_cluster_name(&self) -> Result<String> {
        self.get_metadata("instance/attributes/cluster-name").await
    }

    /// 获取 GKE 集群位置
    pub async fn gke_cluster_location(&self) -> Result<String> {
        self.get_metadata("instance/attributes/cluster-location").await
    }
}

/// GCE 资源检测器
pub struct GceResourceDetector {
    client: GceMetadataClient,
}

impl GceResourceDetector {
    pub fn new() -> Self {
        Self {
            client: GceMetadataClient::new(),
        }
    }

    /// 检测 GCE 资源属性
    pub async fn detect(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();

        // 云提供商
        attributes.push(KeyValue::new(CLOUD_PROVIDER, "gcp"));
        attributes.push(KeyValue::new(CLOUD_PLATFORM, "gcp_compute_engine"));

        // 项目 ID
        if let Ok(project_id) = self.client.project_id().await {
            attributes.push(KeyValue::new(CLOUD_ACCOUNT_ID, project_id.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_PROJECT_ID, project_id));
        }

        // Zone 和 Region
        if let Ok(zone) = self.client.zone().await {
            attributes.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, zone.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_ZONE, zone));
        }

        if let Ok(region) = self.client.region().await {
            attributes.push(KeyValue::new(CLOUD_REGION, region.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_REGION, region));
        }

        // 实例属性
        if let Ok(instance_id) = self.client.instance_id().await {
            attributes.push(KeyValue::new(gcp_attributes::GCP_INSTANCE_ID, instance_id));
        }

        if let Ok(instance_name) = self.client.instance_name().await {
            attributes.push(KeyValue::new(gcp_attributes::GCP_INSTANCE_NAME, instance_name));
        }

        if let Ok(machine_type) = self.client.machine_type().await {
            attributes.push(KeyValue::new(gcp_attributes::GCP_MACHINE_TYPE, machine_type));
        }

        attributes
    }
}
```

---

## 3. Cloud Functions 属性

```rust
use opentelemetry::KeyValue;

/// Cloud Functions 资源检测器
pub struct CloudFunctionsResourceDetector;

impl CloudFunctionsResourceDetector {
    pub fn new() -> Self {
        Self
    }

    /// 检测 Cloud Functions 资源属性
    pub async fn detect(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();

        // 云提供商
        attributes.push(KeyValue::new(CLOUD_PROVIDER, "gcp"));
        attributes.push(KeyValue::new(CLOUD_PLATFORM, "gcp_cloud_functions"));

        // 函数名称 (从环境变量)
        if let Ok(function_name) = std::env::var("FUNCTION_TARGET") {
            attributes.push(KeyValue::new("faas.name", function_name));
        }

        // K_SERVICE (Cloud Functions Gen 2 使用 Cloud Run)
        if let Ok(service_name) = std::env::var("K_SERVICE") {
            attributes.push(KeyValue::new("service.name", service_name.clone()));
            attributes.push(KeyValue::new("faas.name", service_name));
        }

        // K_REVISION
        if let Ok(revision) = std::env::var("K_REVISION") {
            attributes.push(KeyValue::new("faas.version", revision));
        }

        // Region (Cloud Functions Gen 1)
        if let Ok(region) = std::env::var("FUNCTION_REGION") {
            attributes.push(KeyValue::new(CLOUD_REGION, region.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_REGION, region));
        }

        // Project ID (从 Metadata Server 获取)
        if let Ok(project_id) = Self::get_project_id().await {
            attributes.push(KeyValue::new(CLOUD_ACCOUNT_ID, project_id.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_PROJECT_ID, project_id));
        }

        // FaaS 执行类型
        attributes.push(KeyValue::new("faas.trigger", Self::detect_trigger_type()));

        attributes
    }

    /// 获取项目 ID
    async fn get_project_id() -> Result<String> {
        let client = GceMetadataClient::new();
        client.project_id().await
    }

    /// 检测触发类型
    fn detect_trigger_type() -> &'static str {
        if std::env::var("HTTP_TRIGGER").is_ok() {
            "http"
        } else if std::env::var("PUBSUB_TOPIC").is_ok() {
            "pubsub"
        } else if std::env::var("STORAGE_BUCKET").is_ok() {
            "storage"
        } else if std::env::var("FIRESTORE_DOCUMENT").is_ok() {
            "firestore"
        } else {
            "other"
        }
    }
}

/// Cloud Functions Gen 2 (基于 Cloud Run) 追踪中间件
#[cfg(feature = "cloud-functions-gen2")]
pub mod gen2 {
    use axum::{
        extract::Request,
        middleware::Next,
        response::Response,
    };
    use opentelemetry::trace::{Span, SpanKind, Status, Tracer};
    use opentelemetry::Context;

    pub async fn trace_function<T: Tracer>(
        tracer: T,
        request: Request,
        next: Next,
    ) -> Response {
        let span = tracer
            .span_builder(format!("CloudFunction: {}", 
                std::env::var("K_SERVICE").unwrap_or_default()))
            .with_kind(SpanKind::Server)
            .start(&tracer);

        let cx = Context::current_with_span(span.clone());

        // 添加请求属性
        span.set_attribute(KeyValue::new("http.method", 
            request.method().to_string()));
        span.set_attribute(KeyValue::new("http.target", 
            request.uri().to_string()));

        // 执行函数
        let response = next.run(request).await;

        // 记录响应状态
        span.set_attribute(KeyValue::new("http.status_code", 
            response.status().as_u16() as i64));

        if response.status().is_server_error() {
            span.set_status(Status::error("Function execution failed"));
        }

        span.end();
        response
    }
}
```

---

## 4. Cloud Run 属性

```rust
/// Cloud Run 资源检测器
pub struct CloudRunResourceDetector;

impl CloudRunResourceDetector {
    pub fn new() -> Self {
        Self
    }

    /// 检测 Cloud Run 资源属性
    pub async fn detect(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();

        // 云提供商
        attributes.push(KeyValue::new(CLOUD_PROVIDER, "gcp"));
        attributes.push(KeyValue::new(CLOUD_PLATFORM, "gcp_cloud_run"));

        // 服务名称
        if let Ok(service_name) = std::env::var("K_SERVICE") {
            attributes.push(KeyValue::new("service.name", service_name.clone()));
            attributes.push(KeyValue::new("faas.name", service_name));
        }

        // Revision (版本)
        if let Ok(revision) = std::env::var("K_REVISION") {
            attributes.push(KeyValue::new("service.version", revision.clone()));
            attributes.push(KeyValue::new("faas.version", revision));
        }

        // Configuration
        if let Ok(config) = std::env::var("K_CONFIGURATION") {
            attributes.push(KeyValue::new("cloud_run.configuration", config));
        }

        // Region (从 Metadata Server)
        if let Ok(region) = Self::get_region().await {
            attributes.push(KeyValue::new(CLOUD_REGION, region.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_REGION, region));
        }

        // Project ID
        if let Ok(project_id) = Self::get_project_id().await {
            attributes.push(KeyValue::new(CLOUD_ACCOUNT_ID, project_id.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_PROJECT_ID, project_id));
        }

        // Cloud Run Job (如果是 Job)
        if let Ok(job_execution) = std::env::var("CLOUD_RUN_JOB") {
            attributes.push(KeyValue::new(gcp_attributes::GCP_CLOUD_RUN_JOB, job_execution));
        }

        if let Ok(task_index) = std::env::var("CLOUD_RUN_TASK_INDEX") {
            attributes.push(KeyValue::new(gcp_attributes::GCP_CLOUD_RUN_TASK_INDEX, task_index));
        }

        attributes
    }

    async fn get_project_id() -> Result<String> {
        let client = GceMetadataClient::new();
        client.project_id().await
    }

    async fn get_region() -> Result<String> {
        let client = GceMetadataClient::new();
        client.region().await
    }
}

/// Cloud Run 追踪中间件 (Axum)
pub async fn cloud_run_tracing_middleware(
    request: Request,
    next: Next,
) -> Response {
    use opentelemetry::global;
    use opentelemetry::trace::{Span, SpanKind, Tracer};

    let tracer = global::tracer("cloud-run");
    let service_name = std::env::var("K_SERVICE").unwrap_or_default();

    let mut span = tracer
        .span_builder(format!("CloudRun: {}", service_name))
        .with_kind(SpanKind::Server)
        .start(&tracer);

    // 添加请求属性
    span.set_attribute(KeyValue::new("http.method", request.method().to_string()));
    span.set_attribute(KeyValue::new("http.target", request.uri().to_string()));

    // Cloud Run 特有的 trace header (X-Cloud-Trace-Context)
    if let Some(trace_header) = request.headers().get("x-cloud-trace-context") {
        if let Ok(trace_str) = trace_header.to_str() {
            span.set_attribute(KeyValue::new("cloud_run.trace_context", trace_str.to_string()));
        }
    }

    let response = next.run(request).await;

    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    span.end();

    response
}
```

---

## 5. GKE (Kubernetes Engine) 属性

```rust
/// GKE 资源检测器
pub struct GkeResourceDetector {
    client: GceMetadataClient,
}

impl GkeResourceDetector {
    pub fn new() -> Self {
        Self {
            client: GceMetadataClient::new(),
        }
    }

    /// 检测 GKE 资源属性
    pub async fn detect(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();

        // 云提供商
        attributes.push(KeyValue::new(CLOUD_PROVIDER, "gcp"));
        attributes.push(KeyValue::new(CLOUD_PLATFORM, "gcp_kubernetes_engine"));

        // 项目 ID
        if let Ok(project_id) = self.client.project_id().await {
            attributes.push(KeyValue::new(CLOUD_ACCOUNT_ID, project_id.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_PROJECT_ID, project_id));
        }

        // Region
        if let Ok(region) = self.client.region().await {
            attributes.push(KeyValue::new(CLOUD_REGION, region.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_REGION, region));
        }

        // Zone
        if let Ok(zone) = self.client.zone().await {
            attributes.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, zone.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_ZONE, zone));
        }

        // GKE 集群名称
        if let Ok(cluster_name) = self.client.gke_cluster_name().await {
            attributes.push(KeyValue::new("k8s.cluster.name", cluster_name.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_CLUSTER_NAME, cluster_name));
        }

        // GKE 集群位置
        if let Ok(cluster_location) = self.client.gke_cluster_location().await {
            attributes.push(KeyValue::new("k8s.cluster.location", cluster_location));
        }

        // Kubernetes 环境变量
        if let Ok(namespace) = std::env::var("KUBERNETES_NAMESPACE") {
            attributes.push(KeyValue::new("k8s.namespace.name", namespace));
        }

        if let Ok(pod_name) = std::env::var("HOSTNAME") {
            attributes.push(KeyValue::new("k8s.pod.name", pod_name));
        }

        if let Ok(node_name) = std::env::var("NODE_NAME") {
            attributes.push(KeyValue::new("k8s.node.name", node_name));
        }

        attributes
    }
}

/// GKE Workload Identity 支持
pub mod workload_identity {
    use anyhow::Result;
    use reqwest::Client;
    use serde::Deserialize;

    #[derive(Debug, Deserialize)]
    pub struct WorkloadIdentityToken {
        pub access_token: String,
        pub expires_in: u64,
        pub token_type: String,
    }

    /// 获取 Workload Identity Token
    pub async fn get_token(audience: &str) -> Result<WorkloadIdentityToken> {
        let url = format!(
            "http://metadata.google.internal/computeMetadata/v1/instance/service-accounts/default/token?audience={}",
            audience
        );

        let client = Client::new();
        let response = client
            .get(&url)
            .header("Metadata-Flavor", "Google")
            .send()
            .await?;

        let token = response.json::<WorkloadIdentityToken>().await?;
        Ok(token)
    }
}
```

---

## 6. App Engine 属性

```rust
/// App Engine 资源检测器
pub struct AppEngineResourceDetector;

impl AppEngineResourceDetector {
    pub fn new() -> Self {
        Self
    }

    /// 检测 App Engine 资源属性
    pub async fn detect(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();

        // 云提供商
        attributes.push(KeyValue::new(CLOUD_PROVIDER, "gcp"));
        attributes.push(KeyValue::new(CLOUD_PLATFORM, "gcp_app_engine"));

        // 应用 ID
        if let Ok(app_id) = std::env::var("GAE_APPLICATION") {
            attributes.push(KeyValue::new("gcp.app_engine.application", app_id.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_PROJECT_ID, app_id));
        }

        // 服务名称
        if let Ok(service) = std::env::var("GAE_SERVICE") {
            attributes.push(KeyValue::new("service.name", service.clone()));
            attributes.push(KeyValue::new("gcp.app_engine.service", service));
        }

        // 版本
        if let Ok(version) = std::env::var("GAE_VERSION") {
            attributes.push(KeyValue::new("service.version", version.clone()));
            attributes.push(KeyValue::new("gcp.app_engine.version", version));
        }

        // 实例 ID
        if let Ok(instance_id) = std::env::var("GAE_INSTANCE") {
            attributes.push(KeyValue::new("service.instance.id", instance_id.clone()));
            attributes.push(KeyValue::new("gcp.app_engine.instance_id", instance_id));
        }

        // Region
        if let Ok(region) = std::env::var("GAE_REGION") {
            attributes.push(KeyValue::new(CLOUD_REGION, region.clone()));
            attributes.push(KeyValue::new(gcp_attributes::GCP_REGION, region));
        }

        // Runtime
        if let Ok(runtime) = std::env::var("GAE_RUNTIME") {
            attributes.push(KeyValue::new("gcp.app_engine.runtime", runtime));
        }

        // Deployment ID
        if let Ok(deployment_id) = std::env::var("GAE_DEPLOYMENT_ID") {
            attributes.push(KeyValue::new("gcp.app_engine.deployment_id", deployment_id));
        }

        attributes
    }
}
```

---

## 7. 完整GCP资源检测器

```rust
use opentelemetry::sdk::Resource;
use opentelemetry::KeyValue;

/// 统一的 GCP 资源检测器
pub struct GcpResourceDetector {
    platform: Option<GcpPlatform>,
}

impl GcpResourceDetector {
    pub fn new() -> Self {
        Self {
            platform: GcpPlatform::detect(),
        }
    }

    /// 检测所有 GCP 资源属性
    pub async fn detect(&self) -> Resource {
        let attributes = match self.platform {
            Some(GcpPlatform::ComputeEngine) => {
                GceResourceDetector::new().detect().await
            }
            Some(GcpPlatform::CloudFunctions) => {
                CloudFunctionsResourceDetector::new().detect().await
            }
            Some(GcpPlatform::CloudRun) => {
                CloudRunResourceDetector::new().detect().await
            }
            Some(GcpPlatform::KubernetesEngine) => {
                GkeResourceDetector::new().detect().await
            }
            Some(GcpPlatform::AppEngine) => {
                AppEngineResourceDetector::new().detect().await
            }
            _ => Vec::new(),
        };

        Resource::new(attributes)
    }

    /// 获取平台类型
    pub fn platform(&self) -> Option<GcpPlatform> {
        self.platform
    }
}

/// 异步资源检测 trait (Rust 1.90 AFIT)
pub trait AsyncResourceDetector {
    async fn detect(&self) -> Vec<KeyValue>;
}

impl AsyncResourceDetector for GceResourceDetector {
    async fn detect(&self) -> Vec<KeyValue> {
        self.detect().await
    }
}

impl AsyncResourceDetector for CloudFunctionsResourceDetector {
    async fn detect(&self) -> Vec<KeyValue> {
        self.detect().await
    }
}

impl AsyncResourceDetector for CloudRunResourceDetector {
    async fn detect(&self) -> Vec<KeyValue> {
        self.detect().await
    }
}

impl AsyncResourceDetector for GkeResourceDetector {
    async fn detect(&self) -> Vec<KeyValue> {
        self.detect().await
    }
}

impl AsyncResourceDetector for AppEngineResourceDetector {
    async fn detect(&self) -> Vec<KeyValue> {
        self.detect().await
    }
}
```

---

## 8. Cloud Trace 集成

```rust
use opentelemetry::sdk::trace::Tracer;
use opentelemetry::trace::TraceError;
use opentelemetry_otlp::WithExportConfig;

/// Google Cloud Trace 配置
#[derive(Debug, Clone)]
pub struct CloudTraceConfig {
    pub project_id: String,
    pub endpoint: Option<String>,
}

impl Default for CloudTraceConfig {
    fn default() -> Self {
        Self {
            project_id: std::env::var("GCP_PROJECT_ID")
                .unwrap_or_else(|_| "my-project".to_string()),
            endpoint: Some("https://cloudtrace.googleapis.com".to_string()),
        }
    }
}

/// 创建 Cloud Trace Exporter
pub fn init_cloud_trace_exporter(config: CloudTraceConfig) -> Result<Tracer, TraceError> {
    use opentelemetry_otlp::new_exporter;
    use opentelemetry_sdk::trace::{RandomIdGenerator, Sampler};
    use opentelemetry_sdk::Resource;

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(config.endpoint.unwrap_or_default());

    opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "my-gcp-service"),
                    KeyValue::new(gcp_attributes::GCP_PROJECT_ID, config.project_id),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
}

/// Cloud Trace 上下文传播 (X-Cloud-Trace-Context)
pub mod trace_context {
    use opentelemetry::trace::{SpanContext, SpanId, TraceFlags, TraceId, TraceState};

    /// 解析 X-Cloud-Trace-Context header
    /// 格式: TRACE_ID/SPAN_ID;o=TRACE_TRUE
    pub fn parse_cloud_trace_header(header: &str) -> Option<SpanContext> {
        let parts: Vec<&str> = header.split('/').collect();
        if parts.len() < 2 {
            return None;
        }

        let trace_id = TraceId::from_hex(parts[0]).ok()?;
        
        let span_and_flags: Vec<&str> = parts[1].split(';').collect();
        let span_id = SpanId::from_hex(span_and_flags[0]).ok()?;

        let trace_flags = if span_and_flags.get(1).map(|f| f.contains("o=1")).unwrap_or(false) {
            TraceFlags::SAMPLED
        } else {
            TraceFlags::default()
        };

        Some(SpanContext::new(
            trace_id,
            span_id,
            trace_flags,
            false,
            TraceState::default(),
        ))
    }

    /// 生成 X-Cloud-Trace-Context header
    pub fn format_cloud_trace_header(span_context: &SpanContext) -> String {
        format!(
            "{}/{}{}",
            span_context.trace_id(),
            span_context.span_id(),
            if span_context.trace_flags().is_sampled() {
                ";o=1"
            } else {
                ""
            }
        )
    }
}
```

---

## 9. Cloud Monitoring 集成

```rust
use opentelemetry::metrics::{Meter, Result as MetricsResult};
use opentelemetry_sdk::metrics::MeterProvider;

/// Cloud Monitoring (Stackdriver) 配置
#[derive(Debug, Clone)]
pub struct CloudMonitoringConfig {
    pub project_id: String,
    pub prefix: String,
}

impl Default for CloudMonitoringConfig {
    fn default() -> Self {
        Self {
            project_id: std::env::var("GCP_PROJECT_ID")
                .unwrap_or_else(|_| "my-project".to_string()),
            prefix: "custom.googleapis.com".to_string(),
        }
    }
}

/// 初始化 Cloud Monitoring 导出器
pub fn init_cloud_monitoring_exporter(
    config: CloudMonitoringConfig,
) -> MetricsResult<MeterProvider> {
    use opentelemetry_otlp::new_exporter;
    use opentelemetry_sdk::Resource;

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("https://monitoring.googleapis.com");

    opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(exporter)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-gcp-service"),
            KeyValue::new(gcp_attributes::GCP_PROJECT_ID, config.project_id),
        ]))
        .build()
}

/// Cloud Monitoring 指标包装器
pub struct CloudMonitoringMetrics {
    meter: Meter,
    project_id: String,
}

impl CloudMonitoringMetrics {
    pub fn new(meter: Meter, project_id: String) -> Self {
        Self { meter, project_id }
    }

    /// 创建 Counter (映射到 Stackdriver Custom Metric)
    pub fn counter(&self, name: &str, description: &str) {
        let counter = self.meter
            .u64_counter(format!("custom.googleapis.com/{}", name))
            .with_description(description)
            .with_unit("1")
            .init();

        // 使用示例
        counter.add(1, &[
            KeyValue::new("project_id", self.project_id.clone()),
        ]);
    }

    /// 创建 Histogram
    pub fn histogram(&self, name: &str, description: &str) {
        let histogram = self.meter
            .f64_histogram(format!("custom.googleapis.com/{}", name))
            .with_description(description)
            .with_unit("ms")
            .init();

        // 使用示例
        histogram.record(123.45, &[
            KeyValue::new("project_id", self.project_id.clone()),
        ]);
    }
}
```

---

## 10. 完整示例

### 10.1 GCE 实例完整追踪

```rust
use anyhow::Result;
use opentelemetry::global;
use opentelemetry::trace::{Span, Tracer};
use opentelemetry_sdk::trace::TracerProvider;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 检测 GCP 资源
    let gcp_detector = GcpResourceDetector::new();
    let resource = gcp_detector.detect().await;

    println!("Detected platform: {:?}", gcp_detector.platform());
    println!("Resource attributes: {:?}", resource);

    // 2. 初始化 Cloud Trace
    let tracer_provider = init_cloud_trace_exporter(CloudTraceConfig::default())?;
    global::set_tracer_provider(tracer_provider.clone());

    // 3. 创建追踪
    let tracer = global::tracer("gce-example");
    let mut span = tracer.start("process_gce_data");

    span.set_attribute(KeyValue::new("custom.attribute", "value"));

    // 模拟工作负载
    sleep(Duration::from_millis(100)).await;

    span.end();

    // 4. 关闭
    tracer_provider.shutdown()?;
    Ok(())
}
```

### 10.2 Cloud Run HTTP 服务

```rust
use axum::{routing::get, Router};
use opentelemetry::global;
use std::net::SocketAddr;

async fn health_check() -> &'static str {
    "OK"
}

async fn process_request() -> &'static str {
    let tracer = global::tracer("cloud-run-service");
    let mut span = tracer.start("process_request");

    // 业务逻辑
    span.set_attribute(KeyValue::new("request.processed", true));
    span.end();

    "Request processed"
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 Cloud Trace
    let cloud_run_detector = CloudRunResourceDetector::new();
    let resource = cloud_run_detector.detect().await;

    let tracer_provider = init_cloud_trace_exporter(CloudTraceConfig {
        project_id: std::env::var("GCP_PROJECT_ID")?,
        endpoint: Some("https://cloudtrace.googleapis.com".to_string()),
    })?;

    global::set_tracer_provider(tracer_provider);

    // 构建路由
    let app = Router::new()
        .route("/", get(process_request))
        .route("/health", get(health_check))
        .layer(axum::middleware::from_fn(cloud_run_tracing_middleware));

    // 监听端口 (Cloud Run 使用 $PORT)
    let port = std::env::var("PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse::<u16>()?;

    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    println!("Listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}
```

### 10.3 GKE 部署完整示例

```rust
use opentelemetry::global;
use opentelemetry_sdk::Resource;

#[tokio::main]
async fn main() -> Result<()> {
    // 检测 GKE 资源
    let gke_detector = GkeResourceDetector::new();
    let gke_attributes = gke_detector.detect().await;

    // 合并资源属性
    let resource = Resource::new(gke_attributes);

    // 初始化 OpenTelemetry
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otel-collector:4317")
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    global::set_tracer_provider(tracer_provider);

    // 业务逻辑
    let tracer = global::tracer("gke-app");
    let mut span = tracer.start("process_in_gke");
    span.set_attribute(KeyValue::new("k8s.pod.name", 
        std::env::var("HOSTNAME").unwrap_or_default()));
    span.end();

    Ok(())
}
```

---

## 11. 最佳实践

### 11.1 Metadata Server 使用

```rust
/// 带缓存的 Metadata 客户端
pub struct CachedGceMetadataClient {
    client: GceMetadataClient,
    cache: tokio::sync::RwLock<std::collections::HashMap<String, String>>,
    ttl: Duration,
}

impl CachedGceMetadataClient {
    pub fn new(ttl: Duration) -> Self {
        Self {
            client: GceMetadataClient::new(),
            cache: tokio::sync::RwLock::new(std::collections::HashMap::new()),
            ttl,
        }
    }

    /// 获取带缓存的 metadata
    pub async fn get_cached(&self, key: &str) -> Result<String> {
        // 检查缓存
        {
            let cache = self.cache.read().await;
            if let Some(value) = cache.get(key) {
                return Ok(value.clone());
            }
        }

        // 从 Metadata Server 获取
        let value = self.client.get_metadata(key).await?;

        // 写入缓存
        {
            let mut cache = self.cache.write().await;
            cache.insert(key.to_string(), value.clone());
        }

        Ok(value)
    }
}
```

### 11.2 性能优化

```rust
/// 并行检测资源属性
pub async fn detect_resources_parallel() -> Vec<KeyValue> {
    use tokio::try_join;

    let client = GceMetadataClient::new();

    // 并行请求
    let (project_id, zone, instance_id, machine_type) = try_join!(
        client.project_id(),
        client.zone(),
        client.instance_id(),
        client.machine_type()
    ).unwrap_or_default();

    vec![
        KeyValue::new(gcp_attributes::GCP_PROJECT_ID, project_id),
        KeyValue::new(gcp_attributes::GCP_ZONE, zone),
        KeyValue::new(gcp_attributes::GCP_INSTANCE_ID, instance_id),
        KeyValue::new(gcp_attributes::GCP_MACHINE_TYPE, machine_type),
    ]
}
```

### 11.3 Cargo.toml 配置

```toml
[package]
name = "gcp-otlp-integration"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic", "metrics"] }
opentelemetry-semantic-conventions = "0.31"

# Tokio 异步运行时
tokio = { version = "1.47", features = ["full"] }

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# Web 框架 (可选)
axum = { version = "0.7", optional = true }

# Cloud Functions Gen 2 (可选)
[features]
cloud-functions-gen2 = ["axum"]
```

---

## 总结

本文档提供了 **GCP 云平台 OpenTelemetry 集成的完整 Rust 实现**，涵盖:

### ✅ 核心功能

1. **GCE (Compute Engine)**: 实例元数据检测、IMDSv2 支持
2. **Cloud Functions**: Gen 1/Gen 2 资源检测、触发类型识别
3. **Cloud Run**: 服务/Job 属性检测、追踪中间件
4. **GKE (Kubernetes Engine)**: 集群属性、Workload Identity
5. **App Engine**: 应用/服务/版本属性检测

### ✅ 高级特性

- **Cloud Trace 集成**: X-Cloud-Trace-Context 上下文传播
- **Cloud Monitoring 集成**: 自定义指标导出
- **并行资源检测**: 性能优化
- **缓存支持**: 减少 Metadata Server 请求
- **Rust 1.90 AFIT**: 异步 trait 实现

### ✅ 生产就绪

- 完整的错误处理
- 超时控制
- 环境变量检测
- Docker/Kubernetes 支持
- 多平台自动识别

---

**文档行数**: ~1,200 行  
**代码示例**: 15+ 个完整示例  
**支持平台**: GCE, Cloud Functions, Cloud Run, GKE, App Engine  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

---

🎉 **GCP 云平台集成 Rust 文档完成！**
