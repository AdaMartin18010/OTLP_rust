# Azure 云平台属性 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Azure SDK**: 1.0+  
> **最后更新**: 2025年10月9日

---

## 目录

- [Azure 云平台属性 - Rust 完整实现](#azure-云平台属性---rust-完整实现)
  - [目录](#目录)
  - [1. Azure 云平台概述](#1-azure-云平台概述)
  - [2. Azure VM 属性](#2-azure-vm-属性)
  - [3. Azure Functions 属性](#3-azure-functions-属性)
  - [4. Azure App Service 属性](#4-azure-app-service-属性)
  - [5. Azure Container Instances](#5-azure-container-instances)
  - [6. Azure Kubernetes Service (AKS)](#6-azure-kubernetes-service-aks)
  - [7. Application Insights 集成](#7-application-insights-集成)
  - [8. 完整示例](#8-完整示例)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 环境变量配置](#91-环境变量配置)
    - [9.2 Managed Identity](#92-managed-identity)
    - [9.3 Cargo.toml 配置](#93-cargotoml-配置)
  - [总结](#总结)

---

## 1. Azure 云平台概述

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::resource::{
    CLOUD_PROVIDER, CLOUD_PLATFORM, CLOUD_REGION,
    CLOUD_ACCOUNT_ID, CLOUD_RESOURCE_ID,
};

/// Azure 平台类型
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AzurePlatform {
    VirtualMachine,
    Functions,
    AppService,
    ContainerInstances,
    KubernetesService,
    ContainerApps,
}

impl AzurePlatform {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::VirtualMachine => "azure_vm",
            Self::Functions => "azure_functions",
            Self::AppService => "azure_app_service",
            Self::ContainerInstances => "azure_container_instances",
            Self::KubernetesService => "azure_kubernetes_service",
            Self::ContainerApps => "azure_container_apps",
        }
    }
    
    /// 自动检测当前 Azure 平台
    pub fn detect() -> Option<Self> {
        if Self::is_functions() {
            Some(Self::Functions)
        } else if Self::is_app_service() {
            Some(Self::AppService)
        } else if Self::is_container_instances() {
            Some(Self::ContainerInstances)
        } else if Self::is_aks() {
            Some(Self::KubernetesService)
        } else if Self::is_container_apps() {
            Some(Self::ContainerApps)
        } else if Self::is_vm() {
            Some(Self::VirtualMachine)
        } else {
            None
        }
    }
    
    fn is_functions() -> bool {
        std::env::var("FUNCTIONS_WORKER_RUNTIME").is_ok()
            || std::env::var("WEBSITE_FUNCTIONS_AZUREMONITOR_CATEGORIES").is_ok()
    }
    
    fn is_app_service() -> bool {
        std::env::var("WEBSITE_SITE_NAME").is_ok()
            && !Self::is_functions()
    }
    
    fn is_container_instances() -> bool {
        std::env::var("ACI_RESOURCE_GROUP").is_ok()
    }
    
    fn is_aks() -> bool {
        std::env::var("KUBERNETES_SERVICE_HOST").is_ok()
            && std::path::Path::new("/run/secrets/kubernetes.io").exists()
    }
    
    fn is_container_apps() -> bool {
        std::env::var("CONTAINER_APP_NAME").is_ok()
    }
    
    fn is_vm() -> bool {
        // 尝试访问 Azure Instance Metadata Service
        std::fs::read_to_string("/sys/class/dmi/id/sys_vendor")
            .map(|content| content.contains("Microsoft Corporation"))
            .unwrap_or(false)
    }
}
```

---

## 2. Azure VM 属性

```rust
use reqwest::Client;
use serde::Deserialize;
use std::time::Duration;

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AzureVmMetadata {
    location: String,
    name: String,
    resource_group_name: String,
    subscription_id: String,
    vm_id: String,
    vm_size: String,
    zone: Option<String>,
}

#[derive(Debug, Deserialize)]
struct AzureComputeMetadata {
    #[serde(rename = "azEnvironment")]
    az_environment: String,
    compute: AzureVmMetadata,
}

/// Azure VM Metadata 服务客户端
pub struct AzureVmMetadataClient {
    client: Client,
    base_url: String,
}

impl AzureVmMetadataClient {
    pub fn new() -> Self {
        Self {
            client: Client::builder()
                .timeout(Duration::from_secs(1))
                .build()
                .unwrap(),
            base_url: "http://169.254.169.254/metadata/instance".to_string(),
        }
    }
    
    /// 获取 VM metadata
    async fn get_metadata(&self) -> anyhow::Result<AzureComputeMetadata> {
        let response = self.client
            .get(&format!("{}?api-version=2021-02-01", self.base_url))
            .header("Metadata", "true")
            .send()
            .await?;
        
        let metadata = response.json::<AzureComputeMetadata>().await?;
        Ok(metadata)
    }
    
    /// 检测 VM 资源属性
    pub async fn detect_attributes(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
            KeyValue::new(CLOUD_PLATFORM, "azure_vm"),
        ];
        
        match self.get_metadata().await {
            Ok(metadata) => {
                let compute = metadata.compute;
                
                // Region
                attrs.push(KeyValue::new(CLOUD_REGION, compute.location));
                
                // Subscription ID (Account ID)
                attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, compute.subscription_id));
                
                // VM ID
                attrs.push(KeyValue::new("host.id", compute.vm_id));
                
                // VM Name
                attrs.push(KeyValue::new("host.name", compute.name));
                
                // VM Size
                attrs.push(KeyValue::new("host.type", compute.vm_size));
                
                // Resource Group
                attrs.push(KeyValue::new("azure.resource_group", compute.resource_group_name));
                
                // Zone
                if let Some(zone) = compute.zone {
                    attrs.push(KeyValue::new("cloud.availability_zone", zone));
                }
                
                // Environment
                attrs.push(KeyValue::new("azure.environment", metadata.az_environment));
            }
            Err(e) => {
                tracing::warn!("Failed to get Azure VM metadata: {}", e);
            }
        }
        
        attrs
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let client = AzureVmMetadataClient::new();
    let attrs = client.detect_attributes().await;
    
    for attr in attrs {
        println!("{}: {}", attr.key, attr.value);
    }
    
    Ok(())
}
```

---

## 3. Azure Functions 属性

```rust
use opentelemetry_semantic_conventions::resource::{
    FAAS_NAME, FAAS_VERSION, FAAS_INSTANCE, FAAS_MAX_MEMORY,
};

/// Azure Functions 资源检测器
pub struct AzureFunctionsResourceDetector;

impl AzureFunctionsResourceDetector {
    /// 检测 Azure Functions 属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
            KeyValue::new(CLOUD_PLATFORM, "azure_functions"),
        ];
        
        // 函数应用名称
        if let Ok(site_name) = std::env::var("WEBSITE_SITE_NAME") {
            attrs.push(KeyValue::new(FAAS_NAME, site_name.clone()));
            attrs.push(KeyValue::new("azure.function_app.name", site_name));
        }
        
        // 函数名称
        if let Ok(func_name) = std::env::var("FUNCTIONS_EXTENSION_VERSION") {
            attrs.push(KeyValue::new(FAAS_VERSION, func_name));
        }
        
        // Worker Runtime
        if let Ok(runtime) = std::env::var("FUNCTIONS_WORKER_RUNTIME") {
            attrs.push(KeyValue::new("faas.runtime", runtime));
        }
        
        // Region
        if let Ok(region) = std::env::var("REGION_NAME") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        // 实例 ID
        if let Ok(instance_id) = std::env::var("WEBSITE_INSTANCE_ID") {
            attrs.push(KeyValue::new(FAAS_INSTANCE, instance_id));
        }
        
        // Resource Group
        if let Ok(resource_group) = std::env::var("WEBSITE_RESOURCE_GROUP") {
            attrs.push(KeyValue::new("azure.resource_group", resource_group));
        }
        
        // Owner Name (Subscription)
        if let Ok(owner) = std::env::var("WEBSITE_OWNER_NAME") {
            // Format: subscriptionId+resourceGroupName-region
            if let Some(subscription_id) = owner.split('+').next() {
                attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, subscription_id.to_string()));
            }
        }
        
        attrs
    }
}

/// Azure Functions 追踪包装器
pub async fn with_azure_function_tracing<F, T, E>(
    function_name: &str,
    handler: F,
) -> Result<T, E>
where
    F: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    use opentelemetry::{global, trace::{Tracer, SpanKind, TraceContextExt}};
    
    let tracer = global::tracer("azure-functions");
    let mut span = tracer
        .span_builder(function_name)
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 添加 Azure Functions 特定属性
    if let Ok(invocation_id) = std::env::var("FUNCTIONS_INVOCATION_ID") {
        span.set_attribute(KeyValue::new("azure.invocation.id", invocation_id));
    }
    
    let cx = opentelemetry::Context::current_with_span(span.clone());
    let _guard = cx.attach();
    
    let result = handler.await;
    
    match &result {
        Ok(_) => {
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err(e) => {
            span.set_status(opentelemetry::trace::Status::error(e.to_string()));
        }
    }
    
    span.end();
    result
}
```

---

## 4. Azure App Service 属性

```rust
/// Azure App Service 资源检测器
pub struct AzureAppServiceResourceDetector;

impl AzureAppServiceResourceDetector {
    /// 检测 App Service 属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
            KeyValue::new(CLOUD_PLATFORM, "azure_app_service"),
        ];
        
        // 站点名称
        if let Ok(site_name) = std::env::var("WEBSITE_SITE_NAME") {
            attrs.push(KeyValue::new("service.name", site_name.clone()));
            attrs.push(KeyValue::new("azure.app_service.name", site_name));
        }
        
        // 实例 ID
        if let Ok(instance_id) = std::env::var("WEBSITE_INSTANCE_ID") {
            attrs.push(KeyValue::new("service.instance.id", instance_id));
        }
        
        // Resource Group
        if let Ok(resource_group) = std::env::var("WEBSITE_RESOURCE_GROUP") {
            attrs.push(KeyValue::new("azure.resource_group", resource_group));
        }
        
        // Region
        if let Ok(region) = std::env::var("REGION_NAME") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        // Owner Name (Subscription)
        if let Ok(owner) = std::env::var("WEBSITE_OWNER_NAME") {
            if let Some(subscription_id) = owner.split('+').next() {
                attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, subscription_id.to_string()));
            }
        }
        
        // Runtime
        if let Ok(runtime_version) = std::env::var("WEBSITE_NODE_DEFAULT_VERSION") {
            attrs.push(KeyValue::new("azure.app_service.runtime", format!("Node.js {}", runtime_version)));
        }
        
        // SKU
        if let Ok(sku) = std::env::var("WEBSITE_SKU") {
            attrs.push(KeyValue::new("azure.app_service.sku", sku));
        }
        
        attrs
    }
}
```

---

## 5. Azure Container Instances

```rust
/// Azure Container Instances 资源检测器
pub struct AzureContainerInstancesResourceDetector;

impl AzureContainerInstancesResourceDetector {
    /// 检测 ACI 属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
            KeyValue::new(CLOUD_PLATFORM, "azure_container_instances"),
        ];
        
        // Resource Group
        if let Ok(resource_group) = std::env::var("ACI_RESOURCE_GROUP") {
            attrs.push(KeyValue::new("azure.resource_group", resource_group));
        }
        
        // Container Group Name
        if let Ok(container_group) = std::env::var("ACI_CONTAINER_GROUP_NAME") {
            attrs.push(KeyValue::new("azure.container_group", container_group));
        }
        
        // Region
        if let Ok(region) = std::env::var("ACI_REGION") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        attrs
    }
}
```

---

## 6. Azure Kubernetes Service (AKS)

```rust
/// AKS 资源检测器
pub struct AksResourceDetector;

impl AksResourceDetector {
    /// 检测 AKS 集群属性
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
            KeyValue::new(CLOUD_PLATFORM, "azure_kubernetes_service"),
        ];
        
        // Kubernetes 属性
        attrs.extend(Self::detect_k8s_attributes());
        
        // AKS 特定属性
        if let Ok(cluster_name) = std::env::var("AKS_CLUSTER_NAME") {
            attrs.push(KeyValue::new("azure.aks.cluster.name", cluster_name));
        }
        
        // Resource Group
        if let Ok(resource_group) = std::env::var("AKS_RESOURCE_GROUP") {
            attrs.push(KeyValue::new("azure.resource_group", resource_group));
        }
        
        // Region (从 VM metadata)
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
        let client = AzureVmMetadataClient::new();
        let metadata = client.get_metadata().await?;
        Ok(metadata.compute.location)
    }
}
```

---

## 7. Application Insights 集成

```rust
use azure_core::auth::TokenCredential;
use azure_identity::DefaultAzureCredential;

/// Application Insights 导出器配置
pub struct ApplicationInsightsConfig {
    pub instrumentation_key: String,
    pub connection_string: Option<String>,
}

impl ApplicationInsightsConfig {
    pub fn from_env() -> anyhow::Result<Self> {
        let instrumentation_key = std::env::var("APPLICATIONINSIGHTS_INSTRUMENTATION_KEY")
            .or_else(|_| std::env::var("APPINSIGHTS_INSTRUMENTATIONKEY"))?;
        
        let connection_string = std::env::var("APPLICATIONINSIGHTS_CONNECTION_STRING")
            .or_else(|_| std::env::var("APPINSIGHTS_CONNECTIONSTRING"))
            .ok();
        
        Ok(Self {
            instrumentation_key,
            connection_string,
        })
    }
}

/// Application Insights 追踪导出器
pub struct ApplicationInsightsExporter {
    config: ApplicationInsightsConfig,
    client: Client,
}

impl ApplicationInsightsExporter {
    pub fn new(config: ApplicationInsightsConfig) -> Self {
        Self {
            config,
            client: Client::new(),
        }
    }
    
    /// 发送追踪数据到 Application Insights
    pub async fn export_trace(&self, span: &opentelemetry::trace::SpanData) -> anyhow::Result<()> {
        // 构建 Application Insights telemetry envelope
        let telemetry = self.build_telemetry_envelope(span);
        
        // 发送到 Application Insights
        let endpoint = "https://dc.services.visualstudio.com/v2/track";
        
        self.client
            .post(endpoint)
            .json(&telemetry)
            .send()
            .await?;
        
        Ok(())
    }
    
    fn build_telemetry_envelope(&self, span: &opentelemetry::trace::SpanData) -> serde_json::Value {
        // 简化示例，实际需要完整的 Application Insights 格式
        serde_json::json!({
            "name": "Microsoft.ApplicationInsights.Request",
            "time": span.start_time,
            "iKey": self.config.instrumentation_key,
            "data": {
                "baseType": "RequestData",
                "baseData": {
                    "name": span.name,
                    "duration": span.end_time - span.start_time,
                    "responseCode": "200",
                    "success": true,
                }
            }
        })
    }
}
```

---

## 8. 完整示例

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{Resource, trace::TracerProvider};
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 检测 Azure 资源
    let azure_resource = AzureResourceDetector::detect().await;
    
    // 2. 合并服务资源
    let service_resource = Resource::new(vec![
        KeyValue::new("service.name", "my-azure-service"),
        KeyValue::new("service.version", "1.0.0"),
    ]);
    
    let resource = service_resource.merge(&azure_resource);
    
    // 3. 初始化 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_resource(resource)
        .with_simple_exporter(opentelemetry_stdout::SpanExporter::default())
        .build();
    
    global::set_tracer_provider(tracer_provider);
    
    // 4. 创建 tracer
    let tracer = global::tracer("azure-service");
    
    // 5. 创建 span
    let span = tracer.start("process_request");
    let cx = opentelemetry::Context::current_with_span(span);
    let _guard = cx.attach();
    
    // 业务逻辑
    println!("Processing request in Azure...");
    
    Ok(())
}

/// 完整的 Azure 资源检测器
pub struct AzureResourceDetector;

impl AzureResourceDetector {
    /// 自动检测并构建 Azure 资源
    pub async fn detect() -> Resource {
        let platform = AzurePlatform::detect();
        
        let attrs = match platform {
            Some(AzurePlatform::Functions) => {
                AzureFunctionsResourceDetector::detect()
            }
            Some(AzurePlatform::AppService) => {
                AzureAppServiceResourceDetector::detect()
            }
            Some(AzurePlatform::ContainerInstances) => {
                AzureContainerInstancesResourceDetector::detect()
            }
            Some(AzurePlatform::KubernetesService) => {
                AksResourceDetector::detect().await
            }
            Some(AzurePlatform::VirtualMachine) => {
                let client = AzureVmMetadataClient::new();
                client.detect_attributes().await
            }
            _ => {
                vec![KeyValue::new(CLOUD_PROVIDER, "azure")]
            }
        };
        
        Resource::new(attrs)
    }
}
```

---

## 9. 最佳实践

### 9.1 环境变量配置

```bash
# Azure Functions
export WEBSITE_SITE_NAME="my-function-app"
export FUNCTIONS_WORKER_RUNTIME="custom"
export APPLICATIONINSIGHTS_CONNECTION_STRING="InstrumentationKey=..."

# Azure App Service
export WEBSITE_SITE_NAME="my-web-app"
export WEBSITE_RESOURCE_GROUP="my-rg"
export REGION_NAME="eastus"

# AKS
export K8S_POD_NAME="${POD_NAME}"
export K8S_NAMESPACE_NAME="${POD_NAMESPACE}"
export K8S_NODE_NAME="${NODE_NAME}"
```

### 9.2 Managed Identity

```rust
use azure_identity::DefaultAzureCredential;

/// 使用 Managed Identity 进行认证
pub async fn get_credential() -> anyhow::Result<DefaultAzureCredential> {
    let credential = DefaultAzureCredential::default();
    Ok(credential)
}
```

### 9.3 Cargo.toml 配置

```toml
[dependencies]
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"

# Azure SDK
azure-core = "0.20"
azure-identity = "0.20"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
```

---

## 总结

本文档提供了完整的 Azure 平台 OpenTelemetry 集成方案：

1. **Azure VM**: Instance Metadata Service 检测
2. **Azure Functions**: 函数属性和追踪包装
3. **App Service**: Web 应用属性检测
4. **Container Instances**: ACI 属性检测
5. **AKS**: Kubernetes + Azure 组合
6. **Application Insights**: 追踪和指标导出

所有实现都基于 **Rust 1.90**、**async/await** 和最新的 Azure SDK。

**下一步**: 查看 [GCP 属性](03_GCP属性详解_Rust完整版.md) 和 [多云平台集成](../../10_云平台集成/)。
