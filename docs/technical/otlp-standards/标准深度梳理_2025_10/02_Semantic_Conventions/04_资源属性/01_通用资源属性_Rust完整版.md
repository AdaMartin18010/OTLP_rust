# 通用资源属性 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [通用资源属性 - Rust 完整实现](#通用资源属性---rust-完整实现)
  - [目录](#目录)
  - [1. 资源属性概述](#1-资源属性概述)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 资源属性分类](#12-资源属性分类)
  - [2. 服务资源属性](#2-服务资源属性)
    - [2.1 服务标识](#21-服务标识)
    - [2.2 服务实例](#22-服务实例)
  - [3. 部署环境属性](#3-部署环境属性)
  - [4. 主机和操作系统属性](#4-主机和操作系统属性)
  - [5. 容器和 Kubernetes 属性](#5-容器和-kubernetes-属性)
  - [6. 云平台属性](#6-云平台属性)
    - [6.1 AWS 属性](#61-aws-属性)
    - [6.2 Azure 属性](#62-azure-属性)
    - [6.3 GCP 属性](#63-gcp-属性)
  - [7. 完整资源构建器](#7-完整资源构建器)
  - [8. 自动检测](#8-自动检测)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 使用环境变量](#91-使用环境变量)
    - [9.2 资源合并优先级](#92-资源合并优先级)
    - [9.3 Cargo.toml 配置](#93-cargotoml-配置)
  - [总结](#总结)

---

## 1. 资源属性概述

### 1.1 核心概念

Resource 表示产生遥测数据的实体，包含一组描述该实体的属性。

```rust
use opentelemetry::{KeyValue, Resource};
use opentelemetry_sdk::resource::{
    EnvResourceDetector, OsResourceDetector, ProcessResourceDetector,
    SdkProvidedResourceDetector, TelemetryResourceDetector,
};
use opentelemetry_semantic_conventions::resource::{
    SERVICE_NAME, SERVICE_VERSION, SERVICE_INSTANCE_ID,
    DEPLOYMENT_ENVIRONMENT, HOST_NAME, HOST_ARCH,
    OS_TYPE, OS_DESCRIPTION, PROCESS_PID, PROCESS_EXECUTABLE_NAME,
};

/// 资源属性构建器
#[derive(Debug, Clone, Default)]
pub struct ResourceBuilder {
    attributes: Vec<KeyValue>,
}

impl ResourceBuilder {
    pub fn new() -> Self {
        Self::default()
    }
    
    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
    
    /// 批量添加属性
    pub fn with_attributes(mut self, attrs: Vec<KeyValue>) -> Self {
        self.attributes.extend(attrs);
        self
    }
    
    /// 构建 Resource
    pub fn build(self) -> Resource {
        Resource::new(self.attributes)
    }
}
```

### 1.2 资源属性分类

```rust
/// 资源属性类别
#[derive(Debug, Clone, Copy)]
pub enum ResourceCategory {
    /// 服务属性
    Service,
    /// 部署环境
    Deployment,
    /// 主机信息
    Host,
    /// 操作系统
    Os,
    /// 进程信息
    Process,
    /// 容器信息
    Container,
    /// Kubernetes
    K8s,
    /// 云平台
    Cloud,
}

impl ResourceCategory {
    pub fn prefix(&self) -> &'static str {
        match self {
            Self::Service => "service.",
            Self::Deployment => "deployment.",
            Self::Host => "host.",
            Self::Os => "os.",
            Self::Process => "process.",
            Self::Container => "container.",
            Self::K8s => "k8s.",
            Self::Cloud => "cloud.",
        }
    }
}
```

---

## 2. 服务资源属性

### 2.1 服务标识

```rust
use opentelemetry_semantic_conventions::resource::{
    SERVICE_NAME,
    SERVICE_VERSION,
    SERVICE_NAMESPACE,
};
use uuid::Uuid;

/// 服务资源构建器
#[derive(Debug, Clone)]
pub struct ServiceResource {
    name: String,
    version: Option<String>,
    namespace: Option<String>,
    instance_id: Option<String>,
}

impl ServiceResource {
    /// 创建新的服务资源
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            namespace: None,
            instance_id: None,
        }
    }
    
    /// 设置版本
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }
    
    /// 设置命名空间
    pub fn with_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.namespace = Some(namespace.into());
        self
    }
    
    /// 设置实例 ID
    pub fn with_instance_id(mut self, instance_id: impl Into<String>) -> Self {
        self.instance_id = Some(instance_id.into());
        self
    }
    
    /// 自动生成实例 ID
    pub fn with_auto_instance_id(mut self) -> Self {
        self.instance_id = Some(Uuid::new_v4().to_string());
        self
    }
    
    /// 构建属性
    pub fn build(self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(SERVICE_NAME, self.name),
        ];
        
        if let Some(version) = self.version {
            attrs.push(KeyValue::new(SERVICE_VERSION, version));
        }
        if let Some(namespace) = self.namespace {
            attrs.push(KeyValue::new(SERVICE_NAMESPACE, namespace));
        }
        if let Some(instance_id) = self.instance_id {
            attrs.push(KeyValue::new(SERVICE_INSTANCE_ID, instance_id));
        }
        
        attrs
    }
}

/// 使用示例
fn create_service_resource() -> Resource {
    let service = ServiceResource::new("my-service")
        .with_version("1.2.3")
        .with_namespace("production")
        .with_auto_instance_id()
        .build();
    
    Resource::new(service)
}
```

### 2.2 服务实例

```rust
use std::sync::OnceLock;

/// 全局服务实例 ID
static SERVICE_INSTANCE_ID: OnceLock<String> = OnceLock::new();

/// 获取或生成服务实例 ID
pub fn get_service_instance_id() -> &'static str {
    SERVICE_INSTANCE_ID.get_or_init(|| {
        // 优先使用环境变量
        std::env::var("SERVICE_INSTANCE_ID")
            .unwrap_or_else(|_| {
                // 使用主机名 + PID
                let hostname = hostname::get()
                    .ok()
                    .and_then(|h| h.into_string().ok())
                    .unwrap_or_else(|| "unknown".to_string());
                
                let pid = std::process::id();
                format!("{}:{}", hostname, pid)
            })
    })
}
```

---

## 3. 部署环境属性

```rust
use opentelemetry_semantic_conventions::resource::DEPLOYMENT_ENVIRONMENT;

/// 部署环境
#[derive(Debug, Clone, Copy)]
pub enum DeploymentEnvironment {
    Development,
    Staging,
    Production,
    Test,
}

impl DeploymentEnvironment {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Development => "development",
            Self::Staging => "staging",
            Self::Production => "production",
            Self::Test => "test",
        }
    }
    
    /// 从环境变量检测
    pub fn detect() -> Self {
        match std::env::var("DEPLOYMENT_ENVIRONMENT")
            .or_else(|_| std::env::var("ENV"))
            .or_else(|_| std::env::var("ENVIRONMENT"))
            .as_deref()
        {
            Ok("production") | Ok("prod") => Self::Production,
            Ok("staging") | Ok("stage") => Self::Staging,
            Ok("test") | Ok("testing") => Self::Test,
            Ok("development") | Ok("dev") | _ => Self::Development,
        }
    }
    
    /// 构建属性
    pub fn to_attribute(self) -> KeyValue {
        KeyValue::new(DEPLOYMENT_ENVIRONMENT, self.as_str().to_string())
    }
}
```

---

## 4. 主机和操作系统属性

```rust
use opentelemetry_semantic_conventions::resource::{
    HOST_NAME, HOST_ARCH, HOST_TYPE,
    OS_TYPE, OS_DESCRIPTION, OS_VERSION,
};
use std::env::consts::{ARCH, OS};

/// 主机资源检测器
pub struct HostResourceDetector;

impl HostResourceDetector {
    /// 检测主机属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        // 主机名
        if let Ok(hostname) = hostname::get() {
            if let Ok(hostname_str) = hostname.into_string() {
                attrs.push(KeyValue::new(HOST_NAME, hostname_str));
            }
        }
        
        // 架构
        attrs.push(KeyValue::new(HOST_ARCH, ARCH.to_string()));
        
        // 操作系统类型
        attrs.push(KeyValue::new(OS_TYPE, OS.to_string()));
        
        // 操作系统版本
        if let Ok(version) = sys_info::os_release() {
            attrs.push(KeyValue::new(OS_VERSION, version));
        }
        
        // 操作系统描述
        if let Ok(desc) = sys_info::os_type() {
            attrs.push(KeyValue::new(OS_DESCRIPTION, desc));
        }
        
        attrs
    }
}

/// 使用示例
fn create_host_resource() -> Resource {
    let attrs = HostResourceDetector::detect();
    Resource::new(attrs)
}
```

---

## 5. 容器和 Kubernetes 属性

```rust
use opentelemetry_semantic_conventions::resource::{
    CONTAINER_ID, CONTAINER_NAME, CONTAINER_IMAGE_NAME,
    K8S_NAMESPACE_NAME, K8S_POD_NAME, K8S_DEPLOYMENT_NAME,
    K8S_NODE_NAME, K8S_CLUSTER_NAME,
};
use std::fs;

/// 容器资源检测器
pub struct ContainerResourceDetector;

impl ContainerResourceDetector {
    /// 检测容器 ID
    pub fn detect_container_id() -> Option<String> {
        // 从 cgroup 文件读取容器 ID
        if let Ok(content) = fs::read_to_string("/proc/self/cgroup") {
            for line in content.lines() {
                if let Some(id) = Self::extract_container_id(line) {
                    return Some(id);
                }
            }
        }
        None
    }
    
    fn extract_container_id(line: &str) -> Option<String> {
        // Docker: 12:pids:/docker/abc123...
        if let Some(idx) = line.find("/docker/") {
            let id = &line[idx + 8..];
            return Some(id.to_string());
        }
        
        // Kubernetes: 12:pids:/kubepods/pod.../abc123...
        if let Some(idx) = line.rfind('/') {
            let id = &line[idx + 1..];
            if !id.is_empty() {
                return Some(id.to_string());
            }
        }
        
        None
    }
}

/// Kubernetes 资源检测器
pub struct K8sResourceDetector;

impl K8sResourceDetector {
    /// 从环境变量检测 K8s 属性
    pub fn detect() -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        // Pod 名称
        if let Ok(pod_name) = std::env::var("K8S_POD_NAME") {
            attrs.push(KeyValue::new(K8S_POD_NAME, pod_name));
        }
        
        // 命名空间
        if let Ok(namespace) = std::env::var("K8S_NAMESPACE_NAME") {
            attrs.push(KeyValue::new(K8S_NAMESPACE_NAME, namespace));
        }
        
        // Deployment 名称
        if let Ok(deployment) = std::env::var("K8S_DEPLOYMENT_NAME") {
            attrs.push(KeyValue::new(K8S_DEPLOYMENT_NAME, deployment));
        }
        
        // Node 名称
        if let Ok(node) = std::env::var("K8S_NODE_NAME") {
            attrs.push(KeyValue::new(K8S_NODE_NAME, node));
        }
        
        // Cluster 名称
        if let Ok(cluster) = std::env::var("K8S_CLUSTER_NAME") {
            attrs.push(KeyValue::new(K8S_CLUSTER_NAME, cluster));
        }
        
        // 容器 ID
        if let Some(container_id) = ContainerResourceDetector::detect_container_id() {
            attrs.push(KeyValue::new(CONTAINER_ID, container_id));
        }
        
        attrs
    }
}
```

---

## 6. 云平台属性

### 6.1 AWS 属性

```rust
use opentelemetry_semantic_conventions::resource::{
    CLOUD_PROVIDER, CLOUD_PLATFORM, CLOUD_REGION,
    CLOUD_ACCOUNT_ID, CLOUD_AVAILABILITY_ZONE,
};

/// AWS 资源检测器
pub struct AwsResourceDetector;

impl AwsResourceDetector {
    /// 从 EC2 metadata 检测
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "aws"),
        ];
        
        // 检测平台类型
        if Self::is_lambda() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_lambda"));
            attrs.extend(Self::detect_lambda().await);
        } else if Self::is_ecs() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_ecs"));
            attrs.extend(Self::detect_ecs().await);
        } else if Self::is_eks() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_eks"));
            attrs.extend(Self::detect_eks().await);
        } else {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "aws_ec2"));
            attrs.extend(Self::detect_ec2().await);
        }
        
        attrs
    }
    
    fn is_lambda() -> bool {
        std::env::var("AWS_LAMBDA_FUNCTION_NAME").is_ok()
    }
    
    fn is_ecs() -> bool {
        std::env::var("ECS_CONTAINER_METADATA_URI").is_ok()
            || std::env::var("ECS_CONTAINER_METADATA_URI_V4").is_ok()
    }
    
    fn is_eks() -> bool {
        std::env::var("KUBERNETES_SERVICE_HOST").is_ok()
            && std::path::Path::new("/var/run/secrets/kubernetes.io").exists()
    }
    
    async fn detect_lambda() -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Ok(func_name) = std::env::var("AWS_LAMBDA_FUNCTION_NAME") {
            attrs.push(KeyValue::new("faas.name", func_name));
        }
        if let Ok(func_version) = std::env::var("AWS_LAMBDA_FUNCTION_VERSION") {
            attrs.push(KeyValue::new("faas.version", func_version));
        }
        if let Ok(region) = std::env::var("AWS_REGION") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        attrs
    }
    
    async fn detect_ecs() -> Vec<KeyValue> {
        // 从 ECS metadata API 获取信息
        Vec::new()
    }
    
    async fn detect_eks() -> Vec<KeyValue> {
        // 结合 K8s 和 AWS 信息
        Vec::new()
    }
    
    async fn detect_ec2() -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        // 从 EC2 metadata service 获取信息
        let client = reqwest::Client::new();
        let base_url = "http://169.254.169.254/latest/meta-data";
        
        // Region
        if let Ok(resp) = client
            .get(format!("{}/placement/region", base_url))
            .timeout(std::time::Duration::from_secs(1))
            .send()
            .await
        {
            if let Ok(region) = resp.text().await {
                attrs.push(KeyValue::new(CLOUD_REGION, region));
            }
        }
        
        // Availability Zone
        if let Ok(resp) = client
            .get(format!("{}/placement/availability-zone", base_url))
            .send()
            .await
        {
            if let Ok(az) = resp.text().await {
                attrs.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, az));
            }
        }
        
        // Instance ID
        if let Ok(resp) = client
            .get(format!("{}/instance-id", base_url))
            .send()
            .await
        {
            if let Ok(instance_id) = resp.text().await {
                attrs.push(KeyValue::new("host.id", instance_id));
            }
        }
        
        attrs
    }
}
```

### 6.2 Azure 属性

```rust
/// Azure 资源检测器
pub struct AzureResourceDetector;

impl AzureResourceDetector {
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "azure"),
        ];
        
        // 检测 Azure Functions
        if let Ok(func_name) = std::env::var("FUNCTIONS_WORKER_RUNTIME") {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "azure_functions"));
        }
        // 检测 Azure App Service
        else if std::env::var("WEBSITE_SITE_NAME").is_ok() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "azure_app_service"));
        }
        // 检测 Azure Container Instances
        else if std::env::var("ACI_RESOURCE_GROUP").is_ok() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "azure_container_instances"));
        }
        // 默认为 Azure VM
        else {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "azure_vm"));
        }
        
        // Region
        if let Ok(region) = std::env::var("REGION_NAME") {
            attrs.push(KeyValue::new(CLOUD_REGION, region));
        }
        
        attrs
    }
}
```

### 6.3 GCP 属性

```rust
/// GCP 资源检测器
pub struct GcpResourceDetector;

impl GcpResourceDetector {
    pub async fn detect() -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(CLOUD_PROVIDER, "gcp"),
        ];
        
        // 检测 Cloud Functions
        if std::env::var("FUNCTION_TARGET").is_ok() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "gcp_cloud_functions"));
        }
        // 检测 Cloud Run
        else if std::env::var("K_SERVICE").is_ok() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "gcp_cloud_run"));
        }
        // 检测 GKE
        else if std::env::var("KUBERNETES_SERVICE_HOST").is_ok() {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "gcp_kubernetes_engine"));
        }
        // 默认为 Compute Engine
        else {
            attrs.push(KeyValue::new(CLOUD_PLATFORM, "gcp_compute_engine"));
        }
        
        // 从 GCP metadata server 获取信息
        Self::fetch_metadata(&mut attrs).await;
        
        attrs
    }
    
    async fn fetch_metadata(attrs: &mut Vec<KeyValue>) {
        let client = reqwest::Client::new();
        let base_url = "http://metadata.google.internal/computeMetadata/v1";
        
        // Project ID
        if let Ok(resp) = client
            .get(format!("{}/project/project-id", base_url))
            .header("Metadata-Flavor", "Google")
            .send()
            .await
        {
            if let Ok(project_id) = resp.text().await {
                attrs.push(KeyValue::new(CLOUD_ACCOUNT_ID, project_id));
            }
        }
        
        // Region/Zone
        if let Ok(resp) = client
            .get(format!("{}/instance/zone", base_url))
            .header("Metadata-Flavor", "Google")
            .send()
            .await
        {
            if let Ok(zone) = resp.text().await {
                // Zone format: projects/123/zones/us-central1-a
                if let Some(region) = zone.rsplit('/').next() {
                    attrs.push(KeyValue::new(CLOUD_AVAILABILITY_ZONE, region.to_string()));
                }
            }
        }
    }
}
```

---

## 7. 完整资源构建器

```rust
use opentelemetry::Resource;
use opentelemetry_sdk::resource::{ResourceDetector, SdkProvidedResourceDetector};

/// 全功能资源构建器
pub struct ComprehensiveResourceBuilder {
    service: ServiceResource,
    environment: Option<DeploymentEnvironment>,
    enable_host_detection: bool,
    enable_cloud_detection: bool,
    enable_k8s_detection: bool,
    custom_attributes: Vec<KeyValue>,
}

impl ComprehensiveResourceBuilder {
    pub fn new(service_name: impl Into<String>) -> Self {
        Self {
            service: ServiceResource::new(service_name),
            environment: None,
            enable_host_detection: true,
            enable_cloud_detection: true,
            enable_k8s_detection: true,
            custom_attributes: Vec::new(),
        }
    }
    
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.service = self.service.with_version(version);
        self
    }
    
    pub fn with_environment(mut self, env: DeploymentEnvironment) -> Self {
        self.environment = Some(env);
        self
    }
    
    pub fn with_custom_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.custom_attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
    
    pub fn disable_host_detection(mut self) -> Self {
        self.enable_host_detection = false;
        self
    }
    
    pub fn disable_cloud_detection(mut self) -> Self {
        self.enable_cloud_detection = false;
        self
    }
    
    /// 异步构建完整资源
    pub async fn build(self) -> Resource {
        let mut all_attrs = Vec::new();
        
        // 服务属性
        all_attrs.extend(self.service.build());
        
        // 环境属性
        if let Some(env) = self.environment {
            all_attrs.push(env.to_attribute());
        } else {
            all_attrs.push(DeploymentEnvironment::detect().to_attribute());
        }
        
        // 主机属性
        if self.enable_host_detection {
            all_attrs.extend(HostResourceDetector::detect());
        }
        
        // K8s 属性
        if self.enable_k8s_detection {
            all_attrs.extend(K8sResourceDetector::detect());
        }
        
        // 云平台属性
        if self.enable_cloud_detection {
            // 检测云平台
            if AwsResourceDetector::is_lambda() || AwsResourceDetector::is_ecs() {
                all_attrs.extend(AwsResourceDetector::detect().await);
            } else if std::env::var("FUNCTIONS_WORKER_RUNTIME").is_ok() {
                all_attrs.extend(AzureResourceDetector::detect().await);
            } else if std::env::var("GOOGLE_CLOUD_PROJECT").is_ok() {
                all_attrs.extend(GcpResourceDetector::detect().await);
            }
        }
        
        // 自定义属性
        all_attrs.extend(self.custom_attributes);
        
        Resource::new(all_attrs)
    }
    
    /// 同步构建 (不包含云平台检测)
    pub fn build_sync(self) -> Resource {
        let mut all_attrs = Vec::new();
        
        all_attrs.extend(self.service.build());
        
        if let Some(env) = self.environment {
            all_attrs.push(env.to_attribute());
        }
        
        if self.enable_host_detection {
            all_attrs.extend(HostResourceDetector::detect());
        }
        
        if self.enable_k8s_detection {
            all_attrs.extend(K8sResourceDetector::detect());
        }
        
        all_attrs.extend(self.custom_attributes);
        
        Resource::new(all_attrs)
    }
}

/// 使用示例
#[tokio::main]
async fn main() {
    let resource = ComprehensiveResourceBuilder::new("my-service")
        .with_version("1.0.0")
        .with_environment(DeploymentEnvironment::Production)
        .with_custom_attribute("team", "backend")
        .with_custom_attribute("component", "api")
        .build()
        .await;
    
    println!("Resource attributes: {:?}", resource);
}
```

---

## 8. 自动检测

```rust
use opentelemetry_sdk::resource::{
    EnvResourceDetector, OsResourceDetector, ProcessResourceDetector,
};

/// 使用 SDK 内置检测器
pub fn create_auto_detected_resource(service_name: &str) -> Resource {
    // 合并多个检测器
    let env_detector = EnvResourceDetector::new();
    let os_detector = OsResourceDetector;
    let process_detector = ProcessResourceDetector;
    
    // 创建基础 resource
    let base_resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, service_name.to_string()),
    ]);
    
    // 检测并合并
    let env_resource = env_detector.detect(std::time::Duration::from_secs(1));
    let os_resource = os_detector.detect(std::time::Duration::from_secs(1));
    let process_resource = process_detector.detect(std::time::Duration::from_secs(1));
    
    base_resource
        .merge(&env_resource)
        .merge(&os_resource)
        .merge(&process_resource)
}
```

---

## 9. 最佳实践

### 9.1 使用环境变量

```bash
# 设置服务信息
export OTEL_SERVICE_NAME="my-service"
export OTEL_SERVICE_VERSION="1.0.0"
export OTEL_RESOURCE_ATTRIBUTES="deployment.environment=production,team=backend"

# Kubernetes 环境
export K8S_POD_NAME="${POD_NAME}"
export K8S_NAMESPACE_NAME="${POD_NAMESPACE}"
export K8S_NODE_NAME="${NODE_NAME}"
```

### 9.2 资源合并优先级

```rust
/// 资源属性按优先级合并
pub fn merge_resources_with_priority(resources: Vec<Resource>) -> Resource {
    resources.into_iter().fold(Resource::empty(), |acc, res| {
        // 后面的 resource 会覆盖前面的相同键
        acc.merge(&res)
    })
}
```

### 9.3 Cargo.toml 配置

```toml
[dependencies]
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"

# 系统信息
hostname = "0.4"
sys-info = "0.9"

# HTTP 客户端 (用于云平台 metadata)
reqwest = { version = "0.12", features = ["json"] }

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具
uuid = { version = "1.11", features = ["v4"] }
```

---

## 总结

本文档提供了完整的 Rust 资源属性检测和构建方案：

1. **服务属性**: 名称、版本、实例 ID
2. **部署环境**: 自动检测和手动设置
3. **主机/OS**: 系统信息自动检测
4. **容器/K8s**: 容器 ID 和 Kubernetes 属性
5. **云平台**: AWS、Azure、GCP 自动检测
6. **完整构建器**: 灵活的链式 API

所有实现都基于 **Rust 1.90** 和 **OpenTelemetry 0.31.0**，支持同步和异步检测。

**下一步**: 查看 [云平台集成](../../10_云平台集成/) 和 [Kubernetes 部署](../../19_容器化与Kubernetes/)。
