# Resource 详解 - Rust 完整版

## 目录

- [Resource 详解 - Rust 完整版](#resource-详解---rust-完整版)
  - [目录](#目录)
  - [1. Resource 概述](#1-resource-概述)
    - [1.1 什么是 Resource](#11-什么是-resource)
    - [1.2 Resource 作用](#12-resource-作用)
  - [2. Resource 数据结构](#2-resource-数据结构)
    - [2.1 核心结构](#21-核心结构)
    - [2.2 标准属性](#22-标准属性)
  - [3. Resource 配置](#3-resource-配置)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 环境变量配置](#32-环境变量配置)
    - [3.3 自动检测](#33-自动检测)
  - [4. 语义约定](#4-语义约定)
    - [4.1 Service 属性](#41-service-属性)
    - [4.2 部署环境属性](#42-部署环境属性)
    - [4.3 主机属性](#43-主机属性)
    - [4.4 容器属性](#44-容器属性)
    - [4.5 Kubernetes 属性](#45-kubernetes-属性)
  - [5. 云平台集成](#5-云平台集成)
    - [5.1 AWS 资源检测](#51-aws-资源检测)
    - [5.2 GCP 资源检测](#52-gcp-资源检测)
    - [5.3 Azure 资源检测](#53-azure-资源检测)
  - [6. 容器环境](#6-容器环境)
    - [6.1 Docker 资源](#61-docker-资源)
    - [6.2 Kubernetes 资源](#62-kubernetes-资源)
  - [7. Resource Detector](#7-resource-detector)
    - [7.1 自定义 Detector](#71-自定义-detector)
    - [7.2 Detector 链](#72-detector-链)
  - [8. Resource 合并](#8-resource-合并)
    - [8.1 合并策略](#81-合并策略)
    - [8.2 优先级](#82-优先级)
  - [9. 完整示例](#9-完整示例)
    - [9.1 本地开发环境](#91-本地开发环境)
    - [9.2 Kubernetes 部署](#92-kubernetes-部署)
    - [9.3 AWS Lambda](#93-aws-lambda)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 必需属性](#101-必需属性)
    - [10.2 命名规范](#102-命名规范)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Resource 属性分类](#resource-属性分类)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Resource 概述

### 1.1 什么是 Resource

````text
Resource 定义:
- 描述遥测数据来源的实体
- 键值对集合，附加到所有 Telemetry 数据
- 不可变，在应用启动时设置

Resource 包含:
1. Service 信息 (service.name, service.version)
2. 部署环境 (deployment.environment)
3. 主机信息 (host.name, host.arch)
4. 容器信息 (container.id, container.name)
5. 云平台信息 (cloud.provider, cloud.region)
6. Kubernetes 信息 (k8s.pod.name, k8s.namespace.name)

示例:
service.name = "order-service"
service.version = "1.2.3"
deployment.environment = "production"
host.name = "server-01"
cloud.provider = "aws"
cloud.region = "us-west-2"
````

### 1.2 Resource 作用

````text
Resource 的作用:

1. 标识遥测数据来源
   - 哪个服务产生的数据
   - 哪个版本
   - 部署在哪里

2. 过滤和聚合
   - 按服务过滤 Trace
   - 按环境聚合 Metrics
   - 按区域分析 Logs

3. 关联多种遥测数据
   - 同一服务的 Trace + Metrics + Logs
   - 通过 Resource 关联

4. 自动化运维
   - 自动发现服务
   - 自动标记告警
   - 自动路由流量

示例查询:
- service.name="order-service" AND deployment.environment="production"
- host.name="server-01"
- k8s.namespace.name="default"
````

---

## 2. Resource 数据结构

### 2.1 核心结构

````rust
use opentelemetry::{KeyValue, sdk::Resource};
use opentelemetry_semantic_conventions as semconv;

/// Resource 是一个键值对集合
pub fn create_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new(semconv::resource::SERVICE_NAME, "order-service"),
        KeyValue::new(semconv::resource::SERVICE_VERSION, "1.2.3"),
        KeyValue::new(semconv::resource::DEPLOYMENT_ENVIRONMENT, "production"),
    ])
}

/// 创建完整的 Resource
pub fn create_full_resource() -> Resource {
    Resource::new(vec![
        // Service 信息
        KeyValue::new(semconv::resource::SERVICE_NAME, "order-service"),
        KeyValue::new(semconv::resource::SERVICE_VERSION, "1.2.3"),
        KeyValue::new(semconv::resource::SERVICE_NAMESPACE, "ecommerce"),
        KeyValue::new(semconv::resource::SERVICE_INSTANCE_ID, "instance-001"),
        
        // 部署环境
        KeyValue::new(semconv::resource::DEPLOYMENT_ENVIRONMENT, "production"),
        
        // 主机信息
        KeyValue::new(semconv::resource::HOST_NAME, "server-01"),
        KeyValue::new(semconv::resource::HOST_ARCH, "x86_64"),
        
        // 进程信息
        KeyValue::new(semconv::resource::PROCESS_PID, std::process::id().to_string()),
        KeyValue::new(semconv::resource::PROCESS_EXECUTABLE_NAME, "order-service"),
        
        // 语言运行时
        KeyValue::new(semconv::resource::TELEMETRY_SDK_NAME, "opentelemetry"),
        KeyValue::new(semconv::resource::TELEMETRY_SDK_LANGUAGE, "rust"),
        KeyValue::new(semconv::resource::TELEMETRY_SDK_VERSION, "0.31.0"),
    ])
}
````

### 2.2 标准属性

````rust
use opentelemetry_semantic_conventions::resource;

/// Resource 标准属性常量
pub mod resource_keys {
    // Service 信息
    pub const SERVICE_NAME: &str = resource::SERVICE_NAME;              // "order-service"
    pub const SERVICE_VERSION: &str = resource::SERVICE_VERSION;         // "1.2.3"
    pub const SERVICE_NAMESPACE: &str = resource::SERVICE_NAMESPACE;     // "ecommerce"
    pub const SERVICE_INSTANCE_ID: &str = resource::SERVICE_INSTANCE_ID; // "instance-001"
    
    // 部署环境
    pub const DEPLOYMENT_ENVIRONMENT: &str = resource::DEPLOYMENT_ENVIRONMENT; // "production"
    
    // 主机信息
    pub const HOST_NAME: &str = resource::HOST_NAME;                     // "server-01"
    pub const HOST_ARCH: &str = resource::HOST_ARCH;                     // "x86_64"
    pub const HOST_TYPE: &str = resource::HOST_TYPE;                     // "t3.medium"
    
    // 容器信息
    pub const CONTAINER_ID: &str = resource::CONTAINER_ID;               // "abc123"
    pub const CONTAINER_NAME: &str = resource::CONTAINER_NAME;           // "order-service-pod"
    pub const CONTAINER_IMAGE_NAME: &str = resource::CONTAINER_IMAGE_NAME; // "order-service"
    pub const CONTAINER_IMAGE_TAG: &str = resource::CONTAINER_IMAGE_TAG;   // "v1.2.3"
    
    // Kubernetes 信息
    pub const K8S_NAMESPACE_NAME: &str = resource::K8S_NAMESPACE_NAME;   // "default"
    pub const K8S_POD_NAME: &str = resource::K8S_POD_NAME;              // "order-service-pod-xyz"
    pub const K8S_DEPLOYMENT_NAME: &str = resource::K8S_DEPLOYMENT_NAME; // "order-service"
    pub const K8S_NODE_NAME: &str = resource::K8S_NODE_NAME;            // "node-01"
    
    // 云平台信息
    pub const CLOUD_PROVIDER: &str = resource::CLOUD_PROVIDER;           // "aws"
    pub const CLOUD_REGION: &str = resource::CLOUD_REGION;              // "us-west-2"
    pub const CLOUD_AVAILABILITY_ZONE: &str = resource::CLOUD_AVAILABILITY_ZONE; // "us-west-2a"
    pub const CLOUD_ACCOUNT_ID: &str = resource::CLOUD_ACCOUNT_ID;      // "123456789012"
}
````

---

## 3. Resource 配置

### 3.1 基础配置

````rust
use opentelemetry::{KeyValue, sdk::Resource};
use opentelemetry_semantic_conventions::resource;

/// 配置 Resource
pub fn init_otlp_with_resource() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, env!("CARGO_PKG_NAME")),
        KeyValue::new(resource::SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
        KeyValue::new(resource::DEPLOYMENT_ENVIRONMENT, get_environment()),
    ]);
    
    // 使用 Resource 初始化 TracerProvider
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource.clone())
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    Ok(())
}

fn get_environment() -> String {
    std::env::var("ENVIRONMENT").unwrap_or_else(|_| "development".to_string())
}
````

### 3.2 环境变量配置

````bash
# 环境变量配置 Resource
export OTEL_RESOURCE_ATTRIBUTES="service.name=order-service,service.version=1.2.3,deployment.environment=production"

# 或者分别设置
export OTEL_SERVICE_NAME="order-service"
export OTEL_SERVICE_VERSION="1.2.3"
export ENVIRONMENT="production"
````

````rust
use opentelemetry::sdk::Resource;

/// 从环境变量加载 Resource
pub fn load_resource_from_env() -> Resource {
    // OpenTelemetry SDK 自动从环境变量读取
    Resource::default()
        .merge(&Resource::from_detectors(
            std::time::Duration::from_secs(3),
            vec![
                Box::new(opentelemetry_sdk::resource::EnvResourceDetector::new()),
                Box::new(opentelemetry_sdk::resource::TelemetryResourceDetector::new()),
            ],
        ))
}
````

### 3.3 自动检测

````rust
use opentelemetry::sdk::Resource;
use opentelemetry_sdk::resource::{
    EnvResourceDetector,
    OsResourceDetector,
    ProcessResourceDetector,
    TelemetryResourceDetector,
};

/// 自动检测 Resource
pub fn detect_resource() -> Resource {
    let detectors: Vec<Box<dyn opentelemetry_sdk::resource::ResourceDetector>> = vec![
        // 环境变量检测
        Box::new(EnvResourceDetector::new()),
        
        // 操作系统检测
        Box::new(OsResourceDetector),
        
        // 进程信息检测
        Box::new(ProcessResourceDetector),
        
        // Telemetry SDK 信息
        Box::new(TelemetryResourceDetector::new()),
    ];
    
    Resource::from_detectors(
        std::time::Duration::from_secs(3),
        detectors,
    )
}
````

---

## 4. 语义约定

### 4.1 Service 属性

````rust
use opentelemetry::{KeyValue, sdk::Resource};
use opentelemetry_semantic_conventions::resource;

/// Service 信息
pub fn create_service_resource(
    name: &str,
    version: &str,
    namespace: Option<&str>,
) -> Resource {
    let mut attributes = vec![
        KeyValue::new(resource::SERVICE_NAME, name.to_string()),
        KeyValue::new(resource::SERVICE_VERSION, version.to_string()),
    ];
    
    if let Some(ns) = namespace {
        attributes.push(KeyValue::new(resource::SERVICE_NAMESPACE, ns.to_string()));
    }
    
    // Service Instance ID (唯一标识实例)
    let instance_id = format!("{}-{}", name, uuid::Uuid::new_v4());
    attributes.push(KeyValue::new(resource::SERVICE_INSTANCE_ID, instance_id));
    
    Resource::new(attributes)
}
````

### 4.2 部署环境属性

````rust
/// 部署环境
pub enum DeploymentEnvironment {
    Development,
    Staging,
    Production,
}

impl DeploymentEnvironment {
    pub fn as_str(&self) -> &str {
        match self {
            Self::Development => "development",
            Self::Staging => "staging",
            Self::Production => "production",
        }
    }
}

pub fn create_deployment_resource(env: DeploymentEnvironment) -> Resource {
    Resource::new(vec![
        KeyValue::new(resource::DEPLOYMENT_ENVIRONMENT, env.as_str()),
    ])
}
````

### 4.3 主机属性

````rust
use sysinfo::{System, SystemExt};

/// 主机信息
pub fn create_host_resource() -> Resource {
    let sys = System::new_all();
    
    Resource::new(vec![
        KeyValue::new(resource::HOST_NAME, sys.host_name().unwrap_or_default()),
        KeyValue::new(resource::HOST_ARCH, std::env::consts::ARCH),
        KeyValue::new(resource::HOST_TYPE, get_host_type()),
        KeyValue::new(resource::OS_TYPE, std::env::consts::OS),
        KeyValue::new(resource::OS_VERSION, sys.os_version().unwrap_or_default()),
    ])
}

fn get_host_type() -> String {
    // 从云平台 Metadata 获取实例类型
    std::env::var("INSTANCE_TYPE").unwrap_or_else(|_| "unknown".to_string())
}
````

### 4.4 容器属性

````rust
use std::fs;

/// 容器信息
pub fn create_container_resource() -> Resource {
    let mut attributes = Vec::new();
    
    // 从 /proc/self/cgroup 读取 Container ID
    if let Ok(cgroup) = fs::read_to_string("/proc/self/cgroup") {
        if let Some(container_id) = extract_container_id(&cgroup) {
            attributes.push(KeyValue::new(resource::CONTAINER_ID, container_id));
        }
    }
    
    // 从环境变量读取 Container 信息
    if let Ok(name) = std::env::var("CONTAINER_NAME") {
        attributes.push(KeyValue::new(resource::CONTAINER_NAME, name));
    }
    
    if let Ok(image) = std::env::var("CONTAINER_IMAGE") {
        if let Some((name, tag)) = image.split_once(':') {
            attributes.push(KeyValue::new(resource::CONTAINER_IMAGE_NAME, name));
            attributes.push(KeyValue::new(resource::CONTAINER_IMAGE_TAG, tag));
        }
    }
    
    Resource::new(attributes)
}

fn extract_container_id(cgroup: &str) -> Option<String> {
    // 提取 Docker Container ID
    for line in cgroup.lines() {
        if line.contains("docker") {
            if let Some(id) = line.split('/').last() {
                return Some(id.to_string());
            }
        }
    }
    None
}
````

### 4.5 Kubernetes 属性

````rust
use std::fs;

/// Kubernetes 信息
pub fn create_k8s_resource() -> Resource {
    let mut attributes = Vec::new();
    
    // 从环境变量读取 K8s 信息
    if let Ok(namespace) = std::env::var("K8S_NAMESPACE") {
        attributes.push(KeyValue::new(resource::K8S_NAMESPACE_NAME, namespace));
    }
    
    if let Ok(pod_name) = std::env::var("K8S_POD_NAME") {
        attributes.push(KeyValue::new(resource::K8S_POD_NAME, pod_name));
    }
    
    if let Ok(deployment) = std::env::var("K8S_DEPLOYMENT_NAME") {
        attributes.push(KeyValue::new(resource::K8S_DEPLOYMENT_NAME, deployment));
    }
    
    if let Ok(node) = std::env::var("K8S_NODE_NAME") {
        attributes.push(KeyValue::new(resource::K8S_NODE_NAME, node));
    }
    
    // 从 Downward API 读取 Pod UID
    if let Ok(uid) = fs::read_to_string("/etc/podinfo/uid") {
        attributes.push(KeyValue::new(resource::K8S_POD_UID, uid.trim()));
    }
    
    Resource::new(attributes)
}
````

---

## 5. 云平台集成

### 5.1 AWS 资源检测

````rust
use reqwest::Client;
use serde::Deserialize;

#[derive(Deserialize)]
struct AwsMetadata {
    #[serde(rename = "instanceId")]
    instance_id: String,
    #[serde(rename = "instanceType")]
    instance_type: String,
    region: String,
    #[serde(rename = "availabilityZone")]
    availability_zone: String,
}

/// 检测 AWS 资源
pub async fn detect_aws_resource() -> Result<Resource, Box<dyn std::error::Error>> {
    let client = Client::new();
    
    // AWS EC2 Metadata API
    let metadata: AwsMetadata = client
        .get("http://169.254.169.254/latest/dynamic/instance-identity/document")
        .timeout(std::time::Duration::from_secs(2))
        .send()
        .await?
        .json()
        .await?;
    
    Ok(Resource::new(vec![
        KeyValue::new(resource::CLOUD_PROVIDER, "aws"),
        KeyValue::new(resource::CLOUD_REGION, metadata.region),
        KeyValue::new(resource::CLOUD_AVAILABILITY_ZONE, metadata.availability_zone),
        KeyValue::new(resource::CLOUD_PLATFORM, "aws_ec2"),
        KeyValue::new(resource::HOST_ID, metadata.instance_id),
        KeyValue::new(resource::HOST_TYPE, metadata.instance_type),
    ]))
}
````

### 5.2 GCP 资源检测

````rust
/// 检测 GCP 资源
pub async fn detect_gcp_resource() -> Result<Resource, Box<dyn std::error::Error>> {
    let client = Client::new();
    
    // GCP Metadata API
    let project_id: String = client
        .get("http://metadata.google.internal/computeMetadata/v1/project/project-id")
        .header("Metadata-Flavor", "Google")
        .send()
        .await?
        .text()
        .await?;
    
    let zone: String = client
        .get("http://metadata.google.internal/computeMetadata/v1/instance/zone")
        .header("Metadata-Flavor", "Google")
        .send()
        .await?
        .text()
        .await?;
    
    // zone 格式: projects/PROJECT_NUM/zones/ZONE_NAME
    let region = zone
        .split('/')
        .last()
        .and_then(|z| z.rsplit_once('-').map(|(r, _)| r))
        .unwrap_or("");
    
    Ok(Resource::new(vec![
        KeyValue::new(resource::CLOUD_PROVIDER, "gcp"),
        KeyValue::new(resource::CLOUD_REGION, region),
        KeyValue::new(resource::CLOUD_AVAILABILITY_ZONE, zone),
        KeyValue::new(resource::CLOUD_PLATFORM, "gcp_compute_engine"),
        KeyValue::new(resource::CLOUD_ACCOUNT_ID, project_id),
    ]))
}
````

### 5.3 Azure 资源检测

````rust
#[derive(Deserialize)]
struct AzureMetadata {
    location: String,
    #[serde(rename = "vmId")]
    vm_id: String,
    #[serde(rename = "vmSize")]
    vm_size: String,
}

/// 检测 Azure 资源
pub async fn detect_azure_resource() -> Result<Resource, Box<dyn std::error::Error>> {
    let client = Client::new();
    
    // Azure Instance Metadata Service
    let metadata: AzureMetadata = client
        .get("http://169.254.169.254/metadata/instance/compute?api-version=2021-02-01")
        .header("Metadata", "true")
        .send()
        .await?
        .json()
        .await?;
    
    Ok(Resource::new(vec![
        KeyValue::new(resource::CLOUD_PROVIDER, "azure"),
        KeyValue::new(resource::CLOUD_REGION, metadata.location),
        KeyValue::new(resource::CLOUD_PLATFORM, "azure_vm"),
        KeyValue::new(resource::HOST_ID, metadata.vm_id),
        KeyValue::new(resource::HOST_TYPE, metadata.vm_size),
    ]))
}
````

---

## 6. 容器环境

### 6.1 Docker 资源

````rust
/// Docker 环境 Resource
pub fn create_docker_resource() -> Resource {
    let mut attributes = vec![
        KeyValue::new(resource::CONTAINER_RUNTIME, "docker"),
    ];
    
    // 从 Docker 环境变量读取
    if let Ok(container_id) = std::env::var("HOSTNAME") {
        attributes.push(KeyValue::new(resource::CONTAINER_ID, container_id));
    }
    
    if let Ok(image) = std::env::var("DOCKER_IMAGE") {
        attributes.push(KeyValue::new(resource::CONTAINER_IMAGE_NAME, image));
    }
    
    Resource::new(attributes)
}
````

### 6.2 Kubernetes 资源

````yaml
# Kubernetes Deployment 配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
spec:
  template:
    spec:
      containers:
      - name: order-service
        image: order-service:v1.2.3
        env:
          # Service 信息
          - name: OTEL_SERVICE_NAME
            value: "order-service"
          - name: OTEL_SERVICE_VERSION
            value: "1.2.3"
          
          # K8s 信息 (Downward API)
          - name: K8S_NAMESPACE
            valueFrom:
              fieldRef:
                fieldPath: metadata.namespace
          - name: K8S_POD_NAME
            valueFrom:
              fieldRef:
                fieldPath: metadata.name
          - name: K8S_POD_UID
            valueFrom:
              fieldRef:
                fieldPath: metadata.uid
          - name: K8S_NODE_NAME
            valueFrom:
              fieldRef:
                fieldPath: spec.nodeName
````

````rust
/// 从 Kubernetes 环境变量创建 Resource
pub fn create_k8s_resource_from_env() -> Resource {
    Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, env_or_default("OTEL_SERVICE_NAME", "unknown")),
        KeyValue::new(resource::SERVICE_VERSION, env_or_default("OTEL_SERVICE_VERSION", "0.0.0")),
        KeyValue::new(resource::K8S_NAMESPACE_NAME, env_or_default("K8S_NAMESPACE", "")),
        KeyValue::new(resource::K8S_POD_NAME, env_or_default("K8S_POD_NAME", "")),
        KeyValue::new(resource::K8S_POD_UID, env_or_default("K8S_POD_UID", "")),
        KeyValue::new(resource::K8S_NODE_NAME, env_or_default("K8S_NODE_NAME", "")),
    ])
}

fn env_or_default(key: &str, default: &str) -> String {
    std::env::var(key).unwrap_or_else(|_| default.to_string())
}
````

---

## 7. Resource Detector

### 7.1 自定义 Detector

````rust
use opentelemetry::sdk::Resource;
use opentelemetry_sdk::resource::ResourceDetector;
use std::time::Duration;

/// 自定义 Resource Detector
pub struct CustomResourceDetector;

impl ResourceDetector for CustomResourceDetector {
    fn detect(&self, _timeout: Duration) -> Resource {
        let mut attributes = Vec::new();
        
        // 检测自定义属性
        if let Ok(datacenter) = std::env::var("DATACENTER") {
            attributes.push(KeyValue::new("datacenter", datacenter));
        }
        
        if let Ok(team) = std::env::var("TEAM") {
            attributes.push(KeyValue::new("team", team));
        }
        
        Resource::new(attributes)
    }
}
````

### 7.2 Detector 链

````rust
/// 使用多个 Detector
pub fn detect_all_resources() -> Resource {
    let detectors: Vec<Box<dyn ResourceDetector>> = vec![
        // 标准 Detector
        Box::new(opentelemetry_sdk::resource::EnvResourceDetector::new()),
        Box::new(opentelemetry_sdk::resource::OsResourceDetector),
        Box::new(opentelemetry_sdk::resource::ProcessResourceDetector),
        
        // 自定义 Detector
        Box::new(CustomResourceDetector),
    ];
    
    Resource::from_detectors(
        Duration::from_secs(3),
        detectors,
    )
}
````

---

## 8. Resource 合并

### 8.1 合并策略

````rust
/// 合并多个 Resource
pub fn merge_resources() -> Resource {
    // 基础 Resource
    let base = Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, "order-service"),
    ]);
    
    // 环境 Resource
    let env = Resource::new(vec![
        KeyValue::new(resource::DEPLOYMENT_ENVIRONMENT, "production"),
    ]);
    
    // 主机 Resource
    let host = create_host_resource();
    
    // 合并 (后面的覆盖前面的)
    base.merge(&env).merge(&host)
}
````

### 8.2 优先级

````text
Resource 合并优先级 (从高到低):

1. 显式设置的 Resource
   let resource = Resource::new(vec![...]);

2. 环境变量 (OTEL_RESOURCE_ATTRIBUTES)
   export OTEL_RESOURCE_ATTRIBUTES="service.name=my-service"

3. 自动检测的 Resource
   Resource::from_detectors(...)

4. 默认值
   Resource::default()

合并规则:
- 相同键: 高优先级覆盖低优先级
- 不同键: 保留所有键值对
````

---

## 9. 完整示例

### 9.1 本地开发环境

````rust
/// 本地开发环境 Resource
pub fn init_local_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, env!("CARGO_PKG_NAME")),
        KeyValue::new(resource::SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
        KeyValue::new(resource::DEPLOYMENT_ENVIRONMENT, "development"),
        KeyValue::new(resource::HOST_NAME, hostname::get().unwrap().to_string_lossy().to_string()),
    ])
}
````

### 9.2 Kubernetes 部署

````rust
/// Kubernetes 部署 Resource
pub fn init_k8s_resource() -> Resource {
    // 基础 Resource
    let base = Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, env!("CARGO_PKG_NAME")),
        KeyValue::new(resource::SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
    ]);
    
    // K8s Resource
    let k8s = create_k8s_resource_from_env();
    
    // 容器 Resource
    let container = create_container_resource();
    
    // 环境 Resource
    let env = Resource::new(vec![
        KeyValue::new(
            resource::DEPLOYMENT_ENVIRONMENT,
            std::env::var("ENVIRONMENT").unwrap_or_else(|_| "production".to_string()),
        ),
    ]);
    
    base.merge(&k8s).merge(&container).merge(&env)
}
````

### 9.3 AWS Lambda

````rust
/// AWS Lambda Resource
pub fn init_lambda_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new(resource::SERVICE_NAME, env!("CARGO_PKG_NAME")),
        KeyValue::new(resource::SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
        KeyValue::new(resource::CLOUD_PROVIDER, "aws"),
        KeyValue::new(resource::CLOUD_PLATFORM, "aws_lambda"),
        KeyValue::new(resource::CLOUD_REGION, std::env::var("AWS_REGION").unwrap_or_default()),
        KeyValue::new(resource::FAAS_NAME, std::env::var("AWS_LAMBDA_FUNCTION_NAME").unwrap_or_default()),
        KeyValue::new(resource::FAAS_VERSION, std::env::var("AWS_LAMBDA_FUNCTION_VERSION").unwrap_or_default()),
    ])
}
````

---

## 10. 最佳实践

### 10.1 必需属性

````text
必需的 Resource 属性:

1. service.name (必需)
   - 服务名称
   - 示例: "order-service", "payment-service"

2. service.version (强烈推荐)
   - 服务版本
   - 示例: "1.2.3", "2024.01.15"

3. deployment.environment (推荐)
   - 部署环境
   - 示例: "development", "staging", "production"

可选但有用的属性:

4. service.namespace
   - 服务命名空间
   - 示例: "ecommerce", "payment"

5. service.instance.id
   - 服务实例 ID
   - 示例: "order-service-12345"

6. host.name
   - 主机名
   - 示例: "server-01", "ip-10-0-1-100"
````

### 10.2 命名规范

````text
Resource 命名规范:

1. 使用点号分隔命名空间
   ✅ service.name, service.version
   ❌ serviceName, service_name

2. 使用小写字母
   ✅ service.name
   ❌ Service.Name, SERVICE.NAME

3. 使用下划线分隔单词
   ✅ deployment.environment, service.instance.id
   ❌ deploymentEnvironment, serviceinstanceid

4. 遵循语义约定
   ✅ 使用标准属性名 (opentelemetry_semantic_conventions)
   ❌ 自定义属性名 (除非必要)
````

---

## 总结

### 核心要点

1. **Resource**: 描述遥测数据来源的实体
2. **不可变**: 应用启动时设置，不会改变
3. **全局共享**: 附加到所有 Telemetry 数据
4. **语义约定**: 使用标准属性名
5. **自动检测**: 支持环境变量、云平台自动检测
6. **合并机制**: 支持多个 Resource 合并

### Resource 属性分类

| 类别 | 属性 | 示例 |
|------|------|------|
| Service | service.name, service.version | order-service, 1.2.3 |
| 部署环境 | deployment.environment | production |
| 主机 | host.name, host.arch | server-01, x86_64 |
| 容器 | container.id, container.name | abc123, order-pod |
| Kubernetes | k8s.pod.name, k8s.namespace.name | order-pod-xyz, default |
| 云平台 | cloud.provider, cloud.region | aws, us-west-2 |

### 最佳实践清单

- ✅ 必须设置 `service.name`
- ✅ 强烈推荐设置 `service.version`
- ✅ 设置 `deployment.environment`
- ✅ 使用语义约定标准属性
- ✅ 使用环境变量配置
- ✅ 自动检测云平台资源
- ✅ Kubernetes 使用 Downward API
- ✅ 合理合并多个 Resource
- ✅ 避免敏感信息 (密钥、密码)
- ✅ 保持 Resource 简洁 (< 100 个属性)

---

**相关文档**:

- [Baggage 详解](./05_Baggage_详解_Rust完整版.md)
- [SDK 最佳实践](./03_SDK最佳实践_Rust完整版.md)
- [AWS X-Ray 集成](../10_云平台集成/01_AWS_X-Ray_Rust完整集成.md)
- [Kubernetes 部署](../09_CI_CD集成/03_Docker_部署_Rust完整指南.md)
