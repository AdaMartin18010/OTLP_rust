# 🏷️ Resource Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🏷️ Resource Rust 完整版](#️-resource-rust-完整版)
  - [📋 目录](#-目录)
  - [1. Resource 概述](#1-resource-概述)
    - [1.1 什么是 Resource？](#11-什么是-resource)
    - [1.2 核心概念](#12-核心概念)
    - [1.3 为什么需要 Resource？](#13-为什么需要-resource)
  - [2. Resource 定义](#2-resource-定义)
    - [2.1 数据结构](#21-数据结构)
    - [2.2 OpenTelemetry SDK 实现](#22-opentelemetry-sdk-实现)
  - [3. 语义约定](#3-语义约定)
    - [3.1 服务属性](#31-服务属性)
    - [3.2 主机属性](#32-主机属性)
    - [3.3 容器属性](#33-容器属性)
    - [3.4 Kubernetes 属性](#34-kubernetes-属性)
    - [3.5 云平台属性](#35-云平台属性)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 基本使用](#41-基本使用)
    - [4.2 从环境变量加载](#42-从环境变量加载)
    - [4.3 合并多个 Resource](#43-合并多个-resource)
  - [5. Resource 检测](#5-resource-检测)
    - [5.1 自动检测器](#51-自动检测器)
    - [5.2 异步检测](#52-异步检测)
  - [6. 合并与优先级](#6-合并与优先级)
    - [6.1 合并规则](#61-合并规则)
    - [6.2 优先级顺序](#62-优先级顺序)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 必需属性](#71-必需属性)
    - [7.2 环境特定配置](#72-环境特定配置)
    - [7.3 动态属性](#73-动态属性)
  - [8. 实战案例](#8-实战案例)
    - [8.1 微服务配置](#81-微服务配置)
    - [8.2 多租户系统](#82-多租户系统)
    - [8.3 A/B 测试](#83-ab-测试)
  - [🔗 参考资源](#-参考资源)

---

## 1. Resource 概述

### 1.1 什么是 Resource？

**Resource** 是描述生成遥测数据的实体的不可变表示，包含服务、主机、容器等信息。

### 1.2 核心概念

| 概念 | 说明 | 示例 |
|------|------|------|
| **service.name** | 服务名称 | `my-api-service` |
| **service.version** | 服务版本 | `1.2.3` |
| **host.name** | 主机名 | `server-01` |
| **container.id** | 容器ID | `abc123...` |
| **cloud.provider** | 云提供商 | `aws`, `gcp`, `azure` |
| **deployment.environment** | 部署环境 | `production`, `staging` |

### 1.3 为什么需要 Resource？

```text
Traces/Metrics/Logs + Resource = 完整上下文

示例：
Span { name: "GET /api/users", duration: 120ms }
  + Resource { 
      service.name: "api-gateway",
      host.name: "prod-server-01",
      cloud.provider: "aws"
    }
= 完整的可观测性数据
```

---

## 2. Resource 定义

### 2.1 数据结构

```rust
use opentelemetry::{KeyValue, Value};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Resource {
    /// 资源属性
    attributes: HashMap<String, Value>,
}

impl Resource {
    /// 创建新的 Resource
    pub fn new(attributes: Vec<KeyValue>) -> Self {
        let mut map = HashMap::new();
        for kv in attributes {
            map.insert(kv.key.to_string(), kv.value);
        }
        Self { attributes: map }
    }
    
    /// 获取属性
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.attributes.get(key)
    }
    
    /// 合并两个 Resource
    pub fn merge(&self, other: &Resource) -> Resource {
        let mut merged = self.attributes.clone();
        for (key, value) in &other.attributes {
            merged.insert(key.clone(), value.clone());
        }
        Resource { attributes: merged }
    }
}
```

### 2.2 OpenTelemetry SDK 实现

```rust
use opentelemetry_sdk::Resource as SdkResource;
use opentelemetry::KeyValue;

// 创建 Resource
let resource = SdkResource::new(vec![
    KeyValue::new("service.name", "my-service"),
    KeyValue::new("service.version", "1.0.0"),
]);

// 从环境变量创建
let resource = SdkResource::from_env();

// 默认 Resource（包含 SDK 信息）
let resource = SdkResource::default();
```

---

## 3. 语义约定

### 3.1 服务属性

```rust
use opentelemetry::KeyValue;

// 服务标识
vec![
    KeyValue::new("service.name", "api-gateway"),
    KeyValue::new("service.namespace", "production"),
    KeyValue::new("service.instance.id", "instance-123"),
    KeyValue::new("service.version", "1.2.3"),
]
```

### 3.2 主机属性

```rust
use sysinfo::{System, SystemExt};

fn get_host_attributes() -> Vec<KeyValue> {
    let mut system = System::new_all();
    system.refresh_all();
    
    vec![
        KeyValue::new("host.name", hostname::get().unwrap().to_string_lossy().to_string()),
        KeyValue::new("host.type", std::env::consts::OS),
        KeyValue::new("host.arch", std::env::consts::ARCH),
        KeyValue::new("host.cpu.count", system.cpus().len() as i64),
    ]
}
```

### 3.3 容器属性

```rust
fn get_container_attributes() -> Vec<KeyValue> {
    let mut attrs = Vec::new();
    
    // Docker 容器 ID
    if let Ok(cgroup) = std::fs::read_to_string("/proc/self/cgroup") {
        if let Some(container_id) = extract_container_id(&cgroup) {
            attrs.push(KeyValue::new("container.id", container_id));
        }
    }
    
    // 容器名称（从环境变量）
    if let Ok(name) = std::env::var("CONTAINER_NAME") {
        attrs.push(KeyValue::new("container.name", name));
    }
    
    attrs
}

fn extract_container_id(cgroup: &str) -> Option<String> {
    // 提取 Docker 容器 ID
    for line in cgroup.lines() {
        if line.contains("/docker/") {
            if let Some(id) = line.split('/').last() {
                return Some(id.to_string());
            }
        }
    }
    None
}
```

### 3.4 Kubernetes 属性

```rust
fn get_k8s_attributes() -> Vec<KeyValue> {
    let mut attrs = Vec::new();
    
    // 从环境变量读取
    if let Ok(pod_name) = std::env::var("POD_NAME") {
        attrs.push(KeyValue::new("k8s.pod.name", pod_name));
    }
    
    if let Ok(namespace) = std::env::var("POD_NAMESPACE") {
        attrs.push(KeyValue::new("k8s.namespace.name", namespace));
    }
    
    if let Ok(deployment) = std::env::var("DEPLOYMENT_NAME") {
        attrs.push(KeyValue::new("k8s.deployment.name", deployment));
    }
    
    if let Ok(node) = std::env::var("NODE_NAME") {
        attrs.push(KeyValue::new("k8s.node.name", node));
    }
    
    attrs
}
```

### 3.5 云平台属性

```rust
// AWS
fn get_aws_attributes() -> Vec<KeyValue> {
    vec![
        KeyValue::new("cloud.provider", "aws"),
        KeyValue::new("cloud.platform", "aws_ec2"),
        KeyValue::new("cloud.region", std::env::var("AWS_REGION").unwrap_or_default()),
        KeyValue::new("cloud.account.id", std::env::var("AWS_ACCOUNT_ID").unwrap_or_default()),
    ]
}

// GCP
fn get_gcp_attributes() -> Vec<KeyValue> {
    vec![
        KeyValue::new("cloud.provider", "gcp"),
        KeyValue::new("cloud.platform", "gcp_compute_engine"),
        KeyValue::new("cloud.region", std::env::var("GCP_REGION").unwrap_or_default()),
        KeyValue::new("cloud.project.id", std::env::var("GCP_PROJECT").unwrap_or_default()),
    ]
}

// Azure
fn get_azure_attributes() -> Vec<KeyValue> {
    vec![
        KeyValue::new("cloud.provider", "azure"),
        KeyValue::new("cloud.platform", "azure_vm"),
        KeyValue::new("cloud.region", std::env::var("AZURE_REGION").unwrap_or_default()),
    ]
}
```

---

## 4. Rust 实现

### 4.1 基本使用

```rust
use opentelemetry_sdk::{Resource, trace::TracerProvider};
use opentelemetry::KeyValue;

fn init_with_resource() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
    ]);
    
    // 应用到 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    Ok(())
}
```

### 4.2 从环境变量加载

```rust
use opentelemetry_sdk::Resource;

// 环境变量配置
// export OTEL_SERVICE_NAME=my-service
// export OTEL_RESOURCE_ATTRIBUTES=service.version=1.0.0,deployment.environment=production

fn init_from_env() -> Result<(), Box<dyn std::error::Error>> {
    // 从环境变量自动加载
    let resource = Resource::from_env();
    
    let tracer_provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    Ok(())
}
```

### 4.3 合并多个 Resource

```rust
fn merge_resources() -> Result<(), Box<dyn std::error::Error>> {
    // 基础 Resource
    let base = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
    ]);
    
    // 主机信息
    let host = Resource::new(get_host_attributes());
    
    // Kubernetes 信息
    let k8s = Resource::new(get_k8s_attributes());
    
    // 合并（后面的覆盖前面的）
    let resource = base.merge(&host).merge(&k8s);
    
    let tracer_provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    Ok(())
}
```

---

## 5. Resource 检测

### 5.1 自动检测器

```rust
use opentelemetry_sdk::Resource;

pub struct ResourceDetector;

impl ResourceDetector {
    pub fn detect() -> Resource {
        let mut attributes = Vec::new();
        
        // 1. 服务信息
        attributes.extend(Self::detect_service());
        
        // 2. 主机信息
        attributes.extend(Self::detect_host());
        
        // 3. 容器信息
        attributes.extend(Self::detect_container());
        
        // 4. Kubernetes 信息
        attributes.extend(Self::detect_k8s());
        
        // 5. 云平台信息
        attributes.extend(Self::detect_cloud());
        
        Resource::new(attributes)
    }
    
    fn detect_service() -> Vec<KeyValue> {
        vec![
            KeyValue::new("service.name", 
                std::env::var("SERVICE_NAME")
                    .unwrap_or_else(|_| env!("CARGO_PKG_NAME").to_string())
            ),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        ]
    }
    
    fn detect_host() -> Vec<KeyValue> {
        get_host_attributes()
    }
    
    fn detect_container() -> Vec<KeyValue> {
        get_container_attributes()
    }
    
    fn detect_k8s() -> Vec<KeyValue> {
        // 检测是否在 K8s 环境
        if std::env::var("KUBERNETES_SERVICE_HOST").is_ok() {
            get_k8s_attributes()
        } else {
            Vec::new()
        }
    }
    
    fn detect_cloud() -> Vec<KeyValue> {
        // 检测云平台
        if std::env::var("AWS_REGION").is_ok() {
            get_aws_attributes()
        } else if std::env::var("GCP_PROJECT").is_ok() {
            get_gcp_attributes()
        } else if std::env::var("AZURE_REGION").is_ok() {
            get_azure_attributes()
        } else {
            Vec::new()
        }
    }
}

// 使用
fn init_with_detection() -> Result<(), Box<dyn std::error::Error>> {
    let resource = ResourceDetector::detect();
    
    let tracer_provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    Ok(())
}
```

### 5.2 异步检测

```rust
use tokio::task::JoinSet;

pub struct AsyncResourceDetector;

impl AsyncResourceDetector {
    pub async fn detect() -> Resource {
        let mut tasks = JoinSet::new();
        
        // 并行检测
        tasks.spawn(Self::detect_service_async());
        tasks.spawn(Self::detect_cloud_async());
        tasks.spawn(Self::detect_container_async());
        
        let mut all_attributes = Vec::new();
        
        while let Some(result) = tasks.join_next().await {
            if let Ok(attrs) = result {
                all_attributes.extend(attrs);
            }
        }
        
        Resource::new(all_attributes)
    }
    
    async fn detect_service_async() -> Vec<KeyValue> {
        vec![
            KeyValue::new("service.name", "my-service"),
        ]
    }
    
    async fn detect_cloud_async() -> Vec<KeyValue> {
        // 异步查询云平台元数据
        // 例如：AWS Instance Metadata Service
        Vec::new()
    }
    
    async fn detect_container_async() -> Vec<KeyValue> {
        tokio::task::spawn_blocking(|| {
            get_container_attributes()
        })
        .await
        .unwrap_or_default()
    }
}
```

---

## 6. 合并与优先级

### 6.1 合并规则

```rust
fn merge_example() {
    let r1 = Resource::new(vec![
        KeyValue::new("service.name", "service-a"),
        KeyValue::new("host.name", "host-1"),
    ]);
    
    let r2 = Resource::new(vec![
        KeyValue::new("service.name", "service-b"),  // 覆盖 r1
        KeyValue::new("cloud.provider", "aws"),      // 新增
    ]);
    
    let merged = r1.merge(&r2);
    
    // 结果:
    // service.name = "service-b"  (r2 覆盖 r1)
    // host.name = "host-1"        (r1 保留)
    // cloud.provider = "aws"      (r2 新增)
}
```

### 6.2 优先级顺序

```text
优先级（从高到低）:

1. 代码中显式设置
2. 环境变量 (OTEL_RESOURCE_ATTRIBUTES)
3. 自动检测
4. SDK 默认值
```

```rust
fn priority_example() -> Resource {
    // 1. SDK 默认值（最低优先级）
    let default_resource = Resource::default();
    
    // 2. 自动检测
    let detected_resource = ResourceDetector::detect();
    
    // 3. 环境变量
    let env_resource = Resource::from_env();
    
    // 4. 代码显式设置（最高优先级）
    let explicit_resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
    ]);
    
    // 合并（优先级递增）
    default_resource
        .merge(&detected_resource)
        .merge(&env_resource)
        .merge(&explicit_resource)
}
```

---

## 7. 最佳实践

### 7.1 必需属性

```rust
// ✅ 最小必需属性
fn minimal_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ])
}

// ✅ 推荐属性
fn recommended_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("service.namespace", "production"),
        KeyValue::new("deployment.environment", "production"),
    ])
}
```

### 7.2 环境特定配置

```rust
fn environment_specific_resource(env: &str) -> Resource {
    let mut attrs = vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("deployment.environment", env),
    ];
    
    match env {
        "production" => {
            attrs.push(KeyValue::new("service.instance.id", generate_instance_id()));
            attrs.push(KeyValue::new("telemetry.sampling.rate", 0.1));
        }
        "staging" => {
            attrs.push(KeyValue::new("telemetry.sampling.rate", 0.5));
        }
        "development" => {
            attrs.push(KeyValue::new("telemetry.sampling.rate", 1.0));
            attrs.push(KeyValue::new("telemetry.debug", true));
        }
        _ => {}
    }
    
    Resource::new(attrs)
}
```

### 7.3 动态属性

```rust
use std::sync::OnceLock;

static RESOURCE: OnceLock<Resource> = OnceLock::new();

fn init_dynamic_resource() {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("process.pid", std::process::id() as i64),
        KeyValue::new("process.runtime.name", "rust"),
        KeyValue::new("process.runtime.version", rustc_version_runtime::version().to_string()),
    ]);
    
    RESOURCE.set(resource).ok();
}

fn get_resource() -> &'static Resource {
    RESOURCE.get().expect("Resource not initialized")
}
```

---

## 8. 实战案例

### 8.1 微服务配置

```rust
use opentelemetry_sdk::{Resource, trace::TracerProvider};
use opentelemetry::KeyValue;

pub struct ServiceConfig {
    pub name: String,
    pub version: String,
    pub environment: String,
}

impl ServiceConfig {
    pub fn to_resource(&self) -> Resource {
        let mut attrs = vec![
            KeyValue::new("service.name", self.name.clone()),
            KeyValue::new("service.version", self.version.clone()),
            KeyValue::new("deployment.environment", self.environment.clone()),
        ];
        
        // 主机信息
        attrs.extend(get_host_attributes());
        
        // 容器信息
        if std::path::Path::new("/.dockerenv").exists() {
            attrs.extend(get_container_attributes());
        }
        
        // K8s 信息
        if std::env::var("KUBERNETES_SERVICE_HOST").is_ok() {
            attrs.extend(get_k8s_attributes());
        }
        
        Resource::new(attrs)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = ServiceConfig {
        name: "api-gateway".to_string(),
        version: "1.2.3".to_string(),
        environment: "production".to_string(),
    };
    
    let resource = config.to_resource();
    
    let tracer_provider = TracerProvider::builder()
        .with_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource)
        )
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter().tonic(),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();
    
    opentelemetry::global::set_tracer_provider(tracer_provider);
    
    // 应用逻辑
    
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 8.2 多租户系统

```rust
pub struct TenantResource {
    base_resource: Resource,
}

impl TenantResource {
    pub fn new(base_resource: Resource) -> Self {
        Self { base_resource }
    }
    
    pub fn for_tenant(&self, tenant_id: &str) -> Resource {
        let tenant_attrs = vec![
            KeyValue::new("tenant.id", tenant_id.to_string()),
        ];
        
        self.base_resource.merge(&Resource::new(tenant_attrs))
    }
}

// 使用
fn multi_tenant_example() {
    let base = Resource::new(vec![
        KeyValue::new("service.name", "multi-tenant-api"),
    ]);
    
    let tenant_resource = TenantResource::new(base);
    
    // 为每个租户创建专用 TracerProvider
    let tenant_a_resource = tenant_resource.for_tenant("tenant-a");
    let tenant_b_resource = tenant_resource.for_tenant("tenant-b");
}
```

### 8.3 A/B 测试

```rust
pub struct ExperimentResource {
    base_resource: Resource,
}

impl ExperimentResource {
    pub fn new(base_resource: Resource) -> Self {
        Self { base_resource }
    }
    
    pub fn with_experiment(&self, experiment_id: &str, variant: &str) -> Resource {
        let experiment_attrs = vec![
            KeyValue::new("experiment.id", experiment_id.to_string()),
            KeyValue::new("experiment.variant", variant.to_string()),
        ];
        
        self.base_resource.merge(&Resource::new(experiment_attrs))
    }
}

// 使用
async fn ab_test_example(user_id: u64) {
    let base = Resource::new(vec![
        KeyValue::new("service.name", "web-app"),
    ]);
    
    let experiment = ExperimentResource::new(base);
    
    // 根据用户ID分配变体
    let variant = if user_id % 2 == 0 { "control" } else { "treatment" };
    let resource = experiment.with_experiment("new-ui-experiment", variant);
    
    // 使用该 Resource 创建 Span
}
```

---

## 🔗 参考资源

- [OpenTelemetry Resource Specification](https://opentelemetry.io/docs/specs/otel/resource/semantic_conventions/)
- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry/)
- [Rust OTLP 快速入门](../../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../../README.md) | [📊 数据模型](../README.md) | [🔍 SpanContext](../01_Traces数据模型/02_SpanContext_Rust完整版.md)
