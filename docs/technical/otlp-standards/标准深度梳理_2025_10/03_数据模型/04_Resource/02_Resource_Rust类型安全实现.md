# OpenTelemetry Resource - Rust 类型安全实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - opentelemetry_sdk: 0.31.0
> - 更新日期: 2025-10-08

## 目录

- [OpenTelemetry Resource - Rust 类型安全实现](#opentelemetry-resource---rust-类型安全实现)
  - [目录](#目录)
  - [概述](#概述)
    - [Resource 特性](#resource-特性)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [Resource 类型定义](#resource-类型定义)
    - [1. 基础 Resource 结构](#1-基础-resource-结构)
    - [2. Resource 构建器](#2-resource-构建器)
  - [语义约定类型](#语义约定类型)
    - [1. Service 属性](#1-service-属性)
    - [2. 部署属性](#2-部署属性)
    - [3. 主机属性](#3-主机属性)
    - [4. 进程属性](#4-进程属性)
  - [Resource 检测器](#resource-检测器)
    - [1. 自动检测](#1-自动检测)
    - [2. 自定义检测器](#2-自定义检测器)
  - [Resource 合并](#resource-合并)
    - [合并策略](#合并策略)
  - [环境变量配置](#环境变量配置)
    - [OTEL\_RESOURCE\_ATTRIBUTES](#otel_resource_attributes)
  - [Kubernetes 集成](#kubernetes-集成)
    - [Pod 信息检测](#pod-信息检测)
  - [云平台集成](#云平台集成)
    - [1. AWS 集成](#1-aws-集成)
    - [2. GCP 集成](#2-gcp-集成)
    - [3. Azure 集成](#3-azure-集成)
  - [最佳实践](#最佳实践)
    - [1. Resource 设计](#1-resource-设计)
    - [2. 性能优化](#2-性能优化)
    - [3. 测试策略](#3-测试策略)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Resource 特性

- **不可变性**: 应用生命周期内不变
- **全局共享**: 所有 Span/Metric/Log 共享
- **类型安全**: 编译时保证属性正确性
- **自动检测**: 环境信息自动发现
- **可合并**: 多个 Resource 合并策略

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "otlp-resource-rust"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }

# 系统信息
hostname = "0.4.0"
sys-info = "0.9.1"

# 环境变量
dotenvy = "0.15.7"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }

# 错误处理
thiserror = "2.0.9"

[target.'cfg(target_os = "linux")'.dependencies]
# Linux 特定依赖
procfs = "0.17.0"
```

---

## Resource 类型定义

### 1. 基础 Resource 结构

```rust
use opentelemetry::{KeyValue, Value};
use opentelemetry_sdk::Resource as SdkResource;
use std::collections::HashMap;

/// 类型安全的 Resource 包装
#[derive(Debug, Clone)]
pub struct Resource {
    inner: SdkResource,
}

impl Resource {
    /// 创建空 Resource
    pub fn empty() -> Self {
        Self {
            inner: SdkResource::empty(),
        }
    }

    /// 从 KeyValue 数组创建
    pub fn new(attributes: Vec<KeyValue>) -> Self {
        Self {
            inner: SdkResource::new(attributes),
        }
    }

    /// 获取属性
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.inner.get(key.into())
    }

    /// 获取所有属性
    pub fn iter(&self) -> impl Iterator<Item = (&opentelemetry::Key, &Value)> {
        self.inner.iter()
    }

    /// 属性数量
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 合并 Resource
    pub fn merge(&mut self, other: &Resource) -> &mut Self {
        self.inner = self.inner.clone().merge(&other.inner);
        self
    }

    /// 转换为 SDK Resource
    pub fn into_sdk_resource(self) -> SdkResource {
        self.inner
    }
}

impl From<SdkResource> for Resource {
    fn from(inner: SdkResource) -> Self {
        Self { inner }
    }
}

impl From<Resource> for SdkResource {
    fn from(resource: Resource) -> Self {
        resource.inner
    }
}
```

### 2. Resource 构建器

```rust
/// Resource 构建器
#[derive(Debug, Default)]
pub struct ResourceBuilder {
    attributes: HashMap<String, Value>,
}

impl ResourceBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加属性
    pub fn with_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<Value>,
    ) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// 批量添加属性
    pub fn with_attributes(mut self, attrs: Vec<KeyValue>) -> Self {
        for kv in attrs {
            self.attributes
                .insert(kv.key.to_string(), kv.value);
        }
        self
    }

    /// 构建 Resource
    pub fn build(self) -> Resource {
        let attributes: Vec<KeyValue> = self
            .attributes
            .into_iter()
            .map(|(k, v)| KeyValue::new(k, v))
            .collect();

        Resource::new(attributes)
    }
}
```

---

## 语义约定类型

### 1. Service 属性

```rust
use opentelemetry::KeyValue;

/// Service 属性构建器
#[derive(Debug, Clone)]
pub struct ServiceAttributes {
    /// 服务名称（必需）
    pub name: String,
    /// 服务版本
    pub version: Option<String>,
    /// 服务命名空间
    pub namespace: Option<String>,
    /// 服务实例 ID
    pub instance_id: Option<String>,
}

impl ServiceAttributes {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            namespace: None,
            instance_id: None,
        }
    }

    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }

    pub fn with_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.namespace = Some(namespace.into());
        self
    }

    pub fn with_instance_id(mut self, instance_id: impl Into<String>) -> Self {
        self.instance_id = Some(instance_id.into());
        self
    }

    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![KeyValue::new("service.name", self.name.clone())];

        if let Some(ref version) = self.version {
            attrs.push(KeyValue::new("service.version", version.clone()));
        }

        if let Some(ref namespace) = self.namespace {
            attrs.push(KeyValue::new("service.namespace", namespace.clone()));
        }

        if let Some(ref instance_id) = self.instance_id {
            attrs.push(KeyValue::new("service.instance.id", instance_id.clone()));
        }

        attrs
    }
}
```

### 2. 部署属性

```rust
/// 部署环境类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeploymentEnvironment {
    Development,
    Staging,
    Production,
}

impl DeploymentEnvironment {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Development => "development",
            Self::Staging => "staging",
            Self::Production => "production",
        }
    }
}

impl From<DeploymentEnvironment> for Value {
    fn from(env: DeploymentEnvironment) -> Self {
        Value::String(env.as_str().into())
    }
}

/// 部署属性
#[derive(Debug, Clone)]
pub struct DeploymentAttributes {
    pub environment: DeploymentEnvironment,
}

impl DeploymentAttributes {
    pub fn new(environment: DeploymentEnvironment) -> Self {
        Self { environment }
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        vec![KeyValue::new(
            "deployment.environment",
            self.environment.as_str(),
        )]
    }
}
```

### 3. 主机属性

```rust
use std::env;

/// 主机属性
#[derive(Debug, Clone)]
pub struct HostAttributes {
    pub name: Option<String>,
    pub arch: Option<String>,
    pub os_type: Option<String>,
    pub os_version: Option<String>,
}

impl HostAttributes {
    /// 自动检测主机属性
    pub fn detect() -> Self {
        Self {
            name: hostname::get().ok().and_then(|h| h.into_string().ok()),
            arch: Some(env::consts::ARCH.to_string()),
            os_type: Some(env::consts::OS.to_string()),
            os_version: sys_info::os_release().ok(),
        }
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();

        if let Some(ref name) = self.name {
            attrs.push(KeyValue::new("host.name", name.clone()));
        }

        if let Some(ref arch) = self.arch {
            attrs.push(KeyValue::new("host.arch", arch.clone()));
        }

        if let Some(ref os_type) = self.os_type {
            attrs.push(KeyValue::new("os.type", os_type.clone()));
        }

        if let Some(ref os_version) = self.os_version {
            attrs.push(KeyValue::new("os.version", os_version.clone()));
        }

        attrs
    }
}
```

### 4. 进程属性

```rust
use std::process;

/// 进程属性
#[derive(Debug, Clone)]
pub struct ProcessAttributes {
    pub pid: u32,
    pub executable_name: Option<String>,
    pub executable_path: Option<String>,
    pub command_args: Option<Vec<String>>,
    pub runtime_name: String,
    pub runtime_version: String,
}

impl ProcessAttributes {
    /// 自动检测进程属性
    pub fn detect() -> Self {
        let pid = process::id();
        let executable_path = env::current_exe().ok();
        let executable_name = executable_path
            .as_ref()
            .and_then(|p| p.file_name())
            .and_then(|n| n.to_str())
            .map(|s| s.to_string());

        let args: Vec<String> = env::args().collect();

        Self {
            pid,
            executable_name,
            executable_path: executable_path.and_then(|p| p.to_str().map(|s| s.to_string())),
            command_args: Some(args),
            runtime_name: "rust".to_string(),
            runtime_version: rustc_version_runtime::version().to_string(),
        }
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("process.pid", self.pid as i64),
            KeyValue::new("process.runtime.name", self.runtime_name.clone()),
            KeyValue::new("process.runtime.version", self.runtime_version.clone()),
        ];

        if let Some(ref name) = self.executable_name {
            attrs.push(KeyValue::new("process.executable.name", name.clone()));
        }

        if let Some(ref path) = self.executable_path {
            attrs.push(KeyValue::new("process.executable.path", path.clone()));
        }

        if let Some(ref args) = self.command_args {
            attrs.push(KeyValue::new(
                "process.command_args",
                args.join(" "),
            ));
        }

        attrs
    }
}
```

---

## Resource 检测器

### 1. 自动检测

```rust
/// Resource 检测器
pub struct ResourceDetector {
    detect_host: bool,
    detect_process: bool,
    detect_env_vars: bool,
}

impl Default for ResourceDetector {
    fn default() -> Self {
        Self {
            detect_host: true,
            detect_process: true,
            detect_env_vars: true,
        }
    }
}

impl ResourceDetector {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_host_detection(mut self, enabled: bool) -> Self {
        self.detect_host = enabled;
        self
    }

    pub fn with_process_detection(mut self, enabled: bool) -> Self {
        self.detect_process = enabled;
        self
    }

    pub fn with_env_vars_detection(mut self, enabled: bool) -> Self {
        self.detect_env_vars = enabled;
        self
    }

    /// 检测并构建 Resource
    pub fn detect(&self) -> Resource {
        let mut builder = ResourceBuilder::new();

        // 检测主机信息
        if self.detect_host {
            let host_attrs = HostAttributes::detect();
            builder = builder.with_attributes(host_attrs.to_key_values());
        }

        // 检测进程信息
        if self.detect_process {
            let process_attrs = ProcessAttributes::detect();
            builder = builder.with_attributes(process_attrs.to_key_values());
        }

        // 从环境变量读取
        if self.detect_env_vars {
            if let Ok(resource_attrs) = env::var("OTEL_RESOURCE_ATTRIBUTES") {
                let attrs = parse_resource_attributes(&resource_attrs);
                builder = builder.with_attributes(attrs);
            }
        }

        builder.build()
    }
}

/// 解析 OTEL_RESOURCE_ATTRIBUTES 环境变量
fn parse_resource_attributes(input: &str) -> Vec<KeyValue> {
    input
        .split(',')
        .filter_map(|pair| {
            let mut parts = pair.splitn(2, '=');
            let key = parts.next()?.trim();
            let value = parts.next()?.trim();
            Some(KeyValue::new(key.to_string(), value.to_string()))
        })
        .collect()
}
```

### 2. 自定义检测器

```rust
use async_trait::async_trait;

/// Resource 检测器 Trait
#[async_trait]
pub trait Detector: Send + Sync {
    async fn detect(&self) -> Result<Resource, Box<dyn std::error::Error>>;
}

/// 示例: Docker 容器检测器
pub struct DockerDetector;

#[async_trait]
impl Detector for DockerDetector {
    async fn detect(&self) -> Result<Resource, Box<dyn std::error::Error>> {
        // 检测是否在 Docker 容器中运行
        let is_docker = std::path::Path::new("/.dockerenv").exists();

        if is_docker {
            let container_id = read_container_id().await?;
            
            Ok(Resource::new(vec![
                KeyValue::new("container.runtime", "docker"),
                KeyValue::new("container.id", container_id),
            ]))
        } else {
            Ok(Resource::empty())
        }
    }
}

async fn read_container_id() -> Result<String, Box<dyn std::error::Error>> {
    // 从 /proc/self/cgroup 读取容器 ID
    let content = tokio::fs::read_to_string("/proc/self/cgroup").await?;
    
    for line in content.lines() {
        if let Some(id) = line.split('/').last() {
            if id.len() == 64 {
                return Ok(id.to_string());
            }
        }
    }
    
    Err("Container ID not found".into())
}
```

---

## Resource 合并

### 合并策略

```rust
/// Resource 合并策略
pub enum MergeStrategy {
    /// 保留第一个值
    KeepFirst,
    /// 使用最后一个值（默认）
    UseLast,
    /// 自定义合并函数
    Custom(fn(&Value, &Value) -> Value),
}

impl Resource {
    /// 使用策略合并 Resource
    pub fn merge_with_strategy(
        &mut self,
        other: &Resource,
        strategy: &MergeStrategy,
    ) -> &mut Self {
        match strategy {
            MergeStrategy::KeepFirst => {
                // 只添加不存在的键
                for (key, value) in other.iter() {
                    if self.get(key.as_str()).is_none() {
                        let mut new_inner = self.inner.clone();
                        new_inner = new_inner.merge(&SdkResource::new(vec![
                            KeyValue::new(key.clone(), value.clone())
                        ]));
                        self.inner = new_inner;
                    }
                }
            }
            MergeStrategy::UseLast => {
                // 默认行为：后者覆盖前者
                self.inner = self.inner.clone().merge(&other.inner);
            }
            MergeStrategy::Custom(merge_fn) => {
                // 自定义合并逻辑
                for (key, new_value) in other.iter() {
                    if let Some(existing_value) = self.get(key.as_str()) {
                        let merged_value = merge_fn(existing_value, new_value);
                        let mut new_inner = self.inner.clone();
                        new_inner = new_inner.merge(&SdkResource::new(vec![
                            KeyValue::new(key.clone(), merged_value)
                        ]));
                        self.inner = new_inner;
                    } else {
                        let mut new_inner = self.inner.clone();
                        new_inner = new_inner.merge(&SdkResource::new(vec![
                            KeyValue::new(key.clone(), new_value.clone())
                        ]));
                        self.inner = new_inner;
                    }
                }
            }
        }
        self
    }
}
```

---

## 环境变量配置

### OTEL_RESOURCE_ATTRIBUTES

```rust
use std::env;

/// 从环境变量创建 Resource
pub fn resource_from_env() -> Resource {
    let mut builder = ResourceBuilder::new();

    // OTEL_RESOURCE_ATTRIBUTES
    if let Ok(attrs) = env::var("OTEL_RESOURCE_ATTRIBUTES") {
        let parsed = parse_resource_attributes(&attrs);
        builder = builder.with_attributes(parsed);
    }

    // OTEL_SERVICE_NAME
    if let Ok(service_name) = env::var("OTEL_SERVICE_NAME") {
        builder = builder.with_attribute("service.name", service_name);
    }

    builder.build()
}

/// 示例环境变量
pub fn example_env_vars() {
    // 设置示例环境变量
    env::set_var(
        "OTEL_RESOURCE_ATTRIBUTES",
        "service.name=my-service,service.version=1.0.0,deployment.environment=production",
    );

    let resource = resource_from_env();
    
    println!("Service Name: {:?}", resource.get("service.name"));
    println!("Service Version: {:?}", resource.get("service.version"));
    println!("Environment: {:?}", resource.get("deployment.environment"));
}
```

---

## Kubernetes 集成

### Pod 信息检测

```rust
use std::fs;

/// Kubernetes 属性
#[derive(Debug, Clone)]
pub struct KubernetesAttributes {
    pub pod_name: Option<String>,
    pub pod_namespace: Option<String>,
    pub pod_uid: Option<String>,
    pub node_name: Option<String>,
}

impl KubernetesAttributes {
    /// 从 Downward API 检测
    pub async fn detect() -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            pod_name: read_k8s_file("/etc/podinfo/name").await.ok(),
            pod_namespace: read_k8s_file("/etc/podinfo/namespace").await.ok(),
            pod_uid: read_k8s_file("/etc/podinfo/uid").await.ok(),
            node_name: env::var("NODE_NAME").ok(),
        })
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();

        if let Some(ref pod_name) = self.pod_name {
            attrs.push(KeyValue::new("k8s.pod.name", pod_name.clone()));
        }

        if let Some(ref namespace) = self.pod_namespace {
            attrs.push(KeyValue::new("k8s.namespace.name", namespace.clone()));
        }

        if let Some(ref uid) = self.pod_uid {
            attrs.push(KeyValue::new("k8s.pod.uid", uid.clone()));
        }

        if let Some(ref node_name) = self.node_name {
            attrs.push(KeyValue::new("k8s.node.name", node_name.clone()));
        }

        attrs
    }
}

async fn read_k8s_file(path: &str) -> Result<String, Box<dyn std::error::Error>> {
    let content = tokio::fs::read_to_string(path).await?;
    Ok(content.trim().to_string())
}
```

---

## 云平台集成

### 1. AWS 集成

```rust
/// AWS EC2 元数据
pub struct AwsEc2Metadata {
    pub instance_id: Option<String>,
    pub region: Option<String>,
    pub availability_zone: Option<String>,
}

impl AwsEc2Metadata {
    pub async fn detect() -> Result<Self, Box<dyn std::error::Error>> {
        let client = reqwest::Client::new();
        let base_url = "http://169.254.169.254/latest/meta-data";

        let instance_id = client
            .get(format!("{}/instance-id", base_url))
            .send()
            .await?
            .text()
            .await
            .ok();

        let availability_zone = client
            .get(format!("{}/placement/availability-zone", base_url))
            .send()
            .await?
            .text()
            .await
            .ok();

        let region = availability_zone
            .as_ref()
            .map(|az| az[..az.len() - 1].to_string());

        Ok(Self {
            instance_id,
            region,
            availability_zone,
        })
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![KeyValue::new("cloud.provider", "aws")];

        if let Some(ref instance_id) = self.instance_id {
            attrs.push(KeyValue::new("cloud.resource_id", instance_id.clone()));
        }

        if let Some(ref region) = self.region {
            attrs.push(KeyValue::new("cloud.region", region.clone()));
        }

        if let Some(ref az) = self.availability_zone {
            attrs.push(KeyValue::new("cloud.availability_zone", az.clone()));
        }

        attrs
    }
}
```

### 2. GCP 集成

```rust
/// GCP 元数据
pub struct GcpMetadata {
    pub project_id: Option<String>,
    pub instance_id: Option<String>,
    pub zone: Option<String>,
}

impl GcpMetadata {
    pub async fn detect() -> Result<Self, Box<dyn std::error::Error>> {
        let client = reqwest::Client::builder()
            .default_headers({
                let mut headers = reqwest::header::HeaderMap::new();
                headers.insert(
                    "Metadata-Flavor",
                    reqwest::header::HeaderValue::from_static("Google"),
                );
                headers
            })
            .build()?;

        let base_url = "http://metadata.google.internal/computeMetadata/v1";

        let project_id = client
            .get(format!("{}/project/project-id", base_url))
            .send()
            .await?
            .text()
            .await
            .ok();

        let instance_id = client
            .get(format!("{}/instance/id", base_url))
            .send()
            .await?
            .text()
            .await
            .ok();

        let zone = client
            .get(format!("{}/instance/zone", base_url))
            .send()
            .await?
            .text()
            .await
            .ok();

        Ok(Self {
            project_id,
            instance_id,
            zone,
        })
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![KeyValue::new("cloud.provider", "gcp")];

        if let Some(ref project_id) = self.project_id {
            attrs.push(KeyValue::new("cloud.account.id", project_id.clone()));
        }

        if let Some(ref instance_id) = self.instance_id {
            attrs.push(KeyValue::new("cloud.resource_id", instance_id.clone()));
        }

        if let Some(ref zone) = self.zone {
            attrs.push(KeyValue::new("cloud.availability_zone", zone.clone()));
        }

        attrs
    }
}
```

### 3. Azure 集成

```rust
/// Azure 元数据
pub struct AzureMetadata {
    pub vm_id: Option<String>,
    pub region: Option<String>,
    pub subscription_id: Option<String>,
}

impl AzureMetadata {
    pub async fn detect() -> Result<Self, Box<dyn std::error::Error>> {
        let client = reqwest::Client::builder()
            .default_headers({
                let mut headers = reqwest::header::HeaderMap::new();
                headers.insert(
                    "Metadata",
                    reqwest::header::HeaderValue::from_static("true"),
                );
                headers
            })
            .build()?;

        let url = "http://169.254.169.254/metadata/instance?api-version=2021-02-01";

        let response: serde_json::Value = client
            .get(url)
            .send()
            .await?
            .json()
            .await?;

        let vm_id = response["compute"]["vmId"].as_str().map(|s| s.to_string());
        let region = response["compute"]["location"].as_str().map(|s| s.to_string());
        let subscription_id = response["compute"]["subscriptionId"].as_str().map(|s| s.to_string());

        Ok(Self {
            vm_id,
            region,
            subscription_id,
        })
    }

    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![KeyValue::new("cloud.provider", "azure")];

        if let Some(ref vm_id) = self.vm_id {
            attrs.push(KeyValue::new("cloud.resource_id", vm_id.clone()));
        }

        if let Some(ref region) = self.region {
            attrs.push(KeyValue::new("cloud.region", region.clone()));
        }

        if let Some(ref subscription_id) = self.subscription_id {
            attrs.push(KeyValue::new("cloud.account.id", subscription_id.clone()));
        }

        attrs
    }
}
```

---

## 最佳实践

### 1. Resource 设计

```rust
// ✅ 推荐: 使用语义约定
let resource = ResourceBuilder::new()
    .with_attribute("service.name", "my-service")
    .with_attribute("service.version", "1.0.0")
    .with_attribute("deployment.environment", "production")
    .build();

// ❌ 避免: 使用自定义键
let resource = ResourceBuilder::new()
    .with_attribute("my_service_name", "my-service") // 不符合约定
    .build();
```

### 2. 性能优化

```rust
// ✅ 推荐: 应用启动时创建一次
lazy_static::lazy_static! {
    static ref RESOURCE: Resource = {
        let detector = ResourceDetector::new();
        detector.detect()
    };
}

// ❌ 避免: 每次请求都创建
async fn handle_request() {
    let resource = ResourceDetector::new().detect(); // 性能浪费
}
```

### 3. 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_service_attributes() {
        let attrs = ServiceAttributes::new("test-service")
            .with_version("1.0.0")
            .to_key_values();

        assert_eq!(attrs.len(), 2);
        assert!(attrs.iter().any(|kv| kv.key.as_str() == "service.name"));
    }

    #[test]
    fn test_resource_merge() {
        let r1 = Resource::new(vec![KeyValue::new("key1", "value1")]);
        let r2 = Resource::new(vec![KeyValue::new("key2", "value2")]);

        let mut merged = r1.clone();
        merged.merge(&r2);

        assert_eq!(merged.len(), 2);
    }
}
```

---

## 完整示例

### main.rs

```rust
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建服务属性
    let service_attrs = ServiceAttributes::new("order-service")
        .with_version("1.0.0")
        .with_namespace("production");

    // 创建部署属性
    let deployment_attrs = DeploymentAttributes::new(DeploymentEnvironment::Production);

    // 自动检测主机和进程属性
    let host_attrs = HostAttributes::detect();
    let process_attrs = ProcessAttributes::detect();

    // 合并所有属性
    let resource = ResourceBuilder::new()
        .with_attributes(service_attrs.to_key_values())
        .with_attributes(deployment_attrs.to_key_values())
        .with_attributes(host_attrs.to_key_values())
        .with_attributes(process_attrs.to_key_values())
        .build();

    // 打印 Resource
    println!("Resource Attributes:");
    for (key, value) in resource.iter() {
        println!("  {}: {:?}", key, value);
    }

    Ok(())
}
```

---

## 总结

本文档提供了 OpenTelemetry Resource 在 Rust 1.90 环境下的完整类型安全实现：

1. ✅ **类型定义**: Resource、ResourceBuilder、语义约定类型
2. ✅ **自动检测**: 主机、进程、环境变量自动检测
3. ✅ **云平台集成**: AWS、GCP、Azure 元数据检测
4. ✅ **Kubernetes 集成**: Pod 信息自动发现
5. ✅ **合并策略**: 灵活的 Resource 合并
6. ✅ **最佳实践**: 设计模式、性能优化、测试策略

通过本文档的指导，您可以构建标准化、类型安全的 Rust Resource 系统。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
