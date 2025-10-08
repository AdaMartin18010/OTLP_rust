# OpenTelemetry Baggage - Rust 类型安全实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08

## 目录

- [OpenTelemetry Baggage - Rust 类型安全实现](#opentelemetry-baggage---rust-类型安全实现)
  - [目录](#目录)
  - [概述](#概述)
    - [Baggage 特性](#baggage-特性)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [Baggage 类型定义](#baggage-类型定义)
    - [1. Baggage Entry](#1-baggage-entry)
    - [2. Baggage 容器](#2-baggage-容器)
  - [Baggage API](#baggage-api)
    - [1. 设置和获取](#1-设置和获取)
    - [2. 传播机制](#2-传播机制)
  - [HTTP 传播](#http-传播)
    - [1. W3C Baggage Header](#1-w3c-baggage-header)
    - [2. HTTP 客户端集成](#2-http-客户端集成)
    - [3. HTTP 服务器集成](#3-http-服务器集成)
  - [gRPC 传播](#grpc-传播)
    - [gRPC 元数据集成](#grpc-元数据集成)
  - [使用场景](#使用场景)
    - [1. 用户标识传播](#1-用户标识传播)
    - [2. A/B 测试](#2-ab-测试)
    - [3. 请求优先级](#3-请求优先级)
  - [性能优化](#性能优化)
    - [1. 大小限制](#1-大小限制)
    - [2. 编码优化](#2-编码优化)
  - [安全考虑](#安全考虑)
    - [1. 敏感数据过滤](#1-敏感数据过滤)
    - [2. 大小验证](#2-大小验证)
  - [最佳实践](#最佳实践)
    - [1. 键命名约定](#1-键命名约定)
    - [2. 值大小控制](#2-值大小控制)
    - [3. 生命周期管理](#3-生命周期管理)
  - [完整示例](#完整示例)
    - [微服务链路追踪](#微服务链路追踪)
  - [总结](#总结)

---

## 概述

### Baggage 特性

- **跨服务传播**: 随请求自动传播
- **类型安全**: 编译时保证键值正确性
- **W3C 标准**: 遵循 W3C Baggage 规范
- **透明传递**: SDK 自动注入和提取
- **可扩展**: 支持自定义元数据

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "otlp-baggage-rust"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = "0.31.0"

# HTTP 客户端
reqwest = "0.12.23"
hyper = "1.7.0"
axum = "0.8.7"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
urlencoding = "2.1.3"

# 错误处理
thiserror = "2.0.9"
```

---

## Baggage 类型定义

### 1. Baggage Entry

```rust
use std::fmt;

/// Baggage 条目
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BaggageEntry {
    /// 值
    value: String,
    /// 元数据（可选）
    metadata: Option<BaggageMetadata>,
}

impl BaggageEntry {
    /// 创建新条目
    pub fn new(value: impl Into<String>) -> Self {
        Self {
            value: value.into(),
            metadata: None,
        }
    }

    /// 添加元数据
    pub fn with_metadata(mut self, metadata: BaggageMetadata) -> Self {
        self.metadata = Some(metadata);
        self
    }

    /// 获取值
    pub fn value(&self) -> &str {
        &self.value
    }

    /// 获取元数据
    pub fn metadata(&self) -> Option<&BaggageMetadata> {
        self.metadata.as_ref()
    }
}

impl From<String> for BaggageEntry {
    fn from(value: String) -> Self {
        Self::new(value)
    }
}

impl From<&str> for BaggageEntry {
    fn from(value: &str) -> Self {
        Self::new(value.to_string())
    }
}

/// Baggage 元数据
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BaggageMetadata {
    properties: Vec<(String, Option<String>)>,
}

impl BaggageMetadata {
    pub fn new() -> Self {
        Self {
            properties: Vec::new(),
        }
    }

    pub fn with_property(
        mut self,
        key: impl Into<String>,
        value: Option<impl Into<String>>,
    ) -> Self {
        self.properties.push((
            key.into(),
            value.map(|v| v.into()),
        ));
        self
    }

    pub fn properties(&self) -> &[(String, Option<String>)] {
        &self.properties
    }
}

impl Default for BaggageMetadata {
    fn default() -> Self {
        Self::new()
    }
}
```

### 2. Baggage 容器

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// Baggage 容器
#[derive(Debug, Clone)]
pub struct Baggage {
    entries: Arc<RwLock<HashMap<String, BaggageEntry>>>,
}

impl Baggage {
    /// 创建空 Baggage
    pub fn new() -> Self {
        Self {
            entries: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 设置条目
    pub fn set(&self, key: impl Into<String>, entry: BaggageEntry) {
        let mut entries = self.entries.write().unwrap();
        entries.insert(key.into(), entry);
    }

    /// 获取条目
    pub fn get(&self, key: &str) -> Option<BaggageEntry> {
        let entries = self.entries.read().unwrap();
        entries.get(key).cloned()
    }

    /// 获取值
    pub fn get_value(&self, key: &str) -> Option<String> {
        self.get(key).map(|entry| entry.value().to_string())
    }

    /// 删除条目
    pub fn remove(&self, key: &str) -> Option<BaggageEntry> {
        let mut entries = self.entries.write().unwrap();
        entries.remove(key)
    }

    /// 检查是否包含键
    pub fn contains_key(&self, key: &str) -> bool {
        let entries = self.entries.read().unwrap();
        entries.contains_key(key)
    }

    /// 获取所有键
    pub fn keys(&self) -> Vec<String> {
        let entries = self.entries.read().unwrap();
        entries.keys().cloned().collect()
    }

    /// 获取条目数量
    pub fn len(&self) -> usize {
        let entries = self.entries.read().unwrap();
        entries.len()
    }

    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 清空所有条目
    pub fn clear(&self) {
        let mut entries = self.entries.write().unwrap();
        entries.clear();
    }

    /// 迭代所有条目
    pub fn iter(&self) -> impl Iterator<Item = (String, BaggageEntry)> {
        let entries = self.entries.read().unwrap();
        entries.clone().into_iter()
    }
}

impl Default for Baggage {
    fn default() -> Self {
        Self::new()
    }
}
```

---

## Baggage API

### 1. 设置和获取

```rust
use opentelemetry::{baggage::BaggageExt, Context};

/// 设置 Baggage
pub fn set_baggage_example() {
    // 获取当前上下文
    let cx = Context::current();

    // 设置 Baggage
    let cx = cx.with_baggage(vec![
        ("user.id".to_string(), "user-123".to_string()),
        ("request.priority".to_string(), "high".to_string()),
    ]);

    // 使该上下文生效
    let _guard = cx.attach();

    // 在此作用域内，Baggage 会自动传播
    do_work();
}

/// 获取 Baggage
pub fn get_baggage_example() {
    let cx = Context::current();
    
    // 获取特定键的值
    if let Some(user_id) = cx.baggage().get("user.id") {
        println!("User ID: {}", user_id);
    }

    // 获取所有 Baggage
    for (key, value) in cx.baggage().iter() {
        println!("{}: {}", key, value);
    }
}

fn do_work() {
    // Baggage 在此函数中自动可用
    let cx = Context::current();
    if let Some(priority) = cx.baggage().get("request.priority") {
        println!("Processing with priority: {}", priority);
    }
}
```

### 2. 传播机制

```rust
use opentelemetry::propagation::{TextMapPropagator, Extractor, Injector};

/// 自定义 Baggage 传播器
pub struct BaggagePropagator;

impl TextMapPropagator for BaggagePropagator {
    fn inject_context(&self, cx: &Context, injector: &mut dyn Injector) {
        let baggage = cx.baggage();
        
        // 编码为 W3C Baggage 格式
        let encoded = encode_baggage(baggage);
        injector.set("baggage", encoded);
    }

    fn extract_with_context(
        &self,
        cx: &Context,
        extractor: &dyn Extractor,
    ) -> Context {
        if let Some(baggage_header) = extractor.get("baggage") {
            let baggage = decode_baggage(baggage_header);
            cx.with_baggage(baggage)
        } else {
            cx.clone()
        }
    }

    fn fields(&self) -> Vec<String> {
        vec!["baggage".to_string()]
    }
}

/// 编码 Baggage 为 W3C 格式
fn encode_baggage(baggage: &opentelemetry::baggage::Baggage) -> String {
    baggage
        .iter()
        .map(|(key, value)| {
            format!(
                "{}={}",
                urlencoding::encode(key),
                urlencoding::encode(value)
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// 解码 W3C Baggage 格式
fn decode_baggage(header: &str) -> Vec<(String, String)> {
    header
        .split(',')
        .filter_map(|pair| {
            let mut parts = pair.splitn(2, '=');
            let key = parts.next()?.trim();
            let value = parts.next()?.trim();
            
            Some((
                urlencoding::decode(key).ok()?.into_owned(),
                urlencoding::decode(value).ok()?.into_owned(),
            ))
        })
        .collect()
}
```

---

## HTTP 传播

### 1. W3C Baggage Header

```rust
use hyper::header::{HeaderMap, HeaderValue};

/// W3C Baggage Header 名称
pub const BAGGAGE_HEADER: &str = "baggage";

/// 注入 Baggage 到 HTTP Headers
pub fn inject_baggage(headers: &mut HeaderMap, baggage: &Baggage) {
    let entries: Vec<String> = baggage
        .iter()
        .map(|(key, entry)| {
            let encoded_key = urlencoding::encode(&key);
            let encoded_value = urlencoding::encode(entry.value());
            
            if let Some(metadata) = entry.metadata() {
                let metadata_str = format_metadata(metadata);
                format!("{}={};{}", encoded_key, encoded_value, metadata_str)
            } else {
                format!("{}={}", encoded_key, encoded_value)
            }
        })
        .collect();

    if !entries.is_empty() {
        let header_value = entries.join(",");
        if let Ok(value) = HeaderValue::from_str(&header_value) {
            headers.insert(BAGGAGE_HEADER, value);
        }
    }
}

/// 从 HTTP Headers 提取 Baggage
pub fn extract_baggage(headers: &HeaderMap) -> Baggage {
    let baggage = Baggage::new();

    if let Some(header_value) = headers.get(BAGGAGE_HEADER) {
        if let Ok(header_str) = header_value.to_str() {
            for pair in header_str.split(',') {
                if let Some((key, value)) = parse_baggage_entry(pair.trim()) {
                    baggage.set(key, value);
                }
            }
        }
    }

    baggage
}

fn parse_baggage_entry(entry: &str) -> Option<(String, BaggageEntry)> {
    let parts: Vec<&str> = entry.splitn(2, ';').collect();
    let key_value = parts[0];
    
    let mut kv_parts = key_value.splitn(2, '=');
    let key = urlencoding::decode(kv_parts.next()?.trim()).ok()?.into_owned();
    let value = urlencoding::decode(kv_parts.next()?.trim()).ok()?.into_owned();
    
    let mut bag_entry = BaggageEntry::new(value);
    
    if parts.len() > 1 {
        let metadata = parse_metadata(parts[1]);
        bag_entry = bag_entry.with_metadata(metadata);
    }
    
    Some((key, bag_entry))
}

fn format_metadata(metadata: &BaggageMetadata) -> String {
    metadata
        .properties()
        .iter()
        .map(|(k, v)| {
            if let Some(val) = v {
                format!("{}={}", k, val)
            } else {
                k.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(";")
}

fn parse_metadata(metadata_str: &str) -> BaggageMetadata {
    let mut metadata = BaggageMetadata::new();
    
    for prop in metadata_str.split(';') {
        let mut parts = prop.splitn(2, '=');
        let key = parts.next().unwrap().trim().to_string();
        let value = parts.next().map(|v| v.trim().to_string());
        metadata = metadata.with_property(key, value);
    }
    
    metadata
}
```

### 2. HTTP 客户端集成

```rust
use reqwest::Client;
use opentelemetry::Context;

/// HTTP 客户端中间件
pub async fn http_client_with_baggage(url: &str) -> Result<String, reqwest::Error> {
    let client = Client::new();
    let cx = Context::current();
    
    // 创建请求
    let mut request = client.get(url).build()?;
    
    // 注入 Baggage
    let baggage = create_baggage_from_context(&cx);
    inject_baggage(request.headers_mut(), &baggage);
    
    // 发送请求
    let response = client.execute(request).await?;
    let body = response.text().await?;
    
    Ok(body)
}

fn create_baggage_from_context(cx: &Context) -> Baggage {
    let baggage = Baggage::new();
    
    // 从 OpenTelemetry Context 提取 Baggage
    for (key, value) in cx.baggage().iter() {
        baggage.set(key.to_string(), BaggageEntry::new(value.to_string()));
    }
    
    baggage
}
```

### 3. HTTP 服务器集成

```rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
};

/// Axum 中间件：提取 Baggage
pub async fn baggage_middleware(request: Request, next: Next) -> Response {
    // 提取 Baggage
    let baggage = extract_baggage(request.headers());
    
    // 创建新的上下文
    let mut cx = Context::current();
    for (key, entry) in baggage.iter() {
        cx = cx.with_value(key, entry.value().to_string());
    }
    
    // 设置上下文
    let _guard = cx.attach();
    
    // 继续处理请求
    next.run(request).await
}

/// 使用示例
pub fn create_app() -> axum::Router {
    axum::Router::new()
        .route("/", axum::routing::get(handler))
        .layer(middleware::from_fn(baggage_middleware))
}

async fn handler() -> &'static str {
    let cx = Context::current();
    
    // 从 Baggage 获取用户 ID
    if let Some(user_id) = cx.baggage().get("user.id") {
        println!("Handling request for user: {}", user_id);
    }
    
    "Hello, World!"
}
```

---

## gRPC 传播

### gRPC 元数据集成

```rust
use tonic::{
    metadata::{MetadataMap, MetadataValue},
    Request, Status,
};

/// 注入 Baggage 到 gRPC 元数据
pub fn inject_baggage_grpc(metadata: &mut MetadataMap, baggage: &Baggage) {
    let entries: Vec<String> = baggage
        .iter()
        .map(|(key, entry)| {
            format!("{}={}", key, entry.value())
        })
        .collect();

    if !entries.is_empty() {
        let header_value = entries.join(",");
        if let Ok(value) = MetadataValue::try_from(header_value) {
            metadata.insert("baggage", value);
        }
    }
}

/// 从 gRPC 元数据提取 Baggage
pub fn extract_baggage_grpc(metadata: &MetadataMap) -> Baggage {
    let baggage = Baggage::new();

    if let Some(header_value) = metadata.get("baggage") {
        if let Ok(header_str) = header_value.to_str() {
            for pair in header_str.split(',') {
                let mut parts = pair.splitn(2, '=');
                if let (Some(key), Some(value)) = (parts.next(), parts.next()) {
                    baggage.set(
                        key.trim().to_string(),
                        BaggageEntry::new(value.trim()),
                    );
                }
            }
        }
    }

    baggage
}

/// gRPC 拦截器示例
pub async fn grpc_interceptor(
    mut request: Request<()>,
) -> Result<Request<()>, Status> {
    // 提取 Baggage
    let baggage = extract_baggage_grpc(request.metadata());
    
    // 设置上下文
    let mut cx = Context::current();
    for (key, entry) in baggage.iter() {
        cx = cx.with_value(key, entry.value().to_string());
    }
    
    let _guard = cx.attach();
    
    Ok(request)
}
```

---

## 使用场景

### 1. 用户标识传播

```rust
/// 在整个请求链路中传播用户信息
pub fn propagate_user_context(user_id: &str, tenant_id: &str) {
    let cx = Context::current();
    
    let cx = cx.with_baggage(vec![
        ("user.id".to_string(), user_id.to_string()),
        ("tenant.id".to_string(), tenant_id.to_string()),
    ]);
    
    let _guard = cx.attach();
    
    // 调用下游服务
    call_downstream_service();
}

fn call_downstream_service() {
    let cx = Context::current();
    
    // 自动获取用户上下文
    if let Some(user_id) = cx.baggage().get("user.id") {
        println!("Processing for user: {}", user_id);
    }
    
    if let Some(tenant_id) = cx.baggage().get("tenant.id") {
        println!("Tenant: {}", tenant_id);
    }
}
```

### 2. A/B 测试

```rust
/// A/B 测试变体传播
#[derive(Debug, Clone, Copy)]
pub enum ExperimentVariant {
    A,
    B,
}

impl ExperimentVariant {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::A => "A",
            Self::B => "B",
        }
    }
}

pub fn set_experiment_variant(variant: ExperimentVariant) {
    let cx = Context::current();
    
    let cx = cx.with_baggage(vec![(
        "experiment.variant".to_string(),
        variant.as_str().to_string(),
    )]);
    
    let _guard = cx.attach();
    
    // 所有下游服务都会收到相同的变体
    process_with_variant();
}

fn process_with_variant() {
    let cx = Context::current();
    
    if let Some(variant) = cx.baggage().get("experiment.variant") {
        match variant.as_str() {
            "A" => println!("Using variant A logic"),
            "B" => println!("Using variant B logic"),
            _ => println!("Unknown variant"),
        }
    }
}
```

### 3. 请求优先级

```rust
/// 请求优先级传播
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RequestPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

impl RequestPriority {
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "low" => Some(Self::Low),
            "normal" => Some(Self::Normal),
            "high" => Some(Self::High),
            "critical" => Some(Self::Critical),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Low => "low",
            Self::Normal => "normal",
            Self::High => "high",
            Self::Critical => "critical",
        }
    }
}

pub fn set_request_priority(priority: RequestPriority) {
    let cx = Context::current();
    
    let cx = cx.with_baggage(vec![(
        "request.priority".to_string(),
        priority.as_str().to_string(),
    )]);
    
    let _guard = cx.attach();
    
    process_with_priority();
}

fn process_with_priority() {
    let cx = Context::current();
    
    if let Some(priority_str) = cx.baggage().get("request.priority") {
        if let Some(priority) = RequestPriority::from_str(&priority_str) {
            match priority {
                RequestPriority::Critical => {
                    println!("Processing critical request immediately");
                }
                RequestPriority::High => {
                    println!("Processing high priority request");
                }
                _ => {
                    println!("Processing normal request");
                }
            }
        }
    }
}
```

---

## 性能优化

### 1. 大小限制

```rust
/// Baggage 大小限制（字节）
pub const MAX_BAGGAGE_SIZE: usize = 8192; // 8KB

/// 验证 Baggage 大小
pub fn validate_baggage_size(baggage: &Baggage) -> Result<(), String> {
    let encoded = encode_baggage_internal(baggage);
    
    if encoded.len() > MAX_BAGGAGE_SIZE {
        return Err(format!(
            "Baggage size {} exceeds maximum {}",
            encoded.len(),
            MAX_BAGGAGE_SIZE
        ));
    }
    
    Ok(())
}

fn encode_baggage_internal(baggage: &Baggage) -> String {
    baggage
        .iter()
        .map(|(key, entry)| format!("{}={}", key, entry.value()))
        .collect::<Vec<_>>()
        .join(",")
}
```

### 2. 编码优化

```rust
use std::borrow::Cow;

/// 高效的 URL 编码
pub fn efficient_encode(input: &str) -> Cow<str> {
    // 检查是否需要编码
    if input.chars().all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.') {
        Cow::Borrowed(input)
    } else {
        Cow::Owned(urlencoding::encode(input).into_owned())
    }
}
```

---

## 安全考虑

### 1. 敏感数据过滤

```rust
/// 敏感数据过滤器
pub struct BaggageFilter {
    blocked_keys: Vec<String>,
}

impl BaggageFilter {
    pub fn new() -> Self {
        Self {
            blocked_keys: vec![
                "password".to_string(),
                "token".to_string(),
                "api_key".to_string(),
                "secret".to_string(),
            ],
        }
    }

    pub fn with_blocked_key(mut self, key: impl Into<String>) -> Self {
        self.blocked_keys.push(key.into());
        self
    }

    /// 过滤 Baggage
    pub fn filter(&self, baggage: &Baggage) -> Baggage {
        let filtered = Baggage::new();
        
        for (key, entry) in baggage.iter() {
            if !self.is_blocked(&key) {
                filtered.set(key, entry);
            }
        }
        
        filtered
    }

    fn is_blocked(&self, key: &str) -> bool {
        self.blocked_keys.iter().any(|blocked| {
            key.to_lowercase().contains(&blocked.to_lowercase())
        })
    }
}
```

### 2. 大小验证

```rust
/// 验证单个条目大小
pub fn validate_entry_size(key: &str, value: &str) -> Result<(), String> {
    const MAX_KEY_SIZE: usize = 256;
    const MAX_VALUE_SIZE: usize = 4096;

    if key.len() > MAX_KEY_SIZE {
        return Err(format!("Key size {} exceeds maximum {}", key.len(), MAX_KEY_SIZE));
    }

    if value.len() > MAX_VALUE_SIZE {
        return Err(format!("Value size {} exceeds maximum {}", value.len(), MAX_VALUE_SIZE));
    }

    Ok(())
}
```

---

## 最佳实践

### 1. 键命名约定

```rust
// ✅ 推荐: 使用命名空间
"user.id"
"request.priority"
"experiment.variant"
"tenant.id"

// ❌ 避免: 无命名空间
"userId"
"priority"
"variant"
```

### 2. 值大小控制

```rust
// ✅ 推荐: 简短的标识符
baggage.set("user.id", BaggageEntry::new("user-123"));

// ❌ 避免: 大型数据结构
baggage.set("user.data", BaggageEntry::new(serde_json::to_string(&large_object)?));
```

### 3. 生命周期管理

```rust
// ✅ 推荐: 在请求边界设置和清除
pub async fn handle_request() {
    let cx = Context::current();
    let cx = cx.with_baggage(vec![("request.id".to_string(), "req-123".to_string())]);
    let _guard = cx.attach();
    
    // 处理请求
    process_request().await;
    
    // guard 离开作用域时自动清除
}
```

---

## 完整示例

### 微服务链路追踪

```rust
use anyhow::Result;
use opentelemetry::{baggage::BaggageExt, Context};
use tracing::{info, instrument};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化追踪
    init_tracing()?;

    // 设置初始 Baggage
    let cx = Context::current();
    let cx = cx.with_baggage(vec![
        ("user.id".to_string(), "user-123".to_string()),
        ("tenant.id".to_string(), "tenant-456".to_string()),
        ("request.priority".to_string(), "high".to_string()),
    ]);

    let _guard = cx.attach();

    // 处理请求链路
    api_gateway_handler().await?;

    Ok(())
}

#[instrument]
async fn api_gateway_handler() -> Result<()> {
    info!("API Gateway: Processing request");
    
    let cx = Context::current();
    if let Some(user_id) = cx.baggage().get("user.id") {
        info!(user_id = %user_id, "User identified");
    }

    // 调用订单服务
    order_service_handler().await?;
    
    Ok(())
}

#[instrument]
async fn order_service_handler() -> Result<()> {
    info!("Order Service: Processing order");
    
    let cx = Context::current();
    let priority = cx.baggage().get("request.priority").unwrap_or("normal".to_string());
    info!(priority = %priority, "Request priority");

    // 调用支付服务
    payment_service_handler().await?;
    
    Ok(())
}

#[instrument]
async fn payment_service_handler() -> Result<()> {
    info!("Payment Service: Processing payment");
    
    let cx = Context::current();
    let tenant_id = cx.baggage().get("tenant.id").unwrap_or("default".to_string());
    info!(tenant_id = %tenant_id, "Tenant identified");

    Ok(())
}

fn init_tracing() -> Result<()> {
    // 初始化追踪（简化版）
    tracing_subscriber::fmt::init();
    Ok(())
}
```

---

## 总结

本文档提供了 OpenTelemetry Baggage 在 Rust 1.90 环境下的完整类型安全实现：

1. ✅ **类型定义**: BaggageEntry、BaggageMetadata、Baggage 容器
2. ✅ **传播机制**: W3C Baggage 标准、HTTP/gRPC 集成
3. ✅ **使用场景**: 用户标识、A/B 测试、请求优先级
4. ✅ **性能优化**: 大小限制、编码优化
5. ✅ **安全考虑**: 敏感数据过滤、大小验证
6. ✅ **最佳实践**: 命名约定、生命周期管理

通过本文档的指导，您可以在 Rust 微服务架构中安全、高效地使用 Baggage 传播上下文信息。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
