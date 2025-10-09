# Baggage 详解 - Rust 完整版

## 目录

- [Baggage 详解 - Rust 完整版](#baggage-详解---rust-完整版)
  - [目录](#目录)
  - [1. Baggage 概述](#1-baggage-概述)
    - [1.1 什么是 Baggage](#11-什么是-baggage)
    - [1.2 与 Span Attributes 的区别](#12-与-span-attributes-的区别)
  - [2. Baggage 数据结构](#2-baggage-数据结构)
    - [2.1 核心结构](#21-核心结构)
    - [2.2 Baggage Entry](#22-baggage-entry)
  - [3. Baggage API](#3-baggage-api)
    - [3.1 基础操作](#31-基础操作)
    - [3.2 Context 集成](#32-context-集成)
  - [4. Baggage 传播](#4-baggage-传播)
    - [4.1 HTTP 传播](#41-http-传播)
    - [4.2 gRPC 传播](#42-grpc-传播)
    - [4.3 消息队列传播](#43-消息队列传播)
  - [5. 使用场景](#5-使用场景)
    - [5.1 用户信息传播](#51-用户信息传播)
    - [5.2 租户标识](#52-租户标识)
    - [5.3 A/B 测试](#53-ab-测试)
    - [5.4 金丝雀发布](#54-金丝雀发布)
  - [6. 完整示例](#6-完整示例)
    - [6.1 HTTP 服务](#61-http-服务)
    - [6.2 微服务链路](#62-微服务链路)
  - [7. 安全性考虑](#7-安全性考虑)
    - [7.1 敏感信息过滤](#71-敏感信息过滤)
    - [7.2 大小限制](#72-大小限制)
  - [8. 性能优化](#8-性能优化)
    - [8.1 Baggage 缓存](#81-baggage-缓存)
    - [8.2 选择性传播](#82-选择性传播)
  - [9. 监控与调试](#9-监控与调试)
    - [9.1 Baggage 指标](#91-baggage-指标)
    - [9.2 调试输出](#92-调试输出)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 命名规范](#101-命名规范)
    - [10.2 数据类型](#102-数据类型)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Baggage vs Span Attributes](#baggage-vs-span-attributes)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Baggage 概述

### 1.1 什么是 Baggage

````text
Baggage 定义:
- 键值对集合，随 Context 传播
- 跨服务边界传递
- 对所有下游服务可见
- 不记录在 Span 中（除非显式添加）

用途:
1. 用户身份传播 (user_id, tenant_id)
2. 请求元数据 (client_version, feature_flag)
3. 业务上下文 (order_id, session_id)
4. A/B 测试标识
5. 金丝雀部署标记

工作原理:
Client → Service A → Service B → Service C
         ↓           ↓           ↓
      Baggage     Baggage     Baggage
      {user_id}   {user_id}   {user_id}
````

### 1.2 与 Span Attributes 的区别

````text
Baggage vs Span Attributes:

┌──────────────────┬────────────────┬──────────────────┐
│      特性        │    Baggage     │ Span Attributes  │
├──────────────────┼────────────────┼──────────────────┤
│ 传播范围         │ 跨服务传播     │ 仅当前 Span      │
│ 存储位置         │ Context        │ Span             │
│ 数据大小限制     │ 小 (KB 级别)   │ 较大             │
│ 性能开销         │ 高 (网络传输)  │ 低               │
│ 导出到后端       │ 否 (需显式)    │ 是               │
│ 使用场景         │ 上下文传播     │ 追踪数据         │
└──────────────────┴────────────────┴──────────────────┘

示例:
- Baggage: user_id=12345 (所有服务都能访问)
- Span Attribute: http.status_code=200 (仅当前 Span)
````

---

## 2. Baggage 数据结构

### 2.1 核心结构

````rust
use opentelemetry::{
    baggage::{Baggage, BaggageExt},
    Context, KeyValue,
};
use std::collections::HashMap;

/// Baggage 是一个键值对集合
pub struct BaggageExample {
    /// 内部存储
    entries: HashMap<String, BaggageEntry>,
}

/// Baggage Entry 包含值和可选的元数据
pub struct BaggageEntry {
    /// 值
    pub value: String,
    /// 元数据 (可选)
    pub metadata: Option<String>,
}

impl BaggageExample {
    /// 创建空 Baggage
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }
    
    /// 添加条目
    pub fn insert(&mut self, key: String, value: String) {
        self.entries.insert(
            key,
            BaggageEntry {
                value,
                metadata: None,
            },
        );
    }
    
    /// 获取条目
    pub fn get(&self, key: &str) -> Option<&BaggageEntry> {
        self.entries.get(key)
    }
    
    /// 删除条目
    pub fn remove(&mut self, key: &str) -> Option<BaggageEntry> {
        self.entries.remove(key)
    }
}
````

### 2.2 Baggage Entry

````rust
use opentelemetry::baggage::{BaggageMetadata, BaggageEntry};

/// 创建带元数据的 Baggage Entry
pub fn create_entry_with_metadata(
    value: String,
    metadata: String,
) -> BaggageEntry {
    BaggageEntry::new(value, BaggageMetadata::from(metadata))
}

/// 示例: 创建用户信息 Entry
pub fn create_user_entry(user_id: u64, role: &str) -> BaggageEntry {
    let value = user_id.to_string();
    let metadata = format!("role={}", role);
    
    BaggageEntry::new(value, BaggageMetadata::from(metadata))
}
````

---

## 3. Baggage API

### 3.1 基础操作

````rust
use opentelemetry::{baggage::BaggageExt, Context, KeyValue};

/// 添加 Baggage
pub fn add_baggage() {
    // 获取当前 Context
    let cx = Context::current();
    
    // 添加单个 Baggage
    let cx = cx.with_baggage(vec![KeyValue::new("user_id", "12345")]);
    
    // 添加多个 Baggage
    let cx = cx.with_baggage(vec![
        KeyValue::new("user_id", "12345"),
        KeyValue::new("tenant_id", "org-abc"),
        KeyValue::new("session_id", "sess-xyz"),
    ]);
    
    // 附加到当前线程
    let _guard = cx.attach();
}

/// 读取 Baggage
pub fn read_baggage() -> Option<String> {
    let cx = Context::current();
    
    // 获取 Baggage
    let baggage = cx.baggage();
    
    // 读取特定键
    baggage.get("user_id").map(|v| v.to_string())
}

/// 删除 Baggage
pub fn remove_baggage() {
    let cx = Context::current();
    
    // 创建新的 Baggage (不包含 user_id)
    let mut entries: Vec<KeyValue> = cx
        .baggage()
        .iter()
        .filter(|(k, _)| k.as_str() != "user_id")
        .map(|(k, v)| KeyValue::new(k.clone(), v.clone()))
        .collect();
    
    let cx = Context::current().with_baggage(entries);
    let _guard = cx.attach();
}
````

### 3.2 Context 集成

````rust
use opentelemetry::{baggage::BaggageExt, Context};
use tracing::{info, instrument};

#[instrument]
pub async fn process_request(user_id: u64) {
    // 创建包含 Baggage 的 Context
    let cx = Context::current().with_baggage(vec![
        opentelemetry::KeyValue::new("user_id", user_id.to_string()),
    ]);
    
    // 在 Context 中执行
    let _guard = cx.attach();
    
    // 下游服务可以访问 Baggage
    call_downstream_service().await;
}

#[instrument]
async fn call_downstream_service() {
    let cx = Context::current();
    
    // 读取上游传递的 Baggage
    if let Some(user_id) = cx.baggage().get("user_id") {
        info!(user_id = %user_id, "Processing request for user");
    }
}
````

---

## 4. Baggage 传播

### 4.1 HTTP 传播

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
    Router,
};
use opentelemetry::{
    baggage::BaggageExt,
    global,
    propagation::{TextMapPropagator, Extractor, Injector},
    Context,
};
use std::collections::HashMap;

/// HTTP Header Extractor
struct HeaderExtractor<'a> {
    headers: &'a http::HeaderMap,
}

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.headers.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers.keys().map(|k| k.as_str()).collect()
    }
}

/// HTTP Header Injector
struct HeaderInjector<'a> {
    headers: &'a mut http::HeaderMap,
}

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = http::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = http::HeaderValue::from_str(&value) {
                self.headers.insert(name, val);
            }
        }
    }
}

/// 提取 Baggage 中间件
pub async fn extract_baggage_middleware(
    mut request: Request,
    next: Next,
) -> Response {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    
    // 从 HTTP Headers 提取 Context
    let extractor = HeaderExtractor {
        headers: request.headers(),
    };
    let cx = propagator.extract(&extractor);
    
    // 附加到请求
    request.extensions_mut().insert(cx.clone());
    
    // 附加到当前线程
    let _guard = cx.attach();
    
    next.run(request).await
}

/// 注入 Baggage 到 HTTP 客户端
pub async fn inject_baggage_to_request(
    mut request: http::Request<String>,
) -> http::Request<String> {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let cx = Context::current();
    
    // 注入 Context 到 HTTP Headers
    let mut injector = HeaderInjector {
        headers: request.headers_mut(),
    };
    propagator.inject_context(&cx, &mut injector);
    
    request
}
````

**Baggage HTTP Header 格式**:

````text
baggage: user_id=12345,tenant_id=org-abc,session_id=sess-xyz

格式: key1=value1,key2=value2,key3=value3

带元数据:
baggage: user_id=12345;metadata=role:admin,tenant_id=org-abc
````

### 4.2 gRPC 传播

````rust
use tonic::{Request, Status};
use opentelemetry::{
    baggage::BaggageExt,
    global,
    propagation::{TextMapPropagator, Extractor, Injector},
    Context,
};

/// gRPC Metadata Extractor
struct MetadataExtractor<'a> {
    metadata: &'a tonic::metadata::MetadataMap,
}

impl<'a> Extractor for MetadataExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.metadata.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.metadata.keys().map(|k| k.as_str()).collect()
    }
}

/// gRPC Metadata Injector
struct MetadataInjector<'a> {
    metadata: &'a mut tonic::metadata::MetadataMap,
}

impl<'a> Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.metadata.insert(key, val);
            }
        }
    }
}

/// 提取 Baggage (gRPC Server)
pub fn extract_baggage_from_grpc_request<T>(
    request: &Request<T>,
) -> Context {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let extractor = MetadataExtractor {
        metadata: request.metadata(),
    };
    propagator.extract(&extractor)
}

/// 注入 Baggage (gRPC Client)
pub fn inject_baggage_to_grpc_request<T>(
    mut request: Request<T>,
) -> Request<T> {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let cx = Context::current();
    
    let mut injector = MetadataInjector {
        metadata: request.metadata_mut(),
    };
    propagator.inject_context(&cx, &mut injector);
    
    request
}
````

### 4.3 消息队列传播

````rust
use rdkafka::message::{Headers, OwnedHeaders};
use opentelemetry::{
    global,
    propagation::{TextMapPropagator, Extractor, Injector},
    Context,
};

/// Kafka Headers Extractor
struct KafkaHeaderExtractor<'a> {
    headers: &'a dyn Headers,
}

impl<'a> Extractor for KafkaHeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        for header in self.headers.iter() {
            if header.key == key {
                return std::str::from_utf8(header.value.unwrap_or(&[])).ok();
            }
        }
        None
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers.iter().map(|h| h.key).collect()
    }
}

/// Kafka Headers Injector
struct KafkaHeaderInjector {
    headers: OwnedHeaders,
}

impl Injector for KafkaHeaderInjector {
    fn set(&mut self, key: &str, value: String) {
        self.headers = std::mem::take(&mut self.headers)
            .insert(rdkafka::message::Header {
                key,
                value: Some(value.as_bytes()),
            });
    }
}

/// 提取 Baggage (Kafka Consumer)
pub fn extract_baggage_from_kafka_message(
    headers: &dyn Headers,
) -> Context {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let extractor = KafkaHeaderExtractor { headers };
    propagator.extract(&extractor)
}

/// 注入 Baggage (Kafka Producer)
pub fn inject_baggage_to_kafka_message() -> OwnedHeaders {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let cx = Context::current();
    
    let mut injector = KafkaHeaderInjector {
        headers: OwnedHeaders::new(),
    };
    propagator.inject_context(&cx, &mut injector);
    
    injector.headers
}
````

---

## 5. 使用场景

### 5.1 用户信息传播

````rust
use opentelemetry::{baggage::BaggageExt, Context, KeyValue};
use tracing::{info, instrument};

#[instrument]
pub async fn handle_login(username: &str, user_id: u64) {
    // 设置用户 Baggage
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("user_id", user_id.to_string()),
        KeyValue::new("username", username.to_string()),
    ]);
    
    let _guard = cx.attach();
    
    info!(user_id, username, "User logged in");
    
    // 后续所有操作都能访问 user_id
    process_user_data().await;
}

#[instrument]
async fn process_user_data() {
    let cx = Context::current();
    
    if let Some(user_id) = cx.baggage().get("user_id") {
        info!(user_id = %user_id, "Processing user data");
        
        // 调用其他服务时自动传播
        call_payment_service().await;
        call_notification_service().await;
    }
}

#[instrument]
async fn call_payment_service() {
    let cx = Context::current();
    
    // Payment Service 也能访问 user_id
    if let Some(user_id) = cx.baggage().get("user_id") {
        info!(user_id = %user_id, service = "payment", "Processing payment");
    }
}
````

### 5.2 租户标识

````rust
#[instrument]
pub async fn handle_multi_tenant_request(tenant_id: &str) {
    // 设置租户 Baggage
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("tenant_id", tenant_id.to_string()),
    ]);
    
    let _guard = cx.attach();
    
    // 所有下游服务都知道当前租户
    query_database().await;
    call_api().await;
}

#[instrument]
async fn query_database() {
    let cx = Context::current();
    
    if let Some(tenant_id) = cx.baggage().get("tenant_id") {
        info!(tenant_id = %tenant_id, "Querying database for tenant");
        
        // 根据租户过滤数据
        // SELECT * FROM users WHERE tenant_id = ?
    }
}
````

### 5.3 A/B 测试

````rust
#[instrument]
pub async fn handle_request_with_experiment(experiment_id: &str, variant: &str) {
    // 设置实验 Baggage
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("experiment_id", experiment_id.to_string()),
        KeyValue::new("experiment_variant", variant.to_string()),
    ]);
    
    let _guard = cx.attach();
    
    // 根据实验变体选择不同的逻辑
    if variant == "variant_a" {
        process_variant_a().await;
    } else {
        process_variant_b().await;
    }
}

#[instrument]
async fn process_variant_a() {
    let cx = Context::current();
    
    // 记录到 Span Attributes (用于分析)
    if let Some(experiment_id) = cx.baggage().get("experiment_id") {
        let span = tracing::Span::current();
        span.record("experiment_id", experiment_id);
        span.record("experiment_variant", "variant_a");
    }
    
    info!("Processing variant A");
}
````

### 5.4 金丝雀发布

````rust
#[instrument]
pub async fn handle_canary_request(is_canary: bool) {
    // 设置金丝雀标记
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("deployment_type", if is_canary { "canary" } else { "stable" }),
    ]);
    
    let _guard = cx.attach();
    
    // 路由到不同版本的服务
    if is_canary {
        call_canary_service().await;
    } else {
        call_stable_service().await;
    }
}

#[instrument]
async fn call_canary_service() {
    let cx = Context::current();
    
    if let Some(deployment_type) = cx.baggage().get("deployment_type") {
        info!(
            deployment_type = %deployment_type,
            "Routing to canary deployment"
        );
    }
}
````

---

## 6. 完整示例

### 6.1 HTTP 服务

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
    routing::get,
    Router,
};
use opentelemetry::{baggage::BaggageExt, global, Context, KeyValue};
use tracing::{info, instrument};

#[tokio::main]
async fn main() {
    // 初始化 OpenTelemetry
    init_otlp().unwrap();
    
    let app = Router::new()
        .route("/api/user/:user_id", get(handle_user_request))
        .layer(middleware::from_fn(extract_baggage_middleware));
    
    axum::Server::bind(&"0.0.0.0:8080".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}

#[instrument(skip(request))]
async fn handle_user_request(
    axum::extract::Path(user_id): axum::extract::Path<u64>,
    request: Request,
) -> String {
    // 添加用户 Baggage
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("user_id", user_id.to_string()),
        KeyValue::new("request_path", "/api/user"),
    ]);
    
    let _guard = cx.attach();
    
    // 处理请求
    let user_data = fetch_user_data(user_id).await;
    let orders = fetch_user_orders(user_id).await;
    
    format!("User: {:?}, Orders: {:?}", user_data, orders)
}

#[instrument]
async fn fetch_user_data(user_id: u64) -> String {
    let cx = Context::current();
    
    // 读取 Baggage
    if let Some(user_id_baggage) = cx.baggage().get("user_id") {
        info!(user_id = %user_id_baggage, "Fetching user data");
    }
    
    format!("User#{}", user_id)
}

#[instrument]
async fn fetch_user_orders(user_id: u64) -> Vec<String> {
    let cx = Context::current();
    
    // Baggage 自动传播到这里
    if let Some(user_id_baggage) = cx.baggage().get("user_id") {
        info!(user_id = %user_id_baggage, "Fetching user orders");
    }
    
    vec![format!("Order#1 for User#{}", user_id)]
}
````

### 6.2 微服务链路

````rust
use reqwest::Client;
use opentelemetry::{baggage::BaggageExt, Context, KeyValue};
use tracing::{info, instrument};

/// Service A: API Gateway
#[instrument]
pub async fn service_a_handle_request(user_id: u64, tenant_id: &str) {
    // 设置 Baggage
    let cx = Context::current().with_baggage(vec![
        KeyValue::new("user_id", user_id.to_string()),
        KeyValue::new("tenant_id", tenant_id.to_string()),
        KeyValue::new("service", "api-gateway"),
    ]);
    
    let _guard = cx.attach();
    
    info!(user_id, tenant_id, "API Gateway received request");
    
    // 调用 Service B
    service_b_process_order().await;
}

/// Service B: Order Service
#[instrument]
async fn service_b_process_order() {
    let cx = Context::current();
    
    // 读取上游传递的 Baggage
    let user_id = cx.baggage().get("user_id").map(|v| v.to_string());
    let tenant_id = cx.baggage().get("tenant_id").map(|v| v.to_string());
    
    info!(
        user_id = ?user_id,
        tenant_id = ?tenant_id,
        "Order Service processing order"
    );
    
    // 调用 Service C
    service_c_payment().await;
}

/// Service C: Payment Service
#[instrument]
async fn service_c_payment() {
    let cx = Context::current();
    
    // Baggage 继续传播
    let user_id = cx.baggage().get("user_id").map(|v| v.to_string());
    let tenant_id = cx.baggage().get("tenant_id").map(|v| v.to_string());
    
    info!(
        user_id = ?user_id,
        tenant_id = ?tenant_id,
        "Payment Service processing payment"
    );
}
````

---

## 7. 安全性考虑

### 7.1 敏感信息过滤

````rust
use opentelemetry::{baggage::BaggageExt, Context, KeyValue};

/// 敏感字段黑名单
const SENSITIVE_KEYS: &[&str] = &[
    "password",
    "token",
    "api_key",
    "secret",
    "credit_card",
];

/// 过滤敏感 Baggage
pub fn filter_sensitive_baggage(cx: &Context) -> Context {
    let filtered: Vec<KeyValue> = cx
        .baggage()
        .iter()
        .filter(|(k, _)| !is_sensitive_key(k.as_str()))
        .map(|(k, v)| KeyValue::new(k.clone(), v.clone()))
        .collect();
    
    Context::current().with_baggage(filtered)
}

fn is_sensitive_key(key: &str) -> bool {
    SENSITIVE_KEYS.iter().any(|&sensitive| {
        key.to_lowercase().contains(sensitive)
    })
}

/// 脱敏处理
pub fn sanitize_baggage_value(key: &str, value: &str) -> String {
    if is_sensitive_key(key) {
        "***REDACTED***".to_string()
    } else if key == "email" {
        // 脱敏 email
        mask_email(value)
    } else {
        value.to_string()
    }
}

fn mask_email(email: &str) -> String {
    if let Some(at_pos) = email.find('@') {
        let (local, domain) = email.split_at(at_pos);
        if local.len() > 2 {
            format!("{}***{}", &local[..2], domain)
        } else {
            format!("***{}", domain)
        }
    } else {
        "***".to_string()
    }
}
````

### 7.2 大小限制

````rust
/// Baggage 大小限制 (8KB)
const MAX_BAGGAGE_SIZE: usize = 8 * 1024;

/// 检查 Baggage 大小
pub fn check_baggage_size(cx: &Context) -> Result<(), String> {
    let total_size: usize = cx
        .baggage()
        .iter()
        .map(|(k, v)| k.len() + v.len())
        .sum();
    
    if total_size > MAX_BAGGAGE_SIZE {
        Err(format!(
            "Baggage size {} exceeds limit {}",
            total_size, MAX_BAGGAGE_SIZE
        ))
    } else {
        Ok(())
    }
}

/// 限制 Baggage 条目数量
const MAX_BAGGAGE_COUNT: usize = 64;

pub fn check_baggage_count(cx: &Context) -> Result<(), String> {
    let count = cx.baggage().iter().count();
    
    if count > MAX_BAGGAGE_COUNT {
        Err(format!(
            "Baggage count {} exceeds limit {}",
            count, MAX_BAGGAGE_COUNT
        ))
    } else {
        Ok(())
    }
}
````

---

## 8. 性能优化

### 8.1 Baggage 缓存

````rust
use std::sync::Arc;
use dashmap::DashMap;

/// Baggage 缓存
pub struct BaggageCache {
    cache: Arc<DashMap<String, String>>,
}

impl BaggageCache {
    pub fn new() -> Self {
        Self {
            cache: Arc::new(DashMap::new()),
        }
    }
    
    /// 缓存 Baggage 值
    pub fn cache_value(&self, key: String, value: String) {
        self.cache.insert(key, value);
    }
    
    /// 从缓存获取
    pub fn get_cached(&self, key: &str) -> Option<String> {
        self.cache.get(key).map(|v| v.clone())
    }
}
````

### 8.2 选择性传播

````rust
/// 只传播特定前缀的 Baggage
pub fn propagate_selected_baggage(
    cx: &Context,
    prefixes: &[&str],
) -> Context {
    let selected: Vec<KeyValue> = cx
        .baggage()
        .iter()
        .filter(|(k, _)| {
            prefixes.iter().any(|&prefix| k.as_str().starts_with(prefix))
        })
        .map(|(k, v)| KeyValue::new(k.clone(), v.clone()))
        .collect();
    
    Context::current().with_baggage(selected)
}

/// 示例: 只传播 "user." 和 "tenant." 前缀
pub fn propagate_user_tenant_baggage(cx: &Context) -> Context {
    propagate_selected_baggage(cx, &["user.", "tenant."])
}
````

---

## 9. 监控与调试

### 9.1 Baggage 指标

````rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct BaggageMetrics {
    pub propagation_count: Counter<u64>,
    pub baggage_size: Histogram<u64>,
}

impl BaggageMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("baggage");
        
        Self {
            propagation_count: meter
                .u64_counter("baggage.propagation.count")
                .with_description("Number of baggage propagations")
                .build(),
            baggage_size: meter
                .u64_histogram("baggage.size")
                .with_description("Baggage size in bytes")
                .build(),
        }
    }
    
    pub fn record_propagation(&self, size: usize) {
        self.propagation_count.add(1, &[]);
        self.baggage_size.record(size as u64, &[]);
    }
}
````

### 9.2 调试输出

````rust
use tracing::info;

/// 打印当前 Baggage
pub fn debug_baggage() {
    let cx = Context::current();
    let baggage: Vec<(String, String)> = cx
        .baggage()
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    
    info!(baggage_count = baggage.len(), "Current Baggage:");
    for (key, value) in baggage {
        info!("  {} = {}", key, value);
    }
}
````

---

## 10. 最佳实践

### 10.1 命名规范

````text
Baggage 命名规范:

1. 使用点号分隔命名空间
   ✅ user.id, user.role, user.tenant_id
   ❌ userid, UserID, user_id

2. 使用小写字母
   ✅ user.id
   ❌ User.ID, USER.ID

3. 简短且描述性
   ✅ user.id, tenant.id, session.id
   ❌ u, t, s

4. 避免敏感信息
   ❌ user.password, user.token, user.credit_card
   ✅ user.id, user.role

5. 使用前缀分组
   user.*    - 用户相关
   tenant.*  - 租户相关
   request.* - 请求相关
   experiment.* - 实验相关
````

### 10.2 数据类型

````text
Baggage 数据类型:

1. 字符串 (推荐)
   user.id = "12345"
   tenant.id = "org-abc"

2. 数字 (转为字符串)
   user.age = "25"
   order.amount = "99.99"

3. 布尔值 (转为字符串)
   user.premium = "true"
   feature.enabled = "false"

4. 避免复杂类型
   ❌ JSON 对象
   ❌ 数组
   ❌ 二进制数据
````

---

## 总结

### 核心要点

1. **Baggage**: 键值对集合，随 Context 跨服务传播
2. **传播机制**: HTTP/gRPC/消息队列自动传播
3. **使用场景**: 用户信息、租户标识、A/B 测试、金丝雀发布
4. **安全性**: 过滤敏感信息、大小限制 (8KB)
5. **性能**: 选择性传播、缓存优化
6. **命名规范**: 点号分隔、小写字母、简短描述性

### Baggage vs Span Attributes

| 特性 | Baggage | Span Attributes |
|------|---------|----------------|
| 传播范围 | 跨服务传播 | 仅当前 Span |
| 性能开销 | 高 (网络传输) | 低 |
| 大小限制 | 8KB | 较大 |
| 导出到后端 | 否 (需显式) | 是 |
| 使用场景 | 上下文传播 | 追踪数据 |

### 最佳实践清单

- ✅ 使用点号分隔命名空间 (`user.id`)
- ✅ 保持 Baggage 小巧 (< 8KB)
- ✅ 限制条目数量 (< 64)
- ✅ 过滤敏感信息 (password, token)
- ✅ 使用字符串类型
- ✅ 选择性传播 (按前缀)
- ✅ 监控 Baggage 大小
- ✅ 用于用户信息、租户标识
- ✅ 用于 A/B 测试、金丝雀发布
- ❌ 不要传播敏感数据
- ❌ 不要传播大量数据
- ❌ 不要使用复杂类型 (JSON, 数组)

---

**相关文档**:
- [Context Propagation 详解](./04_Context_Propagation详解_Rust完整版.md)
- [HTTP 追踪](../02_Semantic_Conventions/02_追踪属性/01_HTTP_Rust完整版.md)
- [gRPC 追踪](../02_Semantic_Conventions/02_追踪属性/02_gRPC_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)

