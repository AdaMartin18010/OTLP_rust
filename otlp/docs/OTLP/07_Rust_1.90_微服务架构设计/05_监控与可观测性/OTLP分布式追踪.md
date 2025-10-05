# OTLP 分布式追踪 - Rust 1.90 微服务架构设计

## 目录

- [OTLP 分布式追踪 - Rust 1.90 微服务架构设计](#otlp-分布式追踪---rust-190-微服务架构设计)
  - [目录](#目录)
  - [🎯 概述](#-概述)
  - [🏗️ 架构设计](#️-架构设计)
    - [整体架构图](#整体架构图)
  - [🔧 核心组件实现](#-核心组件实现)
    - [1. 追踪上下文管理](#1-追踪上下文管理)
    - [2. 分布式追踪中间件](#2-分布式追踪中间件)
    - [3. 数据库追踪集成](#3-数据库追踪集成)
    - [4. 外部服务调用追踪](#4-外部服务调用追踪)
  - [🔌 追踪数据导出](#-追踪数据导出)
    - [1. OTLP导出器配置](#1-otlp导出器配置)
    - [2. 自定义导出器](#2-自定义导出器)
  - [🚀 使用示例](#-使用示例)
    - [1. 完整的微服务追踪示例](#1-完整的微服务追踪示例)
  - [📊 性能优化](#-性能优化)
    - [1. 采样策略优化](#1-采样策略优化)
    - [2. 批量导出优化](#2-批量导出优化)
  - [📚 参考资料](#-参考资料)

## 🎯 概述

分布式追踪是微服务架构中实现可观测性的核心技术，通过OpenTelemetry Protocol (OTLP)可以实现跨服务的请求追踪。
本文将详细介绍基于Rust 1.90和OTLP的分布式追踪系统的设计与实现。

## 🏗️ 架构设计

### 整体架构图

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   服务A          │    │   服务B         │    │   服务C         │
│  (Service A)    │    │  (Service B)    │    │  (Service C)    │
│                 │    │                 │    │                 │
│ ┌─────────────┐ │    │ ┌─────────────┐ │    │ ┌─────────────┐ │
│ │   Span 1    │ │──▶│ │   Span 2    │ │───▶│ │   Span 3    │ │
│ │  (HTTP)     │ │    │ │ (Database)  │ │    │ │  (Cache)    │ │
│ └─────────────┘ │    │ └─────────────┘ │    │ └─────────────┘ │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
                    ┌─────────────────┐
                    │   OTLP导出器     │
                    │  (Exporter)     │
                    │                 │
                    │ • gRPC导出      │
                    │ • HTTP导出      │
                    │ • 批量处理      │
                    └─────────────────┘
                                 │
                    ┌─────────────────┐
                    │   收集器集群     │
                    │ (Collector)     │
                    │                 │
                    │ • Jaeger        │
                    │ • Zipkin        │
                    │ • 自定义后端     │
                    └─────────────────┘
```

## 🔧 核心组件实现

### 1. 追踪上下文管理

```rust
use std::sync::Arc;
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, TraceContextExt, TraceState},
    Context, KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, error};
use tokio::sync::RwLock;

/// 追踪上下文管理器
pub struct TraceContextManager {
    tracer: Tracer,
    context_store: Arc<RwLock<HashMap<String, Context>>>,
    span_store: Arc<RwLock<HashMap<String, Span>>>,
    propagation_config: PropagationConfig,
}

/// 传播配置
#[derive(Debug, Clone)]
pub struct PropagationConfig {
    pub trace_context_header: String,
    pub baggage_header: String,
    pub custom_headers: HashMap<String, String>,
}

/// 追踪配置
#[derive(Debug, Clone)]
pub struct TracingConfig {
    pub service_name: String,
    pub service_version: String,
    pub environment: String,
    pub sampling_ratio: f64,
    pub export_batch_size: usize,
    pub export_timeout: Duration,
    pub otlp_endpoint: String,
    pub otlp_protocol: OTLPProtocol,
}

/// OTLP协议类型
#[derive(Debug, Clone)]
pub enum OTLPProtocol {
    Grpc,
    HttpJson,
    HttpProtobuf,
}

impl TraceContextManager {
    /// 创建新的追踪上下文管理器
    pub async fn new(config: TracingConfig) -> Result<Self, TracingError> {
        let tracer = Self::create_tracer(&config).await?;
        
        let propagation_config = PropagationConfig {
            trace_context_header: "traceparent".to_string(),
            baggage_header: "baggage".to_string(),
            custom_headers: HashMap::new(),
        };

        Ok(Self {
            tracer,
            context_store: Arc::new(RwLock::new(HashMap::new())),
            span_store: Arc::new(RwLock::new(HashMap::new())),
            propagation_config,
        })
    }

    /// 创建追踪器
    async fn create_tracer(config: &TracingConfig) -> Result<Tracer, TracingError> {
        let resource = Resource::new(vec![
            KeyValue::new("service.name", config.service_name.clone()),
            KeyValue::new("service.version", config.service_version.clone()),
            KeyValue::new("deployment.environment", config.environment.clone()),
        ]);

        let exporter = match config.otlp_protocol {
            OTLPProtocol::Grpc => {
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint(&config.otlp_endpoint)
                    .with_timeout(config.export_timeout)
            }
            OTLPProtocol::HttpJson => {
                opentelemetry_otlp::new_exporter()
                    .http()
                    .with_endpoint(&config.otlp_endpoint)
                    .with_timeout(config.export_timeout)
            }
            OTLPProtocol::HttpProtobuf => {
                opentelemetry_otlp::new_exporter()
                    .http()
                    .with_endpoint(&config.otlp_endpoint)
                    .with_timeout(config.export_timeout)
            }
        };

        let provider = trace::TracerProvider::builder()
            .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
            .with_resource(resource)
            .with_sampler(Sampler::TraceIdRatioBased(config.sampling_ratio))
            .with_id_generator(RandomIdGenerator::default())
            .build();

        let tracer = provider.tracer("otlp-rust", Some(env!("CARGO_PKG_VERSION")));
        global::set_tracer_provider(provider);

        Ok(tracer)
    }

    /// 创建根span
    pub fn create_root_span(&self, name: &str, kind: SpanKind) -> Span {
        let span = self.tracer
            .span_builder(name)
            .with_kind(kind)
            .with_attributes(vec![
                KeyValue::new("span.type", "root"),
                KeyValue::new("span.kind", format!("{:?}", kind)),
            ])
            .start(&self.tracer);

        info!(
            span_name = %name,
            trace_id = %span.span_context().trace_id(),
            span_id = %span.span_context().span_id(),
            "Root span created"
        );

        span
    }

    /// 创建子span
    pub fn create_child_span(&self, name: &str, parent_context: &Context, kind: SpanKind) -> Span {
        let span = self.tracer
            .span_builder(name)
            .with_kind(kind)
            .with_parent_context(parent_context)
            .with_attributes(vec![
                KeyValue::new("span.type", "child"),
                KeyValue::new("span.kind", format!("{:?}", kind)),
            ])
            .start(&self.tracer);

        info!(
            span_name = %name,
            trace_id = %span.span_context().trace_id(),
            span_id = %span.span_context().span_id(),
            parent_span_id = %parent_context.span().span_context().span_id(),
            "Child span created"
        );

        span
    }

    /// 从HTTP头中提取追踪上下文
    pub fn extract_context_from_headers(&self, headers: &HashMap<String, String>) -> Context {
        let mut context = Context::current();

        // 提取traceparent头
        if let Some(traceparent) = headers.get(&self.propagation_config.trace_context_header) {
            if let Ok(span_context) = self.parse_traceparent(traceparent) {
                context = context.with_remote_span_context(span_context);
            }
        }

        // 提取baggage头
        if let Some(baggage) = headers.get(&self.propagation_config.baggage_header) {
            context = self.parse_baggage(&context, baggage);
        }

        context
    }

    /// 将追踪上下文注入到HTTP头中
    pub fn inject_context_to_headers(&self, context: &Context, headers: &mut HashMap<String, String>) {
        let span_context = context.span().span_context();
        
        // 注入traceparent头
        let traceparent = format!(
            "00-{}-{}-{:02x}",
            span_context.trace_id(),
            span_context.span_id(),
            if span_context.is_sampled() { 1 } else { 0 }
        );
        headers.insert(self.propagation_config.trace_context_header.clone(), traceparent);

        // 注入baggage头
        if let Some(baggage) = context.baggage().get("baggage") {
            headers.insert(self.propagation_config.baggage_header.clone(), baggage.to_string());
        }
    }

    /// 解析traceparent头
    fn parse_traceparent(&self, traceparent: &str) -> Result<opentelemetry::trace::SpanContext, TracingError> {
        let parts: Vec<&str> = traceparent.split('-').collect();
        if parts.len() != 4 {
            return Err(TracingError::InvalidTraceParent);
        }

        let trace_id = parts[1].parse::<u128>()?;
        let span_id = parts[2].parse::<u64>()?;
        let flags = u8::from_str_radix(parts[3], 16)?;

        Ok(opentelemetry::trace::SpanContext::new(
            trace_id,
            span_id,
            flags & 1 != 0,
            TraceState::default(),
        ))
    }

    /// 解析baggage头
    fn parse_baggage(&self, context: &Context, baggage: &str) -> Context {
        let mut new_context = context.clone();
        
        for item in baggage.split(',') {
            if let Some((key, value)) = item.split_once('=') {
                new_context = new_context.with_baggage(vec![KeyValue::new(key.trim(), value.trim())]);
            }
        }

        new_context
    }

    /// 存储追踪上下文
    pub async fn store_context(&self, key: String, context: Context) {
        let mut store = self.context_store.write().await;
        store.insert(key, context);
    }

    /// 获取追踪上下文
    pub async fn get_context(&self, key: &str) -> Option<Context> {
        let store = self.context_store.read().await;
        store.get(key).cloned()
    }

    /// 删除追踪上下文
    pub async fn remove_context(&self, key: &str) {
        let mut store = self.context_store.write().await;
        store.remove(key);
    }
}
```

### 2. 分布式追踪中间件

```rust
use axum::{
    extract::{Request, State},
    middleware::Next,
    response::Response,
    http::{HeaderMap, HeaderName, HeaderValue},
};
use std::time::Instant;

/// Axum追踪中间件
pub async fn tracing_middleware(
    State(state): State<Arc<AppState>>,
    mut request: Request,
    next: Next,
) -> Response {
    let start_time = Instant::now();
    
    // 提取追踪上下文
    let headers = extract_headers(&request);
    let context = state.trace_manager.extract_context_from_headers(&headers);
    
    // 创建HTTP请求span
    let span = state.trace_manager.create_child_span(
        "http_request",
        &context,
        SpanKind::Server,
    );

    let _guard = span.enter();
    
    // 添加请求信息到span
    if let Some(uri) = request.uri().path_and_query() {
        span.set_attribute(KeyValue::new("http.url", uri.to_string()));
    }
    
    if let Some(method) = request.method().as_str().parse::<String>().ok() {
        span.set_attribute(KeyValue::new("http.method", method));
    }

    // 处理请求
    let response = next.run(request).await;
    
    // 记录响应信息
    let duration = start_time.elapsed();
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    span.set_attribute(KeyValue::new("http.response.duration_ms", duration.as_millis() as i64));
    
    // 设置span状态
    if response.status().is_success() {
        span.set_status(Status::Ok);
    } else {
        span.set_status(Status::Error);
    }

    response
}

/// 提取HTTP头
fn extract_headers(request: &Request) -> HashMap<String, String> {
    let mut headers = HashMap::new();
    
    for (key, value) in request.headers() {
        if let Ok(value_str) = value.to_str() {
            headers.insert(key.as_str().to_string(), value_str.to_string());
        }
    }
    
    headers
}

/// gRPC追踪拦截器
pub struct TracingInterceptor;

impl tonic::service::Interceptor for TracingInterceptor {
    fn call(&mut self, mut request: tonic::Request<()>) -> Result<tonic::Request<()>, tonic::Status> {
        let start_time = Instant::now();
        
        // 提取追踪上下文
        let metadata = request.metadata();
        let headers = extract_grpc_metadata(metadata);
        
        // 创建gRPC请求span
        let context = Context::current();
        let span = global::tracer("grpc-client")
            .span_builder("grpc_request")
            .with_kind(SpanKind::Client)
            .with_parent_context(&context)
            .with_attributes(vec![
                KeyValue::new("rpc.method", request.get_ref().type_url()),
                KeyValue::new("rpc.system", "grpc"),
            ])
            .start(&global::tracer("grpc-client"));

        let _guard = span.enter();
        
        // 注入追踪上下文到gRPC元数据
        inject_grpc_metadata(request.metadata_mut(), &context);
        
        Ok(request)
    }
}

/// 提取gRPC元数据
fn extract_grpc_metadata(metadata: &tonic::metadata::MetadataMap) -> HashMap<String, String> {
    let mut headers = HashMap::new();
    
    for (key, value) in metadata {
        if let Ok(key_str) = key.to_string().parse::<String>() {
            if let Ok(value_str) = value.to_str() {
                headers.insert(key_str, value_str.to_string());
            }
        }
    }
    
    headers
}

/// 注入gRPC元数据
fn inject_grpc_metadata(metadata: &mut tonic::metadata::MetadataMap, context: &Context) {
    let span_context = context.span().span_context();
    
    // 注入traceparent
    let traceparent = format!(
        "00-{}-{}-{:02x}",
        span_context.trace_id(),
        span_context.span_id(),
        if span_context.is_sampled() { 1 } else { 0 }
    );
    
    if let Ok(header_value) = traceparent.parse::<HeaderValue>() {
        metadata.insert("traceparent", header_value);
    }
}
```

### 3. 数据库追踪集成

```rust
use sqlx::{Pool, Postgres, Row};
use opentelemetry::trace::{Tracer, SpanKind, Status};

/// 数据库追踪包装器
pub struct TracedDatabase {
    pool: Pool<Postgres>,
    tracer: Tracer,
}

impl TracedDatabase {
    pub fn new(pool: Pool<Postgres>) -> Self {
        Self {
            pool,
            tracer: global::tracer("database"),
        }
    }

    /// 执行查询并记录追踪
    pub async fn query<F, R>(&self, query_name: &str, query: F) -> Result<R, sqlx::Error>
    where
        F: FnOnce(&Pool<Postgres>) -> BoxFuture<'_, Result<R, sqlx::Error>>,
    {
        let span = self.tracer
            .span_builder(query_name)
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "postgresql"),
                KeyValue::new("db.operation", query_name),
            ])
            .start(&self.tracer);

        let _guard = span.enter();
        
        let start_time = Instant::now();
        let result = query(&self.pool).await;
        let duration = start_time.elapsed();

        // 记录查询结果
        span.set_attribute(KeyValue::new("db.query.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(_) => {
                span.set_status(Status::Ok);
            }
            Err(e) => {
                span.set_status(Status::Error);
                span.set_attribute(KeyValue::new("db.error", e.to_string()));
            }
        }

        result
    }

    /// 执行事务并记录追踪
    pub async fn transaction<F, R>(&self, transaction_name: &str, f: F) -> Result<R, sqlx::Error>
    where
        F: FnOnce(sqlx::Transaction<'_, Postgres>) -> BoxFuture<'_, Result<(R, sqlx::Transaction<'_, Postgres>), sqlx::Error>>,
    {
        let span = self.tracer
            .span_builder(transaction_name)
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "postgresql"),
                KeyValue::new("db.operation", "transaction"),
            ])
            .start(&self.tracer);

        let _guard = span.enter();
        
        let start_time = Instant::now();
        let mut tx = self.pool.begin().await?;
        let (result, tx) = f(tx).await?;
        
        match tx.commit().await {
            Ok(_) => {
                span.set_status(Status::Ok);
                span.set_attribute(KeyValue::new("db.transaction.status", "committed"));
            }
            Err(e) => {
                span.set_status(Status::Error);
                span.set_attribute(KeyValue::new("db.transaction.status", "rolled_back"));
                span.set_attribute(KeyValue::new("db.error", e.to_string()));
            }
        }

        let duration = start_time.elapsed();
        span.set_attribute(KeyValue::new("db.transaction.duration_ms", duration.as_millis() as i64));

        Ok(result)
    }
}
```

### 4. 外部服务调用追踪

```rust
use reqwest::Client;
use opentelemetry::trace::{Tracer, SpanKind, Status};

/// 追踪HTTP客户端
pub struct TracedHttpClient {
    client: Client,
    tracer: Tracer,
}

impl TracedHttpClient {
    pub fn new() -> Self {
        Self {
            client: Client::new(),
            tracer: global::tracer("http-client"),
        }
    }

    /// 执行HTTP请求并记录追踪
    pub async fn request(&self, method: &str, url: &str) -> Result<reqwest::Response, reqwest::Error> {
        let span = self.tracer
            .span_builder("http_request")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.url", url.to_string()),
                KeyValue::new("http.scheme", "https"),
            ])
            .start(&self.tracer);

        let _guard = span.enter();
        
        let start_time = Instant::now();
        let request = self.client
            .request(method.parse().unwrap(), url)
            .build()?;
        
        let response = self.client.execute(request).await;
        let duration = start_time.elapsed();

        // 记录响应信息
        span.set_attribute(KeyValue::new("http.response.duration_ms", duration.as_millis() as i64));
        
        match &response {
            Ok(resp) => {
                span.set_attribute(KeyValue::new("http.status_code", resp.status().as_u16() as i64));
                span.set_attribute(KeyValue::new("http.response.size", resp.content_length().unwrap_or(0) as i64));
                
                if resp.status().is_success() {
                    span.set_status(Status::Ok);
                } else {
                    span.set_status(Status::Error);
                }
            }
            Err(e) => {
                span.set_status(Status::Error);
                span.set_attribute(KeyValue::new("http.error", e.to_string()));
            }
        }

        response
    }

    /// 执行GET请求
    pub async fn get(&self, url: &str) -> Result<reqwest::Response, reqwest::Error> {
        self.request("GET", url).await
    }

    /// 执行POST请求
    pub async fn post(&self, url: &str) -> Result<reqwest::Response, reqwest::Error> {
        self.request("POST", url).await
    }
}
```

## 🔌 追踪数据导出

### 1. OTLP导出器配置

```rust
/// OTLP导出器配置
#[derive(Debug, Clone)]
pub struct OTLPExporterConfig {
    pub endpoint: String,
    pub protocol: OTLPProtocol,
    pub headers: HashMap<String, String>,
    pub timeout: Duration,
    pub batch_size: usize,
    pub export_timeout: Duration,
    pub max_export_timeout: Duration,
    pub max_queue_size: usize,
}

impl OTLPExporterConfig {
    pub fn new(endpoint: String) -> Self {
        Self {
            endpoint,
            protocol: OTLPProtocol::Grpc,
            headers: HashMap::new(),
            timeout: Duration::from_secs(30),
            batch_size: 512,
            export_timeout: Duration::from_millis(5000),
            max_export_timeout: Duration::from_secs(30),
            max_queue_size: 2048,
        }
    }

    /// 创建gRPC导出器
    pub fn create_grpc_exporter(&self) -> Result<opentelemetry_otlp::SpanExporter, TracingError> {
        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(&self.endpoint)
            .with_timeout(self.timeout)
            .with_headers(self.headers.clone());

        Ok(exporter)
    }

    /// 创建HTTP导出器
    pub fn create_http_exporter(&self) -> Result<opentelemetry_otlp::SpanExporter, TracingError> {
        let exporter = opentelemetry_otlp::new_exporter()
            .http()
            .with_endpoint(&self.endpoint)
            .with_timeout(self.timeout)
            .with_headers(self.headers.clone());

        Ok(exporter)
    }
}
```

### 2. 自定义导出器

```rust
use opentelemetry_sdk::export::trace::{ExportResult, SpanData, SpanExporter};

/// 自定义追踪导出器
pub struct CustomSpanExporter {
    endpoint: String,
    client: reqwest::Client,
    batch_size: usize,
}

impl CustomSpanExporter {
    pub fn new(endpoint: String, batch_size: usize) -> Self {
        Self {
            endpoint,
            client: reqwest::Client::new(),
            batch_size,
        }
    }
}

#[async_trait]
impl SpanExporter for CustomSpanExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        if batch.is_empty() {
            return Ok(());
        }

        let start_time = Instant::now();
        
        // 转换span数据为自定义格式
        let custom_spans: Vec<CustomSpan> = batch
            .into_iter()
            .map(|span_data| CustomSpan::from_span_data(span_data))
            .collect();

        // 发送到自定义端点
        match self.send_spans(custom_spans).await {
            Ok(_) => {
                let duration = start_time.elapsed();
                info!(
                    spans_count = batch.len(),
                    duration_ms = duration.as_millis(),
                    "Spans exported successfully"
                );
                Ok(())
            }
            Err(e) => {
                error!(
                    error = %e,
                    "Failed to export spans"
                );
                Err(opentelemetry_sdk::export::trace::ExportError::from(e))
            }
        }
    }

    fn shutdown(&mut self) {
        info!("Custom span exporter shutdown");
    }
}

impl CustomSpanExporter {
    async fn send_spans(&self, spans: Vec<CustomSpan>) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let payload = serde_json::to_string(&spans)?;
        
        let response = self.client
            .post(&self.endpoint)
            .header("Content-Type", "application/json")
            .body(payload)
            .send()
            .await?;

        if response.status().is_success() {
            Ok(())
        } else {
            Err(format!("Export failed with status: {}", response.status()).into())
        }
    }
}

/// 自定义span格式
#[derive(Debug, Serialize)]
struct CustomSpan {
    trace_id: String,
    span_id: String,
    parent_span_id: Option<String>,
    name: String,
    kind: String,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, String>,
    events: Vec<CustomEvent>,
    status: String,
}

impl CustomSpan {
    fn from_span_data(span_data: SpanData) -> Self {
        Self {
            trace_id: span_data.span_context.trace_id().to_string(),
            span_id: span_data.span_context.span_id().to_string(),
            parent_span_id: span_data.parent_span_id.map(|id| id.to_string()),
            name: span_data.name.to_string(),
            kind: format!("{:?}", span_data.span_kind),
            start_time: span_data.start_time.unix_timestamp_nanos() as u64,
            end_time: span_data.end_time.unix_timestamp_nanos() as u64,
            attributes: span_data.attributes.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            events: vec![], // 简化处理
            status: "Ok".to_string(), // 简化处理
        }
    }
}
```

## 🚀 使用示例

### 1. 完整的微服务追踪示例

```rust
use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde_json::{json, Value};

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub trace_manager: Arc<TraceContextManager>,
    pub db: TracedDatabase,
    pub http_client: TracedHttpClient,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OTLP追踪
    let tracing_config = TracingConfig {
        service_name: "user-service".to_string(),
        service_version: "1.0.0".to_string(),
        environment: "production".to_string(),
        sampling_ratio: 1.0,
        export_batch_size: 512,
        export_timeout: Duration::from_millis(5000),
        otlp_endpoint: "http://localhost:4317".to_string(),
        otlp_protocol: OTLPProtocol::Grpc,
    };

    let trace_manager = Arc::new(TraceContextManager::new(tracing_config).await?);
    
    // 初始化数据库
    let database_url = "postgresql://user:password@localhost/database";
    let pool = sqlx::PgPool::connect(database_url).await?;
    let db = TracedDatabase::new(pool);
    
    // 初始化HTTP客户端
    let http_client = TracedHttpClient::new();

    let app_state = AppState {
        trace_manager,
        db,
        http_client,
    };

    // 创建路由
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user))
        .route("/health", get(health_check))
        .layer(axum::middleware::from_fn_with_state(
            app_state.clone(),
            tracing_middleware,
        ))
        .with_state(app_state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;

    Ok(())
}

/// 获取用户信息
async fn get_user(
    State(state): State<AppState>,
    Path(user_id): Path<String>,
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<Value>, StatusCode> {
    let span = state.trace_manager.create_child_span(
        "get_user",
        &Context::current(),
        SpanKind::Internal,
    );

    let _guard = span.enter();
    
    span.set_attribute(KeyValue::new("user.id", user_id.clone()));
    span.set_attribute(KeyValue::new("operation.name", "get_user"));

    // 从数据库获取用户信息
    let user = state.db
        .query("get_user_by_id", |pool| {
            Box::pin(async move {
                let row = sqlx::query("SELECT * FROM users WHERE id = $1")
                    .bind(&user_id)
                    .fetch_one(pool)
                    .await?;
                
                Ok(User {
                    id: row.get("id"),
                    name: row.get("name"),
                    email: row.get("email"),
                })
            })
        })
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // 调用外部服务获取用户详细信息
    let external_data = state.http_client
        .get(&format!("https://api.external.com/users/{}", user_id))
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    span.set_attribute(KeyValue::new("user.found", true));
    span.set_status(Status::Ok);

    Ok(Json(json!({
        "user": user,
        "external_data": external_data.json::<Value>().await.unwrap_or(json!({}))
    })))
}

/// 创建用户
async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<Value>, StatusCode> {
    let span = state.trace_manager.create_child_span(
        "create_user",
        &Context::current(),
        SpanKind::Internal,
    );

    let _guard = span.enter();
    
    span.set_attribute(KeyValue::new("operation.name", "create_user"));
    span.set_attribute(KeyValue::new("user.email", payload.email.clone()));

    // 在事务中创建用户
    let user = state.db
        .transaction("create_user_transaction", |mut tx| {
            Box::pin(async move {
                // 插入用户
                let row = sqlx::query(
                    "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id, name, email"
                )
                .bind(&payload.name)
                .bind(&payload.email)
                .fetch_one(&mut *tx)
                .await?;

                let user = User {
                    id: row.get("id"),
                    name: row.get("name"),
                    email: row.get("email"),
                };

                // 创建用户配置
                sqlx::query("INSERT INTO user_configs (user_id, settings) VALUES ($1, $2)")
                    .bind(&user.id)
                    .bind("{}")
                    .execute(&mut *tx)
                    .await?;

                Ok((user, tx))
            })
        })
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    span.set_attribute(KeyValue::new("user.created", true));
    span.set_status(Status::Ok);

    Ok(Json(json!({
        "user": user,
        "message": "User created successfully"
    })))
}

/// 健康检查
async fn health_check() -> Result<Json<Value>, StatusCode> {
    Ok(Json(json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339()
    })))
}
```

## 📊 性能优化

### 1. 采样策略优化

```rust
/// 智能采样器
pub struct IntelligentSampler {
    sampling_ratios: HashMap<String, f64>,
    default_ratio: f64,
}

impl IntelligentSampler {
    pub fn new() -> Self {
        let mut sampling_ratios = HashMap::new();
        sampling_ratios.insert("health_check".to_string(), 0.01); // 1%采样
        sampling_ratios.insert("get_user".to_string(), 0.1); // 10%采样
        sampling_ratios.insert("create_user".to_string(), 1.0); // 100%采样

        Self {
            sampling_ratios,
            default_ratio: 0.05, // 5%默认采样
        }
    }

    pub fn get_sampling_ratio(&self, operation_name: &str) -> f64 {
        self.sampling_ratios
            .get(operation_name)
            .copied()
            .unwrap_or(self.default_ratio)
    }
}
```

### 2. 批量导出优化

```rust
/// 优化的批量导出器
pub struct OptimizedBatchExporter {
    batch_size: usize,
    flush_interval: Duration,
    max_queue_size: usize,
    queue: Arc<Mutex<VecDeque<SpanData>>>,
}

impl OptimizedBatchExporter {
    pub fn new(batch_size: usize, flush_interval: Duration) -> Self {
        Self {
            batch_size,
            flush_interval,
            max_queue_size: batch_size * 10,
            queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub async fn start_background_flush(&self) {
        let queue = self.queue.clone();
        let batch_size = self.batch_size;
        let flush_interval = self.flush_interval;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(flush_interval);
            loop {
                interval.tick().await;
                
                let mut batch = Vec::new();
                {
                    let mut queue = queue.lock().await;
                    for _ in 0..batch_size {
                        if let Some(span) = queue.pop_front() {
                            batch.push(span);
                        } else {
                            break;
                        }
                    }
                }

                if !batch.is_empty() {
                    // 导出批次数据
                    self.export_batch(batch).await;
                }
            }
        });
    }

    async fn export_batch(&self, batch: Vec<SpanData>) {
        // 实现批量导出逻辑
        info!("Exporting batch of {} spans", batch.len());
    }
}
```

## 📚 参考资料

1. [OpenTelemetry Tracing](https://opentelemetry.io/docs/concepts/signals/traces/)
2. [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)
3. [Rust OpenTelemetry](https://opentelemetry.io/docs/instrumentation/rust/)
4. [Distributed Tracing Best Practices](https://opentelemetry.io/docs/concepts/distributions/)

---

**注意**: 本文档基于Rust 1.90和OpenTelemetry最新版本，将持续更新以反映技术发展。
