# 微服务网格 Rust + OTLP 完整集成（Linkerd & Istio）

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Linkerd**: 2.15+  
> **Istio**: 1.21+  
> **状态**: Production Ready  
> **最后更新**: 2025年10月9日

---

## 目录

- [微服务网格 Rust + OTLP 完整集成（Linkerd \& Istio）](#微服务网格-rust--otlp-完整集成linkerd--istio)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 为什么需要服务网格 + OpenTelemetry](#11-为什么需要服务网格--opentelemetry)
    - [1.2 架构对比](#12-架构对比)
  - [2. Linkerd 集成](#2-linkerd-集成)
    - [2.1 Linkerd 安装与配置](#21-linkerd-安装与配置)
    - [2.2 Rust 服务 Linkerd 集成](#22-rust-服务-linkerd-集成)
    - [2.3 Axum 中间件集成](#23-axum-中间件集成)
  - [3. Istio 集成](#3-istio-集成)
    - [3.1 Istio 安装与配置](#31-istio-安装与配置)
    - [3.2 Rust 服务 Istio 集成](#32-rust-服务-istio-集成)
    - [3.3 Istio VirtualService 追踪](#33-istio-virtualservice-追踪)
  - [4. 服务网格上下文传播](#4-服务网格上下文传播)
    - [4.1 跨服务调用追踪](#41-跨服务调用追踪)
  - [5. mTLS 与安全追踪](#5-mtls-与安全追踪)
    - [5.1 mTLS 元数据追踪](#51-mtls-元数据追踪)
  - [6. 流量管理与追踪](#6-流量管理与追踪)
    - [6.1 金丝雀发布追踪](#61-金丝雀发布追踪)
    - [6.2 A/B 测试追踪](#62-ab-测试追踪)
  - [7. 分布式追踪最佳实践](#7-分布式追踪最佳实践)
    - [7.1 Span 命名规范](#71-span-命名规范)
    - [7.2 采样策略（服务网格环境）](#72-采样策略服务网格环境)
  - [8. 性能优化](#8-性能优化)
    - [8.1 批量导出优化（高流量场景）](#81-批量导出优化高流量场景)
    - [8.2 资源属性缓存](#82-资源属性缓存)
  - [9. 故障注入与混沌工程](#9-故障注入与混沌工程)
    - [9.1 Istio Fault Injection 追踪](#91-istio-fault-injection-追踪)
  - [10. 完整示例](#10-完整示例)
    - [10.1 Linkerd 完整服务](#101-linkerd-完整服务)
    - [10.2 Kubernetes Deployment（Linkerd）](#102-kubernetes-deploymentlinkerd)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [最佳实践](#最佳实践)

---

## 1. 概述

### 1.1 为什么需要服务网格 + OpenTelemetry

```text
✅ 自动追踪（无需修改应用代码）
✅ 统一遥测（所有服务统一采集）
✅ 安全通信（mTLS 自动加密）
✅ 流量控制（A/B 测试、金丝雀发布）
✅ 故障恢复（重试、超时、断路器）
✅ 可视化（调用链拓扑、依赖关系）
```

### 1.2 架构对比

| 特性 | Linkerd | Istio |
|-----|---------|-------|
| 性能 | 极低延迟 (~1ms) | 中等延迟 (~5ms) |
| 内存占用 | 低 (~10MB) | 中 (~50MB) |
| 复杂度 | 简单 | 复杂 |
| 功能 | 核心功能 | 全功能 |
| Rust 支持 | 原生 (Rust 编写) | Envoy (C++) |
| OpenTelemetry | 内置支持 | 插件支持 |

---

## 2. Linkerd 集成

### 2.1 Linkerd 安装与配置

**安装 Linkerd**:

```bash
# 1. 安装 Linkerd CLI
curl -sL https://run.linkerd.io/install | sh

# 2. 验证 Kubernetes 集群
linkerd check --pre

# 3. 安装 Linkerd 控制平面
linkerd install --crds | kubectl apply -f -
linkerd install | kubectl apply -f -

# 4. 验证安装
linkerd check

# 5. 安装 OpenTelemetry Collector 扩展
linkerd install --addon-config \
  global.proxy.traceCollector=otel-collector.linkerd-jaeger:55678 | kubectl apply -f -
```

### 2.2 Rust 服务 Linkerd 集成

**`Cargo.toml`**:

```toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["trace", "tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# HTTP 框架
axum = { version = "0.7", features = ["tracing"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 工具库
anyhow = "1.0"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
```

**`src/linkerd.rs`**:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{SERVICE_NAME, SERVICE_VERSION};
use anyhow::Result;

/// 初始化 OpenTelemetry for Linkerd
///
/// Linkerd 会自动注入追踪头部（l5d-*），我们需要：
/// 1. 提取 Linkerd 的追踪上下文
/// 2. 将 OpenTelemetry Span 与 Linkerd 追踪关联
/// 3. 导出到 OTLP Collector
pub async fn init_otel_linkerd() -> Result<TracerProvider> {
    // 1. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, std::env::var("SERVICE_NAME").unwrap_or_else(|_| "rust-service".to_string())),
        KeyValue::new(SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
        KeyValue::new("service.mesh", "linkerd"),
        KeyValue::new("service.mesh.version", "2.15"),
    ]);

    // 2. 创建 OTLP Exporter
    // Linkerd 会将追踪数据发送到配置的 Collector
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://otel-collector.linkerd-jaeger:4317".to_string());

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(otlp_endpoint)
        .build()?;

    // 3. 创建 BatchSpanProcessor
    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5))
    .build();

    // 4. 创建 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    // 5. 注册全局 TracerProvider
    global::set_tracer_provider(tracer_provider.clone());

    tracing::info!("✅ OpenTelemetry initialized for Linkerd");
    Ok(tracer_provider)
}

/// Linkerd 上下文提取器
///
/// Linkerd 使用以下头部传播追踪上下文：
/// - `l5d-ctx-trace`: Trace ID
/// - `l5d-ctx-parent`: Parent Span ID
pub struct LinkerdPropagator;

impl opentelemetry::propagation::TextMapPropagator for LinkerdPropagator {
    fn inject_context(
        &self,
        cx: &opentelemetry::Context,
        injector: &mut dyn opentelemetry::propagation::Injector,
    ) {
        // Linkerd 自动注入，我们只需确保 W3C Trace Context 也存在
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        TraceContextPropagator::new().inject_context(cx, injector);
    }

    fn extract_with_context(
        &self,
        cx: &opentelemetry::Context,
        extractor: &dyn opentelemetry::propagation::Extractor,
    ) -> opentelemetry::Context {
        // 优先使用 W3C Trace Context
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        let w3c_cx = TraceContextPropagator::new().extract_with_context(cx, extractor);

        // 如果 W3C 上下文不存在，尝试从 Linkerd 头部提取
        if !w3c_cx.has_active_span() {
            if let Some(trace_id) = extractor.get("l5d-ctx-trace") {
                // 解析 Linkerd Trace ID 并创建 Span Context
                // （简化处理，实际需要完整解析）
                tracing::debug!("Extracted Linkerd trace ID: {}", trace_id);
            }
        }

        w3c_cx
    }

    fn fields(&self) -> opentelemetry::propagation::FieldSet {
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        TraceContextPropagator::new().fields()
    }
}
```

### 2.3 Axum 中间件集成

**`src/middleware.rs`**:

```rust
use axum::{
    body::Body,
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use opentelemetry::{global, trace::{Span, SpanKind, Status, Tracer}, KeyValue};
use opentelemetry_semantic_conventions::trace::{
    HTTP_METHOD, HTTP_ROUTE, HTTP_STATUS_CODE, HTTP_TARGET, HTTP_USER_AGENT,
};

/// Linkerd 感知的追踪中间件
pub async fn linkerd_tracing_middleware(
    req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let tracer = global::tracer("axum-linkerd");

    // 提取请求信息
    let method = req.method().to_string();
    let uri = req.uri().to_string();
    let user_agent = req
        .headers()
        .get("user-agent")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("");

    // 提取 Linkerd 元数据
    let linkerd_request_id = req
        .headers()
        .get("l5d-request-id")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("");

    // 创建 Span
    let mut span = tracer
        .span_builder(format!("{} {}", method, uri))
        .with_kind(SpanKind::Server)
        .start(&tracer);

    // 添加标准 HTTP 属性
    span.set_attribute(KeyValue::new(HTTP_METHOD, method.clone()));
    span.set_attribute(KeyValue::new(HTTP_TARGET, uri.clone()));
    span.set_attribute(KeyValue::new(HTTP_USER_AGENT, user_agent.to_string()));

    // 添加 Linkerd 特定属性
    if !linkerd_request_id.is_empty() {
        span.set_attribute(KeyValue::new("linkerd.request_id", linkerd_request_id.to_string()));
    }

    // 添加服务网格标识
    span.set_attribute(KeyValue::new("service.mesh", "linkerd"));

    // 执行请求
    let response = next.run(req).await;

    // 记录响应状态码
    let status = response.status();
    span.set_attribute(KeyValue::new(HTTP_STATUS_CODE, status.as_u16() as i64));

    if status.is_client_error() || status.is_server_error() {
        span.set_status(Status::error(format!("HTTP {}", status.as_u16())));
    } else {
        span.set_status(Status::Ok);
    }

    span.end();

    Ok(response)
}
```

---

## 3. Istio 集成

### 3.1 Istio 安装与配置

**安装 Istio**:

```bash
# 1. 下载 Istio
curl -L https://istio.io/downloadIstio | sh -
cd istio-1.21.0

# 2. 安装 istioctl
export PATH=$PWD/bin:$PATH

# 3. 安装 Istio with OpenTelemetry
istioctl install --set profile=demo \
  --set meshConfig.extensionProviders[0].name=otel \
  --set meshConfig.extensionProviders[0].opentelemetry.service=otel-collector.istio-system.svc.cluster.local \
  --set meshConfig.extensionProviders[0].opentelemetry.port=4317 \
  -y

# 4. 启用 Sidecar 注入
kubectl label namespace default istio-injection=enabled

# 5. 配置 Telemetry
kubectl apply -f - <<EOF
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: otel-tracing
  namespace: istio-system
spec:
  tracing:
  - providers:
    - name: otel
    randomSamplingPercentage: 100.0
EOF
```

### 3.2 Rust 服务 Istio 集成

**`src/istio.rs`**:

```rust
use opentelemetry::{global, propagation::TextMapPropagator, KeyValue};
use opentelemetry_sdk::{
    propagation::TraceContextPropagator,
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{SERVICE_NAME, SERVICE_VERSION};
use anyhow::Result;

/// 初始化 OpenTelemetry for Istio
pub async fn init_otel_istio() -> Result<TracerProvider> {
    // 1. 创建 Resource（包含 Istio 元数据）
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, std::env::var("SERVICE_NAME").unwrap_or_else(|_| "rust-service".to_string())),
        KeyValue::new(SERVICE_VERSION, env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", std::env::var("ENVIRONMENT").unwrap_or_else(|_| "production".to_string())),
        KeyValue::new("service.mesh", "istio"),
        KeyValue::new("service.mesh.version", "1.21"),
        // Istio 注入的环境变量
        KeyValue::new("istio.canonical_service", std::env::var("CANONICAL_SERVICE").unwrap_or_default()),
        KeyValue::new("istio.canonical_revision", std::env::var("CANONICAL_REVISION").unwrap_or_default()),
        KeyValue::new("istio.mesh_id", std::env::var("MESH_ID").unwrap_or_default()),
    ]);

    // 2. 创建 OTLP Exporter
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://otel-collector.istio-system:4317".to_string());

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(otlp_endpoint)
        .build()?;

    // 3. 创建 BatchSpanProcessor
    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::Tokio,
    )
    .with_max_queue_size(4096) // Istio 环境流量大，增加队列
    .with_max_export_batch_size(1024)
    .with_scheduled_delay(std::time::Duration::from_secs(3))
    .build();

    // 4. 创建 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    // 5. 注册全局 TracerProvider
    global::set_tracer_provider(tracer_provider.clone());

    // 6. 注册 W3C Trace Context Propagator（Istio 使用 B3/W3C）
    global::set_text_map_propagator(TraceContextPropagator::new());

    tracing::info!("✅ OpenTelemetry initialized for Istio");
    Ok(tracer_provider)
}

/// Istio Baggage 提取器
///
/// Istio 支持 Baggage 传播，用于跨服务传递业务上下文
pub struct IstioBaggagePropagator;

impl TextMapPropagator for IstioBaggagePropagator {
    fn inject_context(
        &self,
        cx: &opentelemetry::Context,
        injector: &mut dyn opentelemetry::propagation::Injector,
    ) {
        // 注入 W3C Trace Context
        TraceContextPropagator::new().inject_context(cx, injector);

        // 注入 Baggage（Istio 支持）
        if let Some(baggage) = cx.get::<opentelemetry::baggage::Baggage>() {
            for (key, (value, _metadata)) in baggage.iter() {
                injector.set(
                    &format!("baggage-{}", key),
                    value.to_string(),
                );
            }
        }
    }

    fn extract_with_context(
        &self,
        cx: &opentelemetry::Context,
        extractor: &dyn opentelemetry::propagation::Extractor,
    ) -> opentelemetry::Context {
        // 提取 W3C Trace Context
        let mut new_cx = TraceContextPropagator::new().extract_with_context(cx, extractor);

        // 提取 Baggage
        let mut baggage = opentelemetry::baggage::Baggage::new();
        for key in extractor.keys() {
            if let Some(stripped_key) = key.strip_prefix("baggage-") {
                if let Some(value) = extractor.get(key) {
                    baggage = baggage.with_entry(stripped_key.to_string(), value.to_string());
                }
            }
        }

        if !baggage.is_empty() {
            new_cx = new_cx.with_baggage(baggage);
        }

        new_cx
    }

    fn fields(&self) -> opentelemetry::propagation::FieldSet {
        TraceContextPropagator::new().fields()
    }
}
```

### 3.3 Istio VirtualService 追踪

**`kubernetes/virtual-service.yaml`**:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: rust-service
  namespace: default
spec:
  hosts:
  - rust-service
  http:
  - match:
    - headers:
        x-canary:
          exact: "true"
    route:
    - destination:
        host: rust-service
        subset: v2
      weight: 100
    # 为金丝雀版本添加自定义追踪标签
    headers:
      request:
        add:
          x-trace-version: "canary"
  - route:
    - destination:
        host: rust-service
        subset: v1
      weight: 100
    headers:
      request:
        add:
          x-trace-version: "stable"
---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: rust-service
  namespace: default
spec:
  host: rust-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        http2MaxRequests: 100
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2
```

---

## 4. 服务网格上下文传播

### 4.1 跨服务调用追踪

**`src/client.rs`**:

```rust
use opentelemetry::{global, propagation::TextMapPropagator, trace::{Span, SpanKind, Tracer}, KeyValue};
use opentelemetry_semantic_conventions::trace::{
    HTTP_METHOD, HTTP_STATUS_CODE, HTTP_TARGET, PEER_SERVICE,
};
use reqwest::{Client, Request, Response};
use anyhow::Result;

/// 服务网格感知的 HTTP 客户端
pub struct MeshAwareClient {
    client: Client,
}

impl MeshAwareClient {
    pub fn new() -> Self {
        Self {
            client: Client::builder()
                .timeout(std::time::Duration::from_secs(30))
                .build()
                .expect("Failed to create HTTP client"),
        }
    }

    /// 发起追踪请求（自动注入上下文）
    pub async fn trace_request(&self, mut req: Request) -> Result<Response> {
        let tracer = global::tracer("mesh-aware-client");
        let method = req.method().to_string();
        let url = req.url().to_string();

        // 创建 Client Span
        let mut span = tracer
            .span_builder(format!("HTTP {} {}", method, url))
            .with_kind(SpanKind::Client)
            .start(&tracer);

        // 添加属性
        span.set_attribute(KeyValue::new(HTTP_METHOD, method.clone()));
        span.set_attribute(KeyValue::new(HTTP_TARGET, url.clone()));

        // 提取目标服务名（从 URL 或 Kubernetes Service）
        if let Some(host) = req.url().host_str() {
            span.set_attribute(KeyValue::new(PEER_SERVICE, host.to_string()));
        }

        // 注入追踪上下文到 HTTP 头部
        let cx = opentelemetry::Context::current_with_span(span.clone());
        let propagator = global::text_map_propagator();
        
        let mut injector = HashMap::new();
        propagator.inject_context(&cx, &mut injector);
        
        for (key, value) in injector {
            req.headers_mut().insert(
                reqwest::header::HeaderName::from_bytes(key.as_bytes())?,
                reqwest::header::HeaderValue::from_str(&value)?,
            );
        }

        // 发起请求
        let response = self.client.execute(req).await?;

        // 记录响应状态码
        let status = response.status();
        span.set_attribute(KeyValue::new(HTTP_STATUS_CODE, status.as_u16() as i64));

        if status.is_client_error() || status.is_server_error() {
            span.set_status(opentelemetry::trace::Status::error(format!("HTTP {}", status.as_u16())));
        } else {
            span.set_status(opentelemetry::trace::Status::Ok);
        }

        span.end();

        Ok(response)
    }
}

use std::collections::HashMap;
```

---

## 5. mTLS 与安全追踪

### 5.1 mTLS 元数据追踪

**`src/mtls.rs`**:

```rust
use opentelemetry::{trace::Span, KeyValue};
use axum::{extract::Request, middleware::Next, response::Response};

/// 提取 mTLS 证书信息并添加到 Span
pub async fn mtls_tracing_middleware(
    req: Request,
    next: Next,
) -> Response {
    let mut span = opentelemetry::trace::get_active_span(|span| {
        // 提取 Istio 注入的 mTLS 头部
        if let Some(client_cert) = req.headers().get("x-forwarded-client-cert") {
            if let Ok(cert_str) = client_cert.to_str() {
                span.set_attribute(KeyValue::new("tls.client_cert", cert_str.to_string()));
                
                // 解析证书信息（简化处理）
                if let Some(subject) = extract_cert_subject(cert_str) {
                    span.set_attribute(KeyValue::new("tls.client_subject", subject));
                }
            }
        }

        // 提取服务身份
        if let Some(spiffe_id) = req.headers().get("x-forwarded-spiffe-id") {
            if let Ok(id_str) = spiffe_id.to_str() {
                span.set_attribute(KeyValue::new("service.spiffe_id", id_str.to_string()));
            }
        }

        span.clone()
    });

    next.run(req).await
}

fn extract_cert_subject(cert: &str) -> Option<String> {
    // 简化：从 X-Forwarded-Client-Cert 头部提取 Subject
    // 格式: By=...; Hash=...; Subject="CN=..."
    cert.split(';')
        .find(|s| s.trim().starts_with("Subject="))
        .and_then(|s| s.split('=').nth(1))
        .map(|s| s.trim().trim_matches('"').to_string())
}
```

---

## 6. 流量管理与追踪

### 6.1 金丝雀发布追踪

**`src/canary.rs`**:

```rust
use opentelemetry::{trace::Span, KeyValue};
use axum::{extract::Request, middleware::Next, response::Response};

/// 金丝雀版本追踪中间件
pub async fn canary_tracing_middleware(
    req: Request,
    next: Next,
) -> Response {
    opentelemetry::trace::get_active_span(|span| {
        // 提取金丝雀标识
        if let Some(canary_header) = req.headers().get("x-canary") {
            if let Ok(is_canary) = canary_header.to_str() {
                span.set_attribute(KeyValue::new("deployment.canary", is_canary == "true"));
            }
        }

        // 提取版本信息（Istio VirtualService 注入）
        if let Some(version) = req.headers().get("x-trace-version") {
            if let Ok(ver_str) = version.to_str() {
                span.set_attribute(KeyValue::new("deployment.version", ver_str.to_string()));
            }
        }

        // 提取流量分割权重（如果可用）
        if let Some(weight) = req.headers().get("x-traffic-weight") {
            if let Ok(weight_str) = weight.to_str() {
                if let Ok(weight_val) = weight_str.parse::<i64>() {
                    span.set_attribute(KeyValue::new("deployment.traffic_weight", weight_val));
                }
            }
        }
    });

    next.run(req).await
}
```

### 6.2 A/B 测试追踪

**`src/ab_testing.rs`**:

```rust
use opentelemetry::{trace::Span, KeyValue, baggage::Baggage};
use axum::{extract::Request, middleware::Next, response::Response};
use rand::Rng;

/// A/B 测试追踪中间件
pub async fn ab_testing_middleware(
    mut req: Request,
    next: Next,
) -> Response {
    // 1. 检测用户是否已分配到 A/B 组
    let ab_group = if let Some(group_header) = req.headers().get("x-ab-group") {
        group_header.to_str().unwrap_or("control").to_string()
    } else {
        // 2. 随机分配（50/50）
        let mut rng = rand::thread_rng();
        if rng.gen_bool(0.5) {
            "experiment".to_string()
        } else {
            "control".to_string()
        }
    };

    // 3. 添加到 Span 属性
    opentelemetry::trace::get_active_span(|span| {
        span.set_attribute(KeyValue::new("ab.group", ab_group.clone()));
        span.set_attribute(KeyValue::new("ab.experiment_id", "homepage-redesign-2024"));
    });

    // 4. 添加到 Baggage（跨服务传播）
    let cx = opentelemetry::Context::current();
    let baggage = cx
        .get::<Baggage>()
        .cloned()
        .unwrap_or_default()
        .with_entry("ab.group".to_string(), ab_group.clone());
    let new_cx = cx.with_baggage(baggage);

    // 5. 设置为当前上下文
    let _guard = new_cx.attach();

    next.run(req).await
}
```

---

## 7. 分布式追踪最佳实践

### 7.1 Span 命名规范

```rust
/// 服务网格环境中的 Span 命名规范
pub mod span_naming {
    /// 入站请求 Span
    /// 格式: "HTTP {METHOD} {ROUTE}"
    pub fn inbound_http_span(method: &str, route: &str) -> String {
        format!("HTTP {} {}", method, route)
    }

    /// 出站请求 Span
    /// 格式: "OUTBOUND HTTP {METHOD} {SERVICE}"
    pub fn outbound_http_span(method: &str, service: &str) -> String {
        format!("OUTBOUND HTTP {} {}", method, service)
    }

    /// 数据库查询 Span
    /// 格式: "DB {OPERATION} {TABLE}"
    pub fn database_span(operation: &str, table: &str) -> String {
        format!("DB {} {}", operation, table)
    }

    /// 消息队列 Span
    /// 格式: "QUEUE {OPERATION} {TOPIC}"
    pub fn queue_span(operation: &str, topic: &str) -> String {
        format!("QUEUE {} {}", operation, topic)
    }
}
```

### 7.2 采样策略（服务网格环境）

```rust
use opentelemetry_sdk::trace::Sampler;

/// 服务网格环境采样策略
pub fn mesh_sampler() -> Sampler {
    // 1. 网关入口：全采样（关键路径）
    // 2. 内部服务：低采样（减少开销）
    // 3. 错误请求：全采样（便于调试）
    
    let is_gateway = std::env::var("IS_GATEWAY").unwrap_or_default() == "true";
    
    if is_gateway {
        // 网关全采样
        Sampler::AlwaysOn
    } else {
        // 内部服务：基于父级采样决策 + 1% 随机采样
        Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.01)))
    }
}
```

---

## 8. 性能优化

### 8.1 批量导出优化（高流量场景）

```rust
use opentelemetry_sdk::trace::BatchSpanProcessor;

/// 高流量服务网格环境的批量导出配置
pub fn high_traffic_batch_processor(
    exporter: impl opentelemetry::trace::SpanExporter + 'static,
) -> BatchSpanProcessor {
    BatchSpanProcessor::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_max_queue_size(8192)        // 增大队列
        .with_max_export_batch_size(2048) // 增大批次
        .with_scheduled_delay(std::time::Duration::from_secs(2)) // 减少延迟
        .with_max_export_timeout(std::time::Duration::from_secs(15)) // 增加超时
        .build()
}
```

### 8.2 资源属性缓存

```rust
use once_cell::sync::Lazy;
use opentelemetry::KeyValue;

/// 缓存静态资源属性（避免重复创建）
pub static MESH_RESOURCE_ATTRS: Lazy<Vec<KeyValue>> = Lazy::new(|| {
    vec![
        KeyValue::new("service.mesh", std::env::var("SERVICE_MESH").unwrap_or_else(|_| "istio".to_string())),
        KeyValue::new("service.mesh.version", std::env::var("MESH_VERSION").unwrap_or_else(|_| "1.21".to_string())),
        KeyValue::new("k8s.cluster.name", std::env::var("CLUSTER_NAME").unwrap_or_default()),
        KeyValue::new("k8s.namespace.name", std::env::var("POD_NAMESPACE").unwrap_or_default()),
        KeyValue::new("k8s.pod.name", std::env::var("POD_NAME").unwrap_or_default()),
    ]
});
```

---

## 9. 故障注入与混沌工程

### 9.1 Istio Fault Injection 追踪

**`kubernetes/fault-injection.yaml`**:

```yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: rust-service-fault
spec:
  hosts:
  - rust-service
  http:
  - fault:
      delay:
        percentage:
          value: 10.0  # 10% 的请求延迟
        fixedDelay: 5s
      abort:
        percentage:
          value: 5.0   # 5% 的请求失败
        httpStatus: 503
    route:
    - destination:
        host: rust-service
    # 为故障注入请求添加追踪标签
    headers:
      request:
        add:
          x-fault-injected: "true"
```

**Rust 代码检测故障注入**:

```rust
use opentelemetry::{trace::Span, KeyValue};

pub async fn fault_detection_middleware(
    req: Request,
    next: Next,
) -> Response {
    opentelemetry::trace::get_active_span(|span| {
        // 检测是否为故障注入请求
        if let Some(fault_header) = req.headers().get("x-fault-injected") {
            if let Ok(is_fault) = fault_header.to_str() {
                span.set_attribute(KeyValue::new("chaos.fault_injected", is_fault == "true"));
            }
        }

        // 检测延迟注入
        if let Some(delay_header) = req.headers().get("x-envoy-fault-delay-request") {
            if let Ok(delay_str) = delay_header.to_str() {
                span.set_attribute(KeyValue::new("chaos.delay_ms", delay_str.to_string()));
            }
        }

        // 检测错误注入
        if let Some(abort_header) = req.headers().get("x-envoy-fault-abort") {
            if let Ok(abort_str) = abort_header.to_str() {
                span.set_attribute(KeyValue::new("chaos.abort_code", abort_str.to_string()));
            }
        }
    });

    next.run(req).await
}
```

---

## 10. 完整示例

### 10.1 Linkerd 完整服务

**`examples/linkerd_service.rs`**:

```rust
use axum::{
    routing::get,
    Router,
};
use std::net::SocketAddr;
use tower_http::trace::TraceLayer;
use anyhow::Result;

mod linkerd;
mod middleware;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 初始化 tracing
    tracing_subscriber::fmt::init();

    // 2. 初始化 OpenTelemetry for Linkerd
    let _tracer_provider = linkerd::init_otel_linkerd().await?;

    // 3. 创建 Axum 应用
    let app = Router::new()
        .route("/", get(root_handler))
        .route("/health", get(health_handler))
        .layer(axum::middleware::from_fn(middleware::linkerd_tracing_middleware))
        .layer(TraceLayer::new_for_http());

    // 4. 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    tracing::info!("✅ Linkerd-enabled service listening on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

async fn root_handler() -> &'static str {
    "Hello from Linkerd + Rust + OpenTelemetry!"
}

async fn health_handler() -> &'static str {
    "OK"
}
```

### 10.2 Kubernetes Deployment（Linkerd）

**`kubernetes/deployment-linkerd.yaml`**:

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: rust-mesh
  annotations:
    linkerd.io/inject: enabled
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-service
  namespace: rust-mesh
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-service
  template:
    metadata:
      labels:
        app: rust-service
        version: v1
    spec:
      containers:
      - name: rust-service
        image: rust-service:latest
        ports:
        - containerPort: 8080
        env:
        - name: SERVICE_NAME
          value: "rust-service"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector.linkerd-jaeger:4317"
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "128Mi"
            cpu: "200m"
---
apiVersion: v1
kind: Service
metadata:
  name: rust-service
  namespace: rust-mesh
spec:
  selector:
    app: rust-service
  ports:
  - port: 80
    targetPort: 8080
  type: ClusterIP
```

---

## 参考资源

### 官方文档

- **Linkerd**: <https://linkerd.io/2.15/reference/architecture/>
- **Istio**: <https://istio.io/latest/docs/concepts/observability/>
- **OpenTelemetry Rust**: <https://docs.rs/opentelemetry/latest/opentelemetry/>

### 最佳实践

- **Service Mesh Tracing**: <https://www.cncf.io/blog/2021/08/26/distributed-tracing-with-istio-and-linkerd/>
- **mTLS Observability**: <https://linkerd.io/2.15/features/automatic-mtls/>

---

**文档维护**: OTLP Rust 项目组  
**最后更新**: 2025年10月9日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐
