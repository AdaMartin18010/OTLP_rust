# Rust OTLP 分布式追踪可视化完整指南

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025-10-08  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Rust OTLP 分布式追踪可视化完整指南](#rust-otlp-分布式追踪可视化完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [为什么需要追踪可视化？](#为什么需要追踪可视化)
    - [主流可视化工具对比](#主流可视化工具对比)
  - [Jaeger 集成](#jaeger-集成)
    - [Jaeger 架构](#jaeger-架构)
    - [Rust 客户端配置](#rust-客户端配置)
    - [直接导出到 Jaeger（Agent）](#直接导出到-jaegeragent)
    - [通过 OTLP 导出到 Jaeger Collector](#通过-otlp-导出到-jaeger-collector)
    - [集成 tracing 宏](#集成-tracing-宏)
    - [Docker Compose 部署 Jaeger](#docker-compose-部署-jaeger)
    - [Jaeger 高级配置](#jaeger-高级配置)
  - [Grafana Tempo 集成](#grafana-tempo-集成)
    - [Tempo 架构](#tempo-架构)
    - [Rust 配置（与 Jaeger 类似）](#rust-配置与-jaeger-类似)
    - [Docker Compose 部署 Tempo](#docker-compose-部署-tempo)
    - [Tempo 配置文件](#tempo-配置文件)
    - [Grafana 数据源配置](#grafana-数据源配置)
    - [TraceQL 查询示例](#traceql-查询示例)
  - [Zipkin 集成](#zipkin-集成)
    - [Zipkin 架构](#zipkin-架构)
    - [Rust 配置](#rust-配置)
    - [Docker Compose 部署 Zipkin](#docker-compose-部署-zipkin)
  - [自定义可视化](#自定义可视化)
    - [使用 D3.js 构建自定义追踪图](#使用-d3js-构建自定义追踪图)
    - [Web API 端点](#web-api-端点)
    - [HTML 可视化页面](#html-可视化页面)
  - [追踪分析工具](#追踪分析工具)
    - [关键路径分析](#关键路径分析)
    - [服务依赖分析](#服务依赖分析)
  - [性能分析](#性能分析)
    - [延迟分析](#延迟分析)
    - [热点分析](#热点分析)
  - [告警与异常检测](#告警与异常检测)
    - [异常检测规则](#异常检测规则)
    - [Prometheus 告警集成](#prometheus-告警集成)
  - [最佳实践](#最佳实践)
    - [1. 采样策略](#1-采样策略)
    - [2. 属性标准化](#2-属性标准化)
    - [3. 存储优化](#3-存储优化)
    - [4. 查询优化](#4-查询优化)
  - [总结](#总结)
    - [工具选择建议](#工具选择建议)
    - [关键指标](#关键指标)
    - [下一步行动](#下一步行动)

---

## 概述

### 为什么需要追踪可视化？

分布式追踪可视化帮助我们：

- ✅ **理解系统行为**: 可视化服务间调用关系
- ✅ **定位性能瓶颈**: 识别慢查询和延迟
- ✅ **故障排查**: 快速定位错误根因
- ✅ **优化路径**: 发现不必要的调用链
- ✅ **容量规划**: 分析系统负载和瓶颈

### 主流可视化工具对比

| 工具 | 优势 | 劣势 | 适用场景 |
|------|------|------|---------|
| **Jaeger** | 成熟、功能丰富、UI友好 | 存储开销大 | 中小规模、功能优先 |
| **Tempo** | Grafana生态、成本低 | 查询功能有限 | 成本敏感、已用Grafana |
| **Zipkin** | 简单易用、历史悠久 | 功能相对基础 | 简单场景、快速上手 |

---

## Jaeger 集成

### Jaeger 架构

```text
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Rust App  │────▶│   Jaeger   │────▶│  Storage    │
│   (OTLP)    │     │  Collector  │     │ (ES/Badger) │
└─────────────┘     └─────────────┘     └─────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │   Jaeger    │
                    │     UI      │
                    └─────────────┘
```

### Rust 客户端配置

```toml
[dependencies]
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }
opentelemetry-jaeger = "0.31.0"
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29.0"
```

### 直接导出到 Jaeger（Agent）

```rust
// src/tracing/jaeger_agent.rs
use opentelemetry::{global, trace::TracerProvider};
use opentelemetry_sdk::trace::{Config, Tracer};
use opentelemetry_jaeger::JaegerPropagator;

pub fn init_jaeger_agent(service_name: &str) -> Result<Tracer, Box<dyn std::error::Error>> {
    // 设置传播器
    global::set_text_map_propagator(JaegerPropagator::new());

    // 配置 Jaeger Agent 导出器
    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name(service_name)
        .with_endpoint("localhost:6831") // Jaeger Agent UDP 端点
        .with_max_packet_size(9_216)     // 最大 UDP 包大小
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    Ok(tracer)
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Jaeger
    let tracer = init_jaeger_agent("my-rust-service")?;

    // 创建 Span
    let span = tracer.span_builder("my-operation").start(&tracer);
    let cx = opentelemetry::Context::current_with_span(span);

    // 执行业务逻辑
    tracer.in_span("sub-operation", |_cx| {
        // 业务代码
        std::thread::sleep(std::time::Duration::from_millis(100));
    });

    // 关闭
    global::shutdown_tracer_provider();

    Ok(())
}
```

### 通过 OTLP 导出到 Jaeger Collector

```rust
// src/tracing/jaeger_otlp.rs
use opentelemetry::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::trace::Config;
use std::time::Duration;

pub fn init_jaeger_otlp(service_name: &str) -> Result<opentelemetry_sdk::trace::Tracer, Box<dyn std::error::Error>> {
    // Jaeger 0.14+ 支持 OTLP
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317") // Jaeger Collector OTLP 端点
        .with_timeout(Duration::from_secs(3))
        .build()?;

    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_config(Config::default().with_resource(
            opentelemetry_sdk::Resource::new(vec![
                opentelemetry::KeyValue::new("service.name", service_name.to_string()),
                opentelemetry::KeyValue::new("service.version", "1.0.0"),
                opentelemetry::KeyValue::new("deployment.environment", "production"),
            ])
        ))
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    let tracer = provider.tracer(service_name);

    Ok(tracer)
}
```

### 集成 tracing 宏

```rust
// src/tracing/integration.rs
use tracing_subscriber::{layer::SubscriberExt, Registry};
use tracing_opentelemetry::OpenTelemetryLayer;

pub fn init_tracing_with_jaeger(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Jaeger
    let tracer = init_jaeger_otlp(service_name)?;

    // 创建 OpenTelemetry layer
    let opentelemetry = OpenTelemetryLayer::new(tracer);

    // 创建 subscriber
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer().with_target(true))
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(opentelemetry);

    tracing::subscriber::set_global_default(subscriber)?;

    Ok(())
}

// 使用示例 - 使用 tracing 宏
#[tracing::instrument]
async fn process_order(order_id: u64) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!(order_id, "Processing order");

    // 子 Span
    fetch_user_info(order_id).await?;
    validate_payment(order_id).await?;
    update_inventory(order_id).await?;

    tracing::info!(order_id, "Order processed successfully");
    Ok(())
}

#[tracing::instrument]
async fn fetch_user_info(order_id: u64) -> Result<(), Box<dyn std::error::Error>> {
    tracing::debug!("Fetching user info");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}
```

### Docker Compose 部署 Jaeger

```yaml
# docker-compose.jaeger.yml
version: '3.8'

services:
  jaeger:
    image: jaegertracing/all-in-one:1.67
    environment:
      - COLLECTOR_OTLP_ENABLED=true
      - SPAN_STORAGE_TYPE=badger
      - BADGER_EPHEMERAL=false
      - BADGER_DIRECTORY_VALUE=/badger/data
      - BADGER_DIRECTORY_KEY=/badger/key
    ports:
      - "16686:16686"  # Jaeger UI
      - "14268:14268"  # Jaeger Collector HTTP
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP
      - "6831:6831/udp" # Jaeger Agent (UDP)
    volumes:
      - jaeger-badger:/badger
    networks:
      - tracing

  # Rust 应用示例
  rust-app:
    build: .
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
      - OTEL_SERVICE_NAME=my-rust-service
    depends_on:
      - jaeger
    networks:
      - tracing

volumes:
  jaeger-badger:

networks:
  tracing:
```

### Jaeger 高级配置

```rust
// src/tracing/jaeger_advanced.rs
use opentelemetry::trace::{Sampler, SamplerResult};

/// 自定义采样器：只采样错误和慢请求
struct ErrorAndSlowSampler {
    slow_threshold_ms: u64,
}

impl Sampler for ErrorAndSlowSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplerResult {
        // 检查是否有错误属性
        let has_error = attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        });

        // 检查是否有 HTTP 状态码 >= 500
        let is_server_error = attributes.iter().any(|kv| {
            if kv.key.as_str() == "http.status_code" {
                if let Some(code) = kv.value.as_i64() {
                    return code >= 500;
                }
            }
            false
        });

        // 如果是错误或服务器错误，采样
        if has_error || is_server_error {
            return SamplerResult {
                decision: opentelemetry::trace::SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            };
        }

        // 默认采样 10%
        SamplerResult {
            decision: if rand::random::<f64>() < 0.1 {
                opentelemetry::trace::SamplingDecision::RecordAndSample
            } else {
                opentelemetry::trace::SamplingDecision::Drop
            },
            attributes: vec![],
            trace_state: Default::default(),
        }
    }
}

pub fn init_jaeger_with_custom_sampler(
    service_name: &str,
) -> Result<opentelemetry_sdk::trace::Tracer, Box<dyn std::error::Error>> {
    let sampler = ErrorAndSlowSampler {
        slow_threshold_ms: 1000,
    };

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Box::new(sampler))
                .with_resource(opentelemetry_sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", service_name.to_string()),
                ]))
        )
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    Ok(provider.tracer(service_name))
}
```

---

## Grafana Tempo 集成

### Tempo 架构

```text
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Rust App  │────▶│    Tempo    │────▶│  S3/GCS/    │
│   (OTLP)    │     │ Distributor │     │  MinIO      │
└─────────────┘     └─────────────┘     └─────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │   Grafana   │
                    │   (Query)   │
                    └─────────────┘
```

### Rust 配置（与 Jaeger 类似）

```rust
// src/tracing/tempo.rs
use opentelemetry_otlp::WithExportConfig;

pub fn init_tempo(service_name: &str) -> Result<opentelemetry_sdk::trace::Tracer, Box<dyn std::error::Error>> {
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317") // Tempo OTLP 端点
        .build()?;

    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_config(Config::default().with_resource(
            opentelemetry_sdk::Resource::new(vec![
                opentelemetry::KeyValue::new("service.name", service_name.to_string()),
                opentelemetry::KeyValue::new("cluster", "production"),
                opentelemetry::KeyValue::new("namespace", "default"),
            ])
        ))
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();

    Ok(provider.tracer(service_name))
}
```

### Docker Compose 部署 Tempo

```yaml
# docker-compose.tempo.yml
version: '3.8'

services:
  tempo:
    image: grafana/tempo:2.7.0
    command: [ "-config.file=/etc/tempo.yaml" ]
    volumes:
      - ./tempo.yaml:/etc/tempo.yaml
      - tempo-data:/tmp/tempo
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "3200:3200"   # Tempo HTTP
    networks:
      - tracing

  grafana:
    image: grafana/grafana:11.4.0
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
      - GF_AUTH_DISABLE_LOGIN_FORM=true
    volumes:
      - ./grafana-datasources.yaml:/etc/grafana/provisioning/datasources/datasources.yaml
    ports:
      - "3000:3000"
    depends_on:
      - tempo
    networks:
      - tracing

volumes:
  tempo-data:

networks:
  tracing:
```

### Tempo 配置文件

```yaml
# tempo.yaml
server:
  http_listen_port: 3200

distributor:
  receivers:
    otlp:
      protocols:
        grpc:
          endpoint: 0.0.0.0:4317
        http:
          endpoint: 0.0.0.0:4318

ingester:
  max_block_duration: 5m

compactor:
  compaction:
    block_retention: 48h

storage:
  trace:
    backend: local
    local:
      path: /tmp/tempo/blocks
    wal:
      path: /tmp/tempo/wal
    pool:
      max_workers: 100
      queue_depth: 10000
```

### Grafana 数据源配置

```yaml
# grafana-datasources.yaml
apiVersion: 1

datasources:
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    uid: tempo
    editable: true
    jsonData:
      httpMethod: GET
      tracesToLogs:
        datasourceUid: 'loki'
        tags: ['job', 'instance', 'pod', 'namespace']
        mappedTags: [{ key: 'service.name', value: 'service' }]
        mapTagNamesEnabled: true
        spanStartTimeShift: '1h'
        spanEndTimeShift: '1h'
```

### TraceQL 查询示例

```go
// Grafana Explore 中使用 TraceQL
{
  service.name = "my-rust-service" &&
  http.status_code >= 500
}

// 查询慢请求
{
  service.name = "my-rust-service" &&
  duration > 1s
}

// 查询特定用户的追踪
{
  user.id = "123" &&
  span.kind = "server"
}
```

---

## Zipkin 集成

### Zipkin 架构

```text
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Rust App  │────▶│   Zipkin    │────▶│  Storage    │
│  (Zipkin)   │     │   Server    │     │  (MySQL/ES) │
└─────────────┘     └─────────────┘     └─────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │   Zipkin    │
                    │     UI      │
                    └─────────────┘
```

### Rust 配置

```toml
[dependencies]
opentelemetry-zipkin = "0.31.0"
```

```rust
// src/tracing/zipkin.rs
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::Config;
use opentelemetry_zipkin::ZipkinPropagator;

pub fn init_zipkin(service_name: &str) -> Result<opentelemetry_sdk::trace::Tracer, Box<dyn std::error::Error>> {
    // 设置传播器
    opentelemetry::global::set_text_map_propagator(ZipkinPropagator::new());

    // 配置 Zipkin
    let tracer = opentelemetry_zipkin::new_pipeline()
        .with_service_name(service_name)
        .with_service_address("127.0.0.1:8080".parse()?)
        .with_collector_endpoint("http://localhost:9411/api/v2/spans")
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    Ok(tracer)
}
```

### Docker Compose 部署 Zipkin

```yaml
# docker-compose.zipkin.yml
version: '3.8'

services:
  zipkin:
    image: openzipkin/zipkin:3.4.3
    environment:
      - STORAGE_TYPE=mem
      # 或使用 Elasticsearch
      # - STORAGE_TYPE=elasticsearch
      # - ES_HOSTS=elasticsearch:9200
    ports:
      - "9411:9411"
    networks:
      - tracing

  # 可选：Elasticsearch 存储
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.17.2
    environment:
      - discovery.type=single-node
      - "ES_JAVA_OPTS=-Xms512m -Xmx512m"
    ports:
      - "9200:9200"
    networks:
      - tracing

networks:
  tracing:
```

---

## 自定义可视化

### 使用 D3.js 构建自定义追踪图

```rust
// src/visualization/trace_graph.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct TraceNode {
    pub span_id: String,
    pub name: String,
    pub service: String,
    pub duration_ms: u64,
    pub start_time: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TraceEdge {
    pub from: String,
    pub to: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TraceGraph {
    pub nodes: Vec<TraceNode>,
    pub edges: Vec<TraceEdge>,
}

impl TraceGraph {
    pub fn from_spans(spans: Vec<SpanData>) -> Self {
        let mut nodes = Vec::new();
        let mut edges = Vec::new();
        let mut parent_map: HashMap<String, String> = HashMap::new();

        for span in spans {
            let span_id = span.span_id().to_hex();
            
            nodes.push(TraceNode {
                span_id: span_id.clone(),
                name: span.name().to_string(),
                service: span.resource()
                    .get("service.name")
                    .map(|v| v.to_string())
                    .unwrap_or_default(),
                duration_ms: span.end_time()
                    .duration_since(span.start_time())
                    .unwrap()
                    .as_millis() as u64,
                start_time: span.start_time()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_millis() as u64,
            });

            if let Some(parent_id) = span.parent_span_id() {
                let parent_id_hex = parent_id.to_hex();
                edges.push(TraceEdge {
                    from: parent_id_hex.clone(),
                    to: span_id.clone(),
                });
                parent_map.insert(span_id, parent_id_hex);
            }
        }

        TraceGraph { nodes, edges }
    }

    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
}
```

### Web API 端点

```rust
// src/api/trace_visualization.rs
use axum::{
    Router,
    routing::get,
    extract::{Path, Query},
    response::Json,
    http::StatusCode,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct TraceQueryParams {
    service: Option<String>,
    start_time: Option<u64>,
    end_time: Option<u64>,
}

async fn get_trace(
    Path(trace_id): Path<String>,
) -> Result<Json<TraceGraph>, StatusCode> {
    // 从存储中获取 Trace
    let spans = fetch_spans_by_trace_id(&trace_id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    let graph = TraceGraph::from_spans(spans);
    Ok(Json(graph))
}

async fn search_traces(
    Query(params): Query<TraceQueryParams>,
) -> Result<Json<Vec<TraceSummary>>, StatusCode> {
    // 搜索 Traces
    let traces = search_traces_in_storage(params)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(Json(traces))
}

pub fn visualization_routes() -> Router {
    Router::new()
        .route("/api/traces/:trace_id", get(get_trace))
        .route("/api/traces/search", get(search_traces))
}
```

### HTML 可视化页面

```html
<!-- static/trace-viewer.html -->
<!DOCTYPE html>
<html>
<head>
    <title>Trace Viewer</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        .node {
            stroke: #fff;
            stroke-width: 1.5px;
        }
        .link {
            stroke: #999;
            stroke-opacity: 0.6;
        }
        .tooltip {
            position: absolute;
            background: #fff;
            border: 1px solid #ddd;
            padding: 10px;
            border-radius: 5px;
            pointer-events: none;
        }
    </style>
</head>
<body>
    <div id="trace-graph"></div>

    <script>
        async function loadTrace(traceId) {
            const response = await fetch(`/api/traces/${traceId}`);
            const data = await response.json();
            renderTraceGraph(data);
        }

        function renderTraceGraph(data) {
            const width = 1200;
            const height = 800;

            const svg = d3.select("#trace-graph")
                .append("svg")
                .attr("width", width)
                .attr("height", height);

            const simulation = d3.forceSimulation(data.nodes)
                .force("link", d3.forceLink(data.edges).id(d => d.span_id))
                .force("charge", d3.forceManyBody().strength(-300))
                .force("center", d3.forceCenter(width / 2, height / 2));

            const link = svg.append("g")
                .selectAll("line")
                .data(data.edges)
                .enter().append("line")
                .attr("class", "link")
                .attr("stroke-width", 2);

            const node = svg.append("g")
                .selectAll("circle")
                .data(data.nodes)
                .enter().append("circle")
                .attr("class", "node")
                .attr("r", d => Math.sqrt(d.duration_ms) + 5)
                .attr("fill", d => colorByService(d.service))
                .call(d3.drag()
                    .on("start", dragstarted)
                    .on("drag", dragged)
                    .on("end", dragended));

            node.append("title")
                .text(d => `${d.name}\n${d.duration_ms}ms`);

            simulation.on("tick", () => {
                link
                    .attr("x1", d => d.source.x)
                    .attr("y1", d => d.source.y)
                    .attr("x2", d => d.target.x)
                    .attr("y2", d => d.target.y);

                node
                    .attr("cx", d => d.x)
                    .attr("cy", d => d.y);
            });
        }

        function colorByService(service) {
            const colors = {
                "user-service": "#1f77b4",
                "order-service": "#ff7f0e",
                "payment-service": "#2ca02c",
            };
            return colors[service] || "#8c564b";
        }

        // 加载示例 Trace
        loadTrace("trace-id-example");
    </script>
</body>
</html>
```

---

## 追踪分析工具

### 关键路径分析

```rust
// src/analysis/critical_path.rs
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct CriticalPath {
    pub spans: Vec<SpanData>,
    pub total_duration_ms: u64,
}

impl CriticalPath {
    pub fn analyze(spans: Vec<SpanData>) -> Self {
        // 构建依赖图
        let mut children_map: HashMap<String, Vec<usize>> = HashMap::new();
        let mut span_index_map: HashMap<String, usize> = HashMap::new();

        for (idx, span) in spans.iter().enumerate() {
            let span_id = span.span_id().to_hex();
            span_index_map.insert(span_id.clone(), idx);

            if let Some(parent_id) = span.parent_span_id() {
                let parent_id_hex = parent_id.to_hex();
                children_map
                    .entry(parent_id_hex)
                    .or_insert_with(Vec::new)
                    .push(idx);
            }
        }

        // 找到根 Span
        let root_span_idx = spans.iter()
            .position(|s| s.parent_span_id().is_none())
            .unwrap_or(0);

        // 递归查找关键路径
        let critical_path_indices = Self::find_critical_path_recursive(
            root_span_idx,
            &spans,
            &children_map,
        );

        let critical_spans: Vec<SpanData> = critical_path_indices
            .into_iter()
            .map(|idx| spans[idx].clone())
            .collect();

        let total_duration_ms = critical_spans
            .iter()
            .map(|s| s.end_time().duration_since(s.start_time()).unwrap().as_millis() as u64)
            .sum();

        CriticalPath {
            spans: critical_spans,
            total_duration_ms,
        }
    }

    fn find_critical_path_recursive(
        span_idx: usize,
        spans: &[SpanData],
        children_map: &HashMap<String, Vec<usize>>,
    ) -> Vec<usize> {
        let span_id = spans[span_idx].span_id().to_hex();
        let mut path = vec![span_idx];

        if let Some(children) = children_map.get(&span_id) {
            // 找到耗时最长的子 Span
            let longest_child = children.iter()
                .max_by_key(|&&child_idx| {
                    spans[child_idx].end_time()
                        .duration_since(spans[child_idx].start_time())
                        .unwrap()
                })
                .copied();

            if let Some(child_idx) = longest_child {
                path.extend(Self::find_critical_path_recursive(child_idx, spans, children_map));
            }
        }

        path
    }
}
```

### 服务依赖分析

```rust
// src/analysis/service_dependency.rs
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct ServiceDependency {
    pub from: String,
    pub to: String,
    pub call_count: u64,
    pub total_duration_ms: u64,
    pub error_count: u64,
}

pub fn analyze_service_dependencies(spans: Vec<SpanData>) -> Vec<ServiceDependency> {
    let mut dependencies: HashMap<(String, String), ServiceDependency> = HashMap::new();

    for span in spans {
        if span.span_kind() == opentelemetry::trace::SpanKind::Server {
            continue; // 跳过服务端 Span
        }

        let from_service = span.resource()
            .get("service.name")
            .map(|v| v.to_string())
            .unwrap_or_default();

        // 查找对应的服务端 Span（通过 parent_span_id）
        if let Some(parent_id) = span.parent_span_id() {
            // 这里需要查询存储来找到 parent span
            // 简化示例
            let to_service = span.attributes()
                .iter()
                .find(|(k, _)| k.as_str() == "peer.service")
                .map(|(_, v)| v.to_string())
                .unwrap_or_default();

            let key = (from_service.clone(), to_service.clone());
            let entry = dependencies.entry(key.clone()).or_insert(ServiceDependency {
                from: from_service,
                to: to_service,
                call_count: 0,
                total_duration_ms: 0,
                error_count: 0,
            });

            entry.call_count += 1;
            entry.total_duration_ms += span.end_time()
                .duration_since(span.start_time())
                .unwrap()
                .as_millis() as u64;

            if span.status() == opentelemetry::trace::Status::error("") {
                entry.error_count += 1;
            }
        }
    }

    dependencies.into_values().collect()
}
```

---

## 性能分析

### 延迟分析

```rust
// src/analysis/latency.rs
use std::collections::HashMap;

#[derive(Debug)]
pub struct LatencyStats {
    pub operation: String,
    pub count: u64,
    pub min_ms: u64,
    pub max_ms: u64,
    pub avg_ms: u64,
    pub p50_ms: u64,
    pub p95_ms: u64,
    pub p99_ms: u64,
}

pub fn analyze_latency(spans: Vec<SpanData>) -> Vec<LatencyStats> {
    let mut latencies_by_operation: HashMap<String, Vec<u64>> = HashMap::new();

    for span in spans {
        let operation = span.name().to_string();
        let duration_ms = span.end_time()
            .duration_since(span.start_time())
            .unwrap()
            .as_millis() as u64;

        latencies_by_operation
            .entry(operation)
            .or_insert_with(Vec::new)
            .push(duration_ms);
    }

    latencies_by_operation
        .into_iter()
        .map(|(operation, mut latencies)| {
            latencies.sort_unstable();
            
            let count = latencies.len() as u64;
            let min_ms = latencies[0];
            let max_ms = latencies[latencies.len() - 1];
            let avg_ms = latencies.iter().sum::<u64>() / count;
            
            let p50_ms = percentile(&latencies, 0.50);
            let p95_ms = percentile(&latencies, 0.95);
            let p99_ms = percentile(&latencies, 0.99);

            LatencyStats {
                operation,
                count,
                min_ms,
                max_ms,
                avg_ms,
                p50_ms,
                p95_ms,
                p99_ms,
            }
        })
        .collect()
}

fn percentile(sorted_data: &[u64], percentile: f64) -> u64 {
    let idx = (sorted_data.len() as f64 * percentile) as usize;
    sorted_data[idx.min(sorted_data.len() - 1)]
}
```

### 热点分析

```rust
// src/analysis/hotspot.rs

#[derive(Debug)]
pub struct Hotspot {
    pub operation: String,
    pub total_time_ms: u64,
    pub percentage: f64,
}

pub fn find_hotspots(spans: Vec<SpanData>) -> Vec<Hotspot> {
    let mut operation_times: HashMap<String, u64> = HashMap::new();
    let mut total_time_ms = 0u64;

    for span in spans {
        let operation = span.name().to_string();
        let duration_ms = span.end_time()
            .duration_since(span.start_time())
            .unwrap()
            .as_millis() as u64;

        *operation_times.entry(operation).or_insert(0) += duration_ms;
        total_time_ms += duration_ms;
    }

    let mut hotspots: Vec<Hotspot> = operation_times
        .into_iter()
        .map(|(operation, time_ms)| {
            let percentage = (time_ms as f64 / total_time_ms as f64) * 100.0;
            Hotspot {
                operation,
                total_time_ms: time_ms,
                percentage,
            }
        })
        .collect();

    hotspots.sort_by(|a, b| b.total_time_ms.cmp(&a.total_time_ms));
    hotspots
}
```

---

## 告警与异常检测

### 异常检测规则

```rust
// src/alerting/anomaly_detection.rs
use chrono::{DateTime, Utc};

#[derive(Debug)]
pub enum Anomaly {
    HighLatency {
        operation: String,
        actual_ms: u64,
        threshold_ms: u64,
    },
    HighErrorRate {
        service: String,
        error_rate: f64,
        threshold: f64,
    },
    UnusualPattern {
        description: String,
    },
}

pub struct AnomalyDetector {
    latency_thresholds: HashMap<String, u64>,
    error_rate_threshold: f64,
}

impl AnomalyDetector {
    pub fn new() -> Self {
        Self {
            latency_thresholds: HashMap::from([
                ("database_query".to_string(), 1000),
                ("api_call".to_string(), 500),
            ]),
            error_rate_threshold: 0.05, // 5%
        }
    }

    pub fn detect(&self, spans: &[SpanData]) -> Vec<Anomaly> {
        let mut anomalies = Vec::new();

        // 检测高延迟
        for span in spans {
            let operation = span.name();
            let duration_ms = span.end_time()
                .duration_since(span.start_time())
                .unwrap()
                .as_millis() as u64;

            if let Some(&threshold_ms) = self.latency_thresholds.get(operation) {
                if duration_ms > threshold_ms {
                    anomalies.push(Anomaly::HighLatency {
                        operation: operation.to_string(),
                        actual_ms: duration_ms,
                        threshold_ms,
                    });
                }
            }
        }

        // 检测高错误率
        let service_stats = self.calculate_service_error_rates(spans);
        for (service, error_rate) in service_stats {
            if error_rate > self.error_rate_threshold {
                anomalies.push(Anomaly::HighErrorRate {
                    service,
                    error_rate,
                    threshold: self.error_rate_threshold,
                });
            }
        }

        anomalies
    }

    fn calculate_service_error_rates(&self, spans: &[SpanData]) -> HashMap<String, f64> {
        let mut service_stats: HashMap<String, (u64, u64)> = HashMap::new();

        for span in spans {
            let service = span.resource()
                .get("service.name")
                .map(|v| v.to_string())
                .unwrap_or_default();

            let stats = service_stats.entry(service).or_insert((0, 0));
            stats.0 += 1; // 总数

            if span.status() == opentelemetry::trace::Status::error("") {
                stats.1 += 1; // 错误数
            }
        }

        service_stats
            .into_iter()
            .map(|(service, (total, errors))| {
                let error_rate = errors as f64 / total as f64;
                (service, error_rate)
            })
            .collect()
    }
}
```

### Prometheus 告警集成

```yaml
# prometheus-alerts.yml
groups:
  - name: tracing
    interval: 30s
    rules:
      - alert: HighTraceLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(otlp_span_duration_seconds_bucket[5m])) by (le, span_name)
          ) > 1.0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High trace latency detected"
          description: "P99 latency for {{ $labels.span_name }} is {{ $value }}s"

      - alert: HighErrorRate
        expr: |
          sum(rate(otlp_span_errors_total[5m])) by (service_name)
          /
          sum(rate(otlp_spans_total[5m])) by (service_name)
          > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate for {{ $labels.service_name }} is {{ $value | humanizePercentage }}"
```

---

## 最佳实践

### 1. 采样策略

```rust
// 生产环境采样策略
pub fn production_sampler() -> Box<dyn Sampler> {
    // 1. 始终采样错误
    // 2. 慢请求（>1s）100% 采样
    // 3. 其他请求 10% 采样
    Box::new(CustomSampler::new())
}
```

### 2. 属性标准化

```rust
// 确保所有服务使用一致的属性名
pub const STANDARD_ATTRIBUTES: &[&str] = &[
    "service.name",
    "service.version",
    "deployment.environment",
    "http.method",
    "http.status_code",
    "db.system",
    "db.operation",
];
```

### 3. 存储优化

```text
✅ 使用采样减少数据量
✅ 设置合理的数据保留期（如 7天）
✅ 使用压缩存储
✅ 冷热数据分离（Tempo + S3）
```

### 4. 查询优化

```text
✅ 为常用字段创建索引
✅ 使用时间范围限制查询
✅ 缓存常见查询结果
✅ 使用 TraceQL 精确查询
```

---

## 总结

### 工具选择建议

| 场景 | 推荐工具 | 原因 |
|------|---------|------|
| 快速上手 | Jaeger | UI友好、功能完整 |
| 成本优先 | Tempo | 对象存储成本低 |
| 已有Grafana | Tempo | 无缝集成 |
| 简单场景 | Zipkin | 轻量级、易部署 |

### 关键指标

```text
✅ P50/P95/P99 延迟
✅ 错误率
✅ 吞吐量（RPS）
✅ 服务依赖健康度
✅ 关键路径耗时
```

### 下一步行动

1. **选择可视化工具**: 根据需求选择 Jaeger/Tempo/Zipkin
2. **配置采样**: 平衡数据量和可见性
3. **设置告警**: 定义关键阈值
4. **定期Review**: 分析热点和瓶颈
5. **持续优化**: 根据数据调整系统

---

**文档作者**: OTLP Rust Team  
**创建日期**: 2025-10-08  
**许可证**: MIT OR Apache-2.0  
**相关文档**:

- [监控与告警](../20_监控与告警/01_Prometheus_Grafana完整集成指南.md)
- [性能基准测试](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)
- [Collector扩展](../22_Collector扩展/01_Rust_OTLP_Collector自定义扩展开发指南.md)
