# 📊 Grafana LGTM Stack + Rust 完整集成指南

> **文档版本**: v1.0  
> **创建日期**: 2025年10月11日  
> **Rust 版本**: 1.90+  
> **Grafana 版本**: 11.3.0  
> **LGTM Stack**: Loki 3.2 + Grafana Tempo 2.6 + Mimir 2.14  
> **难度等级**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [📊 Grafana LGTM Stack + Rust 完整集成指南](#-grafana-lgtm-stack--rust-完整集成指南)
  - [📋 目录](#-目录)
  - [🎯 LGTM Stack 概述](#-lgtm-stack-概述)
    - [什么是 LGTM Stack？](#什么是-lgtm-stack)
    - [为什么选择 LGTM？](#为什么选择-lgtm)
  - [🏗️ 架构设计](#️-架构设计)
    - [完整架构图](#完整架构图)
  - [📝 Grafana Loki (日志)](#-grafana-loki-日志)
    - [1. Loki 配置](#1-loki-配置)
    - [2. Rust + Loki 集成](#2-rust--loki-集成)
    - [3. LogQL 查询示例](#3-logql-查询示例)
  - [🔍 Grafana Tempo (追踪)](#-grafana-tempo-追踪)
    - [1. Tempo 配置](#1-tempo-配置)
    - [2. Rust + Tempo 集成](#2-rust--tempo-集成)
    - [3. TraceQL 查询示例](#3-traceql-查询示例)
  - [📈 Grafana Mimir (指标)](#-grafana-mimir-指标)
    - [1. Mimir 配置](#1-mimir-配置)
    - [2. Rust + Mimir 集成](#2-rust--mimir-集成)
    - [3. PromQL 查询示例](#3-promql-查询示例)
  - [🎨 Grafana 可视化](#-grafana-可视化)
    - [1. Dashboard JSON 配置](#1-dashboard-json-配置)
  - [🚀 完整部署](#-完整部署)
    - [Docker Compose 配置](#docker-compose-配置)
    - [Grafana 数据源配置](#grafana-数据源配置)
  - [🔗 关联查询](#-关联查询)
    - [Logs → Traces](#logs--traces)
    - [Traces → Logs](#traces--logs)
    - [Metrics → Traces](#metrics--traces)
  - [✅ 最佳实践](#-最佳实践)
    - [1. 采样策略](#1-采样策略)
    - [2. 保留策略](#2-保留策略)
  - [📚 参考资源](#-参考资源)

---

## 🎯 LGTM Stack 概述

### 什么是 LGTM Stack？

**LGTM** = **L**oki + **G**rafana + **T**empo + **M**imir

这是 Grafana Labs 提供的完整可观测性解决方案,包含:

| 组件 | 用途 | 特点 |
|------|------|------|
| **Loki** | 日志聚合 | 类似 Prometheus 的日志系统 |
| **Grafana** | 可视化 | 统一可视化平台 |
| **Tempo** | 分布式追踪 | 大规模追踪存储 |
| **Mimir** | 指标存储 | 高可用 Prometheus 后端 |

### 为什么选择 LGTM？

✅ **优势**:

1. **统一可观测性**: 日志、指标、追踪一站式解决方案
2. **开源免费**: 完全开源,可自托管
3. **高性能**: 专为大规模设计
4. **关联查询**: Logs ↔ Traces ↔ Metrics 无缝关联
5. **成本优化**: 使用对象存储(S3/GCS)降低成本

❌ **挑战**:

1. **运维复杂度**: 需要管理多个组件
2. **资源消耗**: 大规模部署需要充足资源
3. **学习曲线**: 每个组件都有独特的查询语言

---

## 🏗️ 架构设计

### 完整架构图

```text
┌─────────────────────────────────────────────────────────────────┐
│                        Rust Application                          │
│                                                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  tracing + opentelemetry                                  │  │
│  │  ├─ Logs    → Loki Exporter                               │  │
│  │  ├─ Traces  → OTLP Exporter → Tempo                       │  │
│  │  └─ Metrics → Prometheus Exporter → Mimir                 │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                      LGTM Stack                                  │
│                                                                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │ Grafana Loki │  │ Grafana Tempo│  │ Grafana Mimir│          │
│  │   (Logs)     │  │  (Traces)    │  │  (Metrics)   │          │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │
│         │                  │                  │                  │
│         │                  │                  │                  │
│         └──────────────────┼──────────────────┘                  │
│                            │                                      │
│                            ▼                                      │
│                  ┌──────────────────┐                            │
│                  │     Grafana      │                            │
│                  │  (Visualization) │                            │
│                  └──────────────────┘                            │
│                                                                  │
│  Storage Backend (S3/GCS/Local)                                 │
│  ├─ Loki Chunks                                                 │
│  ├─ Tempo Traces                                                │
│  └─ Mimir Blocks                                                │
└─────────────────────────────────────────────────────────────────┘
```

---

## 📝 Grafana Loki (日志)

### 1. Loki 配置

```yaml
# loki-config.yaml
auth_enabled: false

server:
  http_listen_port: 3100
  grpc_listen_port: 9096

common:
  instance_addr: 127.0.0.1
  path_prefix: /tmp/loki
  storage:
    filesystem:
      chunks_directory: /tmp/loki/chunks
      rules_directory: /tmp/loki/rules
  replication_factor: 1
  ring:
    kvstore:
      store: inmemory

query_range:
  results_cache:
    cache:
      embedded_cache:
        enabled: true
        max_size_mb: 100

schema_config:
  configs:
    - from: 2024-01-01
      store: tsdb
      object_store: filesystem
      schema: v13
      index:
        prefix: index_
        period: 24h

ruler:
  alertmanager_url: http://localhost:9093

# 限流配置
limits_config:
  enforce_metric_name: false
  reject_old_samples: true
  reject_old_samples_max_age: 168h
  max_cache_freshness_per_query: 10m
  split_queries_by_interval: 15m
  max_query_parallelism: 32
  max_streams_per_user: 10000
  max_global_streams_per_user: 50000
  max_query_series: 5000
```

### 2. Rust + Loki 集成

```rust
// src/logging/loki_exporter.rs
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use tracing_loki::Layer as LokiLayer;
use url::Url;

pub fn init_loki_logging(loki_url: &str) -> anyhow::Result<()> {
    let (layer, task) = LokiLayer::new(
        Url::parse(loki_url)?,
        vec![
            ("service".to_string(), "rust-app".to_string()),
            ("environment".to_string(), "production".to_string()),
        ].into_iter().collect(),
    )?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(layer)
        .init();

    // 启动后台任务发送日志
    tokio::spawn(task);

    Ok(())
}

/// 使用 LogQL 查询日志
pub async fn query_logs() -> anyhow::Result<()> {
    let client = reqwest::Client::new();
    
    // LogQL 查询
    let query = r#"{service="rust-app"} |= "error""#;
    
    let response = client
        .get("http://localhost:3100/loki/api/v1/query_range")
        .query(&[
            ("query", query),
            ("start", "1704067200000000000"), // Unix nano
            ("end", "1704153600000000000"),
        ])
        .send()
        .await?;

    let logs: serde_json::Value = response.json().await?;
    println!("查询结果: {:#?}", logs);

    Ok(())
}
```

### 3. LogQL 查询示例

```logql
# 1. 基本过滤
{service="rust-app", environment="production"} |= "error"

# 2. 正则表达式
{service="rust-app"} |~ "error|panic|fatal"

# 3. JSON 提取
{service="rust-app"} | json | level="error"

# 4. 统计错误数
sum(count_over_time({service="rust-app"} |= "error" [5m]))

# 5. 按端点分组的错误率
sum by (endpoint) (
  rate({service="rust-app"} |= "error" [5m])
)

# 6. P95 延迟
histogram_quantile(0.95,
  sum(rate({service="rust-app"} | json | unwrap latency_ms [5m])) by (le)
)
```

---

## 🔍 Grafana Tempo (追踪)

### 1. Tempo 配置

```yaml
# tempo-config.yaml
server:
  http_listen_port: 3200
  grpc_listen_port: 9095

distributor:
  receivers:
    otlp:
      protocols:
        http:
          endpoint: "0.0.0.0:4318"
        grpc:
          endpoint: "0.0.0.0:4317"

ingester:
  max_block_duration: 5m

compactor:
  compaction:
    block_retention: 24h

storage:
  trace:
    backend: local
    local:
      path: /tmp/tempo/blocks
    pool:
      max_workers: 100
      queue_depth: 10000

query_frontend:
  search:
    duration_slo: 5s
    throughput_bytes_slo: 1.073741824e+09
  trace_by_id:
    duration_slo: 5s

metrics_generator:
  registry:
    external_labels:
      source: tempo
  storage:
    path: /tmp/tempo/generator/wal
  traces_storage:
    path: /tmp/tempo/generator/traces
```

### 2. Rust + Tempo 集成

```rust
// src/tracing/tempo_exporter.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use std::time::Duration;

pub fn init_tempo_tracing(tempo_endpoint: &str) -> anyhow::Result<()> {
    // 1. 配置 OTLP Exporter (Tempo)
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(tempo_endpoint)
                .with_timeout(Duration::from_secs(3)),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::ParentBased(Box::new(
                    Sampler::TraceIdRatioBased(1.0) // 100% 采样
                )))
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "rust-app"),
                    KeyValue::new("deployment.environment", "production"),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 2. 配置 tracing-subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

/// 使用 TraceQL 查询追踪
pub async fn query_traces() -> anyhow::Result<()> {
    let client = reqwest::Client::new();
    
    // TraceQL 查询
    let query = r#"{ span.http.method = "GET" && duration > 100ms }"#;
    
    let response = client
        .get("http://localhost:3200/api/search")
        .query(&[
            ("q", query),
            ("start", "1704067200"),
            ("end", "1704153600"),
        ])
        .send()
        .await?;

    let traces: serde_json::Value = response.json().await?;
    println!("查询结果: {:#?}", traces);

    Ok(())
}
```

### 3. TraceQL 查询示例

```traceql
# 1. 查找慢请求
{ duration > 500ms }

# 2. 查找特定服务的错误
{ service.name = "rust-app" && status = error }

# 3. 查找包含数据库调用的追踪
{ span.db.system = "postgresql" }

# 4. 复杂查询
{
  service.name = "rust-app" &&
  span.http.method = "POST" &&
  span.http.status_code >= 500 &&
  duration > 100ms
}

# 5. 聚合查询
# 按服务分组的平均延迟
rate({ service.name = "rust-app" }) by (service.name)
```

---

## 📈 Grafana Mimir (指标)

### 1. Mimir 配置

```yaml
# mimir-config.yaml
multitenancy_enabled: false

server:
  http_listen_port: 9009
  grpc_listen_port: 9095

distributor:
  pool:
    health_check_ingesters: true

ingester:
  ring:
    final_sleep: 0s
    num_tokens: 512
    replication_factor: 1

blocks_storage:
  backend: filesystem
  bucket_store:
    sync_dir: /tmp/mimir/tsdb-sync
  filesystem:
    dir: /tmp/mimir/blocks
  tsdb:
    dir: /tmp/mimir/tsdb

compactor:
  data_dir: /tmp/mimir/compactor
  sharding_ring:
    kvstore:
      store: memberlist

store_gateway:
  sharding_ring:
    replication_factor: 1

ruler:
  rule_path: /tmp/mimir/rules

limits:
  max_global_series_per_user: 0
  max_global_exemplars_per_user: 100000
  ingestion_rate: 10000
  ingestion_burst_size: 200000
```

### 2. Rust + Mimir 集成

```rust
// src/metrics/mimir_exporter.rs
use metrics_exporter_prometheus::PrometheusBuilder;
use std::net::SocketAddr;

pub fn init_mimir_metrics(listen_addr: SocketAddr) -> anyhow::Result<()> {
    // Prometheus Exporter (Mimir 兼容 Prometheus)
    PrometheusBuilder::new()
        .with_http_listener(listen_addr)
        .install()?;

    Ok(())
}

/// 记录业务指标
pub fn record_business_metrics() {
    // Counter
    metrics::counter!("http_requests_total", 
        "method" => "GET", 
        "path" => "/api/users"
    ).increment(1);

    // Gauge
    metrics::gauge!("active_connections").set(42.0);

    // Histogram
    metrics::histogram!("http_request_duration_seconds").record(0.035);
}

/// Prometheus 配置 (抓取 Rust 应用指标)
pub fn prometheus_config() -> &'static str {
    r#"
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'production'

remote_write:
  - url: http://mimir:9009/api/v1/push

scrape_configs:
  - job_name: 'rust-app'
    static_configs:
      - targets: ['rust-app:9090']
    "#
}
```

### 3. PromQL 查询示例

```promql
# 1. HTTP 请求速率 (每秒)
rate(http_requests_total[5m])

# 2. P95 延迟
histogram_quantile(0.95, 
  rate(http_request_duration_seconds_bucket[5m])
)

# 3. 错误率
sum(rate(http_requests_total{status=~"5.."}[5m])) 
/ 
sum(rate(http_requests_total[5m]))

# 4. 按路径分组的请求量
sum by (path) (
  rate(http_requests_total[5m])
)

# 5. CPU 使用率
100 - (avg by (instance) (
  rate(node_cpu_seconds_total{mode="idle"}[5m])
) * 100)
```

---

## 🎨 Grafana 可视化

### 1. Dashboard JSON 配置

```json
{
  "dashboard": {
    "title": "Rust OTLP - LGTM 完整可观测性",
    "tags": ["rust", "otlp", "lgtm"],
    "timezone": "browser",
    "panels": [
      {
        "id": 1,
        "title": "HTTP 请求速率",
        "type": "graph",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total[5m])) by (method)",
            "legendFormat": "{{method}}",
            "datasource": "Mimir"
          }
        ]
      },
      {
        "id": 2,
        "title": "请求延迟 (P50/P95/P99)",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.50, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P50",
            "datasource": "Mimir"
          },
          {
            "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P95",
            "datasource": "Mimir"
          },
          {
            "expr": "histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P99",
            "datasource": "Mimir"
          }
        ]
      },
      {
        "id": 3,
        "title": "错误日志",
        "type": "logs",
        "targets": [
          {
            "expr": "{service=\"rust-app\"} |= \"error\"",
            "datasource": "Loki"
          }
        ]
      },
      {
        "id": 4,
        "title": "分布式追踪",
        "type": "traces",
        "targets": [
          {
            "query": "{ service.name = \"rust-app\" }",
            "datasource": "Tempo"
          }
        ]
      }
    ],
    "templating": {
      "list": [
        {
          "name": "service",
          "type": "query",
          "query": "label_values(http_requests_total, service)",
          "datasource": "Mimir"
        }
      ]
    }
  }
}
```

---

## 🚀 完整部署

### Docker Compose 配置

```yaml
# docker-compose.yml
version: '3.9'

services:
  # Rust 应用
  rust-app:
    build: .
    ports:
      - "3000:3000"   # HTTP API
      - "9090:9090"   # Prometheus Metrics
    environment:
      RUST_LOG: info,rust_app=debug
      LOKI_URL: http://loki:3100
      TEMPO_ENDPOINT: http://tempo:4317
      MIMIR_ENDPOINT: http://mimir:9009
    depends_on:
      - loki
      - tempo
      - mimir

  # Grafana Loki (日志)
  loki:
    image: grafana/loki:3.2.0
    ports:
      - "3100:3100"
    volumes:
      - ./config/loki-config.yaml:/etc/loki/local-config.yaml
      - loki-data:/tmp/loki
    command: -config.file=/etc/loki/local-config.yaml

  # Grafana Tempo (追踪)
  tempo:
    image: grafana/tempo:2.6.0
    ports:
      - "3200:3200"   # Tempo HTTP
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
    volumes:
      - ./config/tempo-config.yaml:/etc/tempo.yaml
      - tempo-data:/tmp/tempo
    command: -config.file=/etc/tempo.yaml

  # Grafana Mimir (指标)
  mimir:
    image: grafana/mimir:2.14.0
    ports:
      - "9009:9009"   # Mimir HTTP
    volumes:
      - ./config/mimir-config.yaml:/etc/mimir.yaml
      - mimir-data:/tmp/mimir
    command: -config.file=/etc/mimir.yaml

  # Prometheus (抓取器)
  prometheus:
    image: prom/prometheus:v2.54.0
    ports:
      - "9091:9090"
    volumes:
      - ./config/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.enable-remote-write-receiver'

  # Grafana (可视化)
  grafana:
    image: grafana/grafana:11.3.0
    ports:
      - "3001:3000"
    environment:
      GF_FEATURE_TOGGLES_ENABLE: traceToMetrics,traceToLogs
      GF_AUTH_ANONYMOUS_ENABLED: "true"
      GF_AUTH_ANONYMOUS_ORG_ROLE: Admin
    volumes:
      - ./config/grafana-datasources.yaml:/etc/grafana/provisioning/datasources/datasources.yaml
      - ./config/grafana-dashboards.yaml:/etc/grafana/provisioning/dashboards/dashboards.yaml
      - ./dashboards:/var/lib/grafana/dashboards
      - grafana-data:/var/lib/grafana
    depends_on:
      - loki
      - tempo
      - mimir

volumes:
  loki-data:
  tempo-data:
  mimir-data:
  prometheus-data:
  grafana-data:
```

### Grafana 数据源配置

```yaml
# config/grafana-datasources.yaml
apiVersion: 1

datasources:
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    isDefault: false

  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    isDefault: false

  - name: Mimir
    type: prometheus
    access: proxy
    url: http://mimir:9009/prometheus
    isDefault: true
    jsonData:
      httpMethod: POST
```

---

## 🔗 关联查询

### Logs → Traces

```logql
# 在日志中点击 trace_id 跳转到追踪
{service="rust-app"} | json | trace_id != ""
```

### Traces → Logs

```traceql
# 在追踪中查看相关日志
{ span.trace_id = "abc123" }
```

### Metrics → Traces

```promql
# 点击高延迟指标跳转到慢追踪
histogram_quantile(0.99, 
  rate(http_request_duration_seconds_bucket[5m])
)
```

---

## ✅ 最佳实践

### 1. 采样策略

```rust
// 生产环境: 1% 采样
Sampler::TraceIdRatioBased(0.01)

// 开发环境: 100% 采样
Sampler::AlwaysOn
```

### 2. 保留策略

```yaml
# Loki: 保留 7 天
limits_config:
  retention_period: 168h

# Tempo: 保留 24 小时
compactor:
  compaction:
    block_retention: 24h

# Mimir: 保留 15 天
limits:
  compactor_blocks_retention_period: 15d
```

---

## 📚 参考资源

- [Grafana Loki 文档](https://grafana.com/docs/loki/)
- [Grafana Tempo 文档](https://grafana.com/docs/tempo/)
- [Grafana Mimir 文档](https://grafana.com/docs/mimir/)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日

---

**📊 使用 Grafana LGTM Stack 构建完整可观测性！🚀**-
