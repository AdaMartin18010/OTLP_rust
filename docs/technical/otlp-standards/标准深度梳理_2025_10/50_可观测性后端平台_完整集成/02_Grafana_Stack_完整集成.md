# Grafana Stack 完整集成指南 (Rust + OTLP)

## 目录

- [Grafana Stack 完整集成指南 (Rust + OTLP)](#grafana-stack-完整集成指南-rust--otlp)
  - [目录](#目录)
  - [1. Grafana Stack 架构](#1-grafana-stack-架构)
    - [1.1 国际标准对标](#11-国际标准对标)
  - [2. Rust 应用集成](#2-rust-应用集成)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 完整 Telemetry 初始化](#22-完整-telemetry-初始化)
  - [3. Loki 日志集成](#3-loki-日志集成)
    - [3.1 Promtail 配置](#31-promtail-配置)
    - [3.2 Rust 应用日志输出](#32-rust-应用日志输出)
  - [4. Tempo 追踪集成](#4-tempo-追踪集成)
    - [4.1 Tempo 配置](#41-tempo-配置)
    - [4.2 Rust 分布式追踪](#42-rust-分布式追踪)
  - [5. Prometheus 指标集成](#5-prometheus-指标集成)
    - [5.1 Prometheus 配置](#51-prometheus-配置)
    - [5.2 Rust 应用指标](#52-rust-应用指标)
  - [6. 完整部署](#6-完整部署)
    - [6.1 Docker Compose](#61-docker-compose)
    - [6.2 Grafana 数据源配置](#62-grafana-数据源配置)
    - [6.3 Grafana Dashboard (JSON 模板)](#63-grafana-dashboard-json-模板)
  - [总结](#总结)

## 1. Grafana Stack 架构

```text
┌──────────────────────────────────────────────────────────┐
│                    Rust 应用程序                          │
│  • Logs → Loki                                           │
│  • Traces → Tempo                                        │
│  • Metrics → Prometheus                                  │
└──────────────────────────────────────────────────────────┘
                           │
        ┌──────────────────┼──────────────────┐
        ▼                  ▼                  ▼
┌──────────────┐  ┌──────────────┐  ┌──────────────────┐
│    Loki      │  │    Tempo     │  │   Prometheus     │
│  (Logs)      │  │  (Traces)    │  │   (Metrics)      │
└──────────────┘  └──────────────┘  └──────────────────┘
        │                  │                  │
        └──────────────────┼──────────────────┘
                           ▼
                  ┌──────────────────┐
                  │     Grafana      │
                  │  (Visualization) │
                  └──────────────────┘
```

### 1.1 国际标准对标

| 组件 | 标准 | 文档 |
|------|------|------|
| **Loki** | LogQL | [Loki Docs](https://grafana.com/docs/loki/latest/) |
| **Tempo** | OTLP, Jaeger, Zipkin | [Tempo Docs](https://grafana.com/docs/tempo/latest/) |
| **Prometheus** | OpenMetrics | [Prometheus Docs](https://prometheus.io/docs/) |
| **Grafana** | JSON Model | [Grafana Docs](https://grafana.com/docs/grafana/latest/) |

---

## 2. Rust 应用集成

### 2.1 Cargo.toml

```toml
[dependencies]
# OpenTelemetry
opentelemetry = { version = "0.31", features = ["trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic", "metrics", "trace", "logs"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# Metrics
metrics = "0.24"
metrics-exporter-prometheus = "0.16"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
```

### 2.2 完整 Telemetry 初始化

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config as TraceConfig, TracerProvider},
    metrics::{SdkMeterProvider, PeriodicReader},
    logs::{Config as LogConfig, LoggerProvider},
    Resource,
    runtime,
};
use opentelemetry_otlp::{WithExportConfig, Protocol};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use std::time::Duration;

pub fn init_grafana_stack() -> anyhow::Result<()> {
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());

    // 1. Tempo 追踪配置
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint)
                .with_protocol(Protocol::Grpc)
        )
        .with_trace_config(
            TraceConfig::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "rust-app"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
        )
        .install_batch(runtime::Tokio)?;

    // 2. Prometheus 指标配置
    let prometheus_exporter = metrics_exporter_prometheus::PrometheusBuilder::new()
        .with_http_listener(([0, 0, 0, 0], 9090))
        .install()?;

    // 3. Loki 日志配置 (通过 tracing-subscriber)
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer()
            .json()
            .with_target(true)
            .with_thread_ids(true)
            .with_line_number(true)
        )
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!("Grafana Stack telemetry initialized");

    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

---

## 3. Loki 日志集成

### 3.1 Promtail 配置

```yaml
# promtail-config.yaml
server:
  http_listen_port: 9080
  grpc_listen_port: 0

positions:
  filename: /tmp/positions.yaml

clients:
  - url: http://loki:3100/loki/api/v1/push

scrape_configs:
  - job_name: rust-app
    static_configs:
      - targets:
          - localhost
        labels:
          job: rust-app
          __path__: /var/log/rust-app/*.log
    pipeline_stages:
      # 解析 JSON 日志
      - json:
          expressions:
            timestamp: timestamp
            level: level
            message: message
            target: target
      - labels:
          level:
          target:
      - timestamp:
          source: timestamp
          format: RFC3339
```

### 3.2 Rust 应用日志输出

```rust
// src/main.rs
use tracing::{info, warn, error};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    telemetry::init_grafana_stack()?;

    info!(
        user_id = "12345",
        action = "login",
        ip = "192.168.1.1",
        "User logged in successfully"
    );

    warn!(
        latency_ms = 1500,
        endpoint = "/api/users",
        "Slow query detected"
    );

    error!(
        error = "Connection refused",
        service = "database",
        "Failed to connect to database"
    );

    Ok(())
}
```

---

## 4. Tempo 追踪集成

### 4.1 Tempo 配置

```yaml
# tempo-config.yaml
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

storage:
  trace:
    backend: local
    local:
      path: /var/tempo/traces

query_frontend:
  search:
    enabled: true
```

### 4.2 Rust 分布式追踪

```rust
use tracing::{info_span, instrument, Instrument};

#[instrument]
async fn handle_request(user_id: &str) -> Result<()> {
    info!("Processing request");

    // 子 Span 自动传播
    let user = fetch_user(user_id).await?;
    let orders = fetch_orders(user_id).await?;

    Ok(())
}

#[instrument(skip(db_pool))]
async fn fetch_user(user_id: &str) -> Result<User> {
    // Tempo 会自动关联此 Span 到父 Span
    sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", user_id)
        .fetch_one(&db_pool)
        .await
}

#[instrument(skip(db_pool))]
async fn fetch_orders(user_id: &str) -> Result<Vec<Order>> {
    sqlx::query_as!(Order, "SELECT * FROM orders WHERE user_id = $1", user_id)
        .fetch_all(&db_pool)
        .await
}
```

---

## 5. Prometheus 指标集成

### 5.1 Prometheus 配置

```yaml
# prometheus.yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'rust-app'
    static_configs:
      - targets: ['rust-app:9090']
    metric_relabel_configs:
      - source_labels: [__name__]
        regex: 'go_.*'
        action: drop

  - job_name: 'tempo'
    static_configs:
      - targets: ['tempo:3200']
```

### 5.2 Rust 应用指标

```rust
use metrics::{counter, histogram, gauge, describe_counter, describe_histogram};

pub fn init_metrics() {
    describe_counter!("http_requests_total", "Total HTTP requests");
    describe_histogram!("http_request_duration_seconds", "HTTP request latency");
    describe_counter!("database_queries_total", "Total database queries");
}

#[instrument]
async fn handle_http_request(path: &str) -> Result<Response> {
    let start = std::time::Instant::now();

    counter!("http_requests_total", "method" => "GET", "path" => path).increment(1);

    // 处理请求
    let response = process_request(path).await?;

    let duration = start.elapsed().as_secs_f64();
    histogram!("http_request_duration_seconds", "path" => path).record(duration);

    // 活跃连接数
    gauge!("active_connections").increment(1.0);

    Ok(response)
}

#[instrument]
async fn query_database(sql: &str) -> Result<Vec<Row>> {
    counter!("database_queries_total", "type" => "SELECT").increment(1);

    let start = std::time::Instant::now();
    let result = sqlx::query(sql).fetch_all(&pool).await?;
    let duration = start.elapsed().as_secs_f64();

    histogram!("database_query_duration_seconds").record(duration);

    Ok(result)
}
```

---

## 6. 完整部署

### 6.1 Docker Compose

```yaml
version: '3.8'

services:
  rust-app:
    build: .
    ports:
      - "8080:8080"
      - "9090:9090"  # Prometheus metrics
    environment:
      OTLP_ENDPOINT: http://tempo:4317
      RUST_LOG: info
    volumes:
      - ./logs:/var/log/rust-app
    depends_on:
      - tempo
      - loki
      - prometheus

  # Tempo (分布式追踪)
  tempo:
    image: grafana/tempo:2.7.2
    command: ["-config.file=/etc/tempo.yaml"]
    volumes:
      - ./tempo-config.yaml:/etc/tempo.yaml
      - tempo-data:/var/tempo
    ports:
      - "3200:3200"   # Tempo HTTP
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP

  # Loki (日志聚合)
  loki:
    image: grafana/loki:3.3.2
    ports:
      - "3100:3100"
    command: -config.file=/etc/loki/local-config.yaml
    volumes:
      - loki-data:/loki

  # Promtail (日志收集)
  promtail:
    image: grafana/promtail:3.3.2
    volumes:
      - ./logs:/var/log/rust-app
      - ./promtail-config.yaml:/etc/promtail/config.yaml
    command: -config.file=/etc/promtail/config.yaml

  # Prometheus (指标收集)
  prometheus:
    image: prom/prometheus:v3.1.0
    volumes:
      - ./prometheus.yaml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.enable-lifecycle'
    ports:
      - "9091:9090"

  # Grafana (可视化)
  grafana:
    image: grafana/grafana:11.4.0
    ports:
      - "3000:3000"
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-datasources.yaml:/etc/grafana/provisioning/datasources/datasources.yaml
      - ./grafana-dashboards.yaml:/etc/grafana/provisioning/dashboards/dashboards.yaml
    depends_on:
      - loki
      - tempo
      - prometheus

volumes:
  tempo-data:
  loki-data:
  prometheus-data:
  grafana-data:
```

### 6.2 Grafana 数据源配置

```yaml
# grafana-datasources.yaml
apiVersion: 1

datasources:
  # Loki
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    isDefault: false

  # Tempo
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    isDefault: false

  # Prometheus
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
```

### 6.3 Grafana Dashboard (JSON 模板)

```json
{
  "dashboard": {
    "title": "Rust Application Observability",
    "panels": [
      {
        "title": "HTTP Request Rate",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "datasource": "Prometheus"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Request Latency (P99)",
        "targets": [
          {
            "expr": "histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))",
            "datasource": "Prometheus"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Recent Logs",
        "targets": [
          {
            "expr": "{job=\"rust-app\"}",
            "datasource": "Loki"
          }
        ],
        "type": "logs"
      },
      {
        "title": "Trace Explorer",
        "targets": [
          {
            "query": "service.name=\"rust-app\"",
            "datasource": "Tempo"
          }
        ],
        "type": "tempo-search"
      }
    ]
  }
}
```

---

## 总结

✅ **Grafana Stack 完整集成** (Loki + Tempo + Prometheus + Grafana)  
✅ **统一可观测性** (日志 + 追踪 + 指标)  
✅ **OTLP 标准** (OpenTelemetry Protocol)  
✅ **生产级部署** (Docker Compose + K8s)  
✅ **自定义 Dashboard** (JSON 模板)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
