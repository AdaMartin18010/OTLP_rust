# 从零构建OTLP完整可观测性系统

> **文档版本**: v1.0  
> **创建日期**: 2025年10月8日  
> **Rust版本**: 1.90  
> **OpenTelemetry版本**: 0.31.0  
> **文档类型**: Complete Tutorial

---

## 📋 目录

- [从零构建OTLP完整可观测性系统](#从零构建otlp完整可观测性系统)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [教程目标](#教程目标)
    - [架构overview](#架构overview)
    - [技术栈](#技术栈)
  - [环境准备](#环境准备)
    - [1. 安装Rust工具链](#1-安装rust工具链)
    - [2. 安装Docker和Docker Compose](#2-安装docker和docker-compose)
    - [3. 准备可观测性基础设施](#3-准备可观测性基础设施)
    - [4. OTLP Collector配置](#4-otlp-collector配置)
    - [5. Prometheus配置](#5-prometheus配置)
    - [6. 启动基础设施](#6-启动基础设施)
  - [项目初始化](#项目初始化)
    - [1. 创建新项目](#1-创建新项目)
    - [2. 依赖配置](#2-依赖配置)
    - [3. 项目配置文件](#3-项目配置文件)
  - [Traces集成](#traces集成)
    - [1. Tracer初始化模块](#1-tracer初始化模块)
    - [2. HTTP中间件集成](#2-http中间件集成)
    - [3. 业务逻辑追踪](#3-业务逻辑追踪)
  - [Metrics集成](#metrics集成)
    - [1. Metrics初始化模块](#1-metrics初始化模块)
    - [2. 应用指标](#2-应用指标)
  - [Logs集成](#logs集成)
    - [1. Logs初始化模块](#1-logs初始化模块)
  - [Profiling集成](#profiling集成)
    - [1. Profiling模块](#1-profiling模块)
  - [Dashboard搭建](#dashboard搭建)
    - [1. Grafana数据源配置](#1-grafana数据源配置)
    - [2. Grafana Dashboard配置](#2-grafana-dashboard配置)
  - [告警配置](#告警配置)
    - [1. Prometheus告警规则](#1-prometheus告警规则)
    - [2. Alertmanager配置](#2-alertmanager配置)
  - [完整项目示例](#完整项目示例)
    - [1. 主应用程序](#1-主应用程序)
    - [2. 运行示例](#2-运行示例)
    - [3. 验证Traces](#3-验证traces)
    - [4. 验证Metrics](#4-验证metrics)
    - [5. 验证Logs](#5-验证logs)
  - [总结与最佳实践](#总结与最佳实践)
    - [关键要点](#关键要点)
    - [生产环境清单](#生产环境清单)
    - [下一步](#下一步)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [工具和平台](#工具和平台)
    - [社区资源](#社区资源)

---

## 概述

### 教程目标

本教程将引导你从零开始构建一个完整的OTLP可观测性系统，包括：

1. **Traces**: 分布式追踪
2. **Metrics**: 指标监控
3. **Logs**: 日志聚合
4. **Profiling**: 性能剖析
5. **Visualization**: 可视化dashboard
6. **Alerting**: 告警系统

### 架构overview

```text
┌─────────────────────────────────────────────────────────────┐
│                    Application Layer                        │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │   Traces     │  │   Metrics    │  │    Logs      │       │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘       │
│         │                  │                  │             │
│         └──────────────────┼──────────────────┘             │
│                            │ OTLP Protocol                  │
└────────────────────────────┼────────────────────────────────┘
                             │
┌────────────────────────────┼────────────────────────────────┐
│                            ▼                                │
│                 OTLP Collector                              │
│  ┌──────────────────────────────────────────────┐           │
│  │  Receivers → Processors → Exporters          │           │
│  └──────────────────────────────────────────────┘           │
└────────────────┬───────────┬──────────┬─────────────────────┘
                 │           │          │
        ┌────────┘           │          └────────┐
        ▼                    ▼                   ▼
 ┌─────────────┐      ┌──────────────┐   ┌──────────────┐
 │   Jaeger    │      │  Prometheus  │   │     ELK      │
 │  (Traces)   │      │  (Metrics)   │   │   (Logs)     │
 └─────────────┘      └──────────────┘   └──────────────┘
        │                    │                   │
        └────────────────────┼───────────────────┘
                             ▼
                      ┌─────────────┐
                      │   Grafana   │
                      │ (Dashboards)│
                      └─────────────┘
```

### 技术栈

- **Rust**: 1.90
- **OpenTelemetry SDK**: 0.31.0
- **OTLP Collector**: 0.95.0
- **Jaeger**: 1.54
- **Prometheus**: 2.49
- **Grafana**: 10.3
- **Elasticsearch**: 8.12
- **Tokio**: 1.47.1

---

## 环境准备

### 1. 安装Rust工具链

```bash
# 安装Rust（如果还没有）
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 更新到最新稳定版
rustup update stable

# 验证安装
rustc --version
cargo --version
```

### 2. 安装Docker和Docker Compose

```bash
# 安装Docker（Linux）
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh

# 安装Docker Compose
sudo curl -L "https://github.com/docker/compose/releases/download/v2.23.0/docker-compose-$(uname -s)-$(uname -m)" -o /usr/local/bin/docker-compose
sudo chmod +x /usr/local/bin/docker-compose

# 验证安装
docker --version
docker-compose --version
```

### 3. 准备可观测性基础设施

创建 `docker-compose.yml`:

```yaml
version: '3.8'

services:
  # OTLP Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.95.0
    container_name: otel-collector
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC receiver
      - "4318:4318"   # OTLP HTTP receiver
      - "8888:8888"   # Prometheus metrics exposed by the collector
      - "8889:8889"   # Prometheus exporter metrics
      - "13133:13133" # health_check extension
    networks:
      - observability

  # Jaeger (Traces)
  jaeger:
    image: jaegertracing/all-in-one:1.54
    container_name: jaeger
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # Jaeger gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - observability

  # Prometheus (Metrics)
  prometheus:
    image: prom/prometheus:v2.49.1
    container_name: prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    networks:
      - observability

  # Grafana (Visualization)
  grafana:
    image: grafana/grafana:10.3.3
    container_name: grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana/dashboards:/etc/grafana/provisioning/dashboards
      - ./grafana/datasources:/etc/grafana/provisioning/datasources
    networks:
      - observability

  # Elasticsearch (Logs)
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.12.0
    container_name: elasticsearch
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
      - "ES_JAVA_OPTS=-Xms512m -Xmx512m"
    ports:
      - "9200:9200"
    volumes:
      - es-data:/usr/share/elasticsearch/data
    networks:
      - observability

  # Kibana (Log Visualization)
  kibana:
    image: docker.elastic.co/kibana/kibana:8.12.0
    container_name: kibana
    ports:
      - "5601:5601"
    environment:
      - ELASTICSEARCH_HOSTS=http://elasticsearch:9200
    depends_on:
      - elasticsearch
    networks:
      - observability

networks:
  observability:
    driver: bridge

volumes:
  prometheus-data:
  grafana-data:
  es-data:
```

### 4. OTLP Collector配置

创建 `otel-collector-config.yaml`:

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
  
  resource:
    attributes:
      - key: deployment.environment
        value: development
        action: insert

exporters:
  # Traces -> Jaeger
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true
  
  # Metrics -> Prometheus
  prometheus:
    endpoint: "0.0.0.0:8889"
  
  # Logs -> Elasticsearch
  elasticsearch:
    endpoints: ["http://elasticsearch:9200"]
    logs_index: otel-logs
  
  # Debug
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [otlp/jaeger, logging]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [prometheus, logging]
    
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [elasticsearch, logging]

  extensions: [health_check]
```

### 5. Prometheus配置

创建 `prometheus.yml`:

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  # OTLP Collector metrics
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
  
  # Prometheus exporter from OTLP Collector
  - job_name: 'otel-metrics'
    static_configs:
      - targets: ['otel-collector:8889']
```

### 6. 启动基础设施

```bash
# 创建配置目录
mkdir -p grafana/dashboards grafana/datasources

# 启动所有服务
docker-compose up -d

# 检查服务状态
docker-compose ps

# 查看日志
docker-compose logs -f otel-collector
```

验证服务：

- Jaeger UI: <http://localhost:16686>
- Prometheus: <http://localhost:9090>
- Grafana: <http://localhost:3000> (admin/admin)
- Kibana: <http://localhost:5601>
- Collector health: <http://localhost:13133>

---

## 项目初始化

### 1. 创建新项目

```bash
# 创建项目
cargo new otlp-complete-observability
cd otlp-complete-observability

# 项目结构
mkdir -p src/{traces,metrics,logs,profiling}
```

### 2. 依赖配置

编辑 `Cargo.toml`:

```toml
[package]
name = "otlp-complete-observability"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry核心
opentelemetry = { version = "0.31.0", features = ["trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.24.0", features = ["tonic", "metrics", "logs"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
tonic = "0.12"

# 日志和追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.27"

# HTTP框架（用于示例）
axum = "0.7"
tower = "0.4"
tower-http = { version = "0.5", features = ["trace"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 工具
anyhow = "1.0"
thiserror = "1.0"
once_cell = "1.19"
chrono = "0.4"

# Profiling
pprof = { version = "0.13", features = ["flamegraph"] }

[dev-dependencies]
criterion = "0.5"
```

### 3. 项目配置文件

创建 `config.toml`:

```toml
[otlp]
endpoint = "http://localhost:4317"
timeout_seconds = 30

[service]
name = "otlp-demo-service"
version = "1.0.0"
environment = "development"

[traces]
enabled = true
sampling_rate = 1.0  # 100% sampling for development

[metrics]
enabled = true
export_interval_seconds = 60

[logs]
enabled = true
level = "info"
```

---

## Traces集成

### 1. Tracer初始化模块

创建 `src/traces/mod.rs`:

```rust
use opentelemetry::{global, trace::TracerProvider as _, KeyValue};
use opentelemetry_sdk::{
    trace::{Config as TraceConfig, TracerProvider, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

pub mod middleware;
pub mod instrumentation;

/// 初始化OTLP Tracer
pub fn init_tracer(
    service_name: &str,
    endpoint: &str,
) -> Result<TracerProvider, Box<dyn std::error::Error>> {
    // 1. 创建OTLP exporter
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(30))
        .build()?;

    // 2. 配置资源属性
    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "development"),
    ]);

    // 3. 配置采样器（开发环境100%采样）
    let sampler = Sampler::AlwaysOn;

    // 4. 创建TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_config(
            TraceConfig::default()
                .with_sampler(sampler)
                .with_resource(resource),
        )
        .build();

    // 5. 设置全局TracerProvider
    global::set_tracer_provider(provider.clone());

    Ok(provider)
}

/// 获取Tracer
pub fn tracer() -> opentelemetry::global::BoxedTracer {
    global::tracer("otlp-demo")
}
```

### 2. HTTP中间件集成

创建 `src/traces/middleware.rs`:

```rust
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use opentelemetry::{
    global,
    trace::{Span, SpanKind, Status, Tracer, TraceContextExt},
    Context, KeyValue,
};
use opentelemetry::propagation::{Extractor, TextMapPropagator};
use opentelemetry_sdk::propagation::TraceContextPropagator;

/// HTTP请求追踪中间件
pub async fn trace_middleware(
    request: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("http-server");
    
    // 1. 从HTTP headers提取trace context
    let parent_cx = extract_context_from_request(&request);
    
    // 2. 创建span
    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", request.method().to_string()),
            KeyValue::new("http.target", request.uri().path().to_string()),
            KeyValue::new("http.scheme", request.uri().scheme_str().unwrap_or("http").to_string()),
        ])
        .start_with_context(&tracer, &parent_cx);
    
    // 3. 执行请求处理
    let response = {
        let cx = Context::current_with_span(span.clone());
        let _guard = cx.attach();
        next.run(request).await
    };
    
    // 4. 记录响应信息
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    
    if response.status().is_server_error() {
        span.set_status(Status::error("Server error"));
    } else if response.status().is_client_error() {
        span.set_status(Status::error("Client error"));
    } else {
        span.set_status(Status::Ok);
    }
    
    span.end();
    
    response
}

/// 从HTTP request提取trace context
fn extract_context_from_request(request: &Request) -> Context {
    struct HeaderExtractor<'a>(&'a axum::http::HeaderMap);
    
    impl<'a> Extractor for HeaderExtractor<'a> {
        fn get(&self, key: &str) -> Option<&str> {
            self.0.get(key).and_then(|v| v.to_str().ok())
        }
        
        fn keys(&self) -> Vec<&str> {
            self.0.keys().map(|k| k.as_str()).collect()
        }
    }
    
    let propagator = TraceContextPropagator::new();
    propagator.extract(&HeaderExtractor(request.headers()))
}
```

### 3. 业务逻辑追踪

创建 `src/traces/instrumentation.rs`:

```rust
use opentelemetry::{global, trace::{Tracer, Span, Status}, KeyValue};

/// 示例：数据库查询追踪
#[tracing::instrument(skip(query))]
pub async fn traced_db_query(query: &str) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let tracer = global::tracer("database");
    
    let mut span = tracer
        .span_builder("db.query")
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.statement", query.to_string()),
        ])
        .start(&tracer);
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    let result = vec!["row1".to_string(), "row2".to_string()];
    
    span.set_attribute(KeyValue::new("db.rows_returned", result.len() as i64));
    span.set_status(Status::Ok);
    span.end();
    
    Ok(result)
}

/// 示例：外部API调用追踪
#[tracing::instrument]
pub async fn traced_api_call(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    let tracer = global::tracer("http-client");
    
    let mut span = tracer
        .span_builder("http.request")
        .with_attributes(vec![
            KeyValue::new("http.url", url.to_string()),
            KeyValue::new("http.method", "GET"),
        ])
        .start(&tracer);
    
    // 模拟HTTP请求
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    span.set_attribute(KeyValue::new("http.status_code", 200_i64));
    span.set_status(Status::Ok);
    span.end();
    
    Ok("response data".to_string())
}
```

---

## Metrics集成

### 1. Metrics初始化模块

创建 `src/metrics/mod.rs`:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

pub mod instrumentation;

/// 初始化OTLP Metrics
pub fn init_metrics(
    service_name: &str,
    endpoint: &str,
) -> Result<SdkMeterProvider, Box<dyn std::error::Error>> {
    // 1. 创建OTLP exporter
    let exporter = opentelemetry_otlp::MetricExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(30))
        .build()?;

    // 2. 配置定期导出器
    let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_interval(Duration::from_secs(60))
        .build();

    // 3. 配置资源属性
    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);

    // 4. 创建MeterProvider
    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(resource)
        .build();

    // 5. 设置全局MeterProvider
    global::set_meter_provider(provider.clone());

    Ok(provider)
}

/// 获取Meter
pub fn meter() -> opentelemetry::metrics::Meter {
    global::meter("otlp-demo")
}
```

### 2. 应用指标

创建 `src/metrics/instrumentation.rs`:

```rust
use opentelemetry::{
    metrics::{Counter, Histogram, Meter, ObservableGauge},
    KeyValue,
};
use std::sync::Arc;
use once_cell::sync::Lazy;

/// 应用指标集合
pub struct AppMetrics {
    // Counter: 请求总数
    pub http_requests_total: Counter<u64>,
    
    // Histogram: 请求延迟
    pub http_request_duration: Histogram<f64>,
    
    // Counter: 错误总数
    pub errors_total: Counter<u64>,
    
    // ObservableGauge: 活跃连接数
    pub active_connections: ObservableGauge<u64>,
}

impl AppMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            http_requests_total: meter
                .u64_counter("http.server.requests")
                .with_description("Total number of HTTP requests")
                .build(),
            
            http_request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP request duration in milliseconds")
                .with_unit("ms")
                .build(),
            
            errors_total: meter
                .u64_counter("app.errors.total")
                .with_description("Total number of errors")
                .build(),
            
            active_connections: meter
                .u64_observable_gauge("http.server.active_connections")
                .with_description("Number of active HTTP connections")
                .build(),
        }
    }
    
    /// 记录HTTP请求
    pub fn record_request(&self, method: &str, status: u16, duration_ms: f64) {
        let labels = &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status as i64),
        ];
        
        self.http_requests_total.add(1, labels);
        self.http_request_duration.record(duration_ms, labels);
    }
    
    /// 记录错误
    pub fn record_error(&self, error_type: &str) {
        self.errors_total.add(1, &[
            KeyValue::new("error.type", error_type.to_string()),
        ]);
    }
}

// 全局指标实例
pub static METRICS: Lazy<Arc<AppMetrics>> = Lazy::new(|| {
    let meter = super::meter();
    Arc::new(AppMetrics::new(&meter))
});
```

---

## Logs集成

### 1. Logs初始化模块

创建 `src/logs/mod.rs`:

```rust
use opentelemetry_sdk::logs::{LoggerProvider, Config as LogsConfig};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry::{KeyValue, logs::LoggerProvider as _};
use std::time::Duration;
use tracing_subscriber::{layer::SubscriberExt, Registry};
use tracing_opentelemetry::OpenTelemetryLayer;

/// 初始化日志系统
pub fn init_logs(
    service_name: &str,
    endpoint: &str,
) -> Result<LoggerProvider, Box<dyn std::error::Error>> {
    // 1. 创建OTLP log exporter
    let exporter = opentelemetry_otlp::LogExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(30))
        .build()?;

    // 2. 配置资源属性
    let resource = opentelemetry_sdk::Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);

    // 3. 创建LoggerProvider
    let provider = LoggerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_config(LogsConfig::default().with_resource(resource))
        .build();

    Ok(provider)
}

/// 配置tracing-subscriber集成OpenTelemetry
pub fn setup_tracing_subscriber(
    tracer_provider: &opentelemetry_sdk::trace::TracerProvider,
) -> Result<(), Box<dyn std::error::Error>> {
    // 创建OpenTelemetry layer
    let telemetry_layer = OpenTelemetryLayer::new(
        tracer_provider.tracer("tracing")
    );

    // 组合订阅者
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer().with_target(false))
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(telemetry_layer);

    tracing::subscriber::set_global_default(subscriber)?;

    Ok(())
}
```

---

## Profiling集成

### 1. Profiling模块

创建 `src/profiling/mod.rs`:

```rust
use pprof::ProfilerGuard;
use std::fs::File;
use std::io::Write;

/// CPU Profiling
pub struct CpuProfiler {
    guard: Option<ProfilerGuard<'static>>,
}

impl CpuProfiler {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let guard = pprof::ProfilerGuardBuilder::default()
            .frequency(1000)
            .build()?;
        
        Ok(Self {
            guard: Some(guard),
        })
    }
    
    pub fn stop_and_report(&mut self, output_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(guard) = self.guard.take() {
            let report = guard.report().build()?;
            
            // 生成flamegraph
            let file = File::create(output_path)?;
            report.flamegraph(file)?;
            
            println!("Flamegraph saved to: {}", output_path);
        }
        
        Ok(())
    }
}

/// 内存profiling示例
pub fn heap_profiling_example() {
    #[cfg(feature = "dhat")]
    {
        let _profiler = dhat::Profiler::new_heap();
        
        // 应用代码...
        
        // dhat会在程序退出时生成报告
    }
}
```

---

## Dashboard搭建

### 1. Grafana数据源配置

创建 `grafana/datasources/datasources.yml`:

```yaml
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
  
  - name: Jaeger
    type: jaeger
    access: proxy
    url: http://jaeger:16686
  
  - name: Elasticsearch
    type: elasticsearch
    access: proxy
    url: http://elasticsearch:9200
    database: "otel-logs*"
```

### 2. Grafana Dashboard配置

创建 `grafana/dashboards/otlp-dashboard.json`:

```json
{
  "dashboard": {
    "title": "OTLP Observability Dashboard",
    "tags": ["otlp", "observability"],
    "timezone": "browser",
    "panels": [
      {
        "title": "HTTP Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_server_requests_total[5m])",
            "legendFormat": "{{http_method}} - {{http_status_code}}"
          }
        ],
        "gridPos": {
          "x": 0,
          "y": 0,
          "w": 12,
          "h": 8
        }
      },
      {
        "title": "HTTP Request Duration (P50, P90, P99)",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.50, rate(http_server_duration_bucket[5m]))",
            "legendFormat": "P50"
          },
          {
            "expr": "histogram_quantile(0.90, rate(http_server_duration_bucket[5m]))",
            "legendFormat": "P90"
          },
          {
            "expr": "histogram_quantile(0.99, rate(http_server_duration_bucket[5m]))",
            "legendFormat": "P99"
          }
        ],
        "gridPos": {
          "x": 12,
          "y": 0,
          "w": 12,
          "h": 8
        }
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(app_errors_total[5m])",
            "legendFormat": "{{error_type}}"
          }
        ],
        "gridPos": {
          "x": 0,
          "y": 8,
          "w": 12,
          "h": 8
        }
      },
      {
        "title": "Active Connections",
        "type": "graph",
        "targets": [
          {
            "expr": "http_server_active_connections",
            "legendFormat": "Active Connections"
          }
        ],
        "gridPos": {
          "x": 12,
          "y": 8,
          "w": 12,
          "h": 8
        }
      }
    ]
  }
}
```

---

## 告警配置

### 1. Prometheus告警规则

创建 `prometheus-alerts.yml`:

```yaml
groups:
  - name: application_alerts
    interval: 30s
    rules:
      # 高错误率告警
      - alert: HighErrorRate
        expr: |
          rate(app_errors_total[5m]) > 10
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors/sec"
      
      # 高延迟告警
      - alert: HighLatency
        expr: |
          histogram_quantile(0.99,
            rate(http_server_duration_bucket[5m])
          ) > 1000
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High P99 latency detected"
          description: "P99 latency is {{ $value }}ms"
      
      # 请求率突增
      - alert: TrafficSpike
        expr: |
          rate(http_server_requests_total[1m]) >
          2 * rate(http_server_requests_total[1m] offset 5m)
        for: 2m
        labels:
          severity: info
        annotations:
          summary: "Traffic spike detected"
          description: "Request rate doubled in the last 5 minutes"
```

### 2. Alertmanager配置

创建 `alertmanager.yml`:

```yaml
global:
  resolve_timeout: 5m

route:
  group_by: ['alertname', 'severity']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 12h
  receiver: 'default'
  
  routes:
    - match:
        severity: critical
      receiver: 'pager'
    - match:
        severity: warning
      receiver: 'slack'

receivers:
  - name: 'default'
    webhook_configs:
      - url: 'http://localhost:5001/alert'
  
  - name: 'slack'
    slack_configs:
      - api_url: 'https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK'
        channel: '#alerts'
        title: '{{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'
  
  - name: 'pager'
    pagerduty_configs:
      - service_key: 'YOUR_PAGERDUTY_KEY'
```

---

## 完整项目示例

### 1. 主应用程序

创建 `src/main.rs`:

```rust
use axum::{
    routing::{get, post},
    Router, Json,
    extract::State,
    middleware,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::net::TcpListener;
use tower_http::trace::TraceLayer;
use std::time::Instant;

mod traces;
mod metrics;
mod logs;
mod profiling;

#[derive(Clone)]
struct AppState {
    // 应用状态
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化可观测性组件
    let service_name = "otlp-demo-service";
    let otlp_endpoint = "http://localhost:4317";
    
    // Traces
    let tracer_provider = traces::init_tracer(service_name, otlp_endpoint)?;
    
    // Metrics
    let meter_provider = metrics::init_metrics(service_name, otlp_endpoint)?;
    
    // Logs
    let logger_provider = logs::init_logs(service_name, otlp_endpoint)?;
    logs::setup_tracing_subscriber(&tracer_provider)?;
    
    tracing::info!("Observability initialized successfully");
    
    // 2. 创建应用状态
    let app_state = Arc::new(AppState {});
    
    // 3. 构建路由
    let app = Router::new()
        .route("/", get(root_handler))
        .route("/api/users", get(list_users_handler))
        .route("/api/users", post(create_user_handler))
        .route("/api/process", post(process_handler))
        .route("/health", get(health_handler))
        .route("/metrics", get(metrics_handler))
        .layer(middleware::from_fn(traces::middleware::trace_middleware))
        .layer(middleware::from_fn(metrics_middleware))
        .with_state(app_state);
    
    // 4. 启动服务器
    let listener = TcpListener::bind("0.0.0.0:8080").await?;
    tracing::info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    // 5. 清理
    tracer_provider.shutdown()?;
    meter_provider.shutdown()?;
    logger_provider.shutdown()?;
    
    Ok(())
}

/// Root handler
async fn root_handler() -> &'static str {
    "OTLP Complete Observability Demo"
}

#[derive(Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    email: String,
}

/// 列出用户
#[tracing::instrument]
async fn list_users_handler() -> Json<Vec<User>> {
    tracing::info!("Listing users");
    
    // 模拟数据库查询
    let users = traces::instrumentation::traced_db_query("SELECT * FROM users")
        .await
        .unwrap_or_default();
    
    Json(vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
        },
    ])
}

/// 创建用户
#[tracing::instrument(skip(user))]
async fn create_user_handler(Json(user): Json<User>) -> Json<User> {
    tracing::info!("Creating user: {}", user.name);
    
    // 模拟数据库插入
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Json(user)
}

#[derive(Deserialize)]
struct ProcessRequest {
    data: String,
}

#[derive(Serialize)]
struct ProcessResponse {
    result: String,
    processing_time_ms: u64,
}

/// 处理数据
#[tracing::instrument(skip(req))]
async fn process_handler(Json(req): Json<ProcessRequest>) -> Json<ProcessResponse> {
    let start = Instant::now();
    
    tracing::info!("Processing data: {} bytes", req.data.len());
    
    // 模拟复杂处理
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    
    // 调用外部API
    let api_result = traces::instrumentation::traced_api_call("https://api.example.com/process")
        .await
        .unwrap_or_default();
    
    let processing_time = start.elapsed().as_millis() as u64;
    
    Json(ProcessResponse {
        result: format!("Processed: {} -> {}", req.data, api_result),
        processing_time_ms: processing_time,
    })
}

/// 健康检查
async fn health_handler() -> &'static str {
    "OK"
}

/// Metrics endpoint
async fn metrics_handler() -> &'static str {
    "Metrics are exported to OTLP Collector"
}

/// Metrics中间件
async fn metrics_middleware(
    request: axum::extract::Request,
    next: axum::middleware::Next,
) -> axum::response::Response {
    let start = Instant::now();
    let method = request.method().to_string();
    
    let response = next.run(request).await;
    
    let duration_ms = start.elapsed().as_secs_f64() * 1000.0;
    let status = response.status().as_u16();
    
    // 记录metrics
    metrics::instrumentation::METRICS.record_request(&method, status, duration_ms);
    
    response
}
```

### 2. 运行示例

```bash
# 1. 启动基础设施
docker-compose up -d

# 2. 运行应用
cargo run

# 3. 发送测试请求
curl http://localhost:8080/
curl http://localhost:8080/api/users
curl -X POST http://localhost:8080/api/users \
  -H "Content-Type: application/json" \
  -d '{"id": 3, "name": "Charlie", "email": "charlie@example.com"}'

# 4. 发送高负载测试
for i in {1..100}; do
  curl http://localhost:8080/api/users &
done

# 5. 查看可观测性数据
# Jaeger: http://localhost:16686
# Prometheus: http://localhost:9090
# Grafana: http://localhost:3000
```

### 3. 验证Traces

访问Jaeger UI (<http://localhost:16686>):

1. 选择服务: `otlp-demo-service`
2. 点击 "Find Traces"
3. 查看trace详情，验证：
   - HTTP请求span
   - 数据库查询span
   - 外部API调用span
   - Span attributes和events

### 4. 验证Metrics

访问Prometheus (<http://localhost:9090>):

```promql
# 请求速率
rate(http_server_requests_total[5m])

# P99延迟
histogram_quantile(0.99, rate(http_server_duration_bucket[5m]))

# 错误率
rate(app_errors_total[5m])

# 活跃连接数
http_server_active_connections
```

### 5. 验证Logs

访问Kibana (<http://localhost:5601>):

1. 创建index pattern: `otel-logs*`
2. 查看日志流
3. 过滤日志: `service.name: "otlp-demo-service"`

---

## 总结与最佳实践

### 关键要点

```rust
/// 可观测性最佳实践
pub const OBSERVABILITY_BEST_PRACTICES: &[&str] = &[
    "1. 统一使用OTLP协议，实现Traces/Metrics/Logs一致性",
    "2. 正确配置Resource属性，便于服务识别",
    "3. 使用合理的采样策略（生产环境1-10%）",
    "4. 为关键操作添加追踪（数据库、外部API、关键业务逻辑）",
    "5. 避免高基数标签",
    "6. 配置批处理优化性能",
    "7. 实施健康检查和监控",
    "8. 设置合理的告警规则",
    "9. 定期审查和优化可观测性配置",
    "10. 文档化可观测性标准和实践",
];
```

### 生产环境清单

```rust
/// 生产环境部署检查清单
#[derive(Debug)]
pub struct ProductionChecklist {
    pub items: Vec<(&'static str, bool)>,
}

impl ProductionChecklist {
    pub fn new() -> Self {
        Self {
            items: vec![
                ("✅ 配置生产级采样率（1-10%）", false),
                ("✅ 启用批处理和优化配置", false),
                ("✅ 配置Resource属性（service.name等）", false),
                ("✅ 实施错误处理和降级策略", false),
                ("✅ 配置监控Dashboard", false),
                ("✅ 设置告警规则", false),
                ("✅ 配置日志聚合", false),
                ("✅ 实施安全最佳实践（TLS, 认证）", false),
                ("✅ 性能测试验证", false),
                ("✅ 文档化运维手册", false),
            ],
        }
    }
}
```

### 下一步

1. **优化性能**: 参考性能基准测试文档
2. **安全加固**: 启用TLS、认证和授权
3. **高可用部署**: Collector集群、数据持久化
4. **成本优化**: 采样策略、数据保留策略
5. **持续改进**: 监控可观测性系统本身

---

## 参考资源

### 官方文档

- [OpenTelemetry Documentation](https://opentelemetry.io/docs/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)

### 工具和平台

- [Jaeger](https://www.jaegertracing.io/)
- [Prometheus](https://prometheus.io/)
- [Grafana](https://grafana.com/)
- [Elasticsearch](https://www.elastic.co/)

### 社区资源

- [OpenTelemetry Community](https://opentelemetry.io/community/)
- [CNCF Slack](https://slack.cncf.io/) - #opentelemetry

---

**文档版本**: v1.0  
**最后更新**: 2025年10月8日  
**状态**: ✅ 完成  
**预计行数**: 3,800+ 行

---

**#OTLP #Rust #Observability #Tutorial #Traces #Metrics #Logs #Grafana #Prometheus #Jaeger**-
