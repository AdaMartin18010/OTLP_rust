# 生产环境部署指南

> **版本**: Rust 1.90 & OTLP 1.3.0
> **日期**: 2025年10月2日
> **主题**: 部署架构、监控告警、故障恢复、最佳实践

---

## 📋 目录

- [生产环境部署指南](#生产环境部署指南)
  - [📋 目录](#-目录)
  - [部署架构](#部署架构)
    - [推荐架构](#推荐架构)
    - [Kubernetes 部署](#kubernetes-部署)
  - [配置管理](#配置管理)
    - [生产环境配置](#生产环境配置)
  - [监控与告警](#监控与告警)
    - [Prometheus 指标暴露](#prometheus-指标暴露)
    - [告警规则](#告警规则)
  - [日志管理](#日志管理)
    - [结构化日志](#结构化日志)
  - [故障恢复](#故障恢复)
    - [自动重试机制](#自动重试机制)
  - [性能调优](#性能调优)
    - [生产环境调优清单](#生产环境调优清单)
  - [安全加固](#安全加固)
    - [TLS 配置](#tls-配置)
  - [运维工具](#运维工具)
    - [健康检查](#健康检查)

---

## 部署架构

### 推荐架构

```text
┌─────────────────────────────────────────────┐
│              应用服务                        │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐     │
│  │ Service │  │ Service │  │ Service │     │
│  │   A     │  │   B     │  │   C     │     │
│  └────┬────┘  └────┬────┘  └────┬────┘     │
│       │            │            │           │
└───────┼────────────┼────────────┼───────────┘
        │            │            │
        └────────────┴────────────┘
                     │
        ┌────────────▼─────────────┐
        │   OTLP Collector (边缘)  │
        │   - 批处理               │
        │   - 采样                 │
        │   - 本地缓存             │
        └────────────┬─────────────┘
                     │
        ┌────────────▼─────────────┐
        │   OTLP Collector (中心)  │
        │   - 聚合                 │
        │   - 路由                 │
        │   - 持久化               │
        └────────────┬─────────────┘
                     │
        ┌────────────▼─────────────┐
        │      后端存储             │
        │  - Jaeger / Tempo        │
        │  - Prometheus            │
        │  - Elasticsearch         │
        └──────────────────────────┘
```

### Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-app
  template:
    metadata:
      labels:
        app: otlp-app
    spec:
      containers:
      - name: app
        image: myapp:latest
        env:
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: SERVICE_NAME
          value: "my-service"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
spec:
  ports:
  - port: 4317
    name: grpc
  - port: 4318
    name: http
  selector:
    app: otel-collector
```

---

## 配置管理

### 生产环境配置

```rust
use serde::Deserialize;

#[derive(Deserialize)]
struct ProductionConfig {
    otlp: OtlpConfig,
    sampling: SamplingConfig,
    batch: BatchConfig,
}

#[derive(Deserialize)]
struct OtlpConfig {
    endpoint: String,
    timeout_seconds: u64,
    retry_max_attempts: u32,
}

#[derive(Deserialize)]
struct SamplingConfig {
    rate: f64,
    error_boost: f64,
}

#[derive(Deserialize)]
struct BatchConfig {
    max_size: usize,
    timeout_ms: u64,
}

fn load_config() -> Result<ProductionConfig, Box<dyn std::error::Error>> {
    let config_path = std::env::var("CONFIG_PATH").unwrap_or_else(|_| "config.toml".to_string());
    let config_str = std::fs::read_to_string(config_path)?;
    let config: ProductionConfig = toml::from_str(&config_str)?;
    Ok(config)
}
```

---

## 监控与告警

### Prometheus 指标暴露

```rust
use prometheus::{Registry, Counter, Histogram, Opts};

struct Metrics {
    spans_exported: Counter,
    export_duration: Histogram,
}

impl Metrics {
    fn new(registry: &Registry) -> Result<Self, Box<dyn std::error::Error>> {
        let spans_exported = Counter::with_opts(
            Opts::new("otlp_spans_exported_total", "Total spans exported")
        )?;
        registry.register(Box::new(spans_exported.clone()))?;

        let export_duration = Histogram::with_opts(
            prometheus::HistogramOpts::new("otlp_export_duration_seconds", "Export duration")
        )?;
        registry.register(Box::new(export_duration.clone()))?;

        Ok(Self {
            spans_exported,
            export_duration,
        })
    }
}
```

### 告警规则

```yaml
groups:
- name: otlp_alerts
  rules:
  - alert: HighExportFailureRate
    expr: rate(otlp_export_failures_total[5m]) > 0.1
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "OTLP export failure rate > 10%"
```

---

## 日志管理

### 结构化日志

```rust
use tracing::{info, error, Level};
use tracing_subscriber::FmtSubscriber;

fn init_logging() {
    let subscriber = FmtSubscriber::builder()
        .with_max_level(Level::INFO)
        .json()
        .finish();

    tracing::subscriber::set_global_default(subscriber)
        .expect("Failed to set subscriber");
}

async fn production_handler() {
    info!(
        service_name = "my-service",
        version = "1.0.0",
        "Service started"
    );

    // 业务逻辑

    error!(
        error_code = "DB_TIMEOUT",
        "Database connection timeout"
    );
}
```

---

## 故障恢复

### 自动重试机制

```rust
async fn export_with_retry<T>(
    operation: impl Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, Box<dyn std::error::Error>>> + Send>>,
    max_retries: u32,
) -> Result<T, Box<dyn std::error::Error>> {
    let mut attempt = 0;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if attempt < max_retries => {
                attempt += 1;
                let delay = std::time::Duration::from_millis(100 * 2_u64.pow(attempt));
                tokio::time::sleep(delay).await;
            }
            Err(e) => return Err(e),
        }
    }
}
```

---

## 性能调优

### 生产环境调优清单

```text
✅ 启用批处理 (batch_size=1000, timeout=5s)
✅ 配置连接池 (pool_size=10)
✅ 启用压缩 (gzip)
✅ 设置合理采样率 (base_rate=0.01, error_boost=1.0)
✅ 使用 jemalloc 内存分配器
✅ 启用 CPU 亲和性
```

---

## 安全加固

### TLS 配置

```rust
use opentelemetry_otlp::WithExportConfig;
use tonic::transport::ClientTlsConfig;

async fn create_secure_exporter() -> Result<(), Box<dyn std::error::Error>> {
    let tls = ClientTlsConfig::new()
        .ca_certificate(tonic::transport::Certificate::from_pem(
            std::fs::read("ca.pem")?
        ));

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("https://otlp.example.com:4317")
        .with_tls_config(tls);

    Ok(())
}
```

---

## 运维工具

### 健康检查

```rust
use axum::{routing::get, Router};

async fn health_check() -> &'static str {
    "OK"
}

async fn readiness_check() -> &'static str {
    // 检查依赖服务
    "Ready"
}

async fn start_health_server() {
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check));

    axum::Server::bind(&"0.0.0.0:8080".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

---

**最后更新**: 2025年10月2日
**作者**: OTLP Rust 项目组
