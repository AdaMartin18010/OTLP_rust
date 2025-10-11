# Datadog - Rust + OTLP 完整集成指南

## 📋 目录

- [Datadog - Rust + OTLP 完整集成指南](#datadog---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Datadog?](#什么是-datadog)
    - [为什么选择 Datadog + Rust?](#为什么选择-datadog--rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Datadog 架构](#1-datadog-架构)
    - [2. 统一标签](#2-统一标签)
  - [环境准备](#环境准备)
    - [1. Datadog 账户设置](#1-datadog-账户设置)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [APM 追踪集成](#apm-追踪集成)
    - [1. OTLP 导出器配置](#1-otlp-导出器配置)
    - [2. 分布式追踪](#2-分布式追踪)
    - [3. 服务地图](#3-服务地图)
  - [指标监控](#指标监控)
    - [1. 自定义指标](#1-自定义指标)
    - [2. DogStatsD 集成](#2-dogstatsd-集成)
    - [3. 预聚合指标](#3-预聚合指标)
  - [日志管理](#日志管理)
    - [1. 结构化日志](#1-结构化日志)
    - [2. 日志与追踪关联](#2-日志与追踪关联)
    - [3. 日志管道](#3-日志管道)
  - [RUM (Real User Monitoring)](#rum-real-user-monitoring)
    - [1. 前端集成](#1-前端集成)
    - [2. 后端关联](#2-后端关联)
  - [Profiling 性能分析](#profiling-性能分析)
    - [1. 持续性能分析](#1-持续性能分析)
    - [2. 火焰图分析](#2-火焰图分析)
  - [告警与监控](#告警与监控)
    - [1. Monitor 配置](#1-monitor-配置)
    - [2. SLO 跟踪](#2-slo-跟踪)
    - [3. 异常检测](#3-异常检测)
  - [仪表板](#仪表板)
    - [1. 自定义仪表板](#1-自定义仪表板)
    - [2. 预制模板](#2-预制模板)
  - [成本优化](#成本优化)
    - [1. 采样策略](#1-采样策略)
    - [2. 索引优化](#2-索引优化)
  - [完整示例](#完整示例)
    - [1. 微服务全栈监控](#1-微服务全栈监控)
    - [2. Kubernetes 集成](#2-kubernetes-集成)
  - [最佳实践](#最佳实践)
    - [1. 标签策略](#1-标签策略)
    - [2. 安全配置](#2-安全配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Datadog vs 其他 APM](#datadog-vs-其他-apm)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Datadog?

**Datadog** 是全球领先的云监控和安全平台:

```text
┌─────────────────────────────────────┐
│        Datadog Platform             │
│  ┌──────────────────────────────┐   │
│  │  APM (追踪)                  │   │
│  │  Metrics (指标)              │   │
│  │  Logs (日志)                 │   │
│  │  RUM (真实用户监控)           │   │
│  │  Profiling (性能分析)         │   │
│  │  Synthetics (合成监控)        │   │
│  │  Security (安全)              │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
         ↑ OTLP + Datadog Agent
┌─────────────────────────────────────┐
│      Rust Application               │
└─────────────────────────────────────┘
```

**核心功能**:

- **APM**: 分布式追踪和性能监控
- **Metrics**: 实时指标收集和可视化
- **Logs**: 集中日志管理和分析
- **RUM**: 真实用户体验监控
- **Profiling**: 持续性能分析

### 为什么选择 Datadog + Rust?

| 优势 | 说明 |
|------|------|
| **全栈可观测性** | APM + Metrics + Logs + RUM 统一平台 |
| **开箱即用** | 丰富的集成和预制仪表板 |
| **AI/ML 能力** | 异常检测和智能告警 |
| **企业级** | 安全、合规、SLA 保证 |
| **OTLP 兼容** | OpenTelemetry 标准支持 |

### OTLP 集成价值

```text
Rust App → OpenTelemetry SDK → OTLP → Datadog Agent → Datadog Cloud
    ↓              ↓               ↓         ↓             ↓
  业务逻辑      标准化追踪      统一协议  本地聚合      全栈分析
```

**优势**:

- **供应商中立**: OpenTelemetry 标准
- **灵活切换**: 可切换到其他后端
- **生态丰富**: 自动注入和仪表盘
- **统一标签**: 跨信号关联

---

## 核心概念

### 1. Datadog 架构

```text
┌─────────────────────────────────────────┐
│         Datadog Cloud (SaaS)            │
│  ┌─────────────────────────────────┐    │
│  │  APM  │ Metrics │ Logs │ RUM    │    │
│  └─────────────────────────────────┘    │
└──────────────────┬──────────────────────┘
                   │ HTTPS
┌──────────────────▼──────────────────────┐
│         Datadog Agent                   │
│  • 本地聚合                              │
│  • 标签丰富                              │
│  • 采样决策                              │
└──────────────────┬──────────────────────┘
                   │ OTLP + DogStatsD
┌──────────────────▼──────────────────────┐
│      Rust Application                   │
│  • OpenTelemetry SDK                    │
│  • DogStatsD Client                     │
└─────────────────────────────────────────┘
```

### 2. 统一标签

**Datadog 标签体系**:

```text
env:production
service:rust-app
version:1.0.0
region:us-east-1
team:backend
```

**标签传播**:

- APM Trace → 自动附加标签
- Metrics → 相同标签
- Logs → 标签关联
- RUM → 跨前后端

---

## 环境准备

### 1. Datadog 账户设置

```bash
# 1. 注册 Datadog 账户
# https://www.datadoghq.com/

# 2. 获取 API Key
# Organization Settings → API Keys → New Key

# 3. 安装 Datadog Agent
# Ubuntu/Debian
DD_API_KEY=your_api_key DD_SITE="datadoghq.com" bash -c "$(curl -L https://s3.amazonaws.com/dd-agent/scripts/install_script_agent7.sh)"

# Docker
docker run -d --name datadog-agent \
  -e DD_API_KEY=your_api_key \
  -e DD_SITE=datadoghq.com \
  -e DD_APM_ENABLED=true \
  -e DD_APM_NON_LOCAL_TRAFFIC=true \
  -e DD_OTLP_CONFIG_RECEIVER_PROTOCOLS_GRPC_ENDPOINT=0.0.0.0:4317 \
  -e DD_OTLP_CONFIG_RECEIVER_PROTOCOLS_HTTP_ENDPOINT=0.0.0.0:4318 \
  -p 8126:8126 \
  -p 4317:4317 \
  -p 4318:4318 \
  -p 8125:8125/udp \
  -v /var/run/docker.sock:/var/run/docker.sock:ro \
  -v /proc/:/host/proc/:ro \
  -v /sys/fs/cgroup/:/host/sys/fs/cgroup:ro \
  gcr.io/datadoghq/agent:7

# 4. 验证 Agent
datadog-agent status
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "datadog-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = "0.30"

# Datadog Exporter (可选,推荐使用 OTLP)
opentelemetry-datadog = "0.30"

# Tracing
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }

# DogStatsD (指标)
dogstatsd = "0.9"

# HTTP
axum = "0.7"
tower-http = { version = "0.5", features = ["trace"] }
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing-log = "0.2"
tracing-appender = "0.2"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

[profile.release]
opt-level = 3
lto = true
```

---

## APM 追踪集成

### 1. OTLP 导出器配置

```rust
// src/datadog.rs
use opentelemetry::{
    global,
    trace::TracerProvider,
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use anyhow::Result;

pub fn init_datadog_tracing(
    service_name: &str,
    service_version: &str,
    environment: &str,
) -> Result<()> {
    // 配置 OTLP 导出器指向 Datadog Agent
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),  // Datadog Agent OTLP endpoint
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::ParentBased(Box::new(
                    Sampler::TraceIdRatioBased(0.1)  // 10% 采样
                )))
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    // Datadog 统一标签
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", service_version.to_string()),
                    KeyValue::new("deployment.environment", environment.to_string()),
                    // 额外标签
                    KeyValue::new("team", "backend"),
                    KeyValue::new("region", "us-east-1"),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider);
    
    // 初始化 Tracing Subscriber
    let telemetry = tracing_opentelemetry::layer()
        .with_tracer(global::tracer(service_name));
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}

pub fn shutdown_datadog_tracing() {
    global::shutdown_tracer_provider();
}
```

### 2. 分布式追踪

```rust
// src/tracing.rs
use tracing::{info, instrument, Span};
use opentelemetry::trace::{SpanKind, Status};

#[instrument(
    name = "http.request",
    fields(
        http.method = %method,
        http.url = %url,
        http.status_code,
        http.response_time_ms,
        // Datadog APM 标准标签
        span.kind = "server",
        resource.name = %format!("{} {}", method, path),
    )
)]
pub async fn handle_http_request(
    method: &str,
    url: &str,
    path: &str,
) -> Result<Response> {
    let span = Span::current();
    
    let start = std::time::Instant::now();
    
    // 处理请求
    let result = process_request().await;
    
    let duration = start.elapsed();
    
    // 记录指标
    span.record("http.response_time_ms", duration.as_millis() as i64);
    
    match &result {
        Ok(resp) => {
            span.record("http.status_code", resp.status_code);
            info!("Request successful");
        }
        Err(e) => {
            span.record("http.status_code", 500);
            span.record("error", true);
            span.record("error.type", &format!("{:?}", e));
            span.record("error.message", &e.to_string());
        }
    }
    
    result
}

#[instrument(
    name = "database.query",
    fields(
        db.system = "postgresql",
        db.operation = "SELECT",
        db.statement,
        span.kind = "client",
    )
)]
pub async fn query_database(sql: &str) -> Result<Vec<Row>> {
    let span = Span::current();
    span.record("db.statement", sql);
    
    // 执行查询...
    
    Ok(vec![])
}
```

### 3. 服务地图

```rust
// Datadog 会自动从追踪数据生成服务地图
// 确保设置正确的 span.kind 和 peer.service

#[instrument(
    fields(
        span.kind = "client",
        peer.service = "payment-service",
    )
)]
async fn call_payment_service(amount: f64) -> Result<PaymentResponse> {
    // Datadog 会在服务地图上显示依赖关系
    Ok(PaymentResponse { success: true })
}
```

---

## 指标监控

### 1. 自定义指标

```rust
// src/metrics.rs
use opentelemetry::metrics::{Counter, Histogram, Meter};
use opentelemetry::KeyValue;

pub struct AppMetrics {
    request_count: Counter<u64>,
    request_duration: Histogram<f64>,
    active_connections: Counter<i64>,
}

impl AppMetrics {
    pub fn new() -> Self {
        let meter = global::meter("rust-app");
        
        Self {
            request_count: meter
                .u64_counter("http.server.requests")
                .with_description("Total HTTP requests")
                .init(),
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP request duration")
                .with_unit("ms")
                .init(),
            active_connections: meter
                .i64_up_down_counter("http.server.active_connections")
                .with_description("Active HTTP connections")
                .init(),
        }
    }
    
    pub fn record_request(&self, duration_ms: f64, status_code: u16, method: &str, path: &str) {
        let attributes = vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", path.to_string()),
            KeyValue::new("http.status_code", status_code as i64),
        ];
        
        self.request_count.add(1, &attributes);
        self.request_duration.record(duration_ms, &attributes);
    }
    
    pub fn increment_connections(&self) {
        self.active_connections.add(1, &[]);
    }
    
    pub fn decrement_connections(&self) {
        self.active_connections.add(-1, &[]);
    }
}
```

### 2. DogStatsD 集成

```rust
// src/dogstatsd.rs
use dogstatsd::{Client, Options};
use std::sync::Arc;

pub struct DogStatsDMetrics {
    client: Arc<Client>,
}

impl DogStatsDMetrics {
    pub fn new() -> Result<Self> {
        let options = Options::new("localhost", 8125, "", vec![
            "env:production",
            "service:rust-app",
            "version:1.0.0",
        ]);
        
        let client = Client::new(options)?;
        
        Ok(Self {
            client: Arc::new(client),
        })
    }
    
    pub fn increment(&self, metric: &str, tags: &[&str]) {
        let _ = self.client.incr(metric, tags);
    }
    
    pub fn gauge(&self, metric: &str, value: f64, tags: &[&str]) {
        let _ = self.client.gauge(metric, value.to_string().as_str(), tags);
    }
    
    pub fn histogram(&self, metric: &str, value: f64, tags: &[&str]) {
        let _ = self.client.histogram(metric, value.to_string().as_str(), tags);
    }
    
    pub fn timing(&self, metric: &str, duration_ms: u64, tags: &[&str]) {
        let _ = self.client.timing(metric, duration_ms, tags);
    }
}

// 使用示例
pub async fn track_operation() {
    let metrics = DogStatsDMetrics::new().unwrap();
    
    let start = std::time::Instant::now();
    
    // 执行操作
    perform_operation().await;
    
    let duration = start.elapsed().as_millis() as u64;
    
    metrics.timing(
        "custom.operation.duration",
        duration,
        &["operation:heavy_compute"],
    );
    
    metrics.increment(
        "custom.operation.count",
        &["status:success"],
    );
}
```

### 3. 预聚合指标

```rust
// Datadog Metrics 预聚合
use std::collections::HashMap;
use std::sync::RwLock;

pub struct MetricsAggregator {
    counters: RwLock<HashMap<String, u64>>,
    gauges: RwLock<HashMap<String, f64>>,
}

impl MetricsAggregator {
    pub fn new() -> Self {
        Self {
            counters: RwLock::new(HashMap::new()),
            gauges: RwLock::new(HashMap::new()),
        }
    }
    
    pub fn increment(&self, metric: &str) {
        let mut counters = self.counters.write().unwrap();
        *counters.entry(metric.to_string()).or_insert(0) += 1;
    }
    
    pub fn set_gauge(&self, metric: &str, value: f64) {
        let mut gauges = self.gauges.write().unwrap();
        gauges.insert(metric.to_string(), value);
    }
    
    pub async fn flush(&self, dogstatsd: &DogStatsDMetrics) {
        // 刷新计数器
        let counters = self.counters.read().unwrap();
        for (metric, count) in counters.iter() {
            dogstatsd.gauge(metric, *count as f64, &[]);
        }
        
        // 刷新仪表
        let gauges = self.gauges.read().unwrap();
        for (metric, value) in gauges.iter() {
            dogstatsd.gauge(metric, *value, &[]);
        }
    }
}
```

---

## 日志管理

### 1. 结构化日志

```rust
// src/logging.rs
use tracing::{error, info, warn};
use serde_json::json;

#[instrument(fields(
    // Datadog 日志标准字段
    ddsource = "rust",
    ddtags = "env:production,service:rust-app",
))]
pub async fn structured_logging_example() {
    // 结构化日志会自动发送到 Datadog
    info!(
        user_id = "user123",
        action = "login",
        status = "success",
        duration_ms = 150,
        "User logged in successfully"
    );
    
    warn!(
        error_code = "RATE_LIMIT",
        user_id = "user456",
        remaining = 5,
        "Rate limit警告"
    );
    
    error!(
        error_type = "DatabaseError",
        error_message = "Connection timeout",
        retry_count = 3,
        "Database connection failed"
    );
}
```

### 2. 日志与追踪关联

```rust
use opentelemetry::trace::{SpanContext, TraceContextExt};
use tracing::Span;

pub fn log_with_trace_context(message: &str) {
    let span = Span::current();
    let ctx = span.context();
    let span_ctx = ctx.span().span_context();
    
    // Datadog 会自动关联日志和追踪
    info!(
        trace_id = %span_ctx.trace_id(),
        span_id = %span_ctx.span_id(),
        "{}",
        message
    );
}
```

### 3. 日志管道

```yaml
# Datadog Agent 日志配置
logs:
  - type: file
    path: /var/log/rust-app/*.log
    service: rust-app
    source: rust
    tags:
      - env:production
    
  - type: docker
    image: rust-app
    service: rust-app
    source: rust
```

---

## RUM (Real User Monitoring)

### 1. 前端集成

```html
<!-- 前端 HTML -->
<script src="https://www.datadoghq-browser-agent.com/datadog-rum-v4.js"></script>
<script>
  window.DD_RUM && window.DD_RUM.init({
    applicationId: 'your_application_id',
    clientToken: 'your_client_token',
    site: 'datadoghq.com',
    service: 'rust-app-frontend',
    env: 'production',
    version: '1.0.0',
    sessionSampleRate: 100,
    sessionReplaySampleRate: 20,
    trackUserInteractions: true,
    trackResources: true,
    trackLongTasks: true,
    defaultPrivacyLevel: 'mask-user-input'
  });
</script>
```

### 2. 后端关联

```rust
// 后端 API 返回 Trace ID 给前端
use axum::{
    http::{HeaderMap, HeaderValue},
    response::IntoResponse,
};

pub async fn api_handler() -> impl IntoResponse {
    let span = Span::current();
    let ctx = span.context();
    let span_ctx = ctx.span().span_context();
    
    let mut headers = HeaderMap::new();
    
    // 返回 Trace ID 给前端 RUM
    headers.insert(
        "x-datadog-trace-id",
        HeaderValue::from_str(&span_ctx.trace_id().to_string()).unwrap(),
    );
    headers.insert(
        "x-datadog-parent-id",
        HeaderValue::from_str(&span_ctx.span_id().to_string()).unwrap(),
    );
    
    (headers, "Response body")
}
```

---

## Profiling 性能分析

### 1. 持续性能分析

```rust
// Datadog Profiling (需要额外配置)
// 使用 pprof-rs 生成性能分析数据

use pprof::ProfilerGuard;

pub struct DatadogProfiler {
    guard: Option<ProfilerGuard<'static>>,
}

impl DatadogProfiler {
    pub fn new() -> Result<Self> {
        let guard = pprof::ProfilerGuardBuilder::default()
            .frequency(100)
            .blocklist(&["libc", "libgcc", "pthread", "vdso"])
            .build()?;
        
        Ok(Self {
            guard: Some(guard),
        })
    }
    
    pub fn generate_report(&mut self) -> Result<()> {
        if let Some(guard) = self.guard.take() {
            let report = guard.report().build()?;
            
            // 导出为 pprof 格式
            let mut file = std::fs::File::create("profile.pb")?;
            report.pprof()?.write_to_vec(&mut file)?;
            
            // 上传到 Datadog (通过 API)
            self.upload_profile("profile.pb")?;
        }
        
        Ok(())
    }
    
    fn upload_profile(&self, file_path: &str) -> Result<()> {
        // 上传到 Datadog Profiling API
        // https://docs.datadoghq.com/profiler/
        Ok(())
    }
}
```

### 2. 火焰图分析

```rust
// 生成火焰图
pub fn generate_flamegraph() -> Result<()> {
    let guard = pprof::ProfilerGuardBuilder::default()
        .frequency(100)
        .build()?;
    
    // 运行性能测试
    heavy_computation();
    
    // 生成火焰图
    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("flamegraph.svg")?;
        report.flamegraph(file)?;
    }
    
    Ok(())
}
```

---

## 告警与监控

### 1. Monitor 配置

```yaml
# Datadog Monitor (通过 API 或 UI 配置)
name: "High Error Rate"
type: "metric alert"
query: "avg(last_5m):sum:http.server.errors{env:production,service:rust-app}.as_count() > 100"
message: |
  {{#is_alert}}
  Error rate is above threshold
  Current value: {{value}}
  {{/is_alert}}
  
  @slack-alerts @pagerduty
thresholds:
  critical: 100
  warning: 50
tags:
  - "team:backend"
  - "service:rust-app"
```

### 2. SLO 跟踪

```rust
// 在代码中记录 SLO 相关指标
pub struct SLOTracker {
    dogstatsd: DogStatsDMetrics,
}

impl SLOTracker {
    pub fn track_slo_request(&self, success: bool, duration_ms: f64) {
        // SLI: 成功率
        self.dogstatsd.increment(
            "slo.requests.total",
            &["slo:availability"],
        );
        
        if success {
            self.dogstatsd.increment(
                "slo.requests.success",
                &["slo:availability"],
            );
        }
        
        // SLI: 延迟
        if duration_ms < 500.0 {
            self.dogstatsd.increment(
                "slo.requests.fast",
                &["slo:latency"],
            );
        }
        
        self.dogstatsd.increment(
            "slo.requests.total",
            &["slo:latency"],
        );
    }
}
```

### 3. 异常检测

```yaml
# Anomaly Monitor (自动检测异常)
name: "Anomalous Request Latency"
type: "anomaly alert"
query: "avg(last_4h):anomalies(avg:http.server.duration{service:rust-app}, 'agile', 2) >= 1"
message: "Request latency is behaving abnormally"
```

---

## 仪表板

### 1. 自定义仪表板

```json
// Datadog Dashboard JSON
{
  "title": "Rust App - Service Overview",
  "widgets": [
    {
      "definition": {
        "type": "timeseries",
        "requests": [
          {
            "q": "avg:http.server.requests{service:rust-app}.as_count()",
            "display_type": "line"
          }
        ],
        "title": "Request Rate"
      }
    },
    {
      "definition": {
        "type": "query_value",
        "requests": [
          {
            "q": "avg:http.server.duration{service:rust-app}",
            "aggregator": "avg"
          }
        ],
        "title": "Avg Latency"
      }
    }
  ]
}
```

### 2. 预制模板

Datadog 提供了许多预制仪表板模板:

- Rust Runtime Dashboard
- HTTP Server Dashboard
- Database Dashboard
- Kubernetes Dashboard

---

## 成本优化

### 1. 采样策略

```rust
// 智能采样
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub fn create_smart_sampler() -> Sampler {
    // 1. 总是采样错误
    // 2. 总是采样慢请求
    // 3. 其他请求 10% 采样
    
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1)
    ))
}
```

### 2. 索引优化

```yaml
# Datadog Log Indexing (只索引重要日志)
indexes:
  - name: main
    filter:
      query: "status:error OR status:warn OR @duration:>1000"
    retention_days: 15
    
  - name: debug
    filter:
      query: "status:debug"
    retention_days: 3
```

---

## 完整示例

### 1. 微服务全栈监控

```rust
// src/main.rs
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 Datadog
    init_datadog_tracing("rust-app", "1.0.0", "production")?;
    
    // 初始化指标
    let metrics = Arc::new(AppMetrics::new());
    let dogstatsd = Arc::new(DogStatsDMetrics::new()?);
    
    // 启动 HTTP 服务器
    let app = Router::new()
        .route("/api/users", get(get_users))
        .layer(Extension(metrics.clone()))
        .layer(Extension(dogstatsd.clone()))
        .layer(tower_http::trace::TraceLayer::new_for_http());
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;
    
    shutdown_datadog_tracing();
    Ok(())
}
```

### 2. Kubernetes 集成

```yaml
# kubernetes/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  labels:
    tags.datadoghq.com/env: "production"
    tags.datadoghq.com/service: "rust-app"
    tags.datadoghq.com/version: "1.0.0"
spec:
  template:
    metadata:
      labels:
        tags.datadoghq.com/env: "production"
        tags.datadoghq.com/service: "rust-app"
        tags.datadoghq.com/version: "1.0.0"
      annotations:
        ad.datadoghq.com/rust-app.logs: '[{"source":"rust","service":"rust-app"}]'
    spec:
      containers:
      - name: rust-app
        image: rust-app:1.0.0
        env:
        - name: DD_AGENT_HOST
          valueFrom:
            fieldRef:
              fieldPath: status.hostIP
        - name: DD_ENV
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/env']
        - name: DD_SERVICE
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/service']
        - name: DD_VERSION
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['tags.datadoghq.com/version']
```

---

## 最佳实践

### 1. 标签策略

```rust
// 统一标签命名
const STANDARD_TAGS: &[&str] = &[
    "env:production",
    "service:rust-app",
    "version:1.0.0",
    "team:backend",
    "region:us-east-1",
];

// 动态标签
pub fn get_request_tags(method: &str, path: &str, status: u16) -> Vec<String> {
    vec![
        format!("http_method:{}", method),
        format!("http_route:{}", path),
        format!("http_status_code:{}", status),
    ]
}
```

### 2. 安全配置

```rust
// 敏感数据脱敏
pub fn sanitize_log_data(data: &str) -> String {
    // 移除敏感信息
    data.replace(r"\b\d{16}\b", "[CREDIT_CARD]")
        .replace(r"\b[\w\.-]+@[\w\.-]+\.\w+\b", "[EMAIL]")
}
```

---

## 总结

### 核心要点

1. **Datadog**: 全栈可观测性平台
2. **OTLP 集成**: OpenTelemetry 标准
3. **统一标签**: 跨信号关联
4. **APM + RUM**: 全链路追踪
5. **AI/ML**: 智能告警和异常检测

### Datadog vs 其他 APM

| 特性 | Datadog | New Relic | Dynatrace | Honeycomb |
|------|---------|-----------|-----------|-----------|
| **全栈监控** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **RUM** | ✅ | ✅ | ✅ | ❌ |
| **Profiling** | ✅ | ✅ | ✅ | ❌ |
| **价格** | 💰💰💰 | 💰💰💰 | 💰💰💰💰 | 💰💰 |

### 下一步

- **Synthetic Monitoring**: 合成监控
- **Security Monitoring**: 安全监控
- **CI/CD Integration**: CI/CD 集成

---

## 参考资料

- [Datadog 官方文档](https://docs.datadoghq.com/)
- [OpenTelemetry + Datadog](https://docs.datadoghq.com/tracing/setup_overview/open_standards/)
- [Datadog API](https://docs.datadoghq.com/api/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.30+  
**Datadog Agent**: 7.x
