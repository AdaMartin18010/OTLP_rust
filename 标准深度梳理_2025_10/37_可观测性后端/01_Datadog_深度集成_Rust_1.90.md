# Datadog 深度集成 - Rust + OTLP 完整指南 (Rust 1.90)

> **文档版本**: v1.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Datadog Agent**: 7.x+
> **对标**: New Relic, Dynatrace, Elastic APM

---

## 📋 概述

**Datadog** 是企业级可观测性平台,提供 APM (应用性能监控)、日志、指标、分布式追踪。

### 核心特性

- ✅ **APM**: 分布式追踪 + 性能分析
- ✅ **Metrics**: DogStatsD 指标收集
- ✅ **Logs**: 结构化日志聚合
- ✅ **Watchdog AI**: 智能异常检测

---

## 完整集成

### 1. OpenTelemetry + Datadog Exporter

```rust
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider},
    KeyValue,
};
use opentelemetry_datadog::DatadogPropagator;
use opentelemetry_sdk::{
    runtime,
    trace::{self as sdktrace, Sampler},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 Datadog OTLP
pub fn init_datadog_telemetry(
    service_name: &str,
    env: &str,
    version: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // 创建 Datadog Exporter
    let datadog_exporter = opentelemetry_datadog::new_pipeline()
        .with_service_name(service_name)
        .with_agent_endpoint("http://datadog-agent:8126")
        .with_version(version)
        .with_env(env)
        .with_tags(vec![
            ("team", "backend"),
            ("region", "us-east-1"),
        ])
        .install_batch(runtime::Tokio)?;

    // 设置 Datadog Propagator (用于分布式追踪)
    global::set_text_map_propagator(DatadogPropagator::new());

    // 创建 tracing 订阅者
    let telemetry = tracing_opentelemetry::layer().with_tracer(datadog_exporter);
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();

    Ok(())
}
```

### 2. Axum Web 服务集成

```rust
use axum::{
    Router,
    routing::get,
    extract::State,
    response::Json,
};
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    pub db: Arc<DatabaseClient>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
}

/// GET /users/:id
#[instrument(skip(state), fields(user.id = id))]
async fn get_user(
    State(state): State<AppState>,
    id: u64,
) -> Result<Json<User>, StatusCode> {
    info!(user_id = id, "Fetching user");
    
    // 数据库查询 (自动追踪)
    let user = state.db.get_user(id).await
        .map_err(|e| {
            tracing::error!(error = %e, "Failed to fetch user");
            StatusCode::INTERNAL_SERVER_ERROR
        })?;
    
    Ok(Json(user))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 Datadog
    init_datadog_telemetry("my-api", "production", "1.0.0")?;

    let state = AppState {
        db: Arc::new(DatabaseClient::new("postgres://...")),
    };

    let app = Router::new()
        .route("/users/:id", get(get_user))
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    info!("Server listening on http://0.0.0.0:8080");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

### 3. DogStatsD 指标集成

```rust
use cadence::{StatsdClient, UdpMetricSink, Counted, Timed, Gauged};
use std::net::UdpSocket;

/// 创建 DogStatsD 客户端
pub fn create_statsd_client() -> Result<StatsdClient, Box<dyn std::error::Error>> {
    let socket = UdpSocket::bind("0.0.0.0:0")?;
    socket.set_nonblocking(true)?;
    
    let sink = UdpMetricSink::from("127.0.0.1:8125", socket)?;
    let client = StatsdClient::from_sink("my_app", sink);
    
    Ok(client)
}

/// 发送自定义指标
pub async fn track_order_created(
    statsd: &StatsdClient,
    order_value: f64,
) -> Result<(), Box<dyn std::error::Error>> {
    // 计数器
    statsd.incr("order.created")?;
    
    // 带标签的计数器
    statsd.incr_with_tags("order.created")
        .with_tag("region", "us-east-1")
        .with_tag("payment_method", "credit_card")
        .send()?;
    
    // Gauge (订单金额)
    statsd.gauge_with_tags("order.value", order_value.to_string())
        .with_tag("currency", "USD")
        .send()?;
    
    Ok(())
}

/// 追踪函数执行时间
#[instrument]
pub async fn process_order(statsd: &StatsdClient) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    
    // 业务逻辑
    tokio::time::sleep(std::time::Duration::from_millis(150)).await;
    
    let elapsed = start.elapsed();
    
    // 记录执行时间
    statsd.time_with_tags("order.process.duration", elapsed.as_millis() as u64)
        .with_tag("status", "success")
        .send()?;
    
    Ok(())
}
```

### 4. 结构化日志集成

```rust
use serde_json::json;
use tracing::{info, warn, error};

/// 结构化日志示例
#[instrument]
pub async fn process_payment(
    order_id: u64,
    amount: f64,
) -> Result<(), PaymentError> {
    // INFO 级别日志
    info!(
        order_id = order_id,
        amount = amount,
        currency = "USD",
        "Processing payment"
    );
    
    // 模拟支付处理
    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    
    // 成功日志
    info!(
        order_id = order_id,
        amount = amount,
        transaction_id = "txn_12345",
        "Payment processed successfully"
    );
    
    Ok(())
}

/// 错误日志示例
#[instrument]
pub async fn handle_payment_error(
    order_id: u64,
    error: &PaymentError,
) {
    // ERROR 级别日志 (会在 Datadog 中触发告警)
    error!(
        order_id = order_id,
        error = %error,
        error_code = error.code(),
        "Payment failed"
    );
    
    // 发送到 Datadog Event API (可选)
    send_datadog_event(json!({
        "title": "Payment Failed",
        "text": format!("Order {} payment failed: {}", order_id, error),
        "alert_type": "error",
        "tags": ["payment", "critical"]
    })).await;
}
```

---

## Docker Compose 部署

```yaml
version: '3.8'

services:
  # Rust 应用
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - DD_AGENT_HOST=datadog-agent
      - DD_TRACE_AGENT_PORT=8126
      - DD_ENV=production
      - DD_SERVICE=my-api
      - DD_VERSION=1.0.0
    depends_on:
      - datadog-agent

  # Datadog Agent
  datadog-agent:
    image: gcr.io/datadoghq/agent:7
    ports:
      - "8125:8125/udp"  # DogStatsD
      - "8126:8126"      # APM
    environment:
      - DD_API_KEY=${DD_API_KEY}
      - DD_APM_ENABLED=true
      - DD_APM_NON_LOCAL_TRAFFIC=true
      - DD_LOGS_ENABLED=true
      - DD_LOGS_CONFIG_CONTAINER_COLLECT_ALL=true
      - DD_DOGSTATSD_NON_LOCAL_TRAFFIC=true
    volumes:
      - /var/run/docker.sock:/var/run/docker.sock:ro
      - /proc/:/host/proc/:ro
      - /sys/fs/cgroup/:/host/sys/fs/cgroup:ro
```

---

## Cargo.toml

```toml
[package]
name = "datadog-rust-integration"
version = "1.0.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Web 框架
axum = "0.8.1"
tokio = { version = "1.41", features = ["full"] }

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-datadog = "0.19"

# Tracing
tracing = "0.1"
tracing-subscriber = "0.3.18"
tracing-opentelemetry = "0.30"

# DogStatsD
cadence = "1.4"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

---

## Datadog Dashboard 配置

### 关键指标

```json
{
  "title": "Rust API - Performance Dashboard",
  "widgets": [
    {
      "definition": {
        "title": "Request Rate",
        "type": "timeseries",
        "requests": [{
          "q": "sum:trace.axum.request{service:my-api}.as_rate()"
        }]
      }
    },
    {
      "definition": {
        "title": "P99 Latency",
        "type": "query_value",
        "requests": [{
          "q": "p99:trace.axum.request.duration{service:my-api}"
        }]
      }
    },
    {
      "definition": {
        "title": "Error Rate",
        "type": "timeseries",
        "requests": [{
          "q": "sum:trace.axum.request{service:my-api,status:error}.as_rate()"
        }]
      }
    }
  ]
}
```

---

## 监控告警

### Datadog Monitor 配置

```json
{
  "name": "High Error Rate - Rust API",
  "type": "metric alert",
  "query": "sum(last_5m):sum:trace.axum.request{service:my-api,status:error}.as_rate() > 10",
  "message": "Error rate is above 10 req/min for service my-api\n@slack-alerts @pagerduty",
  "tags": ["team:backend", "service:my-api"],
  "priority": 2,
  "notify_audit": false,
  "notify_no_data": true,
  "no_data_timeframe": 10
}
```

---

**🐕 Datadog + Rust = 企业级可观测性 🐕**-
