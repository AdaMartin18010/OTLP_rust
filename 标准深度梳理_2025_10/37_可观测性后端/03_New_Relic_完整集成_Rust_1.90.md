# 🌟 New Relic 完整集成 - Rust 1.90 OTLP 指南

> **文档版本**: v1.0  
> **创建日期**: 2025年10月11日  
> **Rust 版本**: 1.90+  
> **New Relic**: OTLP 原生支持  
> **OpenTelemetry**: 0.31.0  
> **难度等级**: ⭐⭐⭐⭐

---

## 📋 目录

- [🌟 New Relic 完整集成 - Rust 1.90 OTLP 指南](#-new-relic-完整集成---rust-190-otlp-指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [什么是 New Relic？](#什么是-new-relic)
    - [为什么选择 New Relic？](#为什么选择-new-relic)
  - [🚀 快速开始](#-快速开始)
    - [Cargo.toml](#cargotoml)
    - [基础配置](#基础配置)
  - [🔍 核心集成](#-核心集成)
    - [1. 追踪集成](#1-追踪集成)
    - [2. 指标集成](#2-指标集成)
    - [3. 日志集成](#3-日志集成)
  - [📦 完整示例 - Web 应用](#-完整示例---web-应用)
    - [项目结构](#项目结构)
    - [主应用](#主应用)
  - [📊 New Relic Dashboard](#-new-relic-dashboard)
    - [自定义仪表板](#自定义仪表板)
    - [NRQL 查询示例](#nrql-查询示例)
  - [🚨 告警配置](#-告警配置)
    - [告警策略](#告警策略)
  - [✅ 最佳实践](#-最佳实践)
    - [1. 性能优化](#1-性能优化)
    - [2. 成本优化](#2-成本优化)
  - [🏢 生产案例](#-生产案例)
    - [案例 1: 电商平台](#案例-1-电商平台)
    - [案例 2: SaaS 应用](#案例-2-saas-应用)
  - [📚 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [开源项目](#开源项目)

---

## 🎯 概述

### 什么是 New Relic？

**New Relic** 是业界领先的全栈可观测性平台：

- 📊 **APM**: 应用性能监控
- 🔍 **分布式追踪**: 端到端请求追踪
- 📈 **基础设施监控**: 服务器/容器/Kubernetes
- 📝 **日志管理**: 集中日志分析
- 🚨 **智能告警**: AI 驱动的异常检测
- 🎯 **业务分析**: 用户体验监控

### 为什么选择 New Relic？

✅ **优势**:

1. **OTLP 原生支持**: 无需专用 SDK
2. **自动化**: AI 辅助的根因分析
3. **统一平台**: 一站式可观测性解决方案
4. **企业级**: 高可用,安全合规
5. **丰富生态**: 300+ 集成

---

## 🚀 快速开始

### Cargo.toml

```toml
[package]
name = "newrelic-rust-demo"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Web 框架
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# OTLP (New Relic 支持)
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["grpc-tonic"] }

# 指标
metrics = "0.23"
metrics-exporter-prometheus = "0.15"

# 工具
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

### 基础配置

```rust
// src/newrelic.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

/// New Relic 配置
pub struct NewRelicConfig {
    pub license_key: String,
    pub service_name: String,
    pub endpoint: String,
}

impl Default for NewRelicConfig {
    fn default() -> Self {
        Self {
            license_key: std::env::var("NEW_RELIC_LICENSE_KEY")
                .expect("NEW_RELIC_LICENSE_KEY 环境变量未设置"),
            service_name: "rust-app".to_string(),
            endpoint: "https://otlp.nr-data.net:4317".to_string(), // US endpoint
            // EU endpoint: "https://otlp.eu01.nr-data.net:4317"
        }
    }
}

/// 初始化 New Relic 遥测
pub fn init_newrelic_telemetry(config: NewRelicConfig) -> anyhow::Result<()> {
    // 1. 配置 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&config.endpoint)
        .with_timeout(Duration::from_secs(5))
        .with_metadata({
            let mut map = tonic::metadata::MetadataMap::new();
            map.insert(
                "api-key",
                config.license_key.parse().unwrap(),
            );
            map
        });

    // 2. 配置 Tracer Provider
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", config.service_name.clone()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    
                    // New Relic 专用属性
                    KeyValue::new("newrelic.source", "opentelemetry"),
                    KeyValue::new("service.instance.id", hostname()),
                    
                    // 环境信息
                    KeyValue::new("deployment.environment", deployment_env()),
                    KeyValue::new("host.name", hostname()),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    global::set_tracer_provider(tracer.provider().unwrap());

    // 3. 配置 tracing-subscriber
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info,rust_app=debug"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(global::tracer("rust-app")))
        .init();

    tracing::info!("✅ New Relic 遥测已初始化");

    Ok(())
}

fn hostname() -> String {
    std::env::var("HOSTNAME")
        .unwrap_or_else(|_| "unknown".to_string())
}

fn deployment_env() -> String {
    std::env::var("DEPLOYMENT_ENVIRONMENT")
        .unwrap_or_else(|_| "development".to_string())
}
```

---

## 🔍 核心集成

### 1. 追踪集成

```rust
// src/tracing_integration.rs
use tracing::{info, instrument, Span};
use opentelemetry::trace::{SpanKind, Status};

/// HTTP 请求追踪
#[instrument(
    skip(body),
    fields(
        http.method = %method,
        http.url = %url,
        http.status_code = tracing::field::Empty,
        http.response_time_ms = tracing::field::Empty,
    )
)]
pub async fn http_request(
    method: &str,
    url: &str,
    body: Option<String>,
) -> Result<Response, Error> {
    let start = std::time::Instant::now();
    let span = Span::current();

    info!("发起 HTTP 请求");

    // 执行请求
    let client = reqwest::Client::new();
    let result = match method {
        "GET" => client.get(url).send().await,
        "POST" => client.post(url)
            .body(body.unwrap_or_default())
            .send()
            .await,
        _ => return Err(Error::UnsupportedMethod),
    };

    let duration = start.elapsed();

    // 记录响应信息
    match result {
        Ok(response) => {
            let status = response.status().as_u16();
            span.record("http.status_code", status);
            span.record("http.response_time_ms", duration.as_millis() as i64);

            info!(status, "请求成功");
            Ok(Response { status, body: response.text().await? })
        }
        Err(e) => {
            span.record("http.status_code", 0);
            span.record("error", true);
            
            tracing::error!(error = %e, "请求失败");
            Err(Error::Request(e))
        }
    }
}

/// 数据库查询追踪
#[instrument(
    skip(db),
    fields(
        db.system = "postgresql",
        db.statement = %sql,
        db.operation = tracing::field::Empty,
        db.rows_affected = tracing::field::Empty,
    )
)]
pub async fn database_query(
    db: &DatabasePool,
    sql: &str,
) -> Result<Vec<Row>, Error> {
    let span = Span::current();

    // 提取操作类型
    let operation = sql.split_whitespace().next().unwrap_or("UNKNOWN");
    span.record("db.operation", operation);

    info!("执行数据库查询");

    let result = db.query(sql).await?;
    span.record("db.rows_affected", result.len() as i64);

    Ok(result)
}

#[derive(Debug)]
pub struct Response {
    pub status: u16,
    pub body: String,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("不支持的 HTTP 方法")]
    UnsupportedMethod,
    #[error("请求错误: {0}")]
    Request(#[from] reqwest::Error),
}
```

### 2. 指标集成

```rust
// src/metrics_integration.rs
use metrics::{counter, gauge, histogram};

/// 业务指标
pub mod business_metrics {
    use super::*;

    /// 订单创建
    pub fn record_order_created(order_value: f64, product_category: &str) {
        counter!("orders_created_total", 1, "category" => product_category.to_string());
        histogram!("order_value_usd", order_value, "category" => product_category.to_string());
    }

    /// 用户注册
    pub fn record_user_registered(source: &str) {
        counter!("users_registered_total", 1, "source" => source.to_string());
    }

    /// 支付成功
    pub fn record_payment_successful(payment_method: &str, amount: f64) {
        counter!(
            "payments_successful_total", 
            1, 
            "method" => payment_method.to_string()
        );
        histogram!(
            "payment_amount_usd", 
            amount, 
            "method" => payment_method.to_string()
        );
    }
}

/// 系统指标
pub mod system_metrics {
    use super::*;

    /// 活跃连接数
    pub fn set_active_connections(count: usize) {
        gauge!("active_connections", count as f64);
    }

    /// 队列长度
    pub fn set_queue_length(queue_name: &str, length: usize) {
        gauge!("queue_length", length as f64, "queue" => queue_name.to_string());
    }

    /// 缓存命中率
    pub fn record_cache_hit(cache_name: &str, hit: bool) {
        let label = if hit { "hit" } else { "miss" };
        counter!("cache_access_total", 1, 
            "cache" => cache_name.to_string(),
            "result" => label.to_string()
        );
    }
}
```

### 3. 日志集成

```rust
// src/logging_integration.rs
use tracing::{error, warn, info, debug};
use serde_json::json;

/// 结构化日志
pub fn log_event(event_type: &str, data: serde_json::Value) {
    info!(
        event_type = %event_type,
        data = %data,
        "业务事件"
    );
}

/// 错误日志 (自动关联追踪)
pub fn log_error(error: &dyn std::error::Error, context: &str) {
    error!(
        error = %error,
        context = %context,
        error_type = std::any::type_name_of_val(error),
        "错误发生"
    );
}

/// 使用示例
pub fn example_logging() {
    // 1. 业务事件
    log_event("user_login", json!({
        "user_id": 12345,
        "ip_address": "192.168.1.1",
        "user_agent": "Mozilla/5.0"
    }));

    // 2. 性能警告
    warn!(
        duration_ms = 1500,
        threshold_ms = 1000,
        "慢查询检测"
    );

    // 3. 调试信息
    debug!(
        cache_key = "user:12345",
        ttl_seconds = 3600,
        "缓存写入"
    );
}
```

---

## 📦 完整示例 - Web 应用

### 项目结构

```text
newrelic-web-app/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── newrelic.rs
│   ├── handlers/
│   │   ├── mod.rs
│   │   ├── users.rs
│   │   └── orders.rs
│   ├── middleware/
│   │   └── tracing.rs
│   └── metrics/
│       └── business.rs
├── .env
└── config/
    └── newrelic.yaml
```

### 主应用

```rust
// src/main.rs
use axum::{Router, routing::get};
use std::net::SocketAddr;
use tower_http::trace::TraceLayer;

mod newrelic;
mod handlers;
mod middleware;
mod metrics;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1. 加载配置
    dotenvy::dotenv().ok();

    // 2. 初始化 New Relic
    let config = newrelic::NewRelicConfig::default();
    newrelic::init_newrelic_telemetry(config)?;

    // 3. 启动 Prometheus 导出器 (可选,用于本地调试)
    let prometheus_exporter = metrics_exporter_prometheus::PrometheusBuilder::new()
        .install_recorder()?;

    tokio::spawn(async move {
        let app = Router::new()
            .route("/metrics", get(|| async move {
                prometheus_exporter.render()
            }));
        
        axum::Server::bind(&"0.0.0.0:9090".parse().unwrap())
            .serve(app.into_make_service())
            .await
            .unwrap();
    });

    // 4. 创建主应用路由
    let app = Router::new()
        .route("/", get(handlers::health_check))
        .route("/api/users/:id", get(handlers::users::get_user))
        .route("/api/orders", get(handlers::orders::create_order))
        .layer(TraceLayer::new_for_http())
        .layer(middleware::tracing::NewRelicTracingMiddleware);

    // 5. 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    tracing::info!("🌐 服务监听: {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    // 6. 关闭遥测
    opentelemetry::global::shutdown_tracer_provider();

    Ok(())
}
```

```rust
// src/handlers/users.rs
use axum::{extract::Path, Json};
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub created_at: String,
}

#[instrument(fields(user.id = %id))]
pub async fn get_user(Path(id): Path<u64>) -> Result<Json<User>, AppError> {
    info!("获取用户信息");

    // 记录自定义指标
    metrics::counter!("api_users_get_total", 1);

    // 模拟数据库查询
    let user = User {
        id,
        name: format!("User {}", id),
        email: format!("user{}@example.com", id),
        created_at: chrono::Utc::now().to_rfc3339(),
    };

    // 记录 New Relic 自定义事件
    tracing::info!(
        event_type = "UserAccess",
        user_id = id,
        timestamp = %chrono::Utc::now(),
        "用户访问事件"
    );

    Ok(Json(user))
}

#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("用户不存在")]
    NotFound,
}

impl axum::response::IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        (
            axum::http::StatusCode::NOT_FOUND,
            self.to_string()
        ).into_response()
    }
}
```

---

## 📊 New Relic Dashboard

### 自定义仪表板

```json
{
  "name": "Rust 应用监控",
  "permissions": "PUBLIC_READ_WRITE",
  "pages": [
    {
      "name": "应用概览",
      "widgets": [
        {
          "title": "响应时间 (P95)",
          "configuration": {
            "nrql": {
              "query": "SELECT percentile(duration, 95) FROM Span WHERE service.name = 'rust-app' TIMESERIES"
            }
          }
        },
        {
          "title": "错误率",
          "configuration": {
            "nrql": {
              "query": "SELECT percentage(count(*), WHERE otel.status_code = 'ERROR') FROM Span WHERE service.name = 'rust-app' TIMESERIES"
            }
          }
        },
        {
          "title": "吞吐量 (RPM)",
          "configuration": {
            "nrql": {
              "query": "SELECT rate(count(*), 1 minute) FROM Span WHERE service.name = 'rust-app' AND kind = 'server' TIMESERIES"
            }
          }
        },
        {
          "title": "慢查询追踪",
          "configuration": {
            "nrql": {
              "query": "SELECT trace.id, name, duration FROM Span WHERE service.name = 'rust-app' AND duration > 1 SINCE 1 hour ago LIMIT 100"
            }
          }
        }
      ]
    },
    {
      "name": "业务指标",
      "widgets": [
        {
          "title": "订单创建趋势",
          "configuration": {
            "nrql": {
              "query": "SELECT count(*) FROM Metric WHERE metricName = 'orders_created_total' TIMESERIES FACET category"
            }
          }
        },
        {
          "title": "平均订单金额",
          "configuration": {
            "nrql": {
              "query": "SELECT average(order_value_usd) FROM Metric FACET category TIMESERIES"
            }
          }
        }
      ]
    }
  ]
}
```

### NRQL 查询示例

```sql
-- 1. 查找最慢的端点
SELECT average(duration) as 'Avg Duration (ms)', count(*) as 'Count'
FROM Span
WHERE service.name = 'rust-app' AND kind = 'server'
FACET name
SINCE 1 hour ago
LIMIT 20

-- 2. 错误分析
SELECT count(*) as 'Error Count', latest(error.message) as 'Latest Error'
FROM Span
WHERE service.name = 'rust-app' AND otel.status_code = 'ERROR'
FACET error.type
SINCE 1 day ago

-- 3. 追踪特定用户的请求
SELECT trace.id, name, duration
FROM Span
WHERE service.name = 'rust-app' AND user.id = '12345'
SINCE 1 hour ago

-- 4. 数据库查询性能
SELECT average(duration) as 'Avg Query Time', percentile(duration, 95) as 'P95'
FROM Span
WHERE service.name = 'rust-app' AND db.system = 'postgresql'
FACET db.operation
SINCE 1 hour ago

-- 5. 业务转化漏斗
SELECT funnel(
  WHERE event_type = 'UserAccess',
  WHERE event_type = 'AddToCart',
  WHERE event_type = 'Checkout',
  WHERE event_type = 'PaymentSuccess'
)
FROM CustomEvent
SINCE 1 day ago
```

---

## 🚨 告警配置

### 告警策略

```yaml
# New Relic Alert Policy Configuration
policies:
  - name: "Rust 应用性能告警"
    incident_preference: "PER_CONDITION"
    
    conditions:
      # 1. 高错误率
      - name: "错误率 > 5%"
        type: "NRQL"
        nrql:
          query: |
            SELECT percentage(count(*), WHERE otel.status_code = 'ERROR')
            FROM Span
            WHERE service.name = 'rust-app'
        critical_threshold:
          value: 5
          duration_minutes: 5
        
      # 2. 响应时间过慢
      - name: "P95 响应时间 > 1s"
        type: "NRQL"
        nrql:
          query: |
            SELECT percentile(duration, 95)
            FROM Span
            WHERE service.name = 'rust-app' AND kind = 'server'
        critical_threshold:
          value: 1000  # 毫秒
          duration_minutes: 5
      
      # 3. 吞吐量异常下降
      - name: "吞吐量下降 > 50%"
        type: "NRQL"
        nrql:
          query: |
            SELECT rate(count(*), 1 minute)
            FROM Span
            WHERE service.name = 'rust-app'
        baseline_direction: "LOWER_ONLY"
        critical_threshold:
          value: 50  # 百分比
          duration_minutes: 10

    notification_channels:
      - type: "EMAIL"
        email: "ops@example.com"
      - type: "SLACK"
        webhook_url: "https://hooks.slack.com/services/xxx"
      - type: "PAGERDUTY"
        integration_key: "xxx"
```

---

## ✅ 最佳实践

### 1. 性能优化

```rust
// 批量导出优化
pub fn configure_batch_exporter() -> opentelemetry_otlp::OtlpTracePipeline {
    opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_batch_config(
            opentelemetry_sdk::trace::BatchConfig::default()
                .with_max_queue_size(2048)
                .with_max_export_batch_size(512)
                .with_scheduled_delay(std::time::Duration::from_secs(5))
        )
}

// 采样策略
pub fn production_sampler() -> Sampler {
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10% 采样
    ))
}
```

### 2. 成本优化

```rust
// 智能采样 (高价值请求 100%,正常请求 10%)
pub struct AdaptiveSampler {
    high_value_endpoints: Vec<String>,
}

impl AdaptiveSampler {
    pub fn should_sample(&self, span_name: &str, user_tier: &str) -> bool {
        // VIP 用户 100% 采样
        if user_tier == "VIP" {
            return true;
        }

        // 关键端点 100% 采样
        if self.high_value_endpoints.iter().any(|e| span_name.contains(e)) {
            return true;
        }

        // 其他请求 10% 采样
        rand::random::<f64>() < 0.1
    }
}
```

---

## 🏢 生产案例

### 案例 1: 电商平台

**背景**: 某电商平台使用 Rust + New Relic 监控微服务

**成果**:

- 🎯 **MTTR**: 平均故障恢复时间从 30 分钟降至 5 分钟
- 📊 **可见性**: 端到端追踪覆盖率 100%
- 💰 **成本**: 通过智能采样节省 60% 监控成本
- 🚀 **性能**: 定位并修复 15+ 性能瓶颈

### 案例 2: SaaS 应用

**背景**: 某 SaaS 应用使用 New Relic 监控全球部署

**成果**:

- 🌐 **全球监控**: 10+ 区域实时监控
- 🔍 **异常检测**: AI 自动检测 80% 的异常
- 📈 **业务洞察**: 实时业务指标分析
- 🏆 **SLA**: 99.95% 可用性保证

---

## 📚 参考资源

### 官方文档

- [New Relic Documentation](https://docs.newrelic.com/)
- [New Relic OTLP Endpoint](https://docs.newrelic.com/docs/more-integrations/open-source-telemetry-integrations/opentelemetry/opentelemetry-setup/)
- [NRQL Reference](https://docs.newrelic.com/docs/nrql/nrql-syntax-clauses-functions/)

### 开源项目

- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
- [New Relic Examples](https://github.com/newrelic/newrelic-telemetry-sdk-rust)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust New Relic 团队  
**下次审查**: 2025年12月11日

---

**🌟 使用 New Relic 构建世界级可观测性平台！🚀**-
