# Prometheus 集成 - Rust 完整版

## 目录

- [Prometheus 集成 - Rust 完整版](#prometheus-集成---rust-完整版)
  - [目录](#目录)
  - [1. Prometheus 概述](#1-prometheus-概述)
    - [1.1 Prometheus 架构](#11-prometheus-架构)
    - [1.2 与 OpenTelemetry 的关系](#12-与-opentelemetry-的关系)
  - [2. Prometheus Exporter](#2-prometheus-exporter)
    - [2.1 基础配置](#21-基础配置)
    - [2.2 Metrics 导出](#22-metrics-导出)
    - [2.3 HTTP 端点](#23-http-端点)
  - [3. 指标类型映射](#3-指标类型映射)
    - [3.1 Counter](#31-counter)
    - [3.2 Gauge](#32-gauge)
    - [3.3 Histogram](#33-histogram)
    - [3.4 Summary](#34-summary)
  - [4. 标签处理](#4-标签处理)
    - [4.1 标签命名](#41-标签命名)
    - [4.2 高基数问题](#42-高基数问题)
  - [5. 完整示例](#5-完整示例)
    - [5.1 HTTP 服务器指标](#51-http-服务器指标)
    - [5.2 业务指标](#52-业务指标)
  - [6. Prometheus 查询](#6-prometheus-查询)
    - [6.1 PromQL 基础](#61-promql-基础)
    - [6.2 常用查询](#62-常用查询)
  - [7. Grafana 集成](#7-grafana-集成)
    - [7.1 数据源配置](#71-数据源配置)
    - [7.2 仪表板](#72-仪表板)
  - [8. 告警规则](#8-告警规则)
    - [8.1 告警配置](#81-告警配置)
    - [8.2 Alertmanager](#82-alertmanager)
  - [9. 性能优化](#9-性能优化)
    - [9.1 采样率](#91-采样率)
    - [9.2 指标聚合](#92-指标聚合)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
    - [10.1 高可用配置](#101-高可用配置)
    - [10.2 数据持久化](#102-数据持久化)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [指标类型对比](#指标类型对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Prometheus 概述

### 1.1 Prometheus 架构

````text
Prometheus 架构:

┌─────────────┐     Pull       ┌──────────────┐
│ Application │ ◄───────────── │  Prometheus  │
│  (Exporter) │                │    Server    │
└─────────────┘                └──────────────┘
                                       │
                                       │ Query
                                       ▼
                               ┌──────────────┐
                               │   Grafana    │
                               └──────────────┘
                                       │
                                       │ Alert
                                       ▼
                               ┌──────────────┐
                               │ Alertmanager │
                               └──────────────┘

核心组件:
1. Prometheus Server: 采集和存储时序数据
2. Client Library: 应用程序指标库
3. Pushgateway: 短期任务支持
4. Exporters: 第三方服务指标导出
5. Alertmanager: 告警管理
````

### 1.2 与 OpenTelemetry 的关系

````text
OpenTelemetry + Prometheus:

┌──────────────────┐
│  Application     │
│  (OpenTelemetry) │
└────────┬─────────┘
         │
         ├──► OTLP Exporter ──► Jaeger (Traces)
         │
         └──► Prometheus      ──► Prometheus (Metrics)
              Exporter

优势:
1. 统一 API: OpenTelemetry 提供统一的指标 API
2. 自动转换: 自动转换为 Prometheus 格式
3. 双向支持: 既支持 OTLP 也支持 Prometheus
4. 灵活部署: 可同时导出到多个后端
````

---

## 2. Prometheus Exporter

### 2.1 基础配置

````toml
[dependencies]
opentelemetry = { version = "0.31.0", features = ["metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["metrics", "rt-tokio"] }
opentelemetry-prometheus = "0.17"
prometheus = "0.13"
tokio = { version = "1.47", features = ["full"] }
axum = "0.7"
````

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::{TextEncoder, Encoder};

/// 初始化 Prometheus Exporter
pub fn init_prometheus() -> PrometheusExporter {
    // 创建 Prometheus Exporter
    let exporter = opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()
        .expect("Failed to create Prometheus exporter");
    
    // 设置全局 MeterProvider
    global::set_meter_provider(exporter.meter_provider().unwrap());
    
    exporter
}
````

### 2.2 Metrics 导出

````rust
use opentelemetry::metrics::{Counter, Histogram, Gauge};

/// 应用指标
pub struct AppMetrics {
    pub http_requests_total: Counter<u64>,
    pub http_request_duration: Histogram<f64>,
    pub active_connections: Gauge<i64>,
}

impl AppMetrics {
    pub fn new() -> Self {
        let meter = global::meter("my-app");
        
        Self {
            http_requests_total: meter
                .u64_counter("http_requests_total")
                .with_description("Total HTTP requests")
                .with_unit("requests")
                .build(),
            
            http_request_duration: meter
                .f64_histogram("http_request_duration_seconds")
                .with_description("HTTP request duration")
                .with_unit("seconds")
                .build(),
            
            active_connections: meter
                .i64_gauge("http_active_connections")
                .with_description("Active HTTP connections")
                .build(),
        }
    }
}
````

### 2.3 HTTP 端点

````rust
use axum::{Router, routing::get, extract::State};
use std::sync::Arc;

/// 创建 Metrics 端点
pub fn metrics_routes(exporter: Arc<PrometheusExporter>) -> Router {
    Router::new()
        .route("/metrics", get(metrics_handler))
        .with_state(exporter)
}

/// Metrics Handler
async fn metrics_handler(
    State(exporter): State<Arc<PrometheusExporter>>,
) -> String {
    let encoder = TextEncoder::new();
    let metric_families = exporter.registry().gather();
    let mut buffer = Vec::new();
    
    encoder.encode(&metric_families, &mut buffer).unwrap();
    
    String::from_utf8(buffer).unwrap()
}

/// 启动服务器
#[tokio::main]
async fn main() {
    let exporter = Arc::new(init_prometheus());
    
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }))
        .merge(metrics_routes(exporter));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:9090")
        .await
        .unwrap();
    
    println!("Metrics server listening on http://0.0.0.0:9090/metrics");
    
    axum::serve(listener, app).await.unwrap();
}
````

**Prometheus 输出示例**:

````text
# HELP http_requests_total Total HTTP requests
# TYPE http_requests_total counter
http_requests_total{method="GET",path="/api/users"} 12345

# HELP http_request_duration_seconds HTTP request duration
# TYPE http_request_duration_seconds histogram
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.005"} 100
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.01"} 200
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.025"} 300
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="+Inf"} 500
http_request_duration_seconds_sum{method="GET",path="/api/users"} 12.5
http_request_duration_seconds_count{method="GET",path="/api/users"} 500

# HELP http_active_connections Active HTTP connections
# TYPE http_active_connections gauge
http_active_connections 42
````

---

## 3. 指标类型映射

### 3.1 Counter

````rust
use opentelemetry::metrics::Counter;

/// Counter 示例 (单调递增)
pub fn counter_example() {
    let meter = global::meter("my-app");
    
    let requests = meter
        .u64_counter("http_requests_total")
        .with_description("Total HTTP requests")
        .build();
    
    // 递增
    requests.add(1, &[
        KeyValue::new("method", "GET"),
        KeyValue::new("path", "/api/users"),
    ]);
}
````

**Prometheus 格式**:

````text
# TYPE http_requests_total counter
http_requests_total{method="GET",path="/api/users"} 12345
````

### 3.2 Gauge

````rust
use opentelemetry::metrics::Gauge;

/// Gauge 示例 (可增可减)
pub fn gauge_example() {
    let meter = global::meter("my-app");
    
    let connections = meter
        .i64_gauge("http_active_connections")
        .with_description("Active HTTP connections")
        .build();
    
    // 记录当前值
    connections.record(42, &[]);
}
````

**Prometheus 格式**:

````text
# TYPE http_active_connections gauge
http_active_connections 42
````

### 3.3 Histogram

````rust
use opentelemetry::metrics::Histogram;

/// Histogram 示例 (分布统计)
pub fn histogram_example() {
    let meter = global::meter("my-app");
    
    let duration = meter
        .f64_histogram("http_request_duration_seconds")
        .with_description("HTTP request duration")
        .build();
    
    // 记录延迟
    duration.record(0.123, &[
        KeyValue::new("method", "GET"),
        KeyValue::new("path", "/api/users"),
    ]);
}
````

**Prometheus 格式**:

````text
# TYPE http_request_duration_seconds histogram
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.005"} 100
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.01"} 200
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.025"} 300
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.05"} 400
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="0.1"} 450
http_request_duration_seconds_bucket{method="GET",path="/api/users",le="+Inf"} 500
http_request_duration_seconds_sum{method="GET",path="/api/users"} 62.5
http_request_duration_seconds_count{method="GET",path="/api/users"} 500
````

### 3.4 Summary

````text
Summary vs Histogram:

Histogram (推荐):
- 服务端计算分位数
- 支持聚合
- 可配置 bucket

Summary:
- 客户端计算分位数
- 不支持聚合
- 精确度高但开销大

推荐: 使用 Histogram，Prometheus 服务端计算分位数
````

---

## 4. 标签处理

### 4.1 标签命名

````text
Prometheus 标签命名规范:

1. 使用小写字母
   ✅ method, status_code, path
   ❌ Method, StatusCode, Path

2. 使用下划线分隔
   ✅ status_code, user_id
   ❌ statusCode, userId

3. 避免保留标签
   ❌ __name__, job, instance (Prometheus 保留)

4. 有意义的标签
   ✅ method="GET", path="/api/users"
   ❌ label1="value1", label2="value2"
````

````rust
/// 标准标签使用
pub fn record_http_request(method: &str, path: &str, status: u16, duration: f64) {
    let meter = global::meter("my-app");
    
    let requests = meter.u64_counter("http_requests_total").build();
    let duration_hist = meter.f64_histogram("http_request_duration_seconds").build();
    
    let labels = &[
        KeyValue::new("method", method.to_string()),
        KeyValue::new("path", path.to_string()),
        KeyValue::new("status_code", status.to_string()),
    ];
    
    requests.add(1, labels);
    duration_hist.record(duration, labels);
}
````

### 4.2 高基数问题

````text
高基数标签问题:

❌ 高基数标签 (避免):
- user_id (数百万用户)
- trace_id (无限唯一值)
- session_id (每次请求不同)
- timestamp (时间戳)

✅ 低基数标签 (推荐):
- method (GET, POST, PUT, DELETE)
- status_code (200, 404, 500)
- path (有限的 API 路径)
- region (us-west-2, eu-central-1)

解决方案:
1. 使用路径模板: /api/users/:id → /api/users/{id}
2. 状态码分组: 200-299 → 2xx
3. 限制标签数量: 每个指标 < 10 个标签
4. 动态标签: 使用 Exemplars (OpenTelemetry)
````

````rust
/// 路径模板化 (避免高基数)
pub fn normalize_path(path: &str) -> String {
    // /api/users/12345 → /api/users/{id}
    let re = regex::Regex::new(r"/\d+").unwrap();
    re.replace_all(path, "/{id}").to_string()
}

pub fn record_request_safe(method: &str, path: &str, status: u16) {
    let normalized_path = normalize_path(path);
    let status_class = format!("{}xx", status / 100);
    
    let labels = &[
        KeyValue::new("method", method.to_string()),
        KeyValue::new("path", normalized_path),
        KeyValue::new("status_class", status_class),
    ];
    
    let meter = global::meter("my-app");
    meter.u64_counter("http_requests_total").build().add(1, labels);
}
````

---

## 5. 完整示例

### 5.1 HTTP 服务器指标

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
    Router,
};
use std::time::Instant;

/// HTTP 指标中间件
pub async fn metrics_middleware(
    request: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = request.method().to_string();
    let path = request.uri().path().to_string();
    
    // 活跃连接 +1
    record_active_connections(1);
    
    // 处理请求
    let response = next.run(request).await;
    
    // 活跃连接 -1
    record_active_connections(-1);
    
    // 记录指标
    let duration = start.elapsed().as_secs_f64();
    let status = response.status().as_u16();
    
    record_http_request(&method, &path, status, duration);
    
    response
}

fn record_http_request(method: &str, path: &str, status: u16, duration: f64) {
    let meter = global::meter("my-app");
    
    let labels = &[
        KeyValue::new("method", method.to_string()),
        KeyValue::new("path", normalize_path(path)),
        KeyValue::new("status_code", status.to_string()),
    ];
    
    // 请求总数
    meter
        .u64_counter("http_requests_total")
        .build()
        .add(1, labels);
    
    // 请求延迟
    meter
        .f64_histogram("http_request_duration_seconds")
        .build()
        .record(duration, labels);
}

fn record_active_connections(delta: i64) {
    let meter = global::meter("my-app");
    
    // 使用 UpDownCounter 或直接设置 Gauge
    meter
        .i64_up_down_counter("http_active_connections")
        .build()
        .add(delta, &[]);
}
````

### 5.2 业务指标

````rust
use opentelemetry::global;

/// 业务指标
pub struct BusinessMetrics {
    meter: opentelemetry::metrics::Meter,
}

impl BusinessMetrics {
    pub fn new() -> Self {
        Self {
            meter: global::meter("my-app-business"),
        }
    }
    
    /// 记录订单
    pub fn record_order(&self, amount: f64, status: &str) {
        // 订单总数
        self.meter
            .u64_counter("orders_total")
            .with_description("Total orders")
            .build()
            .add(1, &[KeyValue::new("status", status.to_string())]);
        
        // 订单金额
        self.meter
            .f64_counter("orders_amount_total")
            .with_description("Total order amount")
            .with_unit("USD")
            .build()
            .add(amount, &[KeyValue::new("status", status.to_string())]);
    }
    
    /// 记录用户注册
    pub fn record_user_registration(&self, source: &str) {
        self.meter
            .u64_counter("users_registered_total")
            .with_description("Total user registrations")
            .build()
            .add(1, &[KeyValue::new("source", source.to_string())]);
    }
    
    /// 记录缓存命中率
    pub fn record_cache_hit(&self, hit: bool) {
        let result = if hit { "hit" } else { "miss" };
        
        self.meter
            .u64_counter("cache_requests_total")
            .with_description("Total cache requests")
            .build()
            .add(1, &[KeyValue::new("result", result.to_string())]);
    }
}
````

---

## 6. Prometheus 查询

### 6.1 PromQL 基础

````promql
# 基础查询
http_requests_total

# 带标签过滤
http_requests_total{method="GET"}
http_requests_total{method="GET", status_code="200"}

# 正则表达式
http_requests_total{path=~"/api/.*"}
http_requests_total{status_code!~"5.."}

# 速率 (每秒请求数)
rate(http_requests_total[5m])

# 增长 (5分钟内的增长)
increase(http_requests_total[5m])

# 分位数 (P95 延迟)
histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))

# 求和
sum(rate(http_requests_total[5m])) by (method)

# 平均值
avg(http_request_duration_seconds_sum / http_request_duration_seconds_count)
````

### 6.2 常用查询

````promql
# 1. QPS (每秒请求数)
sum(rate(http_requests_total[1m]))

# 2. 错误率
sum(rate(http_requests_total{status_code=~"5.."}[5m])) 
  / 
sum(rate(http_requests_total[5m]))

# 3. P95 延迟
histogram_quantile(0.95, 
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# 4. 按接口的 QPS
sum(rate(http_requests_total[1m])) by (path)

# 5. 活跃连接数
http_active_connections

# 6. 内存使用率
process_resident_memory_bytes / 1024 / 1024

# 7. CPU 使用率
rate(process_cpu_seconds_total[1m]) * 100

# 8. 成功率
sum(rate(http_requests_total{status_code=~"2.."}[5m])) 
  / 
sum(rate(http_requests_total[5m])) * 100
````

---

## 7. Grafana 集成

### 7.1 数据源配置

````yaml
# Grafana 数据源配置
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
    editable: true
````

### 7.2 仪表板

````json
{
  "dashboard": {
    "title": "Application Metrics",
    "panels": [
      {
        "title": "QPS",
        "type": "graph",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total[1m]))",
            "legendFormat": "QPS"
          }
        ]
      },
      {
        "title": "P95 Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
            "legendFormat": "P95"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total{status_code=~\"5..\"}[5m])) / sum(rate(http_requests_total[5m])) * 100",
            "legendFormat": "Error Rate %"
          }
        ]
      }
    ]
  }
}
````

**常用 Panel**:

````text
1. QPS (Time Series)
   - Query: sum(rate(http_requests_total[1m]))
   - Legend: QPS

2. P50/P95/P99 Latency (Time Series)
   - P50: histogram_quantile(0.50, ...)
   - P95: histogram_quantile(0.95, ...)
   - P99: histogram_quantile(0.99, ...)

3. Error Rate (Gauge)
   - Query: sum(rate(...{status=~"5.."})) / sum(rate(...))
   - Thresholds: 0-1% green, 1-5% yellow, >5% red

4. Active Connections (Stat)
   - Query: http_active_connections
   - Display: Current value

5. Top Endpoints (Table)
   - Query: topk(10, sum(rate(http_requests_total[5m])) by (path))
   - Format: Table
````

---

## 8. 告警规则

### 8.1 告警配置

````yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

alerting:
  alertmanagers:
    - static_configs:
        - targets:
            - alertmanager:9093

rule_files:
  - "alerts.yml"

scrape_configs:
  - job_name: 'my-app'
    static_configs:
      - targets: ['app:9090']
````

**alerts.yml**:

````yaml
groups:
  - name: application
    interval: 30s
    rules:
      # 高错误率告警
      - alert: HighErrorRate
        expr: |
          sum(rate(http_requests_total{status_code=~"5.."}[5m])) 
            / 
          sum(rate(http_requests_total[5m])) 
          > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }} (threshold: 5%)"
      
      # 高延迟告警
      - alert: HighLatency
        expr: |
          histogram_quantile(0.95,
            sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
          ) > 1.0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "P95 latency is {{ $value }}s (threshold: 1s)"
      
      # 服务下线告警
      - alert: ServiceDown
        expr: up{job="my-app"} == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "Service is down"
          description: "Service {{ $labels.instance }} is down"
      
      # 高内存使用告警
      - alert: HighMemoryUsage
        expr: |
          process_resident_memory_bytes / 1024 / 1024 > 1024
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage"
          description: "Memory usage is {{ $value }}MB (threshold: 1024MB)"
````

### 8.2 Alertmanager

````yaml
# alertmanager.yml
global:
  resolve_timeout: 5m

route:
  group_by: ['alertname', 'severity']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 12h
  receiver: 'slack'
  routes:
    - match:
        severity: critical
      receiver: 'pagerduty'
      continue: true

receivers:
  - name: 'slack'
    slack_configs:
      - api_url: 'https://hooks.slack.com/services/YOUR/WEBHOOK/URL'
        channel: '#alerts'
        title: '{{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'
  
  - name: 'pagerduty'
    pagerduty_configs:
      - service_key: 'YOUR_PAGERDUTY_KEY'
````

---

## 9. 性能优化

### 9.1 采样率

````rust
/// 采样配置
pub fn init_prometheus_with_sampling() -> PrometheusExporter {
    // 对于高频指标，考虑采样
    // 但 Prometheus 通常不需要采样，因为是拉取模式
    
    opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()
        .unwrap()
}
````

### 9.2 指标聚合

````promql
# 聚合查询减少基数

# ❌ 高基数 (每个路径单独)
http_requests_total{path="/api/users/1"}
http_requests_total{path="/api/users/2"}
...

# ✅ 低基数 (路径模板化)
http_requests_total{path="/api/users/{id}"}

# 聚合计算
sum(rate(http_requests_total[5m])) by (method, status_code)
````

---

## 10. 生产环境最佳实践

### 10.1 高可用配置

````yaml
# docker-compose.yml
version: '3.8'

services:
  prometheus-1:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-1-data:/prometheus
    ports:
      - "9091:9090"
  
  prometheus-2:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-2-data:/prometheus
    ports:
      - "9092:9090"
  
  # 使用 Thanos 实现高可用和长期存储
  thanos-sidecar-1:
    image: quay.io/thanos/thanos:latest
    command:
      - sidecar
      - --prometheus.url=http://prometheus-1:9090
      - --tsdb.path=/prometheus
    volumes:
      - prometheus-1-data:/prometheus

volumes:
  prometheus-1-data:
  prometheus-2-data:
````

### 10.2 数据持久化

````yaml
# Kubernetes StatefulSet
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: prometheus
spec:
  serviceName: prometheus
  replicas: 2
  selector:
    matchLabels:
      app: prometheus
  template:
    metadata:
      labels:
        app: prometheus
    spec:
      containers:
        - name: prometheus
          image: prom/prometheus:latest
          volumeMounts:
            - name: data
              mountPath: /prometheus
  volumeClaimTemplates:
    - metadata:
        name: data
      spec:
        accessModes: ["ReadWriteOnce"]
        resources:
          requests:
            storage: 100Gi
````

---

## 总结

### 核心要点

1. **Prometheus Exporter**: OpenTelemetry → Prometheus 格式转换
2. **指标类型**: Counter、Gauge、Histogram
3. **标签处理**: 避免高基数标签
4. **PromQL**: 强大的查询语言
5. **Grafana**: 可视化仪表板
6. **告警**: Alertmanager 集成

### 指标类型对比

| 类型 | 用途 | 示例 | Prometheus 类型 |
|------|------|------|----------------|
| Counter | 单调递增 | http_requests_total | counter |
| Gauge | 可增可减 | http_active_connections | gauge |
| Histogram | 分布统计 | http_request_duration_seconds | histogram |
| UpDownCounter | 可增可减计数 | queue_size | gauge |

### 最佳实践清单

- ✅ 使用 Prometheus Exporter 导出指标
- ✅ 指标命名遵循 Prometheus 规范
- ✅ 使用低基数标签（< 10 个标签）
- ✅ 路径模板化避免高基数
- ✅ HTTP 端点暴露 `/metrics`
- ✅ 配置合理的抓取间隔（15s）
- ✅ 使用 Histogram 而非 Summary
- ✅ 设置告警规则（错误率、延迟、服务下线）
- ✅ Grafana 可视化监控
- ✅ 生产环境高可用配置
- ❌ 不要使用高基数标签（user_id、trace_id）
- ❌ 不要过度细化指标
- ❌ 不要忘记设置单位（seconds、bytes）

---

**相关文档**:

- [Metrics 最佳实践](./01_Metrics_最佳实践_Rust完整版.md)
- [Metrics 数据模型](../01_数据模型/02_Metrics_数据模型_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [自定义 Exporter](../06_高级特性/01_自定义_Exporter_Rust完整版.md)
