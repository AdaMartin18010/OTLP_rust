# Prometheus & Grafana 完整集成指南 - Rust OTLP

> **Prometheus**: 3.1.0+  
> **Grafana**: 11.6.0+  
> **Rust**: 1.90+  
> **最后更新**: 2025年10月8日

---

---

## 1. Prometheus指标导出

### 1.1 Rust Prometheus集成

`Cargo.toml`:

```toml
[dependencies]
prometheus = { version = "0.13.4", features = ["process"] }
prometheus-hyper = "0.1.5"
hyper = { version = "1.7.0", features = ["full"] }
tokio = { version = "1.47.1", features = ["full"] }
```

### 1.2 指标定义

`src/metrics.rs`:

```rust
use prometheus::{
    Registry, Counter, Histogram, Gauge, IntGauge, IntCounter,
    IntCounterVec, HistogramVec, GaugeVec, Opts, HistogramOpts,
};
use once_cell::sync::Lazy;

/// 全局Prometheus Registry
pub static REGISTRY: Lazy<Registry> = Lazy::new(|| {
    Registry::new()
});

/// Span相关指标
pub mod spans {
    use super::*;
    
    /// Span创建总数
    pub static CREATED_TOTAL: Lazy<IntCounterVec> = Lazy::new(|| {
        let counter = IntCounterVec::new(
            Opts::new("otlp_spans_created_total", "Total number of spans created")
                .namespace("otlp")
                .subsystem("spans"),
            &["service_name", "span_kind"],
        ).unwrap();
        REGISTRY.register(Box::new(counter.clone())).unwrap();
        counter
    });
    
    /// Span导出总数
    pub static EXPORTED_TOTAL: Lazy<IntCounterVec> = Lazy::new(|| {
        let counter = IntCounterVec::new(
            Opts::new("otlp_spans_exported_total", "Total number of spans exported")
                .namespace("otlp")
                .subsystem("spans"),
            &["exporter", "status"],
        ).unwrap();
        REGISTRY.register(Box::new(counter.clone())).unwrap();
        counter
    });
    
    /// Span导出失败总数
    pub static EXPORT_ERRORS_TOTAL: Lazy<IntCounterVec> = Lazy::new(|| {
        let counter = IntCounterVec::new(
            Opts::new("otlp_spans_export_errors_total", "Total number of span export errors")
                .namespace("otlp")
                .subsystem("spans"),
            &["exporter", "error_type"],
        ).unwrap();
        REGISTRY.register(Box::new(counter.clone())).unwrap();
        counter
    });
    
    /// Span持续时间分布
    pub static DURATION_SECONDS: Lazy<HistogramVec> = Lazy::new(|| {
        let histogram = HistogramVec::new(
            HistogramOpts::new("otlp_spans_duration_seconds", "Span duration in seconds")
                .namespace("otlp")
                .subsystem("spans")
                .buckets(vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0, 10.0]),
            &["service_name", "span_kind"],
        ).unwrap();
        REGISTRY.register(Box::new(histogram.clone())).unwrap();
        histogram
    });
}

/// 导出器相关指标
pub mod exporter {
    use super::*;
    
    /// 导出批次大小分布
    pub static BATCH_SIZE: Lazy<Histogram> = Lazy::new(|| {
        let histogram = Histogram::with_opts(
            HistogramOpts::new("otlp_exporter_batch_size", "Exporter batch size")
                .namespace("otlp")
                .subsystem("exporter")
                .buckets(vec![10.0, 50.0, 100.0, 500.0, 1000.0, 5000.0]),
        ).unwrap();
        REGISTRY.register(Box::new(histogram.clone())).unwrap();
        histogram
    });
    
    /// 导出延迟分布
    pub static EXPORT_LATENCY_SECONDS: Lazy<HistogramVec> = Lazy::new(|| {
        let histogram = HistogramVec::new(
            HistogramOpts::new("otlp_exporter_latency_seconds", "Exporter latency in seconds")
                .namespace("otlp")
                .subsystem("exporter")
                .buckets(vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0]),
            &["exporter", "protocol"],
        ).unwrap();
        REGISTRY.register(Box::new(histogram.clone())).unwrap();
        histogram
    });
    
    /// 当前队列大小
    pub static QUEUE_SIZE: Lazy<IntGaugeVec> = Lazy::new(|| {
        let gauge = IntGaugeVec::new(
            Opts::new("otlp_exporter_queue_size", "Current queue size")
                .namespace("otlp")
                .subsystem("exporter"),
            &["exporter"],
        ).unwrap();
        REGISTRY.register(Box::new(gauge.clone())).unwrap();
        gauge
    });
}

/// 系统资源指标
pub mod system {
    use super::*;
    
    /// CPU使用率
    pub static CPU_USAGE: Lazy<Gauge> = Lazy::new(|| {
        let gauge = Gauge::with_opts(
            Opts::new("otlp_system_cpu_usage_percent", "CPU usage percentage")
                .namespace("otlp")
                .subsystem("system"),
        ).unwrap();
        REGISTRY.register(Box::new(gauge.clone())).unwrap();
        gauge
    });
    
    /// 内存使用量（字节）
    pub static MEMORY_USAGE_BYTES: Lazy<IntGauge> = Lazy::new(|| {
        let gauge = IntGauge::with_opts(
            Opts::new("otlp_system_memory_usage_bytes", "Memory usage in bytes")
                .namespace("otlp")
                .subsystem("system"),
        ).unwrap();
        REGISTRY.register(Box::new(gauge.clone())).unwrap();
        gauge
    });
    
    /// Goroutine/Task数量
    pub static TASKS_COUNT: Lazy<IntGauge> = Lazy::new(|| {
        let gauge = IntGauge::with_opts(
            Opts::new("otlp_system_tasks_count", "Number of active tasks")
                .namespace("otlp")
                .subsystem("system"),
        ).unwrap();
        REGISTRY.register(Box::new(gauge.clone())).unwrap();
        gauge
    });
}

/// 初始化所有指标
pub fn init_metrics() {
    Lazy::force(&spans::CREATED_TOTAL);
    Lazy::force(&spans::EXPORTED_TOTAL);
    Lazy::force(&spans::EXPORT_ERRORS_TOTAL);
    Lazy::force(&spans::DURATION_SECONDS);
    
    Lazy::force(&exporter::BATCH_SIZE);
    Lazy::force(&exporter::EXPORT_LATENCY_SECONDS);
    Lazy::force(&exporter::QUEUE_SIZE);
    
    Lazy::force(&system::CPU_USAGE);
    Lazy::force(&system::MEMORY_USAGE_BYTES);
    Lazy::force(&system::TASKS_COUNT);
}
```

### 1.3 指标HTTP端点

`src/metrics_server.rs`:

```rust
use prometheus::{Encoder, TextEncoder};
use hyper::{
    Body, Request, Response, Server, StatusCode,
    service::{make_service_fn, service_fn},
};
use std::convert::Infallible;

/// 启动Prometheus metrics HTTP服务器
pub async fn serve_metrics(port: u16) -> Result<(), Box<dyn std::error::Error>> {
    let addr = ([0, 0, 0, 0], port).into();
    
    let make_svc = make_service_fn(|_conn| async {
        Ok::<_, Infallible>(service_fn(metrics_handler))
    });
    
    let server = Server::bind(&addr).serve(make_svc);
    
    println!("📊 Metrics server listening on http://{}", addr);
    
    server.await?;
    
    Ok(())
}

async fn metrics_handler(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let encoder = TextEncoder::new();
    let metric_families = crate::metrics::REGISTRY.gather();
    
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    
    let response = Response::builder()
        .status(StatusCode::OK)
        .header("Content-Type", encoder.format_type())
        .body(Body::from(buffer))
        .unwrap();
    
    Ok(response)
}
```

### 1.4 指标使用示例

```rust
use crate::metrics;

/// Span创建示例
pub fn create_span(service_name: &str, kind: SpanKind) {
    // 记录span创建
    metrics::spans::CREATED_TOTAL
        .with_label_values(&[service_name, kind.as_str()])
        .inc();
    
    // ... 创建span逻辑 ...
}

/// Span导出示例
pub async fn export_spans(spans: Vec<Span>) -> Result<(), ExportError> {
    let start = std::time::Instant::now();
    
    // 记录批次大小
    metrics::exporter::BATCH_SIZE.observe(spans.len() as f64);
    
    // 导出spans
    let result = do_export(spans).await;
    
    // 记录延迟
    let duration = start.elapsed().as_secs_f64();
    metrics::exporter::EXPORT_LATENCY_SECONDS
        .with_label_values(&["grpc", "otlp"])
        .observe(duration);
    
    match &result {
        Ok(_) => {
            metrics::spans::EXPORTED_TOTAL
                .with_label_values(&["grpc", "success"])
                .inc();
        }
        Err(e) => {
            metrics::spans::EXPORT_ERRORS_TOTAL
                .with_label_values(&["grpc", &e.error_type()])
                .inc();
        }
    }
    
    result
}

/// 系统资源监控
pub async fn monitor_system_resources() {
    use sysinfo::{System, SystemExt, ProcessExt};
    
    let mut sys = System::new_all();
    
    loop {
        sys.refresh_all();
        
        // CPU使用率
        let cpu_usage = sys.global_cpu_info().cpu_usage();
        metrics::system::CPU_USAGE.set(cpu_usage as f64);
        
        // 内存使用量
        let memory_used = sys.used_memory();
        metrics::system::MEMORY_USAGE_BYTES.set(memory_used as i64);
        
        // Task数量（简化）
        let task_count = tokio::runtime::Handle::current().metrics().num_workers();
        metrics::system::TASKS_COUNT.set(task_count as i64);
        
        tokio::time::sleep(tokio::time::Duration::from_secs(15)).await;
    }
}
```

---

## 2. Grafana Dashboard配置

### 2.1 完整Dashboard JSON

`grafana/dashboards/otlp-overview.json`:

```json
{
  "dashboard": {
    "title": "OTLP Service Overview",
    "tags": ["otlp", "observability", "rust"],
    "timezone": "browser",
    "schemaVersion": 38,
    "version": 1,
    "refresh": "30s",
    
    "panels": [
      {
        "id": 1,
        "title": "Span Creation Rate",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 0},
        "targets": [
          {
            "expr": "rate(otlp_spans_created_total[5m])",
            "legendFormat": "{{service_name}} - {{span_kind}}"
          }
        ],
        "yaxes": [
          {"format": "ops", "label": "Spans/sec"},
          {"format": "short"}
        ]
      },
      
      {
        "id": 2,
        "title": "Span Export Success Rate",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 0},
        "targets": [
          {
            "expr": "sum(rate(otlp_spans_exported_total{status=\"success\"}[5m])) / sum(rate(otlp_spans_exported_total[5m]))",
            "legendFormat": "Success Rate"
          }
        ],
        "yaxes": [
          {"format": "percentunit", "max": 1, "min": 0},
          {"format": "short"}
        ]
      },
      
      {
        "id": 3,
        "title": "Export Latency (P50, P95, P99)",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 8},
        "targets": [
          {
            "expr": "histogram_quantile(0.50, sum(rate(otlp_exporter_latency_seconds_bucket[5m])) by (le))",
            "legendFormat": "P50"
          },
          {
            "expr": "histogram_quantile(0.95, sum(rate(otlp_exporter_latency_seconds_bucket[5m])) by (le))",
            "legendFormat": "P95"
          },
          {
            "expr": "histogram_quantile(0.99, sum(rate(otlp_exporter_latency_seconds_bucket[5m])) by (le))",
            "legendFormat": "P99"
          }
        ],
        "yaxes": [
          {"format": "s", "label": "Latency"},
          {"format": "short"}
        ]
      },
      
      {
        "id": 4,
        "title": "Queue Size",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 8},
        "targets": [
          {
            "expr": "otlp_exporter_queue_size",
            "legendFormat": "{{exporter}}"
          }
        ],
        "yaxes": [
          {"format": "short", "label": "Queue Size"},
          {"format": "short"}
        ]
      },
      
      {
        "id": 5,
        "title": "CPU Usage",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 16},
        "targets": [
          {
            "expr": "otlp_system_cpu_usage_percent",
            "legendFormat": "CPU Usage"
          }
        ],
        "yaxes": [
          {"format": "percent", "max": 100, "min": 0},
          {"format": "short"}
        ]
      },
      
      {
        "id": 6,
        "title": "Memory Usage",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 16},
        "targets": [
          {
            "expr": "otlp_system_memory_usage_bytes",
            "legendFormat": "Memory Usage"
          }
        ],
        "yaxes": [
          {"format": "bytes", "label": "Memory"},
          {"format": "short"}
        ]
      },
      
      {
        "id": 7,
        "title": "Error Rate by Type",
        "type": "piechart",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 24},
        "targets": [
          {
            "expr": "sum(rate(otlp_spans_export_errors_total[5m])) by (error_type)",
            "legendFormat": "{{error_type}}"
          }
        ]
      },
      
      {
        "id": 8,
        "title": "Batch Size Distribution",
        "type": "heatmap",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 24},
        "targets": [
          {
            "expr": "sum(rate(otlp_exporter_batch_size_bucket[5m])) by (le)",
            "format": "heatmap"
          }
        ]
      }
    ]
  }
}
```

### 2.2 Grafana Provisioning

`grafana/provisioning/datasources/prometheus.yaml`:

```yaml
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
    version: 1
    editable: false
    jsonData:
      timeInterval: "30s"
      httpMethod: POST
```

`grafana/provisioning/dashboards/default.yaml`:

```yaml
apiVersion: 1

providers:
  - name: 'OTLP Dashboards'
    orgId: 1
    folder: 'OTLP'
    type: file
    disableDeletion: false
    updateIntervalSeconds: 30
    allowUiUpdates: true
    options:
      path: /etc/grafana/dashboards
      foldersFromFilesStructure: true
```

---

## 3. 告警规则配置

### 3.1 Prometheus告警规则

`prometheus/alerts/otlp-alerts.yaml`:

```yaml
groups:
  - name: otlp_service_alerts
    interval: 30s
    rules:
      # 高错误率告警
      - alert: HighExportErrorRate
        expr: |
          sum(rate(otlp_spans_export_errors_total[5m])) 
          / 
          sum(rate(otlp_spans_exported_total[5m])) 
          > 0.05
        for: 5m
        labels:
          severity: warning
          component: exporter
        annotations:
          summary: "High export error rate detected"
          description: "Export error rate is {{ $value | humanizePercentage }} (threshold: 5%)"
      
      # 导出延迟过高
      - alert: HighExportLatency
        expr: |
          histogram_quantile(0.95, 
            sum(rate(otlp_exporter_latency_seconds_bucket[5m])) by (le)
          ) > 1.0
        for: 5m
        labels:
          severity: warning
          component: exporter
        annotations:
          summary: "High export latency detected"
          description: "P95 export latency is {{ $value }}s (threshold: 1s)"
      
      # 队列积压告警
      - alert: ExporterQueueBacklog
        expr: otlp_exporter_queue_size > 10000
        for: 10m
        labels:
          severity: warning
          component: exporter
        annotations:
          summary: "Exporter queue backlog detected"
          description: "Queue size is {{ $value }} spans (threshold: 10000)"
      
      # 内存使用率过高
      - alert: HighMemoryUsage
        expr: |
          (otlp_system_memory_usage_bytes / 1024 / 1024 / 1024) > 3.5
        for: 5m
        labels:
          severity: warning
          component: system
        annotations:
          summary: "High memory usage detected"
          description: "Memory usage is {{ $value }}GB (threshold: 3.5GB)"
      
      # CPU使用率过高
      - alert: HighCPUUsage
        expr: otlp_system_cpu_usage_percent > 80
        for: 10m
        labels:
          severity: warning
          component: system
        annotations:
          summary: "High CPU usage detected"
          description: "CPU usage is {{ $value }}% (threshold: 80%)"
      
      # 服务不可用
      - alert: ServiceDown
        expr: up{job="otlp-service"} == 0
        for: 1m
        labels:
          severity: critical
          component: service
        annotations:
          summary: "OTLP service is down"
          description: "OTLP service {{$labels.instance}} has been down for more than 1 minute"
      
      # Span创建率异常低
      - alert: LowSpanCreationRate
        expr: |
          sum(rate(otlp_spans_created_total[5m])) < 100
        for: 10m
        labels:
          severity: info
          component: tracer
        annotations:
          summary: "Low span creation rate"
          description: "Span creation rate is {{ $value }} spans/sec (threshold: 100)"
      
      # 导出成功率过低（严重）
      - alert: CriticalExportFailureRate
        expr: |
          sum(rate(otlp_spans_exported_total{status="success"}[5m])) 
          / 
          sum(rate(otlp_spans_exported_total[5m])) 
          < 0.90
        for: 5m
        labels:
          severity: critical
          component: exporter
        annotations:
          summary: "Critical export failure rate"
          description: "Export success rate is {{ $value | humanizePercentage }} (threshold: 90%)"
```

### 3.2 Alertmanager配置

`alertmanager/config.yaml`:

```yaml
global:
  resolve_timeout: 5m
  slack_api_url: 'https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK'

route:
  group_by: ['alertname', 'cluster', 'service']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 12h
  receiver: 'default'
  
  routes:
    # 严重告警立即发送到Slack和PagerDuty
    - match:
        severity: critical
      receiver: 'critical-alerts'
      group_wait: 0s
      repeat_interval: 5m
    
    # 警告级别发送到Slack
    - match:
        severity: warning
      receiver: 'warning-alerts'
      repeat_interval: 1h
    
    # 信息级别只记录日志
    - match:
        severity: info
      receiver: 'info-alerts'
      repeat_interval: 24h

receivers:
  - name: 'default'
    slack_configs:
      - channel: '#alerts'
        title: '{{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'
  
  - name: 'critical-alerts'
    slack_configs:
      - channel: '#critical-alerts'
        title: '🚨 CRITICAL: {{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'
        send_resolved: true
    
    pagerduty_configs:
      - service_key: 'YOUR_PAGERDUTY_KEY'
        description: '{{ .GroupLabels.alertname }}'
  
  - name: 'warning-alerts'
    slack_configs:
      - channel: '#warnings'
        title: '⚠️  WARNING: {{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'
  
  - name: 'info-alerts'
    slack_configs:
      - channel: '#info'
        title: 'ℹ️  INFO: {{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'

inhibit_rules:
  # 如果服务已down，抑制其他告警
  - source_match:
      severity: 'critical'
      alertname: 'ServiceDown'
    target_match:
      severity: 'warning'
    equal: ['instance']
```

---

## 4. 完整监控方案

### 4.1 Docker Compose部署

`docker-compose.monitoring.yaml`:

```yaml
version: '3.9'

services:
  prometheus:
    image: prom/prometheus:v3.1.0
    container_name: prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/etc/prometheus/console_libraries'
      - '--web.console.templates=/etc/prometheus/consoles'
      - '--storage.tsdb.retention.time=30d'
      - '--web.enable-lifecycle'
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus/prometheus.yml:/etc/prometheus/prometheus.yml
      - ./prometheus/alerts:/etc/prometheus/alerts
      - prometheus-data:/prometheus
    networks:
      - monitoring
    restart: unless-stopped
  
  alertmanager:
    image: prom/alertmanager:v0.28.0
    container_name: alertmanager
    command:
      - '--config.file=/etc/alertmanager/config.yml'
      - '--storage.path=/alertmanager'
    ports:
      - "9093:9093"
    volumes:
      - ./alertmanager/config.yaml:/etc/alertmanager/config.yml
      - alertmanager-data:/alertmanager
    networks:
      - monitoring
    restart: unless-stopped
  
  grafana:
    image: grafana/grafana:11.6.0
    container_name: grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_USER=admin
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - ./grafana/provisioning:/etc/grafana/provisioning
      - ./grafana/dashboards:/etc/grafana/dashboards
      - grafana-data:/var/lib/grafana
    networks:
      - monitoring
    restart: unless-stopped
  
  node-exporter:
    image: prom/node-exporter:v1.8.2
    container_name: node-exporter
    command:
      - '--path.rootfs=/host'
    ports:
      - "9100:9100"
    volumes:
      - '/:/host:ro,rslave'
    networks:
      - monitoring
    restart: unless-stopped

networks:
  monitoring:
    driver: bridge

volumes:
  prometheus-data:
  alertmanager-data:
  grafana-data:
```

### 4.2 Prometheus配置

`prometheus/prometheus.yml`:

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'production'
    region: 'us-east-1'

alerting:
  alertmanagers:
    - static_configs:
        - targets: ['alertmanager:9093']

rule_files:
  - '/etc/prometheus/alerts/*.yaml'

scrape_configs:
  # OTLP Service
  - job_name: 'otlp-service'
    static_configs:
      - targets: ['otlp-service:9090']
    metric_relabel_configs:
      - source_labels: [__name__]
        regex: 'otlp_.*'
        action: keep
  
  # Node Exporter
  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node-exporter:9100']
  
  # Prometheus自监控
  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']
```

---

## 5. 生产最佳实践

### 5.1 指标命名规范

```text
命名规范:
<namespace>_<subsystem>_<metric_name>_<unit>

示例:
✅ otlp_spans_created_total           (Counter)
✅ otlp_exporter_latency_seconds      (Histogram)
✅ otlp_system_memory_usage_bytes     (Gauge)

❌ SpansCreated                       (不符合规范)
❌ export_time                        (缺少namespace)
```

### 5.2 标签使用最佳实践

```rust
// ✅ 好的标签设计：基数可控
metrics::spans::CREATED_TOTAL
    .with_label_values(&[
        "user-service",        // service_name: 有限数量
        "server",              // span_kind: 固定值
    ])
    .inc();

// ❌ 坏的标签设计：基数爆炸
// 不要用user_id、request_id等高基数值作为标签！
metrics::requests::TOTAL
    .with_label_values(&[
        &user_id,             // ❌ 高基数
        &request_id,          // ❌ 高基数
    ])
    .inc();
```

### 5.3 告警阈值设置

```yaml
# 基于历史数据设置合理阈值

# 错误率告警
- P95错误率 < 1%    → 正常
- P95错误率 1-5%    → warning
- P95错误率 > 5%    → critical

# 延迟告警
- P95延迟 < 100ms   → 正常
- P95延迟 100-500ms → warning
- P95延迟 > 500ms   → critical

# 资源使用告警
- CPU < 70%         → 正常
- CPU 70-85%        → warning
- CPU > 85%         → critical

- Memory < 75%      → 正常
- Memory 75-90%     → warning
- Memory > 90%      → critical
```

### 5.4 监控Dashboard层次

```text
层次1: 概览Dashboard
- 整体健康状态
- 关键指标趋势
- 告警概览

层次2: 服务Dashboard
- 服务级别详细指标
- 依赖关系
- 资源使用

层次3: 组件Dashboard
- 单个组件深度分析
- 性能瓶颈定位
- 调试信息

层次4: 实时Dashboard
- 实时监控
- 快速响应
- 故障排查
```

---

## 总结

完整的监控方案包括：

1. ✅ **指标导出** - Prometheus metrics集成
2. ✅ **可视化** - Grafana Dashboard配置
3. ✅ **告警** - Alertmanager规则配置
4. ✅ **部署** - Docker Compose完整方案
5. ✅ **最佳实践** - 生产环境经验总结

---

**文档日期**: 2025年10月8日  
**创建者**: AI Assistant  
**项目**: OTLP Rust 标准深度梳理  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [🐳 Kubernetes部署](../19_容器化与Kubernetes/01_Rust_OTLP_Kubernetes完整部署指南.md)
