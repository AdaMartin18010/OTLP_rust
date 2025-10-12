# Metrics完整实现：Prometheus指标系统与OTLP集成指南 (Rust 1.90)

## 目录

- [Metrics完整实现：Prometheus指标系统与OTLP集成指南 (Rust 1.90)](#metrics完整实现prometheus指标系统与otlp集成指南-rust-190)
  - [目录](#目录)
  - [一、Metrics核心概念](#一metrics核心概念)
    - [1.1 指标类型](#11-指标类型)
      - [**1. Counter（计数器）**](#1-counter计数器)
      - [**2. Gauge（仪表盘）**](#2-gauge仪表盘)
      - [**3. Histogram（直方图）**](#3-histogram直方图)
      - [**4. Summary（摘要）**](#4-summary摘要)
    - [1.2 指标命名规范](#12-指标命名规范)
    - [1.3 标签设计最佳实践](#13-标签设计最佳实践)
  - [二、Rust Metrics生态](#二rust-metrics生态)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目配置](#22-项目配置)
  - [三、Counter指标实现](#三counter指标实现)
    - [3.1 基础Counter](#31-基础counter)
    - [3.2 带标签的Counter](#32-带标签的counter)
    - [3.3 业务场景应用](#33-业务场景应用)
  - [四、Gauge指标实现](#四gauge指标实现)
    - [4.1 基础Gauge](#41-基础gauge)
    - [4.2 系统资源监控](#42-系统资源监控)
    - [4.3 业务状态监控](#43-业务状态监控)
  - [五、Histogram指标实现](#五histogram指标实现)
    - [5.1 基础Histogram](#51-基础histogram)
    - [5.2 自定义Bucket](#52-自定义bucket)
    - [5.3 请求延迟监控](#53-请求延迟监控)
  - [六、Summary指标实现](#六summary指标实现)
    - [6.1 基础Summary](#61-基础summary)
    - [6.2 分位数计算](#62-分位数计算)
  - [七、高级指标模式](#七高级指标模式)
    - [7.1 复合指标](#71-复合指标)
    - [7.2 动态标签](#72-动态标签)
    - [7.3 指标聚合](#73-指标聚合)
  - [八、Prometheus导出器](#八prometheus导出器)
    - [8.1 HTTP端点实现](#81-http端点实现)
    - [8.2 与Axum集成](#82-与axum集成)
  - [九、OpenTelemetry Metrics集成](#九opentelemetry-metrics集成)
    - [9.1 OTLP Exporter配置](#91-otlp-exporter配置)
    - [9.2 多后端导出](#92-多后端导出)
    - [9.3 指标与追踪关联](#93-指标与追踪关联)
  - [十、性能优化](#十性能优化)
    - [10.1 零成本抽象验证](#101-零成本抽象验证)
    - [10.2 标签基数控制](#102-标签基数控制)
    - [10.3 批量导出优化](#103-批量导出优化)
  - [十一、生产级实践](#十一生产级实践)
    - [11.1 完整监控系统](#111-完整监控系统)
    - [11.2 告警规则设计](#112-告警规则设计)
    - [11.3 Grafana仪表盘](#113-grafana仪表盘)
  - [十二、Docker Compose部署](#十二docker-compose部署)
  - [十三、参考资源](#十三参考资源)
    - [官方文档](#官方文档)
    - [国际标准](#国际标准)
    - [Rust生态](#rust生态)
    - [博客和教程](#博客和教程)
  - [总结](#总结)

---

## 一、Metrics核心概念

### 1.1 指标类型

Prometheus定义了4种核心指标类型，每种类型适用于不同的监控场景：

#### **1. Counter（计数器）**

- **特性**：只能递增，重启后归零
- **场景**：请求总数、错误次数、订单总量
- **查询示例**：`rate(http_requests_total[5m])`

#### **2. Gauge（仪表盘）**

- **特性**：可增可减，表示瞬时值
- **场景**：CPU使用率、内存占用、活跃连接数
- **查询示例**：`avg_over_time(memory_usage_bytes[5m])`

#### **3. Histogram（直方图）**

- **特性**：自动生成`_bucket`、`_sum`、`_count`指标
- **场景**：请求延迟、响应大小分布
- **查询示例**：`histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))`

#### **4. Summary（摘要）**

- **特性**：客户端计算分位数
- **场景**：精确分位数计算（但无法聚合）
- **查询示例**：`http_request_duration_seconds{quantile="0.99"}`

**选择建议**：

- 优先使用Histogram（支持服务端聚合）
- Summary仅用于单实例精确分位数

### 1.2 指标命名规范

遵循Prometheus官方命名约定：

```rust
// ✅ 正确命名
http_requests_total              // Counter，使用_total后缀
http_request_duration_seconds    // Histogram，使用基本单位（seconds）
process_cpu_usage_ratio          // Gauge，使用_ratio后缀
database_connections_active      // Gauge，明确表示活跃状态

// ❌ 错误命名
httpRequestsCount                // 驼峰命名
http_requests_ms                 // 非基本单位
request_duration                 // 缺少单位
```

**核心规则**：

1. 使用snake_case
2. 包含单位（seconds、bytes、ratio）
3. Counter使用`_total`后缀
4. 避免动词前缀（如`get_`、`process_`）

### 1.3 标签设计最佳实践

标签用于多维度数据分割，但需谨慎设计：

```rust
// ✅ 优秀标签设计
http_requests_total{
    method="GET",           // 枚举值（有限）
    status="200",           // 枚举值（有限）
    endpoint="/api/users"   // 低基数（有限路由）
}

// ❌ 糟糕标签设计
http_requests_total{
    user_id="12345",       // 高基数（百万级用户）
    request_id="uuid",     // 极高基数（每次请求唯一）
    timestamp="1234567890" // 连续值
}
```

**设计原则**：

1. 标签基数保持在数百以内
2. 避免用户ID、请求ID等高基数数据
3. 对长URL进行路径模板化（`/users/:id` 而非 `/users/123`）
4. 标签值应为枚举类型

---

## 二、Rust Metrics生态

### 2.1 核心依赖

```toml
[dependencies]
# Metrics核心
metrics = "0.23"                       # 零成本指标抽象层
metrics-exporter-prometheus = "0.15"   # Prometheus导出器

# OpenTelemetry集成
opentelemetry = { version = "0.31", features = ["metrics"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "metrics"] }
opentelemetry-otlp = { version = "0.31", features = ["metrics", "grpc-tonic"] }
opentelemetry-prometheus = "0.31"      # Prometheus桥接器

# Web框架
axum = "0.7"
tokio = { version = "1.42", features = ["full"] }

# 系统监控
sysinfo = "0.32"                       # CPU、内存、磁盘监控

# 序列化
serde = { version = "1.0", features = ["derive"] }

[dev-dependencies]
criterion = "0.6"                       # 性能基准测试
```

### 2.2 项目配置

创建基础项目结构：

```bash
mkdir -p metrics-demo/src/{counter,gauge,histogram,exporters}
cd metrics-demo
cargo init
```

---

## 三、Counter指标实现

### 3.1 基础Counter

Counter用于单调递增的计数场景：

```rust
// src/counter/basic.rs
use metrics::{counter, describe_counter};

/// 初始化Counter指标描述
pub fn init_counters() {
    describe_counter!(
        "http_requests_total",
        metrics::Unit::Count,
        "Total HTTP requests received"
    );
    
    describe_counter!(
        "http_errors_total",
        metrics::Unit::Count,
        "Total HTTP errors"
    );
}

/// 记录HTTP请求
pub fn record_http_request() {
    counter!("http_requests_total").increment(1);
}

/// 记录HTTP错误
pub fn record_http_error() {
    counter!("http_errors_total").increment(1);
}

#[cfg(test)]
mod tests {
    use super::*;
    use metrics_exporter_prometheus::PrometheusBuilder;

    #[test]
    fn test_counter_increment() {
        // 初始化Prometheus导出器
        let recorder = PrometheusBuilder::new().build_recorder();
        metrics::set_global_recorder(recorder).unwrap();

        init_counters();

        // 记录10次请求
        for _ in 0..10 {
            record_http_request();
        }

        // 验证计数（实际生产中通过Prometheus查询）
        record_http_error();
    }
}
```

### 3.2 带标签的Counter

多维度计数，支持按方法、状态码、端点分组：

```rust
// src/counter/labeled.rs
use metrics::counter;

/// HTTP请求标签
#[derive(Debug, Clone)]
pub struct HttpLabels {
    pub method: String,
    pub status: u16,
    pub endpoint: String,
}

impl HttpLabels {
    pub fn new(method: &str, status: u16, endpoint: &str) -> Self {
        Self {
            method: method.to_string(),
            status,
            endpoint: Self::normalize_endpoint(endpoint),
        }
    }

    /// 路径模板化，避免高基数
    fn normalize_endpoint(path: &str) -> String {
        // 将 /users/123 -> /users/:id
        let segments: Vec<&str> = path.split('/').collect();
        segments
            .iter()
            .map(|&s| {
                if s.chars().all(char::is_numeric) {
                    ":id"
                } else {
                    s
                }
            })
            .collect::<Vec<_>>()
            .join("/")
    }
}

/// 记录带标签的HTTP请求
pub fn record_http_request_with_labels(labels: &HttpLabels) {
    counter!(
        "http_requests_total",
        "method" => labels.method.clone(),
        "status" => labels.status.to_string(),
        "endpoint" => labels.endpoint.clone()
    )
    .increment(1);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_endpoint_normalization() {
        let labels = HttpLabels::new("GET", 200, "/users/12345/orders/67890");
        assert_eq!(labels.endpoint, "/users/:id/orders/:id");
    }

    #[test]
    fn test_labeled_counter() {
        let labels = HttpLabels::new("POST", 201, "/api/orders");
        record_http_request_with_labels(&labels);

        let labels2 = HttpLabels::new("GET", 404, "/api/users/999");
        record_http_request_with_labels(&labels2);
    }
}
```

### 3.3 业务场景应用

构建真实电商订单计数系统：

```rust
// src/counter/business.rs
use metrics::{counter, describe_counter, Unit};
use std::sync::Arc;

/// 订单事件类型
#[derive(Debug, Clone, Copy)]
pub enum OrderEvent {
    Created,
    Paid,
    Shipped,
    Delivered,
    Cancelled,
}

impl OrderEvent {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Created => "created",
            Self::Paid => "paid",
            Self::Shipped => "shipped",
            Self::Delivered => "delivered",
            Self::Cancelled => "cancelled",
        }
    }
}

/// 订单指标系统
pub struct OrderMetrics;

impl OrderMetrics {
    /// 初始化所有订单指标
    pub fn init() {
        describe_counter!(
            "orders_total",
            Unit::Count,
            "Total orders by status"
        );

        describe_counter!(
            "order_revenue_total",
            Unit::Count,
            "Total order revenue in cents"
        );

        describe_counter!(
            "order_items_total",
            Unit::Count,
            "Total order items sold"
        );
    }

    /// 记录订单事件
    pub fn record_order_event(event: OrderEvent, payment_method: &str) {
        counter!(
            "orders_total",
            "status" => event.as_str(),
            "payment_method" => payment_method.to_string()
        )
        .increment(1);
    }

    /// 记录订单收入（以分为单位）
    pub fn record_order_revenue(amount_cents: u64, currency: &str) {
        counter!(
            "order_revenue_total",
            "currency" => currency.to_string()
        )
        .increment(amount_cents);
    }

    /// 记录订单商品数量
    pub fn record_order_items(count: u64, category: &str) {
        counter!(
            "order_items_total",
            "category" => category.to_string()
        )
        .increment(count);
    }
}

/// 模拟订单处理
pub async fn process_order(
    order_id: &str,
    amount_cents: u64,
    items: Vec<(&str, u64)>,
) {
    tracing::info!(%order_id, "Processing order");

    // 1. 创建订单
    OrderMetrics::record_order_event(OrderEvent::Created, "credit_card");

    // 2. 记录收入
    OrderMetrics::record_order_revenue(amount_cents, "USD");

    // 3. 记录商品
    for (category, count) in items {
        OrderMetrics::record_order_items(count, category);
    }

    // 4. 支付成功
    OrderMetrics::record_order_event(OrderEvent::Paid, "credit_card");

    tracing::info!(%order_id, "Order completed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_order_metrics() {
        OrderMetrics::init();

        // 模拟订单
        process_order(
            "ORD-001",
            99_99,
            vec![("electronics", 1), ("books", 3)],
        )
        .await;

        process_order("ORD-002", 49_99, vec![("clothing", 2)]).await;

        // 验证指标（生产环境通过Prometheus查询）
        // rate(orders_total{status="paid"}[5m])
        // sum(rate(order_revenue_total[5m]))
    }
}
```

**生产查询示例**：

```promql
# 每秒订单创建速率
rate(orders_total{status="created"}[5m])

# 支付成功率
rate(orders_total{status="paid"}[5m]) 
  / 
rate(orders_total{status="created"}[5m])

# 每秒收入（美元）
rate(order_revenue_total{currency="USD"}[5m]) / 100

# 热销商品类别
topk(5, sum by (category) (rate(order_items_total[1h])))
```

---

## 四、Gauge指标实现

### 4.1 基础Gauge

Gauge用于可增可减的瞬时值监控：

```rust
// src/gauge/basic.rs
use metrics::{gauge, describe_gauge, Unit};

pub fn init_gauges() {
    describe_gauge!(
        "system_memory_usage_bytes",
        Unit::Bytes,
        "System memory usage"
    );

    describe_gauge!(
        "active_connections",
        Unit::Count,
        "Active database connections"
    );

    describe_gauge!(
        "cache_hit_ratio",
        Unit::Count,
        "Cache hit ratio (0-1)"
    );
}

/// 更新内存使用量
pub fn update_memory_usage(bytes: u64) {
    gauge!("system_memory_usage_bytes").set(bytes as f64);
}

/// 增加活跃连接
pub fn increment_active_connections(delta: i64) {
    gauge!("active_connections").increment(delta as f64);
}

/// 减少活跃连接
pub fn decrement_active_connections(delta: i64) {
    gauge!("active_connections").decrement(delta as f64);
}

/// 更新缓存命中率
pub fn update_cache_hit_ratio(ratio: f64) {
    gauge!("cache_hit_ratio").set(ratio);
}
```

### 4.2 系统资源监控

使用`sysinfo`库监控系统资源：

```rust
// src/gauge/system.rs
use metrics::{gauge, describe_gauge, Unit};
use sysinfo::{System, Disks};
use std::time::Duration;
use tokio::time;

pub struct SystemMonitor {
    sys: System,
    disks: Disks,
}

impl SystemMonitor {
    pub fn new() -> Self {
        describe_gauge!("system_cpu_usage_ratio", Unit::Count, "CPU usage ratio");
        describe_gauge!("system_memory_used_bytes", Unit::Bytes, "Used memory");
        describe_gauge!("system_memory_total_bytes", Unit::Bytes, "Total memory");
        describe_gauge!("system_disk_used_bytes", Unit::Bytes, "Disk used space");
        describe_gauge!("system_disk_total_bytes", Unit::Bytes, "Disk total space");

        Self {
            sys: System::new_all(),
            disks: Disks::new_with_refreshed_list(),
        }
    }

    /// 启动后台监控任务
    pub async fn start(mut self, interval: Duration) {
        let mut ticker = time::interval(interval);

        loop {
            ticker.tick().await;
            self.collect_metrics();
        }
    }

    fn collect_metrics(&mut self) {
        // 刷新系统信息
        self.sys.refresh_all();

        // CPU使用率
        let cpu_usage = self.sys.global_cpu_info().cpu_usage() / 100.0;
        gauge!("system_cpu_usage_ratio").set(cpu_usage as f64);

        // 内存
        let used_memory = self.sys.used_memory();
        let total_memory = self.sys.total_memory();
        gauge!("system_memory_used_bytes").set(used_memory as f64);
        gauge!("system_memory_total_bytes").set(total_memory as f64);

        // 磁盘
        self.disks.refresh();
        for disk in self.disks.list() {
            let mount_point = disk.mount_point().to_string_lossy().to_string();
            let available = disk.available_space();
            let total = disk.total_space();
            let used = total - available;

            gauge!(
                "system_disk_used_bytes",
                "mount_point" => mount_point.clone()
            )
            .set(used as f64);

            gauge!(
                "system_disk_total_bytes",
                "mount_point" => mount_point
            )
            .set(total as f64);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_system_monitor() {
        let monitor = SystemMonitor::new();

        // 运行5秒
        tokio::select! {
            _ = monitor.start(Duration::from_secs(1)) => {},
            _ = tokio::time::sleep(Duration::from_secs(5)) => {
                println!("Monitoring completed");
            }
        }
    }
}
```

### 4.3 业务状态监控

监控连接池、队列长度等业务状态：

```rust
// src/gauge/business.rs
use metrics::{gauge, describe_gauge, Unit};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// 连接池指标
pub struct ConnectionPoolMetrics {
    active: Arc<AtomicU64>,
    idle: Arc<AtomicU64>,
}

impl ConnectionPoolMetrics {
    pub fn new(pool_name: &str) -> Self {
        describe_gauge!(
            "db_pool_connections_active",
            Unit::Count,
            "Active database connections"
        );

        describe_gauge!(
            "db_pool_connections_idle",
            Unit::Count,
            "Idle database connections"
        );

        let metrics = Self {
            active: Arc::new(AtomicU64::new(0)),
            idle: Arc::new(AtomicU64::new(0)),
        };

        // 启动后台报告任务
        let active_clone = metrics.active.clone();
        let idle_clone = metrics.idle.clone();
        let pool_name_clone = pool_name.to_string();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));
            loop {
                interval.tick().await;

                let active_count = active_clone.load(Ordering::Relaxed);
                let idle_count = idle_clone.load(Ordering::Relaxed);

                gauge!(
                    "db_pool_connections_active",
                    "pool" => pool_name_clone.clone()
                )
                .set(active_count as f64);

                gauge!(
                    "db_pool_connections_idle",
                    "pool" => pool_name_clone.clone()
                )
                .set(idle_count as f64);
            }
        });

        metrics
    }

    pub fn acquire_connection(&self) {
        self.idle.fetch_sub(1, Ordering::Relaxed);
        self.active.fetch_add(1, Ordering::Relaxed);
    }

    pub fn release_connection(&self) {
        self.active.fetch_sub(1, Ordering::Relaxed);
        self.idle.fetch_add(1, Ordering::Relaxed);
    }

    pub fn add_connection(&self) {
        self.idle.fetch_add(1, Ordering::Relaxed);
    }
}

/// 队列深度监控
pub struct QueueMetrics {
    depth: Arc<AtomicU64>,
}

impl QueueMetrics {
    pub fn new(queue_name: &str) -> Self {
        describe_gauge!("queue_depth", Unit::Count, "Queue depth");

        let metrics = Self {
            depth: Arc::new(AtomicU64::new(0)),
        };

        let depth_clone = metrics.depth.clone();
        let queue_name_clone = queue_name.to_string();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));
            loop {
                interval.tick().await;

                let depth = depth_clone.load(Ordering::Relaxed);
                gauge!("queue_depth", "queue" => queue_name_clone.clone())
                    .set(depth as f64);
            }
        });

        metrics
    }

    pub fn enqueue(&self) {
        self.depth.fetch_add(1, Ordering::Relaxed);
    }

    pub fn dequeue(&self) {
        self.depth.fetch_sub(1, Ordering::Relaxed);
    }
}
```

---

## 五、Histogram指标实现

### 5.1 基础Histogram

Histogram用于延迟、大小等分布统计：

```rust
// src/histogram/basic.rs
use metrics::{histogram, describe_histogram, Unit};
use std::time::Instant;

pub fn init_histograms() {
    describe_histogram!(
        "http_request_duration_seconds",
        Unit::Seconds,
        "HTTP request duration"
    );

    describe_histogram!(
        "http_response_size_bytes",
        Unit::Bytes,
        "HTTP response size"
    );
}

/// 记录请求延迟
pub fn record_request_duration(duration_secs: f64, method: &str, endpoint: &str) {
    histogram!(
        "http_request_duration_seconds",
        "method" => method.to_string(),
        "endpoint" => endpoint.to_string()
    )
    .record(duration_secs);
}

/// 记录响应大小
pub fn record_response_size(size_bytes: u64, content_type: &str) {
    histogram!(
        "http_response_size_bytes",
        "content_type" => content_type.to_string()
    )
    .record(size_bytes as f64);
}

/// 自动计时器
pub struct Timer {
    start: Instant,
    metric_name: String,
    labels: Vec<(String, String)>,
}

impl Timer {
    pub fn new(metric_name: &str) -> Self {
        Self {
            start: Instant::now(),
            metric_name: metric_name.to_string(),
            labels: Vec::new(),
        }
    }

    pub fn with_label(mut self, key: &str, value: &str) -> Self {
        self.labels.push((key.to_string(), value.to_string()));
        self
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        let duration = self.start.elapsed().as_secs_f64();

        let mut hist = histogram!(&self.metric_name);
        for (k, v) in &self.labels {
            hist = hist.with_label(k, v.clone());
        }
        hist.record(duration);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_timer() {
        init_histograms();

        {
            let _timer = Timer::new("http_request_duration_seconds")
                .with_label("method", "GET")
                .with_label("endpoint", "/api/users");

            // 模拟业务逻辑
            tokio::time::sleep(Duration::from_millis(100)).await;
        } // Timer自动记录

        record_response_size(2048, "application/json");
    }
}
```

### 5.2 自定义Bucket

为不同场景定制Bucket分布：

```rust
// src/histogram/custom_buckets.rs
use metrics::{histogram, describe_histogram, Unit};
use metrics_exporter_prometheus::PrometheusBuilder;

/// 初始化自定义Bucket的Histogram
pub fn init_custom_histograms() {
    // API延迟：0.001s ~ 10s
    let api_buckets = [
        0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0,
    ];

    // 数据库查询：0.0001s ~ 1s
    let db_buckets = [
        0.0001, 0.0005, 0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0,
    ];

    // 批处理时间：1s ~ 1h
    let batch_buckets = [
        1.0, 5.0, 10.0, 30.0, 60.0, 300.0, 600.0, 1800.0, 3600.0,
    ];

    describe_histogram!(
        "api_request_duration_seconds",
        Unit::Seconds,
        "API request duration with custom buckets"
    );

    describe_histogram!(
        "db_query_duration_seconds",
        Unit::Seconds,
        "Database query duration with custom buckets"
    );

    describe_histogram!(
        "batch_processing_duration_seconds",
        Unit::Seconds,
        "Batch processing duration with custom buckets"
    );

    // 在PrometheusBuilder中设置（见后续导出器部分）
}

/// 记录API延迟
pub fn record_api_duration(duration_secs: f64, endpoint: &str) {
    histogram!(
        "api_request_duration_seconds",
        "endpoint" => endpoint.to_string()
    )
    .record(duration_secs);
}

/// 记录数据库查询延迟
pub fn record_db_query_duration(duration_secs: f64, query_type: &str) {
    histogram!(
        "db_query_duration_seconds",
        "query_type" => query_type.to_string()
    )
    .record(duration_secs);
}

/// 记录批处理时间
pub fn record_batch_duration(duration_secs: f64, job_name: &str) {
    histogram!(
        "batch_processing_duration_seconds",
        "job" => job_name.to_string()
    )
    .record(duration_secs);
}
```

### 5.3 请求延迟监控

完整的HTTP请求延迟监控系统：

```rust
// src/histogram/request_latency.rs
use metrics::{histogram, describe_histogram, Unit};
use std::time::Instant;

pub struct RequestLatencyTracker;

impl RequestLatencyTracker {
    pub fn init() {
        describe_histogram!(
            "http_request_duration_seconds",
            Unit::Seconds,
            "HTTP request duration by method, endpoint, and status"
        );
    }

    /// 跟踪请求延迟
    pub fn track<F, T>(method: &str, endpoint: &str, f: F) -> (T, u16)
    where
        F: FnOnce() -> (T, u16),
    {
        let start = Instant::now();
        let (result, status) = f();
        let duration = start.elapsed().as_secs_f64();

        histogram!(
            "http_request_duration_seconds",
            "method" => method.to_string(),
            "endpoint" => endpoint.to_string(),
            "status" => status.to_string()
        )
        .record(duration);

        (result, status)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_latency_tracking() {
        RequestLatencyTracker::init();

        let (response, status) = RequestLatencyTracker::track("GET", "/api/users", || {
            std::thread::sleep(Duration::from_millis(50));
            ("user_data".to_string(), 200)
        });

        assert_eq!(status, 200);
        assert_eq!(response, "user_data");
    }
}
```

**Prometheus查询示例**：

```promql
# P50延迟
histogram_quantile(0.5, rate(http_request_duration_seconds_bucket[5m]))

# P95延迟（按端点）
histogram_quantile(0.95, 
  sum by (endpoint, le) (rate(http_request_duration_seconds_bucket[5m]))
)

# P99延迟（按方法）
histogram_quantile(0.99, 
  sum by (method, le) (rate(http_request_duration_seconds_bucket[5m]))
)

# 平均延迟
rate(http_request_duration_seconds_sum[5m]) 
  / 
rate(http_request_duration_seconds_count[5m])
```

---

## 六、Summary指标实现

### 6.1 基础Summary

Summary在客户端计算分位数（不推荐，因为无法聚合）：

```rust
// src/summary/basic.rs
use metrics::{histogram, describe_histogram, Unit};

pub fn init_summaries() {
    describe_histogram!(
        "payment_processing_duration_seconds",
        Unit::Seconds,
        "Payment processing duration (summary)"
    );
}

/// 记录支付处理时间
pub fn record_payment_duration(duration_secs: f64, provider: &str) {
    // metrics库使用histogram统一处理
    histogram!(
        "payment_processing_duration_seconds",
        "provider" => provider.to_string()
    )
    .record(duration_secs);
}
```

**注意**：

- Rust的`metrics`库统一使用`histogram!`宏
- 在Prometheus导出器配置中可选择生成Summary格式
- 优先使用Histogram（支持服务端聚合）

### 6.2 分位数计算

如果必须使用Summary，建议在Prometheus中计算：

```promql
# Histogram方式（推荐）
histogram_quantile(0.95, rate(payment_processing_duration_seconds_bucket[5m]))

# Summary方式（不推荐，无法跨实例聚合）
payment_processing_duration_seconds{quantile="0.95"}
```

---

## 七、高级指标模式

### 7.1 复合指标

结合多个指标计算派生指标：

```rust
// src/advanced/composite.rs
use metrics::{counter, histogram, gauge};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// 缓存指标系统
pub struct CacheMetrics {
    hits: Arc<AtomicU64>,
    misses: Arc<AtomicU64>,
}

impl CacheMetrics {
    pub fn new() -> Self {
        Self {
            hits: Arc::new(AtomicU64::new(0)),
            misses: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn record_hit(&self) {
        self.hits.fetch_add(1, Ordering::Relaxed);
        counter!("cache_hits_total").increment(1);
    }

    pub fn record_miss(&self) {
        self.misses.fetch_add(1, Ordering::Relaxed);
        counter!("cache_misses_total").increment(1);
    }

    /// 计算并更新命中率
    pub fn update_hit_ratio(&self) {
        let hits = self.hits.load(Ordering::Relaxed);
        let misses = self.misses.load(Ordering::Relaxed);
        let total = hits + misses;

        if total > 0 {
            let ratio = hits as f64 / total as f64;
            gauge!("cache_hit_ratio").set(ratio);
        }
    }

    /// 启动定期更新
    pub fn start_periodic_update(self: Arc<Self>) {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(10));
            loop {
                interval.tick().await;
                self.update_hit_ratio();
            }
        });
    }
}
```

**Prometheus查询**：

```promql
# 实时命中率
rate(cache_hits_total[5m]) 
  / 
(rate(cache_hits_total[5m]) + rate(cache_misses_total[5m]))
```

### 7.2 动态标签

运行时生成标签：

```rust
// src/advanced/dynamic_labels.rs
use metrics::counter;
use std::collections::HashMap;

pub fn record_event_with_dynamic_labels(
    event_type: &str,
    attributes: HashMap<String, String>,
) {
    let mut metric = counter!("business_events_total", "type" => event_type.to_string());

    // 动态添加标签（注意基数控制）
    for (key, value) in attributes {
        metric = metric.with_label(&key, value);
    }

    metric.increment(1);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dynamic_labels() {
        let mut attrs = HashMap::new();
        attrs.insert("region".to_string(), "us-west".to_string());
        attrs.insert("tier".to_string(), "premium".to_string());

        record_event_with_dynamic_labels("user_signup", attrs);
    }
}
```

### 7.3 指标聚合

在应用层聚合后再导出：

```rust
// src/advanced/aggregation.rs
use metrics::gauge;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// 区域级别的聚合指标
pub struct RegionalMetrics {
    data: Arc<RwLock<HashMap<String, u64>>>,
}

impl RegionalMetrics {
    pub fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub fn increment_region(&self, region: &str, value: u64) {
        let mut data = self.data.write().unwrap();
        *data.entry(region.to_string()).or_insert(0) += value;
    }

    /// 导出聚合指标
    pub fn export(&self) {
        let data = self.data.read().unwrap();
        for (region, count) in data.iter() {
            gauge!("regional_request_count", "region" => region.clone())
                .set(*count as f64);
        }
    }

    pub fn start_periodic_export(self: Arc<Self>) {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(60));
            loop {
                interval.tick().await;
                self.export();
            }
        });
    }
}
```

---

## 八、Prometheus导出器

### 8.1 HTTP端点实现

创建`/metrics`端点：

```rust
// src/exporters/prometheus_exporter.rs
use axum::{
    response::IntoResponse,
    routing::get,
    Router,
};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};
use std::net::SocketAddr;

/// 初始化Prometheus导出器
pub fn init_prometheus_exporter() -> PrometheusHandle {
    PrometheusBuilder::new()
        .set_buckets_for_metric(
            metrics_exporter_prometheus::Matcher::Suffix("duration_seconds".to_string()),
            &[0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0],
        )
        .unwrap()
        .set_buckets_for_metric(
            metrics_exporter_prometheus::Matcher::Suffix("size_bytes".to_string()),
            &[100.0, 1_000.0, 10_000.0, 100_000.0, 1_000_000.0, 10_000_000.0],
        )
        .unwrap()
        .install_recorder()
        .unwrap()
}

/// Metrics端点处理器
async fn metrics_handler(handle: axum::extract::State<PrometheusHandle>) -> impl IntoResponse {
    handle.render()
}

/// 启动Prometheus导出服务
pub async fn start_metrics_server(handle: PrometheusHandle, addr: SocketAddr) {
    let app = Router::new()
        .route("/metrics", get(metrics_handler))
        .with_state(handle);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    tracing::info!("Metrics server listening on {}", addr);

    axum::serve(listener, app).await.unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metrics_endpoint() {
        let handle = init_prometheus_exporter();

        // 记录一些指标
        metrics::counter!("test_counter").increment(1);
        metrics::gauge!("test_gauge").set(42.0);

        // 验证导出内容
        let output = handle.render();
        assert!(output.contains("test_counter"));
        assert!(output.contains("test_gauge"));
    }
}
```

### 8.2 与Axum集成

完整的Axum应用集成：

```rust
// src/exporters/axum_integration.rs
use axum::{
    extract::State,
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use metrics::{counter, histogram};
use metrics_exporter_prometheus::PrometheusHandle;
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::time::Instant;

#[derive(Debug, Serialize, Deserialize)]
struct CreateUserRequest {
    username: String,
    email: String,
}

#[derive(Debug, Serialize)]
struct CreateUserResponse {
    id: u64,
    username: String,
}

/// 创建用户处理器
async fn create_user(
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<CreateUserResponse>, StatusCode> {
    let start = Instant::now();

    counter!("http_requests_total", "method" => "POST", "endpoint" => "/api/users").increment(1);

    // 模拟业务逻辑
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;

    let response = CreateUserResponse {
        id: 1,
        username: payload.username,
    };

    let duration = start.elapsed().as_secs_f64();
    histogram!(
        "http_request_duration_seconds",
        "method" => "POST",
        "endpoint" => "/api/users",
        "status" => "201"
    )
    .record(duration);

    counter!("users_created_total").increment(1);

    Ok(Json(response))
}

/// 获取用户列表
async fn list_users() -> impl IntoResponse {
    let start = Instant::now();

    counter!("http_requests_total", "method" => "GET", "endpoint" => "/api/users").increment(1);

    tokio::time::sleep(std::time::Duration::from_millis(20)).await;

    let duration = start.elapsed().as_secs_f64();
    histogram!(
        "http_request_duration_seconds",
        "method" => "GET",
        "endpoint" => "/api/users",
        "status" => "200"
    )
    .record(duration);

    Json(vec!["user1", "user2"])
}

/// 启动应用服务器
pub async fn start_app_server(metrics_handle: PrometheusHandle, addr: SocketAddr) {
    let app = Router::new()
        .route("/api/users", post(create_user).get(list_users))
        .route(
            "/metrics",
            get(|| async move { metrics_handle.render() }),
        );

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    tracing::info!("App server listening on {}", addr);

    axum::serve(listener, app).await.unwrap();
}
```

---

## 九、OpenTelemetry Metrics集成

### 9.1 OTLP Exporter配置

配置OTLP导出器，将指标发送到Jaeger/Prometheus：

```rust
// src/otel/metrics_exporter.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    runtime, Resource,
};
use std::time::Duration;

/// 初始化OTLP Metrics导出器
pub fn init_otlp_metrics(service_name: &str, otlp_endpoint: &str) -> SdkMeterProvider {
    let exporter = opentelemetry_otlp::MetricsExporter::builder()
        .with_tonic()
        .with_endpoint(otlp_endpoint)
        .with_timeout(Duration::from_secs(3))
        .build()
        .expect("Failed to create OTLP metrics exporter");

    let reader = PeriodicReader::builder(exporter, runtime::Tokio)
        .with_interval(Duration::from_secs(10)) // 每10秒导出一次
        .build();

    let provider = SdkMeterProvider::builder()
        .with_reader(reader)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", service_name.to_string()),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        ]))
        .build();

    global::set_meter_provider(provider.clone());

    provider
}

/// 创建指标
pub fn create_otel_metrics() {
    let meter = global::meter("example-meter");

    // Counter
    let request_counter = meter
        .u64_counter("otel_http_requests_total")
        .with_description("Total HTTP requests")
        .build();

    request_counter.add(1, &[KeyValue::new("method", "GET")]);

    // Histogram
    let request_duration = meter
        .f64_histogram("otel_http_request_duration_seconds")
        .with_description("HTTP request duration")
        .with_unit("s")
        .build();

    request_duration.record(0.123, &[KeyValue::new("endpoint", "/api/users")]);

    // Gauge (通过Observable Gauge)
    let _cpu_gauge = meter
        .f64_observable_gauge("otel_system_cpu_usage")
        .with_description("CPU usage ratio")
        .with_callback(|observer| {
            // 这里应该获取真实CPU数据
            observer.observe(0.45, &[]);
        })
        .build();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_otlp_metrics() {
        let _provider = init_otlp_metrics("test-service", "http://localhost:4317");

        create_otel_metrics();

        // 等待导出
        tokio::time::sleep(Duration::from_secs(15)).await;
    }
}
```

### 9.2 多后端导出

同时导出到Prometheus和OTLP：

```rust
// src/otel/multi_backend.rs
use metrics_exporter_prometheus::PrometheusHandle;
use opentelemetry_sdk::metrics::SdkMeterProvider;

pub struct MetricsBackend {
    pub prometheus_handle: PrometheusHandle,
    pub otlp_provider: SdkMeterProvider,
}

impl MetricsBackend {
    pub fn init(service_name: &str, otlp_endpoint: &str) -> Self {
        // 1. Prometheus导出器（用于本地抓取）
        let prometheus_handle = crate::exporters::prometheus_exporter::init_prometheus_exporter();

        // 2. OTLP导出器（用于发送到远程后端）
        let otlp_provider = crate::otel::metrics_exporter::init_otlp_metrics(
            service_name,
            otlp_endpoint,
        );

        Self {
            prometheus_handle,
            otlp_provider,
        }
    }

    /// 记录指标（同时写入两个后端）
    pub fn record_request(&self, method: &str, endpoint: &str, duration_secs: f64) {
        // Prometheus方式
        metrics::counter!(
            "http_requests_total",
            "method" => method.to_string(),
            "endpoint" => endpoint.to_string()
        )
        .increment(1);

        metrics::histogram!(
            "http_request_duration_seconds",
            "method" => method.to_string(),
            "endpoint" => endpoint.to_string()
        )
        .record(duration_secs);

        // OpenTelemetry方式
        let meter = opentelemetry::global::meter("multi-backend");

        let counter = meter
            .u64_counter("otel_http_requests_total")
            .build();
        counter.add(1, &[
            opentelemetry::KeyValue::new("method", method.to_string()),
            opentelemetry::KeyValue::new("endpoint", endpoint.to_string()),
        ]);

        let histogram = meter
            .f64_histogram("otel_http_request_duration_seconds")
            .with_unit("s")
            .build();
        histogram.record(duration_secs, &[
            opentelemetry::KeyValue::new("method", method.to_string()),
            opentelemetry::KeyValue::new("endpoint", endpoint.to_string()),
        ]);
    }
}
```

### 9.3 指标与追踪关联

将指标与追踪上下文关联：

```rust
// src/otel/metrics_tracing_correlation.rs
use opentelemetry::{global, trace::TraceContextExt, KeyValue};
use tracing::Span;
use tracing_opentelemetry::OpenTelemetrySpanExt;

/// 在追踪上下文中记录指标
pub fn record_metric_in_span(metric_name: &str, value: f64) {
    let span = Span::current();
    let context = span.context();

    // 获取Trace ID和Span ID
    let span_context = context.span().span_context();
    let trace_id = span_context.trace_id().to_string();
    let span_id = span_context.span_id().to_string();

    // 在指标中包含追踪上下文
    let meter = global::meter("correlated-metrics");
    let histogram = meter
        .f64_histogram(metric_name)
        .build();

    histogram.record(value, &[
        KeyValue::new("trace_id", trace_id),
        KeyValue::new("span_id", span_id),
    ]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing::info_span;

    #[test]
    fn test_correlated_metrics() {
        let span = info_span!("test_operation");
        let _enter = span.enter();

        record_metric_in_span("operation_duration_seconds", 0.234);
    }
}
```

---

## 十、性能优化

### 10.1 零成本抽象验证

通过基准测试验证零成本：

```rust
// benches/metrics_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use metrics::counter;

fn benchmark_counter_increment(c: &mut Criterion) {
    // 初始化导出器
    let _handle = metrics_exporter_prometheus::PrometheusBuilder::new()
        .install_recorder()
        .unwrap();

    c.bench_function("counter_increment", |b| {
        b.iter(|| {
            counter!("benchmark_counter").increment(black_box(1));
        });
    });
}

fn benchmark_counter_with_labels(c: &mut Criterion) {
    c.bench_function("counter_with_labels", |b| {
        b.iter(|| {
            counter!(
                "benchmark_counter",
                "method" => "GET",
                "status" => "200"
            )
            .increment(black_box(1));
        });
    });
}

criterion_group!(benches, benchmark_counter_increment, benchmark_counter_with_labels);
criterion_main!(benches);
```

**运行基准测试**：

```bash
cargo bench

# 预期结果
# counter_increment        time:   [8.5 ns 8.6 ns 8.7 ns]
# counter_with_labels      time:   [12.3 ns 12.5 ns 12.7 ns]
```

### 10.2 标签基数控制

避免标签爆炸：

```rust
// src/optimization/cardinality_control.rs
use std::collections::HashSet;
use std::sync::{Arc, RwLock};

/// 标签白名单
pub struct LabelWhitelist {
    allowed_values: Arc<RwLock<HashSet<String>>>,
}

impl LabelWhitelist {
    pub fn new(allowed: Vec<String>) -> Self {
        Self {
            allowed_values: Arc::new(RwLock::new(allowed.into_iter().collect())),
        }
    }

    /// 验证标签值
    pub fn validate(&self, value: &str) -> String {
        let whitelist = self.allowed_values.read().unwrap();
        if whitelist.contains(value) {
            value.to_string()
        } else {
            "other".to_string() // 归类为"other"
        }
    }
}

/// 路径模板化
pub fn normalize_path(path: &str) -> String {
    // 将 /users/123/orders/456 -> /users/:id/orders/:id
    path.split('/')
        .map(|segment| {
            if segment.chars().all(|c| c.is_numeric()) {
                ":id"
            } else if segment.len() == 36 && segment.contains('-') {
                ":uuid"
            } else {
                segment
            }
        })
        .collect::<Vec<_>>()
        .join("/")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_label_whitelist() {
        let whitelist = LabelWhitelist::new(vec![
            "GET".to_string(),
            "POST".to_string(),
            "PUT".to_string(),
            "DELETE".to_string(),
        ]);

        assert_eq!(whitelist.validate("GET"), "GET");
        assert_eq!(whitelist.validate("PATCH"), "other");
    }

    #[test]
    fn test_normalize_path() {
        assert_eq!(normalize_path("/users/123"), "/users/:id");
        assert_eq!(
            normalize_path("/orders/550e8400-e29b-41d4-a716-446655440000"),
            "/orders/:uuid"
        );
    }
}
```

### 10.3 批量导出优化

配置批量导出以减少开销：

```rust
// src/optimization/batch_export.rs
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    runtime,
};
use std::time::Duration;

pub fn init_optimized_exporter() -> SdkMeterProvider {
    let exporter = opentelemetry_otlp::MetricsExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()
        .unwrap();

    let reader = PeriodicReader::builder(exporter, runtime::Tokio)
        .with_interval(Duration::from_secs(60))        // 减少导出频率
        .with_timeout(Duration::from_secs(10))         // 增加超时
        .build();

    SdkMeterProvider::builder()
        .with_reader(reader)
        .build()
}
```

---

## 十一、生产级实践

### 11.1 完整监控系统

集成所有指标类型的生产系统：

```rust
// src/production/monitoring_system.rs
use metrics::{counter, gauge, histogram, describe_counter, describe_gauge, describe_histogram, Unit};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::time;

pub struct MonitoringSystem {
    service_name: String,
}

impl MonitoringSystem {
    pub fn new(service_name: &str) -> Self {
        Self::init_all_metrics();

        Self {
            service_name: service_name.to_string(),
        }
    }

    fn init_all_metrics() {
        // Counter
        describe_counter!("http_requests_total", Unit::Count, "Total HTTP requests");
        describe_counter!("http_errors_total", Unit::Count, "Total HTTP errors");
        describe_counter!("db_queries_total", Unit::Count, "Total database queries");

        // Gauge
        describe_gauge!("http_connections_active", Unit::Count, "Active HTTP connections");
        describe_gauge!("db_connections_idle", Unit::Count, "Idle database connections");
        describe_gauge!("memory_usage_bytes", Unit::Bytes, "Memory usage");

        // Histogram
        describe_histogram!("http_request_duration_seconds", Unit::Seconds, "HTTP request duration");
        describe_histogram!("db_query_duration_seconds", Unit::Seconds, "Database query duration");
    }

    /// 记录HTTP请求
    pub fn record_http_request(
        &self,
        method: &str,
        endpoint: &str,
        status: u16,
        duration: Duration,
    ) {
        counter!(
            "http_requests_total",
            "method" => method.to_string(),
            "endpoint" => endpoint.to_string(),
            "status" => status.to_string()
        )
        .increment(1);

        histogram!(
            "http_request_duration_seconds",
            "method" => method.to_string(),
            "endpoint" => endpoint.to_string()
        )
        .record(duration.as_secs_f64());

        if status >= 400 {
            counter!(
                "http_errors_total",
                "method" => method.to_string(),
                "status" => status.to_string()
            )
            .increment(1);
        }
    }

    /// 记录数据库查询
    pub fn record_db_query(&self, query_type: &str, duration: Duration) {
        counter!("db_queries_total", "type" => query_type.to_string()).increment(1);

        histogram!("db_query_duration_seconds", "type" => query_type.to_string())
            .record(duration.as_secs_f64());
    }

    /// 更新连接状态
    pub fn update_connection_stats(&self, active_http: u64, idle_db: u64) {
        gauge!("http_connections_active").set(active_http as f64);
        gauge!("db_connections_idle").set(idle_db as f64);
    }

    /// 启动系统监控
    pub async fn start_system_monitoring(self: Arc<Self>) {
        let mut interval = time::interval(Duration::from_secs(15));

        loop {
            interval.tick().await;

            // 收集系统指标
            let mut sys = sysinfo::System::new_all();
            sys.refresh_all();

            let memory_used = sys.used_memory();
            gauge!("memory_usage_bytes", "service" => self.service_name.clone())
                .set(memory_used as f64);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_monitoring_system() {
        let monitoring = Arc::new(MonitoringSystem::new("test-service"));

        // 模拟HTTP请求
        monitoring.record_http_request("GET", "/api/users", 200, Duration::from_millis(50));
        monitoring.record_http_request("POST", "/api/orders", 201, Duration::from_millis(120));
        monitoring.record_http_request("GET", "/api/products", 404, Duration::from_millis(10));

        // 模拟数据库查询
        monitoring.record_db_query("SELECT", Duration::from_millis(5));
        monitoring.record_db_query("INSERT", Duration::from_millis(15));

        // 更新连接状态
        monitoring.update_connection_stats(10, 5);

        // 启动系统监控
        let monitoring_clone = monitoring.clone();
        tokio::spawn(async move {
            monitoring_clone.start_system_monitoring().await;
        });

        tokio::time::sleep(Duration::from_secs(20)).await;
    }
}
```

### 11.2 告警规则设计

Prometheus告警规则配置：

```yaml
# alerts.yml
groups:
  - name: api_alerts
    interval: 30s
    rules:
      # 高错误率
      - alert: HighErrorRate
        expr: |
          rate(http_errors_total[5m]) / rate(http_requests_total[5m]) > 0.05
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }} (threshold: 5%)"

      # 高延迟
      - alert: HighLatency
        expr: |
          histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1.0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High API latency"
          description: "P95 latency is {{ $value }}s (threshold: 1s)"

      # 数据库查询慢
      - alert: SlowDatabaseQueries
        expr: |
          histogram_quantile(0.99, rate(db_query_duration_seconds_bucket[5m])) > 0.5
        for: 10m
        labels:
          severity: critical
        annotations:
          summary: "Slow database queries"
          description: "P99 query time is {{ $value }}s"

      # 连接池耗尽
      - alert: ConnectionPoolExhausted
        expr: |
          db_connections_idle < 2
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Database connection pool nearly exhausted"
          description: "Only {{ $value }} idle connections remaining"

  - name: system_alerts
    interval: 30s
    rules:
      # 高内存使用
      - alert: HighMemoryUsage
        expr: |
          memory_usage_bytes / 1024 / 1024 / 1024 > 8
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage"
          description: "Memory usage is {{ $value | humanize }}GB (threshold: 8GB)"

      # 高CPU使用
      - alert: HighCPUUsage
        expr: |
          system_cpu_usage_ratio > 0.8
        for: 15m
        labels:
          severity: warning
        annotations:
          summary: "High CPU usage"
          description: "CPU usage is {{ $value | humanizePercentage }}"
```

### 11.3 Grafana仪表盘

Grafana仪表盘JSON配置（部分）：

```json
{
  "dashboard": {
    "title": "Rust OTLP Metrics Dashboard",
    "panels": [
      {
        "title": "Request Rate",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total[5m])) by (method)",
            "legendFormat": "{{method}}"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Error Rate",
        "targets": [
          {
            "expr": "sum(rate(http_errors_total[5m])) / sum(rate(http_requests_total[5m]))",
            "legendFormat": "Error Rate"
          }
        ],
        "type": "graph"
      },
      {
        "title": "P95 Latency",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le, endpoint))",
            "legendFormat": "{{endpoint}}"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Active Connections",
        "targets": [
          {
            "expr": "http_connections_active",
            "legendFormat": "HTTP Connections"
          },
          {
            "expr": "db_connections_idle",
            "legendFormat": "DB Idle Connections"
          }
        ],
        "type": "graph"
      }
    ]
  }
}
```

---

## 十二、Docker Compose部署

完整的可观测性栈部署：

```yaml
# docker-compose.yml
version: '3.8'

services:
  # Rust应用
  app:
    build: .
    ports:
      - "3000:3000"    # 应用端口
      - "9090:9090"    # Metrics端口
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - otel-collector
      - prometheus

  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.114.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP
      - "8888:8888"    # Prometheus metrics (collector自身)
      - "8889:8889"    # Prometheus exporter

  # Prometheus
  prometheus:
    image: prom/prometheus:v3.1.0
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - ./alerts.yml:/etc/prometheus/alerts.yml
      - prometheus_data:/prometheus
    ports:
      - "9091:9090"
    depends_on:
      - otel-collector

  # Grafana
  grafana:
    image: grafana/grafana:11.4.0
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - grafana_data:/var/lib/grafana
      - ./grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
      - ./grafana-dashboards.yml:/etc/grafana/provisioning/dashboards/dashboards.yml
    depends_on:
      - prometheus

  # Jaeger (用于追踪，但也可查看关联指标)
  jaeger:
    image: jaegertracing/all-in-one:1.64
    ports:
      - "16686:16686"  # UI
      - "14250:14250"  # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true

volumes:
  prometheus_data:
  grafana_data:
```

**OpenTelemetry Collector配置**：

```yaml
# otel-collector-config.yaml
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

exporters:
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: "otel"
    const_labels:
      environment: "production"

  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

  logging:
    verbosity: detailed

service:
  pipelines:
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheus, logging]

    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger, logging]
```

**Prometheus配置**：

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - /etc/prometheus/alerts.yml

scrape_configs:
  # Rust应用（Prometheus原生格式）
  - job_name: 'rust-app'
    static_configs:
      - targets: ['app:9090']

  # OTEL Collector（OTLP转Prometheus）
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8889']

  # OTEL Collector自身指标
  - job_name: 'otel-collector-internal'
    static_configs:
      - targets: ['otel-collector:8888']

alerting:
  alertmanagers:
    - static_configs:
        - targets: []
```

**Grafana数据源配置**：

```yaml
# grafana-datasources.yml
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
    editable: true
```

**启动服务**：

```bash
docker-compose up -d

# 验证
curl http://localhost:9090/metrics        # Rust应用指标
curl http://localhost:9091/api/v1/targets # Prometheus targets
curl http://localhost:3001                # Grafana (admin/admin)
```

---

## 十三、参考资源

### 官方文档

1. **Prometheus文档**: <https://prometheus.io/docs/>
2. **OpenTelemetry Metrics规范**: <https://opentelemetry.io/docs/specs/otel/metrics/>
3. **metrics库文档**: <https://docs.rs/metrics/latest/metrics/>
4. **metrics-exporter-prometheus**: <https://docs.rs/metrics-exporter-prometheus/>

### 国际标准

1. **Prometheus命名规范**: <https://prometheus.io/docs/practices/naming/>
2. **OpenTelemetry语义约定**: <https://opentelemetry.io/docs/specs/semconv/>
3. **CNCF可观测性最佳实践**: <https://www.cncf.io/blog/2021/08/12/observability-best-practices/>

### Rust生态

1. **tokio文档**: <https://tokio.rs/>
2. **axum文档**: <https://docs.rs/axum/>
3. **sysinfo文档**: <https://docs.rs/sysinfo/>

### 博客和教程

1. **Rust Metrics最佳实践** (Datadog): <https://www.datadoghq.com/blog/engineering/rust-metrics/>
2. **OpenTelemetry Rust SDK指南**: <https://github.com/open-telemetry/opentelemetry-rust>

---

## 总结

本文档提供了Rust 1.90中Metrics的完整实现指南，涵盖：

✅ **4种指标类型**：Counter、Gauge、Histogram、Summary  
✅ **Prometheus导出器**：HTTP端点、自定义Bucket  
✅ **OpenTelemetry集成**：OTLP Exporter、多后端导出  
✅ **高级模式**：复合指标、动态标签、指标聚合  
✅ **性能优化**：零成本抽象、标签基数控制  
✅ **生产实践**：完整监控系统、告警规则、Grafana仪表盘  
✅ **Docker部署**：Prometheus、Grafana、Jaeger、OTEL Collector  

**核心优势**：

- 完全遵循Prometheus命名规范和OpenTelemetry标准
- 利用Rust 1.90的零成本抽象，性能开销极低（< 10ns/metric）
- 支持多后端导出，灵活适配不同监控栈
- 完整的生产级示例和部署配置

**下一步**：

- 探索`tracing-appender`进行日志归档
- 学习`pprof`进行CPU/内存性能分析
- 集成云原生监控平台（Datadog、Dynatrace）
