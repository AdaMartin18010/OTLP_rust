# OTLP Rust 架构概览

**版本**: 2.0
**更新日期**: 2026-03-15
**架构状态**: ✅ 稳定

---

## 📐 架构总览

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           应用层 (Application)                               │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │   Client    │  │   Tracing   │  │   Metrics   │  │      Logging        │ │
│  │   Builder   │  │   Builder   │  │   Builder   │  │      Builder        │ │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘ │
└─────────┼────────────────┼────────────────┼────────────────────┼────────────┘
          │                │                │                    │
          └────────────────┴────────────────┴────────────────────┘
                                    │
┌───────────────────────────────────┼─────────────────────────────────────────┐
│                         核心层 (Core)                                       │
│  ┌────────────────────────────────┼────────────────────────────────────┐   │
│  │                      TelemetryData                                   │   │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌────────────────────┐  │   │
│  │  │  Trace   │  │  Metric  │  │   Log    │  │      Profile       │  │   │
│  │  │  Data    │  │  Data    │  │  Data    │  │      (New)         │  │   │
│  │  └──────────┘  └──────────┘  └──────────┘  └────────────────────┘  │   │
│  └────────────────────────────────┼────────────────────────────────────┘   │
│                                   │                                         │
│  ┌────────────────────────────────┼────────────────────────────────────┐   │
│  │                      OtlpExporter                                    │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────────┐  │   │
│  │  │   Export    │  │    Retry    │  │        Transport            │  │   │
│  │  │    Batch    │  │   Policy    │  │       (Pool)                │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────────┘  │   │
│  └────────────────────────────────┼────────────────────────────────────┘   │
└───────────────────────────────────┼─────────────────────────────────────────┘
                                    │
┌───────────────────────────────────┼─────────────────────────────────────────┐
│                         传输层 (Transport)                                  │
│  ┌────────────────────────────────┼────────────────────────────────────┐   │
│  │                    TransportPool                                     │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────┐  │   │
│  │  │    gRPC     │  │    HTTP/    │  │   HTTP/     │  │  WebSocket │  │   │
│  │  │  (4317)     │  │  Protobuf   │  │    JSON     │  │ (Optional) │  │   │
│  │  └─────────────┘  │  (4318)     │  │  (4318)     │  └────────────┘  │   │
│  │                   └─────────────┘  └─────────────┘                   │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         后端层 (Backend)                                     │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────────────┐ │
│  │  OpenTelemetry│  │   Jaeger    │  │  Prometheus │  │   Custom Backend   │ │
│  │  Collector  │  │             │  │             │  │                    │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 🏗️ 模块架构

### 1. 数据模型层 (Data Model)

```rust
// crates/otlp/src/data.rs

/// 核心数据类型枚举
pub enum TelemetryDataType {
    Trace,      // 分布式追踪
    Metric,     // 指标数据
    Log,        // 日志数据
    Profile,    // 性能分析 (OTLP 1.10+)
}

/// 统一数据容器
pub struct TelemetryData {
    pub data_type: TelemetryDataType,
    pub timestamp: u64,
    pub resource_attributes: HashMap<String, String>,
    pub scope_attributes: HashMap<String, String>,
    pub content: TelemetryContent,
}

/// 数据内容枚举
pub enum TelemetryContent {
    Trace(TraceData),
    Metric(MetricData),
    Log(LogData),
    Profile(ProfileData),  // OTLP 1.10+
}
```

### 2. 客户端层 (Client Layer)

```rust
// crates/otlp/src/client/

/// 构建器模式实现
pub struct OtlpClientBuilder {
    config: OtlpConfig,
    endpoint: String,
    protocol: TransportProtocol,
    resource_attrs: HashMap<String, String>,
}

impl OtlpClientBuilder {
    pub fn new() -> Self;
    pub fn endpoint(mut self, url: impl Into<String>) -> Self;
    pub fn protocol(mut self, protocol: TransportProtocol) -> Self;
    pub async fn build(self) -> Result<OtlpClient>;
}
```

### 3. 导出器层 (Exporter Layer)

```rust
// crates/otlp/src/exporter.rs

/// 核心导出器
pub struct OtlpExporter {
    config: OtlpConfig,
    transport_pool: Arc<RwLock<TransportPool>>,
    export_queue: mpsc::Sender<Vec<TelemetryData>>,
    metrics: Arc<RwLock<ExporterMetrics>>,
}

impl OtlpExporter {
    pub fn new(config: OtlpConfig) -> Self;
    pub async fn initialize(&self) -> Result<()>;
    pub async fn export(&self, data: Vec<TelemetryData>) -> Result<ExportResult>;

    /// OTLP 1.10+ 支持的 Partial Success 处理
    async fn handle_partial_success(
        &self,
        partial: PartialSuccess,
    ) -> Result<RetryDecision>;
}
```

### 4. 传输层 (Transport Layer)

```rust
// crates/otlp/src/transport.rs

/// 传输池实现
pub struct TransportPool {
    transports: Vec<Box<dyn Transport>>,
    current_index: AtomicUsize,
    config: TransportPoolConfig,
}

/// 传输协议枚举
pub enum TransportProtocol {
    Grpc,           // gRPC 协议 (端口 4317)
    HttpProtobuf,   // HTTP + Protobuf (端口 4318)
    HttpJson,       // HTTP + JSON (端口 4318)
}

#[async_trait]
pub trait Transport: Send + Sync {
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()>;
    async fn health_check(&self) -> Result<HealthStatus>;
    fn protocol(&self) -> TransportProtocol;
}
```

---

## 🔧 核心组件

### 批处理系统

```rust
/// 批处理配置
pub struct BatchConfig {
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 最大批次大小
    pub max_export_batch_size: usize,
    /// 调度延迟
    pub scheduled_delay: Duration,
    /// 导出超时
    pub export_timeout: Duration,
}

/// 批处理器
pub struct BatchProcessor {
    queue: BoundedQueue<TelemetryData>,
    config: BatchConfig,
    exporter: Arc<dyn Exporter>,
}

impl BatchProcessor {
    pub async fn start(&self) {
        // 定时导出循环
        loop {
            tokio::time::sleep(self.config.scheduled_delay).await;

            let batch = self.queue.drain(self.config.max_export_batch_size);
            if !batch.is_empty() {
                match self.exporter.export(batch).await {
                    Ok(result) => self.handle_success(result),
                    Err(e) => self.handle_error(e).await,
                }
            }
        }
    }
}
```

### 重试机制

```rust
/// 重试策略
pub enum RetryPolicy {
    /// 固定间隔重试
    FixedInterval {
        interval: Duration,
        max_retries: u32,
    },
    /// 指数退避
    ExponentialBackoff {
        initial_interval: Duration,
        max_interval: Duration,
        max_retries: u32,
        multiplier: f64,
    },
    /// 自定义策略
    Custom(Box<dyn RetryStrategy>),
}

/// 重试实现
pub struct RetryHandler {
    policy: RetryPolicy,
    metrics: RetryMetrics,
}

impl RetryHandler {
    pub async fn execute<F, Fut, T>(&self, operation: F) -> Result<T>
    where
        F: Fn() -> Fut,
        Fut: Future<Output = Result<T>>,
    {
        let mut attempts = 0;
        let mut delay = self.initial_delay();

        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) if attempts >= self.max_retries() => return Err(e),
                Err(e) => {
                    attempts += 1;
                    self.metrics.record_retry(attempts, &e);
                    tokio::time::sleep(delay).await;
                    delay = self.next_delay(delay);
                }
            }
        }
    }
}
```

---

## 🚀 Rust 1.94 特性集成

### array_windows 在异常检测中的应用

```rust
/// 使用 array_windows 进行异常检测
pub fn detect_anomaly_pattern(data: &[u8]) -> Vec<Anomaly> {
    data.array_windows()
        .enumerate()
        .filter(|(_, [a, b, c, d])| {
            // 检测 ABBA 异常模式
            a == d && b == c && a != b
        })
        .map(|(idx, _)| Anomaly {
            position: idx,
            pattern: PatternType::Abnormal,
        })
        .collect()
}
```

### element_offset 在零拷贝中的应用

```rust
/// 使用 element_offset 进行零拷贝序列化
pub fn zero_copy_serialize<T>(data: &[T]) -> SerializedData {
    let offsets: Vec<_> = data.iter()
        .map(|elem| data.element_offset(elem))
        .collect();

    SerializedData {
        base_ptr: data.as_ptr(),
        offsets,
        len: data.len(),
    }
}
```

### SIMD 优化

```rust
/// AVX-512 FP16 加速（Rust 1.94）
#[cfg(target_feature = "avx512fp16")]
pub fn avx512_aggregate(values: &[f16]) -> AggregationResult {
    use std::arch::x86_64::*;

    unsafe {
        let mut sum = _mm256_set1_ph(0.0);

        for chunk in values.chunks_exact(16) {
            let vec = _mm256_loadu_ph(chunk.as_ptr());
            sum = _mm256_add_ph(sum, vec);
        }

        // 水平求和
        let temp: [f16; 16] = std::mem::transmute(sum);
        AggregationResult {
            sum: temp.iter().sum(),
            count: values.len(),
        }
    }
}
```

---

## 📊 数据流

### 导出流程

```
┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
│  App     │     │  Batch   │     │  Export  │     │ Transport│     │ Backend  │
│  Code    │────▶│  Queue   │────▶│  Engine  │────▶│  Layer   │────▶│  Server  │
└──────────┘     └──────────┘     └──────────┘     └──────────┘     └──────────┘
     │                 │                │                 │                │
     │ create span     │                │                 │                │
     │────────────────▶│                │                 │                │
     │                 │ enqueue        │                 │                │
     │                 │───────────────▶│                 │                │
     │                 │                │ batch full      │                │
     │                 │                │ or timeout      │                │
     │                 │                │────────────────▶│                │
     │                 │                │                 │ serialize      │
     │                 │                │                 │────────────────▶
     │                 │                │                 │                │
     │                 │                │                 │ retry if       │
     │                 │                │                 │ needed         │
     │                 │                │                 │◀───────────────│
     │                 │                │                 │                │
     │                 │                │ success/failure │                │
     │                 │◀───────────────│                 │                │
     │                 │                │                 │                │
```

### 错误处理流程

```
┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
│  Export  │     │  Error   │     │  Retry   │     │  Circuit │
│  Attempt │────▶│  Classify│────▶│  Handler │────▶│  Breaker │
└──────────┘     └──────────┘     └──────────┘     └──────────┘
     │                 │                │                 │
     │                 │ retryable?     │                 │
     │                 ├───────────────▶│                 │
     │                 │ yes            │ retry count     │
     │                 │                ├───────────────▶│
     │                 │                │ < max?          │
     │                 │                │                 ├──────────┐
     │                 │                │                 │ yes      │
     │◀────────────────│                │◀────────────────│          │
     │ retry           │                │ wait & retry   │          │
     │                 │                │                 │          │
     │                 │ no             │                 │ no       │
     │                 ├───────────────▶│                 │          │
     │                 │                │ drop & record  │          │
     │                 │                │                 │          │
     │                 │◀───────────────│                 │          │
     │                 │ report error   │                 │          │
```

---

## 🔒 安全架构

### 数据脱敏

```rust
/// 敏感数据脱敏
pub struct Sanitizer {
    patterns: Vec<SensitivePattern>,
}

impl Sanitizer {
    pub fn sanitize_attributes(&self, attrs: &mut HashMap<String, AttributeValue>) {
        for (key, value) in attrs.iter_mut() {
            if self.is_sensitive(key) {
                *value = self.mask(value);
            }
        }
    }

    fn is_sensitive(&self, key: &str) -> bool {
        // 检测敏感键
        matches!(key.to_lowercase().as_str(),
            "password" | "token" | "secret" | "key" | "auth")
    }

    fn mask(&self, value: &AttributeValue) -> AttributeValue {
        match value {
            AttributeValue::String(s) => {
                AttributeValue::String(format!("{}***", &s[..s.len().min(4)]))
            }
            _ => AttributeValue::String("[REDACTED]".to_string()),
        }
    }
}
```

### TLS 配置

```rust
/// TLS 传输配置
pub struct TlsConfig {
    pub cert_path: Option<PathBuf>,
    pub key_path: Option<PathBuf>,
    pub ca_path: Option<PathBuf>,
    pub verify_hostname: bool,
    pub min_version: TlsVersion,
}

impl TlsConfig {
    pub fn new() -> Self {
        Self {
            cert_path: None,
            key_path: None,
            ca_path: None,
            verify_hostname: true,
            min_version: TLS_1_2,
        }
    }
}
```

---

## 📈 性能指标

### 关键指标

| 指标 | 目标 | 说明 |
|------|------|------|
| 导出延迟 | < 100ms | p99 导出耗时 |
| 批处理吞吐量 | > 10,000/s | 每秒处理数据点数 |
| 内存使用 | < 100MB | 稳定状态内存 |
| CPU 开销 | < 5% | 相对应用 CPU |
| 成功率 | > 99.9% | 导出成功比例 |

### 监控点

```rust
/// 关键监控指标
pub struct TelemetryMetrics {
    /// 导出延迟分布
    pub export_latency: Histogram<f64>,
    /// 批次大小分布
    pub batch_size: Histogram<usize>,
    /// 队列大小
    pub queue_size: Gauge<usize>,
    /// 导出成功率
    pub export_success_rate: Gauge<f64>,
    /// 重试次数
    pub retry_count: Counter<u64>,
    /// 丢弃数据数
    pub dropped_count: Counter<u64>,
}
```

---

## 🔗 集成点

### OpenTelemetry Collector

```yaml
# collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  jaeger:
    endpoint: jaeger:14250
  prometheus:
    endpoint: 0.0.0.0:8889

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheus]
```

---

**文档维护**: OTLP Rust Team
**最后更新**: 2026-03-15
