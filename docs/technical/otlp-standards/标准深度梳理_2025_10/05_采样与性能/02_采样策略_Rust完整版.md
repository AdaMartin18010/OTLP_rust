# 采样策略 - Rust 完整版

## 目录

- [采样策略 - Rust 完整版](#采样策略---rust-完整版)
  - [目录](#目录)
  - [1. 采样基础](#1-采样基础)
    - [1.1 为什么需要采样](#11-为什么需要采样)
    - [1.2 采样决策](#12-采样决策)
  - [2. 内置采样器](#2-内置采样器)
    - [2.1 AlwaysOn / AlwaysOff](#21-alwayson--alwaysoff)
    - [2.2 TraceIdRatioBased](#22-traceidratiobased)
    - [2.3 ParentBased](#23-parentbased)
  - [3. 自定义采样器](#3-自定义采样器)
    - [3.1 基于优先级](#31-基于优先级)
    - [3.2 基于路由](#32-基于路由)
    - [3.3 基于错误率](#33-基于错误率)
  - [4. 自适应采样](#4-自适应采样)
    - [4.1 基于流量](#41-基于流量)
    - [4.2 基于延迟](#42-基于延迟)
    - [4.3 基于资源使用](#43-基于资源使用)
  - [5. 分布式采样](#5-分布式采样)
    - [5.1 头部采样 (Head-based)](#51-头部采样-head-based)
    - [5.2 尾部采样 (Tail-based)](#52-尾部采样-tail-based)
    - [5.3 混合采样](#53-混合采样)
  - [6. 采样与 Span 链接](#6-采样与-span-链接)
    - [6.1 Span Links](#61-span-links)
    - [6.2 跨服务采样一致性](#62-跨服务采样一致性)
  - [7. 性能监控](#7-性能监控)
    - [7.1 采样率指标](#71-采样率指标)
    - [7.2 存储成本监控](#72-存储成本监控)
  - [8. 生产环境配置](#8-生产环境配置)
    - [8.1 推荐配置](#81-推荐配置)
    - [8.2 环境变量](#82-环境变量)
    - [8.3 完整示例](#83-完整示例)
  - [9. 调试采样决策](#9-调试采样决策)
    - [9.1 采样日志](#91-采样日志)
    - [9.2 Jaeger 采样标记](#92-jaeger-采样标记)
  - [10. Rust 1.90 特性应用](#10-rust-190-特性应用)
    - [10.1 AFIT 在采样器](#101-afit-在采样器)
    - [10.2 零成本抽象](#102-零成本抽象)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [推荐采样率](#推荐采样率)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 采样基础

### 1.1 为什么需要采样

````text
全量追踪问题:
- 高流量下生成海量 Span（100k+ req/s → 1M+ spans/s）
- 存储成本高（1 Span ≈ 1KB → 1GB/s）
- 网络带宽占用大
- 后端处理压力大

采样好处:
- 降低开销 95% (10% 采样率)
- 保留代表性样本
- 保证错误/慢请求被追踪
````

### 1.2 采样决策

````rust
use opentelemetry_sdk::trace::{SamplingDecision, SamplingResult};

pub enum SamplingDecision {
    Drop,               // 丢弃 Span，不记录
    RecordOnly,         // 记录但不导出
    RecordAndSample,    // 记录并导出
}

pub struct SamplingResult {
    pub decision: SamplingDecision,
    pub attributes: Vec<opentelemetry::KeyValue>,  // 额外属性
    pub trace_state: Option<opentelemetry::trace::TraceState>,
}
````

---

## 2. 内置采样器

### 2.1 AlwaysOn / AlwaysOff

````rust
use opentelemetry_sdk::trace::Sampler;

// ✅ 开发环境: 总是采样
pub fn dev_sampler() -> Sampler {
    Sampler::AlwaysOn
}

// ✅ 性能测试: 不采样
pub fn benchmark_sampler() -> Sampler {
    Sampler::AlwaysOff
}
````

### 2.2 TraceIdRatioBased

````rust
use opentelemetry_sdk::trace::Sampler;

// 基于 TraceId 的确定性采样 (10%)
pub fn ratio_sampler() -> Sampler {
    Sampler::TraceIdRatioBased(0.1)
}

// 原理: hash(trace_id) % 100 < (ratio * 100)
// 优势: 同一 Trace 在所有服务中采样决策一致
````

### 2.3 ParentBased

````rust
use opentelemetry_sdk::trace::Sampler;

// 尊重父 Span 采样决策
pub fn parent_based_sampler() -> Sampler {
    Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))
}

// 逻辑:
// - 有父 Span 且已采样 → 采样
// - 有父 Span 但未采样 → 不采样
// - 无父 Span → 使用回退采样器 (TraceIdRatioBased 10%)
````

---

## 3. 自定义采样器

### 3.1 基于优先级

````rust
use opentelemetry::{
    trace::{SpanKind, TraceId},
    Context, KeyValue,
};
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct PrioritySampler {
    default_ratio: f64,
}

impl PrioritySampler {
    pub fn new(default_ratio: f64) -> Self {
        Self { default_ratio }
    }
}

impl Sampler for PrioritySampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 1. 高优先级请求总是采样
        if attributes.iter().any(|kv| {
            kv.key.as_str() == "priority" && kv.value.as_str() == "high"
        }) {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![KeyValue::new("sampler.type", "priority")],
                trace_state: None,
            };
        }

        // 2. 错误请求总是采样
        if attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        }) {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![KeyValue::new("sampler.type", "error")],
                trace_state: None,
            };
        }

        // 3. 其他请求按概率采样
        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < self.default_ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![KeyValue::new("sampler.type", "ratio")],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

**使用示例**:

````rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{Config, TracerProvider};

pub fn init_priority_sampling() -> anyhow::Result<()> {
    let sampler = PrioritySampler::new(0.1);

    let provider = TracerProvider::builder()
        .with_config(Config::default().with_sampler(sampler))
        .build();

    global::set_tracer_provider(provider);
    Ok(())
}
````

### 3.2 基于路由

````rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct RouteSampler {
    high_traffic_ratio: f64,
    low_traffic_ratio: f64,
}

impl Sampler for RouteSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 查找 http.route 属性
        let route = attributes
            .iter()
            .find(|kv| kv.key.as_str() == "http.route")
            .and_then(|kv| kv.value.as_str())
            .map(|s| s.as_ref());

        let ratio = match route {
            // 高流量端点: 低采样率
            Some("/api/health") | Some("/api/metrics") => 0.01,
            // 重要端点: 高采样率
            Some("/api/payment") | Some("/api/orders") => 0.5,
            // 其他端点: 默认采样率
            _ => self.low_traffic_ratio,
        };

        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![opentelemetry::KeyValue::new("sampler.ratio", ratio)],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

### 3.3 基于错误率

````rust
use std::sync::Arc;
use tokio::sync::RwLock;
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct ErrorRateSampler {
    error_count: Arc<RwLock<u64>>,
    total_count: Arc<RwLock<u64>>,
    base_ratio: f64,
}

impl ErrorRateSampler {
    pub fn new(base_ratio: f64) -> Self {
        Self {
            error_count: Arc::new(RwLock::new(0)),
            total_count: Arc::new(RwLock::new(0)),
            base_ratio,
        }
    }

    pub async fn error_rate(&self) -> f64 {
        let total = *self.total_count.read().await;
        if total == 0 {
            return 0.0;
        }
        let errors = *self.error_count.read().await;
        (errors as f64) / (total as f64)
    }
}

impl Sampler for ErrorRateSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 检查是否为错误
        let is_error = attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        });

        // 错误总是采样
        if is_error {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: None,
            };
        }

        // 正常请求按基础比例采样
        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < self.base_ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

---

## 4. 自适应采样

### 4.1 基于流量

````rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct AdaptiveSampler {
    current_ratio: Arc<RwLock<f64>>,
    request_count: Arc<RwLock<u64>>,
    last_adjust: Arc<RwLock<Instant>>,
    target_spans_per_sec: u64,
}

impl AdaptiveSampler {
    pub fn new(target_spans_per_sec: u64) -> Self {
        Self {
            current_ratio: Arc::new(RwLock::new(0.1)),
            request_count: Arc::new(RwLock::new(0)),
            last_adjust: Arc::new(RwLock::new(Instant::now())),
            target_spans_per_sec,
        }
    }

    pub async fn adjust_ratio(&self) {
        let mut last = self.last_adjust.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last);

        if elapsed < Duration::from_secs(10) {
            return;
        }

        let count = *self.request_count.read().await;
        let req_per_sec = count / elapsed.as_secs();
        let mut ratio = self.current_ratio.write().await;

        // 计算新的采样率
        let new_ratio = (self.target_spans_per_sec as f64) / (req_per_sec as f64);
        *ratio = new_ratio.clamp(0.01, 1.0);

        tracing::info!(
            old_ratio = *ratio,
            new_ratio = new_ratio,
            req_per_sec,
            "Adjusted sampling ratio"
        );

        *self.request_count.write().await = 0;
        *last = now;
    }
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 注意: 需要使用 tokio::task::block_in_place 或其他机制
        // 因为 should_sample 是同步方法
        let ratio = 0.1; // 简化示例，实际应从 self.current_ratio 读取

        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

### 4.2 基于延迟

````rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct LatencySampler {
    base_ratio: f64,
    slow_threshold_ms: u64,
}

impl LatencySampler {
    pub fn new(base_ratio: f64, slow_threshold_ms: u64) -> Self {
        Self {
            base_ratio,
            slow_threshold_ms,
        }
    }
}

impl Sampler for LatencySampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 检查是否为慢请求
        let is_slow = attributes.iter().any(|kv| {
            if kv.key.as_str() == "http.duration_ms" {
                if let Some(duration) = kv.value.as_i64() {
                    return duration as u64 > self.slow_threshold_ms;
                }
            }
            false
        });

        // 慢请求总是采样
        if is_slow {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![opentelemetry::KeyValue::new("sampler.reason", "slow")],
                trace_state: None,
            };
        }

        // 正常请求按比例采样
        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < self.base_ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

### 4.3 基于资源使用

````rust
use sysinfo::{System, SystemExt, CpuExt};
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct ResourceAwareSampler {
    base_ratio: f64,
    cpu_threshold: f32,
}

impl ResourceAwareSampler {
    pub fn new(base_ratio: f64, cpu_threshold: f32) -> Self {
        Self {
            base_ratio,
            cpu_threshold,
        }
    }

    fn get_cpu_usage() -> f32 {
        let mut sys = System::new_all();
        sys.refresh_cpu();
        std::thread::sleep(std::time::Duration::from_millis(100));
        sys.refresh_cpu();
        sys.global_cpu_info().cpu_usage()
    }
}

impl Sampler for ResourceAwareSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // CPU 使用率高时降低采样率
        let cpu_usage = Self::get_cpu_usage();
        let effective_ratio = if cpu_usage > self.cpu_threshold {
            self.base_ratio * 0.5  // 降低 50%
        } else {
            self.base_ratio
        };

        let trace_id_bytes = trace_id.to_bytes();
        let hash = u64::from_be_bytes([
            trace_id_bytes[8], trace_id_bytes[9], trace_id_bytes[10], trace_id_bytes[11],
            trace_id_bytes[12], trace_id_bytes[13], trace_id_bytes[14], trace_id_bytes[15],
        ]);
        let probability = (hash as f64) / (u64::MAX as f64);

        if probability < effective_ratio {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![
                    opentelemetry::KeyValue::new("sampler.cpu_usage", cpu_usage.to_string()),
                ],
                trace_state: None,
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: None,
            }
        }
    }
}
````

---

## 5. 分布式采样

### 5.1 头部采样 (Head-based)

````rust
// 在 API Gateway 决定采样，所有下游服务遵循
use opentelemetry_sdk::trace::Sampler;

pub fn head_based_sampling() -> Sampler {
    // 使用 ParentBased，确保下游服务遵循上游决策
    Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)))
}

// 优势: 决策快，开销低
// 劣势: 无法基于尾部信息（如错误、延迟）
````

### 5.2 尾部采样 (Tail-based)

````yaml
# otel-collector-config.yaml
processors:
  tail_sampling:
    policies:
      # 策略 1: 采样所有错误
      - name: error-traces
        type: status_code
        status_code:
          status_codes: [ERROR]

      # 策略 2: 采样慢请求 (>1s)
      - name: slow-traces
        type: latency
        latency:
          threshold_ms: 1000

      # 策略 3: 10% 基础采样
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [tail_sampling, batch]
      exporters: [jaeger]
````

**Rust 客户端配置**:

````rust
// 客户端总是发送到 Collector（RecordOnly）
use opentelemetry_sdk::trace::Sampler;

pub fn tail_based_client() -> Sampler {
    // 记录所有 Span，由 Collector 决定是否导出
    Sampler::AlwaysOn
}
````

### 5.3 混合采样

````rust
// 头部采样 10% + 错误/慢请求总是采样
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

pub struct HybridSampler {
    head_sampler: Box<dyn Sampler + Send + Sync>,
}

impl HybridSampler {
    pub fn new() -> Self {
        Self {
            head_sampler: Box::new(Sampler::TraceIdRatioBased(0.1)),
        }
    }
}

impl Sampler for HybridSampler {
    fn should_sample(
        &self,
        parent_context: Option<&opentelemetry::Context>,
        trace_id: opentelemetry::trace::TraceId,
        name: &str,
        span_kind: &opentelemetry::trace::SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 头部采样决策
        let head_result = self.head_sampler.should_sample(
            parent_context,
            trace_id,
            name,
            span_kind,
            attributes,
            links,
        );

        // 强制采样条件
        let force_sample = attributes.iter().any(|kv| {
            matches!(
                kv.key.as_str(),
                "error" | "priority" if kv.value.as_str() == "high"
            )
        });

        if force_sample {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![opentelemetry::KeyValue::new("sampler.forced", "true")],
                trace_state: None,
            }
        } else {
            head_result
        }
    }
}
````

---

## 6. 采样与 Span 链接

### 6.1 Span Links

````rust
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::global;

pub async fn span_with_links() {
    let tracer = global::tracer("my-service");

    // Span A (已采样)
    let span_a = tracer.span_builder("operation_a").start(&tracer);
    let context_a = opentelemetry::Context::current_with_span(span_a);

    // Span B (未采样，但链接到 A)
    let span_b = tracer
        .span_builder("operation_b")
        .with_links(vec![
            opentelemetry::trace::Link::new(
                context_a.span().span_context().clone(),
                Vec::new(),
            )
        ])
        .start(&tracer);

    // Span B 未采样，但通过 Link 可以找到 Span A
}
````

### 6.2 跨服务采样一致性

````rust
// 确保 TraceId 一致性
use opentelemetry::propagation::TextMapPropagator;
use opentelemetry_sdk::propagation::TraceContextPropagator;

pub fn ensure_sampling_consistency() {
    // 使用 W3C Trace Context 传播采样决策
    let propagator = TraceContextPropagator::new();
    opentelemetry::global::set_text_map_propagator(propagator);

    // traceparent Header 包含 sampled flag (01 = sampled, 00 = not sampled)
    // 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
    //                                                         ^^ sampled
}
````

---

## 7. 性能监控

### 7.1 采样率指标

````rust
use opentelemetry::metrics::{Counter, Meter};

pub struct SamplingMetrics {
    sampled_count: Counter<u64>,
    dropped_count: Counter<u64>,
}

impl SamplingMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            sampled_count: meter
                .u64_counter("sampling.sampled.count")
                .with_description("Number of sampled spans")
                .build(),
            dropped_count: meter
                .u64_counter("sampling.dropped.count")
                .with_description("Number of dropped spans")
                .build(),
        }
    }

    pub fn record_sampled(&self, sampler_type: &str) {
        self.sampled_count.add(1, &[
            ("sampler.type", sampler_type.to_string()).into(),
        ]);
    }

    pub fn record_dropped(&self, sampler_type: &str) {
        self.dropped_count.add(1, &[
            ("sampler.type", sampler_type.to_string()).into(),
        ]);
    }

    pub fn sampling_ratio(&self) -> f64 {
        // 需要从指标后端查询
        0.1
    }
}
````

### 7.2 存储成本监控

````rust
use opentelemetry::metrics::{Histogram, Meter};

pub struct StorageMetrics {
    span_size: Histogram<f64>,
}

impl StorageMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            span_size: meter
                .f64_histogram("span.size.bytes")
                .with_description("Size of exported spans in bytes")
                .build(),
        }
    }

    pub fn record_span_size(&self, size_bytes: f64) {
        self.span_size.record(size_bytes, &[]);
    }

    pub fn estimated_monthly_cost(&self, avg_span_size_kb: f64, spans_per_day: u64) -> f64 {
        // 假设: $0.10/GB/月
        let gb_per_month = (avg_span_size_kb * spans_per_day as f64 * 30.0) / 1_000_000.0;
        gb_per_month * 0.10
    }
}
````

---

## 8. 生产环境配置

### 8.1 推荐配置

````rust
use opentelemetry::global;
use opentelemetry_sdk::trace::{Config, Sampler, TracerProvider};

pub fn production_sampling() -> anyhow::Result<()> {
    let sampler = PrioritySampler::new(0.1);  // 10% 基础采样

    let provider = TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(sampler)))
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128)
                .with_max_links_per_span(128)
        )
        .build();

    global::set_tracer_provider(provider);
    Ok(())
}
````

### 8.2 环境变量

````bash
# .env
OTEL_TRACES_SAMPLER=parentbased_traceidratio
OTEL_TRACES_SAMPLER_ARG=0.1

# 或使用自定义采样器
SAMPLING_STRATEGY=priority
SAMPLING_BASE_RATIO=0.1
SAMPLING_FORCE_SAMPLE_ERRORS=true
SAMPLING_FORCE_SAMPLE_SLOW_THRESHOLD_MS=1000
````

### 8.3 完整示例

````rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, Sampler, TracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;

pub fn init_production_tracing() -> anyhow::Result<()> {
    // 1. 读取环境变量
    let base_ratio = std::env::var("SAMPLING_BASE_RATIO")
        .unwrap_or_else(|_| "0.1".to_string())
        .parse::<f64>()?;

    // 2. 创建采样器
    let sampler = PrioritySampler::new(base_ratio);

    // 3. 创建资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);

    // 4. 创建 OTLP 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(sampler)))
                .with_resource(resource)
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 5. 设置全局 Tracer
    global::set_tracer_provider(tracer.provider().unwrap());

    Ok(())
}
````

---

## 9. 调试采样决策

### 9.1 采样日志

````rust
use tracing::{info, Span};
use opentelemetry::trace::TraceContextExt;

pub fn log_sampling_decision() {
    let span = Span::current();
    let context = span.context();
    let span_context = context.span().span_context();

    let is_sampled = span_context.is_sampled();
    let trace_id = span_context.trace_id();

    info!(
        trace_id = %trace_id,
        is_sampled = is_sampled,
        "Sampling decision"
    );
}
````

### 9.2 Jaeger 采样标记

```bash
# 查询采样的 Trace
curl "http://localhost:16686/api/traces?service=my-service&tags={\"sampled\":\"true\"}"

# 查询未采样的 Trace（需要配置 RecordOnly）
curl "http://localhost:16686/api/traces?service=my-service&tags={\"sampled\":\"false\"}"
```

---

## 10. Rust 1.90 特性应用

### 10.1 AFIT 在采样器

````rust
// Rust 1.90: async fn in Traits (AFIT)
pub trait AsyncSampler {
    async fn should_sample_async(
        &self,
        trace_id: opentelemetry::trace::TraceId,
        attributes: &[opentelemetry::KeyValue],
    ) -> bool;
}

pub struct DatabaseSampler {
    pool: sqlx::PgPool,
}

impl AsyncSampler for DatabaseSampler {
    async fn should_sample_async(
        &self,
        trace_id: opentelemetry::trace::TraceId,
        attributes: &[opentelemetry::KeyValue],
    ) -> bool {
        // 从数据库查询采样规则
        let result = sqlx::query_scalar::<_, bool>(
            "SELECT should_sample FROM sampling_rules WHERE trace_id = $1"
        )
        .bind(trace_id.to_string())
        .fetch_optional(&self.pool)
        .await;

        result.unwrap_or(false)
    }
}
````

### 10.2 零成本抽象

````rust
// 编译时采样决策
macro_rules! sample_span {
    ($name:expr, $ratio:expr) => {
        if (rand::random::<f64>() < $ratio) {
            tracing::info_span!($name)
        } else {
            tracing::Span::none()
        }
    };
}

pub fn optimized_sampling() {
    let span = sample_span!("my_operation", 0.1);
    let _enter = span.enter();
    // 业务逻辑...
}
````

---

## 总结

### 核心要点

1. **头部采样 vs 尾部采样**: 头部快但盲目，尾部智能但昂贵
2. **TraceIdRatioBased**: 确保同一 Trace 在所有服务中采样一致
3. **ParentBased**: 尊重上游采样决策，避免不完整 Trace
4. **强制采样**: 错误、慢请求、高优先级请求总是采样
5. **自适应采样**: 根据流量、资源使用动态调整
6. **采样与成本**: 10% 采样率可降低 90% 存储成本

### 推荐采样率

| 场景 | 采样率 | 说明 |
|------|--------|------|
| 开发环境 | 100% | AlwaysOn |
| 测试环境 | 50% | 保留足够样本 |
| 预生产环境 | 20% | 模拟生产 |
| 生产环境（低流量） | 50% | < 1k req/s |
| 生产环境（中流量） | 10% | 1k-10k req/s |
| 生产环境（高流量） | 1% | > 10k req/s |
| 健康检查端点 | 0.1% | 高频低价值 |
| 支付端点 | 100% | 关键业务 |

### 最佳实践清单

- ✅ 使用 `ParentBased` 确保跨服务一致性
- ✅ 错误和慢请求总是采样
- ✅ 健康检查端点使用极低采样率 (0.1%)
- ✅ 关键业务端点使用高采样率 (50-100%)
- ✅ 监控实际采样率和存储成本
- ✅ 使用尾部采样 (Collector) 实现智能决策
- ✅ 考虑自适应采样应对流量突增
- ✅ 使用 Span Links 关联未采样的 Span
- ✅ 记录采样决策日志便于调试
- ✅ 定期评估和调整采样策略

---

**相关文档**:

- [性能优化指南](./01_Rust_1.90_性能优化完整指南.md)
- [分布式追踪进阶](../02_Semantic_Conventions/03_日志与事件/02_分布式追踪进阶_Rust完整版.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
- [故障排查指南](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
