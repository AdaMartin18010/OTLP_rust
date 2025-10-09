# 采样策略与优化 - Rust 完整版

## 目录

- [采样策略与优化 - Rust 完整版](#采样策略与优化---rust-完整版)
  - [目录](#目录)
  - [1. 采样概述](#1-采样概述)
    - [1.1 为什么需要采样](#11-为什么需要采样)
    - [1.2 采样决策点](#12-采样决策点)
    - [1.3 采样器接口](#13-采样器接口)
  - [2. 固定采样策略](#2-固定采样策略)
    - [2.1 AlwaysOn / AlwaysOff](#21-alwayson--alwaysoff)
    - [2.2 TraceIdRatioBased（按比例采样）](#22-traceidratiobased按比例采样)
    - [2.3 ParentBased（继承父 Span 决策）](#23-parentbased继承父-span-决策)
  - [3. 自适应采样](#3-自适应采样)
    - [3.1 基于负载的自适应采样](#31-基于负载的自适应采样)
  - [4. 尾部采样](#4-尾部采样)
    - [4.1 尾部采样器架构](#41-尾部采样器架构)
    - [4.2 尾部采样策略](#42-尾部采样策略)
  - [5. 优先级采样](#5-优先级采样)
    - [5.1 优先级采样器](#51-优先级采样器)
  - [6. 分布式采样决策](#6-分布式采样决策)
    - [6.1 采样决策传播](#61-采样决策传播)
  - [7. 完整示例](#7-完整示例)
    - [7.1 综合采样策略](#71-综合采样策略)
  - [总结](#总结)

---

## 1. 采样概述

**采样（Sampling）** 是控制数据量的关键手段，在保留关键信息的同时降低存储和传输成本。

### 1.1 为什么需要采样

```text
问题：
- 高流量系统每秒产生数百万 Span
- 存储成本高昂
- 网络带宽有限
- 查询性能下降

解决方案：
- 智能采样：保留有价值的 Trace，丢弃冗余数据
- 目标：95%+ 的重要 Trace 被保留
```

### 1.2 采样决策点

```text
┌──────────────┐
│  应用程序     │ ← Head Sampling (头部采样)
└──────┬───────┘
       │
       ↓
┌──────────────┐
│  Collector   │ ← Tail Sampling (尾部采样)
└──────┬───────┘
       │
       ↓
┌──────────────┐
│  后端存储     │
└──────────────┘
```

### 1.3 采样器接口

```rust
use async_trait::async_trait;
use opentelemetry::trace::{TraceId, SpanId, TraceFlags};
use opentelemetry_sdk::export::trace::SpanData;

#[derive(Debug, Clone, PartialEq)]
pub enum SamplingDecision {
    /// 丢弃 Span
    Drop,
    /// 记录但不导出
    RecordOnly,
    /// 记录并导出
    RecordAndSample,
}

#[derive(Debug, Clone)]
pub struct SamplingResult {
    pub decision: SamplingDecision,
    pub attributes: Vec<(String, String)>,
    pub trace_state: String,
}

#[async_trait]
pub trait Sampler: Send + Sync {
    /// 做出采样决策
    async fn should_sample(
        &self,
        parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        name: &str,
        span_kind: SpanKind,
        attributes: &[(String, String)],
        links: &[SpanLink],
    ) -> SamplingResult;
    
    /// 获取描述
    fn description(&self) -> String;
}

#[derive(Debug)]
pub struct TraceContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub trace_flags: TraceFlags,
    pub is_remote: bool,
}
```

---

## 2. 固定采样策略

### 2.1 AlwaysOn / AlwaysOff

```rust
pub struct AlwaysOnSampler;

#[async_trait]
impl Sampler for AlwaysOnSampler {
    async fn should_sample(
        &self,
        _parent_context: Option<&TraceContext>,
        _trace_id: TraceId,
        _name: &str,
        _span_kind: SpanKind,
        _attributes: &[(String, String)],
        _links: &[SpanLink],
    ) -> SamplingResult {
        SamplingResult {
            decision: SamplingDecision::RecordAndSample,
            attributes: vec![],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        "AlwaysOnSampler".to_string()
    }
}

pub struct AlwaysOffSampler;

#[async_trait]
impl Sampler for AlwaysOffSampler {
    async fn should_sample(
        &self,
        _parent_context: Option<&TraceContext>,
        _trace_id: TraceId,
        _name: &str,
        _span_kind: SpanKind,
        _attributes: &[(String, String)],
        _links: &[SpanLink],
    ) -> SamplingResult {
        SamplingResult {
            decision: SamplingDecision::Drop,
            attributes: vec![],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        "AlwaysOffSampler".to_string()
    }
}
```

### 2.2 TraceIdRatioBased（按比例采样）

```rust
pub struct TraceIdRatioBasedSampler {
    ratio: f64,
    threshold: u64,
}

impl TraceIdRatioBasedSampler {
    pub fn new(ratio: f64) -> Self {
        assert!(ratio >= 0.0 && ratio <= 1.0, "Ratio must be between 0.0 and 1.0");
        
        let threshold = (ratio * (u64::MAX as f64)) as u64;
        
        Self { ratio, threshold }
    }
    
    fn should_sample_trace_id(&self, trace_id: TraceId) -> bool {
        // 使用 TraceID 的低 8 字节作为随机源
        let bytes = trace_id.to_bytes();
        let lower_64 = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        lower_64 < self.threshold
    }
}

#[async_trait]
impl Sampler for TraceIdRatioBasedSampler {
    async fn should_sample(
        &self,
        _parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: SpanKind,
        _attributes: &[(String, String)],
        _links: &[SpanLink],
    ) -> SamplingResult {
        let decision = if self.should_sample_trace_id(trace_id) {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            attributes: vec![("sampling.ratio".to_string(), self.ratio.to_string())],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        format!("TraceIdRatioBasedSampler{{{}}}", self.ratio)
    }
}
```

### 2.3 ParentBased（继承父 Span 决策）

```rust
pub struct ParentBasedSampler {
    root_sampler: Arc<dyn Sampler>,
    remote_parent_sampled: Arc<dyn Sampler>,
    remote_parent_not_sampled: Arc<dyn Sampler>,
    local_parent_sampled: Arc<dyn Sampler>,
    local_parent_not_sampled: Arc<dyn Sampler>,
}

impl ParentBasedSampler {
    pub fn new(root_sampler: Arc<dyn Sampler>) -> Self {
        let always_on = Arc::new(AlwaysOnSampler);
        let always_off = Arc::new(AlwaysOffSampler);
        
        Self {
            root_sampler,
            remote_parent_sampled: always_on.clone(),
            remote_parent_not_sampled: always_off.clone(),
            local_parent_sampled: always_on.clone(),
            local_parent_not_sampled: always_off.clone(),
        }
    }
}

#[async_trait]
impl Sampler for ParentBasedSampler {
    async fn should_sample(
        &self,
        parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        name: &str,
        span_kind: SpanKind,
        attributes: &[(String, String)],
        links: &[SpanLink],
    ) -> SamplingResult {
        match parent_context {
            None => {
                // 根 Span，使用 root_sampler
                self.root_sampler.should_sample(
                    None, trace_id, name, span_kind, attributes, links
                ).await
            }
            Some(parent) => {
                let sampler = if parent.trace_flags.is_sampled() {
                    if parent.is_remote {
                        &self.remote_parent_sampled
                    } else {
                        &self.local_parent_sampled
                    }
                } else {
                    if parent.is_remote {
                        &self.remote_parent_not_sampled
                    } else {
                        &self.local_parent_not_sampled
                    }
                };
                
                sampler.should_sample(
                    Some(parent), trace_id, name, span_kind, attributes, links
                ).await
            }
        }
    }
    
    fn description(&self) -> String {
        format!("ParentBased{{{}}}", self.root_sampler.description())
    }
}
```

---

## 3. 自适应采样

根据系统负载动态调整采样率。

### 3.1 基于负载的自适应采样

```rust
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::time::interval;

pub struct AdaptiveSampler {
    /// 当前采样率（0-100）
    current_rate: Arc<AtomicUsize>,
    /// 目标吞吐量（Spans/秒）
    target_throughput: usize,
    /// 当前吞吐量计数器
    current_count: Arc<AtomicU64>,
    /// 上次调整时间
    last_adjustment: Arc<tokio::sync::Mutex<Instant>>,
}

impl AdaptiveSampler {
    pub fn new(target_throughput: usize) -> Self {
        let sampler = Self {
            current_rate: Arc::new(AtomicUsize::new(100)),
            target_throughput,
            current_count: Arc::new(AtomicU64::new(0)),
            last_adjustment: Arc::new(tokio::sync::Mutex::new(Instant::now())),
        };
        
        // 启动自适应调整任务
        sampler.start_adjustment_loop();
        
        sampler
    }
    
    fn start_adjustment_loop(&self) {
        let current_rate = self.current_rate.clone();
        let current_count = self.current_count.clone();
        let target_throughput = self.target_throughput;
        let last_adjustment = self.last_adjustment.clone();
        
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(10));
            
            loop {
                ticker.tick().await;
                
                let mut last = last_adjustment.lock().await;
                let elapsed = last.elapsed().as_secs_f64();
                *last = Instant::now();
                
                let count = current_count.swap(0, Ordering::Relaxed);
                let actual_throughput = (count as f64 / elapsed) as usize;
                
                let rate = current_rate.load(Ordering::Relaxed);
                
                let new_rate = if actual_throughput > target_throughput * 110 / 100 {
                    // 超过目标 10%，降低采样率
                    (rate * 90 / 100).max(1)
                } else if actual_throughput < target_throughput * 90 / 100 {
                    // 低于目标 10%，提高采样率
                    (rate * 110 / 100).min(100)
                } else {
                    rate
                };
                
                if new_rate != rate {
                    current_rate.store(new_rate, Ordering::Relaxed);
                    tracing::info!(
                        "Adaptive sampling rate adjusted: {}% → {}% (throughput: {} spans/s)",
                        rate, new_rate, actual_throughput
                    );
                }
            }
        });
    }
}

#[async_trait]
impl Sampler for AdaptiveSampler {
    async fn should_sample(
        &self,
        _parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: SpanKind,
        _attributes: &[(String, String)],
        _links: &[SpanLink],
    ) -> SamplingResult {
        self.current_count.fetch_add(1, Ordering::Relaxed);
        
        let rate = self.current_rate.load(Ordering::Relaxed);
        let ratio = rate as f64 / 100.0;
        
        let bytes = trace_id.to_bytes();
        let lower_64 = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        let threshold = (ratio * (u64::MAX as f64)) as u64;
        
        let decision = if lower_64 < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            attributes: vec![("sampling.rate".to_string(), rate.to_string())],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        format!(
            "AdaptiveSampler{{rate={}%, target={} spans/s}}",
            self.current_rate.load(Ordering::Relaxed),
            self.target_throughput
        )
    }
}
```

---

## 4. 尾部采样

在 Trace 完成后，基于完整信息做出采样决策。

### 4.1 尾部采样器架构

```rust
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct TailSampler {
    /// 缓存的 Trace（TraceID → Spans）
    trace_buffer: Arc<RwLock<HashMap<TraceId, Vec<SpanData>>>>,
    /// 采样策略
    policies: Vec<Arc<dyn TailSamplingPolicy>>,
    /// 决策延迟
    decision_wait: Duration,
}

#[async_trait]
pub trait TailSamplingPolicy: Send + Sync {
    /// 评估 Trace 是否应该被采样
    async fn evaluate(&self, trace: &[SpanData]) -> bool;
    
    fn name(&self) -> &str;
}

impl TailSampler {
    pub fn new(
        policies: Vec<Arc<dyn TailSamplingPolicy>>,
        decision_wait: Duration,
    ) -> Self {
        let sampler = Self {
            trace_buffer: Arc::new(RwLock::new(HashMap::new())),
            policies,
            decision_wait,
        };
        
        // 启动决策循环
        sampler.start_decision_loop();
        
        sampler
    }
    
    pub async fn add_span(&self, span: SpanData) {
        let trace_id = span.span_context.trace_id();
        
        let mut buffer = self.trace_buffer.write().await;
        buffer.entry(trace_id).or_insert_with(Vec::new).push(span);
    }
    
    fn start_decision_loop(&self) {
        let trace_buffer = self.trace_buffer.clone();
        let policies = self.policies.clone();
        let decision_wait = self.decision_wait;
        
        tokio::spawn(async move {
            let mut ticker = interval(decision_wait);
            
            loop {
                ticker.tick().await;
                
                let mut buffer = trace_buffer.write().await;
                let mut to_remove = Vec::new();
                
                for (trace_id, spans) in buffer.iter() {
                    // 检查 Trace 是否完成（所有 Span 已接收）
                    if Self::is_trace_complete(spans) {
                        let should_sample = Self::evaluate_policies(&policies, spans).await;
                        
                        if should_sample {
                            // 导出 Trace
                            tracing::info!("Tail sampling: keeping trace {:?}", trace_id);
                            // TODO: 发送到 Exporter
                        } else {
                            tracing::debug!("Tail sampling: dropping trace {:?}", trace_id);
                        }
                        
                        to_remove.push(*trace_id);
                    }
                }
                
                for trace_id in to_remove {
                    buffer.remove(&trace_id);
                }
            }
        });
    }
    
    fn is_trace_complete(spans: &[SpanData]) -> bool {
        // 简化逻辑：假设等待时间后 Trace 完成
        // 实际应检查根 Span 是否结束
        !spans.is_empty()
    }
    
    async fn evaluate_policies(
        policies: &[Arc<dyn TailSamplingPolicy>],
        spans: &[SpanData],
    ) -> bool {
        for policy in policies {
            if policy.evaluate(spans).await {
                return true;
            }
        }
        false
    }
}
```

### 4.2 尾部采样策略

```rust
// 错误优先策略
pub struct ErrorPolicy;

#[async_trait]
impl TailSamplingPolicy for ErrorPolicy {
    async fn evaluate(&self, trace: &[SpanData]) -> bool {
        trace.iter().any(|span| {
            span.status.code == opentelemetry::trace::StatusCode::Error
        })
    }
    
    fn name(&self) -> &str {
        "ErrorPolicy"
    }
}

// 慢请求策略
pub struct LatencyPolicy {
    threshold_ms: u64,
}

impl LatencyPolicy {
    pub fn new(threshold_ms: u64) -> Self {
        Self { threshold_ms }
    }
}

#[async_trait]
impl TailSamplingPolicy for LatencyPolicy {
    async fn evaluate(&self, trace: &[SpanData]) -> bool {
        if let Some(root_span) = trace.iter().find(|s| s.parent_span_id == SpanId::INVALID) {
            let duration_ms = (root_span.end_time - root_span.start_time).as_millis() as u64;
            duration_ms > self.threshold_ms
        } else {
            false
        }
    }
    
    fn name(&self) -> &str {
        "LatencyPolicy"
    }
}

// 采样率策略（兜底）
pub struct RatePolicy {
    rate: f64,
}

impl RatePolicy {
    pub fn new(rate: f64) -> Self {
        Self { rate }
    }
}

#[async_trait]
impl TailSamplingPolicy for RatePolicy {
    async fn evaluate(&self, trace: &[SpanData]) -> bool {
        if let Some(root_span) = trace.first() {
            let trace_id = root_span.span_context.trace_id();
            let bytes = trace_id.to_bytes();
            let lower_64 = u64::from_be_bytes([
                bytes[8], bytes[9], bytes[10], bytes[11],
                bytes[12], bytes[13], bytes[14], bytes[15],
            ]);
            
            let threshold = (self.rate * (u64::MAX as f64)) as u64;
            lower_64 < threshold
        } else {
            false
        }
    }
    
    fn name(&self) -> &str {
        "RatePolicy"
    }
}
```

---

## 5. 优先级采样

根据业务价值确定采样优先级。

### 5.1 优先级采样器

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Critical = 100,
    High = 75,
    Normal = 50,
    Low = 25,
}

pub struct PrioritySampler {
    /// 各优先级的采样率
    rates: HashMap<Priority, f64>,
}

impl PrioritySampler {
    pub fn new() -> Self {
        let mut rates = HashMap::new();
        rates.insert(Priority::Critical, 1.0);
        rates.insert(Priority::High, 0.5);
        rates.insert(Priority::Normal, 0.1);
        rates.insert(Priority::Low, 0.01);
        
        Self { rates }
    }
    
    fn extract_priority(&self, attributes: &[(String, String)]) -> Priority {
        attributes
            .iter()
            .find(|(k, _)| k == "priority")
            .and_then(|(_, v)| match v.as_str() {
                "critical" => Some(Priority::Critical),
                "high" => Some(Priority::High),
                "low" => Some(Priority::Low),
                _ => Some(Priority::Normal),
            })
            .unwrap_or(Priority::Normal)
    }
}

#[async_trait]
impl Sampler for PrioritySampler {
    async fn should_sample(
        &self,
        _parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: SpanKind,
        attributes: &[(String, String)],
        _links: &[SpanLink],
    ) -> SamplingResult {
        let priority = self.extract_priority(attributes);
        let rate = self.rates.get(&priority).copied().unwrap_or(0.1);
        
        let bytes = trace_id.to_bytes();
        let lower_64 = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        let threshold = (rate * (u64::MAX as f64)) as u64;
        
        let decision = if lower_64 < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            attributes: vec![
                ("sampling.priority".to_string(), format!("{:?}", priority)),
                ("sampling.rate".to_string(), rate.to_string()),
            ],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        "PrioritySampler".to_string()
    }
}
```

---

## 6. 分布式采样决策

### 6.1 采样决策传播

```rust
use opentelemetry::propagation::{TextMapPropagator, Injector, Extractor};

pub struct SamplingPropagator;

impl TextMapPropagator for SamplingPropagator {
    fn inject_context(&self, cx: &opentelemetry::Context, injector: &mut dyn Injector) {
        let span_context = cx.span().span_context();
        
        if span_context.is_sampled() {
            injector.set("x-sampling-decision", "1");
        } else {
            injector.set("x-sampling-decision", "0");
        }
    }
    
    fn extract_with_context(
        &self,
        cx: &opentelemetry::Context,
        extractor: &dyn Extractor,
    ) -> opentelemetry::Context {
        if let Some(decision) = extractor.get("x-sampling-decision") {
            if decision == "1" {
                // 设置采样标志
                // cx.with_sampled(true)
            }
        }
        cx.clone()
    }
    
    fn fields(&self) -> FieldIter<'_> {
        FieldIter::new(&["x-sampling-decision"])
    }
}
```

---

## 7. 完整示例

### 7.1 综合采样策略

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建头部采样器（应用端）
    let head_sampler = Arc::new(ParentBasedSampler::new(
        Arc::new(TraceIdRatioBasedSampler::new(0.1))
    ));
    
    // 2. 创建尾部采样器（Collector 端）
    let tail_sampler = TailSampler::new(
        vec![
            Arc::new(ErrorPolicy),
            Arc::new(LatencyPolicy::new(1000)),
            Arc::new(RatePolicy::new(0.05)),
        ],
        Duration::from_secs(30),
    );
    
    // 3. 创建自适应采样器
    let adaptive_sampler = Arc::new(AdaptiveSampler::new(10000));
    
    // 4. 创建优先级采样器
    let priority_sampler = Arc::new(PrioritySampler::new());
    
    // 5. 使用组合采样器
    let composite_sampler = CompositeSampler::new(vec![
        priority_sampler,
        adaptive_sampler,
    ]);
    
    println!("Sampling strategy initialized");
    
    Ok(())
}

// 组合采样器
pub struct CompositeSampler {
    samplers: Vec<Arc<dyn Sampler>>,
}

impl CompositeSampler {
    pub fn new(samplers: Vec<Arc<dyn Sampler>>) -> Self {
        Self { samplers }
    }
}

#[async_trait]
impl Sampler for CompositeSampler {
    async fn should_sample(
        &self,
        parent_context: Option<&TraceContext>,
        trace_id: TraceId,
        name: &str,
        span_kind: SpanKind,
        attributes: &[(String, String)],
        links: &[SpanLink],
    ) -> SamplingResult {
        for sampler in &self.samplers {
            let result = sampler.should_sample(
                parent_context, trace_id, name, span_kind, attributes, links
            ).await;
            
            if result.decision == SamplingDecision::RecordAndSample {
                return result;
            }
        }
        
        SamplingResult {
            decision: SamplingDecision::Drop,
            attributes: vec![],
            trace_state: String::new(),
        }
    }
    
    fn description(&self) -> String {
        "CompositeSampler".to_string()
    }
}
```

---

## 总结

采样是 OTLP 系统的**成本优化核心**，Rust 实现时需要考虑：

1. **头部采样**：TraceIdRatioBased、ParentBased
2. **尾部采样**：基于错误、延迟、业务规则
3. **自适应采样**：根据系统负载动态调整
4. **优先级采样**：按业务价值分级
5. **分布式一致性**：通过 Propagator 传播决策

通过多层采样策略组合，可以在保留关键信息的同时，显著降低存储和传输成本。
