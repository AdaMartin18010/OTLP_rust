# 高级采样算法 - Rust完整实现

> **Rust版本**: 1.90+  
> **核心依赖**: tokio 1.47.1, rand 0.8  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [高级采样算法 - Rust完整实现](#高级采样算法---rust完整实现)
  - [📋 目录](#-目录)
  - [1. 采样算法概述](#1-采样算法概述)
    - [1.1 采样类型对比](#11-采样类型对比)
    - [1.2 采样器trait](#12-采样器trait)
  - [2. 固定比例采样](#2-固定比例采样)
    - [2.1 TraceID哈希采样](#21-traceid哈希采样)
    - [2.2 概率采样器](#22-概率采样器)
  - [3. 自适应采样](#3-自适应采样)
    - [3.1 动态速率采样器](#31-动态速率采样器)
    - [3.2 负载感知采样器](#32-负载感知采样器)
  - [4. 尾部采样](#4-尾部采样)
    - [4.1 基于窗口的尾部采样](#41-基于窗口的尾部采样)
  - [5. 优先级采样](#5-优先级采样)
    - [5.1 基于优先级的采样器](#51-基于优先级的采样器)
  - [6. 一致性采样](#6-一致性采样)
    - [6.1 一致性哈希采样器](#61-一致性哈希采样器)
  - [7. 机器学习采样](#7-机器学习采样)
    - [7.1 特征提取](#71-特征提取)
  - [8. 完整实现](#8-完整实现)
    - [8.1 综合采样策略](#81-综合采样策略)
  - [总结](#总结)

---

## 1. 采样算法概述

### 1.1 采样类型对比

```text
┌──────────────────┬────────────┬────────────┬────────────┬────────────┐
│ 采样类型          │  决策时机   │  上下文    │  准确性    │  成本      │
├──────────────────┼────────────┼────────────┼────────────┼────────────┤
│ Head-based       │  Span开始  │  部分      │  中等      │  低        │
│ Tail-based       │  Trace结束 │  完整      │  高        │  高        │
│ Adaptive         │  动态      │  运行时    │  中等      │  中等      │
│ Priority-based   │  Span开始  │  业务规则  │  高        │  中等      │
│ Consistent       │  Span开始  │  TraceID   │  高        │  低        │
│ ML-based         │  动态      │  历史数据  │  很高      │  很高      │
└──────────────────┴────────────┴────────────┴────────────┴────────────┘
```

### 1.2 采样器trait

```rust
use opentelemetry::trace::{SpanId, TraceId, TraceFlags};
use std::sync::Arc;

/// 采样决策
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SamplingDecision {
    /// 采样
    Sample,
    
    /// 不采样
    Drop,
    
    /// 延迟决策(用于尾部采样)
    Defer,
}

/// 采样结果
#[derive(Debug, Clone)]
pub struct SamplingResult {
    pub decision: SamplingDecision,
    pub trace_flags: TraceFlags,
    pub attributes: Vec<(String, AttributeValue)>,
}

/// 采样上下文
#[derive(Debug, Clone)]
pub struct SamplingContext {
    pub trace_id: TraceId,
    pub parent_span_id: Option<SpanId>,
    pub name: String,
    pub kind: SpanKind,
    pub attributes: Vec<(String, AttributeValue)>,
    pub parent_sampled: Option<bool>,
}

/// 采样器trait
#[async_trait::async_trait]
pub trait Sampler: Send + Sync {
    /// 采样决策
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult;
    
    /// 采样器描述
    fn description(&self) -> String;
}

use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Int(i64),
    Double(f64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    Internal,
    Server,
    Client,
    Producer,
    Consumer,
}
```

---

## 2. 固定比例采样

### 2.1 TraceID哈希采样

```rust
/// TraceID哈希采样器
pub struct TraceIdRatioSampler {
    /// 采样率 (0.0 - 1.0)
    sampling_rate: f64,
    
    /// 阈值 (用于快速比较)
    threshold: u64,
    
    /// 描述
    description: String,
}

impl TraceIdRatioSampler {
    pub fn new(sampling_rate: f64) -> Self {
        assert!((0.0..=1.0).contains(&sampling_rate), "Sampling rate must be between 0.0 and 1.0");
        
        let threshold = (sampling_rate * u64::MAX as f64) as u64;
        
        Self {
            sampling_rate,
            threshold,
            description: format!("TraceIdRatioSampler({})", sampling_rate),
        }
    }
    
    /// 从TraceID计算哈希
    fn hash_trace_id(&self, trace_id: &TraceId) -> u64 {
        let bytes = trace_id.to_bytes();
        
        // 使用低64位作为哈希
        let mut hash = 0u64;
        for i in 0..8 {
            hash = (hash << 8) | bytes[i + 8] as u64;
        }
        
        hash
    }
}

#[async_trait::async_trait]
impl Sampler for TraceIdRatioSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        let hash = self.hash_trace_id(&ctx.trace_id);
        
        let decision = if hash < self.threshold {
            SamplingDecision::Sample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            trace_flags: if decision == SamplingDecision::Sample {
                TraceFlags::SAMPLED
            } else {
                TraceFlags::default()
            },
            attributes: vec![],
        }
    }
    
    fn description(&self) -> String {
        self.description.clone()
    }
}
```

### 2.2 概率采样器

```rust
use rand::Rng;

/// 概率采样器
pub struct ProbabilitySampler {
    /// 采样率
    sampling_rate: f64,
    
    /// 随机数生成器
    rng: Arc<Mutex<rand::rngs::ThreadRng>>,
}

impl ProbabilitySampler {
    pub fn new(sampling_rate: f64) -> Self {
        Self {
            sampling_rate,
            rng: Arc::new(Mutex::new(rand::thread_rng())),
        }
    }
}

#[async_trait::async_trait]
impl Sampler for ProbabilitySampler {
    async fn should_sample(&self, _ctx: &SamplingContext) -> SamplingResult {
        let mut rng = self.rng.lock().await;
        let random: f64 = rng.gen();
        
        let decision = if random < self.sampling_rate {
            SamplingDecision::Sample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            trace_flags: if decision == SamplingDecision::Sample {
                TraceFlags::SAMPLED
            } else {
                TraceFlags::default()
            },
            attributes: vec![],
        }
    }
    
    fn description(&self) -> String {
        format!("ProbabilitySampler({})", self.sampling_rate)
    }
}
```

---

## 3. 自适应采样

### 3.1 动态速率采样器

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 动态速率采样器
pub struct DynamicRateSampler {
    /// 目标QPS
    target_qps: Arc<AtomicU64>,
    
    /// 当前采样率
    current_rate: Arc<RwLock<f64>>,
    
    /// 统计窗口
    stats: Arc<RwLock<SamplingStats>>,
    
    /// 调整间隔
    adjustment_interval: Duration,
}

#[derive(Debug, Default)]
struct SamplingStats {
    /// 窗口内的span数
    span_count: u64,
    
    /// 窗口内采样的span数
    sampled_count: u64,
    
    /// 窗口开始时间
    window_start: Option<Instant>,
}

impl DynamicRateSampler {
    pub fn new(initial_rate: f64, target_qps: u64) -> Arc<Self> {
        let sampler = Arc::new(Self {
            target_qps: Arc::new(AtomicU64::new(target_qps)),
            current_rate: Arc::new(RwLock::new(initial_rate)),
            stats: Arc::new(RwLock::new(SamplingStats::default())),
            adjustment_interval: Duration::from_secs(10),
        });
        
        // 启动自适应调整
        let sampler_clone = Arc::clone(&sampler);
        tokio::spawn(async move {
            sampler_clone.adjust_sampling_rate_loop().await;
        });
        
        sampler
    }
    
    /// 自适应调整循环
    async fn adjust_sampling_rate_loop(&self) {
        let mut ticker = tokio::time::interval(self.adjustment_interval);
        
        loop {
            ticker.tick().await;
            
            self.adjust_sampling_rate().await;
        }
    }
    
    /// 调整采样率
    async fn adjust_sampling_rate(&self) {
        let mut stats = self.stats.write().await;
        
        if let Some(window_start) = stats.window_start {
            let elapsed = window_start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64();
            
            if elapsed_secs > 0.0 {
                // 计算当前QPS
                let current_qps = stats.sampled_count as f64 / elapsed_secs;
                let target_qps = self.target_qps.load(Ordering::Relaxed) as f64;
                
                // 计算新的采样率
                let mut current_rate = self.current_rate.write().await;
                let adjustment_factor = target_qps / current_qps.max(1.0);
                let new_rate = (*current_rate * adjustment_factor).clamp(0.001, 1.0);
                
                tracing::info!(
                    "Adjusting sampling rate: {:.4} -> {:.4} (current_qps={:.2}, target_qps={:.2})",
                    *current_rate,
                    new_rate,
                    current_qps,
                    target_qps
                );
                
                *current_rate = new_rate;
            }
            
            // 重置统计
            stats.span_count = 0;
            stats.sampled_count = 0;
            stats.window_start = Some(Instant::now());
        } else {
            stats.window_start = Some(Instant::now());
        }
    }
    
    /// 更新统计
    async fn record_decision(&self, sampled: bool) {
        let mut stats = self.stats.write().await;
        stats.span_count += 1;
        if sampled {
            stats.sampled_count += 1;
        }
    }
}

#[async_trait::async_trait]
impl Sampler for DynamicRateSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        let current_rate = *self.current_rate.read().await;
        
        // 使用TraceID哈希决策
        let trace_id_sampler = TraceIdRatioSampler::new(current_rate);
        let result = trace_id_sampler.should_sample(ctx).await;
        
        // 记录统计
        self.record_decision(result.decision == SamplingDecision::Sample).await;
        
        result
    }
    
    fn description(&self) -> String {
        "DynamicRateSampler".to_string()
    }
}
```

### 3.2 负载感知采样器

```rust
/// 负载感知采样器
pub struct LoadAwareSampler {
    /// 基础采样率
    base_rate: f64,
    
    /// 当前采样率
    current_rate: Arc<RwLock<f64>>,
    
    /// 负载监控器
    load_monitor: Arc<LocalLoadMonitor>,
    
    /// 降级阈值
    degradation_thresholds: DegradationThresholds,
}

#[derive(Debug, Clone)]
pub struct DegradationThresholds {
    pub cpu_warning: f64,
    pub cpu_critical: f64,
    pub memory_warning: f64,
    pub memory_critical: f64,
}

impl LoadAwareSampler {
    pub fn new(
        base_rate: f64,
        load_monitor: Arc<LocalLoadMonitor>,
        thresholds: DegradationThresholds,
    ) -> Arc<Self> {
        let sampler = Arc::new(Self {
            base_rate,
            current_rate: Arc::new(RwLock::new(base_rate)),
            load_monitor,
            degradation_thresholds: thresholds,
        });
        
        // 启动负载监控
        let sampler_clone = Arc::clone(&sampler);
        tokio::spawn(async move {
            sampler_clone.monitor_load_loop().await;
        });
        
        sampler
    }
    
    /// 负载监控循环
    async fn monitor_load_loop(&self) {
        let mut ticker = tokio::time::interval(Duration::from_secs(5));
        
        loop {
            ticker.tick().await;
            
            self.adjust_rate_based_on_load().await;
        }
    }
    
    /// 根据负载调整采样率
    async fn adjust_rate_based_on_load(&self) {
        let load = self.load_monitor.get_current_load().await;
        
        // 计算降级因子
        let cpu_factor = self.calculate_degradation_factor(
            load.cpu_usage,
            self.degradation_thresholds.cpu_warning,
            self.degradation_thresholds.cpu_critical,
        );
        
        let memory_factor = self.calculate_degradation_factor(
            load.memory_usage,
            self.degradation_thresholds.memory_warning,
            self.degradation_thresholds.memory_critical,
        );
        
        // 使用最小因子
        let degradation_factor = cpu_factor.min(memory_factor);
        
        let new_rate = self.base_rate * degradation_factor;
        
        let mut current_rate = self.current_rate.write().await;
        if (*current_rate - new_rate).abs() > 0.01 {
            tracing::info!(
                "Load-aware rate adjustment: {:.4} -> {:.4} (CPU={:.2}%, MEM={:.2}%)",
                *current_rate,
                new_rate,
                load.cpu_usage,
                load.memory_usage
            );
            *current_rate = new_rate;
        }
    }
    
    /// 计算降级因子
    fn calculate_degradation_factor(&self, current: f64, warning: f64, critical: f64) -> f64 {
        if current < warning {
            1.0
        } else if current < critical {
            // 线性降级
            1.0 - (current - warning) / (critical - warning) * 0.9
        } else {
            0.1 // 最小10%
        }
    }
}

#[async_trait::async_trait]
impl Sampler for LoadAwareSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        let current_rate = *self.current_rate.read().await;
        
        let trace_id_sampler = TraceIdRatioSampler::new(current_rate);
        trace_id_sampler.should_sample(ctx).await
    }
    
    fn description(&self) -> String {
        "LoadAwareSampler".to_string()
    }
}

// 简化的负载监控器
use tokio::sync::Mutex;
use std::collections::HashMap;

pub struct LocalLoadMonitor {
    current_load: Arc<Mutex<Load>>,
}

#[derive(Debug, Clone, Default)]
pub struct Load {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub qps: u64,
    pub bps: u64,
    pub queue_depth: u64,
    pub error_rate: f64,
    pub avg_latency_ms: f64,
}

impl LocalLoadMonitor {
    pub fn new(_history_size: usize) -> Self {
        Self {
            current_load: Arc::new(Mutex::new(Load::default())),
        }
    }
    
    pub async fn get_current_load(&self) -> Load {
        self.current_load.lock().await.clone()
    }
}
```

---

## 4. 尾部采样

### 4.1 基于窗口的尾部采样

```rust
use std::collections::VecDeque;

/// 尾部采样器
pub struct TailSampler {
    /// 完整的trace缓存
    trace_cache: Arc<RwLock<HashMap<TraceId, CachedTrace>>>,
    
    /// 采样规则
    rules: Arc<Vec<TailSamplingRule>>,
    
    /// 缓存超时
    cache_timeout: Duration,
    
    /// 最大缓存大小
    max_cache_size: usize,
}

/// 缓存的Trace
#[derive(Debug, Clone)]
struct CachedTrace {
    trace_id: TraceId,
    spans: Vec<CachedSpan>,
    first_seen: Instant,
    is_complete: bool,
}

#[derive(Debug, Clone)]
struct CachedSpan {
    span_id: SpanId,
    name: String,
    kind: SpanKind,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, AttributeValue>,
    status: SpanStatus,
}

#[derive(Debug, Clone)]
struct SpanStatus {
    code: StatusCode,
    message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StatusCode {
    Ok,
    Error,
}

/// 尾部采样规则
#[derive(Debug, Clone)]
pub enum TailSamplingRule {
    /// 所有错误trace
    AllErrors,
    
    /// 慢trace
    SlowTraces { threshold_ms: u64 },
    
    /// 特定服务
    SpecificService { service_name: String },
    
    /// 采样率
    SampleRate { rate: f64 },
    
    /// 复合规则
    Composite { rules: Vec<TailSamplingRule>, operator: RuleOperator },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleOperator {
    And,
    Or,
}

impl TailSampler {
    pub fn new(
        rules: Vec<TailSamplingRule>,
        cache_timeout: Duration,
        max_cache_size: usize,
    ) -> Arc<Self> {
        let sampler = Arc::new(Self {
            trace_cache: Arc::new(RwLock::new(HashMap::new())),
            rules: Arc::new(rules),
            cache_timeout,
            max_cache_size,
        });
        
        // 启动缓存清理
        let sampler_clone = Arc::clone(&sampler);
        tokio::spawn(async move {
            sampler_clone.cleanup_loop().await;
        });
        
        // 启动采样决策
        let sampler_clone = Arc::clone(&sampler);
        tokio::spawn(async move {
            sampler_clone.sampling_decision_loop().await;
        });
        
        sampler
    }
    
    /// 添加span到缓存
    pub async fn add_span(&self, span: CachedSpan, trace_id: TraceId) {
        let mut cache = self.trace_cache.write().await;
        
        // 检查缓存大小
        if cache.len() >= self.max_cache_size {
            // 移除最老的trace
            if let Some(oldest_trace_id) = cache.iter()
                .min_by_key(|(_, trace)| trace.first_seen)
                .map(|(id, _)| *id)
            {
                cache.remove(&oldest_trace_id);
            }
        }
        
        cache.entry(trace_id)
            .or_insert_with(|| CachedTrace {
                trace_id,
                spans: Vec::new(),
                first_seen: Instant::now(),
                is_complete: false,
            })
            .spans.push(span);
    }
    
    /// 标记trace为完成
    pub async fn mark_complete(&self, trace_id: TraceId) {
        let mut cache = self.trace_cache.write().await;
        if let Some(trace) = cache.get_mut(&trace_id) {
            trace.is_complete = true;
        }
    }
    
    /// 采样决策循环
    async fn sampling_decision_loop(&self) {
        let mut ticker = tokio::time::interval(Duration::from_millis(100));
        
        loop {
            ticker.tick().await;
            
            let mut cache = self.trace_cache.write().await;
            let mut to_remove = Vec::new();
            
            for (trace_id, trace) in cache.iter() {
                if trace.is_complete || trace.first_seen.elapsed() > self.cache_timeout {
                    // 执行采样决策
                    let should_sample = self.evaluate_rules(trace).await;
                    
                    if should_sample {
                        tracing::debug!("Tail sampling: keeping trace {:?}", trace_id);
                        // 实际应该导出trace
                    } else {
                        tracing::debug!("Tail sampling: dropping trace {:?}", trace_id);
                    }
                    
                    to_remove.push(*trace_id);
                }
            }
            
            for trace_id in to_remove {
                cache.remove(&trace_id);
            }
        }
    }
    
    /// 评估规则
    async fn evaluate_rules(&self, trace: &CachedTrace) -> bool {
        for rule in self.rules.iter() {
            if self.evaluate_rule(rule, trace).await {
                return true;
            }
        }
        false
    }
    
    /// 评估单个规则
    async fn evaluate_rule(&self, rule: &TailSamplingRule, trace: &CachedTrace) -> bool {
        match rule {
            TailSamplingRule::AllErrors => {
                trace.spans.iter().any(|span| span.status.code == StatusCode::Error)
            }
            
            TailSamplingRule::SlowTraces { threshold_ms } => {
                if let Some(duration) = self.calculate_trace_duration(trace) {
                    duration > *threshold_ms
                } else {
                    false
                }
            }
            
            TailSamplingRule::SpecificService { service_name } => {
                trace.spans.iter().any(|span| {
                    span.attributes.get("service.name")
                        .and_then(|v| match v {
                            AttributeValue::String(s) => Some(s == service_name),
                            _ => None,
                        })
                        .unwrap_or(false)
                })
            }
            
            TailSamplingRule::SampleRate { rate } => {
                let trace_id_sampler = TraceIdRatioSampler::new(*rate);
                let ctx = SamplingContext {
                    trace_id: trace.trace_id,
                    parent_span_id: None,
                    name: "".to_string(),
                    kind: SpanKind::Internal,
                    attributes: vec![],
                    parent_sampled: None,
                };
                
                let result = trace_id_sampler.should_sample(&ctx).await;
                result.decision == SamplingDecision::Sample
            }
            
            TailSamplingRule::Composite { rules, operator } => {
                match operator {
                    RuleOperator::And => {
                        for rule in rules {
                            if !self.evaluate_rule(rule, trace).await {
                                return false;
                            }
                        }
                        true
                    }
                    RuleOperator::Or => {
                        for rule in rules {
                            if self.evaluate_rule(rule, trace).await {
                                return true;
                            }
                        }
                        false
                    }
                }
            }
        }
    }
    
    /// 计算trace持续时间
    fn calculate_trace_duration(&self, trace: &CachedTrace) -> Option<u64> {
        if trace.spans.is_empty() {
            return None;
        }
        
        let min_start = trace.spans.iter().map(|s| s.start_time).min()?;
        let max_end = trace.spans.iter().map(|s| s.end_time).max()?;
        
        Some((max_end - min_start) / 1_000_000) // 转换为毫秒
    }
    
    /// 缓存清理循环
    async fn cleanup_loop(&self) {
        let mut ticker = tokio::time::interval(Duration::from_secs(60));
        
        loop {
            ticker.tick().await;
            
            let mut cache = self.trace_cache.write().await;
            cache.retain(|_, trace| {
                trace.first_seen.elapsed() < self.cache_timeout * 2
            });
            
            tracing::debug!("Cache size after cleanup: {}", cache.len());
        }
    }
}
```

---

## 5. 优先级采样

### 5.1 基于优先级的采样器

```rust
/// 优先级采样器
pub struct PrioritySampler {
    /// 优先级规则
    priority_rules: Arc<Vec<PriorityRule>>,
    
    /// 默认采样率
    default_rate: f64,
}

/// 优先级规则
#[derive(Debug, Clone)]
pub struct PriorityRule {
    /// 优先级
    pub priority: Priority,
    
    /// 匹配条件
    pub condition: RuleCondition,
    
    /// 采样率
    pub sampling_rate: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Critical = 3,
    High = 2,
    Normal = 1,
    Low = 0,
}

#[derive(Debug, Clone)]
pub enum RuleCondition {
    /// 服务名匹配
    ServiceName(String),
    
    /// 操作名匹配
    OperationName(String),
    
    /// 属性匹配
    Attribute { key: String, value: AttributeValue },
    
    /// Span类型
    SpanKind(SpanKind),
    
    /// 复合条件
    Composite {
        conditions: Vec<RuleCondition>,
        operator: RuleOperator,
    },
}

impl PrioritySampler {
    pub fn new(priority_rules: Vec<PriorityRule>, default_rate: f64) -> Self {
        // 按优先级排序规则
        let mut rules = priority_rules;
        rules.sort_by(|a, b| b.priority.cmp(&a.priority));
        
        Self {
            priority_rules: Arc::new(rules),
            default_rate,
        }
    }
    
    /// 匹配规则
    fn match_rule(&self, ctx: &SamplingContext) -> Option<&PriorityRule> {
        for rule in self.priority_rules.iter() {
            if self.evaluate_condition(&rule.condition, ctx) {
                return Some(rule);
            }
        }
        None
    }
    
    /// 评估条件
    fn evaluate_condition(&self, condition: &RuleCondition, ctx: &SamplingContext) -> bool {
        match condition {
            RuleCondition::ServiceName(name) => {
                ctx.attributes.iter().any(|(k, v)| {
                    k == "service.name" && matches!(v, AttributeValue::String(s) if s == name)
                })
            }
            
            RuleCondition::OperationName(name) => {
                &ctx.name == name
            }
            
            RuleCondition::Attribute { key, value } => {
                ctx.attributes.iter().any(|(k, v)| {
                    k == key && self.match_attribute_value(v, value)
                })
            }
            
            RuleCondition::SpanKind(kind) => {
                ctx.kind == *kind
            }
            
            RuleCondition::Composite { conditions, operator } => {
                match operator {
                    RuleOperator::And => {
                        conditions.iter().all(|c| self.evaluate_condition(c, ctx))
                    }
                    RuleOperator::Or => {
                        conditions.iter().any(|c| self.evaluate_condition(c, ctx))
                    }
                }
            }
        }
    }
    
    fn match_attribute_value(&self, actual: &AttributeValue, expected: &AttributeValue) -> bool {
        match (actual, expected) {
            (AttributeValue::String(a), AttributeValue::String(e)) => a == e,
            (AttributeValue::Int(a), AttributeValue::Int(e)) => a == e,
            (AttributeValue::Double(a), AttributeValue::Double(e)) => (a - e).abs() < f64::EPSILON,
            (AttributeValue::Bool(a), AttributeValue::Bool(e)) => a == e,
            _ => false,
        }
    }
}

#[async_trait::async_trait]
impl Sampler for PrioritySampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        let sampling_rate = if let Some(rule) = self.match_rule(ctx) {
            tracing::debug!(
                "Matched priority rule: priority={:?}, rate={}",
                rule.priority,
                rule.sampling_rate
            );
            rule.sampling_rate
        } else {
            self.default_rate
        };
        
        let trace_id_sampler = TraceIdRatioSampler::new(sampling_rate);
        trace_id_sampler.should_sample(ctx).await
    }
    
    fn description(&self) -> String {
        "PrioritySampler".to_string()
    }
}
```

---

## 6. 一致性采样

### 6.1 一致性哈希采样器

```rust
use std::collections::BTreeMap;

/// 一致性采样器
pub struct ConsistentSampler {
    /// 采样率
    sampling_rate: f64,
    
    /// 一致性哈希环
    hash_ring: Arc<RwLock<ConsistentHashRing>>,
}

/// 一致性哈希环
struct ConsistentHashRing {
    /// 虚拟节点数
    virtual_nodes: usize,
    
    /// 哈希环
    ring: BTreeMap<u64, String>,
    
    /// 节点采样率
    node_rates: HashMap<String, f64>,
}

impl ConsistentHashRing {
    fn new(virtual_nodes: usize) -> Self {
        Self {
            virtual_nodes,
            ring: BTreeMap::new(),
            node_rates: HashMap::new(),
        }
    }
    
    /// 添加节点
    fn add_node(&mut self, node_id: String, sampling_rate: f64) {
        for i in 0..self.virtual_nodes {
            let key = format!("{}:{}", node_id, i);
            let hash = self.hash_key(&key);
            self.ring.insert(hash, node_id.clone());
        }
        
        self.node_rates.insert(node_id, sampling_rate);
    }
    
    /// 获取节点
    fn get_node(&self, key: &str) -> Option<&String> {
        if self.ring.is_empty() {
            return None;
        }
        
        let hash = self.hash_key(key);
        
        // 找到第一个大于等于hash的节点
        self.ring.range(hash..)
            .next()
            .or_else(|| self.ring.iter().next())
            .map(|(_, node)| node)
    }
    
    /// 获取采样率
    fn get_sampling_rate(&self, node_id: &str) -> f64 {
        self.node_rates.get(node_id).copied().unwrap_or(0.0)
    }
    
    /// 哈希函数
    fn hash_key(&self, key: &str) -> u64 {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

impl ConsistentSampler {
    pub fn new(sampling_rate: f64, num_buckets: usize) -> Self {
        let mut ring = ConsistentHashRing::new(100);
        
        // 创建采样桶
        for i in 0..num_buckets {
            let rate = if i < (num_buckets as f64 * sampling_rate) as usize {
                1.0
            } else {
                0.0
            };
            ring.add_node(format!("bucket-{}", i), rate);
        }
        
        Self {
            sampling_rate,
            hash_ring: Arc::new(RwLock::new(ring)),
        }
    }
}

#[async_trait::async_trait]
impl Sampler for ConsistentSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        let trace_id_str = format!("{:?}", ctx.trace_id);
        
        let ring = self.hash_ring.read().await;
        let node = ring.get_node(&trace_id_str);
        
        let sampling_rate = node
            .map(|n| ring.get_sampling_rate(n))
            .unwrap_or(0.0);
        
        let decision = if sampling_rate >= 1.0 {
            SamplingDecision::Sample
        } else {
            SamplingDecision::Drop
        };
        
        SamplingResult {
            decision,
            trace_flags: if decision == SamplingDecision::Sample {
                TraceFlags::SAMPLED
            } else {
                TraceFlags::default()
            },
            attributes: vec![],
        }
    }
    
    fn description(&self) -> String {
        format!("ConsistentSampler({})", self.sampling_rate)
    }
}
```

---

## 7. 机器学习采样

### 7.1 特征提取

```rust
/// ML采样器
pub struct MlSampler {
    /// 模型
    model: Arc<RwLock<SamplingModel>>,
    
    /// 特征提取器
    feature_extractor: Arc<FeatureExtractor>,
    
    /// 训练数据收集器
    training_collector: Arc<Mutex<TrainingDataCollector>>,
}

/// 采样模型(简化版)
struct SamplingModel {
    /// 权重
    weights: Vec<f64>,
    
    /// 偏置
    bias: f64,
}

impl SamplingModel {
    fn new() -> Self {
        Self {
            weights: vec![0.0; 10], // 10个特征
            bias: 0.0,
        }
    }
    
    /// 预测
    fn predict(&self, features: &[f64]) -> f64 {
        let mut score = self.bias;
        
        for (w, f) in self.weights.iter().zip(features.iter()) {
            score += w * f;
        }
        
        // Sigmoid激活
        1.0 / (1.0 + (-score).exp())
    }
    
    /// 训练(简化版)
    fn train(&mut self, samples: &[(Vec<f64>, bool)], learning_rate: f64) {
        for (features, label) in samples {
            let prediction = self.predict(features);
            let error = if *label { 1.0 } else { 0.0 } - prediction;
            
            // 更新权重
            for (w, f) in self.weights.iter_mut().zip(features.iter()) {
                *w += learning_rate * error * f;
            }
            
            self.bias += learning_rate * error;
        }
    }
}

/// 特征提取器
struct FeatureExtractor;

impl FeatureExtractor {
    /// 提取特征
    fn extract_features(&self, ctx: &SamplingContext) -> Vec<f64> {
        let mut features = Vec::with_capacity(10);
        
        // 1. TraceID哈希归一化
        let trace_hash = self.hash_trace_id(&ctx.trace_id);
        features.push(trace_hash as f64 / u64::MAX as f64);
        
        // 2. Span类型
        features.push(ctx.kind as i32 as f64);
        
        // 3. 名称长度
        features.push(ctx.name.len() as f64 / 100.0);
        
        // 4. 属性数量
        features.push(ctx.attributes.len() as f64 / 10.0);
        
        // 5-10. 特定属性存在性
        features.push(if self.has_error_attribute(ctx) { 1.0 } else { 0.0 });
        features.push(if self.has_db_attribute(ctx) { 1.0 } else { 0.0 });
        features.push(if self.has_http_attribute(ctx) { 1.0 } else { 0.0 });
        features.push(if self.has_rpc_attribute(ctx) { 1.0 } else { 0.0 });
        features.push(if ctx.parent_sampled.unwrap_or(false) { 1.0 } else { 0.0 });
        features.push(if ctx.parent_span_id.is_some() { 1.0 } else { 0.0 });
        
        features
    }
    
    fn hash_trace_id(&self, trace_id: &TraceId) -> u64 {
        let bytes = trace_id.to_bytes();
        let mut hash = 0u64;
        for i in 0..8 {
            hash = (hash << 8) | bytes[i] as u64;
        }
        hash
    }
    
    fn has_error_attribute(&self, ctx: &SamplingContext) -> bool {
        ctx.attributes.iter().any(|(k, _)| k.contains("error"))
    }
    
    fn has_db_attribute(&self, ctx: &SamplingContext) -> bool {
        ctx.attributes.iter().any(|(k, _)| k.starts_with("db."))
    }
    
    fn has_http_attribute(&self, ctx: &SamplingContext) -> bool {
        ctx.attributes.iter().any(|(k, _)| k.starts_with("http."))
    }
    
    fn has_rpc_attribute(&self, ctx: &SamplingContext) -> bool {
        ctx.attributes.iter().any(|(k, _)| k.starts_with("rpc."))
    }
}

/// 训练数据收集器
struct TrainingDataCollector {
    samples: VecDeque<(Vec<f64>, bool)>,
    max_samples: usize,
}

impl TrainingDataCollector {
    fn new(max_samples: usize) -> Self {
        Self {
            samples: VecDeque::with_capacity(max_samples),
            max_samples,
        }
    }
    
    fn add_sample(&mut self, features: Vec<f64>, label: bool) {
        if self.samples.len() >= self.max_samples {
            self.samples.pop_front();
        }
        self.samples.push_back((features, label));
    }
    
    fn get_samples(&self) -> Vec<(Vec<f64>, bool)> {
        self.samples.iter().cloned().collect()
    }
}

impl MlSampler {
    pub fn new() -> Arc<Self> {
        let sampler = Arc::new(Self {
            model: Arc::new(RwLock::new(SamplingModel::new())),
            feature_extractor: Arc::new(FeatureExtractor),
            training_collector: Arc::new(Mutex::new(TrainingDataCollector::new(10000))),
        });
        
        // 启动定期训练
        let sampler_clone = Arc::clone(&sampler);
        tokio::spawn(async move {
            sampler_clone.training_loop().await;
        });
        
        sampler
    }
    
    /// 训练循环
    async fn training_loop(&self) {
        let mut ticker = tokio::time::interval(Duration::from_secs(300)); // 每5分钟
        
        loop {
            ticker.tick().await;
            
            let samples = {
                let collector = self.training_collector.lock().await;
                collector.get_samples()
            };
            
            if samples.len() >= 100 {
                let mut model = self.model.write().await;
                model.train(&samples, 0.01);
                
                tracing::info!("Model trained with {} samples", samples.len());
            }
        }
    }
}

#[async_trait::async_trait]
impl Sampler for MlSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        // 提取特征
        let features = self.feature_extractor.extract_features(ctx);
        
        // 模型预测
        let model = self.model.read().await;
        let probability = model.predict(&features);
        
        // 概率采样
        let decision = if rand::random::<f64>() < probability {
            SamplingDecision::Sample
        } else {
            SamplingDecision::Drop
        };
        
        // 收集训练数据(简化：基于简单规则)
        let label = self.should_be_sampled_for_training(ctx);
        let mut collector = self.training_collector.lock().await;
        collector.add_sample(features, label);
        
        SamplingResult {
            decision,
            trace_flags: if decision == SamplingDecision::Sample {
                TraceFlags::SAMPLED
            } else {
                TraceFlags::default()
            },
            attributes: vec![],
        }
    }
    
    fn description(&self) -> String {
        "MlSampler".to_string()
    }
}

impl MlSampler {
    fn should_be_sampled_for_training(&self, ctx: &SamplingContext) -> bool {
        // 简化的标签逻辑
        ctx.attributes.iter().any(|(k, _)| k.contains("error"))
            || ctx.kind == SpanKind::Server
    }
}
```

---

## 8. 完整实现

### 8.1 综合采样策略

```rust
/// 组合采样器
pub struct CompositeSampler {
    samplers: Vec<(String, Arc<dyn Sampler>)>,
    strategy: CompositeStrategy,
}

pub enum CompositeStrategy {
    /// 第一个采样即采样
    Any,
    
    /// 所有采样器都采样
    All,
    
    /// 按优先级
    Priority,
}

impl CompositeSampler {
    pub fn new(samplers: Vec<(String, Arc<dyn Sampler>)>, strategy: CompositeStrategy) -> Self {
        Self {
            samplers,
            strategy,
        }
    }
}

#[async_trait::async_trait]
impl Sampler for CompositeSampler {
    async fn should_sample(&self, ctx: &SamplingContext) -> SamplingResult {
        match self.strategy {
            CompositeStrategy::Any => {
                for (name, sampler) in &self.samplers {
                    let result = sampler.should_sample(ctx).await;
                    if result.decision == SamplingDecision::Sample {
                        tracing::debug!("Sampled by: {}", name);
                        return result;
                    }
                }
                
                SamplingResult {
                    decision: SamplingDecision::Drop,
                    trace_flags: TraceFlags::default(),
                    attributes: vec![],
                }
            }
            
            CompositeStrategy::All => {
                for (name, sampler) in &self.samplers {
                    let result = sampler.should_sample(ctx).await;
                    if result.decision != SamplingDecision::Sample {
                        tracing::debug!("Not sampled by: {}", name);
                        return result;
                    }
                }
                
                SamplingResult {
                    decision: SamplingDecision::Sample,
                    trace_flags: TraceFlags::SAMPLED,
                    attributes: vec![],
                }
            }
            
            CompositeStrategy::Priority => {
                // 使用第一个采样器
                if let Some((name, sampler)) = self.samplers.first() {
                    tracing::debug!("Using priority sampler: {}", name);
                    sampler.should_sample(ctx).await
                } else {
                    SamplingResult {
                        decision: SamplingDecision::Drop,
                        trace_flags: TraceFlags::default(),
                        attributes: vec![],
                    }
                }
            }
        }
    }
    
    fn description(&self) -> String {
        format!("CompositeSampler({:?})", self.strategy)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 创建各种采样器
    let samplers: Vec<(String, Arc<dyn Sampler>)> = vec![
        (
            "base_rate".to_string(),
            Arc::new(TraceIdRatioSampler::new(0.1)),
        ),
        (
            "priority".to_string(),
            Arc::new(PrioritySampler::new(
                vec![
                    PriorityRule {
                        priority: Priority::Critical,
                        condition: RuleCondition::ServiceName("payment".to_string()),
                        sampling_rate: 1.0,
                    },
                ],
                0.1,
            )),
        ),
    ];
    
    let composite = CompositeSampler::new(samplers, CompositeStrategy::Any);
    
    // 测试采样
    let ctx = SamplingContext {
        trace_id: TraceId::from_bytes([1u8; 16]),
        parent_span_id: None,
        name: "test".to_string(),
        kind: SpanKind::Server,
        attributes: vec![
            ("service.name".to_string(), AttributeValue::String("payment".to_string())),
        ],
        parent_sampled: None,
    };
    
    let result = composite.should_sample(&ctx).await;
    println!("Sampling decision: {:?}", result.decision);
    
    Ok(())
}
```

---

## 总结

本文档提供了高级采样算法的完整Rust实现，包括:

✅ **固定比例采样**:

- TraceID哈希采样
- 概率采样

✅ **自适应采样**:

- 动态速率调整
- 负载感知采样

✅ **尾部采样**:

- 基于窗口的缓存
- 规则评估引擎

✅ **优先级采样**:

- 多优先级规则
- 复合条件匹配

✅ **一致性采样**:

- 一致性哈希环
- 跨服务一致性

✅ **机器学习采样**:

- 特征提取
- 在线学习

---

**参考资源**:

- [OpenTelemetry Sampling](https://opentelemetry.io/docs/specs/otel/trace/sdk/#sampling)
- [Consistent Hashing](https://en.wikipedia.org/wiki/Consistent_hashing)
- [Machine Learning Systems](https://ml-ops.org/)
