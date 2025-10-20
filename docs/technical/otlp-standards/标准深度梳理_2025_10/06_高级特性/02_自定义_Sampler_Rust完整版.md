# 自定义 Sampler - Rust 完整版

## 目录

- [自定义 Sampler - Rust 完整版](#自定义-sampler---rust-完整版)
  - [目录](#目录)
  - [1. Sampler 概述](#1-sampler-概述)
    - [1.1 什么是 Sampler](#11-什么是-sampler)
    - [1.2 使用场景](#12-使用场景)
  - [2. Sampler Trait](#2-sampler-trait)
    - [2.1 Trait 定义](#21-trait-定义)
    - [2.2 SamplingDecision](#22-samplingdecision)
  - [3. 内置 Sampler](#3-内置-sampler)
    - [3.1 AlwaysOn/AlwaysOff](#31-alwaysonalwaysoff)
    - [3.2 TraceIdRatioBased](#32-traceidratiobased)
    - [3.3 ParentBased](#33-parentbased)
  - [4. 自定义 Sampler 实现](#4-自定义-sampler-实现)
    - [4.1 基于错误的采样](#41-基于错误的采样)
    - [4.2 基于延迟的采样](#42-基于延迟的采样)
    - [4.3 基于路径的采样](#43-基于路径的采样)
  - [5. 复杂采样策略](#5-复杂采样策略)
    - [5.1 组合采样器](#51-组合采样器)
    - [5.2 速率限制采样](#52-速率限制采样)
    - [5.3 自适应采样](#53-自适应采样)
  - [6. 采样决策](#6-采样决策)
    - [6.1 决策因素](#61-决策因素)
    - [6.2 属性传播](#62-属性传播)
  - [7. 性能优化](#7-性能优化)
    - [7.1 快速路径](#71-快速路径)
    - [7.2 缓存决策](#72-缓存决策)
  - [8. 监控与调试](#8-监控与调试)
    - [8.1 Sampler 指标](#81-sampler-指标)
    - [8.2 日志输出](#82-日志输出)
  - [9. 测试](#9-测试)
    - [9.1 单元测试](#91-单元测试)
    - [9.2 统计测试](#92-统计测试)
  - [10. 生产环境配置](#10-生产环境配置)
    - [10.1 动态调整](#101-动态调整)
    - [10.2 配置热更新](#102-配置热更新)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Sampler 对比](#sampler-对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Sampler 概述

### 1.1 什么是 Sampler

````text
Sampler 定义:
- 决定是否采样一个 Span
- 在 Span 创建时执行
- 返回采样决策 (SamplingDecision)

采样目的:
1. 降低数据量
2. 减少存储成本
3. 降低网络开销
4. 保留重要 Trace

采样时机:
- Head-based Sampling (头部采样)
  在 Span 创建时决定
  
- Tail-based Sampling (尾部采样)
  在 Trace 完成后决定 (需要特殊架构)
````

### 1.2 使用场景

````text
自定义 Sampler 使用场景:

1. 错误优先
   - 所有错误 100% 采样
   - 正常请求按比例采样

2. 慢请求优先
   - 慢请求 100% 采样
   - 快请求低比例采样

3. 路径过滤
   - 健康检查 0% 采样
   - 业务接口 100% 采样

4. 用户分级
   - VIP 用户 100% 采样
   - 普通用户 10% 采样

5. 自适应采样
   - 根据系统负载动态调整采样率
````

---

## 2. Sampler Trait

### 2.1 Trait 定义

````rust
use opentelemetry::{
    trace::{
        SamplingDecision, SamplingResult, TraceContextExt, TraceId, TraceState,
        SpanKind, Link,
    },
    Context, KeyValue,
};

/// Sampler Trait
pub trait Sampler: Send + Sync + std::fmt::Debug {
    /// 采样决策
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult;
}
````

### 2.2 SamplingDecision

````rust
/// 采样决策
pub enum SamplingDecision {
    /// 丢弃 Span (不记录)
    Drop,
    
    /// 记录 Span (但不导出)
    RecordOnly,
    
    /// 记录并导出 Span
    RecordAndSample,
}

/// 采样结果
pub struct SamplingResult {
    /// 采样决策
    pub decision: SamplingDecision,
    
    /// 要添加的属性
    pub attributes: Vec<KeyValue>,
    
    /// TraceState (W3C Trace Context)
    pub trace_state: TraceState,
}

impl SamplingResult {
    /// 创建采样结果
    pub fn new(
        decision: SamplingDecision,
        attributes: Vec<KeyValue>,
        trace_state: TraceState,
    ) -> Self {
        Self {
            decision,
            attributes,
            trace_state,
        }
    }
    
    /// DROP 决策
    pub fn drop() -> Self {
        Self::new(SamplingDecision::Drop, vec![], TraceState::default())
    }
    
    /// RECORD_ONLY 决策
    pub fn record_only(attributes: Vec<KeyValue>) -> Self {
        Self::new(SamplingDecision::RecordOnly, attributes, TraceState::default())
    }
    
    /// RECORD_AND_SAMPLE 决策
    pub fn record_and_sample(attributes: Vec<KeyValue>) -> Self {
        Self::new(SamplingDecision::RecordAndSample, attributes, TraceState::default())
    }
}
````

---

## 3. 内置 Sampler

### 3.1 AlwaysOn/AlwaysOff

````rust
use opentelemetry::trace::{Sampler, SamplingResult};

/// 始终采样
#[derive(Debug)]
pub struct AlwaysOnSampler;

impl Sampler for AlwaysOnSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        _trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        SamplingResult::record_and_sample(vec![])
    }
}

/// 从不采样
#[derive(Debug)]
pub struct AlwaysOffSampler;

impl Sampler for AlwaysOffSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        _trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        SamplingResult::drop()
    }
}
````

### 3.2 TraceIdRatioBased

````rust
/// 基于 TraceId 的比例采样
#[derive(Debug)]
pub struct TraceIdRatioBasedSampler {
    ratio: f64,
    threshold: u64,
}

impl TraceIdRatioBasedSampler {
    pub fn new(ratio: f64) -> Self {
        let ratio = ratio.clamp(0.0, 1.0);
        let threshold = (ratio * (u64::MAX as f64)) as u64;
        
        Self { ratio, threshold }
    }
}

impl Sampler for TraceIdRatioBasedSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        // 使用 TraceId 的后 8 字节作为随机数
        let bytes = trace_id.to_bytes();
        let value = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        if value < self.threshold {
            SamplingResult::record_and_sample(vec![
                KeyValue::new("sampling.ratio", self.ratio),
            ])
        } else {
            SamplingResult::drop()
        }
    }
}
````

### 3.3 ParentBased

````rust
/// 基于父 Span 的采样
#[derive(Debug)]
pub struct ParentBasedSampler {
    root: Box<dyn Sampler>,
}

impl ParentBasedSampler {
    pub fn new(root_sampler: Box<dyn Sampler>) -> Self {
        Self { root: root_sampler }
    }
}

impl Sampler for ParentBasedSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查父 Span 是否被采样
        if let Some(cx) = parent_context {
            let span_context = cx.span().span_context();
            
            if span_context.is_sampled() {
                // 父 Span 被采样，子 Span 也采样
                return SamplingResult::record_and_sample(vec![]);
            } else {
                // 父 Span 未采样，子 Span 也不采样
                return SamplingResult::drop();
            }
        }
        
        // 无父 Span，使用 root sampler
        self.root.should_sample(
            parent_context,
            trace_id,
            name,
            span_kind,
            attributes,
            links,
        )
    }
}
````

---

## 4. 自定义 Sampler 实现

### 4.1 基于错误的采样

````rust
/// 错误优先采样器
#[derive(Debug)]
pub struct ErrorPrioritySampler {
    error_ratio: f64,      // 错误采样率 (通常 1.0)
    normal_ratio: f64,     // 正常采样率 (通常 0.1)
    normal_sampler: TraceIdRatioBasedSampler,
}

impl ErrorPrioritySampler {
    pub fn new(error_ratio: f64, normal_ratio: f64) -> Self {
        Self {
            error_ratio,
            normal_ratio,
            normal_sampler: TraceIdRatioBasedSampler::new(normal_ratio),
        }
    }
}

impl Sampler for ErrorPrioritySampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查是否有错误标记
        let has_error = attributes.iter().any(|kv| {
            kv.key.as_str() == "error" && kv.value.as_str() == "true"
        });
        
        if has_error {
            // 错误请求，高采样率
            SamplingResult::record_and_sample(vec![
                KeyValue::new("sampling.reason", "error"),
                KeyValue::new("sampling.ratio", self.error_ratio),
            ])
        } else {
            // 正常请求，使用正常采样率
            let mut result = self.normal_sampler.should_sample(
                parent_context,
                trace_id,
                name,
                span_kind,
                attributes,
                links,
            );
            
            result.attributes.push(KeyValue::new("sampling.reason", "normal"));
            result
        }
    }
}
````

### 4.2 基于延迟的采样

````rust
/// 延迟优先采样器
#[derive(Debug)]
pub struct LatencyPrioritySampler {
    slow_threshold_ms: u64,  // 慢请求阈值 (毫秒)
    slow_ratio: f64,         // 慢请求采样率
    fast_ratio: f64,         // 快请求采样率
    fast_sampler: TraceIdRatioBasedSampler,
}

impl LatencyPrioritySampler {
    pub fn new(slow_threshold_ms: u64, slow_ratio: f64, fast_ratio: f64) -> Self {
        Self {
            slow_threshold_ms,
            slow_ratio,
            fast_ratio,
            fast_sampler: TraceIdRatioBasedSampler::new(fast_ratio),
        }
    }
}

impl Sampler for LatencyPrioritySampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查延迟属性 (需要在 Span 创建时设置)
        let latency_ms = attributes.iter().find_map(|kv| {
            if kv.key.as_str() == "expected_latency_ms" {
                kv.value.as_str().parse::<u64>().ok()
            } else {
                None
            }
        });
        
        match latency_ms {
            Some(latency) if latency > self.slow_threshold_ms => {
                // 预期慢请求，高采样率
                SamplingResult::record_and_sample(vec![
                    KeyValue::new("sampling.reason", "slow"),
                    KeyValue::new("sampling.ratio", self.slow_ratio),
                ])
            }
            _ => {
                // 快请求，使用正常采样率
                self.fast_sampler.should_sample(
                    parent_context,
                    trace_id,
                    name,
                    span_kind,
                    attributes,
                    links,
                )
            }
        }
    }
}
````

### 4.3 基于路径的采样

````rust
/// 路径过滤采样器
#[derive(Debug)]
pub struct PathFilterSampler {
    ignore_patterns: Vec<String>,
    default_sampler: Box<dyn Sampler>,
}

impl PathFilterSampler {
    pub fn new(ignore_patterns: Vec<String>, default_sampler: Box<dyn Sampler>) -> Self {
        Self {
            ignore_patterns,
            default_sampler,
        }
    }
}

impl Sampler for PathFilterSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查路径是否在忽略列表中
        let path = attributes.iter().find_map(|kv| {
            if kv.key.as_str() == "http.target" || kv.key.as_str() == "http.route" {
                Some(kv.value.as_str())
            } else {
                None
            }
        });
        
        if let Some(path) = path {
            for pattern in &self.ignore_patterns {
                if path.starts_with(pattern) {
                    // 匹配忽略模式，不采样
                    return SamplingResult::drop();
                }
            }
        }
        
        // 使用默认采样器
        self.default_sampler.should_sample(
            parent_context,
            trace_id,
            name,
            span_kind,
            attributes,
            links,
        )
    }
}

/// 使用示例
pub fn create_path_filter_sampler() -> PathFilterSampler {
    PathFilterSampler::new(
        vec![
            "/health".to_string(),
            "/metrics".to_string(),
            "/ready".to_string(),
        ],
        Box::new(TraceIdRatioBasedSampler::new(0.1)),
    )
}
````

---

## 5. 复杂采样策略

### 5.1 组合采样器

````rust
/// 组合采样器 (AND 逻辑)
#[derive(Debug)]
pub struct CompositeSampler {
    samplers: Vec<Box<dyn Sampler>>,
}

impl CompositeSampler {
    pub fn new(samplers: Vec<Box<dyn Sampler>>) -> Self {
        Self { samplers }
    }
}

impl Sampler for CompositeSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        let mut all_attributes = Vec::new();
        
        // 所有采样器都必须同意采样
        for sampler in &self.samplers {
            let result = sampler.should_sample(
                parent_context,
                trace_id,
                name,
                span_kind,
                attributes,
                links,
            );
            
            match result.decision {
                SamplingDecision::Drop => {
                    // 任何一个采样器拒绝，则不采样
                    return result;
                }
                _ => {
                    all_attributes.extend(result.attributes);
                }
            }
        }
        
        SamplingResult::record_and_sample(all_attributes)
    }
}
````

### 5.2 速率限制采样

````rust
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// 速率限制采样器
#[derive(Debug)]
pub struct RateLimitSampler {
    max_per_second: u64,
    counter: Arc<AtomicU64>,
    last_reset: Arc<std::sync::Mutex<Instant>>,
}

impl RateLimitSampler {
    pub fn new(max_per_second: u64) -> Self {
        Self {
            max_per_second,
            counter: Arc::new(AtomicU64::new(0)),
            last_reset: Arc::new(std::sync::Mutex::new(Instant::now())),
        }
    }
    
    fn check_and_increment(&self) -> bool {
        let mut last_reset = self.last_reset.lock().unwrap();
        
        // 每秒重置计数器
        if last_reset.elapsed() >= Duration::from_secs(1) {
            self.counter.store(0, Ordering::Relaxed);
            *last_reset = Instant::now();
        }
        
        let count = self.counter.fetch_add(1, Ordering::Relaxed);
        count < self.max_per_second
    }
}

impl Sampler for RateLimitSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        _trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        if self.check_and_increment() {
            SamplingResult::record_and_sample(vec![
                KeyValue::new("sampling.reason", "rate_limit"),
            ])
        } else {
            SamplingResult::drop()
        }
    }
}
````

### 5.3 自适应采样

````rust
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicU32, Ordering};

/// 自适应采样器
#[derive(Debug)]
pub struct AdaptiveSampler {
    target_rate: u64,          // 目标采样率 (spans/sec)
    window_size: Duration,      // 时间窗口
    current_rate: Arc<AtomicU64>,
    sampled_count: Arc<AtomicU64>,
    last_adjustment: Arc<std::sync::Mutex<Instant>>,
    current_ratio: Arc<AtomicU32>,  // f32 as u32
}

impl AdaptiveSampler {
    pub fn new(target_rate: u64) -> Self {
        Self {
            target_rate,
            window_size: Duration::from_secs(10),
            current_rate: Arc::new(AtomicU64::new(0)),
            sampled_count: Arc::new(AtomicU64::new(0)),
            last_adjustment: Arc::new(std::sync::Mutex::new(Instant::now())),
            current_ratio: Arc::new(AtomicU32::new(f32::to_bits(1.0))),
        }
    }
    
    fn adjust_ratio(&self) {
        let mut last_adjustment = self.last_adjustment.lock().unwrap();
        
        if last_adjustment.elapsed() >= self.window_size {
            let sampled = self.sampled_count.swap(0, Ordering::Relaxed);
            let window_secs = last_adjustment.elapsed().as_secs();
            let actual_rate = sampled / window_secs;
            
            let current_ratio = f32::from_bits(self.current_ratio.load(Ordering::Relaxed));
            
            // 调整采样率
            let new_ratio = if actual_rate > self.target_rate {
                (current_ratio * 0.9).max(0.01)  // 降低 10%
            } else if actual_rate < self.target_rate {
                (current_ratio * 1.1).min(1.0)   // 提高 10%
            } else {
                current_ratio
            };
            
            self.current_ratio.store(f32::to_bits(new_ratio), Ordering::Relaxed);
            *last_adjustment = Instant::now();
            
            tracing::info!(
                actual_rate,
                new_ratio,
                "Adjusted sampling ratio"
            );
        }
    }
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        self.adjust_ratio();
        
        let ratio = f32::from_bits(self.current_ratio.load(Ordering::Relaxed));
        let threshold = (ratio * (u64::MAX as f32)) as u64;
        
        let bytes = trace_id.to_bytes();
        let value = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        if value < threshold {
            self.sampled_count.fetch_add(1, Ordering::Relaxed);
            SamplingResult::record_and_sample(vec![
                KeyValue::new("sampling.ratio", ratio as f64),
                KeyValue::new("sampling.reason", "adaptive"),
            ])
        } else {
            SamplingResult::drop()
        }
    }
}
````

---

## 6. 采样决策

### 6.1 决策因素

````text
采样决策考虑因素:

1. 父 Span 状态
   - 父 Span 被采样 → 子 Span 也采样
   - 保持 Trace 完整性

2. Span 属性
   - error=true → 100% 采样
   - http.status_code=5xx → 100% 采样
   - latency > threshold → 高采样率

3. Span 名称
   - 健康检查 → 0% 采样
   - 业务接口 → 正常采样

4. TraceId
   - 基于 TraceId 的随机采样
   - 保证同一 Trace 的采样一致性

5. 系统负载
   - 高负载 → 降低采样率
   - 低负载 → 提高采样率
````

### 6.2 属性传播

````rust
/// 带属性的采样决策
pub fn sample_with_attributes(
    trace_id: TraceId,
    attributes: &[KeyValue],
) -> SamplingResult {
    let mut sampling_attrs = Vec::new();
    
    // 检查错误
    let has_error = attributes.iter().any(|kv| {
        kv.key.as_str() == "error" && kv.value.as_str() == "true"
    });
    
    if has_error {
        sampling_attrs.push(KeyValue::new("sampling.reason", "error"));
        sampling_attrs.push(KeyValue::new("sampling.priority", "high"));
        return SamplingResult::record_and_sample(sampling_attrs);
    }
    
    // 检查状态码
    if let Some(status) = attributes.iter().find(|kv| kv.key.as_str() == "http.status_code") {
        let status_code = status.value.as_str().parse::<u16>().unwrap_or(0);
        if status_code >= 500 {
            sampling_attrs.push(KeyValue::new("sampling.reason", "5xx_error"));
            return SamplingResult::record_and_sample(sampling_attrs);
        }
    }
    
    // 默认采样逻辑
    SamplingResult::drop()
}
````

---

## 7. 性能优化

### 7.1 快速路径

````rust
/// 优化的采样器
#[derive(Debug)]
pub struct OptimizedSampler {
    ratio: f64,
    threshold: u64,
}

impl OptimizedSampler {
    pub fn new(ratio: f64) -> Self {
        let threshold = (ratio * (u64::MAX as f64)) as u64;
        Self { ratio, threshold }
    }
}

impl Sampler for OptimizedSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        // 快速路径: 只比较 TraceId
        let bytes = trace_id.to_bytes();
        let value = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        if value < self.threshold {
            SamplingResult::record_and_sample(vec![])
        } else {
            SamplingResult::drop()
        }
    }
}
````

### 7.2 缓存决策

````rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// 缓存采样决策
#[derive(Debug, Clone)]
pub struct CachedSampler {
    inner: Arc<Box<dyn Sampler>>,
    cache: Arc<Mutex<HashMap<TraceId, SamplingDecision>>>,
    max_cache_size: usize,
}

impl CachedSampler {
    pub fn new(sampler: Box<dyn Sampler>, max_cache_size: usize) -> Self {
        Self {
            inner: Arc::new(sampler),
            cache: Arc::new(Mutex::new(HashMap::new())),
            max_cache_size,
        }
    }
}

impl Sampler for CachedSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 检查缓存
        {
            let cache = self.cache.lock().unwrap();
            if let Some(decision) = cache.get(&trace_id) {
                return SamplingResult::new(decision.clone(), vec![], TraceState::default());
            }
        }
        
        // 执行采样
        let result = self.inner.should_sample(
            parent_context,
            trace_id,
            name,
            span_kind,
            attributes,
            links,
        );
        
        // 缓存结果
        {
            let mut cache = self.cache.lock().unwrap();
            if cache.len() >= self.max_cache_size {
                cache.clear();  // 简单策略: 清空缓存
            }
            cache.insert(trace_id, result.decision.clone());
        }
        
        result
    }
}
````

---

## 8. 监控与调试

### 8.1 Sampler 指标

````rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct SamplerMetrics {
    pub sampled_count: Counter<u64>,
    pub dropped_count: Counter<u64>,
    pub sampling_decision_duration: Histogram<f64>,
}

impl SamplerMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("sampler");
        
        Self {
            sampled_count: meter
                .u64_counter("sampler.sampled")
                .with_description("Number of sampled spans")
                .build(),
            dropped_count: meter
                .u64_counter("sampler.dropped")
                .with_description("Number of dropped spans")
                .build(),
            sampling_decision_duration: meter
                .f64_histogram("sampler.decision.duration")
                .with_description("Sampling decision duration")
                .build(),
        }
    }
}
````

### 8.2 日志输出

````rust
impl Sampler for LoggingSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        let start = std::time::Instant::now();
        
        let result = self.inner.should_sample(
            parent_context,
            trace_id,
            name,
            span_kind,
            attributes,
            links,
        );
        
        let duration = start.elapsed();
        
        tracing::debug!(
            trace_id = %trace_id,
            name,
            decision = ?result.decision,
            duration_us = duration.as_micros(),
            "Sampling decision"
        );
        
        result
    }
}
````

---

## 9. 测试

### 9.1 单元测试

````rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_priority_sampler() {
        let sampler = ErrorPrioritySampler::new(1.0, 0.1);
        
        // 测试错误请求
        let result = sampler.should_sample(
            None,
            TraceId::from_hex("00000000000000000000000000000001").unwrap(),
            "test_span",
            &SpanKind::Server,
            &[KeyValue::new("error", "true")],
            &[],
        );
        
        assert!(matches!(result.decision, SamplingDecision::RecordAndSample));
    }
    
    #[test]
    fn test_ratio_sampler() {
        let sampler = TraceIdRatioBasedSampler::new(0.5);
        let mut sampled = 0;
        let total = 1000;
        
        for i in 0..total {
            let trace_id = TraceId::from_hex(&format!("{:032x}", i)).unwrap();
            let result = sampler.should_sample(
                None,
                trace_id,
                "test",
                &SpanKind::Server,
                &[],
                &[],
            );
            
            if matches!(result.decision, SamplingDecision::RecordAndSample) {
                sampled += 1;
            }
        }
        
        // 允许 10% 误差
        assert!((sampled as f64 - total as f64 * 0.5).abs() < total as f64 * 0.1);
    }
}
````

### 9.2 统计测试

````rust
#[test]
fn test_sampling_distribution() {
    let sampler = TraceIdRatioBasedSampler::new(0.1);
    let iterations = 10000;
    let mut sampled = 0;
    
    for _ in 0..iterations {
        let trace_id = TraceId::from_random();
        let result = sampler.should_sample(
            None,
            trace_id,
            "test",
            &SpanKind::Server,
            &[],
            &[],
        );
        
        if matches!(result.decision, SamplingDecision::RecordAndSample) {
            sampled += 1;
        }
    }
    
    let actual_ratio = sampled as f64 / iterations as f64;
    assert!((actual_ratio - 0.1).abs() < 0.01);  // ±1% 误差
}
````

---

## 10. 生产环境配置

### 10.1 动态调整

````rust
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

/// 可动态调整的采样器
pub struct DynamicSampler {
    ratio: Arc<AtomicU32>,  // f32 as u32
}

impl DynamicSampler {
    pub fn new(initial_ratio: f64) -> Self {
        Self {
            ratio: Arc::new(AtomicU32::new(f32::to_bits(initial_ratio as f32))),
        }
    }
    
    pub fn set_ratio(&self, ratio: f64) {
        let ratio = (ratio.clamp(0.0, 1.0) as f32);
        self.ratio.store(f32::to_bits(ratio), Ordering::Relaxed);
        tracing::info!(ratio, "Sampling ratio updated");
    }
    
    pub fn get_ratio(&self) -> f64 {
        f32::from_bits(self.ratio.load(Ordering::Relaxed)) as f64
    }
}

impl Sampler for DynamicSampler {
    fn should_sample(
        &self,
        _parent_context: Option<&Context>,
        trace_id: TraceId,
        _name: &str,
        _span_kind: &SpanKind,
        _attributes: &[KeyValue],
        _links: &[Link],
    ) -> SamplingResult {
        let ratio = self.get_ratio();
        let threshold = (ratio * (u64::MAX as f64)) as u64;
        
        let bytes = trace_id.to_bytes();
        let value = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        
        if value < threshold {
            SamplingResult::record_and_sample(vec![
                KeyValue::new("sampling.ratio", ratio),
            ])
        } else {
            SamplingResult::drop()
        }
    }
}
````

### 10.2 配置热更新

````rust
use tokio::sync::watch;

/// 支持热更新的采样器
pub struct ReloadableSampler {
    receiver: watch::Receiver<Box<dyn Sampler>>,
}

impl ReloadableSampler {
    pub fn new(initial_sampler: Box<dyn Sampler>) -> (Self, watch::Sender<Box<dyn Sampler>>) {
        let (sender, receiver) = watch::channel(initial_sampler);
        (Self { receiver }, sender)
    }
}

impl Sampler for ReloadableSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        let sampler = self.receiver.borrow();
        sampler.should_sample(parent_context, trace_id, name, span_kind, attributes, links)
    }
}
````

---

## 总结

### 核心要点

1. **Sampler Trait**: 实现 `should_sample` 方法
2. **采样决策**: Drop, RecordOnly, RecordAndSample
3. **内置 Sampler**: AlwaysOn, AlwaysOff, TraceIdRatioBased, ParentBased
4. **自定义策略**: 错误优先、延迟优先、路径过滤
5. **性能优化**: 快速路径、缓存决策
6. **监控**: 指标和日志

### Sampler 对比

| Sampler | 采样率 | 适用场景 | 性能 |
|---------|--------|---------|------|
| AlwaysOn | 100% | 调试 | 最低 |
| AlwaysOff | 0% | 禁用追踪 | 最高 |
| TraceIdRatioBased | 固定比例 | 生产环境 | 高 |
| ParentBased | 继承父 Span | 分布式追踪 | 高 |
| ErrorPriority | 动态 | 错误优先 | 中 |
| Adaptive | 自适应 | 高动态负载 | 中 |

### 最佳实践清单

- ✅ 实现 `Sampler` trait
- ✅ 使用 `ParentBased` 保持 Trace 完整性
- ✅ 错误和慢请求 100% 采样
- ✅ 健康检查 0% 采样
- ✅ 生产环境 1-10% 采样率
- ✅ 使用 TraceId 保证一致性
- ✅ 添加采样原因到属性
- ✅ 监控采样率和决策时间
- ✅ 支持动态调整采样率
- ✅ 编写单元测试验证比例
- ❌ 不要在采样决策中执行耗时操作
- ❌ 不要基于 Span 内容采样 (Tail-based Sampling 需要特殊架构)

---

**相关文档**:

- [自定义 Exporter](./01_自定义_Exporter_Rust完整版.md)
- [采样策略](../05_采样与性能/02_采样策略_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [SDK 最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)
