# Collector Processors - Rust 完整版

## 目录

- [Collector Processors - Rust 完整版](#collector-processors---rust-完整版)
  - [目录](#目录)
  - [1. Processor 概述](#1-processor-概述)
    - [1.1 核心功能](#11-核心功能)
    - [1.2 Processor 接口定义](#12-processor-接口定义)
  - [2. Batch Processor](#2-batch-processor)
    - [2.1 核心实现](#21-核心实现)
    - [2.2 配置示例](#22-配置示例)
  - [3. Attributes Processor](#3-attributes-processor)
    - [3.1 核心实现](#31-核心实现)
    - [3.2 配置示例](#32-配置示例)
  - [4. Filter Processor](#4-filter-processor)
    - [4.1 核心实现](#41-核心实现)
    - [4.2 配置示例](#42-配置示例)
  - [5. Transform Processor](#5-transform-processor)
    - [5.1 核心实现](#51-核心实现)
  - [6. Resource Processor](#6-resource-processor)
    - [6.1 核心实现](#61-核心实现)
    - [6.2 配置示例](#62-配置示例)
  - [7. Memory Limiter Processor](#7-memory-limiter-processor)
    - [7.1 核心实现](#71-核心实现)
    - [7.2 配置示例](#72-配置示例)
  - [8. 自定义 Processor 开发](#8-自定义-processor-开发)
    - [8.1 采样 Processor](#81-采样-processor)
    - [8.2 PII 脱敏 Processor](#82-pii-脱敏-processor)
  - [9. 完整示例](#9-完整示例)
    - [9.1 多 Processor 管道](#91-多-processor-管道)
    - [9.2 配置驱动的 Processor 工厂](#92-配置驱动的-processor-工厂)
  - [总结](#总结)

---

## 1. Processor 概述

**Processor** 位于 Receiver 和 Exporter 之间，负责对遥测数据进行**转换、过滤、增强**。

### 1.1 核心功能

```text
Receiver → [Processor 1] → [Processor 2] → [Processor N] → Exporter
              ↓                ↓                ↓
           转换/过滤         批处理            脱敏
```

**常见操作**：

- **批处理**：减少网络调用
- **过滤**：丢弃不需要的数据
- **转换**：修改属性、重命名字段
- **脱敏**：删除敏感信息
- **采样**：降低数据量

### 1.2 Processor 接口定义

```rust
use async_trait::async_trait;
use opentelemetry_sdk::export::trace::SpanData;
use std::sync::Arc;

#[async_trait]
pub trait Processor: Send + Sync {
    /// Processor 名称
    fn name(&self) -> &str;
    
    /// 处理单个 Span
    async fn process_span(&self, span: SpanData) -> Option<SpanData>;
    
    /// 批量处理
    async fn process_batch(&self, spans: Vec<SpanData>) -> Vec<SpanData> {
        let mut result = Vec::new();
        for span in spans {
            if let Some(processed) = self.process_span(span).await {
                result.push(processed);
            }
        }
        result
    }
    
    /// 启动 Processor
    async fn start(&mut self) -> Result<(), ProcessorError> {
        Ok(())
    }
    
    /// 关闭 Processor
    async fn shutdown(&mut self) -> Result<(), ProcessorError> {
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ProcessorError {
    #[error("Processing error: {0}")]
    ProcessingError(String),
    
    #[error("Configuration error: {0}")]
    ConfigError(String),
}
```

---

## 2. Batch Processor

将多个 Span 批量处理，减少网络调用次数。

### 2.1 核心实现

```rust
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::Mutex;
use tokio::time::interval;

pub struct BatchProcessor {
    /// 最大批量大小
    max_batch_size: usize,
    /// 超时时间
    timeout: Duration,
    /// 内部缓冲区
    buffer: Arc<Mutex<Vec<SpanData>>>,
    /// 刷新回调
    flush_fn: Arc<dyn Fn(Vec<SpanData>) + Send + Sync>,
}

impl BatchProcessor {
    pub fn new(
        max_batch_size: usize,
        timeout: Duration,
        flush_fn: impl Fn(Vec<SpanData>) + Send + Sync + 'static,
    ) -> Self {
        Self {
            max_batch_size,
            timeout,
            buffer: Arc::new(Mutex::new(Vec::with_capacity(max_batch_size))),
            flush_fn: Arc::new(flush_fn),
        }
    }
    
    /// 添加 Span（非阻塞）
    pub async fn add(&self, span: SpanData) -> Option<Vec<SpanData>> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(span);
        
        if buffer.len() >= self.max_batch_size {
            Some(buffer.drain(..).collect())
        } else {
            None
        }
    }
    
    /// 强制刷新缓冲区
    pub async fn flush(&self) -> Vec<SpanData> {
        let mut buffer = self.buffer.lock().await;
        buffer.drain(..).collect()
    }
    
    /// 启动定时刷新
    pub async fn start_timer(&self) {
        let buffer = self.buffer.clone();
        let flush_fn = self.flush_fn.clone();
        let timeout = self.timeout;
        
        tokio::spawn(async move {
            let mut ticker = interval(timeout);
            loop {
                ticker.tick().await;
                let batch = {
                    let mut buf = buffer.lock().await;
                    buf.drain(..).collect::<Vec<_>>()
                };
                
                if !batch.is_empty() {
                    flush_fn(batch);
                }
            }
        });
    }
}

#[async_trait]
impl Processor for BatchProcessor {
    fn name(&self) -> &str {
        "batch"
    }
    
    async fn process_span(&self, span: SpanData) -> Option<SpanData> {
        // Batch Processor 不修改 Span，只是缓冲
        if let Some(batch) = self.add(span.clone()).await {
            (self.flush_fn)(batch);
        }
        Some(span)
    }
    
    async fn start(&mut self) -> Result<(), ProcessorError> {
        self.start_timer().await;
        Ok(())
    }
}
```

### 2.2 配置示例

```yaml
processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
```

```rust
let batch_processor = BatchProcessor::new(
    1024,  // max_batch_size
    Duration::from_secs(10),  // timeout
    |batch| {
        println!("Flushing {} spans", batch.len());
        // 调用 Exporter
    },
);
```

---

## 3. Attributes Processor

修改、添加、删除 Span 的 Attributes。

### 3.1 核心实现

```rust
use opentelemetry::KeyValue;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum AttributeAction {
    Insert { key: String, value: String },
    Update { key: String, value: String },
    Upsert { key: String, value: String },
    Delete { key: String },
    Hash { key: String },  // 对值进行哈希
}

pub struct AttributesProcessor {
    actions: Vec<AttributeAction>,
}

impl AttributesProcessor {
    pub fn new(actions: Vec<AttributeAction>) -> Self {
        Self { actions }
    }
    
    fn apply_actions(&self, attributes: &mut Vec<KeyValue>) {
        let mut attr_map: HashMap<String, String> = attributes
            .iter()
            .map(|kv| (kv.key.to_string(), kv.value.to_string()))
            .collect();
        
        for action in &self.actions {
            match action {
                AttributeAction::Insert { key, value } => {
                    attr_map.entry(key.clone()).or_insert(value.clone());
                }
                AttributeAction::Update { key, value } => {
                    if attr_map.contains_key(key) {
                        attr_map.insert(key.clone(), value.clone());
                    }
                }
                AttributeAction::Upsert { key, value } => {
                    attr_map.insert(key.clone(), value.clone());
                }
                AttributeAction::Delete { key } => {
                    attr_map.remove(key);
                }
                AttributeAction::Hash { key } => {
                    if let Some(value) = attr_map.get_mut(key) {
                        *value = format!("{:x}", md5::compute(value.as_bytes()));
                    }
                }
            }
        }
        
        *attributes = attr_map
            .into_iter()
            .map(|(k, v)| KeyValue::new(k, v))
            .collect();
    }
}

#[async_trait]
impl Processor for AttributesProcessor {
    fn name(&self) -> &str {
        "attributes"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        self.apply_actions(&mut span.attributes);
        Some(span)
    }
}
```

### 3.2 配置示例

```yaml
processors:
  attributes:
    actions:
      - key: environment
        value: production
        action: insert
      - key: user_email
        action: hash
      - key: password
        action: delete
```

```rust
let attributes_processor = AttributesProcessor::new(vec![
    AttributeAction::Insert {
        key: "environment".to_string(),
        value: "production".to_string(),
    },
    AttributeAction::Hash {
        key: "user_email".to_string(),
    },
    AttributeAction::Delete {
        key: "password".to_string(),
    },
]);
```

---

## 4. Filter Processor

根据规则过滤 Span。

### 4.1 核心实现

```rust
use regex::Regex;

#[derive(Debug, Clone)]
pub enum FilterRule {
    /// Span 名称匹配
    SpanNameMatches { pattern: String },
    /// 属性匹配
    AttributeMatches { key: String, pattern: String },
    /// 持续时间过滤
    DurationGreaterThan { threshold_ms: u64 },
    /// 状态码过滤
    StatusCodeEquals { code: i32 },
}

pub struct FilterProcessor {
    rules: Vec<FilterRule>,
    /// true = 保留匹配的, false = 丢弃匹配的
    keep_matched: bool,
}

impl FilterProcessor {
    pub fn new(rules: Vec<FilterRule>, keep_matched: bool) -> Self {
        Self { rules, keep_matched }
    }
    
    fn matches(&self, span: &SpanData) -> bool {
        for rule in &self.rules {
            match rule {
                FilterRule::SpanNameMatches { pattern } => {
                    let regex = Regex::new(pattern).unwrap();
                    if regex.is_match(&span.name) {
                        return true;
                    }
                }
                FilterRule::AttributeMatches { key, pattern } => {
                    let regex = Regex::new(pattern).unwrap();
                    for attr in &span.attributes {
                        if attr.key.as_str() == key && regex.is_match(&attr.value.to_string()) {
                            return true;
                        }
                    }
                }
                FilterRule::DurationGreaterThan { threshold_ms } => {
                    let duration_ms = (span.end_time - span.start_time).as_millis() as u64;
                    if duration_ms > *threshold_ms {
                        return true;
                    }
                }
                FilterRule::StatusCodeEquals { code } => {
                    if span.status.code as i32 == *code {
                        return true;
                    }
                }
            }
        }
        false
    }
}

#[async_trait]
impl Processor for FilterProcessor {
    fn name(&self) -> &str {
        "filter"
    }
    
    async fn process_span(&self, span: SpanData) -> Option<SpanData> {
        let matched = self.matches(&span);
        
        if (self.keep_matched && matched) || (!self.keep_matched && !matched) {
            Some(span)
        } else {
            None  // 丢弃
        }
    }
}
```

### 4.2 配置示例

```yaml
processors:
  filter:
    spans:
      include:
        match_type: regexp
        span_names:
          - "^/health.*"
          - "^/metrics.*"
      exclude:
        attributes:
          - key: http.status_code
            value: 200
```

```rust
let filter_processor = FilterProcessor::new(
    vec![
        FilterRule::SpanNameMatches {
            pattern: "^/health.*".to_string(),
        },
        FilterRule::StatusCodeEquals { code: 200 },
    ],
    false,  // 丢弃匹配的
);
```

---

## 5. Transform Processor

复杂的数据转换（重命名、格式转换、条件逻辑）。

### 5.1 核心实现

```rust
use serde_json::Value;

#[derive(Debug, Clone)]
pub enum TransformRule {
    /// 重命名属性
    RenameAttribute { from: String, to: String },
    /// 条件转换
    ConditionalTransform {
        condition: String,  // 简单条件表达式
        action: Box<TransformRule>,
    },
    /// 提取子字符串
    ExtractSubstring {
        key: String,
        start: usize,
        end: usize,
    },
    /// JSON 解析
    ParseJson { key: String, target_key: String },
}

pub struct TransformProcessor {
    rules: Vec<TransformRule>,
}

impl TransformProcessor {
    pub fn new(rules: Vec<TransformRule>) -> Self {
        Self { rules }
    }
    
    fn apply_transforms(&self, attributes: &mut Vec<KeyValue>) {
        for rule in &self.rules {
            match rule {
                TransformRule::RenameAttribute { from, to } => {
                    for attr in attributes.iter_mut() {
                        if attr.key.as_str() == from {
                            attr.key = to.clone().into();
                        }
                    }
                }
                TransformRule::ExtractSubstring { key, start, end } => {
                    for attr in attributes.iter_mut() {
                        if attr.key.as_str() == key {
                            let value = attr.value.to_string();
                            let substring = value.get(*start..*end).unwrap_or(&value);
                            attr.value = substring.to_string().into();
                        }
                    }
                }
                TransformRule::ParseJson { key, target_key } => {
                    for attr in attributes.iter() {
                        if attr.key.as_str() == key {
                            if let Ok(json_value) = serde_json::from_str::<Value>(&attr.value.to_string()) {
                                if let Some(extracted) = json_value.get(target_key) {
                                    attributes.push(KeyValue::new(
                                        target_key.clone(),
                                        extracted.to_string(),
                                    ));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[async_trait]
impl Processor for TransformProcessor {
    fn name(&self) -> &str {
        "transform"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        self.apply_transforms(&mut span.attributes);
        Some(span)
    }
}
```

---

## 6. Resource Processor

修改 Resource 信息（服务名、版本、环境等）。

### 6.1 核心实现

```rust
use opentelemetry_sdk::Resource;

pub struct ResourceProcessor {
    additional_attributes: Vec<KeyValue>,
}

impl ResourceProcessor {
    pub fn new(additional_attributes: Vec<KeyValue>) -> Self {
        Self { additional_attributes }
    }
}

#[async_trait]
impl Processor for ResourceProcessor {
    fn name(&self) -> &str {
        "resource"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        // 合并 Resource 属性
        let mut resource_attributes = span.resource.iter().cloned().collect::<Vec<_>>();
        resource_attributes.extend(self.additional_attributes.clone());
        
        span.resource = Arc::new(Resource::new(resource_attributes));
        Some(span)
    }
}
```

### 6.2 配置示例

```yaml
processors:
  resource:
    attributes:
      - key: service.version
        value: "1.0.0"
        action: upsert
      - key: deployment.environment
        value: "production"
        action: insert
```

---

## 7. Memory Limiter Processor

内存压力保护，防止 OOM。

### 7.1 核心实现

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

pub struct MemoryLimiterProcessor {
    current_usage: Arc<AtomicUsize>,
    limit_mib: usize,
    spike_limit_mib: usize,
}

impl MemoryLimiterProcessor {
    pub fn new(limit_mib: usize, spike_limit_mib: usize) -> Self {
        Self {
            current_usage: Arc::new(AtomicUsize::new(0)),
            limit_mib,
            spike_limit_mib,
        }
    }
    
    fn estimate_span_size(&self, span: &SpanData) -> usize {
        // 粗略估算 Span 大小（字节）
        std::mem::size_of::<SpanData>() + span.attributes.len() * 100
    }
    
    fn can_accept(&self, size: usize) -> bool {
        let current = self.current_usage.load(Ordering::Relaxed);
        let limit = self.limit_mib * 1024 * 1024;
        let spike_limit = self.spike_limit_mib * 1024 * 1024;
        
        current + size < limit + spike_limit
    }
}

#[async_trait]
impl Processor for MemoryLimiterProcessor {
    fn name(&self) -> &str {
        "memory_limiter"
    }
    
    async fn process_span(&self, span: SpanData) -> Option<SpanData> {
        let size = self.estimate_span_size(&span);
        
        if self.can_accept(size) {
            self.current_usage.fetch_add(size, Ordering::Relaxed);
            Some(span)
        } else {
            // 丢弃数据（或触发降级）
            eprintln!("Memory limit exceeded, dropping span");
            None
        }
    }
}
```

### 7.2 配置示例

```yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
```

---

## 8. 自定义 Processor 开发

### 8.1 采样 Processor

```rust
use rand::Rng;

pub struct SamplingProcessor {
    sample_rate: f64,  // 0.0 - 1.0
}

impl SamplingProcessor {
    pub fn new(sample_rate: f64) -> Self {
        Self { sample_rate }
    }
}

#[async_trait]
impl Processor for SamplingProcessor {
    fn name(&self) -> &str {
        "sampling"
    }
    
    async fn process_span(&self, span: SpanData) -> Option<SpanData> {
        let mut rng = rand::thread_rng();
        if rng.gen::<f64>() < self.sample_rate {
            Some(span)
        } else {
            None
        }
    }
}
```

### 8.2 PII 脱敏 Processor

```rust
use regex::Regex;

pub struct PiiRedactionProcessor {
    email_regex: Regex,
    phone_regex: Regex,
    credit_card_regex: Regex,
}

impl PiiRedactionProcessor {
    pub fn new() -> Self {
        Self {
            email_regex: Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap(),
            phone_regex: Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap(),
            credit_card_regex: Regex::new(r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b").unwrap(),
        }
    }
    
    fn redact(&self, text: &str) -> String {
        let text = self.email_regex.replace_all(text, "[EMAIL_REDACTED]");
        let text = self.phone_regex.replace_all(&text, "[PHONE_REDACTED]");
        let text = self.credit_card_regex.replace_all(&text, "[CC_REDACTED]");
        text.to_string()
    }
}

#[async_trait]
impl Processor for PiiRedactionProcessor {
    fn name(&self) -> &str {
        "pii_redaction"
    }
    
    async fn process_span(&self, mut span: SpanData) -> Option<SpanData> {
        for attr in &mut span.attributes {
            let value = attr.value.to_string();
            let redacted = self.redact(&value);
            attr.value = redacted.into();
        }
        Some(span)
    }
}
```

---

## 9. 完整示例

### 9.1 多 Processor 管道

```rust
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 Processors
    let memory_limiter = Arc::new(MemoryLimiterProcessor::new(512, 128));
    
    let filter = Arc::new(FilterProcessor::new(
        vec![FilterRule::StatusCodeEquals { code: 200 }],
        false,  // 丢弃 200 状态码
    ));
    
    let attributes = Arc::new(AttributesProcessor::new(vec![
        AttributeAction::Insert {
            key: "environment".to_string(),
            value: "production".to_string(),
        },
        AttributeAction::Delete {
            key: "password".to_string(),
        },
    ]));
    
    let pii_redaction = Arc::new(PiiRedactionProcessor::new());
    
    let batch = Arc::new(BatchProcessor::new(
        1024,
        Duration::from_secs(10),
        |batch| {
            println!("Exporting {} spans", batch.len());
        },
    ));
    
    // 2. 组装 Pipeline
    let processors: Vec<Arc<dyn Processor>> = vec![
        memory_limiter,
        filter,
        attributes,
        pii_redaction,
        batch,
    ];
    
    // 3. 处理数据
    let mut spans = vec![/* ... */];
    
    for processor in processors {
        spans = processor.process_batch(spans).await;
    }
    
    Ok(())
}
```

### 9.2 配置驱动的 Processor 工厂

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ProcessorConfig {
    Batch {
        timeout_secs: u64,
        max_batch_size: usize,
    },
    Attributes {
        actions: Vec<AttributeAction>,
    },
    Filter {
        rules: Vec<FilterRule>,
        keep_matched: bool,
    },
}

pub fn create_processor(config: ProcessorConfig) -> Arc<dyn Processor> {
    match config {
        ProcessorConfig::Batch { timeout_secs, max_batch_size } => {
            Arc::new(BatchProcessor::new(
                max_batch_size,
                Duration::from_secs(timeout_secs),
                |_| {},
            ))
        }
        ProcessorConfig::Attributes { actions } => {
            Arc::new(AttributesProcessor::new(actions))
        }
        ProcessorConfig::Filter { rules, keep_matched } => {
            Arc::new(FilterProcessor::new(rules, keep_matched))
        }
    }
}
```

---

## 总结

Processor 是 Collector 的**数据处理核心**，Rust 实现时需要注意：

1. **链式调用**：多个 Processor 串联处理
2. **不可变性**：尽量避免修改原始数据，返回新副本
3. **错误处理**：Processor 失败时的降级策略
4. **性能优化**：使用 `Arc` 避免拷贝，批量处理
5. **可观测性**：记录处理耗时、丢弃率

通过模块化设计，可以灵活组合不同的 Processors，实现复杂的数据处理逻辑。
