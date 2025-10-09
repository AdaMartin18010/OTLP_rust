# Rust 1.90 OTLP 性能优化完整指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月9日

---

## 目录

- [Rust 1.90 OTLP 性能优化完整指南](#rust-190-otlp-性能优化完整指南)
  - [目录](#目录)
  - [1. 性能优化概述](#1-性能优化概述)
    - [性能目标](#性能目标)
    - [优化优先级矩阵](#优化优先级矩阵)
  - [2. 采样策略](#2-采样策略)
    - [2.1 采样器类型](#21-采样器类型)
    - [2.2 智能采样](#22-智能采样)
  - [3. 批处理优化](#3-批处理优化)
    - [3.1 批处理配置](#31-批处理配置)
    - [3.2 自定义批处理器](#32-自定义批处理器)
  - [4. 零分配优化](#4-零分配优化)
    - [4.1 静态字符串](#41-静态字符串)
    - [4.2 对象池](#42-对象池)
    - [4.3 栈分配](#43-栈分配)
  - [5. 异步性能优化](#5-异步性能优化)
    - [5.1 Tokio Runtime 优化](#51-tokio-runtime-优化)
    - [5.2 避免过度并发](#52-避免过度并发)
  - [6. 编译器优化](#6-编译器优化)
    - [6.1 Cargo.toml 优化](#61-cargotoml-优化)
    - [6.2 CPU 特性](#62-cpu-特性)
  - [7. 内存管理](#7-内存管理)
    - [7.1 内存监控](#71-内存监控)
  - [8. 性能基准测试](#8-性能基准测试)
    - [8.1 Criterion 基准](#81-criterion-基准)
  - [9. 生产环境优化](#9-生产环境优化)
    - [9.1 完整优化配置](#91-完整优化配置)

---

## 1. 性能优化概述

### 性能目标

```rust
/// 性能目标基准
pub struct PerformanceTargets {
    /// 追踪开销 < 5%
    pub tracing_overhead_percent: f64,
    
    /// P99 延迟增加 < 10ms
    pub p99_latency_increase_ms: f64,
    
    /// 内存开销 < 100MB
    pub memory_overhead_mb: usize,
    
    /// CPU 额外使用 < 5%
    pub cpu_overhead_percent: f64,
}

impl PerformanceTargets {
    pub const PRODUCTION: Self = Self {
        tracing_overhead_percent: 5.0,
        p99_latency_increase_ms: 10.0,
        memory_overhead_mb: 100,
        cpu_overhead_percent: 5.0,
    };
}
```

### 优化优先级矩阵

| 优先级 | 优化项 | 影响 | 复杂度 |
|-------|-------|------|--------|
| P0 | 采样策略 | 极高 | 低 |
| P0 | 批处理 | 极高 | 低 |
| P1 | 异步优化 | 高 | 中 |
| P1 | 编译优化 | 高 | 低 |
| P2 | 零分配 | 中 | 高 |

---

## 2. 采样策略

### 2.1 采样器类型

```rust
use opentelemetry_sdk::trace::{Sampler, SamplerDecision, Config};

/// 采样策略
pub enum SamplingStrategy {
    /// 全采样 (开发环境)
    AlwaysOn,
    
    /// 不采样 (禁用追踪)
    AlwaysOff,
    
    /// 按比例采样 (生产环境)
    TraceIdRatio(f64),
    
    /// 基于父 Span 采样
    ParentBased(Box<Sampler>),
    
    /// 自定义采样
    Custom(Box<dyn Fn(&opentelemetry::trace::SpanContext) -> bool + Send + Sync>),
}

impl SamplingStrategy {
    /// 创建生产环境采样器 (10% 采样)
    pub fn production() -> Sampler {
        Sampler::ParentBased(Box::new(
            Sampler::TraceIdRatioBased(0.1) // 10% 采样
        ))
    }
    
    /// 创建开发环境采样器 (全采样)
    pub fn development() -> Sampler {
        Sampler::AlwaysOn
    }
    
    /// 动态采样 (基于错误率)
    pub fn error_based(base_rate: f64, error_multiplier: f64) -> Sampler {
        // 实现自定义采样逻辑
        Sampler::TraceIdRatioBased(base_rate)
    }
}
```

### 2.2 智能采样

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// 动态采样器 (根据负载调整)
pub struct AdaptiveSampler {
    base_rate: f64,
    current_rate: Arc<AtomicU64>,
    error_count: Arc<AtomicU64>,
    total_count: Arc<AtomicU64>,
}

impl AdaptiveSampler {
    pub fn new(base_rate: f64) -> Self {
        Self {
            base_rate,
            current_rate: Arc::new(AtomicU64::new((base_rate * 1000.0) as u64)),
            error_count: Arc::new(AtomicU64::new(0)),
            total_count: Arc::new(AtomicU64::new(0)),
        }
    }
    
    /// 根据错误率调整采样率
    pub fn adjust_rate(&self) {
        let errors = self.error_count.load(Ordering::Relaxed) as f64;
        let total = self.total_count.load(Ordering::Relaxed) as f64;
        
        if total < 100.0 {
            return; // 样本不足
        }
        
        let error_rate = errors / total;
        
        let new_rate = if error_rate > 0.05 {
            // 错误率 > 5%, 提高采样率
            (self.base_rate * 2.0).min(1.0)
        } else if error_rate < 0.01 {
            // 错误率 < 1%, 降低采样率
            (self.base_rate * 0.5).max(0.01)
        } else {
            self.base_rate
        };
        
        self.current_rate.store((new_rate * 1000.0) as u64, Ordering::Relaxed);
        
        // 重置计数器
        self.error_count.store(0, Ordering::Relaxed);
        self.total_count.store(0, Ordering::Relaxed);
    }
    
    /// 判断是否采样
    pub fn should_sample(&self) -> bool {
        self.total_count.fetch_add(1, Ordering::Relaxed);
        
        let rate = self.current_rate.load(Ordering::Relaxed) as f64 / 1000.0;
        
        rand::random::<f64>() < rate
    }
    
    /// 记录错误
    pub fn record_error(&self) {
        self.error_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 使用示例
#[tokio::main]
async fn main() {
    let sampler = Arc::new(AdaptiveSampler::new(0.1));
    
    // 定期调整采样率
    let sampler_clone = sampler.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
            sampler_clone.adjust_rate();
        }
    });
}
```

---

## 3. 批处理优化

### 3.1 批处理配置

```rust
use opentelemetry_sdk::trace::{BatchConfig, BatchSpanProcessor};
use std::time::Duration;

/// 优化的批处理配置
pub fn optimized_batch_config() -> BatchConfig {
    BatchConfig::builder()
        // 批量大小: 更大的批次减少导出次数
        .with_max_export_batch_size(512)
        
        // 队列大小: 防止内存溢出
        .with_max_queue_size(2048)
        
        // 导出延迟: 平衡实时性和性能
        .with_scheduled_delay(Duration::from_millis(500))
        
        // 导出超时
        .with_max_export_timeout(Duration::from_secs(30))
        
        .build()
}

/// 不同环境的配置
pub mod configs {
    use super::*;
    
    /// 开发环境: 低延迟，小批次
    pub fn development() -> BatchConfig {
        BatchConfig::builder()
            .with_max_export_batch_size(32)
            .with_scheduled_delay(Duration::from_millis(100))
            .build()
    }
    
    /// 生产环境: 高吞吐，大批次
    pub fn production() -> BatchConfig {
        BatchConfig::builder()
            .with_max_export_batch_size(512)
            .with_max_queue_size(4096)
            .with_scheduled_delay(Duration::from_millis(1000))
            .build()
    }
    
    /// 高负载环境: 极大批次
    pub fn high_throughput() -> BatchConfig {
        BatchConfig::builder()
            .with_max_export_batch_size(2048)
            .with_max_queue_size(8192)
            .with_scheduled_delay(Duration::from_secs(2))
            .build()
    }
}
```

### 3.2 自定义批处理器

```rust
use tokio::sync::mpsc;

/// 高性能批处理器
pub struct HighPerformanceBatcher<T> {
    tx: mpsc::Sender<T>,
    batch_size: usize,
}

impl<T: Send + 'static> HighPerformanceBatcher<T> {
    pub fn new<F>(batch_size: usize, processor: F) -> Self
    where
        F: Fn(Vec<T>) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send>> + Send + 'static,
    {
        let (tx, mut rx) = mpsc::channel(1000);
        
        tokio::spawn(async move {
            let mut batch = Vec::with_capacity(batch_size);
            let mut interval = tokio::time::interval(Duration::from_millis(500));
            
            loop {
                tokio::select! {
                    Some(item) = rx.recv() => {
                        batch.push(item);
                        
                        if batch.len() >= batch_size {
                            let full_batch = std::mem::replace(
                                &mut batch,
                                Vec::with_capacity(batch_size)
                            );
                            processor(full_batch).await;
                        }
                    }
                    _ = interval.tick() => {
                        if !batch.is_empty() {
                            let current_batch = std::mem::replace(
                                &mut batch,
                                Vec::with_capacity(batch_size)
                            );
                            processor(current_batch).await;
                        }
                    }
                }
            }
        });
        
        Self { tx, batch_size }
    }
    
    pub async fn send(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.tx.send(item).await
    }
}
```

---

## 4. 零分配优化

### 4.1 静态字符串

```rust
// ❌ 运行时分配
span.set_attribute("http.method".to_string(), "GET".to_string());

// ✅ 零分配
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::trace::HTTP_METHOD;

span.set_attribute(HTTP_METHOD.string("GET"));

// ✅ 使用 &'static str
const ATTR_KEY: &str = "custom.key";
span.set_attribute(KeyValue::new(ATTR_KEY, "value"));
```

### 4.2 对象池

```rust
use std::sync::Arc;
use parking_lot::Mutex;

/// Span 数据对象池
pub struct SpanDataPool {
    pool: Arc<Mutex<Vec<Box<SpanData>>>>,
    max_size: usize,
}

impl SpanDataPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(max_size))),
            max_size,
        }
    }
    
    /// 获取或创建 SpanData
    pub fn acquire(&self) -> Box<SpanData> {
        self.pool.lock().pop()
            .unwrap_or_else(|| Box::new(SpanData::default()))
    }
    
    /// 归还 SpanData
    pub fn release(&self, mut span_data: Box<SpanData>) {
        span_data.clear(); // 清理数据
        
        let mut pool = self.pool.lock();
        if pool.len() < self.max_size {
            pool.push(span_data);
        }
    }
}

/// 使用示例
static SPAN_POOL: OnceCell<SpanDataPool> = OnceCell::new();

pub fn init_pool() {
    SPAN_POOL.get_or_init(|| SpanDataPool::new(1000));
}
```

### 4.3 栈分配

```rust
use smallvec::SmallVec;

/// 使用 SmallVec 避免小数组堆分配
pub struct OptimizedAttributes {
    // 大多数 Span 只有 < 8 个属性
    attributes: SmallVec<[KeyValue; 8]>,
}

impl OptimizedAttributes {
    pub fn new() -> Self {
        Self {
            attributes: SmallVec::new(),
        }
    }
    
    pub fn add(&mut self, key: &'static str, value: String) {
        self.attributes.push(KeyValue::new(key, value));
    }
}
```

---

## 5. 异步性能优化

### 5.1 Tokio Runtime 优化

```rust
/// 生产环境 Tokio 配置
pub fn optimized_runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .thread_name("otlp-worker")
        .thread_stack_size(2 * 1024 * 1024) // 2MB
        .enable_all()
        .build()
        .unwrap()
}

/// 专用 runtime for OTLP
pub fn dedicated_otlp_runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2) // 专用线程
        .thread_name("otlp-exporter")
        .enable_io()
        .enable_time()
        .build()
        .unwrap()
}
```

### 5.2 避免过度并发

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

/// 限流器
pub struct RateLimiter {
    semaphore: Arc<Semaphore>,
}

impl RateLimiter {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }
    
    pub async fn acquire(&self) -> tokio::sync::SemaphorePermit<'_> {
        self.semaphore.acquire().await.unwrap()
    }
}

/// 使用示例
#[tracing::instrument]
async fn export_with_rate_limit(
    data: Vec<SpanData>,
    limiter: &RateLimiter,
) -> Result<(), Box<dyn std::error::Error>> {
    let _permit = limiter.acquire().await;
    
    // 导出逻辑
    export_spans(data).await?;
    
    Ok(())
}
```

---

## 6. 编译器优化

### 6.1 Cargo.toml 优化

```toml
[profile.release]
opt-level = 3              # 最大优化
lto = "fat"                # 全局 LTO
codegen-units = 1          # 单一代码生成单元 (最佳优化)
panic = "abort"            # Panic 时直接中止 (避免展开开销)
strip = true               # 移除符号信息

[profile.release.build-override]
opt-level = 3

# 优化依赖
[profile.release.package."*"]
opt-level = 3
```

### 6.2 CPU 特性

```toml
# .cargo/config.toml
[build]
rustflags = [
    "-C", "target-cpu=native",  # 使用本地 CPU 特性
    "-C", "target-feature=+aes,+avx2",
]
```

---

## 7. 内存管理

### 7.1 内存监控

```rust
use sysinfo::{System, SystemExt};

pub struct MemoryMonitor {
    system: System,
}

impl MemoryMonitor {
    pub fn new() -> Self {
        Self {
            system: System::new_all(),
        }
    }
    
    pub fn check_memory_usage(&mut self) -> MemoryStats {
        self.system.refresh_memory();
        
        MemoryStats {
            used_mb: self.system.used_memory() / 1024 / 1024,
            total_mb: self.system.total_memory() / 1024 / 1024,
            available_mb: self.system.available_memory() / 1024 / 1024,
        }
    }
}

#[derive(Debug)]
pub struct MemoryStats {
    pub used_mb: u64,
    pub total_mb: u64,
    pub available_mb: u64,
}
```

---

## 8. 性能基准测试

### 8.1 Criterion 基准

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_tracing(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    c.bench_function("create_span", |b| {
        b.iter(|| {
            let tracer = opentelemetry::global::tracer("bench");
            let _span = tracer.start(black_box("test-span"));
        });
    });
    
    c.bench_function("traced_function", |b| {
        b.to_async(&rt).iter(|| async {
            traced_operation(black_box(100)).await
        });
    });
}

#[tracing::instrument]
async fn traced_operation(n: u64) -> u64 {
    n * 2
}

criterion_group!(benches, benchmark_tracing);
criterion_main!(benches);
```

---

## 9. 生产环境优化

### 9.1 完整优化配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::{Config, TracerProvider};

pub async fn init_production_telemetry() -> TracerProvider {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://collector:4317")
        .build_span_exporter()
        .unwrap();
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(
            exporter,
            tokio::spawn,
            configs::production(), // 大批次配置
        )
        .with_config(
            Config::default()
                .with_sampler(SamplingStrategy::production()) // 10% 采样
                .with_max_attributes_per_span(32)
                .with_max_events_per_span(128)
        )
        .with_resource(opentelemetry_sdk::Resource::new(vec![
            KeyValue::new("service.name", "production-service"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    provider
}
```

---

**相关文档**:

- [基准测试框架](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)
- [SDK最佳实践](../04_核心组件/03_SDK最佳实践_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
