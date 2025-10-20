# 🦀 性能优化速查手册 - Rust OTLP版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 性能优化速查手册 - Rust OTLP版](#-性能优化速查手册---rust-otlp版)
  - [📋 快速索引](#-快速索引)
  - [🎯 采样优化](#-采样优化)
    - [智能采样策略](#智能采样策略)
    - [自定义采样器](#自定义采样器)
  - [📦 批处理优化](#-批处理优化)
    - [配置建议](#配置建议)
    - [动态批处理](#动态批处理)
  - [🗜️ 压缩策略](#️-压缩策略)
    - [gRPC压缩对比](#grpc压缩对比)
    - [条件压缩](#条件压缩)
  - [💾 资源管理](#-资源管理)
    - [内存池化](#内存池化)
    - [连接池](#连接池)
  - [⚡ 异步优化](#-异步优化)
    - [并行导出](#并行导出)
    - [非阻塞追踪](#非阻塞追踪)
  - [🎯 属性优化](#-属性优化)
    - [减少高基数属性](#减少高基数属性)
  - [📊 基准测试](#-基准测试)
    - [性能测试套件](#性能测试套件)
    - [负载测试](#负载测试)
  - [🏆 最佳实践总结](#-最佳实践总结)
    - [配置检查清单](#配置检查清单)
    - [性能优化顺序](#性能优化顺序)
  - [📈 性能指标](#-性能指标)
    - [目标指标](#目标指标)
  - [📚 参考资源](#-参考资源)

---

## 🎯 采样优化

### 智能采样策略

```rust
use opentelemetry_sdk::trace::Sampler;

/// 推荐: 父级采样 + 比例采样
pub fn production_sampler() -> Sampler {
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1) // 10%采样
    ))
}

/// 开发环境: 100%采样
pub fn dev_sampler() -> Sampler {
    Sampler::AlwaysOn
}

/// 高流量场景: 1%采样
pub fn high_traffic_sampler() -> Sampler {
    Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.01)
    ))
}
```

### 自定义采样器

```rust
use opentelemetry::{
    trace::{SamplingDecision, SamplingResult, TraceId, SpanKind},
    Context, KeyValue,
};
use opentelemetry_sdk::trace::{Sampler, ShouldSample};

/// 基于URL路径的智能采样
pub struct PathBasedSampler {
    high_priority_paths: Vec<String>,
    default_rate: f64,
}

impl PathBasedSampler {
    pub fn new(high_priority_paths: Vec<String>, default_rate: f64) -> Self {
        Self {
            high_priority_paths,
            default_rate,
        }
    }
}

impl ShouldSample for PathBasedSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        _links: &[opentelemetry::trace::Link],
    ) -> SamplingResult {
        // 检查是否是高优先级路径
        let is_high_priority = self.high_priority_paths
            .iter()
            .any(|path| name.contains(path));
        
        let sampling_rate = if is_high_priority { 1.0 } else { self.default_rate };
        
        // 使用TraceID进行一致性采样
        let trace_id_upper = trace_id.to_bytes()[0..8]
            .iter()
            .fold(0u64, |acc, &b| (acc << 8) | b as u64);
        
        let threshold = (sampling_rate * u64::MAX as f64) as u64;
        
        if trace_id_upper < threshold {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: Default::default(),
            }
        }
    }
}

// 使用示例
let sampler = PathBasedSampler::new(
    vec!["/api/checkout".to_string(), "/api/payment".to_string()],
    0.05, // 其他路径5%采样
);
```

---

## 📦 批处理优化

### 配置建议

```rust
use opentelemetry_sdk::trace::Config;
use std::time::Duration;

/// 高吞吐量配置
pub fn high_throughput_config() -> Config {
    Config::default()
        .with_max_export_batch_size(2048)      // 大批次
        .with_max_queue_size(8192)             // 大队列
        .with_scheduled_delay(Duration::from_secs(10)) // 延迟导出
}

/// 低延迟配置
pub fn low_latency_config() -> Config {
    Config::default()
        .with_max_export_batch_size(256)       // 小批次
        .with_max_queue_size(1024)             // 小队列
        .with_scheduled_delay(Duration::from_millis(500)) // 快速导出
}

/// 平衡配置 (推荐生产)
pub fn balanced_config() -> Config {
    Config::default()
        .with_max_export_batch_size(1024)
        .with_max_queue_size(4096)
        .with_scheduled_delay(Duration::from_secs(5))
}
```

### 动态批处理

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct AdaptiveBatchConfig {
    current_batch_size: Arc<RwLock<usize>>,
    min_batch: usize,
    max_batch: usize,
}

impl AdaptiveBatchConfig {
    pub fn new() -> Self {
        Self {
            current_batch_size: Arc::new(RwLock::new(512)),
            min_batch: 128,
            max_batch: 2048,
        }
    }
    
    /// 根据负载调整批次大小
    pub async fn adjust_based_on_load(&self, queue_depth: usize) {
        let mut batch_size = self.current_batch_size.write().await;
        
        if queue_depth > 1000 {
            // 队列积压，增大批次
            *batch_size = (*batch_size * 2).min(self.max_batch);
        } else if queue_depth < 100 {
            // 队列空闲，减小批次
            *batch_size = (*batch_size / 2).max(self.min_batch);
        }
    }
    
    pub async fn get_batch_size(&self) -> usize {
        *self.current_batch_size.read().await
    }
}
```

---

## 🗜️ 压缩策略

### gRPC压缩对比

```rust
use tonic::codec::CompressionEncoding;

/// 性能对比
pub fn compression_benchmark() {
    println!("压缩算法对比:");
    println!("┌─────────┬──────────┬───────────┬─────────────┐");
    println!("│ 算法    │ 压缩率   │ CPU开销   │ 推荐场景    │");
    println!("├─────────┼──────────┼───────────┼─────────────┤");
    println!("│ None    │ 0%       │ 最低      │ 内网        │");
    println!("│ Gzip    │ 70-80%   │ 中等      │ 生产推荐    │");
    println!("│ Snappy  │ 50-60%   │ 低        │ 高吞吐      │");
    println!("│ Zstd    │ 75-85%   │ 低-中     │ 最佳压缩    │");
    println!("└─────────┴──────────┴───────────┴─────────────┘");
}

/// 推荐配置
pub fn recommended_compression() -> CompressionEncoding {
    // 生产环境推荐
    CompressionEncoding::Gzip
}

/// 高吞吐场景
pub fn high_throughput_compression() -> CompressionEncoding {
    CompressionEncoding::Snappy
}
```

### 条件压缩

```rust
use opentelemetry_otlp::SpanExporter;

pub async fn create_exporter_with_conditional_compression(
    data_size_bytes: usize,
) -> anyhow::Result<SpanExporter> {
    // 只有数据量大时才使用压缩
    let compression = if data_size_bytes > 1024 {
        Some(CompressionEncoding::Gzip)
    } else {
        None
    };
    
    let mut builder = SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317");
    
    if let Some(comp) = compression {
        builder = builder.with_compression(comp);
    }
    
    builder.build()
}
```

---

## 💾 资源管理

### 内存池化

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

/// Span池化
pub struct SpanPool {
    semaphore: Arc<Semaphore>,
    max_concurrent_spans: usize,
}

impl SpanPool {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent_spans: max_concurrent,
        }
    }
    
    pub async fn acquire(&self) -> Result<SpanGuard, anyhow::Error> {
        let permit = self.semaphore.clone().acquire_owned().await?;
        Ok(SpanGuard { _permit: permit })
    }
}

pub struct SpanGuard {
    _permit: tokio::sync::OwnedSemaphorePermit,
}

// 使用
let pool = SpanPool::new(1000);
let _guard = pool.acquire().await?; // 限制并发Span数
```

### 连接池

```rust
use std::time::Duration;

pub struct ExporterPool {
    exporters: Vec<Arc<SpanExporter>>,
    current_index: Arc<AtomicUsize>,
}

impl ExporterPool {
    pub fn new(endpoint: &str, pool_size: usize) -> anyhow::Result<Self> {
        let exporters: Result<Vec<_>, _> = (0..pool_size)
            .map(|_| {
                SpanExporter::builder()
                    .with_endpoint(endpoint)
                    .with_timeout(Duration::from_secs(30))
                    .build()
                    .map(Arc::new)
            })
            .collect();
        
        Ok(Self {
            exporters: exporters?,
            current_index: Arc::new(AtomicUsize::new(0)),
        })
    }
    
    pub fn get_exporter(&self) -> Arc<SpanExporter> {
        let index = self.current_index.fetch_add(1, Ordering::Relaxed);
        self.exporters[index % self.exporters.len()].clone()
    }
}
```

---

## ⚡ 异步优化

### 并行导出

```rust
use futures::future::join_all;

pub async fn export_traces_parallel(
    traces: Vec<TraceBatch>,
    exporter: &SpanExporter,
) -> Vec<Result<(), anyhow::Error>> {
    // 并行导出多个批次
    let futures = traces
        .into_iter()
        .map(|batch| async move {
            exporter.export(batch).await
        });
    
    join_all(futures).await
        .into_iter()
        .map(|r| r.map_err(Into::into))
        .collect()
}
```

### 非阻塞追踪

```rust
use tokio::task;

pub async fn non_blocking_trace<F, Fut>(
    tracer: &dyn Tracer,
    name: &str,
    operation: F,
) -> anyhow::Result<()>
where
    F: FnOnce() -> Fut + Send + 'static,
    Fut: Future<Output = ()> + Send + 'static,
{
    let mut span = tracer.start(name);
    
    // 在后台执行
    let handle = task::spawn(async move {
        operation().await;
        span.end();
    });
    
    // 不等待完成
    Ok(())
}
```

---

## 🎯 属性优化

### 减少高基数属性

```rust
use std::collections::HashMap;

/// 属性白名单
pub struct AttributeFilter {
    allowed_keys: HashMap<String, usize>, // key -> max_length
}

impl AttributeFilter {
    pub fn new() -> Self {
        let mut allowed_keys = HashMap::new();
        allowed_keys.insert("http.method".to_string(), 10);
        allowed_keys.insert("http.status_code".to_string(), 3);
        allowed_keys.insert("db.system".to_string(), 20);
        
        Self { allowed_keys }
    }
    
    pub fn filter(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .filter(|kv| {
                self.allowed_keys.contains_key(kv.key.as_str())
            })
            .map(|mut kv| {
                // 截断过长的值
                if let Some(&max_len) = self.allowed_keys.get(kv.key.as_str()) {
                    if let Some(s) = kv.value.as_str() {
                        if s.len() > max_len {
                            kv.value = format!("{}...", &s[..max_len]).into();
                        }
                    }
                }
                kv
            })
            .collect()
    }
}
```

---

## 📊 基准测试

### 性能测试套件

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use opentelemetry::{global, trace::Tracer, KeyValue};

fn bench_span_creation(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_creation", |b| {
        b.iter(|| {
            let mut span = tracer.start("test");
            span.end();
        });
    });
}

fn bench_span_with_attributes(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_with_10_attributes", |b| {
        b.iter(|| {
            let mut span = tracer.start("test");
            for i in 0..10 {
                span.set_attribute(KeyValue::new(
                    format!("attr{}", i),
                    i as i64
                ));
            }
            span.end();
        });
    });
}

fn bench_export_batch(c: &mut Criterion) {
    // 设置exporter
    
    c.bench_function("export_1000_spans", |b| {
        b.iter(|| {
            let tracer = global::tracer("benchmark");
            for i in 0..1000 {
                let mut span = tracer.start(format!("span-{}", i));
                span.end();
            }
            // flush
        });
    });
}

criterion_group!(
    benches,
    bench_span_creation,
    bench_span_with_attributes,
    bench_export_batch
);
criterion_main!(benches);
```

### 负载测试

```rust
use tokio::time::{Duration, interval};
use std::sync::atomic::{AtomicU64, Ordering};

pub async fn load_test(
    duration_secs: u64,
    requests_per_sec: u64,
) -> LoadTestResult {
    let tracer = global::tracer("load-test");
    let counter = Arc::new(AtomicU64::new(0));
    let errors = Arc::new(AtomicU64::new(0));
    
    let mut interval = interval(Duration::from_millis(1000 / requests_per_sec));
    let start = std::time::Instant::now();
    
    while start.elapsed().as_secs() < duration_secs {
        interval.tick().await;
        
        let counter = counter.clone();
        let errors = errors.clone();
        let tracer = tracer.clone();
        
        tokio::spawn(async move {
            let mut span = tracer.start("load-test-span");
            span.set_attribute(KeyValue::new("test.iteration", 
                counter.load(Ordering::Relaxed) as i64));
            
            // 模拟工作
            tokio::time::sleep(Duration::from_millis(10)).await;
            
            span.end();
            counter.fetch_add(1, Ordering::Relaxed);
        });
    }
    
    // 等待完成
    tokio::time::sleep(Duration::from_secs(5)).await;
    
    LoadTestResult {
        total_requests: counter.load(Ordering::Relaxed),
        errors: errors.load(Ordering::Relaxed),
        duration: duration_secs,
    }
}

pub struct LoadTestResult {
    pub total_requests: u64,
    pub errors: u64,
    pub duration: u64,
}

impl LoadTestResult {
    pub fn print_summary(&self) {
        println!("\n📊 Load Test Results:");
        println!("   Duration: {}s", self.duration);
        println!("   Total requests: {}", self.total_requests);
        println!("   Errors: {}", self.errors);
        println!("   RPS: {:.2}", self.total_requests as f64 / self.duration as f64);
        println!("   Error rate: {:.2}%", 
            (self.errors as f64 / self.total_requests as f64) * 100.0);
    }
}
```

---

## 🏆 最佳实践总结

### 配置检查清单

```rust
pub fn validate_production_config(config: &Config) -> Vec<String> {
    let mut warnings = Vec::new();
    
    // 1. 批次大小
    if config.max_export_batch_size < 512 {
        warnings.push("批次大小过小，建议>=512".to_string());
    }
    
    // 2. 队列大小
    if config.max_queue_size < 2048 {
        warnings.push("队列大小过小，建议>=2048".to_string());
    }
    
    // 3. 采样率
    // (检查采样器配置)
    
    warnings
}
```

### 性能优化顺序

1. **采样**: 最高优先级，减少数据量
2. **批处理**: 减少网络往返
3. **压缩**: 减少带宽
4. **异步**: 减少阻塞
5. **连接池**: 复用连接

---

## 📈 性能指标

### 目标指标

| 指标 | 目标值 | 说明 |
|------|--------|------|
| **Span创建延迟** | <1μs | 单个Span创建时间 |
| **导出延迟** | <100ms | P99 |
| **内存开销** | <50MB | 稳定状态 |
| **CPU开销** | <5% | 空闲时 |
| **吞吐量** | >10K spans/s | 单实例 |

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **性能最佳实践** | <https://opentelemetry.io/docs/specs/otel/performance/> |
| **Rust性能指南** | <https://nnethercote.github.io/perf-book/> |
| **Criterion.rs** | <https://github.com/bheisler/criterion.rs> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [故障排查速查手册_Rust版](./04_故障排查速查手册_Rust版.md)  
**下一篇**: [安全配置速查手册_Rust版](./06_安全配置速查手册_Rust版.md)
