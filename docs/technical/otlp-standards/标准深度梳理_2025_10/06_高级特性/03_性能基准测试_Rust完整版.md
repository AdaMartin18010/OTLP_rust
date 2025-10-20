# 性能基准测试 - Rust 完整版

## 目录

- [性能基准测试 - Rust 完整版](#性能基准测试---rust-完整版)
  - [目录](#目录)
  - [1. 性能测试概述](#1-性能测试概述)
    - [1.1 核心指标](#11-核心指标)
    - [1.2 测试场景](#12-测试场景)
  - [2. Criterion 基准测试](#2-criterion-基准测试)
    - [2.1 基本配置](#21-基本配置)
    - [2.2 Span 序列化基准测试](#22-span-序列化基准测试)
    - [2.3 批处理性能测试](#23-批处理性能测试)
    - [2.4 采样器性能测试](#24-采样器性能测试)
  - [3. 负载测试](#3-负载测试)
    - [3.1 使用 `tokio-test` 进行异步负载测试](#31-使用-tokio-test-进行异步负载测试)
    - [3.2 使用 `k6` 进行 HTTP 负载测试](#32-使用-k6-进行-http-负载测试)
  - [4. 并发性能测试](#4-并发性能测试)
    - [4.1 多线程并发测试](#41-多线程并发测试)
    - [4.2 异步并发测试](#42-异步并发测试)
  - [5. 内存性能测试](#5-内存性能测试)
    - [5.1 内存分配分析](#51-内存分配分析)
    - [5.2 内存泄漏检测](#52-内存泄漏检测)
  - [6. 端到端性能测试](#6-端到端性能测试)
    - [6.1 完整链路测试](#61-完整链路测试)
  - [7. 性能监控与分析](#7-性能监控与分析)
    - [7.1 使用 `pprof` 进行 CPU 分析](#71-使用-pprof-进行-cpu-分析)
    - [7.2 延迟分布统计](#72-延迟分布统计)
  - [8. 完整示例](#8-完整示例)
    - [8.1 综合性能测试套件](#81-综合性能测试套件)
    - [8.2 运行测试](#82-运行测试)
  - [总结](#总结)

---

## 1. 性能测试概述

性能测试是确保 OTLP 系统满足 **吞吐量、延迟、资源利用率** 要求的关键手段。

### 1.1 核心指标

```text
┌────────────────────────────────────────┐
│  吞吐量 (Throughput)                   │
│  - Spans/秒                            │
│  - Metrics/秒                          │
│  - Logs/秒                             │
└────────────────────────────────────────┘

┌────────────────────────────────────────┐
│  延迟 (Latency)                        │
│  - P50 (中位数)                        │
│  - P95                                 │
│  - P99                                 │
│  - P99.9                               │
└────────────────────────────────────────┘

┌────────────────────────────────────────┐
│  资源利用率 (Resource Usage)           │
│  - CPU 使用率                          │
│  - 内存占用                            │
│  - 网络带宽                            │
└────────────────────────────────────────┘
```

### 1.2 测试场景

- **微基准测试**：单个函数/模块性能
- **组件测试**：Receiver、Processor、Exporter 性能
- **集成测试**：端到端性能
- **压力测试**：极限负载下的表现
- **稳定性测试**：长时间运行的稳定性

---

## 2. Criterion 基准测试

### 2.1 基本配置

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports", "async_tokio"] }

[[bench]]
name = "otlp_benchmarks"
harness = false
```

### 2.2 Span 序列化基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use opentelemetry_sdk::export::trace::SpanData;
use opentelemetry_proto::tonic::trace::v1::Span;

fn span_serialization_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("span_serialization");
    
    // 创建测试数据
    let span = create_test_span();
    
    group.bench_function("protobuf", |b| {
        b.iter(|| {
            let proto_span = convert_to_proto(black_box(&span));
            black_box(proto_span);
        });
    });
    
    group.bench_function("json", |b| {
        b.iter(|| {
            let json = serde_json::to_string(black_box(&span)).unwrap();
            black_box(json);
        });
    });
    
    group.finish();
}

fn create_test_span() -> SpanData {
    // 创建包含典型属性的 Span
    todo!()
}

fn convert_to_proto(span: &SpanData) -> Span {
    // 转换为 Protobuf 格式
    todo!()
}

criterion_group!(benches, span_serialization_benchmark);
criterion_main!(benches);
```

### 2.3 批处理性能测试

```rust
fn batch_processor_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_processor");
    
    for batch_size in [100, 500, 1000, 5000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(batch_size),
            batch_size,
            |b, &size| {
                let spans: Vec<SpanData> = (0..size).map(|_| create_test_span()).collect();
                let processor = BatchProcessor::new(size, Duration::from_secs(10), |_| {});
                
                b.iter(|| {
                    for span in &spans {
                        let _ = processor.add(black_box(span.clone()));
                    }
                });
            },
        );
    }
    
    group.finish();
}
```

### 2.4 采样器性能测试

```rust
fn sampler_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("samplers");
    
    let trace_id = TraceId::from_bytes([1u8; 16]);
    
    // AlwaysOn Sampler
    group.bench_function("always_on", |b| {
        let sampler = AlwaysOnSampler;
        b.iter(|| {
            let result = sampler.should_sample(
                None,
                black_box(trace_id),
                "test-span",
                SpanKind::Internal,
                &[],
                &[],
            );
            black_box(result);
        });
    });
    
    // TraceIdRatioBased Sampler
    group.bench_function("ratio_based", |b| {
        let sampler = TraceIdRatioBasedSampler::new(0.1);
        b.iter(|| {
            let result = sampler.should_sample(
                None,
                black_box(trace_id),
                "test-span",
                SpanKind::Internal,
                &[],
                &[],
            );
            black_box(result);
        });
    });
    
    group.finish();
}
```

---

## 3. 负载测试

### 3.1 使用 `tokio-test` 进行异步负载测试

```rust
use tokio::time::{Duration, Instant};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[tokio::test]
async fn load_test_otlp_receiver() {
    let (receiver, mut rx, _, _) = OtlpGrpcReceiver::new(
        "127.0.0.1:4317".parse().unwrap(),
        10000,
    );
    
    // 启动接收器
    let mut receiver = receiver;
    tokio::spawn(async move {
        receiver.start().await.unwrap();
    });
    
    // 等待启动
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    // 发送负载
    let total_requests = Arc::new(AtomicU64::new(0));
    let start = Instant::now();
    let duration = Duration::from_secs(10);
    
    let mut tasks = Vec::new();
    
    for _ in 0..10 {
        let total = total_requests.clone();
        let task = tokio::spawn(async move {
            let client = create_test_client("http://127.0.0.1:4317").await;
            
            while start.elapsed() < duration {
                let request = create_test_request();
                let _ = client.export(request).await;
                total.fetch_add(1, Ordering::Relaxed);
            }
        });
        tasks.push(task);
    }
    
    for task in tasks {
        task.await.unwrap();
    }
    
    let elapsed = start.elapsed();
    let total = total_requests.load(Ordering::Relaxed);
    let qps = total as f64 / elapsed.as_secs_f64();
    
    println!("Load Test Results:");
    println!("  Total Requests: {}", total);
    println!("  Duration: {:?}", elapsed);
    println!("  QPS: {:.2}", qps);
    
    assert!(qps > 1000.0, "QPS too low: {}", qps);
}

async fn create_test_client(endpoint: &str) -> TraceServiceClient<Channel> {
    let channel = Channel::from_shared(endpoint.to_string())
        .unwrap()
        .connect()
        .await
        .unwrap();
    TraceServiceClient::new(channel)
}

fn create_test_request() -> ExportTraceServiceRequest {
    // 创建测试请求
    todo!()
}
```

### 3.2 使用 `k6` 进行 HTTP 负载测试

```javascript
// k6_load_test.js
import http from 'k6/http';
import { check, sleep } from 'k6';

export let options = {
  stages: [
    { duration: '30s', target: 100 },  // 30秒内升至 100 VUs
    { duration: '1m', target: 100 },   // 保持 1 分钟
    { duration: '30s', target: 200 },  // 升至 200 VUs
    { duration: '1m', target: 200 },   // 保持 1 分钟
    { duration: '30s', target: 0 },    // 降至 0
  ],
  thresholds: {
    http_req_duration: ['p(95)<500', 'p(99)<1000'],  // 95% < 500ms, 99% < 1s
    http_req_failed: ['rate<0.01'],                   // 错误率 < 1%
  },
};

export default function () {
  const payload = JSON.stringify({
    resourceSpans: [{
      resource: {
        attributes: [{ key: 'service.name', value: { stringValue: 'test-service' } }]
      },
      scopeSpans: [{
        spans: [{
          traceId: generateTraceId(),
          spanId: generateSpanId(),
          name: 'test-span',
          kind: 1,
          startTimeUnixNano: Date.now() * 1000000,
          endTimeUnixNano: (Date.now() + 100) * 1000000,
        }]
      }]
    }]
  });

  const headers = {
    'Content-Type': 'application/json',
    'x-api-key': 'test-key',
  };

  const res = http.post('http://localhost:4318/v1/traces', payload, { headers });

  check(res, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });
}

function generateTraceId() {
  return Array.from({length: 32}, () => Math.floor(Math.random() * 16).toString(16)).join('');
}

function generateSpanId() {
  return Array.from({length: 16}, () => Math.floor(Math.random() * 16).toString(16)).join('');
}
```

运行命令：

```bash
k6 run k6_load_test.js
```

---

## 4. 并发性能测试

### 4.1 多线程并发测试

```rust
use std::thread;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

#[test]
fn concurrent_span_processing() {
    let processor = Arc::new(BatchProcessor::new(1000, Duration::from_secs(1), |_| {}));
    let total_processed = Arc::new(AtomicU64::new(0));
    
    let num_threads = 10;
    let spans_per_thread = 10000;
    
    let start = Instant::now();
    
    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let processor = processor.clone();
            let total = total_processed.clone();
            
            thread::spawn(move || {
                for _ in 0..spans_per_thread {
                    let span = create_test_span();
                    let _ = processor.add(span);
                    total.fetch_add(1, Ordering::Relaxed);
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let elapsed = start.elapsed();
    let total = total_processed.load(Ordering::Relaxed);
    let throughput = total as f64 / elapsed.as_secs_f64();
    
    println!("Concurrent Processing Results:");
    println!("  Threads: {}", num_threads);
    println!("  Total Spans: {}", total);
    println!("  Duration: {:?}", elapsed);
    println!("  Throughput: {:.2} spans/sec", throughput);
    
    assert!(throughput > 100_000.0, "Throughput too low");
}
```

### 4.2 异步并发测试

```rust
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn async_concurrent_export() {
    let exporter = Arc::new(OtlpGrpcExporter::new("http://localhost:4317".to_string()).await.unwrap());
    let total_exported = Arc::new(AtomicU64::new(0));
    
    let num_tasks = 100;
    let spans_per_task = 1000;
    
    let start = Instant::now();
    
    let tasks: Vec<_> = (0..num_tasks)
        .map(|_| {
            let exporter = exporter.clone();
            let total = total_exported.clone();
            
            tokio::spawn(async move {
                for _ in 0..spans_per_task {
                    let spans = vec![create_test_span()];
                    let _ = exporter.export_traces(spans).await;
                    total.fetch_add(1, Ordering::Relaxed);
                }
            })
        })
        .collect();
    
    for task in tasks {
        task.await.unwrap();
    }
    
    let elapsed = start.elapsed();
    let total = total_exported.load(Ordering::Relaxed);
    let throughput = total as f64 / elapsed.as_secs_f64();
    
    println!("Async Concurrent Export Results:");
    println!("  Tasks: {}", num_tasks);
    println!("  Total Spans: {}", total);
    println!("  Duration: {:?}", elapsed);
    println!("  Throughput: {:.2} spans/sec", throughput);
}
```

---

## 5. 内存性能测试

### 5.1 内存分配分析

```rust
#[cfg(target_os = "linux")]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[test]
fn memory_allocation_test() {
    use jemalloc_ctl::{stats, epoch};
    
    // 更新统计
    epoch::mib().unwrap().advance().unwrap();
    let allocated_before = stats::allocated::mib().unwrap().read().unwrap();
    
    // 执行操作
    let mut spans = Vec::new();
    for _ in 0..100_000 {
        spans.push(create_test_span());
    }
    
    // 更新统计
    epoch::mib().unwrap().advance().unwrap();
    let allocated_after = stats::allocated::mib().unwrap().read().unwrap();
    
    let memory_used = allocated_after - allocated_before;
    let bytes_per_span = memory_used / 100_000;
    
    println!("Memory Allocation Results:");
    println!("  Total Memory: {} bytes", memory_used);
    println!("  Per Span: {} bytes", bytes_per_span);
    
    assert!(bytes_per_span < 1024, "Memory per span too high");
}
```

### 5.2 内存泄漏检测

```rust
#[tokio::test]
async fn memory_leak_test() {
    let initial_memory = get_current_memory_usage();
    
    // 运行多次迭代
    for _ in 0..100 {
        let spans: Vec<_> = (0..1000).map(|_| create_test_span()).collect();
        
        // 处理 Spans
        let processor = BatchProcessor::new(1000, Duration::from_secs(1), |_| {});
        for span in spans {
            let _ = processor.add(span).await;
        }
        
        // 强制释放
        drop(processor);
    }
    
    // 触发 GC
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    let final_memory = get_current_memory_usage();
    let memory_increase = final_memory - initial_memory;
    
    println!("Memory Leak Test:");
    println!("  Initial: {} MB", initial_memory / 1024 / 1024);
    println!("  Final: {} MB", final_memory / 1024 / 1024);
    println!("  Increase: {} MB", memory_increase / 1024 / 1024);
    
    assert!(memory_increase < 10 * 1024 * 1024, "Potential memory leak detected");
}

fn get_current_memory_usage() -> usize {
    #[cfg(target_os = "linux")]
    {
        use jemalloc_ctl::stats;
        stats::allocated::mib().unwrap().read().unwrap()
    }
    
    #[cfg(not(target_os = "linux"))]
    {
        0
    }
}
```

---

## 6. 端到端性能测试

### 6.1 完整链路测试

```rust
#[tokio::test]
async fn end_to_end_performance_test() {
    // 1. 启动 Collector
    let config = CollectorConfig::load("test-config.yaml").unwrap();
    let mut service = PipelineBuilder::new(config).build().await.unwrap();
    service.start().await.unwrap();
    
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    // 2. 创建客户端
    let client = create_otlp_client("http://localhost:4317").await;
    
    // 3. 发送数据
    let num_traces = 10_000;
    let start = Instant::now();
    
    for _ in 0..num_traces {
        let request = create_test_request();
        let _ = client.export(request).await;
    }
    
    let send_duration = start.elapsed();
    
    // 4. 等待处理完成
    tokio::time::sleep(Duration::from_secs(5)).await;
    
    let total_duration = start.elapsed();
    
    println!("End-to-End Performance:");
    println!("  Traces Sent: {}", num_traces);
    println!("  Send Duration: {:?}", send_duration);
    println!("  Total Duration: {:?}", total_duration);
    println!("  Send Throughput: {:.2} traces/sec", 
             num_traces as f64 / send_duration.as_secs_f64());
    
    // 5. 关闭 Collector
    service.shutdown().await.unwrap();
}
```

---

## 7. 性能监控与分析

### 7.1 使用 `pprof` 进行 CPU 分析

```rust
use pprof::ProfilerGuard;

#[test]
fn cpu_profiling_test() {
    let guard = ProfilerGuard::new(100).unwrap();
    
    // 执行性能测试
    for _ in 0..1_000_000 {
        let span = create_test_span();
        let _ = convert_to_proto(&span);
    }
    
    // 生成 Flamegraph
    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();
        println!("Flamegraph saved to flamegraph.svg");
    }
}
```

### 7.2 延迟分布统计

```rust
use hdrhistogram::Histogram;

#[tokio::test]
async fn latency_distribution_test() {
    let mut histogram = Histogram::<u64>::new(3).unwrap();
    
    let exporter = OtlpGrpcExporter::new("http://localhost:4317".to_string()).await.unwrap();
    
    for _ in 0..10_000 {
        let start = Instant::now();
        
        let spans = vec![create_test_span()];
        let _ = exporter.export_traces(spans).await;
        
        let latency_micros = start.elapsed().as_micros() as u64;
        histogram.record(latency_micros).unwrap();
    }
    
    println!("Latency Distribution:");
    println!("  P50:  {} μs", histogram.value_at_quantile(0.50));
    println!("  P90:  {} μs", histogram.value_at_quantile(0.90));
    println!("  P95:  {} μs", histogram.value_at_quantile(0.95));
    println!("  P99:  {} μs", histogram.value_at_quantile(0.99));
    println!("  P99.9: {} μs", histogram.value_at_quantile(0.999));
    println!("  Max:  {} μs", histogram.max());
}
```

---

## 8. 完整示例

### 8.1 综合性能测试套件

```rust
// benches/comprehensive.rs

use criterion::{criterion_group, criterion_main, Criterion};

fn comprehensive_benchmark(c: &mut Criterion) {
    // 1. 序列化性能
    span_serialization_benchmark(c);
    
    // 2. 批处理性能
    batch_processor_benchmark(c);
    
    // 3. 采样器性能
    sampler_benchmark(c);
    
    // 4. Exporter 性能
    exporter_benchmark(c);
}

fn exporter_benchmark(c: &mut Criterion) {
    let runtime = tokio::runtime::Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("exporters");
    
    group.bench_function("otlp_grpc", |b| {
        b.to_async(&runtime).iter(|| async {
            let exporter = OtlpGrpcExporter::new("http://localhost:4317".to_string())
                .await
                .unwrap();
            
            let spans = vec![create_test_span()];
            let _ = exporter.export_traces(spans).await;
        });
    });
    
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .sample_size(100)
        .measurement_time(Duration::from_secs(10));
    targets = comprehensive_benchmark
);
criterion_main!(benches);
```

### 8.2 运行测试

```bash
# 运行基准测试
cargo bench

# 查看 HTML 报告
open target/criterion/report/index.html

# 运行负载测试
cargo test --test load_test -- --nocapture

# CPU 分析
cargo test --test cpu_profiling -- --nocapture

# 内存分析
cargo test --test memory_test -- --nocapture
```

---

## 总结

性能基准测试是 OTLP 系统质量保证的**关键环节**，Rust 实现时需要：

1. **微基准测试**：使用 `criterion` 测试关键函数
2. **负载测试**：使用 `tokio-test` 或 `k6` 模拟真实负载
3. **并发测试**：验证多线程/异步并发性能
4. **内存分析**：使用 `jemalloc` 检测内存泄漏
5. **端到端测试**：验证完整链路性能
6. **性能监控**：使用 `pprof`、`hdrhistogram` 分析瓶颈

**性能目标参考**：

- 吞吐量：单机 100k+ spans/sec
- P99 延迟：< 10ms
- 内存占用：< 500 bytes/span
- CPU 利用率：< 80%

通过持续的性能测试和优化，可以确保 OTLP 系统在生产环境中的高性能运行。
