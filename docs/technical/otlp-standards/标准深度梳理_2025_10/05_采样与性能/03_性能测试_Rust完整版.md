# 性能测试 - Rust 完整版

## 目录

- [性能测试 - Rust 完整版](#性能测试---rust-完整版)
  - [目录](#目录)
  - [1. 性能测试概述](#1-性能测试概述)
    - [1.1 测试类型](#11-测试类型)
    - [1.2 测试指标](#12-测试指标)
  - [2. Criterion 基准测试](#2-criterion-基准测试)
    - [2.1 安装配置](#21-安装配置)
    - [2.2 基础基准测试](#22-基础基准测试)
    - [2.3 参数化测试](#23-参数化测试)
    - [2.4 对比测试](#24-对比测试)
  - [3. OTLP 性能测试](#3-otlp-性能测试)
    - [3.1 Span 创建性能](#31-span-创建性能)
    - [3.2 导出性能](#32-导出性能)
    - [3.3 批处理性能](#33-批处理性能)
  - [4. 压力测试](#4-压力测试)
    - [4.1 wrk 压测](#41-wrk-压测)
    - [4.2 Apache Bench](#42-apache-bench)
    - [4.3 Gatling 测试](#43-gatling-测试)
  - [5. 负载测试](#5-负载测试)
    - [5.1 渐进式负载](#51-渐进式负载)
    - [5.2 峰值负载](#52-峰值负载)
    - [5.3 持续负载](#53-持续负载)
  - [6. 内存性能测试](#6-内存性能测试)
    - [6.1 内存分配](#61-内存分配)
    - [6.2 内存泄漏检测](#62-内存泄漏检测)
  - [7. 并发性能测试](#7-并发性能测试)
    - [7.1 多线程测试](#71-多线程测试)
    - [7.2 异步性能](#72-异步性能)
  - [8. 性能剖析](#8-性能剖析)
    - [8.1 CPU 剖析](#81-cpu-剖析)
    - [8.2 火焰图分析](#82-火焰图分析)
  - [9. 性能监控](#9-性能监控)
    - [9.1 Prometheus 集成](#91-prometheus-集成)
    - [9.2 实时监控](#92-实时监控)
  - [10. CI/CD 集成](#10-cicd-集成)
    - [10.1 GitHub Actions](#101-github-actions)
    - [10.2 性能回归检测](#102-性能回归检测)
  - [11. 完整示例](#11-完整示例)
    - [11.1 HTTP 服务器性能测试](#111-http-服务器性能测试)
    - [11.2 OTLP 端到端测试](#112-otlp-端到端测试)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能指标对比](#性能指标对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 性能测试概述

### 1.1 测试类型

````text
性能测试分类:

1. 基准测试 (Benchmark)
   - 测量函数/模块性能
   - 工具: Criterion
   - 目标: 优化热点代码

2. 压力测试 (Stress Test)
   - 高负载下的系统表现
   - 工具: wrk, Apache Bench
   - 目标: 找到系统极限

3. 负载测试 (Load Test)
   - 模拟真实负载
   - 工具: Gatling, Locust
   - 目标: 验证容量规划

4. 持久性测试 (Endurance Test)
   - 长时间运行
   - 目标: 检测内存泄漏

5. 并发测试 (Concurrency Test)
   - 多线程/异步性能
   - 目标: 优化并发设计
````

### 1.2 测试指标

````text
关键指标:

1. 吞吐量 (Throughput)
   - 每秒请求数 (RPS)
   - 每秒事务数 (TPS)

2. 延迟 (Latency)
   - 平均延迟 (Average)
   - P50/P95/P99 百分位数
   - 最大延迟 (Max)

3. 资源使用
   - CPU 使用率
   - 内存使用量
   - 网络带宽

4. 错误率
   - 错误数 / 总请求数
   - 目标: < 0.1%

5. 并发数
   - 同时活跃连接数
   - 最大并发数
````

---

## 2. Criterion 基准测试

### 2.1 安装配置

````toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "otlp_benchmarks"
harness = false
````

### 2.2 基础基准测试

````rust
// benches/otlp_benchmarks.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use opentelemetry::{global, trace::Tracer, KeyValue};

fn bench_span_creation(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_creation", |b| {
        b.iter(|| {
            let span = tracer.start("test_span");
            black_box(span);
        });
    });
}

fn bench_span_with_attributes(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_with_5_attributes", |b| {
        b.iter(|| {
            let mut span = tracer.start("test_span");
            span.set_attribute(KeyValue::new("attr1", "value1"));
            span.set_attribute(KeyValue::new("attr2", "value2"));
            span.set_attribute(KeyValue::new("attr3", "value3"));
            span.set_attribute(KeyValue::new("attr4", "value4"));
            span.set_attribute(KeyValue::new("attr5", "value5"));
            black_box(span);
        });
    });
}

criterion_group!(benches, bench_span_creation, bench_span_with_attributes);
criterion_main!(benches);
````

**运行基准测试**:

````bash
cargo bench

# 输出示例
span_creation           time:   [125.23 ns 127.45 ns 129.82 ns]
span_with_5_attributes  time:   [342.56 ns 345.12 ns 347.89 ns]
````

### 2.3 参数化测试

````rust
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

fn bench_span_with_n_attributes(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    let mut group = c.benchmark_group("span_attributes");
    
    for attr_count in [1, 5, 10, 20, 50].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(attr_count),
            attr_count,
            |b, &count| {
                b.iter(|| {
                    let mut span = tracer.start("test_span");
                    for i in 0..count {
                        span.set_attribute(KeyValue::new(
                            format!("attr{}", i),
                            format!("value{}", i),
                        ));
                    }
                    black_box(span);
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_span_with_n_attributes);
criterion_main!(benches);
````

**结果**:

````text
span_attributes/1       time:   [150.23 ns 152.45 ns 154.82 ns]
span_attributes/5       time:   [342.56 ns 345.12 ns 347.89 ns]
span_attributes/10      time:   [625.78 ns 628.34 ns 631.12 ns]
span_attributes/20      time:   [1.234 µs 1.245 µs 1.256 µs]
span_attributes/50      time:   [3.012 µs 3.034 µs 3.056 µs]
````

### 2.4 对比测试

````rust
use criterion::{Criterion, criterion_group, criterion_main};
use opentelemetry::trace::Tracer;

fn bench_sync_vs_async_span(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    let mut group = c.benchmark_group("sync_vs_async");
    
    // 同步 Span
    group.bench_function("sync_span", |b| {
        b.iter(|| {
            let span = tracer.start("sync_span");
            // 模拟工作
            std::thread::sleep(std::time::Duration::from_micros(10));
            black_box(span);
        });
    });
    
    // 异步 Span
    group.bench_function("async_span", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.to_async(&rt).iter(|| async {
            let span = tracer.start("async_span");
            // 模拟异步工作
            tokio::time::sleep(tokio::time::Duration::from_micros(10)).await;
            black_box(span);
        });
    });
    
    group.finish();
}

criterion_group!(benches, bench_sync_vs_async_span);
criterion_main!(benches);
````

---

## 3. OTLP 性能测试

### 3.1 Span 创建性能

````rust
use criterion::{Criterion, criterion_group, criterion_main};
use tracing::{info_span, instrument};

fn bench_span_macro(c: &mut Criterion) {
    c.bench_function("info_span_macro", |b| {
        b.iter(|| {
            let span = info_span!("test_span", user_id = 12345);
            black_box(span);
        });
    });
}

fn bench_instrument_macro(c: &mut Criterion) {
    #[instrument]
    fn instrumented_function(x: i32) -> i32 {
        x * 2
    }
    
    c.bench_function("instrument_macro", |b| {
        b.iter(|| {
            let result = instrumented_function(42);
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_span_macro, bench_instrument_macro);
criterion_main!(benches);
````

### 3.2 导出性能

````rust
use criterion::{Criterion, criterion_group, criterion_main, Throughput};
use opentelemetry_sdk::trace::{Tracer, TracerProvider};
use opentelemetry_otlp::SpanExporter;

fn bench_span_export(c: &mut Criterion) {
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()
        .unwrap();
    
    let provider = TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    
    let tracer = provider.tracer("benchmark");
    
    let mut group = c.benchmark_group("span_export");
    group.throughput(Throughput::Elements(1));
    
    group.bench_function("single_span_export", |b| {
        b.iter(|| {
            let span = tracer.start("test_span");
            drop(span); // 触发导出
        });
    });
    
    group.finish();
}

criterion_group!(benches, bench_span_export);
criterion_main!(benches);
````

### 3.3 批处理性能

````rust
use criterion::{Criterion, criterion_group, criterion_main, BenchmarkId};

fn bench_batch_sizes(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    let mut group = c.benchmark_group("batch_export");
    
    for batch_size in [10, 100, 500, 1000].iter() {
        group.throughput(Throughput::Elements(*batch_size as u64));
        
        group.bench_with_input(
            BenchmarkId::from_parameter(batch_size),
            batch_size,
            |b, &size| {
                b.iter(|| {
                    for _ in 0..size {
                        let span = tracer.start("test_span");
                        drop(span);
                    }
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_batch_sizes);
criterion_main!(benches);
````

---

## 4. 压力测试

### 4.1 wrk 压测

````bash
# 安装 wrk
git clone https://github.com/wg/wrk.git
cd wrk
make
sudo cp wrk /usr/local/bin/

# 基础压测
wrk -t12 -c400 -d30s http://localhost:8080/api/test

# 输出示例
Running 30s test @ http://localhost:8080/api/test
  12 threads and 400 connections
  Thread Stats   Avg      Stdev     Max   +/- Stdev
    Latency    45.23ms   12.34ms  250.12ms   85.67%
    Req/Sec     8.85k     1.23k   12.34k    78.90%
  3,180,234 requests in 30.00s, 1.23GB read
Requests/sec: 106,007.80
Transfer/sec:     41.89MB
````

**自定义 Lua 脚本**:

````lua
-- post.lua
wrk.method = "POST"
wrk.body   = '{"user_id": 12345, "action": "login"}'
wrk.headers["Content-Type"] = "application/json"
````

````bash
wrk -t12 -c400 -d30s -s post.lua http://localhost:8080/api/login
````

### 4.2 Apache Bench

````bash
# 安装
sudo apt-get install apache2-utils

# 基础测试
ab -n 10000 -c 100 http://localhost:8080/api/test

# POST 请求
ab -n 1000 -c 100 -p data.json -T application/json \
   http://localhost:8080/api/login

# 输出示例
Requests per second:    8500.23 [#/sec] (mean)
Time per request:       11.764 [ms] (mean)
Time per request:       0.118 [ms] (mean, across all concurrent requests)
Percentage of the requests served within a certain time (ms)
  50%     10
  66%     12
  75%     14
  80%     15
  90%     18
  95%     22
  98%     28
  99%     35
 100%     85 (longest request)
````

### 4.3 Gatling 测试

````scala
// BasicSimulation.scala
import io.gatling.core.Predef._
import io.gatling.http.Predef._
import scala.concurrent.duration._

class BasicSimulation extends Simulation {
  val httpProtocol = http
    .baseUrl("http://localhost:8080")
    .acceptHeader("application/json")
    .userAgentHeader("Gatling")

  val scn = scenario("OTLP Load Test")
    .exec(
      http("create_order")
        .post("/api/orders")
        .body(StringBody("""{"user_id": 12345, "amount": 99.99}"""))
        .check(status.is(200))
    )

  setUp(
    scn.inject(
      rampUsersPerSec(10) to 100 during (1 minute),
      constantUsersPerSec(100) during (5 minutes)
    )
  ).protocols(httpProtocol)
}
````

````bash
# 运行 Gatling
mvn gatling:test
````

---

## 5. 负载测试

### 5.1 渐进式负载

````rust
// tests/load_test.rs
use tokio::time::{sleep, Duration};
use reqwest::Client;

#[tokio::test]
async fn test_ramp_up_load() {
    let client = Client::new();
    let url = "http://localhost:8080/api/test";
    
    // 从 10 RPS 逐渐增加到 1000 RPS
    for rps in (10..=1000).step_by(10) {
        let interval = Duration::from_millis(1000 / rps);
        
        let mut tasks = vec![];
        for _ in 0..rps {
            let client = client.clone();
            let url = url.to_string();
            
            tasks.push(tokio::spawn(async move {
                let start = std::time::Instant::now();
                let response = client.get(&url).send().await;
                let duration = start.elapsed();
                
                (response.is_ok(), duration)
            }));
            
            sleep(interval).await;
        }
        
        let results: Vec<_> = futures::future::join_all(tasks)
            .await
            .into_iter()
            .filter_map(|r| r.ok())
            .collect();
        
        let success_rate = results.iter().filter(|(ok, _)| *ok).count() as f64 / results.len() as f64;
        let avg_latency = results.iter().map(|(_, d)| d.as_millis()).sum::<u128>() / results.len() as u128;
        
        println!("RPS: {}, Success Rate: {:.2}%, Avg Latency: {}ms", 
                 rps, success_rate * 100.0, avg_latency);
        
        // 如果成功率低于 95%，停止增加负载
        if success_rate < 0.95 {
            println!("System limit reached at {} RPS", rps);
            break;
        }
    }
}
````

### 5.2 峰值负载

````rust
#[tokio::test]
async fn test_spike_load() {
    let client = Client::new();
    let url = "http://localhost:8080/api/test";
    
    // 正常负载
    println!("Baseline load: 100 RPS for 1 minute");
    run_load(&client, &url, 100, Duration::from_secs(60)).await;
    
    // 突发峰值
    println!("Spike load: 1000 RPS for 10 seconds");
    run_load(&client, &url, 1000, Duration::from_secs(10)).await;
    
    // 恢复正常
    println!("Recovery: 100 RPS for 1 minute");
    run_load(&client, &url, 100, Duration::from_secs(60)).await;
}

async fn run_load(client: &Client, url: &str, rps: u64, duration: Duration) {
    let start = std::time::Instant::now();
    let mut request_count = 0;
    
    while start.elapsed() < duration {
        let _ = client.get(url).send().await;
        request_count += 1;
        
        let expected_time = Duration::from_millis(request_count * 1000 / rps);
        let actual_time = start.elapsed();
        
        if expected_time > actual_time {
            sleep(expected_time - actual_time).await;
        }
    }
}
````

### 5.3 持续负载

````rust
#[tokio::test]
async fn test_endurance() {
    let client = Client::new();
    let url = "http://localhost:8080/api/test";
    
    // 持续 1 小时，100 RPS
    let duration = Duration::from_secs(3600);
    let rps = 100;
    let interval = Duration::from_millis(1000 / rps);
    
    let start = std::time::Instant::now();
    let mut request_count = 0;
    let mut error_count = 0;
    
    while start.elapsed() < duration {
        match client.get(url).send().await {
            Ok(_) => request_count += 1,
            Err(_) => error_count += 1,
        }
        
        sleep(interval).await;
        
        // 每 1000 个请求输出一次统计
        if (request_count + error_count) % 1000 == 0 {
            let error_rate = error_count as f64 / (request_count + error_count) as f64;
            println!("Requests: {}, Errors: {}, Error Rate: {:.2}%", 
                     request_count, error_count, error_rate * 100.0);
        }
    }
}
````

---

## 6. 内存性能测试

### 6.1 内存分配

````rust
use criterion::{Criterion, criterion_group, criterion_main};

fn bench_memory_allocation(c: &mut Criterion) {
    c.bench_function("vec_allocation_1000", |b| {
        b.iter(|| {
            let v: Vec<u64> = (0..1000).collect();
            black_box(v);
        });
    });
    
    c.bench_function("string_allocation", |b| {
        b.iter(|| {
            let s = format!("trace_id: {}", "4bf92f3577b34da6a3ce929d0e0e4736");
            black_box(s);
        });
    });
}

criterion_group!(benches, bench_memory_allocation);
criterion_main!(benches);
````

### 6.2 内存泄漏检测

````bash
# 使用 valgrind
valgrind --leak-check=full --show-leak-kinds=all \
  ./target/release/my-app

# 使用 heaptrack
heaptrack ./target/release/my-app
heaptrack_gui heaptrack.my-app.12345.gz
````

---

## 7. 并发性能测试

### 7.1 多线程测试

````rust
use criterion::{Criterion, criterion_group, criterion_main, BenchmarkId};
use std::sync::Arc;
use std::thread;

fn bench_concurrent_span_creation(c: &mut Criterion) {
    let tracer = Arc::new(global::tracer("benchmark"));
    
    let mut group = c.benchmark_group("concurrent_spans");
    
    for thread_count in [1, 2, 4, 8, 16].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &count| {
                b.iter(|| {
                    let handles: Vec<_> = (0..count)
                        .map(|_| {
                            let tracer = Arc::clone(&tracer);
                            thread::spawn(move || {
                                let span = tracer.start("concurrent_span");
                                black_box(span);
                            })
                        })
                        .collect();
                    
                    for handle in handles {
                        handle.join().unwrap();
                    }
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_concurrent_span_creation);
criterion_main!(benches);
````

### 7.2 异步性能

````rust
use criterion::{Criterion, criterion_group, criterion_main, BenchmarkId};
use tokio::runtime::Runtime;

fn bench_async_spans(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let tracer = global::tracer("benchmark");
    
    let mut group = c.benchmark_group("async_spans");
    
    for task_count in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(task_count),
            task_count,
            |b, &count| {
                b.to_async(&rt).iter(|| async {
                    let tasks: Vec<_> = (0..count)
                        .map(|_| {
                            tokio::spawn(async {
                                let span = tracer.start("async_span");
                                black_box(span);
                            })
                        })
                        .collect();
                    
                    futures::future::join_all(tasks).await;
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_async_spans);
criterion_main!(benches);
````

---

## 8. 性能剖析

### 8.1 CPU 剖析

````bash
# 使用 perf (Linux)
perf record -g ./target/release/my-app
perf report

# 使用 Instruments (macOS)
instruments -t "Time Profiler" ./target/release/my-app
````

### 8.2 火焰图分析

````bash
# 安装 cargo-flamegraph
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin my-app

# 输出: flamegraph.svg
open flamegraph.svg
````

---

## 9. 性能监控

### 9.1 Prometheus 集成

````rust
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::{Encoder, TextEncoder};

pub fn init_prometheus() -> PrometheusExporter {
    opentelemetry_prometheus::exporter()
        .with_registry(prometheus::default_registry().clone())
        .build()
        .unwrap()
}

pub async fn metrics_handler(exporter: PrometheusExporter) -> String {
    let encoder = TextEncoder::new();
    let metric_families = exporter.registry().gather();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}
````

### 9.2 实时监控

````yaml
# docker-compose.yml
version: '3.8'
services:
  app:
    build: .
    ports:
      - "8080:8080"
      - "9090:9090"  # Prometheus metrics

  prometheus:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9091:9090"

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
````

---

## 10. CI/CD 集成

### 10.1 GitHub Actions

````yaml
name: Performance Tests

on:
  pull_request:
    branches: [main]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
      
      - name: Run Benchmarks
        run: cargo bench -- --output-format bencher | tee output.txt
      
      - name: Store Benchmark Result
        uses: benchmark-action/github-action-benchmark@v1
        with:
          tool: 'cargo'
          output-file-path: output.txt
          github-token: ${{ secrets.GITHUB_TOKEN }}
          auto-push: true
````

### 10.2 性能回归检测

````rust
// tests/performance_regression.rs
#[test]
fn test_no_performance_regression() {
    let baseline = load_baseline_metrics();
    let current = run_performance_tests();
    
    for (metric, value) in current.iter() {
        if let Some(baseline_value) = baseline.get(metric) {
            let regression = (value - baseline_value) / baseline_value;
            
            assert!(
                regression < 0.1,  // 允许 10% 性能回归
                "Performance regression detected for {}: {:.2}%",
                metric, regression * 100.0
            );
        }
    }
}
````

---

## 11. 完整示例

### 11.1 HTTP 服务器性能测试

````rust
// benches/http_server.rs
use criterion::{Criterion, criterion_group, criterion_main};
use axum::{Router, routing::get};
use tokio::runtime::Runtime;

async fn start_server() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }));
    
    axum::Server::bind(&"127.0.0.1:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}

fn bench_http_requests(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    // 启动服务器
    rt.spawn(async {
        start_server().await;
    });
    
    // 等待服务器启动
    std::thread::sleep(std::time::Duration::from_secs(1));
    
    let client = reqwest::Client::new();
    
    c.bench_function("http_get_request", |b| {
        b.to_async(&rt).iter(|| async {
            let response = client
                .get("http://127.0.0.1:3000/")
                .send()
                .await
                .unwrap();
            black_box(response);
        });
    });
}

criterion_group!(benches, bench_http_requests);
criterion_main!(benches);
````

### 11.2 OTLP 端到端测试

````rust
// benches/otlp_e2e.rs
use criterion::{Criterion, criterion_group, criterion_main, Throughput};
use opentelemetry::{global, trace::Tracer, KeyValue};

fn bench_otlp_e2e(c: &mut Criterion) {
    // 初始化 OTLP
    init_otlp().unwrap();
    
    let tracer = global::tracer("benchmark");
    
    let mut group = c.benchmark_group("otlp_e2e");
    group.throughput(Throughput::Elements(1));
    
    group.bench_function("create_and_export_span", |b| {
        b.iter(|| {
            let mut span = tracer.start("test_span");
            span.set_attribute(KeyValue::new("user.id", 12345));
            span.set_attribute(KeyValue::new("action", "test"));
            span.add_event("test_event", vec![]);
            drop(span);  // 触发导出
        });
    });
    
    group.finish();
    
    // 清理
    global::shutdown_tracer_provider();
}

criterion_group!(benches, bench_otlp_e2e);
criterion_main!(benches);
````

---

## 总结

### 核心要点

1. **Criterion**: Rust 标准基准测试工具，支持统计分析
2. **压力测试**: wrk 和 Apache Bench 用于 HTTP 服务压测
3. **负载测试**: 模拟真实场景，测试系统容量
4. **性能剖析**: 使用火焰图找到性能瓶颈
5. **CI/CD 集成**: 自动化性能测试，检测性能回归
6. **监控集成**: Prometheus + Grafana 实时监控

### 性能指标对比

| 操作 | 延迟 | 吞吐量 | 备注 |
|------|------|--------|------|
| Span 创建 | ~125ns | 8M ops/s | 无属性 |
| Span + 5 属性 | ~345ns | 3M ops/s | 字符串属性 |
| Span 导出 (批量) | ~50µs | 20K spans/s | OTLP gRPC |
| HTTP 请求 | ~1ms | 100K req/s | Axum 服务器 |
| 数据库查询 | ~5ms | 20K queries/s | PostgreSQL |

### 最佳实践清单

- ✅ 使用 Criterion 进行微基准测试
- ✅ 参数化测试找到最优配置
- ✅ wrk 压测验证系统极限
- ✅ 负载测试模拟真实场景
- ✅ 持久性测试检测内存泄漏
- ✅ 并发测试验证多线程性能
- ✅ 火焰图定位性能瓶颈
- ✅ CI/CD 集成自动化测试
- ✅ 性能回归检测（允许 10% 偏差）
- ✅ Prometheus 监控生产环境性能
- ✅ 设置性能基线并持续监控
- ✅ 针对热点代码优化

---

**相关文档**:

- [性能优化完整指南](./01_Rust_1.90_性能优化完整指南.md)
- [采样策略](./02_采样策略_Rust完整版.md)
- [调试工具](../08_故障排查/02_调试工具_Rust完整版.md)
- [CI/CD 集成](../09_CI_CD集成/01_GitHub_Actions_Rust完整配置.md)
