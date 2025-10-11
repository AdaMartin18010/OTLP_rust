# 🦀 故障排查速查手册 - Rust OTLP版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 故障排查速查手册 - Rust OTLP版](#-故障排查速查手册---rust-otlp版)
  - [📋 快速索引](#-快速索引)
  - [🔌 连接问题](#-连接问题)
    - [问题1: 无法连接到Collector](#问题1-无法连接到collector)
    - [问题2: TLS握手失败](#问题2-tls握手失败)
  - [💨 数据丢失](#-数据丢失)
    - [问题3: Spans未出现在后端](#问题3-spans未出现在后端)
  - [⚡ 性能问题](#-性能问题)
    - [问题4: 高延迟](#问题4-高延迟)
    - [问题5: CPU使用率过高](#问题5-cpu使用率过高)
  - [🧠 内存泄漏](#-内存泄漏)
    - [问题6: 内存持续增长](#问题6-内存持续增长)
  - [🔐 认证错误](#-认证错误)
    - [问题7: Unauthenticated错误](#问题7-unauthenticated错误)
  - [🛠️ 诊断工具集](#️-诊断工具集)
    - [完整诊断脚本](#完整诊断脚本)
    - [运行诊断](#运行诊断)
  - [📊 监控指标](#-监控指标)
    - [关键指标](#关键指标)
  - [📚 快速参考](#-快速参考)
    - [错误代码对照](#错误代码对照)
    - [常用命令](#常用命令)

---

## 🔌 连接问题

### 问题1: 无法连接到Collector

**症状**:

```rust
Error: transport error: Connection refused (os error 111)
```

**诊断**:

```rust
use reqwest::Client;

pub async fn diagnose_connection(endpoint: &str) -> anyhow::Result<()> {
    let client = Client::new();
    
    // 1. 基础网络测试
    println!("🔍 Testing connection to {}", endpoint);
    
    match client.get(endpoint).send().await {
        Ok(resp) => {
            println!("✅ Network reachable");
            println!("   Status: {}", resp.status());
        }
        Err(e) => {
            println!("❌ Network error: {}", e);
            
            if e.is_timeout() {
                println!("   → Timeout: Check firewall/network");
            } else if e.is_connect() {
                println!("   → Connection refused: Collector not running?");
            } else if e.is_request() {
                println!("   → Invalid request: Check endpoint format");
            }
        }
    }
    
    Ok(())
}
```

**解决方案**:

1. **检查Collector是否运行**:

    ```bash
    docker ps | grep otel-collector
    # 或
    curl http://localhost:13133/health
    ```

2. **验证端口**:

    ```rust
    // gRPC: 4317
    let endpoint = "http://localhost:4317";

    // HTTP: 4318
    let endpoint = "http://localhost:4318/v1/traces";
    ```

3. **检查防火墙**:

    ```bash
    # Linux
    sudo ufw status
    sudo iptables -L -n

    # Windows
    netsh advfirewall show allprofiles
    ```

4. **Rust端配置**:

    ```rust
    use opentelemetry_otlp::SpanExporter;
    use std::time::Duration;

    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(30))  // 增加超时
        .build()?;
    ```

---

### 问题2: TLS握手失败

**症状**:

```text
Error: tls handshake eof
```

**诊断**:

```rust
pub async fn diagnose_tls(endpoint: &str) -> anyhow::Result<()> {
    println!("🔐 Diagnosing TLS for {}", endpoint);
    
    // 1. 检查证书
    let client = reqwest::Client::builder()
        .danger_accept_invalid_certs(true) // 仅用于测试!
        .build()?;
    
    match client.get(endpoint).send().await {
        Ok(_) => println!("✅ Server responds (ignoring cert validation)"),
        Err(e) => println!("❌ Server unreachable: {}", e),
    }
    
    // 2. 验证证书链
    println!("\n📜 Certificate validation:");
    let client = reqwest::Client::builder().build()?;
    
    match client.get(endpoint).send().await {
        Ok(_) => println!("✅ Valid certificate chain"),
        Err(e) if e.to_string().contains("certificate") => {
            println!("❌ Certificate error: {}", e);
            println!("   → Check CA certificate");
        }
        Err(e) => println!("❌ Other error: {}", e),
    }
    
    Ok(())
}
```

**解决方案**:

```rust
use tonic::transport::{Certificate, ClientTlsConfig};

// 1. 加载CA证书
let ca_cert = tokio::fs::read("/path/to/ca.crt").await?;
let ca = Certificate::from_pem(ca_cert);

// 2. 配置TLS
let tls_config = ClientTlsConfig::new()
    .ca_certificate(ca)
    .domain_name("collector.example.com"); // 必须匹配证书CN

// 3. 创建exporter
let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(tls_config)
    .build()?;
```

---

## 💨 数据丢失

### 问题3: Spans未出现在后端

**症状**:

- Spans成功创建
- 无错误日志
- 但后端查询无数据

**诊断**:

```rust
use opentelemetry::{global, trace::{Span, Tracer}};
use std::time::Duration;
use tokio::time::sleep;

pub async fn diagnose_data_export() -> anyhow::Result<()> {
    println!("📊 Diagnosing data export...\n");
    
    // 1. 创建测试span
    let tracer = global::tracer("diagnostic");
    let mut span = tracer.start("test-span");
    span.set_attribute(opentelemetry::KeyValue::new("test", "true"));
    span.end();
    
    println!("✅ Span created");
    
    // 2. 等待导出 (重要!)
    println!("⏳ Waiting for export (10s)...");
    sleep(Duration::from_secs(10)).await;
    
    // 3. 强制flush
    println!("🔄 Forcing flush...");
    if let Some(provider) = global::tracer_provider().downcast_ref::<
        opentelemetry_sdk::trace::TracerProvider
    >() {
        provider.force_flush();
        println!("✅ Flush completed");
    }
    
    Ok(())
}
```

**常见原因与解决**:

1. **未调用shutdown/flush**:

    ```rust
    #[tokio::main]
    async fn main() -> anyhow::Result<()> {
        let tracer_provider = init_tracer()?;
        
        // ... 应用逻辑 ...
        
        // ⚠️ 必须调用shutdown!
        tracer_provider.shutdown()?;
        Ok(())
    }
    ```

2. **批处理队列满**:

    ```rust
    use opentelemetry_sdk::trace::Config;

    let config = Config::default()
        .with_max_queue_size(8192)  // 增大队列
        .with_scheduled_delay(Duration::from_secs(5)); // 减少延迟
    ```

3. **采样丢弃**:

    ```rust
    use opentelemetry_sdk::trace::Sampler;

    // 检查采样率
    let sampler = Sampler::AlwaysOn; // 测试时使用100%采样

    // 生产环境
    let sampler = Sampler::TraceIdRatioBased(0.1); // 10%采样
    ```

4. **Exporter超时**:

    ```rust
    let exporter = SpanExporter::builder()
        .with_timeout(Duration::from_secs(60))  // 增加超时
        .build()?;
    ```

---

## ⚡ 性能问题

### 问题4: 高延迟

**症状**:

- 应用响应变慢
- CPU使用率高

**诊断**:

```rust
use std::time::Instant;

pub async fn diagnose_latency() -> anyhow::Result<()> {
    println!("⏱️  Measuring OTLP overhead...\n");
    
    let tracer = global::tracer("perf-test");
    
    // 无追踪基准
    let start = Instant::now();
    for _ in 0..1000 {
        // 模拟业务逻辑
        tokio::time::sleep(Duration::from_micros(10)).await;
    }
    let baseline = start.elapsed();
    println!("Baseline (no tracing): {:?}", baseline);
    
    // 带追踪
    let start = Instant::now();
    for i in 0..1000 {
        let mut span = tracer.start(format!("operation-{}", i));
        tokio::time::sleep(Duration::from_micros(10)).await;
        span.end();
    }
    let with_tracing = start.elapsed();
    println!("With tracing: {:?}", with_tracing);
    
    let overhead = with_tracing.saturating_sub(baseline);
    println!("\n📊 Overhead: {:?} ({:.2}%)", 
        overhead,
        (overhead.as_micros() as f64 / baseline.as_micros() as f64) * 100.0
    );
    
    Ok(())
}
```

**优化方案**:

1. **使用异步导出**:

    ```rust
    use opentelemetry_sdk::runtime;

    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio) // 异步
        .build();
    ```

2. **增大批次大小**:

    ```rust
    let config = Config::default()
        .with_max_export_batch_size(2048)  // 从512增到2048
        .with_scheduled_delay(Duration::from_secs(10)); // 延迟批量导出
    ```

3. **减少属性数量**:

    ```rust
    // ❌ 避免过多属性
    span.set_attribute(KeyValue::new("http.request.headers", serialize_all_headers()));

    // ✅ 只记录关键属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.status_code", 200));
    ```

4. **优化采样**:

    ```rust
    // 使用父级采样决策
    let sampler = Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.05) // 5%采样
    ));
    ```

---

### 问题5: CPU使用率过高

**诊断**:

```rust
use tokio::runtime::Handle;

pub fn diagnose_cpu_usage() {
    let handle = Handle::current();
    let metrics = handle.metrics();
    
    println!("📊 Tokio Runtime Metrics:");
    println!("   Workers: {}", metrics.num_workers());
    println!("   Blocking threads: {}", metrics.num_blocking_threads());
    
    // 检查是否有任务阻塞
    for worker in 0..metrics.num_workers() {
        println!("   Worker {}: {} tasks", 
            worker, 
            metrics.worker_local_queue_depth(worker)
        );
    }
}
```

**解决方案**:

```rust
// 1. 使用专用的Tokio runtime
let runtime = tokio::runtime::Builder::new_multi_thread()
    .worker_threads(4)  // 限制线程数
    .thread_name("otlp-worker")
    .enable_all()
    .build()?;

// 2. 减少序列化开销
let exporter = SpanExporter::builder()
    .with_compression(tonic::codec::CompressionEncoding::Gzip) // 使用压缩
    .build()?;
```

---

## 🧠 内存泄漏

### 问题6: 内存持续增长

**诊断**:

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

// 自定义分配器追踪
struct TrackingAllocator;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
        System.alloc(layout)
    }
    
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        ALLOCATED.fetch_sub(layout.size(), Ordering::SeqCst);
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;

pub fn print_memory_usage() {
    let allocated_mb = ALLOCATED.load(Ordering::SeqCst) as f64 / 1024.0 / 1024.0;
    println!("💾 Allocated memory: {:.2} MB", allocated_mb);
}
```

**常见原因**:

1. **未释放Provider**:

    ```rust
    // ❌ 错误: Provider泄漏
    fn bad_example() {
        let provider = init_tracer().unwrap();
        // 忘记调用shutdown
    }

    // ✅ 正确: 确保释放
    async fn good_example() -> anyhow::Result<()> {
        let provider = init_tracer()?;
        
        // ... 使用 ...
        
        provider.shutdown()?; // 必须调用
        Ok(())
    }
    ```

2. **循环引用**:

    ```rust
    // ✅ 使用Weak引用避免循环
    use std::sync::{Arc, Weak};

    struct SpanHolder {
        parent: Option<Weak<SpanHolder>>, // 使用Weak
    }
    ```

3. **队列溢出**:

    ```rust
    // 限制队列大小
    let config = Config::default()
        .with_max_queue_size(2048); // 防止无限增长
    ```

---

## 🔐 认证错误

### 问题7: Unauthenticated错误

**症状**:

```text
Error: status: Unauthenticated, message: "invalid authentication credentials"
```

**诊断**:

```rust
use tonic::metadata::MetadataMap;

pub fn diagnose_auth(endpoint: &str, token: &str) -> anyhow::Result<()> {
    println!("🔐 Diagnosing authentication...\n");
    
    // 1. 检查token格式
    println!("1️⃣ Token format check:");
    if token.is_empty() {
        println!("   ❌ Token is empty!");
    } else {
        println!("   ✅ Token present (length: {})", token.len());
    }
    
    // 2. 检查metadata
    let mut metadata = MetadataMap::new();
    match format!("Bearer {}", token).parse() {
        Ok(val) => {
            metadata.insert("authorization", val);
            println!("   ✅ Metadata valid");
        }
        Err(e) => println!("   ❌ Metadata invalid: {}", e),
    }
    
    Ok(())
}
```

**解决方案**:

```rust
// 1. Bearer Token
let mut metadata = MetadataMap::new();
metadata.insert(
    "authorization",
    format!("Bearer {}", token).parse()?
);

// 2. API Key
metadata.insert(
    "x-api-key",
    api_key.parse()?
);

// 3. 自定义头
metadata.insert(
    "x-custom-auth",
    auth_value.parse()?
);

// 4. 应用到exporter
let exporter = SpanExporter::builder()
    .with_metadata(metadata)
    .build()?;
```

---

## 🛠️ 诊断工具集

### 完整诊断脚本

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};
use std::time::Duration;
use tokio::time::sleep;

pub async fn comprehensive_diagnosis(
    endpoint: &str,
) -> anyhow::Result<()> {
    println!("🔍 OpenTelemetry Comprehensive Diagnosis\n");
    println!("Endpoint: {}\n", endpoint);
    
    // 1. 网络连接
    println!("═══ 1. Network Connectivity ═══");
    diagnose_connection(endpoint).await?;
    
    // 2. TLS配置
    if endpoint.starts_with("https") {
        println!("\n═══ 2. TLS Configuration ═══");
        diagnose_tls(endpoint).await?;
    }
    
    // 3. 数据导出
    println!("\n═══ 3. Data Export ═══");
    diagnose_data_export().await?;
    
    // 4. 性能测试
    println!("\n═══ 4. Performance ═══");
    diagnose_latency().await?;
    
    // 5. 内存使用
    println!("\n═══ 5. Memory Usage ═══");
    print_memory_usage();
    
    // 6. 配置验证
    println!("\n═══ 6. Configuration ═══");
    verify_configuration()?;
    
    println!("\n✅ Diagnosis complete!");
    Ok(())
}

fn verify_configuration() -> anyhow::Result<()> {
    // 检查环境变量
    let vars = [
        "OTEL_EXPORTER_OTLP_ENDPOINT",
        "OTEL_SERVICE_NAME",
        "OTEL_RESOURCE_ATTRIBUTES",
    ];
    
    for var in &vars {
        match std::env::var(var) {
            Ok(val) => println!("   ✅ {}: {}", var, val),
            Err(_) => println!("   ⚠️  {} not set", var),
        }
    }
    
    Ok(())
}
```

### 运行诊断

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    comprehensive_diagnosis(&endpoint).await?;
    
    Ok(())
}
```

---

## 📊 监控指标

### 关键指标

```rust
use opentelemetry::metrics::Meter;

pub struct OtlpMetrics {
    pub spans_exported: Counter<u64>,
    pub export_errors: Counter<u64>,
    pub export_duration: Histogram<f64>,
}

impl OtlpMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            spans_exported: meter
                .u64_counter("otlp.spans.exported")
                .with_description("Total spans exported")
                .init(),
            
            export_errors: meter
                .u64_counter("otlp.export.errors")
                .with_description("Total export errors")
                .init(),
            
            export_duration: meter
                .f64_histogram("otlp.export.duration")
                .with_unit("s")
                .init(),
        }
    }
}
```

---

## 📚 快速参考

### 错误代码对照

| 错误信息 | 原因 | 解决方案 |
|---------|------|---------|
| `Connection refused` | Collector未运行 | 启动Collector |
| `Timeout` | 网络延迟 | 增加timeout |
| `Unauthenticated` | 认证失败 | 检查token |
| `TLS handshake failed` | 证书问题 | 验证证书链 |
| `Resource exhausted` | 队列满 | 增大队列 |

### 常用命令

```bash
# 检查Collector健康
curl http://localhost:13133/health

# 查看Collector指标
curl http://localhost:8888/metrics

# 测试OTLP endpoint
grpcurl -plaintext localhost:4317 list

# 查看应用日志
RUST_LOG=debug cargo run
```

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [Collector配置速查手册_Rust版](./03_Collector配置速查手册_Rust版.md)  
**下一篇**: [性能优化速查手册_Rust版](./05_性能优化速查手册_Rust版.md)
