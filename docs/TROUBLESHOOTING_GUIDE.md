# OTLP Rust 故障排查指南

全面的故障诊断和解决方案指南。

## 目录

- [OTLP Rust 故障排查指南](#otlp-rust-故障排查指南)
  - [目录](#目录)
  - [1. 常见问题速查](#1-常见问题速查)
  - [2. 连接问题](#2-连接问题)
    - [2.1 连接超时](#21-连接超时)
    - [2.2 TLS/SSL 错误](#22-tlsssl-错误)
    - [2.3 认证失败](#23-认证失败)
  - [3. 性能问题](#3-性能问题)
    - [3.1 高 CPU 使用](#31-高-cpu-使用)
    - [3.2 高内存使用](#32-高内存使用)
    - [3.3 导出延迟高](#33-导出延迟高)
  - [4. 内存问题](#4-内存问题)
    - [4.1 内存泄漏](#41-内存泄漏)
    - [4.2 堆栈溢出](#42-堆栈溢出)
  - [5. 数据丢失](#5-数据丢失)
    - [5.1 应用崩溃时丢失](#51-应用崩溃时丢失)
    - [5.2 网络中断时丢失](#52-网络中断时丢失)
  - [6. 编译问题](#6-编译问题)
    - [6.1 依赖冲突](#61-依赖冲突)
    - [6.2 功能标志冲突](#62-功能标志冲突)
    - [6.3 链接错误](#63-链接错误)
  - [7. 运行时错误](#7-运行时错误)
    - [7.1 Panic](#71-panic)
    - [7.2 死锁](#72-死锁)
  - [8. 调试工具](#8-调试工具)
    - [8.1 日志级别](#81-日志级别)
    - [8.2 指标监控](#82-指标监控)
    - [8.3 分布式追踪自身](#83-分布式追踪自身)
    - [8.4 调试端点](#84-调试端点)
  - [快速诊断清单](#快速诊断清单)
  - [获取帮助](#获取帮助)

---

## 1. 常见问题速查

| 问题 | 可能原因 | 快速解决方案 |
|------|---------|-------------|
| 连接超时 | 网络问题/Collector 未启动 | 检查网络、确认 Collector 状态 |
| 导出失败 | 认证失败/配置错误 | 验证 API Key、检查配置 |
| 内存泄漏 | 缓冲区未释放/循环引用 | 使用内存分析工具、检查生命周期 |
| 高 CPU | 频繁序列化/无批处理 | 启用批处理、优化序列化 |
| 数据延迟 | 批处理过大/网络慢 | 调整批处理大小、检查网络 |

---

## 2. 连接问题

### 2.1 连接超时

**症状：**

```
ERROR: export failed: deadline has elapsed
ERROR: connection timeout after 30s
```

**诊断步骤：**

1. 检查 Collector 是否可达

```bash
# 测试 gRPC 端口
telnet otel-collector 4317

# 测试 HTTP 端口
curl http://otel-collector:4318/v1/traces

# 检查 DNS 解析
nslookup otel-collector
```

1. 验证网络策略

```bash
# Kubernetes
kubectl get networkpolicies
kubectl get svc otel-collector

# 检查防火墙
iptables -L | grep 4317
```

**解决方案：**

```rust
// 增加超时时间
let client = OtlpClientBuilder::new()
    .timeout(Duration::from_secs(60))  // 增加超时
    .endpoint("http://otel-collector:4317")
    .build()?;

// 添加重试
let exporter = RetryExporter::new(
    base_exporter,
    RetryPolicy::exponential_backoff()
        .max_attempts(5)
        .initial_delay(Duration::from_millis(100))
);
```

### 2.2 TLS/SSL 错误

**症状：**

```
ERROR: tls handshake failed
ERROR: certificate verify failed
```

**解决方案：**

```rust
// 开发环境：允许不安全连接（不推荐用于生产）
let client = OtlpClientBuilder::new()
    .tls_config(
        TlsConfig::new()
            .danger_accept_invalid_certs(true)  // 仅开发使用！
    )
    .build()?;

// 生产环境：配置正确的证书
let client = OtlpClientBuilder::new()
    .tls_config(
        TlsConfig::new()
            .ca_cert(include_bytes!("/path/to/ca.crt"))
            .client_cert(
                include_bytes!("/path/to/client.crt"),
                include_bytes!("/path/to/client.key")
            )
    )
    .build()?;
```

### 2.3 认证失败

**症状：**

```
ERROR: HTTP 401 Unauthorized
ERROR: authentication failed
```

**解决方案：**

```rustn// 检查 Header 设置
let client = OtlpClientBuilder::new()
    .with_header("Authorization", format!("Bearer {}", api_key))
    .with_header("X-API-Key", api_key)
    .build()?;

// 验证 API Key 是否有效
println!("Using API Key: {}...", &api_key[..8]);
```

---

## 3. 性能问题

### 3.1 高 CPU 使用

**诊断：**

```rustn// 启用 CPU Profiling
#[cfg(feature = "profiling")]
fn run_with_profiling<F>(f: F)
where
    F: FnOnce(),
{
    let guard = pprof::ProfilerGuard::new(100).unwrap();
    f();

    if let Ok(report) = guard.report().build() {
        let file = File::create("cpu_profile.pb").unwrap();
        report.pprof().unwrap().write_to_writer(file).unwrap();
    }
}
```

**常见原因和解决方案：**

1. **频繁序列化**

```rustn// 优化前：每次导出都序列化
for span in spans {
    let json = serde_json::to_string(&span)?;
    send(json).await?;
}

// 优化后：批量序列化
let batch = spans.chunks(100);
for chunk in batch {
    let json = serde_json::to_string(&chunk)?;
    send(json).await?;
}
```

1. **无批处理**

```rustn// 启用批处理
let batch_processor = BatchSpanProcessor::builder(runtime::Tokio)
    .with_batch_config(
        BatchConfig::default()
            .max_queue_size(2048)
            .max_export_batch_size(512)
            .schedule_delay(Duration::from_millis(1000))
    )
    .build();
```

### 3.2 高内存使用

**诊断工具：**

```rustn// 内存使用监控
use std::alloc::{GlobalAlloc, Layout, System};

struct TrackingAllocator;

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
        ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;
```

**解决方案：**

```rustn// 1. 使用内存池
let buffer_pool = ByteBufferPool::new(1024, 100);

// 2. 限制队列大小
let (tx, rx) = mpsc::channel::<Span>(1000); // 限制为 1000

// 3. 定期刷新缓冲区
let mut interval = tokio::time::interval(Duration::from_secs(5));
loop {
    tokio::select! {
        _ = interval.tick() => {
            buffer.flush().await?;
        }
        // ...
    }
}
```

### 3.3 导出延迟高

**诊断：**

```rustn// 测量导出时间
let start = Instant::now();
match exporter.export(spans).await {
    Ok(_) => {
        let elapsed = start.elapsed();
        println!("Export took {:?}", elapsed);

        if elapsed > Duration::from_secs(5) {
            println!("WARNING: Export is slow!");
        }
    }
    Err(e) => println!("Export failed: {}", e),
}
```

**优化方案：**

```rustn// 异步导出
let exporter = exporter.with_async_export(true);

// 并发导出
let exporter = exporter.with_max_concurrent_exports(10);

// 压缩
let exporter = CompressionExporter::new(exporter, Compression::Zstd);
```

---

## 4. 内存问题

### 4.1 内存泄漏

**症状：**

- 内存使用持续增长
- OOMKilled (Kubernetes)

**诊断：**

```bashn# 使用 valgrind
valgrind --tool=memcheck --leak-check=full ./your_app

# 使用 heaptrack
heaptrack ./your_app

# Rust 特定
RUST_BACKTRACE=1 cargo run
```

**常见原因：**

1. **通道未正确关闭**

```rustn// 错误：忘记关闭发送者
let (tx, rx) = mpsc::channel();
// ... 使用 tx
// tx 未关闭，rx 永远等待

// 正确：确保关闭
drop(tx); // 显式关闭
```

1. **循环引用（使用 Arc）**

```rustn// 错误：循环引用
struct Node {
    next: Option<Arc<Mutex<Node>>>,
    prev: Option<Arc<Mutex<Node>>>, // 循环引用！
}

// 正确：使用 Weak
struct Node {
    next: Option<Arc<Mutex<Node>>>,
    prev: Option<Weak<Mutex<Node>>>, // 使用 Weak
}
```

### 4.2 堆栈溢出

**症状：**

```
thread 'main' has overflowed its stack
fatal runtime error: stack overflow
```

**解决方案：**

```rustn// 增加栈大小
RUST_MIN_STACK=8388608 cargo run

// 使用 Box 分配大对象到堆
let large_array = Box::new([0u8; 1000000]);

// 避免深度递归，使用迭代
// 递归（可能栈溢出）
fn recursive_process(items: &[Item]) {
    if items.is_empty() { return; }
    process(&items[0]);
    recursive_process(&items[1..]); // 深度递归！
}

// 迭代（安全）
fn iterative_process(items: &[Item]) {
    for item in items {
        process(item);
    }
}
```

---

## 5. 数据丢失

### 5.1 应用崩溃时丢失

**解决方案：**

```rustn// 使用持久化队列
let exporter = FileQueueExporter::new(
    base_exporter,
    "/var/lib/app/queue",
    FileQueueConfig {
        max_file_size: 100 * 1024 * 1024, // 100MB
        max_files: 10,
    }
);

// 优雅关闭
async fn shutdown_gracefully(exporter: &dyn SpanExporter) {
    // 设置关闭超时
    let timeout = Duration::from_secs(10);

    match tokio::time::timeout(timeout, exporter.shutdown()).await {
        Ok(_) => println!("Shutdown completed"),
        Err(_) => println!("Shutdown timed out"),
    }
}
```

### 5.2 网络中断时丢失

```rustn// 使用重试和死信队列
let exporter = DeadLetterQueueExporter::new(
    base_exporter,
    DeadLetterConfig {
        max_retries: 5,
        retry_delay: Duration::from_secs(1),
        dlq_path: "/var/lib/app/dlq",
    }
);
```

---

## 6. 编译问题

### 6.1 依赖冲突

**症状：**

```
error: failed to select a version for `tokio`.
```

**解决方案：**

```toml
# Cargo.toml
[patch.crates-io]
tokio = { version = "1.0" }

# 或使用特定版本
[dependencies]
tokio = "=1.35.0"  # 使用 = 锁定版本
```

### 6.2 功能标志冲突

```toml
# 确保功能标志一致
[dependencies]
otlp = { version = "0.6", features = ["grpc", "tls"] }
# 不要同时启用冲突的功能
# otlp = { version = "0.6", features = ["grpc", "http"] }  // 可能冲突
```

### 6.3 链接错误

**症状：**

```
error: linking with `cc` failed
undefined reference to `OPENSSL_*`
```

**解决方案：**

```bashn# 安装 OpenSSL 开发包
# Ubuntu/Debian
sudo apt-get install libssl-dev pkg-config

# macOS
brew install openssl

# 使用 rustls 替代 OpenSSL
[dependencies]
otlp = { version = "0.6", default-features = false, features = ["grpc", "tls-rustls"] }
```

---

## 7. 运行时错误

### 7.1 Panic

**捕获和处理：**

```rustnuse std::panic;

fn setup_panic_handler() {
    panic::set_hook(Box::new(|info| {
        // 记录 panic
        log::error!("Panic occurred: {}", info);

        // 导出剩余的遥测数据
        if let Some(exporter) = GLOBAL_EXPORTER.get() {
            exporter.force_flush();
        }
    }));
}

// 在 async 中捕获 panic
let result = AssertUnwindSafe(async {
    risky_operation().await
}).catch_unwind().await;

match result {
    Ok(val) => println!("Success: {:?}", val),
    Err(_) => println!("Operation panicked"),
}
```

### 7.2 死锁

**诊断：**

```rustn// 使用 parking_lot 的死锁检测
use parking_lot::deadlock;

// 定期检查死锁
std::thread::spawn(move || {
    loop {
        std::thread::sleep(Duration::from_secs(10));
        let deadlocks = deadlock::check_deadlock();
        if !deadlocks.is_empty() {
            println!("{} deadlocks detected", deadlocks.len());
        }
    }
});
```

**预防：**

```rustn// 1. 使用 try_lock
if let Ok(guard) = mutex.try_lock() {
    // 使用 guard
} else {
    println!("Could not acquire lock");
}

// 2. 使用 RwLock 替代 Mutex 如果读多写少
use std::sync::RwLock;

// 3. 使用 tokio::sync 的异步锁
use tokio::sync::Mutex;
```

---

## 8. 调试工具

### 8.1 日志级别

```rustn// 初始化日志
use tracing_subscriber;

fn init_logging() {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::from_default_env()
                .add_directive("otlp=debug".parse().unwrap())
                .add_directive("tokio=warn".parse().unwrap())
        )
        .with_thread_ids(true)
        .with_thread_names(true)
        .init();
}
```

### 8.2 指标监控

```rustn// 内部指标
lazy_static! {
    static ref EXPORT_DURATION: Histogram = register_histogram!(
        "otlp_export_duration_seconds",
        "Export operation duration"
    ).unwrap();

    static ref EXPORT_ERRORS: Counter = register_counter!(
        "otlp_export_errors_total",
        "Total export errors"
    ).unwrap();
}

// 使用
let timer = EXPORT_DURATION.start_timer();
match exporter.export(spans).await {
    Ok(_) => {},
    Err(_) => EXPORT_ERRORS.inc(),
}
timer.observe_duration();
```

### 8.3 分布式追踪自身

```rustn// 自追踪
let tracer = global::tracer("otlp-internal");

async fn export_with_tracing(spans: Vec<Span>) -> Result<()> {
    let span = tracer.span_builder("export")
        .with_attribute(KeyValue::new("span_count", spans.len() as i64))
        .start(&tracer);

    let cx = Context::current_with_span(span);

    export_internal(spans).with_context(cx).await
}
```

### 8.4 调试端点

```rustn// 添加健康检查端点
async fn health_check() -> impl Responder {
    HttpResponse::Ok().json(json!({
        "status": "healthy",
        "uptime": get_uptime(),
        "memory": get_memory_usage(),
        "queue_size": get_queue_size(),
    }))
}

// 添加调试端点
async fn debug_info() -> impl Responder {
    HttpResponse::Ok().json(json!({
        "config": get_config(),
        "exporters": list_exporters(),
        "processors": list_processors(),
    }))
}
```

---

## 快速诊断清单

- [ ] 检查网络连通性
- [ ] 验证配置文件
- [ ] 检查资源限制（CPU/内存）
- [ ] 查看日志输出
- [ ] 启用调试日志
- [ ] 检查依赖版本
- [ ] 验证权限和认证
- [ ] 测试回退配置
- [ ] 监控指标和告警
- [ ] 复现问题并记录

---

## 获取帮助

1. **查看文档：** [API 参考](./API_QUICK_REFERENCE.md)
2. **检查示例：** [示例代码](../examples/)
3. **搜索 Issues：** GitHub Issues
4. **社区支持：** Discord / Slack
5. **提交 Bug：** 包含复现步骤和日志
