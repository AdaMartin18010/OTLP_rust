# 🔧 故障排除指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: 故障排除指南 - 常见问题、连接问题、性能问题、数据丢失等完整排查方案。

---

## 📋 目录

- [🔧 故障排除指南](#-故障排除指南)
  - [📋 目录](#-目录)
  - [❓ 常见问题](#-常见问题)
    - [Q1: 无法连接到 OTLP Collector](#q1-无法连接到-otlp-collector)
    - [Q2: 数据发送超时](#q2-数据发送超时)
    - [Q3: Span 数据不完整](#q3-span-数据不完整)
  - [🔌 连接问题](#-连接问题)
    - [连接池耗尽](#连接池耗尽)
    - [TLS/SSL 错误](#tlsssl-错误)
  - [⚡ 性能问题](#-性能问题)
    - [高延迟](#高延迟)
    - [高CPU使用率](#高cpu使用率)
  - [💾 数据丢失问题](#-数据丢失问题)
    - [Span 丢失](#span-丢失)
    - [监控数据丢失](#监控数据丢失)
  - [🧠 内存问题](#-内存问题)
    - [内存泄漏](#内存泄漏)
  - [📋 日志分析](#-日志分析)
    - [启用详细日志](#启用详细日志)
    - [日志分析技巧](#日志分析技巧)
  - [🐛 调试技巧](#-调试技巧)
    - [使用调试工具](#使用调试工具)
    - [性能分析](#性能分析)
  - [🆘 获取帮助](#-获取帮助)
    - [收集诊断信息](#收集诊断信息)
    - [报告问题](#报告问题)
    - [社区资源](#社区资源)

---

## ❓ 常见问题

### Q1: 无法连接到 OTLP Collector

**症状**:

```text
Error: Failed to connect to http://localhost:4317
Connection refused
```

**原因**:

- Collector 未启动
- 端口配置错误
- 网络不可达
- 防火墙阻止

**解决方案**:

```bash
# 1. 检查 Collector 是否运行
docker ps | grep otel-collector

# 2. 检查端口是否监听
netstat -an | grep 4317  # Linux/Mac
netstat -an | findstr 4317  # Windows

# 3. 测试网络连通性
telnet localhost 4317
# 或
curl -v http://localhost:4317

# 4. 检查防火墙规则
sudo iptables -L | grep 4317  # Linux
netsh advfirewall firewall show rule name=all | findstr 4317  # Windows

# 5. 启动 Collector
docker run -d -p 4317:4317 -p 4318:4318 \
  otel/opentelemetry-collector-contrib:latest
```

**验证**:

```rust
use otlp::core::EnhancedOtlpClient;

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_connect_timeout(Duration::from_secs(5))
    .build()
    .await?;

// 测试连接
match client.health_check().await {
    Ok(_) => println!("✅ 连接成功"),
    Err(e) => println!("❌ 连接失败: {}", e),
}
```

---

### Q2: 数据发送超时

**症状**:

```text
Error: Request timeout after 30s
```

**原因**:

- 网络延迟高
- Collector 负载过高
- 批次大小过大
- 超时配置过小

**解决方案**:

```rust
// 1. 增加超时时间
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_request_timeout(Duration::from_secs(60))  // 增加到 60 秒
    .build()
    .await?;

// 2. 减小批次大小
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_batch_config(BatchConfig {
        max_batch_size: 500,  // 从 1000 减少到 500
        batch_timeout: Duration::from_millis(100),
        max_queue_size: 10000,
        strategy: BatchStrategy::Hybrid,
    })
    .build()
    .await?;

// 3. 启用重试机制
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_retry_config(RetryConfig {
        max_attempts: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![ErrorType::Timeout],
    })
    .build()
    .await?;
```

**诊断工具**:

```bash
# 检查网络延迟
ping collector-hostname

# 使用 tcpdump 抓包分析
sudo tcpdump -i any port 4317 -w otlp-traffic.pcap

# 分析 Collector 负载
docker stats otel-collector
```

---

### Q3: Span 数据不完整

**症状**:

- Span 缺少属性
- 父子关系丢失
- 时间戳不准确

**原因**:

- Span 未正确结束
- 上下文传播失败
- 时钟不同步

**解决方案**:

```rust
// 1. 确保 Span 正确结束
let mut span = tracer.start("my-operation");
span.set_attribute("key", "value");

// 确保在所有代码路径中都调用 end()
let result = risky_operation().await;

match result {
    Ok(v) => {
        span.set_status(StatusCode::Ok, "Success".to_string());
        span.end();  // 成功路径
        Ok(v)
    }
    Err(e) => {
        span.set_status(StatusCode::Error, e.to_string());
        span.end();  // 错误路径
        Err(e)
    }
}

// 2. 使用 RAII 模式自动结束 Span
{
    let _span = tracer.start("auto-end-operation");
    // Span 在作用域结束时自动调用 end()
    do_work().await?;
} // _span 在这里自动结束

// 3. 正确传播上下文
async fn parent_function() {
    let mut parent_span = tracer.start("parent");
    let context = parent_span.context();

    // 传递上下文给子函数
    child_function(&context).await;

    parent_span.end();
}

async fn child_function(parent_context: &TraceContext) {
    let mut child_span = tracer.start_with_context(
        "child",
        SpanKind::Internal,
        parent_context
    );

    // 子操作
    child_span.end();
}

// 4. 同步系统时钟
// Linux/Mac:
// sudo ntpdate -s time.nist.gov
// 或使用 chrony/systemd-timesyncd

// 在代码中使用统一的时间源
use chrono::Utc;
let timestamp = Utc::now().timestamp_nanos() as u64;
```

---

## 🔌 连接问题

### 连接池耗尽

**症状**:

```text
Error: No available connections in pool
```

**解决方案**:

```rust
// 增加连接池大小
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_connection_pool_config(ConnectionPoolConfig {
        max_connections: 200,      // 增加最大连接数
        min_connections: 20,        // 增加最小连接数
        connection_timeout: Duration::from_secs(5),
        idle_timeout: Duration::from_secs(300),
        keep_alive: true,
    })
    .build()
    .await?;

// 监控连接池状态
let pool_stats = client.get_connection_pool_stats().await?;
println!("活跃连接: {}", pool_stats.active_connections);
println!("空闲连接: {}", pool_stats.idle_connections);
println!("等待连接: {}", pool_stats.waiting_connections);
```

### TLS/SSL 错误

**症状**:

```text
Error: SSL certificate verification failed
```

**解决方案**:

```rust
// 1. 配置 TLS
let client = EnhancedOtlpClient::builder()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(TlsConfig {
        enabled: true,
        cert_file: "/path/to/client.crt".to_string(),
        key_file: "/path/to/client.key".to_string(),
        ca_file: "/path/to/ca.crt".to_string(),
        verify_server: true,
    })
    .build()
    .await?;

// 2. 禁用证书验证（仅用于开发环境）
let client = EnhancedOtlpClient::builder()
    .with_endpoint("https://localhost:4317")
    .with_tls_config(TlsConfig {
        enabled: true,
        verify_server: false,  // 禁用验证
        ..Default::default()
    })
    .build()
    .await?;
```

---

## ⚡ 性能问题

### 高延迟

**诊断步骤**:

```rust
use std::time::Instant;

// 1. 测量端到端延迟
let start = Instant::now();

let mut span = tracer.start("operation");
span.set_attribute("test.id", "latency-test");

// 执行操作
do_work().await?;

span.end();

let elapsed = start.elapsed();
println!("总延迟: {:?}", elapsed);

// 2. 分段测量
async fn diagnose_latency() -> Result<(), Box<dyn std::error::Error>> {
    let mut timings = Vec::new();

    // 测量 Span 创建时间
    let t1 = Instant::now();
    let mut span = tracer.start("test");
    timings.push(("span_creation", t1.elapsed()));

    // 测量属性设置时间
    let t2 = Instant::now();
    for i in 0..100 {
        span.set_attribute(format!("attr_{}", i), i);
    }
    timings.push(("attribute_setting", t2.elapsed()));

    // 测量 Span 结束时间
    let t3 = Instant::now();
    span.end();
    timings.push(("span_ending", t3.elapsed()));

    // 测量导出时间
    let t4 = Instant::now();
    client.flush().await?;
    timings.push(("export", t4.elapsed()));

    // 打印结果
    for (name, duration) in timings {
        println!("{}: {:?}", name, duration);
    }

    Ok(())
}
```

**优化方案**:

```rust
// 1. 启用批处理
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_batch_config(BatchConfig {
        max_batch_size: 1000,
        batch_timeout: Duration::from_millis(100),
        max_queue_size: 10000,
        strategy: BatchStrategy::Hybrid,
    })
    .build()
    .await?;

// 2. 启用压缩
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_compression(Compression::Gzip)
    .build()
    .await?;

// 3. 使用连接池
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_connection_pool_config(ConnectionPoolConfig {
        max_connections: 100,
        min_connections: 10,
        keep_alive: true,
        ..Default::default()
    })
    .build()
    .await?;

// 4. 异步导出
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_async_export(true)
    .build()
    .await?;
```

### 高CPU使用率

**诊断**:

```bash
# 1. 使用 perf 分析
sudo perf record -F 99 -p $(pgrep otlp-app) -g -- sleep 30
sudo perf report

# 2. 使用火焰图
cargo flamegraph --bin otlp-app

# 3. 使用 tokio-console
RUSTFLAGS="--cfg tokio_unstable" cargo run --features tokio-console
```

**优化**:

```rust
// 1. 减少不必要的属性
// 避免：
span.set_attribute("large_data", serialize_large_object());

// 推荐：
span.set_attribute("data_id", object.id);
span.set_attribute("data_size", object.size);

// 2. 使用采样
let sampler = TraceIdRatioBasedSampler::new(0.1);  // 10% 采样率
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_sampler(sampler)
    .build()
    .await?;

// 3. 优化序列化
// 使用高效的序列化格式
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_serialization_format(SerializationFormat::Protobuf)
    .build()
    .await?;
```

---

## 💾 数据丢失问题

### Span 丢失

**原因**:

- 队列满
- 导出失败未重试
- 应用崩溃前未刷新

**解决方案**:

```rust
// 1. 增大队列大小
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_batch_config(BatchConfig {
        max_batch_size: 1000,
        batch_timeout: Duration::from_millis(100),
        max_queue_size: 50000,  // 增大队列
        strategy: BatchStrategy::Hybrid,
    })
    .build()
    .await?;

// 2. 启用重试
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_retry_config(RetryConfig {
        max_attempts: 5,  // 增加重试次数
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(10),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![
            ErrorType::Network,
            ErrorType::Timeout,
            ErrorType::Unavailable,
        ],
    })
    .build()
    .await?;

// 3. 优雅关闭
use tokio::signal;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = create_client().await?;

    // 设置信号处理
    tokio::spawn(async move {
        signal::ctrl_c().await.expect("Failed to listen for Ctrl+C");

        println!("收到关闭信号，刷新数据...");
        if let Err(e) = client.flush().await {
            eprintln!("刷新失败: {}", e);
        }

        println!("优雅关闭完成");
        std::process::exit(0);
    });

    // 应用逻辑
    run_application().await?;

    // 确保刷新
    client.flush().await?;

    Ok(())
}

// 4. 定期刷新
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(30));
    loop {
        interval.tick().await;
        if let Err(e) = client.flush().await {
            eprintln!("定期刷新失败: {}", e);
        }
    }
});
```

### 监控数据丢失

```rust
// 实现丢失监控
struct LossMonitor {
    sent_count: AtomicU64,
    success_count: AtomicU64,
    failure_count: AtomicU64,
}

impl LossMonitor {
    fn record_sent(&self) {
        self.sent_count.fetch_add(1, Ordering::Relaxed);
    }

    fn record_success(&self) {
        self.success_count.fetch_add(1, Ordering::Relaxed);
    }

    fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
    }

    fn get_loss_rate(&self) -> f64 {
        let sent = self.sent_count.load(Ordering::Relaxed);
        let failed = self.failure_count.load(Ordering::Relaxed);

        if sent == 0 {
            0.0
        } else {
            failed as f64 / sent as f64
        }
    }
}

// 使用监控
let monitor = Arc::new(LossMonitor::new());

let mon = Arc::clone(&monitor);
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let loss_rate = mon.get_loss_rate();

        if loss_rate > 0.01 {  // 超过 1% 丢失率
            eprintln!("⚠️ 数据丢失率过高: {:.2}%", loss_rate * 100.0);
        }
    }
});
```

---

## 🧠 内存问题

### 内存泄漏

**诊断**:

```bash
# 1. 使用 valgrind
valgrind --leak-check=full --show-leak-kinds=all ./target/release/otlp-app

# 2. 使用 heaptrack
heaptrack ./target/release/otlp-app

# 3. 在 Rust 中使用 jemalloc
# Cargo.toml
[dependencies]
jemallocator = "0.5"

# main.rs
#[global_allocator]
static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;
```

**常见原因和解决方案**:

```rust
// 1. Span 未结束
// 错误：
let span = tracer.start("operation");
// 忘记调用 span.end()

// 正确：
{
    let mut span = tracer.start("operation");
    // 操作
    span.end();  // 或使用 Drop trait 自动结束
}

// 2. 循环引用
// 错误：
struct Service {
    client: Arc<Client>,
    spans: Vec<Span>,  // Span 持有 Client 的引用
}

// 正确：
struct Service {
    client: Arc<Client>,
    span_ids: Vec<String>,  // 只存储 ID
}

// 3. 队列积压
// 监控队列大小
let queue_size = client.get_queue_size().await?;
if queue_size > 40000 {
    eprintln!("⚠️ 队列积压严重: {}", queue_size);
    // 触发刷新或降低采样率
}

// 4. 使用内存池
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_memory_pool_config(MemoryPoolConfig {
        initial_size: 1024 * 1024,
        max_size: 100 * 1024 * 1024,
        chunk_size: 64 * 1024,
        growth_factor: 2.0,
        gc_threshold: 0.8,
    })
    .build()
    .await?;
```

---

## 📋 日志分析

### 启用详细日志

```bash
# 设置日志级别
export RUST_LOG=otlp=debug,info

# 或在代码中配置
env_logger::Builder::from_env(
    env_logger::Env::default()
        .default_filter_or("otlp=debug,info")
).init();
```

### 日志分析技巧

```bash
# 1. 查找错误
grep "ERROR" app.log | tail -n 50

# 2. 统计错误类型
grep "ERROR" app.log | awk '{print $5}' | sort | uniq -c | sort -nr

# 3. 分析延迟
grep "duration" app.log | awk '{print $NF}' | sort -n | tail -n 100

# 4. 查找特定 Span
grep "span_id=abc123" app.log

# 5. 使用 jq 分析 JSON 日志
cat app.log | jq 'select(.level == "ERROR")'
cat app.log | jq 'select(.duration > 1000)'
```

---

## 🐛 调试技巧

### 使用调试工具

```rust
// 1. 添加调试输出
#[cfg(debug_assertions)]
{
    println!("DEBUG: Span created: {:?}", span);
    println!("DEBUG: Queue size: {}", client.get_queue_size().await?);
}

// 2. 使用条件断点
// 在 VS Code 中设置断点条件
// span.name == "slow-operation"

// 3. 使用 tracing 库
use tracing::{debug, info, warn, error, instrument};

#[instrument]
async fn traced_function(param: &str) {
    debug!("Function called with: {}", param);
    // 自动记录函数调用和参数
}

// 4. 环境变量控制调试
if std::env::var("OTLP_DEBUG").is_ok() {
    // 启用详细日志
    enable_debug_logging();
}
```

### 性能分析

```rust
// 使用 criterion 进行基准测试
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_span_creation(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let client = rt.block_on(async {
        create_client().await.unwrap()
    });

    c.bench_function("span_creation", |b| {
        b.to_async(&rt).iter(|| async {
            let tracer = client.tracer("bench");
            let mut span = tracer.start("operation");
            span.set_attribute("test", "value");
            span.end();
        });
    });
}

criterion_group!(benches, benchmark_span_creation);
criterion_main!(benches);
```

---

## 🆘 获取帮助

### 收集诊断信息

```bash
#!/bin/bash
# collect-diagnostics.sh

echo "=== 系统信息 ===" > diagnostics.txt
uname -a >> diagnostics.txt
date >> diagnostics.txt

echo -e "\n=== Rust 版本 ===" >> diagnostics.txt
rustc --version >> diagnostics.txt
cargo --version >> diagnostics.txt

echo -e "\n=== 应用日志 ===" >> diagnostics.txt
tail -n 1000 app.log >> diagnostics.txt

echo -e "\n=== 资源使用 ===" >> diagnostics.txt
ps aux | grep otlp >> diagnostics.txt
free -h >> diagnostics.txt
df -h >> diagnostics.txt

echo -e "\n=== 网络连接 ===" >> diagnostics.txt
netstat -an | grep 4317 >> diagnostics.txt

echo -e "\n=== 配置文件 ===" >> diagnostics.txt
cat config.yaml >> diagnostics.txt 2>&1

echo "诊断信息已保存到 diagnostics.txt"
```

### 报告问题

提交 Issue 时请包含：

1. **环境信息**
   - OS 版本
   - Rust 版本
   - 依赖版本

2. **问题描述**
   - 预期行为
   - 实际行为
   - 错误消息

3. **复现步骤**
   - 最小可复现示例
   - 配置文件
   - 日志输出

4. **尝试的解决方案**
   - 已经尝试的方法
   - 结果如何

### 社区资源

- 📖 [项目文档](../README.md)
- 💬 [GitHub Discussions](https://github.com/your-org/OTLP_rust/discussions)
- 🐛 [Issue Tracker](https://github.com/your-org/OTLP_rust/issues)
- 📧 [邮件列表](mailto:otlp-rust@example.com)

---

_最后更新: 2025年10月20日_
_版本: 1.0.0_
