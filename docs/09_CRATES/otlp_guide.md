# 📊 OTLP Crate 使用指南

**版本**: 1.0
**定位**: Rust的OTLP全面梳理、通用封装和惯用法
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: OTLP Crate 使用指南 - Rust OTLP 实现的完整指南，包括信号处理、传输和优化。

---

## 📋 目录

- [📊 OTLP Crate 使用指南](#-otlp-crate-使用指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心功能](#核心功能)
    - [📦 功能模块](#-功能模块)
  - [快速开始](#快速开始)
    - [安装依赖](#安装依赖)
    - [基础示例](#基础示例)
  - [OTLP信号](#otlp信号)
    - [Trace (分布式追踪)](#trace-分布式追踪)
    - [Metric (指标采集)](#metric-指标采集)
    - [Log (日志聚合)](#log-日志聚合)
    - [Profile (性能分析)](#profile-性能分析)
    - [Event (事件追踪)](#event-事件追踪)
  - [传输协议](#传输协议)
    - [gRPC](#grpc)
    - [HTTP/JSON](#httpjson)
    - [HTTP/Protobuf](#httpprotobuf)
    - [OTLP/Arrow](#otlparrow)
  - [性能优化](#性能优化)
    - [SIMD优化](#simd优化)
    - [内存池](#内存池)
    - [连接池](#连接池)
    - [Tracezip压缩](#tracezip压缩)
  - [语义约定](#语义约定)
    - [HTTP语义约定](#http语义约定)
    - [Database语义约定](#database语义约定)
    - [Messaging语义约定](#messaging语义约定)
    - [Kubernetes语义约定](#kubernetes语义约定)
  - [高级特性](#高级特性)
    - [Profiling API](#profiling-api)
    - [OpAMP (Open Agent Management Protocol)](#opamp-open-agent-management-protocol)
    - [OTTL (OpenTelemetry Transformation Language)](#ottl-opentelemetry-transformation-language)
  - [最佳实践](#最佳实践)
    - [综合示例](#综合示例)
    - [性能优化建议](#性能优化建议)
  - [完整文档](#完整文档)
    - [📚 详细文档](#-详细文档)
    - [📖 主要文档索引](#-主要文档索引)
    - [🎯 示例代码](#-示例代码)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [架构文档](#架构文档)
    - [主文档](#主文档)
    - [OTLP标准](#otlp标准)
  - [🤝 贡献](#-贡献)

---

## 概述

`otlp` crate 提供了 OpenTelemetry Protocol (OTLP) 的完整 Rust 实现。它专注于:

- ✅ **OTLP信号**: Trace、Metric、Log、Profile、Event 全信号支持
- ✅ **传输协议**: gRPC、HTTP/JSON、HTTP/Protobuf 多种传输方式
- ✅ **性能优化**: SIMD、内存池、连接池、零拷贝等极致优化
- ✅ **语义约定**: HTTP、Database、Messaging、Kubernetes 等标准化约定
- ✅ **高级特性**: Profiling API、Tracezip压缩、OpAMP管理协议

---

## 核心功能

### 📦 功能模块

```text
otlp/
├── 📡 OTLP信号 (signals/)
│   ├── Trace (分布式追踪)
│   ├── Metric (指标采集)
│   ├── Log (日志聚合)
│   ├── Profile (性能分析)
│   └── Event (事件追踪)
│
├── 🚀 传输协议 (transport/)
│   ├── gRPC (高性能RPC)
│   ├── HTTP/JSON (易用性)
│   ├── HTTP/Protobuf (高效二进制)
│   └── OTLP/Arrow (列式存储)
│
├── ⚡ 性能优化 (performance/)
│   ├── SIMD (向量化计算)
│   ├── 内存池 (减少分配)
│   ├── 连接池 (连接复用)
│   ├── 零拷贝 (减少复制)
│   └── Tracezip (专用压缩)
│
├── 📝 语义约定 (semantic_conventions/)
│   ├── HTTP (HTTP属性)
│   ├── Database (数据库属性)
│   ├── Messaging (消息队列属性)
│   ├── RPC (RPC属性)
│   └── Kubernetes (K8s属性)
│
└── 🔧 高级特性 (advanced_features/)
    ├── Profiling API (CPU/内存分析)
    ├── OpAMP (远程管理)
    ├── OTTL (转换语言)
    └── 自定义扩展
```

---

## 快速开始

### 安装依赖

在 `Cargo.toml` 中添加:

```toml
[dependencies]
otlp = { path = "crates/otlp" }

# 或使用特性标志
otlp = { path = "crates/otlp", features = ["trace", "metrics", "logs", "profiling"] }
```

### 基础示例

```rust
use otlp::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 创建 OTLP 客户端
    let client = OtlpClient::builder()
        .endpoint("http://localhost:4317")
        .with_compression(CompressionType::Gzip)
        .with_timeout(Duration::from_secs(5))
        .build()?;

    // 2. 发送 Trace
    let span = Span::builder("my_operation")
        .with_attribute("service.name", "my-service")
        .with_attribute("http.method", "GET")
        .build();

    client.send_trace(vec![span]).await?;

    // 3. 发送 Metric
    let metric = Metric::counter("requests_total")
        .with_value(1.0)
        .with_attribute("status", "success")
        .build();

    client.send_metric(vec![metric]).await?;

    // 4. 发送 Log
    let log = LogRecord::builder()
        .with_severity(Severity::Info)
        .with_body("Application started")
        .with_attribute("version", "1.0.0")
        .build();

    client.send_log(vec![log]).await?;

    Ok(())
}
```

---

## OTLP信号

### Trace (分布式追踪)

**Trace** 追踪请求在分布式系统中的完整路径:

```rust
use otlp::trace::*;

// 创建 Tracer
let tracer = Tracer::builder()
    .with_service_name("my-service")
    .with_service_version("1.0.0")
    .build()?;

// 创建根 Span
let mut root_span = tracer.start_span("handle_request");
root_span.set_attribute("http.method", "GET");
root_span.set_attribute("http.url", "https://api.example.com/users");
root_span.set_attribute("http.status_code", 200);

// 创建子 Span
let mut db_span = tracer.start_span_with_parent("database_query", &root_span);
db_span.set_attribute("db.system", "postgresql");
db_span.set_attribute("db.statement", "SELECT * FROM users WHERE id = $1");
db_span.set_attribute("db.name", "mydb");

// 记录事件
db_span.add_event(Event {
    name: "query_start".to_string(),
    timestamp: SystemTime::now(),
    attributes: HashMap::new(),
});

// 模拟查询
tokio::time::sleep(Duration::from_millis(50)).await;

db_span.add_event(Event {
    name: "query_end".to_string(),
    timestamp: SystemTime::now(),
    attributes: HashMap::new(),
});

// 结束 Span
db_span.end();
root_span.end();

// 导出 Trace
tracer.export().await?;
```

### Metric (指标采集)

**Metric** 采集和聚合系统指标:

```rust
use otlp::metrics::*;

// 创建 Meter
let meter = Meter::builder()
    .with_service_name("my-service")
    .build()?;

// Counter: 单调递增计数器
let request_counter = meter.create_counter("http_requests_total")
    .with_description("Total HTTP requests")
    .with_unit("1")
    .build()?;

request_counter.add(1, &[
    ("method", "GET"),
    ("status", "200"),
]);

// Gauge: 瞬时值
let memory_gauge = meter.create_gauge("process_memory_bytes")
    .with_description("Process memory usage")
    .with_unit("bytes")
    .build()?;

memory_gauge.record(1024 * 1024 * 128, &[]); // 128 MB

// Histogram: 分布统计
let latency_histogram = meter.create_histogram("http_request_duration_seconds")
    .with_description("HTTP request latency")
    .with_unit("s")
    .with_boundaries(vec![0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0])
    .build()?;

latency_histogram.record(0.023, &[
    ("method", "GET"),
    ("endpoint", "/api/users"),
]);

// UpDownCounter: 可增可减计数器
let active_requests = meter.create_up_down_counter("active_requests")
    .with_description("Number of active requests")
    .with_unit("1")
    .build()?;

active_requests.add(1, &[]);  // 请求开始
// ... 处理请求 ...
active_requests.add(-1, &[]); // 请求结束

// 导出 Metric
meter.export().await?;
```

### Log (日志聚合)

**Log** 结构化日志采集:

```rust
use otlp::logs::*;

// 创建 Logger
let logger = Logger::builder()
    .with_service_name("my-service")
    .build()?;

// 发送日志
logger.info("Application started", &[
    ("version", "1.0.0"),
    ("environment", "production"),
]);

logger.error("Database connection failed", &[
    ("error", "connection timeout"),
    ("host", "localhost"),
    ("port", "5432"),
]);

// 结构化日志
logger.log(LogRecord {
    timestamp: SystemTime::now(),
    severity: Severity::Warning,
    body: LogBody::String("High memory usage detected".to_string()),
    attributes: vec![
        ("memory_usage_percent", AttributeValue::F64(85.5)),
        ("threshold_percent", AttributeValue::F64(80.0)),
    ].into_iter().collect(),
    trace_id: Some(trace_id),  // 关联到 Trace
    span_id: Some(span_id),
    ..Default::default()
});

// 导出 Log
logger.export().await?;
```

### Profile (性能分析)

**Profile** 采集性能分析数据:

```rust
use otlp::profiling::*;

// 创建 CPU Profiler
let cpu_profiler = CpuProfiler::builder()
    .with_sampling_frequency(100) // 100 Hz
    .with_duration(Duration::from_secs(60))
    .build()?;

// 开始采样
cpu_profiler.start()?;

// 运行应用...
run_application().await?;

// 停止采样
let profile = cpu_profiler.stop()?;

// 导出 Profile
let exporter = ProfileExporter::builder()
    .with_endpoint("http://localhost:4317")
    .build()?;

exporter.export(profile).await?;

// 内存 Profiler
let memory_profiler = MemoryProfiler::builder()
    .with_sampling_rate(1024 * 1024) // 每 1MB 采样一次
    .build()?;

memory_profiler.start()?;
// ... 运行应用 ...
let memory_profile = memory_profiler.stop()?;
exporter.export(memory_profile).await?;
```

### Event (事件追踪)

**Event** 捕获业务事件:

```rust
use otlp::events::*;

// 创建 Event Emitter
let emitter = EventEmitter::builder()
    .with_service_name("my-service")
    .build()?;

// 发送事件
emitter.emit(Event {
    name: "user.created".to_string(),
    domain: "user_management".to_string(),
    timestamp: SystemTime::now(),
    attributes: vec![
        ("user.id", AttributeValue::I64(12345)),
        ("user.email", AttributeValue::String("user@example.com".to_string())),
        ("user.role", AttributeValue::String("admin".to_string())),
    ].into_iter().collect(),
    ..Default::default()
}).await?;

// 关联到 Trace
emitter.emit_with_trace(Event {
    name: "order.placed".to_string(),
    domain: "order_management".to_string(),
    timestamp: SystemTime::now(),
    attributes: vec![
        ("order.id", AttributeValue::String("ORD-001".to_string())),
        ("order.amount", AttributeValue::F64(99.99)),
    ].into_iter().collect(),
    trace_id: Some(trace_id),
    span_id: Some(span_id),
    ..Default::default()
}).await?;
```

---

## 传输协议

### gRPC

**gRPC** 提供高性能的二进制传输:

```rust
use otlp::transport::grpc::*;

// 创建 gRPC 客户端
let grpc_client = GrpcClient::builder()
    .endpoint("http://localhost:4317")
    .with_tls(TlsConfig {
        cert_path: "/path/to/cert.pem",
        key_path: "/path/to/key.pem",
        ca_path: Some("/path/to/ca.pem"),
    })
    .with_compression(GrpcCompression::Gzip)
    .with_metadata("api-key", "secret")
    .build()?;

// 发送数据
grpc_client.export_trace(trace_data).await?;
grpc_client.export_metrics(metrics_data).await?;
grpc_client.export_logs(logs_data).await?;
```

### HTTP/JSON

**HTTP/JSON** 提供易用性和调试便利:

```rust
use otlp::transport::http::*;

// 创建 HTTP/JSON 客户端
let http_client = HttpClient::builder()
    .endpoint("http://localhost:4318/v1/traces")
    .with_format(HttpFormat::Json)
    .with_header("Authorization", "Bearer token")
    .with_timeout(Duration::from_secs(10))
    .build()?;

// 发送数据
http_client.send(trace_data).await?;
```

### HTTP/Protobuf

**HTTP/Protobuf** 平衡性能和兼容性:

```rust
use otlp::transport::http::*;

// 创建 HTTP/Protobuf 客户端
let proto_client = HttpClient::builder()
    .endpoint("http://localhost:4318/v1/traces")
    .with_format(HttpFormat::Protobuf)
    .with_compression(HttpCompression::Gzip)
    .build()?;

// 发送数据
proto_client.send(trace_data).await?;
```

### OTLP/Arrow

**OTLP/Arrow** 提供极致性能的列式存储传输:

```rust
use otlp::transport::arrow::*;

// 创建 OTLP/Arrow 客户端
let arrow_client = ArrowClient::builder()
    .endpoint("http://localhost:4317")
    .with_batch_size(10000)
    .with_compression(ArrowCompression::Zstd)
    .build()?;

// 批量发送数据
arrow_client.send_batch(trace_data).await?;

// 性能统计
let stats = arrow_client.get_stats();
println!("Compression ratio: {:.2}x", stats.compression_ratio);
println!("Throughput: {} spans/s", stats.throughput);
```

---

## 性能优化

### SIMD优化

**SIMD** 向量化计算加速数据处理:

```rust
use otlp::simd::*;

// CPU特性检测
let features = CpuFeatures::detect();
println!("AVX2: {}", features.has_avx2());
println!("AVX512: {}", features.has_avx512());

// 批量序列化
let serializer = BatchSerializer::new();
let spans: Vec<Span> = vec![/* ... */];

let serialized = serializer.serialize_batch(&spans)?;
println!("Serialized {} spans in {:?}", spans.len(), elapsed);

// 批量聚合
let aggregator = Aggregator::new();
let metrics: Vec<Metric> = vec![/* ... */];

let aggregated = aggregator.aggregate(&metrics)?;
println!("Aggregated {} metrics", metrics.len());
```

### 内存池

**内存池** 减少内存分配开销:

```rust
use otlp::performance::memory_pool::*;

// 创建内存池
let pool = MemoryPool::builder()
    .with_pool_size(1024)
    .with_buffer_size(4096)
    .build()?;

// 从池中获取缓冲区
let mut buffer = pool.acquire().await?;

// 使用缓冲区
buffer.write_all(data)?;

// 自动归还到池中
drop(buffer);
```

### 连接池

**连接池** 复用网络连接:

```rust
use otlp::transport::connection_pool::*;

// 创建连接池
let pool = ConnectionPool::builder()
    .with_max_connections(50)
    .with_min_connections(5)
    .with_idle_timeout(Duration::from_secs(300))
    .build()?;

// 获取连接
let conn = pool.get().await?;

// 使用连接
conn.send(data).await?;

// 自动归还到池中
drop(conn);
```

### Tracezip压缩

**Tracezip** 专为trace数据设计的压缩算法:

```rust
use otlp::compression::tracezip::*;

// 创建压缩器
let compressor = TraceCompressor::builder()
    .with_compression_level(6)
    .with_dictionary_size(32 * 1024)
    .build()?;

// 压缩trace数据
let compressed = compressor.compress(&trace_data)?;
println!("Original size: {} bytes", trace_data.len());
println!("Compressed size: {} bytes", compressed.len());
println!("Compression ratio: {:.2}x",
    trace_data.len() as f64 / compressed.len() as f64);

// 解压缩
let decompressed = compressor.decompress(&compressed)?;
assert_eq!(trace_data, decompressed);
```

---

## 语义约定

### HTTP语义约定

```rust
use otlp::semantic_conventions::http::*;

// 创建HTTP属性
let http_attrs = HttpAttributes::builder()
    .method(HttpMethod::GET)
    .url("https://api.example.com/users/123")
    .status_code(200)
    .request_content_length(0)
    .response_content_length(1024)
    .user_agent("MyApp/1.0")
    .build();

// 添加到Span
span.set_attributes(http_attrs.into_iter());

// 服务器端
let server_attrs = HttpAttributes::builder()
    .method(HttpMethod::POST)
    .target("/api/users")
    .scheme(HttpScheme::HTTPS)
    .host("api.example.com")
    .server_name("web-server-01")
    .route("/api/users")
    .build();
```

### Database语义约定

```rust
use otlp::semantic_conventions::database::*;

// 创建Database属性
let db_attrs = DatabaseAttributes::builder()
    .system(DatabaseSystem::PostgreSQL)
    .name("mydb")
    .statement("SELECT * FROM users WHERE id = $1")
    .operation(DatabaseOperation::Select)
    .connection_string("postgresql://localhost:5432/mydb")
    .user("dbuser")
    .build();

// 添加到Span
span.set_attributes(db_attrs.into_iter());
```

### Messaging语义约定

```rust
use otlp::semantic_conventions::messaging::*;

// 创建Messaging属性
let msg_attrs = MessagingAttributes::builder()
    .system(MessagingSystem::Kafka)
    .destination("orders-topic")
    .destination_kind(DestinationKind::Topic)
    .operation(MessagingOperation::Publish)
    .message_id("msg-123")
    .conversation_id("conv-456")
    .build();

// 消费者端
let consumer_attrs = MessagingAttributes::builder()
    .system(MessagingSystem::Kafka)
    .destination("orders-topic")
    .operation(MessagingOperation::Receive)
    .consumer_group("order-processors")
    .build();
```

### Kubernetes语义约定

```rust
use otlp::semantic_conventions::k8s::*;

// 创建K8s属性
let k8s_attrs = K8sAttributes::builder()
    .namespace("production")
    .pod_name("my-service-7d8f9b5c6d-x8k9m")
    .deployment_name("my-service")
    .container_name("app")
    .node_name("node-1")
    .resource_type(K8sResourceType::Pod)
    .build();

// 自动从环境检测
let k8s_attrs = K8sAttributes::from_env()?;
```

---

## 高级特性

### Profiling API

**Profiling API** 持续性能分析:

```rust
use otlp::profiling::*;

// CPU性能分析
let cpu_profiler = CpuProfiler::builder()
    .with_sampling_frequency(100)
    .build()?;

// 开始采样
cpu_profiler.start()?;

// 异步性能分析
let _guard = profile_async(|| async {
    expensive_operation().await?;
    Ok(())
}).await?;

// 生成pprof格式
let pprof_data = cpu_profiler.generate_pprof()?;
std::fs::write("cpu.pprof", pprof_data)?;

// 链接到Trace
let profile_id = link_profile_to_current_trace()?;
```

### OpAMP (Open Agent Management Protocol)

**OpAMP** 远程管理和配置:

```rust
use otlp::opamp::*;

// 创建OpAMP客户端
let opamp_client = OpAMPClient::builder()
    .endpoint("ws://localhost:4320")
    .with_instance_uid("agent-123")
    .build()?;

// 连接到OpAMP服务器
opamp_client.connect().await?;

// 发送agent状态
opamp_client.update_status(AgentStatus {
    health: Health::Healthy,
    effective_config: current_config,
    remote_config_status: RemoteConfigStatus::Applied,
}).await?;

// 接收远程配置
opamp_client.on_config_change(|new_config| {
    // 应用新配置
    apply_config(new_config)?;
    Ok(())
}).await?;

// 接收自定义命令
opamp_client.on_custom_command(|command| {
    match command.type_ {
        "restart" => restart_agent()?,
        "update" => update_agent()?,
        _ => {}
    }
    Ok(())
}).await?;
```

### OTTL (OpenTelemetry Transformation Language)

**OTTL** 数据转换语言:

```rust
use otlp::ottl::*;

// 创建OTTL处理器
let ottl = OttlProcessor::new();

// 过滤Span
ottl.add_rule(r#"
    attributes["http.status_code"] >= 500
"#)?;

// 转换属性
ottl.add_transformation(r#"
    set(attributes["http.method"], Uppercase(attributes["http.method"]))
"#)?;

// 删除敏感信息
ottl.add_transformation(r#"
    delete_key(attributes, "password")
    delete_key(attributes, "api_key")
"#)?;

// 应用规则
let filtered_spans = ottl.process(spans)?;
```

---

## 最佳实践

### 综合示例

```rust
use otlp::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 创建优化的客户端
    let client = OtlpClient::builder()
        .endpoint("http://localhost:4317")
        .with_compression(CompressionType::Zstd)
        .with_batch_size(1000)
        .with_timeout(Duration::from_secs(5))
        .with_retry_policy(RetryPolicy {
            max_attempts: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
        })
        .with_connection_pool(ConnectionPoolConfig {
            max_connections: 20,
            min_connections: 5,
        })
        .with_memory_pool(MemoryPoolConfig {
            pool_size: 1024,
            buffer_size: 4096,
        })
        .build()?;

    // 2. 创建Tracer (使用语义约定)
    let tracer = client.create_tracer("my-service");

    // 3. 发送HTTP请求 (完整追踪)
    let span = tracer.start_span("http_request");

    // 添加HTTP语义约定
    let http_attrs = HttpAttributes::builder()
        .method(HttpMethod::GET)
        .url("https://api.example.com/users")
        .status_code(200)
        .build();

    span.set_attributes(http_attrs.into_iter());

    // 4. 数据库查询 (子Span)
    let db_span = tracer.start_span_with_parent("db_query", &span);

    let db_attrs = DatabaseAttributes::builder()
        .system(DatabaseSystem::PostgreSQL)
        .statement("SELECT * FROM users")
        .build();

    db_span.set_attributes(db_attrs.into_iter());
    db_span.end();

    // 5. 记录指标
    let meter = client.create_meter("my-service");

    meter.counter("http_requests_total")
        .add(1, &[("status", "200")]);

    meter.histogram("http_request_duration_seconds")
        .record(0.123, &[("endpoint", "/users")]);

    // 6. 记录日志
    let logger = client.create_logger("my-service");

    logger.info("Request completed", &[
        ("user_id", "123"),
        ("duration_ms", "123"),
    ]);

    // 7. 结束Span
    span.end();

    // 8. 刷新数据
    client.force_flush().await?;

    Ok(())
}
```

### 性能优化建议

```rust
// 1. 批量发送
let batch_config = BatchConfig {
    max_batch_size: 1000,
    max_batch_delay: Duration::from_secs(5),
};

// 2. 使用SIMD
#[cfg(target_feature = "avx2")]
let serializer = SimdSerializer::new();

// 3. 启用压缩
let compression = if data_size > 1024 {
    CompressionType::Zstd
} else {
    CompressionType::None
};

// 4. 连接池配置
let pool_config = ConnectionPoolConfig {
    max_connections: num_cpus::get() * 4,
    connection_timeout: Duration::from_secs(10),
    idle_timeout: Duration::from_secs(300),
};

// 5. 内存池配置
let memory_config = MemoryPoolConfig {
    pool_size: 2048,
    buffer_size: 8192,
    prealloc: true,
};
```

---

## 完整文档

### 📚 详细文档

otlp crate 包含 **190+ 篇** 详细文档，覆盖:

- **OTLP协议规范** (完整的协议文档和实现指南)
- **信号类型详解** (Trace、Metric、Log、Profile、Event)
- **传输协议** (gRPC、HTTP、OTLP/Arrow)
- **性能优化** (SIMD、内存池、连接池、压缩)
- **语义约定** (HTTP、Database、Messaging、K8s等)
- **高级特性** (Profiling、OpAMP、OTTL)

访问: [crates/otlp/docs/](../../crates/otlp/docs/)

### 📖 主要文档索引

| 文档 | 说明 | 规模 |
|------|------|------|
| [完整API文档](../03_API_REFERENCE/README.md) | API参考 | 3000+行 |
| [Profiling API](../03_API_REFERENCE/profiling_api.md) | 性能分析 | 500+行 |
| [SIMD API](../03_API_REFERENCE/simd_api.md) | SIMD优化 | 650+行 |
| [Compression API](../03_API_REFERENCE/compression_api.md) | 压缩算法 | 600+行 |
| [Semantic Conventions](../03_API_REFERENCE/semantic_conventions_api.md) | 语义约定 | 700+行 |
| [OTLP标准对齐](../08_REFERENCE/otlp_standards_alignment.md) | 标准参考 | 1300+行 |
| [2024-2025特性](../08_REFERENCE/otlp_2024_2025_features.md) | 最新特性 | 800+行 |

### 🎯 示例代码

32个完整示例位于 `crates/otlp/examples/`:

```bash
# 运行示例
cd crates/otlp

# 基础示例
cargo run --example hello_world
cargo run --example simple_demo
cargo run --example simple_usage

# 性能示例
cargo run --example performance_demo
cargo run --example performance_optimization_demo
cargo run --example core_optimization_demo

# SIMD示例
cargo run --example simd_demo

# 压缩示例
cargo run --example tracezip_demo

# Profiling示例
cargo run --example profiling_demo

# 语义约定示例
cargo run --example semantic_conventions_demo
cargo run --example database_semantic_conventions_demo
cargo run --example messaging_semantic_conventions_demo
cargo run --example k8s_semantic_conventions_demo

# 微服务示例
cargo run --example microservices_demo
cargo run --example advanced_microservices_demo

# 综合示例
cargo run --example comprehensive_demo
cargo run --example comprehensive_usage
```

---

## 🔗 相关资源

### 项目文档

- [返回 Crates 总览](README.md)
- [libraries 使用指南](libraries_guide.md)
- [model 使用指南](model_guide.md)
- [reliability 使用指南](reliability_guide.md)

### 架构文档

- [架构重组计划](../CRATES_ARCHITECTURE_REORG_2025_10_26.md)
- [知识图谱](../CRATES_KNOWLEDGE_GRAPH_2025_10_26.md)
- [矩阵对比](../CRATES_MATRIX_COMPARISON_2025_10_26.md)

### 主文档

- [项目主文档](../README.md)
- [文档导航](../DOCUMENTATION_GUIDE.md)
- [快速开始](../01_GETTING_STARTED/README.md)

### OTLP标准

- [OTLP规范](https://github.com/open-telemetry/opentelemetry-proto)
- [OpenTelemetry官方文档](https://opentelemetry.io/docs/)
- [语义约定规范](https://opentelemetry.io/docs/specs/semconv/)

---

## 🤝 贡献

欢迎贡献！

1. **添加新功能**: 实现更多OTLP特性
2. **改进文档**: 完善使用指南和最佳实践
3. **提供示例**: 分享实际项目经验
4. **报告问题**: 反馈使用中的问题

详见: [贡献指南](../guides/CONTRIBUTING.md)

---

**最后更新**: 2025年10月26日
**文档版本**: v1.0.0
**维护状态**: 🔄 持续维护中
