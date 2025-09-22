# OTLP 基础概念

## 📚 概述

OpenTelemetry Protocol (OTLP) 是一个开放标准的遥测数据传输协议，旨在提供统一的API、库和工具，用于生成、收集和导出遥测数据。

## 🎯 核心概念

### 1. 遥测数据 (Telemetry Data)

遥测数据是描述系统行为和性能的数据，主要包括三种类型：

#### 1.1 Traces (追踪)

**定义**: 追踪数据描述了请求在分布式系统中的执行路径。

**关键概念**:

- **Span**: 表示操作的一个工作单元
- **Trace**: 表示请求的完整执行路径
- **Context**: 包含传播信息的上下文

```rust
// Span 示例
let span = tracer.start("http_request");
span.set_attribute("http.method", "GET");
span.set_attribute("http.url", "/api/users");
span.end();
```

#### 1.2 Metrics (指标)

**定义**: 指标数据描述了系统的可量化测量值。

**关键概念**:

- **Counter**: 累积计数器
- **Gauge**: 瞬时值
- **Histogram**: 分布统计

```rust
// Metrics 示例
let counter = meter.create_counter("requests_total");
counter.add(1, &[KeyValue::new("method", "GET")]);

let histogram = meter.create_histogram("request_duration");
histogram.record(150.0, &[KeyValue::new("endpoint", "/api")]);
```

#### 1.3 Logs (日志)

**定义**: 日志数据包含结构化的事件记录。

**关键概念**:

- **Severity**: 日志级别
- **Message**: 日志消息
- **Attributes**: 结构化属性

```rust
// Logs 示例
logger.emit(LogRecord {
    severity: LogSeverity::Info,
    body: "User login successful".into(),
    attributes: vec![
        KeyValue::new("user_id", "12345"),
        KeyValue::new("ip_address", "192.168.1.100"),
    ],
});
```

### 2. 数据模型

#### 2.1 Resource (资源)

资源描述了生成遥测数据的实体：

```rust
let resource = Resource::new(vec![
    KeyValue::new("service.name", "user-service"),
    KeyValue::new("service.version", "1.0.0"),
    KeyValue::new("deployment.environment", "production"),
]);
```

#### 2.2 Scope (作用域)

作用域定义了遥测数据的来源：

```rust
let scope = InstrumentationScope {
    name: "opentelemetry-rust",
    version: "0.21.0",
    attributes: vec![],
    schema_url: None,
};
```

#### 2.3 Attributes (属性)

属性是键值对，提供额外的上下文信息：

```rust
let attributes = vec![
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.status_code", 200),
    KeyValue::new("user.id", "12345"),
];
```

### 3. 协议规范

#### 3.1 OTLP v1.0.0

OTLP协议定义了遥测数据的编码、传输和传递机制：

**核心特性**:

- 统一的协议支持Traces、Metrics、Logs
- 基于Protocol Buffers的编码
- 支持gRPC和HTTP传输
- 内置压缩和批处理支持

#### 3.2 传输协议

**gRPC传输**:

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc);
```

**HTTP传输**:

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4318")
    .with_protocol(TransportProtocol::Http);
```

### 4. 语义约定

#### 4.1 资源语义约定

标准化的资源属性命名：

```rust
// 服务信息
KeyValue::new("service.name", "user-service")
KeyValue::new("service.version", "1.0.0")
KeyValue::new("service.namespace", "production")

// 部署信息
KeyValue::new("deployment.environment", "production")
KeyValue::new("deployment.version", "v1.2.3")

// 主机信息
KeyValue::new("host.name", "web-server-01")
KeyValue::new("host.type", "AWS EC2")
```

#### 4.2 跨度语义约定

标准化的跨度属性命名：

```rust
// HTTP相关
KeyValue::new("http.method", "GET")
KeyValue::new("http.url", "/api/users")
KeyValue::new("http.status_code", 200)

// 数据库相关
KeyValue::new("db.system", "postgresql")
KeyValue::new("db.name", "users")
KeyValue::new("db.operation", "SELECT")
```

## 🏗️ 架构组件

### 1. API层

API层定义了遥测数据生成的接口：

```rust
// Traces API
pub trait Tracer {
    fn start(&self, name: &str) -> Span;
}

// Metrics API
pub trait Meter {
    fn create_counter(&self, name: &str) -> Counter<u64>;
    fn create_gauge(&self, name: &str) -> Gauge<f64>;
    fn create_histogram(&self, name: &str) -> Histogram<f64>;
}

// Logs API
pub trait Logger {
    fn emit(&self, record: LogRecord);
}
```

### 2. SDK层

SDK层提供了API的具体实现：

```rust
pub struct OtlpSDK {
    tracer: Tracer,
    meter: Meter,
    logger: Logger,
    exporter: Box<dyn Exporter>,
    processor: Box<dyn Processor>,
}
```

### 3. 导出器层

导出器负责将数据发送到后端系统：

```rust
pub trait Exporter {
    async fn export_traces(&self, traces: Vec<Trace>) -> Result<ExportResult>;
    async fn export_metrics(&self, metrics: Vec<Metric>) -> Result<ExportResult>;
    async fn export_logs(&self, logs: Vec<Log>) -> Result<ExportResult>;
}
```

### 4. 传输层

传输层处理网络通信：

```rust
pub trait Transport {
    async fn send_traces(&self, data: &[u8]) -> Result<()>;
    async fn send_metrics(&self, data: &[u8]) -> Result<()>;
    async fn send_logs(&self, data: &[u8]) -> Result<()>;
}
```

## 🔄 数据流

### 1. 数据生成流程

```text
应用代码 → API调用 → SDK处理 → 处理器 → 导出器 → 传输层 → 后端系统
```

### 2. 处理管道

```rust
// 数据流示例
let span = tracer.start("operation");
// 1. 生成遥测数据
span.set_attribute("key", "value");
span.end();

// 2. SDK处理
// 3. 批处理
// 4. 序列化
// 5. 传输
// 6. 后端存储
```

## 📊 采样策略

### 1. 概率采样

```rust
let sampler = ProbabilitySampler::new(0.1); // 10%采样率
```

### 2. 基于规则的采样

```rust
let sampler = RuleBasedSampler::new(vec![
    SamplingRule::new()
        .with_attribute("service.name", "critical-service")
        .with_sampling_rate(1.0),
    SamplingRule::new()
        .with_default_sampling_rate(0.01),
]);
```

### 3. 基于尾部的采样

```rust
let sampler = TailBasedSampler::new(TailBasedSamplerConfig {
    decision_wait: Duration::from_secs(10),
    num_traces: 10000,
    expected_new_traces_per_sec: 1000,
});
```

## 🔧 配置管理

### 1. 基础配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc)
    .with_timeout(Duration::from_secs(10));
```

### 2. 高级配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("https://api.honeycomb.io:443")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_api_key("your-api-key")
    .with_batch_config(BatchConfig {
        max_export_batch_size: 512,
        export_timeout: Duration::from_millis(5000),
        max_queue_size: 2048,
        scheduled_delay: Duration::from_millis(5000),
    })
    .with_retry_config(RetryConfig {
        max_retries: 5,
        initial_retry_delay: Duration::from_millis(1000),
        max_retry_delay: Duration::from_secs(30),
        retry_delay_multiplier: 2.0,
        randomize_retry_delay: true,
    });
```

## 🛡️ 错误处理

### 1. 错误类型

```rust
#[derive(Debug, thiserror::Error)]
pub enum OtlpError {
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("传输错误: {0}")]
    TransportError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
    
    #[error("导出错误: {0}")]
    ExportError(String),
}
```

### 2. 重试机制

```rust
let retry_config = RetryConfig {
    max_retries: 5,
    initial_retry_delay: Duration::from_millis(1000),
    max_retry_delay: Duration::from_secs(30),
    retry_delay_multiplier: 2.0,
    randomize_retry_delay: true,
};
```

## 📈 性能考虑

### 1. 批处理

```rust
let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_millis(5000),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(5000),
};
```

### 2. 压缩

```rust
let config = OtlpConfig::default()
    .with_compression(Compression::Gzip);
```

### 3. 异步处理

```rust
// 异步发送数据
let result = client.send_trace("operation").await?
    .with_attribute("key", "value")
    .finish()
    .await?;
```

## 🔍 调试和监控

### 1. 调试模式

```rust
let config = OtlpConfig::default()
    .with_debug(true);
```

### 2. 内置指标

```rust
let metrics = client.get_metrics().await;
println!("总发送数据量: {}", metrics.total_data_sent);
println!("平均延迟: {:?}", metrics.average_latency);
```

## 📚 最佳实践

### 1. 资源属性

```rust
// 设置全局资源属性
let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
    KeyValue::new("service.version", "1.0.0"),
    KeyValue::new("deployment.environment", "production"),
]);
```

### 2. 属性命名

```rust
// 使用语义约定的属性名
span.set_attribute("http.method", "GET");
span.set_attribute("db.system", "postgresql");
span.set_attribute("rpc.method", "GetUser");
```

### 3. 错误处理

```rust
// 适当的错误处理
match client.send_trace("operation").await {
    Ok(result) => println!("发送成功: {} 条", result.success_count),
    Err(e) => eprintln!("发送失败: {}", e),
}
```

## 🚀 下一步

### 深入学习

1. **[数学基础](数学基础/集合论应用.md)** - 了解理论基础
2. **[形式化验证](形式化验证/TLA+规范.md)** - 学习形式化方法
3. **[技术实现](../03_技术实现/Rust实现/核心架构.md)** - 深入了解实现细节

### 实践应用

1. **[快速开始指南](../00_总览与导航/快速开始指南.md)** - 动手实践
2. **[使用示例](../05_实践应用/使用示例/基础使用.md)** - 更多示例
3. **[集成指南](../05_实践应用/集成指南/Kubernetes集成.md)** - 系统集成

---

**基础概念文档版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP 2025 文档团队
