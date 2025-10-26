# OTLP API 参考

## 概述

本文档提供了 OTLP Rust 项目的完整 API 参考。API 设计遵循 Rust 生态系统的最佳实践，提供类型安全、高性能的接口。

## 核心 API

### EnhancedOtlpClient

主要的 OTLP 客户端接口，提供统一的遥测数据收集和传输功能。

```rust
pub struct EnhancedOtlpClient {
    // 内部实现细节
}

impl EnhancedOtlpClient {
    /// 创建客户端构建器
    pub fn builder() -> ClientBuilder;
    
    /// 获取追踪器
    pub fn tracer(&self, name: &str) -> Tracer;
    
    /// 导出追踪数据
    pub async fn export_traces(&self, traces: Vec<TraceData>) -> Result<()>;
    
    /// 导出指标数据
    pub async fn export_metrics(&self, metrics: Vec<MetricData>) -> Result<()>;
    
    /// 导出日志数据
    pub async fn export_logs(&self, logs: Vec<LogData>) -> Result<()>;
    
    /// 获取客户端统计信息
    pub fn stats(&self) -> ClientStats;
    
    /// 健康检查
    pub async fn health_check(&self) -> Result<HealthStatus>;
}
```

### ClientBuilder

客户端构建器，支持链式配置。

```rust
pub struct ClientBuilder {
    // 内部配置
}

impl ClientBuilder {
    /// 设置 OTLP 端点
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self;
    
    /// 设置服务名称
    pub fn with_service_name(mut self, name: impl Into<String>) -> Self;
    
    /// 设置服务版本
    pub fn with_service_version(mut self, version: impl Into<String>) -> Self;
    
    /// 设置连接超时
    pub fn with_connect_timeout(mut self, timeout: Duration) -> Self;
    
    /// 设置请求超时
    pub fn with_request_timeout(mut self, timeout: Duration) -> Self;
    
    /// 设置重试配置
    pub fn with_retry_config(mut self, config: RetryConfig) -> Self;
    
    /// 设置批处理配置
    pub fn with_batch_config(mut self, config: BatchConfig) -> Self;
    
    /// 设置压缩算法
    pub fn with_compression(mut self, compression: Compression) -> Self;
    
    /// 启用 gRPC 传输
    pub fn with_grpc_transport(mut self) -> Self;
    
    /// 启用 HTTP/JSON 传输
    pub fn with_http_transport(mut self) -> Self;
    
    /// 设置认证信息
    pub fn with_auth(mut self, auth: AuthConfig) -> Self;
    
    /// 构建客户端
    pub async fn build(self) -> Result<EnhancedOtlpClient>;
}
```

## 数据模型

### TraceData

追踪数据模型，表示分布式追踪中的一个 span。

```rust
pub struct TraceData {
    /// 追踪 ID
    pub trace_id: String,
    
    /// Span ID
    pub span_id: String,
    
    /// 父 Span ID（可选）
    pub parent_span_id: Option<String>,
    
    /// Span 名称
    pub name: String,
    
    /// Span 类型
    pub span_kind: SpanKind,
    
    /// 开始时间（纳秒）
    pub start_time: u64,
    
    /// 结束时间（纳秒）
    pub end_time: u64,
    
    /// Span 状态
    pub status: SpanStatus,
    
    /// 属性键值对
    pub attributes: HashMap<String, AttributeValue>,
    
    /// 事件列表
    pub events: Vec<Event>,
    
    /// 链接列表
    pub links: Vec<Link>,
}

pub enum SpanKind {
    /// 内部操作
    Internal,
    /// 服务器端操作
    Server,
    /// 客户端操作
    Client,
    /// 生产者操作
    Producer,
    /// 消费者操作
    Consumer,
}

pub struct SpanStatus {
    /// 状态码
    pub code: StatusCode,
    /// 状态消息
    pub message: Option<String>,
}

pub enum StatusCode {
    /// 未设置
    Unset,
    /// 成功
    Ok,
    /// 错误
    Error,
}
```

### MetricData

指标数据模型，表示一个指标及其数据点。

```rust
pub struct MetricData {
    /// 指标名称
    pub name: String,
    
    /// 指标描述
    pub description: String,
    
    /// 指标单位
    pub unit: String,
    
    /// 指标类型
    pub metric_type: MetricType,
    
    /// 数据点列表
    pub data_points: Vec<DataPoint>,
}

pub enum MetricType {
    /// 计数器
    Counter,
    /// 仪表
    Gauge,
    /// 直方图
    Histogram,
    /// 摘要
    Summary,
}

pub struct DataPoint {
    /// 时间戳（纳秒）
    pub timestamp: u64,
    
    /// 数据值
    pub value: DataPointValue,
    
    /// 属性键值对
    pub attributes: HashMap<String, AttributeValue>,
}

pub enum DataPointValue {
    /// 整数值
    Int64(i64),
    /// 浮点值
    Double(f64),
    /// 直方图值
    Histogram(HistogramData),
    /// 摘要值
    Summary(SummaryData),
}
```

### LogData

日志数据模型，表示一条结构化日志。

```rust
pub struct LogData {
    /// 时间戳（纳秒）
    pub timestamp: u64,
    
    /// 日志级别
    pub severity: LogSeverity,
    
    /// 日志正文
    pub body: String,
    
    /// 属性键值对
    pub attributes: HashMap<String, AttributeValue>,
    
    /// 资源信息
    pub resource: Option<Resource>,
}

pub enum LogSeverity {
    /// 未设置
    Unset,
    /// 跟踪
    Trace,
    /// 调试
    Debug,
    /// 信息
    Info,
    /// 警告
    Warn,
    /// 错误
    Error,
    /// 致命
    Fatal,
}
```

### AttributeValue

属性值类型，支持多种数据类型。

```rust
pub enum AttributeValue {
    /// 布尔值
    Bool(bool),
    /// 整数值
    Int64(i64),
    /// 浮点值
    Double(f64),
    /// 字符串值
    String(String),
    /// 布尔数组
    BoolArray(Vec<bool>),
    /// 整数数组
    Int64Array(Vec<i64>),
    /// 浮点数组
    DoubleArray(Vec<f64>),
    /// 字符串数组
    StringArray(Vec<String>),
}
```

## 配置类型

### OtlpConfig

OTLP 客户端配置。

```rust
pub struct OtlpConfig {
    /// OTLP 端点
    pub endpoint: String,
    
    /// 传输协议
    pub protocol: TransportProtocol,
    
    /// 连接超时
    pub connect_timeout: Duration,
    
    /// 请求超时
    pub request_timeout: Duration,
    
    /// 重试配置
    pub retry_config: RetryConfig,
    
    /// 批处理配置
    pub batch_config: BatchConfig,
    
    /// 压缩设置
    pub compression: Compression,
    
    /// 认证配置
    pub auth: Option<AuthConfig>,
}

pub enum TransportProtocol {
    /// gRPC 协议
    Grpc,
    /// HTTP/JSON 协议
    HttpJson,
}
```

### RetryConfig

重试配置。

```rust
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    
    /// 初始重试间隔
    pub initial_interval: Duration,
    
    /// 最大重试间隔
    pub max_interval: Duration,
    
    /// 重试间隔乘数
    pub multiplier: f64,
    
    /// 随机化因子
    pub randomization_factor: f64,
    
    /// 可重试的错误类型
    pub retryable_errors: Vec<ErrorType>,
}
```

### BatchConfig

批处理配置。

```rust
pub struct BatchConfig {
    /// 最大批处理大小
    pub max_batch_size: usize,
    
    /// 批处理超时
    pub batch_timeout: Duration,
    
    /// 最大队列大小
    pub max_queue_size: usize,
    
    /// 批处理策略
    pub strategy: BatchStrategy,
}

pub enum BatchStrategy {
    /// 基于大小
    SizeBased,
    /// 基于时间
    TimeBased,
    /// 混合策略
    Hybrid,
}
```

### Compression

压缩配置。

```rust
pub enum Compression {
    /// 无压缩
    None,
    /// gzip 压缩
    Gzip,
    /// brotli 压缩
    Brotli,
    /// zstd 压缩
    Zstd,
}
```

## 错误类型

### OtlpError

OTLP 相关错误类型。

```rust
#[derive(Debug, thiserror::Error)]
pub enum OtlpError {
    /// 网络错误
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    /// 序列化错误
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    /// 配置错误
    #[error("Configuration error: {0}")]
    Configuration(String),
    
    /// 验证错误
    #[error("Validation error: {0}")]
    Validation(String),
    
    /// 超时错误
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    /// 认证错误
    #[error("Authentication error: {0}")]
    Authentication(String),
    
    /// 授权错误
    #[error("Authorization error: {0}")]
    Authorization(String),
    
    /// 批处理错误
    #[error("Batch processing error: {0}")]
    BatchProcessing(String),
    
    /// 传输错误
    #[error("Transport error: {0}")]
    Transport(String),
}
```

## 监控和统计

### ClientStats

客户端统计信息。

```rust
pub struct ClientStats {
    /// 发送的追踪数量
    pub traces_sent: u64,
    
    /// 发送的指标数量
    pub metrics_sent: u64,
    
    /// 发送的日志数量
    pub logs_sent: u64,
    
    /// 发送失败的数量
    pub send_failures: u64,
    
    /// 平均响应时间
    pub avg_response_time: Duration,
    
    /// 当前连接数
    pub active_connections: u32,
    
    /// 队列大小
    pub queue_size: usize,
    
    /// 最后更新时间
    pub last_updated: SystemTime,
}
```

### HealthStatus

健康状态。

```rust
pub struct HealthStatus {
    /// 整体健康状态
    pub status: HealthState,
    
    /// 检查项目列表
    pub checks: Vec<HealthCheck>,
    
    /// 最后检查时间
    pub last_check: SystemTime,
}

pub enum HealthState {
    /// 健康
    Healthy,
    /// 不健康
    Unhealthy,
    /// 未知
    Unknown,
}

pub struct HealthCheck {
    /// 检查名称
    pub name: String,
    
    /// 检查状态
    pub status: HealthState,
    
    /// 检查消息
    pub message: Option<String>,
    
    /// 检查持续时间
    pub duration: Duration,
}
```

## 使用示例

### 基本使用

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .with_service_version("1.0.0")
        .with_http_transport()
        .build()
        .await?;
    
    // 创建追踪器
    let tracer = client.tracer("my-component");
    let span = tracer.start("my-operation");
    
    // 添加属性
    span.set_attribute("user.id", "12345");
    span.set_attribute("operation.type", "database");
    
    // 执行业务逻辑
    // ...
    
    // 结束 span
    drop(span);
    
    Ok(())
}
```

### 高级配置

```rust
use otlp::{core::EnhancedOtlpClient, config::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置重试策略
    let retry_config = RetryConfig {
        max_attempts: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
    };
    
    // 配置批处理
    let batch_config = BatchConfig {
        max_batch_size: 1000,
        batch_timeout: Duration::from_secs(5),
        max_queue_size: 10000,
        strategy: BatchStrategy::Hybrid,
    };
    
    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .with_retry_config(retry_config)
        .with_batch_config(batch_config)
        .with_compression(Compression::Gzip)
        .with_grpc_transport()
        .build()
        .await?;
    
    // 获取统计信息
    let stats = client.stats();
    println!("Client stats: {:?}", stats);
    
    // 健康检查
    let health = client.health_check().await?;
    println!("Health status: {:?}", health);
    
    Ok(())
}
```

### 批量导出

```rust
use otlp::{core::EnhancedOtlpClient, data::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 创建追踪数据
    let traces = vec![
        TraceData {
            trace_id: "trace-1".to_string(),
            span_id: "span-1".to_string(),
            parent_span_id: None,
            name: "operation-1".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 0,
            end_time: 1000000,
            status: SpanStatus {
                code: StatusCode::Ok,
                message: None,
            },
            attributes: HashMap::new(),
            events: vec![],
            links: vec![],
        },
    ];
    
    // 批量导出
    client.export_traces(traces).await?;
    
    Ok(())
}
```

## 性能优化

### 连接池配置

```rust
use otlp::core::EnhancedOtlpClient;

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_connect_timeout(Duration::from_secs(5))
    .with_request_timeout(Duration::from_secs(30))
    .build()
    .await?;
```

### 批处理优化

```rust
use otlp::{core::EnhancedOtlpClient, config::BatchConfig};

let batch_config = BatchConfig {
    max_batch_size: 1000,        // 最大批处理大小
    batch_timeout: Duration::from_secs(5),  // 批处理超时
    max_queue_size: 10000,      // 最大队列大小
    strategy: BatchStrategy::Hybrid,  // 混合策略
};

let client = EnhancedOtlpClient::builder()
    .with_batch_config(batch_config)
    .build()
    .await?;
```

### 压缩优化

```rust
use otlp::{core::EnhancedOtlpClient, config::Compression};

let client = EnhancedOtlpClient::builder()
    .with_compression(Compression::Gzip)  // 使用 gzip 压缩
    .build()
    .await?;
```

---

*本文档最后更新: 2025年10月20日*-
