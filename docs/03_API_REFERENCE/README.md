# 🔧 API 参考文档

本文档提供了 OTLP Rust 库的完整 API 参考，包括所有公共接口、数据类型、配置选项和错误处理机制。

## 📋 目录

- [🔧 API 参考文档](#-api-参考文档)
  - [📋 目录](#-目录)
  - [🚀 客户端 API](#-客户端-api)
    - [OtlpClient](#otlpclient)
      - [构造函数](#构造函数)
      - [生命周期管理](#生命周期管理)
      - [数据发送方法](#数据发送方法)
      - [配置管理](#配置管理)
    - [TraceBuilder](#tracebuilder)
  - [⚙️ 配置选项](#️-配置选项)
    - [OtlpConfig](#otlpconfig)
      - [配置构建器方法](#配置构建器方法)
    - [传输协议](#传输协议)
    - [压缩算法](#压缩算法)
    - [重试配置](#重试配置)
    - [批处理配置](#批处理配置)
  - [📊 数据类型](#-数据类型)
    - [TelemetryData](#telemetrydata)
      - [构建方法](#构建方法)
    - [属性值类型](#属性值类型)
    - [指标值类型](#指标值类型)
    - [日志严重程度](#日志严重程度)
    - [状态码](#状态码)
  - [❌ 错误处理](#-错误处理)
    - [OtlpError](#otlperror)
    - [结果类型](#结果类型)
  - [📝 示例代码](#-示例代码)
    - [基本使用](#基本使用)
    - [高级配置](#高级配置)
    - [错误处理](#错误处理)
  - [🔗 相关文档](#-相关文档)

## 🚀 客户端 API

### OtlpClient

主要的 OTLP 客户端接口，提供发送遥测数据的功能。

#### 构造函数

```rust
impl OtlpClient {
    /// 创建新的 OTLP 客户端
    pub async fn new(config: OtlpConfig) -> Result<Self, OtlpError>
    
    /// 从环境变量创建客户端
    pub async fn from_env() -> Result<Self, OtlpError>
    
    /// 使用默认配置创建客户端
    pub async fn default() -> Result<Self, OtlpError>
}
```

#### 生命周期管理

```rust
impl OtlpClient {
    /// 初始化客户端
    pub async fn initialize(&self) -> Result<(), OtlpError>
    
    /// 关闭客户端
    pub async fn shutdown(&self) -> Result<(), OtlpError>
    
    /// 检查客户端状态
    pub fn is_healthy(&self) -> bool
}
```

#### 数据发送方法

```rust
impl OtlpClient {
    /// 发送单个追踪数据
    pub async fn send_trace(&self, operation: &str) -> Result<TraceBuilder, OtlpError>
    
    /// 发送单个指标数据
    pub async fn send_metric(&self, data: TelemetryData) -> Result<SendResult, OtlpError>
    
    /// 发送单个日志数据
    pub async fn send_log(&self, data: TelemetryData) -> Result<SendResult, OtlpError>
    
    /// 批量发送数据
    pub async fn send_batch(&self, data: Vec<TelemetryData>) -> Result<BatchResult, OtlpError>
    
    /// 发送原始 OTLP 数据
    pub async fn send_raw(&self, data: OtlpData) -> Result<SendResult, OtlpError>
}
```

#### 配置管理

```rust
impl OtlpClient {
    /// 更新客户端配置
    pub async fn update_config(&self, config: OtlpConfig) -> Result<(), OtlpError>
    
    /// 获取当前配置
    pub fn get_config(&self) -> &OtlpConfig
    
    /// 设置审计钩子
    pub async fn set_audit_hook(&self, hook: Arc<dyn AuditHook>) -> Result<(), OtlpError>
}
```

### TraceBuilder

用于构建和发送追踪数据的构建器模式。

```rust
impl TraceBuilder {
    /// 添加字符串属性
    pub fn with_attribute(mut self, key: &str, value: &str) -> Self
    
    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: &str, value: f64) -> Self
    
    /// 添加布尔属性
    pub fn with_bool_attribute(mut self, key: &str, value: bool) -> Self
    
    /// 设置状态码
    pub fn with_status(mut self, code: StatusCode, message: Option<String>) -> Self
    
    /// 设置开始时间
    pub fn with_start_time(mut self, time: SystemTime) -> Self
    
    /// 设置持续时间
    pub fn with_duration(mut self, duration: Duration) -> Self
    
    /// 完成并发送追踪数据
    pub async fn finish(self) -> Result<SendResult, OtlpError>
}
```

## ⚙️ 配置选项

### OtlpConfig

主要的配置结构，用于配置 OTLP 客户端的行为。

```rust
#[derive(Debug, Clone)]
pub struct OtlpConfig {
    pub endpoint: String,
    pub protocol: TransportProtocol,
    pub compression: Option<Compression>,
    pub timeout: Duration,
    pub retry_config: RetryConfig,
    pub batch_config: BatchConfig,
    pub auth_config: Option<AuthConfig>,
    pub tls_config: Option<TlsConfig>,
    pub resource_attributes: HashMap<String, String>,
    pub instrumentation_scope: Option<InstrumentationScope>,
}
```

#### 配置构建器方法

```rust
impl OtlpConfig {
    /// 创建默认配置
    pub fn default() -> Self
    
    /// 设置端点 URL
    pub fn with_endpoint(mut self, endpoint: &str) -> Self
    
    /// 设置传输协议
    pub fn with_protocol(mut self, protocol: TransportProtocol) -> Self
    
    /// 设置压缩算法
    pub fn with_compression(mut self, compression: Compression) -> Self
    
    /// 设置超时时间
    pub fn with_timeout(mut self, timeout: Duration) -> Self
    
    /// 设置重试配置
    pub fn with_retry_config(mut self, config: RetryConfig) -> Self
    
    /// 设置批处理配置
    pub fn with_batch_config(mut self, config: BatchConfig) -> Self
    
    /// 设置认证配置
    pub fn with_auth_config(mut self, config: AuthConfig) -> Self
    
    /// 设置 TLS 配置
    pub fn with_tls_config(mut self, config: TlsConfig) -> Self
    
    /// 添加资源属性
    pub fn with_resource_attribute(mut self, key: &str, value: &str) -> Self
    
    /// 设置仪器化范围
    pub fn with_instrumentation_scope(mut self, scope: InstrumentationScope) -> Self
    
    /// 验证配置
    pub fn validate(&self) -> Result<(), ConfigError>
}
```

### 传输协议

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum TransportProtocol {
    /// gRPC 传输协议
    Grpc,
    /// HTTP/JSON 传输协议
    HttpJson,
    /// HTTP/Protobuf 传输协议
    HttpProtobuf,
}
```

### 压缩算法

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Compression {
    /// Gzip 压缩
    Gzip,
    /// Brotli 压缩
    Brotli,
    /// Zstd 压缩
    Zstd,
    /// LZ4 压缩
    Lz4,
    /// Snappy 压缩
    Snappy,
}
```

### 重试配置

```rust
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_retries: u32,
    /// 初始重试延迟
    pub initial_retry_delay: Duration,
    /// 最大重试延迟
    pub max_retry_delay: Duration,
    /// 重试延迟倍数
    pub retry_delay_multiplier: f64,
    /// 是否随机化重试延迟
    pub randomize_retry_delay: bool,
}
```

### 批处理配置

```rust
#[derive(Debug, Clone)]
pub struct BatchConfig {
    /// 最大导出批处理大小
    pub max_export_batch_size: usize,
    /// 导出超时时间
    pub export_timeout: Duration,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 调度延迟
    pub scheduled_delay: Duration,
}
```

## 📊 数据类型

### TelemetryData

统一的遥测数据类型，支持追踪、指标和日志数据。

```rust
#[derive(Debug, Clone)]
pub enum TelemetryData {
    /// 追踪数据
    Trace {
        operation: String,
        attributes: HashMap<String, AttributeValue>,
        status: Option<SpanStatus>,
        start_time: Option<SystemTime>,
        duration: Option<Duration>,
    },
    /// 指标数据
    Metric {
        name: String,
        value: MetricValue,
        attributes: HashMap<String, AttributeValue>,
        timestamp: Option<SystemTime>,
    },
    /// 日志数据
    Log {
        message: String,
        severity: LogSeverity,
        attributes: HashMap<String, AttributeValue>,
        timestamp: Option<SystemTime>,
    },
}
```

#### 构建方法

```rust
impl TelemetryData {
    /// 创建追踪数据
    pub fn trace(operation: &str) -> Self
    
    /// 创建指标数据
    pub fn metric(name: &str, value: MetricValue) -> Self
    
    /// 创建日志数据
    pub fn log(message: &str, severity: LogSeverity) -> Self
    
    /// 添加属性
    pub fn with_attribute(mut self, key: &str, value: AttributeValue) -> Self
    
    /// 设置时间戳
    pub fn with_timestamp(mut self, timestamp: SystemTime) -> Self
}
```

### 属性值类型

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    /// 字符串值
    String(String),
    /// 整数值
    Int(i64),
    /// 浮点数值
    Double(f64),
    /// 布尔值
    Bool(bool),
    /// 字符串数组
    StringArray(Vec<String>),
    /// 整数数组
    IntArray(Vec<i64>),
    /// 浮点数数组
    DoubleArray(Vec<f64>),
    /// 布尔数组
    BoolArray(Vec<bool>),
}
```

### 指标值类型

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum MetricValue {
    /// 计数器值
    Counter(f64),
    /// 仪表值
    Gauge(f64),
    /// 直方图值
    Histogram {
        sum: f64,
        count: u64,
        buckets: Vec<HistogramBucket>,
    },
    /// 摘要值
    Summary {
        sum: f64,
        count: u64,
        quantiles: Vec<SummaryQuantile>,
    },
}
```

### 日志严重程度

```rust
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LogSeverity {
    /// 未指定
    Unspecified,
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

### 状态码

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum StatusCode {
    /// 未设置
    Unset,
    /// 成功
    Ok,
    /// 错误
    Error,
}
```

## ❌ 错误处理

### OtlpError

主要的错误类型，包含所有可能的 OTLP 相关错误。

```rust
#[derive(Debug, thiserror::Error)]
pub enum OtlpError {
    /// 网络错误
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    /// gRPC 错误
    #[error("gRPC error: {0}")]
    Grpc(#[from] tonic::Status),
    
    /// 序列化错误
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    /// 配置错误
    #[error("Configuration error: {0}")]
    Config(#[from] ConfigError),
    
    /// 认证错误
    #[error("Authentication error: {0}")]
    Auth(String),
    
    /// 超时错误
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    /// 批处理错误
    #[error("Batch processing error: {0}")]
    Batch(String),
    
    /// 自定义错误
    #[error("Custom error: {0}")]
    Custom(String),
}
```

### 结果类型

```rust
/// 发送结果
#[derive(Debug, Clone)]
pub struct SendResult {
    /// 成功发送的数据条数
    pub success_count: u64,
    /// 失败的数据条数
    pub failure_count: u64,
    /// 错误信息
    pub errors: Vec<String>,
}

/// 批处理结果
#[derive(Debug, Clone)]
pub struct BatchResult {
    /// 总处理的数据条数
    pub total_count: u64,
    /// 成功处理的数据条数
    pub success_count: u64,
    /// 失败处理的数据条数
    pub failure_count: u64,
    /// 处理时间
    pub processing_time: Duration,
    /// 错误信息
    pub errors: Vec<String>,
}
```

## 📝 示例代码

### 基本使用

```rust
use otlp::{OtlpClient, OtlpConfig, TelemetryData};
use otlp::config::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_timeout(Duration::from_secs(10));
    
    // 创建客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("service.version", "1.0.0")
        .finish()
        .await?;
    
    println!("发送结果: {:?}", result);
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

### 高级配置

```rust
use otlp::config::{Compression, BatchConfig, RetryConfig};

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_millis(5000),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(5000),
};

let retry_config = RetryConfig {
    max_retries: 5,
    initial_retry_delay: Duration::from_millis(1000),
    max_retry_delay: Duration::from_secs(30),
    retry_delay_multiplier: 2.0,
    randomize_retry_delay: true,
};

let config = OtlpConfig::default()
    .with_endpoint("https://api.example.com/otlp")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_batch_config(batch_config)
    .with_retry_config(retry_config);
```

### 错误处理

```rust
use otlp::OtlpError;

match client.send_trace("operation").await {
    Ok(trace_builder) => {
        match trace_builder.finish().await {
            Ok(result) => println!("发送成功: {:?}", result),
            Err(OtlpError::Network(e)) => eprintln!("网络错误: {}", e),
            Err(OtlpError::Timeout(e)) => eprintln!("超时错误: {}", e),
            Err(e) => eprintln!("其他错误: {}", e),
        }
    }
    Err(OtlpError::Config(e)) => eprintln!("配置错误: {}", e),
    Err(e) => eprintln!("客户端错误: {}", e),
}
```

## 🔗 相关文档

- [快速开始指南](../01_GETTING_STARTED/README.md)
- [架构设计文档](../04_ARCHITECTURE/README.md)
- [实现指南](../05_IMPLEMENTATION/README.md)
- [部署运维指南](../06_DEPLOYMENT/README.md)

---

**API 版本**: 0.1.0  
**最后更新**: 2025年1月  
**维护者**: OTLP Rust 团队
