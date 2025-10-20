# OTLP Rust 核心API文档

## 目录

- [OTLP Rust 核心API文档](#otlp-rust-核心api文档)
  - [目录](#目录)
  - [📚 概述](#-概述)
  - [🏗️ 核心组件](#️-核心组件)
    - [OtlpClient](#otlpclient)
      - [主要方法](#主要方法)
        - [`new(config: OtlpConfig) -> Result<Self, OtlpError>`](#newconfig-otlpconfig---resultself-otlperror)
        - [`initialize() -> Result<(), OtlpError>`](#initialize---result-otlperror)
        - [`send_trace(operation: &str) -> Result<TraceBuilder, OtlpError>`](#send_traceoperation-str---resulttracebuilder-otlperror)
        - [`send_metric(name: &str, value: f64) -> Result<MetricBuilder, OtlpError>`](#send_metricname-str-value-f64---resultmetricbuilder-otlperror)
        - [`send_log(message: &str, severity: LogSeverity) -> Result<LogBuilder, OtlpError>`](#send_logmessage-str-severity-logseverity---resultlogbuilder-otlperror)
        - [`send_batch(data: Vec<TelemetryData>) -> Result<ExportResult, OtlpError>`](#send_batchdata-vectelemetrydata---resultexportresult-otlperror)
        - [`get_metrics() -> ClientMetrics`](#get_metrics---clientmetrics)
        - [`shutdown() -> Result<(), OtlpError>`](#shutdown---result-otlperror)
  - [⚙️ 配置管理](#️-配置管理)
    - [OtlpConfig](#otlpconfig)
      - [主要方法1](#主要方法1)
        - [`default() -> Self`](#default---self)
        - [`with_endpoint(endpoint: &str) -> Self`](#with_endpointendpoint-str---self)
        - [`with_protocol(protocol: TransportProtocol) -> Self`](#with_protocolprotocol-transportprotocol---self)
        - [`with_service(name: &str, version: &str) -> Self`](#with_servicename-str-version-str---self)
        - [`with_timeout(timeout: Duration) -> Self`](#with_timeouttimeout-duration---self)
        - [`with_compression(compression: Compression) -> Self`](#with_compressioncompression-compression---self)
        - [`with_sampling_ratio(ratio: f64) -> Self`](#with_sampling_ratioratio-f64---self)
        - [`with_api_key(key: &str) -> Self`](#with_api_keykey-str---self)
        - [`with_bearer_token(token: &str) -> Self`](#with_bearer_tokentoken-str---self)
        - [`with_tls(enabled: bool) -> Self`](#with_tlsenabled-bool---self)
        - [`with_debug(enabled: bool) -> Self`](#with_debugenabled-bool---self)
        - [`with_batch_config(config: BatchConfig) -> Self`](#with_batch_configconfig-batchconfig---self)
        - [`with_retry_config(config: RetryConfig) -> Self`](#with_retry_configconfig-retryconfig---self)
        - [`with_resource_attribute(key: &str, value: &str) -> Self`](#with_resource_attributekey-str-value-str---self)
  - [📊 数据构建器](#-数据构建器)
    - [TraceBuilder](#tracebuilder)
      - [主要方法2](#主要方法2)
        - [`with_attribute(key: &str, value: &str) -> Self`](#with_attributekey-str-value-str---self)
        - [`with_numeric_attribute(key: &str, value: f64) -> Self`](#with_numeric_attributekey-str-value-f64---self)
        - [`with_boolean_attribute(key: &str, value: bool) -> Self`](#with_boolean_attributekey-str-value-bool---self)
        - [`with_status(status: StatusCode, message: Option<String>) -> Self`](#with_statusstatus-statuscode-message-optionstring---self)
        - [`with_event(name: &str, attributes: Vec<KeyValue>) -> Self`](#with_eventname-str-attributes-veckeyvalue---self)
        - [`with_link(trace_id: &str, span_id: &str, attributes: Vec<KeyValue>) -> Self`](#with_linktrace_id-str-span_id-str-attributes-veckeyvalue---self)
        - [`finish() -> Result<ExportResult, OtlpError>`](#finish---resultexportresult-otlperror)
    - [MetricBuilder](#metricbuilder)
      - [主要方法3](#主要方法3)
        - [`with_label(key: &str, value: &str) -> Self`](#with_labelkey-str-value-str---self)
        - [`with_description(description: &str) -> Self`](#with_descriptiondescription-str---self)
        - [`with_unit(unit: &str) -> Self`](#with_unitunit-str---self)
        - [`with_timestamp(timestamp: SystemTime) -> Self`](#with_timestamptimestamp-systemtime---self)
        - [`send() -> Result<ExportResult, OtlpError>`](#send---resultexportresult-otlperror)
    - [LogBuilder](#logbuilder)
      - [主要方法4](#主要方法4)
        - [`with_attribute(key: &str, value: &str) -> Self`1](#with_attributekey-str-value-str---self1)
        - [`with_numeric_attribute(key: &str, value: f64) -> Self`2](#with_numeric_attributekey-str-value-f64---self2)
        - [`with_trace_context(trace_id: &str, span_id: &str) -> Self`](#with_trace_contexttrace_id-str-span_id-str---self)
        - [`with_timestamp(timestamp: SystemTime) -> Self`3](#with_timestamptimestamp-systemtime---self3)
        - [`send() -> Result<ExportResult, OtlpError>`2](#send---resultexportresult-otlperror2)
  - [🔧 配置结构](#-配置结构)
    - [BatchConfig](#batchconfig)
      - [字段说明](#字段说明)
    - [RetryConfig](#retryconfig)
      - [字段说明1](#字段说明1)
  - [📊 数据类型](#-数据类型)
    - [TelemetryData](#telemetrydata)
      - [变体](#变体)
    - [KeyValue](#keyvalue)
      - [主要方法5](#主要方法5)
        - [`new(key: &str, value: impl Into<AttributeValue>) -> Self`](#newkey-str-value-impl-intoattributevalue---self)
    - [AttributeValue](#attributevalue)
      - [变体1](#变体1)
    - [LogSeverity](#logseverity)
      - [变体2](#变体2)
    - [StatusCode](#statuscode)
      - [变体3](#变体3)
  - [🚀 传输协议](#-传输协议)
    - [TransportProtocol](#transportprotocol)
      - [变体4](#变体4)
    - [Compression](#compression)
      - [变体5](#变体5)
  - [📈 结果类型](#-结果类型)
    - [ExportResult](#exportresult)
      - [字段说明2](#字段说明2)
    - [ClientMetrics](#clientmetrics)
      - [字段说明3](#字段说明3)
  - [❌ 错误处理](#-错误处理)
    - [OtlpError](#otlperror)
      - [错误类型](#错误类型)
  - [🎯 使用示例](#-使用示例)
    - [基础使用](#基础使用)
    - [高级使用](#高级使用)
  - [📚 总结](#-总结)

## 📚 概述

本文档详细介绍了OTLP Rust实现的核心API，包括客户端、配置、数据模型、传输层等主要组件的使用方法。

## 🏗️ 核心组件

### OtlpClient

OTLP客户端是主要的接口，用于发送遥测数据。

```rust
use c21_otlp::{OtlpClient, OtlpConfig};

// 创建客户端
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_service("my-service", "1.0.0");

let client = OtlpClient::new(config).await?;
client.initialize().await?;

// 使用客户端发送数据
let result = client.send_trace("operation").await?
    .with_attribute("key", "value")
    .finish()
    .await?;

// 关闭客户端
client.shutdown().await?;
```

#### 主要方法

##### `new(config: OtlpConfig) -> Result<Self, OtlpError>`

创建新的OTLP客户端实例。

**参数**:

- `config`: 客户端配置

**返回值**:

- `Result<Self, OtlpError>`: 客户端实例或错误

**示例**:

```rust
let client = OtlpClient::new(config).await?;
```

##### `initialize() -> Result<(), OtlpError>`

初始化客户端，建立连接和启动内部服务。

**返回值**:

- `Result<(), OtlpError>`: 初始化结果

**示例**:

```rust
client.initialize().await?;
```

##### `send_trace(operation: &str) -> Result<TraceBuilder, OtlpError>`

发送追踪数据。

**参数**:

- `operation`: 操作名称

**返回值**:

- `Result<TraceBuilder, OtlpError>`: 追踪构建器

**示例**:

```rust
let builder = client.send_trace("user-login").await?;
let result = builder
    .with_attribute("user.id", "12345")
    .finish()
    .await?;
```

##### `send_metric(name: &str, value: f64) -> Result<MetricBuilder, OtlpError>`

发送指标数据。

**参数**:

- `name`: 指标名称
- `value`: 指标值

**返回值**:

- `Result<MetricBuilder, OtlpError>`: 指标构建器

**示例**:

```rust
let builder = client.send_metric("request_count", 1.0).await?;
let result = builder
    .with_label("method", "GET")
    .send()
    .await?;
```

##### `send_log(message: &str, severity: LogSeverity) -> Result<LogBuilder, OtlpError>`

发送日志数据。

**参数**:

- `message`: 日志消息
- `severity`: 日志级别

**返回值**:

- `Result<LogBuilder, OtlpError>`: 日志构建器

**示例**:

```rust
let builder = client.send_log("User login successful", LogSeverity::Info).await?;
let result = builder
    .with_attribute("user.id", "12345")
    .send()
    .await?;
```

##### `send_batch(data: Vec<TelemetryData>) -> Result<ExportResult, OtlpError>`

批量发送遥测数据。

**参数**:

- `data`: 遥测数据向量

**返回值**:

- `Result<ExportResult, OtlpError>`: 导出结果

**示例**:

```rust
let mut batch_data = Vec::new();
for i in 0..10 {
    batch_data.push(TelemetryData::trace(format!("operation-{}", i)));
}
let result = client.send_batch(batch_data).await?;
```

##### `get_metrics() -> ClientMetrics`

获取客户端性能指标。

**返回值**:

- `ClientMetrics`: 客户端指标

**示例**:

```rust
let metrics = client.get_metrics().await;
println!("Total sent: {}", metrics.total_data_sent);
```

##### `shutdown() -> Result<(), OtlpError>`

关闭客户端，清理资源。

**返回值**:

- `Result<(), OtlpError>`: 关闭结果

**示例**:

```rust
client.shutdown().await?;
```

## ⚙️ 配置管理

### OtlpConfig

OTLP客户端配置类。

```rust
use c21_otlp::{OtlpConfig, TransportProtocol, Compression};
use std::time::Duration;

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc)
    .with_service("my-service", "1.0.0")
    .with_timeout(Duration::from_secs(10));
```

#### 主要方法1

##### `default() -> Self`

创建默认配置。

**返回值**:

- `Self`: 默认配置实例

##### `with_endpoint(endpoint: &str) -> Self`

设置服务端点。

**参数**:

- `endpoint`: 服务端点URL

**返回值**:

- `Self`: 配置实例

##### `with_protocol(protocol: TransportProtocol) -> Self`

设置传输协议。

**参数**:

- `protocol`: 传输协议

**返回值**:

- `Self`: 配置实例

##### `with_service(name: &str, version: &str) -> Self`

设置服务信息。

**参数**:

- `name`: 服务名称
- `version`: 服务版本

**返回值**:

- `Self`: 配置实例

##### `with_timeout(timeout: Duration) -> Self`

设置请求超时时间。

**参数**:

- `timeout`: 超时时间

**返回值**:

- `Self`: 配置实例

##### `with_compression(compression: Compression) -> Self`

设置压缩算法。

**参数**:

- `compression`: 压缩算法

**返回值**:

- `Self`: 配置实例

##### `with_sampling_ratio(ratio: f64) -> Self`

设置采样率。

**参数**:

- `ratio`: 采样率 (0.0-1.0)

**返回值**:

- `Self`: 配置实例

##### `with_api_key(key: &str) -> Self`

设置API密钥。

**参数**:

- `key`: API密钥

**返回值**:

- `Self`: 配置实例

##### `with_bearer_token(token: &str) -> Self`

设置Bearer令牌。

**参数**:

- `token`: Bearer令牌

**返回值**:

- `Self`: 配置实例

##### `with_tls(enabled: bool) -> Self`

启用或禁用TLS。

**参数**:

- `enabled`: 是否启用TLS

**返回值**:

- `Self`: 配置实例

##### `with_debug(enabled: bool) -> Self`

启用或禁用调试模式。

**参数**:

- `enabled`: 是否启用调试模式

**返回值**:

- `Self`: 配置实例

##### `with_batch_config(config: BatchConfig) -> Self`

设置批处理配置。

**参数**:

- `config`: 批处理配置

**返回值**:

- `Self`: 配置实例

##### `with_retry_config(config: RetryConfig) -> Self`

设置重试配置。

**参数**:

- `config`: 重试配置

**返回值**:

- `Self`: 配置实例

##### `with_resource_attribute(key: &str, value: &str) -> Self`

添加资源属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 配置实例

## 📊 数据构建器

### TraceBuilder

追踪数据构建器，用于构建和发送追踪数据。

```rust
let builder = client.send_trace("operation").await?;
let result = builder
    .with_attribute("key", "value")
    .with_numeric_attribute("duration", 150.0)
    .with_status(StatusCode::Ok, Some("Success".to_string()))
    .finish()
    .await?;
```

#### 主要方法2

##### `with_attribute(key: &str, value: &str) -> Self`

添加字符串属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 构建器实例

##### `with_numeric_attribute(key: &str, value: f64) -> Self`

添加数值属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 构建器实例

##### `with_boolean_attribute(key: &str, value: bool) -> Self`

添加布尔属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 构建器实例

##### `with_status(status: StatusCode, message: Option<String>) -> Self`

设置追踪状态。

**参数**:

- `status`: 状态码
- `message`: 状态消息

**返回值**:

- `Self`: 构建器实例

##### `with_event(name: &str, attributes: Vec<KeyValue>) -> Self`

添加事件。

**参数**:

- `name`: 事件名称
- `attributes`: 事件属性

**返回值**:

- `Self`: 构建器实例

##### `with_link(trace_id: &str, span_id: &str, attributes: Vec<KeyValue>) -> Self`

添加链接。

**参数**:

- `trace_id`: 追踪ID
- `span_id`: 跨度ID
- `attributes`: 链接属性

**返回值**:

- `Self`: 构建器实例

##### `finish() -> Result<ExportResult, OtlpError>`

完成追踪构建并发送。

**返回值**:

- `Result<ExportResult, OtlpError>`: 导出结果

### MetricBuilder

指标数据构建器，用于构建和发送指标数据。

```rust
let builder = client.send_metric("request_count", 1.0).await?;
let result = builder
    .with_label("method", "GET")
    .with_description("HTTP request count")
    .with_unit("count")
    .send()
    .await?;
```

#### 主要方法3

##### `with_label(key: &str, value: &str) -> Self`

添加标签。

**参数**:

- `key`: 标签键
- `value`: 标签值

**返回值**:

- `Self`: 构建器实例

##### `with_description(description: &str) -> Self`

设置指标描述。

**参数**:

- `description`: 描述文本

**返回值**:

- `Self`: 构建器实例

##### `with_unit(unit: &str) -> Self`

设置指标单位。

**参数**:

- `unit`: 单位

**返回值**:

- `Self`: 构建器实例

##### `with_timestamp(timestamp: SystemTime) -> Self`

设置时间戳。

**参数**:

- `timestamp`: 时间戳

**返回值**:

- `Self`: 构建器实例

##### `send() -> Result<ExportResult, OtlpError>`

发送指标数据。

**返回值**:

- `Result<ExportResult, OtlpError>`: 导出结果

### LogBuilder

日志数据构建器，用于构建和发送日志数据。

```rust
let builder = client.send_log("User login", LogSeverity::Info).await?;
let result = builder
    .with_attribute("user.id", "12345")
    .with_trace_context("trace-123", "span-456")
    .send()
    .await?;
```

#### 主要方法4

##### `with_attribute(key: &str, value: &str) -> Self`1

添加属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 构建器实例

##### `with_numeric_attribute(key: &str, value: f64) -> Self`2

添加数值属性。

**参数**:

- `key`: 属性键
- `value`: 属性值

**返回值**:

- `Self`: 构建器实例

##### `with_trace_context(trace_id: &str, span_id: &str) -> Self`

添加追踪上下文。

**参数**:

- `trace_id`: 追踪ID
- `span_id`: 跨度ID

**返回值**:

- `Self`: 构建器实例

##### `with_timestamp(timestamp: SystemTime) -> Self`3

设置时间戳。

**参数**:

- `timestamp`: 时间戳

**返回值**:

- `Self`: 构建器实例

##### `send() -> Result<ExportResult, OtlpError>`2

发送日志数据。

**返回值**:

- `Result<ExportResult, OtlpError>`: 导出结果

## 🔧 配置结构

### BatchConfig

批处理配置。

```rust
use std::time::Duration;

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_millis(5000),
    max_queue_size: 2048,
    scheduled_delay: Duration::from_millis(5000),
    max_export_timeout: Duration::from_secs(30),
};
```

#### 字段说明

- `max_export_batch_size`: 最大导出批次大小
- `export_timeout`: 导出超时时间
- `max_queue_size`: 最大队列大小
- `scheduled_delay`: 调度延迟
- `max_export_timeout`: 最大导出超时时间

### RetryConfig

重试配置。

```rust
use std::time::Duration;

let retry_config = RetryConfig {
    max_retries: 5,
    initial_retry_delay: Duration::from_millis(1000),
    max_retry_delay: Duration::from_secs(30),
    retry_delay_multiplier: 2.0,
    randomize_retry_delay: true,
    retryable_status_codes: vec![429, 500, 502, 503, 504],
};
```

#### 字段说明1

- `max_retries`: 最大重试次数
- `initial_retry_delay`: 初始重试延迟
- `max_retry_delay`: 最大重试延迟
- `retry_delay_multiplier`: 重试延迟倍数
- `randomize_retry_delay`: 是否随机化重试延迟
- `retryable_status_codes`: 可重试的状态码

## 📊 数据类型

### TelemetryData

遥测数据枚举类型。

```rust
use c21_otlp::TelemetryData;

// 创建追踪数据
let trace_data = TelemetryData::trace("operation")
    .with_attribute("key", "value");

// 创建指标数据
let metric_data = TelemetryData::metric("request_count", 1.0)
    .with_label("method", "GET");

// 创建日志数据
let log_data = TelemetryData::log("message", LogSeverity::Info)
    .with_attribute("key", "value");
```

#### 变体

- `Trace`: 追踪数据
- `Metric`: 指标数据
- `Log`: 日志数据

### KeyValue

键值对类型。

```rust
use c21_otlp::data::KeyValue;

let kv = KeyValue::new("key", "value");
let numeric_kv = KeyValue::new("duration", 150.0);
let bool_kv = KeyValue::new("success", true);
```

#### 主要方法5

##### `new(key: &str, value: impl Into<AttributeValue>) -> Self`

创建新的键值对。

**参数**:

- `key`: 键
- `value`: 值

**返回值**:

- `Self`: 键值对实例

### AttributeValue

属性值枚举类型。

```rust
use c21_otlp::data::AttributeValue;

let string_value = AttributeValue::String("value".to_string());
let numeric_value = AttributeValue::Number(123.45);
let bool_value = AttributeValue::Boolean(true);
let array_value = AttributeValue::Array(vec![
    AttributeValue::String("item1".to_string()),
    AttributeValue::String("item2".to_string()),
]);
```

#### 变体1

- `String(String)`: 字符串值
- `Number(f64)`: 数值
- `Boolean(bool)`: 布尔值
- `Array(Vec<AttributeValue>)`: 数组值

### LogSeverity

日志级别枚举。

```rust
use c21_otlp::data::LogSeverity;

let trace = LogSeverity::Trace;
let debug = LogSeverity::Debug;
let info = LogSeverity::Info;
let warn = LogSeverity::Warn;
let error = LogSeverity::Error;
let fatal = LogSeverity::Fatal;
```

#### 变体2

- `Trace`: 追踪级别
- `Debug`: 调试级别
- `Info`: 信息级别
- `Warn`: 警告级别
- `Error`: 错误级别
- `Fatal`: 致命级别

### StatusCode

状态码枚举。

```rust
use c21_otlp::data::StatusCode;

let ok = StatusCode::Ok;
let error = StatusCode::Error;
```

#### 变体3

- `Ok`: 成功状态
- `Error`: 错误状态

## 🚀 传输协议

### TransportProtocol

传输协议枚举。

```rust
use c21_otlp::transport::TransportProtocol;

let grpc = TransportProtocol::Grpc;
let http = TransportProtocol::Http;
```

#### 变体4

- `Grpc`: gRPC协议
- `Http`: HTTP协议

### Compression

压缩算法枚举。

```rust
use c21_otlp::transport::Compression;

let none = Compression::None;
let gzip = Compression::Gzip;
let brotli = Compression::Brotli;
let zstd = Compression::Zstd;
```

#### 变体5

- `None`: 无压缩
- `Gzip`: Gzip压缩
- `Brotli`: Brotli压缩
- `Zstd`: Zstd压缩

## 📈 结果类型

### ExportResult

导出结果类型。

```rust
use c21_otlp::ExportResult;

let result = client.send_trace("operation").await?
    .finish()
    .await?;

println!("Success count: {}", result.success_count);
println!("Failure count: {}", result.failure_count);
```

#### 字段说明2

- `success_count`: 成功导出的数据条数
- `failure_count`: 失败的数据条数
- `export_time`: 导出时间
- `batch_size`: 批次大小

### ClientMetrics

客户端指标类型。

```rust
use c21_otlp::ClientMetrics;

let metrics = client.get_metrics().await;

println!("Total sent: {}", metrics.total_data_sent);
println!("Total received: {}", metrics.total_data_received);
println!("Uptime: {:?}", metrics.uptime);
```

#### 字段说明3

- `total_data_sent`: 总发送数据量
- `total_data_received`: 总接收数据量
- `uptime`: 运行时间
- `exporter_metrics`: 导出器指标
- `processor_metrics`: 处理器指标

## ❌ 错误处理

### OtlpError

OTLP错误类型。

```rust
use c21_otlp::error::OtlpError;

match client.send_trace("operation").await {
    Ok(builder) => {
        // 处理成功情况
    }
    Err(OtlpError::ConfigError(msg)) => {
        eprintln!("配置错误: {}", msg);
    }
    Err(OtlpError::TransportError(msg)) => {
        eprintln!("传输错误: {}", msg);
    }
    Err(OtlpError::SerializationError(msg)) => {
        eprintln!("序列化错误: {}", msg);
    }
    Err(OtlpError::ExportError(msg)) => {
        eprintln!("导出错误: {}", msg);
    }
    Err(e) => {
        eprintln!("其他错误: {}", e);
    }
}
```

#### 错误类型

- `ConfigError(String)`: 配置错误
- `TransportError(String)`: 传输错误
- `SerializationError(String)`: 序列化错误
- `ExportError(String)`: 导出错误
- `TimeoutError`: 超时错误
- `ConnectionError`: 连接错误
- `AuthenticationError`: 认证错误
- `AuthorizationError`: 授权错误

## 🎯 使用示例

### 基础使用

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_service("example-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 创建客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "example-service")
        .finish()
        .await?;
    
    println!("发送成功: {} 条", result.success_count);
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

### 高级使用

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use c21_otlp::data::{LogSeverity, StatusCode};
use c21_otlp::transport::{TransportProtocol, Compression};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建高级配置
    let config = OtlpConfig::default()
        .with_endpoint("https://api.honeycomb.io:443")
        .with_protocol(TransportProtocol::Grpc)
        .with_compression(Compression::Gzip)
        .with_api_key("your-api-key")
        .with_sampling_ratio(0.1)
        .with_batch_config(BatchConfig {
            max_export_batch_size: 512,
            export_timeout: Duration::from_millis(5000),
            max_queue_size: 2048,
            scheduled_delay: Duration::from_millis(5000),
        });
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送多种类型的数据
    let trace_result = client.send_trace("user-login").await?
        .with_attribute("user.id", "12345")
        .with_status(StatusCode::Ok, Some("Login successful".to_string()))
        .finish()
        .await?;
    
    let metric_result = client.send_metric("login_attempts", 1.0).await?
        .with_label("method", "password")
        .with_description("User login attempts")
        .with_unit("count")
        .send()
        .await?;
    
    let log_result = client.send_log("User logged in", LogSeverity::Info).await?
        .with_attribute("user.id", "12345")
        .with_attribute("ip.address", "192.168.1.100")
        .send()
        .await?;
    
    // 批量发送
    let mut batch_data = Vec::new();
    for i in 0..10 {
        batch_data.push(TelemetryData::trace(format!("batch-operation-{}", i))
            .with_attribute("batch.id", "BATCH-001"));
    }
    
    let batch_result = client.send_batch(batch_data).await?;
    
    println!("追踪: {} 条", trace_result.success_count);
    println!("指标: {} 条", metric_result.success_count);
    println!("日志: {} 条", log_result.success_count);
    println!("批量: {} 条", batch_result.success_count);
    
    // 获取指标
    let metrics = client.get_metrics().await;
    println!("总发送: {}", metrics.total_data_sent);
    
    client.shutdown().await?;
    Ok(())
}
```

## 📚 总结

本文档涵盖了OTLP Rust实现的核心API，包括：

1. **OtlpClient**: 主要的客户端接口
2. **OtlpConfig**: 配置管理
3. **数据构建器**: TraceBuilder、MetricBuilder、LogBuilder
4. **数据类型**: TelemetryData、KeyValue、AttributeValue等
5. **传输协议**: TransportProtocol、Compression
6. **结果类型**: ExportResult、ClientMetrics
7. **错误处理**: OtlpError

通过合理使用这些API，可以构建强大的可观测性系统。

---

**核心API文档版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP 2025 文档团队
