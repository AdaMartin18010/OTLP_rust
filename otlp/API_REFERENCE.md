# OTLP Rust API 参考

## 📚 概述

本文档提供了 OTLP Rust 库的完整 API 参考。所有公共 API 都包含详细的文档和示例。

## 🔧 核心模块

### Client 模块

#### `OtlpClient`

主要的 OTLP 客户端，用于发送遥测数据。

```rust
pub struct OtlpClient {
    // 私有字段
}
```

**方法**:

- `traces() -> TraceBuilder`: 获取追踪数据构建器
- `metrics() -> MetricBuilder`: 获取指标数据构建器  
- `logs() -> LogBuilder`: 获取日志数据构建器

**示例**:

```rust
let client = OtlpClientBuilder::new()
    .config(config)
    .build()
    .await?;

let trace_builder = client.traces();
```

#### `OtlpClientBuilder`

OTLP 客户端构建器。

```rust
pub struct OtlpClientBuilder {
    // 私有字段
}
```

**方法**:

- `new() -> Self`: 创建新的构建器
- `config(config: OtlpConfig) -> Self`: 设置配置
- `build() -> Result<OtlpClient>`: 构建客户端

**示例**:

```rust
let client = OtlpClientBuilder::new()
    .config(config)
    .build()
    .await?;
```

#### `TraceBuilder`

追踪数据构建器。

```rust
pub struct TraceBuilder {
    // 私有字段
}
```

**方法**:

- `send(data: Vec<TelemetryData>) -> Result<()>`: 发送追踪数据

**示例**:

```rust
let trace_data = create_trace_data();
client.traces().send(vec![trace_data]).await?;
```

### Config 模块

#### `OtlpConfig`

OTLP 客户端配置。

```rust
pub struct OtlpConfig {
    pub endpoint: String,
    pub protocol: TransportProtocol,
    pub compression: Compression,
    pub connect_timeout: Duration,
    pub request_timeout: Duration,
    pub batch_config: BatchConfig,
    pub retry_config: RetryConfig,
    pub tls_config: TlsConfig,
    pub auth_config: AuthConfig,
    pub service_name: String,
    // ... 其他字段
}
```

#### `OtlpConfigBuilder`

配置构建器。

```rust
pub struct OtlpConfigBuilder {
    // 私有字段
}
```

**方法**:

- `new() -> Self`: 创建新的构建器
- `endpoint(endpoint: impl Into<String>) -> Self`: 设置端点
- `protocol(protocol: TransportProtocol) -> Self`: 设置协议
- `compression(compression: Compression) -> Self`: 设置压缩
- `build() -> OtlpConfig`: 构建配置

**示例**:

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("http://localhost:4317")
    .protocol(TransportProtocol::Grpc)
    .compression(Compression::Gzip)
    .build();
```

#### `TransportProtocol`

传输协议枚举。

```rust
pub enum TransportProtocol {
    Grpc,
    Http,
    HttpProtobuf,
}
```

#### `Compression`

压缩算法枚举。

```rust
pub enum Compression {
    None,
    Gzip,
    Brotli,
    Zstd,
}
```

### Data 模块

#### `TelemetryData`

遥测数据容器。

```rust
pub struct TelemetryData {
    pub data_type: TelemetryDataType,
    pub content: TelemetryContent,
    pub timestamp: u64,
    pub resource_attributes: HashMap<String, String>,
    pub scope_attributes: HashMap<String, String>,
}
```

**方法**:

- `new(data_type: TelemetryDataType, content: TelemetryContent) -> Self`: 创建新的遥测数据

#### `TelemetryDataType`

遥测数据类型枚举。

```rust
pub enum TelemetryDataType {
    Trace,
    Metric,
    Log,
}
```

#### `TelemetryContent`

遥测数据内容联合体。

```rust
pub enum TelemetryContent {
    Trace(TraceData),
    Metric(MetricData),
    Log(LogData),
}
```

#### `TraceData`

追踪数据结构。

```rust
pub struct TraceData {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub name: String,
    pub span_kind: SpanKind,
    pub start_time: u64,
    pub end_time: u64,
    pub status: SpanStatus,
    pub attributes: HashMap<String, AttributeValue>,
    pub events: Vec<SpanEvent>,
    pub links: Vec<SpanLink>,
}
```

#### `SpanKind`

跨度类型枚举。

```rust
pub enum SpanKind {
    Unset,
    Internal,
    Server,
    Client,
    Producer,
    Consumer,
}
```

#### `AttributeValue`

属性值联合体。

```rust
pub enum AttributeValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    StringArray(Vec<String>),
    BoolArray(Vec<bool>),
    IntArray(Vec<i64>),
    DoubleArray(Vec<f64>),
}
```

### Transport 模块

#### `Transport`

传输层接口。

```rust
#[async_trait]
pub trait Transport: Send + Sync {
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()>;
    async fn send_single(&self, data: TelemetryData) -> Result<()>;
    async fn is_connected(&self) -> bool;
    async fn close(&self) -> Result<()>;
    fn protocol(&self) -> TransportProtocol;
}
```

#### `GrpcTransport`

gRPC 传输实现。

```rust
pub struct GrpcTransport {
    // 私有字段
}
```

**方法**:

- `new(config: OtlpConfig) -> Result<Self>`: 创建新的 gRPC 传输

#### `HttpTransport`

HTTP 传输实现。

```rust
pub struct HttpTransport {
    // 私有字段
}
```

**方法**:

- `new(config: OtlpConfig) -> Result<Self>`: 创建新的 HTTP 传输

#### `TransportFactory`

传输工厂。

```rust
pub struct TransportFactory {
    // 私有字段
}
```

**方法**:

- `new() -> Self`: 创建新的工厂
- `add_transport(name: &str, config: OtlpConfig) -> Result<()>`: 添加传输
- `send(data: Vec<TelemetryData>) -> Result<()>`: 发送数据
- `close_all() -> Result<()>`: 关闭所有传输

### Validation 模块

#### `DataValidator`

数据验证器。

```rust
pub struct DataValidator {
    strict_mode: bool,
}
```

**方法**:

- `new(strict_mode: bool) -> Self`: 创建新的验证器
- `validate_telemetry_data(&self, data: &TelemetryData) -> Result<()>`: 验证遥测数据

**示例**:

```rust
let validator = DataValidator::new(true);
validator.validate_telemetry_data(&telemetry_data)?;
```

#### `ConfigValidator`

配置验证器。

```rust
pub struct ConfigValidator;
```

**方法**:

- `validate_config(config: &OtlpConfig) -> Result<()>`: 验证配置

**示例**:

```rust
ConfigValidator::validate_config(&config)?;
```

### OTTL 模块

#### `OtlpTransform`

OTTL 转换器。

```rust
pub struct OtlpTransform {
    config: TransformConfig,
}
```

**方法**:

- `new(config: TransformConfig) -> Result<Self>`: 创建新的转换器
- `transform(&self, data: Vec<TelemetryData>) -> Result<TransformResult>`: 转换数据

#### `TransformConfig`

转换配置。

```rust
pub struct TransformConfig {
    pub statements: Vec<Statement>,
}
```

**方法**:

- `new() -> Self`: 创建新的配置
- `add_statement(self, statement: Statement) -> Self`: 添加语句

#### `Statement`

OTTL 语句枚举。

```rust
pub enum Statement {
    Set { path: Path, value: Expression },
    Where { condition: Expression },
    KeepKeys { path: Path, keys: Vec<Expression> },
    Limit { path: Path, count: Expression },
    Convert { path: Path, target_type: String },
    Route { path: Path, destinations: Vec<Expression> },
}
```

#### `Expression`

OTTL 表达式枚举。

```rust
pub enum Expression {
    Literal(Literal),
    Path(Box<Path>),
    FunctionCall { name: String, args: Vec<Expression> },
    Binary { left: Box<Expression>, op: BinaryOp, right: Box<Expression> },
    Unary { op: UnaryOp, expr: Box<Expression> },
    Conditional { condition: Box<Expression>, true_expr: Box<Expression>, false_expr: Box<Expression> },
}
```

#### `Path`

OTTL 路径枚举。

```rust
pub enum Path {
    ResourceAttribute { key: String },
    ScopeAttribute { key: String },
    MetricAttribute { key: String },
    SpanAttribute { key: String },
    LogAttribute { key: String },
    Nested { base: Box<Path>, subpath: String },
    Indexed { base: Box<Path>, index: Expression },
}
```

### Profiling 模块

#### `Profiler`

性能分析器。

```rust
pub struct Profiler {
    config: ProfilingConfig,
    is_running: bool,
}
```

**方法**:

- `new(config: ProfilingConfig) -> Self`: 创建新的分析器
- `start(&mut self) -> Result<()>`: 启动分析
- `stop(&mut self) -> Result<()>`: 停止分析
- `collect_data(&self) -> Result<Vec<TelemetryData>>`: 收集数据
- `is_running(&self) -> bool`: 检查是否运行中

#### `ProfilingConfig`

性能分析配置。

```rust
pub struct ProfilingConfig {
    pub sampling_rate: u32,
    pub duration: Duration,
    pub enable_cpu_profiling: bool,
    pub enable_memory_profiling: bool,
    pub enable_lock_profiling: bool,
}
```

**默认值**:

```rust
impl Default for ProfilingConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 99,
            duration: Duration::from_secs(30),
            enable_cpu_profiling: true,
            enable_memory_profiling: false,
            enable_lock_profiling: false,
        }
    }
}
```

### Error 模块

#### `OtlpError`

主要错误类型。

```rust
#[derive(Debug, thiserror::Error)]
pub enum OtlpError {
    #[error("传输错误: {0}")]
    Transport(#[from] TransportError),
    
    #[error("序列化错误: {0}")]
    Serialization(String),
    
    #[error("配置错误: {0}")]
    Configuration(String),
    
    #[error("处理错误: {0}")]
    Processing(String),
    
    #[error("导出错误: {0}")]
    Export(String),
    
    #[error("数据验证错误: {0}")]
    ValidationError(String),
    
    #[error("性能分析器已在运行")]
    ProfilerAlreadyRunning,
    
    #[error("性能分析器未运行")]
    ProfilerNotRunning,
    
    // ... 其他错误类型
}
```

#### `TransportError`

传输错误类型。

```rust
#[derive(Debug, thiserror::Error)]
pub enum TransportError {
    #[error("连接错误: {endpoint} - {reason}")]
    Connection { endpoint: String, reason: String },
    
    #[error("网络错误: {0}")]
    NetworkError(String),
    
    #[error("超时错误: {operation}")]
    Timeout { operation: String },
    
    #[error("空数据错误")]
    EmptyData,
}
```

## 🔄 使用模式

### 基本使用模式

```rust
use otlp::{
    client::{OtlpClient, OtlpClientBuilder},
    config::{OtlpConfigBuilder, TransportProtocol},
    data::{TelemetryData, TelemetryDataType, TelemetryContent, TraceData, SpanKind},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建配置
    let config = OtlpConfigBuilder::new()
        .endpoint("http://localhost:4317")
        .protocol(TransportProtocol::Grpc)
        .build();

    // 2. 创建客户端
    let client = OtlpClientBuilder::new()
        .config(config)
        .build()
        .await?;

    // 3. 创建数据
    let trace_data = TraceData {
        // ... 设置字段
    };

    let telemetry_data = TelemetryData::new(
        TelemetryDataType::Trace,
        TelemetryContent::Trace(trace_data)
    );

    // 4. 发送数据
    client.traces().send(vec![telemetry_data]).await?;

    Ok(())
}
```

### 高级使用模式

```rust
use otlp::{
    ottl::{OtlpTransform, TransformConfig, Statement, Expression, Path, Literal},
    validation::DataValidator,
};

// 1. 数据验证
let validator = DataValidator::new(true);
validator.validate_telemetry_data(&telemetry_data)?;

// 2. OTTL 转换
let config = TransformConfig::new()
    .add_statement(Statement::Set {
        path: Path::ResourceAttribute { key: "env".to_string() },
        value: Expression::Literal(Literal::String("production".to_string())),
    });

let transformer = OtlpTransform::new(config)?;
let result = transformer.transform(vec![telemetry_data]).await?;

// 3. 发送转换后的数据
client.traces().send(result.data).await?;
```

## 📊 性能考虑

### 批量处理

```rust
// 好的做法：批量发送
let batch_size = 100;
let batches: Vec<Vec<TelemetryData>> = data.chunks(batch_size)
    .map(|chunk| chunk.to_vec())
    .collect();

for batch in batches {
    client.traces().send(batch).await?;
}
```

### 并发处理

```rust
use tokio::task;

// 并发发送多个批次
let handles: Vec<_> = batches.into_iter()
    .map(|batch| {
        let client = client.clone();
        task::spawn(async move {
            client.traces().send(batch).await
        })
    })
    .collect();

// 等待所有任务完成
for handle in handles {
    handle.await??;
}
```

## 🛠️ 扩展和自定义

### 自定义传输

```rust
use otlp::transport::Transport;
use async_trait::async_trait;

struct CustomTransport;

#[async_trait]
impl Transport for CustomTransport {
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()> {
        // 自定义发送逻辑
        Ok(())
    }

    async fn send_single(&self, data: TelemetryData) -> Result<()> {
        self.send(vec![data]).await
    }

    async fn is_connected(&self) -> bool {
        true
    }

    async fn close(&self) -> Result<()> {
        Ok(())
    }

    fn protocol(&self) -> TransportProtocol {
        TransportProtocol::Http
    }
}
```

### 自定义验证器

```rust
use otlp::validation::DataValidator;

struct CustomValidator {
    validator: DataValidator,
}

impl CustomValidator {
    fn validate_custom(&self, data: &TelemetryData) -> Result<()> {
        // 自定义验证逻辑
        self.validator.validate_telemetry_data(data)?;
        
        // 额外的验证...
        Ok(())
    }
}
```

## 📝 版本兼容性

### Rust 版本要求

- **最低版本**: Rust 1.90
- **推荐版本**: Rust 1.95+

### 依赖版本

- **tokio**: 1.47+
- **serde**: 1.0+
- **tonic**: 0.14+ (可选)
- **reqwest**: 0.12+ (可选)

## 🔗 相关链接

- [用户指南](USER_GUIDE.md)
- [贡献指南](CONTRIBUTING.md)
- [GitHub 仓库](https://github.com/your-org/otlp-rust)
- [OpenTelemetry 规范](https://opentelemetry.io/docs/specs/otlp/)

---

**最后更新**: 2025年1月  
**版本**: 0.1.0
