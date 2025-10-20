# OTLP Rust 用户指南

## 📖 简介

OTLP Rust 是一个高质量、生产就绪的 OpenTelemetry Protocol (OTLP) 实现，专为 Rust 1.90+ 设计。本指南将帮助您快速上手并充分利用 OTLP Rust 的强大功能。

## 🚀 快速开始

### 安装

在您的 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.47", features = ["full"] }
```

### 基本使用

#### 1. 创建 OTLP 客户端

```rust
use otlp::{
    client::{OtlpClient, OtlpClientBuilder},
    config::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression},
    data::{TelemetryData, TelemetryDataType, TelemetryContent, TraceData, SpanKind},
};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置
    let config = OtlpConfigBuilder::new()
        .endpoint("http://localhost:4317")
        .protocol(TransportProtocol::Grpc)
        .compression(Compression::Gzip)
        .build();

    // 创建客户端
    let client = OtlpClientBuilder::new()
        .config(config)
        .build()
        .await?;

    // 创建追踪数据
    let trace_data = TraceData {
        trace_id: "12345678901234567890123456789012".to_string(),
        span_id: "1234567890123456".to_string(),
        parent_span_id: None,
        name: "my-operation".to_string(),
        span_kind: SpanKind::Internal,
        start_time: 1000,
        end_time: 2000,
        status: otlp::data::SpanStatus::default(),
        attributes: HashMap::from([
            ("service.name".to_string(), otlp::data::AttributeValue::String("my-service".to_string())),
        ]),
        events: vec![],
        links: vec![],
    };

    let telemetry_data = TelemetryData::new(
        TelemetryDataType::Trace,
        TelemetryContent::Trace(trace_data)
    );

    // 发送数据
    client.traces().send(vec![telemetry_data]).await?;

    Ok(())
}
```

## 📊 数据传输

### 支持的传输协议

OTLP Rust 支持多种传输协议：

#### gRPC 传输

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("http://localhost:4317")
    .protocol(TransportProtocol::Grpc)
    .build();
```

#### HTTP 传输

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("http://localhost:4318")
    .protocol(TransportProtocol::Http)
    .build();
```

#### HTTP/Protobuf 传输

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("http://localhost:4318")
    .protocol(TransportProtocol::HttpProtobuf)
    .build();
```

### 压缩支持

OTLP Rust 支持多种压缩算法：

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("http://localhost:4317")
    .compression(Compression::Gzip)  // 或 Brotli, Zstd, None
    .build();
```

## 🔄 OTTL 数据转换

OTTL (OpenTelemetry Transformation Language) 允许您在发送数据前进行转换和过滤。

### 基本转换

```rust
use otlp::ottl::{OtlpTransform, TransformConfig, Statement, Expression, Path, Literal};

// 创建转换配置
let config = TransformConfig::new()
    .add_statement(Statement::Set {
        path: Path::ResourceAttribute { key: "service.name".to_string() },
        value: Expression::Literal(Literal::String("transformed-service".to_string())),
    })
    .add_statement(Statement::Where {
        condition: Expression::Literal(Literal::Bool(true)),
    });

// 创建转换器
let transformer = OtlpTransform::new(config)?;

// 转换数据
let result = transformer.transform(telemetry_data).await?;
```

### 支持的 OTTL 语句

#### Set 语句

设置属性值：

```rust
Statement::Set {
    path: Path::ResourceAttribute { key: "env".to_string() },
    value: Expression::Literal(Literal::String("production".to_string())),
}
```

#### Where 语句

过滤数据：

```rust
Statement::Where {
    condition: Expression::Literal(Literal::Bool(true)),
}
```

#### KeepKeys 语句

保留指定的键：

```rust
Statement::KeepKeys {
    path: Path::ResourceAttribute { key: "attributes".to_string() },
    keys: vec![Expression::Literal(Literal::String("service.name".to_string()))],
}
```

## 🔧 数据验证

OTLP Rust 提供强大的数据验证功能：

```rust
use otlp::validation::DataValidator;

let validator = DataValidator::new(true); // 严格模式

// 验证数据
validator.validate_telemetry_data(&telemetry_data)?;
```

### 验证模式

- **严格模式** (`true`): 进行完整的格式验证
- **宽松模式** (`false`): 只进行基本验证

## 📈 性能分析

OTLP Rust 内置性能分析功能：

```rust
use otlp::profiling::{Profiler, ProfilingConfig};
use std::time::Duration;

let config = ProfilingConfig {
    sampling_rate: 99,
    duration: Duration::from_secs(30),
    enable_cpu_profiling: true,
    enable_memory_profiling: true,
    enable_lock_profiling: false,
};

let mut profiler = Profiler::new(config);

// 启动性能分析
profiler.start().await?;

// 收集性能数据
let data = profiler.collect_data().await?;

// 停止性能分析
profiler.stop().await?;
```

## 🏭 生产环境配置

### 推荐配置

```rust
let config = OtlpConfigBuilder::new()
    .endpoint("https://your-otlp-endpoint.com")
    .protocol(TransportProtocol::Grpc)
    .compression(Compression::Gzip)
    .build();
```

### 错误处理

```rust
use otlp::error::{OtlpError, Result};

async fn send_telemetry_data(data: Vec<TelemetryData>) -> Result<()> {
    match client.traces().send(data).await {
        Ok(_) => {
            println!("数据发送成功");
            Ok(())
        }
        Err(OtlpError::Transport(_)) => {
            eprintln!("传输错误，请检查网络连接");
            Err(OtlpError::Transport(/* ... */))
        }
        Err(e) => {
            eprintln!("其他错误: {}", e);
            Err(e)
        }
    }
}
```

## 🔍 监控和调试

### 日志配置

```rust
use tracing::{info, error, debug};

// 启用详细日志
env_logger::init();

// 在代码中使用日志
info!("发送遥测数据: {} 条记录", data.len());
debug!("数据详情: {:?}", data);
```

### 健康检查

```rust
// 检查传输连接状态
if transport.is_connected().await {
    println!("传输连接正常");
} else {
    println!("传输连接异常");
}
```

## 📚 最佳实践

### 1. 批量发送

```rust
// 好的做法：批量发送
let batch_data: Vec<TelemetryData> = collect_telemetry_data();
client.traces().send(batch_data).await?;

// 避免：逐条发送
for data in telemetry_data {
    client.traces().send(vec![data]).await?;
}
```

### 2. 错误重试

```rust
use tokio::time::{sleep, Duration};

async fn send_with_retry(data: Vec<TelemetryData>, max_retries: u32) -> Result<()> {
    for attempt in 0..max_retries {
        match client.traces().send(data.clone()).await {
            Ok(_) => return Ok(()),
            Err(e) if attempt < max_retries - 1 => {
                let delay = Duration::from_millis(100 * 2_u64.pow(attempt));
                sleep(delay).await;
                continue;
            }
            Err(e) => return Err(e),
        }
    }
    Ok(())
}
```

### 3. 资源管理

```rust
// 使用 RAII 确保资源正确释放
{
    let client = OtlpClientBuilder::new()
        .config(config)
        .build()
        .await?;
    
    // 使用客户端...
} // 客户端在这里自动清理
```

## 🐛 故障排查

### 常见问题

#### 1. 连接超时

```text
错误: Transport error: Connection timeout
解决: 检查网络连接和端点配置
```

#### 2. 数据验证失败

```text
错误: Validation error: trace_id cannot be empty
解决: 确保所有必需字段都已设置
```

#### 3. 序列化错误

```text
错误: Serialization failed: Invalid data format
解决: 检查数据格式是否符合 OTLP 规范
```

### 调试技巧

1. **启用详细日志**：

   ```bash
   RUST_LOG=debug cargo run
   ```

2. **使用数据验证**：

   ```rust
   let validator = DataValidator::new(true);
   validator.validate_telemetry_data(&data)?;
   ```

3. **检查配置**：

   ```rust
   ConfigValidator::validate_config(&config)?;
   ```

## 📖 API 参考

### 核心类型

- `OtlpClient`: 主要的 OTLP 客户端
- `TelemetryData`: 遥测数据容器
- `TraceData`: 追踪数据
- `MetricData`: 指标数据
- `LogData`: 日志数据

### 源码参考（跳转）

- 客户端与构建器：`otlp/src/client.rs`
- 配置体系：`otlp/src/config.rs`
- 数据模型：`otlp/src/data.rs`
- 传输实现：`otlp/src/transport.rs`, `otlp/src/protobuf.rs`
- 导出与批处理：`otlp/src/exporter.rs`
- 处理器流水线：`otlp/src/processor.rs`

### 配置类型

- `OtlpConfig`: OTLP 配置
- `TransportProtocol`: 传输协议枚举
- `Compression`: 压缩算法枚举

### 错误类型

- `OtlpError`: 主要错误类型
- `TransportError`: 传输相关错误
- `ValidationError`: 验证相关错误

## 🤝 贡献指南

我们欢迎社区贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与项目开发。

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 许可证。详情请查看 [LICENSE](LICENSE) 文件。

## 🆘 获取帮助

- 查看 [GitHub Issues](https://github.com/your-org/otlp-rust/issues)
- 加入我们的 [Discord 社区](https://discord.gg/your-discord)
- 阅读 [文档网站](https://docs.otlp-rust.dev)

---

**版本**: 0.1.0  
**最后更新**: 2025年1月
