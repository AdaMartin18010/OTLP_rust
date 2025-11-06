# 核心 API 使用指南

## EnhancedOtlpClient - 基于 opentelemetry-otlp 0.31.0

---

## 📋 目录

- [快速开始](#快速开始)
- [API 参考](#api-参考)
- [配置选项](#配置选项)
- [使用示例](#使用示例)
- [最佳实践](#最佳实践)
- [故障排查](#故障排查)

---

## 快速开始

### 基本用法

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .build()
        .await?;

    // 2. 获取 Tracer
    let tracer = client.tracer("my-component");

    // 3. 创建 Span
    let span = tracer.start("my-operation");

    // 4. 业务逻辑
    println!("Processing...");

    // 5. Span 自动结束
    drop(span);

    // 6. 查看统计
    let stats = client.stats().await;
    println!("Spans exported: {}", stats.spans_exported);

    // 7. 优雅关闭
    client.shutdown().await?;

    Ok(())
}
```

### 添加依赖

```toml
[dependencies]
otlp = { path = "../otlp" }
tokio = { version = "1", features = ["full"] }
```

---

## API 参考

### EnhancedOtlpClient

#### 创建客户端

##### `builder() -> ClientBuilder`

创建客户端构建器。

```rust
let builder = EnhancedOtlpClient::builder();
```

**返回值**: `ClientBuilder` - 用于配置客户端

---

#### 获取 Tracer

##### `tracer(&self, name: impl Into<String>) -> impl Tracer`

获取指定名称的 Tracer。

```rust
let tracer = client.tracer("my-component");
```

**参数**:

- `name`: Tracer 名称，通常是组件或模块名称

**返回值**: 实现了 `opentelemetry::trace::Tracer` trait 的对象

**示例**:

```rust
// 为不同模块创建不同的 tracer
let auth_tracer = client.tracer("auth-service");
let db_tracer = client.tracer("database");
let api_tracer = client.tracer("api-handler");
```

---

#### 获取统计信息

##### `stats(&self) -> Future<Output = ClientStats>`

获取客户端的运行时统计信息。

```rust
let stats = client.stats().await;
println!("Exported: {}", stats.spans_exported);
```

**返回值**: `ClientStats` 包含以下字段：

- `spans_exported: u64` - 已导出的 span 数量
- `export_errors: u64` - 导出错误数量
- `avg_export_time_ms: u64` - 平均导出时间（毫秒）
- `performance_optimizations_applied: u64` - 性能优化应用次数
- `reliability_retries: u64` - 可靠性重试次数

**示例**:

```rust
let stats = client.stats().await;
println!("📊 客户端统计:");
println!("  导出 Spans: {}", stats.spans_exported);
println!("  导出错误: {}", stats.export_errors);
println!("  平均时间: {}ms", stats.avg_export_time_ms);
```

---

#### 获取配置

##### `config(&self) -> &ClientConfig`

获取客户端配置的只读引用。

```rust
let config = client.config();
println!("Endpoint: {}", config.endpoint);
```

**返回值**: `&ClientConfig` 包含：

- `endpoint: String` - OTLP 端点
- `service_name: String` - 服务名称
- `timeout: Duration` - 超时时间
- `protocol: Protocol` - 传输协议
- `enable_performance: bool` - 是否启用性能优化
- `enable_reliability: bool` - 是否启用可靠性增强
- `set_global: bool` - 是否设置为全局 provider

---

#### 关闭客户端

##### `shutdown(&self) -> Future<Output = Result<()>>`

优雅地关闭客户端，确保所有数据已导出。

```rust
client.shutdown().await?;
```

**返回值**: `Result<()>` - 成功返回 `Ok(())`，失败返回错误

**重要**:

- 应该在程序结束前调用
- 确保所有 span 数据被导出
- 释放资源

---

### ClientBuilder

#### 配置方法

##### `with_endpoint(url: impl Into<String>) -> Self`

设置 OTLP 端点 URL。

```rust
let builder = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317");
```

**参数**:

- `url`: OTLP Collector 的端点地址

**示例**:

```rust
// gRPC (默认端口 4317)
.with_endpoint("http://localhost:4317")

// HTTP (端口 4318)
.with_endpoint("http://localhost:4318")

// 远程服务
.with_endpoint("https://otel-collector.example.com:4317")
```

---

##### `with_service_name(name: impl Into<String>) -> Self`

设置服务名称。

```rust
let builder = EnhancedOtlpClient::builder()
    .with_service_name("my-service");
```

**参数**:

- `name`: 服务名称，用于标识遥测数据来源

---

##### `with_timeout(duration: Duration) -> Self`

设置导出超时时间。

```rust
use std::time::Duration;

let builder = EnhancedOtlpClient::builder()
    .with_timeout(Duration::from_secs(30));
```

**参数**:

- `duration`: 超时时间，默认 10 秒

**建议**:

- 本地开发: 5-10 秒
- 生产环境: 15-30 秒
- 高延迟网络: 30-60 秒

---

##### `with_protocol(protocol: Protocol) -> Self`

设置传输协议。

```rust
use opentelemetry_otlp::Protocol;

let builder = EnhancedOtlpClient::builder()
    .with_protocol(Protocol::Grpc);
```

**参数**:

- `protocol`: `Protocol::Grpc` 或 `Protocol::HttpBinary`

**协议对比**:

- **gRPC**: 高性能，二进制协议，推荐用于生产
- **HTTP**: 更好的兼容性，易于调试

---

##### `with_performance_optimization(enable: bool) -> Self`

启用或禁用性能优化。

```rust
let builder = EnhancedOtlpClient::builder()
    .with_performance_optimization(true);
```

**功能**:

- 对象池
- 批处理
- 数据压缩

**建议**: 生产环境启用

---

##### `with_reliability_enhancement(enable: bool) -> Self`

启用或禁用可靠性增强。

```rust
let builder = EnhancedOtlpClient::builder()
    .with_reliability_enhancement(true);
```

**功能**:

- 自动重试
- 熔断器
- 超时控制

**建议**: 生产环境启用

---

##### `with_global_provider(enable: bool) -> Self`

设置为全局 TracerProvider。

```rust
let builder = EnhancedOtlpClient::builder()
    .with_global_provider(true);
```

**作用**: 允许使用 `opentelemetry::global::tracer()` 获取 tracer

**注意**: 整个程序只能有一个全局 provider

---

##### `build() -> Future<Output = Result<EnhancedOtlpClient>>`

构建并初始化客户端。

```rust
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .build()
    .await?;
```

**返回值**: `Result<EnhancedOtlpClient>` - 成功返回客户端实例

---

## 配置选项

### 完整配置示例

```rust
use std::time::Duration;
use opentelemetry_otlp::Protocol;
use otlp::core::EnhancedOtlpClient;

let client = EnhancedOtlpClient::builder()
    // 基础配置
    .with_endpoint("http://localhost:4317")
    .with_service_name("production-service")
    .with_timeout(Duration::from_secs(30))
    .with_protocol(Protocol::Grpc)

    // 增强功能
    .with_performance_optimization(true)
    .with_reliability_enhancement(true)
    .with_global_provider(true)

    .build()
    .await?;
```

### 配置建议

#### 开发环境

```rust
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_service_name("dev-service")
    .with_timeout(Duration::from_secs(5))
    .with_performance_optimization(false)  // 便于调试
    .with_reliability_enhancement(false)   // 快速失败
    .build()
    .await?;
```

#### 生产环境

```rust
let client = EnhancedOtlpClient::builder()
    .with_endpoint("https://otel-collector.prod:4317")
    .with_service_name("prod-service")
    .with_timeout(Duration::from_secs(30))
    .with_performance_optimization(true)   // 提升性能
    .with_reliability_enhancement(true)    // 确保可靠
    .with_global_provider(true)            // 全局访问
    .build()
    .await?;
```

---

## 使用示例

### 示例 1: 基本 Span 创建

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("example-service")
        .build()
        .await?;

    let tracer = client.tracer("main");

    // 创建 span
    let span = tracer.start("example-operation");

    // 模拟工作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    drop(span);

    client.shutdown().await?;
    Ok(())
}
```

### 示例 2: 嵌套 Spans

```rust
use opentelemetry::trace::{Tracer, SpanKind};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("nested-example")
        .build()
        .await?;

    let tracer = client.tracer("main");

    // 父 span
    let parent = tracer.start("parent-operation");

    {
        // 子 span
        let child = tracer.start("child-operation");

        // 工作
        process_data().await;

        drop(child);
    }

    drop(parent);

    client.shutdown().await?;
    Ok(())
}

async fn process_data() {
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
}
```

### 示例 3: 并发使用

```rust
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Arc::new(
        EnhancedOtlpClient::builder()
            .with_endpoint("http://localhost:4317")
            .with_service_name("concurrent-service")
            .build()
            .await?
    );

    let mut handles = vec![];

    // 启动多个并发任务
    for i in 0..5 {
        let client_clone = Arc::clone(&client);
        let handle = tokio::spawn(async move {
            let tracer = client_clone.tracer(format!("worker-{}", i));
            let span = tracer.start(format!("task-{}", i));

            // 模拟工作
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

            drop(span);
        });

        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await?;
    }

    // 查看统计
    let stats = client.stats().await;
    println!("Total spans: {}", stats.spans_exported);

    client.shutdown().await?;
    Ok(())
}
```

### 示例 4: 添加属性和事件

```rust
use opentelemetry::{KeyValue, trace::{Tracer, Status}};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("attributes-example")
        .build()
        .await?;

    let tracer = client.tracer("main");
    let mut span = tracer.start("operation-with-attributes");

    // 添加属性
    span.set_attribute(KeyValue::new("user.id", "123"));
    span.set_attribute(KeyValue::new("operation.type", "read"));

    // 添加事件
    span.add_event("Processing started", vec![
        KeyValue::new("item.count", 10),
    ]);

    // 模拟工作
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    // 设置状态
    span.set_status(Status::Ok);

    drop(span);

    client.shutdown().await?;
    Ok(())
}
```

### 示例 5: 错误处理

```rust
use opentelemetry::trace::{Tracer, Status, StatusCode};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("error-handling")
        .build()
        .await?;

    let tracer = client.tracer("main");
    let mut span = tracer.start("operation-with-error");

    match risky_operation().await {
        Ok(result) => {
            span.set_attribute(KeyValue::new("result", result));
            span.set_status(Status::Ok);
        }
        Err(e) => {
            span.set_attribute(KeyValue::new("error", e.to_string()));
            span.set_status(Status::error(e.to_string()));
        }
    }

    drop(span);

    client.shutdown().await?;
    Ok(())
}

async fn risky_operation() -> Result<String, Box<dyn std::error::Error>> {
    // 可能失败的操作
    Ok("success".to_string())
}
```

---

## 最佳实践

### 1. 客户端生命周期

```rust
// ✅ 好: 在程序启动时创建一次
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .build()
        .await?;

    // 使用客户端...

    // 程序结束时关闭
    client.shutdown().await?;
    Ok(())
}

// ❌ 差: 频繁创建和销毁
async fn bad_example() {
    for _ in 0..100 {
        let client = EnhancedOtlpClient::builder()
            .build()
            .await
            .unwrap();  // 开销大

        // 使用...
    }
}
```

### 2. Tracer 命名

```rust
// ✅ 好: 使用有意义的名称
let auth_tracer = client.tracer("auth-service");
let db_tracer = client.tracer("database");
let api_tracer = client.tracer("api-handler");

// ❌ 差: 通用名称
let tracer1 = client.tracer("tracer1");
let tracer2 = client.tracer("test");
```

### 3. Span 生命周期

```rust
// ✅ 好: 使用作用域控制 span 生命周期
{
    let span = tracer.start("operation");
    // 操作...
}  // span 自动结束

// ✅ 好: 显式 drop
let span = tracer.start("operation");
// 操作...
drop(span);

// ❌ 差: 忘记结束 span
let span = tracer.start("operation");
// 操作...
// span 一直存在到函数结束
```

### 4. 错误处理

```rust
// ✅ 好: 记录错误信息
match operation().await {
    Ok(result) => {
        span.set_status(Status::Ok);
    }
    Err(e) => {
        span.set_attribute(KeyValue::new("error.type", e.type_name()));
        span.set_attribute(KeyValue::new("error.message", e.to_string()));
        span.set_status(Status::error(e.to_string()));
    }
}

// ❌ 差: 忽略错误
let _ = operation().await;  // 没有追踪
```

### 5. 并发安全

```rust
// ✅ 好: 使用 Arc 共享客户端
let client = Arc::new(client);

for i in 0..10 {
    let client_clone = Arc::clone(&client);
    tokio::spawn(async move {
        let tracer = client_clone.tracer("worker");
        // 使用...
    });
}

// ❌ 差: 尝试移动客户端
for i in 0..10 {
    tokio::spawn(async move {
        let tracer = client.tracer("worker");  // 编译错误
    });
}
```

---

## 故障排查

### 问题 1: 连接失败

**症状**: 无法连接到 OTLP Collector

**检查**:

```rust
// 确保 Collector 正在运行
// Docker 启动:
// docker run -p 4317:4317 otel/opentelemetry-collector

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")  // 检查端点
    .with_timeout(Duration::from_secs(10))   // 增加超时
    .build()
    .await?;
```

**解决方案**:

1. 检查 Collector 是否运行
2. 验证端口号 (gRPC: 4317, HTTP: 4318)
3. 检查防火墙设置

### 问题 2: Spans 未导出

**症状**: 统计显示 `spans_exported = 0`

**检查**:

```rust
// 确保创建了 span
let span = tracer.start("operation");
// ... 操作
drop(span);  // 确保 span 结束

// 检查统计
let stats = client.stats().await;
println!("Exported: {}", stats.spans_exported);
println!("Errors: {}", stats.export_errors);
```

**解决方案**:

1. 确保 span 被正确结束 (drop)
2. 检查是否有导出错误
3. 在关闭前调用 `client.shutdown().await`

### 问题 3: 性能问题

**症状**: 导出延迟高

**优化**:

```rust
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_performance_optimization(true)   // 启用性能优化
    .with_timeout(Duration::from_secs(30))  // 增加超时
    .build()
    .await?;
```

**建议**:

1. 启用性能优化
2. 使用本地 Collector
3. 调整批处理大小

---

## 📖 相关资源

- [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
- [OTLP 规范](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md)
- [Rust API 文档](https://docs.rs/opentelemetry/)

---

**最后更新**: 2025-10-18
**版本**: 0.1.0

---

