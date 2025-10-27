# 🚀 快速入门教程

**版本**: 1.0  
**最后更新**: 2025年10月26日  
**状态**: 🟢 活跃维护

> **简介**: 快速入门教程 - 5分钟上手 OTLP Rust，从环境准备到第一个应用的完整流程。

---

## 📋 目录

- [🚀 快速入门教程](#-快速入门教程)
  - [📋 目录](#-目录)
  - [⚡ 5分钟快速开始](#-5分钟快速开始)
    - [步骤 1: 环境准备](#步骤-1-环境准备)
    - [步骤 2: 创建项目](#步骤-2-创建项目)
    - [步骤 3: 编写第一个程序](#步骤-3-编写第一个程序)
    - [步骤 4: 运行程序](#步骤-4-运行程序)
  - [📚 基础概念](#-基础概念)
    - [什么是 OTLP？](#什么是-otlp)
    - [核心组件](#核心组件)
      - [1. EnhancedOtlpClient](#1-enhancedotlpclient)
      - [2. Tracer](#2-tracer)
      - [3. Meter](#3-meter)
    - [数据流](#数据流)
  - [🎯 第一个应用](#-第一个应用)
    - [完整的示例应用](#完整的示例应用)
    - [运行完整示例](#运行完整示例)
  - [🔥 进阶示例](#-进阶示例)
    - [1. 配置和优化](#1-配置和优化)
    - [2. 错误处理](#2-错误处理)
    - [3. 性能监控](#3-性能监控)
  - [📖 下一步学习](#-下一步学习)
    - [推荐学习路径](#推荐学习路径)
      - [1. 基础掌握（1-2天）](#1-基础掌握1-2天)
      - [2. 进阶应用（3-5天）](#2-进阶应用3-5天)
      - [3. 深入理解（1-2周）](#3-深入理解1-2周)
      - [4. 生产部署（1-2周）](#4-生产部署1-2周)
    - [实践项目建议](#实践项目建议)
      - [初级项目](#初级项目)
      - [中级项目](#中级项目)
      - [高级项目](#高级项目)
    - [社区资源](#社区资源)
      - [官方文档](#官方文档)
      - [学习资源](#学习资源)
      - [社区支持](#社区支持)
  - [❓ 常见问题](#-常见问题)
    - [Q1: 客户端连接失败](#q1-客户端连接失败)
    - [Q2: 数据没有发送](#q2-数据没有发送)
    - [Q3: 性能问题](#q3-性能问题)
    - [Q4: 内存使用过高](#q4-内存使用过高)
    - [Q5: 编译错误](#q5-编译错误)
  - [🎉 总结](#-总结)
    - [下一步行动](#下一步行动)

---

## ⚡ 5分钟快速开始

### 步骤 1: 环境准备

确保你已经安装了 Rust 1.90+ 和必要的依赖：

```bash
# 检查 Rust 版本
rustc --version
# 预期输出: rustc 1.90.0+

# 检查 Cargo 版本
cargo --version
# 预期输出: cargo 1.90.0+
```

### 步骤 2: 创建项目

```bash
# 创建新的 Rust 项目
cargo new my_otlp_app
cd my_otlp_app

# 添加 OTLP 依赖
cargo add --path ../crates/otlp
cargo add tokio --features full
```

### 步骤 3: 编写第一个程序

编辑 `src/main.rs`：

```rust
use otlp::core::EnhancedOtlpClient;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动 OTLP 客户端...");
    
    // 创建 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")  // OTLP Collector 地址
        .with_service_name("my-first-app")
        .with_service_version("1.0.0")
        .with_http_transport()
        .with_connect_timeout(Duration::from_secs(5))
        .build()
        .await?;
    
    println!("✅ OTLP 客户端创建成功！");
    
    // 创建追踪器
    let tracer = client.tracer("main-component");
    let mut span = tracer.start("my-first-operation");
    
    // 添加属性
    span.set_attribute("user.id", "12345");
    span.set_attribute("operation.type", "demo");
    
    // 模拟一些工作
    println!("📊 执行业务逻辑...");
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 结束 span
    span.end();
    
    println!("🎉 第一个 OTLP 应用运行成功！");
    Ok(())
}
```

### 步骤 4: 运行程序

```bash
# 运行程序
cargo run

# 预期输出:
# 🚀 启动 OTLP 客户端...
# ✅ OTLP 客户端创建成功！
# 📊 执行业务逻辑...
# 🎉 第一个 OTLP 应用运行成功！
```

**恭喜！** 你已经成功创建了第一个 OTLP 应用！🎉

---

## 📚 基础概念

### 什么是 OTLP？

**OTLP (OpenTelemetry Protocol)** 是一个开放标准，用于收集、处理和传输遥测数据：

- **Traces**: 分布式追踪数据，记录请求在系统中的完整路径
- **Metrics**: 指标数据，监控系统性能和业务指标
- **Logs**: 结构化日志数据，提供丰富的上下文信息

### 核心组件

#### 1. EnhancedOtlpClient

主要的客户端接口，提供统一的遥测数据收集和传输功能。

```rust
let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .build()
    .await?;
```

#### 2. Tracer

用于创建和管理分布式追踪的 Span。

```rust
let tracer = client.tracer("component-name");
let span = tracer.start("operation-name");
```

#### 3. Meter

用于记录和收集指标数据。

```rust
let meter = client.meter("metrics-component");
let counter = meter.u64_counter("requests_total").init();
```

### 数据流

```text
应用代码 → OTLP 客户端 → 数据收集器 → 后端系统
    ↓           ↓            ↓           ↓
  生成数据    → 格式化    → 批处理    → 存储/分析
```

---

## 🎯 第一个应用

让我们创建一个更完整的示例，展示 OTLP 的主要功能：

### 完整的示例应用

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::trace::{Tracer, SpanKind, StatusCode};
use opentelemetry::metrics::{Meter, Counter, Unit};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 启动完整的 OTLP 示例应用...");
    
    // 创建 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("demo-app")
        .with_service_version("1.0.0")
        .with_http_transport()
        .build()
        .await?;
    
    // 1. 分布式追踪示例
    println!("📊 演示分布式追踪...");
    demo_tracing(&client).await?;
    
    // 2. 指标收集示例
    println!("📈 演示指标收集...");
    demo_metrics(&client).await?;
    
    // 3. 日志记录示例
    println!("📝 演示日志记录...");
    demo_logging(&client).await?;
    
    println!("🎉 所有示例运行完成！");
    Ok(())
}

// 分布式追踪示例
async fn demo_tracing(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = client.tracer("demo-tracer");
    
    // 创建根 span
    let mut root_span = tracer.start_with_kind("user-request", SpanKind::Server);
    root_span.set_attribute("user.id", "12345");
    root_span.set_attribute("request.method", "GET");
    root_span.set_attribute("request.path", "/api/users");
    
    // 模拟数据库查询
    let mut db_span = tracer.start_with_kind("database-query", SpanKind::Client);
    db_span.set_attribute("db.system", "postgresql");
    db_span.set_attribute("db.operation", "SELECT");
    
    tokio::time::sleep(Duration::from_millis(50)).await;
    db_span.set_status(StatusCode::Ok, "Query successful".to_string());
    db_span.end();
    
    // 模拟外部 API 调用
    let mut api_span = tracer.start_with_kind("external-api-call", SpanKind::Client);
    api_span.set_attribute("http.method", "GET");
    api_span.set_attribute("http.url", "https://api.example.com/data");
    
    tokio::time::sleep(Duration::from_millis(30)).await;
    api_span.set_status(StatusCode::Ok, "API call successful".to_string());
    api_span.end();
    
    root_span.set_status(StatusCode::Ok, "Request completed".to_string());
    root_span.end();
    
    println!("  ✅ 追踪数据已发送");
    Ok(())
}

// 指标收集示例
async fn demo_metrics(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let meter = client.meter("demo-metrics");
    
    // 创建计数器
    let request_counter = meter
        .u64_counter("requests_total")
        .with_description("Total number of requests")
        .with_unit(Unit::new("1"))
        .init();
    
    // 创建直方图
    let response_time_histogram = meter
        .f64_histogram("response_time_seconds")
        .with_description("Response time in seconds")
        .with_unit(Unit::new("s"))
        .init();
    
    // 记录一些指标
    for i in 0..10 {
        let mut attributes = HashMap::new();
        attributes.insert("method".to_string(), "GET".into());
        attributes.insert("status_code".to_string(), "200".into());
        
        request_counter.add(1, &attributes);
        
        let response_time = 0.1 + (i as f64 * 0.01);
        response_time_histogram.record(response_time, &attributes);
        
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    
    println!("  ✅ 指标数据已发送");
    Ok(())
}

// 日志记录示例
async fn demo_logging(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    use otlp::data::{LogData, LogSeverity, AttributeValue};
    
    let mut attributes = HashMap::new();
    attributes.insert("service.name".to_string(), AttributeValue::String("demo-app".to_string()));
    attributes.insert("user.id".to_string(), AttributeValue::String("12345".to_string()));
    attributes.insert("request.id".to_string(), AttributeValue::String("req-001".to_string()));
    
    let log_entries = vec![
        LogData {
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
            severity: LogSeverity::Info,
            body: "User login successful".to_string(),
            attributes: attributes.clone(),
            resource: None,
        },
        LogData {
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
            severity: LogSeverity::Warn,
            body: "High memory usage detected".to_string(),
            attributes: {
                let mut attrs = attributes.clone();
                attrs.insert("memory.usage".to_string(), AttributeValue::Double(85.5));
                attrs
            },
            resource: None,
        },
    ];
    
    client.export_logs(log_entries).await?;
    
    println!("  ✅ 日志数据已发送");
    Ok(())
}
```

### 运行完整示例

```bash
# 添加必要的依赖
cargo add tracing tracing-subscriber

# 运行示例
cargo run

# 预期输出:
# 🚀 启动完整的 OTLP 示例应用...
# 📊 演示分布式追踪...
#   ✅ 追踪数据已发送
# 📈 演示指标收集...
#   ✅ 指标数据已发送
# 📝 演示日志记录...
#   ✅ 日志数据已发送
# 🎉 所有示例运行完成！
```

---

## 🔥 进阶示例

### 1. 配置和优化

```rust
use otlp::{core::EnhancedOtlpClient, config::*};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 高级配置示例
    let retry_config = RetryConfig {
        max_attempts: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
    };
    
    let batch_config = BatchConfig {
        max_batch_size: 1000,
        batch_timeout: Duration::from_secs(5),
        max_queue_size: 10000,
        strategy: BatchStrategy::Hybrid,
    };
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("advanced-app")
        .with_retry_config(retry_config)
        .with_batch_config(batch_config)
        .with_compression(Compression::Gzip)
        .with_grpc_transport()
        .build()
        .await?;
    
    println!("✅ 高级配置的 OTLP 客户端创建成功！");
    Ok(())
}
```

### 2. 错误处理

```rust
use otlp::{core::EnhancedOtlpClient, error::OtlpError};

async fn robust_operation(client: &EnhancedOtlpClient) -> Result<(), OtlpError> {
    let tracer = client.tracer("robust-component");
    let mut span = tracer.start("robust-operation");
    
    match risky_operation().await {
        Ok(result) => {
            span.set_attribute("operation.status", "success");
            span.set_attribute("operation.result", result);
            span.set_status(opentelemetry::trace::StatusCode::Ok, "Operation successful".to_string());
            Ok(())
        }
        Err(e) => {
            span.set_attribute("operation.status", "error");
            span.set_attribute("error.message", e.to_string());
            span.set_status(opentelemetry::trace::StatusCode::Error, e.to_string());
            Err(e)
        }
    }
}

async fn risky_operation() -> Result<String, OtlpError> {
    // 模拟可能失败的操作
    if rand::random::<f64>() < 0.3 {
        Err(OtlpError::System("Random failure".to_string()))
    } else {
        Ok("Success".to_string())
    }
}
```

### 3. 性能监控

```rust
use otlp::core::EnhancedOtlpClient;
use std::time::Instant;

async fn monitored_operation(client: &EnhancedOtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = client.tracer("performance-monitor");
    let meter = client.meter("performance-metrics");
    
    let mut span = tracer.start("monitored-operation");
    let start_time = Instant::now();
    
    // 执行业务逻辑
    let result = business_logic().await?;
    
    let duration = start_time.elapsed();
    
    // 记录性能指标
    let duration_counter = meter
        .f64_histogram("operation_duration_seconds")
        .init();
    
    let mut attributes = HashMap::new();
    attributes.insert("operation.type".to_string(), "business_logic".into());
    
    duration_counter.record(duration.as_secs_f64(), &attributes);
    
    span.set_attribute("operation.duration_ms", duration.as_millis() as i64);
    span.set_attribute("operation.result", result);
    span.end();
    
    Ok(())
}

async fn business_logic() -> Result<String, Box<dyn std::error::Error>> {
    // 模拟业务逻辑
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok("Business logic completed".to_string())
}
```

---

## 📖 下一步学习

### 推荐学习路径

#### 1. 基础掌握（1-2天）

- ✅ 完成本快速入门教程
- 📖 阅读 [OTLP 客户端使用指南](otlp-client.md)
- 📖 阅读 [可靠性框架使用指南](reliability-framework.md)

#### 2. 进阶应用（3-5天）

- 📖 学习 [性能优化指南](performance-optimization.md)
- 📖 学习 [监控配置指南](monitoring.md)
- 🔧 实践 [基础示例](../examples/basic-examples.md)
- 🔧 实践 [高级示例](../examples/advanced-examples.md)

#### 3. 深入理解（1-2周）

- 📖 研究 [系统架构设计](../architecture/system-architecture.md)
- 📖 研究 [模块设计文档](../architecture/module-design.md)
- 📖 查看 [完整 API 参考](../api/otlp.md)
- 🔬 运行 [性能基准测试](../examples/benchmarks.md)

#### 4. 生产部署（1-2周）

- 🚀 学习 [微服务集成](../examples/microservices.md)
- 🔧 配置 [CI/CD 流程](../guides/deployment.md)
- 📊 设置 [监控和告警](../guides/monitoring.md)
- 🛡️ 实施 [安全最佳实践](../guides/security.md)

### 实践项目建议

#### 初级项目

1. **简单 Web 服务**: 创建一个带有 OTLP 追踪的 HTTP 服务
2. **数据库应用**: 集成数据库操作和指标收集
3. **API 客户端**: 构建带有重试和监控的 API 客户端

#### 中级项目

1. **微服务架构**: 构建多个服务间的分布式追踪
2. **批处理系统**: 实现高性能的数据处理管道
3. **实时监控**: 创建实时指标收集和告警系统

#### 高级项目

1. **云原生应用**: 在 Kubernetes 中部署可观测性系统
2. **边缘计算**: 在资源受限环境中优化 OTLP 性能
3. **多租户系统**: 实现隔离的遥测数据收集

### 社区资源

#### 官方文档

- [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
- [Rust OpenTelemetry 文档](https://docs.rs/opentelemetry/)
- [OTLP 协议规范](https://github.com/open-telemetry/opentelemetry-proto)

#### 学习资源

- [Rust 异步编程指南](https://rust-lang.github.io/async-book/)
- [Tokio 教程](https://tokio.rs/tokio/tutorial)
- [分布式追踪最佳实践](https://opentelemetry.io/docs/concepts/distributions/)

#### 社区支持

- [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
- [Stack Overflow](https://stackoverflow.com/questions/tagged/otlp-rust)
- [Rust 用户论坛](https://users.rust-lang.org/)

---

## ❓ 常见问题

### Q1: 客户端连接失败

**问题**: `error: failed to connect to http://localhost:4317`

**解决方案**:

```bash
# 启动 OTLP Collector（使用 Docker）
docker run -p 4317:4317 -p 4318:4318 \
  -v $(pwd)/otel-collector-config.yaml:/etc/otelcol-contrib/otel-collector-config.yaml \
  otel/opentelemetry-collector-contrib:latest

# 或者使用本地安装的 Collector
otelcol-contrib --config=otel-collector-config.yaml
```

### Q2: 数据没有发送

**问题**: 程序运行但没有看到数据

**解决方案**:

```rust
// 确保正确结束 span
span.end();

// 或者使用 drop 确保 span 被释放
drop(span);

// 添加显式刷新
client.flush().await?;
```

### Q3: 性能问题

**问题**: 程序运行缓慢

**解决方案**:

```rust
// 使用批处理配置
let batch_config = BatchConfig {
    max_batch_size: 1000,
    batch_timeout: Duration::from_secs(5),
    max_queue_size: 10000,
    strategy: BatchStrategy::Hybrid,
};

// 使用 gRPC 传输
let client = EnhancedOtlpClient::builder()
    .with_grpc_transport()
    .with_batch_config(batch_config)
    .build()
    .await?;
```

### Q4: 内存使用过高

**问题**: 程序内存占用过大

**解决方案**:

```rust
// 限制批处理大小
let batch_config = BatchConfig {
    max_batch_size: 100,  // 减小批处理大小
    batch_timeout: Duration::from_secs(1),  // 减少超时时间
    max_queue_size: 1000,  // 限制队列大小
    strategy: BatchStrategy::SizeBased,
};
```

### Q5: 编译错误

**问题**: `error: trait bound not satisfied`

**解决方案**:

```rust
// 确保添加了正确的依赖
cargo add tokio --features full
cargo add opentelemetry
cargo add tracing

// 检查 Cargo.toml 中的特性
[dependencies]
otlp = { path = "../crates/otlp", features = ["full"] }
```

---

## 🎉 总结

恭喜你完成了 OTLP Rust 的快速入门！你现在已经掌握了：

- ✅ **基础概念**: 了解 OTLP 的核心组件和数据流
- ✅ **第一个应用**: 成功创建并运行了 OTLP 客户端
- ✅ **完整示例**: 学会了追踪、指标和日志的使用
- ✅ **进阶技巧**: 掌握了配置、错误处理和性能监控
- ✅ **学习路径**: 知道了如何继续深入学习

### 下一步行动

1. 🔧 **实践项目**: 选择一个实践项目开始动手
2. 📖 **深入学习**: 阅读更详细的文档和指南
3. 🤝 **社区参与**: 加入社区讨论和贡献代码
4. 🚀 **生产部署**: 将学到的知识应用到实际项目中

记住，学习是一个持续的过程。不要害怕犯错，每个错误都是学习的机会！

---

*最后更新: 2025年10月20日*  
*教程版本: 1.0.0*
