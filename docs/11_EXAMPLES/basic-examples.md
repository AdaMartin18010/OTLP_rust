# 📚 基础示例

**版本**: 1.0
**最后更新**: 2025年10月26日
**难度**: ⭐ 入门
**预计时间**: 2-3小时
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 基础示例 - 7个循序渐进的示例，从 Hello World 到完整应用。

---

## 📋 目录

- [📚 基础示例](#-基础示例)
  - [📋 目录](#-目录)
  - [🎯 示例概览](#-示例概览)
    - [示例分类](#示例分类)
  - [🌍 Hello World](#-hello-world)
    - [最简单的 OTLP 客户端](#最简单的-otlp-客户端)
    - [运行步骤](#运行步骤)
    - [预期输出](#预期输出)
    - [常见问题](#常见问题)
  - [📊 基础追踪](#-基础追踪)
    - [创建和管理 Span](#创建和管理-span)
    - [运行示例](#运行示例)
    - [预期输出1](#预期输出1)
    - [关键概念](#关键概念)
  - [📈 指标收集](#-指标收集)
    - [计数器和直方图](#计数器和直方图)
    - [运行示例1](#运行示例1)
    - [预期输出2](#预期输出2)
    - [指标类型](#指标类型)
  - [📝 日志记录](#-日志记录)
    - [结构化日志](#结构化日志)
    - [运行示例3](#运行示例3)
    - [预期输出3](#预期输出3)
    - [日志级别](#日志级别)
  - [⚠️ 错误处理](#️-错误处理)
    - [错误处理和恢复](#错误处理和恢复)
    - [运行示例4](#运行示例4)
    - [预期输出4](#预期输出4)
  - [⚙️ 配置示例](#️-配置示例)
    - [高级配置选项](#高级配置选项)
    - [运行示例5](#运行示例5)
    - [预期输出5](#预期输出5)
  - [🎯 完整应用](#-完整应用)
    - [综合示例](#综合示例)
    - [运行示例7](#运行示例7)
    - [预期输出7](#预期输出7)
  - [🚀 下一步](#-下一步)
    - [学习路径](#学习路径)
    - [实践建议](#实践建议)
    - [获取帮助](#获取帮助)

---

## 🎯 示例概览

本部分提供了 OTLP Rust 项目的基础使用示例，适合初学者快速上手。所有示例都包含：

- ✅ 完整的可运行代码
- ✅ 详细的注释说明
- ✅ 预期的输出结果
- ✅ 常见问题解答

### 示例分类

| 示例 | 难度 | 预计时间 | 主要功能 |
|------|------|----------|----------|
| Hello World | ⭐ | 5分钟 | 基础客户端创建 |
| 基础追踪 | ⭐⭐ | 10分钟 | Span 创建和管理 |
| 指标收集 | ⭐⭐ | 10分钟 | 计数器和直方图 |
| 日志记录 | ⭐⭐ | 10分钟 | 结构化日志 |
| 错误处理 | ⭐⭐⭐ | 15分钟 | 错误处理和恢复 |
| 配置示例 | ⭐⭐⭐ | 15分钟 | 高级配置选项 |
| 完整应用 | ⭐⭐⭐⭐ | 30分钟 | 综合应用示例 |

---

## 🌍 Hello World

### 最简单的 OTLP 客户端

这是最基础的示例，展示如何创建和初始化 OTLP 客户端。

```rust
use otlp::core::EnhancedOtlpClient;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Hello OTLP World!");

    // 创建 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("hello-world")
        .with_service_version("1.0.0")
        .with_http_transport()
        .with_connect_timeout(Duration::from_secs(5))
        .build()
        .await?;

    println!("✅ OTLP 客户端创建成功！");
    println!("📊 服务名称: hello-world");
    println!("🌐 端点: http://localhost:4317");

    Ok(())
}
```

### 运行步骤

1. **创建项目**:

    ```bash
    cargo new hello_otlp
    cd hello_otlp
    ```

2. **添加依赖**:

    ```bash
    cargo add --path ../crates/otlp
    cargo add tokio --features full
    ```

3. **运行示例**:

    ```bash
    cargo run
    ```

### 预期输出

```text
🚀 Hello OTLP World!
✅ OTLP 客户端创建成功！
📊 服务名称: hello-world
🌐 端点: http://localhost:4317
```

### 常见问题

**Q: 为什么没有发送数据？**
A: 这个示例只是创建客户端，没有实际发送数据。继续看下面的示例学习如何发送数据。

---

## 📊 基础追踪

### 创建和管理 Span

这个示例展示如何创建 Span 并添加属性。

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::trace::{Tracer, SpanKind, StatusCode};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("📊 基础追踪示例");

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("tracing-demo")
        .build()
        .await?;

    // 创建追踪器
    let tracer = client.tracer("main-component");

    // 创建根 Span
    let mut root_span = tracer.start_with_kind("user-request", SpanKind::Server);

    // 添加属性
    root_span.set_attribute("user.id", "12345");
    root_span.set_attribute("request.method", "GET");
    root_span.set_attribute("request.path", "/api/users");
    root_span.set_attribute("request.size", 1024);

    println!("🔍 开始处理用户请求...");

    // 模拟处理时间
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 创建子 Span
    let mut db_span = tracer.start_with_kind("database-query", SpanKind::Client);
    db_span.set_attribute("db.system", "postgresql");
    db_span.set_attribute("db.operation", "SELECT");
    db_span.set_attribute("db.table", "users");

    println!("🗄️ 执行数据库查询...");
    tokio::time::sleep(Duration::from_millis(50)).await;

    // 设置 Span 状态
    db_span.set_status(StatusCode::Ok, "Query successful".to_string());
    db_span.end();

    // 创建另一个子 Span
    let mut cache_span = tracer.start_with_kind("cache-operation", SpanKind::Client);
    cache_span.set_attribute("cache.operation", "GET");
    cache_span.set_attribute("cache.key", "user:12345");

    println!("💾 检查缓存...");
    tokio::time::sleep(Duration::from_millis(20)).await;

    cache_span.set_status(StatusCode::Ok, "Cache hit".to_string());
    cache_span.end();

    // 完成根 Span
    root_span.set_status(StatusCode::Ok, "Request completed successfully".to_string());
    root_span.end();

    println!("✅ 追踪数据已发送");
    Ok(())
}
```

### 运行示例

```bash
cargo run
```

### 预期输出1

```text
📊 基础追踪示例
🔍 开始处理用户请求...
🗄️ 执行数据库查询...
💾 检查缓存...
✅ 追踪数据已发送
```

### 关键概念

- **Span**: 表示操作的一个单元，有开始和结束时间
- **属性**: 键值对，提供 Span 的上下文信息
- **状态**: Span 的执行结果（成功/失败）
- **父子关系**: Span 可以嵌套，形成调用链

---

## 📈 指标收集

### 计数器和直方图

这个示例展示如何收集不同类型的指标。

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::metrics::{Meter, Counter, Histogram, Unit};
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("📈 指标收集示例");

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("metrics-demo")
        .build()
        .await?;

    // 创建指标收集器
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

    // 创建仪表盘
    let active_connections_gauge = meter
        .i64_up_down_counter("active_connections")
        .with_description("Number of active connections")
        .with_unit(Unit::new("1"))
        .init();

    println!("📊 开始收集指标...");

    // 模拟请求处理
    for i in 0..20 {
        let mut attributes = HashMap::new();
        attributes.insert("method".to_string(), "GET".into());
        attributes.insert("endpoint".to_string(), "/api/users".into());
        attributes.insert("status_code".to_string(), "200".into());

        // 增加请求计数
        request_counter.add(1, &attributes);

        // 模拟响应时间
        let response_time = 0.05 + (i as f64 * 0.01) + (rand::random::<f64>() * 0.02);
        response_time_histogram.record(response_time, &attributes);

        // 更新连接数
        let connections = 10 + (i % 5);
        active_connections_gauge.add(connections, &attributes);

        println!("📊 处理请求 {}: 响应时间 {:.3}s, 连接数 {}",
                i + 1, response_time, connections);

        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    println!("✅ 指标数据已发送");
    Ok(())
}
```

### 运行示例1

```bash
# 添加随机数依赖
cargo add rand

cargo run
```

### 预期输出2

```text
📈 指标收集示例
📊 开始收集指标...
📊 处理请求 1: 响应时间 0.067s, 连接数 10
📊 处理请求 2: 响应时间 0.078s, 连接数 11
📊 处理请求 3: 响应时间 0.089s, 连接数 12
...
📊 处理请求 20: 响应时间 0.245s, 连接数 14
✅ 指标数据已发送
```

### 指标类型

- **Counter**: 只增不减的计数器
- **Histogram**: 记录数值分布
- **Gauge**: 可增可减的仪表盘

---

## 📝 日志记录

### 结构化日志

这个示例展示如何发送结构化日志数据。

```rust
use otlp::core::EnhancedOtlpClient;
use otlp::data::{LogData, LogSeverity, AttributeValue};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("📝 日志记录示例");

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("logging-demo")
        .build()
        .await?;

    // 创建日志条目
    let mut logs = Vec::new();

    // 信息日志
    let mut info_attributes = HashMap::new();
    info_attributes.insert("user.id".to_string(), AttributeValue::String("12345".to_string()));
    info_attributes.insert("action".to_string(), AttributeValue::String("login".to_string()));
    info_attributes.insert("ip_address".to_string(), AttributeValue::String("192.168.1.100".to_string()));

    logs.push(LogData {
        timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
        severity: LogSeverity::Info,
        body: "User login successful".to_string(),
        attributes: info_attributes,
        resource: None,
    });

    // 警告日志
    let mut warn_attributes = HashMap::new();
    warn_attributes.insert("component".to_string(), AttributeValue::String("database".to_string()));
    warn_attributes.insert("query_time".to_string(), AttributeValue::Double(2.5));
    warn_attributes.insert("threshold".to_string(), AttributeValue::Double(1.0));

    logs.push(LogData {
        timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
        severity: LogSeverity::Warn,
        body: "Slow database query detected".to_string(),
        attributes: warn_attributes,
        resource: None,
    });

    // 错误日志
    let mut error_attributes = HashMap::new();
    error_attributes.insert("error.type".to_string(), AttributeValue::String("ValidationError".to_string()));
    error_attributes.insert("error.code".to_string(), AttributeValue::String("INVALID_EMAIL".to_string()));
    error_attributes.insert("field".to_string(), AttributeValue::String("email".to_string()));
    error_attributes.insert("value".to_string(), AttributeValue::String("invalid-email".to_string()));

    logs.push(LogData {
        timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
        severity: LogSeverity::Error,
        body: "Validation failed for email field".to_string(),
        attributes: error_attributes,
        resource: None,
    });

    // 调试日志
    let mut debug_attributes = HashMap::new();
    debug_attributes.insert("function".to_string(), AttributeValue::String("process_payment".to_string()));
    debug_attributes.insert("step".to_string(), AttributeValue::String("validate_card".to_string()));
    debug_attributes.insert("card_type".to_string(), AttributeValue::String("visa".to_string()));

    logs.push(LogData {
        timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
        severity: LogSeverity::Debug,
        body: "Processing payment validation".to_string(),
        attributes: debug_attributes,
        resource: None,
    });

    println!("📤 发送日志数据...");

    // 发送日志
    client.export_logs(logs).await?;

    println!("✅ 日志数据已发送");
    Ok(())
}
```

### 运行示例3

```bash
cargo run
```

### 预期输出3

```text
📝 日志记录示例
📤 发送日志数据...
✅ 日志数据已发送
```

### 日志级别

- **Debug**: 调试信息
- **Info**: 一般信息
- **Warn**: 警告信息
- **Error**: 错误信息
- **Fatal**: 严重错误

---

## ⚠️ 错误处理

### 错误处理和恢复

这个示例展示如何处理各种错误情况。

```rust
use otlp::{core::EnhancedOtlpClient, error::OtlpError};
use opentelemetry::trace::{Tracer, StatusCode};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("⚠️ 错误处理示例");

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("error-handling-demo")
        .build()
        .await?;

    let tracer = client.tracer("error-handler");

    // 示例 1: 处理网络错误
    println!("🌐 测试网络错误处理...");
    match simulate_network_error().await {
        Ok(result) => println!("✅ 网络操作成功: {}", result),
        Err(e) => {
            println!("❌ 网络操作失败: {}", e);
            log_error(&tracer, "network_error", &e).await;
        }
    }

    // 示例 2: 处理业务逻辑错误
    println!("💼 测试业务逻辑错误处理...");
    match simulate_business_error().await {
        Ok(result) => println!("✅ 业务操作成功: {}", result),
        Err(e) => {
            println!("❌ 业务操作失败: {}", e);
            log_error(&tracer, "business_error", &e).await;
        }
    }

    // 示例 3: 处理超时错误
    println!("⏰ 测试超时错误处理...");
    match simulate_timeout_error().await {
        Ok(result) => println!("✅ 超时操作成功: {}", result),
        Err(e) => {
            println!("❌ 超时操作失败: {}", e);
            log_error(&tracer, "timeout_error", &e).await;
        }
    }

    println!("✅ 错误处理示例完成");
    Ok(())
}

async fn simulate_network_error() -> Result<String, OtlpError> {
    // 模拟网络错误
    if rand::random::<f64>() < 0.5 {
        Err(OtlpError::Network("Connection timeout".to_string()))
    } else {
        Ok("Network operation successful".to_string())
    }
}

async fn simulate_business_error() -> Result<String, OtlpError> {
    // 模拟业务逻辑错误
    if rand::random::<f64>() < 0.3 {
        Err(OtlpError::System("Invalid user input".to_string()))
    } else {
        Ok("Business operation successful".to_string())
    }
}

async fn simulate_timeout_error() -> Result<String, OtlpError> {
    // 模拟超时错误
    tokio::time::sleep(Duration::from_millis(100)).await;
    if rand::random::<f64>() < 0.4 {
        Err(OtlpError::Timeout("Operation timed out".to_string()))
    } else {
        Ok("Timeout operation successful".to_string())
    }
}

async fn log_error(tracer: &Tracer, error_type: &str, error: &OtlpError) {
    let mut span = tracer.start("error-handling");

    span.set_attribute("error.type", error_type);
    span.set_attribute("error.message", error.to_string());
    span.set_attribute("error.timestamp", chrono::Utc::now().timestamp());

    span.set_status(StatusCode::Error, error.to_string());
    span.end();
}
```

### 运行示例4

```bash
# 添加时间处理依赖
cargo add chrono

cargo run
```

### 预期输出4

```text
⚠️ 错误处理示例
🌐 测试网络错误处理...
❌ 网络操作失败: Network error: Connection timeout
💼 测试业务逻辑错误处理...
✅ 业务操作成功: Business operation successful
⏰ 测试超时错误处理...
❌ 超时操作失败: Timeout error: Operation timed out
✅ 错误处理示例完成
```

---

## ⚙️ 配置示例

### 高级配置选项

这个示例展示如何使用各种配置选项。

```rust
use otlp::{core::EnhancedOtlpClient, config::*};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("⚙️ 配置示例");

    // 重试配置
    let retry_config = RetryConfig {
        max_attempts: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
    };

    // 批处理配置
    let batch_config = BatchConfig {
        max_batch_size: 1000,
        batch_timeout: Duration::from_secs(5),
        max_queue_size: 10000,
        strategy: BatchStrategy::Hybrid,
    };

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("config-demo")
        .with_service_version("1.0.0")
        .with_retry_config(retry_config)
        .with_batch_config(batch_config)
        .with_compression(Compression::Gzip)
        .with_grpc_transport()
        .with_connect_timeout(Duration::from_secs(10))
        .with_request_timeout(Duration::from_secs(30))
        .build()
        .await?;

    println!("✅ 高级配置的客户端创建成功");
    println!("🔄 重试配置: 最多 3 次重试");
    println!("📦 批处理配置: 最大批次 1000 条");
    println!("🗜️ 压缩: Gzip");
    println!("🌐 传输: gRPC");

    Ok(())
}
```

### 运行示例5

```bash
cargo run
```

### 预期输出5

```text
⚙️ 配置示例
✅ 高级配置的客户端创建成功
🔄 重试配置: 最多 3 次重试
📦 批处理配置: 最大批次 1000 条
🗜️ 压缩: Gzip
🌐 传输: gRPC
```

---

## 🎯 完整应用

### 综合示例

这是一个完整的应用示例，展示了 OTLP 的所有主要功能。

```rust
use otlp::core::EnhancedOtlpClient;
use otlp::data::{LogData, LogSeverity, AttributeValue};
use opentelemetry::trace::{Tracer, SpanKind, StatusCode};
use opentelemetry::metrics::{Meter, Counter, Histogram, Unit};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🎯 完整应用示例");

    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("complete-demo")
        .with_service_version("1.0.0")
        .with_http_transport()
        .build()
        .await?;

    let tracer = client.tracer("main-component");
    let meter = client.meter("main-metrics");

    // 创建指标
    let request_counter = meter
        .u64_counter("requests_total")
        .with_description("Total requests")
        .init();

    let response_time_histogram = meter
        .f64_histogram("response_time_seconds")
        .with_description("Response time")
        .init();

    // 模拟处理多个请求
    for i in 0..5 {
        println!("📊 处理请求 {}...", i + 1);

        let start_time = SystemTime::now();
        let mut root_span = tracer.start_with_kind("user-request", SpanKind::Server);

        root_span.set_attribute("request.id", format!("req-{}", i + 1));
        root_span.set_attribute("user.id", "12345");

        // 模拟业务逻辑
        let result = process_request(&tracer, &meter, i + 1).await;

        let duration = start_time.elapsed();

        // 记录指标
        let mut attributes = HashMap::new();
        attributes.insert("method".to_string(), "GET".into());
        attributes.insert("status".to_string(), "200".into());

        request_counter.add(1, &attributes);
        response_time_histogram.record(duration.as_secs_f64(), &attributes);

        // 记录日志
        let mut log_attributes = HashMap::new();
        log_attributes.insert("request.id".to_string(), AttributeValue::String(format!("req-{}", i + 1)));
        log_attributes.insert("duration_ms".to_string(), AttributeValue::Int64(duration.as_millis() as i64));

        let logs = vec![LogData {
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
            severity: if result.is_ok() { LogSeverity::Info } else { LogSeverity::Error },
            body: format!("Request {} completed", i + 1),
            attributes: log_attributes,
            resource: None,
        }];

        client.export_logs(logs).await?;

        // 完成 Span
        match result {
            Ok(_) => {
                root_span.set_status(StatusCode::Ok, "Request successful".to_string());
                println!("✅ 请求 {} 处理成功", i + 1);
            }
            Err(e) => {
                root_span.set_status(StatusCode::Error, e.to_string());
                println!("❌ 请求 {} 处理失败: {}", i + 1, e);
            }
        }

        root_span.end();

        tokio::time::sleep(Duration::from_millis(200)).await;
    }

    println!("🎉 完整应用示例运行完成");
    Ok(())
}

async fn process_request(
    tracer: &Tracer,
    meter: &Meter,
    request_id: u32,
) -> Result<String, Box<dyn std::error::Error>> {
    // 数据库查询
    let mut db_span = tracer.start_with_kind("database-query", SpanKind::Client);
    db_span.set_attribute("db.operation", "SELECT");
    db_span.set_attribute("db.table", "users");

    tokio::time::sleep(Duration::from_millis(50)).await;

    // 模拟偶尔的数据库错误
    if rand::random::<f64>() < 0.1 {
        db_span.set_status(StatusCode::Error, "Database connection failed".to_string());
        db_span.end();
        return Err("Database error".into());
    }

    db_span.set_status(StatusCode::Ok, "Query successful".to_string());
    db_span.end();

    // 外部 API 调用
    let mut api_span = tracer.start_with_kind("external-api", SpanKind::Client);
    api_span.set_attribute("http.method", "GET");
    api_span.set_attribute("http.url", "https://api.example.com/data");

    tokio::time::sleep(Duration::from_millis(30)).await;

    // 模拟偶尔的 API 错误
    if rand::random::<f64>() < 0.05 {
        api_span.set_status(StatusCode::Error, "API call failed".to_string());
        api_span.end();
        return Err("API error".into());
    }

    api_span.set_status(StatusCode::Ok, "API call successful".to_string());
    api_span.end();

    Ok(format!("Request {} processed successfully", request_id))
}
```

### 运行示例7

```bash
cargo run
```

### 预期输出7

```text
🎯 完整应用示例
📊 处理请求 1...
✅ 请求 1 处理成功
📊 处理请求 2...
✅ 请求 2 处理成功
📊 处理请求 3...
❌ 请求 3 处理失败: Database error
📊 处理请求 4...
✅ 请求 4 处理成功
📊 处理请求 5...
✅ 请求 5 处理成功
🎉 完整应用示例运行完成
```

---

## 🚀 下一步

### 学习路径

1. **掌握基础**: 完成所有基础示例
2. **进阶学习**: 查看 [高级示例](advanced-examples.md)
3. **性能优化**: 学习 [性能优化指南](../guides/performance-optimization.md)
4. **生产部署**: 参考 [部署指南](../guides/deployment.md)

### 实践建议

1. **修改示例**: 尝试修改示例代码，添加自己的功能
2. **集成项目**: 将 OTLP 集成到现有项目中
3. **监控系统**: 设置完整的监控和告警系统
4. **性能测试**: 运行基准测试，优化性能

### 获取帮助

- 📖 [完整文档](../README.md)
- 💬 [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
- 🏠 [项目主页](https://github.com/your-org/OTLP_rust)

---

_最后更新: 2025年10月20日_
_示例版本: 1.0.0_
