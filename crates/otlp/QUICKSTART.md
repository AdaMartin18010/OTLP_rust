# OTLP Rust 快速开始指南

> **⚡ 5分钟快速上手** - 从零到第一个OTLP应用

---

## 📋 目录

- [OTLP Rust 快速开始指南](#otlp-rust-快速开始指南)
  - [📋 目录](#-目录)
  - [🎯 环境准备](#-环境准备)
    - [系统要求](#系统要求)
    - [安装Rust](#安装rust)
    - [启动OTLP后端 (可选)](#启动otlp后端-可选)
  - [📦 安装](#-安装)
    - [创建新项目](#创建新项目)
    - [添加依赖](#添加依赖)
  - [🚀 第一个应用](#-第一个应用)
    - [基础示例](#基础示例)
    - [运行程序](#运行程序)
  - [💡 核心概念](#-核心概念)
    - [1. 遥测数据类型](#1-遥测数据类型)
      - [Traces (追踪)](#traces-追踪)
      - [Metrics (指标)](#metrics-指标)
      - [Logs (日志)](#logs-日志)
    - [2. 配置选项](#2-配置选项)
      - [基础配置](#基础配置)
      - [完整配置](#完整配置)
    - [3. 错误处理](#3-错误处理)
  - [🎯 常见使用场景](#-常见使用场景)
    - [场景1: Web API追踪](#场景1-web-api追踪)
    - [场景2: 后台任务监控](#场景2-后台任务监控)
    - [场景3: 微服务通信追踪](#场景3-微服务通信追踪)
  - [📚 下一步](#-下一步)
    - [学习更多](#学习更多)
    - [运行示例](#运行示例)
    - [文档资源](#文档资源)
    - [社区支持](#社区支持)
  - [❓ 常见问题](#-常见问题)
    - [Q1: 如何处理连接失败?](#q1-如何处理连接失败)
    - [Q2: 如何在生产环境使用?](#q2-如何在生产环境使用)
    - [Q3: 如何优化性能?](#q3-如何优化性能)
    - [Q4: 支持哪些后端?](#q4-支持哪些后端)
  - [🎉 恭喜](#-恭喜)

---

## 🎯 环境准备

### 系统要求

```text
✓ Rust 1.90 或更高版本
✓ 支持异步运行时的操作系统
✓ OTLP后端 (如 Jaeger, Prometheus, OpenTelemetry Collector)
```

### 安装Rust

如果还没有安装Rust:

```bash
# Linux / macOS
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Windows
# 访问 https://rustup.rs/ 下载安装程序
```

验证安装:

```bash
rustc --version
# 应显示: rustc 1.90.0 或更高
```

### 启动OTLP后端 (可选)

使用Docker快速启动Jaeger:

```bash
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 16686:16686 \
  -p 4317:4317 \
  -p 4318:4318 \
  jaegertracing/all-in-one:latest
```

访问 Jaeger UI: <http://localhost:16686>

---

## 📦 安装

### 创建新项目

```bash
cargo new my-otlp-app
cd my-otlp-app
```

### 添加依赖

编辑 `Cargo.toml`:

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
anyhow = "1.0"
```

---

## 🚀 第一个应用

### 基础示例

创建 `src/main.rs`:

```rust
use otlp::{OtlpClient, OtlpConfig};
use otlp::data::{LogSeverity, StatusCode};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 OTLP快速开始示例\n");
    
    // 1. 创建配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")  // Jaeger OTLP endpoint
        .with_service("my-app", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 2. 创建客户端
    let client = OtlpClient::new(config).await?;
    println!("✅ OTLP客户端已初始化");
    
    // 3. 发送追踪数据
    println!("\n📊 发送追踪数据...");
    let trace_result = client.send_trace("user_login").await?
        .with_attribute("user_id", "12345")
        .with_attribute("username", "alice")
        .with_numeric_attribute("duration_ms", 150.0)
        .with_status(StatusCode::Ok, Some("登录成功".to_string()))
        .finish()
        .await?;
    
    println!("   成功发送 {} 条追踪数据", trace_result.success_count);
    println!("   Trace ID: {}", trace_result.trace_id);
    println!("   Span ID: {}", trace_result.span_id);
    
    // 4. 发送指标数据
    println!("\n📈 发送指标数据...");
    let metric_result = client.send_metric("login_count", 1.0).await?
        .with_label("status", "success")
        .with_label("method", "password")
        .with_description("用户登录计数")
        .with_unit("count")
        .send()
        .await?;
    
    println!("   成功发送 {} 条指标数据", metric_result.success_count);
    
    // 5. 发送日志数据
    println!("\n📝 发送日志数据...");
    let log_result = client.send_log("用户登录成功", LogSeverity::Info).await?
        .with_attribute("user_id", "12345")
        .with_attribute("ip_address", "192.168.1.100")
        .with_trace_context(&trace_result.trace_id, &trace_result.span_id)
        .send()
        .await?;
    
    println!("   成功发送 {} 条日志数据", log_result.success_count);
    
    // 6. 刷新缓冲区
    println!("\n🔄 刷新缓冲区...");
    client.flush().await?;
    println!("   ✅ 所有数据已发送");
    
    // 7. 关闭客户端
    println!("\n👋 关闭客户端...");
    client.shutdown().await?;
    
    println!("\n🎉 示例完成！");
    println!("   访问 http://localhost:16686 查看追踪数据");
    
    Ok(())
}
```

### 运行程序

```bash
cargo run
```

**预期输出**:

```text
🚀 OTLP快速开始示例

✅ OTLP客户端已初始化

📊 发送追踪数据...
   成功发送 1 条追踪数据
   Trace ID: 7f3d9c8b-1a2e-4f5c-9d8a-6b7e8f9a0c1d
   Span ID: 1a2b3c4d5e6f7g8h

📈 发送指标数据...
   成功发送 1 条指标数据

📝 发送日志数据...
   成功发送 1 条日志数据

🔄 刷新缓冲区...
   ✅ 所有数据已发送

👋 关闭客户端...

🎉 示例完成！
   访问 http://localhost:16686 查看追踪数据
```

---

## 💡 核心概念

### 1. 遥测数据类型

OTLP支持三种类型的遥测数据:

#### Traces (追踪)

追踪请求在分布式系统中的流转路径。

```rust
client.send_trace("operation_name").await?
    .with_attribute("key", "value")
    .with_status(StatusCode::Ok, Some("成功".to_string()))
    .finish()
    .await?;
```

#### Metrics (指标)

记录系统的数值测量。

```rust
client.send_metric("request_count", 1.0).await?
    .with_label("endpoint", "/api/users")
    .with_unit("count")
    .send()
    .await?;
```

#### Logs (日志)

记录应用事件和诊断信息。

```rust
client.send_log("用户登录", LogSeverity::Info).await?
    .with_attribute("user_id", "12345")
    .send()
    .await?;
```

### 2. 配置选项

#### 基础配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_service("my-service", "1.0.0");
```

#### 完整配置

```rust
use otlp::transport::TransportProtocol;
use std::time::Duration;

let config = OtlpConfig::default()
    // 基础配置
    .with_endpoint("http://localhost:4317")
    .with_service("my-service", "1.0.0")
    .with_protocol(TransportProtocol::Grpc)
    
    // 超时配置
    .with_timeout(Duration::from_secs(10))
    .with_connect_timeout(Duration::from_secs(5))
    
    // 批处理配置
    .with_batch_size(100)
    .with_batch_timeout(Duration::from_secs(5))
    
    // 资源属性
    .with_resource_attribute("environment", "production")
    .with_resource_attribute("region", "us-east-1");
```

### 3. 错误处理

```rust
use otlp::error::{OtlpError, ErrorContext};

match client.send_trace("operation").await {
    Ok(result) => {
        println!("成功: {}", result.success_count);
    },
    Err(OtlpError::Timeout { operation, timeout }) => {
        eprintln!("操作 {} 超时 ({}ms)", operation, timeout.as_millis());
    },
    Err(OtlpError::Transport(e)) => {
        eprintln!("传输错误: {}", e);
        // 实现重试逻辑
    },
    Err(e) => {
        eprintln!("其他错误: {}", e);
    }
}
```

---

## 🎯 常见使用场景

### 场景1: Web API追踪

```rust
use otlp::{OtlpClient, OtlpConfig};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Arc::new(OtlpClient::new(
        OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_service("api-server", "1.0.0")
    ).await?);
    
    // 模拟HTTP请求处理
    handle_request(&client, "GET", "/api/users").await?;
    
    Ok(())
}

async fn handle_request(
    client: &OtlpClient,
    method: &str,
    path: &str
) -> Result<(), Box<dyn std::error::Error>> {
    // 创建请求追踪
    let trace = client.send_trace(&format!("{} {}", method, path)).await?
        .with_attribute("http.method", method)
        .with_attribute("http.path", path)
        .with_attribute("http.status_code", "200");
    
    // 模拟数据库查询
    let db_trace = client.send_trace("database_query").await?
        .with_attribute("db.system", "postgresql")
        .with_attribute("db.statement", "SELECT * FROM users");
    
    // 模拟处理
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    db_trace.finish().await?;
    trace.finish().await?;
    
    // 记录指标
    client.send_metric("http_requests_total", 1.0).await?
        .with_label("method", method)
        .with_label("path", path)
        .with_label("status", "200")
        .send()
        .await?;
    
    Ok(())
}
```

### 场景2: 后台任务监控

```rust
use otlp::{OtlpClient, OtlpConfig};
use otlp::data::LogSeverity;

async fn process_job(
    client: &OtlpClient,
    job_id: &str
) -> Result<(), Box<dyn std::error::Error>> {
    // 开始任务追踪
    let trace = client.send_trace("background_job").await?
        .with_attribute("job.id", job_id)
        .with_attribute("job.type", "data_processing");
    
    client.send_log(&format!("开始处理任务: {}", job_id), LogSeverity::Info).await?
        .with_attribute("job.id", job_id)
        .send()
        .await?;
    
    // 处理逻辑
    let start = std::time::Instant::now();
    
    // 模拟处理
    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
    
    let duration = start.elapsed();
    
    // 记录完成
    trace.with_numeric_attribute("duration_ms", duration.as_millis() as f64)
        .with_attribute("status", "completed")
        .finish()
        .await?;
    
    client.send_log(&format!("任务完成: {}", job_id), LogSeverity::Info).await?
        .with_attribute("job.id", job_id)
        .with_numeric_attribute("duration_ms", duration.as_millis() as f64)
        .send()
        .await?;
    
    // 记录处理时长指标
    client.send_metric("job_duration_seconds", duration.as_secs_f64()).await?
        .with_label("job_type", "data_processing")
        .with_label("status", "completed")
        .send()
        .await?;
    
    Ok(())
}
```

### 场景3: 微服务通信追踪

```rust
use otlp::{OtlpClient, OtlpConfig};
use std::sync::Arc;

// 服务A: 用户服务
async fn user_service_handler(
    client: &OtlpClient
) -> Result<(String, String), Box<dyn std::error::Error>> {
    let trace = client.send_trace("user_service.get_user").await?
        .with_attribute("service", "user-service");
    
    // 返回trace_id和span_id用于传递
    let trace_id = trace.trace_id.clone();
    let span_id = trace.span_id.clone();
    
    // 处理
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    trace.finish().await?;
    
    Ok((trace_id, span_id))
}

// 服务B: 订单服务
async fn order_service_handler(
    client: &OtlpClient,
    parent_trace_id: &str,
    parent_span_id: &str
) -> Result<(), Box<dyn std::error::Error>> {
    let trace = client.send_trace("order_service.create_order").await?
        .with_attribute("service", "order-service")
        .with_attribute("parent_trace_id", parent_trace_id)
        .with_attribute("parent_span_id", parent_span_id);
    
    // 处理
    tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;
    
    trace.finish().await?;
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Arc::new(OtlpClient::new(
        OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_service("microservices-demo", "1.0.0")
    ).await?);
    
    // 调用服务A
    let (trace_id, span_id) = user_service_handler(&client).await?;
    
    // 传递上下文到服务B
    order_service_handler(&client, &trace_id, &span_id).await?;
    
    client.shutdown().await?;
    Ok(())
}
```

---

## 📚 下一步

### 学习更多

1. **理论基础**
   - 📖 [理论框架总导航](../docs/OTLP_THEORETICAL_FRAMEWORK_INDEX.md)
   - 💡 [理论到实践指南](THEORY_TO_PRACTICE_GUIDE.md)

2. **进阶功能**
   - 🛡️ [弹性机制使用](examples/resilience_usage.rs)
   - ⚡ [性能优化示例](examples/performance_demo.rs)
   - 📊 [监控集成](examples/monitoring_demo.rs)

3. **实际应用**
   - 🏢 [微服务示例](examples/microservices_demo.rs)
   - 🔧 [完整应用示例](examples/comprehensive_demo.rs)

### 运行示例

```bash
# 查看所有示例
ls examples/

# 运行简单示例
cargo run --example simple_demo

# 运行性能示例
cargo run --example performance_demo

# 运行微服务示例
cargo run --example microservices_demo
```

### 文档资源

- 📘 [API参考](API_REFERENCE.md)
- 📗 [部署指南](DEPLOYMENT_GUIDE.md)
- 🚀 [集成概览](COMPREHENSIVE_INTEGRATION_OVERVIEW.md)
- 🗺️ [项目路线图](PROJECT_PROGRESS_ROADMAP_2025_10_08.md)

### 社区支持

- 💬 [GitHub Issues](https://github.com/your-org/otlp-rust/issues)
- 📧 Email: <support@otlp-rust.com>
- 💡 [Discussions](https://github.com/your-org/otlp-rust/discussions)

---

## ❓ 常见问题

### Q1: 如何处理连接失败?

**A**: OTLP客户端内置了自动重试机制:

```rust
use otlp::resilience::retry::{RetryStrategy, ExponentialBackoff};
use std::time::Duration;

let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_service("my-service", "1.0.0")
    .with_retry_strategy(RetryStrategy::ExponentialBackoff(
        ExponentialBackoff {
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
            max_retries: 3,
            jitter: true,
        }
    ));
```

### Q2: 如何在生产环境使用?

**A**: 建议配置:

```rust
let config = OtlpConfig::default()
    .with_endpoint("https://otlp-collector.example.com:4317")
    .with_service("production-service", "1.0.0")
    
    // 启用TLS
    .with_tls(true)
    
    // 配置超时
    .with_timeout(Duration::from_secs(10))
    
    // 批处理优化
    .with_batch_size(1000)
    .with_batch_timeout(Duration::from_secs(5))
    
    // 启用压缩
    .with_compression(true)
    
    // 资源标签
    .with_resource_attribute("environment", "production")
    .with_resource_attribute("region", "us-east-1")
    .with_resource_attribute("instance_id", &instance_id);
```

### Q3: 如何优化性能?

**A**: 多种优化方案:

1. **批处理**: 增大batch_size减少网络请求
2. **压缩**: 启用gzip压缩
3. **异步**: 使用异步API避免阻塞
4. **连接池**: 客户端内置连接池
5. **采样**: 对于高流量服务，使用采样减少数据量

### Q4: 支持哪些后端?

**A**: 所有支持OTLP协议的后端:

- ✅ Jaeger
- ✅ Zipkin (通过OTLP Collector)
- ✅ Prometheus
- ✅ OpenTelemetry Collector
- ✅ Grafana Tempo
- ✅ DataDog (通过OTLP)
- ✅ New Relic (通过OTLP)

---

## 🎉 恭喜

你已经掌握了OTLP Rust的基础使用！

**接下来可以**:

1. 在你的项目中集成OTLP
2. 探索高级特性 (弹性、性能优化、监控)
3. 深入学习理论框架

**需要帮助?**

- 查看[文档](README.md)
- 提交[Issue](https://github.com/your-org/otlp-rust/issues)
- 加入[讨论](https://github.com/your-org/otlp-rust/discussions)

**开始你的可观测性之旅吧！** 🚀

---

*最后更新: 2025年10月8日*  
*版本: 1.0.0*
