# 🚀 Rust OTLP 30分钟快速入门教程

> **目标读者**: Rust 初学者、想要快速上手 OpenTelemetry 的开发者  
> **完成时间**: 30 分钟  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0+  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🚀 Rust OTLP 30分钟快速入门教程](#-rust-otlp-30分钟快速入门教程)
  - [📋 目录](#-目录)
  - [🎯 学习目标](#-学习目标)
  - [⚙️ 环境准备 (5分钟)](#️-环境准备-5分钟)
    - [1. 安装 Rust](#1-安装-rust)
    - [2. 验证安装](#2-验证安装)
    - [3. 创建项目](#3-创建项目)
  - [📦 第一步: 添加依赖 (3分钟)](#-第一步-添加依赖-3分钟)
  - [🔧 第二步: 初始化 OpenTelemetry (5分钟)](#-第二步-初始化-opentelemetry-5分钟)
  - [📊 第三步: 创建你的第一个 Span (5分钟)](#-第三步-创建你的第一个-span-5分钟)
  - [🌐 第四步: HTTP 服务追踪 (7分钟)](#-第四步-http-服务追踪-7分钟)
  - [💾 第五步: 数据库操作追踪 (5分钟)](#-第五步-数据库操作追踪-5分钟)
  - [🎉 恭喜完成](#-恭喜完成)
  - [📚 下一步学习](#-下一步学习)
    - [初级进阶](#初级进阶)
    - [中级进阶](#中级进阶)
    - [高级主题](#高级主题)
  - [❓ 常见问题](#-常见问题)
    - [Q1: 连接 Collector 失败怎么办？](#q1-连接-collector-失败怎么办)
    - [Q2: 为什么看不到 Traces？](#q2-为什么看不到-traces)
    - [Q3: 如何减少追踪开销？](#q3-如何减少追踪开销)
    - [Q4: 如何在生产环境使用？](#q4-如何在生产环境使用)
    - [Q5: 支持哪些后端？](#q5-支持哪些后端)
  - [🔗 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [本项目文档](#本项目文档)
    - [社区资源](#社区资源)

---

## 🎯 学习目标

完成本教程后，你将能够：

- ✅ 配置 Rust OpenTelemetry 环境
- ✅ 创建和导出 Traces
- ✅ 为 HTTP 服务添加追踪
- ✅ 追踪数据库操作
- ✅ 查看和分析遥测数据

---

## ⚙️ 环境准备 (5分钟)

### 1. 安装 Rust

```bash
# Unix/Linux/macOS
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Windows
# 下载并运行: https://rustup.rs/
```

### 2. 验证安装

```bash
rustc --version
# 应该显示: rustc 1.90.0 或更高版本

cargo --version
# 应该显示: cargo 1.90.0 或更高版本
```

### 3. 创建项目

```bash
cargo new otlp_quickstart
cd otlp_quickstart
```

---

## 📦 第一步: 添加依赖 (3分钟)

编辑 `Cargo.toml`：

```toml
[package]
name = "otlp_quickstart"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# HTTP 服务
axum = "0.7"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"
```

**安装依赖**：

```bash
cargo build
```

---

## 🔧 第二步: 初始化 OpenTelemetry (5分钟)

创建 `src/main.rs`：

```rust
use opentelemetry::{global, trace::TracerProvider as _, KeyValue};
use opentelemetry_sdk::{
    trace::{self, TracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::error::Error;

/// 初始化 OpenTelemetry
fn init_tracer() -> Result<TracerProvider, Box<dyn Error>> {
    // 1. 创建 OTLP 导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317") // Jaeger/OTEL Collector 地址
        .build_span_exporter()?;
    
    // 2. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-quickstart"),
            KeyValue::new("service.version", "0.1.0"),
        ]))
        .build();
    
    // 3. 设置全局 TracerProvider
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    let provider = init_tracer()?;
    
    println!("✅ OpenTelemetry 初始化成功!");
    println!("📊 Traces 将发送到: http://localhost:4317");
    
    // 你的应用代码将在这里...
    
    // 确保所有 spans 都被导出
    provider.force_flush();
    
    Ok(())
}
```

**测试运行**（暂时会报错，因为还没有启动 Collector）：

```bash
cargo run
```

---

## 📊 第三步: 创建你的第一个 Span (5分钟)

更新 `src/main.rs`：

```rust
use opentelemetry::{
    global, 
    trace::{Tracer, TracerProvider as _, SpanKind, Status},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, TracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::error::Error;
use std::time::Duration;

fn init_tracer() -> Result<TracerProvider, Box<dyn Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-quickstart"),
            KeyValue::new("service.version", "0.1.0"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}

/// 示例业务函数
async fn process_order(order_id: &str) -> Result<(), Box<dyn Error>> {
    // 获取 Tracer
    let tracer = global::tracer("otlp-quickstart");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("process_order")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    
    // 添加属性
    span.set_attribute(KeyValue::new("order.id", order_id.to_string()));
    span.set_attribute(KeyValue::new("order.status", "processing"));
    
    // 模拟业务处理
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 设置状态
    span.set_status(Status::Ok);
    
    println!("✅ 订单 {} 处理完成", order_id);
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::fmt::init();
    
    let provider = init_tracer()?;
    
    println!("🚀 开始处理订单...\n");
    
    // 处理多个订单
    for i in 1..=5 {
        let order_id = format!("ORDER-{:03}", i);
        process_order(&order_id).await?;
    }
    
    println!("\n📊 所有订单处理完成!");
    
    // 强制刷新，确保数据发送
    provider.force_flush();
    
    // 等待一下，确保数据传输完成
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    Ok(())
}
```

**运行**：

```bash
cargo run
```

**预期输出**：

```text
🚀 开始处理订单...

✅ 订单 ORDER-001 处理完成
✅ 订单 ORDER-002 处理完成
✅ 订单 ORDER-003 处理完成
✅ 订单 ORDER-004 处理完成
✅ 订单 ORDER-005 处理完成

📊 所有订单处理完成!
```

---

## 🌐 第四步: HTTP 服务追踪 (7分钟)

创建一个简单的 HTTP 服务并添加追踪。

**完整代码** `src/main.rs`：

```rust
use axum::{
    Router,
    routing::get,
    http::{StatusCode, HeaderMap},
    extract::Path,
};
use opentelemetry::{
    global,
    trace::{Tracer, SpanKind, Status},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, TracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::error::Error;
use std::time::Duration;

fn init_tracer() -> Result<TracerProvider, Box<dyn Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-http-service"),
            KeyValue::new("service.version", "0.1.0"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}

/// GET /hello/:name
async fn hello_handler(
    Path(name): Path<String>,
    headers: HeaderMap,
) -> Result<String, StatusCode> {
    let tracer = global::tracer("otlp-http-service");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("handle_hello")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    // 添加 HTTP 属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.route", "/hello/:name"));
    span.set_attribute(KeyValue::new("http.target", format!("/hello/{}", name)));
    span.set_attribute(KeyValue::new("user.name", name.clone()));
    
    // 模拟业务处理
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    let response = format!("Hello, {}! 🎉", name);
    
    // 设置响应属性
    span.set_attribute(KeyValue::new("http.status_code", 200i64));
    span.set_status(Status::Ok);
    
    Ok(response)
}

/// GET /api/users/:id
async fn get_user_handler(Path(id): Path<u64>) -> Result<String, StatusCode> {
    let tracer = global::tracer("otlp-http-service");
    
    let mut span = tracer
        .span_builder("get_user")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.route", "/api/users/:id"));
    span.set_attribute(KeyValue::new("user.id", id as i64));
    
    // 模拟数据库查询
    tokio::time::sleep(Duration::from_millis(30)).await;
    
    if id == 0 {
        span.set_attribute(KeyValue::new("http.status_code", 404i64));
        span.set_status(Status::error("User not found"));
        return Err(StatusCode::NOT_FOUND);
    }
    
    let user = format!(r#"{{"id": {}, "name": "User {}", "email": "user{}@example.com"}}"#, id, id, id);
    
    span.set_attribute(KeyValue::new("http.status_code", 200i64));
    span.set_status(Status::Ok);
    
    Ok(user)
}

/// GET /health
async fn health_handler() -> &'static str {
    "OK"
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    let provider = init_tracer()?;
    
    // 创建路由
    let app = Router::new()
        .route("/hello/:name", get(hello_handler))
        .route("/api/users/:id", get(get_user_handler))
        .route("/health", get(health_handler));
    
    let addr = "127.0.0.1:3000";
    println!("🚀 HTTP 服务启动成功!");
    println!("📍 监听地址: http://{}", addr);
    println!("📊 Traces 发送到: http://localhost:4317");
    println!("\n尝试访问:");
    println!("  - http://localhost:3000/hello/World");
    println!("  - http://localhost:3000/api/users/1");
    println!("  - http://localhost:3000/health");
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    // 清理
    provider.force_flush();
    
    Ok(())
}
```

**运行服务**：

```bash
cargo run
```

**测试 API**（在另一个终端）：

```bash
# 测试 hello 端点
curl http://localhost:3000/hello/Alice
# 输出: Hello, Alice! 🎉

# 测试 user 端点
curl http://localhost:3000/api/users/1
# 输出: {"id": 1, "name": "User 1", "email": "user1@example.com"}

# 测试健康检查
curl http://localhost:3000/health
# 输出: OK
```

---

## 💾 第五步: 数据库操作追踪 (5分钟)

添加数据库操作追踪。首先更新 `Cargo.toml`：

```toml
[dependencies]
# ... 之前的依赖 ...

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "sqlite", "macros"] }
```

**创建数据库操作模块** `src/db.rs`：

```rust
use opentelemetry::{global, trace::{Tracer, SpanKind, Status}, KeyValue};
use sqlx::{SqlitePool, Row};
use std::error::Error;

/// 创建数据库连接池
pub async fn create_pool() -> Result<SqlitePool, Box<dyn Error>> {
    let pool = SqlitePool::connect("sqlite::memory:").await?;
    
    // 创建表
    sqlx::query(
        r#"
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT NOT NULL
        )
        "#
    )
    .execute(&pool)
    .await?;
    
    Ok(pool)
}

/// 插入用户（带追踪）
pub async fn insert_user(
    pool: &SqlitePool,
    name: &str,
    email: &str,
) -> Result<i64, Box<dyn Error>> {
    let tracer = global::tracer("database");
    
    // 创建 Span
    let mut span = tracer
        .span_builder("db.insert_user")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 添加数据库属性
    span.set_attribute(KeyValue::new("db.system", "sqlite"));
    span.set_attribute(KeyValue::new("db.operation", "INSERT"));
    span.set_attribute(KeyValue::new("db.table", "users"));
    span.set_attribute(KeyValue::new("db.user", "app"));
    
    // 执行 SQL（注意：生产环境中不要记录实际 SQL，可能包含敏感信息）
    let result = sqlx::query(
        "INSERT INTO users (name, email) VALUES (?, ?)"
    )
    .bind(name)
    .bind(email)
    .execute(pool)
    .await;
    
    match result {
        Ok(res) => {
            let id = res.last_insert_rowid();
            span.set_attribute(KeyValue::new("db.rows_affected", 1i64));
            span.set_attribute(KeyValue::new("user.id", id));
            span.set_status(Status::Ok);
            Ok(id)
        }
        Err(e) => {
            span.set_status(Status::error(format!("Database error: {}", e)));
            Err(e.into())
        }
    }
}

/// 查询用户（带追踪）
pub async fn get_user(
    pool: &SqlitePool,
    id: i64,
) -> Result<Option<(String, String)>, Box<dyn Error>> {
    let tracer = global::tracer("database");
    
    let mut span = tracer
        .span_builder("db.get_user")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("db.system", "sqlite"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    span.set_attribute(KeyValue::new("db.table", "users"));
    span.set_attribute(KeyValue::new("user.id", id));
    
    let result = sqlx::query("SELECT name, email FROM users WHERE id = ?")
        .bind(id)
        .fetch_optional(pool)
        .await;
    
    match result {
        Ok(Some(row)) => {
            let name: String = row.get(0);
            let email: String = row.get(1);
            span.set_attribute(KeyValue::new("db.rows_returned", 1i64));
            span.set_status(Status::Ok);
            Ok(Some((name, email)))
        }
        Ok(None) => {
            span.set_attribute(KeyValue::new("db.rows_returned", 0i64));
            span.set_status(Status::Ok);
            Ok(None)
        }
        Err(e) => {
            span.set_status(Status::error(format!("Database error: {}", e)));
            Err(e.into())
        }
    }
}
```

**更新 `src/main.rs`** 使用数据库：

```rust
mod db;

use axum::{Router, routing::get, http::StatusCode, extract::Path};
use opentelemetry::{global, trace::{Tracer, SpanKind, Status}, KeyValue};
use opentelemetry_sdk::{trace::TracerProvider, Resource};
use opentelemetry_otlp::WithExportConfig;
use std::error::Error;
use std::sync::Arc;
use sqlx::SqlitePool;

// ... init_tracer 函数保持不变 ...

fn init_tracer() -> Result<TracerProvider, Box<dyn Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-db-service"),
            KeyValue::new("service.version", "0.1.0"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    
    Ok(provider)
}

/// GET /api/users/:id - 查询用户
async fn get_user_handler(
    Path(id): Path<i64>,
    axum::extract::State(pool): axum::extract::State<Arc<SqlitePool>>,
) -> Result<String, StatusCode> {
    let tracer = global::tracer("api");
    
    let mut span = tracer
        .span_builder("api.get_user")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("user.id", id));
    
    // 调用数据库
    match db::get_user(&pool, id).await {
        Ok(Some((name, email))) => {
            let response = format!(
                r#"{{"id": {}, "name": "{}", "email": "{}"}}"#,
                id, name, email
            );
            span.set_status(Status::Ok);
            Ok(response)
        }
        Ok(None) => {
            span.set_status(Status::error("User not found"));
            Err(StatusCode::NOT_FOUND)
        }
        Err(e) => {
            span.set_status(Status::error(format!("{}", e)));
            Err(StatusCode::INTERNAL_SERVER_ERROR)
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    let provider = init_tracer()?;
    
    // 创建数据库连接池
    let pool = Arc::new(db::create_pool().await?);
    
    // 插入测试数据
    println!("📊 插入测试数据...");
    for i in 1..=5 {
        db::insert_user(
            &pool,
            &format!("User {}", i),
            &format!("user{}@example.com", i),
        ).await?;
    }
    println!("✅ 测试数据插入完成!\n");
    
    // 创建路由
    let app = Router::new()
        .route("/api/users/:id", get(get_user_handler))
        .with_state(pool);
    
    let addr = "127.0.0.1:3000";
    println!("🚀 服务启动成功!");
    println!("📍 监听地址: http://{}", addr);
    println!("📊 Traces 发送到: http://localhost:4317");
    println!("\n尝试访问: http://localhost:3000/api/users/1");
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    // 清理
    provider.force_flush();
    
    Ok(())
}
```

**运行并测试**：

```bash
cargo run

# 在另一个终端测试
curl http://localhost:3000/api/users/1
# 输出: {"id": 1, "name": "User 1", "email": "user1@example.com"}
```

---

## 🎉 恭喜完成

你已经成功完成了 Rust OTLP 快速入门教程！🎊

你现在掌握了：

- ✅ OpenTelemetry 的基本配置
- ✅ 创建和管理 Spans
- ✅ HTTP 服务的追踪
- ✅ 数据库操作的追踪
- ✅ 属性和状态的设置

---

## 📚 下一步学习

### 初级进阶

1. **Context 传播**
   - 学习如何在微服务间传播 Trace Context
   - 参考: `01_OTLP核心协议/04_Context传播.md`

2. **Metrics 指标**
   - 添加 Counter、Histogram、Gauge
   - 参考: `03_数据模型/02_Metrics数据模型/`

3. **Logs 日志**
   - 集成结构化日志
   - 参考: `03_数据模型/03_Logs数据模型/`

### 中级进阶

1. **Semantic Conventions**
   - 学习标准化的属性命名
   - 参考: `02_Semantic_Conventions/`

2. **采样策略**
   - 实现智能采样
   - 参考: `05_采样与性能/`

3. **性能优化**
   - SIMD 加速、Arrow 优化
   - 参考: `35_性能优化深化/`

### 高级主题

1. **分布式追踪**
   - 多服务链路追踪
   - 参考: `36_分布式OTLP控制/`

2. **生产部署**
   - Kubernetes、Collector 配置
   - 参考: `10_云平台集成/`

---

## ❓ 常见问题

### Q1: 连接 Collector 失败怎么办？

**A**: 确保 Jaeger 或 OpenTelemetry Collector 正在运行。

**快速启动 Jaeger**（推荐用于学习）：

```bash
docker run -d --name jaeger \
  -p 4317:4317 \
  -p 4318:4318 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest
```

访问 Jaeger UI: <http://localhost:16686>

### Q2: 为什么看不到 Traces？

**A**: 检查以下几点：

1. **Collector 是否运行**：

   ```bash
   docker ps | grep jaeger
   ```

2. **端点是否正确**：
   - gRPC: `http://localhost:4317`
   - HTTP: `http://localhost:4318`

3. **强制刷新**：

   ```rust
   provider.force_flush();
   ```

4. **等待数据传输**：

   ```rust
   tokio::time::sleep(Duration::from_secs(2)).await;
   ```

### Q3: 如何减少追踪开销？

**A**: 使用采样策略：

```rust
use opentelemetry_sdk::trace::Sampler;

let provider = TracerProvider::builder()
    .with_config(
        trace::Config::default()
            .with_sampler(Sampler::TraceIdRatioBased(0.1)) // 10% 采样率
    )
    // ... 其他配置
    .build();
```

### Q4: 如何在生产环境使用？

**A**: 关键配置：

1. **使用批量导出器**（已经在用）
2. **配置合理的采样率**（1-10%）
3. **设置超时和重试**
4. **监控 Exporter 性能**
5. **使用异步运行时**（Tokio）

### Q5: 支持哪些后端？

**A**: OpenTelemetry 支持多种后端：

- ✅ Jaeger
- ✅ Zipkin
- ✅ Prometheus
- ✅ Grafana Tempo
- ✅ Datadog
- ✅ New Relic
- ✅ AWS X-Ray
- ✅ Azure Monitor
- ✅ Google Cloud Trace

---

## 🔗 参考资源

### 官方文档

- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/)
- [Rust 官方文档](https://doc.rust-lang.org/)

### 本项目文档

- [完整文档导航](../README.md)
- [Rust 最佳实践](./02_Rust_OTLP_最佳实践.md)
- [学习路径指南](../20_学习路径导航/01_按角色分类的学习路径.md)

### 社区资源

- [OpenTelemetry Discord](https://cloud-native.slack.com/archives/C01N3AT62SJ)
- [Rust 论坛](https://users.rust-lang.org/)
- [Stack Overflow - opentelemetry-rust](https://stackoverflow.com/questions/tagged/opentelemetry-rust)

---

**教程版本**: v1.0  
**创建日期**: 2025年10月10日  
**预计完成时间**: 30 分钟  
**难度**: 🟢 入门级

---

[🏠 返回主目录](../README.md) | [➡️ 下一步: 最佳实践](./02_Rust_OTLP_常见模式.md) | [📚 学习路径](../20_学习路径导航/)
