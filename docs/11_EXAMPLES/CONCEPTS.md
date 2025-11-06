# 示例集合核心概念

**版本**: 2.0
**日期**: 2025年10月28日
**状态**: ✅ 完整

---

## 📋 目录

- [示例分类](#1-示例分类)
- [快速开始示例](#2-快速开始示例)
- [集成示例](#3-集成示例)
- [高级示例](#4-高级示例)

---

## 📖 示例分类

### 1.1 示例体系

```
示例层次结构:

Level 1: 入门示例 (5分钟)
├─ Hello OTLP
├─ 简单Trace
└─ 基础配置

Level 2: 集成示例 (30分钟)
├─ Axum集成
├─ Actix-web集成
├─ Tonic集成
└─ 中间件示例

Level 3: 实战示例 (2小时)
├─ 完整微服务
├─ 生产配置
├─ 性能优化
└─ 故障处理

Level 4: 高级示例 (1天)
├─ 自定义导出器
├─ 复杂状态机
├─ 形式化验证
└─ 分布式追踪
```

### 1.2 示例统计

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
示例统计
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
类别          数量    难度    时间
────────────────────────────────────────
入门          10个    ⭐      5-10min
集成          15个    ⭐⭐    30-60min
实战          12个    ⭐⭐⭐  2-4h
高级          8个     ⭐⭐⭐⭐ 1-2天
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
总计          45+个
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 🔍 快速开始示例

### 2.1 Hello OTLP (5分钟)

#### 最简示例

```rust
// examples/01_hello_otlp.rs
use otlp_rust::otlp::TracerProvider;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建TracerProvider
    let provider = TracerProvider::builder()
        .with_simple_exporter()
        .build();

    // 2. 获取Tracer
    let tracer = provider.tracer("hello-otlp");

    // 3. 创建Span
    let span = tracer.start("hello");

    println!("Hello, OTLP!");

    // 4. 结束Span
    span.end();

    Ok(())
}
```

**运行**:

```bash
cargo run --example 01_hello_otlp
```

**输出**:

```
Hello, OTLP!
Span exported: hello (duration: 1.2ms)
```

---

### 2.2 简单HTTP服务 (10分钟)

```rust
// examples/02_simple_http.rs
use axum::{Router, routing::get};
use otlp_rust::otlp::{TracerProvider, Layer};

#[tokio::main]
async fn main() {
    // 初始化OTLP
    let provider = TracerProvider::builder()
        .with_endpoint("http://localhost:4317")
        .build();

    // 创建路由
    let app = Router::new()
        .route("/", get(handler))
        .layer(Layer::new(provider));

    // 启动服务
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}

async fn handler() -> &'static str {
    "Hello, World!"
}
```

**运行**:

```bash
# 终端1: 启动Collector
docker run -p 4317:4317 otel/opentelemetry-collector

# 终端2: 启动服务
cargo run --example 02_simple_http

# 终端3: 测试
curl http://localhost:3000
```

---

## 💡 集成示例

### 3.1 Axum完整集成 (30分钟)

```rust
// examples/10_axum_integration.rs
use axum::{Router, routing::{get, post}, Json, extract::State};
use otlp_rust::otlp::{TracerProvider, Tracer};
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    tracer: Arc<Tracer>,
}

#[tokio::main]
async fn main() {
    // 1. 初始化追踪
    let provider = TracerProvider::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("axum-example")
        .build();

    let tracer = Arc::new(provider.tracer("http-server"));

    // 2. 创建路由
    let app = Router::new()
        .route("/", get(index))
        .route("/user", post(create_user))
        .route("/user/:id", get(get_user))
        .with_state(AppState { tracer });

    // 3. 启动服务
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

async fn index(State(state): State<AppState>) -> &'static str {
    let span = state.tracer.start("GET /");
    // 业务逻辑
    span.end();
    "Welcome!"
}

async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<User>,
) -> Json<User> {
    let span = state.tracer.start("POST /user");
    span.set_attribute("user.name", &payload.name);

    // 创建用户逻辑
    let user = User {
        id: 1,
        name: payload.name,
    };

    span.end();
    Json(user)
}

async fn get_user(
    State(state): State<AppState>,
    axum::extract::Path(id): axum::extract::Path<i32>,
) -> Json<User> {
    let span = state.tracer.start("GET /user/:id");
    span.set_attribute("user.id", id);

    // 查询用户逻辑
    let user = User {
        id,
        name: "John".to_string(),
    };

    span.end();
    Json(user)
}

#[derive(serde::Serialize, serde::Deserialize)]
struct User {
    id: i32,
    name: String,
}
```

**测试**:

```bash
# 创建用户
curl -X POST http://localhost:3000/user \
  -H "Content-Type: application/json" \
  -d '{"name":"Alice"}'

# 查询用户
curl http://localhost:3000/user/1
```

---

### 3.2 带熔断器的gRPC客户端 (45分钟)

```rust
// examples/11_grpc_with_circuit_breaker.rs
use otlp_rust::{
    otlp::Tracer,
    reliability::CircuitBreaker,
};
use tonic::transport::Channel;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化
    let tracer = Tracer::new("grpc-client");
    let circuit_breaker = CircuitBreaker::new()
        .failure_threshold(5)
        .timeout(Duration::from_secs(60))
        .build();

    // 2. 连接gRPC服务
    let channel = Channel::from_static("http://[::1]:50051")
        .connect()
        .await?;

    let mut client = MyServiceClient::new(channel);

    // 3. 使用熔断器执行请求
    for i in 0..100 {
        let span = tracer.start(format!("request-{}", i));

        let result = circuit_breaker.call(|| async {
            client.my_method(Request::new(MyRequest {
                data: format!("data-{}", i),
            })).await
        }).await;

        match result {
            Ok(response) => {
                span.set_status(SpanStatus::Ok);
                println!("Success: {:?}", response);
            }
            Err(e) => {
                span.set_status(SpanStatus::Error);
                span.record_error(&e);
                println!("Error: {}", e);
            }
        }

        span.end();
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}
```

---

## ⚙️ 高级示例

### 4.1 完整微服务 (2小时)

```rust
// examples/20_microservice_complete.rs
use axum::{Router, routing::get};
use otlp_rust::{
    otlp::{TracerProvider, Tracer},
    reliability::{CircuitBreaker, RateLimiter, RetryPolicy},
    libraries::ObjectPool,
};
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // 1. 初始化所有组件
    let provider = TracerProvider::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("complete-microservice")
        .with_batch_config(BatchConfig {
            max_queue_size: 2048,
            scheduled_delay: Duration::from_secs(5),
            max_export_batch_size: 512,
        })
        .build();

    let tracer = Arc::new(provider.tracer("main"));

    let circuit_breaker = Arc::new(
        CircuitBreaker::new()
            .failure_threshold(10)
            .timeout(Duration::from_secs(30))
            .build()
    );

    let rate_limiter = Arc::new(RateLimiter::new(100)); // 100 req/s

    let span_pool = Arc::new(ObjectPool::new(1000, || Span::default()));

    // 2. 创建应用状态
    let state = AppState {
        tracer,
        circuit_breaker,
        rate_limiter,
        span_pool,
    };

    // 3. 创建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/api/users", get(list_users))
        .route("/api/process", get(process_data))
        .with_state(state);

    // 4. 启动服务
    println!("🚀 Server running at http://0.0.0.0:3000");

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

#[derive(Clone)]
struct AppState {
    tracer: Arc<Tracer>,
    circuit_breaker: Arc<CircuitBreaker>,
    rate_limiter: Arc<RateLimiter>,
    span_pool: Arc<ObjectPool<Span>>,
}

async fn health_check() -> &'static str {
    "OK"
}

async fn list_users(State(state): State<AppState>) -> Json<Vec<User>> {
    // 1. 限流检查
    if !state.rate_limiter.check() {
        return Json(vec![]);
    }

    // 2. 从对象池获取Span
    let span = state.span_pool.get();
    let _guard = state.tracer.start_with_span("list_users", span.as_ref());

    // 3. 使用熔断器执行数据库查询
    let users = state.circuit_breaker.call(|| async {
        // 模拟数据库查询
        tokio::time::sleep(Duration::from_millis(10)).await;
        vec![
            User { id: 1, name: "Alice".to_string() },
            User { id: 2, name: "Bob".to_string() },
        ]
    }).await.unwrap_or_default();

    Json(users)
}

async fn process_data(State(state): State<AppState>) -> &'static str {
    let span = state.span_pool.get();
    let _guard = state.tracer.start_with_span("process_data", span.as_ref());

    // 复杂的数据处理逻辑
    "Processed"
}

#[derive(serde::Serialize)]
struct User {
    id: i32,
    name: String,
}
```

---

## 📊 运行所有示例

### 5.1 快速测试脚本

```bash
#!/bin/bash
# scripts/run_examples.sh

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "运行所有示例"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 入门示例
echo "1. 入门示例..."
cargo run --example 01_hello_otlp
cargo run --example 02_simple_http &
sleep 5
curl http://localhost:3000
pkill -f 02_simple_http

# 集成示例
echo "2. 集成示例..."
cargo run --example 10_axum_integration &
sleep 5
curl http://localhost:3000
pkill -f 10_axum_integration

# 更多示例...

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ 所有示例运行完成!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
```

---

## 🔗 相关资源

- [对比矩阵](./COMPARISON_MATRIX.md) - 示例对比
- [知识图谱](./KNOWLEDGE_GRAPH.md) - 示例关系
- [快速入门](../01_GETTING_STARTED/) - 开始学习

---

**版本**: 2.0
**创建日期**: 2025-10-28
**最后更新**: 2025-10-28

---

> **💡 提示**: 从`01_hello_otlp`开始，逐步尝试更复杂的示例。所有示例都可以直接运行！

