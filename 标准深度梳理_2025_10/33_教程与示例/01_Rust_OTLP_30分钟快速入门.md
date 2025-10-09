# Rust OTLP 30分钟快速入门

> **Rust版本**: 1.90+  
> **难度**: ⭐⭐ 入门级  
> **预计时间**: 30分钟  
> **最后更新**: 2025年10月9日

---

## 🎯 学习目标

完成本教程后，您将能够：

✅ 在 Rust 项目中集成 OpenTelemetry  
✅ 发送追踪数据到 OTLP Collector  
✅ 追踪 HTTP 请求和数据库操作  
✅ 在 Jaeger 中查看追踪数据

---

## 📋 前置要求

1. **Rust 1.90+**: `rustc --version`
2. **Docker**: 用于运行 Jaeger
3. **基础 Rust 知识**: async/await, tokio

---

## 🚀 第1步: 创建项目 (2分钟)

```bash
# 创建新项目
cargo new otlp-quickstart
cd otlp-quickstart

# 添加依赖
cargo add tokio --features full
cargo add axum
cargo add opentelemetry --features trace
cargo add opentelemetry_sdk --features rt-tokio,trace
cargo add opentelemetry-otlp --features grpc-tonic
cargo add tracing
cargo add tracing-subscriber --features env-filter
cargo add tracing-opentelemetry
```

**Cargo.toml** 应该包含：

```toml
[dependencies]
tokio = { version = "1.47", features = ["full"] }
axum = "0.8"
opentelemetry = { version = "0.31", features = ["trace"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
```

---

## 🔧 第2步: 初始化 OpenTelemetry (5分钟)

创建 `src/telemetry.rs`:

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{self, TracerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 OpenTelemetry
pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 OTLP exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317") // Jaeger endpoint
        .build_span_exporter()?;
    
    // 2. 创建 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "quickstart-app"),
            KeyValue::new("service.version", "1.0.0"),
        ]))
        .build();
    
    // 3. 设置全局 tracer provider
    global::set_tracer_provider(provider.clone());
    
    // 4. 创建 tracing layer
    let telemetry = tracing_opentelemetry::layer()
        .with_tracer(global::tracer("quickstart"));
    
    // 5. 初始化 tracing subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry)
        .init();
    
    Ok(())
}

/// 关闭 OpenTelemetry
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

---

## 🌐 第3步: 创建 HTTP 服务器 (10分钟)

修改 `src/main.rs`:

```rust
mod telemetry;

use axum::{
    Router,
    routing::get,
    response::IntoResponse,
    http::StatusCode,
};
use std::time::Duration;
use tracing::{info, instrument};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    telemetry::init_telemetry()?;
    
    info!("Starting quickstart application");
    
    // 创建路由
    let app = Router::new()
        .route("/", get(root_handler))
        .route("/users/:id", get(get_user_handler))
        .route("/slow", get(slow_handler));
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    
    info!("Server listening on http://localhost:3000");
    
    axum::serve(listener, app).await?;
    
    // 关闭 OpenTelemetry
    telemetry::shutdown_telemetry();
    
    Ok(())
}

/// 根路径处理器
#[instrument]
async fn root_handler() -> impl IntoResponse {
    info!("Handling root request");
    "Welcome to OTLP Quickstart!"
}

/// 获取用户处理器
#[instrument]
async fn get_user_handler(
    axum::extract::Path(user_id): axum::extract::Path<u64>,
) -> impl IntoResponse {
    info!("Getting user: {}", user_id);
    
    // 模拟数据库查询
    fetch_user_from_db(user_id).await;
    
    format!("User {}", user_id)
}

/// 慢速处理器 (演示性能追踪)
#[instrument]
async fn slow_handler() -> impl IntoResponse {
    info!("Processing slow request");
    
    // 模拟耗时操作
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    "Slow operation completed"
}

/// 模拟数据库查询
#[instrument]
async fn fetch_user_from_db(user_id: u64) {
    info!("Querying database for user {}", user_id);
    
    // 模拟数据库延迟
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    info!("User {} fetched from database", user_id);
}
```

---

## 🐳 第4步: 启动 Jaeger (3分钟)

```bash
# 使用 Docker 运行 Jaeger
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 16686:16686 \
  -p 4317:4317 \
  -p 4318:4318 \
  jaegertracing/all-in-one:latest

# 等待 Jaeger 启动
sleep 5

# 打开 Jaeger UI
open http://localhost:16686
```

---

## 🎮 第5步: 测试应用 (5分钟)

```bash
# 在新终端运行应用
cargo run

# 在另一个终端发送请求
curl http://localhost:3000/
curl http://localhost:3000/users/123
curl http://localhost:3000/slow
```

---

## 👀 第6步: 查看追踪数据 (5分钟)

1. **打开 Jaeger UI**: <http://localhost:16686>
2. **选择服务**: `quickstart-app`
3. **点击 "Find Traces"**
4. **查看追踪详情**:
   - 可以看到 HTTP 请求
   - 数据库查询的耗时
   - 完整的调用链路

**你应该看到**:

```text
quickstart-app
├── GET /users/123 (55ms)
│   └── fetch_user_from_db (50ms)
│       └── Database query (50ms)
```

---

## 🎓 进阶: 添加自定义属性 (可选)

```rust
use opentelemetry::trace::TraceContextExt;

#[instrument]
async fn advanced_handler() -> impl IntoResponse {
    let span = tracing::Span::current();
    
    // 添加自定义属性
    span.record("user.id", 123);
    span.record("request.priority", "high");
    
    // 添加事件
    tracing::info!(
        user_id = 123,
        action = "login",
        "User logged in successfully"
    );
    
    "Advanced tracking"
}
```

---

## ✅ 完成检查清单

- [ ] Rust 项目创建成功
- [ ] 依赖添加正确
- [ ] OpenTelemetry 初始化成功
- [ ] HTTP 服务器运行正常
- [ ] Jaeger 启动成功
- [ ] 可以在 Jaeger 中看到追踪数据

---

## 🎯 下一步

恭喜！您已经完成了 Rust OTLP 快速入门。接下来可以：

### 继续学习

1. 📘 [Rust同步异步编程集成](../04_核心组件/05_Rust同步异步编程集成.md) - 深入理解异步追踪
2. 📗 [HTTP客户端追踪](../04_核心组件/08_HTTP_客户端追踪_Reqwest_中间件完整版.md) - 追踪外部API调用
3. 📙 [数据库追踪](../02_Semantic_Conventions/05_数据库属性/01_SQLx_数据库追踪_Rust完整版.md) - 集成数据库追踪

### 实战项目

1. 🏭 [微服务完整实战](../06_实战案例/00_Rust微服务完整实战_2025最新版.md) - 构建真实微服务
2. 🎨 添加数据库集成 (PostgreSQL + SQLx)
3. 🔄 添加消息队列 (Kafka/NATS)

### 优化性能

1. ⚡ [性能优化指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md) - 提升性能
2. 📊 [基准测试](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md) - 测量性能

---

## 🐛 常见问题

### 问题1: 连接 Jaeger 失败

```text
Error: Connection refused
```

**解决**:

```bash
# 检查 Jaeger 是否运行
docker ps | grep jaeger

# 重启 Jaeger
docker restart jaeger
```

### 问题2: 看不到追踪数据

**解决**:

1. 检查 service name 是否正确
2. 等待几秒让数据导出
3. 确保 Jaeger 端口正确 (4317)

### 问题3: 编译错误

```text
error: failed to resolve: use of undeclared crate or module
```

**解决**:

```bash
# 清理并重新构建
cargo clean
cargo build
```

---

## 📚 完整代码

完整代码可以在以下位置找到：

- GitHub: <https://github.com/example/otlp-quickstart>
- 本地: `examples/quickstart/`

---

## 🤝 获取帮助

- 📖 [文档导航](../📖_Rust_OTLP文档导航_2025_10_09.md)
- 🔧 [故障排查指南](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
- 💬 [GitHub Discussions](https://github.com/open-telemetry/opentelemetry-rust/discussions)

---

**文档状态**: ✅ 完成  
**难度**: ⭐⭐ 入门级  
**最后更新**: 2025年10月9日

**恭喜您完成快速入门！🎉**-
