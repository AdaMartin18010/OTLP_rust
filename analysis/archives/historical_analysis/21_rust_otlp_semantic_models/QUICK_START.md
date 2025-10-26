# 快速入门指南

> **面向**: 刚接触 Rust OTLP 的开发者  
> **时间**: 30 分钟  
> **目标**: 快速上手 OpenTelemetry Rust

---

## 🚀 5 分钟快速体验

### 1. 安装依赖

```toml
# Cargo.toml
[dependencies]
opentelemetry = "0.27"
opentelemetry-otlp = "0.27"
opentelemetry-sdk = "0.27"
tokio = { version = "1.47", features = ["full"] }
tracing = "0.1"
tracing-opentelemetry = "0.28"
tracing-subscriber = "0.3"
```

### 2. 最小化代码

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::trace::TracerProvider;
use tracing::{info, instrument};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化
    let provider = TracerProvider::default();
    global::set_tracer_provider(provider);
    
    // 2. 运行应用
    hello_world().await;
    
    // 3. 关闭
    global::shutdown_tracer_provider();
    Ok(())
}

#[instrument]
async fn hello_world() {
    info!("Hello, OpenTelemetry!");
}
```

### 3. 运行

```bash
cargo run
```

---

## 📚 学习路径

### 第 1 天: 理解基础概念

**阅读材料**:

- [README.md](README.md) - 10分钟
- [01_rust_sync_async_core.md](01_rust_sync_async_core.md) §1-2 - 20分钟

**实践**:

- 创建一个简单的 Span
- 添加 Attributes

### 第 2 天: OTLP 语义模型

**阅读材料**:

- [04_otlp_semantic_conventions.md](04_otlp_semantic_conventions.md) §1-4 - 30分钟

**实践**:

- 配置 Resource
- 发送 HTTP 请求追踪

### 第 3 天: 分布式追踪

**阅读材料**:

- [07_distributed_tracing_model.md](07_distributed_tracing_model.md) §1-3 - 30分钟

**实践**:

- 跨服务上下文传播
- 实现采样策略

### 第 4 天: 生产环境

**阅读材料**:

- [10_opentelemetry_rust_libraries.md](10_opentelemetry_rust_libraries.md) §5-7 - 30分钟

**实践**:

- 集成 Actix-Web/Tonic
- 配置批处理导出器

---

## 🎯 常见场景

### HTTP 服务追踪

```rust
use actix_web::{web, App, HttpServer};
use opentelemetry::global;
use tracing::instrument;

#[instrument]
async fn hello() -> &'static str {
    "Hello World"
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化 OpenTelemetry
    init_telemetry();
    
    HttpServer::new(|| {
        App::new().route("/", web::get().to(hello))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}

fn init_telemetry() {
    // 见完整示例
}
```

### 数据库查询追踪

```rust
use sqlx::PgPool;
use tracing::instrument;

#[instrument(fields(db.system = "postgresql"))]
async fn fetch_users(pool: &PgPool) -> Result<Vec<User>, sqlx::Error> {
    sqlx::query_as::<_, User>("SELECT * FROM users")
        .fetch_all(pool)
        .await
}
```

### gRPC 服务追踪

```rust
use tonic::{Request, Response, Status};
use tracing::instrument;

#[tonic::async_trait]
impl MyService for MyServiceImpl {
    #[instrument(skip(self))]
    async fn get_user(&self, req: Request<GetUserRequest>) -> Result<Response<User>, Status> {
        // 自动追踪
        Ok(Response::new(User::default()))
    }
}
```

---

## 🔧 故障排查

### 问题 1: Span 没有导出

**检查**:

```rust
// 确保调用了 shutdown
global::shutdown_tracer_provider();
```

### 问题 2: 上下文没有传播

**检查**:

```rust
// 使用 with_current_context()
use opentelemetry::trace::FutureExt;

let future = async {
    // your code
}.with_current_context();
```

### 问题 3: 性能问题

**优化**:

```rust
// 调整采样率
Sampler::TraceIdRatioBased(0.1)  // 10%

// 增加批处理大小
BatchConfig::default()
    .with_max_export_batch_size(1024)
```

---

## 📖 推荐资源

### 官方文档

- [OpenTelemetry Docs](https://opentelemetry.io/docs/)
- [opentelemetry-rust](https://github.com/open-telemetry/opentelemetry-rust)

### 本项目文档

- [完整文档列表](README.md#文档体系架构)
- [交叉引用索引](CROSS_REFERENCE.md)

---

## 💡 下一步

1. **深入学习**: 阅读完整文档系列
2. **实践项目**: 将 OTLP 集成到实际项目
3. **性能优化**: 阅读性能优化文档
4. **社区贡献**: 参与开源贡献

---

**需要帮助?** 请查看 [CROSS_REFERENCE.md](CROSS_REFERENCE.md) 按场景导航
