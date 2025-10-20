# ❓ Rust OTLP 常见问题解答 (FAQ)

> **目标读者**: 所有 Rust OTLP 开发者  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [❓ Rust OTLP 常见问题解答 (FAQ)](#-rust-otlp-常见问题解答-faq)
  - [📋 目录](#-目录)
  - [1. 安装与配置](#1-安装与配置)
    - [Q1.1: 如何安装 OpenTelemetry Rust SDK?](#q11-如何安装-opentelemetry-rust-sdk)
    - [Q1.2: 需要安装哪些依赖？](#q12-需要安装哪些依赖)
    - [Q1.3: 如何选择导出器（gRPC vs HTTP）？](#q13-如何选择导出器grpc-vs-http)
    - [Q1.4: 为什么编译时间这么长？](#q14-为什么编译时间这么长)
  - [2. 初始化与配置](#2-初始化与配置)
    - [Q2.1: TracerProvider 应该在哪里初始化？](#q21-tracerprovider-应该在哪里初始化)
    - [Q2.2: 如何配置采样率？](#q22-如何配置采样率)
    - [Q2.3: 如何设置 Service Name？](#q23-如何设置-service-name)
    - [Q2.4: 初始化失败怎么办？](#q24-初始化失败怎么办)
  - [3. Span 操作](#3-span-操作)
    - [Q3.1: 为什么我的 Span 没有显示在 Jaeger 中？](#q31-为什么我的-span-没有显示在-jaeger-中)
    - [Q3.2: 如何在异步函数中创建 Span？](#q32-如何在异步函数中创建-span)
    - [Q3.3: Span 什么时候会被发送？](#q33-span-什么时候会被发送)
    - [Q3.4: 如何添加自定义属性？](#q34-如何添加自定义属性)
    - [Q3.5: 如何记录错误到 Span？](#q35-如何记录错误到-span)
  - [4. 上下文传播](#4-上下文传播)
    - [Q4.1: 如何在 HTTP 请求间传播 Context？](#q41-如何在-http-请求间传播-context)
    - [Q4.2: 跨线程传播 Context 失败怎么办？](#q42-跨线程传播-context-失败怎么办)
    - [Q4.3: 如何在 Tokio 任务间传播 Context？](#q43-如何在-tokio-任务间传播-context)
    - [Q4.4: gRPC 调用如何传播 Context？](#q44-grpc-调用如何传播-context)
  - [5. 性能问题](#5-性能问题)
    - [Q5.1: OTLP 会影响应用性能吗？](#q51-otlp-会影响应用性能吗)
    - [Q5.2: 如何减少追踪开销？](#q52-如何减少追踪开销)
    - [Q5.3: 批量导出配置建议？](#q53-批量导出配置建议)
    - [Q5.4: 为什么内存使用增加了？](#q54-为什么内存使用增加了)
  - [6. Metrics 相关](#6-metrics-相关)
    - [Q6.1: 如何创建 Counter？](#q61-如何创建-counter)
    - [Q6.2: Histogram vs Gauge 如何选择？](#q62-histogram-vs-gauge-如何选择)
    - [Q6.3: Metrics 为什么没有数据？](#q63-metrics-为什么没有数据)
    - [Q6.4: 如何控制 Metrics 基数？](#q64-如何控制-metrics-基数)
  - [7. 错误处理](#7-错误处理)
    - [Q7.1: 连接 Collector 失败怎么办？](#q71-连接-collector-失败怎么办)
    - [Q7.2: 如何处理导出失败？](#q72-如何处理导出失败)
    - [Q7.3: panic 会影响追踪吗？](#q73-panic-会影响追踪吗)
    - [Q7.4: 证书验证失败怎么办？](#q74-证书验证失败怎么办)
  - [8. 集成问题](#8-集成问题)
    - [Q8.1: 如何集成 Axum？](#q81-如何集成-axum)
    - [Q8.2: 如何集成 Tonic (gRPC)？](#q82-如何集成-tonic-grpc)
    - [Q8.3: 如何集成数据库追踪？](#q83-如何集成数据库追踪)
    - [Q8.4: 如何与 tracing crate 集成？](#q84-如何与-tracing-crate-集成)
  - [9. 测试](#9-测试)
    - [Q9.1: 如何在测试中使用 OTLP？](#q91-如何在测试中使用-otlp)
    - [Q9.2: 如何验证 Span 是否正确创建？](#q92-如何验证-span-是否正确创建)
    - [Q9.3: 集成测试如何配置？](#q93-集成测试如何配置)
  - [10. 生产部署](#10-生产部署)
    - [Q10.1: 生产环境推荐配置？](#q101-生产环境推荐配置)
    - [Q10.2: 如何实现优雅关闭？](#q102-如何实现优雅关闭)
    - [Q10.3: 如何监控 OTLP 健康状态？](#q103-如何监控-otlp-健康状态)
    - [Q10.4: Docker 容器中注意事项？](#q104-docker-容器中注意事项)
  - [11. 升级与迁移](#11-升级与迁移)
    - [Q11.1: 如何从旧版本升级？](#q111-如何从旧版本升级)
    - [Q11.2: Breaking Changes 有哪些？](#q112-breaking-changes-有哪些)
    - [Q11.3: 如何从其他追踪系统迁移？](#q113-如何从其他追踪系统迁移)
  - [12. 高级用法](#12-高级用法)
    - [Q12.1: 如何实现自定义 Sampler？](#q121-如何实现自定义-sampler)
    - [Q12.2: 如何实现自定义 Exporter？](#q122-如何实现自定义-exporter)
    - [Q12.3: 如何修改 Span 在导出前？](#q123-如何修改-span-在导出前)
  - [🔗 参考资源](#-参考资源)

---

## 1. 安装与配置

### Q1.1: 如何安装 OpenTelemetry Rust SDK?

**A**: 在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
opentelemetry = "0.31.0"
opentelemetry-otlp = "0.31.0"
opentelemetry-sdk = "0.31.0"
tokio = { version = "1", features = ["full"] }

# 可选：tracing 集成
tracing = "0.1"
tracing-opentelemetry = "0.31.0"
tracing-subscriber = "0.3"
```

然后运行：

```bash
cargo build
```

**提示**: 如果编译慢，可以使用 [sccache](https://github.com/mozilla/sccache) 加速编译。

---

### Q1.2: 需要安装哪些依赖？

**A**: 根据使用场景选择：

**最小配置**（仅 Tracing）:

```toml
opentelemetry = "0.31.0"
opentelemetry-otlp = "0.31.0"
opentelemetry-sdk = "0.31.0"
```

**完整配置**（Tracing + Metrics + Logs）:

```toml
opentelemetry = { version = "0.31.0", features = ["trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31.0", features = ["trace", "metrics", "logs"] }
opentelemetry-sdk = { version = "0.31.0", features = ["trace", "metrics", "logs"] }
```

**gRPC 传输**:

```toml
opentelemetry-otlp = { version = "0.31.0", features = ["tonic"] }
tonic = "0.12"
```

**HTTP 传输**:

```toml
opentelemetry-otlp = { version = "0.31.0", features = ["reqwest"] }
reqwest = "0.12"
```

---

### Q1.3: 如何选择导出器（gRPC vs HTTP）？

**A**: 对比表：

| 特性 | gRPC (Tonic) | HTTP (Reqwest) |
|------|--------------|----------------|
| 性能 | ⚡ 更快（二进制协议） | 🐌 较慢（JSON） |
| 兼容性 | ✅ 广泛支持 | ✅ 广泛支持 |
| 配置复杂度 | 🟡 中等 | 🟢 简单 |
| 依赖大小 | 📦 较大 | 📦 较小 |
| 调试难度 | 🔴 难（二进制） | 🟢 易（JSON） |
| 推荐场景 | 生产环境 | 开发/调试 |

**推荐配置**：

```rust
// gRPC（推荐生产环境）
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317")
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;

// HTTP（开发环境）
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .http()
            .with_endpoint("http://localhost:4318")
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

---

### Q1.4: 为什么编译时间这么长？

**A**: OpenTelemetry 依赖较多，首次编译会较慢。优化方法：

1. **使用 sccache**:

    ```bash
    cargo install sccache
    export RUSTC_WRAPPER=sccache
    ```

2. **减少 features**:

    ```toml
    # 只启用需要的 features
    opentelemetry = { version = "0.31.0", default-features = false, features = ["trace"] }
    ```

3. **使用 mold 链接器** (Linux):

    ```toml
    # .cargo/config.toml
    [target.x86_64-unknown-linux-gnu]
    linker = "clang"
    rustflags = ["-C", "link-arg=-fuse-ld=mold"]
    ```

4. **增量编译**:

```bash
export CARGO_INCREMENTAL=1
```

---

## 2. 初始化与配置

### Q2.1: TracerProvider 应该在哪里初始化？

**A**: 在应用启动时初始化一次，使用全局单例：

```rust
use opentelemetry::global;
use std::sync::OnceLock;

static INIT: OnceLock<()> = OnceLock::new();

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    INIT.get_or_init(|| {
        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint("http://localhost:4317")
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)
            .expect("Failed to initialize tracer");
        
        global::set_tracer_provider(tracer);
    });
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    // 应用逻辑
    
    // 关闭前刷新
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

**❌ 错误做法**：在每个函数中重复初始化。

---

### Q2.2: 如何配置采样率？

**A**: 使用 `Sampler` 配置：

```rust
use opentelemetry_sdk::trace::{Config, Sampler};

// 1. 固定比例采样（推荐生产环境）
let config = Config::default()
    .with_sampler(Sampler::TraceIdRatioBased(0.1)); // 10% 采样

// 2. 总是采样（开发环境）
let config = Config::default()
    .with_sampler(Sampler::AlwaysOn);

// 3. 从不采样
let config = Config::default()
    .with_sampler(Sampler::AlwaysOff);

// 4. 父级采样（推荐）
let config = Config::default()
    .with_sampler(Sampler::ParentBased(
        Box::new(Sampler::TraceIdRatioBased(0.1))
    ));

// 应用配置
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_trace_config(config)
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

**环境变量配置**：

```bash
export OTEL_TRACES_SAMPLER=traceidratio
export OTEL_TRACES_SAMPLER_ARG=0.1  # 10%
```

---

### Q2.3: 如何设置 Service Name？

**A**: 三种方法：

**方法1: Resource API**（推荐）:

```rust
use opentelemetry_sdk::Resource;
use opentelemetry::KeyValue;

let config = Config::default()
    .with_resource(Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]));

let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_trace_config(config)
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

**方法2: 环境变量**:

```bash
export OTEL_SERVICE_NAME=my-service
export OTEL_RESOURCE_ATTRIBUTES=service.version=1.0.0,deployment.environment=production
```

**方法3: Exporter 配置**:

```rust
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317")
            .with_metadata(std::collections::HashMap::from([
                ("service-name".to_string(), "my-service".to_string()),
            ]))
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

---

### Q2.4: 初始化失败怎么办？

**A**: 常见错误和解决方案：

**错误1**: "Connection refused"

```rust
// 问题：Collector 未运行
// 解决：启动 Collector
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 4317:4317 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest
```

**错误2**: "Runtime not found"

```rust
// 问题：未指定运行时
// 解决：添加 Tokio 运行时
.install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

**错误3**: "Feature not enabled"

```toml
# 问题：未启用必要的 feature
# 解决：在 Cargo.toml 中添加
opentelemetry-otlp = { version = "0.31.0", features = ["tonic", "trace"] }
```

**调试技巧**：

```rust
// 启用详细日志
std::env::set_var("RUST_LOG", "opentelemetry=debug,opentelemetry_otlp=debug");
tracing_subscriber::fmt()
    .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
    .init();
```

---

## 3. Span 操作

### Q3.1: 为什么我的 Span 没有显示在 Jaeger 中？

**A**: 检查清单：

1. **Collector 是否运行**:

    ```bash
    docker ps | grep jaeger
    # 或者
    curl http://localhost:16686
    ```

2. **检查端点配置**:

    ```rust
    // 确保端点正确
    .with_endpoint("http://localhost:4317")  // gRPC
    // 或
    .with_endpoint("http://localhost:4318")  // HTTP
    ```

3. **确保 Span 已结束**:

    ```rust
    let mut span = tracer.start("my-operation");
    // ... 操作 ...
    span.end();  // ✅ 必须调用 end()
    ```

4. **等待批量导出**:

    ```rust
    // 方法1：强制刷新
    global::tracer_provider().force_flush();

    // 方法2：等待
    tokio::time::sleep(Duration::from_secs(2)).await;

    // 方法3：优雅关闭
    global::shutdown_tracer_provider();
    ```

5. **检查采样率**:

    ```rust
    // 确保采样率不是 0
    .with_sampler(Sampler::AlwaysOn)  // 测试时使用
    ```

6. **查看 Collector 日志**:

```bash
docker logs jaeger
```

---

### Q3.2: 如何在异步函数中创建 Span？

**A**: 使用 `tracing` crate 的 `#[instrument]` 宏（推荐）：

```rust
use tracing::instrument;

#[instrument]
async fn fetch_user(user_id: u64) -> Result<User, Error> {
    // Span 自动创建和管理
    let user = db.query(user_id).await?;
    tracing::info!("User fetched");
    Ok(user)
}

// 手动创建
async fn manual_span() {
    let tracer = global::tracer("my-service");
    let mut span = tracer.start("async-operation");
    
    // 在异步操作中使用
    let result = async_operation().await;
    
    span.end();
}

// 使用 Context
async fn with_context() {
    let tracer = global::tracer("my-service");
    let span = tracer.start("parent");
    let cx = Context::current_with_span(span);
    
    let _guard = cx.attach();
    
    // 子操作会自动继承父 Span
    child_operation().await;
}
```

---

### Q3.3: Span 什么时候会被发送？

**A**: Span 发送时机：

1. **批量导出达到阈值**:

    ```rust
    use opentelemetry_sdk::trace::BatchConfig;

    let config = BatchConfig::default()
        .with_max_queue_size(2048)      // 队列大小
        .with_max_export_batch_size(512) // 批量大小
        .with_scheduled_delay(Duration::from_millis(5000)); // 定时导出（5秒）

    // 当满足以下任一条件时发送：
    // - 队列中有 512 个 Span
    // - 距离上次发送超过 5 秒
    // - 调用 force_flush()
    // - 应用关闭
    ```

2. **强制刷新**:

    ```rust
    global::tracer_provider().force_flush();
    ```

3. **应用关闭**:

    ```rust
    global::shutdown_tracer_provider(); // 会自动刷新
    ```

**开发环境立即发送**：

```rust
// 使用 SimpleSpanProcessor（不推荐生产环境）
use opentelemetry_sdk::trace::TracerProvider;

let provider = TracerProvider::builder()
    .with_simple_exporter(exporter)  // 立即导出
    .build();
```

---

### Q3.4: 如何添加自定义属性？

**A**: 多种方式添加属性：

```rust
use opentelemetry::{KeyValue, trace::{Tracer, Span}};

let tracer = global::tracer("my-service");
let mut span = tracer.start("operation");

// 1. 单个属性
span.set_attribute(KeyValue::new("user.id", 123));
span.set_attribute(KeyValue::new("user.name", "Alice"));

// 2. 多个属性
span.set_attributes(vec![
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.url", "/api/users"),
    KeyValue::new("http.status_code", 200),
]);

// 3. 条件属性
if user.is_premium() {
    span.set_attribute(KeyValue::new("user.tier", "premium"));
}

// 4. 使用 tracing
#[instrument(fields(user.id = %user_id))]
async fn process_user(user_id: u64) {
    tracing::Span::current().record("user.name", "Alice");
}
```

**属性类型**：

```rust
// 字符串
KeyValue::new("key", "value")

// 数字
KeyValue::new("count", 42i64)
KeyValue::new("ratio", 3.14f64)

// 布尔
KeyValue::new("is_active", true)

// 数组
KeyValue::new("tags", vec!["rust", "otlp"])
```

---

### Q3.5: 如何记录错误到 Span？

**A**: 标准做法：

```rust
use opentelemetry::trace::{Span, Status};

// 方法1：使用 record_error
fn handle_error(err: &dyn std::error::Error) {
    let mut span = tracing::Span::current();
    span.record_error(err);
    span.set_status(Status::Error {
        description: err.to_string().into(),
    });
}

// 方法2：使用 Result 扩展
trait SpanResultExt<T, E> {
    fn trace_err(self, span: &mut dyn Span) -> Result<T, E>;
}

impl<T, E: std::error::Error> SpanResultExt<T, E> for Result<T, E> {
    fn trace_err(self, span: &mut dyn Span) -> Result<T, E> {
        if let Err(ref e) = self {
            span.record_error(e);
            span.set_status(Status::Error {
                description: e.to_string().into(),
            });
        }
        self
    }
}

// 使用
#[instrument]
async fn process() -> Result<(), Error> {
    let mut span = tracing::Span::current();
    
    risky_operation()
        .await
        .trace_err(&mut span)?;
    
    Ok(())
}

// 方法3：使用 tracing
#[instrument(err)]
async fn auto_trace_error() -> Result<(), Error> {
    // 错误会自动记录
    Err(Error::new("Something went wrong"))
}
```

---

## 4. 上下文传播

### Q4.1: 如何在 HTTP 请求间传播 Context？

**A**: 客户端注入 + 服务端提取：

**客户端**：

```rust
use opentelemetry::{global, propagation::TextMapPropagator};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

async fn make_request(url: &str) -> Result<Response, Error> {
    let cx = Context::current();
    
    // 注入 context 到 headers
    let mut injector = HashMap::new();
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut injector);
    });
    
    let mut headers = HeaderMap::new();
    for (key, value) in injector {
        headers.insert(
            HeaderName::from_bytes(key.as_bytes()).unwrap(),
            HeaderValue::from_str(&value).unwrap(),
        );
    }
    
    reqwest::Client::new()
        .get(url)
        .headers(headers)
        .send()
        .await
}
```

**服务端**：

```rust
use axum::{http::HeaderMap, middleware::Next, response::Response};

async fn extract_context(
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Response {
    // 提取 context
    let mut extractor = HashMap::new();
    for (key, value) in headers.iter() {
        if let Ok(v) = value.to_str() {
            extractor.insert(key.as_str().to_string(), v.to_string());
        }
    }
    
    let parent_cx = global::get_text_map_propagator(|propagator| {
        propagator.extract(&extractor)
    });
    
    let _guard = parent_cx.attach();
    
    next.run(request).await
}
```

---

### Q4.2: 跨线程传播 Context 失败怎么办？

**A**: Context 不是自动传播的，需要显式传递：

```rust
use opentelemetry::Context;

// ❌ 错误：Context 丢失
std::thread::spawn(|| {
    // 这里获取不到父 Context
    let tracer = global::tracer("worker");
    let span = tracer.start("work");
});

// ✅ 正确：显式传递 Context
let cx = Context::current();
std::thread::spawn(move || {
    let _guard = cx.attach();
    
    let tracer = global::tracer("worker");
    let span = tracer.start("work"); // 会链接到父 Span
});

// Tokio 任务也需要
let cx = Context::current();
tokio::spawn(async move {
    let _guard = cx.attach();
    work().await;
});
```

---

### Q4.3: 如何在 Tokio 任务间传播 Context？

**A**: 使用 `task-local-extensions` 或显式传递：

```rust
// 方法1：显式传递（推荐）
#[instrument]
async fn parent_task() {
    let cx = Context::current();
    
    tokio::spawn(async move {
        let _guard = cx.attach();
        child_task().await;
    });
}

// 方法2：使用 tracing
#[instrument]
async fn with_tracing() {
    let span = tracing::Span::current();
    
    tokio::spawn(
        async move {
            child_task().await;
        }
        .instrument(span) // 传播 tracing span
    );
}
```

---

### Q4.4: gRPC 调用如何传播 Context？

**A**: 使用 Tonic interceptor：

```rust
use tonic::{Request, Status, metadata::MetadataMap};

// 客户端
#[derive(Clone)]
struct PropagationInterceptor;

impl tonic::service::Interceptor for PropagationInterceptor {
    fn call(&mut self, mut request: Request<()>) -> Result<Request<()>, Status> {
        let cx = Context::current();
        
        // 注入到 metadata
        let mut injector = HashMap::new();
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(&cx, &mut injector);
        });
        
        for (key, value) in injector {
            request.metadata_mut().insert(
                key.parse().unwrap(),
                value.parse().unwrap(),
            );
        }
        
        Ok(request)
    }
}

// 使用
let channel = Channel::from_static("http://[::1]:50051").connect().await?;
let client = MyServiceClient::with_interceptor(channel, PropagationInterceptor);

// 服务端
// 在 request handler 中提取
let metadata = request.metadata();
let mut extractor = HashMap::new();
for key_value in metadata.iter() {
    if let Ok(value) = key_value.1.to_str() {
        extractor.insert(key_value.0.as_str().to_string(), value.to_string());
    }
}

let parent_cx = global::get_text_map_propagator(|propagator| {
    propagator.extract(&extractor)
});
```

---

## 5. 性能问题

### Q5.1: OTLP 会影响应用性能吗？

**A**: 正常情况下影响很小（< 5%），优化建议：

**性能影响因素**：

- ✅ Span 创建：~100-500ns（几乎无影响）
- ⚠️ 属性添加：取决于数量和类型
- ⚠️ 采样：如果采样率过高会有影响
- ⚠️ 导出：批量导出降低影响

**基准测试结果**：

```rust
// 无追踪
fn no_tracing() {
    work(); // 100 µs
}

// 有追踪（采样率 100%）
fn with_tracing() {
    let mut span = tracer.start("work");
    work(); // 105 µs (+5%)
    span.end();
}

// 有追踪（采样率 10%）
fn with_sampling() {
    let mut span = tracer.start("work");
    work(); // 100.5 µs (+0.5%)
    span.end();
}
```

---

### Q5.2: 如何减少追踪开销？

**A**: 优化策略：

**1. 降低采样率**：

```rust
.with_sampler(Sampler::TraceIdRatioBased(0.1)) // 10%
```

**2. 减少属性数量**：

```rust
// ❌ 过多属性
span.set_attributes(vec![
    KeyValue::new("attr1", "value1"),
    // ... 50+ 个属性
]);

// ✅ 只记录关键属性
span.set_attributes(vec![
    KeyValue::new("user.id", user_id),
    KeyValue::new("status", status),
]);
```

**3. 使用条件追踪**：

```rust
if should_trace() {
    let _span = tracer.start("expensive_operation");
    // ...
}
```

**4. 优化批量配置**：

```rust
BatchConfig::default()
    .with_max_export_batch_size(2048)  // 增大批量
    .with_scheduled_delay(Duration::from_secs(10))  // 延长间隔
```

**5. 缓存常用属性**：

```rust
static HTTP_METHOD_GET: OnceLock<KeyValue> = OnceLock::new();

fn get_method_attr() -> &'static KeyValue {
    HTTP_METHOD_GET.get_or_init(|| KeyValue::new("http.method", "GET"))
}
```

---

### Q5.3: 批量导出配置建议？

**A**: 根据场景选择配置：

**开发环境**（快速反馈）：

```rust
BatchConfig::default()
    .with_max_export_batch_size(128)
    .with_scheduled_delay(Duration::from_secs(1))
```

**生产环境**（平衡性能）：

```rust
BatchConfig::default()
    .with_max_queue_size(4096)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(Duration::from_secs(5))
    .with_max_export_timeout(Duration::from_secs(30))
```

**高吞吐量**（优先性能）：

```rust
BatchConfig::default()
    .with_max_queue_size(8192)
    .with_max_export_batch_size(2048)
    .with_scheduled_delay(Duration::from_secs(10))
```

**低延迟**（快速导出）：

```rust
BatchConfig::default()
    .with_max_queue_size(1024)
    .with_max_export_batch_size(256)
    .with_scheduled_delay(Duration::from_millis(500))
```

---

### Q5.4: 为什么内存使用增加了？

**A**: 常见原因和解决方案：

**原因1: 队列积压**:

```rust
// 问题：队列太大且未及时导出
.with_max_queue_size(100000)  // ❌ 过大

// 解决：合理设置
.with_max_queue_size(2048)  // ✅ 合理
```

**原因2: Span 泄漏**:

```rust
// ❌ Span 未结束
let span = tracer.start("operation");
// 忘记调用 span.end()

// ✅ 使用 RAII
{
    let _span = tracer.start("operation");
    // 作用域结束自动 drop
}
```

**原因3: 属性过多**:

```rust
// ❌ 大量字符串属性
for i in 0..10000 {
    span.set_attribute(KeyValue::new(format!("key_{}", i), "value"));
}

// ✅ 限制属性数量
const MAX_ATTRS: usize = 64;
```

**监控内存使用**：

```rust
use tokio::time::{interval, Duration};

tokio::spawn(async {
    let mut interval = interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        
        let stats = global::tracer_provider().get_stats();
        println!("Queue size: {}", stats.queue_size);
        
        if stats.queue_size > 5000 {
            eprintln!("Warning: Queue size too large!");
        }
    }
});
```

---

## 6. Metrics 相关

### Q6.1: 如何创建 Counter？

**A**: 完整示例：

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry::metrics::Counter;

// 1. 获取 Meter
let meter = global::meter("my-service");

// 2. 创建 Counter
let counter = meter
    .u64_counter("http.requests")
    .with_description("Total HTTP requests")
    .with_unit("requests")
    .init();

// 3. 记录值
counter.add(1, &[
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.status_code", 200),
]);

// 静态 Counter（推荐）
use std::sync::OnceLock;

static HTTP_REQUESTS: OnceLock<Counter<u64>> = OnceLock::new();

fn init_metrics() {
    let meter = global::meter("my-service");
    HTTP_REQUESTS.set(
        meter.u64_counter("http.requests").init()
    ).ok();
}

fn record_request(method: &str, status: u16) {
    if let Some(counter) = HTTP_REQUESTS.get() {
        counter.add(1, &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.status_code", status as i64),
        ]);
    }
}
```

---

### Q6.2: Histogram vs Gauge 如何选择？

**A**: 选择指南：

| 场景 | 使用 | 示例 |
|------|------|------|
| 测量持续时间 | Histogram | HTTP 请求延迟 |
| 测量大小 | Histogram | 响应体大小 |
| 测量分布 | Histogram | 数据库查询时间 |
| 当前状态值 | Gauge | CPU 使用率 |
| 队列长度 | Gauge | 待处理任务数 |
| 温度/压力 | Gauge | 系统温度 |

**Histogram 示例**：

```rust
let histogram = meter
    .f64_histogram("http.request.duration")
    .with_description("HTTP request duration in seconds")
    .with_unit("s")
    .init();

let start = Instant::now();
// 处理请求
let duration = start.elapsed().as_secs_f64();
histogram.record(duration, &[
    KeyValue::new("http.method", "GET"),
]);
```

**Gauge 示例**：

```rust
let gauge = meter
    .i64_observable_gauge("process.cpu.usage")
    .with_description("Current CPU usage")
    .with_unit("%")
    .with_callback(|observer| {
        let cpu_usage = get_cpu_usage();
        observer.observe(cpu_usage, &[]);
    })
    .init();
```

---

### Q6.3: Metrics 为什么没有数据？

**A**: 检查清单：

1. **是否初始化 MeterProvider**:

    ```rust
    let meter_provider = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .build()?;

    global::set_meter_provider(meter_provider);
    ```

2. **是否定期读取**:

    ```rust
    // Metrics 需要定期读取才会导出
    use tokio::time::{interval, Duration};

    tokio::spawn(async {
        let mut interval = interval(Duration::from_secs(10));
        loop {
            interval.tick().await;
            // Metrics 会在这里被收集和导出
        }
    });
    ```

3. **Observable Gauge 是否注册回调**:

    ```rust
    // ❌ 忘记 with_callback
    let gauge = meter.i64_observable_gauge("memory").init();

    // ✅ 正确
    let gauge = meter
        .i64_observable_gauge("memory")
        .with_callback(|observer| {
            observer.observe(get_memory_usage(), &[]);
        })
        .init();
    ```

4. **检查 Collector 配置**:

    ```yaml
    # otel-collector-config.yaml
    receivers:
    otlp:
        protocols:
        grpc:
            endpoint: 0.0.0.0:4317

    exporters:
    prometheus:
        endpoint: "0.0.0.0:8889"

    service:
    pipelines:
        metrics:
        receivers: [otlp]
        exporters: [prometheus]
    ```

---

### Q6.4: 如何控制 Metrics 基数？

**A**: 基数控制策略：

**问题示例**（高基数）：

```rust
// ❌ 用户 ID 作为标签 -> 百万级基数
counter.add(1, &[
    KeyValue::new("user.id", user_id.to_string()),
]);
```

**解决方案**：

**1. 使用分类**：

```rust
// ✅ 用户类型代替 ID
let user_type = if user.is_premium() { "premium" } else { "free" };
counter.add(1, &[
    KeyValue::new("user.type", user_type),
]);
```

**2. 限制标签数量**：

```rust
const MAX_LABELS: usize = 10;

fn get_safe_labels(labels: Vec<KeyValue>) -> Vec<KeyValue> {
    labels.into_iter().take(MAX_LABELS).collect()
}
```

**3. 使用哈希桶**：

```rust
// 将高基数值映射到固定数量的桶
fn hash_to_bucket(value: &str, num_buckets: usize) -> usize {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    (hasher.finish() % num_buckets as u64) as usize
}

let bucket = hash_to_bucket(&user_id.to_string(), 100);
counter.add(1, &[
    KeyValue::new("user.bucket", bucket as i64),
]);
```

**4. 动态采样**：

```rust
// 只记录部分高基数值
if should_record_metric(&user_id) {
    counter.add(1, &[KeyValue::new("user.id", user_id.to_string())]);
}
```

---

## 7. 错误处理

### Q7.1: 连接 Collector 失败怎么办？

**A**: 诊断步骤：

**1. 检查 Collector 是否运行**:

```bash
# 检查进程
docker ps | grep collector

# 检查端口
netstat -an | grep 4317  # gRPC
netstat -an | grep 4318  # HTTP

# 测试连接
curl http://localhost:4318/v1/traces
```

**2. 检查网络配置**:

```rust
// 确保端点正确
.with_endpoint("http://localhost:4317")  // ✅
.with_endpoint("localhost:4317")         // ❌ 缺少协议
.with_endpoint("https://localhost:4317") // ❌ 协议错误（应该是 http）
```

**3. 容器网络问题**:

```bash
# Docker 容器中使用 host.docker.internal
export OTEL_EXPORTER_OTLP_ENDPOINT=http://host.docker.internal:4317

# Kubernetes 使用服务名
export OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector.default.svc.cluster.local:4317
```

**4. 添加重试逻辑**:

```rust
use opentelemetry_otlp::WithExportConfig;

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(10));
```

**5. 降级方案**:

```rust
// 如果连接失败，使用 stdout exporter
let provider = match opentelemetry_otlp::new_pipeline()
    .tracing()
    .install_batch(opentelemetry_sdk::runtime::Tokio)
{
    Ok(provider) => provider,
    Err(e) => {
        eprintln!("Failed to connect to OTLP collector: {}", e);
        eprintln!("Falling back to stdout exporter");
        opentelemetry_stdout::new_pipeline().install_simple()
    }
};
```

---

### Q7.2: 如何处理导出失败？

**A**: 实现错误处理和重试：

```rust
// 自定义错误处理
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};

struct RetryExporter<E> {
    inner: E,
    max_retries: usize,
}

#[async_trait::async_trait]
impl<E: SpanExporter> SpanExporter for RetryExporter<E> {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry_sdk::export::trace::ExportResult {
        let mut retries = 0;
        
        loop {
            match self.inner.export(batch.clone()).await {
                Ok(()) => return Ok(()),
                Err(e) if retries < self.max_retries => {
                    retries += 1;
                    eprintln!("Export failed (attempt {}): {}", retries, e);
                    tokio::time::sleep(Duration::from_secs(2u64.pow(retries as u32))).await;
                }
                Err(e) => {
                    eprintln!("Export failed after {} retries: {}", self.max_retries, e);
                    return Err(e);
                }
            }
        }
    }
}

// 监控导出失败
use opentelemetry::global;

tokio::spawn(async {
    let mut interval = interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        
        // 检查导出统计
        if let Some(stats) = global::tracer_provider().get_export_stats() {
            if stats.failed > 0 {
                eprintln!("Export failures: {}", stats.failed);
            }
        }
    }
});
```

---

### Q7.3: panic 会影响追踪吗？

**A**: 是的，但可以处理：

```rust
use std::panic::{catch_unwind, AssertUnwindSafe};

// 方法1：捕获 panic
fn safe_trace<F>(f: F)
where
    F: FnOnce() + std::panic::UnwindSafe,
{
    let tracer = global::tracer("my-service");
    let mut span = tracer.start("operation");
    
    let result = catch_unwind(AssertUnwindSafe(|| f()));
    
    match result {
        Ok(_) => span.set_status(Status::Ok),
        Err(panic_info) => {
            let panic_msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "Unknown panic".to_string()
            };
            
            span.set_status(Status::Error {
                description: panic_msg.into(),
            });
            span.set_attribute(KeyValue::new("error.type", "panic"));
        }
    }
    
    span.end();
}

// 方法2：全局 panic hook
use std::panic;

fn setup_panic_handler() {
    panic::set_hook(Box::new(|panic_info| {
        let tracer = global::tracer("panic-handler");
        let mut span = tracer.start("panic");
        
        span.set_attribute(KeyValue::new("panic.message", panic_info.to_string()));
        
        if let Some(location) = panic_info.location() {
            span.set_attribute(KeyValue::new("panic.file", location.file().to_string()));
            span.set_attribute(KeyValue::new("panic.line", location.line() as i64));
        }
        
        span.end();
        
        // 强制刷新
        global::tracer_provider().force_flush();
    }));
}
```

---

### Q7.4: 证书验证失败怎么办？

**A**: TLS 配置：

```rust
use tonic::transport::{Certificate, ClientTlsConfig};

// 方法1：使用自签名证书
let cert = tokio::fs::read("ca.pem").await?;
let cert = Certificate::from_pem(cert);

let tls = ClientTlsConfig::new()
    .ca_certificate(cert)
    .domain_name("otel-collector");

let channel = Channel::from_static("https://collector:4317")
    .tls_config(tls)?
    .connect()
    .await?;

// 方法2：跳过验证（仅开发环境）
let tls = ClientTlsConfig::new()
    .danger_accept_invalid_certs(true);  // ⚠️ 不安全

// 方法3：使用环境变量
std::env::set_var("OTEL_EXPORTER_OTLP_CERTIFICATE", "/path/to/ca.pem");
std::env::set_var("OTEL_EXPORTER_OTLP_INSECURE", "true");  // HTTP 模式
```

---

## 8. 集成问题

### Q8.1: 如何集成 Axum？

**A**: 完整集成示例：

```rust
use axum::{
    Router,
    routing::get,
    middleware,
    extract::Request,
    response::Response,
};
use tower_http::trace::TraceLayer;

// 方法1：使用 tower-http（推荐）
fn app() -> Router {
    Router::new()
        .route("/users", get(list_users))
        .layer(TraceLayer::new_for_http())
}

// 方法2：自定义中间件
async fn tracing_middleware(
    request: Request,
    next: middleware::Next,
) -> Response {
    let tracer = global::tracer("http-server");
    
    let mut span = tracer
        .span_builder(format!("{} {}", request.method(), request.uri().path()))
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    let response = next.run(request).await;
    
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    span.end();
    
    response
}

fn app_with_custom_middleware() -> Router {
    Router::new()
        .route("/users", get(list_users))
        .layer(middleware::from_fn(tracing_middleware))
}

// 启动服务器
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    let app = app();
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

---

### Q8.2: 如何集成 Tonic (gRPC)？

**A**: gRPC 服务追踪：

```rust
use tonic::{transport::Server, Request, Response, Status};

// 定义拦截器
#[derive(Clone)]
struct TracingInterceptor;

impl tonic::service::Interceptor for TracingInterceptor {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        let tracer = global::tracer("grpc-server");
        
        // 提取 metadata 中的 context
        let metadata = request.metadata();
        let mut extractor = HashMap::new();
        for key_value in metadata.iter() {
            if let Ok(value) = key_value.1.to_str() {
                extractor.insert(key_value.0.as_str().to_string(), value.to_string());
            }
        }
        
        let parent_cx = global::get_text_map_propagator(|propagator| {
            propagator.extract(&extractor)
        });
        
        let _guard = parent_cx.attach();
        
        let span = tracer
            .span_builder("grpc.request")
            .with_kind(SpanKind::Server)
            .start(&tracer);
        
        // 存储 span 到 extensions
        let mut request = request;
        request.extensions_mut().insert(span);
        
        Ok(request)
    }
}

// 使用拦截器
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    let addr = "[::1]:50051".parse()?;
    
    Server::builder()
        .add_service(
            MyServiceServer::with_interceptor(
                MyService::default(),
                TracingInterceptor,
            )
        )
        .serve(addr)
        .await?;
    
    Ok(())
}
```

---

### Q8.3: 如何集成数据库追踪？

**A**: SQLx 集成示例：

```rust
use sqlx::{PgPool, Row};
use tracing::instrument;

#[instrument(skip(pool))]
async fn get_user(pool: &PgPool, user_id: i64) -> Result<User, sqlx::Error> {
    let row = sqlx::query("SELECT * FROM users WHERE id = $1")
        .bind(user_id)
        .fetch_one(pool)
        .await?;
    
    Ok(User {
        id: row.get("id"),
        name: row.get("name"),
    })
}

// 或者手动创建 Span
async fn get_user_manual(pool: &PgPool, user_id: i64) -> Result<User, sqlx::Error> {
    let tracer = global::tracer("database");
    let mut span = tracer
        .span_builder("db.query")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"));
    span.set_attribute(KeyValue::new("db.user", user_id));
    
    let result = sqlx::query("SELECT * FROM users WHERE id = $1")
        .bind(user_id)
        .fetch_one(pool)
        .await;
    
    match &result {
        Ok(_) => span.set_status(Status::Ok),
        Err(e) => {
            span.record_error(e);
            span.set_status(Status::Error {
                description: e.to_string().into(),
            });
        }
    }
    
    span.end();
    
    result.map(|row| User {
        id: row.get("id"),
        name: row.get("name"),
    })
}
```

---

### Q8.4: 如何与 tracing crate 集成？

**A**: 完整集成：

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_tracing() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    opentelemetry::global::set_tracer_provider(tracer.clone());
    
    // 2. 创建 OpenTelemetry layer
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer.tracer("my-service"));
    
    // 3. 创建 fmt layer（控制台输出）
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_target(true)
        .with_thread_ids(true);
    
    // 4. 组合 layers
    tracing_subscriber::registry()
        .with(telemetry_layer)
        .with(fmt_layer)
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}

// 使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_tracing()?;
    
    // 现在可以使用 tracing 宏
    tracing::info!("Application started");
    
    process_request().await?;
    
    global::shutdown_tracer_provider();
    
    Ok(())
}

#[tracing::instrument]
async fn process_request() -> Result<(), Error> {
    tracing::info!("Processing request");
    
    let result = risky_operation().await?;
    
    tracing::info!(result = ?result, "Request processed successfully");
    
    Ok(())
}
```

---

## 9. 测试

### Q9.1: 如何在测试中使用 OTLP？

**A**: 测试配置：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    fn init_test_telemetry() {
        // 使用 stdout exporter 用于测试
        let tracer = opentelemetry_stdout::new_pipeline()
            .install_simple();
        
        global::set_tracer_provider(tracer);
    }

    #[tokio::test]
    async fn test_with_tracing() {
        init_test_telemetry();
        
        let tracer = global::tracer("test");
        let span = tracer.start("test_operation");
        
        // 测试逻辑
        
        drop(span);
    }

    // 或者使用 in-memory exporter
    use opentelemetry_sdk::export::trace::{SpanData, SpanExporter};
    use std::sync::{Arc, Mutex};

    #[derive(Clone)]
    struct InMemoryExporter {
        spans: Arc<Mutex<Vec<SpanData>>>,
    }

    impl InMemoryExporter {
        fn new() -> Self {
            Self {
                spans: Arc::new(Mutex::new(Vec::new())),
            }
        }

        fn get_spans(&self) -> Vec<SpanData> {
            self.spans.lock().unwrap().clone()
        }
    }

    #[async_trait::async_trait]
    impl SpanExporter for InMemoryExporter {
        async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry_sdk::export::trace::ExportResult {
            self.spans.lock().unwrap().extend(batch);
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_span_creation() {
        let exporter = InMemoryExporter::new();
        
        let provider = TracerProvider::builder()
            .with_simple_exporter(exporter.clone())
            .build();
        
        let tracer = provider.tracer("test");
        
        let span = tracer.start("test_span");
        drop(span);
        
        provider.force_flush();
        
        let spans = exporter.get_spans();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].name, "test_span");
    }
}
```

---

### Q9.2: 如何验证 Span 是否正确创建？

**A**: 断言辅助函数：

```rust
#[cfg(test)]
mod test_helpers {
    use opentelemetry_sdk::export::trace::SpanData;
    
    pub struct SpanAsserter<'a> {
        span: &'a SpanData,
    }
    
    impl<'a> SpanAsserter<'a> {
        pub fn new(span: &'a SpanData) -> Self {
            Self { span }
        }
        
        pub fn has_name(self, name: &str) -> Self {
            assert_eq!(self.span.name, name);
            self
        }
        
        pub fn has_attribute(self, key: &str, value: &str) -> Self {
            let found = self.span.attributes.iter()
                .any(|kv| kv.key.as_str() == key && kv.value.as_str() == value);
            assert!(found, "Attribute {}={} not found", key, value);
            self
        }
        
        pub fn has_status_ok(self) -> Self {
            assert_eq!(self.span.status, Status::Ok);
            self
        }
        
        pub fn has_error(self) -> Self {
            assert!(matches!(self.span.status, Status::Error { .. }));
            self
        }
    }
}

// 使用
#[tokio::test]
async fn test_error_span() {
    let exporter = InMemoryExporter::new();
    // ... setup ...
    
    let spans = exporter.get_spans();
    
    SpanAsserter::new(&spans[0])
        .has_name("error_operation")
        .has_attribute("error.type", "database")
        .has_error();
}
```

---

### Q9.3: 集成测试如何配置？

**A**: 使用 testcontainers：

```rust
#[cfg(test)]
mod integration_tests {
    use testcontainers::{clients, images::generic::GenericImage};

    #[tokio::test]
    async fn test_e2e_tracing() {
        let docker = clients::Cli::default();
        
        // 启动 Jaeger
        let jaeger = docker.run(
            GenericImage::new("jaegertracing/all-in-one", "latest")
                .with_exposed_port(4317)
                .with_exposed_port(16686)
                .with_env_var("COLLECTOR_OTLP_ENABLED", "true")
        );
        
        let otlp_port = jaeger.get_host_port_ipv4(4317);
        
        // 配置 tracer
        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint(format!("http://localhost:{}", otlp_port))
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)
            .unwrap();
        
        global::set_tracer_provider(tracer);
        
        // 执行测试
        let tracer = global::tracer("test");
        let span = tracer.start("integration_test");
        drop(span);
        
        // 等待导出
        tokio::time::sleep(Duration::from_secs(2)).await;
        
        // 验证（通过 Jaeger API）
        let query_port = jaeger.get_host_port_ipv4(16686);
        let response = reqwest::Client::new()
            .get(format!("http://localhost:{}/api/traces?service=test", query_port))
            .send()
            .await
            .unwrap();
        
        assert!(response.status().is_success());
    }
}
```

---

## 10. 生产部署

### Q10.1: 生产环境推荐配置？

**A**: 生产级配置：

```rust
use opentelemetry_sdk::trace::{Config, BatchConfig, Sampler};
use opentelemetry_sdk::Resource;
use std::time::Duration;

pub fn init_production_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // 资源配置
    let resource = Resource::new(vec![
        KeyValue::new("service.name", std::env::var("SERVICE_NAME")?),
        KeyValue::new("service.version", std::env::var("SERVICE_VERSION")?),
        KeyValue::new("deployment.environment", "production"),
    ]);
    
    // 采样配置（10% 采样率）
    let sampler = Sampler::ParentBased(
        Box::new(Sampler::TraceIdRatioBased(0.1))
    );
    
    // 批处理配置
    let batch_config = BatchConfig::default()
        .with_max_queue_size(4096)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .with_max_export_timeout(Duration::from_secs(30));
    
    // Trace 配置
    let trace_config = Config::default()
        .with_sampler(sampler)
        .with_resource(resource)
        .with_max_attributes_per_span(64)
        .with_max_events_per_span(128);
    
    // 创建 exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")?)
        .with_timeout(Duration::from_secs(10));
    
    // 创建 provider
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .with_trace_config(trace_config)
        .with_batch_config(batch_config)
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer);
    
    Ok(())
}
```

---

### Q10.2: 如何实现优雅关闭？

**A**: 完整的优雅关闭实现：

```rust
use tokio::signal;
use tokio::sync::oneshot;

pub async fn run_with_graceful_shutdown<F, Fut>(
    app: F
) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnOnce(oneshot::Receiver<()>) -> Fut,
    Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
{
    let (shutdown_tx, shutdown_rx) = oneshot::channel();
    
    // 监听关闭信号
    tokio::spawn(async move {
        signal::ctrl_c().await.expect("Failed to listen for CTRL+C");
        println!("Received shutdown signal");
        shutdown_tx.send(()).ok();
    });
    
    // 运行应用
    let result = app(shutdown_rx).await;
    
    // 关闭 telemetry
    println!("Shutting down telemetry...");
    global::shutdown_tracer_provider();
    
    // 等待最后的数据导出
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    println!("Shutdown complete");
    result
}

// 使用
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;
    
    run_with_graceful_shutdown(|shutdown_rx| async move {
        let app = create_app();
        
        let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
        
        axum::serve(listener, app)
            .with_graceful_shutdown(async move {
                shutdown_rx.await.ok();
            })
            .await?;
        
        Ok(())
    }).await
}
```

---

### Q10.3: 如何监控 OTLP 健康状态？

**A**: 健康检查实现：

```rust
use axum::{Json, routing::get};
use serde::Serialize;

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    telemetry: TelemetryHealth,
}

#[derive(Serialize)]
struct TelemetryHealth {
    tracing_enabled: bool,
    metrics_enabled: bool,
    last_export_time: Option<String>,
    queue_size: usize,
    export_errors: usize,
}

async fn health_check() -> Json<HealthResponse> {
    // 检查 tracer 状态
    let tracing_enabled = {
        let tracer = global::tracer("health");
        tracer.start("test").span_context().is_valid()
    };
    
    // 检查队列状态
    let (queue_size, export_errors) = {
        // 获取统计信息（需要自定义实现）
        (0, 0) // 占位符
    };
    
    let status = if tracing_enabled && export_errors == 0 {
        "healthy"
    } else {
        "degraded"
    };
    
    Json(HealthResponse {
        status: status.to_string(),
        telemetry: TelemetryHealth {
            tracing_enabled,
            metrics_enabled: true,
            last_export_time: Some(chrono::Utc::now().to_rfc3339()),
            queue_size,
            export_errors,
        },
    })
}

fn app() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/metrics", get(prometheus_metrics))
}
```

---

### Q10.4: Docker 容器中注意事项？

**A**: Docker 最佳实践：

**Dockerfile**：

```dockerfile
FROM rust:1.90 as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 生产构建
RUN cargo build --release

FROM debian:bookworm-slim

# 安装 CA 证书（用于 HTTPS）
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/myapp /usr/local/bin/

# 环境变量
ENV RUST_LOG=info
ENV OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
ENV OTEL_SERVICE_NAME=myapp

CMD ["myapp"]
```

**docker-compose.yml**：

```yaml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "3000:3000"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
      - OTEL_SERVICE_NAME=myapp
    depends_on:
      - jaeger

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "4317:4317"  # OTLP gRPC
      - "16686:16686"  # Jaeger UI
    environment:
      - COLLECTOR_OTLP_ENABLED=true
```

**注意事项**：

1. **使用服务名而不是 localhost**:

    ```rust
    // ❌ 错误
    .with_endpoint("http://localhost:4317")

    // ✅ 正确
    .with_endpoint("http://jaeger:4317")
    ```

2. **设置合理的超时**:

    ```rust
    .with_timeout(Duration::from_secs(10))
    ```

3. **优雅关闭**:

    ```bash
    # Dockerfile
    STOPSIGNAL SIGTERM
    ```

---

## 11. 升级与迁移

### Q11.1: 如何从旧版本升级？

**A**: 升级步骤：

**从 0.20.x 升级到 0.31.0**：

1. **更新依赖**:

    ```toml
    # 旧版本
    opentelemetry = "0.20"
    opentelemetry-otlp = "0.13"

    # 新版本
    opentelemetry = "0.31.0"
    opentelemetry-otlp = "0.31.0"
    opentelemetry-sdk = "0.31.0"
    ```

2. **API 变更**:

    ```rust
    // 旧版本
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(opentelemetry_otlp::new_exporter().tonic())
        .install_batch(opentelemetry::runtime::Tokio)?;

    // 新版本
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    ```

3. **运行测试**:

    ```bash
    cargo test
    ```

---

### Q11.2: Breaking Changes 有哪些？

**A**: 主要变更：

**0.31.0 主要变更**：

1. **运行时模块移动**:

    ```rust
    // 旧
    opentelemetry::runtime::Tokio

    // 新
    opentelemetry_sdk::runtime::Tokio
    ```

2. **TracerProvider 变更**:

    ```rust
    // 旧
    use opentelemetry::sdk::trace::TracerProvider;

    // 新
    use opentelemetry_sdk::trace::TracerProvider;
    ```

3. **配置 API 变更**:

    ```rust
    // 旧
    .with_trace_config(
        opentelemetry::sdk::trace::config()
            .with_sampler(Sampler::AlwaysOn)
    )

    // 新
    .with_trace_config(
        opentelemetry_sdk::trace::Config::default()
            .with_sampler(opentelemetry_sdk::trace::Sampler::AlwaysOn)
    )
    ```

---

### Q11.3: 如何从其他追踪系统迁移？

**A**: 迁移指南：

**从 Jaeger Client 迁移**：

```rust
// 旧代码（Jaeger）
use jaeger_client::Tracer;

let tracer = Tracer::builder()
    .with_service_name("myapp")
    .build();

// 新代码（OTLP）
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317")
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

**从 Zipkin 迁移**：

```rust
// 旧代码（Zipkin）
use zipkin::Tracer;

// 新代码（OTLP）
// 相同的代码，但配置不同的后端
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://zipkin:9411")  // Zipkin endpoint
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

---

## 12. 高级用法

### Q12.1: 如何实现自定义 Sampler？

**A**: 实现 Sampler trait：

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};
use opentelemetry::trace::{TraceId, SpanKind, Link};
use opentelemetry::Context;

pub struct CustomSampler {
    default_rate: f64,
}

impl Sampler for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[opentelemetry::KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 自定义采样逻辑
        let should_sample = match span_kind {
            SpanKind::Server => true,  // 总是采样服务端 Span
            SpanKind::Client => {
                // 只采样慢请求
                attributes.iter().any(|kv| {
                    kv.key.as_str() == "duration_ms" 
                    && kv.value.as_i64() > 1000
                })
            }
            _ => rand::random::<f64>() < self.default_rate,
        };
        
        SamplingResult {
            decision: if should_sample {
                SamplingDecision::RecordAndSample
            } else {
                SamplingDecision::Drop
            },
            attributes: vec![],
            trace_state: None,
        }
    }
}
```

---

### Q12.2: 如何实现自定义 Exporter？

**A**: 实现 SpanExporter trait：

```rust
use opentelemetry_sdk::export::trace::{SpanData, SpanExporter, ExportResult};

pub struct CustomExporter {
    client: reqwest::Client,
    endpoint: String,
}

#[async_trait::async_trait]
impl SpanExporter for CustomExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 自定义导出逻辑
        let response = self.client
            .post(&self.endpoint)
            .json(&batch)
            .send()
            .await
            .map_err(|e| opentelemetry::trace::TraceError::from(e.to_string()))?;
        
        if response.status().is_success() {
            Ok(())
        } else {
            Err(opentelemetry::trace::TraceError::from(
                format!("Export failed: {}", response.status())
            ))
        }
    }
}
```

---

### Q12.3: 如何修改 Span 在导出前？

**A**: 使用自定义 SpanProcessor：

```rust
use opentelemetry_sdk::trace::{SpanProcessor, SpanData};
use opentelemetry_sdk::Context;

pub struct FilteringProcessor<P> {
    inner: P,
}

impl<P: SpanProcessor> SpanProcessor for FilteringProcessor<P> {
    fn on_start(&self, span: &mut opentelemetry_sdk::trace::Span, cx: &Context) {
        self.inner.on_start(span, cx);
    }

    fn on_end(&self, mut span: SpanData) {
        // 修改 Span
        // 例如：移除敏感属性
        span.attributes.retain(|kv| {
            !kv.key.as_str().contains("password")
            && !kv.key.as_str().contains("secret")
        });
        
        self.inner.on_end(span);
    }

    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.shutdown()
    }
}
```

---

## 🔗 参考资源

- [OpenTelemetry Rust 官方文档](https://docs.rs/opentelemetry/)
- [OTLP 规范](https://opentelemetry.io/docs/specs/otlp/)
- [Rust OTLP 快速入门](./01_Rust_OTLP_30分钟快速入门.md)
- [Rust OTLP 常见模式](./02_Rust_OTLP_常见模式.md)
- [Rust OTLP 最佳实践](../17_最佳实践清单/Rust_OTLP_最佳实践Checklist.md)
- [GitHub Issues](https://github.com/open-telemetry/opentelemetry-rust/issues)
- [Discord Community](https://discord.gg/opentelemetry)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [📚 快速入门](./01_Rust_OTLP_30分钟快速入门.md) | [🎯 常见模式](./02_Rust_OTLP_常见模式.md)
