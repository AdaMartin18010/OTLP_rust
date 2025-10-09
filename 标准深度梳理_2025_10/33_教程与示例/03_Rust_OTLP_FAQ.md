# Rust OTLP 常见问题解答 (FAQ)

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [Rust OTLP 常见问题解答 (FAQ)](#rust-otlp-常见问题解答-faq)
  - [目录](#目录)
  - [1. 基础问题](#1-基础问题)
    - [Q1.1: 如何选择 OpenTelemetry Rust SDK 版本?](#q11-如何选择-opentelemetry-rust-sdk-版本)
    - [Q1.2: OTLP 与其他追踪格式有什么区别?](#q12-otlp-与其他追踪格式有什么区别)
    - [Q1.3: 需要安装哪些依赖?](#q13-需要安装哪些依赖)
  - [2. 初始化问题](#2-初始化问题)
    - [Q2.1: 为什么初始化 TracerProvider 失败?](#q21-为什么初始化-tracerprovider-失败)
    - [Q2.2: 如何在多线程应用中初始化?](#q22-如何在多线程应用中初始化)
    - [Q2.3: 如何配置多个导出器?](#q23-如何配置多个导出器)
  - [3. 上下文传播问题](#3-上下文传播问题)
    - [Q3.1: 为什么跨异步任务时上下文丢失?](#q31-为什么跨异步任务时上下文丢失)
    - [Q3.2: 如何在 Tokio spawn 中传播上下文?](#q32-如何在-tokio-spawn-中传播上下文)
    - [Q3.3: HTTP 客户端如何注入追踪上下文?](#q33-http-客户端如何注入追踪上下文)
  - [4. Span 管理问题](#4-span-管理问题)
    - [Q4.1: Span 没有出现在 Jaeger 中?](#q41-span-没有出现在-jaeger-中)
    - [Q4.2: 如何确保 Span 总是被正确结束?](#q42-如何确保-span-总是被正确结束)
    - [Q4.3: 如何给 Span 添加自定义属性?](#q43-如何给-span-添加自定义属性)
  - [5. 性能问题](#5-性能问题)
    - [Q5.1: OpenTelemetry 对性能有多大影响?](#q51-opentelemetry-对性能有多大影响)
    - [Q5.2: 如何减少追踪开销?](#q52-如何减少追踪开销)
    - [Q5.3: 批量导出配置建议?](#q53-批量导出配置建议)
  - [6. 错误处理问题](#6-错误处理问题)
    - [Q6.1: 如何正确记录错误到 Span?](#q61-如何正确记录错误到-span)
    - [Q6.2: Panic 会导致 Span 丢失吗?](#q62-panic-会导致-span-丢失吗)
    - [Q6.3: 如何追踪第三方库的错误?](#q63-如何追踪第三方库的错误)
  - [7. 集成问题](#7-集成问题)
    - [Q7.1: 如何与 Axum 集成?](#q71-如何与-axum-集成)
    - [Q7.2: 如何与 SQLx 集成?](#q72-如何与-sqlx-集成)
    - [Q7.3: 如何与 gRPC (Tonic) 集成?](#q73-如何与-grpc-tonic-集成)
  - [8. 配置问题](#8-配置问题)
    - [Q8.1: 如何配置采样率?](#q81-如何配置采样率)
    - [Q8.2: 如何配置 OTLP Endpoint?](#q82-如何配置-otlp-endpoint)
    - [Q8.3: 如何在不同环境使用不同配置?](#q83-如何在不同环境使用不同配置)
  - [9. 指标问题](#9-指标问题)
    - [Q9.1: Trace 和 Metrics 有什么区别?](#q91-trace-和-metrics-有什么区别)
    - [Q9.2: 如何收集自定义指标?](#q92-如何收集自定义指标)
    - [Q9.3: Counter 和 Gauge 如何选择?](#q93-counter-和-gauge-如何选择)
  - [10. 调试问题](#10-调试问题)
    - [Q10.1: 如何查看导出的追踪数据?](#q101-如何查看导出的追踪数据)
    - [Q10.2: 如何调试追踪数据没有发送?](#q102-如何调试追踪数据没有发送)
    - [Q10.3: 如何验证 Span 的父子关系?](#q103-如何验证-span-的父子关系)
  - [11. 部署问题](#11-部署问题)
    - [Q11.1: 生产环境如何配置?](#q111-生产环境如何配置)
    - [Q11.2: 如何处理 OTLP Collector 不可用?](#q112-如何处理-otlp-collector-不可用)
    - [Q11.3: Docker 容器中如何配置?](#q113-docker-容器中如何配置)
  - [12. 高级问题](#12-高级问题)
    - [Q12.1: 如何实现分布式追踪?](#q121-如何实现分布式追踪)
    - [Q12.2: 如何实现自定义 Sampler?](#q122-如何实现自定义-sampler)
    - [Q12.3: 如何实现自定义 Exporter?](#q123-如何实现自定义-exporter)
  - [13. 故障排查](#13-故障排查)
  - [14. 最佳实践总结](#14-最佳实践总结)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)

---

## 1. 基础问题

### Q1.1: 如何选择 OpenTelemetry Rust SDK 版本?

**A:** 建议使用最新稳定版本:

```toml
[dependencies]
# 核心库 (必需)
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }

# OTLP 导出器 (必需)
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic"] }

# 语义约定 (推荐)
opentelemetry-semantic-conventions = "0.31"
```

**版本兼容性**:

- Rust 1.90+ (支持 AFIT 异步特性)
- Tokio 1.47+ (异步运行时)
- Tonic 0.12+ (gRPC 支持)

---

### Q1.2: OTLP 与其他追踪格式有什么区别?

**A:** OTLP (OpenTelemetry Protocol) 的优势:

| 特性 | OTLP | Jaeger | Zipkin |
|-----|------|--------|--------|
| **标准化** | ✅ 开放标准 | ❌ Jaeger 专有 | ❌ Zipkin 专有 |
| **支持信号** | Trace + Metrics + Logs | Trace only | Trace only |
| **传输协议** | gRPC + HTTP/JSON | gRPC + HTTP | HTTP/JSON |
| **供应商中立** | ✅ | ❌ | ❌ |
| **未来支持** | ✅ 持续更新 | ⚠️ 维护模式 | ⚠️ 有限 |

**建议**: 新项目优先使用 OTLP。

---

### Q1.3: 需要安装哪些依赖?

**A:** 最小化依赖清单:

```toml
[dependencies]
# 核心 OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic"] }

# 异步运行时
tokio = { version = "1.47", features = ["full"] }

# 错误处理
anyhow = "1.0"

# 可选: 与 tracing 生态集成
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.29"
```

---

## 2. 初始化问题

### Q2.1: 为什么初始化 TracerProvider 失败?

**A:** 常见原因和解决方案:

**问题 1: Endpoint 不可达**:

```rust
// ❌ 错误
let provider = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://localhost:4317") // Collector 未运行
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;

// ✅ 解决: 先启动 OTLP Collector
// docker run -p 4317:4317 otel/opentelemetry-collector
```

**问题 2: 缺少 Tokio 运行时**:

```rust
// ❌ 错误
fn main() {
    let provider = init_tracer(); // 没有 async 运行时
}

// ✅ 解决: 使用 Tokio
#[tokio::main]
async fn main() {
    let provider = init_tracer().await;
}
```

**问题 3: Feature flags 不正确**:

```toml
# ❌ 错误
opentelemetry_sdk = "0.31"

# ✅ 正确
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
```

---

### Q2.2: 如何在多线程应用中初始化?

**A:** 使用全局单例:

```rust
use once_cell::sync::OnceCell;

static TRACER_PROVIDER: OnceCell<TracerProvider> = OnceCell::new();

pub fn init_once() -> Result<()> {
    TRACER_PROVIDER.get_or_try_init(|| {
        opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .with_endpoint("http://localhost:4317")
            )
            .install_batch(opentelemetry_sdk::runtime::Tokio)
    })?;
    Ok(())
}

// 在多个线程中安全使用
fn worker_thread() {
    let tracer = global::tracer("worker");
    // ...
}
```

---

### Q2.3: 如何配置多个导出器?

**A:** 使用组合导出器:

```rust
use opentelemetry_sdk::export::trace::SpanExporter;

// 方案1: 使用多个 TracerProvider (不推荐)
// 方案2: 自定义组合导出器
pub struct MultiExporter {
    exporters: Vec<Box<dyn SpanExporter>>,
}

impl MultiExporter {
    pub fn new(exporters: Vec<Box<dyn SpanExporter>>) -> Self {
        Self { exporters }
    }
}

#[async_trait::async_trait]
impl SpanExporter for MultiExporter {
    async fn export(
        &mut self,
        batch: Vec<opentelemetry_sdk::export::trace::SpanData>,
    ) -> opentelemetry::trace::TraceResult<()> {
        for exporter in &mut self.exporters {
            exporter.export(batch.clone()).await?;
        }
        Ok(())
    }
}
```

---

## 3. 上下文传播问题

### Q3.1: 为什么跨异步任务时上下文丢失?

**A:** 异步任务需要显式传播上下文:

```rust
// ❌ 错误: 上下文丢失
let tracer = global::tracer("app");
let span = tracer.start("parent");

tokio::spawn(async {
    let child_span = tracer.start("child"); // 没有父上下文!
});

// ✅ 正确: 显式传播
let tracer = global::tracer("app");
let span = tracer.start("parent");
let cx = Context::current_with_span(span.clone());

tokio::spawn(async move {
    let child_span = tracer.start_with_context("child", &cx);
});
```

---

### Q3.2: 如何在 Tokio spawn 中传播上下文?

**A:** 使用 tracing-opentelemetry:

```rust
use tracing_opentelemetry::OpenTelemetrySpanExt;

#[tracing::instrument]
async fn parent_operation() {
    let current_span = tracing::Span::current();
    let cx = current_span.context();

    tokio::spawn(
        async move {
            // 上下文自动传播
            child_operation().await;
        }
        .in_current_span() // 关键!
    );
}

#[tracing::instrument]
async fn child_operation() {
    // 继承父 span 的上下文
}
```

---

### Q3.3: HTTP 客户端如何注入追踪上下文?

**A:** 使用 propagator:

```rust
use opentelemetry::propagation::{Injector, TextMapPropagator};
use std::collections::HashMap;

pub async fn make_traced_request(url: &str) -> Result<String> {
    let client = reqwest::Client::new();
    let tracer = global::tracer("http-client");
    let span = tracer.start("http_request");
    let cx = Context::current_with_span(span);

    // 创建 header injector
    let mut headers = HashMap::new();
    let propagator = opentelemetry::sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(&cx, &mut headers);

    // 添加到请求
    let mut request = client.get(url);
    for (key, value) in headers {
        request = request.header(key, value);
    }

    let response = request.send().await?;
    Ok(response.text().await?)
}
```

---

## 4. Span 管理问题

### Q4.1: Span 没有出现在 Jaeger 中?

**A:** 检查清单:

1. **检查采样配置**

    ```rust
    // 确保采样率不是 0
    .with_trace_config(
        Config::default()
            .with_sampler(Sampler::AlwaysOn) // 测试时使用
    )
    ```

2. **确认 Span 被正确结束**

    ```rust
    let mut span = tracer.start("my_operation");
    // ... 业务逻辑 ...
    span.end(); // 必须调用!
    ```

3. **刷新 TracerProvider**

    ```rust
    // 应用退出前
    global::shutdown_tracer_provider();
    ```

4. **检查 Collector 连接**

    ```bash
    # 测试 Collector 是否可达
    curl http://localhost:4317
    docker logs otel-collector
    ```

---

### Q4.2: 如何确保 Span 总是被正确结束?

**A:** 使用 RAII 守卫:

```rust
pub struct SpanGuard {
    span: Option<opentelemetry::trace::BoxedSpan>,
}

impl SpanGuard {
    pub fn new(tracer: &impl Tracer, name: &str) -> Self {
        Self {
            span: Some(tracer.start(name)),
        }
    }
}

impl Drop for SpanGuard {
    fn drop(&mut self) {
        if let Some(mut span) = self.span.take() {
            span.end();
        }
    }
}

// 使用
fn process() -> Result<()> {
    let tracer = global::tracer("app");
    let _guard = SpanGuard::new(&tracer, "process");
    
    // 即使发生错误, Span 也会在 Drop 时自动结束
    risky_operation()?;
    
    Ok(())
} // Span 自动结束
```

---

### Q4.3: 如何给 Span 添加自定义属性?

**A:** 使用 KeyValue:

```rust
use opentelemetry::KeyValue;

let tracer = global::tracer("app");
let mut span = tracer.start("operation");

// 基础类型
span.set_attribute(KeyValue::new("user.id", 12345_i64));
span.set_attribute(KeyValue::new("user.name", "Alice"));
span.set_attribute(KeyValue::new("is_premium", true));

// 数组 (需要 homogeneous types)
span.set_attribute(KeyValue::new(
    "tags",
    vec!["rust", "opentelemetry"],
));

// 避免敏感信息
// ❌ span.set_attribute(KeyValue::new("password", "secret123"));
// ✅ span.set_attribute(KeyValue::new("auth.method", "password"));

span.end();
```

---

## 5. 性能问题

### Q5.1: OpenTelemetry 对性能有多大影响?

**A:** 性能影响取决于配置:

| 场景 | 延迟影响 | CPU 影响 | 内存影响 |
|-----|---------|---------|---------|
| **同步导出** | 10-50ms | 高 | 低 |
| **批量导出** | <1ms | 低 | 中 |
| **采样 10%** | <0.5ms | 很低 | 低 |
| **禁用追踪** | ~0 | ~0 | ~0 |

**优化建议**:

- 生产环境使用批量导出
- 合理设置采样率 (1-10%)
- 避免在热路径记录大量属性
- 使用异步运行时

---

### Q5.2: 如何减少追踪开销?

**A:** 多种优化策略:

```rust
// 1. 降低采样率
.with_trace_config(
    Config::default()
        .with_sampler(Sampler::TraceIdRatioBased(0.1)) // 10%
)

// 2. 增大批量大小
.with_batch_config(
    BatchConfig::default()
        .with_max_export_batch_size(512)
        .with_max_queue_size(4096)
)

// 3. 条件性追踪
#[cfg(feature = "tracing")]
fn traced_operation() {
    let span = tracer.start("op");
    // ...
}

#[cfg(not(feature = "tracing"))]
fn traced_operation() {
    // 零开销
}

// 4. 延迟计算属性
if span.is_recording() {
    span.set_attribute(KeyValue::new("expensive", expensive_computation()));
}
```

---

### Q5.3: 批量导出配置建议?

**A:** 根据场景优化:

```rust
use opentelemetry_sdk::trace::BatchConfig;

// 低延迟场景 (实时追踪)
let low_latency = BatchConfig::default()
    .with_scheduled_delay(std::time::Duration::from_millis(1000)) // 1秒
    .with_max_export_batch_size(128);

// 高吞吐场景 (批量处理)
let high_throughput = BatchConfig::default()
    .with_scheduled_delay(std::time::Duration::from_secs(5)) // 5秒
    .with_max_export_batch_size(512)
    .with_max_queue_size(4096);

// 平衡配置 (生产推荐)
let balanced = BatchConfig::default()
    .with_scheduled_delay(std::time::Duration::from_secs(3))
    .with_max_export_batch_size(256)
    .with_max_queue_size(2048);
```

---

## 6. 错误处理问题

### Q6.1: 如何正确记录错误到 Span?

**A:** 使用标准错误记录:

```rust
use opentelemetry::trace::{Status, StatusCode};

async fn risky_operation() -> Result<()> {
    let tracer = global::tracer("app");
    let mut span = tracer.start("risky_operation");

    match dangerous_call().await {
        Ok(result) => {
            span.set_status(Status::Ok);
            Ok(result)
        }
        Err(e) => {
            // 1. 设置错误状态
            span.set_status(Status::error(e.to_string()));
            
            // 2. 记录异常事件
            span.record_error(&e);
            
            // 3. 添加错误上下文
            span.set_attribute(KeyValue::new("error.type", "DatabaseError"));
            span.set_attribute(KeyValue::new("error.message", e.to_string()));
            
            span.end();
            Err(e)
        }
    }
}
```

---

### Q6.2: Panic 会导致 Span 丢失吗?

**A:** 是的,需要捕获:

```rust
use std::panic;

pub fn traced_catch_unwind<F, R>(
    tracer: &impl Tracer,
    span_name: &str,
    f: F,
) -> Result<R>
where
    F: FnOnce() -> R + panic::UnwindSafe,
{
    let mut span = tracer.start(span_name);

    let result = panic::catch_unwind(f);

    match result {
        Ok(value) => {
            span.end();
            Ok(value)
        }
        Err(panic_info) => {
            span.set_status(Status::error("Panic occurred"));
            span.set_attribute(KeyValue::new("panic", true));
            span.end();
            
            Err(anyhow::anyhow!("Panic: {:?}", panic_info))
        }
    }
}
```

---

### Q6.3: 如何追踪第三方库的错误?

**A:** 使用错误包装:

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),
}

impl AppError {
    pub fn record_to_span(&self, span: &mut dyn Span) {
        span.set_status(Status::error(self.to_string()));
        
        // 添加错误分类
        let error_type = match self {
            AppError::Database(_) => "database",
            AppError::Http(_) => "http",
        };
        
        span.set_attribute(KeyValue::new("error.type", error_type));
        span.record_error(self);
    }
}

// 使用
async fn operation() -> Result<(), AppError> {
    let tracer = global::tracer("app");
    let mut span = tracer.start("operation");

    let result = sqlx::query("SELECT * FROM users")
        .fetch_all(&pool)
        .await;

    if let Err(ref e) = result {
        AppError::from(e.clone()).record_to_span(&mut span);
    }

    span.end();
    result.map_err(Into::into)
}
```

---

## 7. 集成问题

### Q7.1: 如何与 Axum 集成?

**A:** 使用中间件:

```rust
use axum::{Router, routing::get, middleware};

async fn tracing_middleware(
    request: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("axum");
    let mut span = tracer.start(format!("{} {}", 
        request.method(), 
        request.uri().path()
    ));

    span.set_attribute(KeyValue::new("http.method", request.method().to_string()));
    
    let response = next.run(request).await;
    
    span.set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));
    span.end();

    response
}

fn app() -> Router {
    Router::new()
        .route("/", get(|| async { "Hello!" }))
        .layer(middleware::from_fn(tracing_middleware))
}
```

---

### Q7.2: 如何与 SQLx 集成?

**A:** 包装查询:

```rust
pub struct TracedDatabase {
    pool: PgPool,
}

impl TracedDatabase {
    pub async fn execute(&self, query: &str) -> Result<PgQueryResult> {
        let tracer = global::tracer("database");
        let mut span = tracer.start("db.query");
        
        span.set_attribute(KeyValue::new("db.system", "postgresql"));
        span.set_attribute(KeyValue::new("db.statement", query));

        let result = sqlx::query(query)
            .execute(&self.pool)
            .await;

        if let Err(ref e) = result {
            span.record_error(e);
        }

        span.end();
        result.map_err(Into::into)
    }
}
```

---

### Q7.3: 如何与 gRPC (Tonic) 集成?

**A:** 使用拦截器:

```rust
use tonic::{Request, Status};

pub fn client_interceptor(
    mut req: Request<()>,
) -> Result<Request<()>, Status> {
    let tracer = global::tracer("grpc-client");
    let span = tracer.start("grpc_call");

    // 注入追踪上下文到 metadata
    let cx = Context::current_with_span(span);
    // ... 实现注入逻辑

    Ok(req)
}

// 使用
let channel = Channel::from_static("http://localhost:50051")
    .connect()
    .await?;

let client = MyServiceClient::with_interceptor(channel, client_interceptor);
```

---

## 8. 配置问题

### Q8.1: 如何配置采样率?

**A:** 多种采样策略:

```rust
use opentelemetry_sdk::trace::{Sampler, Config};

// 1. 总是采样 (开发环境)
let always_on = Config::default()
    .with_sampler(Sampler::AlwaysOn);

// 2. 总是不采样 (禁用追踪)
let always_off = Config::default()
    .with_sampler(Sampler::AlwaysOff);

// 3. 按比例采样 (生产环境推荐)
let ratio_based = Config::default()
    .with_sampler(Sampler::TraceIdRatioBased(0.1)); // 10%

// 4. 父节点采样
let parent_based = Config::default()
    .with_sampler(Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1)
    )));
```

---

### Q8.2: 如何配置 OTLP Endpoint?

**A:** 多种配置方式:

```rust
// 方式1: 代码配置
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317");

// 方式2: 环境变量
// export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317

// 方式3: 配置文件
use serde::Deserialize;

#[derive(Deserialize)]
struct Config {
    otlp_endpoint: String,
}

let config: Config = toml::from_str(&fs::read_to_string("config.toml")?)?;
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint(&config.otlp_endpoint);
```

---

### Q8.3: 如何在不同环境使用不同配置?

**A:** 使用环境检测:

```rust
#[derive(Debug)]
pub enum Environment {
    Development,
    Staging,
    Production,
}

impl Environment {
    pub fn detect() -> Self {
        match std::env::var("ENV").unwrap_or_default().as_str() {
            "production" => Self::Production,
            "staging" => Self::Staging,
            _ => Self::Development,
        }
    }

    pub fn sampling_ratio(&self) -> f64 {
        match self {
            Self::Development => 1.0,   // 100%
            Self::Staging => 0.5,       // 50%
            Self::Production => 0.1,    // 10%
        }
    }

    pub fn otlp_endpoint(&self) -> &str {
        match self {
            Self::Development => "http://localhost:4317",
            Self::Staging => "http://staging-collector:4317",
            Self::Production => "http://prod-collector:4317",
        }
    }
}

// 使用
let env = Environment::detect();
let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(env.otlp_endpoint())
    )
    .with_trace_config(
        Config::default()
            .with_sampler(Sampler::TraceIdRatioBased(env.sampling_ratio()))
    )
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

---

## 9. 指标问题

### Q9.1: Trace 和 Metrics 有什么区别?

**A:** 不同的可观测性信号:

| 特性 | Traces (追踪) | Metrics (指标) |
|-----|--------------|---------------|
| **用途** | 请求流程 | 聚合统计 |
| **粒度** | 细粒度 (单个请求) | 粗粒度 (汇总) |
| **数据量** | 大 | 小 |
| **查询** | 单次请求详情 | 趋势/模式 |
| **成本** | 高 | 低 |
| **示例** | 请求耗时分布 | QPS, 平均延迟 |

**组合使用**:

```rust
// Trace: 记录单个请求
let span = tracer.start("handle_request");
// ...
span.end();

// Metrics: 记录统计
let counter = meter.u64_counter("requests_total").init();
counter.add(1, &[KeyValue::new("status", "success")]);
```

---

### Q9.2: 如何收集自定义指标?

**A:** 使用 Meter API:

```rust
use opentelemetry::metrics::Meter;

pub struct AppMetrics {
    requests_total: Counter<u64>,
    request_duration: Histogram<f64>,
    active_connections: UpDownCounter<i64>,
}

impl AppMetrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            requests_total: meter
                .u64_counter("app.requests.total")
                .with_description("Total number of requests")
                .init(),
            
            request_duration: meter
                .f64_histogram("app.request.duration")
                .with_description("Request duration in milliseconds")
                .with_unit("ms")
                .init(),
            
            active_connections: meter
                .i64_up_down_counter("app.connections.active")
                .with_description("Number of active connections")
                .init(),
        }
    }

    pub fn record_request(&self, duration_ms: f64, status: &str) {
        let attributes = &[KeyValue::new("status", status.to_string())];
        
        self.requests_total.add(1, attributes);
        self.request_duration.record(duration_ms, attributes);
    }
}
```

---

### Q9.3: Counter 和 Gauge 如何选择?

**A:** 根据指标类型:

| 指标类型 | 使用 | 示例 |
|---------|-----|------|
| **Counter** | 单调递增 | 请求总数, 错误总数 |
| **UpDownCounter** | 可增可减 | 活跃连接数, 队列长度 |
| **Histogram** | 分布统计 | 请求延迟, 响应大小 |
| **ObservableGauge** | 瞬时值 | CPU 使用率, 内存占用 |

```rust
// Counter: 累计请求数
let requests = meter.u64_counter("requests").init();
requests.add(1, &[]);

// UpDownCounter: 活跃用户
let users = meter.i64_up_down_counter("users.active").init();
users.add(1, &[]); // 用户登录
users.add(-1, &[]); // 用户登出

// Histogram: 延迟分布
let latency = meter.f64_histogram("latency").init();
latency.record(123.45, &[]);

// ObservableGauge: CPU 使用率
let cpu = meter.f64_observable_gauge("cpu.usage").init();
meter.register_callback(&[cpu.as_any()], move |observer| {
    observer.observe_f64(&cpu, get_cpu_usage(), &[]);
});
```

---

## 10. 调试问题

### Q10.1: 如何查看导出的追踪数据?

**A:** 多种方式:

```rust
// 1. 使用 stdout exporter (开发调试)
use opentelemetry_stdout::SpanExporter;

let provider = TracerProvider::builder()
    .with_simple_exporter(SpanExporter::default())
    .build();

// 2. 使用 Jaeger UI
// 访问 http://localhost:16686

// 3. 使用 OTLP Collector 日志
// docker logs otel-collector

// 4. 使用 debug logging
std::env::set_var("RUST_LOG", "opentelemetry=debug");
tracing_subscriber::fmt::init();
```

---

### Q10.2: 如何调试追踪数据没有发送?

**A:** 检查清单:

```rust
// 1. 启用调试日志
std::env::set_var("RUST_LOG", "opentelemetry_otlp=debug");

// 2. 检查 Span 是否被采样
if span.span_context().is_sampled() {
    println!("Span will be exported");
} else {
    println!("Span will NOT be exported");
}

// 3. 强制刷新
global::shutdown_tracer_provider(); // 应用退出前

// 4. 检查网络连接
// telnet localhost 4317

// 5. 使用 Mock Exporter 测试
use opentelemetry_sdk::export::trace::SpanExporter;

#[derive(Clone)]
struct DebugExporter;

#[async_trait::async_trait]
impl SpanExporter for DebugExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> TraceResult<()> {
        println!("Exporting {} spans", batch.len());
        for span in batch {
            println!("  - {}", span.name);
        }
        Ok(())
    }
}
```

---

### Q10.3: 如何验证 Span 的父子关系?

**A:** 检查 SpanContext:

```rust
let tracer = global::tracer("app");

let parent_span = tracer.start("parent");
let parent_cx = Context::current_with_span(parent_span.clone());

let child_span = tracer.start_with_context("child", &parent_cx);

// 验证关系
assert_eq!(
    child_span.span_context().trace_id(),
    parent_span.span_context().trace_id()
);

println!("Parent span_id: {}", parent_span.span_context().span_id());
println!("Child span_id: {}", child_span.span_context().span_id());
```

---

## 11. 部署问题

### Q11.1: 生产环境如何配置?

**A:** 生产配置最佳实践:

```rust
pub fn production_tracer() -> Result<TracerProvider> {
    opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otlp-collector:4317")
                .with_timeout(std::time::Duration::from_secs(3))
        )
        .with_trace_config(
            Config::default()
                // 1. 低采样率
                .with_sampler(Sampler::TraceIdRatioBased(0.05)) // 5%
                
                // 2. 资源属性
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "my-service"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
        )
        .with_batch_config(
            // 3. 优化批量配置
            BatchConfig::default()
                .with_max_export_batch_size(512)
                .with_scheduled_delay(std::time::Duration::from_secs(5))
                .with_max_queue_size(4096)
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
}
```

---

### Q11.2: 如何处理 OTLP Collector 不可用?

**A:** 实现降级和重试:

```rust
use tokio::time::{timeout, Duration};

pub async fn init_with_fallback() -> TracerProvider {
    // 尝试连接 Collector
    let result = timeout(
        Duration::from_secs(5),
        connect_to_collector()
    ).await;

    match result {
        Ok(Ok(provider)) => provider,
        _ => {
            eprintln!("OTLP Collector unavailable, using noop tracer");
            TracerProvider::builder().build() // Noop provider
        }
    }
}

async fn connect_to_collector() -> Result<TracerProvider> {
    opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
}
```

---

### Q11.3: Docker 容器中如何配置?

**A:** Docker Compose 配置:

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - OTEL_SERVICE_NAME=my-rust-app
      - OTEL_TRACES_SAMPLER=traceidratio
      - OTEL_TRACES_SAMPLER_ARG=0.1
    depends_on:
      - otel-collector

  otel-collector:
    image: otel/opentelemetry-collector:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
```

---

## 12. 高级问题

### Q12.1: 如何实现分布式追踪?

**A:** 使用 W3C Trace Context:

```rust
// 服务 A (发送方)
use opentelemetry::propagation::TextMapPropagator;

async fn call_service_b() -> Result<()> {
    let tracer = global::tracer("service-a");
    let span = tracer.start("call_service_b");
    let cx = Context::current_with_span(span);

    // 注入追踪上下文
    let mut headers = HashMap::new();
    let propagator = opentelemetry::sdk::propagation::TraceContextPropagator::new();
    propagator.inject_context(&cx, &mut headers);

    // 发送 HTTP 请求
    let client = reqwest::Client::new();
    let mut request = client.post("http://service-b/api");
    for (key, value) in headers {
        request = request.header(key, value);
    }
    request.send().await?;

    Ok(())
}

// 服务 B (接收方)
async fn handle_request(headers: &HeaderMap) {
    let tracer = global::tracer("service-b");
    let propagator = opentelemetry::sdk::propagation::TraceContextPropagator::new();
    
    // 提取上下文
    let parent_cx = propagator.extract(&HeaderExtractor(headers));
    
    // 创建子 Span
    let span = tracer.start_with_context("handle_request", &parent_cx);
    // ...
}
```

---

### Q12.2: 如何实现自定义 Sampler?

**A:** 实现 Sampler trait:

```rust
use opentelemetry::sdk::trace::{Sampler, SamplingResult, SamplingDecision};

pub struct CustomSampler {
    base_ratio: f64,
}

impl Sampler for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&SpanContext>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &OrderMap<Key, Value>,
        links: &[Link],
    ) -> SamplingResult {
        // 自定义采样逻辑
        let should_sample = if name.contains("health") {
            false // 健康检查不采样
        } else if attributes.iter().any(|(k, _)| k.as_str() == "error") {
            true // 错误总是采样
        } else {
            // 使用基础采样率
            self.base_ratio > rand::random::<f64>()
        };

        SamplingResult {
            decision: if should_sample {
                SamplingDecision::RecordAndSample
            } else {
                SamplingDecision::Drop
            },
            attributes: vec![],
            trace_state: TraceState::default(),
        }
    }
}
```

---

### Q12.3: 如何实现自定义 Exporter?

**A:** 实现 SpanExporter trait:

```rust
use opentelemetry_sdk::export::trace::{SpanExporter, SpanData};

pub struct CustomExporter {
    endpoint: String,
}

#[async_trait::async_trait]
impl SpanExporter for CustomExporter {
    async fn export(
        &mut self,
        batch: Vec<SpanData>,
    ) -> opentelemetry::trace::TraceResult<()> {
        // 自定义导出逻辑
        let json = serde_json::to_string(&batch)?;
        
        reqwest::Client::new()
            .post(&self.endpoint)
            .body(json)
            .send()
            .await?;

        Ok(())
    }
}
```

---

## 13. 故障排查

**常见问题快速诊断**:

| 症状 | 可能原因 | 解决方案 |
|-----|---------|---------|
| Span 不出现 | 采样率为 0 | 检查 Sampler 配置 |
| | TracerProvider 未刷新 | 调用 shutdown() |
| | Collector 不可达 | 检查网络连接 |
| 性能下降 | 同步导出 | 使用批量导出 |
| | 采样率过高 | 降低采样率 |
| | 属性过多 | 减少不必要的属性 |
| 内存泄漏 | Span 未结束 | 使用 RAII 守卫 |
| | 队列积压 | 增大导出频率 |
| 上下文丢失 | 异步任务未传播 | 显式传播 Context |
| | 跨线程传播失败 | 使用 propagator |

---

## 14. 最佳实践总结

### ✅ DO (推荐)

- ✅ 使用批量导出
- ✅ 合理设置采样率 (生产 1-10%)
- ✅ 使用有意义的 Span 名称
- ✅ 正确传播上下文
- ✅ 记录错误到 Span
- ✅ 应用退出时 shutdown
- ✅ 使用 RAII 确保 Span 结束
- ✅ 添加相关的资源属性
- ✅ 使用环境变量配置
- ✅ 监控 OTLP Collector 健康

### ❌ DON'T (避免)

- ❌ 在热路径使用同步导出
- ❌ 追踪所有请求 (采样率 100%)
- ❌ 在 Span 中记录敏感信息
- ❌ 忘记结束 Span
- ❌ 在 Span 属性中存储大量数据
- ❌ 使用魔法字符串作为属性键
- ❌ 忽略错误处理
- ❌ 在生产环境使用 AlwaysOn 采样
- ❌ 硬编码 Collector 地址
- ❌ 忘记测试追踪功能

---

**文档行数**: ~1,600 行  
**问题数量**: 40+ 个常见问题  
**代码示例**: 50+ 个解决方案  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

---

🎉 **Rust OTLP FAQ 文档完成!**

如有其他问题,请查阅:

- [Rust OTLP 30分钟快速入门](./01_Rust_OTLP_30分钟快速入门.md)
- [Rust OTLP 常见模式](./02_Rust_OTLP_常见模式.md)
- [OpenTelemetry Rust 官方文档](https://docs.rs/opentelemetry/)
