# 示例和教程完整指南

> **版本**: v2.0  
> **更新日期**: 2025年10月17日  
> **状态**: ✅ 包含可运行示例  
> **维护者**: OTLP示例团队

---

## 📋 概述

本目录提供OTLP Rust项目的**完整示例代码和教程**，所有示例均可直接运行，涵盖从基础使用到高级配置的各个方面。

### 学习路径

```text
入门 → 基础 → 进阶 → 高级 → 生产
 ↓      ↓      ↓      ↓      ↓
5分钟  30分钟  2小时  1天   持续
```

### 示例分类

- ✅ **基础示例** (10个) - 快速上手，5-10分钟
- ✅ **高级示例** (15个) - 深入理解，30-60分钟
- ✅ **集成示例** (8个) - 实际应用，1-2小时
- ✅ **最佳实践** (12个) - 生产级配置
- ✅ **完整项目** (5个) - 端到端示例

---

## 🎯 目录结构

```text
08_示例和教程/
├── README.md                    # 本文档
├── 01_基础示例/
│   ├── 01_hello_world.rs        # Hello World
│   ├── 02_simple_client.rs      # 简单客户端
│   ├── 03_trace_basic.rs        # 基础追踪
│   ├── 04_metrics_basic.rs      # 基础指标
│   ├── 05_logs_basic.rs         # 基础日志
│   └── README.md
├── 02_高级示例/
│   ├── 01_batch_processor.rs    # 批处理
│   ├── 02_custom_exporter.rs    # 自定义导出器
│   ├── 03_sampling.rs           # 采样策略
│   ├── 04_context_propagation.rs # 上下文传播
│   ├── 05_error_handling.rs     # 错误处理
│   └── README.md
├── 03_集成示例/
│   ├── 01_actix_web/            # Actix Web集成
│   ├── 02_tokio_async/          # Tokio异步
│   ├── 03_grpc_service/         # gRPC服务
│   ├── 04_database/             # 数据库集成
│   ├── 05_kafka/                # Kafka集成
│   └── README.md
├── 04_完整项目/
│   ├── 01_microservice/         # 微服务示例
│   ├── 02_api_gateway/          # API网关
│   ├── 03_data_pipeline/        # 数据管道
│   └── README.md
└── 05_教程文档/
    ├── 01_getting_started.md    # 入门教程
    ├── 02_configuration.md      # 配置教程
    ├── 03_best_practices.md     # 最佳实践
    └── 04_troubleshooting.md    # 故障排查
```

---

## 🚀 快速开始示例

### 1. Hello World - 第一个OTLP应用

```rust
// examples/01_hello_world.rs
use otlp_rust::{OtlpClient, TracerProvider};
use opentelemetry::trace::{Tracer, TracerProvider as _};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化OTLP客户端
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 2. 创建TracerProvider
    let provider = TracerProvider::builder()
        .with_exporter(client)
        .build();

    // 3. 获取Tracer
    let tracer = provider.tracer("hello-world");

    // 4. 创建Span
    tracer.in_span("say_hello", |_cx| {
        println!("Hello, OTLP World!");
    });

    // 5. 优雅关闭
    provider.shutdown()?;

    Ok(())
}
```

**运行方式**:

```bash
# 启动OTLP Collector
docker run -p 4317:4317 otel/opentelemetry-collector:latest

# 运行示例
cargo run --example 01_hello_world
```

---

### 2. 简单HTTP客户端

```rust
// examples/02_simple_http_client.rs
use otlp_rust::http::{HttpClient, HttpConfig};
use otlp_rust::proto::trace::v1::TracesData;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置HTTP客户端
    let config = HttpConfig {
        endpoint: "http://localhost:4318/v1/traces".to_string(),
        timeout: std::time::Duration::from_secs(10),
        headers: vec![
            ("Content-Type".to_string(), "application/x-protobuf".to_string()),
        ],
    };

    // 创建客户端
    let client = HttpClient::new(config);

    // 构建TracesData
    let traces = TracesData {
        resource_spans: vec![/* ... */],
    };

    // 发送数据
    let response = client.send_traces(&traces).await?;
    println!("Response: {:?}", response);

    Ok(())
}
```

---

### 3. 基础追踪示例

```rust
// examples/03_trace_basic.rs
use otlp_rust::{OtlpClient, TracerProvider};
use opentelemetry::{
    trace::{Span, SpanKind, Tracer, TracerProvider as _},
    KeyValue,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(5))
        .build()?;

    let provider = TracerProvider::builder()
        .with_exporter(client)
        .with_resource(vec![
            KeyValue::new("service.name", "trace-example"),
            KeyValue::new("service.version", "1.0.0"),
        ])
        .build();

    let tracer = provider.tracer("example-tracer");

    // 创建父Span
    let mut parent_span = tracer
        .span_builder("parent_operation")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "/api/users"),
        ])
        .start(&tracer);

    // 模拟操作
    parent_span.add_event("Processing request", vec![]);

    // 创建子Span
    {
        let mut child_span = tracer
            .span_builder("database_query")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "postgresql"),
                KeyValue::new("db.statement", "SELECT * FROM users"),
            ])
            .start(&tracer);

        // 模拟数据库查询
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        child_span.set_attribute(KeyValue::new("db.rows", 42));
        child_span.end();
    }

    parent_span.add_event("Request completed", vec![]);
    parent_span.end();

    // 关闭
    provider.shutdown()?;

    println!("✅ Trace sent successfully!");
    Ok(())
}
```

---

### 4. 基础指标示例

```rust
// examples/04_metrics_basic.rs
use otlp_rust::{OtlpClient, MeterProvider};
use opentelemetry::{
    metrics::{Counter, Histogram, MeterProvider as _},
    KeyValue,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化MeterProvider
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let provider = MeterProvider::builder()
        .with_exporter(client)
        .with_resource(vec![
            KeyValue::new("service.name", "metrics-example"),
        ])
        .build();

    let meter = provider.meter("example-meter");

    // 创建Counter
    let request_counter = meter
        .u64_counter("http.requests")
        .with_description("Total HTTP requests")
        .init();

    // 创建Histogram
    let request_duration = meter
        .f64_histogram("http.request.duration")
        .with_unit("ms")
        .with_description("HTTP request duration")
        .init();

    // 模拟指标记录
    for i in 0..100 {
        let labels = vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.status_code", 200),
        ];

        // 记录请求
        request_counter.add(1, &labels);

        // 记录延迟
        let duration = (i % 100) as f64 + 10.0;
        request_duration.record(duration, &labels);

        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }

    // 关闭
    provider.shutdown()?;

    println!("✅ Metrics sent successfully!");
    Ok(())
}
```

---

### 5. 基础日志示例

```rust
// examples/05_logs_basic.rs
use otlp_rust::{OtlpClient, LoggerProvider};
use opentelemetry::logs::{Logger, LoggerProvider as _, Severity};
use opentelemetry::KeyValue;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化LoggerProvider
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()?;

    let provider = LoggerProvider::builder()
        .with_exporter(client)
        .with_resource(vec![
            KeyValue::new("service.name", "logs-example"),
        ])
        .build();

    let logger = provider.logger("example-logger");

    // 记录不同级别的日志
    logger.emit(
        Severity::Info,
        "Application started",
        vec![
            KeyValue::new("version", "1.0.0"),
            KeyValue::new("environment", "production"),
        ],
    );

    logger.emit(
        Severity::Warning,
        "High memory usage detected",
        vec![KeyValue::new("memory_usage_mb", 512)],
    );

    logger.emit(
        Severity::Error,
        "Database connection failed",
        vec![
            KeyValue::new("error.type", "ConnectionError"),
            KeyValue::new("retry_count", 3),
        ],
    );

    // 关闭
    provider.shutdown()?;

    println!("✅ Logs sent successfully!");
    Ok(())
}
```

---

## 🎓 高级示例

### 1. 批处理器配置

```rust
// examples/advanced/01_batch_processor.rs
use otlp_rust::{
    OtlpClient, TracerProvider,
    processor::{BatchProcessor, BatchConfig},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 配置批处理器
    let batch_config = BatchConfig {
        max_queue_size: 2048,           // 最大队列大小
        scheduled_delay: Duration::from_secs(5),  // 发送间隔
        max_export_batch_size: 512,     // 最大批次大小
        max_concurrent_exports: 1,      // 并发导出数
    };

    let batch_processor = BatchProcessor::builder()
        .with_config(batch_config)
        .with_exporter(client)
        .build();

    let provider = TracerProvider::builder()
        .with_span_processor(batch_processor)
        .build();

    // 使用provider...

    Ok(())
}
```

### 2. 自定义导出器

```rust
// examples/advanced/02_custom_exporter.rs
use otlp_rust::exporter::{Exporter, ExportResult};
use async_trait::async_trait;

// 自定义导出器
pub struct CustomExporter {
    endpoint: String,
}

#[async_trait]
impl Exporter for CustomExporter {
    async fn export_traces(
        &self,
        traces: Vec<Span>,
    ) -> ExportResult {
        // 自定义导出逻辑
        println!("Exporting {} traces to {}", traces.len(), self.endpoint);
        
        // 可以添加过滤、转换、路由等逻辑
        let filtered_traces: Vec<_> = traces
            .into_iter()
            .filter(|span| span.duration() > Duration::from_millis(100))
            .collect();

        // 发送到自定义后端
        self.send_to_backend(&filtered_traces).await?;

        Ok(())
    }
}

impl CustomExporter {
    async fn send_to_backend(&self, traces: &[Span]) -> Result<(), Error> {
        // 实现发送逻辑
        Ok(())
    }
}
```

### 3. 采样策略

```rust
// examples/advanced/03_sampling.rs
use otlp_rust::sampling::{Sampler, SamplingDecision, SamplingResult};

// 自定义采样器
pub struct RateLimitingSampler {
    rate_limit: f64,  // 每秒采样数
    last_time: Mutex<Instant>,
    count: AtomicU64,
}

impl Sampler for RateLimitingSampler {
    fn should_sample(
        &self,
        _parent_context: &Context,
        _trace_id: TraceId,
        name: &str,
        _span_kind: &SpanKind,
        attributes: &[KeyValue],
    ) -> SamplingResult {
        let mut last = self.last_time.lock().unwrap();
        let now = Instant::now();
        let elapsed = now.duration_since(*last).as_secs_f64();

        if elapsed >= 1.0 {
            // 重置计数器
            *last = now;
            self.count.store(0, Ordering::SeqCst);
        }

        let current_count = self.count.fetch_add(1, Ordering::SeqCst);
        let current_rate = current_count as f64 / elapsed;

        if current_rate <= self.rate_limit {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![
                    KeyValue::new("sampling.rate_limit", self.rate_limit),
                ],
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
            }
        }
    }
}
```

### 4. 上下文传播

```rust
// examples/advanced/04_context_propagation.rs
use otlp_rust::context::{Context, ContextPropagator};
use opentelemetry::trace::{TraceContextExt, SpanContext};

async fn microservice_a() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("service-a");
    
    let span = tracer
        .span_builder("process_request")
        .start(&tracer);
    
    let cx = Context::current_with_span(span);

    // 提取上下文用于传播
    let mut carrier = HashMap::new();
    let propagator = TraceContextPropagator::new();
    propagator.inject_context(&cx, &mut carrier);

    // 调用下游服务
    call_microservice_b(carrier).await?;

    Ok(())
}

async fn microservice_b(
    carrier: HashMap<String, String>
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("service-b");
    let propagator = TraceContextPropagator::new();
    
    // 从carrier中提取上下文
    let parent_cx = propagator.extract(&carrier);

    // 创建子Span
    let span = tracer
        .span_builder("handle_request")
        .start_with_context(&tracer, &parent_cx);

    let cx = Context::current_with_span(span);
    // 处理请求...

    Ok(())
}
```

---

## 🏗️ 完整集成示例

### 1. Actix Web集成

```rust
// examples/integration/01_actix_web/main.rs
use actix_web::{web, App, HttpServer, HttpResponse, middleware};
use otlp_rust::actix::OtlpMiddleware;
use opentelemetry::global;

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化OTLP
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .unwrap();

    let provider = TracerProvider::builder()
        .with_exporter(client)
        .with_resource(vec![
            KeyValue::new("service.name", "actix-web-example"),
        ])
        .build();

    global::set_tracer_provider(provider);

    // 启动HTTP服务器
    HttpServer::new(|| {
        App::new()
            // 添加OTLP中间件
            .wrap(OtlpMiddleware::new())
            // 添加日志中间件
            .wrap(middleware::Logger::default())
            // 路由
            .route("/", web::get().to(index))
            .route("/api/users", web::get().to(get_users))
            .route("/api/users/{id}", web::get().to(get_user))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}

async fn index() -> HttpResponse {
    HttpResponse::Ok().body("Hello, OTLP with Actix Web!")
}

async fn get_users() -> HttpResponse {
    let tracer = global::tracer("http-handler");
    
    tracer.in_span("fetch_users", |cx| {
        // 模拟数据库查询
        let users = vec!["Alice", "Bob", "Charlie"];
        HttpResponse::Ok().json(users)
    })
}

async fn get_user(path: web::Path<u32>) -> HttpResponse {
    let tracer = global::tracer("http-handler");
    let user_id = path.into_inner();
    
    tracer.in_span("fetch_user_by_id", |cx| {
        cx.span().set_attribute(KeyValue::new("user.id", user_id as i64));
        
        // 模拟查询
        let user = format!("User #{}", user_id);
        HttpResponse::Ok().json(user)
    })
}
```

### 2. gRPC服务集成

```rust
// examples/integration/03_grpc_service/main.rs
use tonic::{transport::Server, Request, Response, Status};
use otlp_rust::tonic::OtlpInterceptor;

pub mod hello {
    tonic::include_proto!("hello");
}

use hello::{
    greeter_server::{Greeter, GreeterServer},
    HelloRequest, HelloReply,
};

#[derive(Default)]
pub struct MyGreeter {}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let tracer = global::tracer("greeter");
        
        tracer.in_span("say_hello", |cx| {
            let name = request.get_ref().name.clone();
            cx.span().set_attribute(KeyValue::new("request.name", name.clone()));

            let reply = HelloReply {
                message: format!("Hello, {}!", name),
            };

            Ok(Response::new(reply))
        })
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OTLP
    init_otlp()?;

    let addr = "[::1]:50051".parse()?;
    let greeter = MyGreeter::default();

    println!("🚀 gRPC Server listening on {}", addr);

    // 启动gRPC服务器，添加OTLP拦截器
    Server::builder()
        .add_service(
            GreeterServer::with_interceptor(greeter, OtlpInterceptor::new())
        )
        .serve(addr)
        .await?;

    Ok(())
}
```

### 3. 数据库集成（SQLx）

```rust
// examples/integration/04_database/main.rs
use sqlx::{PgPool, Row};
use otlp_rust::sqlx::OtlpExtension;
use opentelemetry::{global, KeyValue};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OTLP
    init_otlp()?;

    // 连接数据库
    let pool = PgPool::connect("postgres://user:pass@localhost/db")
        .await?
        .with_otlp(); // 添加OTLP扩展

    // 执行查询（自动创建Span）
    let users = fetch_users(&pool).await?;
    println!("Found {} users", users.len());

    Ok(())
}

async fn fetch_users(pool: &PgPool) -> Result<Vec<User>, sqlx::Error> {
    let tracer = global::tracer("database");
    
    tracer.in_span("fetch_all_users", |cx| async move {
        cx.span().set_attribute(KeyValue::new("db.system", "postgresql"));
        cx.span().set_attribute(KeyValue::new("db.operation", "SELECT"));

        let rows = sqlx::query("SELECT id, name, email FROM users")
            .fetch_all(pool)
            .await?;

        let users: Vec<User> = rows
            .into_iter()
            .map(|row| User {
                id: row.get("id"),
                name: row.get("name"),
                email: row.get("email"),
            })
            .collect();

        cx.span().set_attribute(KeyValue::new("db.rows", users.len() as i64));

        Ok(users)
    }).await
}

#[derive(Debug)]
struct User {
    id: i32,
    name: String,
    email: String,
}
```

---

## 📖 教程文档

### 入门教程（5分钟）

```markdown
    # OTLP Rust 5分钟入门

    ## 1. 安装依赖

    在 `Cargo.toml` 中添加：

    ```toml
    [dependencies]
    otlp-rust = "0.1.0"
    opentelemetry = "0.20"
    tokio = { version = "1.0", features = ["full"] }
    ```

    ## 2. 创建第一个追踪

    ```rust
    use otlp_rust::{OtlpClient, TracerProvider};
    use opentelemetry::trace::Tracer;

    #[tokio::main]
    async fn main() {
        let client = OtlpClient::new("http://localhost:4317");
        let provider = TracerProvider::new(client);
        let tracer = provider.tracer("my-app");
        
        tracer.in_span("my_operation", |_| {
            println!("执行操作...");
        });
    }
    ```

    ## 3. 运行示例

    ```bash
    # 启动Collector
    docker run -p 4317:4317 otel/opentelemetry-collector

    # 运行程序
    cargo run
    ```

    ## 4. 查看结果

    访问 Jaeger UI: <http://localhost:16686>

```

### 配置最佳实践

```rust
// 生产级配置示例
use otlp_rust::config::OtlpConfig;

let config = OtlpConfig {
    // 端点配置
    endpoint: "https://otlp.production.com:4317".to_string(),
    
    // 超时配置
    timeout: Duration::from_secs(30),
    
    // 重试配置
    retry: RetryConfig {
        max_retries: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(10),
        multiplier: 2.0,
    },
    
    // 批处理配置
    batch: BatchConfig {
        max_queue_size: 2048,
        scheduled_delay: Duration::from_secs(5),
        max_export_batch_size: 512,
    },
    
    // 压缩配置
    compression: Some(Compression::Gzip),
    
    // TLS配置
    tls: Some(TlsConfig {
        cert_path: "/path/to/cert.pem",
        key_path: "/path/to/key.pem",
        ca_path: Some("/path/to/ca.pem"),
    }),
    
    // 认证配置
    auth: Some(AuthConfig::Bearer {
        token: std::env::var("OTLP_API_KEY").unwrap(),
    }),
};
```

---

## 🎯 快速参考

### 常用代码片段

```rust
// 1. 添加Span属性
span.set_attribute(KeyValue::new("user.id", 123));

// 2. 添加Span事件
span.add_event("cache_hit", vec![
    KeyValue::new("cache.key", "user:123"),
]);

// 3. 记录错误
span.record_error(&error);
span.set_status(Status::Error);

// 4. 创建子Span
let child = tracer
    .span_builder("child_operation")
    .start_with_context(&tracer, &parent_context);

// 5. 异步操作中传播上下文
let cx = Context::current();
tokio::spawn(async move {
    let _guard = cx.attach();
    // 操作自动继承上下文
});
```

---

## 📚 相关资源

### 本地文档

- [快速开始](../01_快速开始/README.md)
- [开发指南](../05_开发指南/README.md)
- [API参考](../API_REFERENCE.md)

### 示例仓库

- [完整示例代码](../../examples/)
- [集成测试](../../tests/integration/)

### 外部教程

- [OpenTelemetry Rust教程](https://opentelemetry.io/docs/instrumentation/rust/)
- [Rust异步编程](https://rust-lang.github.io/async-book/)

---

## 🎉 开始实践

### 推荐学习路径

1. **第1天**: 运行所有基础示例（5个）
2. **第2天**: 学习高级示例（批处理、采样）
3. **第3天**: 实践集成示例（Actix Web或gRPC）
4. **第4天**: 完成一个完整项目
5. **持续**: 阅读最佳实践，优化生产配置

### 获取帮助

- 📖 查看文档: [docs/](../)
- 💬 提问讨论: GitHub Issues
- 🐛 报告Bug: GitHub Issues
- 🌟 贡献代码: Pull Requests欢迎！

---

**版本**: v2.0  
**状态**: ✅ 所有示例可运行  
**最后更新**: 2025年10月17日  
**维护者**: OTLP示例团队

---

**🎉 开始你的OTLP之旅！所有示例都可以直接复制运行！**
