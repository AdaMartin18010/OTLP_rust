# HTTP 追踪最佳实践 - HTTP Tracing Best Practices

**创建日期**: 2025年10月29日
**技术标准**: W3C Trace Context + OpenTelemetry Semantic Conventions
**状态**: ✅ 生产验证

---

## 📋 目录

- [概述](#概述)
- [W3C Trace Context](#w3c-trace-context)
- [HTTP语义约定](#http语义约定)
- [自动化追踪](#自动化追踪)
- [手动追踪](#手动追踪)
- [上下文传播](#上下文传播)
- [错误处理](#错误处理)
- [性能优化](#性能优化)
- [最佳实践](#最佳实践)

---

## 概述

HTTP追踪是分布式系统可观测性的基础，本文档提供：

- ✅ **标准化追踪**: 遵循W3C和OpenTelemetry标准
- ✅ **零侵入**: 通过中间件自动追踪
- ✅ **完整覆盖**: 请求/响应生命周期
- ✅ **性能优化**: 低开销(<5%)追踪
- ✅ **生产验证**: 实际生产环境验证

---

## W3C Trace Context

### 标准概述

W3C Trace Context定义了分布式追踪的HTTP头标准：

```text
traceparent: 00-{trace-id}-{parent-id}-{trace-flags}
tracestate: vendor1=value1,vendor2=value2
```

### 实现示例

```rust
use opentelemetry::{
    propagation::{Extractor, Injector, TextMapPropagator},
    trace::TraceContextExt,
    Context,
};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use std::collections::HashMap;

// 提取trace context from HTTP headers
fn extract_trace_context<T>(headers: &HeaderMap) -> Context
where
    T: for<'a> Extractor<'a>,
{
    let propagator = TraceContextPropagator::new();
    let extractor = HeaderExtractor(headers);
    propagator.extract(&extractor)
}

// 注入trace context to HTTP headers
fn inject_trace_context(cx: &Context, headers: &mut HeaderMap) {
    let propagator = TraceContextPropagator::new();
    let mut injector = HeaderInjector(headers);
    propagator.inject_context(cx, &mut injector);
}

// Header Extractor实现
struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

// Header Injector实现
struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}
```

### Axum集成示例

```rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
};

async fn trace_context_middleware(
    mut request: Request,
    next: Next,
) -> Response {
    // 1. 提取入站trace context
    let parent_cx = extract_trace_context(request.headers());

    // 2. 创建新span并关联到parent context
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder("http_request")
        .with_kind(SpanKind::Server)
        .start_with_context(&tracer, &parent_cx);

    // 3. 附加到当前上下文
    let cx = Context::current_with_span(span);
    let _guard = cx.attach();

    // 4. 处理请求
    let mut response = next.run(request).await;

    // 5. 注入trace context到响应头
    inject_trace_context(&cx, response.headers_mut());

    response
}
```

---

## HTTP语义约定

### OpenTelemetry HTTP Semantic Conventions

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions as semconv;

fn set_http_span_attributes(
    span: &mut Span,
    request: &Request<Body>,
    response: &Response<Body>,
) {
    // HTTP方法
    span.set_attribute(semconv::trace::HTTP_REQUEST_METHOD.string(
        request.method().to_string()
    ));

    // HTTP URL
    span.set_attribute(semconv::trace::URL_FULL.string(
        request.uri().to_string()
    ));

    // HTTP版本
    span.set_attribute(semconv::trace::NETWORK_PROTOCOL_VERSION.string(
        format!("{:?}", request.version())
    ));

    // HTTP状态码
    span.set_attribute(semconv::trace::HTTP_RESPONSE_STATUS_CODE.i64(
        response.status().as_u16() as i64
    ));

    // 服务器地址和端口
    if let Some(host) = request.headers().get("host") {
        if let Ok(host_str) = host.to_str() {
            let parts: Vec<&str> = host_str.split(':').collect();
            span.set_attribute(semconv::trace::SERVER_ADDRESS.string(parts[0]));
            if parts.len() > 1 {
                if let Ok(port) = parts[1].parse::<i64>() {
                    span.set_attribute(semconv::trace::SERVER_PORT.i64(port));
                }
            }
        }
    }

    // 用户代理
    if let Some(ua) = request.headers().get("user-agent") {
        if let Ok(ua_str) = ua.to_str() {
            span.set_attribute(semconv::trace::USER_AGENT_ORIGINAL.string(ua_str));
        }
    }

    // HTTP路由
    if let Some(route) = request.extensions().get::<MatchedPath>() {
        span.set_attribute(semconv::trace::HTTP_ROUTE.string(route.as_str()));
    }

    // 请求体大小
    if let Some(len) = request.headers().get("content-length") {
        if let Ok(len_str) = len.to_str() {
            if let Ok(size) = len_str.parse::<i64>() {
                span.set_attribute(semconv::trace::HTTP_REQUEST_BODY_SIZE.i64(size));
            }
        }
    }

    // 响应体大小
    if let Some(len) = response.headers().get("content-length") {
        if let Ok(len_str) = len.to_str() {
            if let Ok(size) = len_str.parse::<i64>() {
                span.set_attribute(semconv::trace::HTTP_RESPONSE_BODY_SIZE.i64(size));
            }
        }
    }
}
```

### 完整的HTTP Span示例

```rust
use opentelemetry::{
    trace::{Span, SpanKind, Status, StatusCode, Tracer},
    KeyValue,
};

async fn traced_http_handler(
    request: Request<Body>,
) -> Result<Response<Body>, Error> {
    let tracer = global::tracer("http-api");

    // 创建server span
    let mut span = tracer
        .span_builder("GET /api/users/:id")
        .with_kind(SpanKind::Server)
        .start(&tracer);

    // 设置基本HTTP属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.url", "/api/users/123"));
    span.set_attribute(KeyValue::new("http.target", "/api/users/123"));
    span.set_attribute(KeyValue::new("http.host", "api.example.com"));
    span.set_attribute(KeyValue::new("http.scheme", "https"));
    span.set_attribute(KeyValue::new("http.route", "/api/users/:id"));

    // 设置网络属性
    span.set_attribute(KeyValue::new("net.protocol.name", "http"));
    span.set_attribute(KeyValue::new("net.protocol.version", "1.1"));
    span.set_attribute(KeyValue::new("net.peer.ip", "192.168.1.100"));
    span.set_attribute(KeyValue::new("net.peer.port", 54321));

    // 处理请求
    match process_request(request).await {
        Ok(response) => {
            // 成功响应
            span.set_attribute(KeyValue::new("http.status_code", 200));
            span.set_status(Status::Ok);
            Ok(response)
        }
        Err(e) => {
            // 错误处理
            span.set_attribute(KeyValue::new("http.status_code", 500));
            span.set_status(Status::error(format!("Request failed: {}", e)));
            span.record_exception(&e);
            Err(e)
        }
    }
}
```

---

## 自动化追踪

### Axum自动追踪

```rust
use tower_http::trace::{
    DefaultMakeSpan, DefaultOnRequest, DefaultOnResponse,
    TraceLayer,
};
use tracing::Level;

let app = Router::new()
    .route("/api/users", get(list_users))
    .layer(
        TraceLayer::new_for_http()
            // 创建span
            .make_span_with(
                DefaultMakeSpan::new()
                    .level(Level::INFO)
                    .include_headers(true)
            )
            // 请求开始
            .on_request(
                DefaultOnRequest::new()
                    .level(Level::INFO)
            )
            // 响应完成
            .on_response(
                DefaultOnResponse::new()
                    .level(Level::INFO)
                    .latency_unit(tower_http::LatencyUnit::Micros)
                    .include_headers(true)
            )
            // 失败处理
            .on_failure(
                DefaultOnFailure::new()
                    .level(Level::ERROR)
            )
    );
```

### Actix-web自动追踪

```rust
use tracing_actix_web::{TracingLogger, RequestId, RootSpanBuilder};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            // 自动追踪中间件
            .wrap(TracingLogger::default())
            // 自定义span构建器
            .wrap(
                TracingLogger::<RootSpanBuilder>::new()
                    .with_request_id()
            )
            .route("/api/users", web::get().to(list_users))
    })
    .bind("0.0.0.0:8080")?
    .run()
    .await
}
```

---

## 手动追踪

### 细粒度控制

```rust
use tracing::{info, warn, error, instrument};

#[instrument(
    name = "http.get_user",
    skip(db),
    fields(
        http.method = "GET",
        http.route = "/api/users/:id",
        user.id = %user_id,
        otel.kind = "server"
    )
)]
async fn get_user_handler(
    user_id: u64,
    db: &DatabasePool,
) -> Result<User, ApiError> {
    info!("Starting user lookup");

    // 数据库查询
    let user = db.get_user(user_id).await.map_err(|e| {
        error!("Database error: {}", e);
        ApiError::DatabaseError(e)
    })?;

    info!("User found successfully");
    Ok(user)
}
```

### 创建子Span

```rust
async fn complex_operation() -> Result<(), Error> {
    let tracer = global::tracer("api");

    // 父span
    let mut parent_span = tracer.start("complex_operation");
    let parent_cx = Context::current_with_span(parent_span);

    // 子span 1: 数据库查询
    {
        let mut span = tracer
            .span_builder("database.query")
            .start_with_context(&tracer, &parent_cx);

        span.set_attribute(KeyValue::new("db.system", "postgresql"));
        span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users"));

        let result = database_query().await;
        span.end();
        result?;
    }

    // 子span 2: 缓存操作
    {
        let mut span = tracer
            .span_builder("cache.set")
            .start_with_context(&tracer, &parent_cx);

        span.set_attribute(KeyValue::new("cache.key", "user:123"));
        cache_set("user:123", &data).await?;
        span.end();
    }

    Ok(())
}
```

---

## 上下文传播

### 分布式追踪链

```rust
use reqwest::Client;

async fn call_downstream_service(user_id: u64) -> Result<Response, Error> {
    let tracer = global::tracer("http-client");
    let mut span = tracer.start("http.client.request");

    // 设置span属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.url", "http://user-service/api/users/123"));
    span.set_attribute(KeyValue::new("peer.service", "user-service"));

    // 创建HTTP client
    let client = Client::new();
    let mut headers = HeaderMap::new();

    // 注入trace context
    let cx = Context::current_with_span(span);
    inject_trace_context(&cx, &mut headers);

    // 发送请求
    let response = client
        .get(&format!("http://user-service/api/users/{}", user_id))
        .headers(headers)
        .send()
        .await?;

    // 记录响应
    cx.span().set_attribute(KeyValue::new(
        "http.status_code",
        response.status().as_u16() as i64
    ));

    Ok(response)
}
```

### 跨服务追踪完整示例

```rust
// 服务A: API网关
async fn api_gateway_handler(request: Request<Body>) -> Response<Body> {
    let tracer = global::tracer("api-gateway");
    let mut span = tracer.start("api_gateway.request");

    // 提取入站context
    let cx = extract_trace_context(request.headers());
    let cx = Context::current_with_span(span);

    // 调用服务B
    let response_b = call_service_b(&cx).await;

    // 调用服务C
    let response_c = call_service_c(&cx).await;

    // 聚合响应
    aggregate_responses(response_b, response_c).await
}

// 服务B: 用户服务
async fn call_service_b(cx: &Context) -> Result<Response, Error> {
    let tracer = global::tracer("user-service");
    let mut span = tracer
        .span_builder("user_service.get_user")
        .start_with_context(&tracer, cx);

    // 注入context到出站请求
    let mut headers = HeaderMap::new();
    inject_trace_context(cx, &mut headers);

    // HTTP请求到服务B
    let client = Client::new();
    client
        .get("http://user-service/api/users/123")
        .headers(headers)
        .send()
        .await
}

// 服务C: 订单服务
async fn call_service_c(cx: &Context) -> Result<Response, Error> {
    let tracer = global::tracer("order-service");
    let mut span = tracer
        .span_builder("order_service.get_orders")
        .start_with_context(&tracer, cx);

    let mut headers = HeaderMap::new();
    inject_trace_context(cx, &mut headers);

    let client = Client::new();
    client
        .get("http://order-service/api/orders")
        .headers(headers)
        .send()
        .await
}
```

---

## 错误处理

### 错误追踪模式

```rust
use opentelemetry::trace::{Status, StatusCode};

#[instrument(err)]
async fn operation_that_may_fail() -> Result<String, ApiError> {
    // 错误会自动记录到span
    Err(ApiError::NotFound("User not found".to_string()))
}

// 手动错误记录
async fn manual_error_handling() -> Result<(), Error> {
    let tracer = global::tracer("api");
    let mut span = tracer.start("risky_operation");

    match risky_operation().await {
        Ok(result) => {
            span.set_status(Status::Ok);
            Ok(result)
        }
        Err(e) => {
            // 设置错误状态
            span.set_status(Status::error(e.to_string()));

            // 记录异常事件
            span.add_event(
                "exception",
                vec![
                    KeyValue::new("exception.type", "ApiError"),
                    KeyValue::new("exception.message", e.to_string()),
                    KeyValue::new("exception.stacktrace", format!("{:?}", e)),
                ],
            );

            Err(e)
        }
    }
}
```

### HTTP错误追踪

```rust
async fn http_error_handler(
    request: Request<Body>,
) -> Result<Response<Body>, Error> {
    let tracer = global::tracer("http-api");
    let mut span = tracer.start("http_request");

    match handle_request(request).await {
        Ok(response) => {
            let status = response.status();
            span.set_attribute(KeyValue::new("http.status_code", status.as_u16() as i64));

            // 根据状态码设置span状态
            if status.is_success() {
                span.set_status(Status::Ok);
            } else if status.is_client_error() {
                span.set_status(Status::error("Client error"));
            } else if status.is_server_error() {
                span.set_status(Status::error("Server error"));
            }

            Ok(response)
        }
        Err(e) => {
            span.set_attribute(KeyValue::new("http.status_code", 500));
            span.set_status(Status::error(e.to_string()));
            span.record_exception(&e);
            Err(e)
        }
    }
}
```

---

## 性能优化

### 采样策略

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingDecision, SamplingResult};

// 1. 比率采样 - 10%的请求
let sampler = Sampler::TraceIdRatioBased(0.1);

// 2. 始终采样 (开发环境)
let sampler = Sampler::AlwaysOn;

// 3. 从不采样 (禁用追踪)
let sampler = Sampler::AlwaysOff;

// 4. 父级采样 (遵循上游决策)
let sampler = Sampler::ParentBased(Box::new(Sampler::TraceIdRatioBased(0.1)));

// 5. 自定义采样策略
struct CustomSampler;

impl ShouldSample for CustomSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 基于请求路径的采样
        let should_sample = attributes
            .iter()
            .any(|kv| {
                kv.key.as_str() == "http.route" &&
                kv.value.as_str().starts_with("/api/important")
            });

        if should_sample {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: Vec::new(),
                trace_state: Default::default(),
            }
        }
    }
}
```

### 批量导出配置

```rust
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

let batch_config = BatchConfig::default()
    // 最大队列大小
    .with_max_queue_size(2048)
    // 最大导出批次大小
    .with_max_export_batch_size(512)
    // 导出延迟
    .with_scheduled_delay(Duration::from_secs(5))
    // 导出超时
    .with_max_export_timeout(Duration::from_secs(30));

let tracer_provider = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_batch_config(batch_config)
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

### 减少span数量

```rust
// ❌ 过度追踪 - 为每个小操作创建span
async fn over_traced() {
    let _span1 = tracer.start("validate_input");  // 不必要
    validate_input();

    let _span2 = tracer.start("parse_json");      // 不必要
    parse_json();

    let _span3 = tracer.start("check_auth");      // 不必要
    check_auth();
}

// ✅ 合理追踪 - 只追踪关键操作
async fn properly_traced() {
    let mut span = tracer.start("process_request");

    // 使用events代替sub-spans
    span.add_event("validation_started", vec![]);
    validate_input();
    span.add_event("validation_completed", vec![]);

    // 只为重要操作创建sub-span
    let result = database_query().await;

    span.end();
}
```

---

## 最佳实践

### ✅ 推荐做法

```rust
// 1. 使用instrument宏
#[instrument(skip(db), fields(user.id = %user_id))]
async fn get_user(user_id: u64, db: &DbPool) -> Result<User, Error> {
    db.get_user(user_id).await
}

// 2. 遵循命名约定
// 格式: {operation}.{resource}
tracer.start("http.request");
tracer.start("db.query");
tracer.start("cache.get");

// 3. 使用语义约定
span.set_attribute(semconv::trace::HTTP_REQUEST_METHOD.string("GET"));

// 4. 记录关键事件
span.add_event("user_authenticated", vec![
    KeyValue::new("user.id", user_id),
    KeyValue::new("auth.method", "oauth2"),
]);

// 5. 正确设置span状态
if success {
    span.set_status(Status::Ok);
} else {
    span.set_status(Status::error("Operation failed"));
}
```

### ❌ 避免的做法

```rust
// ❌ 不要在span中存储敏感信息
span.set_attribute(KeyValue::new("password", "secret123"));  // 危险!
span.set_attribute(KeyValue::new("credit_card", "1234-5678-9012-3456"));  // 危险!

// ❌ 不要创建过多的span
for item in items {
    let _span = tracer.start("process_item");  // 过度追踪
    process(item);
}

// ❌ 不要忘记结束span
let span = tracer.start("operation");
// ... 忘记调用 span.end()

// ❌ 不要在同步代码中使用异步追踪
fn sync_function() {
    // 会导致runtime错误
    let _span = tracer.start("sync_op");
}
```

### 📊 性能checklist

- [ ] 使用采样策略(生产环境<20%)
- [ ] 配置批量导出
- [ ] 限制span属性数量(<50个/span)
- [ ] 避免高频操作的详细追踪
- [ ] 使用异步导出
- [ ] 监控追踪开销(<5%)

---

## 总结

HTTP追踪的关键要素：

1. **标准化**: 遵循W3C Trace Context和OpenTelemetry语义约定
2. **自动化**: 使用中间件实现零侵入追踪
3. **完整性**: 覆盖请求生命周期的所有阶段
4. **性能**: 通过采样和批处理优化开销
5. **可观测**: 提供足够的上下文信息用于故障排查

**下一步**:

- 🔍 [REST API可观测性](./rest_api_observability.md)
- 📈 [性能优化](./performance_optimization.md)
- 🚀 [生产环境部署](./production_deployment.md)
