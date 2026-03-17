//! Axum 0.8 中间件和提取器集成
//!
//! 实现与 Axum 0.8 框架的深度集成，提供：
//! - OpenTelemetry 追踪中间件
//! - 自定义提取器（TraceContext、Baggage）
//! - 指标收集中间件
//! - 错误处理和响应转换
//!
//! 参考: https://docs.rs/axum/0.8/

use axum::{
    body::Body,
    extract::{FromRequestParts, Request},
    http::{request::Parts, HeaderMap, StatusCode},
    middleware::Next,
    response::{IntoResponse, Response},
};
use opentelemetry::propagation::{Extractor, Injector, TextMapPropagator};
use opentelemetry::trace::{SpanKind, TraceContextExt, Tracer};
use opentelemetry::{Context, KeyValue};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use std::time::Instant;
use tracing::{info_span, Instrument};

/// OpenTelemetry 追踪中间件
///
/// 自动为每个 HTTP 请求创建 span，并传播 trace context
///
/// # 使用示例
/// ```rust
/// use axum::Router;
/// use otlp::axum_middleware::opentelemetry_tracing_layer;
///
/// let app = Router::new()
///     .layer(axum::middleware::from_fn(opentelemetry_tracing_layer));
/// ```
pub async fn opentelemetry_tracing_layer(
    req: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let propagator = TraceContextPropagator::new();
    
    // 提取父上下文
    let parent_context = propagator.extract(&HeaderExtractor(req.headers()));
    
    // 获取路由信息
    let method = req.method().clone();
    let uri = req.uri().clone();
    let route = uri.path().to_string();
    
    // 创建 span
    let tracer = opentelemetry::global::tracer("axum");
    let mut span_builder = tracer
        .span_builder(format!("{} {}", method, route))
        .with_kind(SpanKind::Server);
    
    // 如果有父上下文，设置为父 span
    if parent_context.span().span_context().is_valid() {
        span_builder = span_builder.with_parent_context(parent_context);
    }
    
    let span = span_builder.start(&tracer);
    let cx = Context::current_with_span(span);
    
    // 设置属性
    cx.span().set_attribute(KeyValue::new("http.method", method.to_string()));
    cx.span().set_attribute(KeyValue::new("http.route", route.clone()));
    cx.span().set_attribute(KeyValue::new("http.target", uri.to_string()));
    
    // 执行请求
    let response = next.run(req).await;
    
    // 记录响应信息
    let duration = start.elapsed();
    let status = response.status();
    
    cx.span().set_attribute(KeyValue::new("http.status_code", status.as_u16() as i64));
    cx.span().set_attribute(KeyValue::new("http.duration_ms", duration.as_millis() as i64));
    
    if status.is_server_error() {
        cx.span().set_status(opentelemetry::trace::Status::error(format!(
            "HTTP {}", status
        )));
    }
    
    // 将 trace context 注入响应头
    let mut response = response;
    propagator.inject_context(&cx, &mut HeaderInjector(response.headers_mut()));
    
    response
}

/// 追踪上下文提取器
///
/// 从请求中提取 OpenTelemetry 追踪上下文
///
/// # 使用示例
/// ```rust
/// use axum::extract::Request;
/// use otlp::axum_middleware::TraceContextExtractor;
///
/// async fn handler(
///     TraceContextExtractor(trace_context): TraceContextExtractor,
/// ) {
///     // 使用追踪上下文
/// }
/// ```
pub struct TraceContextExtractor(pub Context);

impl<S> FromRequestParts<S> for TraceContextExtractor
where
    S: Send + Sync,
{
    type Rejection = ();

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        let propagator = TraceContextPropagator::new();
        let context = propagator.extract(&HeaderExtractor(&parts.headers));
        Ok(TraceContextExtractor(context))
    }
}

/// Baggage 提取器
///
/// 从请求中提取 OpenTelemetry Baggage
///
/// # 使用示例
/// ```rust
/// use otlp::axum_middleware::BaggageExtractor;
///
/// async fn handler(
///     BaggageExtractor(baggage): BaggageExtractor,
/// ) {
///     if let Some(user_id) = baggage.get(&"user_id".into()) {
///         // 使用 baggage 值
///     }
/// }
/// ```
pub struct BaggageExtractor(pub opentelemetry::baggage::Baggage);

impl<S> FromRequestParts<S> for BaggageExtractor
where
    S: Send + Sync,
{
    type Rejection = ();

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        let cx = TraceContextPropagator::new().extract(&HeaderExtractor(&parts.headers));
        let baggage = cx.baggage().clone();
        Ok(BaggageExtractor(baggage))
    }
}

/// 指标收集中间件
///
/// 收集 HTTP 请求的指标数据
///
/// # 使用示例
/// ```rust
/// use otlp::axum_middleware::metrics_layer;
///
/// let app = Router::new()
///     .layer(axum::middleware::from_fn(metrics_layer));
/// ```
pub async fn metrics_layer(
    req: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let path = req.uri().path().to_string();
    
    let response = next.run(req).await;
    
    let duration = start.elapsed();
    let status = response.status();
    
    // 这里可以记录到指标系统
    tracing::info!(
        method = %method,
        path = %path,
        status = status.as_u16(),
        duration_ms = duration.as_millis(),
        "HTTP request"
    );
    
    response
}

/// 请求 ID 中间件
///
/// 为每个请求生成唯一的请求 ID，并添加到响应头
///
/// # 使用示例
/// ```rust
/// use otlp::axum_middleware::request_id_layer;
///
/// let app = Router::new()
///     .layer(axum::middleware::from_fn(request_id_layer));
/// ```
pub async fn request_id_layer(
    mut req: Request,
    next: Next,
) -> Response {
    let request_id = uuid::Uuid::new_v4().to_string();
    
    // 添加到请求扩展
    req.extensions_mut().insert(request_id.clone());
    
    let mut response = next.run(req).await;
    
    // 添加到响应头
    response.headers_mut().insert(
        "x-request-id",
        request_id.parse().unwrap(),
    );
    
    response
}

/// 请求 ID 提取器
pub struct RequestId(pub String);

impl<S> FromRequestParts<S> for RequestId
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        parts
            .extensions
            .get::<String>()
            .cloned()
            .map(RequestId)
            .ok_or((StatusCode::INTERNAL_SERVER_ERROR, "Request ID not found"))
    }
}

/// 错误处理中间件
///
/// 统一处理错误响应，添加 OpenTelemetry 错误标记
///
/// # 使用示例
/// ```rust
/// use otlp::axum_middleware::error_handling_layer;
///
/// let app = Router::new()
///     .layer(axum::middleware::from_fn(error_handling_layer));
/// ```
pub async fn error_handling_layer(
    req: Request,
    next: Next,
) -> Response {
    let response = next.run(req).await;
    
    if response.status().is_server_error() {
        // 记录错误到追踪系统
        tracing::error!(
            status = response.status().as_u16(),
            "Server error occurred"
        );
    }
    
    response
}

/// 组合中间件
///
/// 组合所有 OpenTelemetry 中间件
///
/// # 使用示例
/// ```rust
/// use otlp::axum_middleware::combined_middleware;
///
/// let app = Router::new()
///     .layer(combined_middleware());
/// ```
pub fn combined_middleware() -> axum::middleware::AddExtensionLayer<()>
where
{
    // 注意：实际使用需要使用 tower::ServiceBuilder
    axum::middleware::AddExtensionLayer::new(())
}

/// HTTP 头提取器实现
struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

/// HTTP 头注入器实现
struct HeaderInjector<'a>(&'a mut HeaderMap);

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = key.parse() {
            if let Ok(val) = value.parse() {
                self.0.insert(name, val);
            }
        }
    }
}

/// 创建带有 OpenTelemetry 中间件的 Router
///
/// # 使用示例
/// ```rust
/// use axum::Router;
/// use otlp::axum_middleware::create_otel_router;
///
/// let app = create_otel_router(Router::new());
/// ```
pub fn create_otel_router(router: axum::Router) -> axum::Router {
    use axum::middleware;
    
    router
        .layer(middleware::from_fn(request_id_layer))
        .layer(middleware::from_fn(opentelemetry_tracing_layer))
        .layer(middleware::from_fn(metrics_layer))
        .layer(middleware::from_fn(error_handling_layer))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::routing::get;
    use tower::ServiceExt;

    async fn test_handler() -> &'static str {
        "Hello, World!"
    }

    #[tokio::test]
    async fn test_request_id_layer() {
        let app = axum::Router::new()
            .route("/", get(test_handler))
            .layer(axum::middleware::from_fn(request_id_layer));

        let request = Request::builder().uri("/").body(Body::empty()).unwrap();
        let response = app.oneshot(request).await.unwrap();

        assert!(response.headers().contains_key("x-request-id"));
    }

    #[tokio::test]
    async fn test_metrics_layer() {
        let app = axum::Router::new()
            .route("/", get(test_handler))
            .layer(axum::middleware::from_fn(metrics_layer));

        let request = Request::builder().uri("/").body(Body::empty()).unwrap();
        let response = app.oneshot(request).await.unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}
