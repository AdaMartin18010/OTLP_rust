# 分布式追踪最佳实践 - Rust 完整版

## 目录

- [分布式追踪最佳实践 - Rust 完整版](#分布式追踪最佳实践---rust-完整版)
  - [目录](#目录)
  - [1. Span 设计原则](#1-span-设计原则)
    - [1.1 粒度控制](#11-粒度控制)
    - [1.2 命名规范](#12-命名规范)
    - [1.3 属性设置](#13-属性设置)
  - [2. Context 传播](#2-context-传播)
    - [2.1 HTTP 传播](#21-http-传播)
    - [2.2 异步任务传播](#22-异步任务传播)
    - [2.3 跨服务传播](#23-跨服务传播)
  - [3. 性能优化](#3-性能优化)
    - [3.1 采样策略](#31-采样策略)
    - [3.2 批量导出](#32-批量导出)
    - [3.3 异步处理](#33-异步处理)
  - [4. Trace 分析技巧](#4-trace-分析技巧)
    - [4.1 延迟分析](#41-延迟分析)
    - [4.2 错误追踪](#42-错误追踪)
    - [4.3 依赖关系](#43-依赖关系)
  - [5. 常见问题排查](#5-常见问题排查)
    - [5.1 Span 丢失](#51-span-丢失)
    - [5.2 Context 断链](#52-context-断链)
    - [5.3 性能瓶颈](#53-性能瓶颈)
  - [6. 高级技巧](#6-高级技巧)
    - [6.1 自定义属性](#61-自定义属性)
    - [6.2 动态采样](#62-动态采样)
    - [6.3 Exemplars](#63-exemplars)
  - [7. 微服务场景](#7-微服务场景)
    - [7.1 API Gateway](#71-api-gateway)
    - [7.2 服务网格](#72-服务网格)
    - [7.3 消息队列](#73-消息队列)
  - [8. 调试技巧](#8-调试技巧)
    - [8.1 本地调试](#81-本地调试)
    - [8.2 Jaeger UI](#82-jaeger-ui)
    - [8.3 日志关联](#83-日志关联)
  - [9. 生产环境实践](#9-生产环境实践)
    - [9.1 监控指标](#91-监控指标)
    - [9.2 告警规则](#92-告警规则)
    - [9.3 容量规划](#93-容量规划)
  - [10. 案例研究](#10-案例研究)
    - [10.1 电商下单流程](#101-电商下单流程)
    - [10.2 支付系统](#102-支付系统)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践清单](#最佳实践清单)
    - [反模式清单](#反模式清单)

---

## 1. Span 设计原则

### 1.1 粒度控制

````rust
use tracing::{info_span, instrument};

/// ✅ 好的粒度 - 关键操作
#[instrument(name = "process_order")]
pub async fn process_order(order_id: &str) -> Result<(), anyhow::Error> {
    // 验证订单
    validate_order(order_id).await?;
    
    // 处理支付
    process_payment(order_id).await?;
    
    // 更新库存
    update_inventory(order_id).await?;
    
    Ok(())
}

/// ✅ 适当的子 Span - 独立的业务操作
#[instrument(name = "validate_order", skip(order_id))]
async fn validate_order(order_id: &str) -> Result<(), anyhow::Error> {
    // 验证逻辑
    Ok(())
}

/// ❌ 过细的粒度 - 避免
async fn bad_example() {
    // 不要为每个小操作创建 Span
    let span1 = info_span!("check_null");
    let _guard1 = span1.enter();
    if order_id.is_empty() { return; }
    drop(_guard1);
    
    let span2 = info_span!("parse_int");
    let _guard2 = span2.enter();
    let id: i32 = order_id.parse().unwrap();
    drop(_guard2);
}

/// ✅ 合理的批处理 Span
#[instrument(name = "process_batch", skip(items), fields(batch_size = items.len()))]
pub async fn process_batch(items: Vec<Item>) -> Result<(), anyhow::Error> {
    for item in items {
        // 不要为每个 item 创建 Span
        process_item_internal(&item).await?;
    }
    Ok(())
}
````

**粒度原则**:

````text
✅ 应该创建 Span 的场景:
- HTTP/gRPC 请求
- 数据库查询
- 外部服务调用
- 关键业务操作
- 耗时操作 (> 10ms)
- 可能失败的操作

❌ 不应该创建 Span 的场景:
- 简单的计算 (< 1ms)
- 变量赋值
- 日志输出
- 循环内的单个迭代
- getter/setter 方法
````

### 1.2 命名规范

````rust
/// ✅ 好的 Span 命名
#[instrument(name = "http.request")]  // 协议.操作
async fn http_request() {}

#[instrument(name = "db.query")]      // 组件.操作
async fn db_query() {}

#[instrument(name = "order.create")]  // 业务.操作
async fn create_order() {}

/// ❌ 不好的 Span 命名
#[instrument(name = "doSomething")]   // 太模糊
async fn do_something() {}

#[instrument(name = "function_123")]  // 无意义
async fn function_123() {}

/// ✅ 动态命名
pub async fn http_request(method: &str, path: &str) {
    let span = tracing::info_span!(
        "http.request",
        "http.method" = %method,
        "http.target" = %path,
    );
    
    let _guard = span.enter();
    // 处理请求
}
````

**命名规范**:

````text
格式: <组件>.<操作>

组件:
- http: HTTP 请求
- grpc: gRPC 调用
- db: 数据库操作
- cache: 缓存操作
- mq: 消息队列
- business: 业务操作

操作:
- request: 请求
- query: 查询
- insert: 插入
- update: 更新
- delete: 删除
- publish: 发布
- consume: 消费
````

### 1.3 属性设置

````rust
use tracing::instrument;
use opentelemetry::KeyValue;

/// ✅ 完整的属性设置
#[instrument(
    name = "http.request",
    skip(request),
    fields(
        "http.method" = %request.method(),
        "http.target" = %request.uri().path(),
        "http.status_code" = tracing::field::Empty,
        "http.response_size" = tracing::field::Empty,
    )
)]
pub async fn handle_request(request: Request) -> Result<Response, Error> {
    let span = tracing::Span::current();
    
    let response = process_request(request).await?;
    
    // 记录响应属性
    span.record("http.status_code", response.status().as_u16());
    span.record("http.response_size", response.body().len());
    
    Ok(response)
}

/// ✅ 业务属性
#[instrument(
    name = "order.process",
    skip(order),
    fields(
        "order.id" = %order.id,
        "order.amount" = order.amount,
        "order.status" = %order.status,
        "user.id" = order.user_id,
    )
)]
pub async fn process_order(order: Order) -> Result<(), Error> {
    // 处理订单
    Ok(())
}

/// ❌ 避免敏感信息
#[instrument(
    name = "user.login",
    skip(credentials),
    fields(
        "user.name" = %credentials.username,
        // ❌ 不要记录密码
        // "password" = %credentials.password,
    )
)]
pub async fn login(credentials: Credentials) -> Result<Token, Error> {
    // 登录逻辑
    Ok(Token::default())
}
````

---

## 2. Context 传播

### 2.1 HTTP 传播

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
};
use opentelemetry::global;
use opentelemetry_http::HeaderExtractor;

/// HTTP Context 传播中间件
pub async fn trace_middleware(
    request: Request,
    next: Next,
) -> Response {
    // 提取 Context
    let parent_context = global::get_text_map_propagator(|propagator| {
        propagator.extract(&HeaderExtractor(request.headers()))
    });
    
    // 创建 Span
    let span = tracing::info_span!(
        "http.request",
        "http.method" = %request.method(),
        "http.target" = %request.uri().path(),
    );
    
    // 设置 parent context
    span.set_parent(parent_context);
    
    let _guard = span.enter();
    
    let response = next.run(request).await;
    
    response
}

/// HTTP 客户端 Context 注入
use reqwest::Client;
use opentelemetry_http::HeaderInjector;

pub async fn http_client_request(url: &str) -> Result<String, reqwest::Error> {
    let client = Client::new();
    let mut request = client.get(url).build()?;
    
    // 注入 Context
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut HeaderInjector(request.headers_mut())
        )
    });
    
    let response = client.execute(request).await?;
    let body = response.text().await?;
    
    Ok(body)
}
````

### 2.2 异步任务传播

````rust
use tokio::task;
use tracing::Instrument;

/// ✅ 正确的异步任务 Context 传播
pub async fn spawn_with_context() {
    let span = tracing::info_span!("parent_operation");
    let _guard = span.enter();
    
    // 方法1: 使用 Instrument trait
    let child_span = tracing::info_span!("child_operation");
    tokio::spawn(
        async move {
            // 子任务逻辑
            process_child_task().await;
        }
        .instrument(child_span)  // 传播 Context
    );
    
    // 方法2: 手动传播
    let current_span = tracing::Span::current();
    tokio::spawn(async move {
        let _guard = current_span.enter();
        // 子任务逻辑
        process_child_task().await;
    });
}

/// ❌ 错误的异步任务 (Context 丢失)
pub async fn spawn_without_context() {
    let span = tracing::info_span!("parent_operation");
    let _guard = span.enter();
    
    // ❌ Context 丢失
    tokio::spawn(async move {
        // 这里没有 parent context
        process_child_task().await;
    });
}

/// ✅ 线程池 Context 传播
use rayon::prelude::*;

pub fn parallel_processing(items: Vec<Item>) {
    let span = tracing::info_span!("parallel_processing");
    let _guard = span.enter();
    
    items.par_iter().for_each(|item| {
        // 每个线程创建独立的 Span
        let item_span = tracing::info_span!(
            "process_item",
            "item.id" = %item.id
        );
        let _item_guard = item_span.enter();
        
        process_item(item);
    });
}
````

### 2.3 跨服务传播

````rust
/// gRPC Context 传播
use tonic::{Request, Response, Status};
use opentelemetry::global;

pub async fn grpc_call(
    request: Request<MyRequest>
) -> Result<Response<MyResponse>, Status> {
    // 提取 Context
    let parent_context = global::get_text_map_propagator(|propagator| {
        propagator.extract(&GrpcMetadataExtractor(request.metadata()))
    });
    
    let span = tracing::info_span!("grpc.call");
    span.set_parent(parent_context);
    
    let _guard = span.enter();
    
    // 处理请求
    Ok(Response::new(MyResponse::default()))
}

/// Kafka Context 传播
use rdkafka::message::Message;

pub async fn kafka_consume(message: &BorrowedMessage<'_>) {
    // 从 Kafka Headers 提取 Context
    let parent_context = extract_context_from_kafka_headers(message.headers());
    
    let span = tracing::info_span!("kafka.consume");
    span.set_parent(parent_context);
    
    let _guard = span.enter();
    
    // 处理消息
}

fn extract_context_from_kafka_headers(headers: Option<&Headers>) -> Context {
    // 实现 Context 提取逻辑
    Context::current()
}
````

---

## 3. 性能优化

### 3.1 采样策略

````rust
use opentelemetry::sdk::trace::{Sampler, SamplingDecision, SamplingResult};
use opentelemetry::trace::{TraceId, SpanKind, Link};

/// 自适应采样器
pub struct AdaptiveSampler {
    base_rate: f64,
    error_rate: f64,
    slow_rate: f64,
}

impl Sampler for AdaptiveSampler {
    fn should_sample(
        &self,
        parent_context: Option<&Context>,
        trace_id: TraceId,
        name: &str,
        span_kind: &SpanKind,
        attributes: &[KeyValue],
        links: &[Link],
    ) -> SamplingResult {
        // 1. 总是采样错误
        if attributes.iter().any(|kv| kv.key.as_str() == "error" && kv.value.as_str() == "true") {
            return SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            };
        }
        
        // 2. 高延迟请求采样
        if let Some(duration) = attributes.iter()
            .find(|kv| kv.key.as_str() == "duration_ms")
            .and_then(|kv| kv.value.as_str().parse::<f64>().ok())
        {
            if duration > 1000.0 {  // > 1s
                return SamplingResult {
                    decision: SamplingDecision::RecordAndSample,
                    attributes: vec![],
                    trace_state: Default::default(),
                };
            }
        }
        
        // 3. 基于 trace_id 的概率采样
        let threshold = (self.base_rate * u64::MAX as f64) as u64;
        let trace_id_u64 = u64::from_be_bytes(trace_id.to_bytes()[..8].try_into().unwrap());
        
        if trace_id_u64 <= threshold {
            SamplingResult {
                decision: SamplingDecision::RecordAndSample,
                attributes: vec![],
                trace_state: Default::default(),
            }
        } else {
            SamplingResult {
                decision: SamplingDecision::Drop,
                attributes: vec![],
                trace_state: Default::default(),
            }
        }
    }
}
````

### 3.2 批量导出

````rust
use opentelemetry_sdk::trace::{Config, BatchConfig};

/// 优化的批量导出配置
pub fn init_tracing_with_batch() -> Result<(), Box<dyn std::error::Error>> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://collector:4317")
        )
        .with_trace_config(
            Config::default()
                .with_sampler(Sampler::ParentBased(Box::new(
                    Sampler::TraceIdRatioBased(0.1)  // 10% 采样
                )))
        )
        .with_batch_config(
            BatchConfig::default()
                .with_max_queue_size(2048)           // 队列大小
                .with_scheduled_delay(Duration::from_secs(5))  // 延迟
                .with_max_export_batch_size(512)     // 批次大小
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(())
}
````

### 3.3 异步处理

````rust
/// ✅ 异步非阻塞
#[instrument(name = "async_operation")]
pub async fn async_operation() {
    // Span 自动异步导出，不阻塞业务逻辑
    heavy_computation().await;
}

/// ✅ 避免在热路径记录
pub async fn hot_path(items: Vec<Item>) {
    // ❌ 不要在循环内记录详细 Span
    // for item in &items {
    //     let span = info_span!("process_item", item_id = item.id);
    //     let _guard = span.enter();
    //     process_item(item);
    // }
    
    // ✅ 只记录批次级别的 Span
    let span = tracing::info_span!(
        "process_batch",
        batch_size = items.len()
    );
    let _guard = span.enter();
    
    for item in items {
        process_item_internal(&item);  // 不创建 Span
    }
}
````

---

## 4. Trace 分析技巧

### 4.1 延迟分析

````promql
# Jaeger UI 查询

# 1. 找出 P99 延迟的 Trace
duration > 1000ms
limit: 100
sort: duration desc

# 2. 查找特定服务的慢 Trace
service="order-service" AND duration > 500ms

# 3. 查找特定操作的慢 Trace
operation="db.query" AND duration > 100ms

# 4. 按 Span 数量排序
sort: spanCount desc
````

**延迟分析步骤**:

````text
1. 找出最慢的 Trace
   - 查看瀑布图
   - 识别最长的 Span

2. 分析 Span 层级
   - 串行 vs 并行
   - 不必要的等待

3. 定位瓶颈
   - 数据库查询慢
   - 外部服务调用慢
   - CPU 密集计算

4. 优化建议
   - 并行化
   - 缓存
   - 索引优化
````

### 4.2 错误追踪

````rust
use tracing::{error, instrument};

#[instrument(name = "process_order", err)]
pub async fn process_order(order_id: &str) -> Result<(), anyhow::Error> {
    // 自动记录错误到 Span
    validate_order(order_id).await?;
    
    Ok(())
}

/// 手动记录错误详情
pub async fn detailed_error_handling() {
    let span = tracing::Span::current();
    
    match risky_operation().await {
        Ok(result) => {
            span.record("result", "success");
        }
        Err(e) => {
            span.record("error", true);
            span.record("error.type", std::any::type_name_of_val(&e));
            span.record("error.message", &format!("{}", e));
            error!(error = %e, "Operation failed");
        }
    }
}
````

**Jaeger UI 错误查询**:

````text
# 查找所有错误 Trace
error=true

# 查找特定错误类型
tags.error.type="DatabaseError"

# 查找特定服务的错误
service="order-service" AND error=true
````

### 4.3 依赖关系

````text
Jaeger UI 依赖关系分析:

1. Dependencies Tab
   - 查看服务依赖图
   - 识别关键路径
   - 发现循环依赖

2. 分析调用链
   A (API Gateway)
   └─> B (Order Service)
       ├─> C (Payment Service)
       ├─> D (Inventory Service)
       └─> E (Notification Service)

3. 识别问题
   - 过多的服务跳转
   - 不必要的依赖
   - 单点故障
````

---

## 5. 常见问题排查

### 5.1 Span 丢失

````text
问题: Trace 中缺少某些 Span

排查步骤:
1. 检查采样率
   - 是否被采样器过滤

2. 检查 Context 传播
   - HTTP headers 是否正确注入
   - 异步任务是否正确传播

3. 检查导出配置
   - 批次是否丢失
   - 网络连接是否正常

4. 检查超时配置
   - Span 是否超时未导出
````

````rust
/// 调试 Span 丢失
pub async fn debug_span_loss() {
    // 1. 启用调试日志
    std::env::set_var("RUST_LOG", "opentelemetry=debug");
    
    // 2. 使用 Logging Exporter 验证
    let tracer = opentelemetry_stdout::new_pipeline()
        .install_simple();
    
    // 3. 检查 Span 是否创建
    let span = tracing::info_span!("test_span");
    let _guard = span.enter();
    
    // 4. 强制刷新
    opentelemetry::global::shutdown_tracer_provider();
}
````

### 5.2 Context 断链

````rust
/// 问题: 子 Span 没有关联到父 Span

/// ❌ 错误示例
pub async fn broken_context() {
    let span1 = tracing::info_span!("parent");
    let _guard1 = span1.enter();
    
    // Context 断链
    tokio::spawn(async {
        // 这里丢失了 parent context
        let span2 = tracing::info_span!("child");
        let _guard2 = span2.enter();
    });
}

/// ✅ 正确示例
pub async fn fixed_context() {
    let span1 = tracing::info_span!("parent");
    let _guard1 = span1.enter();
    
    let child_span = tracing::info_span!("child");
    tokio::spawn(async move {}.instrument(child_span));
}

/// 验证 Context 传播
pub fn verify_context() {
    let span = tracing::Span::current();
    let context = span.context();
    let span_context = context.span().span_context();
    
    println!("Trace ID: {}", span_context.trace_id());
    println!("Span ID: {}", span_context.span_id());
    println!("Is Sampled: {}", span_context.is_sampled());
}
````

### 5.3 性能瓶颈

````text
问题: Tracing 导致性能下降

排查步骤:
1. 检查采样率
   - 生产环境建议 1-10%
   - 开发环境可以 100%

2. 检查 Span 粒度
   - 是否创建了过多细粒度 Span
   - 热路径是否有不必要的 Span

3. 检查导出配置
   - 批量导出大小
   - 导出延迟

4. 检查属性数量
   - 避免大量属性
   - 避免大对象序列化
````

````rust
/// 性能优化配置
pub fn optimized_tracing_config() -> Config {
    Config::default()
        // 低采样率
        .with_sampler(Sampler::TraceIdRatioBased(0.01))  // 1%
        // 大批次
        .with_max_events_per_span(32)
        .with_max_attributes_per_span(32)
}
````

---

## 6. 高级技巧

### 6.1 自定义属性

````rust
use opentelemetry::trace::{TraceContextExt, SpanKind};

/// 自定义业务属性
pub async fn custom_attributes() {
    let span = tracing::Span::current();
    let context = span.context();
    let otel_span = context.span();
    
    // 添加自定义属性
    otel_span.set_attribute(KeyValue::new("business.tenant_id", "tenant-123"));
    otel_span.set_attribute(KeyValue::new("business.user_tier", "premium"));
    otel_span.set_attribute(KeyValue::new("business.ab_test", "variant-b"));
    
    // 添加事件
    otel_span.add_event(
        "order.validated",
        vec![
            KeyValue::new("validation.result", "success"),
            KeyValue::new("validation.duration_ms", 45),
        ],
    );
}
````

### 6.2 动态采样

````rust
/// 基于实时负载的动态采样
pub struct LoadBasedSampler {
    base_rate: AtomicU64,  // 基础采样率 (0-100)
    max_qps: u64,
    current_qps: AtomicU64,
}

impl LoadBasedSampler {
    pub fn adjust_sampling_rate(&self) {
        let current = self.current_qps.load(Ordering::Relaxed);
        
        let new_rate = if current > self.max_qps {
            // 负载高，降低采样率
            (self.base_rate.load(Ordering::Relaxed) / 2).max(1)
        } else {
            // 负载低，提高采样率
            (self.base_rate.load(Ordering::Relaxed) * 2).min(100)
        };
        
        self.base_rate.store(new_rate, Ordering::Relaxed);
    }
}
````

### 6.3 Exemplars

````rust
/// Exemplars: 将 Trace 关联到 Metrics
use prometheus::{HistogramOpts, HistogramVec, register_histogram_vec};

pub struct MetricsWithExemplars {
    http_duration: HistogramVec,
}

impl MetricsWithExemplars {
    pub fn record_request(&self, duration: f64, trace_id: &str, span_id: &str) {
        // 记录 Metrics
        self.http_duration
            .with_label_values(&["GET", "/api/users"])
            .observe(duration);
        
        // 添加 Exemplar (Prometheus 1.x+)
        // 将 trace_id 和 span_id 关联到 metric
    }
}
````

---

## 7. 微服务场景

### 7.1 API Gateway

````rust
/// API Gateway Tracing
#[instrument(
    name = "gateway.request",
    skip(request),
    fields(
        "http.method" = %request.method(),
        "http.target" = %request.uri().path(),
        "gateway.route" = tracing::field::Empty,
    )
)]
pub async fn gateway_handler(request: Request) -> Result<Response, Error> {
    let span = tracing::Span::current();
    
    // 路由匹配
    let route = match_route(&request)?;
    span.record("gateway.route", &route.service_name);
    
    // 转发请求 (自动传播 Context)
    let response = forward_request(&route, request).await?;
    
    Ok(response)
}
````

### 7.2 服务网格

````yaml
# Istio / Linkerd 配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-tracing
data:
  tracing: |
    enableTracing: true
    sampling: 1.0  # 100% 采样 (由 Istio 控制)
    zipkin:
      address: collector.monitoring:9411
````

### 7.3 消息队列

````rust
/// Kafka Producer with Tracing
use rdkafka::producer::{FutureProducer, FutureRecord};
use opentelemetry::global;
use opentelemetry_http::HeaderInjector;

#[instrument(name = "kafka.produce", skip(producer, message))]
pub async fn produce_with_tracing(
    producer: &FutureProducer,
    topic: &str,
    message: &str,
) -> Result<(), Error> {
    // 创建 Kafka Headers
    let mut headers = OwnedHeaders::new();
    
    // 注入 Trace Context
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(
            &tracing::Span::current().context(),
            &mut KafkaHeaderInjector(&mut headers)
        )
    });
    
    // 发送消息
    let record = FutureRecord::to(topic)
        .payload(message)
        .headers(headers);
    
    producer.send(record, Duration::from_secs(0)).await?;
    
    Ok(())
}
````

---

## 8. 调试技巧

### 8.1 本地调试

````rust
/// 本地调试配置
pub fn init_local_debugging() {
    // 1. 使用 stdout exporter
    let tracer = opentelemetry_stdout::new_pipeline()
        .with_pretty_print(true)
        .install_simple();
    
    // 2. 100% 采样
    std::env::set_var("OTEL_TRACES_SAMPLER", "always_on");
    
    // 3. 详细日志
    std::env::set_var("RUST_LOG", "debug,opentelemetry=trace");
    
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::TRACE)
        .init();
}
````

### 8.2 Jaeger UI

````text
Jaeger UI 使用技巧:

1. 查找 Trace
   - Service: 选择服务
   - Operation: 选择操作
   - Tags: 添加过滤条件
   - Duration: 设置延迟范围

2. 分析 Trace
   - Timeline View: 瀑布图
   - Trace Graph: 依赖关系
   - JSON View: 原始数据

3. 比较 Trace
   - 选择多个 Trace
   - Compare 对比差异

4. 快捷键
   - [ / ]: 展开/折叠所有 Span
   - Ctrl+F: 搜索
````

### 8.3 日志关联

````rust
use tracing::{info, instrument};
use opentelemetry::trace::TraceContextExt;

#[instrument(name = "operation_with_logs")]
pub async fn operation_with_logs() {
    let span = tracing::Span::current();
    let context = span.context();
    let span_context = context.span().span_context();
    
    // 日志中包含 trace_id 和 span_id
    info!(
        trace_id = %span_context.trace_id(),
        span_id = %span_context.span_id(),
        "Processing operation"
    );
}
````

---

## 9. 生产环境实践

### 9.1 监控指标

````promql
# Prometheus 监控 Tracing 系统

# 1. Trace 生成速率
rate(traces_generated_total[5m])

# 2. Span 丢弃率
rate(spans_dropped_total[5m]) / rate(spans_generated_total[5m])

# 3. 导出延迟
histogram_quantile(0.99, rate(span_export_duration_seconds_bucket[5m]))

# 4. 错误率
rate(trace_errors_total[5m])
````

### 9.2 告警规则

````yaml
# alerts.yml
groups:
  - name: tracing
    rules:
      - alert: HighSpanDropRate
        expr: |
          rate(spans_dropped_total[5m]) / rate(spans_generated_total[5m]) > 0.1
        for: 5m
        annotations:
          summary: "High span drop rate"
          description: "{{ $value }}% spans are being dropped"
      
      - alert: TraceExportFailure
        expr: |
          rate(trace_export_errors_total[5m]) > 10
        for: 5m
        annotations:
          summary: "Trace export failing"
````

### 9.3 容量规划

````text
容量规划计算:

1. 估算 Span 生成量
   QPS: 10,000 请求/秒
   Spans per request: 20
   Total Spans/s: 200,000

2. 采样后的 Span 量
   Sampling rate: 1%
   Sampled Spans/s: 2,000

3. 存储需求
   Span size: ~2KB
   Daily data: 2000 * 86400 * 2KB ≈ 345GB/天
   Retention: 7 天
   Total storage: ~2.4TB

4. 网络带宽
   2000 spans/s * 2KB = 4MB/s
   Peak (3x): 12MB/s
````

---

## 10. 案例研究

### 10.1 电商下单流程

````rust
/// 完整的电商下单 Trace
#[instrument(name = "order.create", skip(order_req))]
pub async fn create_order(order_req: OrderRequest) -> Result<Order, Error> {
    // 1. 验证用户
    let user = validate_user(&order_req.user_id).await?;
    
    // 2. 检查库存
    let inventory_check = check_inventory(&order_req.items).await?;
    
    // 3. 计算价格
    let price = calculate_price(&order_req.items, &user).await?;
    
    // 4. 创建订单
    let order = create_order_record(&order_req, price).await?;
    
    // 5. 并行处理
    let (payment_result, inventory_result, notification_result) = tokio::join!(
        process_payment(&order),
        reserve_inventory(&order),
        send_notification(&order),
    );
    
    payment_result?;
    inventory_result?;
    notification_result?;
    
    Ok(order)
}

#[instrument(name = "payment.process", skip(order))]
async fn process_payment(order: &Order) -> Result<(), Error> {
    // 支付逻辑
    Ok(())
}
````

**Trace 分析**:

````text
order.create (500ms)
├─ user.validate (50ms)
├─ inventory.check (100ms)
├─ price.calculate (30ms)
├─ order.create_record (20ms)
└─ [parallel]
   ├─ payment.process (200ms)  ← 瓶颈
   ├─ inventory.reserve (80ms)
   └─ notification.send (50ms)

优化建议: 优化支付处理，从 200ms 降到 100ms
````

### 10.2 支付系统

````rust
/// 支付系统 Trace
#[instrument(
    name = "payment.process",
    skip(payment_req),
    fields(
        "payment.id" = %payment_req.id,
        "payment.amount" = payment_req.amount,
        "payment.method" = %payment_req.method,
        "payment.status" = tracing::field::Empty,
    )
)]
pub async fn process_payment(payment_req: PaymentRequest) -> Result<Payment, Error> {
    let span = tracing::Span::current();
    
    // 1. 风控检查
    let risk_check = risk_assessment(&payment_req).await?;
    if risk_check.is_high_risk() {
        span.record("payment.status", "rejected");
        return Err(Error::HighRisk);
    }
    
    // 2. 调用第三方支付
    let payment_result = call_payment_gateway(&payment_req).await?;
    
    // 3. 更新数据库
    let payment = save_payment_record(&payment_result).await?;
    
    span.record("payment.status", "success");
    
    Ok(payment)
}
````

---

## 总结

### 核心要点

1. **Span 设计**: 合理粒度、清晰命名、完整属性
2. **Context 传播**: HTTP、异步、跨服务正确传播
3. **性能优化**: 采样策略、批量导出、异步处理
4. **Trace 分析**: 延迟分析、错误追踪、依赖关系
5. **问题排查**: Span 丢失、Context 断链、性能瓶颈

### 最佳实践清单

- ✅ 使用 `#[instrument]` 宏简化 Span 创建
- ✅ 为关键操作创建 Span（HTTP、DB、外部调用）
- ✅ 使用语义化命名（`http.request`, `db.query`）
- ✅ 设置完整的属性（method, path, status）
- ✅ 正确传播 Context（HTTP headers、异步任务）
- ✅ 配置合理的采样率（生产环境 1-10%）
- ✅ 使用批量导出减少开销
- ✅ 记录错误到 Span（`err` 参数）
- ✅ 关联日志和 Trace（trace_id、span_id）
- ✅ 监控 Tracing 系统本身（drop rate、export latency）
- ✅ 定期分析 Trace 优化性能
- ✅ 使用 Jaeger UI 进行可视化分析

### 反模式清单

- ❌ 不要创建过细粒度的 Span
- ❌ 不要在循环内创建 Span
- ❌ 不要记录敏感信息（密码、token）
- ❌ 不要在异步任务中丢失 Context
- ❌ 不要使用 100% 采样率（生产环境）
- ❌ 不要忽略 Span 导出失败
- ❌ 不要设置过多的属性
- ❌ 不要忘记设置超时
- ❌ 不要在热路径创建详细 Span
- ❌ 不要忽略 Tracing 系统的性能影响

---

**相关文档**:

- [分布式追踪进阶](../02_Semantic_Conventions/03_日志与事件/02_分布式追踪进阶_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [故障排查指南](./01_Rust_OTLP_故障排查完全指南.md)
- [调试工具](./02_调试工具_Rust完整版.md)
