# 🔗 SpanLinks Rust 完整版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [1. SpanLinks 概述](#1-spanlinks-概述)
- [2. SpanLinks 定义](#2-spanlinks-定义)
- [3. 使用场景](#3-使用场景)
- [4. Rust 实现](#4-rust-实现)
- [5. 高级用法](#5-高级用法)
- [6. 最佳实践](#6-最佳实践)
- [7. 性能优化](#7-性能优化)
- [8. 实战案例](#8-实战案例)

---

## 1. SpanLinks 概述

### 1.1 什么是 SpanLinks？

**SpanLinks** 用于关联 Span 之间的因果关系，但不同于父子关系：

- **父子关系**: 强依赖，同步调用链
- **SpanLinks**: 弱关联，异步/批处理关系

### 1.2 SpanLinks vs Parent-Child

```text
父子关系（Parent-Child）:
Parent Span
    └─► Child Span (同步，强依赖)

SpanLinks:
Span A ─┐
Span B ─┼──► Span C (异步，弱关联)
Span D ─┘
```

### 1.3 核心概念

| 概念 | 说明 | 示例 |
|------|------|------|
| **Link** | 指向另一个 Span 的引用 | 批处理任务链接源消息 |
| **TraceContext** | 被链接 Span 的上下文 | TraceId + SpanId |
| **Attributes** | 描述链接关系的元数据 | link.type = "follows_from" |

---

## 2. SpanLinks 定义

### 2.1 数据结构

根据 OpenTelemetry 规范，SpanLink 包含：

```rust
use opentelemetry::trace::{SpanContext, TraceContextExt};
use opentelemetry::KeyValue;

#[derive(Debug, Clone)]
pub struct SpanLink {
    /// 被链接 Span 的上下文
    pub span_context: SpanContext,
    
    /// 描述链接关系的属性
    pub attributes: Vec<KeyValue>,
}

impl SpanLink {
    pub fn new(span_context: SpanContext, attributes: Vec<KeyValue>) -> Self {
        Self {
            span_context,
            attributes,
        }
    }
}
```

### 2.2 SpanContext 结构

```rust
use opentelemetry::trace::{TraceId, SpanId, TraceFlags, TraceState};

#[derive(Debug, Clone)]
pub struct SpanContext {
    /// 128-bit Trace ID
    pub trace_id: TraceId,
    
    /// 64-bit Span ID
    pub span_id: SpanId,
    
    /// Trace 标志（采样位）
    pub trace_flags: TraceFlags,
    
    /// 供应商特定的追踪状态
    pub trace_state: TraceState,
    
    /// 是否为远程 SpanContext
    pub is_remote: bool,
}
```

### 2.3 OpenTelemetry Rust SDK 实现

```rust
use opentelemetry::{
    trace::{Link, SpanContext, TraceContextExt},
    KeyValue,
};

// OpenTelemetry SDK 提供的 Link 定义
pub struct Link {
    span_context: SpanContext,
    attributes: Vec<KeyValue>,
}

impl Link {
    pub fn new(span_context: SpanContext, attributes: Vec<KeyValue>) -> Self {
        Self {
            span_context,
            attributes,
        }
    }
    
    pub fn span_context(&self) -> &SpanContext {
        &self.span_context
    }
    
    pub fn attributes(&self) -> &[KeyValue] {
        &self.attributes
    }
}
```

---

## 3. 使用场景

### 3.1 批处理场景

**问题**: 一个批处理任务处理多条消息，如何关联？

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};

async fn batch_processor(messages: Vec<Message>) -> Result<(), Error> {
    let tracer = global::tracer("batch-processor");
    
    // 收集所有消息的 SpanContext
    let links: Vec<Link> = messages
        .iter()
        .filter_map(|msg| msg.span_context.as_ref())
        .map(|ctx| {
            Link::new(
                ctx.clone(),
                vec![KeyValue::new("link.type", "batch_item")],
            )
        })
        .collect();
    
    // 创建批处理 Span，链接所有消息
    let mut span = tracer
        .span_builder("process_batch")
        .with_links(links)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("batch.size", messages.len() as i64));
    
    for msg in messages {
        process_message(msg).await?;
    }
    
    span.end();
    Ok(())
}
```

### 3.2 消息队列场景

**问题**: 生产者和消费者之间的异步关系

```rust
// 生产者端
async fn produce_message(content: String) -> Result<(), Error> {
    let tracer = global::tracer("producer");
    let mut span = tracer.start("produce_message");
    
    // 提取 SpanContext 用于传递
    let span_context = span.span_context().clone();
    
    let message = Message {
        content,
        trace_id: span_context.trace_id().to_string(),
        span_id: span_context.span_id().to_string(),
        trace_flags: span_context.trace_flags().to_u8(),
    };
    
    queue.send(message).await?;
    
    span.end();
    Ok(())
}

// 消费者端
async fn consume_message(message: Message) -> Result<(), Error> {
    let tracer = global::tracer("consumer");
    
    // 重建 SpanContext
    let span_context = SpanContext::new(
        TraceId::from_hex(&message.trace_id)?,
        SpanId::from_hex(&message.span_id)?,
        TraceFlags::new(message.trace_flags),
        false,
        TraceState::default(),
    );
    
    // 创建 Link
    let link = Link::new(
        span_context,
        vec![
            KeyValue::new("link.type", "follows_from"),
            KeyValue::new("messaging.system", "rabbitmq"),
        ],
    );
    
    // 创建消费者 Span
    let mut span = tracer
        .span_builder("consume_message")
        .with_links(vec![link])
        .start(&tracer);
    
    process_content(&message.content).await?;
    
    span.end();
    Ok(())
}
```

### 3.3 分布式追踪聚合

**问题**: 多个独立 Trace 合并为一个分析任务

```rust
async fn aggregate_traces(trace_ids: Vec<TraceId>) -> Result<(), Error> {
    let tracer = global::tracer("aggregator");
    
    // 为每个 Trace 创建 Link
    let links: Vec<Link> = trace_ids
        .into_iter()
        .map(|trace_id| {
            // 创建一个虚拟的 SpanContext 指向该 Trace
            let span_context = SpanContext::new(
                trace_id,
                SpanId::from_hex("0000000000000000").unwrap(), // 根 Span
                TraceFlags::SAMPLED,
                false,
                TraceState::default(),
            );
            
            Link::new(
                span_context,
                vec![KeyValue::new("link.type", "aggregated_trace")],
            )
        })
        .collect();
    
    let mut span = tracer
        .span_builder("aggregate_analysis")
        .with_links(links)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("traces.count", trace_ids.len() as i64));
    
    // 执行聚合分析
    perform_analysis().await?;
    
    span.end();
    Ok(())
}
```

### 3.4 扇入扇出（Fan-in/Fan-out）

**扇出 (Fan-out)**: 一个任务分发到多个子任务

```rust
async fn fan_out_task(job_id: Uuid) -> Result<(), Error> {
    let tracer = global::tracer("fan-out");
    let mut parent_span = tracer.start("fan_out");
    
    let parent_context = parent_span.span_context().clone();
    
    let tasks = vec!["task_1", "task_2", "task_3"];
    
    let handles: Vec<_> = tasks
        .into_iter()
        .map(|task_name| {
            let context = parent_context.clone();
            tokio::spawn(async move {
                let tracer = global::tracer("worker");
                
                // 子任务链接到父任务
                let link = Link::new(
                    context,
                    vec![KeyValue::new("link.type", "spawned_from")],
                );
                
                let mut span = tracer
                    .span_builder(task_name)
                    .with_links(vec![link])
                    .start(&tracer);
                
                // 执行子任务
                tokio::time::sleep(Duration::from_secs(1)).await;
                
                span.end();
            })
        })
        .collect();
    
    for handle in handles {
        handle.await?;
    }
    
    parent_span.end();
    Ok(())
}
```

**扇入 (Fan-in)**: 多个子任务结果合并

```rust
async fn fan_in_task(subtask_contexts: Vec<SpanContext>) -> Result<(), Error> {
    let tracer = global::tracer("fan-in");
    
    // 创建 Links 指向所有子任务
    let links: Vec<Link> = subtask_contexts
        .into_iter()
        .map(|ctx| {
            Link::new(
                ctx,
                vec![KeyValue::new("link.type", "aggregates")],
            )
        })
        .collect();
    
    let mut span = tracer
        .span_builder("fan_in_aggregate")
        .with_links(links)
        .start(&tracer);
    
    // 合并结果
    let result = aggregate_results().await?;
    
    span.set_attribute(KeyValue::new("result.count", result.len() as i64));
    span.end();
    
    Ok(())
}
```

---

## 4. Rust 实现

### 4.1 基本使用

```rust
use opentelemetry::{
    global,
    trace::{Link, Tracer, SpanContext, TraceContextExt},
    KeyValue,
};

fn create_span_with_link(linked_context: SpanContext) {
    let tracer = global::tracer("my-service");
    
    // 创建 Link
    let link = Link::new(
        linked_context,
        vec![
            KeyValue::new("link.type", "follows_from"),
            KeyValue::new("link.description", "Processing related task"),
        ],
    );
    
    // 创建 Span 并添加 Link
    let mut span = tracer
        .span_builder("linked_operation")
        .with_links(vec![link])
        .start(&tracer);
    
    // 业务逻辑
    do_work();
    
    span.end();
}
```

### 4.2 多个 Links

```rust
fn create_span_with_multiple_links(contexts: Vec<SpanContext>) {
    let tracer = global::tracer("my-service");
    
    let links: Vec<Link> = contexts
        .into_iter()
        .enumerate()
        .map(|(i, ctx)| {
            Link::new(
                ctx,
                vec![
                    KeyValue::new("link.index", i as i64),
                    KeyValue::new("link.type", "related_operation"),
                ],
            )
        })
        .collect();
    
    let mut span = tracer
        .span_builder("multi_linked_operation")
        .with_links(links)
        .start(&tracer);
    
    span.set_attribute(KeyValue::new("links.count", contexts.len() as i64));
    
    // 业务逻辑
    
    span.end();
}
```

### 4.3 条件链接

```rust
async fn conditional_linking(
    should_link: bool,
    optional_context: Option<SpanContext>,
) -> Result<(), Error> {
    let tracer = global::tracer("my-service");
    
    let mut builder = tracer.span_builder("conditional_operation");
    
    // 根据条件添加 Link
    if should_link {
        if let Some(ctx) = optional_context {
            let link = Link::new(
                ctx,
                vec![KeyValue::new("link.type", "conditional")],
            );
            builder = builder.with_links(vec![link]);
        }
    }
    
    let mut span = builder.start(&tracer);
    
    // 业务逻辑
    
    span.end();
    Ok(())
}
```

### 4.4 提取和注入 SpanContext

**HTTP 场景**：

```rust
use opentelemetry::propagation::TextMapPropagator;
use std::collections::HashMap;

// 服务 A：提取 SpanContext 并发送
async fn service_a_send_request() -> Result<(), Error> {
    let tracer = global::tracer("service-a");
    let mut span = tracer.start("send_request");
    
    let cx = Context::current_with_span(span);
    
    // 注入到 HTTP headers
    let mut injector = HashMap::new();
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut injector);
    });
    
    // 发送请求
    let response = reqwest::Client::new()
        .post("http://service-b/process")
        .headers(injector.into())
        .send()
        .await?;
    
    Ok(())
}

// 服务 B：提取 SpanContext 并创建 Link
async fn service_b_process(headers: HeaderMap) -> Result<(), Error> {
    let tracer = global::tracer("service-b");
    
    // 提取 SpanContext
    let mut extractor = HashMap::new();
    for (key, value) in headers.iter() {
        if let Ok(v) = value.to_str() {
            extractor.insert(key.as_str().to_string(), v.to_string());
        }
    }
    
    let parent_cx = global::get_text_map_propagator(|propagator| {
        propagator.extract(&extractor)
    });
    
    let parent_span_context = parent_cx.span().span_context().clone();
    
    // 创建 Link（而不是父子关系）
    let link = Link::new(
        parent_span_context,
        vec![KeyValue::new("link.type", "http_request")],
    );
    
    let mut span = tracer
        .span_builder("process_request")
        .with_links(vec![link])
        .start(&tracer);
    
    // 处理请求
    
    span.end();
    Ok(())
}
```

---

## 5. 高级用法

### 5.1 自定义 Link 类型

```rust
#[derive(Debug, Clone)]
pub enum LinkType {
    FollowsFrom,
    CausedBy,
    Aggregates,
    BatchItem,
    RetryOf,
    Custom(String),
}

impl LinkType {
    pub fn as_str(&self) -> &str {
        match self {
            LinkType::FollowsFrom => "follows_from",
            LinkType::CausedBy => "caused_by",
            LinkType::Aggregates => "aggregates",
            LinkType::BatchItem => "batch_item",
            LinkType::RetryOf => "retry_of",
            LinkType::Custom(s) => s.as_str(),
        }
    }
}

fn create_typed_link(context: SpanContext, link_type: LinkType) -> Link {
    Link::new(
        context,
        vec![KeyValue::new("link.type", link_type.as_str().to_string())],
    )
}
```

### 5.2 Link 工厂模式

```rust
pub struct LinkFactory;

impl LinkFactory {
    /// 创建批处理项链接
    pub fn batch_item(context: SpanContext, index: usize) -> Link {
        Link::new(
            context,
            vec![
                KeyValue::new("link.type", "batch_item"),
                KeyValue::new("batch.index", index as i64),
            ],
        )
    }
    
    /// 创建重试链接
    pub fn retry(context: SpanContext, attempt: u32) -> Link {
        Link::new(
            context,
            vec![
                KeyValue::new("link.type", "retry_of"),
                KeyValue::new("retry.attempt", attempt as i64),
            ],
        )
    }
    
    /// 创建聚合链接
    pub fn aggregate(context: SpanContext, source: &str) -> Link {
        Link::new(
            context,
            vec![
                KeyValue::new("link.type", "aggregates"),
                KeyValue::new("aggregate.source", source.to_string()),
            ],
        )
    }
    
    /// 创建因果链接
    pub fn causal(context: SpanContext, reason: &str) -> Link {
        Link::new(
            context,
            vec![
                KeyValue::new("link.type", "caused_by"),
                KeyValue::new("causal.reason", reason.to_string()),
            ],
        )
    }
}

// 使用
async fn use_link_factory() {
    let tracer = global::tracer("my-service");
    
    let links = vec![
        LinkFactory::batch_item(context1, 0),
        LinkFactory::retry(context2, 3),
        LinkFactory::aggregate(context3, "upstream"),
    ];
    
    let mut span = tracer
        .span_builder("operation")
        .with_links(links)
        .start(&tracer);
    
    // ...
}
```

### 5.3 动态 Link 管理

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

#[derive(Clone)]
pub struct DynamicLinkCollector {
    links: Arc<RwLock<Vec<Link>>>,
}

impl DynamicLinkCollector {
    pub fn new() -> Self {
        Self {
            links: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    pub async fn add_link(&self, link: Link) {
        self.links.write().await.push(link);
    }
    
    pub async fn get_links(&self) -> Vec<Link> {
        self.links.read().await.clone()
    }
    
    pub async fn clear(&self) {
        self.links.write().await.clear();
    }
}

// 使用
async fn dynamic_linking_example() -> Result<(), Error> {
    let collector = DynamicLinkCollector::new();
    
    // 在异步任务中收集 Links
    let collector_clone = collector.clone();
    tokio::spawn(async move {
        // 处理过程中动态添加 Links
        for i in 0..5 {
            let context = get_context_from_somewhere(i).await;
            let link = Link::new(
                context,
                vec![KeyValue::new("dynamic.index", i)],
            );
            collector_clone.add_link(link).await;
        }
    });
    
    // 等待收集完成
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 创建 Span with collected Links
    let tracer = global::tracer("my-service");
    let links = collector.get_links().await;
    
    let mut span = tracer
        .span_builder("dynamic_operation")
        .with_links(links)
        .start(&tracer);
    
    span.end();
    
    Ok(())
}
```

---

## 6. 最佳实践

### 6.1 何时使用 Links

**✅ 应该使用 Links**:

1. **异步处理**: 消息队列、事件驱动
2. **批处理**: 多个输入合并处理
3. **重试**: 关联重试的原始请求
4. **聚合**: 多个独立任务的结果合并
5. **松耦合关系**: 不需要同步等待的依赖

**❌ 不应该使用 Links**:

1. **同步调用**: 使用父子关系
2. **强依赖**: 必须等待完成的操作
3. **简单的函数调用**: 使用普通的 Span 嵌套

### 6.2 Link 属性命名规范

```rust
// ✅ 好的实践
Link::new(
    context,
    vec![
        KeyValue::new("link.type", "follows_from"),           // 标准化
        KeyValue::new("messaging.system", "kafka"),           // 遵循 OTel 规范
        KeyValue::new("messaging.destination", "orders"),     // 遵循 OTel 规范
        KeyValue::new("link.source_service", "payment-svc"),  // 清晰命名
    ],
);

// ❌ 不好的实践
Link::new(
    context,
    vec![
        KeyValue::new("type", "link"),                        // 太泛化
        KeyValue::new("sys", "k"),                            // 缩写不清晰
        KeyValue::new("from", "svc1"),                        // 不明确
    ],
);
```

### 6.3 限制 Links 数量

```rust
const MAX_LINKS: usize = 128;

fn create_span_with_bounded_links(mut links: Vec<Link>) -> Result<(), Error> {
    let tracer = global::tracer("my-service");
    
    // 限制 Links 数量
    if links.len() > MAX_LINKS {
        tracing::warn!(
            "Too many links: {}, truncating to {}",
            links.len(),
            MAX_LINKS
        );
        links.truncate(MAX_LINKS);
        
        // 记录被截断的信息
        links.last_mut().unwrap().attributes.push(
            KeyValue::new("links.truncated", true)
        );
        links.last_mut().unwrap().attributes.push(
            KeyValue::new("links.original_count", links.len() as i64)
        );
    }
    
    let mut span = tracer
        .span_builder("operation")
        .with_links(links)
        .start(&tracer);
    
    span.end();
    Ok(())
}
```

### 6.4 Links 去重

```rust
use std::collections::HashSet;

fn deduplicate_links(links: Vec<Link>) -> Vec<Link> {
    let mut seen = HashSet::new();
    links
        .into_iter()
        .filter(|link| {
            let key = (
                link.span_context().trace_id(),
                link.span_context().span_id(),
            );
            seen.insert(key)
        })
        .collect()
}
```

---

## 7. 性能优化

### 7.1 延迟链接

```rust
pub struct LazyLinkBuilder {
    context_provider: Box<dyn Fn() -> Vec<SpanContext> + Send + Sync>,
}

impl LazyLinkBuilder {
    pub fn new<F>(provider: F) -> Self
    where
        F: Fn() -> Vec<SpanContext> + Send + Sync + 'static,
    {
        Self {
            context_provider: Box::new(provider),
        }
    }
    
    pub fn build_links(&self) -> Vec<Link> {
        (self.context_provider)()
            .into_iter()
            .map(|ctx| {
                Link::new(
                    ctx,
                    vec![KeyValue::new("link.type", "lazy")],
                )
            })
            .collect()
    }
}

// 使用
fn lazy_linking_example() {
    let builder = LazyLinkBuilder::new(|| {
        // 只在需要时才获取 contexts
        expensive_context_lookup()
    });
    
    // 只在创建 Span 时才构建 Links
    let links = builder.build_links();
}
```

### 7.2 链接缓存

```rust
use std::sync::Arc;
use lru::LruCache;
use tokio::sync::Mutex;

pub struct LinkCache {
    cache: Arc<Mutex<LruCache<String, Link>>>,
}

impl LinkCache {
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: Arc::new(Mutex::new(LruCache::new(capacity))),
        }
    }
    
    pub async fn get_or_create<F>(
        &self,
        key: &str,
        creator: F,
    ) -> Link
    where
        F: FnOnce() -> Link,
    {
        let mut cache = self.cache.lock().await;
        
        if let Some(link) = cache.get(key) {
            return link.clone();
        }
        
        let link = creator();
        cache.put(key.to_string(), link.clone());
        link
    }
}
```

---

## 8. 实战案例

### 8.1 电商订单处理

```rust
// 订单服务
async fn create_order(user_id: Uuid, items: Vec<Item>) -> Result<Order, Error> {
    let tracer = global::tracer("order-service");
    let mut span = tracer.start("create_order");
    
    span.set_attribute(KeyValue::new("user.id", user_id.to_string()));
    
    let order = Order::new(user_id, items);
    db.save_order(&order).await?;
    
    // 提取 SpanContext 用于后续链接
    let order_context = span.span_context().clone();
    
    // 发送订单创建事件
    publish_order_created_event(order.id, order_context).await?;
    
    span.end();
    Ok(order)
}

// 支付服务（异步处理）
async fn process_payment(order_id: Uuid, order_context: SpanContext) -> Result<(), Error> {
    let tracer = global::tracer("payment-service");
    
    // 链接到订单创建 Span
    let link = Link::new(
        order_context,
        vec![
            KeyValue::new("link.type", "follows_from"),
            KeyValue::new("order.id", order_id.to_string()),
        ],
    );
    
    let mut span = tracer
        .span_builder("process_payment")
        .with_links(vec![link])
        .start(&tracer);
    
    // 处理支付
    let payment = charge_customer(order_id).await?;
    
    span.set_attribute(KeyValue::new("payment.amount", payment.amount));
    span.set_attribute(KeyValue::new("payment.status", payment.status.as_str()));
    
    span.end();
    Ok(())
}

// 发货服务（异步处理）
async fn ship_order(
    order_id: Uuid,
    order_context: SpanContext,
    payment_context: SpanContext,
) -> Result<(), Error> {
    let tracer = global::tracer("shipping-service");
    
    // 链接到订单和支付
    let links = vec![
        Link::new(
            order_context,
            vec![
                KeyValue::new("link.type", "follows_from"),
                KeyValue::new("link.source", "order_service"),
            ],
        ),
        Link::new(
            payment_context,
            vec![
                KeyValue::new("link.type", "follows_from"),
                KeyValue::new("link.source", "payment_service"),
            ],
        ),
    ];
    
    let mut span = tracer
        .span_builder("ship_order")
        .with_links(links)
        .start(&tracer);
    
    // 创建发货单
    let shipment = create_shipment(order_id).await?;
    
    span.set_attribute(KeyValue::new("shipment.tracking_number", shipment.tracking));
    
    span.end();
    Ok(())
}
```

### 8.2 数据ETL管道

```rust
// 数据提取
async fn extract_data(sources: Vec<DataSource>) -> Result<Vec<SpanContext>, Error> {
    let tracer = global::tracer("etl-extract");
    let mut contexts = Vec::new();
    
    for source in sources {
        let mut span = tracer.start(format!("extract_{}", source.name));
        
        let data = source.fetch().await?;
        
        span.set_attribute(KeyValue::new("rows.count", data.len() as i64));
        
        contexts.push(span.span_context().clone());
        span.end();
    }
    
    Ok(contexts)
}

// 数据转换（链接到所有提取操作）
async fn transform_data(
    data: Vec<Data>,
    extract_contexts: Vec<SpanContext>,
) -> Result<SpanContext, Error> {
    let tracer = global::tracer("etl-transform");
    
    let links: Vec<Link> = extract_contexts
        .into_iter()
        .map(|ctx| {
            Link::new(
                ctx,
                vec![
                    KeyValue::new("link.type", "aggregates"),
                    KeyValue::new("pipeline.stage", "extract"),
                ],
            )
        })
        .collect();
    
    let mut span = tracer
        .span_builder("transform_data")
        .with_links(links)
        .start(&tracer);
    
    let transformed = apply_transformations(data).await?;
    
    span.set_attribute(KeyValue::new("transformed.count", transformed.len() as i64));
    
    let context = span.span_context().clone();
    span.end();
    
    Ok(context)
}

// 数据加载（链接到转换操作）
async fn load_data(
    data: Vec<Data>,
    transform_context: SpanContext,
) -> Result<(), Error> {
    let tracer = global::tracer("etl-load");
    
    let link = Link::new(
        transform_context,
        vec![
            KeyValue::new("link.type", "follows_from"),
            KeyValue::new("pipeline.stage", "transform"),
        ],
    );
    
    let mut span = tracer
        .span_builder("load_data")
        .with_links(vec![link])
        .start(&tracer);
    
    database.bulk_insert(data).await?;
    
    span.set_attribute(KeyValue::new("loaded.count", data.len() as i64));
    
    span.end();
    Ok(())
}
```

---

## 🔗 参考资源

- [OpenTelemetry Specification - SpanLinks](https://opentelemetry.io/docs/specs/otel/trace/api/#link)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry/)
- [Rust OTLP 快速入门](../../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)
- [SpanContext 完整版](./02_SpanContext_Rust完整版.md)
- [SpanKind 完整版](./03_SpanKind_Rust完整版.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../../README.md) | [📚 数据模型](../README.md) | [🔍 SpanContext](./02_SpanContext_Rust完整版.md)

