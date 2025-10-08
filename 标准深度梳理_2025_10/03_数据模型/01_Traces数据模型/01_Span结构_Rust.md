# Span 结构 - Rust 类型安全实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Span 结构 - Rust 类型安全实现](#span-结构---rust-类型安全实现)
  - [目录](#目录)
  - [1. Span 类型安全定义](#1-span-类型安全定义)
    - [1.1 基础 Span 类型](#11-基础-span-类型)
  - [2. Rust 所有权模式](#2-rust-所有权模式)
    - [2.1 Span 构建器模式](#21-span-构建器模式)
    - [2.2 Span 借用和共享](#22-span-借用和共享)
  - [3. Span 生命周期管理](#3-span-生命周期管理)
    - [3.1 RAII 模式](#31-raii-模式)
    - [3.2 异步生命周期](#32-异步生命周期)
  - [4. 零成本抽象](#4-零成本抽象)
    - [4.1 编译时 Span 类型](#41-编译时-span-类型)
    - [4.2 零开销属性系统](#42-零开销属性系统)
  - [5. 异步 Span 操作](#5-异步-span-操作)
    - [5.1 异步 Span 导出](#51-异步-span-导出)
    - [5.2 异步上下文传播](#52-异步上下文传播)
  - [6. 实战示例](#6-实战示例)
    - [6.1 HTTP 请求追踪](#61-http-请求追踪)
    - [6.2 数据库查询追踪](#62-数据库查询追踪)
  - [7. 性能优化](#7-性能优化)
    - [7.1 属性预分配](#71-属性预分配)
    - [7.2 零拷贝属性](#72-零拷贝属性)
  - [8. 最佳实践](#8-最佳实践)

---

## 1. Span 类型安全定义

### 1.1 基础 Span 类型

```rust
use opentelemetry::{
    trace::{Span, SpanContext, SpanId, SpanKind, Status, StatusCode, TraceFlags, TraceId, TraceState},
    KeyValue,
};
use std::time::SystemTime;

/// Span 的完整类型定义 (编译时类型安全)
pub struct TypeSafeSpan {
    /// Span 上下文 - 包含 TraceID 和 SpanID
    context: SpanContext,
    
    /// Span 名称 - 不可变引用确保线程安全
    name: String,
    
    /// Span 类型
    kind: SpanKind,
    
    /// 开始时间
    start_time: SystemTime,
    
    /// 结束时间 (Option 表示可能未结束)
    end_time: Option<SystemTime>,
    
    /// 状态
    status: Status,
    
    /// 属性 - 使用 Vec 确保可变性和所有权
    attributes: Vec<KeyValue>,
    
    /// 事件
    events: Vec<SpanEvent>,
    
    /// 链接
    links: Vec<SpanLink>,
}

/// Span 事件 - 值类型，无引用
#[derive(Debug, Clone)]
pub struct SpanEvent {
    pub name: String,
    pub timestamp: SystemTime,
    pub attributes: Vec<KeyValue>,
}

/// Span 链接 - 值类型，无引用
#[derive(Debug, Clone)]
pub struct SpanLink {
    pub span_context: SpanContext,
    pub attributes: Vec<KeyValue>,
}

impl TypeSafeSpan {
    /// 创建新 Span - 获取所有权
    pub fn new(name: impl Into<String>, kind: SpanKind) -> Self {
        Self {
            context: Self::generate_context(),
            name: name.into(),
            kind,
            start_time: SystemTime::now(),
            end_time: None,
            status: Status::Unset,
            attributes: Vec::new(),
            events: Vec::new(),
            links: Vec::new(),
        }
    }
    
    /// 生成 SpanContext
    fn generate_context() -> SpanContext {
        SpanContext::new(
            TraceId::from_u128(rand::random()),
            SpanId::from_u64(rand::random()),
            TraceFlags::SAMPLED,
            false,
            TraceState::default(),
        )
    }
    
    /// 添加属性 - 消费所有权
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
    
    /// 添加事件 - 借用自身
    pub fn add_event(&mut self, name: impl Into<String>, attributes: Vec<KeyValue>) {
        self.events.push(SpanEvent {
            name: name.into(),
            timestamp: SystemTime::now(),
            attributes,
        });
    }
    
    /// 设置状态 - 可变借用
    pub fn set_status(&mut self, status: Status) {
        self.status = status;
    }
    
    /// 结束 Span - 消费所有权
    pub fn end(mut self) -> FinishedSpan {
        self.end_time = Some(SystemTime::now());
        
        FinishedSpan {
            context: self.context,
            name: self.name,
            kind: self.kind,
            start_time: self.start_time,
            end_time: self.end_time.unwrap(),
            status: self.status,
            attributes: self.attributes,
            events: self.events,
            links: self.links,
        }
    }
}

/// 已完成的 Span - 不可变
#[derive(Debug, Clone)]
pub struct FinishedSpan {
    pub context: SpanContext,
    pub name: String,
    pub kind: SpanKind,
    pub start_time: SystemTime,
    pub end_time: SystemTime,
    pub status: Status,
    pub attributes: Vec<KeyValue>,
    pub events: Vec<SpanEvent>,
    pub links: Vec<SpanLink>,
}

impl FinishedSpan {
    /// 计算持续时间 - 不可变借用
    pub fn duration(&self) -> std::time::Duration {
        self.end_time.duration_since(self.start_time).unwrap_or_default()
    }
    
    /// 转换为 OTLP 格式 - 消费所有权
    pub fn into_otlp(self) -> opentelemetry_proto::tonic::trace::v1::Span {
        // 转换逻辑...
        todo!()
    }
}
```

---

## 2. Rust 所有权模式

### 2.1 Span 构建器模式

```rust
/// Span 构建器 - 流式 API，链式调用
pub struct SpanBuilder {
    name: String,
    kind: SpanKind,
    attributes: Vec<KeyValue>,
    links: Vec<SpanLink>,
    parent_context: Option<SpanContext>,
}

impl SpanBuilder {
    /// 创建新构建器 - 获取名称所有权
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: SpanKind::Internal,
            attributes: Vec::new(),
            links: Vec::new(),
            parent_context: None,
        }
    }
    
    /// 设置类型 - 消费并返回 self
    pub fn with_kind(mut self, kind: SpanKind) -> Self {
        self.kind = kind;
        self
    }
    
    /// 添加属性 - 消费并返回 self
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) -> Self {
        self.attributes.push(KeyValue::new(key.into(), value.into()));
        self
    }
    
    /// 批量添加属性 - 转移所有权
    pub fn with_attributes(mut self, attrs: Vec<KeyValue>) -> Self {
        self.attributes.extend(attrs);
        self
    }
    
    /// 设置父 Span
    pub fn with_parent(mut self, parent: SpanContext) -> Self {
        self.parent_context = Some(parent);
        self
    }
    
    /// 构建 Span - 消费构建器
    pub fn start(self) -> TypeSafeSpan {
        let mut span = TypeSafeSpan::new(self.name, self.kind);
        span.attributes = self.attributes;
        span.links = self.links;
        span
    }
}

/// 使用示例 - 展示所有权转移
fn example_builder_pattern() {
    let span = SpanBuilder::new("database_query")
        .with_kind(SpanKind::Client)
        .with_attribute("db.system", "postgresql")
        .with_attribute("db.name", "users")
        .start();  // 消费构建器，获得 Span 所有权
    
    // span 现在拥有所有数据
}
```

### 2.2 Span 借用和共享

```rust
use std::sync::Arc;
use parking_lot::RwLock;

/// 共享 Span - 使用 Arc 实现多线程共享
pub struct SharedSpan {
    inner: Arc<RwLock<TypeSafeSpan>>,
}

impl SharedSpan {
    pub fn new(span: TypeSafeSpan) -> Self {
        Self {
            inner: Arc::new(RwLock::new(span)),
        }
    }
    
    /// 添加属性 - 写锁
    pub fn add_attribute(&self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) {
        let mut span = self.inner.write();
        span.attributes.push(KeyValue::new(key.into(), value.into()));
    }
    
    /// 读取属性 - 读锁
    pub fn get_name(&self) -> String {
        let span = self.inner.read();
        span.name.clone()
    }
    
    /// 克隆共享引用 - 廉价操作
    pub fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl Clone for SharedSpan {
    fn clone(&self) -> Self {
        Self::clone(self)
    }
}
```

---

## 3. Span 生命周期管理

### 3.1 RAII 模式

```rust
/// RAII Span - 自动结束
pub struct ScopedSpan {
    span: Option<TypeSafeSpan>,
}

impl ScopedSpan {
    pub fn new(span: TypeSafeSpan) -> Self {
        Self { span: Some(span) }
    }
    
    /// 获取可变引用
    pub fn span_mut(&mut self) -> &mut TypeSafeSpan {
        self.span.as_mut().expect("Span already ended")
    }
}

impl Drop for ScopedSpan {
    fn drop(&mut self) {
        if let Some(span) = self.span.take() {
            let finished = span.end();
            // 自动导出 finished span
            tracing::info!("Span ended: {} ({:?})", finished.name, finished.duration());
        }
    }
}

/// 使用示例 - 自动清理
fn example_raii() {
    {
        let mut scoped = ScopedSpan::new(
            SpanBuilder::new("database_operation").start()
        );
        
        scoped.span_mut().add_event("query_start", vec![]);
        
        // 执行操作...
        
    } // scoped 离开作用域，自动调用 Drop，结束 Span
    
    // Span 已自动结束和导出
}
```

### 3.2 异步生命周期

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context as TaskContext, Poll};

/// 异步 Span 包装器
pub struct AsyncSpan<F> {
    span: Option<TypeSafeSpan>,
    fut: F,
}

impl<F> AsyncSpan<F> {
    pub fn new(span: TypeSafeSpan, fut: F) -> Self {
        Self {
            span: Some(span),
            fut,
        }
    }
}

impl<F> Future for AsyncSpan<F>
where
    F: Future,
{
    type Output = F::Output;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        // 安全地获取 Future 的可变引用
        let fut = unsafe { self.as_mut().map_unchecked_mut(|s| &mut s.fut) };
        
        let result = fut.poll(cx);
        
        if result.is_ready() {
            // Future 完成，结束 Span
            if let Some(span) = self.span.take() {
                let finished = span.end();
                tracing::info!("Async span ended: {}", finished.name);
            }
        }
        
        result
    }
}

/// 使用示例
async fn example_async_span() {
    let span = SpanBuilder::new("async_operation").start();
    
    let result = AsyncSpan::new(span, async {
        // 异步操作
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        "result"
    }).await;
    
    // Span 自动结束
}
```

---

## 4. 零成本抽象

### 4.1 编译时 Span 类型

```rust
use std::marker::PhantomData;

/// Span 状态类型标记
pub struct Active;
pub struct Ended;

/// 带状态的 Span - 编译时保证正确性
pub struct StatefulSpan<S> {
    inner: TypeSafeSpan,
    _marker: PhantomData<S>,
}

impl StatefulSpan<Active> {
    /// 创建活跃 Span
    pub fn new(span: TypeSafeSpan) -> Self {
        Self {
            inner: span,
            _marker: PhantomData,
        }
    }
    
    /// 添加事件 - 只能在活跃状态调用
    pub fn add_event(&mut self, name: impl Into<String>, attributes: Vec<KeyValue>) {
        self.inner.add_event(name, attributes);
    }
    
    /// 结束 Span - 状态转换
    pub fn end(self) -> StatefulSpan<Ended> {
        let finished = self.inner.end();
        StatefulSpan {
            inner: TypeSafeSpan {
                context: finished.context,
                name: finished.name,
                kind: finished.kind,
                start_time: finished.start_time,
                end_time: Some(finished.end_time),
                status: finished.status,
                attributes: finished.attributes,
                events: finished.events,
                links: finished.links,
            },
            _marker: PhantomData,
        }
    }
}

impl StatefulSpan<Ended> {
    /// 获取持续时间 - 只能在结束状态调用
    pub fn duration(&self) -> std::time::Duration {
        self.inner.end_time.unwrap()
            .duration_since(self.inner.start_time)
            .unwrap_or_default()
    }
}

/// 编译时错误示例
fn compile_time_safety() {
    let active_span = StatefulSpan::<Active>::new(
        SpanBuilder::new("test").start()
    );
    
    let ended_span = active_span.end();
    
    // 编译错误：ended_span 没有 add_event 方法
    // ended_span.add_event("test", vec![]);
    
    // 正确：只能获取持续时间
    let _ = ended_span.duration();
}
```

### 4.2 零开销属性系统

```rust
use opentelemetry::Value;

/// 强类型属性 - 编译时类型检查
pub trait SpanAttribute {
    fn key(&self) -> &'static str;
    fn value(&self) -> Value;
}

/// 预定义属性类型
pub struct HttpMethod(&'static str);
pub struct HttpStatusCode(u16);
pub struct DatabaseSystem(&'static str);

impl SpanAttribute for HttpMethod {
    fn key(&self) -> &'static str {
        "http.method"
    }
    
    fn value(&self) -> Value {
        Value::String(self.0.into())
    }
}

impl SpanAttribute for HttpStatusCode {
    fn key(&self) -> &'static str {
        "http.status_code"
    }
    
    fn value(&self) -> Value {
        Value::I64(self.0 as i64)
    }
}

/// 类型安全的属性添加
impl TypeSafeSpan {
    pub fn add_typed_attribute<A: SpanAttribute>(&mut self, attr: A) {
        self.attributes.push(KeyValue::new(attr.key(), attr.value()));
    }
}

/// 使用示例 - 编译时类型安全
fn example_typed_attributes() {
    let mut span = SpanBuilder::new("http_request").start();
    
    // 类型安全
    span.add_typed_attribute(HttpMethod("GET"));
    span.add_typed_attribute(HttpStatusCode(200));
    
    // 编译错误：类型不匹配
    // span.add_typed_attribute(HttpMethod(123));
}
```

---

## 5. 异步 Span 操作

### 5.1 异步 Span 导出

```rust
use tokio::sync::mpsc;

/// 异步 Span 导出器
pub struct AsyncSpanExporter {
    sender: mpsc::Sender<FinishedSpan>,
}

impl AsyncSpanExporter {
    pub fn new(buffer_size: usize) -> (Self, mpsc::Receiver<FinishedSpan>) {
        let (tx, rx) = mpsc::channel(buffer_size);
        (Self { sender: tx }, rx)
    }
    
    /// 异步导出 Span - 非阻塞
    pub async fn export(&self, span: FinishedSpan) -> Result<(), String> {
        self.sender
            .send(span)
            .await
            .map_err(|e| format!("Failed to send span: {}", e))
    }
    
    /// 同步导出 (非阻塞尝试)
    pub fn try_export(&self, span: FinishedSpan) -> Result<(), String> {
        self.sender
            .try_send(span)
            .map_err(|e| format!("Failed to send span: {}", e))
    }
}

/// 后台导出任务
pub async fn run_exporter_task(mut receiver: mpsc::Receiver<FinishedSpan>) {
    while let Some(span) = receiver.recv().await {
        // 实际导出逻辑
        tracing::info!("Exporting span: {} ({:?})", span.name, span.duration());
        
        // 发送到 OTLP 后端...
    }
}

/// 使用示例
#[tokio::main]
async fn example_async_exporter() {
    let (exporter, receiver) = AsyncSpanExporter::new(1000);
    
    // 启动后台导出任务
    tokio::spawn(run_exporter_task(receiver));
    
    // 创建和导出 Span
    let span = SpanBuilder::new("example").start();
    let finished = span.end();
    
    exporter.export(finished).await.unwrap();
}
```

### 5.2 异步上下文传播

```rust
use tokio::task::JoinHandle;

/// 异步任务 Span 包装
pub async fn spawn_traced<F, T>(
    span: TypeSafeSpan,
    future: F,
) -> JoinHandle<T>
where
    F: Future<Output = T> + Send + 'static,
    T: Send + 'static,
{
    tokio::spawn(async move {
        let scoped_span = ScopedSpan::new(span);
        
        // 执行异步任务
        let result = future.await;
        
        // Span 自动结束
        drop(scoped_span);
        
        result
    })
}

/// 使用示例
async fn example_spawn_traced() {
    let span = SpanBuilder::new("background_task")
        .with_kind(SpanKind::Internal)
        .start();
    
    let handle = spawn_traced(span, async {
        // 后台任务
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        "result"
    }).await;
    
    let result = handle.await.unwrap();
}
```

---

## 6. 实战示例

### 6.1 HTTP 请求追踪

```rust
use reqwest::Client;

/// HTTP 请求 Span
pub async fn traced_http_request(
    client: &Client,
    url: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    // 创建 Span
    let mut span = SpanBuilder::new("http_request")
        .with_kind(SpanKind::Client)
        .with_attribute("http.method", "GET")
        .with_attribute("http.url", url)
        .start();
    
    // 记录开始事件
    span.add_event("request_start", vec![]);
    
    // 执行请求
    let start = std::time::Instant::now();
    let result = client.get(url).send().await;
    let duration = start.elapsed();
    
    match result {
        Ok(response) => {
            let status = response.status().as_u16();
            
            // 记录成功
            span.add_typed_attribute(HttpStatusCode(status));
            span.set_status(Status::Ok);
            span.add_event("response_received", vec![
                KeyValue::new("http.status_code", status as i64),
                KeyValue::new("duration_ms", duration.as_millis() as i64),
            ]);
            
            let body = response.text().await?;
            
            // 结束 Span
            let _ = span.end();
            
            Ok(body)
        }
        Err(e) => {
            // 记录错误
            span.set_status(Status::error(e.to_string()));
            span.add_event("request_error", vec![
                KeyValue::new("error.message", e.to_string()),
            ]);
            
            // 结束 Span
            let _ = span.end();
            
            Err(Box::new(e))
        }
    }
}
```

### 6.2 数据库查询追踪

```rust
use sqlx::{PgPool, Row};

/// 数据库查询 Span
pub async fn traced_db_query(
    pool: &PgPool,
    query: &str,
) -> Result<Vec<String>, sqlx::Error> {
    let mut span = SpanBuilder::new("db_query")
        .with_kind(SpanKind::Client)
        .with_attribute("db.system", "postgresql")
        .with_attribute("db.statement", query)
        .start();
    
    span.add_event("query_start", vec![]);
    
    let start = std::time::Instant::now();
    let result = sqlx::query(query)
        .fetch_all(pool)
        .await;
    let duration = start.elapsed();
    
    match result {
        Ok(rows) => {
            span.set_status(Status::Ok);
            span.add_event("query_complete", vec![
                KeyValue::new("db.row_count", rows.len() as i64),
                KeyValue::new("duration_ms", duration.as_millis() as i64),
            ]);
            
            let results = rows.iter()
                .map(|row| row.get(0))
                .collect();
            
            let _ = span.end();
            
            Ok(results)
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.add_event("query_error", vec![
                KeyValue::new("error.message", e.to_string()),
            ]);
            
            let _ = span.end();
            
            Err(e)
        }
    }
}
```

---

## 7. 性能优化

### 7.1 属性预分配

```rust
/// 优化的 Span 构建器
pub struct OptimizedSpanBuilder {
    name: String,
    kind: SpanKind,
    attributes: Vec<KeyValue>,
}

impl OptimizedSpanBuilder {
    /// 预分配属性容量
    pub fn with_capacity(name: impl Into<String>, capacity: usize) -> Self {
        Self {
            name: name.into(),
            kind: SpanKind::Internal,
            attributes: Vec::with_capacity(capacity),
        }
    }
}
```

### 7.2 零拷贝属性

```rust
use std::borrow::Cow;

/// 零拷贝字符串属性
pub fn add_str_attribute<'a>(
    span: &mut TypeSafeSpan,
    key: &'static str,
    value: impl Into<Cow<'a, str>>,
) {
    let value_cow: Cow<'a, str> = value.into();
    span.attributes.push(KeyValue::new(
        key,
        value_cow.into_owned(),
    ));
}
```

---

## 8. 最佳实践

```rust
/// 生产级 Span 管理器
pub struct SpanManager {
    exporter: AsyncSpanExporter,
    max_attributes: usize,
    max_events: usize,
}

impl SpanManager {
    pub fn new(exporter: AsyncSpanExporter) -> Self {
        Self {
            exporter,
            max_attributes: 128,
            max_events: 128,
        }
    }
    
    /// 创建受限 Span
    pub fn create_span(&self, name: impl Into<String>) -> LimitedSpan {
        LimitedSpan {
            span: SpanBuilder::new(name).start(),
            max_attributes: self.max_attributes,
            max_events: self.max_events,
        }
    }
}

/// 受限 Span - 防止内存泄漏
pub struct LimitedSpan {
    span: TypeSafeSpan,
    max_attributes: usize,
    max_events: usize,
}

impl LimitedSpan {
    pub fn add_attribute(&mut self, key: impl Into<String>, value: impl Into<opentelemetry::Value>) {
        if self.span.attributes.len() < self.max_attributes {
            self.span.attributes.push(KeyValue::new(key.into(), value.into()));
        } else {
            tracing::warn!("Max attributes reached, dropping attribute");
        }
    }
    
    pub fn add_event(&mut self, name: impl Into<String>, attributes: Vec<KeyValue>) {
        if self.span.events.len() < self.max_events {
            self.span.add_event(name, attributes);
        } else {
            tracing::warn!("Max events reached, dropping event");
        }
    }
}
```

**Rust 特定最佳实践**:

```text
✅ 利用所有权系统防止数据竞争
✅ 使用 RAII 模式自动清理
✅ 编译时类型安全
✅ 零成本抽象
✅ 避免不必要的克隆
✅ 使用 Cow 优化字符串
✅ 预分配容量
✅ 限制资源使用
✅ 异步优先设计
✅ 类型状态模式
```

---

**最后更新**: 2025年10月8日  
**维护者**: OTLP Rust团队  
**许可证**: MIT OR Apache-2.0
