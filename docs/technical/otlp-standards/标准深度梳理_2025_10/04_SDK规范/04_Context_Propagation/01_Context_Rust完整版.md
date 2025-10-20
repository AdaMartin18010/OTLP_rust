# Context - Rust 完整实现指南

## 📋 目录

- [Context - Rust 完整实现指南](#context---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Context 的职责](#context-的职责)
    - [1. **进程内传播**](#1-进程内传播)
    - [2. **跨服务传播**](#2-跨服务传播)
    - [3. **存储机制**](#3-存储机制)
  - [Rust 实现](#rust-实现)
    - [基础用法](#基础用法)
      - [**创建和访问 Context**](#创建和访问-context)
      - [**Context 的不可变性**](#context-的不可变性)
    - [Context 传播](#context-传播)
      - [**显式传递**](#显式传递)
      - [**隐式传递（Task-local）**](#隐式传递task-local)
    - [异步任务](#异步任务)
      - [**tokio 任务间传播**](#tokio-任务间传播)
      - [**多任务并发**](#多任务并发)
    - [线程间传递](#线程间传递)
      - [**跨线程传播**](#跨线程传播)
      - [**Rayon 并行计算**](#rayon-并行计算)
  - [与 tracing 集成](#与-tracing-集成)
    - [**手动管理 Span Guard**](#手动管理-span-guard)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**tracing 集成**](#tracing-集成)
    - [**并行计算**](#并行计算)
  - [总结](#总结)

---

## 核心概念

**Context** 是 OpenTelemetry 的核心抽象，用于在分布式系统中传播上下文信息：

```text
┌────────────────────────────────────────────────┐
│              Context                           │
│  ┌──────────────────────────────────────────┐  │
│  │ Trace Context: trace_id, span_id         │  │
│  │ Baggage: key-value pairs                 │  │
│  │ Custom Data: 自定义键值对                 │  │
│  └──────────────────────────────────────────┘  │
│                                                │
│  进程内传播  ──→  跨服务传播                     │
│  (线程/异步)     (HTTP Header/gRPC Metadata)    │
└────────────────────────────────────────────────┘
```

**关键特性**：

- **不可变**：Context 是不可变的，修改会创建新实例
- **类型安全**：使用 `ContextKey` 区分不同类型的数据
- **线程安全**：可安全地在多线程间传递

---

## Context 的职责

### 1. **进程内传播**

- 在函数调用链中传递 Trace/Baggage
- 在异步任务间传递上下文
- 在线程间传递上下文

### 2. **跨服务传播**

- 通过 HTTP Header 传播（W3C TraceContext）
- 通过 gRPC Metadata 传播
- 通过消息队列传播（Kafka、RabbitMQ）

### 3. **存储机制**

- **Task-local storage**：tokio 异步任务
- **Thread-local storage**：多线程环境
- **显式传递**：函数参数

---

## Rust 实现

### 基础用法

#### **创建和访问 Context**

```rust
use opentelemetry::{Context, KeyValue};
use opentelemetry::trace::{TraceContextExt, Tracer, TracerProvider};

#[tokio::main]
async fn main() {
    // 1. 获取当前 Context
    let current_ctx = Context::current();
    
    // 2. 创建新 Span 并关联到 Context
    let tracer = global::tracer("my-service");
    let span = tracer.start("my-operation");
    let cx = Context::current_with_span(span);
    
    // 3. 从 Context 中提取 Span
    let span = cx.span();
    span.set_attribute(KeyValue::new("user_id", 123));
    
    // 4. 使用 Context 执行操作
    process_request(cx).await;
}

async fn process_request(cx: Context) {
    // Context 作为参数显式传递
    let span = cx.span();
    span.add_event("Processing started", vec![]);
}
```

---

#### **Context 的不可变性**

```rust
// Context 是不可变的
let cx1 = Context::new();

// 添加数据会创建新 Context
let span = tracer.start("operation");
let cx2 = cx1.with_span(span);

// cx1 仍然是空的，cx2 包含 Span
assert!(cx1.span().span_context().is_valid() == false);
assert!(cx2.span().span_context().is_valid() == true);
```

---

### Context 传播

#### **显式传递**

```rust
async fn handle_request(cx: Context) {
    // 显式传递到子函数
    fetch_data(cx.clone()).await;
    process_data(cx.clone()).await;
}

async fn fetch_data(cx: Context) {
    let span = cx.span();
    span.add_event("Fetching data", vec![]);
    // 业务逻辑...
}

async fn process_data(cx: Context) {
    let span = cx.span();
    span.add_event("Processing data", vec![]);
    // 业务逻辑...
}
```

---

#### **隐式传递（Task-local）**

```rust
use opentelemetry::Context;

async fn handle_request() {
    // 设置当前 Context
    let tracer = global::tracer("service");
    let span = tracer.start("request");
    let cx = Context::current_with_span(span);
    
    // 在 Context 作用域内执行
    cx.attach(|| async {
        // 子函数自动使用当前 Context
        fetch_data().await;
        process_data().await;
    }).await;
}

async fn fetch_data() {
    // 自动获取当前 Context
    let cx = Context::current();
    let span = cx.span();
    span.add_event("Fetching", vec![]);
}
```

---

### 异步任务

#### **tokio 任务间传播**

```rust
use tokio::task;

async fn spawn_with_context() {
    let tracer = global::tracer("service");
    let span = tracer.start("parent-task");
    let cx = Context::current_with_span(span);
    
    // 方式 1: 显式传递 Context
    let cx_clone = cx.clone();
    task::spawn(async move {
        let span = cx_clone.span();
        span.add_event("Child task started", vec![]);
        // 子任务逻辑...
    });
    
    // 方式 2: 使用 instrument 宏（推荐）
    tokio::spawn(async_task().instrument(cx.span().clone()));
}

#[tracing::instrument]
async fn async_task() {
    // tracing 自动管理 Context
    tracing::info!("Task executing");
}
```

---

#### **多任务并发**

```rust
use futures::future::join_all;

async fn parallel_operations(cx: Context) {
    let tracer = global::tracer("service");
    
    let tasks: Vec<_> = (0..10)
        .map(|i| {
            let cx = cx.clone();
            let tracer = tracer.clone();
            tokio::spawn(async move {
                let span = tracer
                    .span_builder(format!("task-{}", i))
                    .with_parent_context(cx)
                    .start(&tracer);
                
                let cx = Context::current_with_span(span);
                cx.attach(|| async {
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }).await;
            })
        })
        .collect();
    
    join_all(tasks).await;
}
```

---

### 线程间传递

#### **跨线程传播**

```rust
use std::thread;

fn cross_thread_context() {
    let tracer = global::tracer("service");
    let span = tracer.start("main-thread");
    let cx = Context::current_with_span(span);
    
    // 克隆 Context 传递到新线程
    let cx_clone = cx.clone();
    thread::spawn(move || {
        let span = cx_clone.span();
        span.add_event("Worker thread started", vec![]);
        
        // 执行业务逻辑
        heavy_computation();
    });
}

fn heavy_computation() {
    // 获取当前线程的 Context
    let cx = Context::current();
    let span = cx.span();
    span.add_event("Computation in progress", vec![]);
}
```

---

#### **Rayon 并行计算**

```rust
use rayon::prelude::*;

fn parallel_computation_with_context(cx: Context) {
    let items: Vec<i32> = (0..1000).collect();
    
    items.par_iter().for_each(|&item| {
        // 每个线程需要克隆 Context
        let cx = cx.clone();
        let span = cx.span();
        
        span.add_event(
            "Processing item",
            vec![KeyValue::new("item", item as i64)],
        );
        
        process_item(item);
    });
}
```

---

## 与 tracing 集成

**推荐方式：使用 `tracing` 生态自动管理 Context**

```rust
use tracing::{info, instrument, Instrument};

#[instrument]
async fn handle_request(user_id: i32) {
    // tracing 自动创建 Span 并管理 Context
    info!(user_id, "Request received");
    
    fetch_user_data(user_id).await;
    process_user_data().await;
}

#[instrument]
async fn fetch_user_data(user_id: i32) {
    info!("Fetching user data");
    tokio::time::sleep(Duration::from_millis(100)).await;
}

#[instrument]
async fn process_user_data() {
    info!("Processing user data");
}

#[tokio::main]
async fn main() {
    // 初始化 tracing + OpenTelemetry
    let tracer = global::tracer("service");
    let subscriber = tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer));
    
    tracing::subscriber::set_global_default(subscriber).unwrap();
    
    // 自动传播 Context
    handle_request(123).await;
}
```

---

### **手动管理 Span Guard**

```rust
async fn manual_span_guard() {
    let tracer = global::tracer("service");
    let span = tracer.start("operation");
    
    // 使用 Guard 自动管理生命周期
    let _guard = span.enter();
    
    // 在作用域内，Context 自动可用
    info!("This log is associated with the span");
    
    // _guard Drop 时自动退出 Span
}
```

---

## 最佳实践

### ✅ **推荐**

1. **使用 tracing 宏**：`#[instrument]` 自动管理 Context
2. **显式传递关键 Context**：HTTP 客户端、数据库调用
3. **克隆 Context**：跨线程/任务时克隆（开销小）
4. **避免全局状态**：使用 Task-local storage
5. **Context 作用域**：

   ```rust
   cx.attach(|| async {
       // 在此作用域内自动可用
   }).await;
   ```

6. **异步任务**：使用 `.instrument(span)` 自动传播

### ❌ **避免**

1. **忘记传递 Context**：导致 Trace 断链
2. **修改 Context**：Context 是不可变的
3. **过度克隆**：虽然开销小，但无意义的克隆应避免
4. **阻塞操作**：Context 传播应快速完成

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
tokio = { version = "1", features = ["full"] }
```

### **tracing 集成**

```toml
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.25"
```

### **并行计算**

```toml
rayon = "1.10"
futures = "0.3"
```

---

## 总结

| 功能 | 实现方式 |
|------|---------|
| 获取当前 Context | `Context::current()` |
| 创建带 Span 的 Context | `Context::current_with_span(span)` |
| 显式传递 | 函数参数 `fn f(cx: Context)` |
| 隐式传递 | `cx.attach(\|\| async { ... })` |
| 异步任务 | `tokio::spawn(task.instrument(span))` |
| 线程间传递 | `cx.clone()` 传递到新线程 |
| tracing 集成 | `#[instrument]` 自动管理 |

**下一步**：[02_Propagator_Rust完整版.md](./02_Propagator_Rust完整版.md) - 学习如何跨服务传播 Context
