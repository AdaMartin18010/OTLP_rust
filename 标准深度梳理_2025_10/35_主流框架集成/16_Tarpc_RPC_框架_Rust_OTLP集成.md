# Tarpc RPC 框架 - Rust + OTLP 完整集成指南

## 📋 目录

- [Tarpc RPC 框架 - Rust + OTLP 完整集成指南](#tarpc-rpc-框架---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Tarpc?](#什么是-tarpc)
    - [为什么选择 Tarpc?](#为什么选择-tarpc)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Tarpc 架构](#1-tarpc-架构)
    - [2. 传输层](#2-传输层)
  - [环境准备](#环境准备)
    - [1. 项目配置](#1-项目配置)
  - [基础集成](#基础集成)
    - [1. 定义服务](#1-定义服务)
    - [2. 服务端实现](#2-服务端实现)
    - [3. 客户端调用](#3-客户端调用)
  - [OTLP 追踪集成](#otlp-追踪集成)
    - [1. 服务端追踪](#1-服务端追踪)
    - [2. 客户端追踪](#2-客户端追踪)
    - [3. 跨服务追踪](#3-跨服务追踪)
  - [高级特性](#高级特性)
    - [1. 双向流](#1-双向流)
    - [2. 中间件](#2-中间件)
    - [3. 负载均衡](#3-负载均衡)
  - [错误处理](#错误处理)
    - [1. 自定义错误](#1-自定义错误)
    - [2. 超时处理](#2-超时处理)
  - [性能优化](#性能优化)
    - [1. 连接池](#1-连接池)
    - [2. 批量请求](#2-批量请求)
  - [完整示例](#完整示例)
    - [1. 微服务架构](#1-微服务架构)
    - [2. 分布式计算](#2-分布式计算)
  - [最佳实践](#最佳实践)
    - [1. 服务设计](#1-服务设计)
    - [2. 监控告警](#2-监控告警)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Tarpc vs 其他 RPC](#tarpc-vs-其他-rpc)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Tarpc?

**Tarpc** 是用 Rust 编写的现代 RPC 框架:

```text
┌─────────────────────────────────────┐
│         Tarpc Framework             │
│  ┌──────────────────────────────┐   │
│  │  宏生成代码 (service!)        │   │
│  │  异步优先 (Tokio)             │   │
│  │  类型安全                     │   │
│  │  传输层抽象                   │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
```

**核心特性**:

- **宏驱动**: `#[tarpc::service]` 自动生成客户端/服务端代码
- **异步原生**: 完全异步,基于 Tokio
- **类型安全**: 编译时检查 RPC 签名
- **传输无关**: TCP, Unix Socket, in-memory
- **零拷贝**: Serde 高效序列化

### 为什么选择 Tarpc?

| 优势 | 说明 |
|------|------|
| **纯 Rust** | 100% Rust,无 protobuf/IDL |
| **简洁API** | trait + 宏,极简实现 |
| **高性能** | 异步 + 零拷贝 |
| **灵活** | 支持多种传输层 |
| **轻量级** | 小巧的依赖树 |

### OTLP 集成价值

```text
Client → Tarpc RPC → Server
   ↓         ↓         ↓
 Trace    Context    Trace
   ↓         ↓         ↓
   └───→ OTLP ←───┘
```

**追踪能力**:

- RPC 调用延迟
- 序列化/反序列化时间
- 网络传输时间
- 跨服务追踪链

---

## 核心概念

### 1. Tarpc 架构

```text
┌─────────────────────────────────────────┐
│           Client Application            │
│  ┌─────────────────────────────────┐    │
│  │  Generated Client Stub          │    │
│  └──────────────┬──────────────────┘    │
└─────────────────┼───────────────────────┘
                  │ RPC Call
┌─────────────────▼────────────────────────┐
│         Transport Layer (TCP)            │
└─────────────────┬────────────────────────┘
                  │ Serialized Request
┌─────────────────▼────────────────────────┐
│           Server Application             │
│  ┌─────────────────────────────────┐     │
│  │  Service Implementation         │     │
│  └─────────────────────────────────┘     │
└──────────────────────────────────────────┘
```

### 2. 传输层

Tarpc 支持多种传输:

- **TCP**: 网络通信
- **Unix Socket**: 本地进程间通信
- **In-Memory**: 测试和基准测试

---

## 环境准备

### 1. 项目配置

```toml
# Cargo.toml
[package]
name = "tarpc-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Tarpc 核心
tarpc = { version = "0.34", features = ["tokio1", "serde-transport", "tcp"] }

# 异步运行时
tokio = { version = "1.37", features = ["full"] }
tokio-serde = { version = "0.9", features = ["bincode"] }

# OTLP
opentelemetry = "0.30"
opentelemetry-otlp = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 序列化
serde = { version = "1.0", features = ["derive"] }
bincode = "1.3"

# 网络
futures = "0.3"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. 定义服务

```rust
// src/service.rs
use serde::{Deserialize, Serialize};

// 定义数据类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

// 定义 RPC 服务
#[tarpc::service]
pub trait UserService {
    /// 获取用户
    async fn get_user(id: String) -> Option<User>;
    
    /// 创建用户
    async fn create_user(req: CreateUserRequest) -> User;
    
    /// 列出所有用户
    async fn list_users(limit: usize) -> Vec<User>;
    
    /// 删除用户
    async fn delete_user(id: String) -> bool;
}
```

### 2. 服务端实现

```rust
// src/server.rs
use tarpc::{
    context::Context,
    server::{self, Channel},
};
use tokio::net::TcpListener;
use tokio_serde::formats::Bincode;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 服务实现
#[derive(Clone)]
pub struct UserServiceServer {
    users: Arc<RwLock<HashMap<String, User>>>,
}

impl UserServiceServer {
    pub fn new() -> Self {
        Self {
            users: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

// 实现 RPC trait
#[tarpc::server]
impl UserService for UserServiceServer {
    async fn get_user(self, _ctx: Context, id: String) -> Option<User> {
        tracing::info!("RPC: get_user({})", id);
        
        let users = self.users.read().unwrap();
        users.get(&id).cloned()
    }
    
    async fn create_user(self, _ctx: Context, req: CreateUserRequest) -> User {
        tracing::info!("RPC: create_user({:?})", req);
        
        let user = User {
            id: uuid::Uuid::new_v4().to_string(),
            name: req.name,
            email: req.email,
        };
        
        let mut users = self.users.write().unwrap();
        users.insert(user.id.clone(), user.clone());
        
        user
    }
    
    async fn list_users(self, _ctx: Context, limit: usize) -> Vec<User> {
        tracing::info!("RPC: list_users({})", limit);
        
        let users = self.users.read().unwrap();
        users.values().take(limit).cloned().collect()
    }
    
    async fn delete_user(self, _ctx: Context, id: String) -> bool {
        tracing::info!("RPC: delete_user({})", id);
        
        let mut users = self.users.write().unwrap();
        users.remove(&id).is_some()
    }
}

// 启动服务器
pub async fn start_server(addr: &str) -> anyhow::Result<()> {
    let listener = TcpListener::bind(addr).await?;
    tracing::info!("Server listening on {}", addr);
    
    let service = UserServiceServer::new();
    
    loop {
        let (stream, peer_addr) = listener.accept().await?;
        tracing::info!("Accepted connection from {}", peer_addr);
        
        let service = service.clone();
        
        tokio::spawn(async move {
            let transport = tarpc::serde_transport::new(
                tokio_util::codec::LengthDelimitedCodec::new().framed(stream),
                Bincode::default(),
            );
            
            let channel = server::BaseChannel::with_defaults(transport);
            
            channel
                .execute(service.serve())
                .await;
        });
    }
}
```

### 3. 客户端调用

```rust
// src/client.rs
use tarpc::client;
use tarpc::context;
use tokio::net::TcpStream;
use tokio_serde::formats::Bincode;

pub struct UserServiceClient {
    client: UserServiceClient,
}

impl UserServiceClient {
    pub async fn connect(addr: &str) -> anyhow::Result<Self> {
        let stream = TcpStream::connect(addr).await?;
        
        let transport = tarpc::serde_transport::new(
            tokio_util::codec::LengthDelimitedCodec::new().framed(stream),
            Bincode::default(),
        );
        
        let client = UserServiceClient::new(client::Config::default(), transport).spawn();
        
        Ok(Self { client })
    }
    
    pub async fn get_user(&self, id: String) -> anyhow::Result<Option<User>> {
        let ctx = context::current();
        let result = self.client.get_user(ctx, id).await?;
        Ok(result)
    }
    
    pub async fn create_user(&self, req: CreateUserRequest) -> anyhow::Result<User> {
        let ctx = context::current();
        let result = self.client.create_user(ctx, req).await?;
        Ok(result)
    }
}

// 使用示例
pub async fn example_usage() -> anyhow::Result<()> {
    let client = UserServiceClient::connect("127.0.0.1:8080").await?;
    
    // 创建用户
    let user = client.create_user(CreateUserRequest {
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    }).await?;
    
    tracing::info!("Created user: {:?}", user);
    
    // 获取用户
    let retrieved = client.get_user(user.id.clone()).await?;
    tracing::info!("Retrieved user: {:?}", retrieved);
    
    Ok(())
}
```

---

## OTLP 追踪集成

### 1. 服务端追踪

```rust
// src/server_tracing.rs
use tracing::{info, instrument, Span};
use opentelemetry::trace::{SpanKind, TraceContextExt};

#[derive(Clone)]
pub struct TracedUserServiceServer {
    inner: UserServiceServer,
}

#[tarpc::server]
impl UserService for TracedUserServiceServer {
    #[instrument(
        name = "UserService.get_user",
        fields(
            rpc.system = "tarpc",
            rpc.service = "UserService",
            rpc.method = "get_user",
            user.id = %id,
        )
    )]
    async fn get_user(self, ctx: Context, id: String) -> Option<User> {
        let span = Span::current();
        
        // 提取客户端 trace context
        if let Some(trace_id) = extract_trace_context(&ctx) {
            // 关联到客户端 trace
        }
        
        let start = std::time::Instant::now();
        let result = self.inner.get_user(ctx, id).await;
        let duration = start.elapsed();
        
        span.record("rpc.duration_ms", duration.as_millis() as i64);
        span.record("rpc.result", if result.is_some() { "found" } else { "not_found" });
        
        result
    }
    
    #[instrument(
        name = "UserService.create_user",
        skip(req),
        fields(
            rpc.system = "tarpc",
            rpc.service = "UserService",
            rpc.method = "create_user",
            user.name = %req.name,
        )
    )]
    async fn create_user(self, ctx: Context, req: CreateUserRequest) -> User {
        let result = self.inner.create_user(ctx, req).await;
        
        Span::current().record("user.id", &result.id.as_str());
        
        result
    }
    
    // 其他方法类似...
}
```

### 2. 客户端追踪

```rust
// src/client_tracing.rs
use opentelemetry::{
    global,
    trace::{Span, Tracer},
    KeyValue,
};

pub struct TracedUserServiceClient {
    inner: UserServiceClient,
}

impl TracedUserServiceClient {
    #[instrument(
        name = "UserService.get_user.client",
        fields(
            rpc.system = "tarpc",
            rpc.service = "UserService",
            rpc.method = "get_user",
            span.kind = "client",
            user.id = %id,
        )
    )]
    pub async fn get_user(&self, id: String) -> anyhow::Result<Option<User>> {
        let tracer = global::tracer("tarpc-client");
        
        let mut span = tracer
            .span_builder("rpc.client.call")
            .with_kind(SpanKind::Client)
            .start(&tracer);
        
        // 注入 trace context 到 RPC context
        let mut ctx = context::current();
        inject_trace_context(&mut ctx, &span);
        
        let start = std::time::Instant::now();
        let result = self.inner.client.get_user(ctx, id).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("rpc.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(Some(_)) => {
                span.set_attribute(KeyValue::new("rpc.status", "success"));
            }
            Ok(None) => {
                span.set_attribute(KeyValue::new("rpc.status", "not_found"));
            }
            Err(e) => {
                span.record_error(e);
                span.set_attribute(KeyValue::new("rpc.status", "error"));
            }
        }
        
        span.end();
        
        Ok(result?)
    }
}
```

### 3. 跨服务追踪

```rust
// 传播 Trace Context
use opentelemetry::propagation::{Injector, Extractor};
use tarpc::context::Context;

struct TarpcContextInjector<'a> {
    context: &'a mut Context,
}

impl<'a> Injector for TarpcContextInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        // 将 trace context 注入到 Tarpc Context
        // Tarpc Context 可以携带任意元数据
        self.context.metadata.insert(key.to_string(), value);
    }
}

struct TarpcContextExtractor<'a> {
    context: &'a Context,
}

impl<'a> Extractor for TarpcContextExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.context.metadata.get(key).map(|s| s.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.context.metadata.keys().map(|k| k.as_str()).collect()
    }
}

// 注入函数
fn inject_trace_context(ctx: &mut Context, span: &Span) {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let mut injector = TarpcContextInjector { context: ctx };
    propagator.inject_context(&span.span_context(), &mut injector);
}

// 提取函数
fn extract_trace_context(ctx: &Context) -> Option<SpanContext> {
    let propagator = global::get_text_map_propagator(|p| p.clone());
    let extractor = TarpcContextExtractor { context: ctx };
    let context = propagator.extract(&extractor);
    Some(context.span().span_context().clone())
}
```

---

## 高级特性

### 1. 双向流

```rust
// 流式 RPC
#[tarpc::service]
pub trait StreamingService {
    /// 服务端流
    async fn stream_data(count: usize) -> futures::stream::BoxStream<'static, i32>;
}

// 实现
#[tarpc::server]
impl StreamingService for MyStreamingService {
    async fn stream_data(
        self,
        _ctx: Context,
        count: usize,
    ) -> futures::stream::BoxStream<'static, i32> {
        use futures::stream::{self, StreamExt};
        
        stream::iter(0..count as i32)
            .then(|i| async move {
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                i
            })
            .boxed()
    }
}
```

### 2. 中间件

```rust
// Tarpc 中间件
use tarpc::server::Channel;

pub async fn logging_middleware<Req, Resp, F>(
    ctx: Context,
    req: Req,
    next: F,
) -> Resp
where
    F: FnOnce(Context, Req) -> Resp,
{
    tracing::info!("RPC request received: {:?}", ctx);
    
    let start = std::time::Instant::now();
    let response = next(ctx, req);
    let duration = start.elapsed();
    
    tracing::info!("RPC completed in {:?}", duration);
    
    response
}
```

### 3. 负载均衡

```rust
// 简单的客户端负载均衡
pub struct LoadBalancedClient {
    clients: Vec<UserServiceClient>,
    current: AtomicUsize,
}

impl LoadBalancedClient {
    pub async fn new(addrs: Vec<String>) -> anyhow::Result<Self> {
        let mut clients = Vec::new();
        
        for addr in addrs {
            let client = UserServiceClient::connect(&addr).await?;
            clients.push(client);
        }
        
        Ok(Self {
            clients,
            current: AtomicUsize::new(0),
        })
    }
    
    pub async fn get_user(&self, id: String) -> anyhow::Result<Option<User>> {
        // 轮询
        let idx = self.current.fetch_add(1, Ordering::Relaxed) % self.clients.len();
        self.clients[idx].get_user(id).await
    }
}
```

---

## 错误处理

### 1. 自定义错误

```rust
#[derive(Debug, Clone, Serialize, Deserialize, thiserror::Error)]
pub enum ServiceError {
    #[error("User not found: {0}")]
    UserNotFound(String),
    
    #[error("Invalid input: {0}")]
    InvalidInput(String),
    
    #[error("Database error: {0}")]
    DatabaseError(String),
}

// 在服务中使用
#[tarpc::service]
pub trait UserServiceFallible {
    async fn get_user(id: String) -> Result<User, ServiceError>;
}
```

### 2. 超时处理

```rust
// 客户端超时
pub async fn call_with_timeout() -> anyhow::Result<Option<User>> {
    let client = UserServiceClient::connect("127.0.0.1:8080").await?;
    
    // 设置超时
    let mut ctx = context::current();
    ctx.deadline = tokio::time::Instant::now() + tokio::time::Duration::from_secs(5);
    
    let result = client.client.get_user(ctx, "user123".to_string()).await?;
    
    Ok(result)
}
```

---

## 性能优化

### 1. 连接池

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

pub struct ClientPool {
    clients: Vec<Arc<UserServiceClient>>,
    semaphore: Arc<Semaphore>,
}

impl ClientPool {
    pub async fn new(addr: &str, pool_size: usize) -> anyhow::Result<Self> {
        let mut clients = Vec::with_capacity(pool_size);
        
        for _ in 0..pool_size {
            let client = UserServiceClient::connect(addr).await?;
            clients.push(Arc::new(client));
        }
        
        Ok(Self {
            clients,
            semaphore: Arc::new(Semaphore::new(pool_size)),
        })
    }
    
    pub async fn execute<F, R>(&self, f: F) -> anyhow::Result<R>
    where
        F: FnOnce(&UserServiceClient) -> futures::future::BoxFuture<'_, anyhow::Result<R>>,
    {
        let _permit = self.semaphore.acquire().await?;
        
        // 简单的轮询选择
        let client = &self.clients[rand::random::<usize>() % self.clients.len()];
        
        f(client).await
    }
}
```

### 2. 批量请求

```rust
// 批量操作
#[tarpc::service]
pub trait BatchUserService {
    async fn get_users_batch(ids: Vec<String>) -> Vec<Option<User>>;
    async fn create_users_batch(reqs: Vec<CreateUserRequest>) -> Vec<User>;
}
```

---

## 完整示例

### 1. 微服务架构

见上文基础集成和追踪部分。

### 2. 分布式计算

```rust
// 分布式任务处理
#[tarpc::service]
pub trait WorkerService {
    async fn process_task(task: Task) -> TaskResult;
    async fn get_status() -> WorkerStatus;
}

#[derive(Serialize, Deserialize)]
pub struct Task {
    pub id: String,
    pub data: Vec<u8>,
}

#[derive(Serialize, Deserialize)]
pub struct TaskResult {
    pub task_id: String,
    pub result: Vec<u8>,
    pub duration_ms: u64,
}
```

---

## 最佳实践

### 1. 服务设计

```rust
// ✅ 好的实践: 小而聚焦的 RPC 方法
#[tarpc::service]
pub trait UserService {
    async fn get_user(id: String) -> Option<User>;
    async fn create_user(req: CreateUserRequest) -> User;
}

// ❌ 避免: 过大的 RPC 方法
#[tarpc::service]
pub trait BadService {
    async fn do_everything(data: Vec<u8>) -> Vec<u8>;  // 太宽泛
}
```

### 2. 监控告警

```rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct RpcMetrics {
    call_count: Counter<u64>,
    call_duration: Histogram<f64>,
}

impl RpcMetrics {
    pub fn record_call(&self, method: &str, duration_ms: f64, success: bool) {
        let attributes = vec![
            KeyValue::new("method", method.to_string()),
            KeyValue::new("status", if success { "success" } else { "error" }),
        ];
        
        self.call_count.add(1, &attributes);
        self.call_duration.record(duration_ms, &attributes);
    }
}
```

---

## 总结

### 核心要点

1. **Tarpc**: 纯 Rust RPC 框架
2. **宏驱动**: 自动生成代码
3. **异步原生**: Tokio 完全异步
4. **OTLP 集成**: 分布式追踪
5. **类型安全**: 编译时检查

### Tarpc vs 其他 RPC

| 特性 | Tarpc | gRPC (Tonic) | Cap'n Proto | JSON-RPC |
|------|-------|--------------|-------------|----------|
| **纯 Rust** | ✅ | ⚠️ Protobuf | ⚠️ IDL | ✅ |
| **性能** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ |
| **流式** | ✅ | ✅ | ✅ | ❌ |
| **跨语言** | ❌ | ✅ | ✅ | ✅ |

### 下一步

- **高级序列化**: 使用 MessagePack, CBOR
- **服务发现**: 集成 Consul/etcd
- **熔断器**: 实现熔断和限流

---

## 参考资料

- [Tarpc 官方文档](https://github.com/google/tarpc)
- [Tarpc Examples](https://github.com/google/tarpc/tree/master/examples)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Tarpc**: 0.34+  
**OpenTelemetry**: 0.30+
