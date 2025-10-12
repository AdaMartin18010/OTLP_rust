# ZeroMQ 高性能异步消息 - 完整实现指南

## 目录

- [ZeroMQ 高性能异步消息 - 完整实现指南](#zeromq-高性能异步消息---完整实现指南)
  - [目录](#目录)
  - [1. ZeroMQ 概述](#1-zeromq-概述)
    - [1.1 什么是 ZeroMQ?](#11-什么是-zeromq)
    - [1.2 ZeroMQ vs 传统消息队列](#12-zeromq-vs-传统消息队列)
    - [1.3 典型应用场景](#13-典型应用场景)
  - [2. 核心架构](#2-核心架构)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
    - [3.2 系统依赖安装](#32-系统依赖安装)
  - [4. 核心消息模式](#4-核心消息模式)
    - [4.1 Request-Reply (REQ-REP)](#41-request-reply-req-rep)
      - [Server 实现](#server-实现)
      - [Client 实现](#client-实现)
    - [4.2 Publish-Subscribe (PUB-SUB)](#42-publish-subscribe-pub-sub)
      - [Publisher 实现](#publisher-实现)
      - [Subscriber 实现](#subscriber-实现)
    - [4.3 Push-Pull (PUSH-PULL)](#43-push-pull-push-pull)
      - [Producer (Ventilator)](#producer-ventilator)
      - [Worker](#worker)
      - [Sink (结果收集器)](#sink-结果收集器)
    - [4.4 Dealer-Router (DEALER-ROUTER)](#44-dealer-router-dealer-router)
      - [Router Server](#router-server)
      - [Dealer Client](#dealer-client)
  - [5. 高级功能](#5-高级功能)
    - [5.1 Multipart Messages](#51-multipart-messages)
    - [5.2 High Water Mark (HWM)](#52-high-water-mark-hwm)
    - [5.3 Linger (优雅关闭)](#53-linger-优雅关闭)
  - [6. 可靠性保证](#6-可靠性保证)
    - [6.1 Lazy Pirate Pattern (客户端重试)](#61-lazy-pirate-pattern-客户端重试)
    - [6.2 Simple Pirate Pattern (服务端心跳)](#62-simple-pirate-pattern-服务端心跳)
  - [7. 性能优化](#7-性能优化)
    - [7.1 批量发送](#71-批量发送)
    - [7.2 Zero-Copy (IPC)](#72-zero-copy-ipc)
  - [8. OTLP 可观测性集成](#8-otlp-可观测性集成)
    - [8.1 追踪初始化](#81-追踪初始化)
    - [8.2 带追踪的消息发送](#82-带追踪的消息发送)
  - [9. 测试策略](#9-测试策略)
    - [9.1 集成测试](#91-集成测试)
  - [10. 生产实践](#10-生产实践)
    - [10.1 配置管理](#101-配置管理)
    - [10.2 Docker Compose 部署](#102-docker-compose-部署)
  - [11. 国际标准对齐](#11-国际标准对齐)
    - [11.1 ZeroMQ Protocol (ZMTP/3.1)](#111-zeromq-protocol-zmtp31)
    - [11.2 OpenTelemetry 语义约定](#112-opentelemetry-语义约定)
  - [总结](#总结)

---

## 1. ZeroMQ 概述

### 1.1 什么是 ZeroMQ?

**ZeroMQ (ØMQ)** 是一个高性能异步消息库，提供：

- **无代理架构**: 直接点对点通信，无需中心化消息代理
- **多种传输协议**: TCP, IPC, In-process, PGM (multicast)
- **多种消息模式**: Request-Reply, Pub-Sub, Push-Pull, Dealer-Router
- **自动重连**: 内置连接管理和故障恢复
- **高吞吐低延迟**: 优化的零拷贝技术

### 1.2 ZeroMQ vs 传统消息队列

| 特性 | ZeroMQ | Kafka | RabbitMQ | NATS |
|------|--------|-------|----------|------|
| **架构** | 无代理（嵌入式） | 中心化代理 | 中心化代理 | 中心化服务器 |
| **延迟** | < 100 μs | 2-10 ms | 1-5 ms | < 1 ms |
| **吞吐量** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **持久化** | ❌ 无 | ✅ 日志存储 | ✅ 队列持久化 | ⚠️ JetStream |
| **消息模式** | 5+ 种 | Pub-Sub | AMQP 多种 | Pub-Sub, Req-Reply |
| **部署复杂度** | ⭐ (库) | ⭐⭐⭐⭐ (集群) | ⭐⭐⭐ (集群) | ⭐⭐ (服务器) |
| **适用场景** | 低延迟、高频交易 | 大数据流 | 企业消息 | 云原生微服务 |

### 1.3 典型应用场景

- ✅ **金融交易系统**: 微秒级延迟要求
- ✅ **实时数据分发**: Pub-Sub 广播
- ✅ **分布式计算**: Task Distribution (Push-Pull)
- ✅ **微服务通信**: Request-Reply
- ✅ **IoT 数据采集**: 边缘设备通信

---

## 2. 核心架构

```text
┌─────────────────────────────────────────────────────────────┐
│                     ZeroMQ 消息模式                          │
├─────────────────────────────────────────────────────────────┤
│  1. Request-Reply (REQ-REP)                                 │
│     Client <─────────────> Server                           │
│                                                             │
│  2. Publish-Subscribe (PUB-SUB)                             │
│     Publisher ────┬────> Subscriber 1                       │
│                   └────> Subscriber 2                       │
│                                                             │
│  3. Push-Pull (PUSH-PULL)                                   │
│     Producer ────> Worker 1 ───┐                            │
│                   Worker 2 ───┤─────> Sink                  │
│                                                             │
│  4. Dealer-Router (DEALER-ROUTER)                           │
│     Client 1 ────┐                                          │
│     Client 2 ────┤───> Router ───> Backend                  │
│                                                             │
│  5. Pair (PAIR)                                             │
│     Thread 1 <─────────────> Thread 2                       │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "zeromq-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# ZeroMQ 异步库
zeromq = { version = "0.4", features = ["all-transports"] }

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"
bincode = "1"

# 错误处理
thiserror = "1"
anyhow = "1"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }

# UUID
uuid = { version = "1", features = ["v4", "serde"] }

[dev-dependencies]
criterion = "0.5"
```

### 3.2 系统依赖安装

```bash
# Ubuntu/Debian
sudo apt-get install libzmq3-dev

# macOS
brew install zeromq

# Windows (vcpkg)
vcpkg install zeromq
```

---

## 4. 核心消息模式

### 4.1 Request-Reply (REQ-REP)

**同步请求-响应模式**，类似 HTTP 的 Client-Server 模式。

#### Server 实现

```rust
use zeromq::{RepSocket, SocketRecv, SocketSend};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Request {
    id: String,
    operation: String,
    params: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct Response {
    id: String,
    result: String,
}

/// REP Server
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = RepSocket::new();
    socket.bind("tcp://0.0.0.0:5555").await?;
    tracing::info!("REP Server listening on tcp://0.0.0.0:5555");

    loop {
        // 1. 接收请求
        let message = socket.recv().await?;
        let request: Request = bincode::deserialize(&message.get(0).unwrap())?;
        tracing::info!("Received request: {:?}", request);

        // 2. 处理请求
        let result = match request.operation.as_str() {
            "add" => {
                let sum: i32 = request.params.iter()
                    .filter_map(|s| s.parse::<i32>().ok())
                    .sum();
                sum.to_string()
            }
            "echo" => request.params.join(" "),
            _ => "Unknown operation".to_string(),
        };

        // 3. 发送响应
        let response = Response {
            id: request.id,
            result,
        };
        let bytes = bincode::serialize(&response)?;
        socket.send(bytes.into()).await?;
    }
}
```

#### Client 实现

```rust
use zeromq::{ReqSocket, SocketRecv, SocketSend};

/// REQ Client
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = ReqSocket::new();
    socket.connect("tcp://localhost:5555").await?;
    tracing::info!("REQ Client connected to tcp://localhost:5555");

    for i in 0..5 {
        // 1. 发送请求
        let request = Request {
            id: format!("req-{}", i),
            operation: "add".to_string(),
            params: vec!["10".to_string(), "20".to_string()],
        };
        let bytes = bincode::serialize(&request)?;
        socket.send(bytes.into()).await?;

        // 2. 接收响应
        let message = socket.recv().await?;
        let response: Response = bincode::deserialize(&message.get(0).unwrap())?;
        tracing::info!("Response: {:?}", response);

        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }

    Ok(())
}
```

---

### 4.2 Publish-Subscribe (PUB-SUB)

**一对多广播模式**，Publisher 发布消息，所有 Subscribers 接收。

#### Publisher 实现

```rust
use zeromq::{PubSocket, SocketSend};

#[derive(Debug, Serialize, Deserialize)]
struct Event {
    topic: String,
    timestamp: i64,
    payload: String,
}

/// PUB Publisher
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = PubSocket::new();
    socket.bind("tcp://0.0.0.0:5556").await?;
    tracing::info!("PUB Publisher bound to tcp://0.0.0.0:5556");

    let mut counter = 0;
    loop {
        for topic in &["weather", "stock", "news"] {
            let event = Event {
                topic: topic.to_string(),
                timestamp: chrono::Utc::now().timestamp_millis(),
                payload: format!("{} update #{}", topic, counter),
            };

            // 发送消息 (Topic Filter + Payload)
            let topic_frame = topic.as_bytes().to_vec();
            let payload_frame = bincode::serialize(&event)?;

            socket.send(vec![topic_frame.into(), payload_frame.into()].into()).await?;
            tracing::info!("Published: {:?}", event);
        }

        counter += 1;
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }
}
```

#### Subscriber 实现

```rust
use zeromq::{SubSocket, SocketRecv};

/// SUB Subscriber
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = SubSocket::new();
    socket.connect("tcp://localhost:5556").await?;

    // 订阅多个 Topic
    socket.subscribe("weather").await?;
    socket.subscribe("stock").await?;

    tracing::info!("SUB Subscriber connected and subscribed to weather, stock");

    loop {
        let message = socket.recv().await?;
        
        let topic = String::from_utf8_lossy(message.get(0).unwrap());
        let event: Event = bincode::deserialize(message.get(1).unwrap())?;

        tracing::info!("Received [{}]: {:?}", topic, event);
    }
}
```

---

### 4.3 Push-Pull (PUSH-PULL)

**任务分发模式**，Producer 推送任务，Workers 负载均衡处理。

#### Producer (Ventilator)

```rust
use zeromq::{PushSocket, SocketSend};

#[derive(Debug, Serialize, Deserialize)]
struct Task {
    id: String,
    workload: u64, // 模拟工作时长（毫秒）
}

/// PUSH Producer
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = PushSocket::new();
    socket.bind("tcp://0.0.0.0:5557").await?;
    tracing::info!("PUSH Producer bound to tcp://0.0.0.0:5557");

    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await; // 等待 Workers 连接

    for i in 0..100 {
        let task = Task {
            id: format!("task-{}", i),
            workload: rand::random::<u64>() % 1000,
        };

        let bytes = bincode::serialize(&task)?;
        socket.send(bytes.into()).await?;
        tracing::info!("Sent: {:?}", task);
    }

    Ok(())
}
```

#### Worker

```rust
use zeromq::{PullSocket, SocketRecv};

/// PULL Worker
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = PullSocket::new();
    socket.connect("tcp://localhost:5557").await?;
    tracing::info!("PULL Worker connected to tcp://localhost:5557");

    loop {
        let message = socket.recv().await?;
        let task: Task = bincode::deserialize(&message.get(0).unwrap())?;

        tracing::info!("Processing: {:?}", task);
        tokio::time::sleep(tokio::time::Duration::from_millis(task.workload)).await;
        tracing::info!("Completed: {}", task.id);
    }
}
```

#### Sink (结果收集器)

```rust
use zeromq::{PullSocket, SocketRecv};

/// PULL Sink
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = PullSocket::new();
    socket.bind("tcp://0.0.0.0:5558").await?;
    tracing::info!("PULL Sink bound to tcp://0.0.0.0:5558");

    let mut completed = 0;
    loop {
        let message = socket.recv().await?;
        let result: String = bincode::deserialize(&message.get(0).unwrap())?;

        completed += 1;
        tracing::info!("Result #{}: {}", completed, result);
    }
}
```

---

### 4.4 Dealer-Router (DEALER-ROUTER)

**异步多路复用模式**，支持多个客户端与单个服务端的异步通信。

#### Router Server

```rust
use zeromq::{RouterSocket, SocketRecv, SocketSend};

/// ROUTER Server
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = RouterSocket::new();
    socket.bind("tcp://0.0.0.0:5559").await?;
    tracing::info!("ROUTER Server bound to tcp://0.0.0.0:5559");

    loop {
        let message = socket.recv().await?;
        
        // Message 结构: [Identity, Empty, Payload]
        let identity = message.get(0).unwrap().clone();
        let payload = message.get(2).unwrap();
        let request: Request = bincode::deserialize(payload)?;

        tracing::info!("Received from {:?}: {:?}", identity, request);

        // 处理请求
        let response = Response {
            id: request.id,
            result: format!("Processed: {}", request.operation),
        };

        // 回复客户端
        let response_bytes = bincode::serialize(&response)?;
        socket.send(vec![
            identity.into(),
            vec![].into(),
            response_bytes.into(),
        ].into()).await?;
    }
}
```

#### Dealer Client

```rust
use zeromq::{DealerSocket, SocketRecv, SocketSend};

/// DEALER Client
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut socket = DealerSocket::new();
    socket.connect("tcp://localhost:5559").await?;
    tracing::info!("DEALER Client connected to tcp://localhost:5559");

    for i in 0..5 {
        let request = Request {
            id: format!("req-{}", i),
            operation: format!("operation-{}", i),
            params: vec![],
        };

        let bytes = bincode::serialize(&request)?;
        socket.send(vec![vec![].into(), bytes.into()].into()).await?;

        let message = socket.recv().await?;
        let response: Response = bincode::deserialize(message.get(1).unwrap())?;
        tracing::info!("Response: {:?}", response);

        tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    }

    Ok(())
}
```

---

## 5. 高级功能

### 5.1 Multipart Messages

```rust
use zeromq::{ZmqMessage, SocketSend};

/// 发送多帧消息
pub async fn send_multipart(socket: &mut impl SocketSend) -> anyhow::Result<()> {
    let message = ZmqMessage::from(vec![
        "header".as_bytes().to_vec().into(),
        "body".as_bytes().to_vec().into(),
        "footer".as_bytes().to_vec().into(),
    ]);

    socket.send(message).await?;
    Ok(())
}

/// 接收多帧消息
pub async fn recv_multipart(socket: &mut impl SocketRecv) -> anyhow::Result<Vec<String>> {
    let message = socket.recv().await?;
    
    let frames: Vec<String> = message.into_vec()
        .into_iter()
        .map(|frame| String::from_utf8_lossy(&frame).to_string())
        .collect();

    Ok(frames)
}
```

### 5.2 High Water Mark (HWM)

```rust
use zeromq::Socket;

/// 设置高水位标记（防止内存溢出）
pub async fn configure_hwm(socket: &mut impl Socket) -> anyhow::Result<()> {
    // 发送队列最大 1000 条消息
    socket.set_snd_hwm(1000)?;
    
    // 接收队列最大 1000 条消息
    socket.set_rcv_hwm(1000)?;

    Ok(())
}
```

### 5.3 Linger (优雅关闭)

```rust
/// 设置 Linger（关闭时等待未发送消息的时间）
pub async fn configure_linger(socket: &mut impl Socket) -> anyhow::Result<()> {
    // 关闭时等待 1000ms 发送剩余消息
    socket.set_linger(Some(std::time::Duration::from_millis(1000)))?;

    Ok(())
}
```

---

## 6. 可靠性保证

### 6.1 Lazy Pirate Pattern (客户端重试)

```rust
use zeromq::{ReqSocket, SocketRecv, SocketSend};
use tokio::time::{timeout, Duration};

const MAX_RETRIES: u32 = 3;
const REQUEST_TIMEOUT: Duration = Duration::from_secs(2);

/// 带重试的可靠客户端
pub async fn reliable_request(
    socket: &mut ReqSocket,
    request: &Request,
) -> anyhow::Result<Response> {
    let bytes = bincode::serialize(request)?;

    for attempt in 1..=MAX_RETRIES {
        tracing::info!("Attempt {}/{}", attempt, MAX_RETRIES);

        socket.send(bytes.clone().into()).await?;

        match timeout(REQUEST_TIMEOUT, socket.recv()).await {
            Ok(Ok(message)) => {
                let response: Response = bincode::deserialize(message.get(0).unwrap())?;
                return Ok(response);
            }
            Ok(Err(e)) => {
                tracing::error!("Recv error: {:?}", e);
            }
            Err(_) => {
                tracing::warn!("Request timeout, retrying...");
            }
        }
    }

    Err(anyhow::anyhow!("Failed after {} retries", MAX_RETRIES))
}
```

### 6.2 Simple Pirate Pattern (服务端心跳)

```rust
use tokio::time::{interval, Duration};

const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(1);
const HEARTBEAT_LIVENESS: u32 = 3;

/// 带心跳的服务端
pub async fn server_with_heartbeat() -> anyhow::Result<()> {
    let mut socket = RepSocket::new();
    socket.bind("tcp://0.0.0.0:5555").await?;

    let mut heartbeat = interval(HEARTBEAT_INTERVAL);

    loop {
        tokio::select! {
            result = socket.recv() => {
                let message = result?;
                // 处理请求...
                socket.send(vec![].into()).await?;
            }
            _ = heartbeat.tick() => {
                tracing::trace!("Heartbeat");
            }
        }
    }
}
```

---

## 7. 性能优化

### 7.1 批量发送

```rust
/// 批量发送消息
pub async fn batch_send(
    socket: &mut impl SocketSend,
    messages: Vec<Vec<u8>>,
) -> anyhow::Result<()> {
    for chunk in messages.chunks(100) {
        for msg in chunk {
            socket.send(msg.clone().into()).await?;
        }
        // 批次间暂停，防止接收端过载
        tokio::task::yield_now().await;
    }

    Ok(())
}
```

### 7.2 Zero-Copy (IPC)

```rust
/// 使用 IPC 传输（进程间零拷贝）
pub async fn ipc_example() -> anyhow::Result<()> {
    let mut socket = PubSocket::new();
    socket.bind("ipc:///tmp/my_ipc.socket").await?;

    // IPC 比 TCP 快 5-10 倍
    socket.send("high-performance message".into()).await?;

    Ok(())
}
```

---

## 8. OTLP 可观测性集成

### 8.1 追踪初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};

pub fn init_telemetry() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            sdktrace::Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "zeromq-service"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 8.2 带追踪的消息发送

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

#[instrument(skip(socket, request), fields(
    messaging.system = "zeromq",
    messaging.destination = "req-rep",
    messaging.operation = "send"
))]
pub async fn traced_send_request(
    socket: &mut ReqSocket,
    request: &Request,
) -> anyhow::Result<Response> {
    let tracer = global::tracer("zeromq-client");
    
    let mut span = tracer
        .span_builder(format!("ZeroMQ Send {}", request.operation))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "zeromq"),
            KeyValue::new("messaging.destination", "req-rep"),
            KeyValue::new("messaging.operation", "send"),
            KeyValue::new("messaging.message_id", request.id.clone()),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let bytes = bincode::serialize(request)?;
    let result = socket.send(bytes.into()).await;
    
    let duration = start.elapsed();
    
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("messaging.latency_us", duration.as_micros() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result?;

    // 接收响应
    let message = socket.recv().await?;
    Ok(bincode::deserialize(message.get(0).unwrap())?)
}
```

---

## 9. 测试策略

### 9.1 集成测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_req_rep_pattern() {
        // 启动服务端
        let server_task = tokio::spawn(async {
            let mut socket = RepSocket::new();
            socket.bind("tcp://127.0.0.1:15555").await.unwrap();

            let message = socket.recv().await.unwrap();
            socket.send(message).await.unwrap(); // Echo
        });

        // 等待服务端启动
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        // 启动客户端
        let mut client = ReqSocket::new();
        client.connect("tcp://127.0.0.1:15555").await.unwrap();

        client.send("hello".into()).await.unwrap();
        let response = client.recv().await.unwrap();

        assert_eq!(response.get(0).unwrap(), b"hello");

        server_task.abort();
    }
}
```

---

## 10. 生产实践

### 10.1 配置管理

```rust
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct ZmqConfig {
    pub bind_address: String,
    pub pattern: String, // "pub-sub", "req-rep", etc.
    pub hwm: usize,
    pub linger_ms: u64,
}

impl ZmqConfig {
    pub fn from_env() -> anyhow::Result<Self> {
        Ok(Self {
            bind_address: std::env::var("ZMQ_BIND_ADDRESS")
                .unwrap_or_else(|_| "tcp://0.0.0.0:5555".to_string()),
            pattern: std::env::var("ZMQ_PATTERN")
                .unwrap_or_else(|_| "req-rep".to_string()),
            hwm: std::env::var("ZMQ_HWM")
                .unwrap_or_else(|_| "1000".to_string())
                .parse()?,
            linger_ms: std::env::var("ZMQ_LINGER_MS")
                .unwrap_or_else(|_| "1000".to_string())
                .parse()?,
        })
    }
}
```

### 10.2 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  zmq-server:
    image: rust:1.90-slim
    command: cargo run --bin server
    volumes:
      - .:/app
    working_dir: /app
    ports:
      - "5555:5555"
    environment:
      ZMQ_BIND_ADDRESS: tcp://0.0.0.0:5555
      RUST_LOG: info

  zmq-client:
    image: rust:1.90-slim
    command: cargo run --bin client
    volumes:
      - .:/app
    working_dir: /app
    depends_on:
      - zmq-server
    environment:
      ZMQ_CONNECT_ADDRESS: tcp://zmq-server:5555
      RUST_LOG: info
```

---

## 11. 国际标准对齐

### 11.1 ZeroMQ Protocol (ZMTP/3.1)

- ✅ **ZMTP/3.1**: ZeroMQ Transmission Protocol
- ✅ **传输层**: TCP, IPC, In-process, PGM
- ✅ **安全机制**: CurveZMQ (Curve25519)

### 11.2 OpenTelemetry 语义约定

```rust
// Messaging Semantic Conventions (v1.21.0)
span.set_attribute(KeyValue::new("messaging.system", "zeromq"));
span.set_attribute(KeyValue::new("messaging.destination", "topic/queue"));
span.set_attribute(KeyValue::new("messaging.operation", "send"));
span.set_attribute(KeyValue::new("messaging.message_id", "msg-123"));
span.set_attribute(KeyValue::new("net.transport", "tcp"));
```

---

## 总结

**ZeroMQ 优势**:

1. **极低延迟**: < 100 微秒（IPC 模式）
2. **无代理架构**: 简化部署，减少故障点
3. **多种模式**: 灵活的消息传递模式
4. **高吞吐量**: 零拷贝技术

**适用场景**:

- ✅ 金融交易系统（低延迟要求）
- ✅ 实时数据分析（高频事件）
- ✅ 分布式计算（Task Distribution）
- ✅ IoT 边缘计算（嵌入式设备）

**不适用场景**:

- ❌ 需要持久化存储（使用 Kafka）
- ❌ 复杂路由逻辑（使用 RabbitMQ）
- ❌ 云原生微服务（使用 NATS）

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
