# WebSocket - Rust 完整版

## 目录

- [WebSocket - Rust 完整版](#websocket---rust-完整版)
  - [目录](#目录)
  - [1. WebSocket 概述](#1-websocket-概述)
    - [1.1 协议特点](#11-协议特点)
    - [1.2 追踪挑战](#12-追踪挑战)
  - [2. tokio-tungstenite 追踪](#2-tokio-tungstenite-追踪)
    - [2.1 基础配置](#21-基础配置)
    - [2.2 客户端追踪](#22-客户端追踪)
    - [2.3 服务器追踪](#23-服务器追踪)
  - [3. 连接生命周期追踪](#3-连接生命周期追踪)
    - [3.1 握手阶段](#31-握手阶段)
    - [3.2 消息传输](#32-消息传输)
    - [3.3 关闭连接](#33-关闭连接)
  - [4. 双向流追踪](#4-双向流追踪)
    - [4.1 Ping/Pong 追踪](#41-pingpong-追踪)
    - [4.2 消息关联](#42-消息关联)
  - [5. 语义约定](#5-语义约定)
    - [5.1 Span 命名](#51-span-命名)
    - [5.2 标准属性](#52-标准属性)
    - [5.3 自定义属性](#53-自定义属性)
  - [6. Axum WebSocket 集成](#6-axum-websocket-集成)
    - [6.1 服务器实现](#61-服务器实现)
    - [6.2 消息处理追踪](#62-消息处理追踪)
  - [7. warp WebSocket 集成](#7-warp-websocket-集成)
    - [7.1 服务器配置](#71-服务器配置)
    - [7.2 过滤器追踪](#72-过滤器追踪)
  - [8. 错误处理](#8-错误处理)
    - [8.1 连接错误](#81-连接错误)
    - [8.2 协议错误](#82-协议错误)
  - [9. 性能优化](#9-性能优化)
    - [9.1 采样策略](#91-采样策略)
    - [9.2 批量处理](#92-批量处理)
  - [10. 监控与指标](#10-监控与指标)
    - [10.1 连接指标](#101-连接指标)
    - [10.2 消息指标](#102-消息指标)
  - [11. 完整示例](#11-完整示例)
    - [11.1 聊天服务器](#111-聊天服务器)
    - [11.2 实时通知系统](#112-实时通知系统)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [WebSocket 属性对比](#websocket-属性对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. WebSocket 概述

### 1.1 协议特点

````text
WebSocket 特点:

1. 全双工通信
   - 客户端和服务器可同时发送消息
   - 实时双向数据流

2. 持久连接
   - 连接建立后保持开放
   - 减少握手开销

3. 低延迟
   - 无需 HTTP 头部
   - 直接传输数据帧

4. 事件驱动
   - onopen, onmessage, onclose, onerror

5. 应用场景
   - 聊天应用
   - 实时通知
   - 协作编辑
   - 游戏服务器
   - 金融行情
````

### 1.2 追踪挑战

````text
WebSocket 追踪难点:

1. 长连接追踪
   - 单个连接可能持续数小时
   - 需要合理划分 Span

2. 双向流
   - 客户端和服务器同时发送消息
   - 需要关联请求/响应

3. 异步消息
   - 消息顺序不确定
   - 需要消息 ID 关联

4. 高频消息
   - 每秒可能数千条消息
   - 需要采样避免性能影响

解决方案:
- 握手阶段创建一个 Span
- 每条消息创建独立 Span
- 使用消息 ID 关联上下文
- 采样策略降低开销
````

---

## 2. tokio-tungstenite 追踪

### 2.1 基础配置

````toml
[dependencies]
tokio = { version = "1.47", features = ["full"] }
tokio-tungstenite = "0.24"
tracing = "0.1.41"
tracing-subscriber = "0.3.19"
tracing-opentelemetry = "0.28.0"
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = "0.24.0"
````

### 2.2 客户端追踪

````rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use tracing::{info, instrument, warn};
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry::global;

#[instrument(name = "ws_client_connect", skip(url))]
pub async fn connect_websocket(url: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 创建连接 Span
    let tracer = global::tracer("websocket-client");
    let mut span = tracer.start("ws.handshake");
    
    span.set_attribute(opentelemetry::KeyValue::new("ws.url", url.to_string()));
    span.set_attribute(opentelemetry::KeyValue::new("ws.protocol", "ws"));
    
    info!(url = %url, "Connecting to WebSocket");
    
    // 建立连接
    let (ws_stream, response) = connect_async(url).await?;
    
    span.set_attribute(opentelemetry::KeyValue::new(
        "http.status_code",
        response.status().as_u16() as i64,
    ));
    
    info!(status_code = response.status().as_u16(), "WebSocket connected");
    drop(span);
    
    // 分离读写流
    let (write, read) = ws_stream.split();
    
    // 处理消息
    tokio::select! {
        _ = handle_read(read) => {},
        _ = handle_write(write) => {},
    }
    
    Ok(())
}

#[instrument(name = "ws_read_messages", skip(read))]
async fn handle_read(
    mut read: futures_util::stream::SplitStream<
        tokio_tungstenite::WebSocketStream<
            tokio_tungstenite::MaybeTlsStream<tokio::net::TcpStream>
        >
    >
) {
    use futures_util::StreamExt;
    
    while let Some(message) = read.next().await {
        match message {
            Ok(msg) => {
                handle_message(msg).await;
            }
            Err(e) => {
                warn!(error = %e, "Error reading message");
                break;
            }
        }
    }
}

#[instrument(name = "ws.receive", skip(msg))]
async fn handle_message(msg: Message) {
    let tracer = global::tracer("websocket-client");
    let mut span = tracer.start("ws.message.receive");
    
    match msg {
        Message::Text(text) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "text"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", text.len() as i64));
            info!(size = text.len(), "Received text message");
        }
        Message::Binary(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "binary"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", data.len() as i64));
            info!(size = data.len(), "Received binary message");
        }
        Message::Ping(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "ping"));
            info!(size = data.len(), "Received ping");
        }
        Message::Pong(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "pong"));
            info!(size = data.len(), "Received pong");
        }
        Message::Close(frame) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "close"));
            if let Some(cf) = frame {
                span.set_attribute(opentelemetry::KeyValue::new("ws.close.code", cf.code.into()));
                span.set_attribute(opentelemetry::KeyValue::new("ws.close.reason", cf.reason.to_string()));
            }
            info!("Received close frame");
        }
        _ => {}
    }
}

#[instrument(name = "ws_write_messages", skip(write))]
async fn handle_write(
    mut write: futures_util::stream::SplitSink<
        tokio_tungstenite::WebSocketStream<
            tokio_tungstenite::MaybeTlsStream<tokio::net::TcpStream>
        >,
        Message
    >
) {
    use futures_util::SinkExt;
    
    // 发送消息示例
    let message = Message::Text("Hello, WebSocket!".to_string());
    send_message(&mut write, message).await.ok();
    
    // 定期发送 Ping
    let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
    loop {
        interval.tick().await;
        if send_message(&mut write, Message::Ping(vec![])).await.is_err() {
            break;
        }
    }
}

#[instrument(name = "ws.send", skip(write, message))]
async fn send_message<S>(
    write: &mut S,
    message: Message,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: futures_util::Sink<Message> + Unpin,
    S::Error: std::error::Error + 'static,
{
    use futures_util::SinkExt;
    
    let tracer = global::tracer("websocket-client");
    let mut span = tracer.start("ws.message.send");
    
    match &message {
        Message::Text(text) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "text"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", text.len() as i64));
        }
        Message::Binary(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "binary"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", data.len() as i64));
        }
        Message::Ping(_) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "ping"));
        }
        _ => {}
    }
    
    write.send(message).await.map_err(|e| e.into())
}
````

### 2.3 服务器追踪

````rust
use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use tracing::{info, instrument, error};

#[instrument(name = "ws_server_start")]
pub async fn start_server(addr: &str) -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind(addr).await?;
    info!(addr = %addr, "WebSocket server listening");
    
    while let Ok((stream, peer_addr)) = listener.accept().await {
        tokio::spawn(handle_connection(stream, peer_addr));
    }
    
    Ok(())
}

#[instrument(name = "ws_handle_connection", skip(stream))]
async fn handle_connection(
    stream: TcpStream,
    peer_addr: std::net::SocketAddr,
) {
    let tracer = global::tracer("websocket-server");
    let mut handshake_span = tracer.start("ws.handshake");
    
    handshake_span.set_attribute(opentelemetry::KeyValue::new(
        "net.peer.ip",
        peer_addr.ip().to_string(),
    ));
    handshake_span.set_attribute(opentelemetry::KeyValue::new(
        "net.peer.port",
        peer_addr.port() as i64,
    ));
    
    info!(peer_addr = %peer_addr, "New WebSocket connection");
    
    // 接受 WebSocket 握手
    let ws_stream = match accept_async(stream).await {
        Ok(ws) => {
            handshake_span.set_attribute(opentelemetry::KeyValue::new("ws.handshake.success", true));
            ws
        }
        Err(e) => {
            handshake_span.set_attribute(opentelemetry::KeyValue::new("ws.handshake.success", false));
            handshake_span.set_attribute(opentelemetry::KeyValue::new("error.type", e.to_string()));
            error!(error = %e, "Failed to accept WebSocket");
            return;
        }
    };
    drop(handshake_span);
    
    // 处理消息
    use futures_util::StreamExt;
    use futures_util::SinkExt;
    
    let (mut write, mut read) = ws_stream.split();
    
    while let Some(message) = read.next().await {
        match message {
            Ok(msg) => {
                if let Err(e) = handle_server_message(&mut write, msg).await {
                    error!(error = %e, "Error handling message");
                    break;
                }
            }
            Err(e) => {
                error!(error = %e, "Error reading message");
                break;
            }
        }
    }
    
    info!(peer_addr = %peer_addr, "WebSocket connection closed");
}

#[instrument(name = "ws_server_handle_message", skip(write, msg))]
async fn handle_server_message<S>(
    write: &mut S,
    msg: Message,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: futures_util::Sink<Message> + Unpin,
    S::Error: std::error::Error + 'static,
{
    let tracer = global::tracer("websocket-server");
    let mut span = tracer.start("ws.message.process");
    
    match msg {
        Message::Text(text) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "text"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", text.len() as i64));
            
            info!(text = %text, "Processing text message");
            
            // 回显消息
            let response = format!("Echo: {}", text);
            write.send(Message::Text(response)).await?;
        }
        Message::Binary(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "binary"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", data.len() as i64));
            
            // 回显二进制数据
            write.send(Message::Binary(data)).await?;
        }
        Message::Ping(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "ping"));
            write.send(Message::Pong(data)).await?;
        }
        Message::Close(frame) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "close"));
            if let Some(cf) = frame {
                span.set_attribute(opentelemetry::KeyValue::new("ws.close.code", cf.code.into()));
            }
            write.send(Message::Close(None)).await?;
        }
        _ => {}
    }
    
    Ok(())
}
````

---

## 3. 连接生命周期追踪

### 3.1 握手阶段

````rust
#[instrument(name = "ws.handshake", skip(request))]
async fn trace_handshake(
    request: &http::Request<()>,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.handshake");
    
    // 记录请求信息
    span.set_attribute(opentelemetry::KeyValue::new(
        "http.method",
        request.method().to_string(),
    ));
    span.set_attribute(opentelemetry::KeyValue::new(
        "http.url",
        request.uri().to_string(),
    ));
    
    // 记录 WebSocket 协议头
    if let Some(upgrade) = request.headers().get("Upgrade") {
        span.set_attribute(opentelemetry::KeyValue::new(
            "ws.upgrade",
            upgrade.to_str().unwrap_or("").to_string(),
        ));
    }
    
    if let Some(protocol) = request.headers().get("Sec-WebSocket-Protocol") {
        span.set_attribute(opentelemetry::KeyValue::new(
            "ws.protocol",
            protocol.to_str().unwrap_or("").to_string(),
        ));
    }
    
    Ok(())
}
````

### 3.2 消息传输

````rust
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct MessageTracker {
    pub message_id: AtomicU64,
}

impl MessageTracker {
    pub fn new() -> Self {
        Self {
            message_id: AtomicU64::new(0),
        }
    }
    
    pub fn next_id(&self) -> u64 {
        self.message_id.fetch_add(1, Ordering::SeqCst)
    }
}

#[instrument(name = "ws.message", skip(tracker, message))]
async fn trace_message(
    tracker: Arc<MessageTracker>,
    message: &Message,
) {
    let message_id = tracker.next_id();
    
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.message");
    
    span.set_attribute(opentelemetry::KeyValue::new("ws.message.id", message_id as i64));
    span.set_attribute(opentelemetry::KeyValue::new(
        "ws.message.timestamp",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64,
    ));
    
    match message {
        Message::Text(text) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "text"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", text.len() as i64));
        }
        Message::Binary(data) => {
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.type", "binary"));
            span.set_attribute(opentelemetry::KeyValue::new("ws.message.size", data.len() as i64));
        }
        _ => {}
    }
}
````

### 3.3 关闭连接

````rust
#[instrument(name = "ws.close")]
async fn trace_close(
    close_frame: Option<tokio_tungstenite::tungstenite::protocol::CloseFrame<'static>>,
) {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.close");
    
    if let Some(frame) = close_frame {
        span.set_attribute(opentelemetry::KeyValue::new(
            "ws.close.code",
            u16::from(frame.code) as i64,
        ));
        span.set_attribute(opentelemetry::KeyValue::new(
            "ws.close.reason",
            frame.reason.to_string(),
        ));
        
        info!(
            code = u16::from(frame.code),
            reason = %frame.reason,
            "WebSocket closing"
        );
    }
}
````

---

## 4. 双向流追踪

### 4.1 Ping/Pong 追踪

````rust
#[instrument(name = "ws.ping")]
async fn trace_ping() {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.ping");
    
    span.set_attribute(opentelemetry::KeyValue::new(
        "ws.ping.timestamp",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64,
    ));
}

#[instrument(name = "ws.pong")]
async fn trace_pong(ping_timestamp: i64) {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.pong");
    
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as i64;
    
    let latency = now - ping_timestamp;
    
    span.set_attribute(opentelemetry::KeyValue::new("ws.pong.latency", latency));
    
    info!(latency_ms = latency, "Pong received");
}
````

### 4.2 消息关联

````rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct TracedMessage {
    pub id: String,
    pub trace_id: String,
    pub span_id: String,
    pub payload: String,
}

#[instrument(name = "ws.send_with_context", skip(write, payload))]
async fn send_with_trace_context<S>(
    write: &mut S,
    payload: String,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: futures_util::Sink<Message> + Unpin,
    S::Error: std::error::Error + 'static,
{
    use futures_util::SinkExt;
    use opentelemetry::trace::TraceContextExt;
    
    let context = opentelemetry::Context::current();
    let span_context = context.span().span_context();
    
    let traced_msg = TracedMessage {
        id: uuid::Uuid::new_v4().to_string(),
        trace_id: span_context.trace_id().to_string(),
        span_id: span_context.span_id().to_string(),
        payload,
    };
    
    let json = serde_json::to_string(&traced_msg)?;
    write.send(Message::Text(json)).await?;
    
    Ok(())
}

#[instrument(name = "ws.receive_with_context", skip(message))]
async fn receive_with_trace_context(
    message: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let traced_msg: TracedMessage = serde_json::from_str(&message)?;
    
    // 恢复 Trace 上下文
    let trace_id = opentelemetry::trace::TraceId::from_hex(&traced_msg.trace_id)?;
    let span_id = opentelemetry::trace::SpanId::from_hex(&traced_msg.span_id)?;
    
    let span_context = opentelemetry::trace::SpanContext::new(
        trace_id,
        span_id,
        opentelemetry::trace::TraceFlags::SAMPLED,
        false,
        opentelemetry::trace::TraceState::default(),
    );
    
    let context = opentelemetry::Context::current().with_remote_span_context(span_context);
    
    // 在恢复的上下文中处理消息
    let _guard = context.attach();
    
    info!(
        message_id = %traced_msg.id,
        trace_id = %traced_msg.trace_id,
        "Processing message with trace context"
    );
    
    Ok(())
}
````

---

## 5. 语义约定

### 5.1 Span 命名

````text
WebSocket Span 命名规范:

1. 握手: ws.handshake
2. 发送消息: ws.send
3. 接收消息: ws.receive
4. Ping: ws.ping
5. Pong: ws.pong
6. 关闭: ws.close

示例:
- ws.handshake
- ws.send {message_type}
- ws.receive text
- ws.ping
````

### 5.2 标准属性

````rust
// WebSocket 标准属性
pub const WS_URL: &str = "ws.url";                    // ws://example.com/chat
pub const WS_PROTOCOL: &str = "ws.protocol";          // ws, wss
pub const WS_MESSAGE_TYPE: &str = "ws.message.type";  // text, binary, ping, pong, close
pub const WS_MESSAGE_SIZE: &str = "ws.message.size";  // 字节数
pub const WS_MESSAGE_ID: &str = "ws.message.id";      // 消息 ID
pub const WS_CLOSE_CODE: &str = "ws.close.code";      // 1000, 1001, etc.
pub const WS_CLOSE_REASON: &str = "ws.close.reason";  // 关闭原因
pub const WS_CONNECTION_ID: &str = "ws.connection.id"; // 连接 ID
pub const WS_PEER_IP: &str = "net.peer.ip";           // 对端 IP
pub const WS_PEER_PORT: &str = "net.peer.port";       // 对端端口
````

### 5.3 自定义属性

````rust
#[instrument(name = "ws.custom_attributes")]
async fn add_custom_attributes() {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.message");
    
    // 业务相关属性
    span.set_attribute(opentelemetry::KeyValue::new("user.id", 12345));
    span.set_attribute(opentelemetry::KeyValue::new("room.id", "chat-room-1"));
    span.set_attribute(opentelemetry::KeyValue::new("message.priority", "high"));
    
    // 性能相关属性
    span.set_attribute(opentelemetry::KeyValue::new("ws.queue.size", 42));
    span.set_attribute(opentelemetry::KeyValue::new("ws.processing.time_ms", 15));
}
````

---

## 6. Axum WebSocket 集成

### 6.1 服务器实现

````rust
use axum::{
    extract::{ws::{WebSocket, WebSocketUpgrade}, State},
    response::Response,
    routing::get,
    Router,
};
use tracing::{info, instrument};

pub fn websocket_routes() -> Router {
    Router::new()
        .route("/ws", get(ws_handler))
}

#[instrument(name = "ws.upgrade", skip(ws))]
async fn ws_handler(ws: WebSocketUpgrade) -> Response {
    info!("WebSocket upgrade requested");
    ws.on_upgrade(handle_socket)
}

#[instrument(name = "ws.connection", skip(socket))]
async fn handle_socket(mut socket: WebSocket) {
    let connection_id = uuid::Uuid::new_v4();
    
    info!(connection_id = %connection_id, "New WebSocket connection");
    
    while let Some(msg) = socket.recv().await {
        match msg {
            Ok(msg) => {
                if let Err(e) = handle_axum_message(&mut socket, msg, connection_id).await {
                    tracing::error!(error = %e, "Error handling message");
                    break;
                }
            }
            Err(e) => {
                tracing::error!(error = %e, "Error receiving message");
                break;
            }
        }
    }
    
    info!(connection_id = %connection_id, "WebSocket connection closed");
}

#[instrument(name = "ws.message", skip(socket, msg))]
async fn handle_axum_message(
    socket: &mut WebSocket,
    msg: axum::extract::ws::Message,
    connection_id: uuid::Uuid,
) -> Result<(), Box<dyn std::error::Error>> {
    use axum::extract::ws::Message;
    
    match msg {
        Message::Text(text) => {
            info!(
                connection_id = %connection_id,
                size = text.len(),
                "Received text message"
            );
            
            // 回显消息
            socket.send(Message::Text(format!("Echo: {}", text))).await?;
        }
        Message::Binary(data) => {
            info!(
                connection_id = %connection_id,
                size = data.len(),
                "Received binary message"
            );
            
            socket.send(Message::Binary(data)).await?;
        }
        Message::Ping(data) => {
            socket.send(Message::Pong(data)).await?;
        }
        Message::Close(_) => {
            info!(connection_id = %connection_id, "Client closed connection");
        }
        _ => {}
    }
    
    Ok(())
}
````

### 6.2 消息处理追踪

````rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

pub struct ConnectionManager {
    connections: Arc<RwLock<HashMap<uuid::Uuid, Arc<RwLock<WebSocket>>>>>,
}

impl ConnectionManager {
    pub fn new() -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    #[instrument(name = "ws.broadcast", skip(self, message))]
    pub async fn broadcast(&self, message: String) -> Result<(), Box<dyn std::error::Error>> {
        let connections = self.connections.read().await;
        
        info!(connection_count = connections.len(), "Broadcasting message");
        
        for (id, socket) in connections.iter() {
            let mut socket = socket.write().await;
            if let Err(e) = socket.send(axum::extract::ws::Message::Text(message.clone())).await {
                tracing::error!(connection_id = %id, error = %e, "Failed to send message");
            }
        }
        
        Ok(())
    }
}
````

---

## 7. warp WebSocket 集成

### 7.1 服务器配置

````rust
use warp::Filter;
use warp::ws::{WebSocket, Message};
use tracing::{info, instrument};

pub fn websocket_route() -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
    warp::path("ws")
        .and(warp::ws())
        .map(|ws: warp::ws::Ws| {
            ws.on_upgrade(handle_warp_socket)
        })
}

#[instrument(name = "ws.connection", skip(ws))]
async fn handle_warp_socket(ws: WebSocket) {
    use futures_util::StreamExt;
    use futures_util::SinkExt;
    
    let (mut tx, mut rx) = ws.split();
    
    while let Some(result) = rx.next().await {
        match result {
            Ok(msg) => {
                if let Err(e) = handle_warp_message(&mut tx, msg).await {
                    tracing::error!(error = %e, "Error handling message");
                    break;
                }
            }
            Err(e) => {
                tracing::error!(error = %e, "WebSocket error");
                break;
            }
        }
    }
}

#[instrument(name = "ws.message", skip(tx, msg))]
async fn handle_warp_message<S>(
    tx: &mut S,
    msg: Message,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: futures_util::Sink<Message> + Unpin,
    S::Error: std::error::Error + 'static,
{
    use futures_util::SinkExt;
    
    if msg.is_text() {
        let text = msg.to_str()?;
        info!(size = text.len(), "Received text message");
        
        tx.send(Message::text(format!("Echo: {}", text))).await?;
    } else if msg.is_binary() {
        let data = msg.as_bytes();
        info!(size = data.len(), "Received binary message");
        
        tx.send(Message::binary(data)).await?;
    }
    
    Ok(())
}
````

### 7.2 过滤器追踪

````rust
use warp::Filter;

pub fn with_tracing() -> impl Filter<Extract = (), Error = std::convert::Infallible> + Clone {
    warp::any().map(|| {
        let tracer = global::tracer("warp-websocket");
        let span = tracer.start("ws.request");
        
        // 在请求上下文中附加 Span
        tracing::Span::current().record("trace_id", &span.span_context().trace_id().to_string());
    })
}

pub fn websocket_with_tracing() -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
    with_tracing()
        .and(warp::path("ws"))
        .and(warp::ws())
        .map(|ws: warp::ws::Ws| {
            ws.on_upgrade(handle_warp_socket)
        })
}
````

---

## 8. 错误处理

### 8.1 连接错误

````rust
#[instrument(name = "ws.error", skip(error))]
async fn handle_connection_error(error: tokio_tungstenite::tungstenite::Error) {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.error");
    
    span.set_attribute(opentelemetry::KeyValue::new("error.type", error.to_string()));
    
    match error {
        tokio_tungstenite::tungstenite::Error::ConnectionClosed => {
            span.set_attribute(opentelemetry::KeyValue::new("error.category", "connection_closed"));
            tracing::warn!("Connection closed");
        }
        tokio_tungstenite::tungstenite::Error::AlreadyClosed => {
            span.set_attribute(opentelemetry::KeyValue::new("error.category", "already_closed"));
            tracing::warn!("Connection already closed");
        }
        tokio_tungstenite::tungstenite::Error::Io(e) => {
            span.set_attribute(opentelemetry::KeyValue::new("error.category", "io"));
            span.set_attribute(opentelemetry::KeyValue::new("error.message", e.to_string()));
            tracing::error!(error = %e, "IO error");
        }
        _ => {
            span.set_attribute(opentelemetry::KeyValue::new("error.category", "other"));
            tracing::error!(error = %error, "WebSocket error");
        }
    }
}
````

### 8.2 协议错误

````rust
#[instrument(name = "ws.protocol_error")]
async fn handle_protocol_error(error: &str) {
    let tracer = global::tracer("websocket");
    let mut span = tracer.start("ws.protocol_error");
    
    span.set_attribute(opentelemetry::KeyValue::new("error.message", error.to_string()));
    span.set_attribute(opentelemetry::KeyValue::new("error.severity", "high"));
    
    tracing::error!(error = %error, "Protocol error");
}
````

---

## 9. 性能优化

### 9.1 采样策略

````rust
use opentelemetry_sdk::trace::Sampler;

pub fn create_websocket_sampler() -> Sampler {
    // WebSocket 消息频繁，采样 1%
    Sampler::TraceIdRatioBased(0.01)
}
````

### 9.2 批量处理

````rust
#[instrument(name = "ws.batch_send", skip(socket, messages))]
async fn batch_send(
    socket: &mut WebSocket,
    messages: Vec<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!(message_count = messages.len(), "Batch sending messages");
    
    for message in messages {
        socket.send(axum::extract::ws::Message::Text(message)).await?;
    }
    
    Ok(())
}
````

---

## 10. 监控与指标

### 10.1 连接指标

````rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct WebSocketMetrics {
    pub connections_total: Counter<u64>,
    pub messages_sent: Counter<u64>,
    pub messages_received: Counter<u64>,
    pub message_size: Histogram<u64>,
}

impl WebSocketMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("websocket");
        
        Self {
            connections_total: meter
                .u64_counter("ws.connections.total")
                .with_description("Total WebSocket connections")
                .build(),
            messages_sent: meter
                .u64_counter("ws.messages.sent")
                .with_description("Total messages sent")
                .build(),
            messages_received: meter
                .u64_counter("ws.messages.received")
                .with_description("Total messages received")
                .build(),
            message_size: meter
                .u64_histogram("ws.message.size")
                .with_description("Message size distribution")
                .build(),
        }
    }
}
````

### 10.2 消息指标

````rust
#[instrument(name = "ws.record_metrics", skip(metrics, message))]
async fn record_message_metrics(
    metrics: &WebSocketMetrics,
    message: &Message,
    direction: &str,
) {
    match direction {
        "send" => metrics.messages_sent.add(1, &[]),
        "receive" => metrics.messages_received.add(1, &[]),
        _ => {}
    }
    
    let size = match message {
        Message::Text(text) => text.len() as u64,
        Message::Binary(data) => data.len() as u64,
        _ => 0,
    };
    
    metrics.message_size.record(size, &[]);
}
````

---

## 11. 完整示例

### 11.1 聊天服务器

````rust
use axum::{Router, extract::{ws::WebSocketUpgrade, State}, response::Response};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Clone)]
pub struct ChatRoom {
    connections: Arc<RwLock<HashMap<Uuid, Arc<tokio::sync::Mutex<axum::extract::ws::WebSocket>>>>>,
}

impl ChatRoom {
    pub fn new() -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    #[instrument(name = "chat.broadcast", skip(self, message))]
    pub async fn broadcast(&self, sender_id: Uuid, message: String) {
        let connections = self.connections.read().await;
        
        for (id, socket) in connections.iter() {
            if *id != sender_id {
                let mut socket = socket.lock().await;
                let _ = socket.send(axum::extract::ws::Message::Text(message.clone())).await;
            }
        }
    }
}

pub fn chat_routes(room: ChatRoom) -> Router {
    Router::new()
        .route("/chat", axum::routing::get(chat_handler))
        .with_state(room)
}

#[instrument(name = "chat.connect", skip(ws, room))]
async fn chat_handler(
    ws: WebSocketUpgrade,
    State(room): State<ChatRoom>,
) -> Response {
    ws.on_upgrade(move |socket| handle_chat_socket(socket, room))
}

#[instrument(name = "chat.session", skip(socket, room))]
async fn handle_chat_socket(mut socket: axum::extract::ws::WebSocket, room: ChatRoom) {
    let user_id = Uuid::new_v4();
    info!(user_id = %user_id, "User joined chat");
    
    // 添加连接
    room.connections.write().await.insert(user_id, Arc::new(tokio::sync::Mutex::new(socket)));
    
    // 通知其他用户
    room.broadcast(user_id, format!("User {} joined", user_id)).await;
}
````

### 11.2 实时通知系统

````rust
#[derive(Clone)]
pub struct NotificationService {
    subscribers: Arc<RwLock<HashMap<u64, Vec<Arc<tokio::sync::Mutex<axum::extract::ws::WebSocket>>>>>>,
}

impl NotificationService {
    pub fn new() -> Self {
        Self {
            subscribers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    #[instrument(name = "notification.send", skip(self, notification))]
    pub async fn send_notification(&self, user_id: u64, notification: String) {
        let subscribers = self.subscribers.read().await;
        
        if let Some(sockets) = subscribers.get(&user_id) {
            for socket in sockets.iter() {
                let mut socket = socket.lock().await;
                let _ = socket.send(axum::extract::ws::Message::Text(notification.clone())).await;
            }
        }
    }
}
````

---

## 总结

### 核心要点

1. **tokio-tungstenite**: Rust 主流 WebSocket 库
2. **双向追踪**: 客户端和服务器消息都需追踪
3. **消息关联**: 使用消息 ID 关联请求/响应
4. **采样策略**: WebSocket 消息频繁，建议 1% 采样
5. **语义约定**: 标准属性 (ws.message.type, ws.message.size)
6. **框架集成**: Axum/Warp WebSocket 支持
7. **性能监控**: 连接数、消息数、消息大小指标

### WebSocket 属性对比

| 属性 | 说明 | 示例值 |
|------|------|--------|
| ws.url | WebSocket URL | ws://localhost:8080/chat |
| ws.protocol | 协议 | ws, wss |
| ws.message.type | 消息类型 | text, binary, ping, pong |
| ws.message.size | 消息大小 (字节) | 1024 |
| ws.message.id | 消息 ID | uuid |
| ws.close.code | 关闭代码 | 1000, 1001 |
| ws.connection.id | 连接 ID | uuid |
| net.peer.ip | 对端 IP | 192.168.1.100 |

### 最佳实践清单

- ✅ 握手阶段创建独立 Span
- ✅ 每条消息创建独立 Span
- ✅ 使用消息 ID 关联上下文
- ✅ 传播 TraceId/SpanId (JSON 消息)
- ✅ 采样策略 (1% - 10%)
- ✅ 记录标准属性 (type, size, id)
- ✅ Ping/Pong 追踪延迟
- ✅ 错误处理和分类
- ✅ 连接池指标监控
- ✅ 批量发送优化
- ✅ 异步消息处理
- ✅ 连接生命周期管理

---

**相关文档**:

- [HTTP 追踪](./02_追踪属性/01_HTTP_Rust完整版.md)
- [gRPC 追踪](./02_追踪属性/02_gRPC_Rust完整版.md)
- [性能优化](../../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
- [性能测试](../../05_采样与性能/03_性能测试_Rust完整版.md)
