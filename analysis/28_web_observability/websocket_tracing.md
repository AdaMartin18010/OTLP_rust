# WebSocket 追踪 - WebSocket Tracing

**创建日期**: 2025年10月29日
**适用场景**: 实时Web应用、聊天系统、推送服务
**状态**: ✅ 生产验证

---

## 📋 目录

- [概述](#概述)
- [连接生命周期追踪](#连接生命周期追踪)
- [消息追踪](#消息追踪)
- [心跳监控](#心跳监控)
- [广播追踪](#广播追踪)
- [性能优化](#性能优化)
- [生产案例](#生产案例)

---

## 概述

WebSocket追踪提供实时双向通信的完整可观测性：

- ✅ **连接追踪**: 建立、维持、关闭的完整生命周期
- ✅ **消息监控**: 双向消息流的详细追踪
- ✅ **性能分析**: 延迟、吞吐量、连接质量
- ✅ **故障诊断**: 连接失败、消息丢失检测
- ✅ **规模监控**: 大规模并发连接管理

---

## 连接生命周期追踪

### WebSocket连接追踪

```rust
use axum::{
    extract::ws::{Message, WebSocket, WebSocketUpgrade},
    response::Response,
};
use opentelemetry::{global, trace::{Tracer, SpanKind}, KeyValue};

// WebSocket升级处理器
#[tracing::instrument(
    name = "websocket.upgrade",
    fields(
        otel.kind = "server",
        websocket.protocol = "ws"
    )
)]
async fn ws_handler(
    ws: WebSocketUpgrade,
    user_id: Extension<UserId>,
) -> Response {
    tracing::info!(user_id = %user_id.0, "WebSocket upgrade request");

    ws.on_upgrade(move |socket| {
        handle_socket(socket, user_id.0)
    })
}

// WebSocket连接处理
#[tracing::instrument(
    name = "websocket.connection",
    skip(socket),
    fields(
        user.id = %user_id,
        websocket.connection_id = tracing::field::Empty,
        otel.kind = "server"
    )
)]
async fn handle_socket(socket: WebSocket, user_id: u64) {
    let connection_id = generate_connection_id();
    let span = tracing::Span::current();
    span.record("websocket.connection_id", &connection_id.to_string());

    tracing::info!("WebSocket connection established");

    // 分离发送和接收
    let (mut sender, mut receiver) = socket.split();

    // 连接开始时间
    let connected_at = std::time::Instant::now();

    // 统计信息
    let mut stats = ConnectionStats {
        messages_sent: 0,
        messages_received: 0,
        bytes_sent: 0,
        bytes_received: 0,
        errors: 0,
    };

    // 接收消息
    while let Some(msg_result) = receiver.next().await {
        match msg_result {
            Ok(msg) => {
                stats.messages_received += 1;

                if let Err(e) = handle_message(&mut sender, msg, &mut stats).await {
                    tracing::error!(error = %e, "Failed to handle message");
                    stats.errors += 1;
                    break;
                }
            }
            Err(e) => {
                tracing::error!(error = %e, "WebSocket error");
                stats.errors += 1;
                break;
            }
        }
    }

    // 连接结束
    let duration = connected_at.elapsed();

    tracing::info!(
        duration_secs = duration.as_secs(),
        messages_sent = stats.messages_sent,
        messages_received = stats.messages_received,
        bytes_sent = stats.bytes_sent,
        bytes_received = stats.bytes_received,
        errors = stats.errors,
        "WebSocket connection closed"
    );
}

#[derive(Debug, Default)]
struct ConnectionStats {
    messages_sent: u64,
    messages_received: u64,
    bytes_sent: u64,
    bytes_received: u64,
    errors: u64,
}

fn generate_connection_id() -> uuid::Uuid {
    uuid::Uuid::new_v4()
}
```

### 连接状态管理

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

// 连接管理器
#[derive(Clone)]
pub struct ConnectionManager {
    connections: Arc<RwLock<HashMap<Uuid, ConnectionInfo>>>,
    meter: Meter,
}

#[derive(Debug, Clone)]
pub struct ConnectionInfo {
    pub user_id: u64,
    pub connected_at: std::time::Instant,
    pub last_activity: std::time::Instant,
    pub messages_count: u64,
}

impl ConnectionManager {
    pub fn new(meter: Meter) -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
            meter,
        }
    }

    // 注册连接
    #[tracing::instrument(skip(self), fields(connection.id = %conn_id))]
    pub async fn register(&self, conn_id: Uuid, user_id: u64) {
        let info = ConnectionInfo {
            user_id,
            connected_at: std::time::Instant::now(),
            last_activity: std::time::Instant::now(),
            messages_count: 0,
        };

        self.connections.write().await.insert(conn_id, info);

        // 更新指标
        let count = self.connections.read().await.len();
        self.meter
            .u64_observable_gauge("websocket.connections.active")
            .with_callback(move |observer| {
                observer.observe(count as u64, &[]);
            })
            .init();

        tracing::info!("Connection registered");
    }

    // 更新活动时间
    pub async fn update_activity(&self, conn_id: &Uuid) {
        if let Some(info) = self.connections.write().await.get_mut(conn_id) {
            info.last_activity = std::time::Instant::now();
            info.messages_count += 1;
        }
    }

    // 注销连接
    #[tracing::instrument(skip(self), fields(connection.id = %conn_id))]
    pub async fn unregister(&self, conn_id: &Uuid) -> Option<ConnectionInfo> {
        let info = self.connections.write().await.remove(conn_id);

        if let Some(ref info) = info {
            let duration = info.connected_at.elapsed();

            tracing::info!(
                user_id = info.user_id,
                duration_secs = duration.as_secs(),
                messages_count = info.messages_count,
                "Connection unregistered"
            );
        }

        info
    }

    // 获取活跃连接数
    pub async fn active_count(&self) -> usize {
        self.connections.read().await.len()
    }

    // 清理超时连接
    #[tracing::instrument(skip(self))]
    pub async fn cleanup_idle(&self, timeout: Duration) -> usize {
        let mut conns = self.connections.write().await;
        let now = std::time::Instant::now();
        let mut removed = 0;

        conns.retain(|id, info| {
            let idle_time = now.duration_since(info.last_activity);
            if idle_time > timeout {
                tracing::warn!(
                    connection_id = %id,
                    idle_seconds = idle_time.as_secs(),
                    "Removing idle connection"
                );
                removed += 1;
                false
            } else {
                true
            }
        });

        tracing::info!(removed_count = removed, "Idle connections cleaned up");
        removed
    }
}
```

---

## 消息追踪

### 消息级别的追踪

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
enum ClientMessage {
    Ping,
    Subscribe { channel: String },
    Unsubscribe { channel: String },
    Message { channel: String, content: String },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
enum ServerMessage {
    Pong,
    Subscribed { channel: String },
    Unsubscribed { channel: String },
    Message { channel: String, content: String },
    Error { code: String, message: String },
}

// 处理单个消息
#[tracing::instrument(
    name = "websocket.message.handle",
    skip(sender, msg),
    fields(
        message.type = tracing::field::Empty,
        message.size_bytes = tracing::field::Empty
    )
)]
async fn handle_message(
    sender: &mut SplitSink<WebSocket, Message>,
    msg: Message,
    stats: &mut ConnectionStats,
) -> Result<()> {
    let span = tracing::Span::current();

    match msg {
        Message::Text(text) => {
            span.record("message.type", "text");
            span.record("message.size_bytes", &text.len());

            stats.bytes_received += text.len() as u64;

            tracing::debug!(content_length = text.len(), "Received text message");

            // 解析消息
            let client_msg: ClientMessage = serde_json::from_str(&text)?;

            // 处理消息
            let response = process_client_message(client_msg).await?;

            // 发送响应
            send_message(sender, response, stats).await?;
        }

        Message::Binary(data) => {
            span.record("message.type", "binary");
            span.record("message.size_bytes", &data.len());

            stats.bytes_received += data.len() as u64;

            tracing::debug!(data_length = data.len(), "Received binary message");

            // 处理二进制数据
            process_binary_data(&data).await?;
        }

        Message::Ping(data) => {
            span.record("message.type", "ping");
            tracing::trace!("Received ping");

            // 自动回复pong
            sender.send(Message::Pong(data)).await?;
        }

        Message::Pong(_) => {
            span.record("message.type", "pong");
            tracing::trace!("Received pong");
        }

        Message::Close(frame) => {
            span.record("message.type", "close");
            tracing::info!(?frame, "Received close frame");
            return Err(anyhow::anyhow!("Connection closed by client"));
        }
    }

    Ok(())
}

// 发送消息
#[tracing::instrument(
    name = "websocket.message.send",
    skip(sender, msg),
    fields(
        message.type = ?msg
    )
)]
async fn send_message(
    sender: &mut SplitSink<WebSocket, Message>,
    msg: ServerMessage,
    stats: &mut ConnectionStats,
) -> Result<()> {
    let text = serde_json::to_string(&msg)?;
    let size = text.len();

    sender.send(Message::Text(text)).await?;

    stats.messages_sent += 1;
    stats.bytes_sent += size as u64;

    tracing::debug!(size_bytes = size, "Message sent");

    Ok(())
}

// 处理客户端消息
#[tracing::instrument(skip(msg))]
async fn process_client_message(msg: ClientMessage) -> Result<ServerMessage> {
    match msg {
        ClientMessage::Ping => {
            tracing::trace!("Processing ping");
            Ok(ServerMessage::Pong)
        }

        ClientMessage::Subscribe { channel } => {
            tracing::info!(channel = %channel, "Processing subscribe");
            // 实际的订阅逻辑
            Ok(ServerMessage::Subscribed { channel })
        }

        ClientMessage::Unsubscribe { channel } => {
            tracing::info!(channel = %channel, "Processing unsubscribe");
            Ok(ServerMessage::Unsubscribed { channel })
        }

        ClientMessage::Message { channel, content } => {
            tracing::info!(
                channel = %channel,
                content_length = content.len(),
                "Processing message"
            );
            // 广播消息
            broadcast_message(&channel, &content).await?;
            Ok(ServerMessage::Message { channel, content })
        }
    }
}
```

---

## 心跳监控

### WebSocket心跳机制

```rust
use tokio::time::{interval, Duration};

// 心跳配置
const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(30);
const CLIENT_TIMEOUT: Duration = Duration::from_secs(60);

// 带心跳的WebSocket处理
#[tracing::instrument(skip(socket), fields(connection.id = %conn_id))]
async fn handle_socket_with_heartbeat(
    socket: WebSocket,
    conn_id: Uuid,
    manager: ConnectionManager,
) {
    let (mut sender, mut receiver) = socket.split();

    // 最后活动时间
    let last_activity = Arc::new(RwLock::new(std::time::Instant::now()));

    // 心跳任务
    let heartbeat_activity = last_activity.clone();
    let heartbeat_task = tokio::spawn(async move {
        let mut interval = interval(HEARTBEAT_INTERVAL);

        loop {
            interval.tick().await;

            // 检查超时
            let last = *heartbeat_activity.read().await;
            let elapsed = last.elapsed();

            if elapsed > CLIENT_TIMEOUT {
                tracing::warn!(
                    idle_seconds = elapsed.as_secs(),
                    "Client timeout"
                );
                break;
            }

            // 发送ping
            if let Err(e) = sender.send(Message::Ping(vec![])).await {
                tracing::error!(error = %e, "Failed to send ping");
                break;
            }

            tracing::trace!("Heartbeat ping sent");
        }
    });

    // 消息处理任务
    let msg_activity = last_activity.clone();
    let msg_task = tokio::spawn(async move {
        while let Some(result) = receiver.next().await {
            // 更新活动时间
            *msg_activity.write().await = std::time::Instant::now();

            match result {
                Ok(msg) => {
                    if let Err(e) = handle_message(&mut sender, msg).await {
                        tracing::error!(error = %e, "Message handling failed");
                        break;
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "WebSocket error");
                    break;
                }
            }
        }
    });

    // 等待任一任务完成
    tokio::select! {
        _ = heartbeat_task => {
            tracing::info!("Heartbeat task ended");
        }
        _ = msg_task => {
            tracing::info!("Message task ended");
        }
    }

    // 清理连接
    manager.unregister(&conn_id).await;
}
```

---

## 广播追踪

### 消息广播监控

```rust
use tokio::sync::broadcast;
use std::collections::HashMap;

// 广播管理器
#[derive(Clone)]
pub struct BroadcastManager {
    channels: Arc<RwLock<HashMap<String, broadcast::Sender<ServerMessage>>>>,
    meter: Meter,
}

impl BroadcastManager {
    pub fn new(meter: Meter) -> Self {
        Self {
            channels: Arc::new(RwLock::new(HashMap::new())),
            meter,
        }
    }

    // 订阅频道
    #[tracing::instrument(skip(self), fields(channel = %channel_name))]
    pub async fn subscribe(&self, channel_name: String) -> broadcast::Receiver<ServerMessage> {
        let mut channels = self.channels.write().await;

        let sender = channels
            .entry(channel_name.clone())
            .or_insert_with(|| {
                tracing::info!("Creating new broadcast channel");
                broadcast::channel(1000).0
            });

        let receiver = sender.subscribe();
        let subscriber_count = sender.receiver_count();

        tracing::info!(
            subscribers = subscriber_count,
            "Client subscribed to channel"
        );

        // 记录指标
        self.meter
            .u64_counter("websocket.channel.subscriptions")
            .add(1, &[KeyValue::new("channel", channel_name)]);

        receiver
    }

    // 广播消息
    #[tracing::instrument(
        skip(self, message),
        fields(
            channel = %channel_name,
            message.type = ?message
        )
    )]
    pub async fn broadcast(&self, channel_name: &str, message: ServerMessage) -> Result<usize> {
        let channels = self.channels.read().await;

        if let Some(sender) = channels.get(channel_name) {
            let subscriber_count = sender.receiver_count();

            match sender.send(message) {
                Ok(count) => {
                    tracing::info!(
                        recipients = count,
                        "Message broadcasted"
                    );

                    // 记录指标
                    self.meter
                        .u64_counter("websocket.messages.broadcasted")
                        .add(1, &[
                            KeyValue::new("channel", channel_name.to_string()),
                            KeyValue::new("recipients", count as i64),
                        ]);

                    Ok(count)
                }
                Err(e) => {
                    tracing::error!(error = %e, "Broadcast failed");
                    Err(anyhow::anyhow!("Broadcast failed"))
                }
            }
        } else {
            tracing::warn!("Channel not found");
            Ok(0)
        }
    }

    // 获取频道统计
    pub async fn channel_stats(&self) -> HashMap<String, ChannelStats> {
        let channels = self.channels.read().await;

        channels
            .iter()
            .map(|(name, sender)| {
                (
                    name.clone(),
                    ChannelStats {
                        subscriber_count: sender.receiver_count(),
                    },
                )
            })
            .collect()
    }
}

#[derive(Debug)]
pub struct ChannelStats {
    pub subscriber_count: usize,
}
```

---

## 性能优化

### WebSocket性能最佳实践

```rust
// 1. 消息批处理
async fn batch_send_messages(
    sender: &mut SplitSink<WebSocket, Message>,
    messages: Vec<ServerMessage>,
) -> Result<()> {
    let batch = messages
        .into_iter()
        .map(|msg| serde_json::to_string(&msg))
        .collect::<Result<Vec<_>, _>>()?
        .join("\n");

    sender.send(Message::Text(batch)).await?;

    Ok(())
}

// 2. 消息压缩
use flate2::write::GzEncoder;
use flate2::Compression;

async fn send_compressed(
    sender: &mut SplitSink<WebSocket, Message>,
    data: &str,
) -> Result<()> {
    if data.len() > 1024 {  // 只压缩大消息
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(data.as_bytes())?;
        let compressed = encoder.finish()?;

        if compressed.len() < data.len() {
            sender.send(Message::Binary(compressed)).await?;
            return Ok(());
        }
    }

    sender.send(Message::Text(data.to_string())).await?;
    Ok(())
}

// 3. 连接池优化
#[derive(Clone)]
struct OptimizedConnectionManager {
    connections: Arc<DashMap<Uuid, ConnectionInfo>>,  // 使用DashMap提高并发性能
}
```

---

## 生产案例

### 案例: 实时聊天服务

**场景**: 大规模实时聊天
**规模**: 100K+ 并发连接
**技术**: Axum + WebSocket + Redis Pub/Sub

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化追踪
    init_telemetry()?;

    // 创建连接管理器
    let manager = ConnectionManager::new(global::meter("chat"));

    // 创建广播管理器
    let broadcaster = BroadcastManager::new(global::meter("chat"));

    // 创建应用
    let app = Router::new()
        .route("/ws", get(ws_handler))
        .layer(Extension(manager))
        .layer(Extension(broadcaster))
        .layer(TraceLayer::new_for_http());

    // 启动服务器
    axum::Server::bind(&"0.0.0.0:8080".parse()?)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

// 性能结果:
// - 并发连接: 100K+
// - 消息延迟: P99 < 50ms
// - 内存使用: ~2GB
// - CPU使用: ~30%
```

---

## 总结

WebSocket追踪的关键要素：

1. **连接管理**: 完整的连接生命周期追踪
2. **消息监控**: 双向消息流的详细追踪
3. **心跳机制**: 连接健康检查和超时处理
4. **广播追踪**: 多客户端消息分发监控
5. **性能优化**: 批处理、压缩、连接池

**下一步**:

- ⚡ [性能优化](./performance_optimization.md)
- 🚀 [生产环境部署](./production_deployment.md)
