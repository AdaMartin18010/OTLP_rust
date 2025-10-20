# 通信协议通用属性 - Rust 完整实现

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月10日

---

## 目录

- [通信协议通用属性 - Rust 完整实现](#通信协议通用属性---rust-完整实现)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是通信协议通用属性](#11-什么是通信协议通用属性)
    - [1.2 Rust 实现优势](#12-rust-实现优势)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 语义约定常量](#23-语义约定常量)
  - [3. 网络传输属性](#3-网络传输属性)
    - [3.1 传输协议枚举](#31-传输协议枚举)
    - [3.2 Socket 协议族](#32-socket-协议族)
    - [3.3 传输属性结构体](#33-传输属性结构体)
  - [4. 协议标识属性](#4-协议标识属性)
    - [4.1 应用层协议](#41-应用层协议)
    - [4.2 协议属性结构体](#42-协议属性结构体)
  - [5. 连接属性](#5-连接属性)
    - [5.1 对等点（Peer）属性](#51-对等点peer属性)
    - [5.2 主机（Host）属性](#52-主机host属性)
    - [5.3 Socket 详细属性](#53-socket-详细属性)
  - [6. 完整协议属性建造者](#6-完整协议属性建造者)
  - [7. 完整示例](#7-完整示例)
    - [7.1 HTTP 客户端](#71-http-客户端)
    - [7.2 数据库连接](#72-数据库连接)
    - [7.3 消息队列（Kafka）](#73-消息队列kafka)
    - [7.4 gRPC 客户端](#74-grpc-客户端)
    - [7.5 Redis 客户端](#75-redis-客户端)
  - [8. 协议特定扩展](#8-协议特定扩展)
    - [8.1 HTTP 协议扩展](#81-http-协议扩展)
    - [8.2 数据库协议扩展](#82-数据库协议扩展)
    - [8.3 消息队列扩展](#83-消息队列扩展)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 属性选择策略](#91-属性选择策略)
    - [9.2 性能优化](#92-性能优化)
    - [9.3 安全考虑](#93-安全考虑)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [Rust Crates](#rust-crates)

---

## 1. 概述

### 1.1 什么是通信协议通用属性

**通信协议通用属性**定义了适用于所有网络通信协议的标准化属性，包括HTTP、gRPC、数据库、消息队列等。

**核心原则**:

```text
✅ 协议无关性 - 适用于所有通信协议
✅ 层次化设计 - 从传输层到应用层
✅ 向后兼容性 - 保持稳定的API
✅ Rust 类型安全 - 编译期保证正确性
```

### 1.2 Rust 实现优势

```rust
// Rust 通信协议属性的优势
// ✅ 强类型协议枚举
// ✅ 零成本抽象
// ✅ 编译期协议验证
// ✅ 所有权系统保证线程安全
// ✅ 异步原生支持
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "protocol-attributes-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 网络
tokio = { version = "1", features = ["full"] }
reqwest = "0.12"

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
```

### 2.2 核心导入

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status},
    KeyValue,
};
use std::net::{IpAddr, SocketAddr};
```

### 2.3 语义约定常量

```rust
pub mod network_conventions {
    // 传输层属性
    pub const NET_TRANSPORT: &str = "net.transport";
    pub const NET_SOCK_FAMILY: &str = "net.sock.family";
    
    // 协议层属性
    pub const NET_PROTOCOL_NAME: &str = "net.protocol.name";
    pub const NET_PROTOCOL_VERSION: &str = "net.protocol.version";
    
    // 对等点属性（逻辑层）
    pub const NET_PEER_NAME: &str = "net.peer.name";
    pub const NET_PEER_PORT: &str = "net.peer.port";
    pub const NET_PEER_IP: &str = "net.peer.ip";
    
    // 主机属性（逻辑层）
    pub const NET_HOST_NAME: &str = "net.host.name";
    pub const NET_HOST_PORT: &str = "net.host.port";
    pub const NET_HOST_IP: &str = "net.host.ip";
    
    // Socket 属性（物理层）
    pub const NET_SOCK_PEER_ADDR: &str = "net.sock.peer.addr";
    pub const NET_SOCK_PEER_PORT: &str = "net.sock.peer.port";
    pub const NET_SOCK_PEER_NAME: &str = "net.sock.peer.name";
    pub const NET_SOCK_HOST_ADDR: &str = "net.sock.host.addr";
    pub const NET_SOCK_HOST_PORT: &str = "net.sock.host.port";
}
```

---

## 3. 网络传输属性

### 3.1 传输协议枚举

```rust
/// 网络传输协议
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetTransport {
    /// TCP over IP (最常用)
    IpTcp,
    /// UDP over IP
    IpUdp,
    /// Named or anonymous pipe
    Pipe,
    /// 进程内通信
    Inproc,
    /// Unix Domain Socket
    Unix,
    /// 其他传输方式
    Other,
}

impl NetTransport {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::IpTcp => "ip_tcp",
            Self::IpUdp => "ip_udp",
            Self::Pipe => "pipe",
            Self::Inproc => "inproc",
            Self::Unix => "unix",
            Self::Other => "other",
        }
    }
}

impl std::fmt::Display for NetTransport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
```

### 3.2 Socket 协议族

```rust
/// Socket 协议族
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SockFamily {
    /// IPv4
    Inet,
    /// IPv6
    Inet6,
    /// Unix Domain Socket
    Unix,
}

impl SockFamily {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Inet => "inet",
            Self::Inet6 => "inet6",
            Self::Unix => "unix",
        }
    }
    
    /// 从 IpAddr 自动推断
    pub fn from_ip_addr(addr: &IpAddr) -> Self {
        match addr {
            IpAddr::V4(_) => Self::Inet,
            IpAddr::V6(_) => Self::Inet6,
        }
    }
}
```

### 3.3 传输属性结构体

```rust
/// 网络传输层属性
#[derive(Debug, Clone)]
pub struct TransportAttributes {
    pub transport: NetTransport,
    pub sock_family: Option<SockFamily>,
}

impl TransportAttributes {
    /// 创建 TCP 传输
    pub fn tcp() -> Self {
        Self {
            transport: NetTransport::IpTcp,
            sock_family: Some(SockFamily::Inet),
        }
    }
    
    /// 创建 UDP 传输
    pub fn udp() -> Self {
        Self {
            transport: NetTransport::IpUdp,
            sock_family: Some(SockFamily::Inet),
        }
    }
    
    /// 创建 Unix Domain Socket 传输
    pub fn unix() -> Self {
        Self {
            transport: NetTransport::Unix,
            sock_family: Some(SockFamily::Unix),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(
                network_conventions::NET_TRANSPORT,
                self.transport.as_str(),
            ),
        ];
        
        if let Some(family) = self.sock_family {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_FAMILY,
                family.as_str(),
            ));
        }
        
        attrs
    }
}
```

---

## 4. 协议标识属性

### 4.1 应用层协议

```rust
/// 应用层协议
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApplicationProtocol {
    Http,
    Https,
    Grpc,
    Amqp,
    Mqtt,
    Redis,
    Mysql,
    Postgresql,
    MongoDB,
    Kafka,
    Custom(String),
}

impl ApplicationProtocol {
    pub fn name(&self) -> &str {
        match self {
            Self::Http | Self::Https => "http",
            Self::Grpc => "grpc",
            Self::Amqp => "amqp",
            Self::Mqtt => "mqtt",
            Self::Redis => "redis",
            Self::Mysql => "mysql",
            Self::Postgresql => "postgresql",
            Self::MongoDB => "mongodb",
            Self::Kafka => "kafka",
            Self::Custom(name) => name,
        }
    }
    
    /// 默认端口
    pub fn default_port(&self) -> Option<u16> {
        match self {
            Self::Http => Some(80),
            Self::Https => Some(443),
            Self::Grpc => Some(50051),
            Self::Amqp => Some(5672),
            Self::Mqtt => Some(1883),
            Self::Redis => Some(6379),
            Self::Mysql => Some(3306),
            Self::Postgresql => Some(5432),
            Self::MongoDB => Some(27017),
            Self::Kafka => Some(9092),
            Self::Custom(_) => None,
        }
    }
}
```

### 4.2 协议属性结构体

```rust
/// 应用层协议属性
#[derive(Debug, Clone)]
pub struct ProtocolAttributes {
    pub protocol: ApplicationProtocol,
    pub version: Option<String>,
}

impl ProtocolAttributes {
    /// 创建协议属性
    pub fn new(protocol: ApplicationProtocol) -> Self {
        Self {
            protocol,
            version: None,
        }
    }
    
    /// 添加版本
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }
    
    /// HTTP/1.1
    pub fn http_1_1() -> Self {
        Self::new(ApplicationProtocol::Http).with_version("1.1")
    }
    
    /// HTTP/2
    pub fn http_2() -> Self {
        Self::new(ApplicationProtocol::Http).with_version("2.0")
    }
    
    /// HTTP/3
    pub fn http_3() -> Self {
        Self::new(ApplicationProtocol::Http).with_version("3.0")
    }
    
    /// gRPC
    pub fn grpc() -> Self {
        Self::new(ApplicationProtocol::Grpc)
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(
                network_conventions::NET_PROTOCOL_NAME,
                self.protocol.name().to_string(),
            ),
        ];
        
        if let Some(ref version) = self.version {
            attrs.push(KeyValue::new(
                network_conventions::NET_PROTOCOL_VERSION,
                version.clone(),
            ));
        }
        
        attrs
    }
}
```

---

## 5. 连接属性

### 5.1 对等点（Peer）属性

```rust
/// 对等点属性 - 用于 CLIENT Span
#[derive(Debug, Clone)]
pub struct PeerAttributes {
    /// DNS 名称或域名
    pub name: Option<String>,
    /// 端口
    pub port: Option<u16>,
    /// IP 地址
    pub ip: Option<IpAddr>,
}

impl PeerAttributes {
    /// 创建对等点属性
    pub fn new(name: impl Into<String>, port: u16) -> Self {
        Self {
            name: Some(name.into()),
            port: Some(port),
            ip: None,
        }
    }
    
    /// 添加 IP 地址
    pub fn with_ip(mut self, ip: IpAddr) -> Self {
        self.ip = Some(ip);
        self
    }
    
    /// 从 URL 解析
    pub fn from_url(url: &str) -> anyhow::Result<Self> {
        let parsed = url::Url::parse(url)?;
        let host = parsed.host_str()
            .ok_or_else(|| anyhow::anyhow!("No host in URL"))?;
        let port = parsed.port()
            .or_else(|| match parsed.scheme() {
                "http" => Some(80),
                "https" => Some(443),
                _ => None,
            });
        
        Ok(Self {
            name: Some(host.to_string()),
            port,
            ip: None,
        })
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Some(ref name) = self.name {
            attrs.push(KeyValue::new(
                network_conventions::NET_PEER_NAME,
                name.clone(),
            ));
        }
        
        if let Some(port) = self.port {
            attrs.push(KeyValue::new(
                network_conventions::NET_PEER_PORT,
                port as i64,
            ));
        }
        
        if let Some(ip) = self.ip {
            attrs.push(KeyValue::new(
                network_conventions::NET_PEER_IP,
                ip.to_string(),
            ));
        }
        
        attrs
    }
}
```

### 5.2 主机（Host）属性

```rust
/// 主机属性 - 用于 SERVER Span
#[derive(Debug, Clone)]
pub struct HostAttributes {
    /// 主机名
    pub name: Option<String>,
    /// 监听端口
    pub port: Option<u16>,
    /// IP 地址
    pub ip: Option<IpAddr>,
}

impl HostAttributes {
    /// 创建主机属性
    pub fn new(port: u16) -> Self {
        Self {
            name: hostname::get().ok()
                .and_then(|h| h.into_string().ok()),
            port: Some(port),
            ip: None,
        }
    }
    
    /// 从 SocketAddr 创建
    pub fn from_socket_addr(addr: SocketAddr) -> Self {
        Self {
            name: None,
            port: Some(addr.port()),
            ip: Some(addr.ip()),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Some(ref name) = self.name {
            attrs.push(KeyValue::new(
                network_conventions::NET_HOST_NAME,
                name.clone(),
            ));
        }
        
        if let Some(port) = self.port {
            attrs.push(KeyValue::new(
                network_conventions::NET_HOST_PORT,
                port as i64,
            ));
        }
        
        if let Some(ip) = self.ip {
            attrs.push(KeyValue::new(
                network_conventions::NET_HOST_IP,
                ip.to_string(),
            ));
        }
        
        attrs
    }
}
```

### 5.3 Socket 详细属性

```rust
/// Socket 级别连接属性（物理层）
#[derive(Debug, Clone)]
pub struct SocketAttributes {
    pub peer_addr: Option<IpAddr>,
    pub peer_port: Option<u16>,
    pub peer_name: Option<String>,
    pub host_addr: Option<IpAddr>,
    pub host_port: Option<u16>,
}

impl SocketAttributes {
    /// 从 SocketAddr 创建
    pub fn from_addrs(peer: SocketAddr, host: SocketAddr) -> Self {
        Self {
            peer_addr: Some(peer.ip()),
            peer_port: Some(peer.port()),
            peer_name: None,
            host_addr: Some(host.ip()),
            host_port: Some(host.port()),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Some(addr) = self.peer_addr {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_PEER_ADDR,
                addr.to_string(),
            ));
        }
        
        if let Some(port) = self.peer_port {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_PEER_PORT,
                port as i64,
            ));
        }
        
        if let Some(ref name) = self.peer_name {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_PEER_NAME,
                name.clone(),
            ));
        }
        
        if let Some(addr) = self.host_addr {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_HOST_ADDR,
                addr.to_string(),
            ));
        }
        
        if let Some(port) = self.host_port {
            attrs.push(KeyValue::new(
                network_conventions::NET_SOCK_HOST_PORT,
                port as i64,
            ));
        }
        
        attrs
    }
}
```

---

## 6. 完整协议属性建造者

```rust
/// 完整的网络协议属性建造者
#[derive(Debug, Clone)]
pub struct NetworkAttributesBuilder {
    transport: Option<TransportAttributes>,
    protocol: Option<ProtocolAttributes>,
    peer: Option<PeerAttributes>,
    host: Option<HostAttributes>,
    socket: Option<SocketAttributes>,
}

impl NetworkAttributesBuilder {
    pub fn new() -> Self {
        Self {
            transport: None,
            protocol: None,
            peer: None,
            host: None,
            socket: None,
        }
    }
    
    /// 设置传输层
    pub fn transport(mut self, transport: TransportAttributes) -> Self {
        self.transport = Some(transport);
        self
    }
    
    /// 设置协议层
    pub fn protocol(mut self, protocol: ProtocolAttributes) -> Self {
        self.protocol = Some(protocol);
        self
    }
    
    /// 设置对等点
    pub fn peer(mut self, peer: PeerAttributes) -> Self {
        self.peer = Some(peer);
        self
    }
    
    /// 设置主机
    pub fn host(mut self, host: HostAttributes) -> Self {
        self.host = Some(host);
        self
    }
    
    /// 设置 Socket 属性
    pub fn socket(mut self, socket: SocketAttributes) -> Self {
        self.socket = Some(socket);
        self
    }
    
    /// 构建最终属性数组
    pub fn build(self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Some(transport) = self.transport {
            attrs.extend(transport.to_key_values());
        }
        
        if let Some(protocol) = self.protocol {
            attrs.extend(protocol.to_key_values());
        }
        
        if let Some(peer) = self.peer {
            attrs.extend(peer.to_key_values());
        }
        
        if let Some(host) = self.host {
            attrs.extend(host.to_key_values());
        }
        
        if let Some(socket) = self.socket {
            attrs.extend(socket.to_key_values());
        }
        
        attrs
    }
}
```

---

## 7. 完整示例

### 7.1 HTTP 客户端

```rust
use reqwest::Client;

pub async fn http_client_with_attributes(url: &str) -> anyhow::Result<()> {
    let tracer = global::tracer("http-client");
    
    let mut span = tracer
        .span_builder("http_request")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 构建网络属性
    let peer = PeerAttributes::from_url(url)?;
    
    let network_attrs = NetworkAttributesBuilder::new()
        .transport(TransportAttributes::tcp())
        .protocol(ProtocolAttributes::http_1_1())
        .peer(peer)
        .build();
    
    span.set_attributes(network_attrs);
    
    // HTTP 特定属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.url", url));
    
    // 执行请求
    let client = Client::new();
    let response = client.get(url).send().await?;
    
    span.set_attribute(KeyValue::new(
        "http.status_code",
        response.status().as_u16() as i64,
    ));
    
    span.set_status(Status::Ok);
    span.end();
    
    Ok(())
}
```

### 7.2 数据库连接

```rust
use sqlx::PgPool;

pub async fn database_query_with_attributes(pool: &PgPool) -> anyhow::Result<()> {
    let tracer = global::tracer("database");
    
    let mut span = tracer
        .span_builder("db_query")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 构建网络属性
    let network_attrs = NetworkAttributesBuilder::new()
        .transport(TransportAttributes::tcp())
        .protocol(ProtocolAttributes::new(ApplicationProtocol::Postgresql)
            .with_version("14.0"))
        .peer(PeerAttributes::new("postgres.example.com", 5432))
        .build();
    
    span.set_attributes(network_attrs);
    
    // 数据库特定属性
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.name", "myapp"));
    span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    
    // 执行查询
    let rows = sqlx::query("SELECT * FROM users")
        .fetch_all(pool)
        .await?;
    
    span.set_attribute(KeyValue::new("db.rows_returned", rows.len() as i64));
    span.set_status(Status::Ok);
    span.end();
    
    Ok(())
}
```

### 7.3 消息队列（Kafka）

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;

pub async fn kafka_producer_with_attributes() -> anyhow::Result<()> {
    let tracer = global::tracer("kafka-producer");
    
    let mut span = tracer
        .span_builder("kafka_produce")
        .with_kind(SpanKind::Producer)
        .start(&tracer);
    
    // 构建网络属性
    let network_attrs = NetworkAttributesBuilder::new()
        .transport(TransportAttributes::tcp())
        .protocol(ProtocolAttributes::new(ApplicationProtocol::Kafka))
        .peer(PeerAttributes::new("kafka.example.com", 9092))
        .build();
    
    span.set_attributes(network_attrs);
    
    // Kafka 特定属性
    span.set_attribute(KeyValue::new("messaging.system", "kafka"));
    span.set_attribute(KeyValue::new("messaging.destination", "user-events"));
    span.set_attribute(KeyValue::new("messaging.destination_kind", "topic"));
    
    // 创建生产者
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "kafka.example.com:9092")
        .create()?;
    
    // 发送消息
    let record = FutureRecord::to("user-events")
        .key("user-123")
        .payload("User created");
    
    let (partition, offset) = producer
        .send(record, std::time::Duration::from_secs(5))
        .await
        .map_err(|(e, _)| e)?;
    
    span.set_attribute(KeyValue::new("messaging.kafka.partition", partition));
    span.set_attribute(KeyValue::new("messaging.kafka.offset", offset));
    
    span.set_status(Status::Ok);
    span.end();
    
    Ok(())
}
```

### 7.4 gRPC 客户端

```rust
pub async fn grpc_client_with_attributes() -> anyhow::Result<()> {
    let tracer = global::tracer("grpc-client");
    
    let mut span = tracer
        .span_builder("grpc_call")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 构建网络属性
    let network_attrs = NetworkAttributesBuilder::new()
        .transport(TransportAttributes::tcp())
        .protocol(ProtocolAttributes::grpc())
        .peer(PeerAttributes::new("grpc.example.com", 50051))
        .build();
    
    span.set_attributes(network_attrs);
    
    // gRPC 特定属性
    span.set_attribute(KeyValue::new("rpc.system", "grpc"));
    span.set_attribute(KeyValue::new("rpc.service", "UserService"));
    span.set_attribute(KeyValue::new("rpc.method", "GetUser"));
    
    // 执行 gRPC 调用
    // ... gRPC client code ...
    
    span.set_status(Status::Ok);
    span.end();
    
    Ok(())
}
```

### 7.5 Redis 客户端

```rust
use redis::AsyncCommands;

pub async fn redis_client_with_attributes() -> anyhow::Result<()> {
    let tracer = global::tracer("redis-client");
    
    let mut span = tracer
        .span_builder("redis_get")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 构建网络属性
    let network_attrs = NetworkAttributesBuilder::new()
        .transport(TransportAttributes::tcp())
        .protocol(ProtocolAttributes::new(ApplicationProtocol::Redis)
            .with_version("7.0"))
        .peer(PeerAttributes::new("redis.example.com", 6379))
        .build();
    
    span.set_attributes(network_attrs);
    
    // Redis 特定属性
    span.set_attribute(KeyValue::new("db.system", "redis"));
    span.set_attribute(KeyValue::new("db.statement", "GET user:123"));
    span.set_attribute(KeyValue::new("db.operation", "GET"));
    
    // 执行 Redis 操作
    let client = redis::Client::open("redis://redis.example.com/")?;
    let mut con = client.get_async_connection().await?;
    let value: String = con.get("user:123").await?;
    
    span.set_status(Status::Ok);
    span.end();
    
    Ok(())
}
```

---

## 8. 协议特定扩展

### 8.1 HTTP 协议扩展

```rust
/// HTTP 协议扩展属性
pub struct HttpProtocolExtension {
    pub method: String,
    pub url: String,
    pub status_code: Option<u16>,
    pub request_content_length: Option<i64>,
    pub response_content_length: Option<i64>,
}

impl HttpProtocolExtension {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("http.method", self.method.clone()),
            KeyValue::new("http.url", self.url.clone()),
        ];
        
        if let Some(status) = self.status_code {
            attrs.push(KeyValue::new("http.status_code", status as i64));
        }
        
        if let Some(len) = self.request_content_length {
            attrs.push(KeyValue::new("http.request_content_length", len));
        }
        
        if let Some(len) = self.response_content_length {
            attrs.push(KeyValue::new("http.response_content_length", len));
        }
        
        attrs
    }
}
```

### 8.2 数据库协议扩展

```rust
/// 数据库协议扩展属性
pub struct DatabaseProtocolExtension {
    pub system: String,
    pub name: String,
    pub statement: String,
    pub operation: String,
    pub user: Option<String>,
}

impl DatabaseProtocolExtension {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("db.system", self.system.clone()),
            KeyValue::new("db.name", self.name.clone()),
            KeyValue::new("db.statement", self.statement.clone()),
            KeyValue::new("db.operation", self.operation.clone()),
        ];
        
        if let Some(ref user) = self.user {
            attrs.push(KeyValue::new("db.user", user.clone()));
        }
        
        attrs
    }
}
```

### 8.3 消息队列扩展

```rust
/// 消息队列协议扩展属性
pub struct MessagingProtocolExtension {
    pub system: String,
    pub destination: String,
    pub destination_kind: String,
    pub message_id: Option<String>,
    pub conversation_id: Option<String>,
}

impl MessagingProtocolExtension {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", self.system.clone()),
            KeyValue::new("messaging.destination", self.destination.clone()),
            KeyValue::new("messaging.destination_kind", self.destination_kind.clone()),
        ];
        
        if let Some(ref id) = self.message_id {
            attrs.push(KeyValue::new("messaging.message_id", id.clone()));
        }
        
        if let Some(ref id) = self.conversation_id {
            attrs.push(KeyValue::new("messaging.conversation_id", id.clone()));
        }
        
        attrs
    }
}
```

---

## 9. 最佳实践

### 9.1 属性选择策略

```rust
pub mod best_practices {
    /// 属性选择决策树
    pub fn select_attributes(scenario: &str) -> &'static str {
        match scenario {
            // 1. 简单 HTTP 调用
            "simple_http" => {
                "使用: transport + protocol + peer"
            }
            
            // 2. 负载均衡场景
            "load_balanced" => {
                "使用: transport + protocol + peer (逻辑) + socket (物理)"
            }
            
            // 3. 服务器端
            "server" => {
                "使用: transport + protocol + host + client IP"
            }
            
            _ => "默认: transport + protocol + peer",
        }
    }
}
```

### 9.2 性能优化

```rust
use once_cell::sync::Lazy;

/// 缓存常用协议属性
pub mod performance {
    use super::*;
    
    /// 缓存 HTTP/1.1 属性
    static HTTP_1_1_ATTRS: Lazy<Vec<KeyValue>> = Lazy::new(|| {
        ProtocolAttributes::http_1_1().to_key_values()
    });
    
    /// 缓存 TCP 传输属性
    static TCP_TRANSPORT_ATTRS: Lazy<Vec<KeyValue>> = Lazy::new(|| {
        TransportAttributes::tcp().to_key_values()
    });
    
    pub fn get_http_1_1_attrs() -> Vec<KeyValue> {
        HTTP_1_1_ATTRS.clone()
    }
    
    pub fn get_tcp_transport_attrs() -> Vec<KeyValue> {
        TCP_TRANSPORT_ATTRS.clone()
    }
}
```

### 9.3 安全考虑

```rust
pub mod security {
    use super::*;
    
    /// 清理敏感的 URL 参数
    pub fn sanitize_url(url: &str) -> String {
        if let Ok(mut parsed) = url::Url::parse(url) {
            // 移除密码
            let _ = parsed.set_password(None);
            
            // 清理查询参数中的敏感信息
            let cleaned_query: Vec<_> = parsed
                .query_pairs()
                .filter(|(key, _)| {
                    !key.contains("password") 
                    && !key.contains("token")
                    && !key.contains("secret")
                })
                .map(|(k, v)| (k.into_owned(), v.into_owned()))
                .collect();
            
            let query_string = serde_urlencoded::to_string(&cleaned_query)
                .unwrap_or_default();
            parsed.set_query(Some(&query_string));
            
            parsed.to_string()
        } else {
            url.to_string()
        }
    }
    
    /// 清理数据库语句中的敏感信息
    pub fn sanitize_db_statement(statement: &str) -> String {
        // 替换 VALUES 子句中的值为占位符
        statement
            .replace("password", "***")
            .replace("PASSWORD", "***")
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Semantic Conventions - General**: <https://opentelemetry.io/docs/specs/semconv/general/>
2. **OpenTelemetry Semantic Conventions - Network**: <https://opentelemetry.io/docs/specs/semconv/general/attributes/#network-attributes>
3. **OpenTelemetry Rust SDK**: <https://github.com/open-telemetry/opentelemetry-rust>

### 相关规范

1. **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
2. **HTTP Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/http/>
3. **Database Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/database/>
4. **Messaging Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/messaging/>

### Rust Crates

1. **reqwest**: <https://github.com/seanmonstar/reqwest>
2. **tokio**: <https://tokio.rs/>
3. **sqlx**: <https://github.com/launchbadge/sqlx>
4. **redis**: <https://github.com/redis-rs/redis-rs>
5. **rdkafka**: <https://github.com/fede1024/rust-rdkafka>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
