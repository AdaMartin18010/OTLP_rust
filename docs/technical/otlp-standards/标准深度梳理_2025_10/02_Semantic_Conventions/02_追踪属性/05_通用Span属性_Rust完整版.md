# Span 通用属性 - Rust 完整实现

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月10日

---

## 目录

- [Span 通用属性 - Rust 完整实现](#span-通用属性---rust-完整实现)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是Span通用属性](#11-什么是span通用属性)
    - [1.2 属性分类](#12-属性分类)
    - [1.3 Rust 实现优势](#13-rust-实现优势)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 属性类型系统](#23-属性类型系统)
  - [3. 网络属性](#3-网络属性)
    - [3.1 传输层属性](#31-传输层属性)
    - [3.2 连接属性](#32-连接属性)
    - [3.3 对等点属性](#33-对等点属性)
    - [3.4 主机属性](#34-主机属性)
  - [4. 错误属性](#4-错误属性)
    - [4.1 错误标记](#41-错误标记)
    - [4.2 异常属性](#42-异常属性)
    - [4.3 Rust 错误处理集成](#43-rust-错误处理集成)
  - [5. 用户与会话属性](#5-用户与会话属性)
    - [5.1 用户标识](#51-用户标识)
    - [5.2 会话标识](#52-会话标识)
  - [6. 线程与代码位置属性](#6-线程与代码位置属性)
    - [6.1 线程信息](#61-线程信息)
    - [6.2 代码位置](#62-代码位置)
  - [7. 对等服务属性](#7-对等服务属性)
  - [8. SpanKind 特定属性](#8-spankind-特定属性)
    - [8.1 CLIENT Span](#81-client-span)
    - [8.2 SERVER Span](#82-server-span)
    - [8.3 PRODUCER Span](#83-producer-span)
    - [8.4 CONSUMER Span](#84-consumer-span)
    - [8.5 INTERNAL Span](#85-internal-span)
  - [9. 类型安全的属性建造者](#9-类型安全的属性建造者)
  - [10. 完整示例](#10-完整示例)
    - [10.1 Rust HTTP 客户端](#101-rust-http-客户端)
    - [10.2 Rust 数据库查询](#102-rust-数据库查询)
    - [10.3 Rust 消息生产者](#103-rust-消息生产者)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 属性选择原则](#111-属性选择原则)
    - [11.2 性能优化](#112-性能优化)
    - [11.3 错误处理](#113-错误处理)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [Rust 资源](#rust-资源)

---

## 1. 概述

### 1.1 什么是Span通用属性

**Span通用属性**是适用于所有或多种类型Span的标准化属性，不依赖于特定的协议、系统或技术栈。

**核心目的**:

```text
✅ 提供跨系统的一致性
✅ 简化查询和分析
✅ 支持自动化告警和监控
✅ 促进工具之间的互操作性
✅ Rust 类型安全保证
```

### 1.2 属性分类

```text
1. 网络属性
   ├─ 传输层 (net.transport, net.protocol.*)
   ├─ 对等点 (net.peer.*)
   └─ 主机 (net.host.*)

2. 错误属性
   ├─ error (布尔标记)
   ├─ exception.* (异常详情)
   └─ error.type (错误类型)

3. 用户与会话属性
   ├─ enduser.* (用户标识)
   └─ session.* (会话信息)

4. 线程与代码位置
   ├─ thread.* (线程信息)
   └─ code.* (代码位置)

5. 对等服务
   └─ peer.service (对等服务名)
```

### 1.3 Rust 实现优势

```rust
// ✅ 编译期类型检查
// ✅ 零成本抽象
// ✅ 所有权系统保证内存安全
// ✅ 强类型属性系统
// ✅ 异步原生支持
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "span-attributes-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 运行时
tokio = { version = "1", features = ["full"] }

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
```

### 2.2 核心导入

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, TraceContextExt},
    KeyValue, Value,
};
use opentelemetry_sdk::trace::TracerProvider;
use std::collections::HashMap;

// 语义约定常量
pub mod semantic_conventions {
    // 网络属性
    pub const NET_TRANSPORT: &str = "net.transport";
    pub const NET_PROTOCOL_NAME: &str = "net.protocol.name";
    pub const NET_PROTOCOL_VERSION: &str = "net.protocol.version";
    pub const NET_SOCK_FAMILY: &str = "net.sock.family";
    
    // 对等点属性
    pub const NET_PEER_NAME: &str = "net.peer.name";
    pub const NET_PEER_PORT: &str = "net.peer.port";
    pub const NET_PEER_IP: &str = "net.peer.ip";
    
    // 主机属性
    pub const NET_HOST_NAME: &str = "net.host.name";
    pub const NET_HOST_PORT: &str = "net.host.port";
    pub const NET_HOST_IP: &str = "net.host.ip";
    
    // 错误属性
    pub const ERROR: &str = "error";
    pub const ERROR_TYPE: &str = "error.type";
    pub const EXCEPTION_TYPE: &str = "exception.type";
    pub const EXCEPTION_MESSAGE: &str = "exception.message";
    pub const EXCEPTION_STACKTRACE: &str = "exception.stacktrace";
    pub const EXCEPTION_ESCAPED: &str = "exception.escaped";
    
    // 用户属性
    pub const ENDUSER_ID: &str = "enduser.id";
    pub const ENDUSER_ROLE: &str = "enduser.role";
    pub const ENDUSER_SCOPE: &str = "enduser.scope";
    
    // 线程属性
    pub const THREAD_ID: &str = "thread.id";
    pub const THREAD_NAME: &str = "thread.name";
    
    // 代码位置
    pub const CODE_FUNCTION: &str = "code.function";
    pub const CODE_NAMESPACE: &str = "code.namespace";
    pub const CODE_FILEPATH: &str = "code.filepath";
    pub const CODE_LINENO: &str = "code.lineno";
    
    // 对等服务
    pub const PEER_SERVICE: &str = "peer.service";
}
```

### 2.3 属性类型系统

```rust
/// 网络传输协议枚举
#[derive(Debug, Clone, Copy)]
pub enum NetTransport {
    IpTcp,
    IpUdp,
    Pipe,
    Inproc,
    Unix,
}

impl NetTransport {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::IpTcp => "ip_tcp",
            Self::IpUdp => "ip_udp",
            Self::Pipe => "pipe",
            Self::Inproc => "inproc",
            Self::Unix => "unix",
        }
    }
}

impl From<NetTransport> for Value {
    fn from(transport: NetTransport) -> Self {
        Value::String(transport.as_str().into())
    }
}

/// Socket 协议族枚举
#[derive(Debug, Clone, Copy)]
pub enum SockFamily {
    Inet,
    Inet6,
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
}
```

---

## 3. 网络属性

### 3.1 传输层属性

```rust
/// 网络传输层属性
pub struct NetworkTransportAttributes {
    pub transport: NetTransport,
    pub protocol_name: Option<String>,
    pub protocol_version: Option<String>,
    pub sock_family: Option<SockFamily>,
}

impl NetworkTransportAttributes {
    /// 创建 TCP 传输属性
    pub fn tcp(protocol_name: &str, protocol_version: &str) -> Self {
        Self {
            transport: NetTransport::IpTcp,
            protocol_name: Some(protocol_name.to_string()),
            protocol_version: Some(protocol_version.to_string()),
            sock_family: Some(SockFamily::Inet),
        }
    }
    
    /// 创建 UDP 传输属性
    pub fn udp() -> Self {
        Self {
            transport: NetTransport::IpUdp,
            protocol_name: None,
            protocol_version: None,
            sock_family: Some(SockFamily::Inet),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                semantic_conventions::NET_TRANSPORT,
                self.transport.as_str(),
            ),
        ];
        
        if let Some(ref name) = self.protocol_name {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_PROTOCOL_NAME,
                name.clone(),
            ));
        }
        
        if let Some(ref version) = self.protocol_version {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_PROTOCOL_VERSION,
                version.clone(),
            ));
        }
        
        if let Some(family) = self.sock_family {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_SOCK_FAMILY,
                family.as_str(),
            ));
        }
        
        attributes
    }
}

// 使用示例
fn example_transport_attributes(span: &mut opentelemetry::trace::BoxedSpan) {
    let transport = NetworkTransportAttributes::tcp("http", "1.1");
    span.set_attributes(transport.to_key_values());
}
```

### 3.2 连接属性

```rust
use std::net::{IpAddr, SocketAddr};

/// Socket 连接属性
pub struct SocketConnectionAttributes {
    pub peer_addr: Option<IpAddr>,
    pub peer_port: Option<u16>,
    pub host_addr: Option<IpAddr>,
    pub host_port: Option<u16>,
}

impl SocketConnectionAttributes {
    /// 从 SocketAddr 创建
    pub fn from_socket_addrs(peer: SocketAddr, host: SocketAddr) -> Self {
        Self {
            peer_addr: Some(peer.ip()),
            peer_port: Some(peer.port()),
            host_addr: Some(host.ip()),
            host_port: Some(host.port()),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        
        if let Some(addr) = self.peer_addr {
            attributes.push(KeyValue::new(
                "net.sock.peer.addr",
                addr.to_string(),
            ));
        }
        
        if let Some(port) = self.peer_port {
            attributes.push(KeyValue::new(
                "net.sock.peer.port",
                port as i64,
            ));
        }
        
        if let Some(addr) = self.host_addr {
            attributes.push(KeyValue::new(
                "net.sock.host.addr",
                addr.to_string(),
            ));
        }
        
        if let Some(port) = self.host_port {
            attributes.push(KeyValue::new(
                "net.sock.host.port",
                port as i64,
            ));
        }
        
        attributes
    }
}
```

### 3.3 对等点属性

```rust
/// 对等点 (Peer) 属性 - 用于 CLIENT Span
pub struct PeerAttributes {
    pub name: Option<String>,
    pub port: Option<u16>,
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
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        
        if let Some(ref name) = self.name {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_PEER_NAME,
                name.clone(),
            ));
        }
        
        if let Some(port) = self.port {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_PEER_PORT,
                port as i64,
            ));
        }
        
        if let Some(ip) = self.ip {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_PEER_IP,
                ip.to_string(),
            ));
        }
        
        attributes
    }
}

// 使用示例
fn example_peer_attributes(span: &mut opentelemetry::trace::BoxedSpan) {
    let peer = PeerAttributes::new("api.example.com", 443)
        .with_ip("203.0.113.42".parse().unwrap());
    
    span.set_attributes(peer.to_key_values());
}
```

### 3.4 主机属性

```rust
/// 主机 (Host) 属性 - 用于 SERVER Span
pub struct HostAttributes {
    pub name: Option<String>,
    pub port: Option<u16>,
    pub ip: Option<IpAddr>,
    pub connection_type: Option<String>,
    pub connection_subtype: Option<String>,
}

impl HostAttributes {
    /// 创建主机属性
    pub fn new(port: u16) -> Self {
        Self {
            name: hostname::get().ok().and_then(|h| h.into_string().ok()),
            port: Some(port),
            ip: None,
            connection_type: None,
            connection_subtype: None,
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        
        if let Some(ref name) = self.name {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_HOST_NAME,
                name.clone(),
            ));
        }
        
        if let Some(port) = self.port {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_HOST_PORT,
                port as i64,
            ));
        }
        
        if let Some(ip) = self.ip {
            attributes.push(KeyValue::new(
                semantic_conventions::NET_HOST_IP,
                ip.to_string(),
            ));
        }
        
        attributes
    }
}
```

---

## 4. 错误属性

### 4.1 错误标记

```rust
/// 设置错误标记 (已废弃，推荐使用 Span Status)
pub fn set_error_flag(span: &mut opentelemetry::trace::BoxedSpan, has_error: bool) {
    span.set_attribute(KeyValue::new(
        semantic_conventions::ERROR,
        has_error,
    ));
}

/// 推荐方式: 使用 Span Status
pub fn set_span_error(span: &mut opentelemetry::trace::BoxedSpan, error: &str) {
    span.set_status(Status::error(error));
}
```

### 4.2 异常属性

```rust
use std::error::Error;
use std::backtrace::Backtrace;

/// 异常属性
pub struct ExceptionAttributes {
    pub exception_type: String,
    pub exception_message: Option<String>,
    pub exception_stacktrace: Option<String>,
    pub exception_escaped: bool,
}

impl ExceptionAttributes {
    /// 从 Rust Error 创建
    pub fn from_error<E: Error>(error: &E, escaped: bool) -> Self {
        Self {
            exception_type: std::any::type_name::<E>().to_string(),
            exception_message: Some(error.to_string()),
            exception_stacktrace: None,
            exception_escaped: escaped,
        }
    }
    
    /// 添加堆栈跟踪
    pub fn with_backtrace(mut self, backtrace: Backtrace) -> Self {
        self.exception_stacktrace = Some(backtrace.to_string());
        self
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                semantic_conventions::EXCEPTION_TYPE,
                self.exception_type.clone(),
            ),
            KeyValue::new(
                semantic_conventions::EXCEPTION_ESCAPED,
                self.exception_escaped,
            ),
        ];
        
        if let Some(ref message) = self.exception_message {
            attributes.push(KeyValue::new(
                semantic_conventions::EXCEPTION_MESSAGE,
                message.clone(),
            ));
        }
        
        if let Some(ref stacktrace) = self.exception_stacktrace {
            attributes.push(KeyValue::new(
                semantic_conventions::EXCEPTION_STACKTRACE,
                stacktrace.clone(),
            ));
        }
        
        attributes
    }
}
```

### 4.3 Rust 错误处理集成

```rust
use anyhow::Result;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

/// Trait 扩展: 自动记录错误到 Span
pub trait SpanErrorExt {
    fn record_error<E: Error>(&mut self, error: &E, escaped: bool);
}

impl SpanErrorExt for opentelemetry::trace::BoxedSpan {
    fn record_error<E: Error>(&mut self, error: &E, escaped: bool) {
        let exception = ExceptionAttributes::from_error(error, escaped);
        
        // 记录异常事件
        self.add_event(
            "exception",
            exception.to_key_values(),
        );
        
        // 设置 Span 状态
        self.set_status(Status::error(error.to_string()));
    }
}

// 使用示例
async fn example_error_handling() -> Result<()> {
    let tracer = global::tracer("example");
    let mut span = tracer
        .span_builder("operation")
        .with_kind(SpanKind::Internal)
        .start(&tracer);
    
    match perform_operation().await {
        Ok(result) => {
            span.set_status(Status::Ok);
            Ok(result)
        }
        Err(e) => {
            span.record_error(&e, false);
            Err(e)
        }
    }
}

async fn perform_operation() -> Result<()> {
    // 业务逻辑
    Ok(())
}
```

---

## 5. 用户与会话属性

### 5.1 用户标识

```rust
/// 用户属性
pub struct EnduserAttributes {
    pub id: String,
    pub role: Option<String>,
    pub scope: Option<String>,
}

impl EnduserAttributes {
    /// 创建用户属性
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            role: None,
            scope: None,
        }
    }
    
    /// 添加角色
    pub fn with_role(mut self, role: impl Into<String>) -> Self {
        self.role = Some(role.into());
        self
    }
    
    /// 添加作用域
    pub fn with_scope(mut self, scope: impl Into<String>) -> Self {
        self.scope = Some(scope.into());
        self
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                semantic_conventions::ENDUSER_ID,
                self.id.clone(),
            ),
        ];
        
        if let Some(ref role) = self.role {
            attributes.push(KeyValue::new(
                semantic_conventions::ENDUSER_ROLE,
                role.clone(),
            ));
        }
        
        if let Some(ref scope) = self.scope {
            attributes.push(KeyValue::new(
                semantic_conventions::ENDUSER_SCOPE,
                scope.clone(),
            ));
        }
        
        attributes
    }
}
```

### 5.2 会话标识

```rust
/// 会话属性
pub struct SessionAttributes {
    pub id: String,
    pub is_previous_session: Option<bool>,
}

impl SessionAttributes {
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            is_previous_session: None,
        }
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new("session.id", self.id.clone()),
        ];
        
        if let Some(is_previous) = self.is_previous_session {
            attributes.push(KeyValue::new(
                "session.previous_id",
                is_previous,
            ));
        }
        
        attributes
    }
}
```

---

## 6. 线程与代码位置属性

### 6.1 线程信息

```rust
use std::thread;

/// 线程属性
pub struct ThreadAttributes {
    pub id: u64,
    pub name: Option<String>,
}

impl ThreadAttributes {
    /// 获取当前线程属性
    pub fn current() -> Self {
        let thread = thread::current();
        Self {
            id: thread_id::get() as u64,
            name: thread.name().map(String::from),
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                semantic_conventions::THREAD_ID,
                self.id as i64,
            ),
        ];
        
        if let Some(ref name) = self.name {
            attributes.push(KeyValue::new(
                semantic_conventions::THREAD_NAME,
                name.clone(),
            ));
        }
        
        attributes
    }
}

// 对于异步任务，使用 Tokio 任务信息
#[cfg(feature = "tokio")]
pub struct TaskAttributes {
    pub task_id: tokio::task::Id,
}

impl TaskAttributes {
    pub fn current() -> Option<Self> {
        tokio::task::try_id().map(|id| Self { task_id: id })
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        vec![
            KeyValue::new("tokio.task.id", self.task_id.to_string()),
        ]
    }
}
```

### 6.2 代码位置

```rust
/// 代码位置属性
pub struct CodeLocationAttributes {
    pub function: String,
    pub namespace: Option<String>,
    pub filepath: Option<String>,
    pub lineno: Option<u32>,
}

impl CodeLocationAttributes {
    /// 创建代码位置属性
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            namespace: None,
            filepath: None,
            lineno: None,
        }
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = vec![
            KeyValue::new(
                semantic_conventions::CODE_FUNCTION,
                self.function.clone(),
            ),
        ];
        
        if let Some(ref namespace) = self.namespace {
            attributes.push(KeyValue::new(
                semantic_conventions::CODE_NAMESPACE,
                namespace.clone(),
            ));
        }
        
        if let Some(ref filepath) = self.filepath {
            attributes.push(KeyValue::new(
                semantic_conventions::CODE_FILEPATH,
                filepath.clone(),
            ));
        }
        
        if let Some(lineno) = self.lineno {
            attributes.push(KeyValue::new(
                semantic_conventions::CODE_LINENO,
                lineno as i64,
            ));
        }
        
        attributes
    }
}

// 宏：自动捕获代码位置
#[macro_export]
macro_rules! code_location {
    () => {
        CodeLocationAttributes {
            function: std::stringify!(function_name!()).to_string(),
            namespace: Some(module_path!().to_string()),
            filepath: Some(file!().to_string()),
            lineno: Some(line!()),
        }
    };
}
```

---

## 7. 对等服务属性

```rust
/// 对等服务属性
pub struct PeerServiceAttribute {
    pub service_name: String,
}

impl PeerServiceAttribute {
    pub fn new(service_name: impl Into<String>) -> Self {
        Self {
            service_name: service_name.into(),
        }
    }
    
    pub fn to_key_value(&self) -> KeyValue {
        KeyValue::new(
            semantic_conventions::PEER_SERVICE,
            self.service_name.clone(),
        )
    }
}
```

---

## 8. SpanKind 特定属性

### 8.1 CLIENT Span

```rust
/// CLIENT Span 完整属性
pub struct ClientSpanAttributes {
    pub peer: PeerAttributes,
    pub transport: NetworkTransportAttributes,
    pub peer_service: Option<PeerServiceAttribute>,
}

impl ClientSpanAttributes {
    pub fn new(peer_name: &str, peer_port: u16) -> Self {
        Self {
            peer: PeerAttributes::new(peer_name, peer_port),
            transport: NetworkTransportAttributes::tcp("http", "1.1"),
            peer_service: None,
        }
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        attributes.extend(self.peer.to_key_values());
        attributes.extend(self.transport.to_key_values());
        
        if let Some(ref service) = self.peer_service {
            attributes.push(service.to_key_value());
        }
        
        attributes
    }
}
```

### 8.2 SERVER Span

```rust
/// SERVER Span 完整属性
pub struct ServerSpanAttributes {
    pub host: HostAttributes,
    pub transport: NetworkTransportAttributes,
    pub client_ip: Option<IpAddr>,
}

impl ServerSpanAttributes {
    pub fn new(port: u16) -> Self {
        Self {
            host: HostAttributes::new(port),
            transport: NetworkTransportAttributes::tcp("http", "1.1"),
            client_ip: None,
        }
    }
    
    pub fn with_client_ip(mut self, ip: IpAddr) -> Self {
        self.client_ip = Some(ip);
        self
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        attributes.extend(self.host.to_key_values());
        attributes.extend(self.transport.to_key_values());
        
        if let Some(ip) = self.client_ip {
            attributes.push(KeyValue::new("client.address", ip.to_string()));
        }
        
        attributes
    }
}
```

### 8.3 PRODUCER Span

```rust
/// PRODUCER Span 属性
pub struct ProducerSpanAttributes {
    pub peer_service: PeerServiceAttribute,
    pub messaging_system: String,
    pub messaging_destination: String,
}

impl ProducerSpanAttributes {
    pub fn new(
        peer_service: &str,
        messaging_system: &str,
        destination: &str,
    ) -> Self {
        Self {
            peer_service: PeerServiceAttribute::new(peer_service),
            messaging_system: messaging_system.to_string(),
            messaging_destination: destination.to_string(),
        }
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        vec![
            self.peer_service.to_key_value(),
            KeyValue::new("messaging.system", self.messaging_system.clone()),
            KeyValue::new("messaging.destination", self.messaging_destination.clone()),
        ]
    }
}
```

### 8.4 CONSUMER Span

```rust
/// CONSUMER Span 属性
pub struct ConsumerSpanAttributes {
    pub peer_service: PeerServiceAttribute,
    pub messaging_system: String,
    pub messaging_source: String,
}

impl ConsumerSpanAttributes {
    pub fn new(
        peer_service: &str,
        messaging_system: &str,
        source: &str,
    ) -> Self {
        Self {
            peer_service: PeerServiceAttribute::new(peer_service),
            messaging_system: messaging_system.to_string(),
            messaging_source: source.to_string(),
        }
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        vec![
            self.peer_service.to_key_value(),
            KeyValue::new("messaging.system", self.messaging_system.clone()),
            KeyValue::new("messaging.source", self.messaging_source.clone()),
        ]
    }
}
```

### 8.5 INTERNAL Span

```rust
/// INTERNAL Span 属性
pub struct InternalSpanAttributes {
    pub thread: ThreadAttributes,
    pub code_location: CodeLocationAttributes,
}

impl InternalSpanAttributes {
    pub fn new(function_name: &str) -> Self {
        Self {
            thread: ThreadAttributes::current(),
            code_location: CodeLocationAttributes::new(function_name),
        }
    }
    
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attributes = Vec::new();
        attributes.extend(self.thread.to_key_values());
        attributes.extend(self.code_location.to_key_values());
        attributes
    }
}
```

---

## 9. 类型安全的属性建造者

```rust
/// 通用 Span 属性建造者
pub struct SpanAttributesBuilder {
    attributes: Vec<KeyValue>,
}

impl SpanAttributesBuilder {
    pub fn new() -> Self {
        Self {
            attributes: Vec::new(),
        }
    }
    
    /// 添加网络传输属性
    pub fn with_transport(mut self, transport: NetworkTransportAttributes) -> Self {
        self.attributes.extend(transport.to_key_values());
        self
    }
    
    /// 添加对等点属性
    pub fn with_peer(mut self, peer: PeerAttributes) -> Self {
        self.attributes.extend(peer.to_key_values());
        self
    }
    
    /// 添加主机属性
    pub fn with_host(mut self, host: HostAttributes) -> Self {
        self.attributes.extend(host.to_key_values());
        self
    }
    
    /// 添加用户属性
    pub fn with_enduser(mut self, enduser: EnduserAttributes) -> Self {
        self.attributes.extend(enduser.to_key_values());
        self
    }
    
    /// 添加线程属性
    pub fn with_thread(mut self, thread: ThreadAttributes) -> Self {
        self.attributes.extend(thread.to_key_values());
        self
    }
    
    /// 添加代码位置
    pub fn with_code_location(mut self, location: CodeLocationAttributes) -> Self {
        self.attributes.extend(location.to_key_values());
        self
    }
    
    /// 添加对等服务
    pub fn with_peer_service(mut self, service: PeerServiceAttribute) -> Self {
        self.attributes.push(service.to_key_value());
        self
    }
    
    /// 构建最终属性数组
    pub fn build(self) -> Vec<KeyValue> {
        self.attributes
    }
}

// 使用示例
fn example_builder() {
    let attributes = SpanAttributesBuilder::new()
        .with_transport(NetworkTransportAttributes::tcp("http", "2.0"))
        .with_peer(PeerAttributes::new("api.example.com", 443))
        .with_enduser(EnduserAttributes::new("user-123").with_role("admin"))
        .with_thread(ThreadAttributes::current())
        .build();
    
    // 应用到 Span
    // span.set_attributes(attributes);
}
```

---

## 10. 完整示例

### 10.1 Rust HTTP 客户端

```rust
use reqwest::Client;
use opentelemetry::global;
use opentelemetry::trace::{Tracer, SpanKind};

async fn http_client_example() -> anyhow::Result<()> {
    let tracer = global::tracer("http-client");
    
    // 创建 CLIENT Span
    let mut span = tracer
        .span_builder("http_request")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 添加通用属性
    let attributes = SpanAttributesBuilder::new()
        .with_transport(NetworkTransportAttributes::tcp("http", "1.1"))
        .with_peer(
            PeerAttributes::new("api.example.com", 443)
                .with_ip("203.0.113.42".parse()?)
        )
        .with_peer_service(PeerServiceAttribute::new("example-api"))
        .build();
    
    span.set_attributes(attributes);
    
    // 添加 HTTP 特定属性
    span.set_attribute(KeyValue::new("http.method", "GET"));
    span.set_attribute(KeyValue::new("http.url", "https://api.example.com/users"));
    
    // 执行 HTTP 请求
    let client = Client::new();
    let result = client
        .get("https://api.example.com/users")
        .send()
        .await;
    
    match result {
        Ok(response) => {
            span.set_attribute(KeyValue::new(
                "http.status_code",
                response.status().as_u16() as i64,
            ));
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err(e) => {
            span.record_error(&e, false);
        }
    }
    
    span.end();
    Ok(())
}
```

### 10.2 Rust 数据库查询

```rust
use sqlx::{PgPool, Row};

async fn database_query_example(pool: &PgPool) -> anyhow::Result<()> {
    let tracer = global::tracer("database");
    
    // 创建 CLIENT Span
    let mut span = tracer
        .span_builder("db_query")
        .with_kind(SpanKind::Client)
        .start(&tracer);
    
    // 添加数据库属性
    let attributes = SpanAttributesBuilder::new()
        .with_peer(PeerAttributes::new("postgres.example.com", 5432))
        .with_peer_service(PeerServiceAttribute::new("postgres"))
        .with_thread(ThreadAttributes::current())
        .build();
    
    span.set_attributes(attributes);
    
    // 数据库特定属性
    span.set_attribute(KeyValue::new("db.system", "postgresql"));
    span.set_attribute(KeyValue::new("db.name", "myapp"));
    span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"));
    span.set_attribute(KeyValue::new("db.operation", "SELECT"));
    
    // 执行查询
    let result = sqlx::query("SELECT * FROM users WHERE id = $1")
        .bind(123)
        .fetch_one(pool)
        .await;
    
    match result {
        Ok(row) => {
            span.set_attribute(KeyValue::new("db.rows_affected", 1));
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err(e) => {
            span.record_error(&e, false);
        }
    }
    
    span.end();
    Ok(())
}
```

### 10.3 Rust 消息生产者

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;

async fn kafka_producer_example() -> anyhow::Result<()> {
    let tracer = global::tracer("kafka-producer");
    
    // 创建 PRODUCER Span
    let mut span = tracer
        .span_builder("kafka_produce")
        .with_kind(SpanKind::Producer)
        .start(&tracer);
    
    // 添加消息队列属性
    let attributes = ProducerSpanAttributes::new(
        "kafka-cluster",
        "kafka",
        "user-events",
    );
    
    span.set_attributes(attributes.to_key_values());
    
    // 额外属性
    span.set_attribute(KeyValue::new("messaging.kafka.partition", 0));
    span.set_attribute(KeyValue::new("messaging.message_id", "msg-123"));
    
    // 创建 Kafka 生产者
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()?;
    
    // 发送消息
    let record = FutureRecord::to("user-events")
        .key("user-123")
        .payload("User created");
    
    let result = producer.send(record, std::time::Duration::from_secs(5)).await;
    
    match result {
        Ok((partition, offset)) => {
            span.set_attribute(KeyValue::new("messaging.kafka.offset", offset));
            span.set_status(opentelemetry::trace::Status::Ok);
        }
        Err((e, _)) => {
            span.record_error(&e, false);
        }
    }
    
    span.end();
    Ok(())
}
```

---

## 11. 最佳实践

### 11.1 属性选择原则

```rust
/// 属性选择指南
pub mod best_practices {
    /// 1. 只添加必要的属性
    /// ❌ 不要添加过多属性，增加存储和网络开销
    pub fn minimal_attributes() {
        // 错误示例：过多冗余属性
        // span.set_attribute(KeyValue::new("redundant.info", "..."));
        
        // ✅ 正确：只添加有价值的属性
        // span.set_attribute(KeyValue::new("http.method", "GET"));
    }
    
    /// 2. 使用标准语义约定
    /// ✅ 优先使用 OpenTelemetry 标准属性名
    pub fn use_semantic_conventions() {
        // ✅ 使用标准属性名
        // span.set_attribute(KeyValue::new("net.peer.name", "example.com"));
        
        // ❌ 避免自定义属性名
        // span.set_attribute(KeyValue::new("custom_peer_name", "example.com"));
    }
    
    /// 3. 避免高基数属性
    /// ⚠️  高基数属性（如用户ID、请求ID）会导致存储爆炸
    pub fn avoid_high_cardinality() {
        // ❌ 避免：用户 ID 作为属性
        // span.set_attribute(KeyValue::new("user.id", unique_user_id));
        
        // ✅ 使用聚合维度
        // span.set_attribute(KeyValue::new("user.tier", "premium"));
    }
}
```

### 11.2 性能优化

```rust
/// 性能优化技巧
pub mod performance {
    use once_cell::sync::Lazy;
    
    /// 1. 缓存常用属性
    static COMMON_ATTRIBUTES: Lazy<Vec<KeyValue>> = Lazy::new(|| {
        vec![
            KeyValue::new("service.name", "my-service"),
            KeyValue::new("service.version", "1.0.0"),
            KeyValue::new("deployment.environment", "production"),
        ]
    });
    
    pub fn use_cached_attributes(span: &mut opentelemetry::trace::BoxedSpan) {
        span.set_attributes(COMMON_ATTRIBUTES.clone());
    }
    
    /// 2. 批量设置属性
    pub fn batch_set_attributes(span: &mut opentelemetry::trace::BoxedSpan) {
        // ✅ 一次设置多个属性
        let attributes = vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "/api/users"),
            KeyValue::new("http.status_code", 200),
        ];
        span.set_attributes(attributes);
        
        // ❌ 避免多次调用
        // span.set_attribute(KeyValue::new("http.method", "GET"));
        // span.set_attribute(KeyValue::new("http.url", "/api/users"));
    }
}
```

### 11.3 错误处理

```rust
/// 错误处理最佳实践
pub mod error_handling {
    use opentelemetry::trace::{Status, BoxedSpan};
    use anyhow::Result;
    
    /// 标准错误处理模式
    pub async fn operation_with_error_handling<F, T>(
        span: &mut BoxedSpan,
        operation: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        match operation.await {
            Ok(result) => {
                span.set_status(Status::Ok);
                Ok(result)
            }
            Err(e) => {
                // 记录异常
                span.record_error(&e, false);
                
                // 添加错误类型
                span.set_attribute(KeyValue::new(
                    "error.type",
                    std::any::type_name_of_val(&e),
                ));
                
                Err(e)
            }
        }
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/>
2. **OpenTelemetry Rust SDK**: <https://github.com/open-telemetry/opentelemetry-rust>
3. **Span Attributes Specification**: <https://opentelemetry.io/docs/specs/otel/trace/api/#set-attributes>

### 相关规范

1. **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
2. **OpenTelemetry Protocol (OTLP)**: <https://github.com/open-telemetry/opentelemetry-proto>

### Rust 资源

1. **Tokio**: <https://tokio.rs/>
2. **Reqwest**: <https://github.com/seanmonstar/reqwest>
3. **SQLx**: <https://github.com/launchbadge/sqlx>
4. **rdkafka**: <https://github.com/fede1024/rust-rdkafka>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
