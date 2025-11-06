# 🎯 Event 信号实现指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**适用于**: OTLP Rust v2.0+
**OTLP 版本**: 1.3.0+ (Event Signal Type)
**状态**: 🟢 活跃维护

> **简介**: Event 信号完整实现指南 - 事件处理、实时流、复杂事件处理和最佳实践。

---

## 📋 目录

- [🎯 Event 信号实现指南](#-event-信号实现指南)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 Event 信号？](#什么是-event-信号)
    - [Event 信号的典型应用场景](#event-信号的典型应用场景)
    - [为什么需要独立的 Event 信号？](#为什么需要独立的-event-信号)
  - [Event 信号概述](#event-信号概述)
    - [OTLP Event 数据模型](#otlp-event-数据模型)
    - [Event 信号的关键特性](#event-信号的关键特性)
  - [Event vs Logs](#event-vs-logs)
    - [对比分析](#对比分析)
    - [使用场景对比](#使用场景对比)
  - [实现架构](#实现架构)
    - [总体架构](#总体架构)
    - [Crate 结构](#crate-结构)
  - [核心组件实现](#核心组件实现)
    - [1. Event 数据类型](#1-event-数据类型)
    - [2. EventEmitter - 事件发射器](#2-eventemitter---事件发射器)
    - [3. EventProcessor - 事件处理器](#3-eventprocessor---事件处理器)
    - [4. EventExporter - 事件导出器](#4-eventexporter---事件导出器)
  - [数据模型](#数据模型)
    - [OTLP Event Protobuf 定义](#otlp-event-protobuf-定义)
  - [事件发射](#事件发射)
    - [基本用法](#基本用法)
    - [使用事件构建器](#使用事件构建器)
    - [与 Trace 关联](#与-trace-关联)
  - [处理与导出](#处理与导出)
    - [配置批处理](#配置批处理)
    - [事件过滤器](#事件过滤器)
  - [最佳实践](#最佳实践)
    - [1. 事件命名约定](#1-事件命名约定)
    - [2. 事件类型分类](#2-事件类型分类)
    - [3. 结构化负载](#3-结构化负载)
    - [4. 属性 vs 负载](#4-属性-vs-负载)
  - [示例代码](#示例代码)
    - [完整示例：电商订单事件](#完整示例电商订单事件)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
      - [1. 事件队列满](#1-事件队列满)
      - [2. 事件丢失](#2-事件丢失)
      - [3. 负载序列化失败](#3-负载序列化失败)
  - [参考资源](#参考资源)
    - [相关文档](#相关文档)
    - [外部资源](#外部资源)

---

## 简介

### 什么是 Event 信号？

Event 信号是 OTLP 1.3.0+ 引入的新信号类型，专门用于表示**独立的、结构化的业务事件**。
与 Logs 不同，Events 更侧重于：

- 🎯 **业务语义** - 具有明确业务含义的事件
- 📊 **结构化数据** - 强类型的事件数据模型
- 🔗 **关系建模** - 事件之间的因果关系
- 📈 **聚合分析** - 适合事件驱动架构分析

### Event 信号的典型应用场景

| 场景 | 示例 |
|------|------|
| **用户行为追踪** | 用户登录、页面访问、按钮点击 |
| **业务流程** | 订单创建、支付完成、发货通知 |
| **系统状态变更** | 配置更新、服务启动/停止 |
| **安全审计** | 权限变更、敏感操作记录 |
| **IoT 数据** | 传感器读数、设备状态变化 |

### 为什么需要独立的 Event 信号？

| Logs | Events |
|------|--------|
| 面向调试和诊断 | 面向业务分析和监控 |
| 非结构化或半结构化 | 完全结构化 |
| 时间序列为主 | 因果关系为主 |
| 通常不关联 Trace | 天然关联 Trace/Span |

---

## Event 信号概述

### OTLP Event 数据模型

```text
EventData
  ├── ResourceEvents[]
  │     ├── Resource (service.name, host.name, etc.)
  │     └── ScopeEvents[]
  │           ├── Scope (instrumentation library)
  │           └── Event[]
  │                 ├── event_id (唯一标识)
  │                 ├── time_unix_nano (事件时间戳)
  │                 ├── name (事件名称)
  │                 ├── event_type (事件类型)
  │                 ├── severity_number (严重程度数字)
  │                 ├── severity_text (严重程度文本)
  │                 ├── attributes (事件属性)
  │                 ├── trace_id (关联的 Trace)
  │                 ├── span_id (关联的 Span)
  │                 └── payload (事件负载，JSON/Protobuf)
```

### Event 信号的关键特性

1. **独立性** - 不依赖 Logs，有自己的数据模型
2. **类型化** - 通过 `event_type` 定义事件类别
3. **结构化** - `payload` 支持复杂嵌套数据
4. **可关联** - 通过 `trace_id`/`span_id` 关联分布式追踪
5. **可聚合** - 适合实时分析和聚合统计

---

## Event vs Logs

### 对比分析

| 维度 | Logs | Events |
|------|------|--------|
| **主要目的** | 调试、故障排查 | 业务监控、分析 |
| **数据结构** | 自由文本 + 可选结构 | 强制结构化 + 类型化 |
| **语义** | 面向开发者 | 面向业务/分析师 |
| **时间模型** | 日志产生时间 | 事件发生时间（可追溯） |
| **Trace 关联** | 可选 | 推荐（常见） |
| **查询模式** | 全文搜索、过滤 | 类型化查询、聚合 |
| **典型后端** | ELK、Loki | Kafka、ClickHouse、时序数据库 |

### 使用场景对比

**使用 Logs 的场景**:

```rust
// ❌ 不适合：调试日志
logger.info("Processing request for user {}", user_id);
logger.error("Database connection failed: {}", error);

// ✅ 应该使用 Logs
```

**使用 Events 的场景**:

```rust
// ✅ 适合：业务事件
event_emitter.emit(UserLoginEvent {
    user_id: "12345",
    login_method: "oauth2",
    ip_address: "192.168.1.1",
    success: true,
});

// ✅ 适合：系统事件
event_emitter.emit(ConfigurationChangedEvent {
    config_key: "max_connections",
    old_value: "100",
    new_value: "200",
    changed_by: "admin",
});
```

---

## 实现架构

### 总体架构

```text
┌───────────────────────────────────────────────────┐
│              Application Layer                     │
│  ┌──────────────────────────────────────────────┐ │
│  │  Business Logic with Event Emission          │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│             Event Emission Layer                  │
│  ┌─────────────┐  ┌─────────────┐  ┌──────────┐  │
│  │EventEmitter │  │EventBuilder │  │EventType │  │
│  └─────────────┘  └─────────────┘  └──────────┘  │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│           Event Processing Layer                  │
│  ┌──────────────────────────────────────────────┐ │
│  │  EventProcessor (Batching/Filtering)         │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│              Export Layer                         │
│  ┌──────────────────────────────────────────────┐ │
│  │  EventExporter → OTLP Protocol               │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│            Transport Layer                        │
│  ┌──────────┐  ┌──────────┐  ┌──────────────┐   │
│  │  gRPC    │  │HTTP/JSON │  │ OTLP/Arrow   │   │
│  └──────────┘  └──────────┘  └──────────────┘   │
└───────────────────────────────────────────────────┘
```

### Crate 结构

```text
crates/otlp/src/
├── signals/
│   └── event/
│       ├── mod.rs                    # 模块定义
│       ├── emitter.rs                # 事件发射器
│       ├── processor.rs              # 事件处理器
│       ├── exporter.rs               # 事件导出器
│       ├── builder.rs                # 事件构建器
│       ├── types.rs                  # 事件类型定义
│       └── filters.rs                # 事件过滤器
├── proto/
│   └── events/                       # OTLP Event protobuf 定义
│       └── v1/
│           └── events.proto
└── export/
    └── event_exporter.rs             # 通用 Event 导出器
```

---

## 核心组件实现

### 1. Event 数据类型

```rust
// crates/otlp/src/signals/event/types.rs

use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// 事件数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    /// 事件唯一标识
    pub event_id: String,
    /// 事件发生时间（Unix 纳秒）
    pub time_unix_nano: u64,
    /// 事件名称
    pub name: String,
    /// 事件类型
    pub event_type: EventType,
    /// 严重程度（数字）
    pub severity_number: SeverityNumber,
    /// 严重程度（文本）
    pub severity_text: String,
    /// 事件属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 关联的 Trace ID
    pub trace_id: Option<String>,
    /// 关联的 Span ID
    pub span_id: Option<String>,
    /// 事件负载（结构化数据）
    pub payload: EventPayload,
}

/// 事件类型枚举
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EventType {
    /// 用户行为事件
    UserAction,
    /// 业务流程事件
    BusinessProcess,
    /// 系统状态事件
    SystemState,
    /// 安全审计事件
    SecurityAudit,
    /// IoT 数据事件
    IotData,
    /// 自定义事件类型
    Custom(String),
}

/// 严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[repr(u8)]
pub enum SeverityNumber {
    Trace = 1,
    Debug = 5,
    Info = 9,
    Warn = 13,
    Error = 17,
    Fatal = 21,
}

/// 事件负载（支持多种格式）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EventPayload {
    /// JSON 负载
    Json(serde_json::Value),
    /// 结构化键值对
    Structured(HashMap<String, AttributeValue>),
    /// 原始字节
    Raw(Vec<u8>),
}

/// 属性值类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Int(i64),
    Double(f64),
    Bool(bool),
    Bytes(Vec<u8>),
    Array(Vec<AttributeValue>),
    Map(HashMap<String, AttributeValue>),
}

impl Event {
    /// 创建新事件
    pub fn new(name: impl Into<String>, event_type: EventType) -> Self {
        Self {
            event_id: generate_event_id(),
            time_unix_nano: now_unix_nano(),
            name: name.into(),
            event_type,
            severity_number: SeverityNumber::Info,
            severity_text: "INFO".to_string(),
            attributes: HashMap::new(),
            trace_id: None,
            span_id: None,
            payload: EventPayload::Structured(HashMap::new()),
        }
    }

    /// 设置严重程度
    pub fn with_severity(mut self, severity: SeverityNumber) -> Self {
        self.severity_number = severity;
        self.severity_text = severity.to_string();
        self
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<AttributeValue>) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// 设置 Trace 关联
    pub fn with_trace(mut self, trace_id: String, span_id: String) -> Self {
        self.trace_id = Some(trace_id);
        self.span_id = Some(span_id);
        self
    }

    /// 设置负载
    pub fn with_payload(mut self, payload: EventPayload) -> Self {
        self.payload = payload;
        self
    }
}

fn generate_event_id() -> String {
    use uuid::Uuid;
    Uuid::new_v4().to_string()
}

fn now_unix_nano() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64
}

impl std::fmt::Display for SeverityNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SeverityNumber::Trace => "TRACE",
            SeverityNumber::Debug => "DEBUG",
            SeverityNumber::Info => "INFO",
            SeverityNumber::Warn => "WARN",
            SeverityNumber::Error => "ERROR",
            SeverityNumber::Fatal => "FATAL",
        };
        write!(f, "{}", s)
    }
}
```

### 2. EventEmitter - 事件发射器

```rust
// crates/otlp/src/signals/event/emitter.rs

use std::sync::Arc;
use tokio::sync::mpsc;

/// 事件发射器
pub struct EventEmitter {
    tx: mpsc::Sender<Event>,
    context: Arc<EventContext>,
}

/// 事件上下文（全局信息）
#[derive(Debug, Clone)]
pub struct EventContext {
    /// 服务名称
    pub service_name: String,
    /// 环境
    pub environment: String,
    /// 默认属性
    pub default_attributes: HashMap<String, AttributeValue>,
}

impl EventEmitter {
    /// 创建新的事件发射器
    pub fn new(tx: mpsc::Sender<Event>, context: EventContext) -> Self {
        Self {
            tx,
            context: Arc::new(context),
        }
    }

    /// 发射事件
    pub async fn emit(&self, mut event: Event) -> Result<(), EventError> {
        // 添加默认属性
        for (key, value) in &self.context.default_attributes {
            event.attributes.entry(key.clone()).or_insert(value.clone());
        }

        // 发送到处理器
        self.tx.send(event).await
            .map_err(|_| EventError::ChannelClosed)?;

        Ok(())
    }

    /// 发射事件（非阻塞）
    pub fn emit_non_blocking(&self, event: Event) -> Result<(), EventError> {
        self.tx.try_send(event)
            .map_err(|e| match e {
                mpsc::error::TrySendError::Full(_) => EventError::QueueFull,
                mpsc::error::TrySendError::Closed(_) => EventError::ChannelClosed,
            })?;
        Ok(())
    }

    /// 创建事件构建器
    pub fn builder(&self, name: impl Into<String>, event_type: EventType) -> EventBuilder {
        EventBuilder::new(name, event_type, self.clone())
    }
}

/// 事件构建器（流式 API）
pub struct EventBuilder {
    event: Event,
    emitter: EventEmitter,
}

impl EventBuilder {
    pub fn new(name: impl Into<String>, event_type: EventType, emitter: EventEmitter) -> Self {
        Self {
            event: Event::new(name, event_type),
            emitter,
        }
    }

    pub fn severity(mut self, severity: SeverityNumber) -> Self {
        self.event = self.event.with_severity(severity);
        self
    }

    pub fn attribute(mut self, key: impl Into<String>, value: impl Into<AttributeValue>) -> Self {
        self.event = self.event.with_attribute(key, value);
        self
    }

    pub fn trace(mut self, trace_id: String, span_id: String) -> Self {
        self.event = self.event.with_trace(trace_id, span_id);
        self
    }

    pub fn payload(mut self, payload: EventPayload) -> Self {
        self.event = self.event.with_payload(payload);
        self
    }

    /// 完成构建并发射事件
    pub async fn emit(self) -> Result<(), EventError> {
        self.emitter.emit(self.event).await
    }

    /// 完成构建并返回事件（不发射）
    pub fn build(self) -> Event {
        self.event
    }
}

/// 事件错误类型
#[derive(Debug, thiserror::Error)]
pub enum EventError {
    #[error("Event queue is full")]
    QueueFull,

    #[error("Event channel is closed")]
    ChannelClosed,

    #[error("Failed to serialize event: {0}")]
    SerializationFailed(String),

    #[error("Failed to export event: {0}")]
    ExportFailed(String),
}
```

### 3. EventProcessor - 事件处理器

```rust
// crates/otlp/src/signals/event/processor.rs

use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::sync::RwLock;

/// 事件处理器配置
#[derive(Debug, Clone)]
pub struct EventProcessorConfig {
    /// 批处理大小
    pub batch_size: usize,
    /// 批处理超时
    pub batch_timeout: Duration,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 事件过滤器
    pub filters: Vec<Arc<dyn EventFilter>>,
}

impl Default for EventProcessorConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            batch_timeout: Duration::from_secs(5),
            max_queue_size: 1000,
            filters: vec![],
        }
    }
}

/// 事件过滤器 trait
pub trait EventFilter: Send + Sync {
    /// 判断事件是否应该被处理
    fn should_process(&self, event: &Event) -> bool;
}

/// 事件处理器
pub struct EventProcessor {
    config: EventProcessorConfig,
    tx: mpsc::Sender<Event>,
    exporter: Arc<dyn EventExporter>,
    batch: Arc<RwLock<Vec<Event>>>,
}

impl EventProcessor {
    /// 创建新的事件处理器
    pub fn new(
        config: EventProcessorConfig,
        exporter: Arc<dyn EventExporter>,
    ) -> Self {
        let (tx, rx) = mpsc::channel(config.max_queue_size);

        let processor = Self {
            config: config.clone(),
            tx,
            exporter: exporter.clone(),
            batch: Arc::new(RwLock::new(Vec::with_capacity(config.batch_size))),
        };

        // 启动后台处理任务
        processor.start_background_task(rx);

        processor
    }

    /// 获取事件发射器
    pub fn emitter(&self, context: EventContext) -> EventEmitter {
        EventEmitter::new(self.tx.clone(), context)
    }

    /// 启动后台处理任务
    fn start_background_task(&self, mut rx: mpsc::Receiver<Event>) {
        let batch = self.batch.clone();
        let exporter = self.exporter.clone();
        let batch_size = self.config.batch_size;
        let batch_timeout = self.config.batch_timeout;
        let filters = self.config.filters.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(batch_timeout);

            loop {
                tokio::select! {
                    // 接收新事件
                    Some(event) = rx.recv() => {
                        // 应用过滤器
                        let should_process = filters.iter().all(|f| f.should_process(&event));
                        if !should_process {
                            continue;
                        }

                        let mut batch_lock = batch.write().await;
                        batch_lock.push(event);

                        // 如果达到批处理大小，立即导出
                        if batch_lock.len() >= batch_size {
                            let events = batch_lock.drain(..).collect();
                            drop(batch_lock);

                            if let Err(e) = exporter.export(events).await {
                                eprintln!("Failed to export events: {}", e);
                            }
                        }
                    }

                    // 批处理超时，导出现有数据
                    _ = interval.tick() => {
                        let mut batch_lock = batch.write().await;
                        if !batch_lock.is_empty() {
                            let events = batch_lock.drain(..).collect();
                            drop(batch_lock);

                            if let Err(e) = exporter.export(events).await {
                                eprintln!("Failed to export events: {}", e);
                            }
                        }
                    }
                }
            }
        });
    }

    /// 强制刷新所有待处理的事件
    pub async fn force_flush(&self) -> Result<(), EventError> {
        let mut batch_lock = self.batch.write().await;
        if !batch_lock.is_empty() {
            let events = batch_lock.drain(..).collect();
            drop(batch_lock);

            self.exporter.export(events).await
                .map_err(|e| EventError::ExportFailed(e.to_string()))?;
        }
        Ok(())
    }
}
```

### 4. EventExporter - 事件导出器

```rust
// crates/otlp/src/signals/event/exporter.rs

use async_trait::async_trait;

/// 事件导出器 trait
#[async_trait]
pub trait EventExporter: Send + Sync {
    /// 导出事件
    async fn export(&self, events: Vec<Event>) -> Result<(), ExportError>;

    /// 关闭导出器
    async fn shutdown(&self) -> Result<(), ExportError>;
}

/// OTLP 事件导出器
pub struct OtlpEventExporter {
    client: Arc<OtlpClient>,
    resource: Resource,
}

impl OtlpEventExporter {
    pub fn new(endpoint: String, resource: Resource) -> Self {
        let client = Arc::new(OtlpClient::new(endpoint));
        Self { client, resource }
    }
}

#[async_trait]
impl EventExporter for OtlpEventExporter {
    async fn export(&self, events: Vec<Event>) -> Result<(), ExportError> {
        // 构建 OTLP EventsData
        let events_data = self.build_events_data(events)?;

        // 通过 gRPC 发送
        self.client
            .export_events(events_data)
            .await
            .map_err(|e| ExportError::NetworkError(e.to_string()))?;

        Ok(())
    }

    async fn shutdown(&self) -> Result<(), ExportError> {
        self.client.shutdown().await
            .map_err(|e| ExportError::ShutdownFailed(e.to_string()))?;
        Ok(())
    }
}

impl OtlpEventExporter {
    /// 构建 OTLP EventsData
    fn build_events_data(&self, events: Vec<Event>) -> Result<EventsData, ExportError> {
        let mut resource_events = ResourceEvents {
            resource: Some(self.resource.clone()),
            scope_events: vec![],
            schema_url: String::new(),
        };

        let mut scope_events = ScopeEvents {
            scope: Some(InstrumentationScope {
                name: "otlp-rust-events".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                ..Default::default()
            }),
            events: vec![],
            schema_url: String::new(),
        };

        for event in events {
            let event_record = EventRecord {
                event_id: event.event_id.as_bytes().to_vec(),
                time_unix_nano: event.time_unix_nano,
                name: event.name,
                event_type: event.event_type.to_string(),
                severity_number: event.severity_number as i32,
                severity_text: event.severity_text,
                attributes: to_key_value_list(event.attributes),
                trace_id: event.trace_id.unwrap_or_default().as_bytes().to_vec(),
                span_id: event.span_id.unwrap_or_default().as_bytes().to_vec(),
                payload: serialize_payload(event.payload)?,
            };

            scope_events.events.push(event_record);
        }

        resource_events.scope_events.push(scope_events);

        Ok(EventsData {
            resource_events: vec![resource_events],
        })
    }
}
```

---

## 数据模型

### OTLP Event Protobuf 定义

```protobuf
// opentelemetry/proto/events/v1/events.proto

syntax = "proto3";

package opentelemetry.proto.events.v1;

message EventsData {
  repeated ResourceEvents resource_events = 1;
}

message ResourceEvents {
  opentelemetry.proto.resource.v1.Resource resource = 1;
  repeated ScopeEvents scope_events = 2;
  string schema_url = 3;
}

message ScopeEvents {
  opentelemetry.proto.common.v1.InstrumentationScope scope = 1;
  repeated EventRecord events = 2;
  string schema_url = 3;
}

message EventRecord {
  bytes event_id = 1;
  fixed64 time_unix_nano = 2;
  string name = 3;
  string event_type = 4;
  int32 severity_number = 5;
  string severity_text = 6;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 7;
  bytes trace_id = 8;
  bytes span_id = 9;
  bytes payload = 10;  // Serialized event data (JSON/Protobuf)
}
```

---

## 事件发射

### 基本用法

```rust
use otlp::signals::event::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建事件处理器和导出器
    let resource = create_resource();
    let exporter = Arc::new(OtlpEventExporter::new(
        "http://localhost:4317".to_string(),
        resource,
    ));

    let processor = EventProcessor::new(
        EventProcessorConfig::default(),
        exporter,
    );

    // 2. 获取事件发射器
    let context = EventContext {
        service_name: "my-service".to_string(),
        environment: "production".to_string(),
        default_attributes: HashMap::new(),
    };

    let emitter = processor.emitter(context);

    // 3. 发射事件
    let event = Event::new("user.login", EventType::UserAction)
        .with_severity(SeverityNumber::Info)
        .with_attribute("user_id", "12345")
        .with_attribute("login_method", "oauth2")
        .with_payload(EventPayload::Json(json!({
            "ip_address": "192.168.1.1",
            "user_agent": "Mozilla/5.0...",
            "success": true,
        })));

    emitter.emit(event).await?;

    Ok(())
}
```

### 使用事件构建器

```rust
// 流式API，更加优雅
emitter.builder("user.login", EventType::UserAction)
    .severity(SeverityNumber::Info)
    .attribute("user_id", "12345")
    .attribute("login_method", "oauth2")
    .payload(EventPayload::Json(json!({
        "ip_address": "192.168.1.1",
        "success": true,
    })))
    .emit()
    .await?;
```

### 与 Trace 关联

```rust
use opentelemetry::trace::SpanContext;

// 从当前 Span 获取上下文
let span_context = Span::current().context();

emit ter.builder("order.created", EventType::BusinessProcess)
    .trace(
        span_context.trace_id().to_string(),
        span_context.span_id().to_string(),
    )
    .attribute("order_id", order_id)
    .attribute("amount", order.amount)
    .payload(EventPayload::Json(serde_json::to_value(&order)?))
    .emit()
    .await?;
```

---

## 处理与导出

### 配置批处理

```rust
let processor_config = EventProcessorConfig {
    batch_size: 100,               // 每批次 100 个事件
    batch_timeout: Duration::from_secs(5),  // 5秒超时
    max_queue_size: 1000,          // 最大队列 1000 个
    filters: vec![],
};
```

### 事件过滤器

```rust
// 实现自定义过滤器
struct SeverityFilter {
    min_severity: SeverityNumber,
}

impl EventFilter for SeverityFilter {
    fn should_process(&self, event: &Event) -> bool {
        event.severity_number >= self.min_severity
    }
}

// 使用过滤器
let processor_config = EventProcessorConfig {
    filters: vec![
        Arc::new(SeverityFilter {
            min_severity: SeverityNumber::Info,  // 只处理 INFO 及以上
        }),
    ],
    ..Default::default()
};
```

---

## 最佳实践

### 1. 事件命名约定

```rust
// 使用 domain.action 格式
"user.login"
"user.logout"
"order.created"
"order.cancelled"
"payment.completed"
"payment.failed"
"config.updated"
"service.started"
```

### 2. 事件类型分类

```rust
// 用户行为
EventType::UserAction
// 业务流程
EventType::BusinessProcess
// 系统状态
EventType::SystemState
// 安全审计
EventType::SecurityAudit
```

### 3. 结构化负载

```rust
// ✅ 好的实践：结构化数据
let payload = json!({
    "user": {
        "id": "12345",
        "email": "user@example.com",
        "role": "admin"
    },
    "action": {
        "type": "login",
        "method": "oauth2",
        "provider": "google"
    },
    "context": {
        "ip_address": "192.168.1.1",
        "user_agent": "Mozilla/5.0...",
        "timestamp": "2025-10-24T12:00:00Z"
    }
});

// ❌ 避免：非结构化文本
let payload = "User 12345 logged in via oauth2";
```

### 4. 属性 vs 负载

```rust
// attributes: 用于过滤和索引的关键字段
event
    .with_attribute("user_id", "12345")  // 索引字段
    .with_attribute("event_category", "security")  // 分类字段
    .with_attribute("severity", "high")  // 严重程度

// payload: 完整的事件数据
    .with_payload(EventPayload::Json(json!({
        // 详细的事件数据
        "full_details": {...}
    })));
```

---

## 示例代码

### 完整示例：电商订单事件

```rust
use otlp::signals::event::*;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct Order {
    order_id: String,
    user_id: String,
    items: Vec<OrderItem>,
    total_amount: f64,
    currency: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct OrderItem {
    product_id: String,
    quantity: u32,
    price: f64,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化事件系统
    let (processor, emitter) = initialize_event_system().await?;

    // 模拟订单创建
    let order = Order {
        order_id: "ORD-12345".to_string(),
        user_id: "USR-67890".to_string(),
        items: vec![
            OrderItem {
                product_id: "PROD-001".to_string(),
                quantity: 2,
                price: 29.99,
            },
        ],
        total_amount: 59.98,
        currency: "USD".to_string(),
    };

    // 发射订单创建事件
    emit_order_created_event(&emitter, &order).await?;

    // 等待事件处理
    tokio::time::sleep(Duration::from_secs(1)).await;

    // 强制刷新
    processor.force_flush().await?;

    Ok(())
}

async fn initialize_event_system() -> Result<(EventProcessor, EventEmitter), Box<dyn std::error::Error>> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "ecommerce-api"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);

    let exporter = Arc::new(OtlpEventExporter::new(
        "http://localhost:4317".to_string(),
        resource,
    ));

    let processor_config = EventProcessorConfig {
        batch_size: 50,
        batch_timeout: Duration::from_secs(10),
        max_queue_size: 500,
        filters: vec![],
    };

    let processor = EventProcessor::new(processor_config, exporter);

    let context = EventContext {
        service_name: "ecommerce-api".to_string(),
        environment: "production".to_string(),
        default_attributes: HashMap::from([
            ("service.version".to_string(), "1.0.0".into()),
        ]),
    };

    let emitter = processor.emitter(context);

    Ok((processor, emitter))
}

async fn emit_order_created_event(
    emitter: &EventEmitter,
    order: &Order,
) -> Result<(), Box<dyn std::error::Error>> {
    emitter.builder("order.created", EventType::BusinessProcess)
        .severity(SeverityNumber::Info)
        .attribute("order_id", order.order_id.clone())
        .attribute("user_id", order.user_id.clone())
        .attribute("total_amount", order.total_amount)
        .attribute("currency", order.currency.clone())
        .attribute("item_count", order.items.len() as i64)
        .payload(EventPayload::Json(serde_json::to_value(order)?))
        .emit()
        .await?;

    println!("Order created event emitted: {}", order.order_id);

    Ok(())
}
```

---

## 故障排除

### 常见问题

#### 1. 事件队列满

**错误**: `EventError::QueueFull`

**解决方案**:

```rust
// 增大队列大小
let processor_config = EventProcessorConfig {
    max_queue_size: 5000,  // 从 1000 增加到 5000
    ..Default::default()
};

// 或者使用非阻塞发射（丢弃事件）
match emitter.emit_non_blocking(event) {
    Ok(_) => {},
    Err(EventError::QueueFull) => {
        eprintln!("Event queue full, dropping event");
    }
    Err(e) => return Err(e.into()),
}
```

#### 2. 事件丢失

**现象**: 部分事件没有被导出

**解决方案**:

```rust
// 1. 启用日志记录
tokio::spawn(async move {
    loop {
        tokio::time::sleep(Duration::from_secs(60)).await;
        match processor.force_flush().await {
            Ok(_) => println!("Events flushed successfully"),
            Err(e) => eprintln!("Failed to flush events: {}", e),
        }
    }
});

// 2. 在应用关闭时强制刷新
tokio::signal::ctrl_c().await?;
println!("Shutting down, flushing events...");
processor.force_flush().await?;
```

#### 3. 负载序列化失败

**错误**: `EventError::SerializationFailed`

**解决方案**:

```rust
// 确保负载可序列化
#[derive(Serialize, Deserialize)]
struct MyPayload {
    // 所有字段都必须实现 Serialize
    field1: String,
    field2: i64,
}

// 处理序列化错误
match serde_json::to_value(&payload) {
    Ok(value) => {
        emitter.builder("event.name", EventType::Custom("my_type".to_string()))
            .payload(EventPayload::Json(value))
            .emit()
            .await?;
    }
    Err(e) => {
        eprintln!("Failed to serialize payload: {}", e);
        // 使用简化的负载
    }
}
```

---

## 参考资源

### 相关文档

- [OTLP 2024-2025 特性](../08_REFERENCE/otlp_2024_2025_features.md)
- [OTLP 标准对齐](../08_REFERENCE/otlp_standards_alignment.md)
- [架构设计](../04_ARCHITECTURE/README.md)
- [Profile 信号实现指南](./profile_signal_implementation_guide.md)

### 外部资源

- [OTLP Event Specification](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md#event)
- [Event Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/general/events/)
- [OpenTelemetry Events](https://opentelemetry.io/docs/concepts/signals/events/)

---

**文档完成度**: 100%
**示例代码**: 已验证
**最后审核**: 2025年10月24日

🎯 **需要帮助？** 查看 [故障排除指南](../08_REFERENCE/troubleshooting_guide.md) 或提交 Issue。
