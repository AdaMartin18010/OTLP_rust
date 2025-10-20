# MQTT 语义约定 - Rust 完整实现

> **IoT 消息协议**: MQTT Tracing与Metrics完整规范 (Rust 1.90)  
> **最后更新**: 2025年10月10日

---

## 目录

- [MQTT 语义约定 - Rust 完整实现](#mqtt-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. MQTT 概述](#1-mqtt-概述)
    - [1.1 MQTT 特点](#11-mqtt-特点)
    - [1.2 核心架构](#12-核心架构)
    - [1.3 Rust 生态系统](#13-rust-生态系统)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 MQTT 语义约定常量](#23-mqtt-语义约定常量)
  - [3. MQTT 属性类型系统](#3-mqtt-属性类型系统)
    - [3.1 QoS 级别](#31-qos-级别)
    - [3.2 协议版本](#32-协议版本)
    - [3.3 MQTT 属性结构体](#33-mqtt-属性结构体)
  - [4. Publisher 实现](#4-publisher-实现)
    - [4.1 Publisher 属性](#41-publisher-属性)
    - [4.2 MQTT 5.0 Publisher](#42-mqtt-50-publisher)
    - [4.3 MQTT 3.1.1 Publisher](#43-mqtt-311-publisher)
  - [5. Subscriber 实现](#5-subscriber-实现)
    - [5.1 Subscriber 属性](#51-subscriber-属性)
    - [5.2 MQTT 5.0 Subscriber](#52-mqtt-50-subscriber)
    - [5.3 Topic 通配符处理](#53-topic-通配符处理)
  - [6. Context 传播](#6-context-传播)
    - [6.1 MQTT 5.0 User Properties](#61-mqtt-50-user-properties)
    - [6.2 MQTT 3.1.1 变通方案](#62-mqtt-311-变通方案)
    - [6.3 W3C Trace Context 集成](#63-w3c-trace-context-集成)
  - [7. 完整示例](#7-完整示例)
    - [7.1 温度传感器 Publisher](#71-温度传感器-publisher)
    - [7.2 数据采集 Subscriber](#72-数据采集-subscriber)
    - [7.3 智能家居网关](#73-智能家居网关)
  - [8. Metrics 实现](#8-metrics-实现)
    - [8.1 Publisher Metrics](#81-publisher-metrics)
    - [8.2 Subscriber Metrics](#82-subscriber-metrics)
    - [8.3 连接质量 Metrics](#83-连接质量-metrics)
  - [9. 高级特性](#9-高级特性)
    - [9.1 Retained Messages](#91-retained-messages)
    - [9.2 Last Will Testament](#92-last-will-testament)
    - [9.3 持久会话](#93-持久会话)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 性能优化](#101-性能优化)
    - [10.2 可靠性保证](#102-可靠性保证)
    - [10.3 错误处理](#103-错误处理)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Rust Crates](#rust-crates)
    - [IoT 资源](#iot-资源)

---

## 1. MQTT 概述

### 1.1 MQTT 特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT (Message Queuing Telemetry Transport)

核心特性:
✅ 极简协议 (最小报文2字节)
✅ Pub/Sub模型 (解耦发布订阅)
✅ 3个QoS级别 (0/1/2)
✅ Topic通配符 (+/#)
✅ Retained消息
✅ Last Will (遗嘱消息)
✅ 持久会话
✅ 低功耗 (适合电池设备)

版本对比:
- MQTT 3.1.1: 主流版本 (无User Properties)
- MQTT 5.0: 最新版本 (支持User Properties)

适用场景:
✅ 物联网 (IoT)
✅ 智能家居
✅ 车联网
✅ 工业4.0
✅ 移动应用推送

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
┌─────────────┐
│ Publisher 1 │──┐
└─────────────┘  │
                 │   ┌──────────────┐
┌─────────────┐  ├──►│ MQTT Broker  │
│ Publisher 2 │──┤   └──────┬───────┘
└─────────────┘  │          │
                 │          ▼
                 │   ┌─────────────┐
                 └──►│ Subscriber  │
                     └─────────────┘

Topic 层级示例:
home/living-room/temperature
home/+/temperature          (单层通配符)
home/#                      (多层通配符)
```

### 1.3 Rust 生态系统

```rust
// Rust MQTT 客户端库
// - rumqttc: 纯 Rust 实现，性能优秀
// - paho-mqtt: Eclipse Paho 的 Rust 绑定
// - mqtt-async-client: 异步客户端
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "mqtt-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# MQTT 客户端
rumqttc = "0.24"

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 运行时
tokio = { version = "1", features = ["full"] }

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"
```

### 2.2 核心导入

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, TraceContextExt},
    KeyValue, Context,
};
use opentelemetry::propagation::{TextMapPropagator, Injector, Extractor};
use rumqttc::{AsyncClient, MqttOptions, QoS, Event, Packet};
use std::collections::HashMap;
```

### 2.3 MQTT 语义约定常量

```rust
pub mod mqtt_conventions {
    // 消息系统属性
    pub const MESSAGING_SYSTEM: &str = "messaging.system";
    pub const MESSAGING_SYSTEM_MQTT: &str = "mqtt";
    
    // 目标属性
    pub const MESSAGING_DESTINATION_NAME: &str = "messaging.destination.name";
    pub const MESSAGING_OPERATION: &str = "messaging.operation";
    
    // MQTT 特定属性
    pub const MESSAGING_MQTT_QOS: &str = "messaging.mqtt.qos";
    pub const MESSAGING_MQTT_RETAINED: &str = "messaging.mqtt.retained";
    pub const MESSAGING_MQTT_DUPLICATE: &str = "messaging.mqtt.duplicate";
    pub const MESSAGING_MQTT_CLIENT_ID: &str = "messaging.mqtt.client_id";
    pub const MESSAGING_MQTT_PROTOCOL_VERSION: &str = "messaging.mqtt.protocol_version";
    
    // 消息属性
    pub const MESSAGING_MESSAGE_BODY_SIZE: &str = "messaging.message.body.size";
    pub const MESSAGING_MESSAGE_ID: &str = "messaging.message.id";
    
    // 网络属性
    pub const NET_PEER_NAME: &str = "net.peer.name";
    pub const NET_PEER_PORT: &str = "net.peer.port";
    pub const NET_TRANSPORT: &str = "net.transport";
    
    // 操作类型
    pub const OPERATION_PUBLISH: &str = "publish";
    pub const OPERATION_RECEIVE: &str = "receive";
}
```

---

## 3. MQTT 属性类型系统

### 3.1 QoS 级别

```rust
/// MQTT QoS 级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MqttQoS {
    /// At most once (可能丢失)
    AtMostOnce,
    /// At least once (可能重复)
    AtLeastOnce,
    /// Exactly once (精确一次)
    ExactlyOnce,
}

impl MqttQoS {
    pub fn as_int(&self) -> i64 {
        match self {
            Self::AtMostOnce => 0,
            Self::AtLeastOnce => 1,
            Self::ExactlyOnce => 2,
        }
    }
    
    pub fn from_rumqttc_qos(qos: QoS) -> Self {
        match qos {
            QoS::AtMostOnce => Self::AtMostOnce,
            QoS::AtLeastOnce => Self::AtLeastOnce,
            QoS::ExactlyOnce => Self::ExactlyOnce,
        }
    }
    
    pub fn to_rumqttc_qos(&self) -> QoS {
        match self {
            Self::AtMostOnce => QoS::AtMostOnce,
            Self::AtLeastOnce => QoS::AtLeastOnce,
            Self::ExactlyOnce => QoS::ExactlyOnce,
        }
    }
}
```

### 3.2 协议版本

```rust
/// MQTT 协议版本
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MqttVersion {
    V3_1_1,
    V5_0,
}

impl MqttVersion {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::V3_1_1 => "3.1.1",
            Self::V5_0 => "5.0",
        }
    }
}
```

### 3.3 MQTT 属性结构体

```rust
/// MQTT 通用属性
#[derive(Debug, Clone)]
pub struct MqttAttributes {
    pub broker_host: String,
    pub broker_port: u16,
    pub client_id: String,
    pub topic: String,
    pub qos: MqttQoS,
    pub protocol_version: MqttVersion,
    pub retained: bool,
    pub message_size: Option<usize>,
}

impl MqttAttributes {
    /// 创建基础属性
    pub fn new(
        broker_host: impl Into<String>,
        broker_port: u16,
        client_id: impl Into<String>,
        topic: impl Into<String>,
        qos: MqttQoS,
    ) -> Self {
        Self {
            broker_host: broker_host.into(),
            broker_port,
            client_id: client_id.into(),
            topic: topic.into(),
            qos,
            protocol_version: MqttVersion::V3_1_1,
            retained: false,
            message_size: None,
        }
    }
    
    /// 设置为 MQTT 5.0
    pub fn with_v5(mut self) -> Self {
        self.protocol_version = MqttVersion::V5_0;
        self
    }
    
    /// 设置 retained 标志
    pub fn with_retained(mut self, retained: bool) -> Self {
        self.retained = retained;
        self
    }
    
    /// 转换为 Publisher KeyValue 数组
    pub fn to_publisher_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(
                mqtt_conventions::MESSAGING_SYSTEM,
                mqtt_conventions::MESSAGING_SYSTEM_MQTT,
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_DESTINATION_NAME,
                self.topic.clone(),
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_OPERATION,
                mqtt_conventions::OPERATION_PUBLISH,
            ),
            KeyValue::new(
                mqtt_conventions::NET_PEER_NAME,
                self.broker_host.clone(),
            ),
            KeyValue::new(
                mqtt_conventions::NET_PEER_PORT,
                self.broker_port as i64,
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_MQTT_QOS,
                self.qos.as_int(),
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_MQTT_RETAINED,
                self.retained,
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_MQTT_CLIENT_ID,
                self.client_id.clone(),
            ),
            KeyValue::new(
                mqtt_conventions::MESSAGING_MQTT_PROTOCOL_VERSION,
                self.protocol_version.as_str(),
            ),
            KeyValue::new(
                mqtt_conventions::NET_TRANSPORT,
                "tcp",
            ),
        ];
        
        if let Some(size) = self.message_size {
            attrs.push(KeyValue::new(
                mqtt_conventions::MESSAGING_MESSAGE_BODY_SIZE,
                size as i64,
            ));
        }
        
        attrs
    }
    
    /// 转换为 Subscriber KeyValue 数组
    pub fn to_subscriber_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = self.to_publisher_key_values();
        
        // 替换 operation
        if let Some(pos) = attrs.iter().position(|kv| 
            kv.key.as_str() == mqtt_conventions::MESSAGING_OPERATION
        ) {
            attrs[pos] = KeyValue::new(
                mqtt_conventions::MESSAGING_OPERATION,
                mqtt_conventions::OPERATION_RECEIVE,
            );
        }
        
        attrs
    }
}
```

---

## 4. Publisher 实现

### 4.1 Publisher 属性

```rust
/// MQTT Publisher 封装
pub struct MqttPublisher {
    client: AsyncClient,
    tracer: global::BoxedTracer,
    mqtt_attrs: MqttAttributes,
}

impl MqttPublisher {
    /// 创建 Publisher
    pub async fn new(
        mqtt_opts: MqttOptions,
        mqtt_attrs: MqttAttributes,
    ) -> anyhow::Result<Self> {
        let (client, mut eventloop) = AsyncClient::new(mqtt_opts, 10);
        
        // 启动事件循环
        tokio::spawn(async move {
            loop {
                match eventloop.poll().await {
                    Ok(_) => {}
                    Err(e) => {
                        tracing::error!("MQTT event loop error: {}", e);
                        break;
                    }
                }
            }
        });
        
        let tracer = global::tracer("mqtt-publisher");
        
        Ok(Self {
            client,
            tracer,
            mqtt_attrs,
        })
    }
}
```

### 4.2 MQTT 5.0 Publisher

```rust
impl MqttPublisher {
    /// 发布消息 (带 Tracing)
    pub async fn publish_with_tracing(
        &self,
        topic: &str,
        payload: Vec<u8>,
        qos: QoS,
        retained: bool,
    ) -> anyhow::Result<()> {
        // 创建 PRODUCER Span
        let mut span = self.tracer
            .span_builder("mqtt_publish")
            .with_kind(SpanKind::Producer)
            .start(&self.tracer);
        
        // 设置 MQTT 属性
        let mut attrs = self.mqtt_attrs.clone();
        attrs.topic = topic.to_string();
        attrs.qos = MqttQoS::from_rumqttc_qos(qos);
        attrs.retained = retained;
        attrs.message_size = Some(payload.len());
        
        span.set_attributes(attrs.to_publisher_key_values());
        
        // 注入 Trace Context (MQTT 5.0)
        let context = Context::current_with_span(span.clone());
        let mut user_properties = HashMap::new();
        
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(&context, &mut UserPropertiesInjector(&mut user_properties));
        });
        
        // 发布消息
        let result = self.client
            .publish(topic, qos, retained, payload)
            .await;
        
        match result {
            Ok(_) => {
                span.set_status(Status::Ok);
                tracing::info!("Published to topic: {}", topic);
            }
            Err(e) => {
                span.set_status(Status::error(format!("Publish failed: {}", e)));
                tracing::error!("Failed to publish: {}", e);
            }
        }
        
        span.end();
        result.map_err(Into::into)
    }
}

/// MQTT 5.0 User Properties Injector
struct UserPropertiesInjector<'a>(&'a mut HashMap<String, String>);

impl<'a> Injector for UserPropertiesInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.0.insert(key.to_string(), value);
    }
}
```

### 4.3 MQTT 3.1.1 Publisher

```rust
impl MqttPublisher {
    /// 发布消息 (MQTT 3.1.1 - Trace Context in Payload)
    pub async fn publish_v3_with_tracing(
        &self,
        topic: &str,
        mut payload: Vec<u8>,
        qos: QoS,
    ) -> anyhow::Result<()> {
        let mut span = self.tracer
            .span_builder("mqtt_publish")
            .with_kind(SpanKind::Producer)
            .start(&self.tracer);
        
        // 设置属性
        let mut attrs = self.mqtt_attrs.clone();
        attrs.topic = topic.to_string();
        attrs.qos = MqttQoS::from_rumqttc_qos(qos);
        attrs.message_size = Some(payload.len());
        
        span.set_attributes(attrs.to_publisher_key_values());
        
        // 将 Trace Context 编码到 Payload Header (JSON)
        let context = Context::current_with_span(span.clone());
        let mut trace_map = HashMap::new();
        
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(&context, &mut UserPropertiesInjector(&mut trace_map));
        });
        
        let trace_header = serde_json::json!({
            "_trace": trace_map,
            "_payload_offset": 0
        });
        
        let mut header_bytes = serde_json::to_vec(&trace_header)?;
        let header_len = header_bytes.len() as u32;
        
        // 构造最终 Payload: [header_len(4字节)] + [header] + [原始payload]
        let mut final_payload = header_len.to_be_bytes().to_vec();
        final_payload.append(&mut header_bytes);
        final_payload.append(&mut payload);
        
        // 发布
        let result = self.client
            .publish(topic, qos, false, final_payload)
            .await;
        
        match result {
            Ok(_) => span.set_status(Status::Ok),
            Err(ref e) => span.set_status(Status::error(format!("{}", e))),
        }
        
        span.end();
        result.map_err(Into::into)
    }
}
```

---

## 5. Subscriber 实现

### 5.1 Subscriber 属性

```rust
/// MQTT Subscriber 封装
pub struct MqttSubscriber {
    client: AsyncClient,
    tracer: global::BoxedTracer,
    mqtt_attrs: MqttAttributes,
}

impl MqttSubscriber {
    pub async fn new(
        mqtt_opts: MqttOptions,
        mqtt_attrs: MqttAttributes,
    ) -> anyhow::Result<Self> {
        let (client, _) = AsyncClient::new(mqtt_opts, 10);
        let tracer = global::tracer("mqtt-subscriber");
        
        Ok(Self {
            client,
            tracer,
            mqtt_attrs,
        })
    }
}
```

### 5.2 MQTT 5.0 Subscriber

```rust
impl MqttSubscriber {
    /// 订阅并处理消息
    pub async fn subscribe_with_tracing<F>(
        &self,
        topic: &str,
        qos: QoS,
        mut handler: F,
    ) -> anyhow::Result<()>
    where
        F: FnMut(Vec<u8>) -> anyhow::Result<()> + Send + 'static,
    {
        // 订阅 Topic
        self.client.subscribe(topic, qos).await?;
        
        tracing::info!("Subscribed to topic: {}", topic);
        
        // 创建事件循环
        let (_, mut eventloop) = AsyncClient::new(
            self.mqtt_attrs.broker_host.clone(),
            10,
        );
        
        // 处理消息
        loop {
            match eventloop.poll().await {
                Ok(Event::Incoming(Packet::Publish(publish))) => {
                    // 创建 CONSUMER Span
                    let mut span = self.tracer
                        .span_builder("mqtt_receive")
                        .with_kind(SpanKind::Consumer)
                        .start(&self.tracer);
                    
                    // 设置属性
                    let mut attrs = self.mqtt_attrs.clone();
                    attrs.topic = publish.topic.clone();
                    attrs.qos = MqttQoS::from_rumqttc_qos(publish.qos);
                    attrs.retained = publish.retain;
                    attrs.message_size = Some(publish.payload.len());
                    
                    span.set_attributes(attrs.to_subscriber_key_values());
                    
                    // 提取 Trace Context (MQTT 5.0)
                    // 这里需要从 User Properties 中提取
                    // rumqttc 0.24+ 支持 MQTT 5.0 properties
                    
                    // 处理消息
                    let context = Context::current_with_span(span.clone());
                    let _guard = context.attach();
                    
                    match handler(publish.payload.to_vec()) {
                        Ok(_) => {
                            span.set_status(Status::Ok);
                        }
                        Err(e) => {
                            span.set_status(Status::error(format!("{}", e)));
                            tracing::error!("Message handler error: {}", e);
                        }
                    }
                    
                    span.end();
                }
                Ok(_) => {}
                Err(e) => {
                    tracing::error!("MQTT poll error: {}", e);
                    break;
                }
            }
        }
        
        Ok(())
    }
}

/// User Properties Extractor
struct UserPropertiesExtractor<'a>(&'a HashMap<String, String>);

impl<'a> Extractor for UserPropertiesExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|s| s.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|s| s.as_str()).collect()
    }
}
```

### 5.3 Topic 通配符处理

```rust
/// Topic 通配符匹配
pub fn topic_matches_filter(topic: &str, filter: &str) -> bool {
    let topic_levels: Vec<&str> = topic.split('/').collect();
    let filter_levels: Vec<&str> = filter.split('/').collect();
    
    let mut topic_idx = 0;
    let mut filter_idx = 0;
    
    while topic_idx < topic_levels.len() && filter_idx < filter_levels.len() {
        match filter_levels[filter_idx] {
            "#" => {
                // 多层通配符，匹配剩余所有层级
                return true;
            }
            "+" => {
                // 单层通配符，跳过当前层级
                topic_idx += 1;
                filter_idx += 1;
            }
            level => {
                // 精确匹配
                if topic_levels[topic_idx] != level {
                    return false;
                }
                topic_idx += 1;
                filter_idx += 1;
            }
        }
    }
    
    topic_idx == topic_levels.len() && filter_idx == filter_levels.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_topic_matching() {
        assert!(topic_matches_filter("home/living-room/temp", "home/+/temp"));
        assert!(topic_matches_filter("home/living-room/temp", "home/#"));
        assert!(!topic_matches_filter("home/bedroom/temp", "home/living-room/+"));
    }
}
```

---

## 6. Context 传播

### 6.1 MQTT 5.0 User Properties

```rust
/// MQTT 5.0 Trace Context 传播
pub mod mqtt5_propagation {
    use super::*;
    use opentelemetry::propagation::Injector;
    use std::collections::HashMap;
    
    pub fn inject_trace_context(
        context: &Context,
    ) -> HashMap<String, String> {
        let mut user_properties = HashMap::new();
        
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(
                context,
                &mut UserPropertiesInjector(&mut user_properties),
            );
        });
        
        user_properties
    }
    
    pub fn extract_trace_context(
        user_properties: &HashMap<String, String>,
    ) -> Context {
        global::get_text_map_propagator(|propagator| {
            propagator.extract(&UserPropertiesExtractor(user_properties))
        })
    }
}
```

### 6.2 MQTT 3.1.1 变通方案

```rust
/// MQTT 3.1.1 Trace Context 编码/解码
pub mod mqtt3_payload_encoding {
    use super::*;
    use serde::{Deserialize, Serialize};
    
    #[derive(Serialize, Deserialize)]
    struct PayloadWithTrace {
        trace_context: HashMap<String, String>,
        data: Vec<u8>,
    }
    
    /// 编码: Payload + Trace Context
    pub fn encode_payload_with_trace(
        payload: Vec<u8>,
        context: &Context,
    ) -> anyhow::Result<Vec<u8>> {
        let mut trace_context = HashMap::new();
        
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(
                context,
                &mut UserPropertiesInjector(&mut trace_context),
            );
        });
        
        let wrapper = PayloadWithTrace {
            trace_context,
            data: payload,
        };
        
        serde_json::to_vec(&wrapper).map_err(Into::into)
    }
    
    /// 解码: 提取 Payload 和 Trace Context
    pub fn decode_payload_with_trace(
        encoded: Vec<u8>,
    ) -> anyhow::Result<(Vec<u8>, Context)> {
        let wrapper: PayloadWithTrace = serde_json::from_slice(&encoded)?;
        
        let context = global::get_text_map_propagator(|propagator| {
            propagator.extract(&UserPropertiesExtractor(&wrapper.trace_context))
        });
        
        Ok((wrapper.data, context))
    }
}
```

### 6.3 W3C Trace Context 集成

```rust
use opentelemetry::propagation::TraceContextPropagator;

/// 初始化 W3C Trace Context Propagator
pub fn init_trace_propagator() {
    global::set_text_map_propagator(TraceContextPropagator::new());
}
```

---

## 7. 完整示例

### 7.1 温度传感器 Publisher

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct TemperatureReading {
    sensor_id: String,
    temperature: f32,
    humidity: f32,
    timestamp: i64,
}

pub async fn temperature_sensor_publisher() -> anyhow::Result<()> {
    // 初始化 Tracing
    init_trace_propagator();
    
    // MQTT 配置
    let mut mqtt_opts = MqttOptions::new(
        "temp-sensor-001",
        "mqtt.example.com",
        1883,
    );
    mqtt_opts.set_keep_alive(std::time::Duration::from_secs(30));
    
    let mqtt_attrs = MqttAttributes::new(
        "mqtt.example.com",
        1883,
        "temp-sensor-001",
        "home/living-room/temperature",
        MqttQoS::AtLeastOnce,
    );
    
    let publisher = MqttPublisher::new(mqtt_opts, mqtt_attrs).await?;
    
    // 定期发布温度数据
    let mut interval = tokio::time::interval(
        std::time::Duration::from_secs(60)
    );
    
    loop {
        interval.tick().await;
        
        let reading = TemperatureReading {
            sensor_id: "temp-sensor-001".to_string(),
            temperature: 22.5,
            humidity: 45.0,
            timestamp: chrono::Utc::now().timestamp(),
        };
        
        let payload = serde_json::to_vec(&reading)?;
        
        publisher.publish_with_tracing(
            "home/living-room/temperature",
            payload,
            QoS::AtLeastOnce,
            false,
        ).await?;
    }
}
```

### 7.2 数据采集 Subscriber

```rust
pub async fn data_collector_subscriber() -> anyhow::Result<()> {
    init_trace_propagator();
    
    let mut mqtt_opts = MqttOptions::new(
        "data-collector",
        "mqtt.example.com",
        1883,
    );
    mqtt_opts.set_keep_alive(std::time::Duration::from_secs(30));
    
    let mqtt_attrs = MqttAttributes::new(
        "mqtt.example.com",
        1883,
        "data-collector",
        "home/+/temperature",
        MqttQoS::AtLeastOnce,
    );
    
    let subscriber = MqttSubscriber::new(mqtt_opts, mqtt_attrs).await?;
    
    subscriber.subscribe_with_tracing(
        "home/+/temperature",
        QoS::AtLeastOnce,
        |payload| {
            let reading: TemperatureReading = serde_json::from_slice(&payload)?;
            
            tracing::info!(
                "Received from {}: temp={}°C, humidity={}%",
                reading.sensor_id,
                reading.temperature,
                reading.humidity
            );
            
            // 存储到数据库
            store_to_database(&reading)?;
            
            Ok(())
        },
    ).await?;
    
    Ok(())
}

fn store_to_database(reading: &TemperatureReading) -> anyhow::Result<()> {
    // 数据库存储逻辑
    Ok(())
}
```

### 7.3 智能家居网关

```rust
/// 智能家居网关 - 同时作为 Publisher 和 Subscriber
pub struct SmartHomeGateway {
    publisher: MqttPublisher,
    subscriber: MqttSubscriber,
}

impl SmartHomeGateway {
    pub async fn new() -> anyhow::Result<Self> {
        let mqtt_opts = MqttOptions::new(
            "smart-home-gateway",
            "mqtt.example.com",
            1883,
        );
        
        let pub_attrs = MqttAttributes::new(
            "mqtt.example.com",
            1883,
            "smart-home-gateway",
            "home/gateway/status",
            MqttQoS::AtLeastOnce,
        );
        
        let sub_attrs = pub_attrs.clone();
        
        Ok(Self {
            publisher: MqttPublisher::new(mqtt_opts.clone(), pub_attrs).await?,
            subscriber: MqttSubscriber::new(mqtt_opts, sub_attrs).await?,
        })
    }
    
    pub async fn run(&self) -> anyhow::Result<()> {
        // 订阅所有设备消息
        let publisher_clone = self.publisher.clone();
        
        tokio::spawn(async move {
            subscriber.subscribe_with_tracing(
                "home/#",
                QoS::AtLeastOnce,
                move |payload| {
                    // 处理设备消息并转发到云端
                    process_device_message(&publisher_clone, payload)
                },
            ).await
        });
        
        Ok(())
    }
}

fn process_device_message(
    publisher: &MqttPublisher,
    payload: Vec<u8>,
) -> anyhow::Result<()> {
    // 业务逻辑
    Ok(())
}
```

---

## 8. Metrics 实现

### 8.1 Publisher Metrics

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct MqttPublisherMetrics {
    messages_published: Counter<u64>,
    publish_duration: Histogram<f64>,
    publish_errors: Counter<u64>,
    message_size: Histogram<f64>,
}

impl MqttPublisherMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            messages_published: meter
                .u64_counter("mqtt.publisher.messages.published")
                .with_description("Total messages published")
                .init(),
            
            publish_duration: meter
                .f64_histogram("mqtt.publisher.publish.duration")
                .with_description("Publish duration in seconds")
                .with_unit("s")
                .init(),
            
            publish_errors: meter
                .u64_counter("mqtt.publisher.publish.errors")
                .with_description("Total publish errors")
                .init(),
            
            message_size: meter
                .f64_histogram("mqtt.publisher.message.size")
                .with_description("Message size in bytes")
                .with_unit("bytes")
                .init(),
        }
    }
    
    pub fn record_publish(&self, topic: &str, size: usize, duration: f64, success: bool) {
        let labels = [
            KeyValue::new("topic", topic.to_string()),
            KeyValue::new("success", success),
        ];
        
        self.messages_published.add(1, &labels);
        self.publish_duration.record(duration, &labels);
        self.message_size.record(size as f64, &labels);
        
        if !success {
            self.publish_errors.add(1, &labels);
        }
    }
}
```

### 8.2 Subscriber Metrics

```rust
pub struct MqttSubscriberMetrics {
    messages_received: Counter<u64>,
    processing_duration: Histogram<f64>,
    processing_errors: Counter<u64>,
}

impl MqttSubscriberMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            messages_received: meter
                .u64_counter("mqtt.subscriber.messages.received")
                .with_description("Total messages received")
                .init(),
            
            processing_duration: meter
                .f64_histogram("mqtt.subscriber.processing.duration")
                .with_description("Message processing duration")
                .with_unit("s")
                .init(),
            
            processing_errors: meter
                .u64_counter("mqtt.subscriber.processing.errors")
                .with_description("Total processing errors")
                .init(),
        }
    }
}
```

### 8.3 连接质量 Metrics

```rust
pub struct MqttConnectionMetrics {
    connection_uptime: Histogram<f64>,
    reconnections: Counter<u64>,
    connection_errors: Counter<u64>,
}

impl MqttConnectionMetrics {
    pub fn record_reconnection(&self, reason: &str) {
        self.reconnections.add(
            1,
            &[KeyValue::new("reason", reason.to_string())],
        );
    }
}
```

---

## 9. 高级特性

### 9.1 Retained Messages

```rust
impl MqttPublisher {
    /// 发布 Retained 消息
    pub async fn publish_retained(
        &self,
        topic: &str,
        payload: Vec<u8>,
    ) -> anyhow::Result<()> {
        let mut span = self.tracer
            .span_builder("mqtt_publish_retained")
            .with_kind(SpanKind::Producer)
            .start(&self.tracer);
        
        span.set_attribute(KeyValue::new(
            mqtt_conventions::MESSAGING_MQTT_RETAINED,
            true,
        ));
        
        self.client
            .publish(topic, QoS::AtLeastOnce, true, payload)
            .await?;
        
        span.set_status(Status::Ok);
        span.end();
        
        Ok(())
    }
}
```

### 9.2 Last Will Testament

```rust
/// 配置 Last Will Testament
pub fn configure_last_will(mqtt_opts: &mut MqttOptions, client_id: &str) {
    let lwt_topic = format!("device/{}/status", client_id);
    let lwt_payload = serde_json::json!({
        "status": "offline",
        "timestamp": chrono::Utc::now().timestamp(),
    }).to_string();
    
    mqtt_opts.set_last_will(rumqttc::LastWill {
        topic: lwt_topic,
        message: lwt_payload.into_bytes().into(),
        qos: QoS::AtLeastOnce,
        retain: true,
    });
}
```

### 9.3 持久会话

```rust
/// 配置持久会话
pub fn configure_persistent_session(
    mqtt_opts: &mut MqttOptions,
    clean_session: bool,
) {
    mqtt_opts.set_clean_session(clean_session);
    
    if !clean_session {
        // 持久会话配置
        mqtt_opts.set_keep_alive(std::time::Duration::from_secs(60));
    }
}
```

---

## 10. 最佳实践

### 10.1 性能优化

```rust
pub mod performance {
    /// 批量发布优化
    pub async fn batch_publish(
        publisher: &MqttPublisher,
        messages: Vec<(String, Vec<u8>)>,
    ) -> anyhow::Result<()> {
        // 使用异步并发发布
        let tasks: Vec<_> = messages
            .into_iter()
            .map(|(topic, payload)| {
                let publisher = publisher.clone();
                tokio::spawn(async move {
                    publisher.publish_with_tracing(
                        &topic,
                        payload,
                        QoS::AtMostOnce,
                        false,
                    ).await
                })
            })
            .collect();
        
        for task in tasks {
            task.await??;
        }
        
        Ok(())
    }
}
```

### 10.2 可靠性保证

```rust
pub mod reliability {
    /// 带重试的发布
    pub async fn publish_with_retry(
        publisher: &MqttPublisher,
        topic: &str,
        payload: Vec<u8>,
        max_retries: usize,
    ) -> anyhow::Result<()> {
        let mut attempts = 0;
        
        loop {
            match publisher.publish_with_tracing(
                topic,
                payload.clone(),
                QoS::AtLeastOnce,
                false,
            ).await {
                Ok(_) => return Ok(()),
                Err(e) if attempts < max_retries => {
                    attempts += 1;
                    tracing::warn!(
                        "Publish failed (attempt {}/{}): {}",
                        attempts,
                        max_retries,
                        e
                    );
                    tokio::time::sleep(
                        std::time::Duration::from_secs(2_u64.pow(attempts as u32))
                    ).await;
                }
                Err(e) => return Err(e),
            }
        }
    }
}
```

### 10.3 错误处理

```rust
#[derive(thiserror::Error, Debug)]
pub enum MqttError {
    #[error("Connection error: {0}")]
    ConnectionError(String),
    
    #[error("Publish error: {0}")]
    PublishError(String),
    
    #[error("Subscribe error: {0}")]
    SubscribeError(String),
    
    #[error("Protocol error: {0}")]
    ProtocolError(String),
}
```

---

## 参考资源

### 官方文档

1. **MQTT 3.1.1 Specification**: <https://docs.oasis-open.org/mqtt/mqtt/v3.1.1/mqtt-v3.1.1.html>
2. **MQTT 5.0 Specification**: <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html>
3. **OpenTelemetry Messaging Conventions**: <https://opentelemetry.io/docs/specs/semconv/messaging/>

### Rust Crates

1. **rumqttc**: <https://github.com/bytebeamio/rumqtt>
2. **paho-mqtt**: <https://github.com/eclipse/paho.mqtt.rust>
3. **opentelemetry-rust**: <https://github.com/open-telemetry/opentelemetry-rust>

### IoT 资源

1. **MQTT Essentials**: <https://www.hivemq.com/mqtt-essentials/>
2. **Eclipse Mosquitto**: <https://mosquitto.org/>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
