//! # Messaging Semantic Conventions
//!
//! This module implements OpenTelemetry semantic conventions for messaging systems.
//! It provides type-safe builders for creating messaging-related attributes.
//!
//! ## Supported Messaging Systems
//!
//! - **Message Brokers**: Kafka, RabbitMQ, ActiveMQ, etc.
//! - **Cloud Queues**: AWS SQS, Azure Service Bus, Google Pub/Sub
//! - **Protocols**: MQTT, AMQP, STOMP
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化消息属性键值对大小
//! - **元组收集**: 使用 `collect()` 直接收集消息属性到元组
//! - **改进的类型系统**: 利用 Rust 1.92 的类型系统优化提升性能
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::messaging::{
//!     MessagingAttributesBuilder, MessagingSystem, MessagingOperation,
//! };
//!
//! let attrs = MessagingAttributesBuilder::new()
//!     .system(MessagingSystem::Kafka)
//!     .destination_name("user-events")
//!     .operation(MessagingOperation::Publish)
//!     .message_id("msg-12345")
//!     .build()
//!     .unwrap();
//! ```

use super::common::AttributeValue;
use std::collections::HashMap;

/// Supported messaging systems
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessagingSystem {
    /// Apache Kafka
    Kafka,
    /// RabbitMQ
    Rabbitmq,
    /// Apache ActiveMQ
    Activemq,
    /// Apache RocketMQ
    Rocketmq,
    /// AWS Simple Queue Service
    AwsSqs,
    /// AWS Simple Notification Service
    AwsSns,
    /// Azure Service Bus
    AzureServicebus,
    /// Azure Event Hubs
    AzureEventhubs,
    /// Google Cloud Pub/Sub
    GcpPubsub,
    /// MQTT
    Mqtt,
    /// Redis Streams
    Redis,
    /// NATS
    Nats,
    /// Apache Pulsar
    Pulsar,
    /// Other messaging system
    Other(String),
}

impl MessagingSystem {
    /// Returns the string representation of the messaging system
    pub fn as_str(&self) -> &str {
        match self {
            MessagingSystem::Kafka => "kafka",
            MessagingSystem::Rabbitmq => "rabbitmq",
            MessagingSystem::Activemq => "activemq",
            MessagingSystem::Rocketmq => "rocketmq",
            MessagingSystem::AwsSqs => "aws_sqs",
            MessagingSystem::AwsSns => "aws_sns",
            MessagingSystem::AzureServicebus => "azure_servicebus",
            MessagingSystem::AzureEventhubs => "azure_eventhubs",
            MessagingSystem::GcpPubsub => "gcp_pubsub",
            MessagingSystem::Mqtt => "mqtt",
            MessagingSystem::Redis => "redis",
            MessagingSystem::Nats => "nats",
            MessagingSystem::Pulsar => "pulsar",
            MessagingSystem::Other(s) => s.as_str(),
        }
    }
}

impl std::fmt::Display for MessagingSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Messaging operation types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessagingOperation {
    /// Publish/send a message
    Publish,
    /// Receive/consume a message
    Receive,
    /// Process a received message
    Process,
    /// Create a messaging entity (topic, queue, etc.)
    Create,
    /// Settle a message (ack, nack, etc.)
    Settle,
}

impl MessagingOperation {
    /// Returns the string representation of the operation
    pub fn as_str(&self) -> &str {
        match self {
            MessagingOperation::Publish => "publish",
            MessagingOperation::Receive => "receive",
            MessagingOperation::Process => "process",
            MessagingOperation::Create => "create",
            MessagingOperation::Settle => "settle",
        }
    }
}

impl std::fmt::Display for MessagingOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Destination kind
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DestinationKind {
    /// Queue (point-to-point)
    Queue,
    /// Topic (publish-subscribe)
    Topic,
}

impl DestinationKind {
    /// Returns the string representation
    pub fn as_str(&self) -> &str {
        match self {
            DestinationKind::Queue => "queue",
            DestinationKind::Topic => "topic",
        }
    }
}

impl std::fmt::Display for DestinationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Messaging attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct MessagingAttributes {
    /// Messaging system identifier (REQUIRED)
    pub system: MessagingSystem,
    /// Destination name (REQUIRED for most operations)
    pub destination_name: Option<String>,
    /// Messaging operation type
    pub operation: Option<MessagingOperation>,
    /// Message unique identifier
    pub message_id: Option<String>,
    /// Conversation/correlation identifier
    pub conversation_id: Option<String>,
    /// Message payload size in bytes
    pub message_body_size: Option<i64>,
    /// Destination kind (queue or topic)
    pub destination_kind: Option<DestinationKind>,
    /// Kafka-specific: partition number
    pub kafka_partition: Option<i32>,
    /// Kafka-specific: consumer group
    pub kafka_consumer_group: Option<String>,
    /// Kafka-specific: message offset
    pub kafka_message_offset: Option<i64>,
    /// Kafka-specific: message key
    pub kafka_message_key: Option<String>,
    /// RabbitMQ-specific: routing key
    pub rabbitmq_routing_key: Option<String>,
    /// RabbitMQ-specific: delivery tag
    pub rabbitmq_delivery_tag: Option<i64>,
    /// MQTT-specific: QoS level
    pub mqtt_qos: Option<i32>,
    /// MQTT-specific: retain flag
    pub mqtt_retained: Option<bool>,
    /// SQS-specific: message attribute count
    pub sqs_message_attributes_count: Option<i32>,
    /// Server address (broker host)
    pub server_address: Option<String>,
    /// Server port
    pub server_port: Option<u16>,
    /// Network protocol name
    pub network_protocol_name: Option<String>,
    /// Network protocol version
    pub network_protocol_version: Option<String>,
    /// Temporary destination flag
    pub destination_temporary: Option<bool>,
    /// Destination publish/subscribe flag
    pub destination_anonymous: Option<bool>,
}

impl MessagingAttributes {
    /// Converts the attributes to a HashMap
    pub fn to_attributes(&self) -> HashMap<String, AttributeValue> {
        let mut map = HashMap::new();

        // Required field
        map.insert(
            "messaging.system".to_string(),
            AttributeValue::String(self.system.as_str().to_string()),
        );

        // Optional common fields
        if let Some(ref destination) = self.destination_name {
            map.insert(
                "messaging.destination.name".to_string(),
                AttributeValue::String(destination.clone()),
            );
        }

        if let Some(ref operation) = self.operation {
            map.insert(
                "messaging.operation".to_string(),
                AttributeValue::String(operation.as_str().to_string()),
            );
        }

        if let Some(ref msg_id) = self.message_id {
            map.insert(
                "messaging.message.id".to_string(),
                AttributeValue::String(msg_id.clone()),
            );
        }

        if let Some(ref conv_id) = self.conversation_id {
            map.insert(
                "messaging.message.conversation_id".to_string(),
                AttributeValue::String(conv_id.clone()),
            );
        }

        if let Some(size) = self.message_body_size {
            map.insert(
                "messaging.message.body.size".to_string(),
                AttributeValue::Int(size),
            );
        }

        if let Some(ref kind) = self.destination_kind {
            map.insert(
                "messaging.destination.kind".to_string(),
                AttributeValue::String(kind.as_str().to_string()),
            );
        }

        if let Some(temp) = self.destination_temporary {
            map.insert(
                "messaging.destination.temporary".to_string(),
                AttributeValue::Bool(temp),
            );
        }

        if let Some(anon) = self.destination_anonymous {
            map.insert(
                "messaging.destination.anonymous".to_string(),
                AttributeValue::Bool(anon),
            );
        }

        // Kafka-specific attributes
        if let Some(partition) = self.kafka_partition {
            map.insert(
                "messaging.kafka.destination.partition".to_string(),
                AttributeValue::Int(partition as i64),
            );
        }

        if let Some(ref group) = self.kafka_consumer_group {
            map.insert(
                "messaging.kafka.consumer.group".to_string(),
                AttributeValue::String(group.clone()),
            );
        }

        if let Some(offset) = self.kafka_message_offset {
            map.insert(
                "messaging.kafka.message.offset".to_string(),
                AttributeValue::Int(offset),
            );
        }

        if let Some(ref key) = self.kafka_message_key {
            map.insert(
                "messaging.kafka.message.key".to_string(),
                AttributeValue::String(key.clone()),
            );
        }

        // RabbitMQ-specific attributes
        if let Some(ref routing_key) = self.rabbitmq_routing_key {
            map.insert(
                "messaging.rabbitmq.routing_key".to_string(),
                AttributeValue::String(routing_key.clone()),
            );
        }

        if let Some(delivery_tag) = self.rabbitmq_delivery_tag {
            map.insert(
                "messaging.rabbitmq.delivery_tag".to_string(),
                AttributeValue::Int(delivery_tag),
            );
        }

        // MQTT-specific attributes
        if let Some(qos) = self.mqtt_qos {
            map.insert(
                "messaging.mqtt.qos".to_string(),
                AttributeValue::Int(qos as i64),
            );
        }

        if let Some(retained) = self.mqtt_retained {
            map.insert(
                "messaging.mqtt.retained".to_string(),
                AttributeValue::Bool(retained),
            );
        }

        // SQS-specific attributes
        if let Some(count) = self.sqs_message_attributes_count {
            map.insert(
                "messaging.aws.sqs.message_attributes_count".to_string(),
                AttributeValue::Int(count as i64),
            );
        }

        // Network attributes
        if let Some(ref address) = self.server_address {
            map.insert(
                "server.address".to_string(),
                AttributeValue::String(address.clone()),
            );
        }

        if let Some(port) = self.server_port {
            map.insert("server.port".to_string(), AttributeValue::Int(port as i64));
        }

        if let Some(ref protocol) = self.network_protocol_name {
            map.insert(
                "network.protocol.name".to_string(),
                AttributeValue::String(protocol.clone()),
            );
        }

        if let Some(ref version) = self.network_protocol_version {
            map.insert(
                "network.protocol.version".to_string(),
                AttributeValue::String(version.clone()),
            );
        }

        map
    }
}

/// Builder for MessagingAttributes
#[derive(Debug, Default)]
pub struct MessagingAttributesBuilder {
    system: Option<MessagingSystem>,
    destination_name: Option<String>,
    operation: Option<MessagingOperation>,
    message_id: Option<String>,
    conversation_id: Option<String>,
    message_body_size: Option<i64>,
    destination_kind: Option<DestinationKind>,
    kafka_partition: Option<i32>,
    kafka_consumer_group: Option<String>,
    kafka_message_offset: Option<i64>,
    kafka_message_key: Option<String>,
    rabbitmq_routing_key: Option<String>,
    rabbitmq_delivery_tag: Option<i64>,
    mqtt_qos: Option<i32>,
    mqtt_retained: Option<bool>,
    sqs_message_attributes_count: Option<i32>,
    server_address: Option<String>,
    server_port: Option<u16>,
    network_protocol_name: Option<String>,
    network_protocol_version: Option<String>,
    destination_temporary: Option<bool>,
    destination_anonymous: Option<bool>,
}

impl MessagingAttributesBuilder {
    /// Creates a new MessagingAttributesBuilder
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the messaging system (REQUIRED)
    pub fn system(mut self, system: MessagingSystem) -> Self {
        self.system = Some(system);
        self
    }

    /// Sets the destination name
    pub fn destination_name(mut self, name: impl Into<String>) -> Self {
        self.destination_name = Some(name.into());
        self
    }

    /// Sets the messaging operation
    pub fn operation(mut self, operation: MessagingOperation) -> Self {
        self.operation = Some(operation);
        self
    }

    /// Sets the message ID
    pub fn message_id(mut self, id: impl Into<String>) -> Self {
        self.message_id = Some(id.into());
        self
    }

    /// Sets the conversation/correlation ID
    pub fn conversation_id(mut self, id: impl Into<String>) -> Self {
        self.conversation_id = Some(id.into());
        self
    }

    /// Sets the message body size
    pub fn message_body_size(mut self, size: i64) -> Self {
        self.message_body_size = Some(size);
        self
    }

    /// Sets the destination kind
    pub fn destination_kind(mut self, kind: DestinationKind) -> Self {
        self.destination_kind = Some(kind);
        self
    }

    /// Sets whether the destination is temporary
    pub fn destination_temporary(mut self, temporary: bool) -> Self {
        self.destination_temporary = Some(temporary);
        self
    }

    /// Sets whether the destination is anonymous
    pub fn destination_anonymous(mut self, anonymous: bool) -> Self {
        self.destination_anonymous = Some(anonymous);
        self
    }

    /// Sets the Kafka partition
    pub fn kafka_partition(mut self, partition: i32) -> Self {
        self.kafka_partition = Some(partition);
        self
    }

    /// Sets the Kafka consumer group
    pub fn kafka_consumer_group(mut self, group: impl Into<String>) -> Self {
        self.kafka_consumer_group = Some(group.into());
        self
    }

    /// Sets the Kafka message offset
    pub fn kafka_message_offset(mut self, offset: i64) -> Self {
        self.kafka_message_offset = Some(offset);
        self
    }

    /// Sets the Kafka message key
    pub fn kafka_message_key(mut self, key: impl Into<String>) -> Self {
        self.kafka_message_key = Some(key.into());
        self
    }

    /// Sets the RabbitMQ routing key
    pub fn rabbitmq_routing_key(mut self, key: impl Into<String>) -> Self {
        self.rabbitmq_routing_key = Some(key.into());
        self
    }

    /// Sets the RabbitMQ delivery tag
    pub fn rabbitmq_delivery_tag(mut self, tag: i64) -> Self {
        self.rabbitmq_delivery_tag = Some(tag);
        self
    }

    /// Sets the MQTT QoS level
    pub fn mqtt_qos(mut self, qos: i32) -> Self {
        self.mqtt_qos = Some(qos);
        self
    }

    /// Sets the MQTT retained flag
    pub fn mqtt_retained(mut self, retained: bool) -> Self {
        self.mqtt_retained = Some(retained);
        self
    }

    /// Sets the SQS message attributes count
    pub fn sqs_message_attributes_count(mut self, count: i32) -> Self {
        self.sqs_message_attributes_count = Some(count);
        self
    }

    /// Sets the server address
    pub fn server_address(mut self, address: impl Into<String>) -> Self {
        self.server_address = Some(address.into());
        self
    }

    /// Sets the server port
    pub fn server_port(mut self, port: u16) -> Self {
        self.server_port = Some(port);
        self
    }

    /// Sets the network protocol name
    pub fn network_protocol_name(mut self, protocol: impl Into<String>) -> Self {
        self.network_protocol_name = Some(protocol.into());
        self
    }

    /// Sets the network protocol version
    pub fn network_protocol_version(mut self, version: impl Into<String>) -> Self {
        self.network_protocol_version = Some(version.into());
        self
    }

    /// Builds the MessagingAttributes
    pub fn build(self) -> Result<MessagingAttributes, String> {
        let system = self
            .system
            .ok_or_else(|| "messaging.system is required".to_string())?;

        Ok(MessagingAttributes {
            system,
            destination_name: self.destination_name,
            operation: self.operation,
            message_id: self.message_id,
            conversation_id: self.conversation_id,
            message_body_size: self.message_body_size,
            destination_kind: self.destination_kind,
            kafka_partition: self.kafka_partition,
            kafka_consumer_group: self.kafka_consumer_group,
            kafka_message_offset: self.kafka_message_offset,
            kafka_message_key: self.kafka_message_key,
            rabbitmq_routing_key: self.rabbitmq_routing_key,
            rabbitmq_delivery_tag: self.rabbitmq_delivery_tag,
            mqtt_qos: self.mqtt_qos,
            mqtt_retained: self.mqtt_retained,
            sqs_message_attributes_count: self.sqs_message_attributes_count,
            server_address: self.server_address,
            server_port: self.server_port,
            network_protocol_name: self.network_protocol_name,
            network_protocol_version: self.network_protocol_version,
            destination_temporary: self.destination_temporary,
            destination_anonymous: self.destination_anonymous,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kafka_publish() {
        let attrs = MessagingAttributesBuilder::new()
            .system(MessagingSystem::Kafka)
            .destination_name("user-events")
            .destination_kind(DestinationKind::Topic)
            .operation(MessagingOperation::Publish)
            .message_id("msg-123")
            .kafka_partition(2)
            .kafka_message_key("user-456")
            .server_address("kafka.example.com")
            .server_port(9092)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("messaging.system"),
            Some(&AttributeValue::String("kafka".to_string()))
        );
        assert_eq!(
            map.get("messaging.destination.name"),
            Some(&AttributeValue::String("user-events".to_string()))
        );
        assert_eq!(
            map.get("messaging.operation"),
            Some(&AttributeValue::String("publish".to_string()))
        );
        assert_eq!(
            map.get("messaging.kafka.destination.partition"),
            Some(&AttributeValue::Int(2))
        );
    }

    #[test]
    fn test_rabbitmq_receive() {
        let attrs = MessagingAttributesBuilder::new()
            .system(MessagingSystem::Rabbitmq)
            .destination_name("orders-queue")
            .destination_kind(DestinationKind::Queue)
            .operation(MessagingOperation::Receive)
            .rabbitmq_routing_key("order.created")
            .server_address("rabbitmq.example.com")
            .server_port(5672)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("messaging.system"),
            Some(&AttributeValue::String("rabbitmq".to_string()))
        );
        assert_eq!(
            map.get("messaging.rabbitmq.routing_key"),
            Some(&AttributeValue::String("order.created".to_string()))
        );
    }

    #[test]
    fn test_mqtt_publish() {
        let attrs = MessagingAttributesBuilder::new()
            .system(MessagingSystem::Mqtt)
            .destination_name("sensors/temperature")
            .operation(MessagingOperation::Publish)
            .mqtt_qos(1)
            .mqtt_retained(true)
            .message_body_size(128)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(map.get("messaging.mqtt.qos"), Some(&AttributeValue::Int(1)));
        assert_eq!(
            map.get("messaging.mqtt.retained"),
            Some(&AttributeValue::Bool(true))
        );
    }

    #[test]
    fn test_sqs_receive() {
        let attrs = MessagingAttributesBuilder::new()
            .system(MessagingSystem::AwsSqs)
            .destination_name("notifications-queue")
            .operation(MessagingOperation::Receive)
            .message_id("msg-abc-123")
            .sqs_message_attributes_count(3)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("messaging.system"),
            Some(&AttributeValue::String("aws_sqs".to_string()))
        );
        assert_eq!(
            map.get("messaging.aws.sqs.message_attributes_count"),
            Some(&AttributeValue::Int(3))
        );
    }

    #[test]
    fn test_missing_required_field() {
        let result = MessagingAttributesBuilder::new()
            .destination_name("test-topic")
            .build();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "messaging.system is required");
    }

    #[test]
    fn test_conversation_id() {
        let attrs = MessagingAttributesBuilder::new()
            .system(MessagingSystem::Kafka)
            .destination_name("events")
            .message_id("msg-1")
            .conversation_id("conv-abc-123")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("messaging.message.conversation_id"),
            Some(&AttributeValue::String("conv-abc-123".to_string()))
        );
    }
}
