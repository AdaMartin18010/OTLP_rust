//! Messaging Semantic Conventions Demo
//!
//! This example demonstrates the usage of messaging semantic conventions
//! for various messaging systems (Kafka, RabbitMQ, MQTT, SQS, etc.).

use otlp::semantic_conventions::messaging::{
    DestinationKind, MessagingAttributesBuilder, MessagingOperation, MessagingSystem,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("📨 OpenTelemetry Messaging Semantic Conventions Demo\n");
    println!("============================================================\n");

    // Demo 1: Kafka Publish
    println!("📊 Demo 1: Kafka Publish Message");
    let kafka_publish = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Kafka)
        .destination_name("user-events")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id("msg-12345")
        .kafka_partition(2)
        .kafka_message_key("user-456")
        .message_body_size(1024)
        .server_address("kafka.example.com")
        .server_port(9092)
        .build()?;

    println!("  ✅ Created Kafka publish attributes:");
    for (key, value) in kafka_publish.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 2: Kafka Consume
    println!("📊 Demo 2: Kafka Consume Message");
    let kafka_consume = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Kafka)
        .destination_name("user-events")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Receive)
        .kafka_consumer_group("analytics-service")
        .kafka_partition(2)
        .kafka_message_offset(12345)
        .server_address("kafka.example.com")
        .server_port(9092)
        .build()?;

    println!("  ✅ Created Kafka consume attributes:");
    for (key, value) in kafka_consume.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 3: RabbitMQ Publish
    println!("📊 Demo 3: RabbitMQ Publish Message");
    let rabbitmq_attrs = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Rabbitmq)
        .destination_name("orders-exchange")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id("order-789")
        .rabbitmq_routing_key("order.created")
        .message_body_size(512)
        .server_address("rabbitmq.example.com")
        .server_port(5672)
        .network_protocol_name("amqp")
        .network_protocol_version("0.9.1")
        .build()?;

    println!("  ✅ Created RabbitMQ attributes:");
    for (key, value) in rabbitmq_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 4: RabbitMQ Receive
    println!("📊 Demo 4: RabbitMQ Receive Message");
    let rabbitmq_receive = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Rabbitmq)
        .destination_name("orders-queue")
        .destination_kind(DestinationKind::Queue)
        .operation(MessagingOperation::Receive)
        .rabbitmq_routing_key("order.created")
        .rabbitmq_delivery_tag(54321)
        .server_address("rabbitmq.example.com")
        .server_port(5672)
        .build()?;

    println!("  ✅ Created RabbitMQ receive attributes:");
    for (key, value) in rabbitmq_receive.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 5: MQTT Publish
    println!("📊 Demo 5: MQTT Publish Message");
    let mqtt_attrs = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Mqtt)
        .destination_name("sensors/temperature")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id("sensor-msg-001")
        .mqtt_qos(1)
        .mqtt_retained(true)
        .message_body_size(128)
        .server_address("mqtt.example.com")
        .server_port(1883)
        .build()?;

    println!("  ✅ Created MQTT attributes:");
    for (key, value) in mqtt_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 6: AWS SQS Send
    println!("📊 Demo 6: AWS SQS Send Message");
    let sqs_send = MessagingAttributesBuilder::new()
        .system(MessagingSystem::AwsSqs)
        .destination_name("notifications-queue")
        .destination_kind(DestinationKind::Queue)
        .operation(MessagingOperation::Publish)
        .message_id("sqs-msg-abc-123")
        .message_body_size(256)
        .sqs_message_attributes_count(3)
        .build()?;

    println!("  ✅ Created SQS send attributes:");
    for (key, value) in sqs_send.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 7: AWS SQS Receive
    println!("📊 Demo 7: AWS SQS Receive Message");
    let sqs_receive = MessagingAttributesBuilder::new()
        .system(MessagingSystem::AwsSqs)
        .destination_name("notifications-queue")
        .operation(MessagingOperation::Receive)
        .message_id("sqs-msg-def-456")
        .sqs_message_attributes_count(2)
        .build()?;

    println!("  ✅ Created SQS receive attributes:");
    for (key, value) in sqs_receive.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 8: Google Pub/Sub
    println!("📊 Demo 8: Google Cloud Pub/Sub Publish");
    let pubsub_attrs = MessagingAttributesBuilder::new()
        .system(MessagingSystem::GcpPubsub)
        .destination_name("projects/my-project/topics/events")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id("pubsub-msg-789")
        .message_body_size(2048)
        .build()?;

    println!("  ✅ Created Pub/Sub attributes:");
    for (key, value) in pubsub_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 9: Full Example with Conversation ID
    println!("📊 Demo 9: Full Example with Conversation ID");
    let full_attrs = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Kafka)
        .destination_name("transaction-events")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id("tx-msg-12345")
        .conversation_id("conv-abc-xyz-789")
        .kafka_partition(5)
        .kafka_message_key("account-123")
        .message_body_size(4096)
        .server_address("kafka-cluster.example.com")
        .server_port(9092)
        .network_protocol_name("kafka")
        .network_protocol_version("3.0")
        .build()?;

    println!("  ✅ Created full messaging attributes:");
    let attributes_map = full_attrs.to_attributes();
    println!("     Total attributes: {}", attributes_map.len());
    for (key, value) in attributes_map {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    println!("✅ All messaging semantic conventions demos completed successfully!\n");

    Ok(())
}
