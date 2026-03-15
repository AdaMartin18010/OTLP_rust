//! Structured logging example
//!
//! Demonstrates structured logging with various field types.
//!
//! Run with: cargo run --example logs_structured

use otlp::data::AttributeValue;
use otlp::logs::{LogRecord, SeverityLevel, LogAppender, LogAppenderBuilder};
use otlp::logs::processor::{BatchLogProcessor, LogProcessor};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== OTLP Structured Logging Example ===\n");

    // Create a batch processor
    let exporter = otlp::logs::exporter::LogExporter::default_with_endpoint("http://localhost:4317");
    let processor = BatchLogProcessor::new(exporter);

    // Create an appender with default attributes
    let appender = LogAppenderBuilder::new()
        .with_service_name("payment-service")
        .with_service_version("2.1.0")
        .with_environment("production")
        .with_host_name("server-01")
        .build(processor);

    // Example 1: Simple structured log
    println!("1. Simple structured log:");
    let log1 = LogRecord::builder()
        .with_severity(SeverityLevel::Info)
        .with_message("Payment processed")
        .with_attribute("amount", AttributeValue::Double(99.99))
        .with_attribute("currency", AttributeValue::String("USD".to_string()))
        .with_attribute("payment_id", AttributeValue::String("pay_12345".to_string()))
        .build();
    
    appender.emit(log1).await?;
    println!("   ✓ Payment log emitted");

    // Example 2: Log with array attributes
    println!("\n2. Log with array attributes:");
    let log2 = LogRecord::builder()
        .with_severity(SeverityLevel::Debug)
        .with_message("Request headers")
        .with_attribute("methods", AttributeValue::StringArray(vec![
            "GET".to_string(),
            "POST".to_string(),
            "PUT".to_string(),
        ]))
        .with_attribute("status_codes", AttributeValue::IntArray(vec![200, 201, 204]))
        .build();
    
    appender.emit(log2).await?;
    println!("   ✓ Headers log emitted");

    // Example 3: Fully structured body (no simple message)
    println!("\n3. Fully structured log body:");
    let mut body = HashMap::new();
    body.insert("event_type".to_string(), AttributeValue::String("user_action".to_string()));
    body.insert("action".to_string(), AttributeValue::String("click".to_string()));
    body.insert("target".to_string(), AttributeValue::String("submit_button".to_string()));
    body.insert("x".to_string(), AttributeValue::Int(150));
    body.insert("y".to_string(), AttributeValue::Int(300));

    let log3 = LogRecord::builder()
        .with_severity(SeverityLevel::Info)
        .with_structured_body(body)
        .with_attribute("session_id", AttributeValue::String("sess_abc123".to_string()))
        .build();
    
    appender.emit(log3).await?;
    println!("   ✓ Structured body log emitted");

    // Example 4: Error log with stack trace context
    println!("\n4. Error log with context:");
    let log4 = LogRecord::builder()
        .with_severity(SeverityLevel::Error)
        .with_message("Database connection failed")
        .with_attribute("error_code", AttributeValue::String("DB_CONN_001".to_string()))
        .with_attribute("retry_count", AttributeValue::Int(3))
        .with_attribute("retryable", AttributeValue::Bool(true))
        .with_attribute("connection_string", AttributeValue::String(
            "postgres://db.example.com:5432/mydb".to_string()))
        .with_source_location("src/db.rs", 42, 15)
        .with_instrumentation_scope("database-layer")
        .build();
    
    appender.emit(log4).await?;
    println!("   ✓ Error log emitted");

    // Example 5: Using severity filter
    println!("\n5. Severity filtering example:");
    let logs_with_severity = vec![
        (SeverityLevel::Trace, "Trace message"),
        (SeverityLevel::Debug, "Debug message"),
        (SeverityLevel::Info, "Info message"),
        (SeverityLevel::Warn, "Warning message"),
        (SeverityLevel::Error, "Error message"),
    ];

    let filter = otlp::logs::SeverityFilter::new(SeverityLevel::Info);
    
    for (severity, message) in logs_with_severity {
        let log = LogRecord::builder()
            .with_severity(severity)
            .with_message(message)
            .build();
        
        if filter.allows(&log) {
            appender.emit(log).await?;
            println!("   ✓ {} passed filter", severity.as_str());
        } else {
            println!("   ✗ {} filtered out", severity.as_str());
        }
    }

    // Flush and shutdown
    println!("\nFlushing remaining logs...");
    appender.shutdown().await?;
    
    println!("\n=== Example Complete ===");
    Ok(())
}
