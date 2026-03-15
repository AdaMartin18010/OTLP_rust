//! Log correlation with traces example
//!
//! Demonstrates how to correlate logs with trace context.
//!
//! Run with: cargo run --example logs_correlation

use otlp::data::{AttributeValue, LogTraceContext};
use otlp::logs::{LogRecord, SeverityLevel};
use otlp::logs::processor::{BatchLogProcessor, LogProcessor, FilterLogProcessor};
use otlp::logs::exporter::{LogExporter, LogExporterBuilder};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== OTLP Log Correlation Example ===\n");

    // Create exporter and processor
    let exporter = LogExporterBuilder::new()
        .with_endpoint("http://localhost:4317")
        .build();

    let batch_processor = BatchLogProcessor::new(exporter);

    // Create a filter processor that only allows INFO and above
    let processor = FilterLogProcessor::with_severity_filter(batch_processor, SeverityLevel::Info);

    // Simulate a distributed trace
    let trace_id = "a1b2c3d4e5f678901234567890123456";
    let span_id_1 = "1234567890abcdef";
    let span_id_2 = "fedcba0987654321";

    println!("Simulating distributed trace...");
    println!("  Trace ID: {}", trace_id);
    println!("  Span 1:   {} (Request handling)", span_id_1);
    println!("  Span 2:   {} (Database query)", span_id_2);

    // Log 1: Request received (linked to span 1)
    println!("\n1. Request received:");
    let log1 = LogRecord::builder()
        .with_severity(SeverityLevel::Info)
        .with_message("HTTP request received")
        .with_trace_context(LogTraceContext::with_sampling(trace_id, span_id_1, true))
        .with_attribute("http.method", AttributeValue::String("POST".to_string()))
        .with_attribute("http.path", AttributeValue::String("/api/users".to_string()))
        .with_attribute("http.remote_addr", AttributeValue::String("10.0.0.1".to_string()))
        .build();

    println!("   Log: {}", log1.message().unwrap_or(""));
    println!("   Trace: {}", log1.trace_context.as_ref().map(|c| c.trace_id.clone()).unwrap_or_default());
    processor.emit(log1).await?;

    // Log 2: Database query (linked to span 2)
    println!("\n2. Database query:");
    let log2 = LogRecord::builder()
        .with_severity(SeverityLevel::Debug) // This will be filtered out
        .with_message("Executing SQL query")
        .with_trace_context(LogTraceContext::new(trace_id, span_id_2))
        .with_attribute("db.system", AttributeValue::String("postgresql".to_string()))
        .with_attribute("db.statement", AttributeValue::String(
            "SELECT * FROM users WHERE id = $1".to_string()))
        .with_attribute("db.user", AttributeValue::String("app_user".to_string()))
        .build();

    println!("   Log: {}", log2.message().unwrap_or(""));
    println!("   Trace: {}", log2.trace_context.as_ref().map(|c| c.trace_id.clone()).unwrap_or_default());
    processor.emit(log2).await?;
    println!("   Note: This DEBUG log is filtered out by severity filter");

    // Log 3: User created (linked to span 1)
    println!("\n3. User created:");
    let log3 = LogRecord::builder()
        .with_severity(SeverityLevel::Info)
        .with_message("User successfully created")
        .with_trace_context(LogTraceContext::with_sampling(trace_id, span_id_1, true))
        .with_attribute("user.id", AttributeValue::String("user_789".to_string()))
        .with_attribute("user.email", AttributeValue::String("alice@example.com".to_string()))
        .with_attribute("event.outcome", AttributeValue::String("success".to_string()))
        .build();

    println!("   Log: {}", log3.message().unwrap_or(""));
    processor.emit(log3).await?;

    // Log 4: Warning about slow query (linked to span 2)
    println!("\n4. Slow query warning:");
    let log4 = LogRecord::builder()
        .with_severity(SeverityLevel::Warn)
        .with_message("Slow database query detected")
        .with_trace_context(LogTraceContext::new(trace_id, span_id_2))
        .with_attribute("db.query_time_ms", AttributeValue::Int(2500))
        .with_attribute("db.threshold_ms", AttributeValue::Int(1000))
        .with_attribute("db.rows_returned", AttributeValue::Int(1))
        .build();

    println!("   Log: {}", log4.message().unwrap_or(""));
    println!("   Query time: 2500ms (threshold: 1000ms)");
    processor.emit(log4).await?;

    // Demonstrate trace context checks
    println!("\n5. Trace context validation:");
    let test_context = LogTraceContext::with_sampling(trace_id, span_id_1, true);
    println!("   Is sampled: {}", test_context.is_sampled());
    
    let unsampled_context = LogTraceContext::with_sampling(trace_id, span_id_1, false);
    println!("   Unsampled context - Is sampled: {}", unsampled_context.is_sampled());

    // Summary
    println!("\n=== Correlation Summary ===");
    println!("All logs with the same trace_id ('{}') can be correlated.", trace_id);
    println!("This enables:", );
    println!("  - Finding all logs related to a specific request");
    println!("  - Understanding the flow across services");
    println!("  - Debugging issues in distributed systems");

    // Shutdown
    processor.shutdown().await?;
    println!("\n=== Example Complete ===");

    Ok(())
}
