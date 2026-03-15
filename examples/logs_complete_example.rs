//! Complete Logging Example
//!
//! This example demonstrates comprehensive logging features:
//! - Basic logging with different severity levels
//! - Structured logging with attributes
//! - Log severity filtering
//! - Log-trace correlation
//! - Batch processing
//!
//! Run with: cargo run --example logs_complete_example

use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use otlp::{
    data::{AttributeValue, LogBody, LogTraceContext, SeverityLevel},
    logs::{
        LogRecord, LogRecordBuilder, LogProcessor, SimpleLogProcessor, BatchLogProcessor,
        SeverityFilter, SourceLocation,
        exporter::{LogExporter, LogExporterBuilder, LogExportResult},
        processor::BatchProcessorConfig,
    },
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║              Complete Logging Example                        ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ====================================================================================
    // SECTION 1: Basic Logging
    // ====================================================================================
    println!("📝 SECTION 1: Basic Logging");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create logs using convenience methods
    println!("1️⃣  Convenience Methods:");
    println!("─────────────────────────────────────────────────────────────────");
    
    let trace_log = LogRecord::trace("Function entry: process_payment");
    let debug_log = LogRecord::debug("Database connection pool: 10/20 active");
    let info_log = LogRecord::info("Payment processed successfully");
    let warn_log = LogRecord::warn("High memory usage: 78%");
    let error_log = LogRecord::error("Database connection failed");
    let fatal_log = LogRecord::fatal("Critical system failure - shutting down");

    print_log(&trace_log, "TRACE");
    print_log(&debug_log, "DEBUG");
    print_log(&info_log, "INFO");
    print_log(&warn_log, "WARN");
    print_log(&error_log, "ERROR");
    print_log(&fatal_log, "FATAL");

    // ====================================================================================
    // SECTION 2: Structured Logging with Builder
    // ====================================================================================
    println!("\n📝 SECTION 2: Structured Logging with Builder");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("1️⃣  User Login Event:");
    println!("─────────────────────────────────────────────────────────────────");
    let login_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Info)
        .with_message("User login successful")
        .with_attribute("user.id", AttributeValue::Int(12345))
        .with_attribute("user.username", AttributeValue::String("alice@example.com".to_string()))
        .with_attribute("auth.method", AttributeValue::String("password".to_string()))
        .with_attribute("auth.mfa_used", AttributeValue::Bool(true))
        .with_attribute("client.ip", AttributeValue::String("192.168.1.100".to_string()))
        .with_attribute("client.user_agent", AttributeValue::String("Mozilla/5.0...".to_string()))
        .with_source_location("auth/handlers.rs", 42, 15)
        .build();
    
    print_structured_log(&login_log);

    println!("\n2️⃣  HTTP Request Event:");
    println!("─────────────────────────────────────────────────────────────────");
    let http_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Info)
        .with_message("HTTP request completed")
        .with_attribute("http.method", AttributeValue::String("POST".to_string()))
        .with_attribute("http.route", AttributeValue::String("/api/v1/users".to_string()))
        .with_attribute("http.status_code", AttributeValue::Int(201))
        .with_attribute("http.request_size", AttributeValue::Int(1024))
        .with_attribute("http.response_size", AttributeValue::Int(512))
        .with_attribute("http.duration_ms", AttributeValue::Double(45.23))
        .with_attributes([
            ("service.name", AttributeValue::String("user-service".to_string())),
            ("service.version", AttributeValue::String("1.2.3".to_string())),
        ])
        .build();
    
    print_structured_log(&http_log);

    println!("\n3️⃣  Database Query Event:");
    println!("─────────────────────────────────────────────────────────────────");
    let db_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Debug)
        .with_message("Database query executed")
        .with_attribute("db.system", AttributeValue::String("postgresql".to_string()))
        .with_attribute("db.statement", AttributeValue::String("SELECT * FROM users WHERE id = $1".to_string()))
        .with_attribute("db.operation", AttributeValue::String("SELECT".to_string()))
        .with_attribute("db.rows_affected", AttributeValue::Int(1))
        .with_attribute("db.duration_ms", AttributeValue::Double(2.5))
        .with_attribute("db.connection_id", AttributeValue::String("conn-12345".to_string()))
        .build();
    
    print_structured_log(&db_log);

    println!("\n4️⃣  Error with Context:");
    println!("─────────────────────────────────────────────────────────────────");
    let error_context_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Error)
        .with_message("Payment processing failed")
        .with_attribute("error.type", AttributeValue::String("PaymentGatewayError".to_string()))
        .with_attribute("error.code", AttributeValue::String("CARD_DECLINED".to_string()))
        .with_attribute("error.retryable", AttributeValue::Bool(false))
        .with_attribute("payment.id", AttributeValue::String("pay_abc123".to_string()))
        .with_attribute("payment.amount", AttributeValue::Double(99.99))
        .with_attribute("payment.currency", AttributeValue::String("USD".to_string()))
        .with_attribute("payment.gateway", AttributeValue::String("stripe".to_string()))
        .with_source_location_full("payments/processor.rs", 156, 10, "process_payment")
        .build();
    
    print_structured_log(&error_context_log);

    // ====================================================================================
    // SECTION 3: Log Severity Levels
    // ====================================================================================
    println!("\n📝 SECTION 3: Log Severity Levels");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("Severity levels (OTLP specification):");
    println!("─────────────────────────────────────────────────────────────────");
    
    let levels = vec![
        SeverityLevel::Trace,
        SeverityLevel::Debug,
        SeverityLevel::Info,
        SeverityLevel::Warn,
        SeverityLevel::Error,
        SeverityLevel::Fatal,
    ];

    for level in levels {
        println!("   {:?}", level);
        println!("      Number: {}", level as u8);
        println!("      Short name: {}", level.short_name());
        println!("      Is error: {}", level.is_error());
        println!("      Is warning: {}", level.is_warn());
    }

    // ====================================================================================
    // SECTION 4: Log-Trace Correlation
    // ====================================================================================
    println!("\n🔗 SECTION 4: Log-Trace Correlation");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("Correlating logs with distributed traces:");
    println!("─────────────────────────────────────────────────────────────────");

    // Simulate a trace context
    let trace_id = "abc123def45678901234567890abcdef";
    let span_id = "span1234567890";

    // Log with trace correlation
    let correlated_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Info)
        .with_message("Processing order #12345")
        .with_trace_context(LogTraceContext {
            trace_id: trace_id.to_string(),
            span_id: span_id.to_string(),
            trace_flags: 1,
        })
        .with_attribute("order.id", AttributeValue::String("order-12345".to_string()))
        .with_attribute("order.total", AttributeValue::Double(250.00))
        .build();

    print_correlated_log(&correlated_log);

    // Another log in the same trace
    let another_correlated_log = LogRecordBuilder::new()
        .with_severity(SeverityLevel::Debug)
        .with_message("Validating payment method")
        .with_trace_ids(trace_id, "span0987654321")
        .with_attribute("payment.method", AttributeValue::String("credit_card".to_string()))
        .with_attribute("validation.step", AttributeValue::String("cvv_check".to_string()))
        .build();

    print_correlated_log(&another_correlated_log);

    println!("\n   💡 Tip: Use trace correlation to find all logs related to a specific request");
    println!("      Query example: trace_id = \"{}\"", trace_id);

    // ====================================================================================
    // SECTION 5: Log Filtering
    // ====================================================================================
    println!("\n🔍 SECTION 5: Log Filtering");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create a collection of logs
    let all_logs = vec![
        LogRecord::trace("Trace message 1"),
        LogRecord::debug("Debug message 1"),
        LogRecord::debug("Debug message 2"),
        LogRecord::info("Info message 1"),
        LogRecord::info("Info message 2"),
        LogRecord::info("Info message 3"),
        LogRecord::warn("Warning message 1"),
        LogRecord::error("Error message 1"),
        LogRecord::error("Error message 2"),
        LogRecord::fatal("Fatal message 1"),
    ];

    println!("Total logs: {}", all_logs.len());
    println!("─────────────────────────────────────────────────────────────────");

    // Filter at different levels
    let filter_levels = vec![
        SeverityLevel::Trace,
        SeverityLevel::Debug,
        SeverityLevel::Info,
        SeverityLevel::Warn,
        SeverityLevel::Error,
        SeverityLevel::Fatal,
    ];

    for filter_level in filter_levels {
        let filter = SeverityFilter::new(filter_level);
        let filtered: Vec<_> = all_logs.iter()
            .filter(|log| filter.allows(log))
            .collect();
        
        println!("   Filter ≥ {:?}: {} logs pass", filter_level, filtered.len());
    }

    // Demonstrate programmatic filtering
    println!("\n1️⃣  Programmatic Filtering Example:");
    println!("─────────────────────────────────────────────────────────────────");
    
    let production_filter = SeverityFilter::new(SeverityLevel::Info);
    let development_filter = SeverityFilter::new(SeverityLevel::Debug);

    println!("   Production (≥ INFO):");
    for log in &all_logs {
        if production_filter.allows(log) {
            println!("      ✓ {:?}", log.severity);
        } else {
            println!("      ✗ {:?} (filtered)", log.severity);
        }
    }

    // ====================================================================================
    // SECTION 6: Different Body Types
    // ====================================================================================
    println!("\n📝 SECTION 6: Different Body Types");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("1️⃣  String Body (Simple message):");
    println!("─────────────────────────────────────────────────────────────────");
    let string_log = LogRecordBuilder::new()
        .with_message("Simple text message")
        .with_severity(SeverityLevel::Info)
        .build();
    println!("   Body type: String");
    println!("   Content: {:?}\n", string_log.body);

    println!("2️⃣  Structured Body (Key-value pairs):");
    println!("─────────────────────────────────────────────────────────────────");
    let mut structured_body = HashMap::new();
    structured_body.insert("event_type".to_string(), AttributeValue::String("user_action".to_string()));
    structured_body.insert("action".to_string(), AttributeValue::String("button_click".to_string()));
    structured_body.insert("element_id".to_string(), AttributeValue::String("submit-btn".to_string()));
    structured_body.insert("timestamp_ms".to_string(), AttributeValue::Int(1234567890));
    
    let structured_log = LogRecordBuilder::new()
        .with_structured_body(structured_body)
        .with_severity(SeverityLevel::Info)
        .build();
    println!("   Body type: Structured");
    println!("   Content: {:?}\n", structured_log.body);

    println!("3️⃣  Array Body (List of values):");
    println!("─────────────────────────────────────────────────────────────────");
    let array_body = vec![
        AttributeValue::String("item1".to_string()),
        AttributeValue::String("item2".to_string()),
        AttributeValue::Int(42),
        AttributeValue::Bool(true),
    ];
    
    let array_log = LogRecordBuilder::new()
        .with_array_body(array_body)
        .with_severity(SeverityLevel::Debug)
        .build();
    println!("   Body type: Array");
    println!("   Content: {:?}\n", array_log.body);

    // ====================================================================================
    // SECTION 7: Batch Processing
    // ====================================================================================
    println!("\n📦 SECTION 7: Batch Processing");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create an exporter
    let exporter = LogExporterBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build();

    // Create a batch processor
    let batch_config = BatchProcessorConfig {
        max_queue_size: 1000,
        batch_size: 100,
        export_timeout: Duration::from_secs(5),
        schedule_delay: Duration::from_secs(1),
    };

    let batch_processor = BatchLogProcessor::new(exporter, batch_config);

    println!("Batch processor configuration:");
    println!("   Max queue size: {}", batch_config.max_queue_size);
    println!("   Batch size: {}", batch_config.batch_size);
    println!("   Export timeout: {:?}", batch_config.export_timeout);
    println!("   Schedule delay: {:?}", batch_config.schedule_delay);

    // Emit logs in batch
    println!("\nEmitting 10 logs in batch...");
    for i in 0..10 {
        let log = LogRecordBuilder::new()
            .with_message(format!("Batch log message {}", i + 1))
            .with_severity(SeverityLevel::Info)
            .with_attribute("batch.id", AttributeValue::Int(i))
            .with_attribute("batch.total", AttributeValue::Int(10))
            .build();
        
        if let Err(e) = batch_processor.emit(log).await {
            eprintln!("   Warning: Failed to emit log: {}", e);
        }
    }

    // Force flush
    println!("\nForcing flush...");
    match batch_processor.force_flush().await {
        Ok(result) => println!("   ✅ Flushed {} logs successfully", result.success_count),
        Err(e) => println!("   ⚠️  Flush warning: {}", e),
    }

    // Shutdown
    println!("Shutting down processor...");
    match batch_processor.shutdown().await {
        Ok(_) => println!("   ✅ Shutdown complete"),
        Err(e) => println!("   ⚠️  Shutdown warning: {}", e),
    }

    // ====================================================================================
    // SECTION 8: Log Comparison and Ordering
    // ====================================================================================
    println!("\n📝 SECTION 8: Log Comparison and Ordering");
    println!("═════════════════════════════════════════════════════════════════\n");

    let logs_for_comparison = vec![
        LogRecord::error("Critical error"),
        LogRecord::info("Info message"),
        LogRecord::fatal("Fatal error"),
        LogRecord::debug("Debug info"),
        LogRecord::warn("Warning"),
        LogRecord::trace("Trace info"),
    ];

    println!("Unsorted logs:");
    for (i, log) in logs_for_comparison.iter().enumerate() {
        println!("   {}. {:?}", i + 1, log.severity);
    }

    // Sort by severity (descending - most severe first)
    let mut sorted_logs = logs_for_comparison.clone();
    sorted_logs.sort_by(|a, b| {
        (b.severity as u8).cmp(&(a.severity as u8))
    });

    println!("\nSorted by severity (most severe first):");
    for (i, log) in sorted_logs.iter().enumerate() {
        println!("   {}. {:?}", i + 1, log.severity);
    }

    // Severity comparisons
    let info_log = LogRecord::info("Test");
    let error_log = LogRecord::error("Test");
    
    println!("\nSeverity comparisons:");
    println!("   INFO >= DEBUG: {}", info_log.is_at_least(SeverityLevel::Debug));
    println!("   INFO >= INFO: {}", info_log.is_at_least(SeverityLevel::Info));
    println!("   INFO >= ERROR: {}", info_log.is_at_least(SeverityLevel::Error));
    println!("   ERROR >= INFO: {}", error_log.is_at_least(SeverityLevel::Info));

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                    Summary                                   ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║                                                              ║");
    println!("║  ✅ Basic logging (convenience methods)                      ║");
    println!("║  ✅ Structured logging (attributes, source location)         ║");
    println!("║  ✅ Severity levels (Trace to Fatal)                         ║");
    println!("║  ✅ Log-trace correlation (distributed tracing)              ║");
    println!("║  ✅ Log filtering (severity-based)                           ║");
    println!("║  ✅ Different body types (String, Structured, Array)         ║");
    println!("║  ✅ Batch processing (efficient export)                      ║");
    println!("║  ✅ Log comparison and ordering                              ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    println!("\n📚 Reference: https://opentelemetry.io/docs/specs/otel/logs/");
    println!("   OTLP Logs signal is stable as of OTLP 1.0");

    Ok(())
}

/// Helper function to print a basic log
fn print_log(log: &LogRecord, level_name: &str) {
    println!("   [{:5}] {}", level_name, log.message().unwrap_or("<structured>"));
}

/// Helper function to print a structured log with attributes
fn print_structured_log(log: &LogRecord) {
    println!("   Severity: {:?}", log.severity);
    println!("   Message: {}", log.message().unwrap_or("<structured>"));
    println!("   Timestamp: {:?}", log.timestamp);
    
    if !log.attributes.is_empty() {
        println!("   Attributes:");
        for (key, value) in &log.attributes {
            println!("      • {} = {}", key, format_value(value));
        }
    }
    
    if let Some(ref source) = log.source_location {
        println!("   Source: {}:{}:{}", source.file, source.line, source.column);
        if let Some(ref func) = source.function_name {
            println!("   Function: {}", func);
        }
    }
    
    println!();
}

/// Helper function to print a correlated log
fn print_correlated_log(log: &LogRecord) {
    println!("   Severity: {:?}", log.severity);
    println!("   Message: {}", log.message().unwrap_or("<structured>"));
    
    if let Some(ref ctx) = log.trace_context {
        println!("   Trace ID: {}", ctx.trace_id);
        println!("   Span ID: {}", ctx.span_id);
        println!("   Trace Flags: {}", ctx.trace_flags);
    }
    
    if !log.attributes.is_empty() {
        println!("   Attributes:");
        for (key, value) in &log.attributes {
            println!("      • {} = {}", key, format_value(value));
        }
    }
    
    println!();
}

/// Helper function to format attribute values
fn format_value(value: &AttributeValue) -> String {
    match value {
        AttributeValue::String(s) => format!("\"{}\"", s),
        AttributeValue::Int(i) => i.to_string(),
        AttributeValue::Double(d) => format!("{:.2}", d),
        AttributeValue::Bool(b) => b.to_string(),
        AttributeValue::Array(arr) => format!("[{} items]", arr.len()),
        AttributeValue::Map(m) => format!("{{{} entries}}", m.len()),
    }
}
