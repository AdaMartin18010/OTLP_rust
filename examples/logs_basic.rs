//! Basic logging example
//!
//! Demonstrates basic log creation, processing, and export.
//!
//! Run with: cargo run --example logs_basic

use otlp::logs::{LogRecord, LogExporter, LogExporterBuilder, SeverityLevel};
use otlp::logs::processor::{SimpleLogProcessor, LogProcessor};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== OTLP Logs Basic Example ===\n");

    // Create a log exporter
    let exporter = LogExporterBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(10))
        .build();

    // Create a simple processor
    let processor = SimpleLogProcessor::new(exporter);

    // Create and emit logs at different severity levels
    println!("Creating logs at different severity levels...");

    let logs = vec![
        LogRecord::trace("This is a trace message"),
        LogRecord::debug("This is a debug message"),
        LogRecord::info("Application started successfully"),
        LogRecord::warn("This is a warning message"),
        LogRecord::error("An error occurred"),
        LogRecord::fatal("Fatal error - system shutdown"),
    ];

    for log in logs {
        println!("  Emitting {:?}: {}", 
            log.severity, 
            log.message().unwrap_or("<structured>"));
        processor.emit(log).await?;
    }

    // Create a structured log
    println!("\nCreating structured log...");
    let structured_log = otlp::logs::LogRecord::builder()
        .with_severity(SeverityLevel::Info)
        .with_message("User login")
        .with_attribute("user_id", otlp::data::AttributeValue::Int(42))
        .with_attribute("username", otlp::data::AttributeValue::String("alice".to_string()))
        .with_attribute("ip_address", otlp::data::AttributeValue::String("192.168.1.1".to_string()))
        .build();

    processor.emit(structured_log).await?;
    println!("  Structured log emitted");

    // Force flush
    println!("\nFlushing logs...");
    let result = processor.force_flush().await?;
    println!("  Flush result: {} successful", result.success_count);

    // Shutdown
    processor.shutdown().await?;
    println!("\n=== Example Complete ===");

    Ok(())
}
