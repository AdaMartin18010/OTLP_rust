//! Severity filtering example
//!
//! Demonstrates different severity filtering approaches.
//!
//! Run with: cargo run --example logs_severity_filter

use otlp::data::AttributeValue;
use otlp::logs::{LogRecord, SeverityLevel, SeverityFilter, LogRecordBuilder};
use otlp::logs::processor::{BatchLogProcessor, FilterLogProcessor, SimpleLogProcessor, CompositeLogProcessor};
use otlp::logs::exporter::{MockLogExporter, LogExporterTrait};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== OTLP Severity Filtering Example ===\n");

    // Create a mock exporter to capture all logs
    let mock_exporter = Arc::new(MockLogExporter::new());

    // Example 1: Severity filter with different levels
    println!("1. Testing SeverityFilter with different levels:\n");
    
    let test_levels = vec![
        SeverityLevel::Trace,
        SeverityLevel::Debug,
        SeverityLevel::Info,
        SeverityLevel::Warn,
        SeverityLevel::Error,
        SeverityLevel::Fatal,
    ];

    for min_level in &[SeverityLevel::Debug, SeverityLevel::Info, SeverityLevel::Warn] {
        let filter = SeverityFilter::new(*min_level);
        println!("   Filter: allow >= {}", min_level.as_str());
        
        for level in &test_levels {
            let log = LogRecord::builder()
                .with_severity(*level)
                .with_message(format!("{} message", level.as_str()))
                .build();
            
            let allowed = filter.allows(&log);
            let status = if allowed { "✓" } else { "✗" };
            println!("     {} {}: {}", status, level.as_str(), if allowed { "PASS" } else { "BLOCK" });
        }
        println!();
    }

    // Example 2: Filter processor
    println!("2. FilterLogProcessor demonstration:");
    
    let exporter1 = Arc::new(MockLogExporter::new());
    let inner_processor = SimpleLogProcessor::with_exporter(exporter1.clone());
    let filter_processor = FilterLogProcessor::with_severity_filter(inner_processor, SeverityLevel::Warn);

    // Send logs of different severities
    let logs = vec![
        LogRecord::debug("Debug info for developers"),
        LogRecord::info("Application started"),
        LogRecord::warn("Disk space low"),
        LogRecord::error("Failed to connect to database"),
        LogRecord::fatal("System crash imminent"),
    ];

    for log in &logs {
        filter_processor.emit(log.clone()).await?;
    }

    // Check what was exported (only WARN and above)
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;
    let exported = exporter1.get_exported_logs().await;
    println!("   Sent: {} logs", logs.len());
    println!("   Exported (>= WARN): {} logs", exported.len());
    for log in &exported {
        println!("     - {}: {}", log.severity.as_str(), log.message().unwrap_or(""));
    }

    // Example 3: Attribute-based filtering
    println!("\n3. Attribute-based filtering:");
    
    let exporter2 = Arc::new(MockLogExporter::new());
    let inner_processor2 = SimpleLogProcessor::with_exporter(exporter2.clone());
    let attr_filter_processor = FilterLogProcessor::new(inner_processor2)
        .with_attribute_filter("environment", AttributeValue::String("production".to_string()));

    // Logs with different environments
    let env_logs = vec![
        LogRecord::builder()
            .with_severity(SeverityLevel::Info)
            .with_message("Production server started")
            .with_attribute("environment", AttributeValue::String("production".to_string()))
            .build(),
        LogRecord::builder()
            .with_severity(SeverityLevel::Info)
            .with_message("Development server started")
            .with_attribute("environment", AttributeValue::String("development".to_string()))
            .build(),
        LogRecord::builder()
            .with_severity(SeverityLevel::Info)
            .with_message("Another production log")
            .with_attribute("environment", AttributeValue::String("production".to_string()))
            .build(),
        LogRecord::info("Log without environment"), // No environment attribute
    ];

    for log in &env_logs {
        attr_filter_processor.emit(log.clone()).await?;
    }

    tokio::time::sleep(std::time::Duration::from_millis(50)).await;
    let exported2 = exporter2.get_exported_logs().await;
    println!("   Sent: {} logs", env_logs.len());
    println!("   Exported (env=production): {} logs", exported2.len());
    for log in &exported2 {
        println!("     - {}", log.message().unwrap_or(""));
    }

    // Example 4: Severity level properties
    println!("\n4. Severity level properties:");
    
    let error_sev = SeverityLevel::Error;
    println!("   Severity: {}", error_sev.as_str());
    println!("   Short name: {}", error_sev.short_name());
    println!("   Numeric value: {}", error_sev as u8);
    println!("   Is error: {}", error_sev.is_error());
    println!("   Is warn or higher: {}", error_sev.is_warn());

    // Example 5: Parsing severity from strings
    println!("\n5. Parsing severity from strings:");
    
    let inputs = vec!["error", "WARN", "Info", "DEBUG", "FATAL", "invalid"];
    for input in inputs {
        match SeverityLevel::from_str(input) {
            Some(level) => println!("   '{}' -> {} ({})", input, level.as_str(), level as u8),
            None => println!("   '{}' -> Unknown", input),
        }
    }

    // Example 6: Sub-level severities
    println!("\n6. Sub-level severities (OTLP 1.10):");
    
    let sub_levels = vec![
        (SeverityLevel::Debug, "DEBUG"),
        (SeverityLevel::Debug2, "DEBUG2"),
        (SeverityLevel::Debug3, "DEBUG3"),
        (SeverityLevel::Debug4, "DEBUG4"),
    ];
    
    for (level, name) in sub_levels {
        println!("   {} = {}", name, level as u8);
    }

    // Cleanup
    filter_processor.shutdown().await?;
    attr_filter_processor.shutdown().await?;

    println!("\n=== Example Complete ===");
    Ok(())
}
