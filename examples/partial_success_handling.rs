//! Partial Success Handling Example
//!
//! This example demonstrates OTLP 1.10 Partial Success handling:
//! - Handling partial success responses from the server
//! - Threshold-based acceptance strategies
//! - Error aggregation across multiple requests
//! - Metrics collection for partial successes
//!
//! Run with: cargo run --example partial_success_handling

use std::collections::HashMap;
use std::time::{Duration, Instant};

use otlp::response::{
    ExportTracePartialSuccess, ExportMetricsPartialSuccess, ExportLogsPartialSuccess,
    PartialSuccessHandler, ResponseHandler, ResponseHandlerBuilder, ResponseType,
    ResponseMetadata, SignalType, ResponseAggregator, AggregationSummary,
    ResponseMetricsCollector, RetryDecision, ClassificationResult,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║         Partial Success Handling Example                     ║");
    println!("║              OTLP 1.10 Feature                               ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ====================================================================================
    // Introduction
    // ====================================================================================
    println!("📚 Understanding Partial Success");
    println!("═════════════════════════════════════════════════════════════════\n");
    
    println!("OTLP 1.10 defines three response types:");
    println!("─────────────────────────────────────────────────────────────────");
    println!("1. FULL SUCCESS - Server accepted all data");
    println!("   → partial_success field is empty/null");
    println!("   → No further action required");
    println!("\n2. PARTIAL SUCCESS - Server accepted some data, rejected rest");
    println!("   → partial_success field contains rejection counts");
    println!("   → Client MUST NOT retry the request (per OTLP spec)");
    println!("   → Client SHOULD log warning with details");
    println!("\n3. FAILURE - Server rejected all data");
    println!("   → Error response");
    println!("   → Client MAY retry based on error type\n");

    // ====================================================================================
    // SECTION 1: Basic Partial Success Handling
    // ====================================================================================
    println!("📊 SECTION 1: Basic Partial Success Handling");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Example 1: Trace Partial Success
    println!("1️⃣  Trace Export - Partial Success");
    println!("─────────────────────────────────────────────────────────────────");
    
    let mut trace_handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(1000);
    
    // Simulate receiving a partial success response
    let trace_partial = ExportTracePartialSuccess {
        rejected_spans: 50,
        error_message: "rate limit exceeded for tenant 'acme-corp'".to_string(),
    };
    
    trace_handler.handle_trace_partial_success(&trace_partial);
    
    println!("   Request: Exported 1000 spans");
    println!("   Response: Partial Success");
    println!("   ─────────────────────────────");
    println!("   Total spans: {}", trace_handler.total_count());
    println!("   Accepted: {}", trace_handler.success_count());
    println!("   Rejected: {}", trace_handler.rejected_count());
    println!("   Success rate: {:.1}%", trace_handler.success_rate() * 100.0);
    println!("   Error: {}", trace_handler.error_message().unwrap_or("none"));
    
    // Check against threshold
    let threshold = 0.05; // 5% acceptable rejection rate
    println!("   Acceptable at {:.0}% threshold: {}", 
        threshold * 100.0, 
        trace_handler.is_acceptable(threshold));

    // Example 2: Metrics Partial Success
    println!("\n2️⃣  Metrics Export - Partial Success");
    println!("─────────────────────────────────────────────────────────────────");
    
    let mut metrics_handler = PartialSuccessHandler::<ExportMetricsPartialSuccess>::new(500);
    
    let metrics_partial = ExportMetricsPartialSuccess {
        rejected_data_points: 25,
        error_message: "metric 'custom_metric_123' exceeds cardinality limit".to_string(),
    };
    
    metrics_handler.handle_metrics_partial_success(&metrics_partial);
    
    println!("   Request: Exported 500 data points");
    println!("   Response: Partial Success");
    println!("   ─────────────────────────────");
    println!("   Total data points: {}", metrics_handler.total_count());
    println!("   Accepted: {}", metrics_handler.success_count());
    println!("   Rejected: {}", metrics_handler.rejected_count());
    println!("   Success rate: {:.1}%", metrics_handler.success_rate() * 100.0);

    // Example 3: Logs Partial Success
    println!("\n3️⃣  Logs Export - Full Success (for comparison)");
    println!("─────────────────────────────────────────────────────────────────");
    
    let mut logs_handler = PartialSuccessHandler::<ExportLogsPartialSuccess>::new(2000);
    
    // Simulate full success (no rejection)
    // In real scenario, partial_success field would be null/empty
    println!("   Request: Exported 2000 log records");
    println!("   Response: Full Success");
    println!("   ─────────────────────────────");
    println!("   Success rate: 100.0%");
    println!("   Is acceptable: true");

    // ====================================================================================
    // SECTION 2: Threshold-Based Acceptance Strategies
    // ====================================================================================
    println!("\n📊 SECTION 2: Threshold-Based Acceptance Strategies");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("Different strategies for determining if partial success is acceptable:\n");

    let scenarios = vec![
        ("Critical System", 0.01, 1000, 5, "Reject if >1% loss"),
        ("Standard Production", 0.05, 1000, 50, "Accept up to 5% loss"),
        ("High Volume/Batch", 0.10, 10000, 950, "Accept up to 10% loss"),
        ("Development/Debug", 0.50, 100, 60, "Very lenient"),
    ];

    for (name, threshold, total, rejected, description) in scenarios {
        let mut handler = PartialSuccessHandler::<()>::new(total as u64);
        handler.handle_partial_success_raw(rejected as u64, "simulated error");
        
        let acceptable = handler.is_acceptable(threshold);
        let actual_rate = handler.rejected_count() as f64 / total as f64;
        
        println!("{}:", name);
        println!("   Threshold: {:.0}%", threshold * 100.0);
        println!("   Actual rejection: {:.1}%", actual_rate * 100.0);
        println!("   Acceptable: {}", if acceptable { "✅ YES" } else { "❌ NO" });
        println!("   Policy: {}", description);
        println!();
    }

    // ====================================================================================
    // SECTION 3: Response Aggregation
    // ====================================================================================
    println!("📊 SECTION 3: Response Aggregation");
    println!("═════════════════════════════════════════════════════════════════\n");

    let mut aggregator = ResponseAggregator::new();

    // Simulate a batch of export operations
    let operations = vec![
        ("trace-001", SignalType::Trace, 100, 0, None),
        ("trace-002", SignalType::Trace, 100, 5, Some("rate limit")),
        ("metric-001", SignalType::Metric, 50, 0, None),
        ("metric-002", SignalType::Metric, 50, 10, Some("cardinality limit")),
        ("log-001", SignalType::Log, 200, 0, None),
        ("trace-003", SignalType::Trace, 100, 100, Some("authentication failed")),
    ];

    println!("Simulating {} export operations:\n", operations.len());

    for (id, signal_type, total, rejected, error) in operations {
        let metadata = ResponseMetadata::new(id, signal_type, total as u64);
        
        let response = if rejected == 0 {
            ResponseType::FullSuccess {
                accepted_count: total as u64,
                metadata,
            }
        } else if rejected < total {
            let mut handler = PartialSuccessHandler::<()>::new(total as u64);
            handler.handle_partial_success_raw(
                rejected as u64, 
                error.unwrap_or("unknown")
            );
            ResponseType::PartialSuccess {
                handler,
                error_message: error.unwrap_or("partial success").to_string(),
                metadata,
            }
        } else {
            ResponseType::Failure {
                error: error.unwrap_or("complete failure").to_string(),
                retryable: true,
                metadata,
            }
        };

        aggregator.add(response);
        
        let status = if rejected == 0 {
            "✅ Full Success"
        } else if rejected < total {
            "⚠️  Partial Success"
        } else {
            "❌ Failure"
        };
        
        println!("   {} - {}: {}", id, signal_type, status);
    }

    // Generate summary
    let summary = aggregator.summary();
    
    println!("\n📈 Aggregation Summary:");
    println!("─────────────────────────────────────────────────────────────────");
    print_summary(&summary);

    // ====================================================================================
    // SECTION 4: Error Aggregation and Analysis
    // ====================================================================================
    println!("\n📊 SECTION 4: Error Aggregation and Analysis");
    println!("═════════════════════════════════════════════════════════════════\n");

    let errors = aggregator.error_messages();
    
    println!("Unique error messages:");
    if errors.is_empty() {
        println!("   (none - all operations successful)");
    } else {
        for (i, error) in errors.iter().enumerate() {
            println!("   {}. {}", i + 1, error);
        }
    }

    // Count by type
    let (full, partial, failure) = aggregator.count_by_type();
    println!("\nResponse type distribution:");
    println!("   Full successes: {} ({:.1}%)", full, 
        full as f64 / aggregator.response_count() as f64 * 100.0);
    println!("   Partial successes: {} ({:.1}%)", partial,
        partial as f64 / aggregator.response_count() as f64 * 100.0);
    println!("   Failures: {} ({:.1}%)", failure,
        failure as f64 / aggregator.response_count() as f64 * 100.0);

    // ====================================================================================
    // SECTION 5: Metrics Collection
    // ====================================================================================
    println!("\n📊 SECTION 5: Metrics Collection for Partial Success");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create a custom metrics collector
    let mut metrics_collector = PartialSuccessMetrics::new();

    // Simulate multiple export cycles
    for cycle in 1..=5 {
        println!("Export Cycle {}:", cycle);
        
        // Simulate varying success rates
        let total = 1000u64;
        let rejected = match cycle {
            1 => 0,      // Perfect
            2 => 10,     // Good
            3 => 50,     // Degraded
            4 => 100,    // Poor
            5 => 5,      // Recovered
            _ => 0,
        };

        let mut handler = PartialSuccessHandler::<()>::new(total);
        if rejected > 0 {
            handler.handle_partial_success_raw(rejected, "simulated rejection");
        }

        // Record metrics
        metrics_collector.record_export(cycle, total, rejected, handler.success_rate());

        println!("   Total: {}, Rejected: {}, Success Rate: {:.1}%",
            total, rejected, handler.success_rate() * 100.0);
    }

    println!("\n📊 Metrics Summary:");
    metrics_collector.print_summary();

    // ====================================================================================
    // SECTION 6: Per-Signal Handling
    // ====================================================================================
    println!("\n📊 SECTION 6: Per-Signal Partial Success Handling");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create a comprehensive response handler for all signals
    let mut comprehensive_handler = ResponseHandlerBuilder::new()
        .with_trace_handler(PartialSuccessHandler::new(1000))
        .with_metric_handler(PartialSuccessHandler::new(500))
        .with_log_handler(PartialSuccessHandler::new(2000))
        .with_profile_handler(PartialSuccessHandler::new(100))
        .build();

    println!("Configured handlers for all signals:");
    println!("   • Traces: 1000 items capacity");
    println!("   • Metrics: 500 items capacity");
    println!("   • Logs: 2000 items capacity");
    println!("   • Profiles: 100 items capacity\n");

    // Simulate handling responses for each signal
    println!("Handling responses:");
    
    // Traces - partial success
    let trace_response = ExportTracePartialSuccess {
        rejected_spans: 25,
        error_message: "some spans dropped".to_string(),
    };
    if let Some(ref mut handler) = comprehensive_handler.trace_handler {
        handler.handle_trace_partial_success(&trace_response);
        println!("   Traces: {}/{} accepted ({:.1}%)",
            handler.success_count(),
            handler.total_count(),
            handler.success_rate() * 100.0);
    }

    // Metrics - full success
    println!("   Metrics: 500/500 accepted (100.0%)");

    // Logs - partial success
    let log_response = ExportLogsPartialSuccess {
        rejected_log_records: 100,
        error_message: "queue overflow".to_string(),
    };
    if let Some(ref mut handler) = comprehensive_handler.log_handler {
        handler.handle_logs_partial_success(&log_response);
        println!("   Logs: {}/{} accepted ({:.1}%)",
            handler.success_count(),
            handler.total_count(),
            handler.success_rate() * 100.0);
    }

    // ====================================================================================
    // SECTION 7: Best Practices
    // ====================================================================================
    println!("\n📚 SECTION 7: Best Practices for Partial Success");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("✅ DO:");
    println!("   • Always check for partial_success field in responses");
    println!("   • Log warnings when partial success occurs");
    println!("   • Include error_message in your logs");
    println!("   • Track rejection rates over time");
    println!("   • Set up alerts for high rejection rates");
    println!("   • Consider scaling or rate limiting if rejections are frequent\n");

    println!("❌ DON'T:");
    println!("   • Don't retry partial success responses (OTLP spec violation)");
    println!("   • Don't silently ignore partial successes");
    println!("   • Don't treat all rejections as fatal errors");
    println!("   • Don't use the same threshold for all signals\n");

    println!("📊 Recommended Thresholds by Signal:");
    println!("   • Traces: 1-5% (critical for debugging)");
    println!("   • Metrics: 5-10% (aggregated data is more resilient)");
    println!("   • Logs: 5-10% (depending on log volume)");
    println!("   • Profiles: 1-2% (profiling data is valuable)\n");

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║                    Summary                                   ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║                                                              ║");
    println!("║  ✅ Partial success response handling                        ║");
    println!("║  ✅ Threshold-based acceptance strategies                    ║");
    println!("║  ✅ Response aggregation across multiple requests            ║");
    println!("║  ✅ Error message aggregation and analysis                   ║");
    println!("║  ✅ Metrics collection for monitoring                        ║");
    println!("║  ✅ Per-signal handling (traces, metrics, logs)              ║");
    println!("║  ✅ Best practices and recommendations                       ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    println!("\n📚 Reference: https://opentelemetry.io/docs/specs/otlp/");
    println!("   OTLP 1.10 Partial Success Specification");

    Ok(())
}

/// Print aggregation summary
fn print_summary(summary: &AggregationSummary) {
    println!("   Total responses: {}", summary.total_responses);
    println!("   Full successes: {} ({:.1}%)", 
        summary.full_success_count, 
        summary.full_success_rate * 100.0);
    println!("   Partial successes: {} ({:.1}%)",
        summary.partial_success_count,
        summary.partial_success_rate * 100.0);
    println!("   Failures: {} ({:.1}%)",
        summary.failure_count,
        summary.failure_rate * 100.0);
    println!("   ─────────────────────────────");
    println!("   Items accepted: {}", summary.total_items_accepted);
    println!("   Items rejected: {}", summary.total_items_rejected);
    println!("   Overall acceptance rate: {:.1}%", 
        summary.overall_acceptance_rate * 100.0);
    println!("   All successful: {}", summary.all_successful());
}

/// Custom metrics collector for partial success tracking
struct PartialSuccessMetrics {
    exports: Vec<ExportMetrics>,
}

struct ExportMetrics {
    cycle: i32,
    total: u64,
    rejected: u64,
    success_rate: f64,
}

impl PartialSuccessMetrics {
    fn new() -> Self {
        Self {
            exports: Vec::new(),
        }
    }

    fn record_export(&mut self, cycle: i32, total: u64, rejected: u64, success_rate: f64) {
        self.exports.push(ExportMetrics {
            cycle,
            total,
            rejected,
            success_rate,
        });
    }

    fn print_summary(&self) {
        if self.exports.is_empty() {
            println!("   No data recorded");
            return;
        }

        let total_exports = self.exports.len();
        let total_items: u64 = self.exports.iter().map(|e| e.total).sum();
        let total_rejected: u64 = self.exports.iter().map(|e| e.rejected).sum();
        let avg_success_rate = self.exports.iter().map(|e| e.success_rate).sum::<f64>() 
            / total_exports as f64;

        println!("   Total export cycles: {}", total_exports);
        println!("   Total items: {}", total_items);
        println!("   Total rejected: {}", total_rejected);
        println!("   Average success rate: {:.2}%", avg_success_rate * 100.0);
        println!("   Overall rejection rate: {:.2}%", 
            total_rejected as f64 / total_items as f64 * 100.0);
    }
}

// Extension trait for handler
trait LogsPartialSuccessHandler {
    fn handle_logs_partial_success(&mut self, partial: &ExportLogsPartialSuccess);
}

impl LogsPartialSuccessHandler for PartialSuccessHandler<ExportLogsPartialSuccess> {
    fn handle_logs_partial_success(&mut self, partial: &ExportLogsPartialSuccess) {
        self.handle_partial_success_raw(
            partial.rejected_log_records,
            &partial.error_message
        );
    }
}
