//! Threshold-Based Acceptance Example
//!
//! Demonstrates how to use acceptance thresholds to determine if a
//! partial success response should be treated as success or failure.

use otlp::response::{
    ExportTracePartialSuccess, ExportMetricsPartialSuccess,
    PartialSuccessHandler, ResponseClassifier, ClassificationResult,
    ResponseClassification, RetryDecision,
};

fn main() {
    println!("=== Threshold-Based Acceptance Demo ===\n");

    // Define different thresholds for different use cases
    let strict_threshold = 0.05;    // 5% - for critical data
    let normal_threshold = 0.10;    // 10% - for normal operations
    let relaxed_threshold = 0.25;   // 25% - for best-effort data

    println!("Thresholds:");
    println!("  Strict (critical data):  {}%", strict_threshold * 100.0);
    println!("  Normal (default):        {}%", normal_threshold * 100.0);
    println!("  Relaxed (best-effort):   {}%\n", relaxed_threshold * 100.0);

    // Test scenarios with different rejection rates
    let scenarios = vec![
        ("Low rejection", 3_u64, 100_u64),
        ("Medium rejection", 10, 100),
        ("High rejection", 20, 100),
        ("Critical rejection", 50, 100),
    ];

    println!("{:<20} {:>10} {:>12} {:>10} {:>10} {:>10}",
        "Scenario", "Rejected", "Total", "Strict", "Normal", "Relaxed");
    println!("{}", "-".repeat(72));

    for (name, rejected, total) in scenarios {
        let handler = PartialSuccessHandler::<()>::new(total);
        let rejection_rate = rejected as f64 / total as f64;
        
        let strict_ok = rejection_rate <= strict_threshold;
        let normal_ok = rejection_rate <= normal_threshold;
        let relaxed_ok = rejection_rate <= relaxed_threshold;
        
        println!("{:<20} {:>10} {:>12} {:>10} {:>10} {:>10}",
            name,
            rejected,
            total,
            if strict_ok { "✓" } else { "✗" },
            if normal_ok { "✓" } else { "✗" },
            if relaxed_ok { "✓" } else { "✗" },
        );
    }

    println!("\n--- Signal-Specific Thresholds ---\n");

    // Different signals may have different tolerance levels
    let trace_threshold = 0.05;   // Traces: low tolerance (5%)
    let metric_threshold = 0.10;  // Metrics: medium tolerance (10%)
    let log_threshold = 0.20;     // Logs: higher tolerance (20%)

    println!("Signal-specific thresholds:");
    println!("  Traces:  {}%", trace_threshold * 100.0);
    println!("  Metrics: {}%", metric_threshold * 100.0);
    println!("  Logs:    {}%\n", log_threshold * 100.0);

    // Simulate partial successes for each signal
    let mut trace_handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
    trace_handler.handle_partial_success_raw(8, "trace rate limit");
    
    let mut metric_handler = PartialSuccessHandler::<ExportMetricsPartialSuccess>::new(100);
    metric_handler.handle_partial_success_raw(8, "metric quota exceeded");

    println!("Rejection rate: 8%\n");
    println!("Traces acceptable (5% threshold):  {}", 
        trace_handler.is_acceptable(trace_threshold));
    println!("Metrics acceptable (10% threshold): {}", 
        metric_handler.is_acceptable(metric_threshold));

    println!("\n--- Using ResponseClassifier with Custom Thresholds ---\n");

    // Create classifiers with different thresholds
    let strict_classifier = ResponseClassifier::with_threshold(0.05);
    let normal_classifier = ResponseClassifier::with_threshold(0.10);
    let relaxed_classifier = ResponseClassifier::with_threshold(0.30);

    let partial = ExportTracePartialSuccess::new(15, "server overloaded");

    println!("15% rejection rate with different classifiers:\n");

    let strict_result = strict_classifier.classify_trace_partial_success(&partial, 100);
    println!("Strict classifier (5% threshold):");
    println!("  Classification: {:?}", strict_result.classification);
    println!("  Decision: {:?}\n", strict_result.decision);

    let normal_result = normal_classifier.classify_trace_partial_success(&partial, 100);
    println!("Normal classifier (10% threshold):");
    println!("  Classification: {:?}", normal_result.classification);
    println!("  Decision: {:?}\n", normal_result.decision);

    let relaxed_result = relaxed_classifier.classify_trace_partial_success(&partial, 100);
    println!("Relaxed classifier (30% threshold):");
    println!("  Classification: {:?}", relaxed_result.classification);
    println!("  Decision: {:?}\n", relaxed_result.decision);

    println!("=== Demo Complete ===");
}
