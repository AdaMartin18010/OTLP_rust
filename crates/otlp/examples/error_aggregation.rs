//! Error Aggregation Example
//!
//! Demonstrates how to aggregate and analyze errors from multiple
//! partial success responses.

use otlp::response::handlers::RetryDecision;
use otlp::response::{
    ClassificationResult, PartialSuccessHandler, ResponseAggregator, ResponseClassification,
    ResponseMetadata, ResponseMetricsCollector, ResponseType, SignalType,
};
use std::sync::Arc;

fn main() {
    println!("=== Error Aggregation Demo ===\n");

    // Create a metrics collector
    let metrics = Arc::new(ResponseMetricsCollector::new());

    println!("Simulating export responses with various errors...\n");

    // Simulate various export scenarios
    let scenarios = vec![
        // (signal, total, rejected, error_message)
        (SignalType::Trace, 100_u64, 0_u64, "".to_string()),
        (SignalType::Trace, 100, 5, "rate limit exceeded".to_string()),
        (SignalType::Metric, 100, 0, "".to_string()),
        (SignalType::Metric, 100, 10, "quota exceeded".to_string()),
        (SignalType::Log, 100, 0, "".to_string()),
        (SignalType::Log, 100, 20, "buffer full".to_string()),
        (SignalType::Trace, 100, 3, "rate limit exceeded".to_string()),
        (SignalType::Metric, 100, 8, "server busy".to_string()),
        (SignalType::Log, 100, 15, "buffer full".to_string()),
    ];

    for (i, (signal, total, rejected, error)) in scenarios.iter().enumerate() {
        let result = if *rejected == 0 {
            ClassificationResult {
                classification: ResponseClassification::FullSuccess,
                decision: RetryDecision::DoNotRetry,
                success_count: *total,
                rejected_count: 0,
                rejection_rate: 0.0,
                error_message: None,
            }
        } else {
            ClassificationResult {
                classification: ResponseClassification::PartialSuccess,
                decision: RetryDecision::DoNotRetry,
                success_count: total - rejected,
                rejected_count: *rejected,
                rejection_rate: *rejected as f64 / *total as f64,
                error_message: if error.is_empty() {
                    None
                } else {
                    Some(error.clone())
                },
            }
        };

        metrics.record_classification(&result);
        println!(
            "Response {}: {:?} - {}/{} rejected - {:?}",
            i + 1,
            signal,
            rejected,
            total,
            if error.is_empty() { "success" } else { error }
        );
    }

    println!("\n--- Error Analysis ---\n");

    // Get error counts
    let error_counts = metrics.error_counts();
    println!("Error frequency:");
    for (error, count) in &error_counts {
        println!("  {}: {} occurrence(s)", error, count);
    }

    // Most common error
    if let Some((error, count)) = metrics.most_common_error() {
        println!("\nMost common error: '{}' ({} occurrence(s))", error, count);
    }

    println!("\n--- Summary Statistics ---\n");

    let summary = metrics.summary();
    println!("Total responses: {}", summary.total_responses);
    println!("Full successes: {:.1}%", summary.full_success_rate * 100.0);
    println!(
        "Partial successes: {:.1}%",
        summary.partial_success_rate * 100.0
    );
    println!("Failures: {:.1}%", summary.failure_rate * 100.0);
    println!("\nItem-level statistics:");
    println!("  Total sent: {}", summary.total_items_sent);
    println!("  Total accepted: {}", summary.total_items_accepted);
    println!("  Total rejected: {}", summary.total_items_rejected);
    println!(
        "  Overall acceptance rate: {:.1}%",
        summary.overall_acceptance_rate * 100.0
    );

    println!("\n--- Response Aggregator Demo ---\n");

    // Demonstrate the ResponseAggregator for grouping responses
    let mut aggregator = ResponseAggregator::new();

    // Add responses from a batch export operation
    let batch_responses = vec![
        ResponseType::FullSuccess {
            accepted_count: 100,
            metadata: ResponseMetadata::new("trace-batch-1", SignalType::Trace, 100),
        },
        ResponseType::PartialSuccess {
            handler: {
                let mut h = PartialSuccessHandler::<()>::new(100);
                h.handle_partial_success_raw(8, "rate limit");
                h
            },
            error_message: "rate limit".to_string(),
            metadata: ResponseMetadata::new("metric-batch-1", SignalType::Metric, 100),
        },
        ResponseType::PartialSuccess {
            handler: {
                let mut h = PartialSuccessHandler::<()>::new(100);
                h.handle_partial_success_raw(15, "buffer full");
                h
            },
            error_message: "buffer full".to_string(),
            metadata: ResponseMetadata::new("log-batch-1", SignalType::Log, 100),
        },
        ResponseType::Failure {
            error: "connection timeout".to_string(),
            retryable: true,
            metadata: ResponseMetadata::new("trace-batch-2", SignalType::Trace, 100),
        },
        ResponseType::FullSuccess {
            accepted_count: 100,
            metadata: ResponseMetadata::new("metric-batch-2", SignalType::Metric, 100),
        },
    ];

    for response in batch_responses {
        aggregator.add(response);
    }

    let agg_summary = aggregator.summary();
    println!("Batch export results:");
    println!("  Total responses: {}", agg_summary.total_responses);
    println!("  Full successes: {}", agg_summary.full_success_count);
    println!("  Partial successes: {}", agg_summary.partial_success_count);
    println!("  Failures: {}", agg_summary.failure_count);
    println!(
        "  All successful (no failures): {}",
        agg_summary.all_successful()
    );
    println!(
        "  Had partial successes: {}",
        agg_summary.had_partial_successes()
    );
    println!(
        "  Overall acceptance rate: {:.1}%",
        agg_summary.overall_acceptance_rate * 100.0
    );

    println!("\n=== Demo Complete ===");
}
