//! Partial Success Response Handling Demo
//!
//! This example demonstrates how to handle OTLP 1.10 Partial Success responses.

use otlp::response::{
    ExportTracePartialSuccess, ExportMetricsPartialSuccess,
    PartialSuccessHandler, ResponseHandler, ResponseHandlerBuilder,
    ResponseMetricsCollector, SignalType,
    ResponseMetadata, ResponseAggregator, ResponseType,
};
use otlp::response::handlers::ResponseClassifier;

fn main() {
    println!("=== OTLP 1.10 Partial Success Response Handling Demo ===\n");

    // Example 1: Handling Trace Partial Success
    println!("1. Trace Partial Success Handling");
    let trace_partial = ExportTracePartialSuccess::new(5, "rate limit exceeded");
    let mut trace_handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
    trace_handler.handle_trace_partial_success(&trace_partial);
    
    println!("   Total spans sent: {}", trace_handler.total_count());
    println!("   Spans accepted: {}", trace_handler.success_count());
    println!("   Spans rejected: {}", trace_handler.rejected_count());
    println!("   Success rate: {:.1}%", trace_handler.success_rate() * 100.0);
    println!("   Is acceptable (< 10% rejection): {}", trace_handler.is_acceptable(0.1));
    println!();

    // Example 2: Handling Metrics Partial Success with threshold
    println!("2. Metrics Partial Success with Threshold");
    let _metrics_partial = ExportMetricsPartialSuccess::new(15, "quota exceeded");
    let metrics_handler = PartialSuccessHandler::<ExportMetricsPartialSuccess>::new(100);
    
    // Check acceptance at different thresholds
    println!("   Rejection rate: 15%");
    println!("   Acceptable at 20% threshold: {}", 
        metrics_handler.rejected_count() as f64 / 100.0 <= 0.20);
    println!("   Acceptable at 10% threshold: {}", 
        metrics_handler.rejected_count() as f64 / 100.0 <= 0.10);
    println!();

    // Example 3: Response Classification
    println!("3. Response Classification");
    let classifier = ResponseClassifier::new();
    
    // Full success
    let full_success = ExportTracePartialSuccess::new(0, "");
    let result = classifier.classify_trace_partial_success(&full_success, 100);
    println!("   Full Success: {:?} - Retry: {:?}", 
        result.classification, result.decision);
    
    // Partial success
    let partial = ExportTracePartialSuccess::new(10, "some spans rejected");
    let result = classifier.classify_trace_partial_success(&partial, 100);
    println!("   Partial Success: {:?} - Retry: {:?}", 
        result.classification, result.decision);
    println!();

    // Example 4: Using ResponseHandler with metrics
    println!("4. Response Handler with Metrics Collection");
    let metrics = std::sync::Arc::new(ResponseMetricsCollector::new());
    let handler = ResponseHandler::with_metrics(metrics.clone());
    
    // Simulate handling multiple responses
    for i in 0..5 {
        let partial = match i {
            0 => ExportTracePartialSuccess::new(0, "success"),  // Full success
            1 => ExportTracePartialSuccess::new(5, "rate limit"), // Partial
            2 => ExportTracePartialSuccess::new(0, "success"),  // Full success
            3 => ExportTracePartialSuccess::new(10, "quota"),   // Partial
            _ => ExportTracePartialSuccess::new(0, "success"),  // Full success
        };
        
        let _result = handler.handle_trace_partial_success(&partial, 100);
    }
    
    let summary = metrics.summary();
    println!("   Total responses: {}", summary.total_responses);
    println!("   Full success rate: {:.1}%", summary.full_success_rate * 100.0);
    println!("   Partial success rate: {:.1}%", summary.partial_success_rate * 100.0);
    println!("   Overall acceptance rate: {:.1}%", summary.overall_acceptance_rate * 100.0);
    println!();

    // Example 5: Response Aggregation
    println!("5. Response Aggregation");
    let mut aggregator = ResponseAggregator::new();
    
    // Add various responses
    aggregator.add(ResponseType::FullSuccess {
        accepted_count: 100,
        metadata: ResponseMetadata::new("req-1", SignalType::Trace, 100),
    });
    
    let mut handler = PartialSuccessHandler::<()>::new(100);
    handler.handle_partial_success_raw(20, "rate limit");
    aggregator.add(ResponseType::PartialSuccess {
        handler,
        error_message: "rate limit".to_string(),
        metadata: ResponseMetadata::new("req-2", SignalType::Metric, 100),
    });
    
    aggregator.add(ResponseType::Failure {
        error: "timeout".to_string(),
        retryable: true,
        metadata: ResponseMetadata::new("req-3", SignalType::Log, 100),
    });
    
    let summary = aggregator.summary();
    println!("   Total responses: {}", summary.total_responses);
    println!("   Full successes: {}", summary.full_success_count);
    println!("   Partial successes: {}", summary.partial_success_count);
    println!("   Failures: {}", summary.failure_count);
    println!("   Overall acceptance rate: {:.1}%", summary.overall_acceptance_rate * 100.0);
    println!();

    // Example 6: Builder Pattern
    println!("6. Response Handler Builder");
    let handler = ResponseHandlerBuilder::new()
        .with_threshold(0.15)  // 15% threshold
        .with_metrics()
        .build();
    
    let partial = ExportTracePartialSuccess::new(12, "high rejection");
    let result = handler.handle_trace_partial_success(&partial, 100);
    
    println!("   12% rejection with 15% threshold");
    println!("   Classification: {:?}", result.classification);
    println!("   Should retry: {}", result.should_retry());
    println!();

    println!("=== Demo Complete ===");
}
