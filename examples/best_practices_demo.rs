//! Best Practices Demo
//!
//! This example demonstrates OTLP best practices:
//! - Proper resource configuration
//! - Effective sampling strategies
//! - Batch processing optimization
//! - Connection reuse
//! - Comprehensive error handling
//!
//! Run with: cargo run --example best_practices_demo

use std::time::Duration;

use otlp::{
    config::BatchConfig,
    response::{PartialSuccessHandler, ExportTracePartialSuccess},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("OTLP Best Practices Demo");
    println!("========================\n");

    // Resource Configuration
    println!("1. Resource Configuration");
    println!("   - service.name: payment-service");
    println!("   - service.version: 1.2.3");
    println!("   - service.namespace: ecommerce");
    println!("   - service.instance.id: payment-service-7d8f9b2c4-a1b2c");
    println!();

    // Batch Configuration
    println!("2. Batch Configuration");
    println!("   - Max batch size: 512 items");
    println!("   - Max queue size: 2048 items");
    println!("   - Schedule delay: 5s");
    println!("   - Export timeout: 30s");
    println!();

    // Sampling
    println!("3. Sampling Strategies");
    println!("   - Development: 100% (no sampling)");
    println!("   - Production low-traffic: 100%");
    println!("   - Production high-traffic: 1-10%");
    println!("   - Always sample errors");
    println!();

    // Error Handling
    println!("4. Partial Success Handling");
    let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(1000);
    handler.handle_partial_success_raw(50, "rate limit exceeded");
    println!("   - Total: {}", handler.total_count());
    println!("   - Accepted: {}", handler.success_count());
    println!("   - Rejected: {}", handler.rejected_count());
    println!("   - Success rate: {:.1}%", handler.success_rate() * 100.0);
    println!();

    // Connection Pooling
    println!("5. Connection Management");
    println!("   - Use connection pooling (10 max, 2 idle)");
    println!("   - Prefer gRPC/HTTP/2");
    println!("   - Reuse connections across requests");
    println!("   - Connection timeout: 5s");
    println!();

    println!("Demo complete!");
    Ok(())
}
