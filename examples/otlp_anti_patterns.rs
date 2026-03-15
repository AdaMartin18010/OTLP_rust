//! OTLP Anti-Patterns - What NOT to Do
//!
//! This example demonstrates common anti-patterns in OTLP usage and
//! shows the correct alternatives. Each section shows:
//!   ❌ BAD: The anti-pattern (what not to do)
//!   ✅ GOOD: The correct approach
//!
//! Run with: cargo run --example otlp_anti_patterns

use std::collections::HashMap;
use std::time::{Duration, Instant};

use otlp::{
    data::{AttributeValue, LogBody, LogTraceContext, SeverityLevel, TraceData, SpanKind, SpanStatus, StatusCode},
    logs::{LogRecord, LogProcessor, SimpleLogProcessor, SeverityFilter},
    logs::exporter::{LogExporter, LogExporterBuilder},
    response::{
        ExportTracePartialSuccess, PartialSuccessHandler, ResponseType,
        ResponseMetadata, SignalType,
    },
    config::{OtlpConfig, OtlpConfigBuilder, TransportProtocol},
    semantic_conventions::http::{HttpAttributesBuilder, HttpMethod},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║            OTLP Anti-Patterns: What NOT to Do                ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    println!("This example demonstrates common anti-patterns and their solutions.\n");
    println!("⚠️  WARNING: The 'BAD' examples are for educational purposes only!\n");

    // ====================================================================================
    // ANTI-PATTERN 1: Ignoring Errors
    // ====================================================================================
    println!("❌ ANTI-PATTERN 1: Ignoring Errors");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Ignoring errors with unwrap() or ?");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Silently ignoring failures
    async fn bad_export_logs(processor: &dyn LogProcessor) {{
        for i in 0..100 {{
            let log = LogRecord::info(format!("Log {{}}", i));
            let _ = processor.emit(log).await;  // Error ignored!
        }}
        // No verification that logs were actually sent
    }}
"#);

    println!("✅ GOOD: Proper error handling and logging");
    println!("─────────────────────────────────────────────────────────────────");
    
    async fn good_export_logs(processor: &dyn LogProcessor) -> Result<(), Box<dyn std::error::Error>> {
        let mut success_count = 0;
        let mut error_count = 0;
        
        for i in 0..100 {
            let log = LogRecord::info(format!("Log {}", i));
            match processor.emit(log).await {
                Ok(_) => success_count += 1,
                Err(e) => {
                    error_count += 1;
                    eprintln!("Failed to emit log {}: {}", i, e);
                    
                    // Decide: retry, buffer, or continue?
                    if error_count > 10 {
                        return Err("Too many export failures".into());
                    }
                }
            }
        }
        
        println!("   Export complete: {} successful, {} failed", success_count, error_count);
        Ok(())
    }

    // Demonstrate good pattern
    let exporter = LogExporterBuilder::new().build();
    let processor = SimpleLogProcessor::new(exporter);
    if let Err(e) = good_export_logs(&processor).await {
        println!("   Export failed: {}", e);
    }

    // ====================================================================================
    // ANTI-PATTERN 2: Creating Spans for Every Function Call
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 2: Creating Spans for Every Function Call");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Excessive span creation");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Creates spans for trivial operations
    fn get_user_bad(user_id: u64) -> User {{
        let span = tracer.start("get_user");
        let span2 = tracer.start("validate_id");  // Unnecessary!
        validate_id(user_id);
        span2.end();
        
        let span3 = tracer.start("query_db");     // Maybe, if slow
        let user = db.query(user_id);             // But not for simple queries
        span3.end();
        
        let span4 = tracer.start("format_user");  // Definitely not!
        let formatted = format_user(user);
        span4.end();
        
        span.end();
        formatted
    }}
"#);

    println!("✅ GOOD: Create spans only for meaningful operations");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DO THIS - Spans for significant boundaries
    fn get_user_good(user_id: u64) -> Result<User, Error> {{
        // One span for the entire operation
        let span = tracer.start("get_user");
        span.set_attribute("user.id", user_id);
        
        // Add events for significant sub-steps (not spans)
        span.add_event("validation_complete");
        
        let user = db.query(user_id)?;
        
        span.add_event("db_query_complete", 
            vec![Attribute::new("rows", 1)]);
        
        span.end();
        Ok(user)
    }}
"#);
    
    println!("   Guidelines for span creation:");
    println!("   • Create spans for: HTTP requests, database queries >10ms, external API calls");
    println!("   • Don't create spans for: simple calculations, in-memory operations, getters");
    println!("   • Use span events instead of child spans for quick sub-steps");

    // ====================================================================================
    // ANTI-PATTERN 3: High Cardinality Attributes
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 3: High Cardinality Attributes");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Using unique IDs as span attributes");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Creates explosion of unique time series
    fn process_request_bad(request: &Request) {{
        let span = tracer.start("process_request");
        
        // HIGH CARDINALITY - Creates unique series per request!
        span.set_attribute("request.id", request.id.to_string());  // UUID
        span.set_attribute("user.id", request.user_id.to_string()); // Unique per user
        span.set_attribute("timestamp", request.timestamp.to_string());
        
        // Even worse: using timestamps
        span.set_attribute("processed_at", Instant::now().to_string());
        
        // ...
    }}
"#);

    println!("✅ GOOD: Use low-cardinality attributes, put unique data in events/logs");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DO THIS - Low cardinality attributes
    fn process_request_good(request: &Request) {{
        let span = tracer.start("process_request");
        
        // LOW CARDINALITY - Good for aggregation
        span.set_attribute("http.method", request.method.clone());
        span.set_attribute("http.route", "/api/v1/users/:id".to_string());
        span.set_attribute("user.type", request.user_type.clone()); // 'premium', 'free'
        
        // HIGH CARDINALITY DATA - Use events or logs instead
        span.add_event("request_received", vec![
            KeyValue::new("request.id", request.id.to_string()),
        ]);
        
        // Or log it separately
        log::info!(request_id = %request.id, "Processing request");
        
        // ...
    }}
"#);
    
    println!("   High cardinality attributes to AVOID:");
    println!("   • UUIDs, request IDs, session IDs (use events/logs instead)");
    println!("   • Timestamps (use span timing)");
    println!("   • User IDs (unless user base is small)");
    println!("   • IP addresses (can be high cardinality)");
    println!("\n   Safe attributes:");
    println!("   • HTTP method, status code, route");
    println!("   • Service name, operation type");
    println!("   • Error types (not full error messages)");

    // ====================================================================================
    // ANTI-PATTERN 4: Blocking on Export
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 4: Blocking on Export");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Blocking the application thread");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Blocks application
    fn handle_request_bad(request: Request) -> Response {{
        let span = tracer.start("handle_request");
        
        // BLOCKING - Application waits for export!
        exporter.export(vec![span]).wait();  // ❌ Synchronous
        
        process(request)
    }}
    
    // Or using blocking in async context
    async fn handle_request_also_bad(request: Request) -> Response {{
        // BLOCKING THE ASYNC EXECUTOR!
        std::thread::sleep(Duration::from_secs(5));  // ❌ Never do this in async
        
        // Or blocking call in async
        blocking_exporter.export(data).await  // If not truly async
    }}
"#);

    println!("✅ GOOD: Use async/batch processing");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DO THIS - Non-blocking export
    async fn handle_request_good(request: Request) -> Response {{
        let span = tracer.start("handle_request");
        
        // Span is queued for export, doesn't block
        let result = process(request).await;
        
        // Span ends, export happens asynchronously
        span.end();
        
        result
    }}
    
    // For sync contexts, use background threads
    fn handle_request_sync(request: Request) -> Response {{
        let span = tracer.start("handle_request");
        
        let result = process(request);
        
        // Handled by background batch processor
        span.end();
        
        result
    }}
"#);
    
    println!("   Best practices:");
    println!("   • Use batch processors for production");
    println!("   • Set appropriate timeouts (don't wait forever)");
    println!("   • Consider using simple processor only for debugging");

    // ====================================================================================
    // ANTI-PATTERN 5: Ignoring Partial Success
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 5: Ignoring Partial Success");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Treating all 200 OK responses as full success");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Ignoring partial success
    async fn export_traces_bad(spans: Vec<Span>) -> Result<(), Error> {{
        let response = client.export(spans).await?;
        
        // WRONG! Response might be partial success
        if response.status().is_success() {{
            println!("Export successful!");  // Not necessarily!
            return Ok(());
        }}
        
        // Missing: check for partial_success field!
        // Some spans might have been rejected
    }}
    
    // ALSO BAD: Retrying partial success
    async fn export_traces_very_bad(spans: Vec<Span>) -> Result<(), Error> {{
        let response = client.export(spans).await?;
        
        if let Some(partial) = response.partial_success {{
            if partial.rejected_spans > 0 {{
                // VIOLATION! Must NOT retry partial success
                return export_traces_very_bad(spans).await;  // ❌ WRONG!
            }}
        }}
        
        Ok(())
    }}
"#);

    println!("✅ GOOD: Handle partial success correctly");
    println!("─────────────────────────────────────────────────────────────────");
    
    println!("   Handling partial success:");
    
    let total_spans = 1000u64;
    let rejected = 50u64;
    
    let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(total_spans);
    handler.handle_partial_success_raw(rejected, "rate limit exceeded");
    
    println!("   • Total spans: {}", handler.total_count());
    println!("   • Accepted: {}", handler.success_count());
    println!("   • Rejected: {}", handler.rejected_count());
    println!("   • Success rate: {:.1}%", handler.success_rate() * 100.0);
    
    // Check threshold
    let threshold = 0.05; // 5%
    if handler.is_acceptable(threshold) {
        println!("   • Status: ✅ Acceptable at {:.0}% threshold", threshold * 100.0);
    } else {
        println!("   • Status: ⚠️  Exceeds {:.0}% threshold - investigate!", threshold * 100.0);
    }
    
    println!("\n   Key rules:");
    println!("   • ALWAYS check partial_success field");
    println!("   • Log warnings when partial success occurs");
    println!("   • NEVER retry partial success (OTLP spec violation)");
    println!("   • Track rejection rates and alert on anomalies");

    // ====================================================================================
    // ANTI-PATTERN 6: Global Tracer Without Context
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 6: Global Tracer Without Context");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Using global tracer without context propagation");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Lost context across boundaries
    fn process_order_bad(order: Order) {{
        // This span won't be connected to the parent
        let span = global::tracer("order-service").start("process_order");
        
        // Context lost when crossing async boundary
        tokio::spawn(async move {{
            // This span is orphaned - no parent!
            let span = global::tracer("order-service").start("charge_payment");
            charge_payment(order).await;
            span.end();
        }});
        
        span.end();
    }}
"#);

    println!("✅ GOOD: Proper context propagation");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DO THIS - Pass context explicitly
    fn process_order_good(order: Order, parent_context: Context) {{
        let tracer = global::tracer("order-service");
        let span = tracer.start_with_context("process_order", &parent_context);
        let cx = Context::current_with_span(span);
        
        // Pass context to async task
        let cx_clone = cx.clone();
        tokio::spawn(async move {{
            // Span has proper parent
            let span = tracer.start_with_context("charge_payment", &cx_clone);
            charge_payment(order).await;
            span.end();
        }});
    }}
    
    // Or use context guards
    fn process_order_alternative(order: Order, parent_context: Context) {{
        let _guard = parent_context.attach();
        let span = tracer.start("process_order");
        
        // All spans created here automatically inherit context
        charge_payment(order).await;
    }}
"#);
    
    println!("   Context propagation rules:");
    println!("   • Always pass context across thread/async boundaries");
    println!("   • Use extract/inject for inter-process communication");
    println!("   • Don't rely on thread-local storage in async contexts");

    // ====================================================================================
    // ANTI-PATTERN 7: Excessive Attribute Collection
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 7: Excessive Attribute Collection");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Collecting too many attributes");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Too many attributes
    let span = tracer.start("http_request");
    span.set_attribute("http.method", "GET");
    span.set_attribute("http.url", url.clone());
    span.set_attribute("http.target", target.clone());
    span.set_attribute("http.path", path.clone());
    span.set_attribute("http.query", query.clone());
    span.set_attribute("http.fragment", fragment.clone());
    span.set_attribute("http.request.headers", format!("{{:?}}", headers));  // Too big!
    span.set_attribute("http.request.body", body.clone());  // Way too big!
    span.set_attribute("http.request.cookies", cookies.clone());  // Sensitive!
    span.set_attribute("user.agent.full", ua.clone());
    span.set_attribute("user.agent.name", ua_name.clone());
    span.set_attribute("user.agent.version", ua_version.clone());
    span.set_attribute("user.agent.os", ua_os.clone());  // Too many!
    // ... 50 more attributes
"#);

    println!("✅ GOOD: Selective, meaningful attributes");
    println!("─────────────────────────────────────────────────────────────────");
    
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Get)
        .url("https://api.example.com/v1/users?page=1")
        .status_code(200)
        .request_body_size(0)
        .response_body_size(2048)
        .user_agent("MyApp/1.0")
        .build()?;

    println!("   Selected attributes:");
    for (key, value) in attrs.as_map() {
        println!("   • {} = {:?}", key, value);
    }
    
    println!("\n   Guidelines:");
    println!("   • Limit to 10-20 key attributes per span");
    println!("   • Don't include: request/response bodies, large headers");
    println!("   • Don't include: PII (emails, phone numbers, SSNs)");
    println!("   • Don't include: secrets (passwords, tokens, API keys)");
    println!("   • Use logs for detailed data, spans for context");

    // ====================================================================================
    // ANTI-PATTERN 8: Not Shutting Down Cleanly
    // ====================================================================================
    println!("\n\n❌ ANTI-PATTERN 8: Not Shutting Down Cleanly");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("❌ BAD: Abrupt termination");
    println!("─────────────────────────────────────────────────────────────────");
    println!(r#"
    // DON'T DO THIS - Lost data on shutdown
    async fn main() {{
        let processor = setup_processor();
        
        // Run application
        run_app().await;
        
        // Abrupt exit - pending exports lost!
        std::process::exit(0);  // ❌ Data loss!
    }}
    
    // Or missing shutdown
    async fn shutdown_bad() {{
        // Just drop the processor
        drop(processor);  // ❌ Pending exports may be lost
    }}
"#);

    println!("✅ GOOD: Graceful shutdown with flush");
    println!("─────────────────────────────────────────────────────────────────");
    
    async fn shutdown_good(processor: &dyn LogProcessor) -> Result<(), Box<dyn std::error::Error>> {
        println!("   Step 1: Stop accepting new data...");
        
        println!("   Step 2: Force flush pending exports...");
        match processor.force_flush().await {
            Ok(result) => println!("      ✅ Flushed {} items", result.success_count),
            Err(e) => println!("      ⚠️  Flush error: {}", e),
        }
        
        println!("   Step 3: Shutdown processor...");
        match processor.shutdown().await {
            Ok(_) => println!("      ✅ Shutdown complete"),
            Err(e) => println!("      ⚠️  Shutdown error: {}", e),
        }
        
        Ok(())
    }
    
    shutdown_good(&processor).await?;

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║           Anti-Patterns Summary                              ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║                                                              ║");
    println!("║  ❌ BAD                        ✅ GOOD                       ║");
    println!("║  ──────────────────────────────────────────────────────────  ║");
    println!("║  Ignoring errors               Handle and log all errors     ║");
    println!("║  Spans for every function      Spans for meaningful ops      ║");
    println!("║  High cardinality attributes   Low-cardinality attributes    ║");
    println!("║  Blocking on export            Async/batch processing        ║");
    println!("║  Ignoring partial success      Check partial_success field   ║");
    println!("║  Global tracer without ctx     Proper context propagation    ║");
    println!("║  Too many attributes           10-20 key attributes          ║");
    println!("║  Abrupt shutdown               Graceful shutdown with flush  ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    println!("\n📚 Remember: These anti-patterns can lead to:");
    println!("   • Data loss and incomplete telemetry");
    println!("   • Performance degradation");
    println!("   • High costs (storage, network)");
    println!("   • Poor debugging experience");

    Ok(())
}

/// Print a log with formatting
fn print_log(log: &LogRecord) {
    println!("      [{:?}] {}", log.severity, 
        log.message().unwrap_or("<structured>"));
}
