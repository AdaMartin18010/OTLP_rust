//! OTLP Complete Walkthrough Example
//!
//! This example demonstrates a complete walkthrough of all OTLP signal types:
//! - Traces (distributed tracing)
//! - Metrics (counters, gauges, histograms, exponential histograms)
//! - Logs (structured logging with severity levels)
//! - Profiles (continuous profiling)
//!
//! Run with: cargo run --example otlp_complete_walkthrough

use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use otlp::{
    // Core data types
    data::{
        AttributeValue, LogBody, LogData, LogSeverity, LogTraceContext,
        MetricData, MetricType, ProfileData, Sample, SampleType,
        SpanKind, SpanStatus, StatusCode, TelemetryData, TraceData,
        ExponentialHistogramData, ExponentialHistogramBuckets,
    },
    // Logs
    logs::{LogRecord, LogProcessor, SimpleLogProcessor, SeverityFilter, SeverityLevel},
    logs::exporter::{LogExporter, LogExporterBuilder},
    // Configuration
    config::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression, BatchConfig},
    // Response handling
    response::{
        ResponseHandler, ResponseHandlerBuilder, ResponseType, SignalType,
        ExportTracePartialSuccess, PartialSuccessHandler, ResponseAggregator,
    },
    // Semantic conventions
    semantic_conventions::{
        http::{HttpAttributesBuilder, HttpMethod, HttpScheme},
        cloud::{CloudAttributesBuilder, CloudProvider, CloudPlatform},
    },
    // Core client
    core::EnhancedOtlpClient,
    // Error handling
    error::{OtlpError, ErrorCategory, ErrorSeverity},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║          OTLP Complete Walkthrough Example                   ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ====================================================================================
    // SECTION 1: Configuration Setup
    // ====================================================================================
    println!("📋 SECTION 1: Configuration Setup");
    println!("─────────────────────────────────────────────────────────────────\n");

    // Create a comprehensive OTLP configuration
    let config = OtlpConfigBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(30))
        .with_protocol(TransportProtocol::Grpc)
        .with_compression(Compression::Gzip)
        .with_batch_config(
            BatchConfig::new()
                .with_max_batch_size(512)
                .with_max_queue_size(2048)
                .with_schedule_delay(Duration::from_secs(5))
                .with_export_timeout(Duration::from_secs(30))
        )
        .build()?;

    println!("✅ Configuration created:");
    println!("   • Endpoint: http://localhost:4317");
    println!("   • Protocol: gRPC");
    println!("   • Compression: Gzip");
    println!("   • Batch size: 512");
    println!("   • Queue size: 2048\n");

    // ====================================================================================
    // SECTION 2: Trace Data
    // ====================================================================================
    println!("📋 SECTION 2: Creating Trace Data");
    println!("─────────────────────────────────────────────────────────────────\n");

    // Create a trace representing a distributed operation
    let trace = create_sample_trace();
    println!("✅ Trace created with ID: {}", trace.trace_id);
    println!("   • Span name: {}", trace.name);
    println!("   • Span kind: {:?}", trace.span_kind);
    println!("   • Duration: {} μs", trace.end_time - trace.start_time);
    println!("   • Attributes: {} items\n", trace.attributes.len());

    // Create a child span
    let child_span = create_child_span(&trace);
    println!("✅ Child span created:");
    println!("   • Parent span ID: {:?}", child_span.parent_span_id);
    println!("   • Span ID: {}", child_span.span_id);
    println!("   • Status: {:?}\n", child_span.status.code);

    // ====================================================================================
    // SECTION 3: Metric Data
    // ====================================================================================
    println!("📋 SECTION 3: Creating Metric Data");
    println!("─────────────────────────────────────────────────────────────────\n");

    // Create different metric types
    let counter = create_counter_metric();
    println!("✅ Counter metric:");
    println!("   • Name: {}", counter.name);
    println!("   • Type: {:?}", counter.metric_type);
    println!("   • Value: {:?}\n", counter.value);

    let gauge = create_gauge_metric();
    println!("✅ Gauge metric:");
    println!("   • Name: {}", gauge.name);
    println!("   • Type: {:?}", gauge.metric_type);
    println!("   • Value: {:?}\n", gauge.value);

    let histogram = create_histogram_metric();
    println!("✅ Histogram metric:");
    println!("   • Name: {}", histogram.name);
    println!("   • Type: {:?}", histogram.metric_type);
    println!("   • Data points: {}\n", histogram.data_points.len());

    // Create exponential histogram (OTLP 1.10+)
    let exp_histogram = create_exponential_histogram();
    println!("✅ Exponential Histogram (OTLP 1.10+):");
    println!("   • Scale: {}", exp_histogram.scale);
    println!("   • Count: {}", exp_histogram.count);
    println!("   • Sum: {:?}", exp_histogram.sum);
    println!("   • Zero count: {}\n", exp_histogram.zero_count);

    // ====================================================================================
    // SECTION 4: Log Data
    // ====================================================================================
    println!("📋 SECTION 4: Creating Log Data");
    println!("─────────────────────────────────────────────────────────────────\n");

    // Create logs at different severity levels
    let logs = create_sample_logs();
    println!("✅ Created {} log records:", logs.len());
    for (i, log) in logs.iter().enumerate() {
        println!("   {}. {:?}: {}", 
            i + 1, 
            log.severity,
            log.body.as_string().unwrap_or("<structured>")
        );
    }
    println!();

    // Create a log with trace correlation
    let correlated_log = create_correlated_log(&trace);
    println!("✅ Correlated log record:");
    if let Some(ref ctx) = correlated_log.trace_context {
        println!("   • Trace ID: {}", ctx.trace_id);
        println!("   • Span ID: {}", ctx.span_id);
    }
    println!("   • Severity: {:?}", correlated_log.severity);
    println!("   • Message: {:?}\n", correlated_log.body);

    // ====================================================================================
    // SECTION 5: Profile Data (OTLP Development Signal)
    // ====================================================================================
    println!("📋 SECTION 5: Creating Profile Data (Development Signal)");
    println!("─────────────────────────────────────────────────────────────────\n");

    let profile = create_sample_profile();
    println!("✅ Profile created:");
    println!("   • Profile ID: {}", profile.profile_id);
    println!("   • Sample types: {} types", profile.sample_types.len());
    println!("   • Samples: {}", profile.samples.len());
    println!("   • Duration: {:?}\n", profile.duration_nanos.map(|d| format!("{}ns", d)).unwrap_or_default());

    // ====================================================================================
    // SECTION 6: Response Handling (OTLP 1.10 Partial Success)
    // ====================================================================================
    println!("📋 SECTION 6: Response Handling (OTLP 1.10 Partial Success)");
    println!("─────────────────────────────────────────────────────────────────\n");

    // Create a response handler
    let response_handler = ResponseHandlerBuilder::new()
        .with_trace_handler(PartialSuccessHandler::new(1000))
        .with_metric_handler(PartialSuccessHandler::new(500))
        .with_log_handler(PartialSuccessHandler::new(2000))
        .build();

    println!("✅ Response handler configured for all signals\n");

    // Simulate handling a partial success response
    let mut trace_handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
    trace_handler.handle_trace_partial_success(&ExportTracePartialSuccess {
        rejected_spans: 5,
        error_message: "rate limit exceeded".to_string(),
    });

    println!("✅ Handled partial success response:");
    println!("   • Total spans: {}", trace_handler.total_count());
    println!("   • Accepted: {}", trace_handler.success_count());
    println!("   • Rejected: {}", trace_handler.rejected_count());
    println!("   • Success rate: {:.1}%", trace_handler.success_rate() * 100.0);
    println!("   • Is acceptable (5% threshold): {}\n", 
        trace_handler.is_acceptable(0.05));

    // Demonstrate response aggregation
    demonstrate_response_aggregation().await?;

    // ====================================================================================
    // SECTION 7: Error Handling
    // ====================================================================================
    println!("📋 SECTION 7: Error Handling");
    println!("─────────────────────────────────────────────────────────────────\n");

    demonstrate_error_handling()?;

    // ====================================================================================
    // SECTION 8: Graceful Shutdown
    // ====================================================================================
    println!("📋 SECTION 8: Graceful Shutdown");
    println!("─────────────────────────────────────────────────────────────────\n");

    demonstrate_shutdown().await?;

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                    Walkthrough Complete!                     ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║ Covered:                                                     ║");
    println!("║   ✅ Configuration (endpoints, timeouts, batching)           ║");
    println!("║   ✅ Traces (spans, parent-child relationships)              ║");
    println!("║   ✅ Metrics (counter, gauge, histogram, exponential)        ║");
    println!("║   ✅ Logs (severity levels, trace correlation)               ║");
    println!("║   ✅ Profiles (pprof-compatible profiling data)              ║");
    println!("║   ✅ Response Handling (partial success OTLP 1.10)           ║");
    println!("║   ✅ Error Handling (categorized errors with context)        ║");
    println!("║   ✅ Graceful Shutdown (flush and cleanup)                   ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    Ok(())
}

/// Create a sample trace representing an HTTP request
fn create_sample_trace() -> TraceData {
    let start_time = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;

    let mut attributes = HashMap::new();
    attributes.insert(
        "http.method".to_string(),
        AttributeValue::String("GET".to_string()),
    );
    attributes.insert(
        "http.url".to_string(),
        AttributeValue::String("https://api.example.com/users/123".to_string()),
    );
    attributes.insert(
        "http.status_code".to_string(),
        AttributeValue::Int(200),
    );
    attributes.insert(
        "service.name".to_string(),
        AttributeValue::String("user-service".to_string()),
    );

    TraceData {
        trace_id: "abc123def45678901234567890123456".to_string(),
        span_id: "span001abc".to_string(),
        parent_span_id: None,
        name: "HTTP GET /users/{id}".to_string(),
        span_kind: SpanKind::Server,
        start_time,
        end_time: start_time + 150_000_000, // 150ms in nanoseconds
        status: SpanStatus {
            code: StatusCode::Ok,
            message: None,
        },
        attributes,
        events: vec![],
        links: vec![],
    }
}

/// Create a child span representing a database query
fn create_child_span(parent: &TraceData) -> TraceData {
    let start_time = parent.start_time + 10_000_000; // 10ms after parent
    let mut attributes = HashMap::new();
    attributes.insert(
        "db.system".to_string(),
        AttributeValue::String("postgresql".to_string()),
    );
    attributes.insert(
        "db.statement".to_string(),
        AttributeValue::String("SELECT * FROM users WHERE id = $1".to_string()),
    );
    attributes.insert(
        "db.operation".to_string(),
        AttributeValue::String("SELECT".to_string()),
    );

    TraceData {
        trace_id: parent.trace_id.clone(),
        span_id: "span002def".to_string(),
        parent_span_id: Some(parent.span_id.clone()),
        name: "db.query".to_string(),
        span_kind: SpanKind::Client,
        start_time,
        end_time: start_time + 50_000_000, // 50ms in nanoseconds
        status: SpanStatus {
            code: StatusCode::Ok,
            message: None,
        },
        attributes,
        events: vec![],
        links: vec![],
    }
}

/// Create a counter metric
fn create_counter_metric() -> MetricData {
    let mut data_points = Vec::new();
    data_points.push(otlp::data::DataPoint {
        timestamp: SystemTime::now(),
        value: otlp::data::DataPointValue::Int(42),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert(
                "http.method".to_string(),
                AttributeValue::String("GET".to_string()),
            );
            attrs.insert(
                "http.route".to_string(),
                AttributeValue::String("/users/{id}".to_string()),
            );
            attrs
        },
    });

    MetricData {
        name: "http_requests_total".to_string(),
        description: "Total number of HTTP requests".to_string(),
        unit: "1".to_string(),
        metric_type: MetricType::Counter,
        data_points,
        aggregation_temporality: otlp::data::AggregationTemporality::Cumulative,
        is_monotonic: true,
    }
}

/// Create a gauge metric
fn create_gauge_metric() -> MetricData {
    let mut data_points = Vec::new();
    data_points.push(otlp::data::DataPoint {
        timestamp: SystemTime::now(),
        value: otlp::data::DataPointValue::Double(67.5),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert(
                "cpu".to_string(),
                AttributeValue::String("cpu0".to_string()),
            );
            attrs
        },
    });

    MetricData {
        name: "cpu_usage_percent".to_string(),
        description: "Current CPU usage percentage".to_string(),
        unit: "%".to_string(),
        metric_type: MetricType::Gauge,
        data_points,
        aggregation_temporality: otlp::data::AggregationTemporality::Unspecified,
        is_monotonic: false,
    }
}

/// Create a histogram metric
fn create_histogram_metric() -> MetricData {
    use otlp::data::{HistogramBucket, HistogramDataPoint};

    let mut data_points = Vec::new();
    data_points.push(otlp::data::DataPoint {
        timestamp: SystemTime::now(),
        value: otlp::data::DataPointValue::Histogram(HistogramDataPoint {
            count: 1000,
            sum: 45600.0,
            min: 1.0,
            max: 500.0,
            buckets: vec![
                HistogramBucket { boundary: 10.0, count: 100 },
                HistogramBucket { boundary: 50.0, count: 500 },
                HistogramBucket { boundary: 100.0, count: 800 },
                HistogramBucket { boundary: 500.0, count: 1000 },
            ],
            explicit_bounds: vec![10.0, 50.0, 100.0, 500.0],
        }),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert(
                "http.route".to_string(),
                AttributeValue::String("/api/v1/users".to_string()),
            );
            attrs
        },
    });

    MetricData {
        name: "http_request_duration_ms".to_string(),
        description: "HTTP request duration in milliseconds".to_string(),
        unit: "ms".to_string(),
        metric_type: MetricType::Histogram,
        data_points,
        aggregation_temporality: otlp::data::AggregationTemporality::Cumulative,
        is_monotonic: false,
    }
}

/// Create an exponential histogram (OTLP 1.10+)
fn create_exponential_histogram() -> ExponentialHistogramData {
    ExponentialHistogramData {
        count: 10000,
        sum: 12345.67,
        min: Some(0.001),
        max: Some(1000.0),
        scale: 3,
        zero_count: 100,
        positive_buckets: ExponentialHistogramBuckets {
            offset: 0,
            bucket_counts: vec![50, 100, 200, 400, 800, 1600, 3200, 1650],
        },
        negative_buckets: ExponentialHistogramBuckets {
            offset: 0,
            bucket_counts: vec![],
        },
    }
}

/// Create sample logs at different severity levels
fn create_sample_logs() -> Vec<LogData> {
    let base_time = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;

    vec![
        LogData {
            timestamp: base_time,
            observed_timestamp: base_time,
            severity: LogSeverity::Trace,
            severity_text: Some("TRACE".to_string()),
            body: LogBody::String("Entering function process_request".to_string()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        },
        LogData {
            timestamp: base_time + 1_000_000,
            observed_timestamp: base_time + 1_000_000,
            severity: LogSeverity::Debug,
            severity_text: Some("DEBUG".to_string()),
            body: LogBody::String("Database connection pool size: 10".to_string()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        },
        LogData {
            timestamp: base_time + 2_000_000,
            observed_timestamp: base_time + 2_000_000,
            severity: LogSeverity::Info,
            severity_text: Some("INFO".to_string()),
            body: LogBody::String("User login successful: user_id=12345".to_string()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        },
        LogData {
            timestamp: base_time + 3_000_000,
            observed_timestamp: base_time + 3_000_000,
            severity: LogSeverity::Warn,
            severity_text: Some("WARN".to_string()),
            body: LogBody::String("High memory usage detected: 85%".to_string()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        },
        LogData {
            timestamp: base_time + 4_000_000,
            observed_timestamp: base_time + 4_000_000,
            severity: LogSeverity::Error,
            severity_text: Some("ERROR".to_string()),
            body: LogBody::String("Failed to connect to database: connection refused".to_string()),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            flags: 0,
        },
    ]
}

/// Create a log record correlated with a trace
fn create_correlated_log(trace: &TraceData) -> LogData {
    let timestamp = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;

    LogData {
        timestamp,
        observed_timestamp: timestamp,
        severity: LogSeverity::Info,
        severity_text: Some("INFO".to_string()),
        body: LogBody::String(format!("Request completed: {}", trace.name)),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert(
                "http.status_code".to_string(),
                AttributeValue::Int(200),
            );
            attrs.insert(
                "http.response_size".to_string(),
                AttributeValue::Int(1024),
            );
            attrs
        },
        resource_attributes: HashMap::new(),
        trace_context: Some(LogTraceContext {
            trace_id: trace.trace_id.clone(),
            span_id: trace.span_id.clone(),
            trace_flags: 1,
        }),
        dropped_attributes_count: 0,
        flags: 0,
    }
}

/// Create a sample profile (continuous profiling data)
fn create_sample_profile() -> ProfileData {
    ProfileData {
        profile_id: "profile-abc-123".to_string(),
        sample_types: vec![
            SampleType {
                sample_type: "cpu".to_string(),
                unit: "nanoseconds".to_string(),
            },
            SampleType {
                sample_type: "allocations".to_string(),
                unit: "bytes".to_string(),
            },
        ],
        samples: vec![
            Sample {
                locations: vec!["main".to_string(), "process_request".to_string(), "db_query".to_string()],
                values: vec![1_000_000, 1024],
            },
            Sample {
                locations: vec!["main".to_string(), "process_request".to_string(), "render".to_string()],
                values: vec![500_000, 2048],
            },
        ],
        duration_nanos: Some(30_000_000_000), // 30 seconds
        time_nanos: SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
    }
}

/// Demonstrate response aggregation across multiple requests
async fn demonstrate_response_aggregation() -> Result<(), Box<dyn std::error::Error>> {
    use std::time::Instant;

    let mut aggregator = ResponseAggregator::new();

    // Simulate multiple export responses
    for i in 0..5 {
        let metadata = otlp::response::ResponseMetadata::new(
            format!("req-{}", i),
            SignalType::Trace,
            100,
        );

        let response = if i < 2 {
            // Full success
            ResponseType::FullSuccess {
                accepted_count: 100,
                metadata,
            }
        } else if i < 4 {
            // Partial success
            let mut handler = PartialSuccessHandler::<()>::new(100);
            handler.handle_partial_success_raw(10, "rate limit");
            ResponseType::PartialSuccess {
                handler,
                error_message: "rate limit".to_string(),
                metadata,
            }
        } else {
            // Failure
            ResponseType::Failure {
                error: "connection timeout".to_string(),
                retryable: true,
                metadata,
            }
        };

        aggregator.add(response);
    }

    let summary = aggregator.summary();
    println!("✅ Response Aggregation Summary:");
    println!("   • Total responses: {}", summary.total_responses);
    println!("   • Full successes: {}", summary.full_success_count);
    println!("   • Partial successes: {}", summary.partial_success_count);
    println!("   • Failures: {}", summary.failure_count);
    println!("   • Items accepted: {}", summary.total_items_accepted);
    println!("   • Items rejected: {}", summary.total_items_rejected);
    println!("   • Overall acceptance rate: {:.1}%\n", 
        summary.overall_acceptance_rate * 100.0);

    Ok(())
}

/// Demonstrate comprehensive error handling
fn demonstrate_error_handling() -> Result<(), Box<dyn std::error::Error>> {
    // Example 1: Network error
    let network_error = OtlpError::new(
        "Failed to connect to OTLP endpoint",
        ErrorCategory::Network,
        ErrorSeverity::Error,
    )
    .with_context("endpoint", "http://localhost:4317")
    .with_context("retryable", "true")
    .with_source(std::io::Error::new(
        std::io::ErrorKind::ConnectionRefused,
        "connection refused",
    ));

    println!("✅ Network Error Example:");
    println!("   • Message: {}", network_error.message());
    println!("   • Category: {:?}", network_error.category());
    println!("   • Severity: {:?}", network_error.severity());
    println!("   • Retryable: {}\n", network_error.is_retryable());

    // Example 2: Validation error
    let validation_error = OtlpError::validation_error(
        "Invalid metric data: negative counter value",
    )
    .with_context("metric_name", "http_requests_total")
    .with_context("value", "-5");

    println!("✅ Validation Error Example:");
    println!("   • Message: {}", validation_error.message());
    println!("   • Category: {:?}", validation_error.category());
    println!("   • Severity: {:?}", validation_error.severity());
    println!("   • Retryable: {}\n", validation_error.is_retryable());

    // Example 3: Timeout error with retry info
    let timeout_error = OtlpError::timeout_error(
        "Export operation timed out",
        Duration::from_secs(30),
    )
    .with_retry_after(Duration::from_secs(5));

    println!("✅ Timeout Error Example:");
    println!("   • Message: {}", timeout_error.message());
    println!("   • Category: {:?}", timeout_error.category());
    println!("   • Has retry_after: {}\n", timeout_error.retry_after().is_some());

    Ok(())
}

/// Demonstrate graceful shutdown procedures
async fn demonstrate_shutdown() -> Result<(), Box<dyn std::error::Error>> {
    // Create a simple log processor for demonstration
    let exporter = LogExporterBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build();

    let processor = SimpleLogProcessor::new(exporter);

    // Emit some logs
    for i in 0..5 {
        let log = LogRecord::builder()
            .with_message(format!("Log message {}", i + 1))
            .with_severity(SeverityLevel::Info)
            .build();
        
        if let Err(e) = processor.emit(log).await {
            eprintln!("   Warning: Failed to emit log: {}", e);
        }
    }

    println!("   • Emitted 5 log records\n");

    // Force flush before shutdown
    println!("   Step 1: Flushing pending data...");
    match processor.force_flush().await {
        Ok(result) => println!("         ✅ Flushed {} logs successfully", result.success_count),
        Err(e) => println!("         ⚠️  Flush warning: {}", e),
    }

    // Shutdown
    println!("   Step 2: Shutting down processor...");
    match processor.shutdown().await {
        Ok(_) => println!("         ✅ Shutdown complete\n"),
        Err(e) => println!("         ⚠️  Shutdown warning: {}\n", e),
    }

    Ok(())
}
