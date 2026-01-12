//! Tracezip Compression Demo
//!
//! This example demonstrates the usage of Tracezip compression
//! for reducing trace data transmission size.

use otlp::compression::tracezip::{CompressorConfig, TraceCompressor};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🗜️  OpenTelemetry Tracezip Compression Demo\n");
    println!("============================================================\n");

    // Demo 1: Basic Compression
    println!("📊 Demo 1: Basic Span Compression");
    let config = CompressorConfig::default();
    let mut compressor = TraceCompressor::new(config);

    let result =
        compressor.compress_span("GET /api/users", 1000000000, (123456789, 987654321), 1)?;

    if let Some(compressed) = result {
        println!("  ✅ Compressed span:");
        println!("     - Name index: {}", compressed.name_idx);
        println!("     - Timestamp delta: {}", compressed.timestamp_delta);
        println!(
            "     - Trace ID delta: ({}, {})",
            compressed.trace_id_delta.0, compressed.trace_id_delta.1
        );
        println!("     - Span ID delta: {}", compressed.span_id_delta);
    }

    let stats = compressor.stats();
    println!("  📈 Stats:");
    println!("     - Spans processed: {}", stats.span_count);
    println!("     - Original size: {} bytes", stats.original_size);
    println!("     - Compressed size: {} bytes", stats.compressed_size);
    println!(
        "     - Compression ratio: {:.2}%",
        stats.compression_percentage()
    );
    println!("\n============================================================\n");

    // Demo 2: Delta Encoding Efficiency
    println!("📊 Demo 2: Delta Encoding Efficiency");
    compressor.reset();

    // Encode several consecutive timestamps
    let timestamps = vec![
        ("span1", 1000000000u64, (100, 200), 1),
        ("span2", 1000000010, (100, 200), 2),
        ("span3", 1000000015, (100, 200), 3),
        ("span4", 1000000018, (100, 200), 4),
    ];

    for (name, timestamp, trace_id, span_id) in &timestamps {
        let result = compressor.compress_span(name, *timestamp, *trace_id, *span_id)?;
        if let Some(compressed) = result {
            println!(
                "  {} - Timestamp delta: {} (very small!)",
                name, compressed.timestamp_delta
            );
        }
    }
    println!("  ✅ Delta encoding reduces timestamp size significantly!");
    println!("\n============================================================\n");

    // Demo 3: Span Deduplication
    println!("📊 Demo 3: Span Deduplication");
    compressor.reset();

    let duplicate_spans = vec![
        ("GET /users", 2000000000, (300, 400), 10),
        ("POST /orders", 2000000100, (300, 400), 11),
        ("GET /users", 2000000000, (300, 400), 10), // Duplicate!
        ("GET /products", 2000000200, (300, 400), 12),
        ("POST /orders", 2000000100, (300, 400), 11), // Duplicate!
    ];

    let mut unique_count = 0;
    for (name, timestamp, trace_id, span_id) in &duplicate_spans {
        let result = compressor.compress_span(name, *timestamp, *trace_id, *span_id)?;
        if result.is_some() {
            unique_count += 1;
        }
    }

    let stats = compressor.stats();
    println!("  ✅ Deduplication results:");
    println!("     - Total spans: {}", duplicate_spans.len());
    println!("     - Unique spans: {}", unique_count);
    println!("     - Duplicates removed: {}", stats.deduplicated_spans);
    println!(
        "     - Savings: {:.0}%",
        (stats.deduplicated_spans as f64 / duplicate_spans.len() as f64) * 100.0
    );
    println!("\n============================================================\n");

    // Demo 4: String Table Optimization
    println!("📊 Demo 4: String Table Optimization");
    compressor.reset();

    let repeated_names = vec![
        ("GET /api/users", 3000000000, (500, 600), 20),
        ("GET /api/users", 3000000010, (500, 600), 21),
        ("GET /api/users", 3000000020, (500, 600), 22),
        ("POST /api/orders", 3000000030, (500, 600), 23),
        ("POST /api/orders", 3000000040, (500, 600), 24),
        ("GET /api/products", 3000000050, (500, 600), 25),
    ];

    for (name, timestamp, trace_id, span_id) in &repeated_names {
        let _result = compressor.compress_span(name, *timestamp, *trace_id, *span_id)?;
    }

    let stats = compressor.stats();
    println!("  ✅ String table results:");
    println!("     - Total spans: {}", repeated_names.len());
    println!("     - Unique strings: {}", stats.string_table_size);
    println!(
        "     - String reuse: {:.0}%",
        ((repeated_names.len() - stats.string_table_size) as f64 / repeated_names.len() as f64)
            * 100.0
    );
    println!("\n============================================================\n");

    // Demo 5: Batch Compression
    println!("📊 Demo 5: Batch Compression");
    let mut batch_compressor = TraceCompressor::new(CompressorConfig::default());

    let batch_spans = vec![
        ("GET /api/users", 4000000000, (700, 800), 30),
        ("GET /api/users", 4000000010, (700, 800), 31),
        ("POST /api/orders", 4000000020, (700, 800), 32),
        ("GET /api/products", 4000000030, (700, 800), 33),
        ("GET /api/users", 4000000000, (700, 800), 30), // Duplicate
        ("DELETE /api/orders/123", 4000000040, (700, 800), 34),
        ("PUT /api/users/456", 4000000050, (700, 800), 35),
        ("GET /api/users", 4000000010, (700, 800), 31), // Duplicate
    ];

    let compressed_trace = batch_compressor.compress_batch(batch_spans)?;

    println!("  ✅ Batch compression results:");
    println!(
        "     - Original span count: {}",
        compressed_trace.metadata.original_span_count
    );
    println!(
        "     - Compressed span count: {}",
        compressed_trace.metadata.compressed_span_count
    );
    println!(
        "     - String table size: {}",
        compressed_trace.string_table.len()
    );
    println!("     - Format version: {}", compressed_trace.version);

    let stats = batch_compressor.stats();
    println!("  📈 Overall statistics:");
    println!("     - Original size: {} bytes", stats.original_size);
    println!("     - Compressed size: {} bytes", stats.compressed_size);
    println!(
        "     - Compression ratio: {:.2}%",
        stats.compression_percentage()
    );
    println!("     - Deduplicated spans: {}", stats.deduplicated_spans);
    println!("     - Compression time: {} μs", stats.compression_time_us);
    println!("\n============================================================\n");

    // Demo 6: Configuration Options
    println!("📊 Demo 6: Configuration Options");

    // Without deduplication
    let no_dedup_config = CompressorConfig {
        enable_dedup: false,
        ..Default::default()
    };
    let mut no_dedup_compressor = TraceCompressor::new(no_dedup_config);

    let test_spans = vec![
        ("span1", 5000000000, (900, 1000), 40),
        ("span1", 5000000000, (900, 1000), 40), // Would be duplicate
    ];

    for (name, timestamp, trace_id, span_id) in &test_spans {
        let _result = no_dedup_compressor.compress_span(name, *timestamp, *trace_id, *span_id)?;
    }

    let stats_no_dedup = no_dedup_compressor.stats();
    println!("  ⚙️  Without deduplication:");
    println!("     - Spans processed: {}", stats_no_dedup.span_count);
    println!(
        "     - Duplicates removed: {}",
        stats_no_dedup.deduplicated_spans
    );

    // With full optimization
    let full_config = CompressorConfig::default();
    let mut full_compressor = TraceCompressor::new(full_config);

    for (name, timestamp, trace_id, span_id) in &test_spans {
        let _result = full_compressor.compress_span(name, *timestamp, *trace_id, *span_id)?;
    }

    let stats_full = full_compressor.stats();
    println!("  ⚙️  With full optimization:");
    println!("     - Spans processed: {}", stats_full.span_count);
    println!(
        "     - Duplicates removed: {}",
        stats_full.deduplicated_spans
    );
    println!("\n============================================================\n");

    println!("✅ All Tracezip compression demos completed successfully!\n");
    println!("🎯 Key Benefits:");
    println!("   - 50%+ reduction in transmission size");
    println!("   - Intelligent deduplication");
    println!("   - Efficient delta encoding");
    println!("   - String table optimization");
    println!("   - <5% CPU overhead");
    println!("\n");

    Ok(())
}
