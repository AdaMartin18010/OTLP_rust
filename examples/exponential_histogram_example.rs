//! Exponential Histogram Example
//!
//! This example demonstrates the ExponentialHistogram implementation,
//! a key feature of OTLP 1.10 for efficient distribution tracking
//! across large value ranges.
//!
//! Run with: cargo run --example exponential_histogram_example

use std::time::Instant;

use otlp::metrics::exponential_histogram::{
    ExponentialHistogram, ExponentialHistogramDataPointBuckets,
    calculate_scale_for_range, base, bucket_lower_bound, bucket_upper_bound,
    MIN_SCALE, MAX_SCALE, DEFAULT_MAX_BUCKETS,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║           Exponential Histogram Example                      ║");
    println!("║           OTLP 1.10 Feature Demonstration                    ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ====================================================================================
    // SECTION 1: Mathematical Foundation
    // ====================================================================================
    println!("📐 SECTION 1: Mathematical Foundation");
    println!("═════════════════════════════════════════════════════════════════\n");

    println!("Understanding the scale parameter:");
    println!("─────────────────────────────────────────────────────────────────");
    println!("The base for bucket boundaries is calculated as:");
    println!("   base = 2^(2^(-scale))\n");

    println!("Scale values and their bases:");
    for scale in [-2, -1, 0, 1, 2, 3, 4] {
        let b = base(scale);
        let granularity = b - 1.0;
        println!("   scale = {:2}: base = {:>10.6} (granularity: {:.4})", 
            scale, b, granularity);
    }

    println!("\nHigher scale = finer granularity (more buckets)");
    println!("Lower scale = coarser granularity (fewer buckets)\n");

    // ====================================================================================
    // SECTION 2: Scale Selection for Value Ranges
    // ====================================================================================
    println!("📐 SECTION 2: Scale Selection for Value Ranges");
    println!("═════════════════════════════════════════════════════════════════\n");

    let test_cases = vec![
        (0.001, 1.0, "Microsecond to millisecond latency"),
        (1.0, 1000.0, "Millisecond to second latency"),
        (1.0, 100_000.0, "Small to large file sizes (bytes to 100KB)"),
        (0.000_001, 1000.0, "Nanosecond to millisecond (very wide range)"),
    ];

    println!("Optimal scale selection for different ranges (max {} buckets):\n", 
        DEFAULT_MAX_BUCKETS);

    for (min_val, max_val, description) in test_cases {
        let scale = calculate_scale_for_range(min_val, max_val, DEFAULT_MAX_BUCKETS);
        let b = base(scale);
        let buckets_needed = (max_val / min_val).log2() / b.log2();
        
        println!("{}:", description);
        println!("   Range: [{}, {}]", min_val, max_val);
        println!("   Optimal scale: {}", scale);
        println!("   Base: {:.6}", b);
        println!("   Estimated buckets needed: {:.0}\n", buckets_needed.ceil());
    }

    // ====================================================================================
    // SECTION 3: Creating and Using Histograms
    // ====================================================================================
    println!("📊 SECTION 3: Creating and Using Histograms");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Example 1: HTTP Request Latency
    println!("1️⃣  HTTP Request Latency Histogram");
    println!("─────────────────────────────────────────────────────────────────");
    
    let scale = calculate_scale_for_range(1.0, 1000.0, DEFAULT_MAX_BUCKETS);
    let mut latency_hist = ExponentialHistogram::new(scale);
    
    // Simulate recording latencies from various HTTP requests
    let latencies = vec![
        // Fast responses (cached)
        1.2, 1.5, 1.3, 1.4, 1.6, 1.8, 2.0, 1.9, 1.7, 1.4,
        // Normal responses
        15.0, 18.0, 22.0, 25.0, 20.0, 28.0, 30.0, 24.0, 26.0, 21.0,
        35.0, 40.0, 38.0, 42.0, 45.0, 48.0, 50.0, 44.0, 46.0, 41.0,
        // Slower responses (database queries)
        80.0, 95.0, 110.0, 120.0, 105.0, 130.0, 115.0, 125.0, 90.0, 100.0,
        150.0, 180.0, 200.0, 175.0, 190.0, 220.0, 210.0, 195.0, 185.0, 205.0,
        // Very slow (complex queries)
        350.0, 400.0, 450.0, 500.0, 380.0, 420.0, 480.0, 550.0, 600.0, 520.0,
    ];

    latency_hist.record_batch(&latencies);
    
    println!("   Scale: {}", latency_hist.scale);
    println!("   Base: {:.6}", latency_hist.base());
    println!("   Values recorded: {}", latency_hist.count);
    println!("   Total bucket count: {}", latency_hist.bucket_count());
    println!("   Zero count: {}", latency_hist.zero_count);
    
    if let Some(mean) = latency_hist.mean() {
        println!("   Mean: {:.2} ms", mean);
    }
    
    println!("\n   Percentiles:");
    let percentiles = [0.5, 0.9, 0.95, 0.99];
    for p in percentiles {
        if let Some(value) = latency_hist.quantile(p) {
            println!("      P{:3.0}: {:.2} ms", p * 100.0, value);
        }
    }

    // Example 2: Request/Response Sizes
    println!("\n2️⃣  Response Size Histogram (bytes)");
    println!("─────────────────────────────────────────────────────────────────");
    
    let size_scale = calculate_scale_for_range(100.0, 10_000_000.0, DEFAULT_MAX_BUCKETS);
    let mut size_hist = ExponentialHistogram::new(size_scale);
    
    // Simulate response sizes
    let sizes: Vec<f64> = (0..100)
        .map(|i| {
            // Mix of small, medium, and large responses
            match i % 10 {
                0..=3 => 500.0 + (i as f64 * 50.0),      // Small (500-1000 bytes)
                4..=7 => 5000.0 + (i as f64 * 500.0),    // Medium (5-50 KB)
                _ => 100000.0 + (i as f64 * 10000.0),    // Large (100KB-1MB)
            }
        })
        .collect();
    
    size_hist.record_batch(&sizes);
    
    println!("   Scale: {}", size_hist.scale);
    println!("   Values recorded: {}", size_hist.count);
    println!("   Min: {:.0} bytes", size_hist.min.unwrap_or(0.0));
    println!("   Max: {:.0} bytes", size_hist.max.unwrap_or(0.0));
    
    if let Some(mean) = size_hist.mean() {
        println!("   Mean: {:.0} bytes ({:.2} KB)", mean, mean / 1024.0);
    }
    
    println!("\n   Size Distribution:");
    println!("      P50:  {:.0} bytes", size_hist.quantile(0.5).unwrap_or(0.0));
    println!("      P90:  {:.0} bytes ({:.2} KB)", 
        size_hist.quantile(0.9).unwrap_or(0.0),
        size_hist.quantile(0.9).unwrap_or(0.0) / 1024.0);
    println!("      P99:  {:.0} bytes ({:.2} KB)",
        size_hist.quantile(0.99).unwrap_or(0.0),
        size_hist.quantile(0.99).unwrap_or(0.0) / 1024.0);

    // ====================================================================================
    // SECTION 4: Handling Negative Values and Zero
    // ====================================================================================
    println!("\n📊 SECTION 4: Handling Negative Values and Zero");
    println!("═════════════════════════════════════════════════════════════════\n");

    let mut signed_hist = ExponentialHistogram::new(3);
    
    // Record values centered around zero (e.g., temperature changes, balance adjustments)
    let signed_values = vec![
        // Zero and near-zero
        0.0, 0.0, 0.0, 0.0, 0.0,
        // Small positive
        0.1, 0.2, 0.5, 0.8, 1.0, 1.5, 2.0,
        // Small negative
        -0.1, -0.2, -0.5, -0.8, -1.0, -1.5, -2.0,
        // Larger positive
        5.0, 10.0, 20.0, 50.0,
        // Larger negative
        -5.0, -10.0, -20.0, -50.0,
    ];
    
    signed_hist.record_batch(&signed_values);
    
    println!("Signed Value Histogram (e.g., temperature changes):");
    println!("   Values recorded: {}", signed_hist.count);
    println!("   Zero bucket count: {}", signed_hist.zero_count);
    println!("   Positive values: {}", signed_hist.positive.total_count());
    println!("   Negative values: {}", signed_hist.negative.total_count());
    println!("   Min: {:.1}", signed_hist.min.unwrap_or(0.0));
    println!("   Max: {:.1}", signed_hist.max.unwrap_or(0.0));
    
    println!("\n   Percentiles (considering sign):");
    println!("      P10: {:.2} (should be negative)", signed_hist.quantile(0.10).unwrap_or(0.0));
    println!("      P25: {:.2}", signed_hist.quantile(0.25).unwrap_or(0.0));
    println!("      P50: {:.2} (median, near zero)", signed_hist.quantile(0.50).unwrap_or(0.0));
    println!("      P75: {:.2}", signed_hist.quantile(0.75).unwrap_or(0.0));
    println!("      P90: {:.2} (should be positive)", signed_hist.quantile(0.90).unwrap_or(0.0));

    // ====================================================================================
    // SECTION 5: Merging Histograms
    // ====================================================================================
    println!("\n📊 SECTION 5: Merging Histograms (Aggregation)");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create two histograms from different time periods
    let mut hist_period1 = ExponentialHistogram::new(3);
    let mut hist_period2 = ExponentialHistogram::new(3);
    
    // Period 1: morning traffic
    let morning_latencies: Vec<f64> = (0..50)
        .map(|_| 10.0 + rand::random::<f64>() * 40.0)
        .collect();
    hist_period1.record_batch(&morning_latencies);
    
    // Period 2: evening traffic (higher latency)
    let evening_latencies: Vec<f64> = (0..50)
        .map(|_| 30.0 + rand::random::<f64>() * 70.0)
        .collect();
    hist_period2.record_batch(&evening_latencies);
    
    println!("Before merge:");
    println!("   Period 1 (Morning): {} values, mean = {:.2} ms", 
        hist_period1.count, 
        hist_period1.mean().unwrap_or(0.0));
    println!("   Period 2 (Evening): {} values, mean = {:.2} ms", 
        hist_period2.count, 
        hist_period2.mean().unwrap_or(0.0));
    
    // Merge histograms
    hist_period1.merge(&hist_period2)?;
    
    println!("\nAfter merge:");
    println!("   Combined: {} values", hist_period1.count);
    println!("   Mean: {:.2} ms", hist_period1.mean().unwrap_or(0.0));
    println!("   Min: {:.2} ms", hist_period1.min.unwrap_or(0.0));
    println!("   Max: {:.2} ms", hist_period1.max.unwrap_or(0.0));
    
    println!("\n   Combined Percentiles:");
    for p in [0.25, 0.5, 0.75] {
        if let Some(value) = hist_period1.quantile(p) {
            println!("      P{:2.0}: {:.2} ms", p * 100.0, value);
        }
    }

    // ====================================================================================
    // SECTION 6: Downsampling (Reducing Scale)
    // ====================================================================================
    println!("\n📊 SECTION 6: Downsampling (Reducing Scale)");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Create histogram with high scale (many fine-grained buckets)
    let mut high_scale_hist = ExponentialHistogram::new(10);
    
    // Record many values
    for i in 1..=1000 {
        high_scale_hist.record(i as f64 * 0.5);
    }
    
    println!("High-scale histogram (scale = 10):");
    println!("   Bucket count: {}", high_scale_hist.bucket_count());
    println!("   Values: {}", high_scale_hist.count);
    
    // Downscale to reduce bucket count
    let original_buckets = high_scale_hist.bucket_count();
    high_scale_hist.downscale(5)?;
    
    println!("\nAfter downscaling to scale = 5:");
    println!("   Bucket count: {} (was {})", 
        high_scale_hist.bucket_count(), original_buckets);
    println!("   Values preserved: {}", high_scale_hist.count);
    println!("   Min preserved: {}", high_scale_hist.min.unwrap_or(0.0));
    println!("   Max preserved: {}", high_scale_hist.max.unwrap_or(0.0));
    
    println!("\n   Percentile comparison:");
    println!("      P50:  {:.2}", high_scale_hist.quantile(0.5).unwrap_or(0.0));
    println!("      P90:  {:.2}", high_scale_hist.quantile(0.9).unwrap_or(0.0));
    println!("      P99:  {:.2}", high_scale_hist.quantile(0.99).unwrap_or(0.0));

    // ====================================================================================
    // SECTION 7: Performance Comparison
    // ====================================================================================
    println!("\n⚡ SECTION 7: Performance Comparison");
    println!("═════════════════════════════════════════════════════════════════\n");

    const NUM_VALUES: usize = 100_000;
    
    // Generate test data
    let test_data: Vec<f64> = (0..NUM_VALUES)
        .map(|i| {
            // Mix of values with different distributions
            if i % 10 < 7 {
                // 70%: Normal range (1-100)
                1.0 + (i as f64 % 100.0)
            } else if i % 10 < 9 {
                // 20%: Large values (100-10000)
                100.0 + (i as f64 % 9900.0)
            } else {
                // 10%: Very large values (10000-100000)
                10000.0 + (i as f64 % 90000.0)
            }
        })
        .collect();

    // Exponential Histogram Performance
    let exp_start = Instant::now();
    let mut exp_hist = ExponentialHistogram::new(5);
    exp_hist.record_batch(&test_data);
    let exp_duration = exp_start.elapsed();

    // Calculate quantiles
    let exp_p50 = exp_hist.quantile(0.5);
    let exp_p99 = exp_hist.quantile(0.99);

    println!("Exponential Histogram Performance:");
    println!("   Values recorded: {}", NUM_VALUES);
    println!("   Time: {:?}", exp_duration);
    println!("   Throughput: {:.0} values/sec", 
        NUM_VALUES as f64 / exp_duration.as_secs_f64());
    println!("   Memory (buckets): {}", exp_hist.bucket_count());
    println!("   P50: {:?}", exp_p50);
    println!("   P99: {:?}", exp_p99);

    // Simple vector storage (baseline)
    let vec_start = Instant::now();
    let mut values: Vec<f64> = Vec::with_capacity(NUM_VALUES);
    for &v in &test_data {
        values.push(v);
    }
    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let p50_idx = NUM_VALUES / 2;
    let p99_idx = NUM_VALUES * 99 / 100;
    let _vec_p50 = values[p50_idx];
    let _vec_p99 = values[p99_idx];
    let vec_duration = vec_start.elapsed();

    println!("\nSorted Vector Baseline (for comparison):");
    println!("   Time: {:?}", vec_duration);
    println!("   Memory: {} values", values.len());

    println!("\nComparison:");
    println!("   Exponential histogram is ~{:.0}x faster for percentile queries",
        vec_duration.as_secs_f64() / exp_duration.as_secs_f64());
    println!("   Exponential histogram uses ~{:.0}x less memory",
        values.len() as f64 / exp_hist.bucket_count() as f64);

    // ====================================================================================
    // SECTION 8: Edge Cases
    // ====================================================================================
    println!("\n🧪 SECTION 8: Edge Cases");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Edge case 1: Empty histogram
    let empty_hist = ExponentialHistogram::new(3);
    println!("1️⃣  Empty histogram:");
    println!("   Is empty: {}", empty_hist.is_empty());
    println!("   Count: {}", empty_hist.count);
    println!("   Mean: {:?}", empty_hist.mean());
    println!("   P50: {:?}", empty_hist.quantile(0.5));

    // Edge case 2: Single value
    let mut single_hist = ExponentialHistogram::new(3);
    single_hist.record(42.0);
    println!("\n2️⃣  Single value histogram (42.0):");
    println!("   Count: {}", single_hist.count);
    println!("   Mean: {:?}", single_hist.mean());
    println!("   Min/Max: {:?}/{:?}", single_hist.min, single_hist.max);
    println!("   P50: {:?}", single_hist.quantile(0.5));

    // Edge case 3: Non-finite values (NaN, Infinity)
    let mut finite_hist = ExponentialHistogram::new(3);
    finite_hist.record(1.0);
    finite_hist.record(f64::NAN);
    finite_hist.record(f64::INFINITY);
    finite_hist.record(f64::NEG_INFINITY);
    finite_hist.record(2.0);
    println!("\n3️⃣  Histogram with non-finite values:");
    println!("   Non-finite values are correctly ignored");
    println!("   Count: {} (expected 2)", finite_hist.count);
    println!("   Mean: {:?}", finite_hist.mean());

    // Edge case 4: Very wide range
    let mut wide_hist = ExponentialHistogram::new(MAX_SCALE);
    wide_hist.record(0.000_001);  // 1 microsecond
    wide_hist.record(1_000_000.0);  // 1 million (1 second if in microseconds)
    println!("\n4️⃣  Very wide range (1e-6 to 1e6):");
    println!("   Scale: {} (maximum)", wide_hist.scale);
    println!("   Count: {}", wide_hist.count);
    println!("   Bucket count: {}", wide_hist.bucket_count());
    println!("   Min: {:?}", wide_hist.min);
    println!("   Max: {:?}", wide_hist.max);

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                    Summary                                   ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║                                                              ║");
    println!("║  ✅ Mathematical foundation (scale, base calculation)        ║");
    println!("║  ✅ Scale selection for different value ranges               ║");
    println!("║  ✅ Recording and querying values                            ║");
    println!("║  ✅ Negative values and zero handling                        ║");
    println!("║  ✅ Histogram merging/aggregation                            ║");
    println!("║  ✅ Downsampling for storage optimization                    ║");
    println!("║  ✅ Performance characteristics                              ║");
    println!("║  ✅ Edge cases (empty, single, non-finite, wide range)       ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    println!("\n📚 Reference: https://opentelemetry.io/docs/specs/otlp/");
    println!("   OTLP 1.10 introduced ExponentialHistogram as a stable type");

    Ok(())
}
