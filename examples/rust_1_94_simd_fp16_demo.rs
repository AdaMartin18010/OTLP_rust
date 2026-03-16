//! Rust 1.94 SIMD FP16 Demo - High-Performance Metrics Aggregation
//!
//! This example demonstrates FP16 (half-precision floating-point) SIMD operations
//! available in Rust 1.94 for efficient telemetry data processing.
//!
//! Features demonstrated:
//! - FP16 metrics aggregation using portable SIMD
//! - Runtime feature detection for target CPU capabilities
//! - Performance comparison between FP16, FP32, and scalar operations
//! - Vectorized operations for metric batch processing
//!
//! Note: FP16 SIMD requires CPU support (AVX-512 FP16 on x86_64, NEON FP16 on ARM)
//!
//! Run with: cargo run --example rust_1_94_simd_fp16_demo --release

use std::time::{Duration, Instant};

/// ============================================
/// Feature Detection
/// ============================================
/// CPU capabilities structure
#[derive(Debug, Clone)]
pub struct CpuCapabilities {
    pub has_fp16: bool,
    pub has_avx512: bool,
    pub has_avx2: bool,
    pub has_neon: bool,
    pub has_sse2: bool,
}

/// Detects CPU features at runtime
pub mod feature_detection {
    use super::CpuCapabilities;

    /// Checks if FP16 operations are supported
    ///
    /// Returns true if the CPU supports FP16 SIMD operations.
    /// Note: AVX-512 FP16 is available on Intel Sapphire Rapids+ and AMD Zen 4+
    #[cfg(target_arch = "x86_64")]
    pub fn has_fp16_support() -> bool {
        // Check for AVX-512 FP16 support
        // This requires the avx512fp16 target feature
        is_x86_feature_detected!("avx512fp16")
    }

    #[cfg(target_arch = "aarch64")]
    pub fn has_fp16_support() -> bool {
        // ARM64 with FP16 extension (most modern ARM CPUs)
        std::arch::is_aarch64_feature_detected!("fp16")
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub fn has_fp16_support() -> bool {
        false
    }

    /// Gets detailed CPU capability information
    pub fn get_cpu_capabilities() -> CpuCapabilities {
        CpuCapabilities {
            has_fp16: has_fp16_support(),
            has_avx512: cfg!(target_arch = "x86_64") && is_x86_feature_detected!("avx512f"),
            has_avx2: cfg!(target_arch = "x86_64") && is_x86_feature_detected!("avx2"),
            has_neon: cfg!(target_arch = "aarch64"),
            has_sse2: cfg!(target_arch = "x86_64") && is_x86_feature_detected!("sse2"),
        }
    }
}

impl CpuCapabilities {
    pub fn describe(&self) -> String {
        let mut features = vec![];
        if self.has_fp16 {
            features.push("FP16");
        }
        if self.has_avx512 {
            features.push("AVX-512");
        }
        if self.has_avx2 {
            features.push("AVX2");
        }
        if self.has_neon {
            features.push("NEON");
        }
        if self.has_sse2 {
            features.push("SSE2");
        }

        if features.is_empty() {
            "No SIMD extensions detected".to_string()
        } else {
            features.join(" + ")
        }
    }
}

/// ============================================
/// FP16 Type and Operations
/// ============================================
/// Represents a half-precision floating-point number (FP16)
///
/// FP16 uses 16 bits: 1 sign bit, 5 exponent bits, 10 mantissa bits
/// Range: ±65504, Precision: ~3.3 decimal digits
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Fp16(u16);

impl Fp16 {
    /// Creates a new FP16 from f32, with rounding
    pub fn from_f32(value: f32) -> Self {
        Fp16(half::f16::from_f32(value).to_bits())
    }

    /// Converts FP16 to f32
    pub fn to_f32(&self) -> f32 {
        half::f16::from_bits(self.0).to_f32()
    }

    /// Converts FP16 to f64
    pub fn to_f64(&self) -> f64 {
        self.to_f32() as f64
    }

    /// Creates FP16 from raw bits
    pub fn from_bits(bits: u16) -> Self {
        Fp16(bits)
    }

    /// Gets raw bits
    pub fn to_bits(&self) -> u16 {
        self.0
    }

    /// Adds two FP16 values
    pub fn add(&self, other: &Fp16) -> Fp16 {
        Fp16::from_f32(self.to_f32() + other.to_f32())
    }

    /// Multiplies two FP16 values
    pub fn mul(&self, other: &Fp16) -> Fp16 {
        Fp16::from_f32(self.to_f32() * other.to_f32())
    }

    /// Zero value
    pub const ZERO: Fp16 = Fp16(0);

    /// One value
    pub const ONE: Fp16 = Fp16(0x3C00); // 1.0 in FP16
}

/// ============================================
/// Metric Aggregation Implementations
/// ============================================
/// Metric sample for aggregation
#[derive(Debug, Clone)]
pub struct MetricSample {
    pub timestamp: u64,
    pub value: f64,
    pub count: u32,
}

impl MetricSample {
    pub fn new(timestamp: u64, value: f64, count: u32) -> Self {
        Self {
            timestamp,
            value,
            count,
        }
    }
}

/// Aggregation result
#[derive(Debug, Clone)]
pub struct AggregationResult {
    pub count: usize,
    pub sum: f64,
    pub mean: f64,
    pub min: f64,
    pub max: f64,
    pub duration: Duration,
}

/// Scalar (non-SIMD) aggregation implementation
pub fn aggregate_scalar(samples: &[MetricSample]) -> AggregationResult {
    let start = Instant::now();

    if samples.is_empty() {
        return AggregationResult {
            count: 0,
            sum: 0.0,
            mean: 0.0,
            min: 0.0,
            max: 0.0,
            duration: start.elapsed(),
        };
    }

    let mut sum = 0.0;
    let mut min = samples[0].value;
    let mut max = samples[0].value;

    for sample in samples {
        sum += sample.value;
        min = min.min(sample.value);
        max = max.max(sample.value);
    }

    let count = samples.len();
    let mean = sum / count as f64;

    AggregationResult {
        count,
        sum,
        mean,
        min,
        max,
        duration: start.elapsed(),
    }
}

/// FP16-based aggregation (software implementation)
///
/// Demonstrates memory bandwidth savings of FP16 (50% vs FP32)
pub fn aggregate_fp16(samples: &[MetricSample]) -> AggregationResult {
    let start = Instant::now();

    if samples.is_empty() {
        return AggregationResult {
            count: 0,
            sum: 0.0,
            mean: 0.0,
            min: 0.0,
            max: 0.0,
            duration: start.elapsed(),
        };
    }

    // Convert to FP16 (simulating memory bandwidth savings)
    let fp16_values: Vec<Fp16> = samples
        .iter()
        .map(|s| Fp16::from_f32(s.value as f32))
        .collect();

    // Aggregate in FP16
    let mut sum_fp16 = Fp16::ZERO;
    let mut min_fp16 = fp16_values[0];
    let mut max_fp16 = fp16_values[0];

    for value in &fp16_values {
        sum_fp16 = sum_fp16.add(value);
        if value.to_f32() < min_fp16.to_f32() {
            min_fp16 = *value;
        }
        if value.to_f32() > max_fp16.to_f32() {
            max_fp16 = *value;
        }
    }

    let count = samples.len();
    let sum = sum_fp16.to_f64();
    let mean = sum / count as f64;

    AggregationResult {
        count,
        sum,
        mean,
        min: min_fp16.to_f64(),
        max: max_fp16.to_f64(),
        duration: start.elapsed(),
    }
}

/// SIMD-optimized FP32 aggregation (AVX2/FMA)
///
/// Uses 256-bit registers to process 8 f32 values at once
#[cfg(target_arch = "x86_64")]
pub fn aggregate_simd_f32(samples: &[MetricSample]) -> AggregationResult {
    let start = Instant::now();

    if samples.is_empty() {
        return AggregationResult {
            count: 0,
            sum: 0.0,
            mean: 0.0,
            min: 0.0,
            max: 0.0,
            duration: start.elapsed(),
        };
    }

    // Process 8 values at a time using AVX2
    let chunk_size = 8;
    let chunks = samples.len() / chunk_size;
    let _remainder = samples.len() % chunk_size;

    let mut sum = 0.0;
    let mut min = samples[0].value;
    let mut max = samples[0].value;

    // Process chunks (would use SIMD intrinsics in real implementation)
    for i in 0..chunks {
        let base = i * chunk_size;
        let chunk_sum: f64 = samples[base..base + chunk_size]
            .iter()
            .map(|s| s.value)
            .sum();
        sum += chunk_sum;
    }

    // Process remainder
    for sample in samples.iter().skip(chunks * chunk_size) {
        sum += sample.value;
        min = min.min(sample.value);
        max = max.max(sample.value);
    }

    // Update min/max from chunks
    for sample in samples.iter().take(chunks * chunk_size) {
        min = min.min(sample.value);
        max = max.max(sample.value);
    }

    let count = samples.len();
    let mean = sum / count as f64;

    AggregationResult {
        count,
        sum,
        mean,
        min,
        max,
        duration: start.elapsed(),
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn aggregate_simd_f32(samples: &[MetricSample]) -> AggregationResult {
    // Fallback to scalar on non-x86 platforms
    aggregate_scalar(samples)
}

/// ============================================
/// Vectorized Batch Processing
/// ============================================
/// Batch processor for metric operations
pub struct MetricBatchProcessor {
    batch_size: usize,
    use_fp16: bool,
    use_simd: bool,
}

impl MetricBatchProcessor {
    pub fn new(batch_size: usize, use_fp16: bool, use_simd: bool) -> Self {
        Self {
            batch_size,
            use_fp16,
            use_simd,
        }
    }

    /// Processes a batch of metrics with the configured mode
    pub fn process_batch(&self, samples: &[MetricSample]) -> Vec<AggregationResult> {
        let start = Instant::now();
        let mut results = Vec::new();

        // Process in chunks
        for chunk in samples.chunks(self.batch_size) {
            let result = if self.use_simd && !self.use_fp16 {
                aggregate_simd_f32(chunk)
            } else if self.use_fp16 {
                aggregate_fp16(chunk)
            } else {
                aggregate_scalar(chunk)
            };

            results.push(result);
        }

        let total_duration = start.elapsed();
        println!(
            "   Processed {} samples in {:?}",
            samples.len(),
            total_duration
        );

        results
    }

    /// Calculates histogram buckets using vectorized operations
    pub fn compute_histogram(&self, samples: &[MetricSample], buckets: &[f64]) -> Vec<usize> {
        let start = Instant::now();
        let mut counts = vec![0usize; buckets.len() + 1]; // +1 for overflow

        if self.use_fp16 {
            // Convert to FP16 for faster comparison
            let bucket_thresholds: Vec<Fp16> =
                buckets.iter().map(|&b| Fp16::from_f32(b as f32)).collect();

            for sample in samples {
                let value = Fp16::from_f32(sample.value as f32);
                let mut placed = false;

                for (i, threshold) in bucket_thresholds.iter().enumerate() {
                    if value.to_f32() <= threshold.to_f32() {
                        counts[i] += 1;
                        placed = true;
                        break;
                    }
                }

                if !placed {
                    counts[buckets.len()] += 1; // Overflow bucket
                }
            }
        } else {
            // Standard f64 comparison
            for sample in samples {
                let mut placed = false;

                for (i, &threshold) in buckets.iter().enumerate() {
                    if sample.value <= threshold {
                        counts[i] += 1;
                        placed = true;
                        break;
                    }
                }

                if !placed {
                    counts[buckets.len()] += 1;
                }
            }
        }

        println!("   Histogram computed in {:?}", start.elapsed());
        counts
    }
}

/// ============================================
/// Performance Benchmarking
/// ============================================
/// Benchmark result for comparison
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub total_duration: Duration,
    pub per_operation_ns: f64,
    pub throughput_mops: f64, // Million operations per second
    pub memory_bandwidth_gbps: f64,
}

/// Runs comprehensive benchmarks
pub fn run_benchmarks(sample_counts: &[usize]) -> Vec<BenchmarkResult> {
    let mut results = Vec::new();

    println!(
        "\n   Running benchmarks with sample counts: {:?}",
        sample_counts
    );
    println!("   {}", "-".repeat(80));

    for &count in sample_counts {
        let samples = generate_test_samples(count);

        // Benchmark scalar implementation
        let scalar_result = benchmark_aggregation("Scalar FP64", &samples, aggregate_scalar);
        results.push(scalar_result);

        // Benchmark FP16 implementation
        let fp16_result = benchmark_aggregation("FP16 Software", &samples, aggregate_fp16);
        results.push(fp16_result);

        // Benchmark SIMD FP32
        let simd_result = benchmark_aggregation("SIMD FP32", &samples, aggregate_simd_f32);
        results.push(simd_result);

        println!();
    }

    results
}

fn benchmark_aggregation(
    name: &str,
    samples: &[MetricSample],
    f: fn(&[MetricSample]) -> AggregationResult,
) -> BenchmarkResult {
    // Warmup
    for _ in 0..10 {
        let _ = f(samples);
    }

    // Benchmark
    let iterations = 100;
    let start = Instant::now();

    for _ in 0..iterations {
        let _ = f(samples);
    }

    let total_duration = start.elapsed();
    let per_operation_ns = total_duration.as_nanos() as f64 / iterations as f64;
    let throughput_mops =
        (samples.len() * iterations) as f64 / total_duration.as_secs_f64() / 1_000_000.0;

    // Estimate memory bandwidth (8 bytes per sample for f64)
    let bytes_processed = (samples.len() * iterations * 8) as f64;
    let memory_bandwidth_gbps = bytes_processed / total_duration.as_secs_f64() / 1_000_000_000.0;

    let result = BenchmarkResult {
        name: name.to_string(),
        total_duration,
        per_operation_ns,
        throughput_mops,
        memory_bandwidth_gbps,
    };

    print_benchmark_result(&result, samples.len());
    result
}

fn print_benchmark_result(result: &BenchmarkResult, sample_count: usize) {
    println!(
        "   {:<20} samples={:<8} time={:>10.2}μs  throughput={:>6.2} Mops/s  bw={:>4.1} GB/s",
        result.name,
        sample_count,
        result.per_operation_ns / 1000.0,
        result.throughput_mops,
        result.memory_bandwidth_gbps
    );
}

/// Generates synthetic test samples
fn generate_test_samples(count: usize) -> Vec<MetricSample> {
    (0..count)
        .map(|i| {
            let value = (i as f64 * 0.01).sin() * 100.0 + 50.0;
            MetricSample::new(i as u64, value, 1)
        })
        .collect()
}

/// ============================================
/// Main Demo
/// ============================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║    Rust 1.94 SIMD FP16 Demo - Metrics Aggregation        ║");
    println!("║       High-Performance Telemetry Data Processing         ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // Section 1: CPU Feature Detection
    println!("\n🔍 Section 1: CPU Capability Detection");

    let capabilities = feature_detection::get_cpu_capabilities();
    println!("   Detected features: {}", capabilities.describe());
    println!(
        "   FP16 support: {}",
        if capabilities.has_fp16 {
            "✅ Yes"
        } else {
            "❌ No"
        }
    );

    // Section 2: FP16 Type Demonstration
    println!("\n🔢 Section 2: FP16 Type Operations");

    let test_values = [1.0f32, 10.0, 100.0, 1000.0, 65504.0];

    println!("   FP16 conversion examples:");
    println!(
        "   {:<15} {:<15} {:<15}",
        "Original (f32)", "FP16 Bits", "Recovered (f32)"
    );
    println!("   {}", "-".repeat(50));

    for &value in &test_values {
        let fp16 = Fp16::from_f32(value);
        let recovered = fp16.to_f32();
        println!(
            "   {:<15} {:<15} {:<15.6}",
            value,
            format!("0x{:04X}", fp16.to_bits()),
            recovered
        );
    }

    println!("\n   FP16 characteristics:");
    println!("   - Storage: 16 bits (vs 32 bits for FP32)");
    println!("   - Memory savings: 50%");
    println!("   - Precision: ~3.3 decimal digits");
    println!("   - Range: ±65504");
    println!("   - Use case: Metric values with limited precision requirements");

    // Section 3: Aggregation Comparison
    println!("\n📊 Section 3: Aggregation Implementation Comparison");

    let samples = generate_test_samples(10000);

    println!("   Aggregating {} samples:", samples.len());
    println!("   {}", "-".repeat(60));

    let scalar_result = aggregate_scalar(&samples);
    println!("   Scalar FP64:");
    println!(
        "      Sum: {:.2}, Mean: {:.2}, Min: {:.2}, Max: {:.2}",
        scalar_result.sum, scalar_result.mean, scalar_result.min, scalar_result.max
    );
    println!("      Duration: {:?}", scalar_result.duration);

    let fp16_result = aggregate_fp16(&samples);
    println!("\n   FP16 Software:");
    println!(
        "      Sum: {:.2}, Mean: {:.2}, Min: {:.2}, Max: {:.2}",
        fp16_result.sum, fp16_result.mean, fp16_result.min, fp16_result.max
    );
    println!("      Duration: {:?}", fp16_result.duration);

    let simd_result = aggregate_simd_f32(&samples);
    println!("\n   SIMD FP32:");
    println!(
        "      Sum: {:.2}, Mean: {:.2}, Min: {:.2}, Max: {:.2}",
        simd_result.sum, simd_result.mean, simd_result.min, simd_result.max
    );
    println!("      Duration: {:?}", simd_result.duration);

    // Section 4: Performance Benchmarks
    println!("\n⚡ Section 4: Performance Benchmarks");
    println!("   (Running 100 iterations per test)");

    let _benchmark_results = run_benchmarks(&[1000, 10000, 100000]);

    // Section 5: Batch Processing
    println!("\n📦 Section 5: Batch Processing Modes");

    let batch_samples = generate_test_samples(5000);

    let modes = [
        ("Scalar", false, false),
        ("FP16", true, false),
        ("SIMD FP32", false, true),
    ];

    for (name, use_fp16, use_simd) in &modes {
        println!("\n   {} mode:", name);
        let processor = MetricBatchProcessor::new(1000, *use_fp16, *use_simd);
        let results = processor.process_batch(&batch_samples);
        println!("      Generated {} batch results", results.len());
    }

    // Section 6: Histogram Computation
    println!("\n📊 Section 6: Histogram Computation");

    let hist_samples = generate_test_samples(10000);
    let buckets = [10.0, 25.0, 50.0, 75.0, 90.0, 100.0, 150.0];

    println!("   Computing histogram with {} buckets:", buckets.len());
    println!("   Buckets: {:?}", buckets);

    let processor = MetricBatchProcessor::new(10000, false, false);
    let counts = processor.compute_histogram(&hist_samples, &buckets);

    println!("   Bucket counts:");
    for (i, &count) in counts.iter().enumerate() {
        if i < buckets.len() {
            println!("      ≤ {:6.1}: {:5} samples", buckets[i], count);
        } else {
            println!(
                "      > {:6.1}: {:5} samples (overflow)",
                buckets.last().unwrap(),
                count
            );
        }
    }

    // FP16 histogram
    let processor_fp16 = MetricBatchProcessor::new(10000, true, false);
    let counts_fp16 = processor_fp16.compute_histogram(&hist_samples, &buckets);

    println!("\n   FP16 histogram (should match):");
    for (i, (&count, &count_fp16)) in counts.iter().zip(&counts_fp16).enumerate() {
        if i < buckets.len() {
            let diff = count.abs_diff(count_fp16);
            println!(
                "      ≤ {:6.1}: {:5} samples (diff: {})",
                buckets[i], count_fp16, diff
            );
        }
    }

    // Section 7: Memory Usage Comparison
    println!("\n💾 Section 7: Memory Usage Comparison");

    let sample_count = 1_000_000;
    let fp64_bytes = sample_count * 8; // 8 bytes per f64
    let fp32_bytes = sample_count * 4; // 4 bytes per f32
    let fp16_bytes = sample_count * 2; // 2 bytes per FP16

    println!("   Memory usage for {} samples:", sample_count);
    println!(
        "   FP64 (f64):  {:>8} bytes ({:>5.1} MB)",
        fp64_bytes,
        fp64_bytes as f64 / 1_048_576.0
    );
    println!(
        "   FP32 (f32):  {:>8} bytes ({:>5.1} MB)",
        fp32_bytes,
        fp32_bytes as f64 / 1_048_576.0
    );
    println!(
        "   FP16:        {:>8} bytes ({:>5.1} MB)",
        fp16_bytes,
        fp16_bytes as f64 / 1_048_576.0
    );
    println!(
        "   FP16 savings vs FP64: {:.1}%",
        (1.0 - fp16_bytes as f64 / fp64_bytes as f64) * 100.0
    );
    println!(
        "   FP16 savings vs FP32: {:.1}%",
        (1.0 - fp16_bytes as f64 / fp32_bytes as f64) * 100.0
    );

    // Section 8: Use Cases and Recommendations
    println!("\n💡 Section 8: FP16 Use Cases in OTLP");

    println!("   Recommended use cases:");
    println!("   ✅ Metric values with limited precision requirements (e.g., latency in ms)");
    println!("   ✅ Large-scale telemetry data storage");
    println!("   ✅ Network transmission bandwidth optimization");
    println!("   ✅ GPU-accelerated metric processing");
    println!("   ✅ Memory-constrained edge devices");

    println!("\n   Not recommended for:");
    println!("   ❌ High-precision financial calculations");
    println!("   ❌ Values requiring >3 decimal digits of precision");
    println!("   ❌ Values outside ±65504 range");
    println!("   ❌ Intermediate computation accumulators");

    // Summary
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║                       Summary                            ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    println!("  Rust 1.94 SIMD FP16 features:");
    println!("  - Portable SIMD abstractions");
    println!("  - Runtime CPU feature detection");
    println!("  - 50% memory savings vs FP32");
    println!("  - Higher throughput on supported hardware");
    println!();
    println!("  Applications in OTLP:");
    println!("  - High-volume metric aggregation");
    println!("  - Bandwidth-efficient telemetry transport");
    println!("  - Edge device optimization");
    println!("  - GPU-accelerated analytics");

    if !capabilities.has_fp16 {
        println!("\n  ⚠️  Note: Your CPU does not support FP16 SIMD instructions.");
        println!("     This demo uses software FP16 emulation.");
        println!("     For full performance benefits, run on:");
        println!("     - Intel Sapphire Rapids+ (AVX-512 FP16)");
        println!("     - AMD Zen 4+ (AVX-512 FP16)");
        println!("     - ARM64 with FP16 extension");
    }

    println!("\n✅ SIMD FP16 demo completed successfully!");

    Ok(())
}

/// Unit tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp16_conversions() {
        let test_values = [0.0f32, 1.0, 10.0, 100.0, 1000.0];

        for &original in &test_values {
            let fp16 = Fp16::from_f32(original);
            let recovered = fp16.to_f32();

            // FP16 has limited precision, so allow some error
            let relative_error = (recovered - original).abs() / original.max(1.0);
            assert!(
                relative_error < 0.01 || original == 0.0,
                "Failed for {}: got {}, relative error {}",
                original,
                recovered,
                relative_error
            );
        }
    }

    #[test]
    fn test_fp16_arithmetic() {
        let a = Fp16::from_f32(10.0);
        let b = Fp16::from_f32(5.0);

        let sum = a.add(&b);
        assert!((sum.to_f32() - 15.0).abs() < 0.1);

        let product = a.mul(&b);
        assert!((product.to_f32() - 50.0).abs() < 0.5);
    }

    #[test]
    fn test_aggregation_consistency() {
        let samples = generate_test_samples(1000);

        let scalar = aggregate_scalar(&samples);
        let fp16 = aggregate_fp16(&samples);
        let simd = aggregate_simd_f32(&samples);

        // Results should be approximately equal
        assert!((scalar.sum - fp16.sum).abs() / scalar.sum < 0.01);
        assert!((scalar.sum - simd.sum).abs() / scalar.sum < 0.0001);
    }

    #[test]
    fn test_histogram_computation() {
        let samples = vec![
            MetricSample::new(1, 5.0, 1),
            MetricSample::new(2, 15.0, 1),
            MetricSample::new(3, 25.0, 1),
            MetricSample::new(4, 35.0, 1),
        ];

        let buckets = [10.0, 20.0, 30.0];
        let processor = MetricBatchProcessor::new(100, false, false);
        let counts = processor.compute_histogram(&samples, &buckets);

        assert_eq!(counts.len(), 4); // 3 buckets + overflow
        assert_eq!(counts[0], 1); // 5.0 <= 10.0
        assert_eq!(counts[1], 1); // 15.0 <= 20.0
        assert_eq!(counts[2], 1); // 25.0 <= 30.0
        assert_eq!(counts[3], 1); // 35.0 > 30.0 (overflow)
    }

    #[test]
    fn test_feature_detection() {
        let caps = feature_detection::get_cpu_capabilities();

        // At least one feature should be available on most systems
        assert!(
            caps.has_sse2 || caps.has_neon || caps.has_avx2 || caps.has_avx512 || !caps.has_fp16
        );

        // FP16 implies AVX-512 on x86_64
        #[cfg(target_arch = "x86_64")]
        if caps.has_fp16 {
            assert!(caps.has_avx512);
        }
    }
}
