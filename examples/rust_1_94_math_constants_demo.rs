//! Rust 1.94 Math Constants Demo - Advanced Telemetry Algorithms
//!
//! This example demonstrates the mathematical constants feature (stabilized in Rust 1.94)
//! for advanced telemetry sampling, retry backoff calculations, and batch sizing.
//!
//! Features demonstrated:
//! - EULER_GAMMA for adaptive sampling algorithms
//! - GOLDEN_RATIO for optimal retry backoff
//! - Fibonacci batch sizing for flow control
//! - PI and TAU for periodic metric calculations
//! - Other math constants for telemetry use cases
//!
//! Run with: cargo run --example rust_1_94_math_constants_demo

use std::f64::consts::{
    E, EULER_GAMMA, GOLDEN_RATIO, LN_2, LN_10, LOG10_E, LOG2_E, PI, SQRT_2, TAU,
};
use std::time::Duration;

/// ============================================
/// EULER_GAMMA - Adaptive Sampling
/// ============================================

/// Adaptive sampler using Euler-Mascheroni constant
/// 
/// EULER_GAMMA (≈ 0.5772) appears in the asymptotic expansion of harmonic series
/// and is used here for intelligent sampling decisions based on accumulated error.
pub struct AdaptiveSampler {
    /// Base sampling rate (0.0 - 1.0)
    base_rate: f64,
    /// Current adaptive rate
    current_rate: f64,
    /// Total samples considered
    total_count: u64,
    /// Samples actually taken
    sampled_count: u64,
    /// Error threshold for adjustment
    error_threshold: f64,
    /// EULER_GAMMA used for harmonic series calculations
    gamma: f64,
}

impl AdaptiveSampler {
    pub fn new(base_rate: f64, error_threshold: f64) -> Self {
        Self {
            base_rate: base_rate.clamp(0.01, 1.0),
            current_rate: base_rate,
            total_count: 0,
            sampled_count: 0,
            error_threshold,
            gamma: EULER_GAMMA,
        }
    }
    
    /// Determines whether to sample the next item using adaptive rate
    /// 
    /// Uses EULER_GAMMA to adjust sampling rate based on the harmonic series
    /// approximation of accumulated error.
    pub fn should_sample(&mut self, estimated_importance: f64) -> bool {
        self.total_count += 1;
        
        // Calculate harmonic number approximation using EULER_GAMMA
        // H_n ≈ ln(n) + γ + 1/(2n)
        let n = self.total_count as f64;
        let harmonic_factor = n.ln() + self.gamma + 1.0 / (2.0 * n);
        
        // Adjust sampling rate based on harmonic factor and importance
        let adjustment = (harmonic_factor.ln() / 10.0).min(0.5);
        let adjusted_rate = (self.current_rate * (1.0 + adjustment * estimated_importance))
            .clamp(self.base_rate * 0.5, 1.0);
        
        let should_sample = rand::random::<f64>() < adjusted_rate;
        
        if should_sample {
            self.sampled_count += 1;
        }
        
        // Periodically adjust rate based on sampling error
        if self.total_count % 100 == 0 {
            self.adjust_rate();
        }
        
        should_sample
    }
    
    /// Adjusts sampling rate based on observed error
    fn adjust_rate(&mut self) {
        let actual_rate = self.sampled_count as f64 / self.total_count as f64;
        let error = (actual_rate - self.base_rate).abs();
        
        if error > self.error_threshold {
            // Use EULER_GAMMA to dampen adjustments
            let adjustment = (error * self.gamma).min(0.1);
            self.current_rate = if actual_rate > self.base_rate {
                self.current_rate - adjustment
            } else {
                self.current_rate + adjustment
            };
            self.current_rate = self.current_rate.clamp(0.01, 1.0);
        }
    }
    
    /// Gets current sampling statistics
    pub fn stats(&self) -> SamplingStats {
        SamplingStats {
            total_count: self.total_count,
            sampled_count: self.sampled_count,
            actual_rate: if self.total_count > 0 {
                self.sampled_count as f64 / self.total_count as f64
            } else {
                0.0
            },
            current_rate: self.current_rate,
            effective_gamma: self.gamma,
        }
    }
}

#[derive(Debug)]
pub struct SamplingStats {
    pub total_count: u64,
    pub sampled_count: u64,
    pub actual_rate: f64,
    pub current_rate: f64,
    pub effective_gamma: f64,
}

/// ============================================
/// GOLDEN_RATIO - Optimal Retry Backoff
/// ============================================

/// Golden ratio-based retry strategy
/// 
/// GOLDEN_RATIO (φ ≈ 1.618) provides optimal spacing for retry attempts,
/// following the principle that the ratio of successive intervals is φ.
pub struct GoldenBackoff {
    /// Initial backoff duration
    base_ms: u64,
    /// Maximum backoff duration
    max_ms: u64,
    /// Current attempt number
    attempt: u32,
    /// Golden ratio constant
    phi: f64,
    /// Previous backoff duration
    prev_backoff_ms: f64,
    /// Current backoff duration
    current_backoff_ms: f64,
}

impl GoldenBackoff {
    pub fn new(base_ms: u64, max_ms: u64) -> Self {
        Self {
            base_ms,
            max_ms,
            attempt: 0,
            phi: GOLDEN_RATIO, // φ ≈ 1.618
            prev_backoff_ms: base_ms as f64,
            current_backoff_ms: (base_ms as f64 * GOLDEN_RATIO).min(max_ms as f64),
        }
    }
    
    /// Calculates the next backoff duration using golden ratio progression
    /// 
    /// Each interval is φ times the previous, providing optimal spacing
    /// that minimizes collision probability while ensuring quick recovery.
    pub fn next_backoff(&mut self) -> Duration {
        self.attempt += 1;
        
        // Golden ratio progression: each term is φ times the previous
        // Using Fibonacci-like progression: next = prev * φ
        let next_backoff = self.prev_backoff_ms * self.phi;
        
        // Add jitter using π for randomization
        let jitter = (PI * self.attempt as f64).sin() * 0.1;
        let jittered_backoff = next_backoff * (1.0 + jitter);
        
        // Update state
        self.prev_backoff_ms = self.current_backoff_ms;
        self.current_backoff_ms = jittered_backoff.min(self.max_ms as f64);
        
        Duration::from_millis(self.current_backoff_ms as u64)
    }
    
    /// Gets the theoretical optimal retry time for nth attempt
    /// 
    /// Uses the formula: t_n = t_0 * φ^n
    pub fn theoretical_backoff_ms(&self, n: u32) -> u64 {
        let n = n.max(1);
        let backoff = self.base_ms as f64 * self.phi.powi(n as i32);
        backoff.min(self.max_ms as f64) as u64
    }
    
    /// Resets the backoff to initial state
    pub fn reset(&mut self) {
        self.attempt = 0;
        self.prev_backoff_ms = self.base_ms as f64;
        self.current_backoff_ms = (self.base_ms as f64 * self.phi).min(self.max_ms as f64);
    }
    
    /// Gets current attempt number
    pub fn attempt(&self) -> u32 {
        self.attempt
    }
}

/// Alternative exponential backoff for comparison
pub struct ExponentialBackoff {
    base_ms: u64,
    max_ms: u64,
    attempt: u32,
    multiplier: f64,
}

impl ExponentialBackoff {
    pub fn new(base_ms: u64, max_ms: u64) -> Self {
        Self {
            base_ms,
            max_ms,
            attempt: 0,
            multiplier: 2.0,
        }
    }
    
    pub fn next_backoff(&mut self) -> Duration {
        self.attempt += 1;
        let backoff = self.base_ms as f64 * self.multiplier.powi(self.attempt as i32 - 1);
        Duration::from_millis(backoff.min(self.max_ms as f64) as u64)
    }
}

/// ============================================
/// Fibonacci Batch Sizing
/// ============================================

/// Fibonacci-based batch size calculator for flow control
/// 
/// Uses Fibonacci sequence (closely related to golden ratio) for
/// adaptive batch sizing that grows exponentially but conservatively.
pub struct FibonacciBatchSizer {
    /// Minimum batch size
    min_size: usize,
    /// Maximum batch size
    max_size: usize,
    /// Current Fibonacci index
    fib_index: usize,
    /// Last batch size (F_n)
    f_n: usize,
    /// Previous batch size (F_{n-1})
    f_n_minus_1: usize,
    /// Success rate for adaptation
    success_rate: f64,
}

impl FibonacciBatchSizer {
    pub fn new(min_size: usize, max_size: usize) -> Self {
        Self {
            min_size,
            max_size,
            fib_index: 2,
            f_n: min_size.max(1),
            f_n_minus_1: 1,
            success_rate: 1.0,
        }
    }
    
    /// Gets the next recommended batch size
    /// 
    /// Uses Fibonacci progression: F_n = F_{n-1} + F_{n-2}
    /// As n grows large, F_{n+1}/F_n approaches φ (GOLDEN_RATIO)
    pub fn next_batch_size(&mut self) -> usize {
        // Calculate next Fibonacci number
        let next_size = self.f_n + self.f_n_minus_1;
        
        // Update state
        self.f_n_minus_1 = self.f_n;
        self.f_n = next_size.min(self.max_size);
        self.fib_index += 1;
        
        self.f_n.max(self.min_size)
    }
    
    /// Adjusts batch size based on success rate
    /// 
    /// Uses natural logarithm and EULER_GAMMA for smooth adaptation
    pub fn adapt(&mut self, success: bool, latency_ms: f64) {
        if success {
            // Gradually increase success rate using E for natural saturation
            self.success_rate = (self.success_rate + 0.1).min(1.0);
        } else {
            // Decrease more aggressively on failure
            self.success_rate *= 0.8;
            
            // Reset to smaller batch size
            self.reset_to_smaller();
        }
        
        // Adjust based on latency using EULER_GAMMA
        if latency_ms > 1000.0 {
            let reduction_factor = (EULER_GAMMA * 1000.0 / latency_ms).max(0.5);
            let new_size = (self.f_n as f64 * reduction_factor) as usize;
            self.f_n = new_size.max(self.min_size);
        }
    }
    
    /// Resets to a smaller batch size (half of current)
    fn reset_to_smaller(&mut self) {
        self.fib_index = 2;
        self.f_n = self.min_size;
        self.f_n_minus_1 = 1;
    }
    
    /// Gets the golden ratio approximation from current Fibonacci ratio
    /// 
    /// As indices increase, F_n / F_{n-1} approaches φ
    pub fn current_phi_approximation(&self) -> f64 {
        if self.f_n_minus_1 > 0 {
            self.f_n as f64 / self.f_n_minus_1 as f64
        } else {
            1.0
        }
    }
    
    /// Gets current statistics
    pub fn stats(&self) -> BatchStats {
        BatchStats {
            current_size: self.f_n,
            fib_index: self.fib_index,
            success_rate: self.success_rate,
            phi_approximation: self.current_phi_approximation(),
        }
    }
}

#[derive(Debug)]
pub struct BatchStats {
    pub current_size: usize,
    pub fib_index: usize,
    pub success_rate: f64,
    pub phi_approximation: f64,
}

/// ============================================
/// PI and TAU - Periodic Metrics
/// ============================================

/// Periodic metric calculator using PI and TAU
/// 
/// TAU (τ = 2π) is the full circle constant, often more natural than PI
/// for periodic calculations.
pub struct PeriodicMetricCalculator {
    /// Base period in seconds
    period_sec: f64,
    /// Phase offset
    phase: f64,
}

impl PeriodicMetricCalculator {
    pub fn new(period_sec: f64, phase: f64) -> Self {
        Self { period_sec, phase }
    }
    
    /// Calculates a sinusoidal value at given time
    /// 
    /// Uses TAU for full-period calculations: sin(τ * t / period + phase)
    pub fn calculate(&self, time_sec: f64) -> f64 {
        (TAU * time_sec / self.period_sec + self.phase).sin()
    }
    
    /// Calculates a cosine value at given time
    pub fn calculate_cosine(&self, time_sec: f64) -> f64 {
        (TAU * time_sec / self.period_sec + self.phase).cos()
    }
    
    /// Generates daily load pattern (24-hour cycle)
    /// 
    /// Returns value between 0.0 and 1.0 representing expected load
    pub fn daily_load_pattern(hour_of_day: f64) -> f64 {
        // Peak at noon (12:00), low at midnight
        // Using PI: sin(π * hour / 12 - π/2) + 1) / 2
        let normalized = ((PI * hour_of_day / 12.0 - PI / 2.0).sin() + 1.0) / 2.0;
        // Add some randomness using E
        normalized * 0.8 + 0.2
    }
    
    /// Generates weekly pattern (7-day cycle)
    pub fn weekly_load_pattern(day_of_week: u8) -> f64 {
        // Weekday vs weekend pattern
        match day_of_week {
            0 | 6 => 0.6, // Weekend
            _ => 1.0,     // Weekday
        }
    }
    
    /// Calculates circular buffer index using TAU
    /// 
    /// Efficiently wraps around using the full circle constant
    pub fn circular_index(&self, position: usize, buffer_size: usize) -> usize {
        let normalized_pos = (position as f64 * TAU) % (buffer_size as f64 * TAU);
        (normalized_pos / TAU) as usize % buffer_size
    }
}

/// ============================================
/// Logarithmic Constants - Compression
/// ============================================

/// Logarithmic compression for metric values
/// 
/// Uses LN_2 and LN_10 for efficient value compression and encoding.
pub struct LogarithmicCompressor {
    /// Base for logarithm (2 or 10)
    #[allow(dead_code)]
    log_base: f64,
    /// Precision for encoding
    precision: f64,
}

impl LogarithmicCompressor {
    pub fn new_binary() -> Self {
        Self {
            log_base: 2.0,
            precision: LN_2, // ln(2) for binary logarithms
        }
    }
    
    pub fn new_decimal() -> Self {
        Self {
            log_base: 10.0,
            precision: LN_10, // ln(10) for decimal logarithms
        }
    }
    
    /// Compresses a value using logarithmic encoding
    /// 
    /// Useful for metrics with wide dynamic ranges
    pub fn compress(&self, value: f64) -> u32 {
        if value <= 0.0 {
            return 0;
        }
        
        // log_b(x) = ln(x) / ln(b)
        let log_value = value.ln() / self.precision;
        (log_value * self.precision * 100.0) as u32
    }
    
    /// Decompresses a value
    pub fn decompress(&self, encoded: u32) -> f64 {
        let log_value = encoded as f64 / (self.precision * 100.0);
        // x = b^y = e^(y * ln(b))
        (log_value * self.precision).exp()
    }
    
    /// Calculates information content using LOG2_E
    /// 
    /// LOG2_E = 1/ln(2), used for converting between natural log and log2
    pub fn information_content(&self, probability: f64) -> f64 {
        if probability <= 0.0 || probability > 1.0 {
            return 0.0;
        }
        // Information in bits: -log2(p) = -ln(p) * log2(e)
        (-probability.ln()) * LOG2_E
    }
    
    /// Calculates entropy using LOG10_E
    /// 
    /// LOG10_E = 1/ln(10), used for converting between natural log and log10
    pub fn entropy_bels(&self, probabilities: &[f64]) -> f64 {
        probabilities.iter()
            .filter(|&&p| p > 0.0)
            .map(|&p| -p * p.ln() * LOG10_E)
            .sum()
    }
}

/// ============================================
/// SQRT_2 - Load Balancing
/// ============================================

/// SQRT_2-based load distribution
/// 
/// SQRT_2 (≈ 1.414) appears in various geometric calculations
/// and can be used for asymmetrical load distribution.
pub struct Sqrt2LoadBalancer {
    /// Total capacity
    capacity: f64,
    /// Primary allocation ratio (sqrt(2) - 1 ≈ 0.414)
    primary_ratio: f64,
    /// Secondary allocation ratio (2 - sqrt(2) ≈ 0.586)
    secondary_ratio: f64,
}

impl Sqrt2LoadBalancer {
    pub fn new(capacity: f64) -> Self {
        // sqrt(2) - 1 is the silver ratio conjugate
        let primary = SQRT_2 - 1.0;  // ≈ 0.414
        let secondary = 2.0 - SQRT_2; // ≈ 0.586
        
        Self {
            capacity,
            primary_ratio: primary,
            secondary_ratio: secondary,
        }
    }
    
    /// Distributes load between primary and secondary nodes
    /// 
    /// Returns (primary_load, secondary_load)
    pub fn distribute(&self, total_load: f64) -> (f64, f64) {
        let primary = total_load * self.primary_ratio;
        let secondary = total_load * self.secondary_ratio;
        (primary.min(self.capacity), secondary.min(self.capacity))
    }
    
    /// Calculates optimal partition sizes using silver ratio
    /// 
    /// The silver ratio (1 + sqrt(2)) appears in A4 paper proportions
    pub fn partition_sizes(&self, n: usize) -> Vec<f64> {
        let silver_ratio = 1.0 + SQRT_2; // ≈ 2.414
        (0..n)
            .map(|i| self.capacity / silver_ratio.powi(i as i32))
            .collect()
    }
}

/// ============================================
/// Combined Math Constants Demo
/// ============================================

/// Demonstrates the relationship between constants
pub fn demonstrate_constant_relationships() {
    println!("\n📐 Mathematical Constant Relationships:");
    println!("  EULER_GAMMA (γ)      = {:.10}", EULER_GAMMA);
    println!("  GOLDEN_RATIO (φ)     = {:.10}", GOLDEN_RATIO);
    println!("  PI (π)               = {:.10}", PI);
    println!("  TAU (τ)              = {:.10}", TAU);
    println!("  E (e)                = {:.10}", E);
    println!("  SQRT_2               = {:.10}", SQRT_2);
    println!("  LN_2                 = {:.10}", LN_2);
    println!("  LN_10                = {:.10}", LN_10);
    
    println!("\n  Interesting relationships:");
    println!("  φ = (1 + sqrt(5)) / 2     = {:.10}", (1.0 + 5.0f64.sqrt()) / 2.0);
    println!("  φ ≈ F_{} / F_{}           = {:.10}", 20, 19, 6765.0 / 4181.0);
    println!("  e^γ ≈ {:.6}", E.powf(EULER_GAMMA));
    println!("  τ = 2π                    = {:.10}", 2.0 * PI);
    println!("  1/φ = φ - 1               = {:.10}", 1.0 / GOLDEN_RATIO);
}

/// ============================================
/// Main Demo
/// ============================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║    Rust 1.94 Math Constants Demo - OTLP Algorithms       ║");
    println!("║       Adaptive Sampling · Retry Backoff · Batching       ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    
    // Display constant relationships
    demonstrate_constant_relationships();
    
    // Section 1: Adaptive Sampling with EULER_GAMMA
    println!("\n📊 Section 1: Adaptive Sampling (EULER_GAMMA)");
    println!("   Using γ ≈ {:.6} for harmonic series calculations", EULER_GAMMA);
    
    let mut sampler = AdaptiveSampler::new(0.1, 0.05);
    
    // Simulate sampling decisions
    println!("\n   Simulating 200 sampling decisions:");
    for i in 0..200 {
        // Vary importance (0.0 to 1.0)
        let importance = (i as f64 / 100.0).sin().abs();
        let should_sample = sampler.should_sample(importance);
        
        if should_sample && i % 20 == 0 {
            print!("   [Sampled at index {}] ", i);
        }
    }
    println!();
    
    let stats = sampler.stats();
    println!("   📈 Sampling statistics:");
    println!("      - Total items: {}", stats.total_count);
    println!("      - Samples taken: {}", stats.sampled_count);
    println!("      - Actual rate: {:.2}%", stats.actual_rate * 100.0);
    println!("      - Current rate: {:.2}%", stats.current_rate * 100.0);
    println!("      - EULER_GAMMA used: {:.6}", stats.effective_gamma);
    
    // Section 2: Golden Ratio Backoff
    println!("\n🔄 Section 2: Golden Ratio Retry Backoff");
    println!("   Using φ ≈ {:.6} for optimal retry spacing", GOLDEN_RATIO);
    
    let mut golden_backoff = GoldenBackoff::new(100, 5000);
    let mut exp_backoff = ExponentialBackoff::new(100, 5000);
    
    println!("\n   Retry attempt comparison:");
    println!("   {:<10} {:<20} {:<20}", "Attempt", "Golden Ratio (ms)", "Exponential (ms)");
    println!("   {}", "-".repeat(55));
    
    for i in 1..=8 {
        let golden_ms = golden_backoff.next_backoff().as_millis();
        let exp_ms = exp_backoff.next_backoff().as_millis();
        let theoretical = golden_backoff.theoretical_backoff_ms(i);
        
        println!("   {:<10} {:<20} {:<20} (theoretical: {}ms)",
            i, golden_ms, exp_ms, theoretical);
    }
    
    println!("\n   Golden ratio progression: each interval ≈ φ × previous");
    println!("   This provides optimal spacing to minimize collision probability");
    
    // Section 3: Fibonacci Batch Sizing
    println!("\n📦 Section 3: Fibonacci Batch Sizing");
    println!("   Fibonacci ratio approaches φ as n increases");
    
    let mut batch_sizer = FibonacciBatchSizer::new(8, 1024);
    
    println!("\n   Fibonacci batch progression:");
    println!("   {:<10} {:<15} {:<20}", "Index", "Batch Size", "F_n / F_{n-1}");
    println!("   {}", "-".repeat(50));
    
    for i in 1..=12 {
        let size = batch_sizer.next_batch_size();
        let stats = batch_sizer.stats();
        
        if i >= 3 {
            println!("   {:<10} {:<15} {:<20.6}",
                stats.fib_index, size, stats.phi_approximation);
        } else {
            println!("   {:<10} {:<15} {:<20}",
                stats.fib_index, size, "N/A");
        }
        
        // Simulate success/failure
        if i % 5 == 0 {
            batch_sizer.adapt(false, 2000.0); // Simulate failure
            println!("   ⚠️  Failure detected - resetting batch size");
        } else {
            batch_sizer.adapt(true, 100.0); // Simulate success
        }
    }
    
    println!("\n   Note: F_n / F_{{n-1}} approaches φ = {:.6}", GOLDEN_RATIO);
    
    // Section 4: Periodic Metrics
    println!("\n📅 Section 4: Periodic Metrics (PI & TAU)");
    println!("   Using τ = 2π = {:.6} for full-circle calculations", TAU);
    
    let calculator = PeriodicMetricCalculator::new(60.0, 0.0); // 60-second period
    
    println!("\n   Daily load pattern (24-hour cycle):");
    println!("   {:<10} {:<20} {:<20}", "Hour", "Expected Load", "Visualization");
    println!("   {}", "-".repeat(60));
    
    for hour in [0, 4, 8, 12, 16, 20] {
        let load = PeriodicMetricCalculator::daily_load_pattern(hour as f64);
        let bar_len = (load * 20.0) as usize;
        let bar = "█".repeat(bar_len);
        println!("   {:<10} {:<20.2} {}", hour, load, bar);
    }
    
    println!("\n   Sinusoidal metric at various times (60s period):");
    for t in [0, 15, 30, 45, 60] {
        let value = calculator.calculate(t as f64);
        println!("   t={}s: {:.4}", t, value);
    }
    
    // Section 5: Logarithmic Compression
    println!("\n🗜️  Section 5: Logarithmic Compression (LN_2, LN_10)");
    println!("   Using ln(2) = {:.6}, ln(10) = {:.6}", LN_2, LN_10);
    
    let binary_compressor = LogarithmicCompressor::new_binary();
    let decimal_compressor = LogarithmicCompressor::new_decimal();
    
    let test_values = [1.0, 10.0, 100.0, 1000.0, 10000.0];
    
    println!("\n   Value compression comparison:");
    println!("   {:<15} {:<20} {:<20}", "Original", "Binary Encoded", "Decimal Encoded");
    println!("   {}", "-".repeat(60));
    
    for &value in &test_values {
        let bin_enc = binary_compressor.compress(value);
        let dec_enc = decimal_compressor.compress(value);
        println!("   {:<15} {:<20} {:<20}", value, bin_enc, dec_enc);
    }
    
    // Section 6: SQRT_2 Load Balancing
    println!("\n⚖️  Section 6: Load Balancing (SQRT_2)");
    println!("   Using sqrt(2) = {:.6}", SQRT_2);
    
    let balancer = Sqrt2LoadBalancer::new(1000.0);
    
    println!("\n   Load distribution:");
    println!("   Primary ratio (sqrt(2)-1):   {:.6}", balancer.primary_ratio);
    println!("   Secondary ratio (2-sqrt(2)): {:.6}", balancer.secondary_ratio);
    
    let test_loads = [500.0, 800.0, 1200.0];
    
    println!("\n   {:<15} {:<20} {:<20}", "Total Load", "Primary", "Secondary");
    println!("   {}", "-".repeat(60));
    
    for &load in &test_loads {
        let (primary, secondary) = balancer.distribute(load);
        println!("   {:<15} {:<20.1} {:<20.1}", load, primary, secondary);
    }
    
    // Summary
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║                       Summary                            ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    println!("  Math constants provide:");
    println!("  - Optimal backoff spacing (GOLDEN_RATIO)");
    println!("  - Adaptive sampling (EULER_GAMMA)");
    println!("  - Fibonacci flow control (converges to φ)");
    println!("  - Periodic calculations (PI, TAU)");
    println!("  - Efficient compression (LN_2, LN_10)");
    println!("  - Asymmetric balancing (SQRT_2)");
    
    println!("\n✅ Math constants demo completed successfully!");
    println!("   Rust 1.94 provides these constants in std::f64::consts");
    println!("   for zero-cost mathematical computations.");
    
    Ok(())
}

/// Unit tests
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_adaptive_sampler() {
        let mut sampler = AdaptiveSampler::new(0.5, 0.1);
        
        // Sample with varying importance
        for i in 0..100 {
            let importance = (i as f64 / 50.0).sin().abs();
            sampler.should_sample(importance);
        }
        
        let stats = sampler.stats();
        assert_eq!(stats.total_count, 100);
        assert!(stats.sampled_count > 0);
        assert!((stats.effective_gamma - EULER_GAMMA).abs() < 0.001);
    }
    
    #[test]
    fn test_golden_backoff() {
        let mut backoff = GoldenBackoff::new(100, 10000);
        
        let first = backoff.next_backoff();
        let second = backoff.next_backoff();
        
        // Second should be approximately φ times first
        let ratio = second.as_millis() as f64 / first.as_millis() as f64;
        assert!(ratio > 1.5 && ratio < 1.7); // Approximate φ
    }
    
    #[test]
    fn test_fibonacci_batch_sizer() {
        let mut sizer = FibonacciBatchSizer::new(1, 1000);
        
        let sizes: Vec<_> = (0..10).map(|_| sizer.next_batch_size()).collect();
        
        // Fibonacci property: F_n = F_{n-1} + F_{n-2}
        for i in 2..sizes.len() {
            if sizes[i-1] + sizes[i-2] <= 1000 {
                assert_eq!(sizes[i], sizes[i-1] + sizes[i-2]);
            }
        }
    }
    
    #[test]
    fn test_periodic_calculator() {
        let calc = PeriodicMetricCalculator::new(60.0, 0.0);
        
        // Periodicity: f(t) = f(t + period)
        let t1 = calc.calculate(0.0);
        let t2 = calc.calculate(60.0);
        assert!((t1 - t2).abs() < 0.001);
        
        // Quarter period should give sin(π/2) = 1
        let quarter = calc.calculate(15.0);
        assert!((quarter - 1.0).abs() < 0.001);
    }
    
    #[test]
    fn test_logarithmic_compressor() {
        let compressor = LogarithmicCompressor::new_decimal();
        
        let original = 100.0;
        let encoded = compressor.compress(original);
        let decoded = compressor.decompress(encoded);
        
        // Should be approximately equal
        assert!((decoded - original).abs() / original < 0.1);
    }
    
    #[test]
    fn test_constant_values() {
        // Verify constant relationships
        assert!((TAU - 2.0 * PI).abs() < 0.0001);
        assert!((LOG2_E - 1.0 / LN_2).abs() < 0.0001);
        assert!((LOG10_E - 1.0 / LN_10).abs() < 0.0001);
        assert!((GOLDEN_RATIO * GOLDEN_RATIO - GOLDEN_RATIO - 1.0).abs() < 0.0001);
    }
}
