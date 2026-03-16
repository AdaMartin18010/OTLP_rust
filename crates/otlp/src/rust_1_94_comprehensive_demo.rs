//! # Rust 1.94 Comprehensive Demo for OTLP
//!
//! This module demonstrates all Rust 1.94 features working together in a cohesive OTLP context.
//!
//! ## Features Demonstrated
//!
//! 1. **`array_windows`** - Pattern detection in telemetry data
//! 2. **`element_offset`** - Zero-copy buffer management
//! 3. **`LazyLock/LazyCell`** - Global configuration and caching
//! 4. **`EULER_GAMMA`** - Adaptive sampling algorithms
//! 5. **`GOLDEN_RATIO`** - Backoff strategies and batch sizing
//! 6. **`const mul_add`** - Compile-time optimizations
//! 7. **SIMD FP16** - High-performance metrics processing (when available)
//! 8. **TOML 1.1** - Configuration parsing with multi-line inline tables
//!
//! ## Architecture Overview
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    OTLP Pipeline with Rust 1.94                      │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐             │
//! │  │   LazyLock   │   │   Sampling   │   │   Retry/     │             │
//! │  │   Config     │──▶│   (EULER_    │──▶│   Backoff    │             │
//! │  │              │   │   GAMMA)     │   │   (GOLDEN_    │             │
//! │  │              │   │              │   │   RATIO)     │             │
//! │  └──────────────┘   └──────────────┘   └──────────────┘             │
//! │         │                  │                  │                     │
//! │         ▼                  ▼                  ▼                     │
//! │  ┌──────────────────────────────────────────────────────┐          │
//! │  │              Data Processing Pipeline                 │          │
//! │  │  ┌──────────────┐  ┌──────────────┐  ┌───────────┐   │          │
//! │  │  │ array_windows│  │element_offset│  │ FP16 SIMD │   │          │
//! │  │  │ Pattern Det. │  │ Zero-copy    │  │ (opt)     │   │          │
//! │  │  └──────────────┘  └──────────────┘  └───────────┘   │          │
//! │  └──────────────────────────────────────────────────────┘          │
//! │                              │                                      │
//! │                              ▼                                      │
//! │  ┌──────────────────────────────────────────────────────┐          │
//! │  │                 Export & Monitoring                   │          │
//! │  │         (TOML 1.1 Config + Performance Stats)         │          │
//! │  └──────────────────────────────────────────────────────┘          │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

#![allow(dead_code)]

use std::cell::LazyCell;
use std::collections::HashMap;
use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};
use std::sync::{LazyLock, RwLock};

// ============================================================================
// Section 1: Global Configuration using LazyLock
// ============================================================================

/// OTLP Service Configuration with TOML 1.1 multi-line inline table support
/// 
/// Example TOML 1.1 configuration:
/// ```toml
/// [service]
/// name = "otlp-processor"
/// version = "1.0.0"
/// attributes = { region = "us-west", 
///                env = "production",
///                team = "platform" }
/// ```
#[derive(Debug, Clone)]
pub struct ServiceConfig {
    pub name: String,
    pub version: String,
    pub endpoint: String,
    pub batch_size: usize,
    pub timeout_ms: u64,
    pub attributes: HashMap<String, String>,
    pub compression: CompressionType,
    pub retry_policy: RetryPolicy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionType {
    None,
    Gzip,
    Zstd,
}

#[derive(Debug, Clone, Copy)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub base_delay_ms: u64,
    pub max_delay_ms: u64,
}

impl Default for ServiceConfig {
    fn default() -> Self {
        Self {
            name: "otlp-service".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
            endpoint: "http://localhost:4317".to_string(),
            batch_size: 512,
            timeout_ms: 30000,
            attributes: HashMap::new(),
            compression: CompressionType::Gzip,
            retry_policy: RetryPolicy {
                max_retries: 3,
                base_delay_ms: 100,
                max_delay_ms: 30000,
            },
        }
    }
}

/// Global configuration - LazyLock for thread-safe lazy initialization
/// 
/// # Rust 1.94 Feature: LazyLock
/// LazyLock provides thread-safe lazy initialization with zero-cost abstraction
pub static GLOBAL_CONFIG: LazyLock<RwLock<ServiceConfig>> = 
    LazyLock::new(|| RwLock::new(ServiceConfig::default()));

/// Metrics cache - LazyLock for efficient metrics storage
pub static METRICS_CACHE: LazyLock<RwLock<HashMap<String, Vec<MetricPoint>>>> = 
    LazyLock::new(|| RwLock::new(HashMap::new()));

/// Configuration manager with Rust 1.94 LazyLock methods
pub struct ConfigManager;

impl ConfigManager {
    /// Get configuration without triggering initialization
    /// 
    /// # Rust 1.94 Feature: LazyLock::get
    /// Returns Option<&T> without initializing if not already initialized
    pub fn try_get() -> Option<std::sync::RwLockReadGuard<'static, ServiceConfig>> {
        LazyLock::get(&GLOBAL_CONFIG).map(|cfg| cfg.read().unwrap())
    }
    
    /// Check if configuration is initialized
    /// 
    /// # Rust 1.94 Feature: LazyLock::get
    pub fn is_initialized() -> bool {
        LazyLock::get(&GLOBAL_CONFIG).is_some()
    }
    
    /// Force initialization and get configuration
    /// 
    /// # Rust 1.94 Feature: LazyLock::force
    pub fn get() -> std::sync::RwLockReadGuard<'static, ServiceConfig> {
        LazyLock::force(&GLOBAL_CONFIG).read().unwrap()
    }
    
    /// Update configuration
    pub fn update<F>(f: F) 
    where
        F: FnOnce(&mut ServiceConfig),
    {
        let mut cfg = LazyLock::force(&GLOBAL_CONFIG).write().unwrap();
        f(&mut cfg);
    }
}

// Thread-local buffer using LazyCell
/// 
/// # Rust 1.94 Feature: LazyCell
/// Single-threaded lazy initialization for performance-critical paths
pub struct ThreadLocalBuffer {
    buffer: LazyCell<Vec<u8>>,
}

impl Default for ThreadLocalBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl ThreadLocalBuffer {
    pub const fn new() -> Self {
        Self {
            buffer: LazyCell::new(Vec::new),
        }
    }
    
    /// Get buffer without triggering initialization
    /// 
    /// # Rust 1.94 Feature: LazyCell::get
    pub fn try_get(&self) -> Option<&Vec<u8>> {
        LazyCell::get(&self.buffer)
    }
    
    /// Force initialization and get mutable reference
    /// 
    /// # Rust 1.94 Feature: LazyCell::force_mut
    pub fn force_mut(&mut self) -> &mut Vec<u8> {
        LazyCell::force_mut(&mut self.buffer)
    }
    
    pub fn write(&mut self, data: &[u8]) {
        self.force_mut().extend_from_slice(data);
    }
}

// ============================================================================
// Section 2: Telemetry Data Processing using array_windows
// ============================================================================

/// Metric data point for time-series analysis
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetricPoint {
    pub timestamp: u64,
    pub value: f64,
}

/// Pattern types detectable in telemetry data
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TelemetryPattern {
    /// Increasing trend (values consistently rising)
    Increasing,
    /// Decreasing trend (values consistently falling)
    Decreasing,
    /// Stable pattern (values relatively constant)
    Stable,
    /// Oscillating pattern (ABAB or ABBA patterns)
    Oscillating,
    /// Spike detected (sudden increase followed by decrease)
    Spike,
    /// Dip detected (sudden decrease followed by increase)
    Dip,
}

/// Detect patterns in metric values using array_windows
/// 
/// # Rust 1.94 Feature: array_windows
/// Returns fixed-size arrays [T; N] instead of slices for better optimization
/// 
/// # Example
/// ```
/// use otlp::rust_1_94_comprehensive_demo::{detect_metric_patterns, MetricPoint};
/// 
/// let metrics = vec![
///     MetricPoint { timestamp: 1, value: 1.0 },
///     MetricPoint { timestamp: 2, value: 2.0 },
///     MetricPoint { timestamp: 3, value: 3.0 },
///     MetricPoint { timestamp: 4, value: 4.0 },
/// ];
/// let patterns = detect_metric_patterns(&metrics);
/// ```
pub fn detect_metric_patterns(metrics: &[MetricPoint]) -> Vec<TelemetryPattern> {
    if metrics.len() < 3 {
        return Vec::new();
    }
    
    metrics
        .array_windows::<3>()
        .map(|[a, b, c]| {
            let diff1 = b.value - a.value;
            let diff2 = c.value - b.value;
            
            // Detect spikes (up then down)
            if diff1 > 0.0 && diff2 < 0.0 && diff1.abs() > 1.0 {
                return TelemetryPattern::Spike;
            }
            
            // Detect dips (down then up)
            if diff1 < 0.0 && diff2 > 0.0 && diff1.abs() > 1.0 {
                return TelemetryPattern::Dip;
            }
            
            // Detect trends
            if diff1 > 0.01 && diff2 > 0.01 {
                TelemetryPattern::Increasing
            } else if diff1 < -0.01 && diff2 < -0.01 {
                TelemetryPattern::Decreasing
            } else if diff1.abs() < 0.01 && diff2.abs() < 0.01 {
                TelemetryPattern::Stable
            } else {
                TelemetryPattern::Oscillating
            }
        })
        .collect()
}

/// Detect ABBA patterns (potential anomalies) in byte sequences
/// 
/// # Rust 1.94 Feature: array_windows
/// Efficiently detects palindrome-like patterns that may indicate issues
pub fn detect_abba_anomalies(data: &[u8]) -> Vec<usize> {
    if data.len() < 4 {
        return Vec::new();
    }
    
    data.array_windows::<4>()
        .enumerate()
        .filter_map(|(idx, [a, b, c, d])| {
            // ABBA pattern: a != b, b == c, a == d
            if *a != *b && *b == *c && *a == *d {
                Some(idx)
            } else {
                None
            }
        })
        .collect()
}

/// Validate span sequence continuity
/// 
/// # Rust 1.94 Feature: array_windows
/// Ensures span timestamps are monotonically increasing
#[derive(Debug, Clone)]
pub struct Span {
    pub id: [u8; 8],
    pub trace_id: [u8; 16],
    pub name: String,
    pub start_time: u64,
    pub end_time: u64,
    pub status: SpanStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanStatus {
    Ok,
    Error,
    Unset,
}

pub fn validate_span_continuity(spans: &[Span]) -> bool {
    if spans.len() < 2 {
        return true;
    }
    
    spans.array_windows::<2>().all(|[prev, curr]| {
        // Each span should start after or when the previous starts
        curr.start_time >= prev.start_time &&
        // End times should be valid
        curr.end_time >= curr.start_time
    })
}

/// Calculate moving average using array_windows
/// 
/// # Rust 1.94 Feature: array_windows
/// Optimized moving average calculation with const generics
pub fn moving_average<const N: usize>(values: &[f64]) -> Vec<f64> {
    if values.len() < N {
        return Vec::new();
    }
    
    match N {
        2 => values.array_windows::<2>().map(|[a, b]| (a + b) / 2.0).collect(),
        3 => values.array_windows::<3>().map(|[a, b, c]| (a + b + c) / 3.0).collect(),
        4 => values.array_windows::<4>().map(|[a, b, c, d]| (a + b + c + d) / 4.0).collect(),
        5 => values.array_windows::<5>().map(|[a, b, c, d, e]| (a + b + c + d + e) / 5.0).collect(),
        _ => values.windows(N).map(|w| w.iter().sum::<f64>() / N as f64).collect(),
    }
}

// ============================================================================
// Section 3: Zero-copy Operations using element_offset
// ============================================================================

/// Zero-copy span serializer
/// 
/// # Rust 1.94 Feature: element_offset
/// Calculates offsets without copying data for efficient serialization
pub struct ZeroCopySpanSerializer<'a> {
    spans: &'a [Span],
}

impl<'a> ZeroCopySpanSerializer<'a> {
    pub fn new(spans: &'a [Span]) -> Self {
        Self { spans }
    }
    
    /// Get the index of a span without searching
    /// 
    /// # Rust 1.94 Feature: element_offset
    /// Returns the offset of an element within the slice in O(1)
    pub fn get_span_index(&self, span: &Span) -> Option<usize> {
        self.spans.element_offset(span)
    }
    
    /// Check if a span reference is from this collection
    pub fn contains(&self, span: &Span) -> bool {
        self.spans.element_offset(span).is_some()
    }
    
    /// Get span range by references
    pub fn get_range(&self, start: &Span, end: &Span) -> Option<&'a [Span]> {
        let start_idx = self.spans.element_offset(start)?;
        let end_idx = self.spans.element_offset(end)?;
        if start_idx <= end_idx {
            Some(&self.spans[start_idx..=end_idx])
        } else {
            None
        }
    }
}

/// Memory-efficient metrics buffer
/// 
/// # Rust 1.94 Feature: element_offset
/// Enables zero-copy slicing and offset tracking
pub struct MetricsBuffer {
    data: Vec<MetricPoint>,
}

impl MetricsBuffer {
    pub fn new(data: Vec<MetricPoint>) -> Self {
        Self { data }
    }
    
    pub fn get(&self, idx: usize) -> Option<&MetricPoint> {
        self.data.get(idx)
    }
    
    /// Get index of a metric point
    /// 
    /// # Rust 1.94 Feature: element_offset
    pub fn index_of(&self, point: &MetricPoint) -> Option<usize> {
        self.data.element_offset(point)
    }
    
    /// Create zero-copy sub-buffer
    pub fn sub_buffer(&self, start: &MetricPoint, end: &MetricPoint) -> Option<&[MetricPoint]> {
        let start_idx = self.data.element_offset(start)?;
        let end_idx = self.data.element_offset(end)?;
        if start_idx <= end_idx {
            Some(&self.data[start_idx..=end_idx])
        } else {
            None
        }
    }
}

// ============================================================================
// Section 4: Adaptive Sampling using EULER_GAMMA
// ============================================================================

/// Adaptive sampling calculator using Euler-Mascheroni constant
/// 
/// # Rust 1.94 Feature: EULER_GAMMA
/// The Euler-Mascheroni constant (γ ≈ 0.5772) provides natural damping
/// for sampling rate calculations
pub struct AdaptiveSampler;

impl AdaptiveSampler {
    /// Pre-computed constants using const mul_add
    /// 
    /// # Rust 1.94 Feature: const mul_add
    /// Compile-time computation with higher precision
    pub const EULER_GAMMA_SQUARED: f64 = EULER_GAMMA.mul_add(EULER_GAMMA, 0.0);
    pub const ONE_PLUS_GAMMA: f64 = 1.0_f64.mul_add(EULER_GAMMA, 1.0);
    
    /// Calculate adaptive sampling rate based on system load
    /// 
    /// Uses EULER_GAMMA as a damping factor to prevent oscillation
    pub fn calculate_rate(load: f64, base_rate: f64) -> f64 {
        if load <= 0.0 || base_rate <= 0.0 {
            return 0.001;
        }
        
        // Normalize load (assuming max load of 10000)
        let normalized_load = ((load + 1.0).ln() / 9.21_f64.ln()).clamp(0.0, 1.0);
        
        // Apply EULER_GAMMA as damping: rate = base * (1 + γ * normalized_load)
        let adjusted = base_rate.mul_add(EULER_GAMMA * normalized_load, base_rate);
        
        adjusted.clamp(0.001, 1.0)
    }
    
    /// Priority-based sampling using harmonic series properties
    /// 
    /// The harmonic series H_n ≈ ln(n) + γ is used for fair sampling
    pub fn priority_weight(priority: u8, base_weight: f64) -> f64 {
        let p = priority.clamp(1, 10) as f64;
        // weight = base * (1 + γ * log10(priority))
        base_weight.mul_add(EULER_GAMMA * p.log10(), base_weight)
    }
    
    /// Should sample decision using cumulative harmonic approximation
    pub fn should_sample(sequence: u64, target_rate: f64) -> bool {
        if target_rate >= 1.0 {
            return true;
        }
        if target_rate <= 0.0 {
            return false;
        }
        
        let n = sequence as f64;
        // H_n ≈ ln(n) + γ
        let harmonic = n.ln() + EULER_GAMMA;
        let interval = 1.0 / target_rate;
        let remainder = harmonic % interval;
        
        remainder < 1.0 || remainder > interval - 1.0
    }
}

// ============================================================================
// Section 5: Retry/Backoff using GOLDEN_RATIO
// ============================================================================

/// Fibonacci-based retry strategy using GOLDEN_RATIO
/// 
/// # Rust 1.94 Feature: GOLDEN_RATIO
/// The golden ratio φ ≈ 1.618 provides optimal spacing for retry delays
pub struct FibonacciRetryStrategy {
    max_retries: u32,
    base_delay_ms: u64,
    max_delay_ms: u64,
}

impl FibonacciRetryStrategy {
    pub fn new(max_retries: u32, base_delay_ms: u64, max_delay_ms: u64) -> Self {
        Self {
            max_retries,
            base_delay_ms,
            max_delay_ms,
        }
    }
    
    /// Pre-computed constants using const mul_add
    /// 
    /// # Rust 1.94 Feature: const mul_add
    pub const PHI_RECIP: f64 = 1.0_f64 / GOLDEN_RATIO;
    pub const PHI_SQUARED: f64 = GOLDEN_RATIO.mul_add(GOLDEN_RATIO, 0.0);
    
    /// Calculate delay using golden ratio exponential backoff
    /// 
    /// delay = base_delay * φ^attempt
    /// 
    /// This provides smoother growth than traditional 2^n exponential backoff
    pub fn calculate_delay(&self, attempt: u32) -> u64 {
        if attempt == 0 {
            return self.base_delay_ms.min(self.max_delay_ms);
        }
        
        // Golden ratio exponential growth: φ^attempt
        let multiplier = GOLDEN_RATIO.powi(attempt as i32);
        let delay = (self.base_delay_ms as f64 * multiplier) as u64;
        
        delay.max(self.base_delay_ms).min(self.max_delay_ms)
    }
    
    /// Golden ratio backoff with jitter
    /// 
    /// Uses φ's fractional part for natural jitter distribution
    pub fn calculate_delay_with_jitter(&self, attempt: u32, jitter_factor: f64) -> u64 {
        let base_delay = self.calculate_delay(attempt);
        let jitter = base_delay as f64 * jitter_factor.clamp(0.0, 1.0) * (GOLDEN_RATIO - 1.0);
        (base_delay as f64 + jitter) as u64
    }
    
    /// Batch size using Fibonacci sequence
    /// 
    /// Returns optimal batch sizes that grow according to Fibonacci
    pub fn optimal_batch_size(&self, iteration: u32, max_size: usize) -> usize {
        let n = iteration as f64;
        let phi_n = GOLDEN_RATIO.powf(n);
        let fib = (phi_n / 2.23606797749979).round() as usize;
        fib.max(1).min(max_size)
    }
    
    /// Golden ratio split for resource allocation
    /// 
    /// Divides resources into optimal proportions (≈ 38.2% and 61.8%)
    pub fn split_resources(&self, total: u64) -> (u64, u64) {
        let small = (total as f64 * Self::PHI_RECIP * Self::PHI_RECIP) as u64;
        let large = total - small;
        (small, large)
    }
}

/// Connection pool size optimizer
pub struct ConnectionPoolOptimizer;

impl ConnectionPoolOptimizer {
    /// Calculate optimal pool size using Euler-Mascheroni constant
    /// 
    /// optimal ≈ concurrency / (1 + γ)
    pub fn optimal_size(expected_concurrency: u32, max_size: u32) -> u32 {
        if expected_concurrency == 0 {
            return 1;
        }
        
        let safety_factor = 1.0 + EULER_GAMMA;
        let optimal = (expected_concurrency as f64 / safety_factor).ceil() as u32;
        optimal.max(1).min(max_size)
    }
}

// ============================================================================
// Section 6: Compile-time Optimizations using const mul_add
// ============================================================================

/// Compile-time mathematical operations
/// 
/// # Rust 1.94 Feature: const mul_add
/// Fused multiply-add operations at compile time for higher precision
pub struct ConstMath;

impl ConstMath {
    /// Compile-time linear interpolation
    /// 
    /// lerp(a, b, t) = a + (b - a) * t
    pub const fn lerp(a: f64, b: f64, t: f64) -> f64 {
        t.mul_add(b - a, a)
    }
    
    /// Compile-time polynomial evaluation (Horner's method)
    pub const fn poly_eval(x: f64, coeffs: &[f64]) -> f64 {
        let mut result: f64 = 0.0;
        let mut i = coeffs.len();
        
        while i > 0 {
            i -= 1;
            result = result.mul_add(x, coeffs[i]);
        }
        
        result
    }
    
    /// Compile-time sigmoid approximation
    pub const fn sigmoid_approx(x: f64) -> f64 {
        if x > 4.0 {
            1.0
        } else if x < -4.0 {
            0.0
        } else {
            // Linear approximation around 0: σ(x) ≈ 0.5 + 0.25x
            0.25_f64.mul_add(x, 0.5)
        }
    }
    
    /// Pre-computed interpolation values for sampling rates
    pub const RATE_LOW: f64 = Self::lerp(0.001, 1.0, 0.1);
    pub const RATE_MEDIUM: f64 = Self::lerp(0.001, 1.0, 0.5);
    pub const RATE_HIGH: f64 = Self::lerp(0.001, 1.0, 0.9);
}

/// Adaptive timeout calculator
pub struct AdaptiveTimeout;

impl AdaptiveTimeout {
    /// Calculate adaptive batch timeout
    /// 
    /// Uses both GOLDEN_RATIO and EULER_GAMMA for optimal adjustment
    pub fn calculate(queue_depth: usize, base_ms: u64, max_ms: u64) -> u64 {
        if queue_depth == 0 {
            return max_ms;
        }
        
        let depth = queue_depth as f64;
        // Golden ratio based load factor
        let load_factor = (depth / 100.0).min(1.0);
        
        // Euler-Mascheroni based adjustment
        let remaining = 1.0 - load_factor;
        let adjusted_remaining = remaining.powf(EULER_GAMMA);
        
        // Linear interpolation with const mul_add
        ConstMath::lerp(base_ms as f64, max_ms as f64, adjusted_remaining) as u64
    }
}

// ============================================================================
// Section 7: High-performance Metrics using FP16 SIMD (when available)
// ============================================================================

/// FP16 metrics processor (with runtime feature detection)
/// 
/// Note: FP16 SIMD is available on:
/// - x86_64: AVX-512 FP16 (Sapphire Rapids+)
/// - aarch64: NEON FP16 (Apple Silicon, ARM Neoverse)
pub struct Fp16MetricsProcessor;

impl Fp16MetricsProcessor {
    /// Check if FP16 SIMD is available
    #[cfg(target_arch = "x86_64")]
    pub fn is_available() -> bool {
        is_x86_feature_detected!("avx512fp16")
    }
    
    #[cfg(target_arch = "aarch64")]
    pub fn is_available() -> bool {
        // NEON FP16 is standard on AArch64
        true
    }
    
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub fn is_available() -> bool {
        false
    }
    
    /// Process metrics batch (uses SIMD if available)
    pub fn process_batch(values: &[f32]) -> f32 {
        if Self::is_available() {
            // In a real implementation, this would use FP16 intrinsics
            // For demo purposes, we use standard f32 operations
            Self::simd_sum(values)
        } else {
            values.iter().sum()
        }
    }
    
    /// Simulated SIMD sum (placeholder for actual FP16 intrinsics)
    fn simd_sum(values: &[f32]) -> f32 {
        // Chunk processing for cache efficiency
        const CHUNK_SIZE: usize = 16;
        
        let mut sum: f32 = 0.0;
        let chunks = values.chunks(CHUNK_SIZE);
        
        for chunk in chunks {
            // In real implementation, this would use _mm256_add_ph (AVX-512 FP16)
            // or vaddq_f16 (NEON FP16)
            sum += chunk.iter().sum::<f32>();
        }
        
        sum
    }
    
    /// Convert f32 metrics to f16 representation (if needed)
    /// 
    /// Note: This is a demonstration - actual implementation would use
    /// hardware FP16 conversion instructions
    pub fn to_fp16_metrics(values: &[f32]) -> Vec<u16> {
        values
            .iter()
            .map(|&v| {
                // Simplified conversion (actual would use hardware)
                // This is placeholder logic
                if v.is_nan() {
                    0x7E00 // NaN in FP16
                } else if v.is_infinite() {
                    if v.is_sign_positive() {
                        0x7C00 // +inf
                    } else {
                        0xFC00 // -inf
                    }
                } else {
                    // Simple truncation for demo (not correct FP16 conversion)
                    let clamped = v.clamp(-65504.0, 65504.0);
                    // In real impl: use _mm_cvtps_ph or similar
                    (clamped as f64 / 256.0) as u16
                }
            })
            .collect()
    }
}

// ============================================================================
// Section 8: TOML 1.1 Configuration Parsing
// ============================================================================

/// TOML 1.1 configuration example with multi-line inline tables
/// 
/// ```toml
/// # TOML 1.1 Configuration Example
/// [otlp]
/// endpoint = "http://localhost:4317"
/// timeout = 30
/// 
/// [otlp.batch]
/// size = 512
/// delay = 1000
/// 
/// [otlp.attributes]  # Multi-line inline table (TOML 1.1)
/// service = "demo-service",
/// version = "1.0.0",
/// region = "us-west-2",
/// team = "platform"
/// 
/// [otlp.retry]
/// max_attempts = 5
/// base_delay = 100
/// multiplier = 1.618  # Golden ratio!
/// ```
#[derive(Debug, Clone)]
pub struct TomlConfig {
    pub raw_config: String,
}

impl TomlConfig {
    /// Example TOML 1.1 configuration with multi-line inline tables
    pub fn example_config() -> String {
        r#"# OTLP Rust 1.94 Demo Configuration
# TOML 1.1 with multi-line inline tables

[service]
name = "otlp-rust-194-demo"
version = "1.0.0"
# Multi-line inline table (TOML 1.1 feature)
attributes = { 
    region = "us-west-2",
    environment = "production",
    team = "observability",
    cost_center = "platform-eng"
}

[export]
endpoint = "http://localhost:4317"
protocol = "grpc"
compression = "gzip"
# Multi-line inline table for headers
headers = {
    Authorization = "Bearer ${OTLP_TOKEN}",
    X-Custom-Header = "value"
}

[batch]
# Fibonacci-based sizing using GOLDEN_RATIO
base_size = 89
max_size = 1440
# Adaptive timeout using EULER_GAMMA
timeout_ms = 5000

[retry]
max_attempts = 5
base_delay_ms = 100
# Golden ratio multiplier for natural backoff
multiplier = 1.618033988749795

[sampling]
# Euler-Mascheroni based adaptive sampling
base_rate = 0.1
adaptive = true
priority_levels = 10

[performance]
# FP16 SIMD acceleration (when available)
use_fp16 = true
vectorize = true
zero_copy = true
"#
        .to_string()
    }
    
    /// Parse configuration values
    pub fn parse_sample_rate(&self) -> f64 {
        // In a real implementation, this would use toml crate
        0.1 // Default value
    }
    
    pub fn parse_batch_size(&self) -> usize {
        512 // Default value
    }
}

// ============================================================================
// Complete Example: Full OTLP Pipeline using all Rust 1.94 features
// ============================================================================

/// Complete OTLP pipeline demo
/// 
/// This function demonstrates how all Rust 1.94 features work together
/// in a realistic OTLP telemetry processing scenario.
/// 
/// # Features Used
/// 
/// 1. **LazyLock** - Global configuration and metrics cache
/// 2. **LazyCell** - Thread-local buffer management
/// 3. **array_windows** - Pattern detection in metrics
/// 4. **element_offset** - Zero-copy span serialization
/// 5. **EULER_GAMMA** - Adaptive sampling calculations
/// 6. **GOLDEN_RATIO** - Retry backoff strategy
/// 7. **const mul_add** - Compile-time optimization constants
/// 8. **FP16 SIMD** - High-performance metric aggregation (when available)
/// 
/// # Example
/// 
/// ```rust,ignore
/// use otlp::rust_1_94_comprehensive_demo::complete_otlp_pipeline_demo;
/// 
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     complete_otlp_pipeline_demo().await
/// }
/// ```
pub async fn complete_otlp_pipeline_demo() -> Result<PipelineResult, Box<dyn std::error::Error>> {
    println!("=== Rust 1.94 OTLP Pipeline Demo ===\n");
    
    // Step 1: Initialize global configuration (LazyLock)
    println!("1. Configuration Initialization (LazyLock)");
    println!("   - Config initialized: {}", ConfigManager::is_initialized());
    
    ConfigManager::update(|cfg| {
        cfg.name = "rust-194-demo".to_string();
        cfg.batch_size = 512;
        cfg.attributes.insert("demo".to_string(), "true".to_string());
    });
    
    let config = ConfigManager::get();
    println!("   - Service name: {}", config.name);
    println!("   - Batch size: {}", config.batch_size);
    
    // Step 2: Initialize thread-local buffer (LazyCell)
    println!("\n2. Thread-Local Buffer (LazyCell)");
    let mut local_buffer = ThreadLocalBuffer::new();
    println!("   - Buffer initialized: {}", local_buffer.try_get().is_some());
    local_buffer.write(b"OTLP telemetry data");
    println!("   - Buffer size: {} bytes", local_buffer.force_mut().len());
    
    // Step 3: Generate sample metrics
    println!("\n3. Metrics Generation");
    let metrics = generate_sample_metrics(20);
    println!("   - Generated {} metric points", metrics.len());
    
    // Step 4: Pattern detection (array_windows)
    println!("\n4. Pattern Detection (array_windows)");
    let patterns = detect_metric_patterns(&metrics);
    let pattern_counts = count_patterns(&patterns);
    println!("   - Detected patterns:");
    for (pattern, count) in pattern_counts {
        println!("     {:?}: {}", pattern, count);
    }
    
    // Step 5: Zero-copy span handling (element_offset)
    println!("\n5. Zero-Copy Span Serialization (element_offset)");
    let spans = generate_sample_spans(10);
    let serializer = ZeroCopySpanSerializer::new(&spans);
    let test_span = &spans[5];
    if let Some(idx) = serializer.get_span_index(test_span) {
        println!("   - Span index lookup: {} (zero-copy)", idx);
    }
    println!("   - Contains span[5]: {}", serializer.contains(test_span));
    
    // Step 6: Adaptive sampling (EULER_GAMMA)
    println!("\n6. Adaptive Sampling (EULER_GAMMA)");
    let loads = vec![10.0, 50.0, 100.0, 500.0, 1000.0];
    for load in &loads {
        let rate = AdaptiveSampler::calculate_rate(*load, 0.1);
        println!("   - Load {:.0}: {:.2}% sampling rate", load, rate * 100.0);
    }
    
    // Step 7: Retry strategy (GOLDEN_RATIO)
    println!("\n7. Fibonacci Retry Strategy (GOLDEN_RATIO)");
    let retry = FibonacciRetryStrategy::new(5, 100, 30000);
    for attempt in 0..5 {
        let delay = retry.calculate_delay(attempt);
        println!("   - Attempt {}: {}ms delay", attempt, delay);
    }
    
    // Step 8: Optimal batch sizing
    println!("\n8. Fibonacci Batch Sizing");
    for i in 0..8 {
        let size = retry.optimal_batch_size(i, 1000);
        println!("   - Iteration {}: {} spans/batch", i, size);
    }
    
    // Step 9: Resource allocation (Golden Ratio split)
    println!("\n9. Resource Allocation (Golden Ratio Split)");
    let (small, large) = retry.split_resources(1000);
    println!("   - Total: 1000 -> Small: {} ({}%), Large: {} ({}%)",
             small, (small as f64 / 10.0), large, (large as f64 / 10.0));
    
    // Step 10: Compile-time constants (const mul_add)
    println!("\n10. Compile-Time Constants (const mul_add)");
    println!("    - EULER_GAMMA^2: {:.10}", AdaptiveSampler::EULER_GAMMA_SQUARED);
    println!("    - 1 + EULER_GAMMA: {:.10}", AdaptiveSampler::ONE_PLUS_GAMMA);
    println!("    - Pre-computed rate (low): {:.3}", ConstMath::RATE_LOW);
    println!("    - Pre-computed rate (high): {:.3}", ConstMath::RATE_HIGH);
    
    // Step 11: FP16 SIMD check
    println!("\n11. FP16 SIMD Support");
    println!("    - FP16 available: {}", Fp16MetricsProcessor::is_available());
    let metric_values: Vec<f32> = metrics.iter().map(|m| m.value as f32).collect();
    let sum = Fp16MetricsProcessor::process_batch(&metric_values);
    println!("    - Metrics sum: {:.2}", sum);
    
    // Step 12: TOML 1.1 config
    println!("\n12. TOML 1.1 Configuration Example");
    println!("    See example_config() for multi-line inline table demo");
    
    // Step 13: Moving average (array_windows)
    println!("\n13. Moving Average (array_windows)");
    let values: Vec<f64> = metrics.iter().map(|m| m.value).collect();
    let ma3 = moving_average::<3>(&values);
    println!("    - 3-point moving average (first 5): {:?}", &ma3[..ma3.len().min(5)]);
    
    // Step 14: Anomaly detection
    println!("\n14. Anomaly Detection");
    let test_data = vec![1u8, 2, 2, 1, 5, 6, 6, 5, 9, 10]; // Contains ABBA patterns
    let anomalies = detect_abba_anomalies(&test_data);
    println!("    - ABBA patterns at indices: {:?}", anomalies);
    
    // Step 15: Adaptive timeout
    println!("\n15. Adaptive Timeout Calculation");
    let queue_depths = vec![0, 10, 50, 100, 200];
    for depth in &queue_depths {
        let timeout = AdaptiveTimeout::calculate(*depth, 100, 5000);
        println!("    - Queue depth {}: {}ms timeout", depth, timeout);
    }
    
    // Summary
    println!("\n=== Pipeline Complete ===");
    
    Ok(PipelineResult {
        metrics_processed: metrics.len(),
        spans_processed: spans.len(),
        patterns_detected: patterns.len(),
        anomalies_detected: anomalies.len(),
        fp16_available: Fp16MetricsProcessor::is_available(),
    })
}

/// Result of the complete pipeline demo
#[derive(Debug)]
pub struct PipelineResult {
    pub metrics_processed: usize,
    pub spans_processed: usize,
    pub patterns_detected: usize,
    pub anomalies_detected: usize,
    pub fp16_available: bool,
}

// Helper functions

fn generate_sample_metrics(count: usize) -> Vec<MetricPoint> {
    (0..count)
        .map(|i| {
            let t = i as f64 * 0.5;
            // Generate some interesting patterns
            let value = if i % 5 == 0 {
                10.0 + t.sin() * 5.0 // Oscillating
            } else if i > count / 2 {
                i as f64 * 0.3 // Increasing trend
            } else {
                5.0 + (i as f64).ln() // Logarithmic
            };
            MetricPoint {
                timestamp: i as u64 * 1000,
                value: value.max(0.0),
            }
        })
        .collect()
}

fn generate_sample_spans(count: usize) -> Vec<Span> {
    (0..count)
        .map(|i| Span {
            id: [i as u8, 0, 0, 0, 0, 0, 0, 0],
            trace_id: [0; 16],
            name: format!("span-{}", i),
            start_time: i as u64 * 1000,
            end_time: (i as u64 + 1) * 1000,
            status: if i % 7 == 0 {
                SpanStatus::Error
            } else {
                SpanStatus::Ok
            },
        })
        .collect()
}

fn count_patterns(patterns: &[TelemetryPattern]) -> HashMap<TelemetryPattern, usize> {
    let mut counts = HashMap::new();
    for pattern in patterns {
        *counts.entry(*pattern).or_insert(0) += 1;
    }
    counts
}

// ============================================================================
// Performance Comparison Utilities
// ============================================================================

/// Performance comparison utilities
pub mod perf_comparison {
    use super::*;
    use std::time::{Duration, Instant};
    
    /// Compare array_windows vs traditional windows performance
    pub fn compare_window_methods(data: &[f64]) -> (Duration, Duration) {
        // array_windows approach
        let start = Instant::now();
        let _: Vec<f64> = data.array_windows::<3>().map(|[a, b, c]| (a + b + c) / 3.0).collect();
        let array_windows_time = start.elapsed();
        
        // Traditional windows approach
        let start = Instant::now();
        let _: Vec<f64> = data.windows(3).map(|w| w.iter().sum::<f64>() / 3.0).collect();
        let windows_time = start.elapsed();
        
        (array_windows_time, windows_time)
    }
    
    /// Compare element_offset vs linear search
    pub fn compare_offset_methods(data: &[MetricPoint], target: &MetricPoint) -> (Duration, Duration) {
        // element_offset approach
        let start = Instant::now();
        let _ = data.element_offset(target);
        let element_offset_time = start.elapsed();
        
        // Linear search approach
        let start = Instant::now();
        let _: Option<usize> = data.iter().position(|p| std::ptr::eq(p, target));
        let linear_time = start.elapsed();
        
        (element_offset_time, linear_time)
    }
}

// ============================================================================
// Best Practices Documentation
// ============================================================================

/// # Rust 1.94 Best Practices for OTLP
///
/// ## 1. LazyLock Usage
///
/// - Use `LazyLock::get()` to check initialization without triggering it
/// - Use `LazyLock::force()` when you need guaranteed initialization
/// - Combine with `RwLock` for mutable global state
/// - Prefer `LazyLock` over `lazy_static` for new code
///
/// ## 2. LazyCell Usage
///
/// - Use `LazyCell` for single-threaded lazy initialization
/// - Use `LazyCell::get_mut()` for mutable access without forcing init
/// - Ideal for thread-local caches and buffers
///
/// ## 3. array_windows Best Practices
///
/// - Use for fixed-size window operations (pattern detection, moving averages)
/// - Prefer over `windows()` when window size is known at compile time
/// - Enables better compiler optimizations
/// - Use const generics for flexible window sizes
///
/// ## 4. element_offset Best Practices
///
/// - Use for zero-copy serialization offset calculation
/// - Validate element belongs to slice before using offset
/// - Combine with sub-slicing for range operations
/// - Ideal for memory pool indexing
///
/// ## 5. Mathematical Constants
///
/// - Use `EULER_GAMMA` for natural damping in adaptive algorithms
/// - Use `GOLDEN_RATIO` for optimal spacing in backoff/retry
/// - Pre-compute constants using `const mul_add` for compile-time optimization
///
/// ## 6. FP16 SIMD
///
/// - Always check availability with `is_available()` at runtime
/// - Provide fallback implementation for non-FP16 platforms
/// - Use for large-scale metric aggregation
/// - Consider precision requirements before converting
pub struct BestPractices;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lazy_lock_config() {
        // Note: When running multiple tests, GLOBAL_CONFIG may already be initialized
        // by other tests. We test the behavior both with and without prior initialization.
        let was_initialized = ConfigManager::is_initialized();
        
        // Access the config (this initializes it if not already done)
        let _guard = ConfigManager::get();
        assert!(ConfigManager::is_initialized());
        drop(_guard);
        
        // Verify it stays initialized after access
        assert!(ConfigManager::is_initialized());
        
        // If it wasn't initialized before, we verified the lazy initialization works
        // If it was already initialized, we verified the access works correctly
        if !was_initialized {
            // First time access - verified lazy initialization
        }
    }
    
    #[test]
    fn test_lazy_cell_buffer() {
        let mut buffer = ThreadLocalBuffer::new();
        assert!(buffer.try_get().is_none());
        buffer.write(b"test");
        assert!(buffer.try_get().is_some());
        assert_eq!(buffer.force_mut().len(), 4);
    }
    
    #[test]
    fn test_array_windows_pattern_detection() {
        let metrics = vec![
            MetricPoint { timestamp: 1, value: 1.0 },
            MetricPoint { timestamp: 2, value: 2.0 },
            MetricPoint { timestamp: 3, value: 3.0 },
            MetricPoint { timestamp: 4, value: 4.0 },
        ];
        let patterns = detect_metric_patterns(&metrics);
        assert!(!patterns.is_empty());
    }
    
    #[test]
    fn test_element_offset() {
        let spans = generate_sample_spans(5);
        let serializer = ZeroCopySpanSerializer::new(&spans);
        assert_eq!(serializer.get_span_index(&spans[2]), Some(2));
        assert!(serializer.contains(&spans[0]));
    }
    
    #[test]
    fn test_euler_gamma_sampling() {
        let rate = AdaptiveSampler::calculate_rate(100.0, 0.1);
        assert!(rate > 0.0 && rate <= 1.0);
        
        let weight = AdaptiveSampler::priority_weight(5, 1.0);
        assert!(weight > 1.0);
    }
    
    #[test]
    fn test_golden_ratio_backoff() {
        let retry = FibonacciRetryStrategy::new(5, 100, 30000);
        let d0 = retry.calculate_delay(0);
        let d1 = retry.calculate_delay(1);
        let d2 = retry.calculate_delay(2);
        
        // Attempt 0 should return base delay
        assert_eq!(d0, 100);
        
        // Delays should increase with each attempt
        assert!(d1 > d0, "Expected d1 ({}) > d0 ({})", d1, d0);
        assert!(d2 > d1, "Expected d2 ({}) > d1 ({})", d2, d1);
        
        // Verify approximate golden ratio growth (with tolerance for floating-point)
        // Expected: d1 ≈ 100 * φ ≈ 162, d2 ≈ 100 * φ² ≈ 262
        assert!((160..=165).contains(&d1), "d1 ({}) should be approximately 161-162", d1);
        assert!((260..=265).contains(&d2), "d2 ({}) should be approximately 261-262", d2);
    }
    
    #[test]
    fn test_const_math() {
        // Test const mul_add results
        const _: () = assert!(ConstMath::RATE_LOW < ConstMath::RATE_HIGH);
        assert!((ConstMath::lerp(0.0, 10.0, 0.5) - 5.0).abs() < f64::EPSILON);
    }
    
    #[test]
    fn test_moving_average() {
        let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let ma2 = moving_average::<2>(&values);
        let ma3 = moving_average::<3>(&values);
        
        assert_eq!(ma2.len(), 4);
        assert_eq!(ma3.len(), 3);
        assert_eq!(ma2[0], 1.5);
        assert_eq!(ma3[0], 2.0);
    }
    
    #[test]
    fn test_abba_detection() {
        let data = vec![1u8, 2, 2, 1, 3, 4, 4, 3];
        let anomalies = detect_abba_anomalies(&data);
        assert_eq!(anomalies, vec![0, 4]);
    }
    
    #[test]
    fn test_adaptive_timeout() {
        let empty = AdaptiveTimeout::calculate(0, 100, 5000);
        let full = AdaptiveTimeout::calculate(200, 100, 5000);
        
        assert_eq!(empty, 5000);
        assert!(full < empty);
    }
    
    #[test]
    fn test_connection_pool_optimization() {
        let size = ConnectionPoolOptimizer::optimal_size(100, 50);
        assert!(size > 0 && size <= 50);
    }
    
    #[tokio::test]
    async fn test_complete_pipeline() {
        let result = complete_otlp_pipeline_demo().await.unwrap();
        assert_eq!(result.metrics_processed, 20);
        assert_eq!(result.spans_processed, 10);
    }
}
