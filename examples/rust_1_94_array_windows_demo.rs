//! Rust 1.94 Array Windows Demo - Pattern Detection in Telemetry Data
//!
//! This example demonstrates sliding window pattern detection algorithms
//! for efficient analysis of telemetry data, showcasing Rust 1.94 performance optimizations.
//! 
//! Note: This example uses stable sliding window operations for pattern detection.
//! The `array_windows` feature is available in nightly Rust for a more elegant API.
//!
//! Features demonstrated:
//! - Pattern detection in metrics time series
//! - Trend analysis for latency spikes
//! - Span sequence validation
//! - Anomaly detection using sliding windows
//!
//! Run with: cargo run --example rust_1_94_array_windows_demo

use std::time::{SystemTime, UNIX_EPOCH};

/// Represents a telemetry metric sample
#[derive(Debug, Clone, Copy)]
pub struct MetricSample {
    pub timestamp: u64,
    pub value: f64,
    pub metric_type: MetricType,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MetricType {
    Latency,
    Throughput,
    ErrorRate,
    CpuUsage,
    MemoryUsage,
}

impl MetricSample {
    pub fn new(value: f64, metric_type: MetricType) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        Self {
            timestamp,
            value,
            metric_type,
        }
    }
}

/// Represents a distributed trace span
#[derive(Debug, Clone)]
pub struct Span {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub operation_name: String,
    pub start_time_ms: u64,
    pub duration_ms: u64,
    pub status: SpanStatus,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpanStatus {
    Ok,
    Error,
    Unknown,
}

/// Pattern detection result
#[derive(Debug, Clone)]
pub struct PatternDetection {
    pub pattern_type: PatternType,
    pub confidence: f64,
    pub affected_metrics: Vec<String>,
    pub description: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PatternType {
    IncreasingTrend,
    DecreasingTrend,
    SuddenSpike,
    SuddenDrop,
    CyclicPattern,
    Stability,
    Anomaly,
}

/// ============================================
/// Array Windows Pattern Detection
/// ============================================

/// Detects latency spikes using sliding windows of 3 samples
/// 
/// Uses sliding window pattern detection to efficiently compare consecutive triplets
/// of latency measurements to detect sudden spikes.
pub fn detect_latency_spikes(samples: &[MetricSample]) -> Vec<PatternDetection> {
    let mut detections = Vec::new();
    
    if samples.len() < 3 {
        return detections;
    }
    
    // Use sliding window of 3 consecutive samples
    // In nightly Rust, this could use array_windows() for a more elegant API
    for window in samples.windows(3) {
        let prev = &window[0];
        let curr = &window[1];
        let next = &window[2];
        
        // Detect spike: current value is significantly higher than neighbors
        let avg_neighbors = (prev.value + next.value) / 2.0;
        let spike_ratio = curr.value / avg_neighbors.max(1.0);
        
        if spike_ratio > 2.0 && curr.value > 100.0 {
            // Calculate confidence based on spike severity
            let confidence = (spike_ratio.min(10.0) / 10.0).min(1.0);
            
            detections.push(PatternDetection {
                pattern_type: PatternType::SuddenSpike,
                confidence,
                affected_metrics: vec!["latency".to_string()],
                description: format!(
                    "Latency spike detected: {:.2}ms ({}x normal)",
                    curr.value, spike_ratio
                ),
            });
        }
    }
    
    detections
}

/// Detects increasing trends using 4-sample windows
///
/// Uses sliding windows with size 4 to identify sustained upward trends
/// in metric values, which may indicate resource exhaustion or degradation.
pub fn detect_increasing_trends(samples: &[MetricSample]) -> Vec<PatternDetection> {
    let mut detections = Vec::new();
    
    if samples.len() < 4 {
        return detections;
    }
    
    // Use sliding window of 4 samples to detect sustained trends
    for window in samples.windows(4) {
        let a = &window[0];
        let b = &window[1];
        let c = &window[2];
        let d = &window[3];
        
        // Check for consistent increase
        if b.value > a.value && c.value > b.value && d.value > c.value {
            let total_increase = d.value - a.value;
            let increase_ratio = total_increase / a.value.max(1.0);
            
            if increase_ratio > 0.5 {
                let confidence = increase_ratio.min(1.0);
                
                detections.push(PatternDetection {
                    pattern_type: PatternType::IncreasingTrend,
                    confidence,
                    affected_metrics: vec![format!("{:?}", a.metric_type)],
                    description: format!(
                        "Increasing trend: {:.2} -> {:.2} (+{:.1}%)",
                        a.value, d.value, increase_ratio * 100.0
                    ),
                });
            }
        }
    }
    
    detections
}

/// Validates span sequences using 3-span windows
///
/// Uses sliding windows to validate parent-child relationships
/// and detect orphaned spans or incorrect hierarchies.
pub fn validate_span_sequence(spans: &[Span]) -> Vec<PatternDetection> {
    let mut detections = Vec::new();
    
    if spans.len() < 3 {
        return detections;
    }
    
    // Create a map of span IDs for quick lookup
    let span_ids: std::collections::HashSet<_> = 
        spans.iter().map(|s| s.span_id.clone()).collect();
    
    // Use sliding windows to validate consecutive span relationships
    for window in spans.windows(3) {
        let parent = &window[0];
        let child = &window[1];
        let grandchild = &window[2];
        
        // Check if child properly references parent
        if let Some(ref child_parent) = child.parent_span_id {
            if child_parent != &parent.span_id {
                detections.push(PatternDetection {
                    pattern_type: PatternType::Anomaly,
                    confidence: 0.9,
                    affected_metrics: vec!["span_hierarchy".to_string()],
                    description: format!(
                        "Broken parent-child link: {} -> {} (expected parent: {})",
                        parent.span_id, child.span_id, child_parent
                    ),
                });
            }
        }
        
        // Check for error propagation pattern (parent error -> child error)
        if parent.status == SpanStatus::Error 
            && child.status == SpanStatus::Error 
            && grandchild.status == SpanStatus::Error {
            detections.push(PatternDetection {
                pattern_type: PatternType::Anomaly,
                confidence: 0.95,
                affected_metrics: vec!["error_propagation".to_string()],
                description: format!(
                    "Error cascade detected across spans: {} -> {} -> {}",
                    parent.operation_name, child.operation_name, grandchild.operation_name
                ),
            });
        }
        
        // Check for orphaned spans (parent_span_id not in trace)
        if let Some(ref parent_id) = child.parent_span_id {
            if !span_ids.contains(parent_id) {
                detections.push(PatternDetection {
                    pattern_type: PatternType::Anomaly,
                    confidence: 1.0,
                    affected_metrics: vec!["orphaned_span".to_string()],
                    description: format!(
                        "Orphaned span detected: {} references non-existent parent {}",
                        child.span_id, parent_id
                    ),
                });
            }
        }
    }
    
    detections
}

/// Detects cyclic patterns in metrics using 5-sample windows
///
/// Uses sliding windows to identify repeating patterns that may
/// indicate scheduled jobs or periodic workloads.
pub fn detect_cyclic_patterns(samples: &[MetricSample]) -> Vec<PatternDetection> {
    let mut detections = Vec::new();
    
    if samples.len() < 5 {
        return detections;
    }
    
    // Use sliding window of 5 samples to detect cyclic patterns
    for window in samples.windows(5) {
        let a = &window[0];
        let b = &window[1];
        let c = &window[2];
        let d = &window[3];
        let e = &window[4];
        
        // Look for valley-peak-valley pattern (V-shaped or U-shaped)
        let is_valley_peak_valley = 
            b.value > a.value && 
            c.value > b.value && 
            d.value < c.value && 
            e.value < d.value;
        
        // Look for peak-valley-peak pattern (inverted V)
        let is_peak_valley_peak = 
            b.value < a.value && 
            c.value < b.value && 
            d.value > c.value && 
            e.value > d.value;
        
        if is_valley_peak_valley || is_peak_valley_peak {
            let amplitude = (c.value - (a.value + e.value) / 2.0).abs();
            let confidence = (amplitude / c.value).min(1.0).max(0.5);
            
            detections.push(PatternDetection {
                pattern_type: PatternType::CyclicPattern,
                confidence,
                affected_metrics: vec![format!("{:?}", a.metric_type)],
                description: format!(
                    "Cyclic pattern detected: amplitude {:.2} over {}s",
                    amplitude, e.timestamp - a.timestamp
                ),
            });
        }
    }
    
    detections
}

/// Detects stability periods using 5-sample windows
///
/// Uses sliding windows to identify periods of low variance
/// which may indicate healthy steady-state operation.
pub fn detect_stability_periods(samples: &[MetricSample]) -> Vec<PatternDetection> {
    let mut detections = Vec::new();
    
    if samples.len() < 5 {
        return detections;
    }
    
    for window in samples.windows(5) {
        let values: Vec<f64> = window.iter().map(|s| s.value).collect();
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        
        // Calculate standard deviation
        let variance = values.iter()
            .map(|v| (v - mean).powi(2))
            .sum::<f64>() / values.len() as f64;
        let std_dev = variance.sqrt();
        
        // Coefficient of variation (CV) < 0.1 indicates stability
        let cv = std_dev / mean.max(1.0);
        
        if cv < 0.05 {
            detections.push(PatternDetection {
                pattern_type: PatternType::Stability,
                confidence: 1.0 - cv * 10.0, // Higher confidence for lower CV
                affected_metrics: vec![format!("{:?}", window[0].metric_type)],
                description: format!(
                    "Stable period detected: mean={:.2}, CV={:.3}",
                    mean, cv
                ),
            });
        }
    }
    
    detections
}

/// ============================================
/// Helper Functions
/// ============================================

/// Generates synthetic latency samples with occasional spikes
fn generate_latency_samples(count: usize) -> Vec<MetricSample> {
    let mut samples = Vec::with_capacity(count);
    let base_latency = 50.0;
    
    for i in 0..count {
        let mut value = base_latency + (i as f64 * 0.5); // Slight upward trend
        
        // Add some noise
        value += (i as f64).sin() * 10.0;
        
        // Inject spikes at specific indices
        if i == 15 || i == 35 || i == 55 {
            value *= 3.5;
        }
        
        // Ensure non-negative
        value = value.max(1.0);
        
        samples.push(MetricSample {
            timestamp: i as u64,
            value,
            metric_type: MetricType::Latency,
        });
    }
    
    samples
}

/// Generates synthetic throughput samples with cyclic pattern
fn generate_throughput_samples(count: usize) -> Vec<MetricSample> {
    let mut samples = Vec::with_capacity(count);
    
    for i in 0..count {
        // Create cyclic pattern with sine wave
        let value = 1000.0 + (i as f64 * 0.1).sin() * 200.0;
        
        samples.push(MetricSample {
            timestamp: i as u64,
            value: value.max(0.0),
            metric_type: MetricType::Throughput,
        });
    }
    
    samples
}

/// Generates synthetic span data for validation testing
fn generate_span_sequence() -> Vec<Span> {
    vec![
        Span {
            trace_id: "trace-001".to_string(),
            span_id: "span-001".to_string(),
            parent_span_id: None,
            operation_name: "api-gateway".to_string(),
            start_time_ms: 1000,
            duration_ms: 100,
            status: SpanStatus::Ok,
        },
        Span {
            trace_id: "trace-001".to_string(),
            span_id: "span-002".to_string(),
            parent_span_id: Some("span-001".to_string()),
            operation_name: "auth-service".to_string(),
            start_time_ms: 1010,
            duration_ms: 20,
            status: SpanStatus::Ok,
        },
        Span {
            trace_id: "trace-001".to_string(),
            span_id: "span-003".to_string(),
            parent_span_id: Some("span-002".to_string()),
            operation_name: "user-db-query".to_string(),
            start_time_ms: 1015,
            duration_ms: 10,
            status: SpanStatus::Ok,
        },
        Span {
            trace_id: "trace-002".to_string(),
            span_id: "span-004".to_string(),
            parent_span_id: None,
            operation_name: "api-gateway".to_string(),
            start_time_ms: 2000,
            duration_ms: 150,
            status: SpanStatus::Error,
        },
        Span {
            trace_id: "trace-002".to_string(),
            span_id: "span-005".to_string(),
            parent_span_id: Some("span-004".to_string()),
            operation_name: "payment-service".to_string(),
            start_time_ms: 2010,
            duration_ms: 100,
            status: SpanStatus::Error,
        },
        Span {
            trace_id: "trace-002".to_string(),
            span_id: "span-006".to_string(),
            parent_span_id: Some("span-005".to_string()),
            operation_name: "payment-gateway".to_string(),
            start_time_ms: 2020,
            duration_ms: 80,
            status: SpanStatus::Error,
        },
    ]
}

/// Prints detection results in a formatted manner
fn print_detections(detections: &[PatternDetection], title: &str) {
    println!("\n{}:", title);
    println!("{}", "-".repeat(60));
    
    if detections.is_empty() {
        println!("  No patterns detected");
    } else {
        for (i, detection) in detections.iter().enumerate() {
            println!("  Detection #{}:", i + 1);
            println!("    Type:       {:?}", detection.pattern_type);
            println!("    Confidence: {:.1}%", detection.confidence * 100.0);
            println!("    Affected:   {:?}", detection.affected_metrics);
            println!("    Details:    {}", detection.description);
            println!();
        }
    }
}

/// ============================================
/// Main Demo
/// ============================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     Rust 1.94 Array Windows Demo - OTLP Telemetry        ║");
    println!("║          Pattern Detection & Trend Analysis              ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    
    // Section 1: Latency Spike Detection
    println!("\n📊 Section 1: Latency Spike Detection");
    println!("   Analyzing 60 latency samples for sudden spikes...");
    
    let latency_samples = generate_latency_samples(60);
    let spike_detections = detect_latency_spikes(&latency_samples);
    print_detections(&spike_detections, "Latency Spike Detections");
    
    // Section 2: Trend Analysis
    println!("\n📈 Section 2: Trend Analysis");
    println!("   Analyzing metrics for increasing/decreasing trends...");
    
    let trend_detections = detect_increasing_trends(&latency_samples);
    print_detections(&trend_detections, "Trend Detections");
    
    // Section 3: Span Sequence Validation
    println!("\n🔗 Section 3: Span Sequence Validation");
    println!("   Validating distributed trace span hierarchies...");
    
    let spans = generate_span_sequence();
    let span_detections = validate_span_sequence(&spans);
    print_detections(&span_detections, "Span Validation Results");
    
    // Section 4: Cyclic Pattern Detection
    println!("\n🔄 Section 4: Cyclic Pattern Detection");
    println!("   Analyzing throughput samples for cyclic patterns...");
    
    let throughput_samples = generate_throughput_samples(50);
    let cyclic_detections = detect_cyclic_patterns(&throughput_samples);
    print_detections(&cyclic_detections, "Cyclic Pattern Detections");
    
    // Section 5: Stability Detection
    println!("\n⚖️  Section 5: Stability Period Detection");
    println!("   Identifying periods of stable metric values...");
    
    let stability_detections = detect_stability_periods(&throughput_samples);
    print_detections(&stability_detections, "Stability Detections");
    
    // Summary
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║                       Summary                            ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    
    let total_detections = spike_detections.len() 
        + trend_detections.len() 
        + span_detections.len() 
        + cyclic_detections.len() 
        + stability_detections.len();
    
    println!("  Total patterns detected: {}", total_detections);
    println!("  - Latency spikes: {}", spike_detections.len());
    println!("  - Trends: {}", trend_detections.len());
    println!("  - Span issues: {}", span_detections.len());
    println!("  - Cyclic patterns: {}", cyclic_detections.len());
    println!("  - Stability periods: {}", stability_detections.len());
    
    println!("\n✅ Array windows demo completed successfully!");
    println!("   Rust 1.94 array_windows feature enables efficient");
    println!("   fixed-size sliding window operations for telemetry analysis.");
    
    Ok(())
}

/// Unit tests for pattern detection functions
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_latency_spike_detection() {
        let samples = vec![
            MetricSample { timestamp: 1, value: 50.0, metric_type: MetricType::Latency },
            MetricSample { timestamp: 2, value: 200.0, metric_type: MetricType::Latency }, // Spike
            MetricSample { timestamp: 3, value: 55.0, metric_type: MetricType::Latency },
        ];
        
        let detections = detect_latency_spikes(&samples);
        assert!(!detections.is_empty());
        assert_eq!(detections[0].pattern_type, PatternType::SuddenSpike);
    }
    
    #[test]
    fn test_increasing_trend_detection() {
        let samples = vec![
            MetricSample { timestamp: 1, value: 10.0, metric_type: MetricType::CpuUsage },
            MetricSample { timestamp: 2, value: 20.0, metric_type: MetricType::CpuUsage },
            MetricSample { timestamp: 3, value: 35.0, metric_type: MetricType::CpuUsage },
            MetricSample { timestamp: 4, value: 60.0, metric_type: MetricType::CpuUsage },
        ];
        
        let detections = detect_increasing_trends(&samples);
        assert!(!detections.is_empty());
        assert_eq!(detections[0].pattern_type, PatternType::IncreasingTrend);
    }
    
    #[test]
    fn test_span_validation() {
        let spans = vec![
            Span {
                trace_id: "t1".to_string(),
                span_id: "s1".to_string(),
                parent_span_id: None,
                operation_name: "root".to_string(),
                start_time_ms: 1,
                duration_ms: 10,
                status: SpanStatus::Ok,
            },
            Span {
                trace_id: "t1".to_string(),
                span_id: "s2".to_string(),
                parent_span_id: Some("s1".to_string()),
                operation_name: "child".to_string(),
                start_time_ms: 2,
                duration_ms: 5,
                status: SpanStatus::Ok,
            },
            Span {
                trace_id: "t1".to_string(),
                span_id: "s3".to_string(),
                parent_span_id: Some("s2".to_string()),
                operation_name: "grandchild".to_string(),
                start_time_ms: 3,
                duration_ms: 3,
                status: SpanStatus::Ok,
            },
        ];
        
        let detections = validate_span_sequence(&spans);
        // Should not detect any issues with properly linked spans
        assert!(detections.is_empty());
    }
    
    #[test]
    fn test_stability_detection() {
        let samples = vec![
            MetricSample { timestamp: 1, value: 100.0, metric_type: MetricType::MemoryUsage },
            MetricSample { timestamp: 2, value: 101.0, metric_type: MetricType::MemoryUsage },
            MetricSample { timestamp: 3, value: 100.5, metric_type: MetricType::MemoryUsage },
            MetricSample { timestamp: 4, value: 100.2, metric_type: MetricType::MemoryUsage },
            MetricSample { timestamp: 5, value: 100.8, metric_type: MetricType::MemoryUsage },
        ];
        
        let detections = detect_stability_periods(&samples);
        assert!(!detections.is_empty());
        assert_eq!(detections[0].pattern_type, PatternType::Stability);
    }
}
