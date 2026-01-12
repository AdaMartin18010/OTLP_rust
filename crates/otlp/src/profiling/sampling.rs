//! # Profiling Sampling Strategies
//!
//! This module provides various sampling strategies for profiling.
//! Sampling is crucial to reduce overhead while still getting representative data.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// Sampling strategy trait
pub trait SamplingStrategy: Send + Sync {
    /// Determine if the current event should be sampled
    fn should_sample(&self) -> bool;

    /// Reset the sampling state
    fn reset(&self);

    /// Get sampling statistics
    fn stats(&self) -> SamplingStats;
}

/// Sampling statistics
#[derive(Debug, Clone)]
pub struct SamplingStats {
    /// Total number of events
    pub total_events: u64,

    /// Number of sampled events
    pub sampled_events: u64,

    /// Sampling rate (0.0 to 1.0)
    pub sampling_rate: f64,
}

/// Always sample (100% sampling rate)
pub struct AlwaysSample {
    counter: Arc<AtomicU64>,
}

impl AlwaysSample {
    pub fn new() -> Self {
        Self {
            counter: Arc::new(AtomicU64::new(0)),
        }
    }
}

impl Default for AlwaysSample {
    fn default() -> Self {
        Self::new()
    }
}

impl SamplingStrategy for AlwaysSample {
    fn should_sample(&self) -> bool {
        self.counter.fetch_add(1, Ordering::Relaxed);
        true
    }

    fn reset(&self) {
        self.counter.store(0, Ordering::Relaxed);
    }

    fn stats(&self) -> SamplingStats {
        let total = self.counter.load(Ordering::Relaxed);
        SamplingStats {
            total_events: total,
            sampled_events: total,
            sampling_rate: 1.0,
        }
    }
}

/// Never sample (0% sampling rate)
pub struct NeverSample {
    counter: Arc<AtomicU64>,
}

impl NeverSample {
    pub fn new() -> Self {
        Self {
            counter: Arc::new(AtomicU64::new(0)),
        }
    }
}

impl Default for NeverSample {
    fn default() -> Self {
        Self::new()
    }
}

impl SamplingStrategy for NeverSample {
    fn should_sample(&self) -> bool {
        self.counter.fetch_add(1, Ordering::Relaxed);
        false
    }

    fn reset(&self) {
        self.counter.store(0, Ordering::Relaxed);
    }

    fn stats(&self) -> SamplingStats {
        let total = self.counter.load(Ordering::Relaxed);
        SamplingStats {
            total_events: total,
            sampled_events: 0,
            sampling_rate: 0.0,
        }
    }
}

/// Probabilistic sampling (random sampling with fixed probability)
pub struct ProbabilisticSampler {
    probability: f64,
    total_counter: Arc<AtomicU64>,
    sampled_counter: Arc<AtomicU64>,
}

impl ProbabilisticSampler {
    /// Create a new probabilistic sampler
    ///
    /// # Arguments
    /// * `probability` - Sampling probability (0.0 to 1.0)
    pub fn new(probability: f64) -> Self {
        assert!(
            (0.0..=1.0).contains(&probability),
            "Probability must be between 0.0 and 1.0"
        );

        Self {
            probability,
            total_counter: Arc::new(AtomicU64::new(0)),
            sampled_counter: Arc::new(AtomicU64::new(0)),
        }
    }
}

impl SamplingStrategy for ProbabilisticSampler {
    fn should_sample(&self) -> bool {
        self.total_counter.fetch_add(1, Ordering::Relaxed);

        let random_value: f64 = rand::random();
        let should_sample = random_value < self.probability;

        if should_sample {
            self.sampled_counter.fetch_add(1, Ordering::Relaxed);
        }

        should_sample
    }

    fn reset(&self) {
        self.total_counter.store(0, Ordering::Relaxed);
        self.sampled_counter.store(0, Ordering::Relaxed);
    }

    fn stats(&self) -> SamplingStats {
        let total = self.total_counter.load(Ordering::Relaxed);
        let sampled = self.sampled_counter.load(Ordering::Relaxed);

        SamplingStats {
            total_events: total,
            sampled_events: sampled,
            sampling_rate: self.probability,
        }
    }
}

/// Rate-based sampling (sample 1 in N events)
pub struct RateSampler {
    rate: u64,
    counter: Arc<AtomicU64>,
    sampled_counter: Arc<AtomicU64>,
}

impl RateSampler {
    /// Create a new rate sampler
    ///
    /// # Arguments
    /// * `rate` - Sample 1 in every N events (must be >= 1)
    pub fn new(rate: u64) -> Self {
        assert!(rate >= 1, "Rate must be at least 1");

        Self {
            rate,
            counter: Arc::new(AtomicU64::new(0)),
            sampled_counter: Arc::new(AtomicU64::new(0)),
        }
    }
}

impl SamplingStrategy for RateSampler {
    fn should_sample(&self) -> bool {
        let count = self.counter.fetch_add(1, Ordering::Relaxed);
        let should_sample = count % self.rate == 0;

        if should_sample {
            self.sampled_counter.fetch_add(1, Ordering::Relaxed);
        }

        should_sample
    }

    fn reset(&self) {
        self.counter.store(0, Ordering::Relaxed);
        self.sampled_counter.store(0, Ordering::Relaxed);
    }

    fn stats(&self) -> SamplingStats {
        let total = self.counter.load(Ordering::Relaxed);
        let sampled = self.sampled_counter.load(Ordering::Relaxed);

        SamplingStats {
            total_events: total,
            sampled_events: sampled,
            sampling_rate: 1.0 / self.rate as f64,
        }
    }
}

/// Adaptive sampling (adjusts rate based on volume)
pub struct AdaptiveSampler {
    target_samples_per_second: u64,
    window_duration: Duration,
    counter: Arc<AtomicU64>,
    sampled_counter: Arc<AtomicU64>,
    window_start: Arc<parking_lot::Mutex<Instant>>,
    current_rate: Arc<AtomicU64>,
}

impl AdaptiveSampler {
    /// Create a new adaptive sampler
    ///
    /// # Arguments
    /// * `target_samples_per_second` - Target number of samples per second
    /// * `window_duration` - Time window for rate adjustment
    pub fn new(target_samples_per_second: u64, window_duration: Duration) -> Self {
        Self {
            target_samples_per_second,
            window_duration,
            counter: Arc::new(AtomicU64::new(0)),
            sampled_counter: Arc::new(AtomicU64::new(0)),
            window_start: Arc::new(parking_lot::Mutex::new(Instant::now())),
            current_rate: Arc::new(AtomicU64::new(1)),
        }
    }

    /// Adjust sampling rate based on current volume
    fn adjust_rate(&self) {
        let mut window_start = self.window_start.lock();
        let elapsed = window_start.elapsed();

        if elapsed >= self.window_duration {
            let sampled = self.sampled_counter.load(Ordering::Relaxed);
            let samples_per_second = sampled as f64 / elapsed.as_secs_f64();

            // Adjust rate to meet target
            if samples_per_second > self.target_samples_per_second as f64 * 1.1 {
                // Too many samples, increase rate (sample less frequently)
                let new_rate = self.current_rate.load(Ordering::Relaxed) * 2;
                self.current_rate.store(new_rate, Ordering::Relaxed);
            } else if samples_per_second < self.target_samples_per_second as f64 * 0.9 {
                // Too few samples, decrease rate (sample more frequently)
                let current = self.current_rate.load(Ordering::Relaxed);
                let new_rate = (current / 2).max(1);
                self.current_rate.store(new_rate, Ordering::Relaxed);
            }

            // Reset counters for next window
            self.sampled_counter.store(0, Ordering::Relaxed);
            *window_start = Instant::now();
        }
    }
}

impl SamplingStrategy for AdaptiveSampler {
    fn should_sample(&self) -> bool {
        self.counter.fetch_add(1, Ordering::Relaxed);
        self.adjust_rate();

        let rate = self.current_rate.load(Ordering::Relaxed);
        let count = self.counter.load(Ordering::Relaxed);
        let should_sample = count % rate == 0;

        if should_sample {
            self.sampled_counter.fetch_add(1, Ordering::Relaxed);
        }

        should_sample
    }

    fn reset(&self) {
        self.counter.store(0, Ordering::Relaxed);
        self.sampled_counter.store(0, Ordering::Relaxed);
        self.current_rate.store(1, Ordering::Relaxed);
        *self.window_start.lock() = Instant::now();
    }

    fn stats(&self) -> SamplingStats {
        let total = self.counter.load(Ordering::Relaxed);
        let sampled = self.sampled_counter.load(Ordering::Relaxed);
        let rate = self.current_rate.load(Ordering::Relaxed);

        SamplingStats {
            total_events: total,
            sampled_events: sampled,
            sampling_rate: 1.0 / rate as f64,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_always_sample() {
        let sampler = AlwaysSample::new();

        for _ in 0..100 {
            assert!(sampler.should_sample());
        }

        let stats = sampler.stats();
        assert_eq!(stats.total_events, 100);
        assert_eq!(stats.sampled_events, 100);
        assert_eq!(stats.sampling_rate, 1.0);
    }

    #[test]
    fn test_never_sample() {
        let sampler = NeverSample::new();

        for _ in 0..100 {
            assert!(!sampler.should_sample());
        }

        let stats = sampler.stats();
        assert_eq!(stats.total_events, 100);
        assert_eq!(stats.sampled_events, 0);
        assert_eq!(stats.sampling_rate, 0.0);
    }

    #[test]
    fn test_probabilistic_sampler() {
        let sampler = ProbabilisticSampler::new(0.5);
        let mut sampled_count = 0;

        for _ in 0..1000 {
            if sampler.should_sample() {
                sampled_count += 1;
            }
        }

        let stats = sampler.stats();
        assert_eq!(stats.total_events, 1000);
        assert_eq!(stats.sampled_events, sampled_count);

        // Should be approximately 50% (with some tolerance for randomness)
        assert!(sampled_count > 400 && sampled_count < 600);
    }

    #[test]
    fn test_rate_sampler() {
        let sampler = RateSampler::new(10);
        let mut sampled_count = 0;

        for _ in 0..100 {
            if sampler.should_sample() {
                sampled_count += 1;
            }
        }

        let stats = sampler.stats();
        assert_eq!(stats.total_events, 100);
        assert_eq!(stats.sampled_events, 10); // Exactly 1 in 10
        assert_eq!(sampled_count, 10);
    }

    #[test]
    fn test_adaptive_sampler() {
        let sampler = AdaptiveSampler::new(100, Duration::from_millis(100));

        for _ in 0..1000 {
            sampler.should_sample();
        }

        let stats = sampler.stats();
        assert_eq!(stats.total_events, 1000);
        assert!(stats.sampled_events > 0);
    }

    #[test]
    fn test_sampler_reset() {
        let sampler = RateSampler::new(2);

        for _ in 0..10 {
            sampler.should_sample();
        }

        let stats_before = sampler.stats();
        assert_eq!(stats_before.total_events, 10);

        sampler.reset();

        let stats_after = sampler.stats();
        assert_eq!(stats_after.total_events, 0);
        assert_eq!(stats_after.sampled_events, 0);
    }
}
