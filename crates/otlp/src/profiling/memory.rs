//! # Memory Profiler
//!
//! This module provides memory profiling capabilities.
//! It tracks memory allocations and provides insights into memory usage patterns.
//!
//! ## Features
//!
//! - System memory information
//! - Process memory tracking
//! - Memory allocation profiling (requires `backtrace` feature)

use super::types::{PprofProfile, ProfileType};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

/// Memory profiler configuration
#[derive(Debug, Clone)]
pub struct MemoryProfilerConfig {
    /// Sampling interval
    pub sampling_interval: Duration,

    /// Maximum tracking duration
    pub max_duration: Duration,

    /// Track allocation stacks
    pub track_allocation_stacks: bool,
}

impl Default for MemoryProfilerConfig {
    fn default() -> Self {
        Self {
            sampling_interval: Duration::from_secs(1),
            max_duration: Duration::from_secs(300),
            track_allocation_stacks: true,
        }
    }
}

impl MemoryProfilerConfig {
    /// Create a new configuration
    pub fn new() -> Self {
        Self::default()
    }

    /// Set sampling interval
    pub fn with_sampling_interval(mut self, interval: Duration) -> Self {
        self.sampling_interval = interval;
        self
    }

    /// Set max duration
    pub fn with_max_duration(mut self, duration: Duration) -> Self {
        self.max_duration = duration;
        self
    }

    /// Enable/disable allocation stack tracking
    pub fn with_allocation_stacks(mut self, enabled: bool) -> Self {
        self.track_allocation_stacks = enabled;
        self
    }
}

/// Memory profiler
pub struct MemoryProfiler {
    config: MemoryProfilerConfig,
    is_running: Arc<std::sync::atomic::AtomicBool>,
    sample_count: Arc<AtomicU64>,
    stats: Arc<Mutex<MemoryStats>>,
    start_time: Option<Instant>,
}

/// Memory statistics
#[derive(Debug, Clone, Default)]
pub struct MemoryStats {
    pub total_allocated: u64,
    pub total_freed: u64,
    pub peak_usage: u64,
    pub current_usage: u64,
    pub allocation_count: u64,
    pub free_count: u64,
    pub sample_count: u64,
}

impl MemoryStats {
    /// Calculate average allocation size
    pub fn average_allocation_size(&self) -> f64 {
        if self.allocation_count == 0 {
            0.0
        } else {
            self.total_allocated as f64 / self.allocation_count as f64
        }
    }

    /// Calculate allocation rate (bytes per allocation)
    pub fn allocation_rate(&self) -> f64 {
        if self.allocation_count == 0 {
            0.0
        } else {
            self.total_allocated as f64 / self.allocation_count as f64
        }
    }
}

impl MemoryProfiler {
    /// Create a new memory profiler
    pub fn new(config: MemoryProfilerConfig) -> Self {
        Self {
            config,
            is_running: Arc::new(std::sync::atomic::AtomicBool::new(false)),
            sample_count: Arc::new(AtomicU64::new(0)),
            stats: Arc::new(Mutex::new(MemoryStats::default())),
            start_time: None,
        }
    }

    /// Start profiling
    pub async fn start(&mut self) -> Result<(), String> {
        if self.is_running.load(Ordering::SeqCst) {
            return Err("Profiler is already running".to_string());
        }

        self.is_running.store(true, Ordering::SeqCst);
        self.start_time = Some(Instant::now());

        // Start sampling task
        self.spawn_sampling_task().await;

        Ok(())
    }

    /// Stop profiling
    pub async fn stop(&mut self) -> Result<(), String> {
        if !self.is_running.load(Ordering::SeqCst) {
            return Err("Profiler is not running".to_string());
        }

        self.is_running.store(false, Ordering::SeqCst);

        Ok(())
    }

    /// Check if profiler is running
    pub fn is_running(&self) -> bool {
        self.is_running.load(Ordering::SeqCst)
    }

    /// Get current memory stats
    pub async fn get_stats(&self) -> MemoryStats {
        let mut stats = self.stats.lock().await.clone();
        stats.sample_count = self.sample_count.load(Ordering::SeqCst);
        stats
    }

    /// Record a manual allocation
    pub async fn record_allocation(&self, size: usize) {
        let mut stats = self.stats.lock().await;
        stats.allocation_count += 1;
        stats.total_allocated += size as u64;
        stats.current_usage += size as u64;
        if stats.current_usage > stats.peak_usage {
            stats.peak_usage = stats.current_usage;
        }
        drop(stats);
        self.sample_count.fetch_add(1, Ordering::SeqCst);
    }

    /// Record a manual deallocation
    pub async fn record_deallocation(&self, size: usize) {
        let mut stats = self.stats.lock().await;
        stats.free_count += 1;
        stats.total_freed += size as u64;
        if stats.current_usage >= size as u64 {
            stats.current_usage -= size as u64;
        }
    }

    /// Spawn the sampling task
    async fn spawn_sampling_task(&self) {
        let is_running = Arc::clone(&self.is_running);
        let sample_count = Arc::clone(&self.sample_count);
        let stats = Arc::clone(&self.stats);
        let interval = self.config.sampling_interval;
        let max_duration = self.config.max_duration;
        let start_time = Instant::now();

        tokio::spawn(async move {
            let mut ticker = tokio::time::interval(interval);

            while is_running.load(Ordering::SeqCst) {
                ticker.tick().await;

                // Check if max duration exceeded
                if start_time.elapsed() >= max_duration {
                    is_running.store(false, Ordering::SeqCst);
                    break;
                }

                // Collect memory sample
                let memory_info = get_system_memory_info();

                // Update stats
                let mut stats_guard = stats.lock().await;
                stats_guard.current_usage = memory_info.used;
                if memory_info.used > stats_guard.peak_usage {
                    stats_guard.peak_usage = memory_info.used;
                }
                drop(stats_guard);

                sample_count.fetch_add(1, Ordering::SeqCst);
            }
        });
    }

    /// Generate a pprof profile from collected samples
    pub async fn generate_profile(&self) -> Result<PprofProfile, String> {
        if self.is_running() {
            return Err("Cannot generate profile while profiler is running".to_string());
        }

        use super::pprof::PprofBuilder;

        let mut builder = PprofBuilder::new(ProfileType::Memory);

        // Add comment with profiler info
        builder.add_comment(&format!(
            "Memory Profile: {} samples",
            self.sample_count.load(Ordering::SeqCst)
        ));

        // Calculate duration
        let duration = self
            .start_time
            .map(|start| start.elapsed())
            .unwrap_or_default();
        builder.set_duration(duration.as_nanos() as i64);

        Ok(builder.build())
    }
}

/// System memory information
#[derive(Debug, Clone, Default)]
pub struct SystemMemoryInfo {
    pub total: u64,
    pub used: u64,
    pub free: u64,
    pub available: u64,
    pub buffers: u64,
    pub cached: u64,
    pub swap_total: u64,
    pub swap_used: u64,
    pub swap_free: u64,
}

/// Get system memory information
pub fn get_system_memory_info() -> SystemMemoryInfo {
    use sysinfo::System;

    let mut system = System::new_all();
    system.refresh_memory();

    SystemMemoryInfo {
        total: system.total_memory(),
        used: system.used_memory(),
        free: system.free_memory(),
        available: system.available_memory(),
        buffers: 0, // sysinfo doesn't provide this directly
        cached: 0,  // sysinfo doesn't provide this directly
        swap_total: system.total_swap(),
        swap_used: system.used_swap(),
        swap_free: system.free_swap(),
    }
}

/// Memory profiler statistics
#[derive(Debug, Clone, Default)]
pub struct MemoryProfilerStats {
    pub sample_count: u64,
    pub total_samples_bytes: u64,
    pub peak_memory_bytes: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_profiler_config() {
        let config = MemoryProfilerConfig::new()
            .with_sampling_interval(Duration::from_millis(500))
            .with_max_duration(Duration::from_secs(60));

        assert_eq!(config.sampling_interval, Duration::from_millis(500));
        assert_eq!(config.max_duration, Duration::from_secs(60));
    }

    #[test]
    fn test_system_memory_info() {
        let info = get_system_memory_info();

        // Should have some memory
        assert!(info.total > 0, "Total memory should be greater than 0");

        // Used + free should equal total (approximately)
        let sum = info.used + info.free;
        let diff = sum.abs_diff(info.total);
        assert!(
            diff < info.total / 10,
            "Used + free should approximate total"
        );
    }

    #[tokio::test]
    async fn test_memory_profiler_lifecycle() {
        let mut profiler = MemoryProfiler::new(MemoryProfilerConfig::default());

        // Start profiling
        assert!(profiler.start().await.is_ok());
        assert!(profiler.is_running());

        // Wait a bit
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Stop profiling
        assert!(profiler.stop().await.is_ok());
        assert!(!profiler.is_running());

        // Generate profile
        let profile = profiler.generate_profile().await;
        assert!(profile.is_ok());
    }
}
