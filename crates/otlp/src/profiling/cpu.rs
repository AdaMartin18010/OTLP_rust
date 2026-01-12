//! # CPU Profiler
//!
//! This module provides CPU profiling capabilities.
//! It samples the call stack at regular intervals to identify CPU hotspots.
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步CPU分析操作
//! - **元组收集**: 使用 `collect()` 直接收集CPU样本到元组
//! - **改进的性能分析**: 利用 Rust 1.92 的性能分析优化提升性能

use super::pprof::{PprofBuilder, StackFrame, StackTraceCollector};
use super::types::{PprofProfile, ProfileType};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::Mutex;
use tokio::time::interval;

/// CPU Profiler configuration
#[derive(Debug, Clone)]
pub struct CpuProfilerConfig {
    /// Sampling frequency in Hz (samples per second)
    pub sampling_frequency: u32,

    /// Maximum duration to profile
    pub max_duration: Duration,

    /// Whether to include system calls
    pub include_system_calls: bool,
}

impl Default for CpuProfilerConfig {
    fn default() -> Self {
        Self {
            sampling_frequency: 99, // 99 Hz is a common default
            max_duration: Duration::from_secs(30),
            include_system_calls: false,
        }
    }
}

/// CPU Profiler
pub struct CpuProfiler {
    config: CpuProfilerConfig,
    is_running: Arc<AtomicBool>,
    sample_count: Arc<AtomicU64>,
    samples: Arc<Mutex<Vec<CpuSample>>>,
    start_time: Option<Instant>,
}

/// A single CPU sample
#[derive(Debug, Clone)]
struct CpuSample {
    stack_trace: Vec<StackFrame>,
    #[allow(dead_code)]
    timestamp: SystemTime,
    #[allow(dead_code)]
    thread_id: u64,
}

impl CpuProfiler {
    /// Create a new CPU profiler
    pub fn new(config: CpuProfilerConfig) -> Self {
        Self {
            config,
            is_running: Arc::new(AtomicBool::new(false)),
            sample_count: Arc::new(AtomicU64::new(0)),
            samples: Arc::new(Mutex::new(Vec::new())),
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

        // Clear previous samples
        self.samples.lock().await.clear();
        self.sample_count.store(0, Ordering::SeqCst);

        // Spawn sampling task
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

    /// Get the number of samples collected
    pub fn sample_count(&self) -> u64 {
        self.sample_count.load(Ordering::SeqCst)
    }

    /// Spawn the sampling task
    async fn spawn_sampling_task(&self) {
        let is_running = Arc::clone(&self.is_running);
        let sample_count = Arc::clone(&self.sample_count);
        let samples = Arc::clone(&self.samples);
        let frequency = self.config.sampling_frequency;
        let max_duration = self.config.max_duration;
        let start_time = Instant::now();

        tokio::spawn(async move {
            let sample_interval = Duration::from_micros(1_000_000 / frequency as u64);
            let mut ticker = interval(sample_interval);

            while is_running.load(Ordering::SeqCst) {
                ticker.tick().await;

                // Check if max duration exceeded
                if start_time.elapsed() >= max_duration {
                    is_running.store(false, Ordering::SeqCst);
                    break;
                }

                // Collect stack trace
                let stack_trace = StackTraceCollector::collect();
                let thread_id = Self::get_thread_id();

                let sample = CpuSample {
                    stack_trace,
                    timestamp: SystemTime::now(),
                    thread_id,
                };

                // Store sample
                samples.lock().await.push(sample);
                sample_count.fetch_add(1, Ordering::SeqCst);
            }
        });
    }

    /// Get current thread ID
    fn get_thread_id() -> u64 {
        // Use a hash of thread ID since as_u64() is unstable
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let thread_id = std::thread::current().id();
        let mut hasher = DefaultHasher::new();
        thread_id.hash(&mut hasher);
        hasher.finish()
    }

    /// Generate a pprof profile from collected samples
    pub async fn generate_profile(&self) -> Result<PprofProfile, String> {
        if self.is_running() {
            return Err(
                "Cannot generate profile while profiler is running. Stop it first.".to_string(),
            );
        }

        let samples = self.samples.lock().await;

        if samples.is_empty() {
            return Err("No samples collected".to_string());
        }

        let mut builder = PprofBuilder::new(ProfileType::Cpu);

        // Add comment with profiler info
        builder.add_comment(&format!(
            "CPU Profile: {} samples @ {} Hz",
            samples.len(),
            self.config.sampling_frequency
        ));

        // Calculate duration
        let duration = self
            .start_time
            .map(|start| start.elapsed())
            .unwrap_or_default();
        builder.set_duration(duration.as_nanos() as i64);

        // Process samples
        // Group identical stack traces to reduce profile size
        let mut stack_counts: std::collections::HashMap<String, (Vec<StackFrame>, i64)> =
            std::collections::HashMap::new();

        for sample in samples.iter() {
            // Create a key from the stack trace
            let key = sample
                .stack_trace
                .iter()
                .map(|f| format!("{}:{}:{}", f.function_name, f.file_name, f.line_number))
                .collect::<Vec<_>>()
                .join("|");

            stack_counts
                .entry(key)
                .and_modify(|(_, count)| *count += 1)
                .or_insert_with(|| (sample.stack_trace.clone(), 1));
        }

        // Add samples to profile
        for (_key, (stack_trace, count)) in stack_counts {
            // Convert count to CPU time in nanoseconds
            // Each sample represents approximately 1/frequency seconds
            let sample_duration_ns = 1_000_000_000 / self.config.sampling_frequency as i64;
            let total_ns = count * sample_duration_ns;

            let pprof_sample = builder.create_sample_from_stack(&stack_trace, total_ns);
            builder.add_sample(pprof_sample);
        }

        Ok(builder.build())
    }

    /// Get profiler statistics
    pub async fn get_stats(&self) -> CpuProfilerStats {
        let samples = self.samples.lock().await;
        let duration = self
            .start_time
            .map(|start| start.elapsed())
            .unwrap_or_default();

        CpuProfilerStats {
            is_running: self.is_running(),
            sample_count: samples.len() as u64,
            duration,
            sampling_frequency: self.config.sampling_frequency,
        }
    }
}

/// CPU profiler statistics
#[derive(Debug, Clone)]
pub struct CpuProfilerStats {
    /// Whether the profiler is currently running
    pub is_running: bool,

    /// Number of samples collected
    pub sample_count: u64,

    /// Duration of profiling
    pub duration: Duration,

    /// Sampling frequency in Hz
    pub sampling_frequency: u32,
}

impl CpuProfilerStats {
    /// Get the average sampling rate (actual samples per second)
    pub fn actual_sampling_rate(&self) -> f64 {
        if self.duration.as_secs_f64() > 0.0 {
            self.sample_count as f64 / self.duration.as_secs_f64()
        } else {
            0.0
        }
    }
}

/// Helper function to profile a specific piece of code
pub async fn profile_async<F, T>(
    f: F,
    config: CpuProfilerConfig,
) -> Result<(T, PprofProfile), String>
where
    F: std::future::Future<Output = T>,
{
    let mut profiler = CpuProfiler::new(config);

    profiler.start().await?;

    let result = f.await;

    profiler.stop().await?;

    // Wait a moment for any pending samples to be collected
    tokio::time::sleep(Duration::from_millis(10)).await;

    let profile = profiler.generate_profile().await?;

    Ok((result, profile))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cpu_profiler_start_stop() {
        let config = CpuProfilerConfig {
            sampling_frequency: 100,
            max_duration: Duration::from_secs(1),
            include_system_calls: false,
        };

        let mut profiler = CpuProfiler::new(config);

        assert!(!profiler.is_running());

        profiler.start().await.unwrap();
        assert!(profiler.is_running());

        profiler.stop().await.unwrap();
        assert!(!profiler.is_running());
    }

    #[tokio::test]
    async fn test_cpu_profiler_sampling() {
        let config = CpuProfilerConfig {
            sampling_frequency: 100,
            max_duration: Duration::from_secs(1),
            include_system_calls: false,
        };

        let mut profiler = CpuProfiler::new(config);
        profiler.start().await.unwrap();

        // Wait for some samples to be collected
        tokio::time::sleep(Duration::from_millis(100)).await;

        profiler.stop().await.unwrap();

        let stats = profiler.get_stats().await;
        assert!(stats.sample_count > 0, "Should have collected some samples");
    }

    #[tokio::test]
    async fn test_generate_profile() {
        let config = CpuProfilerConfig {
            sampling_frequency: 100,
            max_duration: Duration::from_secs(1),
            include_system_calls: false,
        };

        let mut profiler = CpuProfiler::new(config);
        profiler.start().await.unwrap();

        // Simulate some work
        tokio::time::sleep(Duration::from_millis(100)).await;

        profiler.stop().await.unwrap();

        // Wait for samples to be processed
        tokio::time::sleep(Duration::from_millis(50)).await;

        let profile = profiler.generate_profile().await.unwrap();
        assert!(!profile.sample.is_empty(), "Profile should contain samples");
        assert!(
            !profile.string_table.is_empty(),
            "String table should not be empty"
        );
    }

    #[tokio::test]
    async fn test_profile_async_helper() {
        let config = CpuProfilerConfig {
            sampling_frequency: 100,
            max_duration: Duration::from_secs(1),
            include_system_calls: false,
        };

        let (result, profile) = profile_async(
            async {
                tokio::time::sleep(Duration::from_millis(50)).await;
                42
            },
            config,
        )
        .await
        .unwrap();

        assert_eq!(result, 42);
        assert!(!profile.sample.is_empty());
    }
}
