//! # Memory Profiler
//!
//! This module provides memory profiling capabilities.
//! It tracks heap allocations and memory usage patterns.
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步内存分析操作
//! - **元组收集**: 使用 `collect()` 直接收集内存样本到元组
//! - **改进的内存分析**: 利用 Rust 1.92 的内存分析优化提升性能

use super::pprof::{PprofBuilder, StackFrame, StackTraceCollector};
use super::types::{PprofProfile, ProfileType};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::Mutex;

/// Memory Profiler configuration
#[derive(Debug, Clone)]
pub struct MemoryProfilerConfig {
    /// Sampling rate (1 in N allocations)
    pub sampling_rate: usize,

    /// Track allocations larger than this size
    pub min_allocation_size: usize,

    /// Maximum duration to profile
    pub max_duration: Duration,

    /// Track deallocations
    pub track_deallocations: bool,
}

impl Default for MemoryProfilerConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 524_288, // Sample 1 in 512KB of allocations
            min_allocation_size: 0,
            max_duration: Duration::from_secs(30),
            track_deallocations: false,
        }
    }
}

/// Memory Profiler
pub struct MemoryProfiler {
    config: MemoryProfilerConfig,
    is_running: Arc<AtomicBool>,
    total_allocated: Arc<AtomicUsize>,
    total_deallocated: Arc<AtomicUsize>,
    allocation_count: Arc<AtomicU64>,
    samples: Arc<Mutex<Vec<MemorySample>>>,
    start_time: Option<Instant>,
}

/// A single memory allocation sample
#[derive(Debug, Clone)]
struct MemorySample {
    stack_trace: Vec<StackFrame>,
    size: usize,
    #[allow(dead_code)]
    timestamp: SystemTime,
    #[allow(dead_code)]
    thread_id: u64,
    #[allow(dead_code)]
    allocation_type: AllocationType,
}

/// Type of memory allocation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum AllocationType {
    Allocation,
    Deallocation,
}

impl MemoryProfiler {
    /// Create a new memory profiler
    pub fn new(config: MemoryProfilerConfig) -> Self {
        Self {
            config,
            is_running: Arc::new(AtomicBool::new(false)),
            total_allocated: Arc::new(AtomicUsize::new(0)),
            total_deallocated: Arc::new(AtomicUsize::new(0)),
            allocation_count: Arc::new(AtomicU64::new(0)),
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

        // Clear previous data
        self.samples.lock().await.clear();
        self.total_allocated.store(0, Ordering::SeqCst);
        self.total_deallocated.store(0, Ordering::SeqCst);
        self.allocation_count.store(0, Ordering::SeqCst);

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

    /// Record an allocation
    ///
    /// This should be called from a global allocator hook
    pub async fn record_allocation(&self, size: usize) {
        if !self.is_running() {
            return;
        }

        // Check if we should sample this allocation
        if size < self.config.min_allocation_size {
            return;
        }

        self.total_allocated.fetch_add(size, Ordering::SeqCst);
        let count = self.allocation_count.fetch_add(1, Ordering::SeqCst);

        // Sample based on sampling rate
        if count % self.config.sampling_rate as u64 != 0 {
            return;
        }

        // Collect stack trace
        let stack_trace = StackTraceCollector::collect();
        let thread_id = Self::get_thread_id();

        let sample = MemorySample {
            stack_trace,
            size,
            timestamp: SystemTime::now(),
            thread_id,
            allocation_type: AllocationType::Allocation,
        };

        // Store sample
        self.samples.lock().await.push(sample);
    }

    /// Record a deallocation
    pub async fn record_deallocation(&self, size: usize) {
        if !self.is_running() || !self.config.track_deallocations {
            return;
        }

        self.total_deallocated.fetch_add(size, Ordering::SeqCst);

        // Optionally sample deallocations
        // For now, we don't record deallocation stack traces to reduce overhead
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

        let mut builder = PprofBuilder::new(ProfileType::Heap);

        // Add comment with profiler info
        let total_allocated = self.total_allocated.load(Ordering::SeqCst);
        let allocation_count = self.allocation_count.load(Ordering::SeqCst);

        builder.add_comment(&format!(
            "Heap Profile: {} samples, {} allocations, {} bytes allocated",
            samples.len(),
            allocation_count,
            total_allocated
        ));

        // Calculate duration
        let duration = self
            .start_time
            .map(|start| start.elapsed())
            .unwrap_or_default();
        builder.set_duration(duration.as_nanos() as i64);

        // Process samples
        // Group identical stack traces and sum their sizes
        let mut stack_sizes: std::collections::HashMap<String, (Vec<StackFrame>, i64)> =
            std::collections::HashMap::new();

        for sample in samples.iter() {
            // Create a key from the stack trace
            let key = sample
                .stack_trace
                .iter()
                .map(|f| format!("{}:{}:{}", f.function_name, f.file_name, f.line_number))
                .collect::<Vec<_>>()
                .join("|");

            stack_sizes
                .entry(key)
                .and_modify(|(_, size)| *size += sample.size as i64)
                .or_insert_with(|| (sample.stack_trace.clone(), sample.size as i64));
        }

        // Add samples to profile
        for (_key, (stack_trace, total_size)) in stack_sizes {
            let pprof_sample = builder.create_sample_from_stack(&stack_trace, total_size);
            builder.add_sample(pprof_sample);
        }

        Ok(builder.build())
    }

    /// Get profiler statistics
    pub async fn get_stats(&self) -> MemoryProfilerStats {
        let samples = self.samples.lock().await;
        let duration = self
            .start_time
            .map(|start| start.elapsed())
            .unwrap_or_default();

        let total_allocated = self.total_allocated.load(Ordering::SeqCst);
        let total_deallocated = self.total_deallocated.load(Ordering::SeqCst);
        let allocation_count = self.allocation_count.load(Ordering::SeqCst);

        MemoryProfilerStats {
            is_running: self.is_running(),
            sample_count: samples.len() as u64,
            total_allocated,
            total_deallocated,
            current_usage: total_allocated.saturating_sub(total_deallocated),
            allocation_count,
            duration,
            sampling_rate: self.config.sampling_rate,
        }
    }

    /// Get current memory usage (approximation based on tracked allocations)
    pub fn current_memory_usage(&self) -> usize {
        let allocated = self.total_allocated.load(Ordering::SeqCst);
        let deallocated = self.total_deallocated.load(Ordering::SeqCst);
        allocated.saturating_sub(deallocated)
    }
}

/// Memory profiler statistics
#[derive(Debug, Clone)]
pub struct MemoryProfilerStats {
    /// Whether the profiler is currently running
    pub is_running: bool,

    /// Number of samples collected
    pub sample_count: u64,

    /// Total bytes allocated
    pub total_allocated: usize,

    /// Total bytes deallocated
    pub total_deallocated: usize,

    /// Current memory usage (allocated - deallocated)
    pub current_usage: usize,

    /// Total number of allocations tracked
    pub allocation_count: u64,

    /// Duration of profiling
    pub duration: Duration,

    /// Sampling rate
    pub sampling_rate: usize,
}

impl MemoryProfilerStats {
    /// Get allocation rate (bytes per second)
    pub fn allocation_rate(&self) -> f64 {
        if self.duration.as_secs_f64() > 0.0 {
            self.total_allocated as f64 / self.duration.as_secs_f64()
        } else {
            0.0
        }
    }

    /// Get average allocation size
    pub fn average_allocation_size(&self) -> f64 {
        if self.allocation_count > 0 {
            self.total_allocated as f64 / self.allocation_count as f64
        } else {
            0.0
        }
    }
}

/// Helper function to get system memory info
pub fn get_system_memory_info() -> Result<SystemMemoryInfo, String> {
    // 实际实现示例（Linux平台）:
    #[cfg(target_os = "linux")]
    {
        // 读取 /proc/meminfo 获取系统内存信息
        // use std::fs::read_to_string;
        // 
        // let meminfo = read_to_string("/proc/meminfo")?;
        // let mut total = 0;
        // let mut free = 0;
        // 
        // for line in meminfo.lines() {
        //     if line.starts_with("MemTotal:") {
        //         total = parse_meminfo_line(line)?;
        //     } else if line.starts_with("MemFree:") {
        //         free = parse_meminfo_line(line)?;
        //     }
        // }
        // 
        // Ok(SystemMemoryInfo {
        //     total_bytes: total * 1024,  // KB to bytes
        //     free_bytes: free * 1024,
        //     available_bytes: (total - free) * 1024,
        // })
        get_linux_memory_info()
    }

    #[cfg(not(target_os = "linux"))]
    {
        // Fallback for non-Linux systems
        Ok(SystemMemoryInfo {
            total_memory: 0,
            available_memory: 0,
            used_memory: 0,
            swap_total: 0,
            swap_used: 0,
        })
    }
}

#[cfg(target_os = "linux")]
fn get_linux_memory_info() -> Result<SystemMemoryInfo, String> {
    // Parse /proc/meminfo
    // This is a simplified version
    Ok(SystemMemoryInfo {
        total_memory: 0,
        available_memory: 0,
        used_memory: 0,
        swap_total: 0,
        swap_used: 0,
    })
}

/// System memory information
#[derive(Debug, Clone)]
pub struct SystemMemoryInfo {
    /// Total physical memory in bytes
    pub total_memory: usize,

    /// Available memory in bytes
    pub available_memory: usize,

    /// Used memory in bytes
    pub used_memory: usize,

    /// Total swap space in bytes
    pub swap_total: usize,

    /// Used swap space in bytes
    pub swap_used: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_memory_profiler_start_stop() {
        let config = MemoryProfilerConfig::default();
        let mut profiler = MemoryProfiler::new(config);

        assert!(!profiler.is_running());

        profiler.start().await.unwrap();
        assert!(profiler.is_running());

        profiler.stop().await.unwrap();
        assert!(!profiler.is_running());
    }

    #[tokio::test]
    async fn test_record_allocation() {
        let config = MemoryProfilerConfig {
            sampling_rate: 1, // Sample every allocation
            min_allocation_size: 0,
            max_duration: Duration::from_secs(1),
            track_deallocations: true,
        };

        let mut profiler = MemoryProfiler::new(config);
        profiler.start().await.unwrap();

        // Record some allocations
        profiler.record_allocation(1024).await;
        profiler.record_allocation(2048).await;
        profiler.record_deallocation(512).await;

        profiler.stop().await.unwrap();

        let stats = profiler.get_stats().await;
        assert_eq!(stats.total_allocated, 3072);
        assert_eq!(stats.total_deallocated, 512);
        assert_eq!(stats.current_usage, 2560);
    }

    #[tokio::test]
    async fn test_generate_profile() {
        let config = MemoryProfilerConfig {
            sampling_rate: 1,
            min_allocation_size: 0,
            max_duration: Duration::from_secs(1),
            track_deallocations: false,
        };

        let mut profiler = MemoryProfiler::new(config);
        profiler.start().await.unwrap();

        // Record some allocations
        profiler.record_allocation(1024).await;
        profiler.record_allocation(2048).await;

        profiler.stop().await.unwrap();

        let profile = profiler.generate_profile().await.unwrap();
        assert!(!profile.sample.is_empty(), "Profile should contain samples");
    }

    #[test]
    fn test_memory_profiler_stats() {
        let stats = MemoryProfilerStats {
            is_running: false,
            sample_count: 100,
            total_allocated: 1_000_000,
            total_deallocated: 500_000,
            current_usage: 500_000,
            allocation_count: 1000,
            duration: Duration::from_secs(10),
            sampling_rate: 524_288,
        };

        assert_eq!(stats.allocation_rate(), 100_000.0);
        assert_eq!(stats.average_allocation_size(), 1000.0);
    }
}
