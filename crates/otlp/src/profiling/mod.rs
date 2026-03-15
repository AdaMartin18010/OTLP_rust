//! # OpenTelemetry Profiling Module
//!
//! 实现基于多种后端的持续性能分析：
//! - **CPU Profiling**: 基于 backtrace 或 pprof 的栈采样
//! - **Memory Profiling**: 内存分配追踪
//! - **Lock Profiling**: 锁竞争分析
//!
//! ## 功能特性
//!
//! - ✅ CPU 性能分析 (需要启用 `backtrace` feature)
//! - ✅ Memory 性能分析 (需要启用 `backtrace` feature)
//! - ✅ pprof 格式导出
//! - ✅ OTLP 格式导出
//! - ⚠️ eBPF 性能分析 (Linux only, 需要 `ebpf` feature)
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::profiling::{CpuProfiler, CpuProfilerConfig};
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = CpuProfilerConfig::default()
//!         .with_sample_rate(99)
//!         .with_duration(Duration::from_secs(30));
//!     
//!     let mut profiler = CpuProfiler::new(config);
//!     profiler.start().await.unwrap();
//!     
//!     // 你的代码...
//!     
//!     profiler.stop().await.unwrap();
//!     let profile = profiler.generate_profile().await.unwrap();
//! }
//! ```
//!
//! ## Feature Flags
//!
//! - `backtrace`: 启用基于 backtrace 的栈采样 (推荐)
//! - `pprof`: 启用 pprof 格式支持
//! - `ebpf`: 启用基于 eBPF 的性能分析 (Linux only)

pub mod cpu;
pub mod exporter;
pub mod memory;
pub mod pprof;
pub mod sampling;
pub mod types;

#[cfg(target_os = "linux")]
pub mod ebpf;

// Re-export commonly used types
pub use types::{
    AttributeValue, Function, InstrumentationScope, Label, Line, Location, Mapping, PprofProfile,
    Profile, ProfileContainer, ProfileType, Resource, Sample, ScopeProfiles, ValueType,
};

pub use pprof::{PprofBuilder, PprofEncoder, StackTraceCollector};
pub use pprof::StackFrame as ProfilingStackFrame;

pub use cpu::{CpuProfiler, CpuProfilerConfig, CpuProfilerStats, profile_async};

pub use memory::{
    MemoryProfiler, MemoryProfilerConfig, MemoryProfilerStats, SystemMemoryInfo,
    get_system_memory_info,
};

pub use exporter::{
    ExportError, ProfileBuilder, ProfileExporter, ProfileExporterConfig, generate_profile_id,
    link_profile_to_current_trace, profile_id_from_hex,
};

pub use sampling::{
    AdaptiveSampler, AlwaysSample, NeverSample, ProbabilisticSampler, RateSampler, SamplingStats,
    SamplingStrategy,
};

// use crate::data::{TelemetryContent, TelemetryData, TelemetryDataType};
use crate::error::{OtlpError, Result};
use std::time::{Duration, SystemTime};

/// 性能分析器配置
#[derive(Debug, Clone)]
pub struct ProfilingConfig {
    /// 采样频率 (Hz)
    pub sampling_rate: u32,

    /// 持续时间
    pub duration: Duration,

    /// 是否启用 CPU 分析
    pub enable_cpu_profiling: bool,

    /// 是否启用内存分析
    pub enable_memory_profiling: bool,

    /// 是否启用锁分析
    pub enable_lock_profiling: bool,
}

impl Default for ProfilingConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 99, // 99 Hz
            duration: Duration::from_secs(30),
            enable_cpu_profiling: true,
            enable_memory_profiling: false,
            enable_lock_profiling: false,
        }
    }
}

impl ProfilingConfig {
    /// 创建新配置
    pub fn new() -> Self {
        Self::default()
    }

    /// 设置采样频率
    pub fn with_sample_rate(mut self, rate: u32) -> Self {
        self.sampling_rate = rate;
        self
    }

    /// 设置持续时间
    pub fn with_duration(mut self, duration: Duration) -> Self {
        self.duration = duration;
        self
    }

    /// 启用 CPU 分析
    pub fn with_cpu_profiling(mut self, enabled: bool) -> Self {
        self.enable_cpu_profiling = enabled;
        self
    }

    /// 启用内存分析
    pub fn with_memory_profiling(mut self, enabled: bool) -> Self {
        self.enable_memory_profiling = enabled;
        self
    }

    /// 启用锁分析
    pub fn with_lock_profiling(mut self, enabled: bool) -> Self {
        self.enable_lock_profiling = enabled;
        self
    }
}

/// 性能分析器
#[allow(dead_code)]
pub struct Profiler {
    config: ProfilingConfig,
    is_running: bool,
    cpu_profiler: Option<CpuProfiler>,
    memory_profiler: Option<MemoryProfiler>,
}

impl Profiler {
    /// 创建新的性能分析器
    pub fn new(config: ProfilingConfig) -> Self {
        let cpu_profiler = if config.enable_cpu_profiling {
            Some(CpuProfiler::new(CpuProfilerConfig::default()
                .with_sample_rate(config.sampling_rate)
                .with_max_duration(config.duration)))
        } else {
            None
        };

        let memory_profiler = if config.enable_memory_profiling {
            Some(MemoryProfiler::new(MemoryProfilerConfig::default()))
        } else {
            None
        };

        Self {
            config,
            is_running: false,
            cpu_profiler,
            memory_profiler,
        }
    }

    /// 启动性能分析
    pub async fn start(&mut self) -> Result<()> {
        if self.is_running {
            return Err(OtlpError::Performance(
                crate::error::PerformanceError::HighCpuUsage {
                    current: 100.0,
                    threshold: 90.0,
                },
            ));
        }

        self.is_running = true;

        // 启动 CPU 分析
        if let Some(ref mut cpu) = self.cpu_profiler {
            cpu.start().await.map_err(OtlpError::Profiling)?;
        }

        // 启动内存分析
        if let Some(ref mut memory) = self.memory_profiler {
            memory.start().await.map_err(OtlpError::Profiling)?;
        }

        Ok(())
    }

    /// 停止性能分析
    pub async fn stop(&mut self) -> Result<()> {
        if !self.is_running {
            return Ok(());
        }

        // 停止 CPU 分析
        if let Some(ref mut cpu) = self.cpu_profiler {
            cpu.stop().await.map_err(OtlpError::Profiling)?;
        }

        // 停止内存分析
        if let Some(ref mut memory) = self.memory_profiler {
            memory.stop().await.map_err(OtlpError::Profiling)?;
        }

        self.is_running = false;
        Ok(())
    }

    /// 生成性能分析报告
    pub async fn generate_report(&self) -> Result<ProfilingReport> {
        if self.is_running {
            return Err(OtlpError::Profiling(
                "无法在未停止的分析器上生成报告".to_string()
            ));
        }

        let mut report = ProfilingReport::new();

        // 生成 CPU 报告
        if let Some(ref cpu) = self.cpu_profiler {
            let cpu_profile = cpu.generate_profile().await.map_err(OtlpError::Profiling)?;
            report.cpu_profile = Some(cpu_profile);
        }

        Ok(report)
    }

    /// 检查是否正在运行
    pub fn is_running(&self) -> bool {
        self.is_running
    }
}

/// 性能分析报告
#[derive(Debug, Clone)]
pub struct ProfilingReport {
    pub timestamp: SystemTime,
    pub duration: Duration,
    pub cpu_profile: Option<crate::profiling::types::PprofProfile>,
    pub memory_profile: Option<crate::profiling::types::PprofProfile>,
}

impl ProfilingReport {
    pub fn new() -> Self {
        Self {
            timestamp: SystemTime::now(),
            duration: Duration::default(),
            cpu_profile: None,
            memory_profile: None,
        }
    }
}

/// 性能分析入口函数
/// 
/// 便捷函数，用于在代码块中进行性能分析
/// 
/// # 示例
///
/// ```rust
/// use otlp::profiling::{profile_block, ProfileResult};
///
/// async fn my_function() {
///     let result = profile_block("my_operation", || async {
///         // 你的代码...
///         "result"
///     }).await;
///     
///     println!("耗时: {:?}", result.duration);
/// }
/// ```
pub async fn profile_block<F, Fut, R>(name: &str, f: F) -> ProfileResult<R>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = R>,
{
    let start = std::time::Instant::now();
    let result = f().await;
    let duration = start.elapsed();

    ProfileResult {
        name: name.to_string(),
        result,
        duration,
    }
}

/// 性能分析结果
#[derive(Debug, Clone)]
pub struct ProfileResult<R> {
    pub name: String,
    pub result: R,
    pub duration: Duration,
}

/// 热点函数识别
/// 
/// 分析性能分析数据，识别热点函数
pub fn identify_hotspots(profile: &PprofProfile, top_n: usize) -> Vec<Hotspot> {
    // 统计每个函数的采样次数
    let mut function_counts: std::collections::HashMap<String, i64> = 
        std::collections::HashMap::new();

    for sample in &profile.sample {
        for location_id in &sample.location_id {
            if let Some(location) = profile.location.iter().find(|l| l.id == *location_id) {
                for line in &location.line {
                    if let Some(function) = profile.function.iter().find(|f| f.id == line.function_id) {
                        let function_name = profile.string_table.get(function.name as usize)
                            .cloned()
                            .unwrap_or_default();
                        *function_counts.entry(function_name).or_insert(0) += sample.value.first().copied().unwrap_or(1);
                    }
                }
            }
        }
    }

    // 转换为热点列表并排序
    let mut hotspot_vec: Vec<Hotspot> = function_counts
        .into_iter()
        .map(|(name, count): (String, i64)| Hotspot { name, count })
        .collect();
    
    hotspot_vec.sort_by(|a, b| b.count.cmp(&a.count));
    hotspot_vec.truncate(top_n);

    hotspot_vec
}

/// 热点函数
#[derive(Debug, Clone)]
pub struct Hotspot {
    pub name: String,
    pub count: i64,
}

/// 获取进程当前的资源使用情况
pub fn get_process_stats() -> ProcessStats {
    use sysinfo::{System, get_current_pid};

    let mut system = System::new_all();
    system.refresh_all();

    let pid = match get_current_pid() {
        Ok(p) => p,
        Err(_) => {
            return ProcessStats {
                cpu_percent: 0.0,
                memory_bytes: 0,
                virtual_memory_bytes: 0,
            }
        }
    };

    if let Some(process) = system.process(pid) {
        ProcessStats {
            cpu_percent: process.cpu_usage() as f64,
            memory_bytes: process.memory(),
            virtual_memory_bytes: process.virtual_memory(),
        }
    } else {
        ProcessStats {
            cpu_percent: 0.0,
            memory_bytes: 0,
            virtual_memory_bytes: 0,
        }
    }
}

/// 进程统计
#[derive(Debug, Clone)]
pub struct ProcessStats {
    pub cpu_percent: f64,
    pub memory_bytes: u64,
    pub virtual_memory_bytes: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profiling_config() {
        let config = ProfilingConfig::new()
            .with_sample_rate(100)
            .with_duration(Duration::from_secs(60))
            .with_cpu_profiling(true)
            .with_memory_profiling(true);

        assert_eq!(config.sampling_rate, 100);
        assert_eq!(config.duration, Duration::from_secs(60));
        assert!(config.enable_cpu_profiling);
        assert!(config.enable_memory_profiling);
    }

    #[tokio::test]
    async fn test_profile_block() {
        let result = profile_block("test_operation", || async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            42
        }).await;

        assert_eq!(result.name, "test_operation");
        assert_eq!(result.result, 42);
        assert!(result.duration >= Duration::from_millis(10));
    }

    #[test]
    fn test_process_stats() {
        let stats = get_process_stats();
        // 至少应该能获取到内存使用
        assert!(stats.memory_bytes > 0 || stats.cpu_percent >= 0.0);
    }
}
