//! # OpenTelemetry Profiling Module
//!
//! This module provides comprehensive profiling support for OpenTelemetry,
//! including CPU profiling, memory profiling, and various sampling strategies.
//!
//! ## Features
//!
//! - **CPU Profiling**: Sample call stacks to identify CPU hotspots
//! - **Memory Profiling**: Track heap allocations and memory usage
//! - **pprof Format**: Industry-standard profile format support
//! - **OTLP Export**: Export profiles to OTLP collectors
//! - **Sampling Strategies**: Multiple sampling strategies (always, probabilistic, rate-based, adaptive)
//! - **Trace Correlation**: Link profiles to distributed traces
//!
//! ## Quick Start
//!
//! ```rust,ignore
//! use otlp::profiling::{CpuProfiler, CpuProfilerConfig};
//!
//! #[tokio::main]
//! async fn main() {
//!     let mut profiler = CpuProfiler::new(CpuProfilerConfig::default());
//!
//!     profiler.start().await.unwrap();
//!
//!     // Your code here
//!
//!     profiler.stop().await.unwrap();
//!     let profile = profiler.generate_profile().await.unwrap();
//! }
//! ```

// Re-export main types and modules
pub mod cpu;
#[cfg(target_os = "linux")]
pub mod ebpf;
pub mod exporter;
pub mod memory;
pub mod pprof;
pub mod sampling;
pub mod types;

// Re-export commonly used types
pub use types::{
    AttributeValue, Function, InstrumentationScope, Label, Line, Location, Mapping, PprofProfile,
    Profile, ProfileContainer, ProfileType, Resource, Sample, ScopeProfiles, ValueType,
};

pub use pprof::{PprofBuilder, PprofEncoder, StackTraceCollector};
// Re-export StackFrame from pprof module
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

use crate::data::{TelemetryContent, TelemetryData, TelemetryDataType};
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

/// 性能分析器
pub struct Profiler {
    config: ProfilingConfig,
    is_running: bool,
}

impl Profiler {
    /// 创建新的性能分析器
    pub fn new(config: ProfilingConfig) -> Self {
        Self {
            config,
            is_running: false,
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

        // 启动分析任务
        if self.config.enable_cpu_profiling {
            self.start_cpu_profiling().await?;
        }

        if self.config.enable_memory_profiling {
            self.start_memory_profiling().await?;
        }

        if self.config.enable_lock_profiling {
            self.start_lock_profiling().await?;
        }

        Ok(())
    }

    /// 停止性能分析
    pub async fn stop(&mut self) -> Result<()> {
        if !self.is_running {
            return Err(OtlpError::Performance(
                crate::error::PerformanceError::HighCpuUsage {
                    current: 0.0,
                    threshold: 10.0,
                },
            ));
        }

        self.is_running = false;
        Ok(())
    }

    /// 启动 CPU 性能分析
    async fn start_cpu_profiling(&self) -> Result<()> {
        // 模拟 CPU 性能分析启动
        // 实际实现中这里会加载 eBPF 程序
        println!(
            "启动 CPU 性能分析，采样频率: {} Hz",
            self.config.sampling_rate
        );
        Ok(())
    }

    /// 启动内存性能分析
    async fn start_memory_profiling(&self) -> Result<()> {
        // 模拟内存性能分析启动
        println!("启动内存性能分析");
        Ok(())
    }

    /// 启动锁性能分析
    async fn start_lock_profiling(&self) -> Result<()> {
        // 模拟锁性能分析启动
        println!("启动锁性能分析");
        Ok(())
    }

    /// 收集性能数据
    pub async fn collect_data(&self) -> Result<Vec<TelemetryData>> {
        if !self.is_running {
            return Err(OtlpError::Performance(
                crate::error::PerformanceError::HighCpuUsage {
                    current: 0.0,
                    threshold: 10.0,
                },
            ));
        }

        let mut data = Vec::new();

        // 收集 CPU 性能数据
        if self.config.enable_cpu_profiling {
            if let Some(cpu_data) = self.collect_cpu_data().await? {
                data.push(cpu_data);
            }
        }

        // 收集内存性能数据
        if self.config.enable_memory_profiling {
            if let Some(memory_data) = self.collect_memory_data().await? {
                data.push(memory_data);
            }
        }

        // 收集锁性能数据
        if self.config.enable_lock_profiling {
            if let Some(lock_data) = self.collect_lock_data().await? {
                data.push(lock_data);
            }
        }

        Ok(data)
    }

    /// 收集 CPU 性能数据
    async fn collect_cpu_data(&self) -> Result<Option<TelemetryData>> {
        // 模拟 CPU 数据收集
        // 实际实现中这里会从 eBPF 程序收集数据

        let cpu_sample = CpuSample {
            timestamp: SystemTime::now(),
            stack_trace: vec![
                StackFrame {
                    function_name: "main".to_string(),
                    file_name: "main.rs".to_string(),
                    line_number: 42,
                    address: 0x12345678,
                },
                StackFrame {
                    function_name: "process_data".to_string(),
                    file_name: "processor.rs".to_string(),
                    line_number: 128,
                    address: 0x87654321,
                },
            ],
            cpu_id: 0,
            process_id: std::process::id(),
            thread_id: 0,
        };

        let cpu_data = CpuProfileData {
            samples: vec![cpu_sample],
            duration: Duration::from_millis(100),
            sampling_rate: self.config.sampling_rate,
        };

        let profile_data = ProfileData::Cpu(cpu_data);
        let telemetry_data = self.create_profile_telemetry_data(profile_data)?;

        Ok(Some(telemetry_data))
    }

    /// 收集内存性能数据
    async fn collect_memory_data(&self) -> Result<Option<TelemetryData>> {
        // 模拟内存数据收集
        let heap_sample = HeapSample {
            timestamp: SystemTime::now(),
            stack_trace: vec![StackFrame {
                function_name: "allocate_memory".to_string(),
                file_name: "allocator.rs".to_string(),
                line_number: 56,
                address: 0x11111111,
            }],
            size: 1024,
            process_id: std::process::id(),
            thread_id: 0,
        };

        let heap_data = HeapProfileData {
            samples: vec![heap_sample],
            duration: Duration::from_millis(100),
            sampling_rate: self.config.sampling_rate,
        };

        let profile_data = ProfileData::Heap(heap_data);
        let telemetry_data = self.create_profile_telemetry_data(profile_data)?;

        Ok(Some(telemetry_data))
    }

    /// 收集锁性能数据
    async fn collect_lock_data(&self) -> Result<Option<TelemetryData>> {
        // 模拟锁数据收集
        let lock_sample = LockSample {
            timestamp: SystemTime::now(),
            stack_trace: vec![StackFrame {
                function_name: "acquire_lock".to_string(),
                file_name: "lock.rs".to_string(),
                line_number: 89,
                address: 0x22222222,
            }],
            lock_address: 0x33333333,
            duration: Duration::from_micros(500),
            process_id: std::process::id(),
            thread_id: 0,
        };

        let lock_data = LockProfileData {
            samples: vec![lock_sample],
            duration: Duration::from_millis(100),
            sampling_rate: self.config.sampling_rate,
        };

        let profile_data = ProfileData::Lock(lock_data);
        let telemetry_data = self.create_profile_telemetry_data(profile_data)?;

        Ok(Some(telemetry_data))
    }

    /// 创建性能遥测数据
    fn create_profile_telemetry_data(&self, _profile_data: ProfileData) -> Result<TelemetryData> {
        // 将性能数据转换为遥测数据
        // 这里使用指标数据来承载性能信息

        let metric_data = crate::data::MetricData {
            name: "profile_data".to_string(),
            description: "Performance profiling data".to_string(),
            unit: "samples".to_string(),
            metric_type: crate::data::MetricType::Counter,
            data_points: vec![crate::data::DataPoint {
                timestamp: SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_nanos() as u64,
                attributes: std::collections::HashMap::new(),
                value: crate::data::DataPointValue::Number(1.0),
            }],
        };

        Ok(TelemetryData::new(
            TelemetryDataType::Metric,
            TelemetryContent::Metric(metric_data),
        ))
    }

    /// 获取分析器状态
    pub fn is_running(&self) -> bool {
        self.is_running
    }

    /// 获取配置
    pub fn config(&self) -> &ProfilingConfig {
        &self.config
    }

    /// 获取性能统计
    pub async fn get_performance_stats(&self) -> Result<PerformanceStats> {
        if !self.is_running {
            return Err(OtlpError::Performance(
                crate::error::PerformanceError::HighCpuUsage {
                    current: 0.0,
                    threshold: 10.0,
                },
            ));
        }

        let cpu_usage = self.get_cpu_usage().await?;
        let memory_usage = self.get_memory_usage().await?;
        let lock_contention = self.get_lock_contention().await?;

        Ok(PerformanceStats {
            cpu_usage,
            memory_usage,
            lock_contention,
            timestamp: SystemTime::now(),
        })
    }

    /// 获取CPU使用率
    async fn get_cpu_usage(&self) -> Result<f64> {
        // 模拟CPU使用率获取
        Ok(45.2)
    }

    /// 获取内存使用情况
    async fn get_memory_usage(&self) -> Result<MemoryUsage> {
        // 模拟内存使用情况获取
        Ok(MemoryUsage {
            heap_size: 1024 * 1024 * 100, // 100MB
            heap_used: 1024 * 1024 * 60,  // 60MB
            stack_size: 1024 * 1024 * 10, // 10MB
            gc_cycles: 5,
        })
    }

    /// 获取锁竞争情况
    async fn get_lock_contention(&self) -> Result<f64> {
        // 模拟锁竞争率获取
        Ok(12.5)
    }

    /// 生成性能报告
    pub async fn generate_report(&self) -> Result<PerformanceReport> {
        if !self.is_running {
            return Err(OtlpError::Performance(
                crate::error::PerformanceError::HighCpuUsage {
                    current: 0.0,
                    threshold: 10.0,
                },
            ));
        }

        let stats = self.get_performance_stats().await?;
        let hotspots = self.identify_hotspots().await?;
        let recommendations = self.generate_recommendations(&stats, &hotspots).await?;

        Ok(PerformanceReport {
            stats,
            hotspots,
            recommendations,
            generated_at: SystemTime::now(),
        })
    }

    /// 识别性能热点
    async fn identify_hotspots(&self) -> Result<Vec<Hotspot>> {
        // 模拟热点识别
        Ok(vec![
            Hotspot {
                function_name: "process_data".to_string(),
                file_name: "processor.rs".to_string(),
                line_number: 128,
                cpu_time_percent: 35.2,
                memory_allocations: 1024,
                call_count: 10000,
            },
            Hotspot {
                function_name: "serialize_json".to_string(),
                file_name: "serializer.rs".to_string(),
                line_number: 45,
                cpu_time_percent: 28.7,
                memory_allocations: 512,
                call_count: 5000,
            },
        ])
    }

    /// 生成性能优化建议
    async fn generate_recommendations(
        &self,
        stats: &PerformanceStats,
        hotspots: &[Hotspot],
    ) -> Result<Vec<Recommendation>> {
        let mut recommendations = Vec::new();

        // CPU使用率建议
        if stats.cpu_usage > 80.0 {
            recommendations.push(Recommendation {
                category: RecommendationCategory::Cpu,
                priority: RecommendationPriority::High,
                title: "高CPU使用率".to_string(),
                description: "CPU使用率过高，建议优化热点函数".to_string(),
                action: "考虑使用缓存或算法优化".to_string(),
            });
        }

        // 内存使用建议
        if stats.memory_usage.heap_used as f64 / stats.memory_usage.heap_size as f64 > 0.8 {
            recommendations.push(Recommendation {
                category: RecommendationCategory::Memory,
                priority: RecommendationPriority::Medium,
                title: "高内存使用率".to_string(),
                description: "堆内存使用率过高".to_string(),
                action: "考虑增加内存或优化内存分配".to_string(),
            });
        }

        // 锁竞争建议
        if stats.lock_contention > 20.0 {
            recommendations.push(Recommendation {
                category: RecommendationCategory::Concurrency,
                priority: RecommendationPriority::High,
                title: "高锁竞争".to_string(),
                description: "锁竞争率过高，影响并发性能".to_string(),
                action: "考虑使用无锁数据结构或减少锁粒度".to_string(),
            });
        }

        // 热点函数建议
        for hotspot in hotspots {
            if hotspot.cpu_time_percent > 30.0 {
                recommendations.push(Recommendation {
                    category: RecommendationCategory::Cpu,
                    priority: RecommendationPriority::High,
                    title: format!("热点函数: {}", hotspot.function_name),
                    description: format!(
                        "函数 {} 占用CPU时间 {}%",
                        hotspot.function_name, hotspot.cpu_time_percent
                    ),
                    action: "考虑优化算法或使用更高效的数据结构".to_string(),
                });
            }
        }

        Ok(recommendations)
    }
}

/// 性能数据类型
#[derive(Debug, Clone)]
pub enum ProfileDataType {
    Cpu,
    Heap,
    Lock,
    Wall,
    Goroutine,
}

/// 性能数据
#[derive(Debug, Clone)]
pub enum ProfileData {
    Cpu(CpuProfileData),
    Heap(HeapProfileData),
    Lock(LockProfileData),
    Wall(WallProfileData),
    Goroutine(GoroutineProfileData),
}

/// CPU 性能数据
#[derive(Debug, Clone)]
pub struct CpuProfileData {
    pub samples: Vec<CpuSample>,
    pub duration: Duration,
    pub sampling_rate: u32,
}

/// CPU 样本
#[derive(Debug, Clone)]
pub struct CpuSample {
    pub timestamp: SystemTime,
    pub stack_trace: Vec<StackFrame>,
    pub cpu_id: u32,
    pub process_id: u32,
    pub thread_id: u32,
}

/// 堆性能数据
#[derive(Debug, Clone)]
pub struct HeapProfileData {
    pub samples: Vec<HeapSample>,
    pub duration: Duration,
    pub sampling_rate: u32,
}

/// 堆样本
#[derive(Debug, Clone)]
pub struct HeapSample {
    pub timestamp: SystemTime,
    pub stack_trace: Vec<StackFrame>,
    pub size: usize,
    pub process_id: u32,
    pub thread_id: u32,
}

/// 锁性能数据
#[derive(Debug, Clone)]
pub struct LockProfileData {
    pub samples: Vec<LockSample>,
    pub duration: Duration,
    pub sampling_rate: u32,
}

/// 锁样本
#[derive(Debug, Clone)]
pub struct LockSample {
    pub timestamp: SystemTime,
    pub stack_trace: Vec<StackFrame>,
    pub lock_address: u64,
    pub duration: Duration,
    pub process_id: u32,
    pub thread_id: u32,
}

/// 墙时间性能数据
#[derive(Debug, Clone)]
pub struct WallProfileData {
    pub samples: Vec<WallSample>,
    pub duration: Duration,
    pub sampling_rate: u32,
}

/// 墙时间样本
#[derive(Debug, Clone)]
pub struct WallSample {
    pub timestamp: SystemTime,
    pub stack_trace: Vec<StackFrame>,
    pub process_id: u32,
    pub thread_id: u32,
}

/// Goroutine 性能数据
#[derive(Debug, Clone)]
pub struct GoroutineProfileData {
    pub samples: Vec<GoroutineSample>,
    pub duration: Duration,
    pub sampling_rate: u32,
}

/// Goroutine 样本
#[derive(Debug, Clone)]
pub struct GoroutineSample {
    pub timestamp: SystemTime,
    pub stack_trace: Vec<StackFrame>,
    pub goroutine_id: u64,
    pub state: String,
}

/// 堆栈帧
#[derive(Debug, Clone)]
pub struct StackFrame {
    pub function_name: String,
    pub file_name: String,
    pub line_number: u32,
    pub address: u64,
}

/// 性能统计
#[derive(Debug, Clone)]
pub struct PerformanceStats {
    pub cpu_usage: f64,
    pub memory_usage: MemoryUsage,
    pub lock_contention: f64,
    pub timestamp: SystemTime,
}

/// 内存使用情况
#[derive(Debug, Clone)]
pub struct MemoryUsage {
    pub heap_size: usize,
    pub heap_used: usize,
    pub stack_size: usize,
    pub gc_cycles: u32,
}

/// 性能热点
#[derive(Debug, Clone)]
pub struct Hotspot {
    pub function_name: String,
    pub file_name: String,
    pub line_number: u32,
    pub cpu_time_percent: f64,
    pub memory_allocations: usize,
    pub call_count: u64,
}

/// 性能报告
#[derive(Debug, Clone)]
pub struct PerformanceReport {
    pub stats: PerformanceStats,
    pub hotspots: Vec<Hotspot>,
    pub recommendations: Vec<Recommendation>,
    pub generated_at: SystemTime,
}

/// 性能优化建议
#[derive(Debug, Clone)]
pub struct Recommendation {
    pub category: RecommendationCategory,
    pub priority: RecommendationPriority,
    pub title: String,
    pub description: String,
    pub action: String,
}

/// 建议类别
#[derive(Debug, Clone)]
pub enum RecommendationCategory {
    Cpu,
    Memory,
    Concurrency,
    Network,
    Io,
    Algorithm,
}

/// 建议优先级
#[derive(Debug, Clone)]
pub enum RecommendationPriority {
    Low,
    Medium,
    High,
    Critical,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_profiler_start_stop() {
        let config = ProfilingConfig::default();
        let mut profiler = Profiler::new(config);

        // 启动分析器
        assert!(profiler.start().await.is_ok());
        assert!(profiler.is_running());

        // 停止分析器
        assert!(profiler.stop().await.is_ok());
        assert!(!profiler.is_running());
    }

    #[tokio::test]
    async fn test_profiler_double_start() {
        let config = ProfilingConfig::default();
        let mut profiler = Profiler::new(config);

        // 第一次启动应该成功
        assert!(profiler.start().await.is_ok());

        // 第二次启动应该失败
        assert!(profiler.start().await.is_err());
    }

    #[tokio::test]
    async fn test_profiler_collect_data() {
        let config = ProfilingConfig::default();
        let mut profiler = Profiler::new(config);

        // 未启动时收集数据应该失败
        assert!(profiler.collect_data().await.is_err());

        // 启动后收集数据应该成功
        assert!(profiler.start().await.is_ok());
        let data = profiler
            .collect_data()
            .await
            .expect("Failed to collect profiler data");
        assert!(!data.is_empty());
    }
}
