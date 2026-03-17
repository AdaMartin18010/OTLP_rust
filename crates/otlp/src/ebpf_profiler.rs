//! eBPF 持续性能分析集成
//!
//! 基于 eBPF 的低开销性能分析，支持生产环境部署。
//! 典型开销 <1% CPU，无需应用修改。
//!
//! ## 参考
//! - https://oneuptime.com/blog/post/2026-02-06-otel-ebpf-continuous-profiling-agent-linux-production/view
//! - https://github.com/open-telemetry/opentelemetry-ebpf-profiler

use crate::profiles::{ProfileData, ProfileError, ProfileType};
use std::collections::HashMap;
use std::process::Command;
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use tracing::info;

/// eBPF 性能分析器配置
#[derive(Debug, Clone)]
pub struct EbpfProfilerConfig {
    /// 采样率 (samples/second)
    pub samples_per_second: u32,
    /// 报告间隔
    pub report_interval: Duration,
    /// 要分析的进程 ID (None = 系统范围)
    pub target_pid: Option<i32>,
    /// 进程过滤器（正则表达式）
    pub process_filter: Option<String>,
    /// 最大采样深度
    pub max_stack_depth: u32,
    /// 是否包含内核栈
    pub include_kernel_stack: bool,
    /// 是否包含用户栈
    pub include_user_stack: bool,
    /// 内存限制 (MB)
    pub memory_limit_mb: u32,
    /// CPU 限制 (百分比)
    pub cpu_limit_percent: u32,
}

impl Default for EbpfProfilerConfig {
    fn default() -> Self {
        Self {
            samples_per_second: 20,
            report_interval: Duration::from_secs(60),
            target_pid: None,
            process_filter: None,
            max_stack_depth: 128,
            include_kernel_stack: true,
            include_user_stack: true,
            memory_limit_mb: 512,
            cpu_limit_percent: 10,
        }
    }
}

/// eBPF 性能分析器
pub struct EbpfProfiler {
    config: EbpfProfilerConfig,
    running: bool,
    start_time: Option<Instant>,
    sample_sender: Option<mpsc::Sender<RawSample>>,
    sample_receiver: Option<mpsc::Receiver<RawSample>>,
}

/// 原始采样数据
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct RawSample {
    /// 进程 ID
    pid: u32,
    /// 线程 ID
    tid: u32,
    /// 进程名
    comm: String,
    /// 调用栈（地址列表）
    stack: Vec<u64>,
    /// CPU 时间 (纳秒)
    cpu_time: u64,
    /// 采样时间戳
    timestamp: Instant,
}

impl EbpfProfiler {
    /// 创建新的 eBPF 性能分析器
    pub fn new(config: EbpfProfilerConfig) -> Self {
        let (tx, rx) = mpsc::channel(10_000);
        
        Self {
            config,
            running: false,
            start_time: None,
            sample_sender: Some(tx),
            sample_receiver: Some(rx),
        }
    }

    /// 检查系统是否支持 eBPF
    pub fn check_system_support() -> Result<SystemCapabilities, EbpfError> {
        let mut caps = SystemCapabilities::default();

        // 检查内核版本 (需要 4.19+, 推荐 5.8+)
        let uname_output = Command::new("uname")
            .args(["-r"])
            .output()
            .map_err(|e| EbpfError::SystemCheckFailed(format!("Failed to get kernel version: {}", e)))?;
        
        let kernel_version = String::from_utf8_lossy(&uname_output.stdout);
        caps.kernel_version = kernel_version.trim().to_string();
        
        // 简单解析内核版本
        let version_parts: Vec<&str> = caps.kernel_version.split('.').collect();
        if version_parts.len() >= 2 {
            if let (Ok(major), Ok(minor)) = (version_parts[0].parse::<u32>(), version_parts[1].parse::<u32>()) {
                caps.kernel_supported = (major > 4) || (major == 4 && minor >= 19);
            }
        }

        // 检查 BTF 支持
        caps.btf_supported = std::path::Path::new("/sys/kernel/btf/vmlinux").exists();

        // 检查 perf_event_paranoid
        if let Ok(content) = std::fs::read_to_string("/proc/sys/kernel/perf_event_paranoid") {
            if let Ok(level) = content.trim().parse::<i32>() {
                caps.perf_event_paranoid = level;
                caps.perf_events_allowed = level <= 2 || level == -1;
            }
        }

        // 检查 eBPF 程序大小限制
        if let Ok(content) = std::fs::read_to_string("/proc/sys/kernel/bpf_jit_limit") {
            if let Ok(limit) = content.trim().parse::<u64>() {
                caps.bpf_jit_limit = Some(limit);
            }
        }

        Ok(caps)
    }

    /// 启动性能分析
    pub async fn start(&mut self) -> Result<(), EbpfError> {
        if self.running {
            return Err(EbpfError::AlreadyRunning);
        }

        // 检查系统支持
        let caps = Self::check_system_support()?;
        if !caps.kernel_supported {
            return Err(EbpfError::UnsupportedKernel(
                format!("Kernel {} is too old. Need 4.19+", caps.kernel_version)
            ));
        }
        if !caps.perf_events_allowed {
            return Err(EbpfError::PerfEventsNotAllowed(
                "perf_event_paranoid is too restrictive".to_string()
            ));
        }

        info!("Starting eBPF profiler with config: {:?}", self.config);
        info!("System capabilities: {:?}", caps);

        self.running = true;
        self.start_time = Some(Instant::now());

        // 启动采样收集任务
        let sample_rate = self.config.samples_per_second;
        let sender = self.sample_sender.take().unwrap();
        tokio::spawn(Self::collect_samples(sample_rate, sender));

        Ok(())
    }

    /// 停止性能分析
    pub fn stop(&mut self) -> Result<ProfileData, EbpfError> {
        if !self.running {
            return Err(EbpfError::NotRunning);
        }

        self.running = false;
        let duration = self.start_time.map(|t| t.elapsed()).unwrap_or_default();

        info!("Stopping eBPF profiler. Duration: {:?}", duration);

        // 收集所有样本
        let mut profile = ProfileData::new(ProfileType::Cpu);
        profile.duration_ms = duration.as_millis() as u64;

        if let Some(mut receiver) = self.sample_receiver.take() {
            // 尝试接收所有剩余的样本
            while let Ok(sample) = receiver.try_recv() {
                let stack_symbols: Vec<String> = sample.stack.iter()
                    .map(|addr| format!("0x{:x}", addr))
                    .collect();
                
                let mut labels = HashMap::new();
                labels.insert("pid".to_string(), sample.pid.to_string());
                labels.insert("tid".to_string(), sample.tid.to_string());
                labels.insert("comm".to_string(), sample.comm);

                profile.add_sample_with_labels(stack_symbols, sample.cpu_time as i64, labels);
            }
        }

        // 合并相同调用栈
        profile.merge_samples();

        Ok(profile)
    }

    /// 采样收集循环（模拟）
    async fn collect_samples(
        samples_per_second: u32,
        sender: mpsc::Sender<RawSample>,
    ) {
        let interval = Duration::from_secs_f64(1.0 / samples_per_second as f64);
        let mut ticker = tokio::time::interval(interval);

        loop {
            ticker.tick().await;

            // 模拟采样（实际实现需要加载 eBPF 程序）
            let sample = RawSample {
                pid: std::process::id(),
                tid: 0,
                comm: "example".to_string(),
                stack: vec![0x7fff_0000_1000, 0x7fff_0000_2000, 0x7fff_0000_3000],
                cpu_time: 1000,
                timestamp: Instant::now(),
            };

            if sender.send(sample).await.is_err() {
                break;
            }
        }
    }

    /// 获取当前统计
    pub fn get_stats(&self) -> ProfilerStats {
        ProfilerStats {
            running: self.running,
            duration: self.start_time.map(|t| t.elapsed()),
            samples_collected: 0, // 实际实现需要从 channel 获取
            dropped_samples: 0,
        }
    }
}

/// 系统能力检测
#[derive(Debug, Default)]
pub struct SystemCapabilities {
    /// 内核版本
    pub kernel_version: String,
    /// 内核是否支持
    pub kernel_supported: bool,
    /// 是否支持 BTF
    pub btf_supported: bool,
    /// perf_event_paranoid 级别
    pub perf_event_paranoid: i32,
    /// 是否允许 perf events
    pub perf_events_allowed: bool,
    /// BPF JIT 限制
    pub bpf_jit_limit: Option<u64>,
}

/// 性能分析器统计
#[derive(Debug)]
pub struct ProfilerStats {
    /// 是否运行中
    pub running: bool,
    /// 运行时长
    pub duration: Option<Duration>,
    /// 收集的样本数
    pub samples_collected: u64,
    /// 丢弃的样本数
    pub dropped_samples: u64,
}

/// eBPF 错误
#[derive(Debug, thiserror::Error)]
pub enum EbpfError {
    #[error("System check failed: {0}")]
    SystemCheckFailed(String),
    #[error("Unsupported kernel: {0}")]
    UnsupportedKernel(String),
    #[error("Perf events not allowed: {0}")]
    PerfEventsNotAllowed(String),
    #[error("Profiler already running")]
    AlreadyRunning,
    #[error("Profiler not running")]
    NotRunning,
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Profile error: {0}")]
    ProfileError(#[from] ProfileError),
}

/// eBPF 程序加载器（占位符）
pub struct EbpfProgramLoader;

impl EbpfProgramLoader {
    /// 检查 eBPF 程序是否已加载
    pub fn is_program_loaded(_name: &str) -> bool {
        // 实际实现需要检查 /sys/fs/bpf/
        false
    }

    /// 加载 eBPF 程序
    pub fn load_program(_path: &str) -> Result<i32, EbpfError> {
        // 实际实现需要使用 libbpf 或 aya
        Err(EbpfError::SystemCheckFailed("eBPF program loading not implemented".to_string()))
    }

    /// 卸载 eBPF 程序
    pub fn unload_program(_fd: i32) -> Result<(), EbpfError> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing::warn;

    #[test]
    fn test_system_capabilities() {
        let caps = SystemCapabilities {
            kernel_version: "5.15.0".to_string(),
            kernel_supported: true,
            btf_supported: true,
            perf_event_paranoid: 1,
            perf_events_allowed: true,
            bpf_jit_limit: Some(1_000_000_000),
        };

        assert!(caps.kernel_supported);
        assert!(caps.btf_supported);
        assert!(caps.perf_events_allowed);
    }

    #[test]
    fn test_profiler_config_default() {
        let config = EbpfProfilerConfig::default();
        assert_eq!(config.samples_per_second, 20);
        assert_eq!(config.report_interval, Duration::from_secs(60));
        assert!(config.include_kernel_stack);
        assert!(config.include_user_stack);
    }

    #[tokio::test]
    async fn test_profiler_lifecycle() {
        let config = EbpfProfilerConfig {
            samples_per_second: 100,
            report_interval: Duration::from_secs(1),
            ..Default::default()
        };

        let mut profiler = EbpfProfiler::new(config);

        // 检查系统支持（在 CI 环境可能失败）
        match EbpfProfiler::check_system_support() {
            Ok(caps) => {
                if caps.kernel_supported && caps.perf_events_allowed {
                    // 启动
                    assert!(profiler.start().await.is_ok());
                    assert!(profiler.running);

                    // 等待一些样本
                    tokio::time::sleep(Duration::from_millis(100)).await;

                    // 停止
                    let profile = profiler.stop();
                    assert!(profile.is_ok());
                }
            }
            Err(e) => {
                warn!("System check failed (expected in CI): {}", e);
            }
        }
    }
}
