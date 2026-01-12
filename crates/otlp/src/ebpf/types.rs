//! eBPF 数据类型定义

use std::time::Duration;

/// eBPF 配置
#[derive(Debug, Clone)]
pub struct EbpfConfig {
    /// 是否启用 CPU 性能分析
    pub enable_cpu_profiling: bool,
    /// 是否启用网络追踪
    pub enable_network_tracing: bool,
    /// 是否启用系统调用追踪
    pub enable_syscall_tracing: bool,
    /// 是否启用内存分配追踪
    pub enable_memory_tracing: bool,
    /// 采样频率 (Hz)
    pub sample_rate: u32,
    /// 采样持续时间
    pub duration: Duration,
    /// 最大采样数
    pub max_samples: usize,
}

impl Default for EbpfConfig {
    fn default() -> Self {
        Self {
            enable_cpu_profiling: true,
            enable_network_tracing: false,
            enable_syscall_tracing: false,
            enable_memory_tracing: false,
            sample_rate: 99, // 默认 99Hz，符合 2025 年标准
            duration: Duration::from_secs(60),
            max_samples: 100000,
        }
    }
}

impl EbpfConfig {
    /// 创建新配置
    pub fn new() -> Self {
        Self::default()
    }

    /// 设置采样频率
    pub fn with_sample_rate(mut self, rate: u32) -> Self {
        self.sample_rate = rate;
        self
    }

    /// 设置采样持续时间
    pub fn with_duration(mut self, duration: Duration) -> Self {
        self.duration = duration;
        self
    }

    /// 启用网络追踪
    pub fn with_network_tracing(mut self, enabled: bool) -> Self {
        self.enable_network_tracing = enabled;
        self
    }

    /// 启用系统调用追踪
    pub fn with_syscall_tracing(mut self, enabled: bool) -> Self {
        self.enable_syscall_tracing = enabled;
        self
    }

    /// 启用内存追踪
    pub fn with_memory_tracing(mut self, enabled: bool) -> Self {
        self.enable_memory_tracing = enabled;
        self
    }

    /// 设置最大采样数
    pub fn with_max_samples(mut self, max: usize) -> Self {
        self.max_samples = max;
        self
    }

    /// 验证配置
    pub fn validate(&self) -> crate::error::Result<()> {
        crate::ebpf::utils::validate_config(self)
    }
}

/// eBPF 事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EbpfEventType {
    /// CPU 采样事件
    CpuSample,
    /// 网络包事件
    NetworkPacket,
    /// 系统调用事件
    Syscall,
    /// 内存分配事件
    MemoryAlloc,
    /// 内存释放事件
    MemoryFree,
}

/// eBPF 事件
#[derive(Debug, Clone)]
pub struct EbpfEvent {
    /// 事件类型
    pub event_type: EbpfEventType,
    /// 时间戳
    pub timestamp: Duration,
    /// 进程 ID
    pub pid: u32,
    /// 线程 ID
    pub tid: u32,
    /// 事件数据
    pub data: Vec<u8>,
}

impl EbpfEvent {
    /// 创建新事件
    pub fn new(
        event_type: EbpfEventType,
        pid: u32,
        tid: u32,
        data: Vec<u8>,
    ) -> Self {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default();

        Self {
            event_type,
            timestamp,
            pid,
            tid,
            data,
        }
    }
}

/// eBPF 性能开销指标
#[derive(Debug, Clone)]
pub struct EbpfOverheadMetrics {
    /// CPU 开销百分比
    pub cpu_percent: f64,
    /// 内存开销 (字节)
    pub memory_bytes: usize,
    /// 事件处理延迟 (微秒)
    pub event_latency_us: u64,
}

impl Default for EbpfOverheadMetrics {
    fn default() -> Self {
        Self {
            cpu_percent: 0.0,
            memory_bytes: 0,
            event_latency_us: 0,
        }
    }
}
