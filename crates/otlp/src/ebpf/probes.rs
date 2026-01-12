//! 探针管理
//!
//! 管理 kprobes、uprobes 和 tracepoints

use crate::error::Result;
use crate::ebpf::error::EbpfError;

/// 探针类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProbeType {
    /// 内核函数探针
    KProbe,
    /// 用户空间函数探针
    UProbe,
    /// 跟踪点
    TracePoint,
}

/// 探针管理器
pub struct ProbeManager {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    probes: Vec<ProbeInfo>,
}

#[derive(Debug, Clone)]
struct ProbeInfo {
    probe_type: ProbeType,
    name: String,
    target: String,
    attached: bool,
}

impl ProbeManager {
    /// 创建新的探针管理器
    pub fn new() -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            probes: Vec::new(),
        }
    }

    /// 附加 kprobe
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_kprobe(&mut self, name: &str, function: &str) -> Result<()> {
        // TODO: 使用 aya 附加 kprobe
        // 实际实现需要:
        // 1. 创建 KProbe 程序
        // 2. 附加到内核函数
        // 3. 记录探针信息

        tracing::info!("KProbe 附加功能待实现: {} -> {}", name, function);

        self.probes.push(ProbeInfo {
            probe_type: ProbeType::KProbe,
            name: name.to_string(),
            target: function.to_string(),
            attached: false,
        });

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_kprobe(&mut self, _name: &str, _function: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 附加 uprobe
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_uprobe(&mut self, name: &str, binary: &str, symbol: &str) -> Result<()> {
        // TODO: 使用 aya 附加 uprobe
        tracing::info!("UProbe 附加功能待实现: {} -> {}:{}", name, binary, symbol);

        self.probes.push(ProbeInfo {
            probe_type: ProbeType::UProbe,
            name: name.to_string(),
            target: format!("{}:{}", binary, symbol),
            attached: false,
        });

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_uprobe(&mut self, _name: &str, _binary: &str, _symbol: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离所有探针
    pub fn detach_all(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            // TODO: 分离所有探针
            tracing::info!("分离 {} 个探针", self.probes.len());
            self.probes.clear();
        }

        Ok(())
    }
}

impl Default for ProbeManager {
    fn default() -> Self {
        Self::new()
    }
}
