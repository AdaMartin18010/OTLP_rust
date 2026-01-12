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

    /// 附加 kprobe（内核函数探针）
    ///
    /// # 参数
    ///
    /// * `name` - 探针名称（用于标识）
    /// * `function` - 要追踪的内核函数名
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// kprobe 用于在内核函数入口处插入探针，可以追踪内核函数的调用。
    /// 需要 CAP_BPF 权限。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::ProbeManager;
    ///
    /// let mut manager = ProbeManager::new();
    /// manager.attach_kprobe("tcp_connect", "tcp_v4_connect")?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_kprobe(&mut self, name: &str, function: &str) -> Result<()> {
        // 验证函数名
        if function.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "函数名不能为空".to_string(),
            )
            .into());
        }

        tracing::info!("附加 KProbe: {} -> {}", name, function);

        // 注意: 实际的 kprobe 附加需要:
        // 1. 使用 aya::programs::kprobe::KProbe
        // 2. 加载并附加到内核函数:
        //    let program: &mut KProbe = bpf.program_mut(name)?;
        //    program.load()?;
        //    program.attach(function, 0)?;
        // 3. 记录探针信息

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        self.probes.push(ProbeInfo {
            probe_type: ProbeType::KProbe,
            name: name.to_string(),
            target: function.to_string(),
            attached: false, // 实际附加后应设置为 true
        });

        tracing::debug!("KProbe 已注册: {} -> {}", name, function);
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_kprobe(&mut self, _name: &str, _function: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 附加 uprobe（用户空间函数探针）
    ///
    /// # 参数
    ///
    /// * `name` - 探针名称（用于标识）
    /// * `binary` - 目标二进制文件路径
    /// * `symbol` - 要追踪的函数符号名
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// uprobe 用于在用户空间函数入口处插入探针，可以追踪用户程序的函数调用。
    /// 需要 CAP_BPF 权限。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::ProbeManager;
    ///
    /// let mut manager = ProbeManager::new();
    /// manager.attach_uprobe("malloc_probe", "/usr/bin/myapp", "malloc")?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_uprobe(&mut self, name: &str, binary: &str, symbol: &str) -> Result<()> {
        // 验证参数
        if binary.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "二进制文件路径不能为空".to_string(),
            )
            .into());
        }
        if symbol.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "符号名不能为空".to_string(),
            )
            .into());
        }

        // 检查二进制文件是否存在
        if !std::path::Path::new(binary).exists() {
            tracing::warn!("二进制文件不存在: {}", binary);
            // 不直接返回错误，因为可能是动态路径
        }

        tracing::info!("附加 UProbe: {} -> {}:{}", name, binary, symbol);

        // 注意: 实际的 uprobe 附加需要:
        // 1. 使用 aya::programs::uprobe::UProbe
        // 2. 加载并附加到用户空间函数:
        //    let program: &mut UProbe = bpf.program_mut(name)?;
        //    program.load()?;
        //    program.attach(Some(binary), symbol, 0, None)?;
        // 3. 记录探针信息

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        self.probes.push(ProbeInfo {
            probe_type: ProbeType::UProbe,
            name: name.to_string(),
            target: format!("{}:{}", binary, symbol),
            attached: false, // 实际附加后应设置为 true
        });

        tracing::debug!("UProbe 已注册: {} -> {}:{}", name, binary, symbol);
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_uprobe(&mut self, _name: &str, _binary: &str, _symbol: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 附加 tracepoint（跟踪点）
    ///
    /// # 参数
    ///
    /// * `name` - 探针名称（用于标识）
    /// * `category` - 跟踪点类别（如 "syscalls"）
    /// * `event` - 跟踪点事件名（如 "sys_enter_openat"）
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// tracepoint 是内核预定义的静态跟踪点，比 kprobe 更稳定，性能开销更小。
    /// 不需要 CAP_BPF 权限（但需要 CAP_SYS_ADMIN 或 root）。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::ProbeManager;
    ///
    /// let mut manager = ProbeManager::new();
    /// manager.attach_tracepoint("openat_trace", "syscalls", "sys_enter_openat")?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_tracepoint(&mut self, name: &str, category: &str, event: &str) -> Result<()> {
        // 验证参数
        if category.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "跟踪点类别不能为空".to_string(),
            )
            .into());
        }
        if event.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "跟踪点事件名不能为空".to_string(),
            )
            .into());
        }

        tracing::info!("附加 Tracepoint: {} -> {}:{}", name, category, event);

        // 注意: 实际的 tracepoint 附加需要:
        // 1. 使用 aya::programs::trace_point::TracePoint
        // 2. 加载并附加到跟踪点:
        //    let program: &mut TracePoint = bpf.program_mut(name)?;
        //    program.load()?;
        //    program.attach(category, event)?;
        // 3. 记录探针信息

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        self.probes.push(ProbeInfo {
            probe_type: ProbeType::TracePoint,
            name: name.to_string(),
            target: format!("{}:{}", category, event),
            attached: false, // 实际附加后应设置为 true
        });

        tracing::debug!("Tracepoint 已注册: {} -> {}:{}", name, category, event);
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_tracepoint(&mut self, _name: &str, _category: &str, _event: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离指定探针
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn detach(&mut self, name: &str) -> Result<()> {
        // TODO: 分离指定探针
        let initial_len = self.probes.len();
        self.probes.retain(|p| p.name != name);

        if self.probes.len() < initial_len {
            tracing::info!("分离探针: {}", name);
            Ok(())
        } else {
            Err(EbpfError::AttachFailed(format!("探针不存在: {}", name)).into())
        }
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn detach(&mut self, _name: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离所有探针
    pub fn detach_all(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            // TODO: 分离所有探针
            let count = self.probes.len();
            tracing::info!("分离 {} 个探针", count);
            self.probes.clear();
        }

        Ok(())
    }

    /// 获取探针列表
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn list_probes(&self) -> Vec<(String, ProbeType, String, bool)> {
        self.probes
            .iter()
            .map(|p| (p.name.clone(), p.probe_type, p.target.clone(), p.attached))
            .collect()
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn list_probes(&self) -> Vec<(String, ProbeType, String, bool)> {
        vec![]
    }

    /// 获取探针数量
    pub fn probe_count(&self) -> usize {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.probes.len()
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            0
        }
    }
}

impl Default for ProbeManager {
    fn default() -> Self {
        Self::new()
    }
}
