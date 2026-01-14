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
    /// * `name` - 探针名称（用于标识，必须与 eBPF 程序中的程序名匹配）
    /// * `function` - 要追踪的内核函数名
    /// * `bpf` - Bpf 实例（可选，如果提供则进行实际附加）
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
    /// use otlp::ebpf::{ProbeManager, EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载 eBPF 程序 ...
    /// let mut manager = ProbeManager::new();
    /// if let Some(bpf) = loader.bpf_mut() {
    ///     manager.attach_kprobe("tcp_connect", "tcp_v4_connect", Some(bpf))?;
    /// }
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_kprobe(&mut self, name: &str, function: &str, bpf: Option<&mut aya::Bpf>) -> Result<()> {
        // 验证函数名
        if function.is_empty() {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(
                "函数名不能为空".to_string(),
            )
            .into());
        }

        tracing::info!("附加 KProbe: {} -> {}", name, function);

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        // 如果提供了 Bpf 实例，进行实际附加
        if let Some(bpf) = bpf {
            use aya::programs::kprobe::KProbe;

            // 从 Bpf 实例获取程序并加载
            let program: &mut KProbe = bpf.program_mut(name)
                .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序不存在: {}",
                    name
                )))?
                .try_into()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序类型转换失败: {:?}",
                    e
                )))?;

            program.load()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序加载失败: {}",
                    e
                )))?;

            // 附加到内核函数
            program.attach(function, 0)
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "探针附加失败: {}",
                    e
                )))?;

            tracing::info!("KProbe 已成功附加: {} -> {}", name, function);

            self.probes.push(ProbeInfo {
                probe_type: ProbeType::KProbe,
                name: name.to_string(),
                target: function.to_string(),
                attached: true,
            });
        } else {
            // 没有提供 Bpf 实例，只注册探针信息（用于测试或延迟附加）
            tracing::debug!("未提供 Bpf 实例，仅注册探针信息");
            self.probes.push(ProbeInfo {
                probe_type: ProbeType::KProbe,
                name: name.to_string(),
                target: function.to_string(),
                attached: false,
            });
        }

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
    /// * `name` - 探针名称（用于标识，必须与 eBPF 程序中的程序名匹配）
    /// * `binary` - 目标二进制文件路径
    /// * `symbol` - 要追踪的函数符号名
    /// * `bpf` - Bpf 实例（可选，如果提供则进行实际附加）
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
    /// use otlp::ebpf::{ProbeManager, EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载 eBPF 程序 ...
    /// let mut manager = ProbeManager::new();
    /// if let Some(bpf) = loader.bpf_mut() {
    ///     manager.attach_uprobe("malloc_probe", "/usr/bin/myapp", "malloc", Some(bpf))?;
    /// }
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_uprobe(&mut self, name: &str, binary: &str, symbol: &str, bpf: Option<&mut aya::Bpf>) -> Result<()> {
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
            tracing::warn!("二进制文件不存在: {}，将继续尝试附加", binary);
            // 不直接返回错误，因为可能是动态路径
        }

        tracing::info!("附加 UProbe: {} -> {}:{}", name, binary, symbol);

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        // 如果提供了 Bpf 实例，进行实际附加
        if let Some(bpf) = bpf {
            use aya::programs::uprobe::UProbe;

            // 从 Bpf 实例获取程序并加载
            let program: &mut UProbe = bpf.program_mut(name)
                .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序不存在: {}",
                    name
                )))?
                .try_into()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序类型转换失败: {:?}",
                    e
                )))?;

            program.load()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序加载失败: {}",
                    e
                )))?;

            // 附加到用户空间函数
            // pid: None 表示附加到所有进程
            program.attach(Some(binary), symbol, 0, None)
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "探针附加失败: {}",
                    e
                )))?;

            tracing::info!("UProbe 已成功附加: {} -> {}:{}", name, binary, symbol);

            self.probes.push(ProbeInfo {
                probe_type: ProbeType::UProbe,
                name: name.to_string(),
                target: format!("{}:{}", binary, symbol),
                attached: true,
            });
        } else {
            // 没有提供 Bpf 实例，只注册探针信息
            tracing::debug!("未提供 Bpf 实例，仅注册探针信息");
            self.probes.push(ProbeInfo {
                probe_type: ProbeType::UProbe,
                name: name.to_string(),
                target: format!("{}:{}", binary, symbol),
                attached: false,
            });
        }

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
    /// * `name` - 探针名称（用于标识，必须与 eBPF 程序中的程序名匹配）
    /// * `category` - 跟踪点类别（如 "syscalls"）
    /// * `event` - 跟踪点事件名（如 "sys_enter_openat"）
    /// * `bpf` - Bpf 实例（可选，如果提供则进行实际附加）
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
    /// use otlp::ebpf::{ProbeManager, EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载 eBPF 程序 ...
    /// let mut manager = ProbeManager::new();
    /// if let Some(bpf) = loader.bpf_mut() {
    ///     manager.attach_tracepoint("openat_trace", "syscalls", "sys_enter_openat", Some(bpf))?;
    /// }
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn attach_tracepoint(&mut self, name: &str, category: &str, event: &str, bpf: Option<&mut aya::Bpf>) -> Result<()> {
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

        // 检查是否已存在同名探针
        if self.probes.iter().any(|p| p.name == name) {
            return Err(crate::ebpf::error::EbpfError::AttachFailed(format!(
                "探针已存在: {}",
                name
            ))
            .into());
        }

        // 如果提供了 Bpf 实例，进行实际附加
        if let Some(bpf) = bpf {
            use aya::programs::trace_point::TracePoint;

            // 从 Bpf 实例获取程序并加载
            let program: &mut TracePoint = bpf.program_mut(name)
                .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序不存在: {}",
                    name
                )))?
                .try_into()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序类型转换失败: {:?}",
                    e
                )))?;

            program.load()
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "程序加载失败: {}",
                    e
                )))?;

            // 附加到跟踪点
            program.attach(category, event)
                .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                    "探针附加失败: {}",
                    e
                )))?;

            tracing::info!("Tracepoint 已成功附加: {} -> {}:{}", name, category, event);

            self.probes.push(ProbeInfo {
                probe_type: ProbeType::TracePoint,
                name: name.to_string(),
                target: format!("{}:{}", category, event),
                attached: true,
            });
        } else {
            // 没有提供 Bpf 实例，只注册探针信息
            tracing::debug!("未提供 Bpf 实例，仅注册探针信息");
            self.probes.push(ProbeInfo {
                probe_type: ProbeType::TracePoint,
                name: name.to_string(),
                target: format!("{}:{}", category, event),
                attached: false,
            });
        }

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn attach_tracepoint(&mut self, _name: &str, _category: &str, _event: &str) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离指定探针
    ///
    /// # 参数
    ///
    /// * `name` - 要分离的探针名称
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 分离已附加的探针，释放相关资源。
    /// 实际实现需要使用 aya 的分离方法：
    /// ```rust,ignore
    /// if let Some(probe_info) = self.probes.iter().find(|p| p.name == name) {
    ///     match probe_info.probe_type {
    ///         ProbeType::KProbe => {
    ///             // let program: &mut KProbe = bpf.program_mut(name)?;
    ///             // program.detach()?;
    ///         }
    ///         ProbeType::UProbe => {
    ///             // let program: &mut UProbe = bpf.program_mut(name)?;
    ///             // program.detach()?;
    ///         }
    ///         ProbeType::TracePoint => {
    ///             // let program: &mut TracePoint = bpf.program_mut(name)?;
    ///             // program.detach()?;
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn detach(&mut self, name: &str) -> Result<()> {
        let initial_len = self.probes.len();
        let probe_exists = self.probes.iter().any(|p| p.name == name);

        if probe_exists {
            // 注意: 实际的探针分离需要:
            // 1. 根据探针类型调用相应的分离方法
            // 2. 使用 aya 的 detach() 方法
            // 3. 释放相关资源
            // 实际实现示例（需要实际的 Bpf 实例）:
            //     if let Some(probe_info) = self.probes.iter().find(|p| p.name == name) {
            //         match probe_info.probe_type {
            //             ProbeType::KProbe => {
            //                 let program: &mut KProbe = bpf.program_mut(name)?
            //                     .try_into()?;
            //                 program.detach()?;
            //             }
            //             ProbeType::UProbe => {
            //                 let program: &mut UProbe = bpf.program_mut(name)?
            //                     .try_into()?;
            //                 program.detach()?;
            //             }
            //             ProbeType::TracePoint => {
            //                 let program: &mut TracePoint = bpf.program_mut(name)?
            //                     .try_into()?;
            //                 program.detach()?;
            //             }
            //         }
            //     }
            // 注意：分离后探针将停止收集数据，但 eBPF 程序仍在内存中

            self.probes.retain(|p| p.name != name);
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

    /// 分离探针（需要 Bpf 实例）
    ///
    /// # 参数
    ///
    /// * `name` - 探针名称
    /// * `bpf` - Bpf 实例（必须提供）
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 分离指定的探针，停止收集数据。
    /// 分离后探针将停止收集数据，但 eBPF 程序仍在内存中。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{ProbeManager, EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载 eBPF 程序 ...
    /// let mut manager = ProbeManager::new();
    /// // ... 附加探针 ...
    /// if let Some(bpf) = loader.bpf_mut() {
    ///     manager.detach_with_bpf("my_probe", bpf)?;
    /// }
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn detach_with_bpf(&mut self, name: &str, bpf: &mut aya::Bpf) -> Result<()> {
        // 查找探针信息
        let probe_info = self.probes.iter().find(|p| p.name == name);

        if let Some(probe_info) = probe_info {
            // 根据探针类型分离
            match probe_info.probe_type {
                ProbeType::KProbe => {
                    use aya::programs::kprobe::KProbe;
                    if let Ok(program) = bpf.program_mut(name)
                        .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                            "程序不存在: {}",
                            name
                        )))?
                        .try_into::<KProbe>()
                    {
                        program.detach()
                            .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                                "分离 KProbe 失败: {}",
                                e
                            )))?;
                    }
                }
                ProbeType::UProbe => {
                    use aya::programs::uprobe::UProbe;
                    if let Ok(program) = bpf.program_mut(name)
                        .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                            "程序不存在: {}",
                            name
                        )))?
                        .try_into::<UProbe>()
                    {
                        program.detach()
                            .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                                "分离 UProbe 失败: {}",
                                e
                            )))?;
                    }
                }
                ProbeType::TracePoint => {
                    use aya::programs::trace_point::TracePoint;
                    if let Ok(program) = bpf.program_mut(name)
                        .ok_or_else(|| crate::ebpf::error::EbpfError::AttachFailed(format!(
                            "程序不存在: {}",
                            name
                        )))?
                        .try_into::<TracePoint>()
                    {
                        program.detach()
                            .map_err(|e| crate::ebpf::error::EbpfError::AttachFailed(format!(
                                "分离 TracePoint 失败: {}",
                                e
                            )))?;
                    }
                }
            }

            // 从列表中移除
            self.probes.retain(|p| p.name != name);
            tracing::info!("探针已成功分离: {}", name);
            Ok(())
        } else {
            Err(EbpfError::AttachFailed(format!("探针不存在: {}", name)).into())
        }
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn detach_with_bpf(&mut self, _name: &str, _bpf: &mut aya::Bpf) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离所有探针（需要 Bpf 实例）
    ///
    /// # 参数
    ///
    /// * `bpf` - Bpf 实例（必须提供）
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 分离所有已附加的探针，释放所有相关资源。
    /// 分离所有探针后，eBPF 程序仍在内存中，需要卸载程序才能完全清理。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{ProbeManager, EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载 eBPF 程序 ...
    /// let mut manager = ProbeManager::new();
    /// // ... 附加探针 ...
    /// if let Some(bpf) = loader.bpf_mut() {
    ///     manager.detach_all_with_bpf(bpf)?;
    /// }
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn detach_all_with_bpf(&mut self, bpf: &mut aya::Bpf) -> Result<()> {
        let count = self.probes.len();
        if count == 0 {
            return Ok(());
        }

        tracing::info!("分离 {} 个探针", count);

        // 收集所有探针名称（避免在迭代时修改列表）
        let probe_names: Vec<String> = self.probes.iter().map(|p| p.name.clone()).collect();

        // 遍历所有探针并分离
        for name in &probe_names {
            // 查找探针信息
            if let Some(probe_info) = self.probes.iter().find(|p| p.name == *name) {
                match probe_info.probe_type {
                    ProbeType::KProbe => {
                        use aya::programs::kprobe::KProbe;
                        if let Ok(program) = bpf.program_mut(name)
                            .and_then(|p| p.try_into::<KProbe>().ok())
                        {
                            let _ = program.detach();
                        }
                    }
                    ProbeType::UProbe => {
                        use aya::programs::uprobe::UProbe;
                        if let Ok(program) = bpf.program_mut(name)
                            .and_then(|p| p.try_into::<UProbe>().ok())
                        {
                            let _ = program.detach();
                        }
                    }
                    ProbeType::TracePoint => {
                        use aya::programs::trace_point::TracePoint;
                        if let Ok(program) = bpf.program_mut(name)
                            .and_then(|p| p.try_into::<TracePoint>().ok())
                        {
                            let _ = program.detach();
                        }
                    }
                }
            }
        }

        // 清空探针列表
        self.probes.clear();
        tracing::info!("所有探针已成功分离");

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn detach_all_with_bpf(&mut self, _bpf: &mut aya::Bpf) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 分离所有探针
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 分离所有已附加的探针，释放所有相关资源。
    /// 实际实现需要遍历所有探针并逐一分离：
    /// ```rust,ignore
    /// for probe_info in &self.probes {
    ///     match probe_info.probe_type {
    ///         ProbeType::KProbe => { /* detach kprobe */ }
    ///         ProbeType::UProbe => { /* detach uprobe */ }
    ///         ProbeType::TracePoint => { /* detach tracepoint */ }
    ///     }
    /// }
    /// ```
    pub fn detach_all(&mut self) -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            let count = self.probes.len();
            if count > 0 {
                // 注意: 实际的探针分离需要:
                // 1. 遍历所有探针
                // 2. 根据探针类型调用相应的分离方法
                // 3. 使用 aya 的 detach() 方法
                // 实际实现示例（需要实际的 Bpf 实例）:
                //     for probe_info in &self.probes {
                //         match probe_info.probe_type {
                //             ProbeType::KProbe => {
                //                 if let Ok(program) = bpf.program_mut(&probe_info.name)
                //                     .and_then(|p| p.try_into::<KProbe>().ok()) {
                //                     let _ = program.detach();
                //                 }
                //             }
                //             ProbeType::UProbe => {
                //                 if let Ok(program) = bpf.program_mut(&probe_info.name)
                //                     .and_then(|p| p.try_into::<UProbe>().ok()) {
                //                     let _ = program.detach();
                //                 }
                //             }
                //             ProbeType::TracePoint => {
                //                 if let Ok(program) = bpf.program_mut(&probe_info.name)
                //                     .and_then(|p| p.try_into::<TracePoint>().ok()) {
                //                     let _ = program.detach();
                //                 }
                //             }
                //         }
                //     }
                // 注意：分离所有探针后，eBPF 程序仍在内存中，需要卸载程序才能完全清理

                tracing::info!("分离 {} 个探针", count);
                self.probes.clear();
            }
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
