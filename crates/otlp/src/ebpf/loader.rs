//! eBPF 程序加载器
//!
//! 负责加载和验证 eBPF 程序

use crate::error::Result;
use crate::ebpf::types::EbpfConfig;
use crate::ebpf::error::EbpfError;

#[cfg(all(feature = "ebpf", target_os = "linux"))]
use aya::Bpf;

/// eBPF 程序加载器
pub struct EbpfLoader {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    bpf: Option<Bpf>,
    config: EbpfConfig,
}

impl EbpfLoader {
    /// 创建新的加载器
    pub fn new(config: EbpfConfig) -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            bpf: None,
            config,
        }
    }

    /// 加载 eBPF 程序
    ///
    /// # 参数
    ///
    /// * `program_bytes` - eBPF 程序的字节码
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 错误
    ///
    /// * `EbpfError::LoadFailed` - 程序加载失败
    /// * `EbpfError::UnsupportedPlatform` - 平台不支持
    /// * `EbpfError::InsufficientPermissions` - 权限不足
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// let program_bytes = include_bytes!("program.o");
    /// loader.load(program_bytes)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn load(&mut self, program_bytes: &[u8]) -> Result<()> {
        // 验证程序字节码
        self.validate_program(program_bytes)?;

        tracing::info!(
            "加载 eBPF 程序，程序大小: {} bytes，配置: {:?}",
            program_bytes.len(),
            self.config
        );

        // 检查程序大小限制（eBPF 程序通常有大小限制）
        const MAX_PROGRAM_SIZE: usize = 1_000_000; // 1MB
        if program_bytes.len() > MAX_PROGRAM_SIZE {
            return Err(EbpfError::LoadFailed(format!(
                "程序字节码过大: {} bytes (最大: {} bytes)",
                program_bytes.len(),
                MAX_PROGRAM_SIZE
            ))
            .into());
        }

        // 检查系统支持
        Self::check_system_support()?;

        // 实际加载 eBPF 程序（使用 aya）
        // 注意：这需要实际的 eBPF 程序字节码和适当的权限
        use aya::util::KernelVersion;

        // 检查内核版本
        match KernelVersion::current() {
            Ok(kernel_version) => {
                if kernel_version < KernelVersion::new(5, 8, 0) {
                    return Err(EbpfError::IncompatibleKernel.into());
                }
                tracing::debug!("内核版本检查通过: {:?}", kernel_version);
            }
            Err(e) => {
                tracing::warn!("无法获取内核版本: {}，继续尝试加载", e);
                // 继续执行，因为某些环境可能无法获取内核版本
            }
        }

        // 尝试加载 eBPF 程序
        // 注意：这需要实际的 eBPF 程序字节码
        // 如果程序字节码无效或权限不足，会返回错误
        match Bpf::load(program_bytes) {
            Ok(mut bpf) => {
                tracing::info!("eBPF 程序加载成功");

                // 验证程序是否包含必要的段
                let program_count = bpf.programs().count();
                if program_count == 0 {
                    tracing::warn!("eBPF 程序未包含任何程序段");
                } else {
                    tracing::debug!("eBPF 程序包含 {} 个程序段", program_count);
                }

                // 验证 Maps
                let map_count = bpf.maps().count();
                if map_count > 0 {
                    tracing::debug!("eBPF 程序包含 {} 个 Maps", map_count);
                }

                self.bpf = Some(bpf);
                tracing::info!("eBPF 程序已成功加载到内核");
                Ok(())
            }
            Err(e) => {
                // 如果加载失败，返回错误
                tracing::warn!("eBPF 程序加载失败: {}，这可能是因为缺少权限或程序格式不正确", e);
                Err(EbpfError::LoadFailed(format!("eBPF 程序加载失败: {}", e)).into())
            }
        }
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn load(&mut self, _program_bytes: &[u8]) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 检查系统是否支持 eBPF
    ///
    /// # 返回
    ///
    /// 如果系统支持 eBPF，返回 `Ok(())`，否则返回错误
    ///
    /// # 检查项
    ///
    /// 1. 平台是否为 Linux
    /// 2. 内核版本 >= 5.8（eBPF 完整支持）
    /// 3. BTF (BPF Type Format) 支持
    /// 4. CAP_BPF 权限（如果可用）
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::EbpfLoader;
    ///
    /// match EbpfLoader::check_system_support() {
    ///     Ok(()) => println!("系统支持 eBPF"),
    ///     Err(e) => eprintln!("系统不支持 eBPF: {}", e),
    /// }
    /// ```
    pub fn check_system_support() -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            // 检查内核版本（需要 >= 5.8 以获得完整的 eBPF 支持）
            use std::fs;

            // 读取内核版本信息
            let version_info = match fs::read_to_string("/proc/version") {
                Ok(info) => info,
                Err(e) => {
                    tracing::warn!("无法读取 /proc/version: {}", e);
                    // 继续执行，不阻塞
                    return Ok(());
                }
            };

            // 解析内核版本 (格式: Linux version X.Y.Z)
            if let Some(version_start) = version_info.find("Linux version ") {
                let version_str = &version_info[version_start + 14..];
                if let Some(space_pos) = version_str.find(' ') {
                    let version = &version_str[..space_pos];
                    let parts: Vec<&str> = version.split('.').collect();
                    if parts.len() >= 2 {
                        if let (Ok(major), Ok(minor)) = (parts[0].parse::<u32>(), parts[1].parse::<u32>()) {
                            if major < 5 || (major == 5 && minor < 8) {
                                return Err(EbpfError::IncompatibleKernel.into());
                            }
                            tracing::debug!("内核版本检查通过: {}.{}", major, minor);
                        }
                    }
                }
            }

            // 检查 BTF 支持
            // BTF 信息通常在 /sys/kernel/btf/vmlinux
            // BTF (BPF Type Format) 允许 eBPF 程序访问内核数据结构
            let btf_path = "/sys/kernel/btf/vmlinux";
            if std::path::Path::new(btf_path).exists() {
                tracing::debug!("检测到 BTF 支持");
            } else {
                tracing::warn!("未检测到 BTF 支持，某些 eBPF 功能可能受限");
                // 注意：BTF 不是必需的，但强烈推荐使用
            }

            // 检查权限（CAP_BPF）
            // 读取进程状态检查能力
            if let Ok(status) = fs::read_to_string("/proc/self/status") {
                // 检查是否是root用户
                let is_root = status.lines()
                    .find(|line| line.starts_with("Uid:"))
                    .and_then(|line| {
                        line.split_whitespace().nth(2).and_then(|uid| uid.parse::<u32>().ok())
                    })
                    .map(|uid| uid == 0)
                    .unwrap_or(false);

                if !is_root {
                    // 检查CAP_BPF能力
                    let has_cap_bpf = status.lines()
                        .find(|line| line.starts_with("CapBpf:"))
                    .and_then(|line| {
                        line.split_whitespace().nth(1)
                                .and_then(|cap| u64::from_str_radix(cap, 16).ok())
                                .map(|cap| cap != 0)
                    })
                        .unwrap_or(false);

                    if !has_cap_bpf {
                        tracing::warn!("未检测到 CAP_BPF 权限，某些 eBPF 功能可能受限");
                        // 不直接返回错误，允许继续（某些功能可能不需要）
                    } else {
                        tracing::debug!("检测到 CAP_BPF 权限");
                    }
                } else {
                    tracing::debug!("检测到 root 权限");
                }
            }

            tracing::debug!("eBPF 系统支持检查完成");
            tracing::info!("eBPF 系统支持检查通过");
            Ok(())
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            Err(EbpfError::UnsupportedPlatform.into())
        }
    }

    /// 获取配置
    pub fn config(&self) -> &EbpfConfig {
        &self.config
    }

    /// 获取 Bpf 实例（用于高级操作）
    ///
    /// # 返回
    ///
    /// 如果程序已加载，返回 `Some(&Bpf)`，否则返回 `None`
    ///
    /// # 注意
    ///
    /// 这个方法返回不可变引用。如果需要可变引用，请使用 `bpf_mut()`。
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn bpf(&self) -> Option<&Bpf> {
        self.bpf.as_ref()
    }

    /// 获取 Bpf 实例的可变引用（用于高级操作）
    ///
    /// # 返回
    ///
    /// 如果程序已加载，返回 `Some(&mut Bpf)`，否则返回 `None`
    ///
    /// # 注意
    ///
    /// 这个方法返回可变引用，可以用于附加探针、操作 Maps 等。
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn bpf_mut(&mut self) -> Option<&mut Bpf> {
        self.bpf.as_mut()
    }

    /// 验证 eBPF 程序字节码
    ///
    /// # 参数
    ///
    /// * `program_bytes` - eBPF 程序的字节码
    ///
    /// # 返回
    ///
    /// 如果程序格式有效，返回 `Ok(())`，否则返回错误
    ///
    /// # 验证项
    ///
    /// 1. 字节码不为空
    /// 2. 字节码长度合理
    /// 3. ELF 格式验证（基本魔数检查）
    /// 4. 使用 object crate 进行完整验证（如果可用）
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let loader = EbpfLoader::new(config);
    /// let program_bytes = include_bytes!("program.o");
    /// loader.validate_program(program_bytes)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn validate_program(&self, program_bytes: &[u8]) -> Result<()> {
        if program_bytes.is_empty() {
            return Err(EbpfError::LoadFailed("程序字节码为空".to_string()).into());
        }

        // 检查最小长度（ELF 头部至少需要 64 字节）
        const MIN_ELF_SIZE: usize = 64;
        if program_bytes.len() < MIN_ELF_SIZE {
            return Err(EbpfError::LoadFailed(format!(
                "程序字节码过短: {} bytes (最小: {} bytes)",
                program_bytes.len(),
                MIN_ELF_SIZE
            ))
            .into());
        }

        // 检查 ELF 魔数 (0x7F 'E' 'L' 'F')
        const ELF_MAGIC: &[u8] = &[0x7F, b'E', b'L', b'F'];
        if program_bytes.starts_with(ELF_MAGIC) {
            tracing::debug!("检测到有效的 ELF 格式");

            // 使用 object crate 进行更详细的验证（如果可用）
            #[cfg(feature = "object")]
            {
                use object::Object;
                if let Ok(obj_file) = object::File::parse(program_bytes) {
                    // 验证是 eBPF 目标
                    let arch = obj_file.architecture();
                    if !matches!(arch, object::Architecture::Bpf) {
                        tracing::warn!("ELF 文件不是 eBPF 目标架构: {:?}", arch);
                    }

                    // 检查是否有 eBPF 程序段
                    let has_programs = obj_file.sections().any(|section| {
                        section.name().map(|name| name.contains("prog")).unwrap_or(false)
                    });

                    if !has_programs {
                        tracing::warn!("ELF 文件中未找到 eBPF 程序段");
                    } else {
                        tracing::debug!("ELF 文件验证通过，包含 eBPF 程序");
                    }
                } else {
                    tracing::warn!("无法解析 ELF 文件，跳过详细验证");
                }
            }

            Ok(())
        } else {
            Err(EbpfError::LoadFailed(format!(
                "无效的程序格式，期望 ELF 格式，但魔数为: {:?}",
                &program_bytes[..4.min(program_bytes.len())]
            ))
            .into())
        }
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn validate_program(&self, _program_bytes: &[u8]) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 检查程序是否已加载
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn is_loaded(&self) -> bool {
        self.bpf.is_some()
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn is_loaded(&self) -> bool {
        false
    }

    /// 卸载 eBPF 程序
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 卸载已加载的 eBPF 程序，释放相关资源。
    /// 注意：实际卸载需要调用 aya 的卸载方法。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{EbpfLoader, EbpfConfig};
    ///
    /// let config = EbpfConfig::default();
    /// let mut loader = EbpfLoader::new(config);
    /// // ... 加载程序 ...
    /// loader.unload()?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn unload(&mut self) -> Result<()> {
        if let Some(mut bpf) = self.bpf.take() {
            tracing::info!("卸载 eBPF 程序");

            // 1. 分离所有附加的探针
            // 遍历所有程序并分离
            let mut program_count = 0;
            let mut detached_count = 0;

            // 获取所有程序并尝试分离
            for program in bpf.programs_mut() {
                program_count += 1;
                // 尝试分离程序（如果已附加）
                // 注意：aya 的 detach 方法在 drop 时会自动调用
                // 这里我们记录程序数量，实际的分离由 drop 处理
                detached_count += 1;
            }

            if program_count > 0 {
                tracing::debug!("分离了 {} 个 eBPF 程序", program_count);
            }

            // 2. 关闭所有 Maps（如果需要）
            // aya 会在 drop 时自动处理 Maps 的清理
            let map_count = bpf.maps().count();
            if map_count > 0 {
                tracing::debug!("清理 {} 个 eBPF Maps", map_count);
            }

            // 3. 显式调用 drop 来触发清理
            // aya 会在 drop 时自动处理所有清理工作
            drop(bpf);

            tracing::info!("eBPF 程序已成功卸载 ({} 个程序, {} 个 Maps)", program_count, map_count);
        } else {
            tracing::debug!("没有已加载的 eBPF 程序");
        }
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn unload(&mut self) -> Result<()> {
        Ok(())
    }
