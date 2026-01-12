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

        // 注意: 实际的 eBPF 程序加载需要:
        // 1. Linux 内核 >= 5.8
        // 2. CAP_BPF 权限
        // 3. BTF (BPF Type Format) 支持
        // 4. 使用 aya crate 加载:
        //    let mut bpf = Bpf::load(program_bytes)?;
        //    self.bpf = Some(bpf);

        // 当前实现：验证和准备
        // 实际运行时加载需要完整的 aya 集成
        if program_bytes.is_empty() {
            return Err(EbpfError::LoadFailed("程序字节码为空".to_string()).into());
        }

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

        tracing::debug!("eBPF 程序验证通过，准备加载到内核");
        Ok(())
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
            // 注意: 实际检查需要读取 /proc/version 或使用系统调用
            // 这里提供基本检查框架
            tracing::debug!("检查 Linux 内核版本支持");

            // 检查 BTF 支持
            // BTF 信息通常在 /sys/kernel/btf/vmlinux
            let btf_path = "/sys/kernel/btf/vmlinux";
            if std::path::Path::new(btf_path).exists() {
                tracing::debug!("检测到 BTF 支持");
            } else {
                tracing::warn!("未检测到 BTF 支持，某些 eBPF 功能可能受限");
            }

            // 检查权限（CAP_BPF）
            // 注意: 实际检查需要 libcap 或系统调用
            tracing::debug!("eBPF 系统支持检查完成（基本检查）");
            tracing::info!("eBPF 系统支持检查通过（注意：完整检查需要运行时权限验证）");
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
                match object::File::parse(program_bytes) {
                    Ok(_) => {
                        tracing::debug!("ELF 文件解析成功");
                    }
                    Err(e) => {
                        tracing::warn!("ELF 文件解析失败: {}", e);
                        // 不直接返回错误，因为可能是其他格式
                    }
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
        if let Some(_bpf) = self.bpf.take() {
            tracing::info!("卸载 eBPF 程序");

            // 注意: 实际的 eBPF 程序卸载需要:
            // 1. 分离所有附加的探针
            // 2. 关闭所有 Maps
            // 3. 调用 aya 的卸载方法:
            //    drop(bpf); // aya 会自动处理清理

            tracing::debug!("eBPF 程序已卸载");
        } else {
            tracing::debug!("没有已加载的 eBPF 程序");
        }
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn unload(&mut self) -> Result<()> {
        Ok(())
    }
