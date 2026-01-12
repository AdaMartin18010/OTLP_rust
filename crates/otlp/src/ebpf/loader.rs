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
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn load(&mut self, program_bytes: &[u8]) -> Result<()> {
        // TODO: 使用 aya 加载 eBPF 程序
        // 实际实现需要:
        // 1. 验证程序字节码
        // 2. 加载到内核
        // 3. 验证程序安全性
        // let mut bpf = Bpf::load(program_bytes)?;
        // self.bpf = Some(bpf);

        tracing::info!(
            "eBPF 程序加载功能待实现，程序大小: {} bytes",
            program_bytes.len()
        );

        // 临时实现：检查基本条件
        if program_bytes.is_empty() {
            return Err(EbpfError::LoadFailed("程序字节码为空".to_string()).into());
        }

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn load(&mut self, _program_bytes: &[u8]) -> Result<()> {
        Err(EbpfError::UnsupportedPlatform.into())
    }

    /// 检查系统支持
    pub fn check_system_support() -> Result<()> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            // TODO: 检查内核版本 >= 5.8
            // TODO: 检查 BTF 支持
            // TODO: 检查 CAP_BPF 权限
            tracing::info!("eBPF 系统支持检查待实现");
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

    /// 验证程序字节码
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn validate_program(&self, program_bytes: &[u8]) -> Result<()> {
        if program_bytes.is_empty() {
            return Err(EbpfError::LoadFailed("程序字节码为空".to_string()).into());
        }

        // TODO: 使用 object crate 验证 eBPF 程序格式
        // 检查基本的 ELF 格式
        if program_bytes.len() < 4 {
            return Err(EbpfError::LoadFailed("程序字节码过短".to_string()).into());
        }

        // 检查 ELF 魔数 (0x7F 'E' 'L' 'F')
        if program_bytes[0] == 0x7F
            && program_bytes[1] == b'E'
            && program_bytes[2] == b'L'
            && program_bytes[3] == b'F'
        {
            tracing::debug!("检测到有效的 ELF 格式");
            Ok(())
        } else {
            Err(EbpfError::LoadFailed("无效的程序格式".to_string()).into())
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

    /// 卸载程序
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn unload(&mut self) -> Result<()> {
        // TODO: 卸载 eBPF 程序
        if self.bpf.is_some() {
            tracing::info!("卸载 eBPF 程序");
            self.bpf = None;
        }
        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn unload(&mut self) -> Result<()> {
        Ok(())
    }
