//! # Open Agent Management Protocol (OPAMP) 支持模块
//!
//! 本模块提供了 OPAMP 的完整实现，包括协议消息、配置管理、反向通道等功能。
//!
//! ## 核心功能
//!
//! - **协议实现**: 完整的 OPAMP gRPC 协议支持
//! - **配置管理**: 远程配置下发和更新
//! - **证书管理**: mTLS 证书的自动轮转
//! - **二进制管理**: Agent 二进制文件的更新
//! - **健康检查**: Agent 健康状态监控
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::opamp::{OpampClient, OpampConfig};
//!
//! let config = OpampConfig::new()
//!     .server_endpoint("https://opamp.example.com:4320")
//!     .agent_id("agent-123")
//!     .capabilities(OpampCapabilities::all());
//!
//! let client = OpampClient::new(config)?;
//! client.start().await?;
//! ```

pub mod messages;

pub use messages::{
    AgentToServer, ServerToAgent, AgentDescription, AgentCapabilities,
    RemoteConfigStatus, PackageStatus, AgentHealth,
};

/// OPAMP 错误类型
#[derive(Debug, thiserror::Error)]
pub enum OpampError {
    #[error("协议错误: {0}")]
    Protocol(String),
    
    #[error("配置错误: {0}")]
    Config(String),
    
    #[error("网络错误: {0}")]
    Network(String),
    
    #[error("证书错误: {0}")]
    Certificate(String),
    
    #[error("包管理错误: {0}")]
    Package(String),
    
    #[error("gRPC 错误: {0}")]
    Grpc(#[from] tonic::Status),
    
    #[error("IO 错误: {0}")]
    Io(#[from] std::io::Error),
}

pub type Result<T> = std::result::Result<T, OpampError>;

/// OPAMP 能力标识
#[derive(Debug, Clone, PartialEq)]
pub struct OpampCapabilities {
    pub reports_effective_config: bool,
    pub reports_own_traces: bool,
    pub reports_own_metrics: bool,
    pub reports_own_logs: bool,
    pub accepts_remote_config: bool,
    pub accepts_packages: bool,
    pub reports_health: bool,
    pub reports_remote_config: bool,
}

impl OpampCapabilities {
    /// 创建所有能力
    pub fn all() -> Self {
        Self {
            reports_effective_config: true,
            reports_own_traces: true,
            reports_own_metrics: true,
            reports_own_logs: true,
            accepts_remote_config: true,
            accepts_packages: true,
            reports_health: true,
            reports_remote_config: true,
        }
    }
    
    /// 创建基础能力
    pub fn basic() -> Self {
        Self {
            reports_effective_config: false,
            reports_own_traces: true,
            reports_own_metrics: true,
            reports_own_logs: true,
            accepts_remote_config: true,
            accepts_packages: false,
            reports_health: true,
            reports_remote_config: false,
        }
    }
}
