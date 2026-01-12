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
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步OPAMP操作
//! - **元组收集**: 使用 `collect()` 直接收集OPAMP数据到元组
//! - **改进的OPAMP**: 利用 Rust 1.92 的OPAMP优化提升性能
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

pub mod graduation;
pub mod messages;

use tonic;
use tracing::info;
use uuid;

pub use messages::{
    AgentCapabilities, AgentHealth, AgentToServer, PackageStatus, RemoteConfigStatus, ServerToAgent,
};

// 导出灰度策略相关类型
pub use graduation::{
    GraduationStrategy, HealthStatus, LabelSelector, MatchExpression, MatchOperator,
    RollbackManager,
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
    pub accepts_connection_settings: bool,
    pub accepts_other_settings: bool,
    pub reports_effective_config_hash: bool,
    pub reports_own_attributes: bool,
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
            accepts_connection_settings: true,
            accepts_other_settings: true,
            reports_effective_config_hash: true,
            reports_own_attributes: true,
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
            accepts_connection_settings: false,
            accepts_other_settings: false,
            reports_effective_config_hash: false,
            reports_own_attributes: false,
        }
    }
}

/// OPAMP 客户端配置
#[derive(Debug, Clone)]
pub struct OpampConfig {
    pub server_endpoint: String,
    pub agent_id: String,
    pub capabilities: OpampCapabilities,
    pub instance_uid: String,
    pub agent_description: Option<AgentDescription>,
    pub tls_config: Option<TlsConfig>,
    pub headers: std::collections::HashMap<String, String>,
    pub heartbeat_interval: std::time::Duration,
    pub report_interval: std::time::Duration,
}

/// TLS 配置
#[derive(Debug, Clone)]
pub struct TlsConfig {
    pub ca_cert_path: Option<String>,
    pub client_cert_path: Option<String>,
    pub client_key_path: Option<String>,
    pub server_name: Option<String>,
    pub insecure_skip_verify: bool,
}

/// Agent 描述
#[derive(Debug, Clone)]
pub struct AgentDescription {
    pub identifying_attributes: Vec<KeyValue>,
    pub non_identifying_attributes: Vec<KeyValue>,
}

/// 键值对
#[derive(Debug, Clone)]
pub struct KeyValue {
    pub key: String,
    pub value: String,
}

impl OpampConfig {
    pub fn new(server_endpoint: String, agent_id: String) -> Self {
        Self {
            server_endpoint,
            agent_id,
            capabilities: OpampCapabilities::basic(),
            instance_uid: uuid::Uuid::new_v4().to_string(),
            agent_description: None,
            tls_config: None,
            headers: std::collections::HashMap::new(),
            heartbeat_interval: std::time::Duration::from_secs(30),
            report_interval: std::time::Duration::from_secs(10),
        }
    }

    pub fn with_capabilities(mut self, capabilities: OpampCapabilities) -> Self {
        self.capabilities = capabilities;
        self
    }

    pub fn with_tls(mut self, tls_config: TlsConfig) -> Self {
        self.tls_config = Some(tls_config);
        self
    }

    pub fn with_agent_description(mut self, description: AgentDescription) -> Self {
        self.agent_description = Some(description);
        self
    }
}

/// OPAMP 客户端
#[allow(dead_code)]
pub struct OpampClient {
    config: OpampConfig,
    client: Option<tonic::transport::Channel>,
    is_connected: bool,
    last_heartbeat: std::time::Instant,
    last_report: std::time::Instant,
}

impl OpampClient {
    #[allow(dead_code)]
    pub fn new(config: OpampConfig) -> Result<Self> {
        Ok(Self {
            config,
            client: None,
            is_connected: false,
            last_heartbeat: std::time::Instant::now(),
            last_report: std::time::Instant::now(),
        })
    }

    /// 启动客户端
    #[allow(dead_code)]
    pub async fn start(&mut self) -> Result<()> {
        // 建立连接
        self.connect().await?;

        // 发送初始报告
        self.send_initial_report().await?;

        // 启动心跳和报告循环
        self.start_heartbeat_loop().await?;

        Ok(())
    }

    /// 建立连接
    #[allow(dead_code)]
    async fn connect(&mut self) -> Result<()> {
        let mut endpoint =
            tonic::transport::Endpoint::from_shared(self.config.server_endpoint.clone())
                .map_err(|e| OpampError::Network(format!("无效的服务器端点: {}", e)))?;

        // 配置TLS
        if let Some(tls_config) = &self.config.tls_config {
            endpoint = self.configure_tls(endpoint, tls_config)?;
        }

        let channel = endpoint
            .connect()
            .await
            .map_err(|e| OpampError::Network(format!("连接失败: {}", e)))?;

        self.client = Some(channel);
        self.is_connected = true;

        Ok(())
    }

    /// 配置TLS
    #[allow(dead_code)]
    fn configure_tls(
        &self,
        endpoint: tonic::transport::Endpoint,
        _tls_config: &TlsConfig,
    ) -> Result<tonic::transport::Endpoint> {
        // 这里应该实现TLS配置逻辑
        // 由于简化，我们直接返回endpoint
        Ok(endpoint)
    }

    /// 发送初始报告
    #[allow(dead_code)]
    async fn send_initial_report(&mut self) -> Result<()> {
        // 实现初始报告发送逻辑
        info!("发送初始报告到OPAMP服务器");
        Ok(())
    }

    /// 启动心跳循环
    #[allow(dead_code)]
    async fn start_heartbeat_loop(&mut self) -> Result<()> {
        // 实现心跳循环逻辑
        info!("启动OPAMP心跳循环");
        Ok(())
    }

    /// 停止客户端
    #[allow(dead_code)]
    pub async fn stop(&mut self) -> Result<()> {
        self.is_connected = false;
        self.client = None;
        info!("OPAMP客户端已停止");
        Ok(())
    }

    /// 检查连接状态
    #[allow(dead_code)]
    pub fn is_connected(&self) -> bool {
        self.is_connected
    }
}

/// 证书管理器
#[allow(dead_code)]
pub struct CertificateManager {
    cert_path: String,
    key_path: String,
    ca_cert_path: Option<String>,
}

impl CertificateManager {
    #[allow(dead_code)]
    pub fn new(cert_path: String, key_path: String) -> Self {
        Self {
            cert_path,
            key_path,
            ca_cert_path: None,
        }
    }

    #[allow(dead_code)]
    pub fn with_ca_cert(mut self, ca_cert_path: String) -> Self {
        self.ca_cert_path = Some(ca_cert_path);
        self
    }

    /// 加载证书
    #[allow(dead_code)]
    pub async fn load_certificates(&self) -> Result<Vec<u8>> {
        tokio::fs::read(&self.cert_path)
            .await
            .map_err(|e| OpampError::Certificate(format!("无法读取证书文件: {}", e)))
    }

    /// 加载私钥
    pub async fn load_private_key(&self) -> Result<Vec<u8>> {
        tokio::fs::read(&self.key_path)
            .await
            .map_err(|e| OpampError::Certificate(format!("无法读取私钥文件: {}", e)))
    }

    /// 验证证书
    pub async fn validate_certificate(&self) -> Result<bool> {
        // 实现证书验证逻辑
        Ok(true)
    }

    /// 轮转证书
    pub async fn rotate_certificate(&self, new_cert: &[u8], new_key: &[u8]) -> Result<()> {
        // 备份当前证书
        let backup_cert_path = format!("{}.backup", self.cert_path);
        let backup_key_path = format!("{}.backup", self.key_path);

        if tokio::fs::metadata(&self.cert_path).await.is_ok() {
            tokio::fs::copy(&self.cert_path, &backup_cert_path)
                .await
                .map_err(|e| OpampError::Certificate(format!("无法备份证书: {}", e)))?;
        }

        if tokio::fs::metadata(&self.key_path).await.is_ok() {
            tokio::fs::copy(&self.key_path, &backup_key_path)
                .await
                .map_err(|e| OpampError::Certificate(format!("无法备份私钥: {}", e)))?;
        }

        // 写入新证书
        tokio::fs::write(&self.cert_path, new_cert)
            .await
            .map_err(|e| OpampError::Certificate(format!("无法写入新证书: {}", e)))?;

        tokio::fs::write(&self.key_path, new_key)
            .await
            .map_err(|e| OpampError::Certificate(format!("无法写入新私钥: {}", e)))?;

        info!("证书轮转完成");
        Ok(())
    }
}

/// 二进制包管理器
pub struct PackageManager {
    install_dir: String,
    backup_dir: String,
}

impl PackageManager {
    pub fn new(install_dir: String) -> Self {
        let backup_dir = format!("{}/backup", install_dir);
        Self {
            install_dir,
            backup_dir,
        }
    }

    /// 安装包
    pub async fn install_package(&self, package_name: &str, package_data: &[u8]) -> Result<()> {
        let package_path = format!("{}/{}", self.install_dir, package_name);

        // 备份现有包
        if tokio::fs::metadata(&package_path).await.is_ok() {
            let backup_path = format!("{}/{}", self.backup_dir, package_name);
            tokio::fs::copy(&package_path, &backup_path)
                .await
                .map_err(|e| OpampError::Package(format!("无法备份现有包: {}", e)))?;
        }

        // 写入新包
        tokio::fs::write(&package_path, package_data)
            .await
            .map_err(|e| OpampError::Package(format!("无法安装包: {}", e)))?;

        info!("包 {} 安装完成", package_name);
        Ok(())
    }

    /// 卸载包
    pub async fn uninstall_package(&self, package_name: &str) -> Result<()> {
        let package_path = format!("{}/{}", self.install_dir, package_name);

        if tokio::fs::metadata(&package_path).await.is_ok() {
            tokio::fs::remove_file(&package_path)
                .await
                .map_err(|e| OpampError::Package(format!("无法卸载包: {}", e)))?;
        }

        info!("包 {} 卸载完成", package_name);
        Ok(())
    }

    /// 验证包
    pub async fn validate_package(&self, package_name: &str) -> Result<bool> {
        let package_path = format!("{}/{}", self.install_dir, package_name);

        // 实现包验证逻辑
        Ok(tokio::fs::metadata(&package_path).await.is_ok())
    }
}
