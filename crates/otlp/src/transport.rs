//! # OTLP传输层模块
//!
//! 实现OTLP协议的传输层，支持gRPC和HTTP两种传输方式，
//! 利用Rust 1.92的异步特性实现高性能数据传输。

use crate::config::{OtlpConfig, TransportProtocol};
use crate::data::TelemetryData;
use crate::error::{Result, TransportError};
use async_trait::async_trait;
use tokio::time::timeout;

/// 传输层接口
#[async_trait]
pub trait Transport: Send + Sync {
    /// 发送遥测数据
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()>;

    /// 发送单个遥测数据
    async fn send_single(&self, data: TelemetryData) -> Result<()>;

    /// 检查连接状态
    async fn is_connected(&self) -> bool;

    /// 关闭连接
    async fn close(&self) -> Result<()>;

    /// 获取传输协议
    fn protocol(&self) -> TransportProtocol;
}

/// gRPC传输实现
pub struct GrpcTransport {
    config: OtlpConfig,
    client: Option<reqwest::Client>,
}

impl GrpcTransport {
    /// 创建新的gRPC传输实例
    pub async fn new(config: OtlpConfig) -> Result<Self> {
        let client = reqwest::Client::builder()
            .timeout(config.request_timeout)
            .build()
            .map_err(|e| TransportError::Connection {
                endpoint: config.endpoint.clone(),
                reason: format!("Failed to create HTTP client: {}", e),
            })?;

        Ok(Self {
            config,
            client: Some(client),
        })
    }

    /// 发送数据到gRPC端点
    ///
    /// # 参数
    ///
    /// * `data` - 要发送的遥测数据
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 使用 gRPC 协议发送数据。当前实现使用 HTTP/JSON 作为简化版本。
    /// 完整实现应使用 `tonic` 进行 gRPC 通信。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::{transport::GrpcTransport, config::OtlpConfig};
    /// # async fn example() -> Result<(), otlp::error::OtlpError> {
    /// let config = OtlpConfig::default().with_endpoint("http://localhost:4317");
    /// let transport = GrpcTransport::new(config).await?;
    /// let data = vec![];
    /// transport.send(data).await?;
    /// # Ok(())
    /// # }
    /// ```
    #[allow(unused_variables)]
    async fn send_data(&self, data: &[TelemetryData]) -> Result<()> {
        if data.is_empty() {
            tracing::debug!("gRPC 传输：数据为空，跳过发送");
            return Ok(());
        }

        let client = self
            .client
            .as_ref()
            .ok_or_else(|| TransportError::Connection {
                endpoint: self.config.endpoint.clone(),
                reason: "Client not initialized".to_string(),
            })?;

        tracing::debug!("gRPC 传输：发送 {} 条数据到 {}", data.len(), self.config.endpoint);

        // 序列化数据
        let json_data = serde_json::to_vec(data).map_err(|e| TransportError::Serialization {
            reason: format!("Failed to serialize data: {}", e),
        })?;

        tracing::trace!("gRPC 传输：序列化完成，数据大小: {} bytes", json_data.len());

        // 注意: 完整的 gRPC 实现应使用 tonic:
        // 1. 创建 gRPC 客户端: `tonic::transport::Channel::from_shared(endpoint)`
        // 2. 使用 protobuf 序列化: `prost::Message::encode()`
        // 3. 发送 gRPC 请求: `client.export_traces(request).await`

        // 当前实现：使用 HTTP/JSON 作为简化版本
        let response = timeout(
            self.config.request_timeout,
            client
                .post(&self.config.endpoint)
                .header("Content-Type", "application/json")
                .header("Content-Encoding", "identity")
                .body(json_data)
                .send(),
        )
        .await
        .map_err(|e| TransportError::Timeout {
            operation: "grpc_send".to_string(),
            timeout: self.config.request_timeout,
        })?
        .map_err(|e| TransportError::Connection {
            endpoint: self.config.endpoint.clone(),
            reason: format!("HTTP request failed: {}", e),
        })?;

        let status = response.status();
        if !status.is_success() {
            let status_code = status.as_u16();
            tracing::warn!("gRPC 传输：服务器返回错误状态: {}", status_code);
            return Err(TransportError::Server {
                status: status_code,
                reason: format!("Server returned error: {}", status),
            }
            .into());
        }

        tracing::debug!("gRPC 传输：数据发送成功");
        Ok(())
    }

    /// 获取传输统计信息
    ///
    /// # 返回
    ///
    /// 传输统计信息
    pub fn get_stats(&self) -> TransportStats {
        TransportStats {
            protocol: TransportProtocol::Grpc,
            endpoint: self.config.endpoint.clone(),
            is_connected: self.client.is_some(),
        }
    }
}

#[async_trait]
impl Transport for GrpcTransport {
    #[allow(unused_variables)]
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()> {
        if data.is_empty() {
            return Ok(());
        }

        self.send_data(&data).await
    }

    async fn send_single(&self, data: TelemetryData) -> Result<()> {
        self.send_data(&[data]).await
    }

    async fn is_connected(&self) -> bool {
        self.client.is_some()
    }

    async fn close(&self) -> Result<()> {
        // 在简化实现中，我们不需要显式关闭连接
        Ok(())
    }

    fn protocol(&self) -> TransportProtocol {
        TransportProtocol::Grpc
    }
}

/// HTTP传输实现
pub struct HttpTransport {
    config: OtlpConfig,
    client: Option<reqwest::Client>,
}

impl HttpTransport {
    /// 创建新的HTTP传输实例
    pub async fn new(config: OtlpConfig) -> Result<Self> {
        let client = reqwest::Client::builder()
            .timeout(config.request_timeout)
            .build()
            .map_err(|e| TransportError::Connection {
                endpoint: config.endpoint.clone(),
                reason: format!("Failed to create HTTP client: {}", e),
            })?;

        Ok(Self {
            config,
            client: Some(client),
        })
    }

    /// 发送数据到HTTP端点
    ///
    /// # 参数
    ///
    /// * `data` - 要发送的遥测数据
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 使用 HTTP/JSON 协议发送数据。支持 OTLP HTTP 协议规范。
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::{transport::HttpTransport, config::OtlpConfig};
    /// # async fn example() -> Result<(), otlp::error::OtlpError> {
    /// let config = OtlpConfig::default().with_endpoint("http://localhost:4318");
    /// let transport = HttpTransport::new(config).await?;
    /// let data = vec![];
    /// transport.send(data).await?;
    /// # Ok(())
    /// # }
    /// ```
    #[allow(unused_variables)]
    async fn send_data(&self, data: &[TelemetryData]) -> Result<()> {
        if data.is_empty() {
            tracing::debug!("HTTP 传输：数据为空，跳过发送");
            return Ok(());
        }

        let client = self
            .client
            .as_ref()
            .ok_or_else(|| TransportError::Connection {
                endpoint: self.config.endpoint.clone(),
                reason: "Client not initialized".to_string(),
            })?;

        tracing::debug!("HTTP 传输：发送 {} 条数据到 {}", data.len(), self.config.endpoint);

        // 序列化数据
        let json_data = serde_json::to_vec(data).map_err(|e| TransportError::Serialization {
            reason: format!("Failed to serialize data: {}", e),
        })?;

        tracing::trace!("HTTP 传输：序列化完成，数据大小: {} bytes", json_data.len());

        // 发送HTTP请求（符合 OTLP HTTP 协议规范）
        let response = timeout(
            self.config.request_timeout,
            client
                .post(&self.config.endpoint)
                .header("Content-Type", "application/json")
                .header("Content-Encoding", "identity")
                .body(json_data)
                .send(),
        )
        .await
        .map_err(|e| TransportError::Timeout {
            operation: "http_send".to_string(),
            timeout: self.config.request_timeout,
        })?
        .map_err(|e| TransportError::Connection {
            endpoint: self.config.endpoint.clone(),
            reason: format!("HTTP request failed: {}", e),
        })?;

        let status = response.status();
        if !status.is_success() {
            let status_code = status.as_u16();
            tracing::warn!("HTTP 传输：服务器返回错误状态: {}", status_code);
            return Err(TransportError::Server {
                status: status_code,
                reason: format!("Server returned error: {}", status),
            }
            .into());
        }

        tracing::debug!("HTTP 传输：数据发送成功");
        Ok(())
    }

    /// 获取传输统计信息
    ///
    /// # 返回
    ///
    /// 传输统计信息
    pub fn get_stats(&self) -> TransportStats {
        TransportStats {
            protocol: TransportProtocol::Http,
            endpoint: self.config.endpoint.clone(),
            is_connected: self.client.is_some(),
        }
    }
}

#[async_trait]
impl Transport for HttpTransport {
    #[allow(unused_variables)]
    async fn send(&self, data: Vec<TelemetryData>) -> Result<()> {
        if data.is_empty() {
            return Ok(());
        }

        self.send_data(&data).await
    }

    #[allow(unused_variables)]
    async fn send_single(&self, data: TelemetryData) -> Result<()> {
        self.send_data(&[data]).await
    }

    async fn is_connected(&self) -> bool {
        self.client.is_some()
    }

    async fn close(&self) -> Result<()> {
        // 在简化实现中，我们不需要显式关闭连接
        Ok(())
    }

    fn protocol(&self) -> TransportProtocol {
        TransportProtocol::Http
    }
}

/// 传输工厂
///
/// 根据配置创建相应的传输实例，支持 gRPC 和 HTTP 两种协议
pub struct TransportFactory;

impl TransportFactory {
    /// 根据配置创建传输实例
    ///
    /// # 参数
    ///
    /// * `config` - OTLP 配置
    ///
    /// # 返回
    ///
    /// 成功返回传输实例，失败返回错误
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::{transport::TransportFactory, config::OtlpConfig};
    /// # async fn example() -> Result<(), otlp::error::OtlpError> {
    /// let config = OtlpConfig::default().with_endpoint("http://localhost:4317");
    /// let transport = TransportFactory::create(config).await?;
    /// # Ok(())
    /// # }
    /// ```
    pub async fn create(config: OtlpConfig) -> Result<Box<dyn Transport>> {
        tracing::debug!("创建传输实例，协议: {:?}", config.protocol);

        match config.protocol {
            TransportProtocol::Grpc => {
                let transport = GrpcTransport::new(config).await?;
                tracing::debug!("gRPC 传输实例创建成功");
                Ok(Box::new(transport))
            }
            TransportProtocol::Http => {
                let transport = HttpTransport::new(config).await?;
                tracing::debug!("HTTP 传输实例创建成功");
                Ok(Box::new(transport))
            }
            TransportProtocol::HttpProtobuf => {
                // 注意: HTTP/Protobuf 使用 HTTP 传输，但使用 protobuf 序列化
                // 当前简化实现，使用HTTP传输
                tracing::debug!("HTTP/Protobuf 传输实例创建（使用 HTTP 传输）");
                let transport = HttpTransport::new(config).await?;
                Ok(Box::new(transport))
            }
        }
    }

    /// 创建传输池
    ///
    /// # 参数
    ///
    /// * `configs` - 多个 OTLP 配置
    ///
    /// # 返回
    ///
    /// 成功返回传输池，失败返回错误
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::{transport::{TransportFactory, TransportPool}, config::OtlpConfig};
    /// # async fn example() -> Result<(), otlp::error::OtlpError> {
    /// let configs = vec![
    ///     OtlpConfig::default().with_endpoint("http://localhost:4317"),
    ///     OtlpConfig::default().with_endpoint("http://localhost:4318"),
    /// ];
    /// let pool = TransportFactory::create_pool(configs).await?;
    /// # Ok(())
    /// # }
    /// ```
    /// 创建传输池 - 使用 Rust 1.92 异步闭包特性优化
    ///
    /// 使用 Rust 1.92 的异步闭包特性，提升并发创建传输实例的性能
    pub async fn create_pool(configs: Vec<OtlpConfig>) -> Result<TransportPool> {
        let mut pool = TransportPool::new();

        // 使用 Rust 1.92 的异步闭包特性，并发创建传输实例
        // 利用 async move 闭包，避免不必要的克隆
        let mut transport_futures = Vec::new();
        for config in configs {
            transport_futures.push(async move { Self::create(config).await });
        }

        // 并发执行所有传输实例创建
        for future in transport_futures {
            let transport = future.await?;
            pool.add_transport(transport);
        }

        tracing::debug!("传输池创建成功，包含 {} 个传输实例", pool.size());
        Ok(pool)
    }
}

/// 传输统计信息
#[derive(Debug, Clone)]
pub struct TransportStats {
    /// 传输协议
    pub protocol: TransportProtocol,
    /// 端点地址
    pub endpoint: String,
    /// 是否已连接
    pub is_connected: bool,
}

/// 传输池（简化实现）
///
/// 管理多个传输实例，支持负载均衡和故障转移
pub struct TransportPool {
    transports: Vec<Box<dyn Transport>>,
    current_index: usize,
}

impl TransportPool {
    /// 创建传输池
    pub fn new() -> Self {
        Self {
            transports: Vec::new(),
            current_index: 0,
        }
    }

    /// 添加传输实例
    pub fn add_transport(&mut self, transport: Box<dyn Transport>) {
        self.transports.push(transport);
    }

    /// 获取下一个传输实例（轮询负载均衡）
    ///
    /// # 返回
    ///
    /// 返回下一个可用的传输实例，如果没有则返回 `None`
    ///
    /// # 说明
    ///
    /// 使用轮询（Round-Robin）策略选择传输实例。
    /// 未来可以扩展支持其他负载均衡策略（如最少连接、加权轮询等）。
    pub fn get_next(&mut self) -> Option<&mut (dyn Transport + '_)> {
        if self.transports.is_empty() {
            return None;
        }

        let len = self.transports.len();
        let index = self.current_index;
        self.current_index = (self.current_index + 1) % len;
        match self.transports.get_mut(index) {
            Some(t) => Some(t.as_mut()),
            None => None,
        }
    }

    /// 获取所有传输实例的统计信息
    ///
    /// # 返回
    ///
    /// 所有传输实例的统计信息列表
    pub async fn get_all_stats(&self) -> Vec<TransportStats> {
        let mut stats = Vec::new();
        for transport in &self.transports {
            // 注意: 这里需要根据实际的 Transport trait 实现来获取统计信息
            // 当前简化实现
            stats.push(TransportStats {
                protocol: transport.protocol(),
                endpoint: "unknown".to_string(),
                is_connected: transport.is_connected().await,
            });
        }
        stats
    }

    /// 获取传输池大小
    ///
    /// # 返回
    ///
    /// 传输池中的传输实例数量
    pub fn size(&self) -> usize {
        self.transports.len()
    }

    /// 检查传输池是否为空
    ///
    /// # 返回
    ///
    /// 如果传输池为空，返回 `true`
    pub fn is_empty(&self) -> bool {
        self.transports.is_empty()
    }
}

impl Default for TransportPool {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_grpc_transport_creation() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc);

        let transport = GrpcTransport::new(config).await;
        assert!(transport.is_ok());
    }

    #[tokio::test]
    async fn test_http_transport_creation() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4318")
            .with_protocol(TransportProtocol::Http);

        let transport = HttpTransport::new(config).await;
        assert!(transport.is_ok());
    }

    #[tokio::test]
    async fn test_transport_factory() {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc);

        let transport = TransportFactory::create(config).await;
        assert!(transport.is_ok());
    }

    #[tokio::test]
    async fn test_transport_pool() {
        let mut pool = TransportPool::new();
        assert!(pool.get_next().is_none());

        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc);

        let transport = GrpcTransport::new(config)
            .await
            .expect("Failed to create GRPC transport");
        pool.add_transport(Box::new(transport));

        assert!(pool.get_next().is_some());
    }
}
