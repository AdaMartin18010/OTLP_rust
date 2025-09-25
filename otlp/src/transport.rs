//! # OTLP传输层模块
//!
//! 实现OTLP协议的传输层，支持gRPC和HTTP两种传输方式，
//! 利用Rust 1.90的异步特性实现高性能数据传输。

use crate::config::{ OtlpConfig, TransportProtocol};
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
    #[allow(unused_variables)]
    async fn send_data(&self, data: &[TelemetryData]) -> Result<()> {
        let client = self.client.as_ref().ok_or_else(|| {
            TransportError::Connection {
                endpoint: self.config.endpoint.clone(),
                reason: "Client not initialized".to_string(),
            }
        })?;

        // 序列化数据
        let json_data = serde_json::to_vec(data).map_err(|e| {
            TransportError::Serialization {
                reason: format!("Failed to serialize data: {}", e),
            }
        })?;

        // 发送HTTP请求（简化实现，实际应该使用gRPC）
        let response = timeout(
            self.config.request_timeout,
            client
                .post(&self.config.endpoint)
                .header("Content-Type", "application/json")
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

        if !response.status().is_success() {
            return Err(TransportError::Server {
                status: response.status().as_u16(),
                reason: format!("Server returned error: {}", response.status()),
            }
            .into());
        }

        Ok(())
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
    #[allow(unused_variables)]
    async fn send_data(&self, data: &[TelemetryData]) -> Result<()> {
        let client = self.client.as_ref().ok_or_else(|| {
            TransportError::Connection {
                endpoint: self.config.endpoint.clone(),
                reason: "Client not initialized".to_string(),
            }
        })?;

        // 序列化数据
        let json_data = serde_json::to_vec(data).map_err(|e| {
            TransportError::Serialization {
                reason: format!("Failed to serialize data: {}", e),
            }
        })?;

        // 发送HTTP请求
        let response = timeout(
            self.config.request_timeout,
            client
                .post(&self.config.endpoint)
                .header("Content-Type", "application/json")
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

        if !response.status().is_success() {
            return Err(TransportError::Server {
                status: response.status().as_u16(),
                reason: format!("Server returned error: {}", response.status()),
            }
            .into());
        }

        Ok(())
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
pub struct TransportFactory;

impl TransportFactory {
    /// 根据配置创建传输实例
    pub async fn create(config: OtlpConfig) -> Result<Box<dyn Transport>> {
        match config.protocol {
            TransportProtocol::Grpc => {
                let transport = GrpcTransport::new(config).await?;
                Ok(Box::new(transport))
            }
            TransportProtocol::Http => {
                let transport = HttpTransport::new(config).await?;
                Ok(Box::new(transport))
            }
            TransportProtocol::HttpProtobuf => {
                // 简化实现，使用HTTP传输
                let transport = HttpTransport::new(config).await?;
                Ok(Box::new(transport))
            }
        }
    }
}

/// 传输池（简化实现）
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

    /// 获取下一个传输实例
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

        let transport = GrpcTransport::new(config).await.unwrap();
        pool.add_transport(Box::new(transport));

        assert!(pool.get_next().is_some());
    }
}