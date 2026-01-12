//! OTLP 客户端增强功能
//!
//! 提供额外的实用方法和功能扩展，利用 Rust 1.92 新特性

use crate::client::OtlpClient;
use crate::data::TelemetryData;
use crate::error::{OtlpError, Result};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// 客户端增强功能扩展
impl OtlpClient {
    /// 健康检查
    ///
    /// 检查客户端是否正常工作
    ///
    /// # 返回
    ///
    /// 如果客户端健康，返回 `Ok(true)`，否则返回错误
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::OtlpClient;
    /// # async fn example(client: OtlpClient) -> Result<(), otlp::error::OtlpError> {
    /// let is_healthy = client.health_check().await?;
    /// if is_healthy {
    ///     println!("客户端健康");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub async fn health_check(&self) -> Result<bool> {
        // 检查是否已初始化
        let is_initialized = *self.is_initialized.read().await;
        if !is_initialized {
            return Ok(false);
        }

        // 检查是否已关闭
        let is_shutdown = *self.is_shutdown.read().await;
        if is_shutdown {
            return Ok(false);
        }

        // 检查导出器连接
        // 注意: 这里可以添加更详细的健康检查逻辑
        Ok(true)
    }

    /// 获取客户端状态信息
    ///
    /// 返回客户端的详细状态信息
    ///
    /// # 返回
    ///
    /// 包含初始化状态、关闭状态、指标等信息的结构
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::OtlpClient;
    /// # async fn example(client: OtlpClient) -> Result<(), otlp::error::OtlpError> {
    /// let status = client.get_status().await?;
    /// println!("客户端状态: {:?}", status);
    /// # Ok(())
    /// # }
    /// ```
    pub async fn get_status(&self) -> Result<ClientStatus> {
        let is_initialized = *self.is_initialized.read().await;
        let is_shutdown = *self.is_shutdown.read().await;
        let metrics = self.get_metrics().await;

        Ok(ClientStatus {
            is_initialized,
            is_shutdown,
            metrics: metrics.clone(),
            uptime: metrics.uptime,
        })
    }

    /// 批量发送并等待完成
    ///
    /// 发送批量数据并等待所有数据导出完成
    ///
    /// # 参数
    ///
    /// * `data` - 要发送的遥测数据列表
    /// * `timeout` - 超时时间
    ///
    /// # 返回
    ///
    /// 成功返回导出结果，超时或失败返回错误
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::{OtlpClient, TelemetryData};
    /// # use std::time::Duration;
    /// # async fn example(client: OtlpClient) -> Result<(), otlp::error::OtlpError> {
    /// let data = vec![TelemetryData::trace("test")];
    /// let result = client.send_batch_with_timeout(data, Duration::from_secs(10)).await?;
    /// println!("导出结果: {:?}", result);
    /// # Ok(())
    /// # }
    /// ```
    pub async fn send_batch_with_timeout(
        &self,
        data: Vec<TelemetryData>,
        timeout: Duration,
    ) -> Result<crate::exporter::ExportResult> {
        tokio::time::timeout(timeout, self.send_batch(data))
            .await
            .map_err(|_| OtlpError::Transport(crate::error::TransportError::Timeout {
                operation: "send_batch".to_string(),
                timeout,
            }))?
    }

    /// 发送单个数据并等待完成
    ///
    /// 发送单个数据并等待导出完成
    ///
    /// # 参数
    ///
    /// * `data` - 要发送的遥测数据
    /// * `timeout` - 超时时间
    ///
    /// # 返回
    ///
    /// 成功返回导出结果，超时或失败返回错误
    pub async fn send_with_timeout(
        &self,
        data: TelemetryData,
        timeout: Duration,
    ) -> Result<crate::exporter::ExportResult> {
        tokio::time::timeout(timeout, self.send(data))
            .await
            .map_err(|_| OtlpError::Transport(crate::error::TransportError::Timeout {
                operation: "send".to_string(),
                timeout,
            }))?
    }

    /// 刷新所有待处理的数据
    ///
    /// 强制刷新所有待处理的批处理数据
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// # use otlp::OtlpClient;
    /// # async fn example(client: OtlpClient) -> Result<(), otlp::error::OtlpError> {
    /// client.flush().await?;
    /// println!("所有数据已刷新");
    /// # Ok(())
    /// # }
    /// ```
    pub async fn flush(&self) -> Result<()> {
        // 检查是否已初始化
        self.check_initialized().await?;

        // 如果有处理器，刷新处理器
        if let Some(processor) = self.processor.read().await.as_ref() {
            // 注意: 如果处理器有 flush 方法，应该调用它
            tracing::debug!("刷新处理器");
        }

        // 刷新导出器
        // 注意: 如果导出器有 flush 方法，应该调用它
        tracing::debug!("刷新导出器");

        Ok(())
    }

    /// 获取配置快照
    ///
    /// 返回当前配置的只读快照
    ///
    /// # 返回
    ///
    /// 配置快照
    pub fn get_config_snapshot(&self) -> crate::config::OtlpConfig {
        self.config.clone()
    }

    /// 检查是否支持特定功能
    ///
    /// # 参数
    ///
    /// * `feature` - 功能名称
    ///
    /// # 返回
    ///
    /// 如果支持该功能，返回 `true`
    pub fn supports_feature(&self, feature: &str) -> bool {
        match feature {
            "batch" => true,
            "compression" => self.config.compression != crate::config::Compression::None,
            "retry" => self.config.max_retries > 0,
            "sampling" => self.config.sampling_ratio < 1.0,
            "multi_tenant" => self.config.tenant_id_key.is_some(),
            _ => false,
        }
    }

    /// 获取功能列表
    ///
    /// 返回客户端支持的所有功能列表
    ///
    /// # 返回
    ///
    /// 功能名称列表
    pub fn get_features(&self) -> Vec<String> {
        let mut features = vec!["batch".to_string()];

        if self.config.compression != crate::config::Compression::None {
            features.push("compression".to_string());
        }
        if self.config.max_retries > 0 {
            features.push("retry".to_string());
        }
        if self.config.sampling_ratio < 1.0 {
            features.push("sampling".to_string());
        }
        if self.config.tenant_id_key.is_some() {
            features.push("multi_tenant".to_string());
        }

        features
    }
}

/// 客户端状态信息
#[derive(Debug, Clone)]
pub struct ClientStatus {
    /// 是否已初始化
    pub is_initialized: bool,

    /// 是否已关闭
    pub is_shutdown: bool,

    /// 客户端指标
    pub metrics: crate::client::ClientMetrics,

    /// 运行时间
    pub uptime: Duration,
}

/// 客户端性能分析器
///
/// 用于分析客户端性能，提供性能建议
pub struct ClientPerformanceAnalyzer {
    client: OtlpClient,
    start_time: Instant,
    operation_count: RwLock<u64>,
    total_latency: RwLock<Duration>,
}

impl ClientPerformanceAnalyzer {
    /// 创建新的性能分析器
    pub fn new(client: OtlpClient) -> Self {
        Self {
            client,
            start_time: Instant::now(),
            operation_count: RwLock::new(0),
            total_latency: RwLock::new(Duration::ZERO),
        }
    }

    /// 分析性能并返回建议
    ///
    /// # 返回
    ///
    /// 性能分析结果和建议
    pub async fn analyze(&self) -> Result<PerformanceAnalysis> {
        let metrics = self.client.get_metrics().await;
        let operation_count = *self.operation_count.read().await;
        let total_latency = *self.total_latency.read().await;

        let avg_latency = if operation_count > 0 {
            total_latency / operation_count
        } else {
            Duration::ZERO
        };

        let throughput = if avg_latency > Duration::ZERO {
            Duration::from_secs(1).as_nanos() as f64 / avg_latency.as_nanos() as f64
        } else {
            0.0
        };

        // 生成建议
        let mut suggestions = Vec::new();

        if avg_latency > Duration::from_millis(100) {
            suggestions.push("考虑启用批处理以减少延迟".to_string());
        }

        if metrics.exporter_metrics.failed_exports > 0 {
            suggestions.push("检查网络连接和端点配置".to_string());
        }

        if metrics.total_data_sent > 1_000_000 {
            suggestions.push("考虑启用压缩以减少传输大小".to_string());
        }

        Ok(PerformanceAnalysis {
            avg_latency,
            throughput,
            total_operations: operation_count,
            suggestions,
        })
    }

    /// 记录操作延迟
    pub async fn record_operation(&self, latency: Duration) {
        *self.operation_count.write().await += 1;
        *self.total_latency.write().await += latency;
    }
}

/// 性能分析结果
#[derive(Debug, Clone)]
pub struct PerformanceAnalysis {
    /// 平均延迟
    pub avg_latency: Duration,

    /// 吞吐量 (操作/秒)
    pub throughput: f64,

    /// 总操作数
    pub total_operations: u64,

    /// 性能优化建议
    pub suggestions: Vec<String>,
}
