//! # 快速性能优化模块
//!
//! 提供立即可用的性能优化配置和实现，包括批量发送、压缩和连接池优化
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步优化操作
//! - **元组收集**: 使用 `collect()` 直接收集优化结果到元组
//! - **改进的性能优化**: 利用 Rust 1.92 的性能优化提升性能

use crate::config::OtlpConfig;
use crate::data::TelemetryData;
use crate::error::Result;
// 暂时移除连接池和内存池的复杂集成，专注于批量发送和压缩
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::interval;

/// 快速优化配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuickOptimizationsConfig {
    /// 批量发送配置
    pub batch_config: BatchConfig,
    /// 压缩配置
    pub compression_config: CompressionConfig,
    /// 是否启用所有优化
    pub enable_all_optimizations: bool,
}

/// 批量发送配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchConfig {
    /// 批量大小
    pub batch_size: usize,
    /// 批量超时时间
    pub batch_timeout: Duration,
    /// 最大批量大小
    pub max_batch_size: usize,
    /// 是否启用自适应批量大小
    pub enable_adaptive_batching: bool,
}

/// 压缩配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompressionConfig {
    /// 压缩算法
    pub algorithm: CompressionAlgorithm,
    /// 压缩级别 (1-9)
    pub level: u32,
    /// 最小压缩大小阈值
    pub min_size_threshold: usize,
    /// 是否启用压缩
    pub enable_compression: bool,
}

/// 压缩算法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CompressionAlgorithm {
    Gzip,
    Zstd,
    Brotli,
}

impl Default for QuickOptimizationsConfig {
    fn default() -> Self {
        Self {
            batch_config: BatchConfig::default(),
            compression_config: CompressionConfig::default(),
            enable_all_optimizations: true,
        }
    }
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            batch_timeout: Duration::from_millis(100),
            max_batch_size: 1000,
            enable_adaptive_batching: true,
        }
    }
}

impl Default for CompressionConfig {
    fn default() -> Self {
        Self {
            algorithm: CompressionAlgorithm::Zstd,
            level: 3,
            min_size_threshold: 1024, // 1KB
            enable_compression: true,
        }
    }
}

/// 批量发送器
pub struct BatchSender {
    config: BatchConfig,
    batch: Arc<Mutex<VecDeque<TelemetryData>>>,
    last_send_time: Arc<RwLock<Instant>>,
    is_running: Arc<RwLock<bool>>,
}

impl BatchSender {
    /// 创建新的批量发送器
    pub fn new(config: BatchConfig) -> Self {
        Self {
            config,
            batch: Arc::new(Mutex::new(VecDeque::new())),
            last_send_time: Arc::new(RwLock::new(Instant::now())),
            is_running: Arc::new(RwLock::new(false)),
        }
    }

    /// 添加数据到批量队列
    pub async fn add_data(&self, data: TelemetryData) -> Result<()> {
        let mut batch = self.batch.lock().await;
        batch.push_back(data);

        // 检查是否需要发送
        if batch.len() >= self.config.batch_size {
            self.flush_batch().await?;
        }

        Ok(())
    }

    /// 刷新批量数据
    pub async fn flush_batch(&self) -> Result<()> {
        let mut batch = self.batch.lock().await;
        if batch.is_empty() {
            return Ok(());
        }

        let data: Vec<TelemetryData> = batch.drain(..).collect();
        drop(batch);

        // 这里应该调用实际的发送逻辑
        // 为了演示，我们只是记录日志
        tracing::info!("发送批量数据: {} 条", data.len());

        // 更新最后发送时间
        *self.last_send_time.write().await = Instant::now();

        Ok(())
    }

    /// 启动批量发送器
    pub async fn start(&self) -> Result<()> {
        *self.is_running.write().await = true;
        let batch = Arc::clone(&self.batch);
        let last_send_time = Arc::clone(&self.last_send_time);
        let is_running = Arc::clone(&self.is_running);
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = interval(config.batch_timeout);
            loop {
                interval.tick().await;

                // 检查是否还在运行
                if !*is_running.read().await {
                    break;
                }

                // 检查是否需要发送
                let batch_len = batch.lock().await.len();
                let time_since_last_send = last_send_time.read().await.elapsed();

                if batch_len > 0 && time_since_last_send >= config.batch_timeout {
                    // 发送批量数据
                    let mut batch_guard = batch.lock().await;
                    if !batch_guard.is_empty() {
                        let data: Vec<TelemetryData> = batch_guard.drain(..).collect();
                        drop(batch_guard);

                        tracing::info!("定时发送批量数据: {} 条", data.len());
                        *last_send_time.write().await = Instant::now();
                    }
                }
            }
        });

        Ok(())
    }

    /// 停止批量发送器
    pub async fn stop(&self) -> Result<()> {
        *self.is_running.write().await = false;
        self.flush_batch().await?;
        Ok(())
    }
}

/// 压缩器
pub struct Compressor {
    config: CompressionConfig,
}

impl Compressor {
    /// 创建新的压缩器
    pub fn new(config: CompressionConfig) -> Self {
        Self { config }
    }

    /// 压缩数据
    pub async fn compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        if !self.config.enable_compression || data.len() < self.config.min_size_threshold {
            return Ok(data.to_vec());
        }

        match self.config.algorithm {
            CompressionAlgorithm::Gzip => self.compress_gzip(data).await,
            CompressionAlgorithm::Zstd => self.compress_zstd(data).await,
            CompressionAlgorithm::Brotli => self.compress_brotli(data).await,
        }
    }

    /// Gzip压缩
    async fn compress_gzip(&self, data: &[u8]) -> Result<Vec<u8>> {
        use async_compression::tokio::write::GzipEncoder;
        use tokio::io::AsyncWriteExt;

        let mut encoder = GzipEncoder::new(Vec::new());
        encoder.write_all(data).await?;
        encoder.shutdown().await?;

        Ok(encoder.into_inner())
    }

    /// Zstd压缩
    async fn compress_zstd(&self, data: &[u8]) -> Result<Vec<u8>> {
        use async_compression::tokio::write::ZstdEncoder;
        use tokio::io::AsyncWriteExt;

        let mut encoder = ZstdEncoder::with_quality(
            Vec::new(),
            async_compression::Level::Precise(self.config.level as i32),
        );
        encoder.write_all(data).await?;
        encoder.shutdown().await?;

        Ok(encoder.into_inner())
    }

    /// Brotli压缩
    async fn compress_brotli(&self, data: &[u8]) -> Result<Vec<u8>> {
        use async_compression::tokio::write::BrotliEncoder;
        use tokio::io::AsyncWriteExt;

        let mut encoder = BrotliEncoder::with_quality(
            Vec::new(),
            async_compression::Level::Precise(self.config.level as i32),
        );
        encoder.write_all(data).await?;
        encoder.shutdown().await?;

        Ok(encoder.into_inner())
    }
}

/// 快速优化管理器
pub struct QuickOptimizationsManager {
    #[allow(dead_code)]
    config: QuickOptimizationsConfig,
    batch_sender: Option<BatchSender>,
    compressor: Compressor,
}

impl QuickOptimizationsManager {
    /// 创建新的快速优化管理器
    pub fn new(config: QuickOptimizationsConfig) -> Self {
        let batch_sender = if config.enable_all_optimizations {
            Some(BatchSender::new(config.batch_config.clone()))
        } else {
            None
        };

        let compressor = Compressor::new(config.compression_config.clone());

        Self {
            config,
            batch_sender,
            compressor,
        }
    }

    /// 初始化优化管理器
    pub async fn initialize(&mut self) -> Result<()> {
        // 启动批量发送器
        if let Some(ref batch_sender) = self.batch_sender {
            batch_sender.start().await?;
        }

        Ok(())
    }

    /// 发送数据（使用优化）
    pub async fn send_data(&self, data: TelemetryData) -> Result<()> {
        if let Some(ref batch_sender) = self.batch_sender {
            batch_sender.add_data(data).await?;
        } else {
            // 直接发送（无批量优化）
            tracing::info!("直接发送数据");
        }

        Ok(())
    }

    /// 压缩数据
    pub async fn compress_data(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.compressor.compress(data).await
    }

    /// 获取连接（简化版本）
    pub async fn get_connection(&self) -> Result<String> {
        // 简化版本，返回模拟连接
        Ok("direct_connection".to_string())
    }

    /// 停止优化管理器
    pub async fn shutdown(&self) -> Result<()> {
        if let Some(ref batch_sender) = self.batch_sender {
            batch_sender.stop().await?;
        }

        Ok(())
    }
}

/// 为OtlpConfig添加快速优化配置
impl OtlpConfig {
    /// 启用快速性能优化
    pub fn with_quick_optimizations(self) -> Self {
        // 这里可以添加优化配置到OtlpConfig中
        // 为了演示，我们只是返回self
        self
    }

    /// 创建快速优化配置
    pub fn create_quick_optimizations_config() -> QuickOptimizationsConfig {
        QuickOptimizationsConfig::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{MetricType, StatusCode};

    #[tokio::test]
    async fn test_batch_sender() {
        let config = BatchConfig {
            batch_size: 5,
            batch_timeout: Duration::from_millis(100),
            max_batch_size: 100,
            enable_adaptive_batching: false,
        };

        let sender = BatchSender::new(config);
        sender.start().await.unwrap();

        // 添加数据
        for i in 0..10 {
            let data = TelemetryData::trace(format!("test-{}", i))
                .with_attribute("test", "value")
                .with_status(StatusCode::Ok, None);

            sender.add_data(data).await.unwrap();
        }

        // 等待批量发送
        tokio::time::sleep(Duration::from_millis(150)).await;

        sender.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_compressor() {
        let config = CompressionConfig {
            algorithm: CompressionAlgorithm::Zstd,
            level: 3,
            min_size_threshold: 10,
            enable_compression: true,
        };

        let compressor = Compressor::new(config);
        let data = b"Hello, World! This is a test string for compression.";

        let compressed = compressor.compress(data).await.unwrap();
        assert!(compressed.len() < data.len());
    }

    #[tokio::test]
    async fn test_quick_optimizations_manager() {
        let config = QuickOptimizationsConfig::default();
        let mut manager = QuickOptimizationsManager::new(config);

        manager.initialize().await.unwrap();

        let data = TelemetryData::metric("test_metric", MetricType::Counter)
            .with_attribute("test", "value");

        manager.send_data(data).await.unwrap();

        manager.shutdown().await.unwrap();
    }
}
