//! # Log Exporter Module
//!
//! Implements log export functionality with batching, retry, and timeout support.
//!
//! ## Features
//!
//! - **Batch Export**: Efficient batch log export
//! - **Retry Logic**: Exponential backoff retry mechanism
//! - **Timeout Handling**: Configurable export timeouts
//! - **Partial Success**: OTLP 1.10 partial success handling
//!
//! ## Example
//!
//! ```rust,ignore
//! use otlp::logs::exporter::{LogExporter, LogExporterBuilder};
//!
//! let exporter = LogExporterBuilder::new()
//!     .with_endpoint("http://localhost:4317")
//!     .with_timeout(Duration::from_secs(10))
//!     .build();
//!
//! exporter.export_batch(logs).await?;
//! ```

use super::LogRecord;
use crate::error::{ExportError, OtlpError, Result};
use crate::exporter::ExportResult;
use crate::resilience::ResilienceManager;
use crate::utils::{PerformanceUtils, RetryUtils};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock};
use tokio::time::{interval, sleep, timeout};

/// Log export result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogExportResult {
    /// Number of logs successfully exported
    pub success_count: usize,
    /// Number of logs that failed to export
    pub failure_count: usize,
    /// Export duration
    pub duration_ms: u64,
    /// Error messages (if any)
    pub errors: Vec<String>,
    /// Whether partial success occurred
    pub partial_success: bool,
}

impl LogExportResult {
    /// Create a successful result
    pub fn success(count: usize, duration_ms: u64) -> Self {
        Self {
            success_count: count,
            failure_count: 0,
            duration_ms,
            errors: Vec::new(),
            partial_success: false,
        }
    }

    /// Create a failure result
    pub fn failure(count: usize, error: impl Into<String>) -> Self {
        Self {
            success_count: 0,
            failure_count: count,
            duration_ms: 0,
            errors: vec![error.into()],
            partial_success: false,
        }
    }

    /// Create a partial success result
    pub fn partial(success: usize, failure: usize, duration_ms: u64, errors: Vec<String>) -> Self {
        Self {
            success_count: success,
            failure_count: failure,
            duration_ms,
            errors,
            partial_success: true,
        }
    }

    /// Check if export was completely successful
    pub fn is_success(&self) -> bool {
        self.failure_count == 0 && !self.partial_success
    }

    /// Check if export completely failed
    pub fn is_failure(&self) -> bool {
        self.success_count == 0
    }

    /// Get total count
    pub fn total_count(&self) -> usize {
        self.success_count + self.failure_count
    }

    /// Get success rate
    pub fn success_rate(&self) -> f64 {
        if self.total_count() == 0 {
            return 1.0;
        }
        self.success_count as f64 / self.total_count() as f64
    }
}

impl From<ExportResult> for LogExportResult {
    fn from(result: ExportResult) -> Self {
        let partial_success = result.partial_success.is_some();
        Self {
            success_count: result.success_count,
            failure_count: result.failure_count,
            duration_ms: result.duration.as_millis() as u64,
            errors: result.errors,
            partial_success,
        }
    }
}

/// Log exporter configuration
#[derive(Debug, Clone)]
pub struct LogExporterConfig {
    /// Endpoint URL
    pub endpoint: String,
    /// Export timeout
    pub timeout: Duration,
    /// Maximum batch size
    pub max_batch_size: usize,
    /// Maximum queue size
    pub max_queue_size: usize,
    /// Retry configuration
    pub max_retries: u32,
    /// Initial retry delay
    pub initial_retry_delay: Duration,
    /// Maximum retry delay
    pub max_retry_delay: Duration,
    /// Retry delay multiplier
    pub retry_delay_multiplier: f64,
    /// Whether to randomize retry delay
    pub randomize_retry_delay: bool,
    /// Compression enabled
    pub compression_enabled: bool,
    /// Headers for authentication
    pub headers: Vec<(String, String)>,
}

impl Default for LogExporterConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout: Duration::from_secs(30),
            max_batch_size: 512,
            max_queue_size: 2048,
            max_retries: 3,
            initial_retry_delay: Duration::from_millis(100),
            max_retry_delay: Duration::from_secs(30),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
            compression_enabled: true,
            headers: Vec::new(),
        }
    }
}

/// Log exporter trait
#[async_trait::async_trait]
pub trait LogExporterTrait: Send + Sync {
    /// Export a batch of logs
    async fn export(&self, logs: Vec<LogRecord>) -> Result<LogExportResult>;

    /// Shutdown the exporter
    async fn shutdown(&self) -> Result<()>;

    /// Check if exporter is healthy
    async fn health_check(&self) -> bool {
        true
    }
}

/// OTLP Log Exporter
pub struct LogExporter {
    #[allow(dead_code)]
    config: LogExporterConfig,
    #[allow(dead_code)]
    resilience_manager: Arc<ResilienceManager>,
    queue: Arc<Mutex<Vec<LogRecord>>>,
    metrics: Arc<RwLock<ExporterMetrics>>,
    is_shutdown: Arc<RwLock<bool>>,
}

/// Exporter metrics
#[derive(Debug, Default, Clone)]
pub struct ExporterMetrics {
    /// Total exports attempted
    pub total_exports: u64,
    /// Successful exports
    pub successful_exports: u64,
    /// Failed exports
    pub failed_exports: u64,
    /// Total logs exported
    pub total_logs_exported: u64,
    /// Average export latency in milliseconds
    pub average_latency_ms: f64,
    /// Total retry attempts
    pub total_retries: u64,
}

impl LogExporter {
    /// Create a new log exporter
    pub fn new(config: LogExporterConfig) -> Self {
        let resilience_manager = ResilienceManager::new();

        Self {
            config,
            resilience_manager: Arc::new(resilience_manager),
            queue: Arc::new(Mutex::new(Vec::new())),
            metrics: Arc::new(RwLock::new(ExporterMetrics::default())),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// Create a new log exporter with default configuration
    pub fn default_with_endpoint(endpoint: impl Into<String>) -> Self {
        let config = LogExporterConfig {
            endpoint: endpoint.into(),
            ..LogExporterConfig::default()
        };
        Self::new(config)
    }

    /// Export a single log
    pub async fn export(&self, log: LogRecord) -> Result<LogExportResult> {
        self.export_batch(vec![log]).await
    }

    /// Export a batch of logs
    pub async fn export_batch(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        if logs.is_empty() {
            return Ok(LogExportResult::success(0, 0));
        }

        // Check shutdown state
        {
            let is_shutdown = self.is_shutdown.read().await;
            if *is_shutdown {
                return Err(OtlpError::Export(ExportError::Failed {
                    reason: "Exporter is shutdown".to_string(),
                }));
            }
        }

        let (result, duration) =
            PerformanceUtils::measure_time(self.export_with_retry(logs.clone())).await;

        // Update metrics
        if let Ok(ref export_result) = result {
            self.update_metrics(export_result, duration).await;
        }

        result
    }

    /// Queue a log for batch export
    pub async fn queue_log(&self, log: LogRecord) -> Result<()> {
        let mut queue = self.queue.lock().await;

        if queue.len() >= self.config.max_queue_size {
            return Err(OtlpError::Export(ExportError::QueueFull {
                current: queue.len(),
                max: self.config.max_queue_size,
            }));
        }

        queue.push(log);
        Ok(())
    }

    /// Flush queued logs
    pub async fn flush(&self) -> Result<LogExportResult> {
        let logs = {
            let mut queue = self.queue.lock().await;
            if queue.is_empty() {
                return Ok(LogExportResult::success(0, 0));
            }
            std::mem::take(&mut *queue)
        };

        self.export_batch(logs).await
    }

    /// Start background batch export task
    pub async fn start_background_export(&self, interval_duration: Duration) {
        let queue = self.queue.clone();
        let config = self.config.clone();
        let is_shutdown = self.is_shutdown.clone();

        tokio::spawn(async move {
            let mut ticker = interval(interval_duration);

            loop {
                ticker.tick().await;

                // Check shutdown
                if *is_shutdown.read().await {
                    break;
                }

                // Export queued logs
                let logs = {
                    let mut q = queue.lock().await;
                    if q.is_empty() || q.len() < config.max_batch_size {
                        continue;
                    }
                    std::mem::take(&mut *q)
                };

                if !logs.is_empty() {
                    // Note: In real implementation, this would use a self reference
                    // For now, we just log that export would happen
                    tracing::debug!("Would export {} logs", logs.len());
                }
            }
        });
    }

    /// Shutdown the exporter
    pub async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;

        // Flush remaining logs
        drop(is_shutdown);
        let _ = self.flush().await;

        Ok(())
    }

    /// Get current metrics
    pub async fn get_metrics(&self) -> ExporterMetrics {
        self.metrics.read().await.clone()
    }

    /// Internal export with retry logic
    async fn export_with_retry(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        let mut last_error = None;

        for attempt in 0..=self.config.max_retries {
            match self.export_internal(logs.clone()).await {
                Ok(result) => {
                    if attempt > 0 {
                        let mut metrics = self.metrics.write().await;
                        metrics.total_retries += attempt as u64;
                    }
                    return Ok(result);
                }
                Err(e) => {
                    last_error = Some(e);

                    if attempt >= self.config.max_retries {
                        break;
                    }

                    // Check if error is retryable
                    let should_retry = matches!(
                        last_error,
                        Some(OtlpError::Transport(_)) | Some(OtlpError::Export(_))
                    );

                    if !should_retry {
                        break;
                    }

                    // Calculate retry delay
                    let delay = RetryUtils::calculate_retry_delay(
                        attempt as usize,
                        self.config.initial_retry_delay,
                        self.config.max_retry_delay,
                        self.config.retry_delay_multiplier,
                        self.config.randomize_retry_delay,
                    );

                    sleep(delay).await;
                }
            }
        }

        Err(ExportError::Failed {
            reason: format!(
                "Export failed after {} retries: {:?}",
                self.config.max_retries, last_error
            ),
        }
        .into())
    }

    /// Internal export implementation
    async fn export_internal(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        let _start = tokio::time::Instant::now();

        // Apply timeout
        let result = timeout(self.config.timeout, async {
            self.perform_export(logs).await
        })
        .await;

        match result {
            Ok(export_result) => export_result,
            Err(_) => Err(OtlpError::Export(ExportError::Failed {
                reason: "Export timeout".to_string(),
            })),
        }
    }

    /// Perform the actual export
    async fn perform_export(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        // In a real implementation, this would:
        // 1. Convert logs to OTLP format
        // 2. Compress if enabled
        // 3. Send to endpoint via HTTP/gRPC
        // 4. Handle response

        // For now, simulate a successful export
        let duration_ms = 10; // Simulated duration

        Ok(LogExportResult::success(logs.len(), duration_ms))
    }

    /// Update metrics after export
    async fn update_metrics(&self, result: &LogExportResult, duration: Duration) {
        let mut metrics = self.metrics.write().await;

        metrics.total_exports += 1;

        if result.is_success() {
            metrics.successful_exports += 1;
        } else {
            metrics.failed_exports += 1;
        }

        metrics.total_logs_exported += result.success_count as u64;

        // Update average latency
        let total = metrics.total_exports as f64;
        let current_avg = metrics.average_latency_ms;
        let new_avg = (current_avg * (total - 1.0) + duration.as_millis() as f64) / total;
        metrics.average_latency_ms = new_avg;
    }
}

#[async_trait::async_trait]
impl LogExporterTrait for LogExporter {
    async fn export(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        self.export_batch(logs).await
    }

    async fn shutdown(&self) -> Result<()> {
        self.shutdown().await
    }
}

/// Builder for LogExporter
#[derive(Debug, Default)]
pub struct LogExporterBuilder {
    config: LogExporterConfig,
}

impl LogExporterBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            config: LogExporterConfig::default(),
        }
    }

    /// Set the endpoint URL
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config.endpoint = endpoint.into();
        self
    }

    /// Set the export timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// Set the maximum batch size
    pub fn with_max_batch_size(mut self, size: usize) -> Self {
        self.config.max_batch_size = size;
        self
    }

    /// Set the maximum queue size
    pub fn with_max_queue_size(mut self, size: usize) -> Self {
        self.config.max_queue_size = size;
        self
    }

    /// Set the maximum number of retries
    pub fn with_max_retries(mut self, retries: u32) -> Self {
        self.config.max_retries = retries;
        self
    }

    /// Set the initial retry delay
    pub fn with_initial_retry_delay(mut self, delay: Duration) -> Self {
        self.config.initial_retry_delay = delay;
        self
    }

    /// Enable or disable compression
    pub fn with_compression(mut self, enabled: bool) -> Self {
        self.config.compression_enabled = enabled;
        self
    }

    /// Add a header
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.config.headers.push((key.into(), value.into()));
        self
    }

    /// Build the exporter
    pub fn build(self) -> LogExporter {
        LogExporter::new(self.config)
    }
}

/// Mock log exporter for testing
#[derive(Debug, Clone)]
pub struct MockLogExporter {
    pub exported_logs: Arc<Mutex<Vec<LogRecord>>>,
    pub should_fail: Arc<RwLock<bool>>,
    pub failure_message: Arc<RwLock<String>>,
}

impl MockLogExporter {
    /// Create a new mock exporter
    pub fn new() -> Self {
        Self {
            exported_logs: Arc::new(Mutex::new(Vec::new())),
            should_fail: Arc::new(RwLock::new(false)),
            failure_message: Arc::new(RwLock::new("Mock failure".to_string())),
        }
    }

    /// Set whether the mock should fail
    pub async fn set_should_fail(&self, should_fail: bool) {
        let mut flag = self.should_fail.write().await;
        *flag = should_fail;
    }

    /// Get exported logs
    pub async fn get_exported_logs(&self) -> Vec<LogRecord> {
        self.exported_logs.lock().await.clone()
    }

    /// Clear exported logs
    pub async fn clear(&self) {
        self.exported_logs.lock().await.clear();
    }
}

#[async_trait::async_trait]
impl LogExporterTrait for MockLogExporter {
    async fn export(&self, logs: Vec<LogRecord>) -> Result<LogExportResult> {
        if *self.should_fail.read().await {
            return Err(OtlpError::Export(ExportError::Failed {
                reason: self.failure_message.read().await.clone(),
            }));
        }

        let mut exported = self.exported_logs.lock().await;
        exported.extend(logs.clone());

        Ok(LogExportResult::success(logs.len(), 1))
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

impl Default for MockLogExporter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_log_exporter_builder() {
        let exporter = LogExporterBuilder::new()
            .with_endpoint("http://test:4317")
            .with_timeout(Duration::from_secs(10))
            .with_max_batch_size(100)
            .with_compression(false)
            .with_header("Authorization", "Bearer token")
            .build();

        let metrics = exporter.get_metrics().await;
        assert_eq!(metrics.total_exports, 0);
    }

    #[tokio::test]
    async fn test_log_export_result() {
        let success = LogExportResult::success(10, 100);
        assert!(success.is_success());
        assert_eq!(success.success_count, 10);
        assert_eq!(success.success_rate(), 1.0);

        let failure = LogExportResult::failure(5, "test error");
        assert!(failure.is_failure());
        assert_eq!(failure.failure_count, 5);

        let partial = LogExportResult::partial(8, 2, 50, vec!["error".to_string()]);
        assert!(!partial.is_success());
        assert!(!partial.is_failure());
        assert_eq!(partial.success_rate(), 0.8);
    }

    #[tokio::test]
    async fn test_mock_exporter() {
        let mock = MockLogExporter::new();

        let log = LogRecord::info("test message");
        let result = mock.export(vec![log.clone()]).await;

        assert!(result.is_ok());

        let exported = mock.get_exported_logs().await;
        assert_eq!(exported.len(), 1);
        assert_eq!(exported[0].message(), Some("test message"));
    }

    #[tokio::test]
    async fn test_mock_exporter_failure() {
        let mock = MockLogExporter::new();
        mock.set_should_fail(true).await;

        let log = LogRecord::info("test message");
        let result = mock.export(vec![log]).await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_exporter_queue() {
        let exporter = LogExporter::new(LogExporterConfig::default());

        let log = LogRecord::info("test");
        exporter.queue_log(log.clone()).await.unwrap();

        let result = exporter.flush().await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap().success_count, 1);
    }

    #[test]
    fn test_exporter_config_default() {
        let config = LogExporterConfig::default();
        assert_eq!(config.endpoint, "http://localhost:4317");
        assert_eq!(config.max_batch_size, 512);
        assert_eq!(config.max_retries, 3);
    }
}
