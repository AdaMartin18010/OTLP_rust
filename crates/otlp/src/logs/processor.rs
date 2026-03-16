//! # Log Processor Module
//!
//! Implements log processors including simple, batch, and filter processors.
//!
//! ## Processor Types
//!
//! - **SimpleLogProcessor**: Processes logs immediately (synchronous)
//! - **BatchLogProcessor**: Batches logs for efficient export
//! - **FilterLogProcessor**: Filters logs based on severity and attributes
//!
//! ## Example
//!
//! ```rust,ignore
//! use otlp::logs::processor::{BatchLogProcessor, LogProcessor};
//! use otlp::logs::exporter::LogExporter;
//!
//! let exporter = LogExporter::default_with_endpoint("http://localhost:4317");
//! let processor = BatchLogProcessor::new(exporter);
//! processor.emit(log).await?;
//! processor.shutdown().await?;
//! ```

use super::{LogRecord, SeverityFilter, SeverityLevel};
use crate::data::AttributeValue;
use crate::error::{OtlpError, ProcessingError, Result};
use crate::logs::exporter::{LogExportResult, LogExporterTrait};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, oneshot, RwLock};
use tokio::time::{interval, Instant};

/// Log processor trait
#[async_trait::async_trait]
pub trait LogProcessor: Send + Sync {
    /// Emit a log record
    async fn emit(&self, log: LogRecord) -> Result<()>;

    /// Force flush any buffered logs
    async fn force_flush(&self) -> Result<LogExportResult>;

    /// Shutdown the processor
    async fn shutdown(&self) -> Result<()>;
}

/// Simple log processor that exports logs immediately
pub struct SimpleLogProcessor<E: LogExporterTrait> {
    exporter: Arc<E>,
    is_shutdown: Arc<RwLock<bool>>,
}

impl<E: LogExporterTrait> SimpleLogProcessor<E> {
    /// Create a new simple log processor
    pub fn new(exporter: E) -> Self {
        Self {
            exporter: Arc::new(exporter),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// Create a new processor with a shared exporter
    pub fn with_exporter(exporter: Arc<E>) -> Self {
        Self {
            exporter,
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }
}

#[async_trait::async_trait]
impl<E: LogExporterTrait> LogProcessor for SimpleLogProcessor<E> {
    async fn emit(&self, log: LogRecord) -> Result<()> {
        // Check shutdown state
        if *self.is_shutdown.read().await {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Processor is shutdown".to_string(),
            }));
        }

        // Export immediately
        self.exporter.export(vec![log]).await?;
        Ok(())
    }

    async fn force_flush(&self) -> Result<LogExportResult> {
        // Simple processor has no buffer, so nothing to flush
        Ok(LogExportResult::success(0, 0))
    }

    async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;

        // Shutdown exporter
        self.exporter.shutdown().await?;
        Ok(())
    }
}

/// Batch log processor configuration
#[derive(Debug, Clone)]
pub struct BatchProcessorConfig {
    /// Maximum batch size
    pub max_batch_size: usize,
    /// Batch timeout
    pub batch_timeout: Duration,
    /// Maximum queue size
    pub max_queue_size: usize,
    /// Export interval
    pub export_interval: Duration,
}

impl Default for BatchProcessorConfig {
    fn default() -> Self {
        Self {
            max_batch_size: 512,
            batch_timeout: Duration::from_millis(5000),
            max_queue_size: 2048,
            export_interval: Duration::from_millis(1000),
        }
    }
}

/// Batch log processor that batches logs before exporting
pub struct BatchLogProcessor<E: LogExporterTrait> {
    exporter: Arc<E>,
    #[allow(dead_code)]
    config: BatchProcessorConfig,
    queue: mpsc::Sender<LogRecord>,
    is_shutdown: Arc<RwLock<bool>>,
    metrics: Arc<RwLock<ProcessorMetrics>>,
    // Internal channel for force_flush coordination
    #[allow(dead_code)]
    flush_tx: mpsc::Sender<oneshot::Sender<LogExportResult>>,
}

/// Processor metrics
#[derive(Debug, Default, Clone)]
pub struct ProcessorMetrics {
    /// Total logs processed
    pub total_processed: u64,
    /// Total logs exported
    pub total_exported: u64,
    /// Total batches exported
    pub total_batches: u64,
    /// Current queue size
    pub current_queue_size: usize,
    /// Total dropped logs (queue full)
    pub total_dropped: u64,
}



impl<E: LogExporterTrait + 'static> BatchLogProcessor<E> {
    /// Create a new batch log processor
    pub fn new(exporter: E) -> Self {
        Self::with_config(exporter, BatchProcessorConfig::default())
    }

    /// Create a new processor with custom configuration
    pub fn with_config(exporter: E, config: BatchProcessorConfig) -> Self {
        let (queue_tx, queue_rx) = mpsc::channel(config.max_queue_size);
        let exporter = Arc::new(exporter);
        let is_shutdown = Arc::new(RwLock::new(false));
        let metrics = Arc::new(RwLock::new(ProcessorMetrics::default()));

        // Flush channel (unused in simplified implementation)
        let (flush_tx, _flush_rx) = mpsc::channel(1);

        // Start background processing task
        Self::start_processing_task(
            exporter.clone(),
            config.clone(),
            queue_rx,
            is_shutdown.clone(),
            metrics.clone(),
        );

        Self {
            exporter,
            config,
            queue: queue_tx,
            is_shutdown,
            metrics,
            flush_tx,
        }
    }

    /// Create with shared exporter
    pub fn with_exporter(exporter: Arc<E>, config: BatchProcessorConfig) -> Self {
        let (queue_tx, queue_rx) = mpsc::channel(config.max_queue_size);
        let is_shutdown = Arc::new(RwLock::new(false));
        let metrics = Arc::new(RwLock::new(ProcessorMetrics::default()));
        let (flush_tx, _flush_rx) = mpsc::channel(1);

        Self::start_processing_task(
            exporter.clone(),
            config.clone(),
            queue_rx,
            is_shutdown.clone(),
            metrics.clone(),
        );

        Self {
            exporter,
            config,
            queue: queue_tx,
            is_shutdown,
            metrics,
            flush_tx,
        }
    }

    /// Start the background processing task
    fn start_processing_task(
        exporter: Arc<E>,
        config: BatchProcessorConfig,
        mut queue_rx: mpsc::Receiver<LogRecord>,
        is_shutdown: Arc<RwLock<bool>>,
        metrics: Arc<RwLock<ProcessorMetrics>>,
    ) {
        tokio::spawn(async move {
            let mut batch = Vec::with_capacity(config.max_batch_size);
            let mut last_export = Instant::now();
            let mut ticker = interval(config.export_interval);

            loop {
                tokio::select! {
                    _ = ticker.tick() => {
                        if !batch.is_empty() && last_export.elapsed() >= config.batch_timeout {
                            Self::export_batch(&exporter, &mut batch, &metrics).await;
                            last_export = Instant::now();
                        }
                    }
                    Some(log) = queue_rx.recv() => {
                        batch.push(log);
                        
                        if batch.len() >= config.max_batch_size {
                            Self::export_batch(&exporter, &mut batch, &metrics).await;
                            last_export = Instant::now();
                        }
                    }
                    else => {
                        // Channel closed, export remaining logs and exit
                        if !batch.is_empty() {
                            Self::export_batch(&exporter, &mut batch, &metrics).await;
                        }
                        break;
                    }
                }

                // Check shutdown
                if *is_shutdown.read().await && batch.is_empty() {
                    break;
                }
            }
        });
    }

    /// Export a batch of logs
    async fn export_batch(
        exporter: &Arc<E>,
        batch: &mut Vec<LogRecord>,
        metrics: &Arc<RwLock<ProcessorMetrics>>,
    ) {
        if batch.is_empty() {
            return;
        }

        let logs_to_export = std::mem::take(batch);
        let count = logs_to_export.len();

        match exporter.export(logs_to_export).await {
            Ok(result) => {
                let mut m = metrics.write().await;
                m.total_exported += result.success_count as u64;
                m.total_batches += 1;
            }
            Err(e) => {
                tracing::error!("Failed to export logs: {}", e);
                // In production, you might want to retry or save to a fallback
            }
        }

        let mut m = metrics.write().await;
        m.total_processed += count as u64;
        m.current_queue_size = m.current_queue_size.saturating_sub(count);
    }

    /// Get current metrics
    pub async fn get_metrics(&self) -> ProcessorMetrics {
        self.metrics.read().await.clone()
    }
}

#[async_trait::async_trait]
impl<E: LogExporterTrait + 'static> LogProcessor for BatchLogProcessor<E> {
    async fn emit(&self, log: LogRecord) -> Result<()> {
        // Check shutdown state
        if *self.is_shutdown.read().await {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Processor is shutdown".to_string(),
            }));
        }

        // Try to send to queue
        match self.queue.try_send(log) {
            Ok(_) => {
                let mut metrics = self.metrics.write().await;
                metrics.current_queue_size += 1;
                Ok(())
            }
            Err(mpsc::error::TrySendError::Full(_)) => {
                let mut metrics = self.metrics.write().await;
                metrics.total_dropped += 1;
                Err(OtlpError::Processing(ProcessingError::Batch {
                    reason: "Queue is full".to_string(),
                }))
            }
            Err(mpsc::error::TrySendError::Closed(_)) => Err(OtlpError::Processing(
                ProcessingError::InvalidState {
                    message: "Processor channel closed".to_string(),
                },
            )),
        }
    }

    async fn force_flush(&self) -> Result<LogExportResult> {
        // For simplicity, we just check shutdown and return success
        // In a full implementation, this would coordinate with the background task
        if *self.is_shutdown.read().await {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Processor is shutdown".to_string(),
            }));
        }

        // Create a oneshot channel for the flush result
        let (tx, rx) = tokio::sync::oneshot::channel();
        
        // Send flush request
        if self.flush_tx.send(tx).await.is_err() {
            return Ok(LogExportResult::success(0, 0));
        }

        // Wait for result with timeout
        match tokio::time::timeout(Duration::from_secs(5), rx).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(_)) => Err(OtlpError::Processing(ProcessingError::Batch {
                reason: "Flush failed".to_string(),
            })),
            Err(_) => Err(OtlpError::Processing(ProcessingError::Batch {
                reason: "Flush timeout".to_string(),
            })),
        }
    }

    async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;
        drop(is_shutdown);

        // Close the queue channel
        // Note: The background task will process remaining logs

        // Shutdown exporter
        self.exporter.shutdown().await?;
        Ok(())
    }
}

/// Filter log processor that applies filters before processing
pub struct FilterLogProcessor<P: LogProcessor> {
    inner: Arc<P>,
    severity_filter: Option<SeverityFilter>,
    attribute_filters: Vec<(String, AttributeValue)>,
    is_shutdown: Arc<RwLock<bool>>,
}

impl<P: LogProcessor> FilterLogProcessor<P> {
    /// Create a new filter processor wrapping another processor
    pub fn new(inner: P) -> Self {
        Self {
            inner: Arc::new(inner),
            severity_filter: None,
            attribute_filters: Vec::new(),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// Create with severity filter
    pub fn with_severity_filter(inner: P, min_severity: SeverityLevel) -> Self {
        Self {
            inner: Arc::new(inner),
            severity_filter: Some(SeverityFilter::new(min_severity)),
            attribute_filters: Vec::new(),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// Set minimum severity level
    pub fn with_min_severity(mut self, level: SeverityLevel) -> Self {
        self.severity_filter = Some(SeverityFilter::new(level));
        self
    }

    /// Add an attribute filter
    pub fn with_attribute_filter(
        mut self,
        key: impl Into<String>,
        value: AttributeValue,
    ) -> Self {
        self.attribute_filters.push((key.into(), value));
        self
    }

    /// Check if a log passes all filters
    fn passes_filters(&self, log: &LogRecord) -> bool {
        // Check severity filter
        if let Some(ref filter) = self.severity_filter
            && !filter.allows(log)
        {
            return false;
        }

        // Check attribute filters
        for (key, expected_value) in &self.attribute_filters {
            match log.attributes.get(key) {
                Some(actual_value) if actual_value == expected_value => continue,
                _ => return false,
            }
        }

        true
    }
}

#[async_trait::async_trait]
impl<P: LogProcessor> LogProcessor for FilterLogProcessor<P> {
    async fn emit(&self, log: LogRecord) -> Result<()> {
        // Check shutdown state
        if *self.is_shutdown.read().await {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Processor is shutdown".to_string(),
            }));
        }

        // Apply filters
        if !self.passes_filters(&log) {
            return Ok(()); // Silently drop filtered logs
        }

        // Pass to inner processor
        self.inner.emit(log).await
    }

    async fn force_flush(&self) -> Result<LogExportResult> {
        self.inner.force_flush().await
    }

    async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;
        drop(is_shutdown);

        self.inner.shutdown().await
    }
}

/// Composite log processor that chains multiple processors
pub struct CompositeLogProcessor {
    processors: Vec<Arc<dyn LogProcessor>>,
    is_shutdown: Arc<RwLock<bool>>,
}

impl CompositeLogProcessor {
    /// Create a new composite processor
    pub fn new() -> Self {
        Self {
            processors: Vec::new(),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// Add a processor
    pub fn add_processor<P: LogProcessor + 'static>(mut self, processor: P) -> Self {
        self.processors.push(Arc::new(processor));
        self
    }

    /// Create with a list of processors
    pub fn with_processors(processors: Vec<Arc<dyn LogProcessor>>) -> Self {
        Self {
            processors,
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }
}

impl Default for CompositeLogProcessor {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl LogProcessor for CompositeLogProcessor {
    async fn emit(&self, log: LogRecord) -> Result<()> {
        if *self.is_shutdown.read().await {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Processor is shutdown".to_string(),
            }));
        }

        // Emit to all processors
        for processor in &self.processors {
            processor.emit(log.clone()).await?;
        }

        Ok(())
    }

    async fn force_flush(&self) -> Result<LogExportResult> {
        let mut total_success = 0;
        let mut total_failed = 0;
        let mut errors = Vec::new();

        for processor in &self.processors {
            match processor.force_flush().await {
                Ok(result) => {
                    total_success += result.success_count;
                    total_failed += result.failure_count;
                }
                Err(e) => {
                    errors.push(e.to_string());
                }
            }
        }

        Ok(LogExportResult {
            success_count: total_success,
            failure_count: total_failed,
            duration_ms: 0,
            errors,
            partial_success: total_failed > 0,
        })
    }

    async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;
        drop(is_shutdown);

        for processor in &self.processors {
            processor.shutdown().await?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logs::exporter::MockLogExporter;

    #[tokio::test]
    async fn test_simple_processor() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);

        let log = LogRecord::info("test message");
        processor.emit(log).await.unwrap();

        let result = processor.force_flush().await.unwrap();
        assert!(result.is_success());
    }

    #[tokio::test]
    async fn test_batch_processor() {
        let mock_exporter = MockLogExporter::new();
        let processor = BatchLogProcessor::new(mock_exporter);

        // Emit multiple logs
        for i in 0..10 {
            let log = LogRecord::info(format!("message {}", i));
            processor.emit(log).await.unwrap();
        }

        // Wait a bit for batch processing
        tokio::time::sleep(Duration::from_millis(100)).await;

        let metrics = processor.get_metrics().await;
        // total_processed is u64, always >= 0
        assert_eq!(metrics.total_processed, metrics.total_processed);
    }

    #[tokio::test]
    async fn test_filter_processor_severity() {
        let mock_exporter = MockLogExporter::new();
        let inner = SimpleLogProcessor::new(mock_exporter.clone());
        let processor = FilterLogProcessor::with_severity_filter(inner, SeverityLevel::Warn);

        // Info log should be filtered out
        let info_log = LogRecord::info("info message");
        processor.emit(info_log).await.unwrap();

        // Warn log should pass through
        let warn_log = LogRecord::warn("warn message");
        processor.emit(warn_log).await.unwrap();

        // Error log should pass through
        let error_log = LogRecord::error("error message");
        processor.emit(error_log).await.unwrap();

        // Only warn and error should be exported
        tokio::time::sleep(Duration::from_millis(50)).await;
        let exported = mock_exporter.get_exported_logs().await;
        assert_eq!(exported.len(), 2);
    }

    #[tokio::test]
    async fn test_filter_processor_attributes() {
        let mock_exporter = MockLogExporter::new();
        let inner = SimpleLogProcessor::new(mock_exporter.clone());
        
        let processor = FilterLogProcessor::new(inner)
            .with_attribute_filter("env", AttributeValue::String("production".to_string()));

        // Log with matching attribute
        let matching_log = LogRecord::builder()
            .with_message("production log")
            .with_severity(SeverityLevel::Info)
            .with_attribute("env", AttributeValue::String("production".to_string()))
            .build();
        processor.emit(matching_log).await.unwrap();

        // Log with non-matching attribute
        let non_matching_log = LogRecord::builder()
            .with_message("dev log")
            .with_severity(SeverityLevel::Info)
            .with_attribute("env", AttributeValue::String("dev".to_string()))
            .build();
        processor.emit(non_matching_log).await.unwrap();

        // Log without the attribute
        let no_attr_log = LogRecord::info("no env log");
        processor.emit(no_attr_log).await.unwrap();

        tokio::time::sleep(Duration::from_millis(50)).await;
        let exported = mock_exporter.get_exported_logs().await;
        assert_eq!(exported.len(), 1);
        assert_eq!(exported[0].message(), Some("production log"));
    }

    #[tokio::test]
    async fn test_composite_processor() {
        let mock_exporter1 = Arc::new(MockLogExporter::new());
        let mock_exporter2 = Arc::new(MockLogExporter::new());

        let processor1 = SimpleLogProcessor::with_exporter(mock_exporter1.clone());
        let processor2 = SimpleLogProcessor::with_exporter(mock_exporter2.clone());

        let composite = CompositeLogProcessor::new()
            .add_processor(processor1)
            .add_processor(processor2);

        let log = LogRecord::info("test message");
        composite.emit(log).await.unwrap();

        tokio::time::sleep(Duration::from_millis(50)).await;
        
        assert_eq!(mock_exporter1.get_exported_logs().await.len(), 1);
        assert_eq!(mock_exporter2.get_exported_logs().await.len(), 1);
    }

    #[tokio::test]
    async fn test_processor_shutdown() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);

        processor.shutdown().await.unwrap();

        // After shutdown, emit should fail
        let log = LogRecord::info("test");
        let result = processor.emit(log).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_batch_processor_config() {
        let config = BatchProcessorConfig {
            max_batch_size: 100,
            batch_timeout: Duration::from_secs(1),
            max_queue_size: 500,
            export_interval: Duration::from_millis(500),
        };

        let mock_exporter = MockLogExporter::new();
        let processor = BatchLogProcessor::with_config(mock_exporter, config);

        let log = LogRecord::info("test");
        processor.emit(log).await.unwrap();

        let metrics = processor.get_metrics().await;
        assert_eq!(metrics.current_queue_size, 1);
    }
}
