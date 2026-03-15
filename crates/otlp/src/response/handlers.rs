//! # Response Handlers
//!
//! Provides response classification, automatic retry decisions, and metrics
//! collection for OTLP export operations.
//!
//! ## Response Classification
//!
//! OTLP 1.10 defines three response types:
//! - **Full Success**: All data accepted (`partial_success` field empty)
//! - **Partial Success**: Some data accepted (`partial_success` field present with counts)
//! - **Failure**: No data accepted (error response)
//!
//! ## Retry Behavior
//!
//! Per OTLP specification:
//! - Full Success: No retry needed
//! - Partial Success: MUST NOT retry (server accepted what it could)
//! - Failure: MAY retry based on error type and retry policy
//!
//! ## Example Usage
//!
//! ```rust
//! use otlp::response::{
//!     ResponseClassifier, RetryDecision, ResponseMetricsCollector,
//!     ExportTracePartialSuccess
//! };
//!
//! # fn example() {
//! let classifier = ResponseClassifier::new();
//!
//! // Classify a partial success response
//! let partial = ExportTracePartialSuccess {
//!     rejected_spans: 5,
//!     error_message: "rate limit".to_string(),
//! };
//!
//! let classification = classifier.classify_partial_success(&partial, 100);
//! assert_eq!(classification.decision, RetryDecision::DoNotRetry);
//! # }
//! ```

use super::partial_success::{
    ExportLogsPartialSuccess, ExportMetricsPartialSuccess, ExportProfilesPartialSuccess,
    ExportTracePartialSuccess,
};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};
use std::time::Instant;

/// Response classification result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResponseClassification {
    /// Full success - all data accepted
    FullSuccess,
    /// Partial success - some data accepted
    PartialSuccess,
    /// Complete failure - no data accepted
    Failure,
}

/// Retry decision based on response classification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetryDecision {
    /// Retry the export operation
    Retry,
    /// Do not retry (partial success or permanent failure)
    DoNotRetry,
    /// Retry with backoff
    RetryWithBackoff,
}

impl ResponseClassification {
    /// Check if this is a success (full or partial)
    pub fn is_success(&self) -> bool {
        matches!(self, Self::FullSuccess | Self::PartialSuccess)
    }

    /// Check if this is a full success
    pub fn is_full_success(&self) -> bool {
        matches!(self, Self::FullSuccess)
    }

    /// Check if this is a partial success
    pub fn is_partial_success(&self) -> bool {
        matches!(self, Self::PartialSuccess)
    }

    /// Check if this is a failure
    pub fn is_failure(&self) -> bool {
        matches!(self, Self::Failure)
    }

    /// Get the default retry decision for this classification
    ///
    /// Per OTLP 1.10 spec:
    /// - Full Success: Do not retry
    /// - Partial Success: MUST NOT retry
    /// - Failure: May retry (implementation dependent)
    pub fn default_retry_decision(&self) -> RetryDecision {
        match self {
            Self::FullSuccess => RetryDecision::DoNotRetry,
            Self::PartialSuccess => RetryDecision::DoNotRetry,
            Self::Failure => RetryDecision::RetryWithBackoff,
        }
    }
}

/// Response classifier for OTLP export responses
///
/// Classifies responses according to OTLP 1.10 specification and determines
/// appropriate retry behavior.
#[derive(Debug, Clone, Default)]
pub struct ResponseClassifier {
    /// Threshold for considering partial success as failure
    /// (e.g., 0.5 means >50% rejection is treated as failure)
    partial_failure_threshold: f64,
}

impl ResponseClassifier {
    /// Create a new response classifier with default settings
    pub fn new() -> Self {
        Self {
            partial_failure_threshold: 1.0, // By default, any partial success is still success
        }
    }

    /// Create a classifier with a custom partial failure threshold
    ///
    /// # Arguments
    ///
    /// * `threshold` - Rejection rate above which partial success is treated as failure (0.0-1.0)
    pub fn with_threshold(threshold: f64) -> Self {
        Self {
            partial_failure_threshold: threshold.clamp(0.0, 1.0),
        }
    }

    /// Classify a trace partial success response
    pub fn classify_trace_partial_success(
        &self,
        partial: &ExportTracePartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        self.classify_by_rejection_rate(partial.rejected_spans, total_sent, &partial.error_message)
    }

    /// Classify a metrics partial success response
    pub fn classify_metrics_partial_success(
        &self,
        partial: &ExportMetricsPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        self.classify_by_rejection_rate(
            partial.rejected_data_points,
            total_sent,
            &partial.error_message,
        )
    }

    /// Classify a logs partial success response
    pub fn classify_logs_partial_success(
        &self,
        partial: &ExportLogsPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        self.classify_by_rejection_rate(
            partial.rejected_log_records,
            total_sent,
            &partial.error_message,
        )
    }

    /// Classify a profiles partial success response
    pub fn classify_profiles_partial_success(
        &self,
        partial: &ExportProfilesPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        self.classify_by_rejection_rate(
            partial.rejected_profiles,
            total_sent,
            &partial.error_message,
        )
    }

    /// Internal method to classify based on rejection rate
    fn classify_by_rejection_rate(
        &self,
        rejected: u64,
        total: u64,
        error_message: &str,
    ) -> ClassificationResult {
        if total == 0 {
            return ClassificationResult {
                classification: ResponseClassification::FullSuccess,
                decision: RetryDecision::DoNotRetry,
                success_count: 0,
                rejected_count: 0,
                rejection_rate: 0.0,
                error_message: None,
            };
        }

        let rejection_rate = rejected as f64 / total as f64;
        let success_count = total.saturating_sub(rejected);

        let classification = if rejected == 0 {
            ResponseClassification::FullSuccess
        } else if rejection_rate >= self.partial_failure_threshold {
            ResponseClassification::Failure
        } else {
            ResponseClassification::PartialSuccess
        };

        let decision = classification.default_retry_decision();

        ClassificationResult {
            classification,
            decision,
            success_count,
            rejected_count: rejected,
            rejection_rate,
            error_message: if error_message.is_empty() {
                None
            } else {
                Some(error_message.to_string())
            },
        }
    }

    /// Classify a general error response
    pub fn classify_error(&self, error: &str, is_retryable: bool) -> ClassificationResult {
        ClassificationResult {
            classification: ResponseClassification::Failure,
            decision: if is_retryable {
                RetryDecision::RetryWithBackoff
            } else {
                RetryDecision::DoNotRetry
            },
            success_count: 0,
            rejected_count: 0,
            rejection_rate: 1.0,
            error_message: Some(error.to_string()),
        }
    }
}

/// Classification result containing all relevant information
#[derive(Debug, Clone)]
pub struct ClassificationResult {
    /// The response classification
    pub classification: ResponseClassification,
    /// The recommended retry decision
    pub decision: RetryDecision,
    /// Number of successfully accepted items
    pub success_count: u64,
    /// Number of rejected items
    pub rejected_count: u64,
    /// Rejection rate (0.0 to 1.0)
    pub rejection_rate: f64,
    /// Error message if any
    pub error_message: Option<String>,
}

impl ClassificationResult {
    /// Check if the response indicates success (full or partial)
    pub fn is_success(&self) -> bool {
        self.classification.is_success()
    }

    /// Check if retry is recommended
    pub fn should_retry(&self) -> bool {
        matches!(
            self.decision,
            RetryDecision::Retry | RetryDecision::RetryWithBackoff
        )
    }

    /// Check if backoff is recommended
    pub fn should_backoff(&self) -> bool {
        matches!(self.decision, RetryDecision::RetryWithBackoff)
    }
}

/// Response handler that combines classification and logging
#[derive(Debug, Clone)]
pub struct ResponseHandler {
    classifier: ResponseClassifier,
    metrics_collector: Option<Arc<ResponseMetricsCollector>>,
}

impl ResponseHandler {
    /// Create a new response handler
    pub fn new() -> Self {
        Self {
            classifier: ResponseClassifier::new(),
            metrics_collector: None,
        }
    }

    /// Create a handler with metrics collection
    pub fn with_metrics(metrics: Arc<ResponseMetricsCollector>) -> Self {
        Self {
            classifier: ResponseClassifier::new(),
            metrics_collector: Some(metrics),
        }
    }

    /// Create a handler with custom threshold and metrics
    pub fn with_threshold_and_metrics(
        threshold: f64,
        metrics: Arc<ResponseMetricsCollector>,
    ) -> Self {
        Self {
            classifier: ResponseClassifier::with_threshold(threshold),
            metrics_collector: Some(metrics),
        }
    }

    /// Handle a trace partial success response
    pub fn handle_trace_partial_success(
        &self,
        partial: &ExportTracePartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        let result = self
            .classifier
            .classify_trace_partial_success(partial, total_sent);

        self.process_result(&result);
        result
    }

    /// Handle a metrics partial success response
    pub fn handle_metrics_partial_success(
        &self,
        partial: &ExportMetricsPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        let result = self
            .classifier
            .classify_metrics_partial_success(partial, total_sent);

        self.process_result(&result);
        result
    }

    /// Handle a logs partial success response
    pub fn handle_logs_partial_success(
        &self,
        partial: &ExportLogsPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        let result = self
            .classifier
            .classify_logs_partial_success(partial, total_sent);

        self.process_result(&result);
        result
    }

    /// Handle a profiles partial success response
    pub fn handle_profiles_partial_success(
        &self,
        partial: &ExportProfilesPartialSuccess,
        total_sent: u64,
    ) -> ClassificationResult {
        let result = self
            .classifier
            .classify_profiles_partial_success(partial, total_sent);

        self.process_result(&result);
        result
    }

    /// Handle an error response
    pub fn handle_error(&self, error: &str, is_retryable: bool) -> ClassificationResult {
        let result = self.classifier.classify_error(error, is_retryable);
        self.process_result(&result);
        result
    }

    /// Process the classification result (logging and metrics)
    fn process_result(&self, result: &ClassificationResult) {
        // Log at appropriate level based on classification
        match result.classification {
            ResponseClassification::FullSuccess => {
                tracing::debug!(
                    "Export successful: {} items accepted",
                    result.success_count
                );
            }
            ResponseClassification::PartialSuccess => {
                tracing::warn!(
                    "Partial success: {}/{} items rejected ({:.1}%). Error: {:?}",
                    result.rejected_count,
                    result.success_count + result.rejected_count,
                    result.rejection_rate * 100.0,
                    result.error_message
                );
            }
            ResponseClassification::Failure => {
                tracing::error!(
                    "Export failed: {}. Decision: {:?}",
                    result.error_message.as_deref().unwrap_or("unknown error"),
                    result.decision
                );
            }
        }

        // Update metrics if collector is configured
        if let Some(ref metrics) = self.metrics_collector {
            metrics.record_classification(result);
        }
    }
}

impl Default for ResponseHandler {
    fn default() -> Self {
        Self::new()
    }
}

/// Metrics for response handling
#[derive(Debug, Default)]
struct ResponseMetrics {
    total_responses: AtomicU64,
    full_successes: AtomicU64,
    partial_successes: AtomicU64,
    failures: AtomicU64,
    total_items_sent: AtomicU64,
    total_items_accepted: AtomicU64,
    total_items_rejected: AtomicU64,
}

/// Thread-safe collector for response metrics
///
/// Tracks statistics about export responses for observability.
#[derive(Debug)]
pub struct ResponseMetricsCollector {
    metrics: ResponseMetrics,
    /// Per-error-type counters
    error_counts: RwLock<HashMap<String, u64>>,
    /// Last update time
    last_update: RwLock<Instant>,
}

impl ResponseMetricsCollector {
    /// Create a new metrics collector
    pub fn new() -> Self {
        Self {
            metrics: ResponseMetrics::default(),
            error_counts: RwLock::new(HashMap::new()),
            last_update: RwLock::new(Instant::now()),
        }
    }

    /// Record a classification result
    pub fn record_classification(&self, result: &ClassificationResult) {
        self.metrics
            .total_responses
            .fetch_add(1, Ordering::Relaxed);
        self.metrics
            .total_items_sent
            .fetch_add(result.success_count + result.rejected_count, Ordering::Relaxed);
        self.metrics
            .total_items_accepted
            .fetch_add(result.success_count, Ordering::Relaxed);
        self.metrics
            .total_items_rejected
            .fetch_add(result.rejected_count, Ordering::Relaxed);

        match result.classification {
            ResponseClassification::FullSuccess => {
                self.metrics
                    .full_successes
                    .fetch_add(1, Ordering::Relaxed);
            }
            ResponseClassification::PartialSuccess => {
                self.metrics
                    .partial_successes
                    .fetch_add(1, Ordering::Relaxed);
            }
            ResponseClassification::Failure => {
                self.metrics.failures.fetch_add(1, Ordering::Relaxed);
            }
        }

        // Record error type if present
        if let Some(ref error) = result.error_message {
            let mut counts = self.error_counts.write().unwrap();
            *counts.entry(error.clone()).or_insert(0) += 1;
        }

        *self.last_update.write().unwrap() = Instant::now();
    }

    /// Get total response count
    pub fn total_responses(&self) -> u64 {
        self.metrics.total_responses.load(Ordering::Relaxed)
    }

    /// Get full success count
    pub fn full_successes(&self) -> u64 {
        self.metrics.full_successes.load(Ordering::Relaxed)
    }

    /// Get partial success count
    pub fn partial_successes(&self) -> u64 {
        self.metrics.partial_successes.load(Ordering::Relaxed)
    }

    /// Get failure count
    pub fn failures(&self) -> u64 {
        self.metrics.failures.load(Ordering::Relaxed)
    }

    /// Get total items sent
    pub fn total_items_sent(&self) -> u64 {
        self.metrics.total_items_sent.load(Ordering::Relaxed)
    }

    /// Get total items accepted
    pub fn total_items_accepted(&self) -> u64 {
        self.metrics.total_items_accepted.load(Ordering::Relaxed)
    }

    /// Get total items rejected
    pub fn total_items_rejected(&self) -> u64 {
        self.metrics.total_items_rejected.load(Ordering::Relaxed)
    }

    /// Get overall acceptance rate
    pub fn acceptance_rate(&self) -> f64 {
        let sent = self.total_items_sent();
        if sent == 0 {
            return 1.0;
        }
        self.total_items_accepted() as f64 / sent as f64
    }

    /// Get error counts
    pub fn error_counts(&self) -> HashMap<String, u64> {
        self.error_counts.read().unwrap().clone()
    }

    /// Get the most common error
    pub fn most_common_error(&self) -> Option<(String, u64)> {
        let counts = self.error_counts.read().unwrap();
        counts
            .iter()
            .max_by_key(|(_, count)| *count)
            .map(|(error, count)| (error.clone(), *count))
    }

    /// Get summary statistics
    pub fn summary(&self) -> MetricsSummary {
        let total = self.total_responses();
        let full = self.full_successes();
        let partial = self.partial_successes();
        let failures = self.failures();

        MetricsSummary {
            total_responses: total,
            full_success_rate: if total == 0 {
                0.0
            } else {
                full as f64 / total as f64
            },
            partial_success_rate: if total == 0 {
                0.0
            } else {
                partial as f64 / total as f64
            },
            failure_rate: if total == 0 {
                0.0
            } else {
                failures as f64 / total as f64
            },
            overall_acceptance_rate: self.acceptance_rate(),
            total_items_sent: self.total_items_sent(),
            total_items_accepted: self.total_items_accepted(),
            total_items_rejected: self.total_items_rejected(),
            most_common_error: self.most_common_error(),
        }
    }

    /// Reset all metrics
    pub fn reset(&self) {
        self.metrics.total_responses.store(0, Ordering::Relaxed);
        self.metrics.full_successes.store(0, Ordering::Relaxed);
        self.metrics.partial_successes.store(0, Ordering::Relaxed);
        self.metrics.failures.store(0, Ordering::Relaxed);
        self.metrics
            .total_items_sent
            .store(0, Ordering::Relaxed);
        self.metrics
            .total_items_accepted
            .store(0, Ordering::Relaxed);
        self.metrics
            .total_items_rejected
            .store(0, Ordering::Relaxed);
        self.error_counts.write().unwrap().clear();
        *self.last_update.write().unwrap() = Instant::now();
    }
}

impl Default for ResponseMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Summary of response metrics
#[derive(Debug, Clone)]
pub struct MetricsSummary {
    /// Total number of responses
    pub total_responses: u64,
    /// Rate of full successes (0.0 to 1.0)
    pub full_success_rate: f64,
    /// Rate of partial successes (0.0 to 1.0)
    pub partial_success_rate: f64,
    /// Rate of failures (0.0 to 1.0)
    pub failure_rate: f64,
    /// Overall acceptance rate (0.0 to 1.0)
    pub overall_acceptance_rate: f64,
    /// Total items sent
    pub total_items_sent: u64,
    /// Total items accepted
    pub total_items_accepted: u64,
    /// Total items rejected
    pub total_items_rejected: u64,
    /// Most common error message and count
    pub most_common_error: Option<(String, u64)>,
}

impl MetricsSummary {
    /// Check if the metrics indicate healthy export behavior
    ///
    /// Healthy is defined as:
    /// - Failure rate < 5%
    /// - Overall acceptance rate > 95%
    pub fn is_healthy(&self) -> bool {
        self.failure_rate < 0.05 && self.overall_acceptance_rate > 0.95
    }

    /// Check if attention is needed (high partial success rate)
    ///
    /// Indicates potential issues that may need investigation
    pub fn needs_attention(&self) -> bool {
        self.partial_success_rate > 0.1
    }
}

/// Builder for creating a response handler with custom configuration
#[derive(Debug)]
pub struct ResponseHandlerBuilder {
    threshold: f64,
    enable_metrics: bool,
    metrics: Option<Arc<ResponseMetricsCollector>>,
}

impl ResponseHandlerBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            threshold: 1.0,
            enable_metrics: false,
            metrics: None,
        }
    }

    /// Set the partial failure threshold
    pub fn with_threshold(mut self, threshold: f64) -> Self {
        self.threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Enable metrics collection
    pub fn with_metrics(mut self) -> Self {
        self.enable_metrics = true;
        self
    }

    /// Use an existing metrics collector
    pub fn with_metrics_collector(mut self, metrics: Arc<ResponseMetricsCollector>) -> Self {
        self.metrics = Some(metrics);
        self.enable_metrics = true;
        self
    }

    /// Build the response handler
    pub fn build(self) -> ResponseHandler {
        let classifier = ResponseClassifier::with_threshold(self.threshold);

        let metrics_collector = if self.enable_metrics {
            self.metrics.or_else(|| Some(Arc::new(ResponseMetricsCollector::new())))
        } else {
            None
        };

        ResponseHandler {
            classifier,
            metrics_collector,
        }
    }
}

impl Default for ResponseHandlerBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_response_classification() {
        assert!(ResponseClassification::FullSuccess.is_success());
        assert!(ResponseClassification::FullSuccess.is_full_success());
        assert!(!ResponseClassification::FullSuccess.is_partial_success());
        assert!(!ResponseClassification::FullSuccess.is_failure());

        assert!(ResponseClassification::PartialSuccess.is_success());
        assert!(!ResponseClassification::PartialSuccess.is_full_success());
        assert!(ResponseClassification::PartialSuccess.is_partial_success());
        assert!(!ResponseClassification::PartialSuccess.is_failure());

        assert!(!ResponseClassification::Failure.is_success());
        assert!(!ResponseClassification::Failure.is_full_success());
        assert!(!ResponseClassification::Failure.is_partial_success());
        assert!(ResponseClassification::Failure.is_failure());
    }

    #[test]
    fn test_retry_decision() {
        assert_eq!(
            ResponseClassification::FullSuccess.default_retry_decision(),
            RetryDecision::DoNotRetry
        );
        assert_eq!(
            ResponseClassification::PartialSuccess.default_retry_decision(),
            RetryDecision::DoNotRetry
        );
        assert_eq!(
            ResponseClassification::Failure.default_retry_decision(),
            RetryDecision::RetryWithBackoff
        );
    }

    #[test]
    fn test_classifier_full_success() {
        let classifier = ResponseClassifier::new();
        let partial = ExportTracePartialSuccess::new(0, "success");

        let result = classifier.classify_trace_partial_success(&partial, 100);

        assert_eq!(result.classification, ResponseClassification::FullSuccess);
        assert_eq!(result.decision, RetryDecision::DoNotRetry);
        assert_eq!(result.success_count, 100);
        assert_eq!(result.rejected_count, 0);
        assert_eq!(result.rejection_rate, 0.0);
    }

    #[test]
    fn test_classifier_partial_success() {
        let classifier = ResponseClassifier::new();
        let partial = ExportTracePartialSuccess::new(10, "rate limit");

        let result = classifier.classify_trace_partial_success(&partial, 100);

        assert_eq!(result.classification, ResponseClassification::PartialSuccess);
        assert_eq!(result.decision, RetryDecision::DoNotRetry);
        assert_eq!(result.success_count, 90);
        assert_eq!(result.rejected_count, 10);
        assert_eq!(result.rejection_rate, 0.1);
    }

    #[test]
    fn test_classifier_with_threshold() {
        // Classifier with 0.1 threshold - 20% rejection should be treated as failure
        let classifier = ResponseClassifier::with_threshold(0.15);
        let partial = ExportTracePartialSuccess::new(20, "high rejection");

        let result = classifier.classify_trace_partial_success(&partial, 100);

        assert_eq!(result.classification, ResponseClassification::Failure);
        assert_eq!(result.decision, RetryDecision::RetryWithBackoff);
    }

    #[test]
    fn test_classifier_error() {
        let classifier = ResponseClassifier::new();
        let result = classifier.classify_error("network error", true);

        assert_eq!(result.classification, ResponseClassification::Failure);
        assert_eq!(result.decision, RetryDecision::RetryWithBackoff);
        assert!(result.should_retry());
        assert!(result.should_backoff());
    }

    #[test]
    fn test_classifier_non_retryable_error() {
        let classifier = ResponseClassifier::new();
        let result = classifier.classify_error("invalid data", false);

        assert_eq!(result.decision, RetryDecision::DoNotRetry);
        assert!(!result.should_retry());
    }

    #[test]
    fn test_metrics_collector() {
        let metrics = ResponseMetricsCollector::new();

        // Record a partial success
        let result = ClassificationResult {
            classification: ResponseClassification::PartialSuccess,
            decision: RetryDecision::DoNotRetry,
            success_count: 90,
            rejected_count: 10,
            rejection_rate: 0.1,
            error_message: Some("rate limit".to_string()),
        };

        metrics.record_classification(&result);

        assert_eq!(metrics.total_responses(), 1);
        assert_eq!(metrics.full_successes(), 0);
        assert_eq!(metrics.partial_successes(), 1);
        assert_eq!(metrics.failures(), 0);
        assert_eq!(metrics.total_items_sent(), 100);
        assert_eq!(metrics.total_items_accepted(), 90);
        assert_eq!(metrics.total_items_rejected(), 10);
        assert_eq!(metrics.acceptance_rate(), 0.9);

        let error_counts = metrics.error_counts();
        assert_eq!(error_counts.get("rate limit"), Some(&1));
    }

    #[test]
    fn test_metrics_summary() {
        let metrics = ResponseMetricsCollector::new();

        // Record various responses
        let full = ClassificationResult {
            classification: ResponseClassification::FullSuccess,
            decision: RetryDecision::DoNotRetry,
            success_count: 100,
            rejected_count: 0,
            rejection_rate: 0.0,
            error_message: None,
        };

        let partial = ClassificationResult {
            classification: ResponseClassification::PartialSuccess,
            decision: RetryDecision::DoNotRetry,
            success_count: 90,
            rejected_count: 10,
            rejection_rate: 0.1,
            error_message: Some("rate limit".to_string()),
        };

        let failure = ClassificationResult {
            classification: ResponseClassification::Failure,
            decision: RetryDecision::RetryWithBackoff,
            success_count: 0,
            rejected_count: 100,
            rejection_rate: 1.0,
            error_message: Some("timeout".to_string()),
        };

        metrics.record_classification(&full);
        metrics.record_classification(&partial);
        metrics.record_classification(&failure);

        let summary = metrics.summary();

        assert_eq!(summary.total_responses, 3);
        assert!((summary.full_success_rate - 1.0 / 3.0).abs() < 0.001);
        assert!((summary.partial_success_rate - 1.0 / 3.0).abs() < 0.001);
        assert!((summary.failure_rate - 1.0 / 3.0).abs() < 0.001);
        assert!(!summary.is_healthy()); // 33% failure rate is not healthy
    }

    #[test]
    fn test_response_handler_builder() {
        let handler = ResponseHandlerBuilder::new()
            .with_threshold(0.1)
            .with_metrics()
            .build();

        let partial = ExportTracePartialSuccess::new(5, "test");
        let result = handler.handle_trace_partial_success(&partial, 100);

        assert_eq!(result.classification, ResponseClassification::PartialSuccess);

        // Metrics should be collected
        if let Some(ref metrics) = handler.metrics_collector {
            assert_eq!(metrics.total_responses(), 1);
        }
    }

    #[test]
    fn test_metrics_reset() {
        let metrics = ResponseMetricsCollector::new();

        let result = ClassificationResult {
            classification: ResponseClassification::FullSuccess,
            decision: RetryDecision::DoNotRetry,
            success_count: 100,
            rejected_count: 0,
            rejection_rate: 0.0,
            error_message: None,
        };

        metrics.record_classification(&result);
        assert_eq!(metrics.total_responses(), 1);

        metrics.reset();
        assert_eq!(metrics.total_responses(), 0);
        assert_eq!(metrics.total_items_sent(), 0);
    }
}
