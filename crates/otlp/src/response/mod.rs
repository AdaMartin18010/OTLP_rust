//! # OTLP Response Handling Module
//!
//! This module provides comprehensive response handling for the OpenTelemetry
//! Protocol (OTLP) according to the OTLP 1.10 specification.
//!
//! ## OTLP 1.10 Response Types
//!
//! The OTLP protocol defines three response types:
//!
//! 1. **Full Success** (`partial_success` field is empty/null)
//!    - The server has accepted all data
//!    - No further action required
//!
//! 2. **Partial Success** (`partial_success` field contains rejection counts)
//!    - The server has accepted some data and rejected the rest
//!    - The client MUST NOT retry the request
//!    - The client SHOULD log a warning with rejection details
//!
//! 3. **Failure** (Error response)
//!    - The server rejected all data
//!    - The client MAY retry based on error type and retry policy
//!
//! ## Module Structure
//!
//! - [`partial_success`]: Partial success response types and handlers
//! - [`handlers`]: Response classification, retry decisions, and metrics
//!
//! ## Example Usage
//!
//! ```rust
//! use otlp::response::{
//!     ExportTracePartialSuccess, PartialSuccessHandler,
//!     ResponseClassifier, ResponseHandler, ResponseMetricsCollector
//! };
//!
//! # fn example() {
//! // Create a handler for trace exports
//! let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
//!
//! // Simulate a partial success response
//! let partial = ExportTracePartialSuccess {
//!     rejected_spans: 5,
//!     error_message: "rate limit exceeded".to_string(),
//! };
//!
//! handler.handle_trace_partial_success(&partial);
//!
//! // Check acceptance
//! if handler.is_acceptable(0.1) {
//!     println!("Acceptable: {}% success rate", handler.success_rate() * 100.0);
//! }
//! # }
//! ```
//!
//! ## Per-Signal Partial Success Types
//!
//! Each signal (Traces, Metrics, Logs, Profiles) has its own partial success type:
//!
//! | Signal | Type | Rejected Field |
//! |--------|------|----------------|
//! | Traces | [`ExportTracePartialSuccess`] | `rejected_spans` |
//! | Metrics | [`ExportMetricsPartialSuccess`] | `rejected_data_points` |
//! | Logs | [`ExportLogsPartialSuccess`] | `rejected_log_records` |
//! | Profiles | [`ExportProfilesPartialSuccess`] | `rejected_profiles` |
//!
//! ## Retry Behavior
//!
//! According to OTLP 1.10 specification:
//!
//! - **Full Success**: No retry needed
//! - **Partial Success**: MUST NOT retry (per spec section "Partial Success")
//! - **Failure**: MAY retry based on error type (e.g., retry on 503, don't retry on 400)

pub mod handlers;
pub mod partial_success;

// Re-export partial success types
pub use partial_success::{
    ExportLogsPartialSuccess, ExportMetricsPartialSuccess, ExportProfilesPartialSuccess,
    ExportTracePartialSuccess, PartialSuccessHandler,
};

// Re-export handler types
pub use handlers::{
    ClassificationResult, MetricsSummary, ResponseClassification, ResponseHandler,
    ResponseHandlerBuilder, ResponseMetricsCollector, RetryDecision,
};

/// Response metadata for tracking export operations
///
/// Provides contextual information about an export response,
/// including timing and correlation data.
#[derive(Debug, Clone)]
pub struct ResponseMetadata {
    /// Request ID for correlation
    pub request_id: String,
    /// Timestamp when the request was sent
    pub request_timestamp: std::time::Instant,
    /// Timestamp when the response was received
    pub response_timestamp: std::time::Instant,
    /// Response processing duration
    pub processing_duration: std::time::Duration,
    /// Signal type (trace, metric, log, profile)
    pub signal_type: SignalType,
    /// Total items in the request
    pub total_items: u64,
}

/// Signal type for response metadata
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignalType {
    /// Trace data
    Trace,
    /// Metric data
    Metric,
    /// Log data
    Log,
    /// Profile data
    Profile,
}

impl ResponseMetadata {
    /// Create new response metadata
    pub fn new(request_id: impl Into<String>, signal_type: SignalType, total_items: u64) -> Self {
        let now = std::time::Instant::now();
        Self {
            request_id: request_id.into(),
            request_timestamp: now,
            response_timestamp: now,
            processing_duration: std::time::Duration::ZERO,
            signal_type,
            total_items,
        }
    }

    /// Set the response timestamp and calculate processing duration
    pub fn set_response_time(&mut self, response_time: std::time::Instant) {
        self.response_timestamp = response_time;
        self.processing_duration = response_time.duration_since(self.request_timestamp);
    }

    /// Get the round-trip time
    pub fn round_trip_time(&self) -> std::time::Duration {
        self.processing_duration
    }
}

impl Default for ResponseMetadata {
    fn default() -> Self {
        Self::new("", SignalType::Trace, 0)
    }
}

impl std::fmt::Display for SignalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignalType::Trace => write!(f, "trace"),
            SignalType::Metric => write!(f, "metric"),
            SignalType::Log => write!(f, "log"),
            SignalType::Profile => write!(f, "profile"),
        }
    }
}

/// Response type enumeration for OTLP exports
///
/// Represents the three possible response types from an OTLP export operation.
#[derive(Debug, Clone)]
pub enum ResponseType {
    /// Full success - all data accepted
    FullSuccess {
        /// Number of items accepted
        accepted_count: u64,
        /// Response metadata
        metadata: ResponseMetadata,
    },
    /// Partial success - some data accepted
    PartialSuccess {
        /// Handler containing partial success details
        handler: PartialSuccessHandler<()>,
        /// Error message from server
        error_message: String,
        /// Response metadata
        metadata: ResponseMetadata,
    },
    /// Complete failure - no data accepted
    Failure {
        /// Error message
        error: String,
        /// Whether the error is retryable
        retryable: bool,
        /// Response metadata
        metadata: ResponseMetadata,
    },
}

impl ResponseType {
    /// Check if this is a full success
    pub fn is_full_success(&self) -> bool {
        matches!(self, Self::FullSuccess { .. })
    }

    /// Check if this is a partial success
    pub fn is_partial_success(&self) -> bool {
        matches!(self, Self::PartialSuccess { .. })
    }

    /// Check if this is a failure
    pub fn is_failure(&self) -> bool {
        matches!(self, Self::Failure { .. })
    }

    /// Check if the response indicates any success (full or partial)
    pub fn is_success(&self) -> bool {
        self.is_full_success() || self.is_partial_success()
    }

    /// Get the success rate (0.0 to 1.0)
    pub fn success_rate(&self) -> f64 {
        match self {
            Self::FullSuccess { .. } => {
                1.0 // Full success is always 100% success rate
            }
            Self::PartialSuccess { handler, .. } => handler.success_rate(),
            Self::Failure { .. } => 0.0,
        }
    }

    /// Get the metadata if available
    pub fn metadata(&self) -> Option<&ResponseMetadata> {
        match self {
            Self::FullSuccess { metadata, .. } => Some(metadata),
            Self::PartialSuccess { metadata, .. } => Some(metadata),
            Self::Failure { metadata, .. } => Some(metadata),
        }
    }

    /// Get the total number of items
    pub fn total_items(&self) -> u64 {
        match self {
            Self::FullSuccess { accepted_count, .. } => *accepted_count,
            Self::PartialSuccess { handler, .. } => handler.total_count(),
            Self::Failure { metadata, .. } => metadata.total_items,
        }
    }

    /// Get the number of accepted items
    pub fn accepted_items(&self) -> u64 {
        match self {
            Self::FullSuccess { accepted_count, .. } => *accepted_count,
            Self::PartialSuccess { handler, .. } => handler.success_count(),
            Self::Failure { .. } => 0,
        }
    }

    /// Get the number of rejected items
    pub fn rejected_items(&self) -> u64 {
        match self {
            Self::FullSuccess { .. } => 0,
            Self::PartialSuccess { handler, .. } => handler.rejected_count(),
            Self::Failure { metadata, .. } => metadata.total_items,
        }
    }

    /// Get the error message if any
    pub fn error_message(&self) -> Option<&str> {
        match self {
            Self::FullSuccess { .. } => None,
            Self::PartialSuccess { error_message, .. } => Some(error_message),
            Self::Failure { error, .. } => Some(error),
        }
    }

    /// Check if the error is retryable (only meaningful for failures)
    pub fn is_retryable(&self) -> bool {
        match self {
            Self::Failure { retryable, .. } => *retryable,
            // Full and partial success should not be retried per spec
            _ => false,
        }
    }
}

/// Response aggregator for collecting and analyzing multiple responses
///
/// Useful for batch processing and statistical analysis of export responses.
#[derive(Debug, Default)]
pub struct ResponseAggregator {
    responses: Vec<ResponseType>,
    total_accepted: u64,
    total_rejected: u64,
}

impl ResponseAggregator {
    /// Create a new response aggregator
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a response to the aggregator
    pub fn add(&mut self, response: ResponseType) {
        self.total_accepted += response.accepted_items();
        self.total_rejected += response.rejected_items();
        self.responses.push(response);
    }

    /// Get the total number of responses
    pub fn response_count(&self) -> usize {
        self.responses.len()
    }

    /// Get the total accepted items across all responses
    pub fn total_accepted(&self) -> u64 {
        self.total_accepted
    }

    /// Get the total rejected items across all responses
    pub fn total_rejected(&self) -> u64 {
        self.total_rejected
    }

    /// Get the overall success rate
    pub fn overall_success_rate(&self) -> f64 {
        let total = self.total_accepted + self.total_rejected;
        if total == 0 {
            return 1.0;
        }
        self.total_accepted as f64 / total as f64
    }

    /// Count responses by type
    pub fn count_by_type(&self) -> (usize, usize, usize) {
        let full = self
            .responses
            .iter()
            .filter(|r| r.is_full_success())
            .count();
        let partial = self
            .responses
            .iter()
            .filter(|r| r.is_partial_success())
            .count();
        let failure = self.responses.iter().filter(|r| r.is_failure()).count();
        (full, partial, failure)
    }

    /// Get all error messages
    pub fn error_messages(&self) -> Vec<&str> {
        self.responses
            .iter()
            .filter_map(|r| r.error_message())
            .collect()
    }

    /// Clear all responses
    pub fn clear(&mut self) {
        self.responses.clear();
        self.total_accepted = 0;
        self.total_rejected = 0;
    }

    /// Get a summary of the aggregated responses
    pub fn summary(&self) -> AggregationSummary {
        let (full, partial, failure) = self.count_by_type();
        let total = self.response_count();

        AggregationSummary {
            total_responses: total,
            full_success_count: full,
            partial_success_count: partial,
            failure_count: failure,
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
                failure as f64 / total as f64
            },
            overall_acceptance_rate: self.overall_success_rate(),
            total_items_accepted: self.total_accepted,
            total_items_rejected: self.total_rejected,
        }
    }
}

/// Summary of aggregated responses
#[derive(Debug, Clone)]
pub struct AggregationSummary {
    /// Total number of responses
    pub total_responses: usize,
    /// Number of full successes
    pub full_success_count: usize,
    /// Number of partial successes
    pub partial_success_count: usize,
    /// Number of failures
    pub failure_count: usize,
    /// Rate of full successes
    pub full_success_rate: f64,
    /// Rate of partial successes
    pub partial_success_rate: f64,
    /// Rate of failures
    pub failure_rate: f64,
    /// Overall item acceptance rate
    pub overall_acceptance_rate: f64,
    /// Total items accepted
    pub total_items_accepted: u64,
    /// Total items rejected
    pub total_items_rejected: u64,
}

impl AggregationSummary {
    /// Check if all responses were successful (full or partial)
    pub fn all_successful(&self) -> bool {
        self.failure_count == 0 && self.total_responses > 0
    }

    /// Check if there were any partial successes
    pub fn had_partial_successes(&self) -> bool {
        self.partial_success_count > 0
    }

    /// Check if there were any failures
    pub fn had_failures(&self) -> bool {
        self.failure_count > 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_response_metadata() {
        let mut metadata = ResponseMetadata::new("req-123", SignalType::Trace, 100);
        assert_eq!(metadata.request_id, "req-123");
        assert_eq!(metadata.signal_type, SignalType::Trace);
        assert_eq!(metadata.total_items, 100);

        std::thread::sleep(std::time::Duration::from_millis(1));
        metadata.set_response_time(Instant::now());
        assert!(metadata.round_trip_time().as_millis() >= 1);
    }

    #[test]
    fn test_signal_type_display() {
        assert_eq!(SignalType::Trace.to_string(), "trace");
        assert_eq!(SignalType::Metric.to_string(), "metric");
        assert_eq!(SignalType::Log.to_string(), "log");
        assert_eq!(SignalType::Profile.to_string(), "profile");
    }

    #[test]
    fn test_response_type_full_success() {
        let metadata = ResponseMetadata::new("req-1", SignalType::Trace, 100);
        let response = ResponseType::FullSuccess {
            accepted_count: 100,
            metadata,
        };

        assert!(response.is_full_success());
        assert!(!response.is_partial_success());
        assert!(!response.is_failure());
        assert!(response.is_success());
        assert_eq!(response.success_rate(), 1.0);
        assert_eq!(response.total_items(), 100);
        assert_eq!(response.accepted_items(), 100);
        assert_eq!(response.rejected_items(), 0);
        assert!(!response.is_retryable());
    }

    #[test]
    fn test_response_type_partial_success() {
        let metadata = ResponseMetadata::new("req-1", SignalType::Trace, 100);
        let mut handler = PartialSuccessHandler::<()>::new(100);
        handler.handle_partial_success_raw(20, "rate limit");

        let response = ResponseType::PartialSuccess {
            handler,
            error_message: "rate limit".to_string(),
            metadata,
        };

        assert!(!response.is_full_success());
        assert!(response.is_partial_success());
        assert!(!response.is_failure());
        assert!(response.is_success());
        assert_eq!(response.success_rate(), 0.8);
        assert_eq!(response.total_items(), 100);
        assert_eq!(response.accepted_items(), 80);
        assert_eq!(response.rejected_items(), 20);
        assert!(!response.is_retryable());
    }

    #[test]
    fn test_response_type_failure() {
        let metadata = ResponseMetadata::new("req-1", SignalType::Trace, 100);
        let response = ResponseType::Failure {
            error: "connection refused".to_string(),
            retryable: true,
            metadata,
        };

        assert!(!response.is_full_success());
        assert!(!response.is_partial_success());
        assert!(response.is_failure());
        assert!(!response.is_success());
        assert_eq!(response.success_rate(), 0.0);
        assert_eq!(response.total_items(), 100);
        assert_eq!(response.accepted_items(), 0);
        assert_eq!(response.rejected_items(), 100);
        assert!(response.is_retryable());
    }

    #[test]
    fn test_response_aggregator() {
        let mut aggregator = ResponseAggregator::new();

        // Add full success
        aggregator.add(ResponseType::FullSuccess {
            accepted_count: 100,
            metadata: ResponseMetadata::new("req-1", SignalType::Trace, 100),
        });

        // Add partial success
        let mut handler = PartialSuccessHandler::<()>::new(100);
        handler.handle_partial_success_raw(10, "rate limit");
        aggregator.add(ResponseType::PartialSuccess {
            handler,
            error_message: "rate limit".to_string(),
            metadata: ResponseMetadata::new("req-2", SignalType::Trace, 100),
        });

        // Add failure
        aggregator.add(ResponseType::Failure {
            error: "timeout".to_string(),
            retryable: true,
            metadata: ResponseMetadata::new("req-3", SignalType::Trace, 100),
        });

        assert_eq!(aggregator.response_count(), 3);
        assert_eq!(aggregator.total_accepted(), 190);
        assert_eq!(aggregator.total_rejected(), 110);

        let (full, partial, failure) = aggregator.count_by_type();
        assert_eq!(full, 1);
        assert_eq!(partial, 1);
        assert_eq!(failure, 1);

        let summary = aggregator.summary();
        assert_eq!(summary.total_responses, 3);
        assert!(summary.had_partial_successes());
        assert!(summary.had_failures());
        assert!(!summary.all_successful());
    }

    #[test]
    fn test_aggregator_clear() {
        let mut aggregator = ResponseAggregator::new();
        aggregator.add(ResponseType::FullSuccess {
            accepted_count: 100,
            metadata: ResponseMetadata::new("req-1", SignalType::Trace, 100),
        });

        assert_eq!(aggregator.response_count(), 1);
        aggregator.clear();
        assert_eq!(aggregator.response_count(), 0);
        assert_eq!(aggregator.total_accepted(), 0);
    }
}
