//! # Partial Success Response Handling
//!
//! Implements OTLP 1.10 Partial Success response handling according to the specification:
//! <https://opentelemetry.io/docs/specs/otlp/#partial-success>
//!
//! ## Key Principles
//!
//! 1. **No Retry on Partial Success**: Per OTLP spec, partial success responses
//!    MUST NOT be retried. The server has accepted what it can.
//! 2. **Warning Logging**: Partial success SHOULD be logged as a warning with
//!    details about rejected items.
//! 3. **Metrics Collection**: Partial success events SHOULD be tracked for
//!    observability of export health.
//!
//! ## Example Usage
//!
//! ```rust
//! use otlp::response::{
//!     ExportTracePartialSuccess, PartialSuccessHandler, ResponseClassification
//! };
//!
//! # fn example() {
//! // Handle partial success for traces
//! let partial = ExportTracePartialSuccess {
//!     rejected_spans: 5,
//!     error_message: "rate limit exceeded".to_string(),
//! };
//!
//! let mut handler = PartialSuccessHandler::new(100);
//! handler.handle_trace_partial_success(&partial);
//!
//! // Check if acceptable (e.g., < 10% rejection rate)
//! if handler.is_acceptable(0.1) {
//!     println!("Acceptable partial success");
//! } else {
//!     println!("High rejection rate - consider backoff");
//! }
//! # }
//! ```

use std::marker::PhantomData;

/// Partial success response for traces
///
/// Contains the count of rejected spans and an error message from the server.
/// The server has accepted the remaining spans successfully.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportTracePartialSuccess {
    /// Number of rejected spans
    pub rejected_spans: u64,
    /// Human-readable error message
    pub error_message: String,
}

impl ExportTracePartialSuccess {
    /// Create a new trace partial success response
    pub fn new(rejected_spans: u64, error_message: impl Into<String>) -> Self {
        Self {
            rejected_spans,
            error_message: error_message.into(),
        }
    }

    /// Check if any spans were rejected
    pub fn has_rejections(&self) -> bool {
        self.rejected_spans > 0
    }
}

/// Partial success response for metrics
///
/// Contains the count of rejected data points and an error message from the server.
/// The server has accepted the remaining data points successfully.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportMetricsPartialSuccess {
    /// Number of rejected data points
    pub rejected_data_points: u64,
    /// Human-readable error message
    pub error_message: String,
}

impl ExportMetricsPartialSuccess {
    /// Create a new metrics partial success response
    pub fn new(rejected_data_points: u64, error_message: impl Into<String>) -> Self {
        Self {
            rejected_data_points,
            error_message: error_message.into(),
        }
    }

    /// Check if any data points were rejected
    pub fn has_rejections(&self) -> bool {
        self.rejected_data_points > 0
    }
}

/// Partial success response for logs
///
/// Contains the count of rejected log records and an error message from the server.
/// The server has accepted the remaining log records successfully.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportLogsPartialSuccess {
    /// Number of rejected log records
    pub rejected_log_records: u64,
    /// Human-readable error message
    pub error_message: String,
}

impl ExportLogsPartialSuccess {
    /// Create a new logs partial success response
    pub fn new(rejected_log_records: u64, error_message: impl Into<String>) -> Self {
        Self {
            rejected_log_records,
            error_message: error_message.into(),
        }
    }

    /// Check if any log records were rejected
    pub fn has_rejections(&self) -> bool {
        self.rejected_log_records > 0
    }
}

/// Partial success response for profiles (Development signal)
///
/// Contains the count of rejected profile records and an error message from the server.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportProfilesPartialSuccess {
    /// Number of rejected profile records
    pub rejected_profiles: u64,
    /// Human-readable error message
    pub error_message: String,
}

impl ExportProfilesPartialSuccess {
    /// Create a new profiles partial success response
    pub fn new(rejected_profiles: u64, error_message: impl Into<String>) -> Self {
        Self {
            rejected_profiles,
            error_message: error_message.into(),
        }
    }

    /// Check if any profiles were rejected
    pub fn has_rejections(&self) -> bool {
        self.rejected_profiles > 0
    }
}

/// Generic partial success handler
///
/// Tracks partial success state and provides utility methods for
/// determining acceptance thresholds and success rates.
///
/// # Type Parameters
///
/// * `T` - A marker type indicating the signal type (Trace, Metric, Log, Profile)
///
/// # Example
///
/// ```rust
/// use otlp::response::{PartialSuccessHandler, ExportTracePartialSuccess};
///
/// # fn example() {
/// let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
///
/// let partial = ExportTracePartialSuccess {
///     rejected_spans: 5,
///     error_message: "rate limited".to_string(),
/// };
///
/// handler.handle_partial_success(&partial);
///
/// assert_eq!(handler.success_rate(), 0.95);
/// assert!(handler.is_acceptable(0.1)); // 5% < 10% threshold
/// # }
/// ```
pub struct PartialSuccessHandler<T> {
    success_count: u64,
    rejected_count: u64,
    total_count: u64,
    error_message: Option<String>,
    _phantom: PhantomData<T>,
}

impl<T> PartialSuccessHandler<T> {
    /// Create a new handler with the total count of items sent
    ///
    /// # Arguments
    ///
    /// * `total_count` - The total number of items in the export request
    pub fn new(total_count: u64) -> Self {
        Self {
            success_count: 0,
            rejected_count: 0,
            total_count,
            error_message: None,
            _phantom: PhantomData,
        }
    }

    /// Handle generic partial success
    ///
    /// Updates the handler state with partial success information and logs
    /// a warning if any items were rejected.
    ///
    /// # Arguments
    ///
    /// * `rejected_count` - Number of items rejected by the server
    /// * `error_message` - Error message from the server
    pub fn handle_partial_success_raw(
        &mut self,
        rejected_count: u64,
        error_message: impl Into<String>,
    ) {
        self.rejected_count = rejected_count;
        self.success_count = self.total_count.saturating_sub(rejected_count);
        let msg = error_message.into();
        self.error_message = Some(msg.clone());

        // Log warning about partial success
        if self.rejected_count > 0 {
            tracing::warn!(
                "Partial success: {}/{} items rejected ({:.1}%). Error: {}",
                self.rejected_count,
                self.total_count,
                self.rejection_rate() * 100.0,
                msg
            );
        }
    }

    /// Check if the response is acceptable based on a rejection rate threshold
    ///
    /// # Arguments
    ///
    /// * `threshold` - Maximum acceptable rejection rate (0.0 to 1.0)
    ///
    /// # Returns
    ///
    /// `true` if the rejection rate is at or below the threshold
    pub fn is_acceptable(&self, threshold: f64) -> bool {
        self.rejection_rate() <= threshold
    }

    /// Get the success rate (0.0 to 1.0)
    ///
    /// Returns 1.0 if total_count is 0 (nothing to send means 100% success)
    pub fn success_rate(&self) -> f64 {
        if self.total_count == 0 {
            return 1.0;
        }
        self.success_count as f64 / self.total_count as f64
    }

    /// Get the rejection rate (0.0 to 1.0)
    ///
    /// Returns 0.0 if total_count is 0
    pub fn rejection_rate(&self) -> f64 {
        if self.total_count == 0 {
            return 0.0;
        }
        self.rejected_count as f64 / self.total_count as f64
    }

    /// Get the success count
    pub fn success_count(&self) -> u64 {
        self.success_count
    }

    /// Get the rejected count
    pub fn rejected_count(&self) -> u64 {
        self.rejected_count
    }

    /// Get the total count
    pub fn total_count(&self) -> u64 {
        self.total_count
    }

    /// Get the error message if any
    pub fn error_message(&self) -> Option<&str> {
        self.error_message.as_deref()
    }

    /// Check if this was a partial success (some items rejected)
    pub fn is_partial(&self) -> bool {
        self.rejected_count > 0
    }

    /// Check if this was a complete success (no items rejected)
    pub fn is_complete_success(&self) -> bool {
        self.rejected_count == 0 && self.total_count > 0
    }

    /// Reset the handler state for reuse
    pub fn reset(&mut self, new_total_count: u64) {
        self.success_count = 0;
        self.rejected_count = 0;
        self.total_count = new_total_count;
        self.error_message = None;
    }
}

impl PartialSuccessHandler<ExportTracePartialSuccess> {
    /// Handle trace partial success response
    pub fn handle_trace_partial_success(&mut self, partial: &ExportTracePartialSuccess) {
        self.handle_partial_success_raw(partial.rejected_spans, partial.error_message.clone());
    }
}

impl PartialSuccessHandler<ExportMetricsPartialSuccess> {
    /// Handle metrics partial success response
    pub fn handle_metrics_partial_success(&mut self, partial: &ExportMetricsPartialSuccess) {
        self.handle_partial_success_raw(
            partial.rejected_data_points,
            partial.error_message.clone(),
        );
    }
}

impl PartialSuccessHandler<ExportLogsPartialSuccess> {
    /// Handle logs partial success response
    pub fn handle_logs_partial_success(&mut self, partial: &ExportLogsPartialSuccess) {
        self.handle_partial_success_raw(
            partial.rejected_log_records,
            partial.error_message.clone(),
        );
    }
}

impl PartialSuccessHandler<ExportProfilesPartialSuccess> {
    /// Handle profiles partial success response
    pub fn handle_profiles_partial_success(&mut self, partial: &ExportProfilesPartialSuccess) {
        self.handle_partial_success_raw(partial.rejected_profiles, partial.error_message.clone());
    }
}

impl<T> Default for PartialSuccessHandler<T> {
    fn default() -> Self {
        Self::new(0)
    }
}

impl<T> std::fmt::Debug for PartialSuccessHandler<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PartialSuccessHandler")
            .field("success_count", &self.success_count)
            .field("rejected_count", &self.rejected_count)
            .field("total_count", &self.total_count)
            .field("success_rate", &self.success_rate())
            .field("error_message", &self.error_message)
            .finish()
    }
}

impl<T> Clone for PartialSuccessHandler<T> {
    fn clone(&self) -> Self {
        Self {
            success_count: self.success_count,
            rejected_count: self.rejected_count,
            total_count: self.total_count,
            error_message: self.error_message.clone(),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trace_partial_success() {
        let partial = ExportTracePartialSuccess::new(5, "rate limit exceeded");
        assert_eq!(partial.rejected_spans, 5);
        assert_eq!(partial.error_message, "rate limit exceeded");
        assert!(partial.has_rejections());

        let no_rejections = ExportTracePartialSuccess::new(0, "success");
        assert!(!no_rejections.has_rejections());
    }

    #[test]
    fn test_metrics_partial_success() {
        let partial = ExportMetricsPartialSuccess::new(10, "quota exceeded");
        assert_eq!(partial.rejected_data_points, 10);
        assert!(partial.has_rejections());
    }

    #[test]
    fn test_logs_partial_success() {
        let partial = ExportLogsPartialSuccess::new(3, "buffer full");
        assert_eq!(partial.rejected_log_records, 3);
        assert!(partial.has_rejections());
    }

    #[test]
    fn test_profiles_partial_success() {
        let partial = ExportProfilesPartialSuccess::new(2, "invalid format");
        assert_eq!(partial.rejected_profiles, 2);
        assert!(partial.has_rejections());
    }

    #[test]
    fn test_partial_success_handler() {
        let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);

        handler.handle_partial_success_raw(10, "some spans rejected");

        assert_eq!(handler.success_count(), 90);
        assert_eq!(handler.rejected_count(), 10);
        assert_eq!(handler.total_count(), 100);
        assert_eq!(handler.success_rate(), 0.9);
        assert_eq!(handler.rejection_rate(), 0.1);
        assert!(handler.is_partial());
        assert!(!handler.is_complete_success());
        assert!(handler.is_acceptable(0.15));
        assert!(!handler.is_acceptable(0.05));
    }

    #[test]
    fn test_handler_with_zero_total() {
        let handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(0);

        assert_eq!(handler.success_rate(), 1.0);
        assert_eq!(handler.rejection_rate(), 0.0);
        assert!(!handler.is_partial());
    }

    #[test]
    fn test_handler_reset() {
        let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
        handler.handle_partial_success_raw(10, "error");

        handler.reset(200);

        assert_eq!(handler.success_count(), 0);
        assert_eq!(handler.rejected_count(), 0);
        assert_eq!(handler.total_count(), 200);
        assert!(handler.error_message().is_none());
    }

    #[test]
    fn test_handler_clone() {
        let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
        handler.handle_partial_success_raw(5, "test error");

        let cloned = handler.clone();

        assert_eq!(cloned.success_count(), handler.success_count());
        assert_eq!(cloned.rejected_count(), handler.rejected_count());
        assert_eq!(cloned.error_message(), handler.error_message());
    }

    #[test]
    fn test_trace_handler_specialized() {
        let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(100);
        let partial = ExportTracePartialSuccess::new(5, "rate limited");

        handler.handle_trace_partial_success(&partial);

        assert_eq!(handler.rejected_count(), 5);
        assert_eq!(handler.success_count(), 95);
    }

    #[test]
    fn test_metrics_handler_specialized() {
        let mut handler = PartialSuccessHandler::<ExportMetricsPartialSuccess>::new(50);
        let partial = ExportMetricsPartialSuccess::new(10, "quota exceeded");

        handler.handle_metrics_partial_success(&partial);

        assert_eq!(handler.rejected_count(), 10);
        assert_eq!(handler.success_count(), 40);
    }

    #[test]
    fn test_logs_handler_specialized() {
        let mut handler = PartialSuccessHandler::<ExportLogsPartialSuccess>::new(200);
        let partial = ExportLogsPartialSuccess::new(20, "buffer full");

        handler.handle_logs_partial_success(&partial);

        assert_eq!(handler.rejected_count(), 20);
        assert_eq!(handler.success_count(), 180);
    }

    #[test]
    fn test_profiles_handler_specialized() {
        let mut handler = PartialSuccessHandler::<ExportProfilesPartialSuccess>::new(30);
        let partial = ExportProfilesPartialSuccess::new(5, "unsupported format");

        handler.handle_profiles_partial_success(&partial);

        assert_eq!(handler.rejected_count(), 5);
        assert_eq!(handler.success_count(), 25);
    }
}
