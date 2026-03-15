//! # OTLP Logs Module
//!
//! Complete implementation of the OpenTelemetry Logs signal per OTLP 1.10 specification.
//!
//! ## Features
//!
//! - **Log Data Model**: Complete OTLP 1.10 compliant log structures
//! - **Severity Levels**: Full range from TRACE to FATAL with sub-levels
//! - **Body Types**: Support for string, structured, and array bodies
//! - **Log Processors**: Simple, batch, and filter processors
//! - **Log Exporters**: Batch export with retry and timeout
//! - **Log Appenders**: Integration with `tracing` and `log` crates
//! - **Trace Correlation**: Link logs with traces via trace context
//!
//! ## Usage Example
//!
//! ```rust,ignore
//! use otlp::logs::{LogRecord, SeverityLevel, LogProcessor};
//!
//! // Create a log record
//! let log = LogRecord::builder()
//!     .with_message("Application started")
//!     .with_severity(SeverityLevel::Info)
//!     .with_attribute("service.name", "my-service")
//!     .build();
//!
//! // Process the log
//! processor.emit(log).await?;
//! ```

use crate::data::{AttributeValue, LogBody, LogData, LogTraceContext, SeverityLevel};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

pub mod appender;
pub mod exporter;
pub mod processor;

// Re-export main types
pub use appender::{LogAppender, LogAppenderBuilder};
pub use exporter::{LogExportResult, LogExporter, LogExporterBuilder, LogExporterTrait, LogExporterConfig, ExporterMetrics};
pub use processor::{
    BatchLogProcessor, BatchProcessorConfig, FilterLogProcessor, LogProcessor, 
    SimpleLogProcessor, CompositeLogProcessor, ProcessorMetrics,
};

// Re-export structured logging from appender
pub use appender::structured;

/// A log record represents a single log entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogRecord {
    /// Timestamp when the log was emitted
    pub timestamp: SystemTime,
    /// Timestamp when the log was observed
    pub observed_timestamp: Option<SystemTime>,
    /// Severity level
    pub severity: SeverityLevel,
    /// Severity text (optional custom text)
    pub severity_text: Option<String>,
    /// Body of the log
    pub body: LogBody,
    /// Attributes
    pub attributes: HashMap<String, AttributeValue>,
    /// Trace context for correlation
    pub trace_context: Option<LogTraceContext>,
    /// Dropped attributes count
    pub dropped_attributes_count: u32,
    /// Source code information (optional)
    pub source_location: Option<SourceLocation>,
    /// Instrumentation scope name
    pub instrumentation_scope: Option<String>,
}

impl LogRecord {
    /// Create a new log record builder
    pub fn builder() -> LogRecordBuilder {
        LogRecordBuilder::new()
    }

    /// Create a simple text log
    pub fn info(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Info)
            .build()
    }

    /// Create a warning log
    pub fn warn(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Warn)
            .build()
    }

    /// Create an error log
    pub fn error(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Error)
            .build()
    }

    /// Create a debug log
    pub fn debug(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Debug)
            .build()
    }

    /// Create a trace log
    pub fn trace(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Trace)
            .build()
    }

    /// Create a fatal log
    pub fn fatal(message: impl Into<String>) -> Self {
        Self::builder()
            .with_message(message)
            .with_severity(SeverityLevel::Fatal)
            .build()
    }

    /// Convert to LogData
    pub fn to_log_data(&self) -> LogData {
        let timestamp_nanos = self
            .timestamp
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;

        let observed_timestamp_nanos = self
            .observed_timestamp
            .map(|t| {
                t.duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_nanos() as u64
            })
            .unwrap_or(timestamp_nanos);

        LogData {
            timestamp: timestamp_nanos,
            observed_timestamp: observed_timestamp_nanos,
            severity: self.severity,
            severity_text: self.severity_text.clone(),
            body: self.body.clone(),
            attributes: self.attributes.clone(),
            resource_attributes: HashMap::new(),
            trace_context: self.trace_context.clone(),
            dropped_attributes_count: self.dropped_attributes_count,
            flags: 0,
        }
    }

    /// Check if severity is at least the given level
    pub fn is_at_least(&self, level: SeverityLevel) -> bool {
        self.severity as u8 >= level as u8
    }

    /// Get severity as numeric value
    pub fn severity_number(&self) -> u8 {
        self.severity as u8
    }

    /// Get the message as a string (if body is a string)
    pub fn message(&self) -> Option<&str> {
        self.body.as_string()
    }

    /// Check if this log should be filtered based on severity
    pub fn should_include(&self, min_severity: SeverityLevel) -> bool {
        self.severity >= min_severity
    }
}

impl Default for LogRecord {
    fn default() -> Self {
        Self {
            timestamp: SystemTime::now(),
            observed_timestamp: None,
            severity: SeverityLevel::Info,
            severity_text: None,
            body: LogBody::Empty,
            attributes: HashMap::new(),
            trace_context: None,
            dropped_attributes_count: 0,
            source_location: None,
            instrumentation_scope: None,
        }
    }
}

/// Source code location information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceLocation {
    /// Source file name
    pub file: String,
    /// Line number
    pub line: u32,
    /// Column number
    pub column: u32,
    /// Function name
    pub function_name: Option<String>,
}

/// Builder for LogRecord
#[derive(Debug, Default)]
pub struct LogRecordBuilder {
    timestamp: Option<SystemTime>,
    observed_timestamp: Option<SystemTime>,
    severity: SeverityLevel,
    severity_text: Option<String>,
    body: LogBody,
    attributes: HashMap<String, AttributeValue>,
    trace_context: Option<LogTraceContext>,
    source_location: Option<SourceLocation>,
    instrumentation_scope: Option<String>,
}

impl LogRecordBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            timestamp: Some(SystemTime::now()),
            observed_timestamp: None,
            severity: SeverityLevel::Info,
            severity_text: None,
            body: LogBody::Empty,
            attributes: HashMap::new(),
            trace_context: None,
            source_location: None,
            instrumentation_scope: None,
        }
    }

    /// Set the timestamp
    pub fn with_timestamp(mut self, timestamp: SystemTime) -> Self {
        self.timestamp = Some(timestamp);
        self
    }

    /// Set the observed timestamp
    pub fn with_observed_timestamp(mut self, timestamp: SystemTime) -> Self {
        self.observed_timestamp = Some(timestamp);
        self
    }

    /// Set severity level
    pub fn with_severity(mut self, severity: SeverityLevel) -> Self {
        self.severity = severity;
        if self.severity_text.is_none() {
            self.severity_text = Some(severity.as_str().to_string());
        }
        self
    }

    /// Set severity text
    pub fn with_severity_text(mut self, text: impl Into<String>) -> Self {
        self.severity_text = Some(text.into());
        self
    }

    /// Set the message body
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.body = LogBody::String(message.into());
        self
    }

    /// Set structured body
    pub fn with_structured_body(
        mut self,
        body: HashMap<String, AttributeValue>,
    ) -> Self {
        self.body = LogBody::Structured(body);
        self
    }

    /// Set array body
    pub fn with_array_body(mut self, body: Vec<AttributeValue>) -> Self {
        self.body = LogBody::Array(body);
        self
    }

    /// Set the body
    pub fn with_body(mut self, body: LogBody) -> Self {
        self.body = body;
        self
    }

    /// Add an attribute
    pub fn with_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<AttributeValue>,
    ) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }

    /// Add multiple attributes
    pub fn with_attributes(
        mut self,
        attributes: impl IntoIterator<Item = (impl Into<String>, impl Into<AttributeValue>)>,
    ) -> Self {
        for (key, value) in attributes {
            self.attributes.insert(key.into(), value.into());
        }
        self
    }

    /// Set trace context
    pub fn with_trace_context(mut self, trace_context: LogTraceContext) -> Self {
        self.trace_context = Some(trace_context);
        self
    }

    /// Set trace context from IDs
    pub fn with_trace_ids(
        mut self,
        trace_id: impl Into<String>,
        span_id: impl Into<String>,
    ) -> Self {
        self.trace_context = Some(LogTraceContext::new(trace_id, span_id));
        self
    }

    /// Set source location
    pub fn with_source_location(
        mut self,
        file: impl Into<String>,
        line: u32,
        column: u32,
    ) -> Self {
        self.source_location = Some(SourceLocation {
            file: file.into(),
            line,
            column,
            function_name: None,
        });
        self
    }

    /// Set source location with function name
    pub fn with_source_location_full(
        mut self,
        file: impl Into<String>,
        line: u32,
        column: u32,
        function_name: impl Into<String>,
    ) -> Self {
        self.source_location = Some(SourceLocation {
            file: file.into(),
            line,
            column,
            function_name: Some(function_name.into()),
        });
        self
    }

    /// Set instrumentation scope
    pub fn with_instrumentation_scope(mut self, scope: impl Into<String>) -> Self {
        self.instrumentation_scope = Some(scope.into());
        self
    }

    /// Build the LogRecord
    pub fn build(self) -> LogRecord {
        LogRecord {
            timestamp: self.timestamp.unwrap_or_else(SystemTime::now),
            observed_timestamp: self.observed_timestamp,
            severity: self.severity,
            severity_text: self.severity_text,
            body: self.body,
            attributes: self.attributes,
            trace_context: self.trace_context,
            dropped_attributes_count: 0,
            source_location: self.source_location,
            instrumentation_scope: self.instrumentation_scope,
        }
    }
}

/// Severity filter for log processing
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeverityFilter {
    min_severity: SeverityLevel,
}

impl SeverityFilter {
    /// Create a new severity filter
    pub fn new(min_severity: SeverityLevel) -> Self {
        Self { min_severity }
    }

    /// Check if a log record passes the filter
    pub fn allows(&self, record: &LogRecord) -> bool {
        record.severity >= self.min_severity
    }

    /// Get the minimum severity level
    pub fn min_severity(&self) -> SeverityLevel {
        self.min_severity
    }
}

impl Default for SeverityFilter {
    fn default() -> Self {
        Self {
            min_severity: SeverityLevel::Debug,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_record_builder() {
        let log = LogRecord::builder()
            .with_message("Test message")
            .with_severity(SeverityLevel::Warn)
            .with_attribute("key", AttributeValue::String("value".to_string()))
            .build();

        assert_eq!(log.message(), Some("Test message"));
        assert_eq!(log.severity, SeverityLevel::Warn);
        assert!(log.attributes.contains_key("key"));
        assert!(log.is_at_least(SeverityLevel::Info));
    }

    #[test]
    fn test_log_record_convenience_methods() {
        let info_log = LogRecord::info("info message");
        assert_eq!(info_log.severity, SeverityLevel::Info);

        let warn_log = LogRecord::warn("warn message");
        assert_eq!(warn_log.severity, SeverityLevel::Warn);

        let error_log = LogRecord::error("error message");
        assert_eq!(error_log.severity, SeverityLevel::Error);

        let debug_log = LogRecord::debug("debug message");
        assert_eq!(debug_log.severity, SeverityLevel::Debug);

        let trace_log = LogRecord::trace("trace message");
        assert_eq!(trace_log.severity, SeverityLevel::Trace);

        let fatal_log = LogRecord::fatal("fatal message");
        assert_eq!(fatal_log.severity, SeverityLevel::Fatal);
    }

    #[test]
    fn test_severity_filter() {
        let filter = SeverityFilter::new(SeverityLevel::Warn);
        
        let info_log = LogRecord::info("info");
        let warn_log = LogRecord::warn("warn");
        let error_log = LogRecord::error("error");

        assert!(!filter.allows(&info_log));
        assert!(filter.allows(&warn_log));
        assert!(filter.allows(&error_log));
    }

    #[test]
    fn test_log_record_to_log_data() {
        let record = LogRecord::builder()
            .with_message("Test")
            .with_severity(SeverityLevel::Info)
            .build();

        let log_data = record.to_log_data();
        
        assert_eq!(log_data.severity, SeverityLevel::Info);
        assert!(matches!(log_data.body, LogBody::String(s) if s == "Test"));
    }

    #[test]
    fn test_severity_level_methods() {
        assert_eq!(SeverityLevel::Error.as_str(), "ERROR");
        assert_eq!(SeverityLevel::Warn.short_name(), "WRN");
        assert!(SeverityLevel::Error.is_error());
        assert!(!SeverityLevel::Warn.is_error());
        assert!(SeverityLevel::Warn.is_warn());
        assert!(!SeverityLevel::Info.is_warn());
    }

    #[test]
    fn test_severity_level_parsing() {
        assert_eq!(SeverityLevel::from_str("ERROR"), Some(SeverityLevel::Error));
        assert_eq!(SeverityLevel::from_str("error"), Some(SeverityLevel::Error));
        assert_eq!(SeverityLevel::from_str("ERR"), Some(SeverityLevel::Error));
        assert_eq!(SeverityLevel::from_str("WARN"), Some(SeverityLevel::Warn));
        assert_eq!(SeverityLevel::from_str("WARNING"), Some(SeverityLevel::Warn));
        assert_eq!(SeverityLevel::from_str("INVALID"), None);
    }

    #[test]
    fn test_log_body_conversions() {
        let string_body: LogBody = "test".into();
        assert!(matches!(string_body, LogBody::String(s) if s == "test"));

        let map: HashMap<String, AttributeValue> = [
            ("key".to_string(), AttributeValue::String("value".to_string())),
        ].into_iter().collect();
        let struct_body: LogBody = map.clone().into();
        assert!(matches!(struct_body, LogBody::Structured(m) if m == map));
    }
}
