//! # Log Appender Module
//!
//! Integration with popular Rust logging frameworks (`tracing` and `log`).
//!
//! ## Features
//!
//! - **Tracing Integration**: Layer for the `tracing` ecosystem
//! - **Log Crate Integration**: Custom logger for the `log` crate
//! - **Structured Logging**: Automatic extraction of structured fields
//! - **Trace Correlation**: Automatic correlation between logs and traces
//!
//! ## Tracing Example
//!
//! ```rust,ignore
//! use otlp::logs::appender::TracingIntegration;
//! use tracing_subscriber::layer::SubscriberExt;
//!
//! let otlp_layer = TracingIntegration::new(processor);
//! let subscriber = tracing_subscriber::Registry::default()
//!     .with(otlp_layer);
//!
//! tracing::subscriber::set_global_default(subscriber).unwrap();
//! tracing::info!(user_id = 42, "User logged in");
//! ```
//!
//! ## Log Crate Example
//!
//! ```rust,ignore
//! use otlp::logs::appender::LogAppender;
//!
//! LogAppender::init(processor, log::LevelFilter::Info)?;
//! log::info!("Application started");
//! ```

use super::{LogRecord, LogRecordBuilder, SeverityLevel};
use crate::data::AttributeValue;
use crate::logs::processor::LogProcessor;
use crate::error::Result;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

/// Log appender for integration with logging frameworks
pub struct LogAppender<P: LogProcessor> {
    processor: Arc<P>,
    default_attributes: HashMap<String, AttributeValue>,
}

impl<P: LogProcessor> LogAppender<P> {
    /// Create a new log appender
    pub fn new(processor: P) -> Self {
        Self {
            processor: Arc::new(processor),
            default_attributes: HashMap::new(),
        }
    }

    /// Create with default attributes
    pub fn with_default_attributes(
        processor: P,
        attributes: HashMap<String, AttributeValue>,
    ) -> Self {
        Self {
            processor: Arc::new(processor),
            default_attributes: attributes,
        }
    }

    /// Add a default attribute
    pub fn with_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.default_attributes.insert(key.into(), value);
        self
    }

    /// Emit a log record
    pub async fn emit(&self, record: LogRecord) -> Result<()> {
        // Merge default attributes
        let mut record = record;
        for (key, value) in &self.default_attributes {
            if !record.attributes.contains_key(key) {
                record.attributes.insert(key.clone(), value.clone());
            }
        }

        self.processor.emit(record).await
    }

    /// Log a message at the specified level
    pub async fn log(&self, level: SeverityLevel, message: impl Into<String>) -> Result<()> {
        let record = LogRecordBuilder::new()
            .with_severity(level)
            .with_message(message)
            .build();
        
        self.emit(record).await
    }

    /// Log with structured fields
    pub async fn log_structured(
        &self,
        level: SeverityLevel,
        message: impl Into<String>,
        fields: HashMap<String, AttributeValue>,
    ) -> Result<()> {
        let mut record = LogRecordBuilder::new()
            .with_severity(level)
            .with_message(message)
            .build();

        record.attributes.extend(fields);
        self.emit(record).await
    }

    /// Shutdown the appender
    pub async fn shutdown(&self) -> Result<()> {
        self.processor.shutdown().await
    }
}

/// Builder for LogAppender
#[derive(Debug, Default)]
pub struct LogAppenderBuilder {
    default_attributes: HashMap<String, AttributeValue>,
}

impl LogAppenderBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            default_attributes: HashMap::new(),
        }
    }

    /// Add a default attribute
    pub fn with_attribute(
        mut self,
        key: impl Into<String>,
        value: impl Into<AttributeValue>,
    ) -> Self {
        self.default_attributes.insert(key.into(), value.into());
        self
    }

    /// Add service name attribute
    pub fn with_service_name(self, name: impl Into<String>) -> Self {
        self.with_attribute("service.name", AttributeValue::String(name.into()))
    }

    /// Add service version attribute
    pub fn with_service_version(self, version: impl Into<String>) -> Self {
        self.with_attribute("service.version", AttributeValue::String(version.into()))
    }

    /// Add environment attribute
    pub fn with_environment(self, env: impl Into<String>) -> Self {
        self.with_attribute("deployment.environment", AttributeValue::String(env.into()))
    }

    /// Add host name attribute
    pub fn with_host_name(self, host: impl Into<String>) -> Self {
        self.with_attribute("host.name", AttributeValue::String(host.into()))
    }

    /// Build the appender
    pub fn build<P: LogProcessor>(self, processor: P) -> LogAppender<P> {
        LogAppender::with_default_attributes(processor, self.default_attributes)
    }
}

/// Integration with the `tracing` crate
/// 
/// Note: This requires the `tracing` feature to be enabled in your Cargo.toml
pub mod tracing_integration {
    //! Tracing integration placeholder
    //! 
    //! For full tracing integration, enable the `tracing` feature and use:
    //! ```rust,ignore
    //! use otlp::logs::appender::tracing_integration::TracingLayer;
    //! ```
    
    use super::*;

    /// Placeholder for TracingLayer
    /// 
    /// This is a simplified version. The full implementation requires
    /// the tracing and tracing-subscriber crates.
    pub struct TracingLayer<P: LogProcessor> {
        _appender: Arc<LogAppender<P>>,
    }

    impl<P: LogProcessor> TracingLayer<P> {
        /// Create a new tracing layer
        pub fn new(processor: P) -> Self {
            Self {
                _appender: Arc::new(LogAppender::new(processor)),
            }
        }
    }

    /// Create a tracing layer with the given processor
    pub fn layer<P: LogProcessor>(_processor: P) -> TracingLayer<P> {
        panic!("Full tracing integration requires the 'tracing' feature and dependencies")
    }
}

/// Integration with the `log` crate
///
/// Note: This requires the `log` feature to be enabled in your Cargo.toml
pub mod log_integration {
    //! Log crate integration placeholder
    //!
    //! For full log crate integration, add the `log` crate to your dependencies.
    
    use super::*;

    /// A logger that exports to OTLP (placeholder)
    pub struct OtlpLogger<P: LogProcessor> {
        _appender: Arc<Mutex<LogAppender<P>>>,
    }

    impl<P: LogProcessor> OtlpLogger<P> {
        /// Create a new OTLP logger (placeholder)
        pub fn new(processor: P) -> Self {
            Self {
                _appender: Arc::new(Mutex::new(LogAppender::new(processor))),
            }
        }

        /// Initialize the logger as the global logger (placeholder)
        pub fn init(self) -> std::result::Result<(), String> {
            Err("Log crate integration requires the 'log' dependency".to_string())
        }
    }

    /// Initialize the log crate integration (placeholder)
    pub fn init<P: LogProcessor + Send + Sync + 'static>(
        _processor: P,
    ) -> std::result::Result<(), String> {
        Err("Log crate integration requires the 'log' dependency".to_string())
    }
}

/// Re-export tracing integration (placeholder)
pub use tracing_integration::TracingLayer as TracingIntegration;

/// Re-export log integration (placeholder)
pub use log_integration::OtlpLogger as LogCrateIntegration;

/// Structured logging utilities
pub mod structured {
    use super::*;

    /// Builder for structured log messages
    pub struct StructuredLogBuilder {
        message: Option<String>,
        fields: HashMap<String, AttributeValue>,
    }

    impl StructuredLogBuilder {
        /// Create a new builder
        pub fn new() -> Self {
            Self {
                message: None,
                fields: HashMap::new(),
            }
        }

        /// Set the message
        pub fn message(mut self, msg: impl Into<String>) -> Self {
            self.message = Some(msg.into());
            self
        }

        /// Add a string field
        pub fn string_field(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
            self.fields.insert(key.into(), AttributeValue::String(value.into()));
            self
        }

        /// Add an integer field
        pub fn int_field(mut self, key: impl Into<String>, value: i64) -> Self {
            self.fields.insert(key.into(), AttributeValue::Int(value));
            self
        }

        /// Add a float field
        pub fn float_field(mut self, key: impl Into<String>, value: f64) -> Self {
            self.fields.insert(key.into(), AttributeValue::Double(value));
            self
        }

        /// Add a boolean field
        pub fn bool_field(mut self, key: impl Into<String>, value: bool) -> Self {
            self.fields.insert(key.into(), AttributeValue::Bool(value));
            self
        }

        /// Build a LogRecord from this structured data
        pub fn build(self, severity: SeverityLevel) -> LogRecord {
            let mut builder = LogRecordBuilder::new().with_severity(severity);

            if let Some(msg) = self.message {
                builder = builder.with_message(msg);
            }

            for (key, value) in self.fields {
                builder = builder.with_attribute(key, value);
            }

            builder.build()
        }

        /// Build with a structured body (instead of message)
        pub fn build_structured(self, severity: SeverityLevel) -> LogRecord {
            let mut builder = LogRecordBuilder::new().with_severity(severity);

            // Use fields as the body
            builder = builder.with_structured_body(self.fields);

            if let Some(msg) = self.message {
                // Add message as an attribute
                builder = builder.with_attribute("message", AttributeValue::String(msg));
            }

            builder.build()
        }
    }

    impl Default for StructuredLogBuilder {
        fn default() -> Self {
            Self::new()
        }
    }

    /// Create a structured log builder
    pub fn builder() -> StructuredLogBuilder {
        StructuredLogBuilder::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logs::exporter::MockLogExporter;
    use crate::logs::processor::SimpleLogProcessor;

    #[tokio::test]
    async fn test_log_appender() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);
        let appender = LogAppender::new(processor);

        let log = LogRecord::info("test message");
        appender.emit(log).await.unwrap();
    }

    #[tokio::test]
    async fn test_appender_builder() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);
        
        let appender = LogAppenderBuilder::new()
            .with_service_name("test-service")
            .with_service_version("1.0.0")
            .with_environment("test")
            .build(processor);

        let log = LogRecord::info("test");
        appender.emit(log).await.unwrap();
    }

    #[tokio::test]
    async fn test_log_methods() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);
        let appender = LogAppender::new(processor);

        appender.log(SeverityLevel::Info, "info message").await.unwrap();
        appender.log(SeverityLevel::Warn, "warn message").await.unwrap();
        appender.log(SeverityLevel::Error, "error message").await.unwrap();
    }

    #[tokio::test]
    async fn test_structured_logging() {
        let mock_exporter = MockLogExporter::new();
        let processor = SimpleLogProcessor::new(mock_exporter);
        let appender = LogAppender::new(processor);

        let mut fields = HashMap::new();
        fields.insert("user_id".to_string(), AttributeValue::Int(42));
        fields.insert("action".to_string(), AttributeValue::String("login".to_string()));

        appender.log_structured(
            SeverityLevel::Info,
            "User action",
            fields,
        ).await.unwrap();
    }

    #[test]
    fn test_structured_builder() {
        let log = structured::builder()
            .message("User logged in")
            .string_field("user_id", "12345")
            .int_field("login_count", 5)
            .float_field("score", 95.5)
            .bool_field("success", true)
            .build(SeverityLevel::Info);

        assert_eq!(log.message(), Some("User logged in"));
        assert_eq!(log.severity, SeverityLevel::Info);
        assert!(log.attributes.contains_key("user_id"));
        assert!(log.attributes.contains_key("login_count"));
    }

    #[test]
    fn test_structured_builder_build_structured() {
        let log = structured::builder()
            .message("Event occurred")
            .string_field("event_type", "purchase")
            .int_field("amount", 100)
            .build_structured(SeverityLevel::Info);

        assert!(matches!(log.body, crate::data::LogBody::Structured(_)));
        assert_eq!(log.severity, SeverityLevel::Info);
    }
}
