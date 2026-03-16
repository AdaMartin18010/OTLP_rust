//! # Exception Semantic Conventions
//!
//! Implementation of OpenTelemetry Exception Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/exceptions/exceptions-spans/>
//!
//! ## Features
//!
//! - **Exception Recording**: Type-safe exception attribute capture
//! - **Stack Trace Handling**: Support for stack trace strings and structured frames
//! - **Escaped Exceptions**: Track exceptions that escape their scope
//! - **Error Classification**: Categorize errors by type
//!
//! ## Rust 1.92 Features
//!
//! - **Structured stack traces**: Vector-based stack frame collection
//! - **Type safety**: Enum-based error classification
//! - **Builder pattern**: Ergonomic exception attribute construction
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::exception::{
//!     ExceptionAttributesBuilder, ErrorType,
//! };
//!
//! let attrs = ExceptionAttributesBuilder::new()
//!     .exception_type("RuntimeError")
//!     .message("Failed to connect to database")
//!     .stack_trace("RuntimeError: Failed to connect\n  at /app/db.rs:42:10")
//!     .escaped(true)
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result, SemanticConventionError};
use std::collections::HashMap;

/// Error types classification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorType {
    /// Database connection or query error
    Database,
    /// Network communication error
    Network,
    /// Authentication or authorization error
    Auth,
    /// Validation error
    Validation,
    /// Not found error
    NotFound,
    /// Timeout error
    Timeout,
    /// Rate limiting error
    RateLimit,
    /// Internal server error
    Internal,
    /// External service error
    External,
    /// Configuration error
    Config,
    /// Programming/development error
    Programming,
    /// Unknown error type
    Unknown,
}

impl ErrorType {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorType::Database => "database",
            ErrorType::Network => "network",
            ErrorType::Auth => "auth",
            ErrorType::Validation => "validation",
            ErrorType::NotFound => "not_found",
            ErrorType::Timeout => "timeout",
            ErrorType::RateLimit => "rate_limit",
            ErrorType::Internal => "internal",
            ErrorType::External => "external",
            ErrorType::Config => "config",
            ErrorType::Programming => "programming",
            ErrorType::Unknown => "unknown",
        }
    }
}

impl std::fmt::Display for ErrorType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Represents a single stack frame
#[derive(Debug, Clone, PartialEq)]
pub struct StackFrame {
    /// Function/method name
    pub function: String,
    /// Source file path
    pub file: Option<String>,
    /// Line number
    pub line: Option<u32>,
    /// Column number
    pub column: Option<u32>,
    /// Module/namespace
    pub module: Option<String>,
}

impl StackFrame {
    /// Create a new stack frame
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            file: None,
            line: None,
            column: None,
            module: None,
        }
    }

    /// Set file path
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Set line number
    pub fn with_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    /// Set column number
    pub fn with_column(mut self, column: u32) -> Self {
        self.column = Some(column);
        self
    }

    /// Set module name
    pub fn with_module(mut self, module: impl Into<String>) -> Self {
        self.module = Some(module.into());
        self
    }

    /// Format as string representation
    pub fn format(&self) -> String {
        let mut result = self.function.clone();
        if let Some(file) = &self.file {
            result.push_str(&format!(" at {}", file));
            if let Some(line) = self.line {
                result.push_str(&format!(":{}", line));
                if let Some(column) = self.column {
                    result.push_str(&format!(":{}", column));
                }
            }
        }
        result
    }
}

/// Exception attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct ExceptionAttributes {
    attributes: AttributeMap,
}

impl ExceptionAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for exception attributes
#[derive(Debug, Default)]
pub struct ExceptionAttributesBuilder {
    // Exception information
    exception_type: Option<String>,
    message: Option<String>,
    stack_trace: Option<String>,
    escaped: Option<bool>,

    // Structured stack frames
    stack_frames: Vec<StackFrame>,

    // Error classification
    error_type: Option<ErrorType>,
    error_code: Option<String>,

    // Context
    target: Option<String>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl ExceptionAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set exception type/class name (required for proper exception tracking)
    pub fn exception_type(mut self, type_name: impl Into<String>) -> Self {
        self.exception_type = Some(type_name.into());
        self
    }

    /// Set exception message
    pub fn message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(msg.into());
        self
    }

    /// Set stack trace as string
    pub fn stack_trace(mut self, trace: impl Into<String>) -> Self {
        self.stack_trace = Some(trace.into());
        self
    }

    /// Set whether the exception escaped the span
    pub fn escaped(mut self, is_escaped: bool) -> Self {
        self.escaped = Some(is_escaped);
        self
    }

    /// Add a stack frame
    pub fn add_stack_frame(mut self, frame: StackFrame) -> Self {
        self.stack_frames.push(frame);
        self
    }

    /// Set all stack frames
    pub fn stack_frames(mut self, frames: Vec<StackFrame>) -> Self {
        self.stack_frames = frames;
        self
    }

    /// Set error type classification
    pub fn error_type(mut self, error_type: ErrorType) -> Self {
        self.error_type = Some(error_type);
        self
    }

    /// Set error code
    pub fn error_code(mut self, code: impl Into<String>) -> Self {
        self.error_code = Some(code.into());
        self
    }

    /// Set target service/resource that threw the error
    pub fn target(mut self, target: impl Into<String>) -> Self {
        self.target = Some(target.into());
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the exception attributes
    pub fn build(self) -> Result<ExceptionAttributes> {
        // At minimum, we need either a message or an exception type
        if self.message.is_none() && self.exception_type.is_none() {
            return Err(SemanticConventionError::MissingRequired(
                "exception.message or exception.type".to_string(),
            ));
        }

        let mut attributes = AttributeMap::new();

        // Exception type
        if let Some(type_name) = self.exception_type {
            attributes.insert(
                "exception.type".to_string(),
                AttributeValue::String(type_name),
            );
        }

        // Exception message
        if let Some(msg) = self.message {
            attributes.insert("exception.message".to_string(), AttributeValue::String(msg));
        }

        // Stack trace - use provided string or build from frames
        if let Some(trace) = self.stack_trace {
            attributes.insert(
                "exception.stacktrace".to_string(),
                AttributeValue::String(trace),
            );
        } else if !self.stack_frames.is_empty() {
            let trace = self
                .stack_frames
                .iter()
                .map(|f| f.format())
                .collect::<Vec<_>>()
                .join("\n");
            attributes.insert(
                "exception.stacktrace".to_string(),
                AttributeValue::String(trace),
            );
        }

        // Escaped flag
        if let Some(escaped) = self.escaped {
            attributes.insert(
                "exception.escaped".to_string(),
                AttributeValue::Bool(escaped),
            );
        }

        // Error type classification
        if let Some(error_type) = self.error_type {
            attributes.insert(
                "error.type".to_string(),
                AttributeValue::String(error_type.as_str().to_string()),
            );
        }

        // Error code
        if let Some(code) = self.error_code {
            attributes.insert("error.code".to_string(), AttributeValue::String(code));
        }

        // Target
        if let Some(target) = self.target {
            attributes.insert("error.target".to_string(), AttributeValue::String(target));
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(ExceptionAttributes { attributes })
    }
}

/// Helper function to capture current backtrace as stack frames
#[cfg(feature = "backtrace")]
pub fn capture_backtrace() -> Vec<StackFrame> {
    use backtrace::Backtrace;

    let bt = Backtrace::new();
    let mut frames = Vec::new();

    for frame in bt.frames() {
        for symbol in frame.symbols() {
            let function = symbol
                .name()
                .map(|n| n.to_string())
                .unwrap_or_else(|| "<unknown>".to_string());

            let mut stack_frame = StackFrame::new(function);

            if let Some(file) = symbol.filename() {
                stack_frame.file = Some(file.to_string_lossy().to_string());
            }

            if let Some(line) = symbol.lineno() {
                stack_frame.line = Some(line);
            }

            if let Some(col) = symbol.colno() {
                stack_frame.column = Some(col);
            }

            frames.push(stack_frame);
        }
    }

    frames
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_type() {
        assert_eq!(ErrorType::Database.as_str(), "database");
        assert_eq!(ErrorType::Network.as_str(), "network");
        assert_eq!(ErrorType::Auth.as_str(), "auth");
        assert_eq!(ErrorType::Timeout.as_str(), "timeout");
    }

    #[test]
    fn test_stack_frame() {
        let frame = StackFrame::new("my_function")
            .with_file("/path/to/file.rs")
            .with_line(42)
            .with_column(10)
            .with_module("my_module");

        assert_eq!(frame.function, "my_function");
        assert_eq!(frame.file, Some("/path/to/file.rs".to_string()));
        assert_eq!(frame.line, Some(42));
        assert_eq!(frame.column, Some(10));
        assert_eq!(frame.module, Some("my_module".to_string()));
    }

    #[test]
    fn test_stack_frame_format() {
        let frame = StackFrame::new("test_func")
            .with_file("test.rs")
            .with_line(10);

        assert_eq!(frame.format(), "test_func at test.rs:10");

        let frame2 = StackFrame::new("anon_func");
        assert_eq!(frame2.format(), "anon_func");
    }

    #[test]
    fn test_exception_attributes_builder_minimal() {
        let attrs = ExceptionAttributesBuilder::new()
            .message("Something went wrong")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("exception.message"),
            Some(&AttributeValue::String("Something went wrong".to_string()))
        );
    }

    #[test]
    fn test_exception_attributes_builder_full() {
        let attrs = ExceptionAttributesBuilder::new()
            .exception_type("RuntimeError")
            .message("Failed to connect to database")
            .stack_trace("RuntimeError: Failed to connect\n  at /app/db.rs:42:10")
            .escaped(true)
            .error_type(ErrorType::Database)
            .error_code("ECONNREFUSED")
            .target("postgresql://localhost:5432/mydb")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("exception.type"),
            Some(&AttributeValue::String("RuntimeError".to_string()))
        );
        assert_eq!(
            attrs.get("exception.escaped"),
            Some(&AttributeValue::Bool(true))
        );
        assert_eq!(
            attrs.get("error.type"),
            Some(&AttributeValue::String("database".to_string()))
        );
        assert_eq!(
            attrs.get("error.code"),
            Some(&AttributeValue::String("ECONNREFUSED".to_string()))
        );
    }

    #[test]
    fn test_exception_with_stack_frames() {
        let frames = vec![
            StackFrame::new("outer_func")
                .with_file("main.rs")
                .with_line(10),
            StackFrame::new("inner_func")
                .with_file("lib.rs")
                .with_line(20),
        ];

        let attrs = ExceptionAttributesBuilder::new()
            .exception_type("StackOverflow")
            .stack_frames(frames)
            .build()
            .unwrap();

        let trace = attrs.get("exception.stacktrace");
        assert!(trace.is_some());
        if let Some(AttributeValue::String(s)) = trace {
            assert!(s.contains("outer_func at main.rs:10"));
            assert!(s.contains("inner_func at lib.rs:20"));
        }
    }

    #[test]
    fn test_exception_attributes_builder_missing_required() {
        let result = ExceptionAttributesBuilder::new().build();

        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert!(field.contains("exception.message") || field.contains("exception.type"));
            }
            _ => panic!("Expected MissingRequired error"),
        }
    }

    #[test]
    fn test_exception_custom_attributes() {
        let attrs = ExceptionAttributesBuilder::new()
            .exception_type("CustomError")
            .custom_attribute("custom.retryable", AttributeValue::Bool(true))
            .custom_attribute("custom.retry_after", AttributeValue::Int(5000))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.retryable"),
            Some(&AttributeValue::Bool(true))
        );
        assert_eq!(
            attrs.get("custom.retry_after"),
            Some(&AttributeValue::Int(5000))
        );
    }

    #[test]
    fn test_error_classification_variants() {
        let error_types = vec![
            ErrorType::Database,
            ErrorType::Network,
            ErrorType::Auth,
            ErrorType::Validation,
            ErrorType::NotFound,
            ErrorType::Timeout,
            ErrorType::RateLimit,
            ErrorType::Internal,
            ErrorType::External,
            ErrorType::Config,
            ErrorType::Programming,
            ErrorType::Unknown,
        ];

        for error_type in error_types {
            let attrs = ExceptionAttributesBuilder::new()
                .message("Test")
                .error_type(error_type)
                .build()
                .unwrap();

            assert!(
                attrs.get("error.type").is_some(),
                "error.type should be present for {:?}",
                error_type
            );
        }
    }
}
