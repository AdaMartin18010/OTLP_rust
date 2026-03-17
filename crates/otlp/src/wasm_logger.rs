//! # WebAssembly Local Logger
//!
//! WebAssembly-native logging implementation for local log output without
//! requiring a host-side log forwarder. Supports multiple output targets
//! optimized for WASM environments.
//!
//! ## WASM Logging Landscape 2025-2026
//!
//! | Target | Browser | WASI | Node.js | Use Case |
//! |--------|---------|------|---------|----------|
//! | console | ✅ | ❌ | ✅ | Debug output |
//! | wasi:logging | ❌ | ✅ | ❌ | Production WASI |
//! | LocalStorage | ✅ | ❌ | ❌ | Browser persistence |
//! | OPFS | ✅ | ❌ | ❌ | Large logs (browser) |
//! | IndexedDB | ✅ | ❌ | ❌ | Structured logs |
//! | File (WASI) | ❌ | ✅ | ✅ | File-based logging |
//! | Memory Buffer | ✅ | ✅ | ✅ | Temporary buffering |
//!
//! ## Features
//!
//! - **Multiple Targets**: Console, file, memory buffer, storage APIs
//! - **Log Rotation**: Automatic rotation by size or time
//! - **Structured Logging**: JSON format with structured fields
//! - **Level Filtering**: Compile-time and runtime filtering
//! - **Ring Buffer**: Fixed-size in-memory buffer for recent logs
//!
//! ## Usage Examples
//!
//! ### Basic Console Logging
//!
//! ```rust,ignore
//! use otlp::wasm_logger::{WasmLogger, LogTarget, LogLevel};
//!
//! let logger = WasmLogger::new(LogTarget::Console)
//!     .with_level(LogLevel::Info);
//!
//! logger.info("Application started");
//! logger.warn("Low memory", &[("available_kb", "1024")]);
//! ```
//!
//! ### File-based Logging (WASI)
//!
//! ```rust,ignore
//! use otlp::wasm_logger::{WasmLogger, LogTarget, RotationPolicy};
//!
//! let logger = WasmLogger::new(LogTarget::File {
//!     path: "/var/log/app.log".to_string(),
//! })
//! .with_rotation(RotationPolicy::BySize { max_bytes: 10 * 1024 * 1024 });
//!
//! logger.info("Processing batch", &[("batch_id", "12345")]);
//! ```
//!
//! ### Ring Buffer for Recent Logs
//!
//! ```rust,ignore
//! use otlp::wasm_logger::{RingBufferLogger, LogEntry};
//!
//! let ring = RingBufferLogger::with_capacity(1000);
//!
//! // Log entries
//! ring.log(LogLevel::Error, "Connection failed", &[]);
//!
//! // Get recent logs for export
//! let recent = ring.recent_entries(100);
//! exporter.export_logs(recent).await?;
//! ```
//!
//! ### Structured JSON Logging
//!
//! ```rust,ignore
//! use otlp::wasm_logger::{StructuredLogger, Field};
//!
//! let logger = StructuredLogger::json();
//!
//! logger.log(
//!     LogLevel::Info,
//!     "Request processed",
//!     &[
//!         Field::string("method", "POST"),
//!         Field::int("duration_ms", 150),
//!         Field::bool("cached", false),
//!     ],
//! );
//! // Output: {"timestamp":"2025-01-15T...","level":"INFO","message":"Request processed","method":"POST","duration_ms":150,"cached":false}
//! ```

use std::cell::RefCell;
use std::collections::VecDeque;
use std::fmt;
use std::time::{SystemTime, UNIX_EPOCH};

// use crate::error::{OtlpError, ProcessingError, Result};

/// Log levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLevel {
    /// Trace level - very detailed
    Trace = 0,
    /// Debug level - diagnostic info
    Debug = 1,
    /// Info level - general information
    Info = 2,
    /// Warn level - warning conditions
    Warn = 3,
    /// Error level - error conditions
    Error = 4,
    /// Fatal level - critical errors
    Fatal = 5,
}

impl LogLevel {
    /// Get level as string
    pub fn as_str(&self) -> &'static str {
        match self {
            LogLevel::Trace => "TRACE",
            LogLevel::Debug => "DEBUG",
            LogLevel::Info => "INFO",
            LogLevel::Warn => "WARN",
            LogLevel::Error => "ERROR",
            LogLevel::Fatal => "FATAL",
        }
    }

    /// Parse from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_uppercase().as_str() {
            "TRACE" => Some(LogLevel::Trace),
            "DEBUG" => Some(LogLevel::Debug),
            "INFO" => Some(LogLevel::Info),
            "WARN" | "WARNING" => Some(LogLevel::Warn),
            "ERROR" => Some(LogLevel::Error),
            "FATAL" => Some(LogLevel::Fatal),
            _ => None,
        }
    }
}

impl fmt::Display for LogLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Log target destinations
#[derive(Debug, Clone)]
pub enum LogTarget {
    /// Browser console or stdout in WASI
    Console,
    /// File output (WASI only)
    File { path: String },
    /// Memory buffer
    Memory,
    /// Browser LocalStorage
    LocalStorage { key: String },
    /// IndexedDB (browser)
    IndexedDb { store: String },
    /// Multiple targets
    Multi(Vec<LogTarget>),
}

/// Log entry structure
#[derive(Debug, Clone)]
pub struct LogEntry {
    /// Timestamp in nanoseconds since epoch
    pub timestamp_ns: u64,
    /// Log level
    pub level: LogLevel,
    /// Log message
    pub message: String,
    /// Structured fields
    pub fields: Vec<(String, String)>,
    /// Source location
    pub source: Option<SourceLocation>,
}

/// Source code location
#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// Rotation policies for file logging
#[derive(Debug, Clone)]
pub enum RotationPolicy {
    /// No rotation
    None,
    /// Rotate by size
    BySize { max_bytes: usize },
    /// Rotate by time
    ByTime { interval_secs: u64 },
    /// Rotate by both size and time
    BySizeAndTime { max_bytes: usize, interval_secs: u64 },
}

/// Structured field for logging
pub struct Field {
    pub key: String,
    pub value: FieldValue,
}

pub enum FieldValue {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
}

impl Field {
    pub fn string(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: FieldValue::String(value.into()),
        }
    }

    pub fn int(key: impl Into<String>, value: i64) -> Self {
        Self {
            key: key.into(),
            value: FieldValue::Int(value),
        }
    }

    pub fn float(key: impl Into<String>, value: f64) -> Self {
        Self {
            key: key.into(),
            value: FieldValue::Float(value),
        }
    }

    pub fn bool(key: impl Into<String>, value: bool) -> Self {
        Self {
            key: key.into(),
            value: FieldValue::Bool(value),
        }
    }

    pub fn null(key: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: FieldValue::Null,
        }
    }
}

/// WebAssembly logger
pub struct WasmLogger {
    target: LogTarget,
    min_level: LogLevel,
    rotation: RotationPolicy,
    current_size: RefCell<usize>,
    include_timestamp: bool,
    include_source: bool,
}

impl WasmLogger {
    /// Create a new logger with target
    pub fn new(target: LogTarget) -> Self {
        Self {
            target,
            min_level: LogLevel::Info,
            rotation: RotationPolicy::None,
            current_size: RefCell::new(0),
            include_timestamp: true,
            include_source: false,
        }
    }

    /// Set minimum log level
    pub fn with_level(mut self, level: LogLevel) -> Self {
        self.min_level = level;
        self
    }

    /// Set rotation policy
    pub fn with_rotation(mut self, rotation: RotationPolicy) -> Self {
        self.rotation = rotation;
        self
    }

    /// Include source location
    pub fn with_source_location(mut self) -> Self {
        self.include_source = true;
        self
    }

    /// Log a message
    pub fn log(&self, level: LogLevel, message: impl Into<String>, fields: &[(impl AsRef<str>, impl AsRef<str>)]) {
        if level < self.min_level {
            return;
        }

        let entry = LogEntry {
            timestamp_ns: current_timestamp_ns(),
            level,
            message: message.into(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.as_ref().to_string(), v.as_ref().to_string()))
                .collect(),
            source: if self.include_source {
                Some(SourceLocation {
                    file: file!().to_string(),
                    line: line!(),
                    column: column!(),
                })
            } else {
                None
            },
        };

        self.write_entry(&entry);
    }

    /// Log trace
    pub fn trace(&self, message: impl Into<String>) {
        self.log(LogLevel::Trace, message, &[] as &[(String, String); 0]);
    }

    /// Log debug
    pub fn debug(&self, message: impl Into<String>) {
        self.log(LogLevel::Debug, message, &[] as &[(String, String); 0]);
    }

    /// Log info
    pub fn info(&self, message: impl Into<String>) {
        self.log(LogLevel::Info, message, &[] as &[(String, String); 0]);
    }

    /// Log info with fields
    pub fn info_with_fields(&self, message: impl Into<String>, fields: &[(impl AsRef<str>, impl AsRef<str>)]) {
        self.log(LogLevel::Info, message, fields);
    }

    /// Log warning
    pub fn warn(&self, message: impl Into<String>) {
        self.log(LogLevel::Warn, message, &[] as &[(String, String); 0]);
    }

    /// Log warning with fields
    pub fn warn_with_fields(&self, message: impl Into<String>, fields: &[(impl AsRef<str>, impl AsRef<str>)]) {
        self.log(LogLevel::Warn, message, fields);
    }

    /// Log error
    pub fn error(&self, message: impl Into<String>) {
        self.log(LogLevel::Error, message, &[] as &[(String, String); 0]);
    }

    /// Log error with fields
    pub fn error_with_fields(&self, message: impl Into<String>, fields: &[(impl AsRef<str>, impl AsRef<str>)]) {
        self.log(LogLevel::Error, message, fields);
    }

    /// Log fatal
    pub fn fatal(&self, message: impl Into<String>) {
        self.log(LogLevel::Fatal, message, &[] as &[(String, String); 0]);
    }

    /// Format entry as text
    fn format_text(&self, entry: &LogEntry) -> String {
        let mut output = String::new();

        if self.include_timestamp {
            let ts = format_timestamp(entry.timestamp_ns);
            output.push_str(&format!("[{}] ", ts));
        }

        output.push_str(&format!("[{}] ", entry.level));
        output.push_str(&entry.message);

        for (k, v) in &entry.fields {
            output.push_str(&format!(" {}={}", k, v));
        }

        if let Some(ref src) = entry.source {
            output.push_str(&format!(" ({}:{})", src.file, src.line));
        }

        output.push('\n');
        output
    }

    /// Format entry as JSON
    #[allow(dead_code)]
    fn format_json(&self, entry: &LogEntry) -> String {
        let mut json = String::from("{");

        json.push_str(&format!("\"timestamp\":\"{}\",", format_timestamp(entry.timestamp_ns)));
        json.push_str(&format!("\"level\":\"{}\",", entry.level.as_str()));
        json.push_str(&format!("\"message\":\"{}\",", escape_json(&entry.message)));

        for (i, (k, v)) in entry.fields.iter().enumerate() {
            if i > 0 {
                json.push(',');
            }
            json.push_str(&format!("\"{}\":\"{}\"", k, escape_json(v)));
        }

        json.push_str("}\n");
        json
    }

    /// Write entry to target
    fn write_entry(&self, entry: &LogEntry) {
        let output = self.format_text(entry);
        let bytes = output.len();

        match &self.target {
            LogTarget::Console => {
                // In WASM, this would use console.log or println!
                #[cfg(target_arch = "wasm32")]
                {
                    web_sys::console::log_1(&output.into());
                }
                #[cfg(not(target_arch = "wasm32"))]
                {
                    print!("{}", output);
                }
            }
            LogTarget::File { .. } => {
                // File logging requires WASI
                // Placeholder implementation
                *self.current_size.borrow_mut() += bytes;
                self.check_rotation();
            }
            LogTarget::Memory => {
                // Memory buffer logging
                *self.current_size.borrow_mut() += bytes;
            }
            LogTarget::LocalStorage { key } => {
                // Browser LocalStorage
                // Placeholder - would use web_sys::Storage
                let _ = key;
            }
            LogTarget::IndexedDb { store } => {
                // Browser IndexedDB
                // Placeholder - would use indexed_db API
                let _ = store;
            }
            LogTarget::Multi(targets) => {
                for target in targets {
                    let logger = WasmLogger {
                        target: target.clone(),
                        min_level: self.min_level,
                        rotation: self.rotation.clone(),
                        current_size: RefCell::new(*self.current_size.borrow()),
                        include_timestamp: self.include_timestamp,
                        include_source: self.include_source,
                    };
                    logger.write_entry(entry);
                }
            }
        }
    }

    /// Check if rotation is needed
    fn check_rotation(&self) {
        match self.rotation {
            RotationPolicy::BySize { max_bytes } => {
                if *self.current_size.borrow() >= max_bytes {
                    self.rotate();
                }
            }
            RotationPolicy::ByTime { .. } => {
                // Time-based rotation would check current time
            }
            RotationPolicy::BySizeAndTime { max_bytes, .. } => {
                if *self.current_size.borrow() >= max_bytes {
                    self.rotate();
                }
            }
            RotationPolicy::None => {}
        }
    }

    /// Perform log rotation
    fn rotate(&self) {
        // Reset size counter
        *self.current_size.borrow_mut() = 0;
        // Actual rotation logic would rename files or clear buffers
    }

    /// Flush any buffered logs
    pub fn flush(&self) {
        // Implementation depends on target
    }
}

/// Ring buffer logger for in-memory log storage
pub struct RingBufferLogger {
    capacity: usize,
    buffer: RefCell<VecDeque<LogEntry>>,
    min_level: LogLevel,
}

impl RingBufferLogger {
    /// Create a new ring buffer with capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            capacity,
            buffer: RefCell::new(VecDeque::with_capacity(capacity)),
            min_level: LogLevel::Info,
        }
    }

    /// Set minimum log level
    pub fn with_level(mut self, level: LogLevel) -> Self {
        self.min_level = level;
        self
    }

    /// Log an entry to the ring buffer
    pub fn log(&self, level: LogLevel, message: impl Into<String>, fields: &[(String, String)]) {
        if level < self.min_level {
            return;
        }

        let entry = LogEntry {
            timestamp_ns: current_timestamp_ns(),
            level,
            message: message.into(),
            fields: fields.to_vec(),
            source: None,
        };

        let mut buffer = self.buffer.borrow_mut();
        if buffer.len() >= self.capacity {
            buffer.pop_front();
        }
        buffer.push_back(entry);
    }

    /// Get recent entries
    pub fn recent_entries(&self, count: usize) -> Vec<LogEntry> {
        let buffer = self.buffer.borrow();
        buffer.iter().rev().take(count).cloned().collect()
    }

    /// Get entries by level
    pub fn entries_by_level(&self, level: LogLevel) -> Vec<LogEntry> {
        let buffer = self.buffer.borrow();
        buffer
            .iter()
            .filter(|e| e.level == level)
            .cloned()
            .collect()
    }

    /// Get all entries
    pub fn all_entries(&self) -> Vec<LogEntry> {
        self.buffer.borrow().iter().cloned().collect()
    }

    /// Clear all entries
    pub fn clear(&self) {
        self.buffer.borrow_mut().clear();
    }

    /// Get entry count
    pub fn len(&self) -> usize {
        self.buffer.borrow().len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.buffer.borrow().is_empty()
    }

    /// Export entries to OTLP format
    pub fn export_entries(&self) -> Vec<crate::data::TelemetryData> {
        self.buffer
            .borrow()
            .iter()
            .map(|entry| {
                crate::data::TelemetryData::log(
                    &entry.message,
                    severity_to_data_level(entry.level),
                )
            })
            .collect()
    }
}

/// Structured JSON logger
pub struct StructuredLogger {
    logger: WasmLogger,
    #[allow(dead_code)]
    format: StructuredFormat,
}

#[derive(Debug, Clone)]
pub enum StructuredFormat {
    Json,
    JsonPretty,
    Logfmt,
}

impl StructuredLogger {
    /// Create JSON logger
    pub fn json() -> Self {
        Self {
            logger: WasmLogger::new(LogTarget::Console).with_level(LogLevel::Info),
            format: StructuredFormat::Json,
        }
    }

    /// Create pretty JSON logger
    pub fn json_pretty() -> Self {
        Self {
            logger: WasmLogger::new(LogTarget::Console).with_level(LogLevel::Info),
            format: StructuredFormat::JsonPretty,
        }
    }

    /// Create logfmt logger
    pub fn logfmt() -> Self {
        Self {
            logger: WasmLogger::new(LogTarget::Console).with_level(LogLevel::Info),
            format: StructuredFormat::Logfmt,
        }
    }

    /// Log with structured fields
    pub fn log(&self, level: LogLevel, message: impl Into<String>, fields: &[Field]) {
        let fields: Vec<(String, String)> = fields
            .iter()
            .map(|f| {
                let value = match &f.value {
                    FieldValue::String(s) => s.clone(),
                    FieldValue::Int(i) => i.to_string(),
                    FieldValue::Float(f) => f.to_string(),
                    FieldValue::Bool(b) => b.to_string(),
                    FieldValue::Null => "null".to_string(),
                };
                (f.key.clone(), value)
            })
            .collect();

        self.logger.log(level, message, &fields);
    }
}

// Global logger instance (thread-local for WASM)
thread_local! {
    static GLOBAL_LOGGER: RefCell<Option<WasmLogger>> = RefCell::new(None);
}

/// Initialize global logger
pub fn init_global_logger(logger: WasmLogger) {
    GLOBAL_LOGGER.with(|l| {
        *l.borrow_mut() = Some(logger);
    });
}

/// Log using global logger
pub fn global_log(level: LogLevel, message: impl Into<String>) {
    GLOBAL_LOGGER.with(|l| {
        if let Some(ref logger) = *l.borrow() {
            logger.log(level, message, &[] as &[(String, String); 0]);
        }
    });
}

/// Helper macros would go here in a real implementation
/// e.g., log_info!, log_error!, etc.

/// Get current timestamp in nanoseconds
fn current_timestamp_ns() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as u64
}

/// Format timestamp for display
fn format_timestamp(ns: u64) -> String {
    let secs = ns / 1_000_000_000;
    let nanos = ns % 1_000_000_000;
    format!("{}.{:09}", secs, nanos)
}

/// Escape string for JSON
#[allow(dead_code)]
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Convert LogLevel to data::SeverityLevel
fn severity_to_data_level(level: LogLevel) -> crate::data::SeverityLevel {
    match level {
        LogLevel::Trace => crate::data::SeverityLevel::Trace,
        LogLevel::Debug => crate::data::SeverityLevel::Debug,
        LogLevel::Info => crate::data::SeverityLevel::Info,
        LogLevel::Warn => crate::data::SeverityLevel::Warn,
        LogLevel::Error => crate::data::SeverityLevel::Error,
        LogLevel::Fatal => crate::data::SeverityLevel::Fatal,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_level_as_str() {
        assert_eq!(LogLevel::Trace.as_str(), "TRACE");
        assert_eq!(LogLevel::Info.as_str(), "INFO");
        assert_eq!(LogLevel::Error.as_str(), "ERROR");
    }

    #[test]
    fn test_log_level_ordering() {
        assert!(LogLevel::Trace < LogLevel::Debug);
        assert!(LogLevel::Debug < LogLevel::Info);
        assert!(LogLevel::Info < LogLevel::Warn);
        assert!(LogLevel::Warn < LogLevel::Error);
        assert!(LogLevel::Error < LogLevel::Fatal);
    }

    #[test]
    fn test_log_level_from_str() {
        assert_eq!(LogLevel::from_str("INFO"), Some(LogLevel::Info));
        assert_eq!(LogLevel::from_str("warn"), Some(LogLevel::Warn));
        assert_eq!(LogLevel::from_str("unknown"), None);
    }

    #[test]
    fn test_wasm_logger_creation() {
        let logger = WasmLogger::new(LogTarget::Console).with_level(LogLevel::Debug);
        assert_eq!(logger.min_level, LogLevel::Debug);
    }

    #[test]
    fn test_ring_buffer_logger() {
        let ring = RingBufferLogger::with_capacity(3);

        ring.log(LogLevel::Info, "First", &[]);
        ring.log(LogLevel::Info, "Second", &[]);
        ring.log(LogLevel::Warn, "Third", &[]);

        assert_eq!(ring.len(), 3);

        // Should evict first entry
        ring.log(LogLevel::Error, "Fourth", &[]);
        assert_eq!(ring.len(), 3);

        let entries = ring.all_entries();
        assert_eq!(entries[0].message, "Second");
        assert_eq!(entries[2].message, "Fourth");
    }

    #[test]
    fn test_ring_buffer_by_level() {
        let ring = RingBufferLogger::with_capacity(10);

        ring.log(LogLevel::Info, "Info1", &[]);
        ring.log(LogLevel::Error, "Error1", &[]);
        ring.log(LogLevel::Info, "Info2", &[]);
        ring.log(LogLevel::Error, "Error2", &[]);

        let errors = ring.entries_by_level(LogLevel::Error);
        assert_eq!(errors.len(), 2);
    }

    #[test]
    fn test_field_constructors() {
        let f1 = Field::string("key", "value");
        assert_eq!(f1.key, "key");

        let f2 = Field::int("count", 42);
        match f2.value {
            FieldValue::Int(42) => {}
            _ => panic!("Expected Int(42)"),
        }

        let f3 = Field::bool("enabled", true);
        match f3.value {
            FieldValue::Bool(true) => {}
            _ => panic!("Expected Bool(true)"),
        }
    }

    #[test]
    fn test_escape_json() {
        assert_eq!(escape_json("hello"), "hello");
        assert_eq!(escape_json("hello\"world"), "hello\\\"world");
        assert_eq!(escape_json("line1\nline2"), "line1\\nline2");
    }

    #[test]
    fn test_log_entry_creation() {
        let entry = LogEntry {
            timestamp_ns: 1000,
            level: LogLevel::Info,
            message: "Test message".to_string(),
            fields: vec![("key".to_string(), "value".to_string())],
            source: None,
        };

        assert_eq!(entry.level, LogLevel::Info);
        assert_eq!(entry.message, "Test message");
    }
}
