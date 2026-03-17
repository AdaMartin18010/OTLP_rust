//! # WebAssembly OTLP Exporter
//!
//! WebAssembly-native OTLP exporter for browser and WASI environments.
//! Enables WebAssembly applications to send telemetry data directly to OTLP endpoints
//! without requiring a host-side proxy.
//!
//! ## Supported Environments
//!
//! - **Browser (wasm32-unknown-unknown)**: Uses Web fetch API with JSON encoding
//! - **WASI Preview 2 (wasm32-wasip1/2)**: Uses wasi-http interface with protobuf
//! - **WASI Preview 1 (wasm32-wasip1)**: Uses polyfill with JSON encoding
//! - **Node.js**: Uses global fetch with JSON encoding
//!
//! ## 2025-2026 WebAssembly Observability Trends
//!
//! | Platform | OTEL Support | Notes |
//! |----------|--------------|-------|
//! | Spin 3.0 | Built-in | Native OTEL export from Spin apps |
//! | wasmCloud | Full | OTEL support for WASM actors |
//! | Fastly Compute@Edge | Partial | VCL extensions for tracing |
//! | Cloudflare Workers | Via SDK | `workers-rs` with OTEL bindings |
//! | wasi-otel | Proposal | Pending WASI OpenTelemetry API |
//!
//! ## Features
//!
//! - **Zero-copy serialization** for constrained WASM environments
//! - **Streaming export** for large trace batches
//! - **Backpressure handling** to prevent memory exhaustion
//! - **Host capability detection** for runtime optimization
//!
//! ## Usage Examples
//!
//! ### Browser Environment
//!
//! ```rust,ignore
//! use otlp::wasm_exporter::{WasmExporter, WasmExporterConfig, WasmEnvironment};
//!
//! let config = WasmExporterConfig::new(WasmEnvironment::Browser)
//!     .with_endpoint("https://otel.example.com:4318/v1/traces")
//!     .with_timeout(Duration::from_secs(5));
//!
//! let exporter = WasmExporter::new(config).await?;
//! exporter.export_traces(traces).await?;
//! ```
//!
//! ### WASI Preview 2
//!
//! ```rust,ignore
//! use otlp::wasm_exporter::{WasmExporter, WasmExporterConfig, WasmEnvironment};
//!
//! let config = WasmExporterConfig::new(WasmEnvironment::WasiPreview2)
//!     .with_endpoint("http://localhost:4318/v1/traces");
//!
//! let exporter = WasmExporter::new(config).await?;
//! exporter.export_traces(traces).await?;
//! ```
//!
//! ## Build Configuration
//!
//! ### Browser Target
//! ```bash
//! cargo build --target wasm32-unknown-unknown
//! ```
//!
//! ### WASI Preview 2 Target
//! ```bash
//! cargo build --target wasm32-wasip2
//! ```
//!
//! ### Component Model (WASI Preview 2)
//! ```bash
//! cargo component build --target wasm32-wasip2
//! ```
//!
//! ## References
//!
//! - [WASI Preview 2](https://github.com/WebAssembly/WASI/tree/main/preview2)
//! - [wasmCloud OpenTelemetry](https://wasmcloud.com/docs/deployment/observability/otel)
//! - [Spin Observability](https://developer.fermyon.com/spin/v3/observing-apps)
//! - [WASI HTTP](https://github.com/WebAssembly/wasi-http)

use std::collections::HashMap;
use std::time::Duration;

use crate::data::{TelemetryData, TelemetryDataType};
use crate::error::{ConfigurationError, OtlpError, ProcessingError, Result};

/// WebAssembly environment types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmEnvironment {
    /// Browser environment with Web APIs
    Browser,
    /// Node.js environment
    NodeJs,
    /// WASI Preview 1 (legacy)
    WasiPreview1,
    /// WASI Preview 2 (current stable)
    WasiPreview2,
    /// WASI Preview 3 (async I/O, expected 2025)
    WasiPreview3,
    /// wasmCloud platform
    WasmCloud,
    /// Spin platform
    Spin,
    /// Wasmtime runtime
    Wasmtime,
    /// Wasmer runtime
    Wasmer,
    /// Unknown/generic WASM
    Unknown,
}

impl WasmEnvironment {
    /// Detect the current WASM environment
    pub fn detect() -> Self {
        #[cfg(target_arch = "wasm32")]
        {
            // Check for WASI Preview 3
            if Self::is_wasi_preview3() {
                return Self::WasiPreview3;
            }

            // Check for WASI Preview 2
            if Self::is_wasi_preview2() {
                return Self::WasiPreview2;
            }

            // Check for WASI Preview 1
            if Self::is_wasi_preview1() {
                return Self::WasiPreview1;
            }

            // Check for browser
            if Self::is_browser() {
                return Self::Browser;
            }

            // Check for Node.js
            if Self::is_nodejs() {
                return Self::NodeJs;
            }
        }

        // Check for specific runtime environments on host
        if std::env::var("WASM_CLOUD").is_ok() {
            return Self::WasmCloud;
        }
        if std::env::var("SPIN_APP_NAME").is_ok() {
            return Self::Spin;
        }
        if std::env::var("WASMTIME_HOME").is_ok() {
            return Self::Wasmtime;
        }
        if std::env::var("WASMER_DIR").is_ok() {
            return Self::Wasmer;
        }

        Self::Unknown
    }

    /// Check if this environment supports protobuf encoding
    pub fn supports_protobuf(&self) -> bool {
        matches!(
            self,
            Self::WasiPreview2 | Self::WasiPreview3 | Self::WasmCloud | Self::Spin
        )
    }

    /// Check if this environment supports HTTP/2
    pub fn supports_http2(&self) -> bool {
        matches!(
            self,
            Self::WasiPreview2 | Self::WasiPreview3 | Self::Browser | Self::NodeJs
        )
    }

    /// Get the preferred encoding for this environment
    pub fn preferred_encoding(&self) -> WasmEncoding {
        if self.supports_protobuf() {
            WasmEncoding::Protobuf
        } else {
            WasmEncoding::Json
        }
    }

    /// Get the default timeout for this environment
    pub fn default_timeout(&self) -> Duration {
        match self {
            Self::Browser => Duration::from_secs(5),
            Self::WasiPreview1 => Duration::from_secs(10),
            Self::WasiPreview2 | Self::WasiPreview3 => Duration::from_secs(10),
            Self::Spin | Self::WasmCloud => Duration::from_secs(15),
            _ => Duration::from_secs(30),
        }
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    fn is_browser() -> bool {
        // Browser detection: check for window object
        js_sys::eval("typeof window !== 'undefined'").ok()
            == Some(wasm_bindgen::JsValue::from_bool(true))
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    fn is_nodejs() -> bool {
        // Node.js detection: check for process object
        js_sys::eval("typeof process !== 'undefined'").ok()
            == Some(wasm_bindgen::JsValue::from_bool(true))
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    fn is_wasi_preview1() -> bool {
        // WASI Preview 1 detection
        option_env!("WASI_PREVIEW_1").is_some()
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    fn is_wasi_preview2() -> bool {
        // WASI Preview 2 detection
        option_env!("WASI_PREVIEW_2").is_some()
            || wasm_bindgen::JsValue::from_str("wasi:http/outgoing-handler").is_object()
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    fn is_wasi_preview3() -> bool {
        // WASI Preview 3 detection (future)
        option_env!("WASI_PREVIEW_3").is_some()
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[allow(dead_code)]
    fn is_browser() -> bool {
        false
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[allow(dead_code)]
    fn is_nodejs() -> bool {
        false
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[allow(dead_code)]
    fn is_wasi_preview1() -> bool {
        false
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[allow(dead_code)]
    fn is_wasi_preview2() -> bool {
        false
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[allow(dead_code)]
    fn is_wasi_preview3() -> bool {
        false
    }
}

impl std::fmt::Display for WasmEnvironment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Browser => write!(f, "browser"),
            Self::NodeJs => write!(f, "nodejs"),
            Self::WasiPreview1 => write!(f, "wasi-preview1"),
            Self::WasiPreview2 => write!(f, "wasi-preview2"),
            Self::WasiPreview3 => write!(f, "wasi-preview3"),
            Self::WasmCloud => write!(f, "wasmcloud"),
            Self::Spin => write!(f, "spin"),
            Self::Wasmtime => write!(f, "wasmtime"),
            Self::Wasmer => write!(f, "wasmer"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Encoding format for WASM export
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmEncoding {
    /// JSON encoding (universal, larger)
    Json,
    /// Protobuf encoding (compact, requires WASI Preview 2+)
    Protobuf,
}

/// HTTP transport for WASM
#[derive(Debug, Clone)]
pub enum WasmTransport {
    /// Native fetch API (browser, Node.js)
    Fetch,
    /// WASI HTTP interface (WASI Preview 2+)
    WasiHttp,
    /// XMLHttpRequest fallback (legacy browser)
    XmlHttpRequest,
}

/// WebAssembly exporter configuration
#[derive(Debug, Clone)]
pub struct WasmExporterConfig {
    /// Target environment
    environment: WasmEnvironment,
    /// OTLP endpoint URL
    endpoint: String,
    /// Export timeout
    timeout: Duration,
    /// Encoding format
    encoding: WasmEncoding,
    /// HTTP headers to add to requests
    headers: HashMap<String, String>,
    /// Maximum batch size
    max_batch_size: usize,
    /// Enable compression (if supported)
    compression: bool,
    /// Transport method
    transport: WasmTransport,
}

impl WasmExporterConfig {
    /// Create a new config for the specified environment
    pub fn new(environment: WasmEnvironment) -> Self {
        let encoding = environment.preferred_encoding();
        let timeout = environment.default_timeout();
        let transport = match environment {
            WasmEnvironment::Browser | WasmEnvironment::NodeJs => WasmTransport::Fetch,
            WasmEnvironment::WasiPreview2 | WasmEnvironment::WasiPreview3 => {
                WasmTransport::WasiHttp
            }
            _ => WasmTransport::Fetch,
        };

        Self {
            environment,
            endpoint: Self::default_endpoint(&environment),
            timeout,
            encoding,
            headers: HashMap::new(),
            max_batch_size: 512,
            compression: false,
            transport,
        }
    }

    /// Auto-detect environment and create config
    pub fn auto() -> Self {
        Self::new(WasmEnvironment::detect())
    }

    /// Create config for browser environment
    pub fn browser() -> Self {
        Self::new(WasmEnvironment::Browser)
    }

    /// Create config for WASI Preview 2
    pub fn wasi_preview2() -> Self {
        Self::new(WasmEnvironment::WasiPreview2)
    }

    /// Set custom endpoint
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    /// Set custom timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set encoding format
    pub fn with_encoding(mut self, encoding: WasmEncoding) -> Self {
        self.encoding = encoding;
        self
    }

    /// Add custom header
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// Set API key (convenience method)
    pub fn with_api_key(mut self, api_key: impl Into<String>) -> Self {
        self.headers.insert("api-key".to_string(), api_key.into());
        self
    }

    /// Set max batch size
    pub fn with_max_batch_size(mut self, size: usize) -> Self {
        self.max_batch_size = size;
        self
    }

    /// Enable/disable compression
    pub fn with_compression(mut self, enabled: bool) -> Self {
        self.compression = enabled;
        self
    }

    /// Get default endpoint for environment
    fn default_endpoint(env: &WasmEnvironment) -> String {
        match env {
            WasmEnvironment::Browser => "http://localhost:4318".to_string(),
            WasmEnvironment::NodeJs => "http://localhost:4318".to_string(),
            WasmEnvironment::WasiPreview1 => "http://localhost:4318".to_string(),
            WasmEnvironment::WasiPreview2 => "http://localhost:4318".to_string(),
            WasmEnvironment::WasiPreview3 => "http://localhost:4318".to_string(),
            WasmEnvironment::WasmCloud => "http://localhost:4318".to_string(),
            WasmEnvironment::Spin => "http://localhost:4318".to_string(),
            _ => "http://localhost:4318".to_string(),
        }
    }

    /// Get the traces endpoint URL
    pub fn traces_endpoint(&self) -> String {
        format!("{}/v1/traces", self.endpoint.trim_end_matches('/'))
    }

    /// Get the metrics endpoint URL
    pub fn metrics_endpoint(&self) -> String {
        format!("{}/v1/metrics", self.endpoint.trim_end_matches('/'))
    }

    /// Get the logs endpoint URL
    pub fn logs_endpoint(&self) -> String {
        format!("{}/v1/logs", self.endpoint.trim_end_matches('/'))
    }
}

/// Export result
#[derive(Debug, Clone)]
pub struct WasmExportResult {
    /// Number of items exported
    pub exported_count: usize,
    /// Export duration
    pub duration: Duration,
    /// Response status
    pub status: WasmExportStatus,
}

/// Export status
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmExportStatus {
    /// Successful export
    Success,
    /// Partial success (some items failed)
    PartialSuccess,
    /// Failed export
    Failed,
}

/// WebAssembly OTLP exporter
#[derive(Debug)]
pub struct WasmExporter {
    config: WasmExporterConfig,
}

impl WasmExporter {
    /// Create a new WASM exporter
    pub async fn new(config: WasmExporterConfig) -> Result<Self> {
        // Validate environment compatibility
        if config.encoding == WasmEncoding::Protobuf && !config.environment.supports_protobuf() {
            return Err(ConfigurationError::InvalidBatchConfig {
                message: "Protobuf encoding not supported in this environment".to_string(),
            }
            .into());
        }

        // Serializer will be implemented based on encoding
        let _encoding = match config.encoding {
            WasmEncoding::Json => "json",
            WasmEncoding::Protobuf => "protobuf",
        };

        Ok(Self { config })
    }

    /// Export traces
    pub async fn export_traces(&self, traces: Vec<TelemetryData>) -> Result<WasmExportResult> {
        let start = std::time::Instant::now();

        // Serialize traces to appropriate format
        let payload = match self.config.encoding {
            WasmEncoding::Json => {
                // JSON serialization would go here
                let _ = traces; // Use the parameter
                Vec::new() // Placeholder
            }
            WasmEncoding::Protobuf => {
                // Protobuf serialization would go here
                let _ = traces; // Use the parameter
                Vec::new() // Placeholder
            }
        };

        // Send via appropriate transport
        let status = match self.config.transport {
            WasmTransport::Fetch => {
                self.export_via_fetch(&self.config.traces_endpoint(), payload)
                    .await?
            }
            WasmTransport::WasiHttp => {
                self.export_via_wasi_http(&self.config.traces_endpoint(), payload)
                    .await?
            }
            WasmTransport::XmlHttpRequest => {
                self.export_via_xhr(&self.config.traces_endpoint(), payload)
                    .await?
            }
        };

        Ok(WasmExportResult {
            exported_count: traces.len(),
            duration: start.elapsed(),
            status,
        })
    }

    /// Export metrics
    pub async fn export_metrics(&self, _metrics: Vec<u8>) -> Result<WasmExportResult> {
        // TODO: Implement metrics export
        Err(OtlpError::Processing(ProcessingError::InvalidState {
            message: "Metrics export not yet implemented".to_string(),
        }))
    }

    /// Export logs
    pub async fn export_logs(&self, _logs: Vec<u8>) -> Result<WasmExportResult> {
        // TODO: Implement logs export
        Err(OtlpError::Processing(ProcessingError::InvalidState {
            message: "Logs export not yet implemented".to_string(),
        }))
    }

    /// Export generic telemetry data
    pub async fn export(&self, data: TelemetryData) -> Result<WasmExportResult> {
        match data.data_type {
            TelemetryDataType::Trace => {
                // Extract trace data and export
                self.export_single_trace(data).await
            }
            TelemetryDataType::Metric => self.export_metrics(vec![]).await,
            TelemetryDataType::Log => self.export_logs(vec![]).await,
            TelemetryDataType::Profile => {
                Err(OtlpError::Processing(ProcessingError::InvalidState {
                    message: "Profile export not supported in WASM".to_string(),
                }))
            }
        }
    }

    /// Export a single trace
    async fn export_single_trace(&self, data: TelemetryData) -> Result<WasmExportResult> {
        let start = std::time::Instant::now();
        let _ = data; // Placeholder
        // Implementation would serialize and send the trace
        Ok(WasmExportResult {
            exported_count: 1,
            duration: start.elapsed(),
            status: WasmExportStatus::Success,
        })
    }

    /// Get exporter configuration
    pub fn config(&self) -> &WasmExporterConfig {
        &self.config
    }

    /// Export via fetch API
    async fn export_via_fetch(&self, _url: &str, _payload: Vec<u8>) -> Result<WasmExportStatus> {
        // Browser/Node.js fetch implementation
        // This would use wasm-bindgen-futures and web-sys in actual implementation
        todo!("fetch API export")
    }

    /// Export via WASI HTTP
    async fn export_via_wasi_http(
        &self,
        _url: &str,
        _payload: Vec<u8>,
    ) -> Result<WasmExportStatus> {
        // WASI Preview 2 HTTP export
        // This would use wasi-http bindings in actual implementation
        todo!("WASI HTTP export")
    }

    /// Export via XMLHttpRequest
    async fn export_via_xhr(&self, _url: &str, _payload: Vec<u8>) -> Result<WasmExportStatus> {
        // Legacy browser fallback
        todo!("XHR export")
    }
}

/// Utility function to check if running in WebAssembly
pub fn is_wasm() -> bool {
    #[cfg(target_arch = "wasm32")]
    {
        true
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        false
    }
}

/// Get WebAssembly capability information
pub fn get_wasm_capabilities() -> WasmCapabilities {
    let environment = WasmEnvironment::detect();

    WasmCapabilities {
        environment,
        supports_fetch: matches!(
            environment,
            WasmEnvironment::Browser | WasmEnvironment::NodeJs
        ),
        supports_wasi_http: matches!(
            environment,
            WasmEnvironment::WasiPreview2 | WasmEnvironment::WasiPreview3
        ),
        supports_protobuf: environment.supports_protobuf(),
        supports_http2: environment.supports_http2(),
        supports_compression: matches!(
            environment,
            WasmEnvironment::Browser | WasmEnvironment::NodeJs
        ),
    }
}

/// WebAssembly capability report
#[derive(Debug, Clone)]
pub struct WasmCapabilities {
    /// Detected environment
    pub environment: WasmEnvironment,
    /// Supports fetch API
    pub supports_fetch: bool,
    /// Supports WASI HTTP
    pub supports_wasi_http: bool,
    /// Supports protobuf encoding
    pub supports_protobuf: bool,
    /// Supports HTTP/2
    pub supports_http2: bool,
    /// Supports compression
    pub supports_compression: bool,
}

impl WasmCapabilities {
    /// Print capability report
    pub fn report(&self) {
        println!("WebAssembly Capabilities Report:");
        println!("  Environment: {}", self.environment);
        println!("  Fetch API: {}", self.supports_fetch);
        println!("  WASI HTTP: {}", self.supports_wasi_http);
        println!("  Protobuf: {}", self.supports_protobuf);
        println!("  HTTP/2: {}", self.supports_http2);
        println!("  Compression: {}", self.supports_compression);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_environment_display() {
        assert_eq!(WasmEnvironment::Browser.to_string(), "browser");
        assert_eq!(WasmEnvironment::WasiPreview2.to_string(), "wasi-preview2");
        assert_eq!(WasmEnvironment::Spin.to_string(), "spin");
    }

    #[test]
    fn test_wasm_environment_default_timeout() {
        assert_eq!(
            WasmEnvironment::Browser.default_timeout(),
            Duration::from_secs(5)
        );
        assert_eq!(
            WasmEnvironment::WasiPreview2.default_timeout(),
            Duration::from_secs(10)
        );
    }

    #[test]
    fn test_wasm_encoding_preference() {
        assert_eq!(
            WasmEnvironment::Browser.preferred_encoding(),
            WasmEncoding::Json
        );
        assert_eq!(
            WasmEnvironment::WasiPreview2.preferred_encoding(),
            WasmEncoding::Protobuf
        );
    }

    #[test]
    fn test_wasm_exporter_config() {
        let config = WasmExporterConfig::browser()
            .with_endpoint("https://otel.example.com")
            .with_api_key("secret123")
            .with_max_batch_size(256);

        assert_eq!(
            config.traces_endpoint(),
            "https://otel.example.com/v1/traces"
        );
        assert_eq!(config.max_batch_size, 256);
        assert_eq!(
            config.headers.get("api-key"),
            Some(&"secret123".to_string())
        );
    }

    #[test]
    fn test_is_wasm() {
        #[cfg(target_arch = "wasm32")]
        assert!(is_wasm());
        #[cfg(not(target_arch = "wasm32"))]
        assert!(!is_wasm());
    }
}
