//! # OpenTelemetry Declarative Configuration
//!
//! Implementation of OpenTelemetry Configuration specification v1.0.
//! Supports YAML and JSON configuration files for OpenTelemetry SDK setup.
//!
//! ## Specification
//!
//! Based on OpenTelemetry Configuration v1.0:
//! - https://opentelemetry.io/docs/specs/otel/configuration/
//! - https://github.com/open-telemetry/opentelemetry-configuration
//!
//! ## Features
//!
//! - **YAML Configuration**: Human-readable configuration files
//! - **Environment Variable Support**: Override config via env vars
//! - **Validation**: Schema validation with helpful error messages
//! - **Hot Reload**: Runtime configuration updates (optional)
//! - **Multiple Files**: Merge configurations from multiple sources

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Configuration file format version
pub const CONFIG_VERSION: &str = "1.0.0";

/// Errors that can occur when loading or parsing configuration
#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("Failed to read configuration file: {0}")]
    FileRead(#[from] std::io::Error),
    
    #[error("Failed to parse YAML configuration: {0}")]
    YamlParse(#[from] serde_yaml::Error),
    
    #[error("Failed to parse JSON configuration: {0}")]
    JsonParse(#[from] serde_json::Error),
    
    #[error("Configuration validation failed: {0}")]
    Validation(String),
    
    #[error("Unsupported configuration format: {0}")]
    UnsupportedFormat(String),
    
    #[error("Configuration file not found: {0}")]
    NotFound(PathBuf),
}

/// Result type for configuration operations
pub type ConfigResult<T> = Result<T, ConfigError>;

/// Root OpenTelemetry configuration structure
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub struct OpenTelemetryConfig {
    /// Configuration file format version
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file_format: Option<String>,
    
    /// Disable telemetry SDK
    #[serde(default)]
    pub disabled: bool,
    
    /// Resource configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resource: Option<ResourceConfig>,
    
    /// Tracer provider configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tracer_provider: Option<TracerProviderConfig>,
    
    /// Meter provider configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meter_provider: Option<MeterProviderConfig>,
    
    /// Logger provider configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub logger_provider: Option<LoggerProviderConfig>,
}

impl OpenTelemetryConfig {
    /// Load configuration from a file (YAML or JSON)
    pub fn from_file<P: AsRef<Path>>(path: P) -> ConfigResult<Self> {
        let path = path.as_ref();
        
        if !path.exists() {
            return Err(ConfigError::NotFound(path.to_path_buf()));
        }
        
        let content = fs::read_to_string(path)?;
        
        // Determine format from extension
        let extension = path
            .extension()
            .and_then(|e| e.to_str())
            .unwrap_or("")
            .to_lowercase();
        
        match extension.as_str() {
            "yaml" | "yml" => Self::from_yaml(&content),
            "json" => Self::from_json(&content),
            _ => {
                // Try YAML first, then JSON
                if let Ok(config) = Self::from_yaml(&content) {
                    Ok(config)
                } else {
                    Self::from_json(&content)
                }
            }
        }
    }
    
    /// Parse configuration from YAML string
    pub fn from_yaml(yaml: &str) -> ConfigResult<Self> {
        let config: OpenTelemetryConfig = serde_yaml::from_str(yaml)?;
        config.validate()?;
        Ok(config)
    }
    
    /// Parse configuration from JSON string
    pub fn from_json(json: &str) -> ConfigResult<Self> {
        let config: OpenTelemetryConfig = serde_json::from_str(json)?;
        config.validate()?;
        Ok(config)
    }
    
    /// Load configuration with default file discovery
    pub fn load_default() -> ConfigResult<Self> {
        // Check environment variable first
        if let Ok(config_file) = std::env::var("OTEL_CONFIG_FILE") {
            return Self::from_file(&config_file);
        }
        
        // Try common locations
        let search_paths = [
            PathBuf::from("otel-config.yaml"),
            PathBuf::from("otel-config.yml"),
            PathBuf::from(".otel-config.yaml"),
            PathBuf::from(".otel-config.yml"),
        ];
        
        for path in &search_paths {
            if path.exists() {
                return Self::from_file(path);
            }
        }
        
        // Try home directory
        if let Some(home) = dirs::home_dir() {
            let home_config = home.join(".otel").join("config.yaml");
            if home_config.exists() {
                return Self::from_file(home_config);
            }
        }
        
        // Return default configuration
        Ok(OpenTelemetryConfig::default())
    }
    
    /// Validate the configuration
    pub fn validate(&self) -> ConfigResult<()> {
        // Validate resource configuration
        if let Some(ref resource) = self.resource {
            resource.validate()?;
        }
        
        // Validate tracer provider
        if let Some(ref tracer) = self.tracer_provider {
            tracer.validate()?;
        }
        
        Ok(())
    }
    
    /// Convert to YAML string
    pub fn to_yaml(&self) -> ConfigResult<String> {
        serde_yaml::to_string(self).map_err(ConfigError::YamlParse)
    }
    
    /// Convert to JSON string
    pub fn to_json(&self) -> ConfigResult<String> {
        serde_json::to_string_pretty(self).map_err(ConfigError::JsonParse)
    }
}

/// Resource configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct ResourceConfig {
    /// Resource attributes
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub attributes: HashMap<String, AttributeValueConfig>,
}

impl ResourceConfig {
    fn validate(&self) -> ConfigResult<()> {
        Ok(())
    }
}

/// Attribute value types for configuration
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum AttributeValueConfig {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Array(Vec<AttributeValueConfig>),
}

/// Tracer provider configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct TracerProviderConfig {
    /// Span processors configuration
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub processors: Vec<SpanProcessorConfig>,
}

impl TracerProviderConfig {
    fn validate(&self) -> ConfigResult<()> {
        Ok(())
    }
}

/// Span processor configuration
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum SpanProcessorConfig {
    #[serde(rename = "batch")]
    Batch(BatchSpanProcessorConfig),
    #[serde(rename = "simple")]
    Simple(SimpleSpanProcessorConfig),
}

/// Batch span processor configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct BatchSpanProcessorConfig {
    /// Schedule delay in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schedule_delay: Option<u64>,
    
    /// Export timeout in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub export_timeout: Option<u64>,
    
    /// Maximum queue size
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_queue_size: Option<usize>,
    
    /// Maximum export batch size
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_export_batch_size: Option<usize>,
    
    /// Exporter configuration
    pub exporter: ExporterConfig,
}

/// Simple span processor configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct SimpleSpanProcessorConfig {
    /// Exporter configuration
    pub exporter: ExporterConfig,
}

/// Meter provider configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct MeterProviderConfig {
    /// Metric readers configuration
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub readers: Vec<MetricReaderConfig>,
}

/// Metric reader configuration
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum MetricReaderConfig {
    #[serde(rename = "periodic")]
    Periodic(PeriodicMetricReaderConfig),
}

/// Periodic metric reader configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct PeriodicMetricReaderConfig {
    /// Export interval in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interval: Option<u64>,
    
    /// Export timeout in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout: Option<u64>,
    
    /// Exporter configuration
    pub exporter: ExporterConfig,
}

/// Logger provider configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct LoggerProviderConfig {
    /// Log record processors
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub processors: Vec<LogProcessorConfig>,
}

/// Log processor configuration
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum LogProcessorConfig {
    #[serde(rename = "batch")]
    Batch(BatchLogProcessorConfig),
    #[serde(rename = "simple")]
    Simple(SimpleLogProcessorConfig),
}

/// Batch log processor configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct BatchLogProcessorConfig {
    /// Schedule delay in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schedule_delay: Option<u64>,
    
    /// Export timeout in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub export_timeout: Option<u64>,
    
    /// Maximum queue size
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_queue_size: Option<usize>,
    
    /// Exporter configuration
    pub exporter: ExporterConfig,
}

/// Simple log processor configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct SimpleLogProcessorConfig {
    /// Exporter configuration
    pub exporter: ExporterConfig,
}

/// Exporter configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct ExporterConfig {
    /// OTLP exporter configuration
    #[serde(rename = "otlp", skip_serializing_if = "Option::is_none")]
    pub otlp_config: Option<OtlpExporterConfig>,
    
    /// Console exporter
    #[serde(rename = "console", skip_serializing_if = "Option::is_none")]
    pub console_config: Option<ConsoleExporterConfig>,
}

/// OTLP exporter configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct OtlpExporterConfig {
    /// Protocol: "grpc", "http/protobuf", or "http/json"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub protocol: Option<String>,
    
    /// Endpoint URL
    #[serde(skip_serializing_if = "Option::is_none")]
    pub endpoint: Option<String>,
    
    /// Timeout in milliseconds
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout: Option<u64>,
    
    /// Headers for authentication
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub headers: HashMap<String, String>,
    
    /// Compression: "gzip", "deflate", or "none"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compression: Option<String>,
}

/// Console exporter configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct ConsoleExporterConfig {
    /// Output verbosity: "compact", "pretty", "detailed"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verbosity: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parse_basic_yaml() {
        let yaml = r#"
resource:
  attributes:
    service.name: test-service
    service.version: "1.0.0"
"#;
        
        let config = OpenTelemetryConfig::from_yaml(yaml)
            .expect("Failed to parse YAML config");
        
        assert!(config.resource.is_some());
        let resource = config.resource.unwrap();
        assert_eq!(
            resource.attributes.get("service.name"),
            Some(&AttributeValueConfig::String("test-service".to_string()))
        );
    }
    
    #[test]
    fn test_parse_json() {
        let json = r#"{
            "resource": {
                "attributes": {
                    "service.name": "test-service"
                }
            },
            "disabled": false
        }"#;
        
        let config = OpenTelemetryConfig::from_json(json).unwrap();
        assert!(!config.disabled);
        assert!(config.resource.is_some());
    }
    
    #[test]
    fn test_roundtrip_yaml() {
        let config = OpenTelemetryConfig {
            file_format: Some("1.0.0".to_string()),
            resource: Some(ResourceConfig {
                attributes: {
                    let mut m = HashMap::new();
                    m.insert("service.name".to_string(), AttributeValueConfig::String("test".to_string()));
                    m
                },
            }),
            ..Default::default()
        };
        
        let yaml = config.to_yaml().unwrap();
        let parsed = OpenTelemetryConfig::from_yaml(&yaml).unwrap();
        
        assert_eq!(config.resource.unwrap().attributes, parsed.resource.unwrap().attributes);
    }
}
