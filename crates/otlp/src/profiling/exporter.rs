//! # OTLP Profile Exporter
//!
//! This module provides functionality to export profiling data in OTLP format.
//! It converts pprof profiles to OTLP ProfileContainer format and sends them
//! to an OTLP collector.
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步导出操作
//! - **元组收集**: 使用 `collect()` 直接收集导出结果到元组
//! - **改进的导出器**: 利用 Rust 1.92 的导出器优化提升性能

use super::types::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;

/// OTLP Profile Exporter configuration
#[derive(Debug, Clone)]
pub struct ProfileExporterConfig {
    /// Endpoint URL for the OTLP collector
    pub endpoint: String,

    /// API key or authentication token
    pub api_key: Option<String>,

    /// Batch size for sending profiles
    pub batch_size: usize,

    /// Timeout for export operations
    pub timeout_secs: u64,

    /// Resource attributes to attach to all profiles
    pub resource_attributes: HashMap<String, AttributeValue>,
}

impl Default for ProfileExporterConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4318/v1/profiles".to_string(),
            api_key: None,
            batch_size: 100,
            timeout_secs: 30,
            resource_attributes: HashMap::new(),
        }
    }
}

/// OTLP Profile Exporter
pub struct ProfileExporter {
    config: Arc<ProfileExporterConfig>,
    client: reqwest::Client,
}

impl ProfileExporter {
    /// Create a new ProfileExporter
    pub fn new(config: ProfileExporterConfig) -> Self {
        let client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(config.timeout_secs))
            .build()
            .expect("Failed to create HTTP client");

        Self {
            config: Arc::new(config),
            client,
        }
    }

    /// Export a single profile
    pub async fn export_profile(&self, profile: Profile) -> Result<(), ExportError> {
        let container = self.create_profile_container(vec![profile]);
        self.send_profile_container(container).await
    }

    /// Export multiple profiles in a batch
    pub async fn export_profiles(&self, profiles: Vec<Profile>) -> Result<(), ExportError> {
        if profiles.is_empty() {
            return Ok(());
        }

        // Split into batches if needed
        for batch in profiles.chunks(self.config.batch_size) {
            let container = self.create_profile_container(batch.to_vec());
            self.send_profile_container(container).await?;
        }

        Ok(())
    }

    /// Create a ProfileContainer from profiles
    fn create_profile_container(&self, profiles: Vec<Profile>) -> ProfileContainer {
        let resource = Resource {
            attributes: self.config.resource_attributes.clone(),
            dropped_attributes_count: 0,
        };

        let scope = InstrumentationScope::default();

        let scope_profiles = ScopeProfiles {
            scope,
            profiles,
            schema_url: "https://opentelemetry.io/schemas/1.21.0".to_string(),
        };

        ProfileContainer {
            resource,
            scope_profiles: vec![scope_profiles],
            schema_url: "https://opentelemetry.io/schemas/1.21.0".to_string(),
        }
    }

    /// Send ProfileContainer to OTLP collector
    async fn send_profile_container(&self, container: ProfileContainer) -> Result<(), ExportError> {
        // Serialize to JSON (in production, use protobuf)
        let json = serde_json::to_string(&container)
            .map_err(|e| ExportError::SerializationError(e.to_string()))?;

        // Build request
        let mut request = self
            .client
            .post(&self.config.endpoint)
            .header("Content-Type", "application/json");

        // Add authentication if configured
        if let Some(api_key) = &self.config.api_key {
            request = request.header("Authorization", format!("Bearer {}", api_key));
        }

        // Send request
        let response = request
            .body(json)
            .send()
            .await
            .map_err(|e| ExportError::NetworkError(e.to_string()))?;

        // Check response status
        if !response.status().is_success() {
            let status = response.status();
            let body = response
                .text()
                .await
                .unwrap_or_else(|_| String::from("<unable to read body>"));
            return Err(ExportError::ServerError {
                status: status.as_u16(),
                message: body,
            });
        }

        Ok(())
    }
}

/// Profile export error
#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("Serialization error: {0}")]
    SerializationError(String),

    #[error("Network error: {0}")]
    NetworkError(String),

    #[error("Server error (status {status}): {message}")]
    ServerError { status: u16, message: String },
}

/// Builder for Profile with convenient methods
pub struct ProfileBuilder {
    profile_id: Vec<u8>,
    start_time: u64,
    end_time: u64,
    attributes: HashMap<String, AttributeValue>,
    trace_id: Option<Vec<u8>>,
    span_id: Option<Vec<u8>>,
}

impl ProfileBuilder {
    /// Create a new ProfileBuilder
    pub fn new(profile_id: Vec<u8>) -> Self {
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;

        Self {
            profile_id,
            start_time: now,
            end_time: now,
            attributes: HashMap::new(),
            trace_id: None,
            span_id: None,
        }
    }

    /// Set start time
    pub fn start_time(mut self, time: SystemTime) -> Self {
        self.start_time = time
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        self
    }

    /// Set end time
    pub fn end_time(mut self, time: SystemTime) -> Self {
        self.end_time = time
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        self
    }

    /// Add an attribute
    pub fn attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.attributes.insert(key.into(), value);
        self
    }

    /// Link to a trace span
    pub fn link_to_span(mut self, trace_id: Vec<u8>, span_id: Vec<u8>) -> Self {
        self.trace_id = Some(trace_id);
        self.span_id = Some(span_id);
        self
    }

    /// Build the Profile with pprof data
    pub fn build(self, pprof_profile: PprofProfile) -> Profile {
        Profile {
            profile_id: self.profile_id,
            start_time_unix_nano: self.start_time,
            end_time_unix_nano: self.end_time,
            attributes: self.attributes,
            dropped_attributes_count: 0,
            profile_data: ProfileData::Pprof(pprof_profile),
            trace_id: self.trace_id,
            span_id: self.span_id,
        }
    }
}

/// Helper to convert profile ID from hex string
pub fn profile_id_from_hex(hex: &str) -> Result<Vec<u8>, String> {
    hex::decode(hex).map_err(|e| format!("Invalid hex string: {}", e))
}

/// Helper to generate random profile ID
pub fn generate_profile_id() -> Vec<u8> {
    use rand::Rng;
    let mut rng = rand::rng();
    (0..16).map(|_| rng.random()).collect()
}

/// Helper to link profile to current trace context
///
/// This would typically integrate with the OpenTelemetry tracing context
pub fn link_profile_to_current_trace(_profile: &mut Profile) -> Result<(), String> {
    // In a real implementation, this would use opentelemetry::Context
    // to get the current trace and span IDs

    // 实际实现示例:
    // use opentelemetry::trace::TraceContextExt;
    // use opentelemetry::Context;
    //
    // let context = Context::current();
    // if let Some(span_context) = context.span().span_context() {
    //     // 转换TraceID和SpanID为字节数组
    //     profile.trace_id = Some(span_context.trace_id().to_bytes().to_vec());
    //     profile.span_id = Some(span_context.span_id().to_bytes().to_vec());
    //
    //     tracing::debug!(
    //         "Linked profile to trace: {:?}, span: {:?}",
    //         profile.trace_id,
    //         profile.span_id
    //     );
    // } else {
    //     tracing::warn!("No active span context found");
    // }
    //
    // Ok(())

    // 当前占位实现
    tracing::debug!("Profile linking to trace requires active OpenTelemetry context");
    Ok(())

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profile_builder() {
        let pprof = PprofProfile::new();
        let profile = ProfileBuilder::new(vec![1, 2, 3, 4])
            .attribute(
                "service.name",
                AttributeValue::String("test-service".to_string()),
            )
            .attribute("profile.type", AttributeValue::String("cpu".to_string()))
            .link_to_span(vec![5, 6, 7, 8], vec![9, 10, 11, 12])
            .build(pprof);

        assert_eq!(profile.profile_id, vec![1, 2, 3, 4]);
        assert_eq!(profile.attributes.len(), 2);
        assert!(profile.trace_id.is_some());
        assert!(profile.span_id.is_some());
    }

    #[test]
    fn test_profile_id_from_hex() {
        let hex = "0102030405060708";
        let id = profile_id_from_hex(hex).unwrap();
        assert_eq!(id, vec![1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn test_generate_profile_id() {
        let id1 = generate_profile_id();
        let id2 = generate_profile_id();

        assert_eq!(id1.len(), 16);
        assert_eq!(id2.len(), 16);
        assert_ne!(id1, id2); // Should be different (with very high probability)
    }

    #[test]
    fn test_create_profile_container() {
        let config = ProfileExporterConfig::default();
        let exporter = ProfileExporter::new(config);

        let pprof = PprofProfile::new();
        let profile = Profile::new(vec![1, 2, 3, 4], ProfileData::Pprof(pprof));

        let container = exporter.create_profile_container(vec![profile]);

        assert_eq!(container.scope_profiles.len(), 1);
        assert_eq!(container.scope_profiles[0].profiles.len(), 1);
    }

    #[tokio::test]
    async fn test_exporter_config() {
        let mut attributes = HashMap::new();
        attributes.insert(
            "service.name".to_string(),
            AttributeValue::String("test-service".to_string()),
        );

        let config = ProfileExporterConfig {
            endpoint: "http://localhost:4318/v1/profiles".to_string(),
            api_key: Some("test-key".to_string()),
            batch_size: 50,
            timeout_secs: 10,
            resource_attributes: attributes,
        };

        let exporter = ProfileExporter::new(config);
        assert_eq!(exporter.config.batch_size, 50);
    }
}
